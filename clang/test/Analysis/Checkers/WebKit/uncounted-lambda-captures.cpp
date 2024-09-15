// RUN: %clang_analyze_cc1 -analyzer-checker=webkit.UncountedLambdaCapturesChecker %s 2>&1 | FileCheck %s --strict-whitespace
#include "mock-types.h"

namespace WTF {

namespace Detail {

template<typename Out, typename... In>
class CallableWrapperBase {
public:
    virtual ~CallableWrapperBase() { }
    virtual Out call(In...) = 0;
};

template<typename, typename, typename...> class CallableWrapper;

template<typename CallableType, typename Out, typename... In>
class CallableWrapper : public CallableWrapperBase<Out, In...> {
public:
    explicit CallableWrapper(CallableType&& callable)
        : m_callable(callable) { }
    CallableWrapper(const CallableWrapper&) = delete;
    CallableWrapper& operator=(const CallableWrapper&) = delete;
    Out call(In... in) final { m_callable(in...); }
private:
    CallableType m_callable;
};

} // namespace Detail

template<typename> class Function;

template<typename Out, typename... In> Function<Out(In...)> adopt(Detail::CallableWrapperBase<Out, In...>*);

template <typename Out, typename... In>
class Function<Out(In...)> {
public:
    using Impl = Detail::CallableWrapperBase<Out, In...>;

    Function() = default;

    template<typename FunctionType>
    Function(FunctionType&& f)
        : m_callableWrapper(new Detail::CallableWrapper<FunctionType, Out, In...>(f)) { }

    Out operator()(In... in) const
    {
      return m_callableWrapper->call(in...);
    }

    explicit operator bool() const { return !!m_callableWrapper; }

private:
    enum AdoptTag { Adopt };
    Function(Impl* impl, AdoptTag)
        : m_callableWrapper(impl)
    {
    }

    friend Function adopt<Out, In...>(Impl*);

    Impl* m_callableWrapper;
};

template<typename Out, typename... In> Function<Out(In...)> adopt(Detail::CallableWrapperBase<Out, In...>* impl)
{
    return Function<Out(In...)>(impl, Function<Out(In...)>::Adopt);
}

}

using WTF::Function;

#define NOESCAPE __attribute__((noescape))

RefCountable* makeObj();
void someFunction(const Function<void()>&&);
void otherFunction(NOESCAPE const Function<void()>&&);

template<typename CallbackType>
void callTrivially(CallbackType Func) {
  return Func();
}

void raw_ptr() {
  RefCountable* ref_countable = makeObj();

  auto foo1 = [ref_countable](){};
  // CHECK: warning: Captured raw-pointer 'ref_countable' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  // CHECK-NEXT:{{^   6 | }}  auto foo1 = [ref_countable](){};
  // CHECK-NEXT:{{^     | }}               ^
  someFunction(foo1);

  auto foo2 = [&ref_countable](){};
  // CHECK: warning: Captured raw-pointer 'ref_countable' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  someFunction(foo2);

  auto foo3 = [&](){ ref_countable = nullptr; };
  // CHECK: warning: Implicitly captured raw-pointer 'ref_countable' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  // CHECK-NEXT:{{^  12 | }}  auto foo3 = [&](){ ref_countable = nullptr; };
  // CHECK-NEXT:{{^     | }}                     ^
  someFunction(foo3);

  auto foo4 = [=](){ (void) ref_countable; };
  // CHECK: warning: Implicitly captured raw-pointer 'ref_countable' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  someFunction(foo4);

  // Confirm that the checker respects [[clang::suppress]].
  RefCountable* suppressed_ref_countable = nullptr;
  [[clang::suppress]] auto foo5 = [suppressed_ref_countable](){};
  // CHECK-NOT: warning: Captured raw-pointer 'suppressed_ref_countable' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]

  {
    RefPtr foo5 = makeObj();
    auto *foo6 = foo5.get();
    auto lambda = [&]() {
      foo6->method();
    };
    // CHECK: warning: Implicitly captured raw-pointer 'foo6' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
    lambda();
  }

  {
    RefPtr foo7 = makeObj();
    {
      auto *foo8 = foo7.get();
      auto lambda = [&]() {
        foo8->method();
      };
      // CHECK: warning: Implicitly captured raw-pointer 'foo8' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
      someFunction(lambda);      
    }
  }

  {
    static WTF::Function<void()> staticFunction;
    RefPtr foo9 = makeObj();
    {
      auto *foo10 = foo9.get();
      auto lambda = [&]() {
        foo10->method();
      };
      // CHECK: warning: Implicitly captured raw-pointer 'foo10' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
      staticFunction = lambda;
    }
  }

  {
    RefPtr foo11 = makeObj();
    {
      auto *foo12 = foo11.get();
      auto lambda = [&]() {
        foo12->method();
      };
      // CHECK: warning: Implicitly captured raw-pointer 'foo12' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
      lambda();
      someFunction(lambda);
    }
  }

  {
    RefPtr foo13 = makeObj();
    {
      auto *foo14 = foo13.get();
      auto lambda = [&]() {
        foo14->method();
      };
      // CHECK: warning: Implicitly captured raw-pointer 'foo14' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
      lambda();
      someFunction(lambda);
    }
  }
}

void references() {
  RefCountable automatic;
  RefCountable& ref_countable_ref = automatic;

  auto foo1 = [ref_countable_ref](){};
  // CHECK: warning: Captured reference 'ref_countable_ref' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  someFunction(foo1);

  auto foo2 = [&ref_countable_ref](){};
  // CHECK: warning: Captured reference 'ref_countable_ref' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  someFunction(foo2);

  auto foo3 = [&](){ (void) ref_countable_ref; };
  // CHECK: warning: Implicitly captured reference 'ref_countable_ref' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  someFunction(foo3);

  auto foo4 = [=](){ (void) ref_countable_ref; };
  // CHECK: warning: Implicitly captured reference 'ref_countable_ref' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]
  someFunction(foo4);
}

void quiet() {
// This code is not expected to trigger any warnings.
  {
    RefCountable automatic;
    RefCountable &ref_countable_ref = automatic;
  }

  auto foo3 = [&]() {};
  auto foo4 = [=]() {};
  RefCountable *ref_countable = nullptr;

  {
    auto *obj = makeObj();
    ([obj](int x) {
      obj->method();
    })(0);
    // CHECK-NOT: warning: Captured raw-pointer 'obj' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
  }

  {
    auto *obj2 = makeObj();
    callTrivially([&]() {
      obj2->trivial();
    });
    // CHECK-NOT: warning: Implicitly captured raw-pointer 'obj2' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
  }

  {
    RefPtr obj3 = makeObj();
    callTrivially([&]() {
      obj3->method();
    });
    // CHECK-NOT: warning: Implicitly captured raw-pointer 'obj3' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
  }

  {
    RefPtr obj4 = makeObj(); // Guardian variable
    {
      auto *ptr4 = obj4.get();
      auto lambda = [&]() {
        ptr4->method();
      };
      // CHECK-NOT: warning: Implicitly captured raw-pointer 'obj4' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
      lambda();
    }
  }

  {
    RefPtr obj5 = makeObj(); // Guardian variable
    {
      auto *ptr5 = obj5.get();
      auto lambda = [&]() {
        ptr5->method();
      };
      // CHECK-NOT: warning: Implicitly captured raw-pointer 'ptr5' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
      otherFunction(lambda); // noescape argument
    }
  }

  {
    RefPtr obj6 = makeObj();
    {
      auto *ptr6 = obj6.get();
      auto lambda = [&]() {
        ptr6->method();
      };
      (void)lambda;
      // CHECK-NOT: warning: Implicitly captured raw-pointer 'ptr6' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
    }
  }

  {
    {
      auto *ptr7 = makeObj();
      auto lambda = [rawPtr = ptr7, protectedPtr = RefPtr { ptr7 }]() {
        rawPtr->method();
      };
      // CHECK-NOT: warning: Implicitly captured raw-pointer 'rawPtr' to uncounted type is unsafe [webkit.UncountedLambdaCapturesChecker]    
      someFunction(lambda);
    }
  }

}
