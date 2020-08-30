(function (global, factory) {
	typeof exports === 'object' && typeof module !== 'undefined' ? factory(exports) :
	typeof define === 'function' && define.amd ? define(['exports'], factory) :
	(global = global || self, factory(global.UI = {}));
}(this, (function (exports) { 'use strict';

	function _extends() {
	  _extends = Object.assign || function (target) {
	    for (var i = 1; i < arguments.length; i++) {
	      var source = arguments[i];

	      for (var key in source) {
	        if (Object.prototype.hasOwnProperty.call(source, key)) {
	          target[key] = source[key];
	        }
	      }
	    }

	    return target;
	  };

	  return _extends.apply(this, arguments);
	}

	function createCommonjsModule(fn, module) {
		return module = { exports: {} }, fn(module, module.exports), module.exports;
	}

	var bind = createCommonjsModule(function (module) {
	/*!
	  Copyright (c) 2017 Jed Watson.
	  Licensed under the MIT License (MIT), see
	  http://jedwatson.github.io/classnames
	*/
	/* global define */

	(function () {

		var hasOwn = {}.hasOwnProperty;

		function classNames () {
			var classes = [];

			for (var i = 0; i < arguments.length; i++) {
				var arg = arguments[i];
				if (!arg) continue;

				var argType = typeof arg;

				if (argType === 'string' || argType === 'number') {
					classes.push(this && this[arg] || arg);
				} else if (Array.isArray(arg)) {
					classes.push(classNames.apply(this, arg));
				} else if (argType === 'object') {
					for (var key in arg) {
						if (hasOwn.call(arg, key) && arg[key]) {
							classes.push(this && this[key] || key);
						}
					}
				}
			}

			return classes.join(' ');
		}

		if ( module.exports) {
			classNames.default = classNames;
			module.exports = classNames;
		} else {
			window.classNames = classNames;
		}
	}());
	});

	/** @license React v16.13.1
	 * react-is.production.min.js
	 *
	 * Copyright (c) Facebook, Inc. and its affiliates.
	 *
	 * This source code is licensed under the MIT license found in the
	 * LICENSE file in the root directory of this source tree.
	 */
	var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
	Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
	function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
	var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
	var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
	var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

	var reactIs_production_min = {
		AsyncMode: AsyncMode,
		ConcurrentMode: ConcurrentMode,
		ContextConsumer: ContextConsumer,
		ContextProvider: ContextProvider,
		Element: Element,
		ForwardRef: ForwardRef,
		Fragment: Fragment,
		Lazy: Lazy,
		Memo: Memo,
		Portal: Portal,
		Profiler: Profiler,
		StrictMode: StrictMode,
		Suspense: Suspense,
		isAsyncMode: isAsyncMode,
		isConcurrentMode: isConcurrentMode,
		isContextConsumer: isContextConsumer,
		isContextProvider: isContextProvider,
		isElement: isElement,
		isForwardRef: isForwardRef,
		isFragment: isFragment,
		isLazy: isLazy,
		isMemo: isMemo,
		isPortal: isPortal,
		isProfiler: isProfiler,
		isStrictMode: isStrictMode,
		isSuspense: isSuspense,
		isValidElementType: isValidElementType,
		typeOf: typeOf
	};

	var reactIs_development = createCommonjsModule(function (module, exports) {



	if (process.env.NODE_ENV !== "production") {
	  (function() {

	// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
	// nor polyfill, then a plain number is used for performance.
	var hasSymbol = typeof Symbol === 'function' && Symbol.for;
	var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
	var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
	var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
	var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
	var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
	var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
	var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
	// (unstable) APIs that have been removed. Can we remove the symbols?

	var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
	var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
	var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
	var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
	var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
	var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
	var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
	var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
	var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
	var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
	var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

	function isValidElementType(type) {
	  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
	  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
	}

	function typeOf(object) {
	  if (typeof object === 'object' && object !== null) {
	    var $$typeof = object.$$typeof;

	    switch ($$typeof) {
	      case REACT_ELEMENT_TYPE:
	        var type = object.type;

	        switch (type) {
	          case REACT_ASYNC_MODE_TYPE:
	          case REACT_CONCURRENT_MODE_TYPE:
	          case REACT_FRAGMENT_TYPE:
	          case REACT_PROFILER_TYPE:
	          case REACT_STRICT_MODE_TYPE:
	          case REACT_SUSPENSE_TYPE:
	            return type;

	          default:
	            var $$typeofType = type && type.$$typeof;

	            switch ($$typeofType) {
	              case REACT_CONTEXT_TYPE:
	              case REACT_FORWARD_REF_TYPE:
	              case REACT_LAZY_TYPE:
	              case REACT_MEMO_TYPE:
	              case REACT_PROVIDER_TYPE:
	                return $$typeofType;

	              default:
	                return $$typeof;
	            }

	        }

	      case REACT_PORTAL_TYPE:
	        return $$typeof;
	    }
	  }

	  return undefined;
	} // AsyncMode is deprecated along with isAsyncMode

	var AsyncMode = REACT_ASYNC_MODE_TYPE;
	var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
	var ContextConsumer = REACT_CONTEXT_TYPE;
	var ContextProvider = REACT_PROVIDER_TYPE;
	var Element = REACT_ELEMENT_TYPE;
	var ForwardRef = REACT_FORWARD_REF_TYPE;
	var Fragment = REACT_FRAGMENT_TYPE;
	var Lazy = REACT_LAZY_TYPE;
	var Memo = REACT_MEMO_TYPE;
	var Portal = REACT_PORTAL_TYPE;
	var Profiler = REACT_PROFILER_TYPE;
	var StrictMode = REACT_STRICT_MODE_TYPE;
	var Suspense = REACT_SUSPENSE_TYPE;
	var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

	function isAsyncMode(object) {
	  {
	    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
	      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

	      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
	    }
	  }

	  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
	}
	function isConcurrentMode(object) {
	  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
	}
	function isContextConsumer(object) {
	  return typeOf(object) === REACT_CONTEXT_TYPE;
	}
	function isContextProvider(object) {
	  return typeOf(object) === REACT_PROVIDER_TYPE;
	}
	function isElement(object) {
	  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
	}
	function isForwardRef(object) {
	  return typeOf(object) === REACT_FORWARD_REF_TYPE;
	}
	function isFragment(object) {
	  return typeOf(object) === REACT_FRAGMENT_TYPE;
	}
	function isLazy(object) {
	  return typeOf(object) === REACT_LAZY_TYPE;
	}
	function isMemo(object) {
	  return typeOf(object) === REACT_MEMO_TYPE;
	}
	function isPortal(object) {
	  return typeOf(object) === REACT_PORTAL_TYPE;
	}
	function isProfiler(object) {
	  return typeOf(object) === REACT_PROFILER_TYPE;
	}
	function isStrictMode(object) {
	  return typeOf(object) === REACT_STRICT_MODE_TYPE;
	}
	function isSuspense(object) {
	  return typeOf(object) === REACT_SUSPENSE_TYPE;
	}

	exports.AsyncMode = AsyncMode;
	exports.ConcurrentMode = ConcurrentMode;
	exports.ContextConsumer = ContextConsumer;
	exports.ContextProvider = ContextProvider;
	exports.Element = Element;
	exports.ForwardRef = ForwardRef;
	exports.Fragment = Fragment;
	exports.Lazy = Lazy;
	exports.Memo = Memo;
	exports.Portal = Portal;
	exports.Profiler = Profiler;
	exports.StrictMode = StrictMode;
	exports.Suspense = Suspense;
	exports.isAsyncMode = isAsyncMode;
	exports.isConcurrentMode = isConcurrentMode;
	exports.isContextConsumer = isContextConsumer;
	exports.isContextProvider = isContextProvider;
	exports.isElement = isElement;
	exports.isForwardRef = isForwardRef;
	exports.isFragment = isFragment;
	exports.isLazy = isLazy;
	exports.isMemo = isMemo;
	exports.isPortal = isPortal;
	exports.isProfiler = isProfiler;
	exports.isStrictMode = isStrictMode;
	exports.isSuspense = isSuspense;
	exports.isValidElementType = isValidElementType;
	exports.typeOf = typeOf;
	  })();
	}
	});
	var reactIs_development_1 = reactIs_development.AsyncMode;
	var reactIs_development_2 = reactIs_development.ConcurrentMode;
	var reactIs_development_3 = reactIs_development.ContextConsumer;
	var reactIs_development_4 = reactIs_development.ContextProvider;
	var reactIs_development_5 = reactIs_development.Element;
	var reactIs_development_6 = reactIs_development.ForwardRef;
	var reactIs_development_7 = reactIs_development.Fragment;
	var reactIs_development_8 = reactIs_development.Lazy;
	var reactIs_development_9 = reactIs_development.Memo;
	var reactIs_development_10 = reactIs_development.Portal;
	var reactIs_development_11 = reactIs_development.Profiler;
	var reactIs_development_12 = reactIs_development.StrictMode;
	var reactIs_development_13 = reactIs_development.Suspense;
	var reactIs_development_14 = reactIs_development.isAsyncMode;
	var reactIs_development_15 = reactIs_development.isConcurrentMode;
	var reactIs_development_16 = reactIs_development.isContextConsumer;
	var reactIs_development_17 = reactIs_development.isContextProvider;
	var reactIs_development_18 = reactIs_development.isElement;
	var reactIs_development_19 = reactIs_development.isForwardRef;
	var reactIs_development_20 = reactIs_development.isFragment;
	var reactIs_development_21 = reactIs_development.isLazy;
	var reactIs_development_22 = reactIs_development.isMemo;
	var reactIs_development_23 = reactIs_development.isPortal;
	var reactIs_development_24 = reactIs_development.isProfiler;
	var reactIs_development_25 = reactIs_development.isStrictMode;
	var reactIs_development_26 = reactIs_development.isSuspense;
	var reactIs_development_27 = reactIs_development.isValidElementType;
	var reactIs_development_28 = reactIs_development.typeOf;

	var reactIs = createCommonjsModule(function (module) {

	if (process.env.NODE_ENV === 'production') {
	  module.exports = reactIs_production_min;
	} else {
	  module.exports = reactIs_development;
	}
	});

	/*
	object-assign
	(c) Sindre Sorhus
	@license MIT
	*/
	/* eslint-disable no-unused-vars */
	var getOwnPropertySymbols = Object.getOwnPropertySymbols;
	var hasOwnProperty = Object.prototype.hasOwnProperty;
	var propIsEnumerable = Object.prototype.propertyIsEnumerable;

	function toObject(val) {
		if (val === null || val === undefined) {
			throw new TypeError('Object.assign cannot be called with null or undefined');
		}

		return Object(val);
	}

	function shouldUseNative() {
		try {
			if (!Object.assign) {
				return false;
			}

			// Detect buggy property enumeration order in older V8 versions.

			// https://bugs.chromium.org/p/v8/issues/detail?id=4118
			var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
			test1[5] = 'de';
			if (Object.getOwnPropertyNames(test1)[0] === '5') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test2 = {};
			for (var i = 0; i < 10; i++) {
				test2['_' + String.fromCharCode(i)] = i;
			}
			var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
				return test2[n];
			});
			if (order2.join('') !== '0123456789') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test3 = {};
			'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
				test3[letter] = letter;
			});
			if (Object.keys(Object.assign({}, test3)).join('') !==
					'abcdefghijklmnopqrst') {
				return false;
			}

			return true;
		} catch (err) {
			// We don't expect any of the above to throw, but better to be safe.
			return false;
		}
	}

	var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
		var from;
		var to = toObject(target);
		var symbols;

		for (var s = 1; s < arguments.length; s++) {
			from = Object(arguments[s]);

			for (var key in from) {
				if (hasOwnProperty.call(from, key)) {
					to[key] = from[key];
				}
			}

			if (getOwnPropertySymbols) {
				symbols = getOwnPropertySymbols(from);
				for (var i = 0; i < symbols.length; i++) {
					if (propIsEnumerable.call(from, symbols[i])) {
						to[symbols[i]] = from[symbols[i]];
					}
				}
			}
		}

		return to;
	};

	/**
	 * Copyright (c) 2013-present, Facebook, Inc.
	 *
	 * This source code is licensed under the MIT license found in the
	 * LICENSE file in the root directory of this source tree.
	 */

	var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

	var ReactPropTypesSecret_1 = ReactPropTypesSecret;

	var printWarning = function() {};

	if (process.env.NODE_ENV !== 'production') {
	  var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
	  var loggedTypeFailures = {};
	  var has = Function.call.bind(Object.prototype.hasOwnProperty);

	  printWarning = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {}
	  };
	}

	/**
	 * Assert that the values match with the type specs.
	 * Error messages are memorized and will only be shown once.
	 *
	 * @param {object} typeSpecs Map of name to a ReactPropType
	 * @param {object} values Runtime values that need to be type-checked
	 * @param {string} location e.g. "prop", "context", "child context"
	 * @param {string} componentName Name of the component for error messages.
	 * @param {?Function} getStack Returns the component stack.
	 * @private
	 */
	function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
	  if (process.env.NODE_ENV !== 'production') {
	    for (var typeSpecName in typeSpecs) {
	      if (has(typeSpecs, typeSpecName)) {
	        var error;
	        // Prop type validation may throw. In case they do, we don't want to
	        // fail the render phase where it didn't fail before. So we log it.
	        // After these have been cleaned up, we'll let them throw.
	        try {
	          // This is intentionally an invariant that gets caught. It's the same
	          // behavior as without this statement except with a better message.
	          if (typeof typeSpecs[typeSpecName] !== 'function') {
	            var err = Error(
	              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
	              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
	            );
	            err.name = 'Invariant Violation';
	            throw err;
	          }
	          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
	        } catch (ex) {
	          error = ex;
	        }
	        if (error && !(error instanceof Error)) {
	          printWarning(
	            (componentName || 'React class') + ': type specification of ' +
	            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
	            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
	            'You may have forgotten to pass an argument to the type checker ' +
	            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
	            'shape all require an argument).'
	          );
	        }
	        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
	          // Only monitor this failure once because there tends to be a lot of the
	          // same error.
	          loggedTypeFailures[error.message] = true;

	          var stack = getStack ? getStack() : '';

	          printWarning(
	            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
	          );
	        }
	      }
	    }
	  }
	}

	/**
	 * Resets warning cache when testing.
	 *
	 * @private
	 */
	checkPropTypes.resetWarningCache = function() {
	  if (process.env.NODE_ENV !== 'production') {
	    loggedTypeFailures = {};
	  }
	};

	var checkPropTypes_1 = checkPropTypes;

	var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
	var printWarning$1 = function() {};

	if (process.env.NODE_ENV !== 'production') {
	  printWarning$1 = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {}
	  };
	}

	function emptyFunctionThatReturnsNull() {
	  return null;
	}

	var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
	  /* global Symbol */
	  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
	  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

	  /**
	   * Returns the iterator method function contained on the iterable object.
	   *
	   * Be sure to invoke the function with the iterable as context:
	   *
	   *     var iteratorFn = getIteratorFn(myIterable);
	   *     if (iteratorFn) {
	   *       var iterator = iteratorFn.call(myIterable);
	   *       ...
	   *     }
	   *
	   * @param {?object} maybeIterable
	   * @return {?function}
	   */
	  function getIteratorFn(maybeIterable) {
	    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
	    if (typeof iteratorFn === 'function') {
	      return iteratorFn;
	    }
	  }

	  /**
	   * Collection of methods that allow declaration and validation of props that are
	   * supplied to React components. Example usage:
	   *
	   *   var Props = require('ReactPropTypes');
	   *   var MyArticle = React.createClass({
	   *     propTypes: {
	   *       // An optional string prop named "description".
	   *       description: Props.string,
	   *
	   *       // A required enum prop named "category".
	   *       category: Props.oneOf(['News','Photos']).isRequired,
	   *
	   *       // A prop named "dialog" that requires an instance of Dialog.
	   *       dialog: Props.instanceOf(Dialog).isRequired
	   *     },
	   *     render: function() { ... }
	   *   });
	   *
	   * A more formal specification of how these methods are used:
	   *
	   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
	   *   decl := ReactPropTypes.{type}(.isRequired)?
	   *
	   * Each and every declaration produces a function with the same signature. This
	   * allows the creation of custom validation functions. For example:
	   *
	   *  var MyLink = React.createClass({
	   *    propTypes: {
	   *      // An optional string or URI prop named "href".
	   *      href: function(props, propName, componentName) {
	   *        var propValue = props[propName];
	   *        if (propValue != null && typeof propValue !== 'string' &&
	   *            !(propValue instanceof URI)) {
	   *          return new Error(
	   *            'Expected a string or an URI for ' + propName + ' in ' +
	   *            componentName
	   *          );
	   *        }
	   *      }
	   *    },
	   *    render: function() {...}
	   *  });
	   *
	   * @internal
	   */

	  var ANONYMOUS = '<<anonymous>>';

	  // Important!
	  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
	  var ReactPropTypes = {
	    array: createPrimitiveTypeChecker('array'),
	    bool: createPrimitiveTypeChecker('boolean'),
	    func: createPrimitiveTypeChecker('function'),
	    number: createPrimitiveTypeChecker('number'),
	    object: createPrimitiveTypeChecker('object'),
	    string: createPrimitiveTypeChecker('string'),
	    symbol: createPrimitiveTypeChecker('symbol'),

	    any: createAnyTypeChecker(),
	    arrayOf: createArrayOfTypeChecker,
	    element: createElementTypeChecker(),
	    elementType: createElementTypeTypeChecker(),
	    instanceOf: createInstanceTypeChecker,
	    node: createNodeChecker(),
	    objectOf: createObjectOfTypeChecker,
	    oneOf: createEnumTypeChecker,
	    oneOfType: createUnionTypeChecker,
	    shape: createShapeTypeChecker,
	    exact: createStrictShapeTypeChecker,
	  };

	  /**
	   * inlined Object.is polyfill to avoid requiring consumers ship their own
	   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
	   */
	  /*eslint-disable no-self-compare*/
	  function is(x, y) {
	    // SameValue algorithm
	    if (x === y) {
	      // Steps 1-5, 7-10
	      // Steps 6.b-6.e: +0 != -0
	      return x !== 0 || 1 / x === 1 / y;
	    } else {
	      // Step 6.a: NaN == NaN
	      return x !== x && y !== y;
	    }
	  }
	  /*eslint-enable no-self-compare*/

	  /**
	   * We use an Error-like object for backward compatibility as people may call
	   * PropTypes directly and inspect their output. However, we don't use real
	   * Errors anymore. We don't inspect their stack anyway, and creating them
	   * is prohibitively expensive if they are created too often, such as what
	   * happens in oneOfType() for any type before the one that matched.
	   */
	  function PropTypeError(message) {
	    this.message = message;
	    this.stack = '';
	  }
	  // Make `instanceof Error` still work for returned errors.
	  PropTypeError.prototype = Error.prototype;

	  function createChainableTypeChecker(validate) {
	    if (process.env.NODE_ENV !== 'production') {
	      var manualPropTypeCallCache = {};
	      var manualPropTypeWarningCount = 0;
	    }
	    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
	      componentName = componentName || ANONYMOUS;
	      propFullName = propFullName || propName;

	      if (secret !== ReactPropTypesSecret_1) {
	        if (throwOnDirectAccess) {
	          // New behavior only for users of `prop-types` package
	          var err = new Error(
	            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
	            'Use `PropTypes.checkPropTypes()` to call them. ' +
	            'Read more at http://fb.me/use-check-prop-types'
	          );
	          err.name = 'Invariant Violation';
	          throw err;
	        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
	          // Old behavior for people using React.PropTypes
	          var cacheKey = componentName + ':' + propName;
	          if (
	            !manualPropTypeCallCache[cacheKey] &&
	            // Avoid spamming the console because they are often not actionable except for lib authors
	            manualPropTypeWarningCount < 3
	          ) {
	            printWarning$1(
	              'You are manually calling a React.PropTypes validation ' +
	              'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
	              'and will throw in the standalone `prop-types` package. ' +
	              'You may be seeing this warning due to a third-party PropTypes ' +
	              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
	            );
	            manualPropTypeCallCache[cacheKey] = true;
	            manualPropTypeWarningCount++;
	          }
	        }
	      }
	      if (props[propName] == null) {
	        if (isRequired) {
	          if (props[propName] === null) {
	            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
	          }
	          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
	        }
	        return null;
	      } else {
	        return validate(props, propName, componentName, location, propFullName);
	      }
	    }

	    var chainedCheckType = checkType.bind(null, false);
	    chainedCheckType.isRequired = checkType.bind(null, true);

	    return chainedCheckType;
	  }

	  function createPrimitiveTypeChecker(expectedType) {
	    function validate(props, propName, componentName, location, propFullName, secret) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== expectedType) {
	        // `propValue` being instance of, say, date/regexp, pass the 'object'
	        // check, but we can offer a more precise error message here rather than
	        // 'of type `object`'.
	        var preciseType = getPreciseType(propValue);

	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createAnyTypeChecker() {
	    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
	  }

	  function createArrayOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
	      }
	      var propValue = props[propName];
	      if (!Array.isArray(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
	      }
	      for (var i = 0; i < propValue.length; i++) {
	        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
	        if (error instanceof Error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!isValidElement(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!reactIs.isValidElementType(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createInstanceTypeChecker(expectedClass) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!(props[propName] instanceof expectedClass)) {
	        var expectedClassName = expectedClass.name || ANONYMOUS;
	        var actualClassName = getClassName(props[propName]);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createEnumTypeChecker(expectedValues) {
	    if (!Array.isArray(expectedValues)) {
	      if (process.env.NODE_ENV !== 'production') {
	        if (arguments.length > 1) {
	          printWarning$1(
	            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
	            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
	          );
	        } else {
	          printWarning$1('Invalid argument supplied to oneOf, expected an array.');
	        }
	      }
	      return emptyFunctionThatReturnsNull;
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      for (var i = 0; i < expectedValues.length; i++) {
	        if (is(propValue, expectedValues[i])) {
	          return null;
	        }
	      }

	      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
	        var type = getPreciseType(value);
	        if (type === 'symbol') {
	          return String(value);
	        }
	        return value;
	      });
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createObjectOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
	      }
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
	      }
	      for (var key in propValue) {
	        if (has$1(propValue, key)) {
	          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
	          if (error instanceof Error) {
	            return error;
	          }
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createUnionTypeChecker(arrayOfTypeCheckers) {
	    if (!Array.isArray(arrayOfTypeCheckers)) {
	      process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
	      return emptyFunctionThatReturnsNull;
	    }

	    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	      var checker = arrayOfTypeCheckers[i];
	      if (typeof checker !== 'function') {
	        printWarning$1(
	          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
	          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
	        );
	        return emptyFunctionThatReturnsNull;
	      }
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	        var checker = arrayOfTypeCheckers[i];
	        if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
	          return null;
	        }
	      }

	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createNodeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!isNode(props[propName])) {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      for (var key in shapeTypes) {
	        var checker = shapeTypes[key];
	        if (!checker) {
	          continue;
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createStrictShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      // We need to check all keys in case some are required but missing from
	      // props.
	      var allKeys = objectAssign({}, props[propName], shapeTypes);
	      for (var key in allKeys) {
	        var checker = shapeTypes[key];
	        if (!checker) {
	          return new PropTypeError(
	            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
	            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
	            '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
	          );
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }

	    return createChainableTypeChecker(validate);
	  }

	  function isNode(propValue) {
	    switch (typeof propValue) {
	      case 'number':
	      case 'string':
	      case 'undefined':
	        return true;
	      case 'boolean':
	        return !propValue;
	      case 'object':
	        if (Array.isArray(propValue)) {
	          return propValue.every(isNode);
	        }
	        if (propValue === null || isValidElement(propValue)) {
	          return true;
	        }

	        var iteratorFn = getIteratorFn(propValue);
	        if (iteratorFn) {
	          var iterator = iteratorFn.call(propValue);
	          var step;
	          if (iteratorFn !== propValue.entries) {
	            while (!(step = iterator.next()).done) {
	              if (!isNode(step.value)) {
	                return false;
	              }
	            }
	          } else {
	            // Iterator will provide entry [k,v] tuples rather than values.
	            while (!(step = iterator.next()).done) {
	              var entry = step.value;
	              if (entry) {
	                if (!isNode(entry[1])) {
	                  return false;
	                }
	              }
	            }
	          }
	        } else {
	          return false;
	        }

	        return true;
	      default:
	        return false;
	    }
	  }

	  function isSymbol(propType, propValue) {
	    // Native Symbol.
	    if (propType === 'symbol') {
	      return true;
	    }

	    // falsy value can't be a Symbol
	    if (!propValue) {
	      return false;
	    }

	    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
	    if (propValue['@@toStringTag'] === 'Symbol') {
	      return true;
	    }

	    // Fallback for non-spec compliant Symbols which are polyfilled.
	    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
	      return true;
	    }

	    return false;
	  }

	  // Equivalent of `typeof` but with special handling for array and regexp.
	  function getPropType(propValue) {
	    var propType = typeof propValue;
	    if (Array.isArray(propValue)) {
	      return 'array';
	    }
	    if (propValue instanceof RegExp) {
	      // Old webkits (at least until Android 4.0) return 'function' rather than
	      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
	      // passes PropTypes.object.
	      return 'object';
	    }
	    if (isSymbol(propType, propValue)) {
	      return 'symbol';
	    }
	    return propType;
	  }

	  // This handles more types than `getPropType`. Only used for error messages.
	  // See `createPrimitiveTypeChecker`.
	  function getPreciseType(propValue) {
	    if (typeof propValue === 'undefined' || propValue === null) {
	      return '' + propValue;
	    }
	    var propType = getPropType(propValue);
	    if (propType === 'object') {
	      if (propValue instanceof Date) {
	        return 'date';
	      } else if (propValue instanceof RegExp) {
	        return 'regexp';
	      }
	    }
	    return propType;
	  }

	  // Returns a string that is postfixed to a warning about an invalid type.
	  // For example, "undefined" or "of type array"
	  function getPostfixForTypeWarning(value) {
	    var type = getPreciseType(value);
	    switch (type) {
	      case 'array':
	      case 'object':
	        return 'an ' + type;
	      case 'boolean':
	      case 'date':
	      case 'regexp':
	        return 'a ' + type;
	      default:
	        return type;
	    }
	  }

	  // Returns class name of the object, if any.
	  function getClassName(propValue) {
	    if (!propValue.constructor || !propValue.constructor.name) {
	      return ANONYMOUS;
	    }
	    return propValue.constructor.name;
	  }

	  ReactPropTypes.checkPropTypes = checkPropTypes_1;
	  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
	  ReactPropTypes.PropTypes = ReactPropTypes;

	  return ReactPropTypes;
	};

	function emptyFunction() {}
	function emptyFunctionWithReset() {}
	emptyFunctionWithReset.resetWarningCache = emptyFunction;

	var factoryWithThrowingShims = function() {
	  function shim(props, propName, componentName, location, propFullName, secret) {
	    if (secret === ReactPropTypesSecret_1) {
	      // It is still safe when called from React.
	      return;
	    }
	    var err = new Error(
	      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
	      'Use PropTypes.checkPropTypes() to call them. ' +
	      'Read more at http://fb.me/use-check-prop-types'
	    );
	    err.name = 'Invariant Violation';
	    throw err;
	  }  shim.isRequired = shim;
	  function getShim() {
	    return shim;
	  }  // Important!
	  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
	  var ReactPropTypes = {
	    array: shim,
	    bool: shim,
	    func: shim,
	    number: shim,
	    object: shim,
	    string: shim,
	    symbol: shim,

	    any: shim,
	    arrayOf: getShim,
	    element: shim,
	    elementType: shim,
	    instanceOf: getShim,
	    node: shim,
	    objectOf: getShim,
	    oneOf: getShim,
	    oneOfType: getShim,
	    shape: getShim,
	    exact: getShim,

	    checkPropTypes: emptyFunctionWithReset,
	    resetWarningCache: emptyFunction
	  };

	  ReactPropTypes.PropTypes = ReactPropTypes;

	  return ReactPropTypes;
	};

	var propTypes = createCommonjsModule(function (module) {
	/**
	 * Copyright (c) 2013-present, Facebook, Inc.
	 *
	 * This source code is licensed under the MIT license found in the
	 * LICENSE file in the root directory of this source tree.
	 */

	if (process.env.NODE_ENV !== 'production') {
	  var ReactIs = reactIs;

	  // By explicitly using `prop-types` you are opting into new development behavior.
	  // http://fb.me/prop-types-in-prod
	  var throwOnDirectAccess = true;
	  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
	} else {
	  // By explicitly using `prop-types` you are opting into new production behavior.
	  // http://fb.me/prop-types-in-prod
	  module.exports = factoryWithThrowingShims();
	}
	});

	/**
	 * 画布
	 * @author tengge / https://github.com/tengge1
	 */

	class Canvas extends React.Component {
	  constructor(props) {
	    super(props);
	    this.dom = React.createRef();
	  }

	  render() {
	    const {
	      className,
	      style,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("canvas", _extends({
	      className: bind('Canvas', className),
	      style: style,
	      ref: this.dom
	    }, others));
	  }

	}

	Canvas.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object
	};
	Canvas.defaultProps = {
	  className: null,
	  style: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 折叠面板
	 * @author tengge / https://github.com/tengge1
	 */
	class Accordion extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 很多按钮
	 * @author tengge / https://github.com/tengge1
	 */
	class Buttons extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 列
	 * @author tengge / https://github.com/tengge1
	 */
	class Column extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 内容
	 * @author tengge / https://github.com/tengge1
	 */
	class Content extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 一项
	 * @author tengge / https://github.com/tengge1
	 */
	class Item extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 菜单
	 * @author tengge / https://github.com/tengge1
	 */
	class Menu extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 行
	 * @author tengge / https://github.com/tengge1
	 */
	class Row extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */

	/**
	 * 很多行
	 * @author tengge / https://github.com/tengge1
	 */
	class Rows extends React.Component {
	  render() {
	    return null;
	  }

	}

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 按钮
	 * @author tengge / https://github.com/tengge1
	 */

	class Button extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      color,
	      disabled,
	      show
	    } = this.props;
	    return /*#__PURE__*/React.createElement("button", {
	      className: bind('Button', color, disabled && 'disabled', !show && 'hidden', className),
	      style: style,
	      disabled: disabled,
	      onClick: this.handleClick
	    }, children);
	  }

	  handleClick(event) {
	    const {
	      name,
	      disabled,
	      onClick
	    } = this.props;
	    !disabled && onClick && onClick(name, event);
	  }

	}

	Button.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  children: propTypes.node,
	  color: propTypes.oneOf(['primary', 'success', 'warn', 'danger']),
	  disabled: propTypes.bool,
	  show: propTypes.bool,
	  onClick: propTypes.func
	};
	Button.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  children: null,
	  color: null,
	  disabled: false,
	  show: true,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 复选框
	 * @author tengge / https://github.com/tengge1
	 */

	class CheckBox extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      checked,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement("input", {
	      type: 'checkbox',
	      className: bind('CheckBox', checked && 'checked', disabled && 'disabled', className),
	      style: style,
	      checked: checked,
	      disabled: disabled,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(event) {
	    const {
	      name,
	      onChange
	    } = this.props;
	    onChange && onChange(event.target.checked, name, event);
	  }

	}

	CheckBox.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  checked: propTypes.bool,
	  disabled: propTypes.bool,
	  onChange: propTypes.func
	};
	CheckBox.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  checked: false,
	  disabled: false,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 表单
	 * @author tengge / https://github.com/tengge1
	 */

	class Form extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleSubmit = this.handleSubmit.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      direction
	    } = this.props;
	    return /*#__PURE__*/React.createElement("form", {
	      className: bind('Form', direction, className),
	      style: style,
	      onSubmit: this.handleSubmit
	    }, children);
	  }

	  handleSubmit() {
	    const {
	      onSubmit
	    } = this.props;
	    event.preventDefault();
	    onSubmit && onSubmit();
	  }

	}

	Form.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  direction: propTypes.oneOf(['horizontal', 'vertical']),
	  onSubmit: propTypes.func
	};
	Form.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  direction: 'horizontal',
	  onSubmit: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 表单项
	 * @author tengge / https://github.com/tengge1
	 */

	class FormControl extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      hidden
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('FormControl', className, hidden && 'hidden'),
	      style: style
	    }, children);
	  }

	}

	FormControl.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  hidden: propTypes.bool
	};
	FormControl.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  hidden: false
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图标按钮
	 * @author tengge / https://github.com/tengge1
	 */

	class IconButton extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      icon,
	      title,
	      show,
	      selected,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement("button", {
	      className: bind('IconButton', selected && 'selected', !show && 'hidden', disabled && 'disabled', className),
	      style: style,
	      title: title,
	      onClick: this.handleClick
	    }, /*#__PURE__*/React.createElement("i", {
	      className: bind('iconfont', icon && 'icon-' + icon)
	    }));
	  }

	  handleClick(event) {
	    const {
	      name,
	      disabled,
	      onClick
	    } = this.props;
	    !disabled && onClick && onClick(name, event);
	  }

	}

	IconButton.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  icon: propTypes.string,
	  name: propTypes.string,
	  title: propTypes.string,
	  show: propTypes.bool,
	  selected: propTypes.bool,
	  disabled: propTypes.bool,
	  onClick: propTypes.func
	};
	IconButton.defaultProps = {
	  className: null,
	  style: null,
	  icon: null,
	  name: null,
	  title: null,
	  show: true,
	  selected: false,
	  disabled: false,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 带下拉菜单的图标按钮
	 * @author tengge / https://github.com/tengge1
	 */

	class IconMenuButton extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      icon,
	      title,
	      show,
	      selected
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('IconMenuButton', selected && 'selected', !show && 'hidden', className),
	      style: style
	    }, /*#__PURE__*/React.createElement("button", {
	      className: 'button',
	      title: title,
	      onClick: this.handleClick
	    }, /*#__PURE__*/React.createElement("i", {
	      className: bind('iconfont', icon && 'icon-' + icon)
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'menu'
	    }, children));
	  }

	  handleClick(event) {
	    const {
	      name,
	      onClick
	    } = this.props;
	    onClick && onClick(name, event);
	  }

	}

	IconMenuButton.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  icon: propTypes.string,
	  name: propTypes.string,
	  title: propTypes.string,
	  show: propTypes.bool,
	  selected: propTypes.bool,
	  onClick: propTypes.func
	};
	IconMenuButton.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  icon: null,
	  name: null,
	  title: null,
	  show: true,
	  selected: false,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图片按钮
	 * @author tengge / https://github.com/tengge1
	 */

	class ImageButton extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      src,
	      title,
	      selected
	    } = this.props;
	    return /*#__PURE__*/React.createElement("button", {
	      className: bind('ImageButton', selected && 'selected', className),
	      style: style,
	      title: title,
	      onClick: this.handleClick
	    }, /*#__PURE__*/React.createElement("img", {
	      src: src
	    }));
	  }

	  handleClick(event) {
	    const {
	      name,
	      onClick
	    } = this.props;
	    onClick && onClick(name, event);
	  }

	}

	ImageButton.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  src: propTypes.string,
	  name: propTypes.string,
	  title: propTypes.string,
	  selected: propTypes.bool,
	  onClick: propTypes.func
	};
	ImageButton.defaultProps = {
	  className: null,
	  style: null,
	  src: null,
	  name: null,
	  title: null,
	  selected: false,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 输入框
	 * @author tengge / https://github.com/tengge1
	 */

	class Input extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleFocus = this.handleFocus.bind(this);
	    this.handleChange = this.handleChange.bind(this);
	    this.handleInput = this.handleInput.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      type,
	      value,
	      min,
	      max,
	      step,
	      show,
	      disabled,
	      accept
	    } = this.props;
	    let val = value === undefined || value === null ? '' : value;
	    return /*#__PURE__*/React.createElement("input", {
	      className: bind('Input', !show && 'hidden', className),
	      style: style,
	      type: type,
	      value: val,
	      min: min,
	      max: max,
	      step: step,
	      disabled: disabled,
	      accept: accept,
	      autoComplete: 'off',
	      onFocus: this.handleFocus,
	      onChange: this.handleChange,
	      onInput: this.handleInput
	    });
	  }

	  handleFocus(event) {
	    const {
	      onFocus
	    } = this.props;
	    onFocus && onFocus(event);
	  }

	  handleChange(event) {
	    const {
	      name,
	      type,
	      onChange
	    } = this.props;
	    const value = event.target.value;

	    if (type === 'number') {
	      if (value.trim() !== '') {
	        const precision = this.props.precision;

	        if (precision === 0) {
	          onChange && onChange(parseInt(value), name, event);
	        } else {
	          onChange && onChange(parseInt(parseFloat(value) * 10 ** precision) / 10 ** precision, name, event);
	        }
	      } else {
	        onChange && onChange(null, name, event);
	      }
	    } else {
	      onChange && onChange(value, name, event);
	    }
	  }

	  handleInput(event) {
	    const {
	      name,
	      type,
	      onInput
	    } = this.props;
	    const value = event.target.value;

	    if (type === 'number') {
	      if (value.trim() !== '') {
	        onInput && onInput(parseFloat(value), name, event);
	      } else {
	        onInput && onInput(null, name, event);
	      }
	    } else {
	      onInput && onInput(value, name, event);
	    }
	  }

	}

	Input.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  type: propTypes.oneOf(['text', 'number', 'color', 'password', 'file']),
	  value: propTypes.oneOfType([propTypes.string, propTypes.number]),
	  min: propTypes.number,
	  max: propTypes.number,
	  step: propTypes.number,
	  precision: propTypes.number,
	  disabled: propTypes.bool,
	  accept: propTypes.string,
	  show: propTypes.bool,
	  onFocus: propTypes.func,
	  onChange: propTypes.func,
	  onInput: propTypes.func
	};
	Input.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  type: 'text',
	  value: '',
	  min: null,
	  max: null,
	  step: null,
	  precision: 3,
	  disabled: false,
	  accept: null,
	  show: true,
	  onFocus: null,
	  onChange: null,
	  onInput: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 标签
	 * @author tengge / https://github.com/tengge1
	 */

	class Label extends React.Component {
	  constructor(props) {
	    super(props);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      id
	    } = this.props;
	    return /*#__PURE__*/React.createElement("label", {
	      className: bind('Label', className),
	      style: style,
	      id: id
	    }, children);
	  }

	}

	Label.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  id: propTypes.string
	};
	Label.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  id: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 链接按钮
	 * @author tengge / https://github.com/tengge1
	 */

	class LinkButton extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement("a", {
	      className: bind('LinkButton', disabled && 'disabled', className),
	      style: style,
	      href: 'javascript:;',
	      disabled: disabled,
	      onClick: this.handleClick
	    }, children);
	  }

	  handleClick(event) {
	    const {
	      disabled,
	      onClick
	    } = this.props;
	    !disabled && onClick && onClick(this.props.name, event);
	  }

	}

	LinkButton.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  children: propTypes.node,
	  disabled: propTypes.bool,
	  onClick: propTypes.func
	};
	LinkButton.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  children: null,
	  disabled: false,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 单选框
	 * @author tengge / https://github.com/tengge1
	 */

	class Radio extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      checked,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement("input", {
	      type: 'radio',
	      className: bind('Radio', checked && 'checked', disabled && 'disabled', className),
	      style: style,
	      checked: checked,
	      disabled: disabled,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(event) {
	    const {
	      name,
	      onChange
	    } = this.props;
	    onChange && onChange(event.target.checked, name, event);
	  }

	}

	Radio.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  checked: propTypes.bool,
	  disabled: propTypes.bool,
	  onChange: propTypes.func
	};
	Radio.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  checked: false,
	  disabled: false,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 搜索框
	 * @author tengge / https://github.com/tengge1
	 */

	class SearchField extends React.Component {
	  constructor(props) {
	    super(props);
	    this.state = {
	      value: props.value,
	      categories: [],
	      filterShow: false
	    };
	    this.handleAdd = this.handleAdd.bind(this);
	    this.handleChange = this.handleChange.bind(this);
	    this.handleInput = this.handleInput.bind(this);
	    this.handleReset = this.handleReset.bind(this);
	    this.handleShowFilter = this.handleShowFilter.bind(this);
	    this.handleHideFilter = this.handleHideFilter.bind(this);
	    this.handleCheckBoxChange = this.handleCheckBoxChange.bind(this);
	    this.stopPropagation = this.stopPropagation.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      data,
	      placeholder,
	      showAddButton,
	      showFilterButton
	    } = this.props;
	    const {
	      value,
	      categories,
	      filterShow
	    } = this.state;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('SearchField', className),
	      onClick: this.stopPropagation
	    }, showAddButton && /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'add',
	      onClick: this.handleAdd
	    }), /*#__PURE__*/React.createElement("input", {
	      className: 'input',
	      style: style,
	      placeholder: placeholder,
	      value: value,
	      onChange: this.handleChange,
	      onInput: this.handleInput,
	      onKeyDown: this.handleKeyDown
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'close',
	      onClick: this.handleReset
	    }), showFilterButton && /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'filter',
	      className: bind(filterShow && 'selected'),
	      onClick: this.handleShowFilter
	    }), showFilterButton && /*#__PURE__*/React.createElement("div", {
	      className: bind('category', !filterShow && 'hidden')
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'item',
	      key: ''
	    }, /*#__PURE__*/React.createElement(CheckBox, {
	      name: '',
	      checked: categories.indexOf('') > -1,
	      onChange: this.handleCheckBoxChange
	    }), /*#__PURE__*/React.createElement("label", {
	      className: 'title'
	    }, _t('No Type'))), data.map(n => {
	      return /*#__PURE__*/React.createElement("div", {
	        className: 'item',
	        key: n.ID
	      }, /*#__PURE__*/React.createElement(CheckBox, {
	        name: n.ID,
	        checked: categories.indexOf(n.ID) > -1,
	        onChange: this.handleCheckBoxChange
	      }), /*#__PURE__*/React.createElement("label", {
	        className: 'title'
	      }, n.Name));
	    })));
	  }

	  componentDidMount() {
	    document.addEventListener(`click`, this.handleHideFilter);
	  }

	  handleAdd(event) {
	    const {
	      onAdd
	    } = this.props;
	    onAdd && onAdd(event);
	  }

	  handleChange(event) {
	    const {
	      onChange
	    } = this.props;
	    event.stopPropagation();
	    const value = event.target.value;
	    this.setState({
	      value
	    });
	    onChange && onChange(value, this.state.categories, event);
	  }

	  handleInput(event) {
	    const {
	      onInput
	    } = this.props;
	    event.stopPropagation();
	    const value = event.target.value;
	    this.setState({
	      value
	    });
	    onInput && onInput(value, this.state.categories, event);
	  }

	  handleReset(event) {
	    const {
	      onInput,
	      onChange
	    } = this.props;
	    const value = '';
	    this.setState({
	      value
	    });
	    onInput && onInput(value, this.state.categories, event);
	    onChange && onChange(value, this.state.categories, event);
	  }

	  handleShowFilter() {
	    this.setState({
	      filterShow: !this.state.filterShow
	    });
	  }

	  handleHideFilter() {
	    this.setState({
	      filterShow: false
	    });
	  }

	  handleCheckBoxChange(checked, name, event) {
	    const {
	      onInput,
	      onChange
	    } = this.props;
	    let categories = this.state.categories;
	    let index = categories.indexOf(name);

	    if (checked && index === -1) {
	      categories.push(name);
	    } else if (!checked && index > -1) {
	      categories.splice(index, 1);
	    } else {
	      console.warn(`SearchField: handleCheckBoxChange error.`);
	      return;
	    }

	    const value = this.state.value;
	    this.setState({
	      categories
	    }, () => {
	      onInput && onInput(value, categories, event);
	      onChange && onChange(value, categories, event);
	    });
	  }

	  stopPropagation(event) {
	    event.nativeEvent.stopImmediatePropagation();
	  }

	}

	SearchField.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  value: propTypes.string,
	  data: propTypes.array,
	  placeholder: propTypes.string,
	  showAddButton: propTypes.bool,
	  showFilterButton: propTypes.bool,
	  onAdd: propTypes.func,
	  onChange: propTypes.func,
	  onInput: propTypes.func
	};
	SearchField.defaultProps = {
	  className: null,
	  style: null,
	  value: '',
	  data: [],
	  placeholder: 'Enter a keyword',
	  showAddButton: false,
	  showFilterButton: false,
	  onAdd: null,
	  onChange: null,
	  onInput: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 输入框
	 * @author tengge / https://github.com/tengge1
	 */

	class Select extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      options,
	      value,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement("select", {
	      className: bind('Select', className),
	      style: style,
	      value: value,
	      disabled: disabled,
	      onChange: this.handleChange
	    }, options && Object.keys(options).map(n => {
	      return /*#__PURE__*/React.createElement("option", {
	        value: n,
	        key: n
	      }, options[n]);
	    }));
	  }

	  handleChange(event) {
	    const {
	      onChange
	    } = this.props;
	    const selectedIndex = event.target.selectedIndex;

	    if (selectedIndex === -1) {
	      onChange && onChange(null, event);
	      return;
	    }

	    const value = event.target.options[selectedIndex].value; // 注意：options的key一定是字符串，所以value也一定是字符串

	    onChange && onChange(value, this.props.name, event);
	  }

	}

	Select.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  options: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.oneOfType([propTypes.string, propTypes.number]),
	  disabled: propTypes.bool,
	  onChange: propTypes.func
	};
	Select.defaultProps = {
	  className: null,
	  style: null,
	  options: null,
	  name: null,
	  value: null,
	  disabled: false,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 文本域
	 * @author tengge / https://github.com/tengge1
	 */

	class TextArea extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this);
	    this.handleInput = this.handleInput.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      value
	    } = this.props;
	    return /*#__PURE__*/React.createElement("textarea", {
	      className: bind('TextArea', className),
	      style: style,
	      value: value,
	      onChange: this.handleChange,
	      onInput: this.handleInput
	    });
	  }

	  handleChange(event) {
	    const {
	      onChange
	    } = this.props;
	    onChange && onChange(event.target.value, this.props.name, event);
	  }

	  handleInput(event) {
	    const {
	      onInput
	    } = this.props;
	    onInput && onInput(event.target.value, this.props.name, event);
	  }

	}

	TextArea.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.string,
	  onChange: propTypes.func,
	  onInput: propTypes.func
	};
	TextArea.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: '',
	  onChange: null,
	  onInput: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 开关
	 * @author tengge / https://github.com/tengge1
	 */

	class Toggle extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      checked,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('Toggle', checked && 'checked', disabled && 'disabled', className),
	      style: style,
	      onClick: disabled ? null : this.handleChange
	    });
	  }

	  handleChange(event) {
	    const {
	      onChange
	    } = this.props;
	    var checked = event.target.classList.contains('checked');
	    onChange && onChange(!checked, this.props.name, event);
	  }

	}

	Toggle.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  checked: propTypes.bool,
	  disabled: propTypes.bool,
	  onChange: propTypes.func
	};
	Toggle.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  checked: false,
	  disabled: false,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图标
	 * @author tengge / https://github.com/tengge1
	 */

	class Icon extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      name,
	      value,
	      icon,
	      title
	    } = this.props;
	    return /*#__PURE__*/React.createElement("i", {
	      className: bind('Icon', 'iconfont', icon && 'icon-' + icon, className),
	      style: style,
	      name: name,
	      value: value,
	      title: title,
	      onClick: this.handleClick
	    });
	  }

	  handleClick(event) {
	    const {
	      onClick
	    } = this.props;
	    const name = event.target.getAttribute('name');
	    onClick && onClick(name, event);
	  }

	}

	Icon.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.string,
	  icon: propTypes.string,
	  title: propTypes.string,
	  onClick: propTypes.func
	};
	Icon.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: null,
	  icon: null,
	  title: null,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图片
	 * @author tengge / https://github.com/tengge1
	 */

	class Image extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleError = this.handleError.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      src,
	      title
	    } = this.props;
	    return /*#__PURE__*/React.createElement("img", {
	      className: bind('Image', className),
	      style: style,
	      src: src,
	      title: title,
	      onError: this.handleError
	    });
	  }

	  handleError(event) {
	    let target = event.target;
	    let parent = target.parentNode;
	    parent.removeChild(target);
	    let img = document.createElement('div');
	    img.className = 'no-img';
	    let icon = document.createElement('i');
	    icon.className = 'Icon iconfont icon-scenes';
	    img.appendChild(icon);
	    let title = parent.children[0];
	    parent.insertBefore(img, title);
	  }

	}

	Image.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  src: propTypes.string,
	  title: propTypes.string
	};
	Image.defaultProps = {
	  className: null,
	  style: null,
	  src: null,
	  title: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图片列表
	 * @author tengge / https://github.com/tengge1
	 */

	class ImageList extends React.Component {
	  constructor(props) {
	    super(props);
	    const {
	      onClick,
	      onEdit,
	      onDelete
	    } = props;
	    this.state = {
	      pageSize: 10,
	      pageNum: 0
	    };
	    this.handleFirstPage = this.handleFirstPage.bind(this);
	    this.handleLastPage = this.handleLastPage.bind(this);
	    this.handlePreviousPage = this.handlePreviousPage.bind(this);
	    this.handleNextPage = this.handleNextPage.bind(this);
	    this.handleClick = this.handleClick.bind(this, onClick);
	    this.handleEdit = this.handleEdit.bind(this, onEdit);
	    this.handleDelete = this.handleDelete.bind(this, onDelete);
	    this.handleError = this.handleError.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      data,
	      showEditButton,
	      showDeleteButton
	    } = this.props;
	    const {
	      pageSize,
	      pageNum
	    } = this.state;
	    const totalPage = this.getTotalPage();
	    const current = data.filter((n, i) => {
	      return i >= pageSize * pageNum && i < pageSize * (pageNum + 1);
	    });
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('ImageList', className),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'content'
	    }, current.map(n => {
	      return /*#__PURE__*/React.createElement("div", {
	        className: 'item',
	        name: n.id,
	        key: n.id,
	        onClick: this.handleClick
	      }, n.src ? /*#__PURE__*/React.createElement("img", {
	        className: 'img',
	        src: n.src,
	        onError: this.handleError
	      }) : /*#__PURE__*/React.createElement("div", {
	        className: 'no-img'
	      }, /*#__PURE__*/React.createElement(Icon, {
	        icon: n.icon
	      })), /*#__PURE__*/React.createElement("div", {
	        className: 'title'
	      }, n.title), n.cornerText && /*#__PURE__*/React.createElement("div", {
	        className: 'cornerText'
	      }, n.cornerText), showEditButton && n.showEditButton !== false && /*#__PURE__*/React.createElement(IconButton, {
	        className: 'edit',
	        icon: 'edit',
	        name: n.id,
	        onClick: this.handleEdit
	      }), showDeleteButton && n.showDeleteButton !== false && /*#__PURE__*/React.createElement(IconButton, {
	        className: 'delete',
	        icon: 'delete',
	        name: n.id,
	        onClick: this.handleDelete
	      }));
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'page'
	    }, /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'backward',
	      title: _t('First Page'),
	      onClick: this.handleFirstPage
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'left-triangle2',
	      title: _t('Previous Page'),
	      onClick: this.handlePreviousPage
	    }), /*#__PURE__*/React.createElement(Input, {
	      className: 'current',
	      value: (pageNum + 1).toString(),
	      title: _t('Current Page'),
	      disabled: true
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'right-triangle2',
	      title: _t('Next Page'),
	      onClick: this.handleNextPage
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'forward',
	      title: _t('Last Page'),
	      onClick: this.handleLastPage
	    }), /*#__PURE__*/React.createElement("div", {
	      className: 'info'
	    }, _t('Total {{totalPage}} Pages', {
	      totalPage: totalPage
	    }))));
	  }

	  handleFirstPage() {
	    this.setState({
	      pageNum: 0
	    });
	  }

	  handleLastPage() {
	    const totalPage = this.getTotalPage();
	    this.setState({
	      pageNum: totalPage < 1 ? 0 : totalPage - 1
	    });
	  }

	  handleNextPage() {
	    this.setState(state => {
	      const totalPage = this.getTotalPage();
	      return {
	        pageNum: state.pageNum < totalPage - 1 ? state.pageNum + 1 : totalPage - 1
	      };
	    });
	  }

	  handlePreviousPage() {
	    this.setState(state => {
	      return {
	        pageNum: state.pageNum > 0 ? state.pageNum - 1 : 0
	      };
	    });
	  }

	  handleClick(onClick, event) {
	    event.stopPropagation();
	    const id = event.target.getAttribute('name');
	    const data = this.props.data.filter(n => n.id === id)[0];
	    onClick && onClick(data, event);
	  }

	  handleEdit(onEdit, name, event) {
	    event.stopPropagation();
	    const data = this.props.data.filter(n => n.id === name)[0];
	    onEdit && onEdit(data, event);
	  }

	  handleDelete(onDelete, name, event) {
	    event.stopPropagation();
	    const data = this.props.data.filter(n => n.id === name)[0];
	    onDelete && onDelete(data, event);
	  }

	  handleError(event) {
	    let target = event.target;
	    let parent = target.parentNode;
	    parent.removeChild(target);
	    let img = document.createElement('div');
	    img.className = 'no-img';
	    let icon = document.createElement('i');
	    icon.className = 'Icon iconfont icon-scenes';
	    img.appendChild(icon);
	    let title = parent.children[0];
	    parent.insertBefore(img, title);
	  }

	  getTotalPage() {
	    const total = this.props.data.length;
	    const pageSize = this.state.pageSize;
	    return total % pageSize === 0 ? total / pageSize : parseInt(total / pageSize) + 1;
	  }

	}

	ImageList.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  data: propTypes.array,
	  showEditButton: propTypes.bool,
	  showDeleteButton: propTypes.bool,
	  onClick: propTypes.func,
	  onEdit: propTypes.func,
	  onDelete: propTypes.func
	};
	ImageList.defaultProps = {
	  className: null,
	  style: null,
	  data: [],
	  showEditButton: true,
	  showDeleteButton: true,
	  onClick: null,
	  onEdit: null,
	  onDelete: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图片选取控件
	 * @author tengge / https://github.com/tengge1
	 */

	class ImageSelector extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleSelect = this.handleSelect.bind(this);
	    this.handleChange = this.handleChange.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      value,
	      noImageText
	    } = this.props;

	    if (value) {
	      return /*#__PURE__*/React.createElement("img", {
	        className: bind('ImageSelector', className),
	        style: style,
	        src: value,
	        onClick: this.handleSelect
	      });
	    } else {
	      return /*#__PURE__*/React.createElement("div", {
	        className: bind('ImageSelector', 'empty', className),
	        style: style,
	        onClick: this.handleSelect
	      }, noImageText);
	    }
	  }

	  componentDidMount() {
	    var input = document.createElement('input');
	    input.type = 'file';
	    input.style.display = 'none';
	    input.addEventListener('change', this.handleChange);
	    document.body.appendChild(input);
	    this.input = input;
	  }

	  componentWillUnmount() {
	    var input = this.input;
	    input.removeEventListener('change', this.handleChange);
	    document.body.removeChild(input);
	    this.input = null;
	  }

	  handleSelect() {
	    this.input.click();
	  }

	  handleChange(event) {
	    const {
	      name,
	      onChange
	    } = this.props;
	    onChange && onChange(name, event.target.files[0], event);
	  }

	}

	ImageSelector.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.any,
	  noImageText: propTypes.string,
	  onChange: propTypes.func
	};
	ImageSelector.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: null,
	  noImageText: 'No Image',
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图片上传控件
	 * @author tengge / https://github.com/tengge1
	 */

	class ImageUploader extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleSelect = this.handleSelect.bind(this);
	    this.handleChange = this.handleChange.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      url,
	      server,
	      noImageText
	    } = this.props;

	    if (url && url !== 'null') {
	      return /*#__PURE__*/React.createElement("img", {
	        className: bind('ImageUploader', className),
	        style: style,
	        src: server + url,
	        onClick: this.handleSelect
	      });
	    } else {
	      return /*#__PURE__*/React.createElement("div", {
	        className: bind('ImageUploader', 'empty', className),
	        onClick: this.handleSelect
	      }, noImageText);
	    }
	  }

	  componentDidMount() {
	    var input = document.createElement('input');
	    input.type = 'file';
	    input.style.display = 'none';
	    input.addEventListener('change', this.handleChange);
	    document.body.appendChild(input);
	    this.input = input;
	  }

	  componentWillUnmount() {
	    var input = this.input;
	    input.removeEventListener('change', this.handleChange);
	    document.body.removeChild(input);
	    this.input = null;
	  }

	  handleSelect() {
	    this.input.click();
	  }

	  handleChange(event) {
	    const {
	      onChange
	    } = this.props;
	    onChange && onChange(event.target.files[0], event);
	  }

	}

	ImageUploader.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  url: propTypes.string,
	  server: propTypes.string,
	  noImageText: propTypes.string,
	  onChange: propTypes.func
	};
	ImageUploader.defaultProps = {
	  className: null,
	  style: null,
	  url: null,
	  server: '',
	  noImageText: 'No Image',
	  onChange: null
	};

	/**
	 * 绝对定位布局
	 * @author tengge / https://github.com/tengge1
	 */

	class AbsoluteLayout extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      left,
	      top,
	      ...others
	    } = this.props;
	    const position = {
	      left: left || 0,
	      top: top || 0
	    };
	    return /*#__PURE__*/React.createElement("div", _extends({
	      className: bind('AbsoluteLayout', className),
	      style: style ? Object.assign({}, style, position) : position
	    }, others), children);
	  }

	}

	AbsoluteLayout.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  left: propTypes.string,
	  top: propTypes.string
	};
	AbsoluteLayout.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  left: '0',
	  top: '0'
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 单个折叠面板
	 * @private
	 * @author tengge / https://github.com/tengge1
	 */

	class AccordionPanel extends React.Component {
	  constructor(props) {
	    super(props);
	    this.state = {
	      maximized: props.maximized
	    };
	    this.handleClick = this.handleClick.bind(this, props.onClick, props.index, props.name);
	    this.handleMaximize = this.handleMaximize.bind(this, props.onMaximize);
	  }

	  handleClick(onClick, index, name, event) {
	    onClick && onClick(index, name, event);
	  }

	  handleMaximize(onMaximize, event) {
	    this.setState(state => ({
	      maximized: !state.maximized
	    }));
	    onMaximize && onMaximize(event);
	  }

	  render() {
	    const {
	      title,
	      className,
	      style,
	      children,
	      show,
	      total,
	      collpased,
	      maximizable
	    } = this.props;
	    const maximizeControl = maximizable && /*#__PURE__*/React.createElement("div", {
	      className: 'control',
	      onClick: this.handleMaximize
	    }, this.state.maximized ? /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-minimize'
	    }) : /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-maximize'
	    }));

	    const _style = collpased ? style : Object.assign({}, style, {
	      height: `calc(100% - ${26 * (total - 1)}px`
	    });

	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('AccordionPanel', this.state.maximized && 'maximized', collpased && 'collpased', !show && 'hidden', className),
	      style: _style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'header',
	      onClick: this.handleClick
	    }, /*#__PURE__*/React.createElement("span", {
	      className: "title"
	    }, title), /*#__PURE__*/React.createElement("div", {
	      className: "controls"
	    }, maximizeControl)), /*#__PURE__*/React.createElement("div", {
	      className: 'body'
	    }, children));
	  }

	}

	AccordionPanel.propTypes = {
	  name: propTypes.string,
	  title: propTypes.string,
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  show: propTypes.bool,
	  total: propTypes.number,
	  index: propTypes.number,
	  collpased: propTypes.bool,
	  maximizable: propTypes.bool,
	  maximized: propTypes.bool,
	  onMaximize: propTypes.bool,
	  onClick: propTypes.func
	};
	AccordionPanel.defaultProps = {
	  name: null,
	  title: null,
	  className: null,
	  style: null,
	  children: null,
	  show: true,
	  total: 1,
	  index: 0,
	  collpased: true,
	  maximizable: false,
	  maximized: false,
	  onMaximize: null,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 折叠布局
	 * @author tengge / https://github.com/tengge1
	 */

	class AccordionLayout extends React.Component {
	  constructor(props) {
	    super(props);
	    this.state = {
	      activeIndex: props.activeIndex
	    };
	    this.handleClick = this.handleClick.bind(this);
	  }

	  handleClick(index, name, event) {
	    const {
	      onActive
	    } = this.props;
	    onActive && onActive(index, name, event);
	    this.setState({
	      activeIndex: index
	    });
	  }

	  render() {
	    const {
	      className,
	      style,
	      children
	    } = this.props;
	    const content = (Array.isArray(children) ? children : [children]).filter(n => n);
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('AccordionLayout', className),
	      style: style
	    }, content.map((n, i) => {
	      return /*#__PURE__*/React.createElement(AccordionPanel, {
	        name: n.props.name,
	        title: n.props.title,
	        show: n.props.show,
	        total: content.length,
	        index: i,
	        collpased: i !== this.state.activeIndex,
	        maximizable: n.props.maximizable,
	        onClick: this.handleClick,
	        key: i
	      }, n.props.children);
	    }));
	  }

	}

	AccordionLayout.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  activeIndex: propTypes.number,
	  onActive: propTypes.func
	};
	AccordionLayout.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  activeIndex: 0,
	  onActive: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 边框布局
	 * @author tengge / https://github.com/tengge1
	 */

	class BorderLayout extends React.Component {
	  constructor(props) {
	    super(props);
	    const children = this.props.children;
	    const north = children && children.filter(n => n && n.props.region === 'north')[0];
	    const south = children && children.filter(n => n && n.props.region === 'south')[0];
	    const west = children && children.filter(n => n && n.props.region === 'west')[0];
	    const east = children && children.filter(n => n && n.props.region === 'east')[0];
	    const northSplit = north && north.props.split || false;
	    const southSplit = south && south.props.split || false;
	    const westSplit = west && west.props.split || false;
	    const eastSplit = east && east.props.split || false;
	    const northCollapsed = north && north.props.collapsed || false;
	    const southCollapsed = south && south.props.collapsed || false;
	    const westCollapsed = west && west.props.collapsed || false;
	    const eastCollapsed = east && east.props.collapsed || false;
	    const onNorthToggle = north && north.props.onToggle || null;
	    const onSouthToggle = south && south.props.onToggle || null;
	    const onWestToggle = west && west.props.onToggle || null;
	    const onEastToggle = east && east.props.onToggle || null;
	    this.northRef = React.createRef();
	    this.southRef = React.createRef();
	    this.westRef = React.createRef();
	    this.eastRef = React.createRef();
	    this.state = {
	      northSplit,
	      southSplit,
	      westSplit,
	      eastSplit,
	      northCollapsed,
	      southCollapsed,
	      westCollapsed,
	      eastCollapsed
	    };
	    this.handleNorthClick = this.handleNorthClick.bind(this, onNorthToggle);
	    this.handleSouthClick = this.handleSouthClick.bind(this, onSouthToggle);
	    this.handleWestClick = this.handleWestClick.bind(this, onWestToggle);
	    this.handleEastClick = this.handleEastClick.bind(this, onEastToggle);
	    this.handleTransitionEnd = this.handleTransitionEnd.bind(this, onNorthToggle, onSouthToggle, onWestToggle, onEastToggle);
	  }

	  handleNorthClick() {
	    if (!this.state.northSplit) {
	      return;
	    }

	    this.setState(state => {
	      const collapsed = !state.northCollapsed;
	      const dom = this.northRef.current;
	      const height = dom.clientHeight;

	      if (collapsed) {
	        dom.style.marginTop = `-${height - 8}px`;
	      } else {
	        dom.style.marginTop = null;
	      }

	      return {
	        northCollapsed: collapsed
	      };
	    });
	  }

	  handleSouthClick() {
	    if (!this.state.southSplit) {
	      return;
	    }

	    this.setState(state => {
	      const collapsed = !state.southCollapsed;
	      const dom = this.southRef.current;
	      const height = dom.clientHeight;

	      if (collapsed) {
	        dom.style.marginBottom = `-${height - 8}px`;
	      } else {
	        dom.style.marginBottom = null;
	      }

	      return {
	        southCollapsed: collapsed
	      };
	    });
	  }

	  handleWestClick() {
	    if (!this.state.westSplit) {
	      return;
	    }

	    const dom = this.westRef.current;
	    this.setState(state => {
	      const collapsed = !state.westCollapsed;
	      const width = dom.clientWidth;

	      if (collapsed) {
	        dom.style.marginLeft = `-${width - 8}px`;
	      } else {
	        dom.style.marginLeft = null;
	      }

	      return {
	        westCollapsed: collapsed
	      };
	    });
	  }

	  handleEastClick() {
	    if (!this.state.eastSplit) {
	      return;
	    }

	    this.setState(state => {
	      const collapsed = !state.eastCollapsed;
	      const dom = this.eastRef.current;
	      const width = dom.clientWidth;

	      if (collapsed) {
	        dom.style.marginRight = `-${width - 8}px`;
	      } else {
	        dom.style.marginRight = null;
	      }

	      return {
	        eastCollapsed: collapsed
	      };
	    });
	  }

	  handleTransitionEnd(onNorthToggle, onSouthToggle, onWestToggle, onEastToggle, event) {
	    const region = event.target.getAttribute('region');

	    switch (region) {
	      case 'north':
	        onNorthToggle && onNorthToggle(!this.state.northCollapsed);
	        break;

	      case 'south':
	        onSouthToggle && onSouthToggle(!this.state.southCollapsed);
	        break;

	      case 'west':
	        onWestToggle && onWestToggle(!this.state.westCollapsed);
	        break;

	      case 'east':
	        onEastToggle && onEastToggle(!this.state.eastCollapsed);
	        break;
	    }
	  }

	  render() {
	    const {
	      className,
	      style,
	      children
	    } = this.props;
	    let north = [],
	        south = [],
	        west = [],
	        east = [],
	        center = [],
	        others = [];
	    children && children.forEach(n => {
	      if (!n) {
	        return;
	      }

	      switch (n.props.region) {
	        case 'north':
	          north.push(n);
	          break;

	        case 'south':
	          south.push(n);
	          break;

	        case 'west':
	          west.push(n);
	          break;

	        case 'east':
	          east.push(n);
	          break;

	        case 'center':
	          center.push(n);
	          break;

	        default:
	          others.push(n);
	          break;
	      }
	    });

	    if (center.length === 0) {
	      console.warn(`BorderLayout: center region is not defined.`);
	    } // north region


	    const northRegion = north.length > 0 && /*#__PURE__*/React.createElement("div", {
	      className: bind('north', this.state.northSplit && 'split', this.state.northCollapsed && 'collapsed', north.every(n => n.props.show === false) && 'hidden'),
	      region: 'north',
	      onTransitionEnd: this.handleTransitionEnd,
	      ref: this.northRef
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'content'
	    }, north), this.state.northSplit && /*#__PURE__*/React.createElement("div", {
	      className: 'control'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'button',
	      onClick: this.handleNorthClick
	    }))); // south region

	    const southRegion = south.length > 0 && /*#__PURE__*/React.createElement("div", {
	      className: bind('south', this.state.northSplit && 'split', this.state.southCollapsed && 'collapsed', south.every(n => n.props.show === false) && 'hidden'),
	      region: 'south',
	      onTransitionEnd: this.handleTransitionEnd,
	      ref: this.southRef
	    }, this.state.southSplit && /*#__PURE__*/React.createElement("div", {
	      className: 'control'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'button',
	      onClick: this.handleSouthClick
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'content'
	    }, south)); // west region

	    const westRegion = west.length > 0 && /*#__PURE__*/React.createElement("div", {
	      className: bind('west', this.state.westSplit && 'split', this.state.westCollapsed && 'collapsed', west.every(n => n.props.show === false) && 'hidden'),
	      region: 'west',
	      onTransitionEnd: this.handleTransitionEnd,
	      ref: this.westRef
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'content'
	    }, west), this.state.westSplit && /*#__PURE__*/React.createElement("div", {
	      className: 'control'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'button',
	      onClick: this.handleWestClick
	    }))); // east region

	    const eastRegion = east.length > 0 && /*#__PURE__*/React.createElement("div", {
	      className: bind('east', this.state.eastSplit && 'split', this.state.eastCollapsed && 'collapsed', east.every(n => n.props.show === false) && 'hidden'),
	      region: 'east',
	      onTransitionEnd: this.handleTransitionEnd,
	      ref: this.eastRef
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'control'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'button',
	      onClick: this.handleEastClick
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'content'
	    }, east)); // center region

	    const centerRegion = center.length > 0 && /*#__PURE__*/React.createElement("div", {
	      className: 'center'
	    }, center);
	    const otherRegion = others.length > 0 && others;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('BorderLayout', className),
	      style: style
	    }, northRegion, /*#__PURE__*/React.createElement("div", {
	      className: 'middle'
	    }, westRegion, centerRegion, eastRegion), southRegion, otherRegion);
	  }

	}

	BorderLayout.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	BorderLayout.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/**
	 * 水平布局
	 * @author tengge / https://github.com/tengge1
	 */

	class HBoxLayout extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", _extends({
	      className: bind('HBoxLayout', className),
	      style: style
	    }, others), children);
	  }

	}

	HBoxLayout.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	HBoxLayout.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 选项卡布局
	 * @author tengge / https://github.com/tengge1
	 */

	class TabLayout extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this, props.onActiveTabChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      activeTabIndex
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('TabLayout', className),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'tabs'
	    }, React.Children.map(children, (n, i) => {
	      return /*#__PURE__*/React.createElement("div", {
	        className: bind('tab', i === activeTabIndex ? 'selected' : null),
	        key: i,
	        tbindex: i,
	        onClick: this.handleClick
	      }, n.props.title);
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'contents'
	    }, React.Children.map(children, (n, i) => {
	      return /*#__PURE__*/React.createElement("div", {
	        className: bind('content', i === activeTabIndex ? 'show' : null),
	        key: i
	      }, n);
	    })));
	  }

	  handleClick(onActiveTabChange, event) {
	    const index = event.target.getAttribute('tbindex');
	    onActiveTabChange && onActiveTabChange(parseInt(index), event.target, event);
	  }

	}

	TabLayout.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  activeTabIndex: propTypes.number,
	  onActiveTabChange: propTypes.func
	};
	TabLayout.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  activeTabIndex: 0,
	  onActiveTabChange: null
	};

	/**
	 * 竖直布局
	 * @author tengge / https://github.com/tengge1
	 */

	class VBoxLayout extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", _extends({
	      className: bind('VBoxLayout', className),
	      style: style
	    }, others), children);
	  }

	}

	VBoxLayout.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	VBoxLayout.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 上下文菜单
	 * @author tengge / https://github.com/tengge1
	 */

	class ContextMenu extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children
	    } = this.props;
	    return /*#__PURE__*/React.createElement("ul", {
	      className: bind('ContextMenu', className),
	      style: style
	    }, children);
	  }

	}

	ContextMenu.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	ContextMenu.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/**
	 * 菜单栏
	 * @author tengge / https://github.com/tengge1
	 */

	class MenuBar extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("ul", _extends({
	      className: bind('MenuBar', className),
	      style: style
	    }, others), children);
	  }

	}

	MenuBar.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	MenuBar.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 菜单栏填充
	 * @author tengge / https://github.com/tengge1
	 */

	class MenuBarFiller extends React.Component {
	  render() {
	    const {
	      className,
	      style
	    } = this.props;
	    return /*#__PURE__*/React.createElement("li", {
	      className: bind('MenuItem', 'MenuBarFiller', className),
	      style: style
	    });
	  }

	}

	MenuBarFiller.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object
	};
	MenuBarFiller.defaultProps = {
	  className: null,
	  style: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 菜单项
	 * @author tengge / https://github.com/tengge1
	 */

	class MenuItem extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this, props.onClick);
	  }

	  render() {
	    const {
	      title,
	      className,
	      style,
	      children,
	      show,
	      checked,
	      selected,
	      disabled
	    } = this.props;
	    const subMenu = React.Children.count(children) ? /*#__PURE__*/React.createElement(React.Fragment, null, /*#__PURE__*/React.createElement("div", {
	      className: 'suffix'
	    }, /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-right-triangle'
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'sub'
	    }, /*#__PURE__*/React.createElement("ul", {
	      className: 'wrap'
	    }, children))) : null;
	    return /*#__PURE__*/React.createElement("li", {
	      className: bind('MenuItem', checked !== undefined && 'checked', selected !== undefined && 'selected', disabled && 'disabled', !show && 'hidden', className),
	      style: style,
	      onClick: this.handleClick
	    }, (checked !== undefined || selected !== undefined) && /*#__PURE__*/React.createElement("div", {
	      className: bind('prefix', (checked || selected) && 'on')
	    }), /*#__PURE__*/React.createElement("span", null, title), subMenu);
	  }

	  handleClick(onClick, event) {
	    event.stopPropagation();

	    if (!event.target.classList.contains('disabled')) {
	      onClick && onClick(this.props.name, event);
	    }
	  }

	}

	MenuItem.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  name: propTypes.string,
	  title: propTypes.string,
	  show: propTypes.bool,
	  checked: propTypes.bool,
	  selected: propTypes.bool,
	  disabled: propTypes.bool,
	  onClick: propTypes.func
	};
	MenuItem.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  name: null,
	  title: null,
	  show: true,
	  checked: undefined,
	  selected: undefined,
	  disabled: false,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 菜单项分隔符
	 * @author tengge / https://github.com/tengge1
	 */

	class MenuItemSeparator extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      direction,
	      show
	    } = this.props;
	    return /*#__PURE__*/React.createElement("li", {
	      className: bind('MenuItemSeparator', direction && direction, !show && 'hidden', className),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: "separator"
	    }));
	  }

	}

	MenuItemSeparator.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  direction: propTypes.oneOf(['horizontal', 'vertical']),
	  show: propTypes.bool
	};
	MenuItemSeparator.defaultProps = {
	  className: null,
	  style: null,
	  direction: 'vertical',
	  show: true
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 菜单选项卡
	 * @author tengge / https://github.com/tengge1
	 */

	class MenuTab extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this, props.onClick);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      selected,
	      show,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement("li", {
	      className: bind('MenuTab', selected && 'selected', disabled && 'disabled', !show && 'hidden', className),
	      style: style,
	      onClick: this.handleClick
	    }, children);
	  }

	  handleClick(onClick, event) {
	    event.stopPropagation();

	    if (!event.target.classList.contains('disabled')) {
	      onClick && onClick(this.props.name, event);
	    }
	  }

	}

	MenuTab.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  name: propTypes.string,
	  selected: propTypes.bool,
	  show: propTypes.bool,
	  disabled: propTypes.bool,
	  onClick: propTypes.func
	};
	MenuTab.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  name: null,
	  selected: false,
	  show: true,
	  disabled: false,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 面板
	 * @author tengge / https://github.com/tengge1
	 */

	class Panel extends React.Component {
	  constructor(props) {
	    super(props);
	    this.state = {
	      collapsed: props.collapsed,
	      maximized: props.maximized,
	      closed: props.closed
	    };
	    this.handleCollapse = this.handleCollapse.bind(this, props.onCollapse);
	    this.handleMaximize = this.handleMaximize.bind(this, props.onMaximize);
	    this.handleClose = this.handleClose.bind(this, props.onClose);
	  }

	  handleCollapse(onCollapse, event) {
	    this.setState(state => ({
	      collapsed: !state.collapsed
	    }));
	    onCollapse && onCollapse(event);
	  }

	  handleMaximize(onMaximize, event) {
	    this.setState(state => ({
	      maximized: !state.maximized
	    }));
	    onMaximize && onMaximize(event);
	  }

	  handleClose(onClose, event) {
	    this.setState(state => ({
	      closed: !state.closed
	    }));
	    onClose && onClose(event);
	  }

	  render() {
	    const {
	      title,
	      className,
	      style,
	      children,
	      show,
	      header,
	      collapsible,
	      maximizable,
	      closable
	    } = this.props;
	    const collapseControl = collapsible && /*#__PURE__*/React.createElement("div", {
	      className: 'control',
	      onClick: this.handleCollapse
	    }, this.state.collapsed ? /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-down-arrow'
	    }) : /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-up-arrow'
	    }));
	    const maximizeControl = maximizable && /*#__PURE__*/React.createElement("div", {
	      className: 'control',
	      onClick: this.handleMaximize
	    }, this.state.maximized ? /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-minimize'
	    }) : /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-maximize'
	    }));
	    const closeControl = closable && /*#__PURE__*/React.createElement("div", {
	      className: 'control',
	      onClick: this.handleClose
	    }, /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-close-thin'
	    }));
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('Panel', this.state.maximized && 'maximized', this.state.collapsed && 'collapsed', this.state.closed && 'hidden', !show && 'hidden', className),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: bind('header', header ? null : 'hidden')
	    }, /*#__PURE__*/React.createElement("span", {
	      className: "title"
	    }, title), /*#__PURE__*/React.createElement("div", {
	      className: "controls"
	    }, collapseControl, maximizeControl, closeControl)), /*#__PURE__*/React.createElement("div", {
	      className: 'body'
	    }, children));
	  }

	}

	Panel.propTypes = {
	  title: propTypes.string,
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  show: propTypes.bool,
	  header: propTypes.bool,
	  collapsible: propTypes.bool,
	  collapsed: propTypes.bool,
	  onCollapse: propTypes.func,
	  maximizable: propTypes.bool,
	  maximized: propTypes.bool,
	  onMaximize: propTypes.bool,
	  closable: propTypes.bool,
	  closed: propTypes.bool,
	  onClose: propTypes.func
	};
	Panel.defaultProps = {
	  title: null,
	  className: null,
	  style: null,
	  children: null,
	  show: true,
	  header: true,
	  collapsible: false,
	  collapsed: false,
	  onCollapse: null,
	  maximizable: false,
	  maximized: false,
	  onMaximize: null,
	  closable: false,
	  closed: false,
	  onClose: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 加载动画
	 * @author tengge / https://github.com/tengge1
	 */

	class LoadMask extends React.Component {
	  constructor(props) {
	    super(props);
	  }

	  render() {
	    const {
	      className,
	      style,
	      show,
	      text
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('LoadMask', className, !show && 'hidden'),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'box'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'msg'
	    }, text)));
	  }

	}

	LoadMask.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  show: propTypes.bool,
	  text: propTypes.string
	};
	LoadMask.defaultProps = {
	  className: null,
	  style: null,
	  show: true,
	  text: 'Waiting...'
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 属性表
	 * @author tengge / https://github.com/tengge1
	 */

	class PropertyGrid extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('PropertyGrid', className),
	      style: style
	    }, children);
	  }

	}

	PropertyGrid.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	PropertyGrid.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 属性组
	 * @author tengge / https://github.com/tengge1
	 */

	class PropertyGroup extends React.Component {
	  constructor(props) {
	    super(props);
	    this.contentRef = React.createRef();
	    this.handleExpand = this.handleExpand.bind(this, props.onExpand);
	  }

	  render() {
	    const {
	      style,
	      children,
	      title,
	      show,
	      expanded
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('PropertyGroup', !show && 'hidden'),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'head',
	      expanded: expanded ? 'true' : 'false',
	      onClick: this.handleExpand
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'icon'
	    }, /*#__PURE__*/React.createElement("i", {
	      className: expanded ? 'icon-expand' : 'icon-collapse'
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'title'
	    }, title)), /*#__PURE__*/React.createElement("div", {
	      className: bind('content', !expanded && 'collapsed'),
	      ref: this.contentRef
	    }, React.Children.map(children, (n, i) => {
	      if (n.props.show === false) {
	        return null;
	      }

	      let typeName = n.type.name;

	      if (typeName.indexOf('$') > -1) {
	        typeName = typeName.split('$')[0];
	      }

	      return /*#__PURE__*/React.createElement("div", {
	        className: bind('property', typeName),
	        key: i
	      }, /*#__PURE__*/React.createElement("div", {
	        className: 'label'
	      }, n.props.label), /*#__PURE__*/React.createElement("div", {
	        className: 'field'
	      }, n));
	    })));
	  }

	  componentDidUpdate() {
	    let content = this.contentRef.current;
	    let height = 0;

	    for (let i = 0; i < content.children.length; i++) {
	      let child = content.children[i];
	      height += child.offsetHeight; // offsetHeight包含下边框
	    }

	    content.style.height = `${height}px`;
	  }

	  handleExpand(onExpand, event) {
	    const expanded = event.target.getAttribute('expanded') === 'true';
	    onExpand && onExpand(!expanded, event);
	  }

	}

	PropertyGroup.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  title: propTypes.string,
	  show: propTypes.bool,
	  expanded: propTypes.bool,
	  onExpand: propTypes.func
	};
	PropertyGroup.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  title: 'Group',
	  show: true,
	  expanded: true,
	  onExpand: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 展示属性
	 * @author tengge / https://github.com/tengge1
	 */

	class DisplayProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this, props.onClick);
	  }

	  render() {
	    const {
	      className,
	      style,
	      value,
	      btnShow,
	      btnText
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('wrap', className),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'label'
	    }, value), btnShow && /*#__PURE__*/React.createElement(Button, {
	      className: 'button',
	      onClick: this.handleClick
	    }, btnText));
	  }

	  handleClick(onClick, name, event) {
	    onClick && onClick(this.props.name, event);
	  }

	}

	DisplayProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.string,
	  btnShow: propTypes.bool,
	  btnText: propTypes.string,
	  onClick: propTypes.func
	};
	DisplayProperty.defaultProps = {
	  className: null,
	  style: null,
	  name: 'name',
	  value: '',
	  btnShow: false,
	  btnText: 'Button',
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 文本属性
	 * @author tengge / https://github.com/tengge1
	 */

	class TextProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this, props.onChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      name,
	      value
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Input, {
	      className: bind('input', className),
	      style: style,
	      name: name,
	      value: value,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(onChange, value, name, event) {
	    onChange && onChange(value, name, event);
	  }

	}

	TextProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.string,
	  onChange: propTypes.func
	};
	TextProperty.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: '',
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 复选框属性
	 * @author tengge / https://github.com/tengge1
	 */

	class CheckBoxProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this, props.onChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      name,
	      value
	    } = this.props;
	    return /*#__PURE__*/React.createElement(CheckBox, {
	      className: bind('checkbox', className),
	      style: style,
	      name: name,
	      checked: value,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(onChange, value, name, event) {
	    onChange && onChange(value, name, event);
	  }

	}

	CheckBoxProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.bool,
	  onChange: propTypes.func
	};
	CheckBoxProperty.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: false,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 数字属性
	 * @author tengge / https://github.com/tengge1
	 */

	class NumberProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this, props.onChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      name,
	      value,
	      min,
	      max,
	      step
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Input, {
	      className: bind('input', className),
	      style: style,
	      name: name,
	      type: 'number',
	      value: value,
	      min: min,
	      max: max,
	      step: step,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(onChange, value, name, event) {
	    onChange && onChange(value, name, event);
	  }

	}

	NumberProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.number,
	  min: propTypes.number,
	  max: propTypes.number,
	  step: propTypes.number,
	  onChange: propTypes.func
	};
	NumberProperty.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: 0,
	  min: null,
	  max: null,
	  step: null,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 按钮属性
	 * @author tengge / https://github.com/tengge1
	 */

	class ButtonProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this, props.onChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      text
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Button, {
	      className: bind('button', className),
	      style: style,
	      onClick: this.handleChange
	    }, text);
	  }

	  handleChange(onChange, name, value, event) {
	    onChange && onChange(name, value, event);
	  }

	}

	ButtonProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  text: propTypes.string,
	  onChange: propTypes.func
	};
	ButtonProperty.defaultProps = {
	  className: null,
	  style: null,
	  text: 'Button',
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 颜色属性
	 * @author tengge / https://github.com/tengge1
	 */

	class ColorProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this, props.onChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      name,
	      value
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Input, {
	      className: bind('input', className),
	      style: style,
	      name: name,
	      type: 'color',
	      value: value,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(onChange, value, name, event) {
	    onChange && onChange(value, name, event);
	  }

	}

	ColorProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.string,
	  onChange: propTypes.func
	};
	ColorProperty.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: '',
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 文本属性
	 * @author tengge / https://github.com/tengge1
	 */

	class SelectProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this, props.onChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      options,
	      name,
	      value,
	      disabled
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Select, {
	      className: bind('select', className),
	      style: style,
	      options: options,
	      name: name,
	      value: value,
	      disabled: disabled,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(onChange, value, name, event) {
	    onChange && onChange(value, name, event);
	  }

	}

	SelectProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  options: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.oneOfType([propTypes.string, propTypes.number]),
	  disabled: propTypes.bool,
	  onChange: propTypes.func
	};
	SelectProperty.defaultProps = {
	  className: null,
	  style: null,
	  options: {},
	  name: null,
	  value: null,
	  disabled: false,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 整数属性
	 * @author tengge / https://github.com/tengge1
	 */

	class IntegerProperty extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleChange = this.handleChange.bind(this, props.onChange);
	  }

	  render() {
	    const {
	      className,
	      style,
	      name,
	      value,
	      min,
	      max
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Input, {
	      className: bind('input', className),
	      style: style,
	      name: name,
	      type: 'number',
	      value: value,
	      min: min,
	      max: max,
	      step: 1,
	      precision: 0,
	      onChange: this.handleChange
	    });
	  }

	  handleChange(onChange, value, name, event) {
	    if (value === null) {
	      onChange && onChange(value, name, event);
	    } else {
	      onChange && onChange(parseInt(value), name, event);
	    }
	  }

	}

	IntegerProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  name: propTypes.string,
	  value: propTypes.number,
	  min: propTypes.number,
	  max: propTypes.number,
	  onChange: propTypes.func
	};
	IntegerProperty.defaultProps = {
	  className: null,
	  style: null,
	  name: null,
	  value: 0,
	  min: null,
	  max: null,
	  onChange: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 按钮组属性
	 * @author tengge / https://github.com/tengge1
	 */

	class ButtonsProperty extends React.Component {
	  constructor(props) {
	    super(props);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('buttons', className),
	      style: style
	    }, children);
	  }

	}

	ButtonsProperty.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	ButtonsProperty.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/**
	 * SVG
	 * @author tengge / https://github.com/tengge1
	 */

	class SVG extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("svg", _extends({
	      className: bind('SVG', className),
	      style: style
	    }, others));
	  }

	}

	SVG.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object
	};
	SVG.defaultProps = {
	  className: null,
	  style: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 工具栏分割线
	 * @author tengge / https://github.com/tengge1
	 */

	class ToolbarSeparator extends React.Component {
	  render() {
	    const {
	      className,
	      style
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('ToolbarSeparator', className),
	      style: style
	    }, /*#__PURE__*/React.createElement("div", {
	      className: "separator"
	    }));
	  }

	}

	ToolbarSeparator.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object
	};
	ToolbarSeparator.defaultProps = {
	  className: null,
	  style: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 工具栏填充
	 * @author tengge / https://github.com/tengge1
	 */

	class ToolbarFiller extends React.Component {
	  render() {
	    const {
	      className,
	      style
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('ToolbarFiller', className),
	      style: style
	    });
	  }

	}

	ToolbarFiller.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object
	};
	ToolbarFiller.defaultProps = {
	  className: null,
	  style: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 数据表格
	 * @author tengge / https://github.com/tengge1
	 */

	class DataGrid extends React.Component {
	  constructor(props) {
	    super(props);
	    this.pageSize = {
	      10: '10',
	      20: '20',
	      50: '50',
	      100: '100'
	    };
	    this.handleClick = this.handleClick.bind(this, props.onSelect);
	    this.handleSelectAll = this.handleSelectAll.bind(this);
	    this.handleChangePageSize = this.handleChangePageSize.bind(this, props.onChangePageSize);
	    this.handleFirstPage = this.handleFirstPage.bind(this, props.onFirstPage);
	    this.handlePreviousPage = this.handlePreviousPage.bind(this, props.onPreviousPage);
	    this.handleNextPage = this.handleNextPage.bind(this, props.onNextPage);
	    this.handleLastPage = this.handleLastPage.bind(this, props.onLastPage);
	    this.handleRefresh = this.handleRefresh.bind(this, props.onRefresh);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      pages,
	      data,
	      keyField,
	      pageSize,
	      pageNum,
	      total,
	      selected,
	      mask
	    } = this.props;
	    const totalPage = total % pageSize === 0 ? total / pageSize : parseInt(total / pageSize) + 1; // 计算列宽：
	    // 数字列(type: number)、复选框列(type: checkbox)：60px。
	    // 其他列：提供的按提供的数值(px)。
	    // 表格列

	    const columns = React.Children.map(children, n => {
	      return n.props;
	    }); // 表格头

	    const head = /*#__PURE__*/React.createElement("table", {
	      className: 'head'
	    }, /*#__PURE__*/React.createElement("thead", null, /*#__PURE__*/React.createElement("tr", null, columns.map(col => {
	      if (col.type === 'number') {
	        return /*#__PURE__*/React.createElement("th", {
	          className: 'number',
	          width: 60,
	          name: 'number',
	          key: 'number'
	        }, '#');
	      } else if (col.type === 'checkbox') {
	        const selectAll = data.length > 0 && data.every(n => n[col.field] === true);
	        return /*#__PURE__*/React.createElement("th", {
	          className: 'checkbox',
	          width: 60,
	          name: 'checkbox',
	          key: 'checkbox'
	        }, /*#__PURE__*/React.createElement(CheckBox, {
	          name: col.field,
	          checked: selectAll,
	          onChange: this.handleSelectAll
	        }));
	      } else {
	        return /*#__PURE__*/React.createElement("th", {
	          width: col.width,
	          name: col.field,
	          key: col.field
	        }, col.title);
	      }
	    })))); // 表格体

	    const body = /*#__PURE__*/React.createElement("table", {
	      className: 'body'
	    }, /*#__PURE__*/React.createElement("tbody", null, data.map((row, i) => {
	      return /*#__PURE__*/React.createElement("tr", {
	        className: selected === row[keyField] ? 'selected' : null,
	        "data-id": row[keyField],
	        key: row[keyField],
	        onClick: this.handleClick
	      }, columns.map(col => {
	        if (col.type === 'number') {
	          const value = pageSize * (pageNum - 1) + i + 1;
	          return /*#__PURE__*/React.createElement("td", {
	            className: 'number',
	            width: 60,
	            align: 'center',
	            key: 'number'
	          }, value);
	        } else if (col.type === 'checkbox') {
	          const value = row[col.field] === true;
	          return /*#__PURE__*/React.createElement("td", {
	            className: col.type,
	            width: 60,
	            align: 'center',
	            key: 'number'
	          }, /*#__PURE__*/React.createElement(CheckBox, {
	            checked: value
	          }));
	        } else {
	          const value = col.renderer ? col.renderer(row[col.field], row) : row[col.field];

	          if (col.danger) {
	            return /*#__PURE__*/React.createElement("td", {
	              width: col.width,
	              align: col.align,
	              key: col.field,
	              dangerouslySetInnerHTML: {
	                __html: value
	              }
	            });
	          } else {
	            return /*#__PURE__*/React.createElement("td", {
	              width: col.width,
	              align: col.align,
	              key: col.field
	            }, value);
	          }
	        }
	      }));
	    })));
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('DataGrid', pages && 'pages', className),
	      style: style
	    }, head, /*#__PURE__*/React.createElement("div", {
	      className: 'wrap'
	    }, body), pages && /*#__PURE__*/React.createElement("div", {
	      className: 'page'
	    }, /*#__PURE__*/React.createElement(Select, {
	      className: 'pageSize',
	      name: 'pageSize',
	      options: this.pageSize,
	      value: pageSize.toString(),
	      onChange: this.handleChangePageSize
	    }), /*#__PURE__*/React.createElement(ToolbarSeparator, {
	      className: 'line'
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'backward',
	      title: _t('First Page'),
	      onClick: this.handleFirstPage
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'left-triangle2',
	      title: _t('Previous Page'),
	      onClick: this.handlePreviousPage
	    }), /*#__PURE__*/React.createElement(Input, {
	      className: 'current',
	      value: pageNum,
	      title: _t('Current Page')
	    }), /*#__PURE__*/React.createElement("span", {
	      className: 'slash'
	    }, " / "), /*#__PURE__*/React.createElement(Label, {
	      className: 'totalPage'
	    }, totalPage), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'right-triangle2',
	      title: _t('Next Page'),
	      onClick: this.handleNextPage
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'forward',
	      title: _t('Last Page'),
	      onClick: this.handleLastPage
	    }), /*#__PURE__*/React.createElement(ToolbarSeparator, {
	      className: 'line'
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'refresh',
	      title: _t('Refresh'),
	      onClick: this.handleRefresh
	    }), /*#__PURE__*/React.createElement(ToolbarFiller, null), /*#__PURE__*/React.createElement("div", {
	      className: 'info'
	    }, _t('{{pageSize}} per page, total {{total}} records.', {
	      pageSize,
	      total
	    }))), /*#__PURE__*/React.createElement(LoadMask, {
	      text: _t('Loading...'),
	      show: mask
	    }));
	  }

	  handleClick(onSelect, event) {
	    const keyField = this.props.keyField;
	    const id = event.currentTarget.getAttribute('data-id');
	    const record = this.props.data.filter(n => n[keyField] === id)[0];
	    onSelect && onSelect(record);
	  }

	  handleSelectAll(value, name, event) {
	    const {
	      onSelectAll
	    } = this.props;
	    onSelectAll && onSelectAll(value, name, event);
	  }

	  handleChangePageSize(onChangePageSize, value, event) {
	    const pageSize = parseInt(value);
	    onChangePageSize && onChangePageSize(pageSize, event);
	  }

	  handleFirstPage(onFirstPage, event) {
	    onFirstPage && onFirstPage(event);
	  }

	  handlePreviousPage(onPreviousPage, event) {
	    onPreviousPage && onPreviousPage(event);
	  }

	  handleNextPage(onNextPage, event) {
	    onNextPage && onNextPage(event);
	  }

	  handleLastPage(onLastPage, event) {
	    onLastPage && onLastPage(event);
	  }

	  handleRefresh(onRefresh, event) {
	    onRefresh && onRefresh(event);
	  }

	}

	DataGrid.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: (props, propName, componentName) => {
	    const children = props[propName];
	    Array.isArray(children) && children.forEach(n => {
	      if (n.type !== Column) {
	        return new TypeError(`Invalid prop \`${propName}\` of type \`${n.type.name}\` supplied to \`${componentName}\`, expected \`Column\`.`);
	      }
	    });
	  },
	  pages: propTypes.bool,
	  data: propTypes.array,
	  keyField: propTypes.string,
	  pageSize: propTypes.number,
	  pageNum: propTypes.number,
	  total: propTypes.number,
	  selected: propTypes.string,
	  mask: propTypes.bool,
	  onSelect: propTypes.func,
	  onSelectAll: propTypes.func,
	  onChangePageSize: propTypes.func,
	  onFirstPage: propTypes.func,
	  onPreviousPage: propTypes.func,
	  onNextPage: propTypes.func,
	  onLastPage: propTypes.func,
	  onRefresh: propTypes.func
	};
	DataGrid.defaultProps = {
	  className: null,
	  style: null,
	  children: [],
	  pages: false,
	  data: [],
	  keyField: 'id',
	  pageSize: 20,
	  pageNum: 1,
	  total: 0,
	  selected: null,
	  mask: false,
	  onSelect: null,
	  onSelectAll: null,
	  onChangePageSize: null,
	  onFirstPage: null,
	  onPreviousPage: null,
	  onNextPage: null,
	  onLastPage: null,
	  onRefresh: null
	};

	/**
	 * 表格
	 * @author tengge / https://github.com/tengge1
	 */

	class Table extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("table", _extends({
	      className: bind('Table', className),
	      style: style
	    }, others), children);
	  }

	}

	Table.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	Table.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/**
	 * 表格内容
	 * @author tengge / https://github.com/tengge1
	 */

	class TableBody extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("tbody", _extends({
	      className: bind('TableBody', className),
	      style: style
	    }, others), children);
	  }

	}

	TableBody.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	TableBody.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/**
	 * 表格单元格
	 * @author tengge / https://github.com/tengge1
	 */

	class TableCell extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("td", _extends({
	      className: bind('TableCell', className),
	      style: style
	    }, others), children);
	  }

	}

	TableCell.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	TableCell.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/**
	 * 表格头部
	 * @author tengge / https://github.com/tengge1
	 */

	class TableHead extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("thead", _extends({
	      className: bind('TableHead', className),
	      style: style
	    }, others), children);
	  }

	}

	TableHead.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	TableHead.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/**
	 * 表格行
	 * @author tengge / https://github.com/tengge1
	 */

	class TableRow extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      ...others
	    } = this.props;
	    return /*#__PURE__*/React.createElement("tr", _extends({
	      className: bind('TableRow', className),
	      style: style
	    }, others), children);
	  }

	}

	TableRow.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	TableRow.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 工具栏
	 * @author tengge / https://github.com/tengge1
	 */

	class Toolbar extends React.Component {
	  render() {
	    const {
	      className,
	      style,
	      children,
	      direction
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('Toolbar', direction, className),
	      style: style
	    }, children);
	  }

	}

	Toolbar.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  direction: propTypes.oneOf(['horizontal', 'vertical']),
	  children: propTypes.node
	};
	Toolbar.defaultProps = {
	  className: null,
	  style: null,
	  direction: 'horizontal',
	  children: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 时间轴
	 * @author tengge / https://github.com/tengge1
	 */

	class Timeline extends React.Component {
	  constructor(props) {
	    super(props);
	    this.duration = 120; // 持续时长(秒)

	    this.scale = 30; // 尺寸，1秒=30像素

	    this.time = 0; // 当前时间

	    this.speed = 16; // 当前速度

	    this.canvasRef = React.createRef();
	    this.layersRef = React.createRef();
	    this.leftRef = React.createRef();
	    this.rightRef = React.createRef();
	    this.sliderRef = React.createRef();
	    this.handleAddLayer = this.handleAddLayer.bind(this, props.onAddLayer);
	    this.handleEditLayer = this.handleEditLayer.bind(this, props.onEditLayer);
	    this.handleDeleteLayer = this.handleDeleteLayer.bind(this, props.onDeleteLayer);
	    this.commitDeleteLayer = this.commitDeleteLayer.bind(this);
	    this.handleSelectedLayerChange = this.handleSelectedLayerChange.bind(this, props.onSelectedLayerChange);
	    this.handleBackward = this.handleBackward.bind(this);
	    this.handlePlay = this.handlePlay.bind(this);
	    this.handlePause = this.handlePause.bind(this);
	    this.handleForward = this.handleForward.bind(this);
	    this.handleStop = this.handleStop.bind(this);
	    this.handleClick = this.handleClick.bind(this, props.onClickAnimation);
	    this.handleDoubleClick = this.handleDoubleClick.bind(this, props.onAddAnimation);
	    this.handleRightScroll = this.handleRightScroll.bind(this);
	    this.handleDragStart = this.handleDragStart.bind(this);
	    this.handleDragEnd = this.handleDragEnd.bind(this);
	    this.handleDragEnter = this.handleDragEnter.bind(this);
	    this.handleDragOver = this.handleDragOver.bind(this);
	    this.handleDragLeave = this.handleDragLeave.bind(this);
	    this.handleDrop = this.handleDrop.bind(this, props.onDropAnimation);
	  }

	  render() {
	    const {
	      className,
	      style,
	      animations,
	      selectedLayer,
	      selected
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('Timeline', className),
	      style: style
	    }, /*#__PURE__*/React.createElement(Toolbar, {
	      className: bind('controls', className),
	      style: style
	    }, /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'add',
	      title: _t('Add Layer'),
	      onClick: this.handleAddLayer
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'edit',
	      title: _t('Edit Layer'),
	      onClick: this.handleEditLayer
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'delete',
	      title: _t('Delete Layer'),
	      onClick: this.handleDeleteLayer
	    }), /*#__PURE__*/React.createElement(ToolbarSeparator, null), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'backward',
	      title: _t('Slower'),
	      onClick: this.handleBackward
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'play',
	      title: _t('Play'),
	      onClick: this.handlePlay
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'pause',
	      title: _t('Pause'),
	      onClick: this.handlePause
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'forward',
	      title: _t('Faster'),
	      onClick: this.handleForward
	    }), /*#__PURE__*/React.createElement(IconButton, {
	      icon: 'stop',
	      title: _t('Stop'),
	      onClick: this.handleStop
	    }), /*#__PURE__*/React.createElement(ToolbarSeparator, null), /*#__PURE__*/React.createElement(Label, {
	      className: 'time'
	    }, this.parseTime(this.time)), /*#__PURE__*/React.createElement(Label, {
	      className: 'speed'
	    }, this.parseSpeed(this.speed)), /*#__PURE__*/React.createElement(ToolbarFiller, null), /*#__PURE__*/React.createElement(Label, null, _t('Illustrate: Double-click the area below the timeline to add an animation.'))), /*#__PURE__*/React.createElement("div", {
	      className: "box"
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'timeline'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: "mask"
	    }), /*#__PURE__*/React.createElement("canvas", {
	      ref: this.canvasRef
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'layers'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'left',
	      ref: this.leftRef
	    }, animations.map(layer => {
	      return /*#__PURE__*/React.createElement("div", {
	        className: 'info',
	        key: layer.uuid
	      }, /*#__PURE__*/React.createElement(CheckBox, {
	        name: layer.uuid,
	        checked: selectedLayer === layer.uuid,
	        onChange: this.handleSelectedLayerChange
	      }), /*#__PURE__*/React.createElement(Label, null, layer.layerName));
	    })), /*#__PURE__*/React.createElement("div", {
	      className: 'right',
	      ref: this.rightRef,
	      onScroll: this.handleRightScroll
	    }, animations.map(layer => {
	      return /*#__PURE__*/React.createElement("div", {
	        className: 'layer',
	        droppable: 'true',
	        "data-type": 'layer',
	        "data-id": layer.uuid,
	        onDoubleClick: this.handleDoubleClick,
	        onDragEnter: this.handleDragEnter,
	        onDragOver: this.handleDragOver,
	        onDragLeave: this.handleDragLeave,
	        onDrop: this.handleDrop,
	        key: layer.uuid
	      }, layer.animations.map(animation => {
	        return /*#__PURE__*/React.createElement("div", {
	          className: bind('animation', selected === animation.uuid && 'selected'),
	          title: animation.name,
	          draggable: 'true',
	          droppable: 'false',
	          "data-type": 'animation',
	          "data-id": animation.uuid,
	          "data-pid": layer.uuid,
	          style: {
	            left: animation.beginTime * this.scale + 'px',
	            width: (animation.endTime - animation.beginTime) * this.scale + 'px'
	          },
	          onClick: this.handleClick,
	          onDragStart: this.handleDragStart,
	          onDragEnd: this.handleDragEnd,
	          key: animation.uuid
	        }, animation.name);
	      }));
	    })), /*#__PURE__*/React.createElement("div", {
	      className: "slider",
	      ref: this.sliderRef
	    }))));
	  }

	  componentDidMount() {
	    this.renderTimeline();
	  }

	  renderTimeline() {
	    const {
	      duration,
	      scale
	    } = this;
	    const width = duration * scale; // 画布宽度

	    const scale5 = scale / 5; // 0.2秒像素数

	    const margin = 0; // 时间轴前后间距

	    const canvas = this.canvasRef.current;
	    canvas.style.width = width + margin * 2 + 'px';
	    canvas.width = canvas.clientWidth;
	    canvas.height = 32;
	    const context = canvas.getContext('2d'); // 时间轴背景

	    context.fillStyle = '#fafafa';
	    context.fillRect(0, 0, canvas.width, canvas.height); // 时间轴刻度

	    context.strokeStyle = '#555';
	    context.beginPath();

	    for (let i = margin; i <= width + margin; i += scale) {
	      // 绘制每一秒
	      for (let j = 0; j < 5; j++) {
	        // 绘制每个小格
	        if (j === 0) {
	          // 长刻度
	          context.moveTo(i + scale5 * j, 22);
	          context.lineTo(i + scale5 * j, 30);
	        } else {
	          // 短刻度
	          context.moveTo(i + scale5 * j, 26);
	          context.lineTo(i + scale5 * j, 30);
	        }
	      }
	    }

	    context.stroke(); // 时间轴文字

	    context.font = '12px Arial';
	    context.fillStyle = '#888';

	    for (let i = 0; i <= duration; i += 2) {
	      // 对于每两秒
	      let minute = Math.floor(i / 60);
	      let second = Math.floor(i % 60);
	      let text = (minute > 0 ? minute + ':' : '') + ('0' + second).slice(-2);

	      if (i === 0) {
	        context.textAlign = 'left';
	      } else if (i === duration) {
	        context.textAlign = 'right';
	      } else {
	        context.textAlign = 'center';
	      }

	      context.fillText(text, margin + i * scale, 16);
	    }
	  }

	  handleAddLayer(onAddLayer, event) {
	    onAddLayer && onAddLayer(event);
	  }

	  handleEditLayer(onEditLayer, event) {
	    const {
	      selectedLayer
	    } = this.props;
	    onEditLayer && onEditLayer(selectedLayer, event);
	  }

	  handleDeleteLayer(onDeleteLayer, event) {
	    const {
	      selectedLayer
	    } = this.props;
	    onDeleteLayer && onDeleteLayer(selectedLayer, event);
	  }

	  commitDeleteLayer() {}

	  handleSelectedLayerChange(onSelectedLayerChange, value, name, event) {
	    onSelectedLayerChange && onSelectedLayerChange(value ? name : null, event);
	  }

	  handleBackward(event) {}

	  handlePlay(event) {}

	  handlePause(event) {}

	  handleForward(event) {}

	  handleStop(event) {}

	  handleClick(onClickAnimation, event) {
	    const type = event.target.getAttribute('data-type');

	    if (type !== 'animation') {
	      return;
	    }

	    const pid = event.target.getAttribute('data-pid');
	    const id = event.target.getAttribute('data-id');
	    onClickAnimation && onClickAnimation(id, pid, event);
	  }

	  handleDoubleClick(onAddAnimation, event) {
	    const type = event.target.getAttribute('data-type');

	    if (type !== 'layer') {
	      return;
	    }

	    const layerID = event.target.getAttribute('data-id');
	    const beginTime = event.nativeEvent.offsetX / this.scale;
	    const endTime = beginTime + 2;
	    onAddAnimation && onAddAnimation(layerID, beginTime, endTime, event);
	  }

	  handleRightScroll(scroll) {
	    let left = this.leftRef.current;
	    let canvas = this.canvasRef.current;
	    left.scrollTop = event.target.scrollTop;
	    canvas.style.left = `${100 - event.target.scrollLeft}px`;
	  }

	  handleDragStart(event) {
	    const type = event.target.getAttribute('data-type');

	    if (type !== 'animation') {
	      return;
	    }

	    const id = event.target.getAttribute('data-id');
	    const pid = event.target.getAttribute('data-pid');
	    event.nativeEvent.dataTransfer.setData('id', id);
	    event.nativeEvent.dataTransfer.setData('pid', pid);
	    event.nativeEvent.dataTransfer.setData('offsetX', event.nativeEvent.offsetX);
	  }

	  handleDragEnd(event) {
	    event.nativeEvent.dataTransfer.clearData();
	  }

	  handleDragEnter(event) {
	    event.preventDefault();
	  }

	  handleDragOver(event) {
	    event.preventDefault();
	  }

	  handleDragLeave(event) {
	    event.preventDefault();
	  }

	  handleDrop(onDropAnimation, event) {
	    const type = event.target.getAttribute('data-type');

	    if (type !== 'layer') {
	      return;
	    }

	    const id = event.nativeEvent.dataTransfer.getData('id');
	    const oldLayerID = event.nativeEvent.dataTransfer.getData('pid');
	    const offsetX = event.nativeEvent.dataTransfer.getData('offsetX');
	    const newLayerID = event.target.getAttribute('data-id');
	    const beginTime = (event.nativeEvent.offsetX - offsetX) / this.scale;
	    onDropAnimation && onDropAnimation(id, oldLayerID, newLayerID, beginTime, event);
	  }

	  parseTime(time) {
	    let minute = `0${parseInt(time / 60)}`;
	    let second = `0${parseInt(time % 60)}`;
	    return `${minute.substr(minute.length - 2, 2)}:${second.substr(second.length - 2, 2)}`;
	  }

	  parseSpeed(speed) {
	    return speed;
	  }

	}

	Timeline.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  animations: propTypes.array,
	  selectedLayer: propTypes.string,
	  selected: propTypes.string,
	  onAddLayer: propTypes.func,
	  onEditLayer: propTypes.func,
	  onDeleteLayer: propTypes.func,
	  onSelectedLayerChange: propTypes.func,
	  onAddAnimation: propTypes.func,
	  onDropAnimation: propTypes.func,
	  onClickAnimation: propTypes.func
	};
	Timeline.defaultProps = {
	  className: null,
	  style: null,
	  animations: [],
	  selectedLayer: null,
	  selected: null,
	  onAddLayer: null,
	  onEditLayer: null,
	  onDeleteLayer: null,
	  onSelectedLayerChange: null,
	  onAddAnimation: null,
	  onDropAnimation: null,
	  onClickAnimation: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 树
	 * @author tengge / https://github.com/tengge1
	 */

	class Tree extends React.Component {
	  constructor(props) {
	    super(props);
	    this.treeRef = React.createRef();
	    const {
	      onExpand,
	      onSelect,
	      onCheck,
	      onDoubleClick,
	      onDrop
	    } = this.props;
	    this.handleExpandNode = this.handleExpandNode.bind(this, onExpand);
	    this.handleClick = this.handleClick.bind(this, onSelect);
	    this.handleCheck = this.handleCheck.bind(this, onCheck);
	    this.handleDoubleClick = this.handleDoubleClick.bind(this, onDoubleClick);
	    this.handleClickIcon = this.handleClickIcon.bind(this, props.onClickIcon);
	    this.handleDrag = this.handleDrag.bind(this);
	    this.handleDragStart = this.handleDragStart.bind(this);
	    this.handleDragOver = this.handleDragOver.bind(this);
	    this.handleDragLeave = this.handleDragLeave.bind(this);
	    this.handleDrop = this.handleDrop.bind(this, onDrop);
	  }

	  render() {
	    const {
	      className,
	      style,
	      data,
	      mask
	    } = this.props; // 创建节点

	    let list = [];
	    Array.isArray(data) && data.forEach(n => {
	      list.push(this.createNode(n));
	    });
	    return /*#__PURE__*/React.createElement("div", {
	      className: 'TreeWrap'
	    }, /*#__PURE__*/React.createElement("ul", {
	      className: bind('Tree', className),
	      style: style,
	      ref: this.treeRef
	    }, list), /*#__PURE__*/React.createElement(LoadMask, {
	      text: _t('Loading...'),
	      show: mask
	    }));
	  }

	  createNode(data) {
	    // TODO: leaf应该根据数据上的left属性判断，而不是children。
	    const leaf = (!data.children || data.children.length === 0) && data.leaf !== false;
	    const children = data.children && data.children.length > 0 ? /*#__PURE__*/React.createElement("ul", {
	      className: bind('sub', data.expanded ? null : 'collpase')
	    }, data.children.map(n => {
	      return this.createNode(n);
	    })) : null;
	    let checkbox = null;

	    if (data.checked === true || data.checked === false) {
	      checkbox = /*#__PURE__*/React.createElement(CheckBox, {
	        name: data.value,
	        checked: data.checked,
	        onChange: this.handleCheck
	      });
	    }

	    return /*#__PURE__*/React.createElement("li", {
	      className: bind('node', this.props.selected === data.value && 'selected'),
	      value: data.value,
	      key: data.value,
	      onClick: this.handleClick,
	      onDoubleClick: this.handleDoubleClick,
	      draggable: 'true',
	      droppable: 'true',
	      onDrag: this.handleDrag,
	      onDragStart: this.handleDragStart,
	      onDragOver: this.handleDragOver,
	      onDragLeave: this.handleDragLeave,
	      onDrop: this.handleDrop
	    }, /*#__PURE__*/React.createElement("i", {
	      className: bind('expand', leaf ? null : data.expanded ? 'minus' : 'plus'),
	      value: data.value,
	      onClick: this.handleExpandNode
	    }), checkbox, /*#__PURE__*/React.createElement("i", {
	      className: bind('type', leaf ? 'leaf' : data.expanded ? 'open' : 'close')
	    }), /*#__PURE__*/React.createElement("a", {
	      href: 'javascript:;'
	    }, data.text), data.icons && data.icons.map(n => {
	      return /*#__PURE__*/React.createElement(Icon, {
	        className: 'control',
	        name: n.name,
	        value: data.value,
	        icon: n.icon,
	        title: n.title,
	        key: n.name,
	        onClick: this.handleClickIcon
	      });
	    }), leaf ? null : children);
	  } // 暂时屏蔽树节点动画，有bug。
	  // componentDidUpdate() {
	  //     let tree = this.treeRef.current;
	  //     // 将每棵子树设置高度，以便显示动画
	  //     this.handleSetTreeHeight(tree);
	  // }
	  // handleSetTreeHeight(node) {
	  //     if (node.children.length === 0) {
	  //         return;
	  //     }
	  //     let height = 0;
	  //     for (let i = 0; i < node.children.length; i++) {
	  //         let child = node.children[i];
	  //         height += child.offsetHeight;
	  //         this.handleSetTreeHeight(child);
	  //     }
	  //     if (node.classList.contains('sub')) { // 子树
	  //         node.style.height = `${height}px`;
	  //     }
	  // }

	  /**
	   * 将某个节点滚动到视野范围内
	   * @param {*} value 节点的值
	   */


	  scrollToView(value) {
	    let root = this.treeRef.current;

	    if (!root) {
	      return;
	    }

	    let node = this.findNode(value, root);

	    if (!node) {
	      return;
	    }

	    const treeHeight = root.clientHeight;
	    const treeTop = root.scrollTop;
	    const nodeHeight = node.clientHeight;
	    const offsetTop = node.offsetTop;
	    const minScrollTop = offsetTop + nodeHeight - treeHeight;
	    const maxScrollTop = offsetTop;

	    if (treeTop >= minScrollTop && treeTop <= maxScrollTop) {
	      // 不需要滚动
	      return;
	    } else if (treeTop < minScrollTop) {
	      root.scrollTop = minScrollTop;
	    } else if (treeTop > maxScrollTop) {
	      root.scrollTop = maxScrollTop;
	    }
	  }

	  findNode(value, node) {
	    const _value = node.getAttribute('value');

	    if (value === _value) {
	      return node;
	    }

	    for (let child of node.children) {
	      const _node = this.findNode(value, child);

	      if (_node) {
	        return _node;
	      }
	    }
	  }

	  handleExpandNode(onExpand, event) {
	    event.stopPropagation();
	    const value = event.target.getAttribute('value');
	    onExpand && onExpand(value, event);
	  }

	  handleClick(onSelect, event) {
	    event.stopPropagation();
	    let value = event.target.getAttribute('value');

	    if (value) {
	      onSelect && onSelect(value, event);
	    }
	  }

	  handleCheck(onCheck, value, name, event) {
	    event.stopPropagation();
	    onCheck && onCheck(value, name, event);
	  }

	  handleDoubleClick(onDoubleClick, event) {
	    const value = event.target.getAttribute('value');

	    if (value) {
	      onDoubleClick && onDoubleClick(value, event);
	    }
	  }

	  handleClickIcon(onClickIcon, name, event) {
	    const value = event.target.getAttribute('value');
	    event.stopPropagation();
	    onClickIcon && onClickIcon(value, name, event);
	  } // --------------------- 拖拽事件 ---------------------------


	  handleDrag(event) {
	    event.stopPropagation();
	    this.currentDrag = event.currentTarget;
	  }

	  handleDragStart(event) {
	    event.stopPropagation();
	    event.dataTransfer.setData('text', 'foo');
	  }

	  handleDragOver(event) {
	    event.preventDefault();
	    event.stopPropagation();
	    let target = event.currentTarget;

	    if (target === this.currentDrag) {
	      return;
	    }

	    let area = event.nativeEvent.offsetY / target.clientHeight;

	    if (area < 0.25) {
	      target.classList.add('dragTop');
	    } else if (area > 0.75) {
	      target.classList.add('dragBottom');
	    } else {
	      target.classList.add('drag');
	    }
	  }

	  handleDragLeave(event) {
	    event.preventDefault();
	    event.stopPropagation();
	    let target = event.currentTarget;

	    if (target === this.currentDrag) {
	      return;
	    }

	    target.classList.remove('dragTop');
	    target.classList.remove('dragBottom');
	    target.classList.remove('drag');
	  }

	  handleDrop(onDrop, event) {
	    event.preventDefault();
	    event.stopPropagation();
	    let target = event.currentTarget;

	    if (target === this.currentDrag) {
	      return;
	    }

	    target.classList.remove('dragTop');
	    target.classList.remove('dragBottom');
	    target.classList.remove('drag');

	    if (typeof onDrop === 'function') {
	      const area = event.nativeEvent.offsetY / target.clientHeight;
	      const currentValue = this.currentDrag.getAttribute('value');

	      if (area < 0.25) {
	        // 放在当前元素前面
	        onDrop(currentValue, // 拖动要素
	        target.parentNode.parentNode.getAttribute('value'), // 新位置父级
	        target.getAttribute('value') // 新位置索引
	        ); // 拖动, 父级, 索引
	      } else if (area > 0.75) {
	        // 放在当前元素后面
	        onDrop(currentValue, target.parentNode.parentNode.getAttribute('value'), !target.nextSibling ? null : target.nextSibling.getAttribute('value') // target.nextSibling为null，说明是最后一个位置
	        );
	      } else {
	        // 成为该元素子级
	        onDrop(currentValue, target.getAttribute('value'), null);
	      }
	    }
	  }

	}

	Tree.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  data: propTypes.array,
	  mask: propTypes.bool,
	  selected: propTypes.string,
	  onExpand: propTypes.func,
	  onSelect: propTypes.func,
	  onCheck: propTypes.func,
	  onDoubleClick: propTypes.func,
	  onClickIcon: propTypes.func,
	  onDrop: propTypes.func
	};
	Tree.defaultProps = {
	  className: null,
	  style: null,
	  data: [],
	  mask: false,
	  selected: null,
	  onExpand: null,
	  onSelect: null,
	  onCheck: null,
	  onDoubleClick: null,
	  onClickIcon: null,
	  onDrop: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 窗口
	 */

	class Window extends React.Component {
	  constructor(props) {
	    super(props);
	    this.dom = React.createRef();
	    this.isDown = false;
	    this.offsetX = 0;
	    this.offsetY = 0;
	    this.handleMouseDown = this.handleMouseDown.bind(this);
	    this.handleMouseMove = this.handleMouseMove.bind(this);
	    this.handleMouseUp = this.handleMouseUp.bind(this);
	    this.handleClose = this.handleClose.bind(this, props.onClose);
	  }

	  render() {
	    const {
	      className,
	      style,
	      title,
	      children,
	      hidden,
	      mask
	    } = this.props;
	    let _children = null;

	    if (children && Array.isArray(children)) {
	      _children = children;
	    } else if (children) {
	      _children = [children];
	    }

	    const content = _children.filter(n => {
	      return n.type === Content;
	    })[0];

	    const buttons = _children.filter(n => {
	      return n.type === Buttons;
	    })[0];

	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('WindowMask', mask && 'mask', hidden && 'hidden')
	    }, /*#__PURE__*/React.createElement("div", {
	      className: bind('Window', className),
	      style: style,
	      ref: this.dom
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'wrap'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'title',
	      onMouseDown: this.handleMouseDown
	    }, /*#__PURE__*/React.createElement("span", null, title), /*#__PURE__*/React.createElement("div", {
	      className: 'controls'
	    }, /*#__PURE__*/React.createElement("i", {
	      className: 'iconfont icon-close icon',
	      onClick: this.handleClose
	    }))), /*#__PURE__*/React.createElement("div", {
	      className: 'content'
	    }, content && content.props.children), buttons && /*#__PURE__*/React.createElement("div", {
	      className: 'buttons'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: 'button-wrap'
	    }, buttons && buttons.props.children)))));
	  }

	  handleMouseDown(event) {
	    this.isDown = true;
	    var dom = this.dom.current;
	    var left = dom.style.left === '' ? 0 : parseInt(dom.style.left.replace('px', ''));
	    var top = dom.style.top === '' ? 0 : parseInt(dom.style.top.replace('px', ''));
	    this.offsetX = event.clientX - left;
	    this.offsetY = event.clientY - top;
	  }

	  handleMouseMove(event) {
	    if (!this.isDown) {
	      return;
	    }

	    var dx = event.clientX - this.offsetX;
	    var dy = event.clientY - this.offsetY;
	    var dom = this.dom.current;
	    dom.style.left = `${dx}px`;
	    dom.style.top = `${dy}px`;
	  }

	  handleMouseUp() {
	    this.isDown = false;
	    this.offsetX = 0;
	    this.offsetY = 0;
	  }

	  handleClose(onClose, event) {
	    onClose && onClose(event);
	  }

	  componentDidMount() {
	    document.body.addEventListener('mousemove', this.handleMouseMove);
	    document.body.addEventListener('mouseup', this.handleMouseUp);
	  }

	  componentWillUnmount() {
	    document.body.removeEventListener('mousemove', this.handleMouseMove);
	    document.body.removeEventListener('mouseup', this.handleMouseUp);
	  }

	}

	Window.show = function () {};

	Window.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  title: propTypes.string,
	  children: propTypes.node,
	  hidden: propTypes.bool,
	  mask: propTypes.bool,
	  onClose: propTypes.func
	};
	Window.defaultProps = {
	  className: null,
	  style: null,
	  title: 'Window',
	  children: null,
	  hidden: false,
	  mask: true,
	  onClose: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 提示框
	 */

	class Alert extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleOK = this.handleOK.bind(this, props.onOK);
	    this.handleClose = this.handleClose.bind(this, props.onClose);
	  }

	  render() {
	    const {
	      className,
	      style,
	      title,
	      children,
	      hidden,
	      mask,
	      okText
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Window, {
	      className: bind('Alert', className),
	      style: style,
	      title: title,
	      hidden: hidden,
	      mask: mask,
	      onClose: this.handleClose
	    }, /*#__PURE__*/React.createElement(Content, null, children), /*#__PURE__*/React.createElement(Buttons, null, /*#__PURE__*/React.createElement(Button, {
	      onClick: this.handleOK
	    }, okText)));
	  }

	  handleOK(onOK, event) {
	    onOK && onOK(event);
	  }

	  handleClose(onClose, event) {
	    onClose && onClose(event);
	  }

	}

	Alert.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  title: propTypes.string,
	  children: propTypes.node,
	  hidden: propTypes.bool,
	  mask: propTypes.bool,
	  okText: propTypes.string,
	  onOK: propTypes.func,
	  onClose: propTypes.func
	};
	Alert.defaultProps = {
	  className: null,
	  style: null,
	  title: 'Message',
	  children: null,
	  hidden: false,
	  mask: false,
	  okText: 'OK',
	  onOK: null,
	  onClose: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 询问框
	 */

	class Confirm extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleOK = this.handleOK.bind(this, props.onOK);
	    this.handleCancel = this.handleCancel.bind(this, props.onCancel);
	    this.handleClose = this.handleClose.bind(this, props.onClose);
	  }

	  render() {
	    const {
	      className,
	      style,
	      title,
	      children,
	      hidden,
	      mask,
	      okText,
	      cancelText
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Window, {
	      className: bind('Confirm', className),
	      style: style,
	      title: title,
	      hidden: hidden,
	      mask: mask,
	      onClose: this.handleClose
	    }, /*#__PURE__*/React.createElement(Content, null, children), /*#__PURE__*/React.createElement(Buttons, null, /*#__PURE__*/React.createElement(Button, {
	      onClick: this.handleOK
	    }, okText), /*#__PURE__*/React.createElement(Button, {
	      onClick: this.handleCancel
	    }, cancelText)));
	  }

	  handleOK(onOK, event) {
	    onOK && onOK(event);
	  }

	  handleCancel(onCancel, event) {
	    onCancel && onCancel(event);
	  }

	  handleClose(onClose, event) {
	    onClose && onClose(event);
	  }

	}

	Confirm.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  title: propTypes.string,
	  children: propTypes.node,
	  hidden: propTypes.bool,
	  mask: propTypes.bool,
	  okText: propTypes.string,
	  cancelText: propTypes.string,
	  onOK: propTypes.func,
	  onCancel: propTypes.func,
	  onClose: propTypes.func
	};
	Confirm.defaultProps = {
	  className: null,
	  style: null,
	  title: 'Confirm',
	  children: null,
	  hidden: false,
	  mask: false,
	  okText: 'OK',
	  cancelText: 'Cancel',
	  onOK: null,
	  onCancel: null,
	  onClose: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 提示窗
	 */

	class Message extends React.Component {
	  constructor(props) {
	    super(props);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children,
	      type
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('Message', type, className),
	      style: style
	    }, /*#__PURE__*/React.createElement("i", {
	      className: bind('iconfont', `icon-${type}`)
	    }), /*#__PURE__*/React.createElement("p", {
	      className: 'content'
	    }, children));
	  }

	}

	Message.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node,
	  type: propTypes.oneOf(['info', 'success', 'warn', 'error'])
	};
	Message.defaultProps = {
	  className: null,
	  style: null,
	  children: null,
	  type: 'info'
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 图片查看器
	 */

	class Photo extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this, props.onClick);
	    this.handleClickImage = this.handleClickImage.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      url
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('PhotoMark', className),
	      style: style,
	      onClick: this.handleClick
	    }, /*#__PURE__*/React.createElement("img", {
	      src: url,
	      onClick: this.handleClickImage
	    }));
	  }

	  handleClick(onClick, event) {
	    onClick && onClick(event);
	  }

	  handleClickImage(event) {
	    event.stopPropagation();
	  }

	}

	Photo.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  url: propTypes.string,
	  onClick: propTypes.func
	};
	Photo.defaultProps = {
	  className: null,
	  style: null,
	  url: null,
	  onClick: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 弹窗输入框
	 */

	class Prompt extends React.Component {
	  constructor(props) {
	    super(props);
	    this.state = {
	      value: props.value
	    };
	    this.handleOK = this.handleOK.bind(this, props.onOK);
	    this.handleClose = this.handleClose.bind(this, props.onClose);
	    this.handleChange = this.handleChange.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      title,
	      content,
	      hidden,
	      mask,
	      okText
	    } = this.props;
	    return /*#__PURE__*/React.createElement(Window, {
	      className: bind('Prompt', className),
	      style: style,
	      title: title,
	      hidden: hidden,
	      mask: mask,
	      onClose: this.handleClose
	    }, /*#__PURE__*/React.createElement(Content, null, content, /*#__PURE__*/React.createElement(Input, {
	      value: this.state.value,
	      onChange: this.handleChange
	    })), /*#__PURE__*/React.createElement(Buttons, null, /*#__PURE__*/React.createElement(Button, {
	      onClick: this.handleOK
	    }, okText)));
	  }

	  handleOK(onOK, event) {
	    onOK && onOK(this.state.value, event);
	  }

	  handleClose(onClose, event) {
	    onClose && onClose(event);
	  }

	  handleChange(value) {
	    this.setState({
	      value
	    });
	  }

	}

	Prompt.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  title: propTypes.string,
	  content: propTypes.node,
	  value: propTypes.string,
	  hidden: propTypes.bool,
	  mask: propTypes.bool,
	  okText: propTypes.string,
	  onOK: propTypes.func,
	  onClose: propTypes.func
	};
	Prompt.defaultProps = {
	  className: null,
	  style: null,
	  title: 'Prompt',
	  content: null,
	  value: '',
	  hidden: false,
	  mask: false,
	  okText: 'OK',
	  onOK: null,
	  onClose: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 提示窗
	 */

	class Toast extends React.Component {
	  constructor(props) {
	    super(props);
	  }

	  render() {
	    const {
	      className,
	      style,
	      children
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: 'ToastMark'
	    }, /*#__PURE__*/React.createElement("div", {
	      className: bind('Toast', className),
	      style: style
	    }, children));
	  }

	}

	Toast.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  children: propTypes.node
	};
	Toast.defaultProps = {
	  className: null,
	  style: null,
	  children: null
	};

	/*
	 * Copyright 2017-2020 The ShadowEditor Authors. All rights reserved.
	 *
	 * Use of this source code is governed by a MIT-style
	 * license that can be found in the LICENSE file.
	 * 
	 * For more information, please visit: https://github.com/tengge1/ShadowEditor
	 * You can also visit: https://gitee.com/tengge1/ShadowEditor
	 */
	/**
	 * 视频查看器
	 */

	class Video extends React.Component {
	  constructor(props) {
	    super(props);
	    this.handleClick = this.handleClick.bind(this, props.onClick);
	    this.handleClickImage = this.handleClickVideo.bind(this);
	  }

	  render() {
	    const {
	      className,
	      style,
	      url
	    } = this.props;
	    return /*#__PURE__*/React.createElement("div", {
	      className: bind('VideoMark', className),
	      style: style,
	      onClick: this.handleClick
	    }, /*#__PURE__*/React.createElement("video", {
	      src: url,
	      autoPlay: 'autoplay',
	      controls: 'controls',
	      onClick: this.handleClickVideo
	    }));
	  }

	  handleClick(onClick, event) {
	    onClick && onClick(event);
	  }

	  handleClickVideo(event) {
	    event.stopPropagation();
	  }

	}

	Video.propTypes = {
	  className: propTypes.string,
	  style: propTypes.object,
	  url: propTypes.string,
	  onClick: propTypes.func
	};
	Video.defaultProps = {
	  className: null,
	  style: null,
	  url: null,
	  onClick: null
	};

	exports.AbsoluteLayout = AbsoluteLayout;
	exports.Accordion = Accordion;
	exports.AccordionLayout = AccordionLayout;
	exports.Alert = Alert;
	exports.BorderLayout = BorderLayout;
	exports.Button = Button;
	exports.ButtonProperty = ButtonProperty;
	exports.Buttons = Buttons;
	exports.ButtonsProperty = ButtonsProperty;
	exports.Canvas = Canvas;
	exports.CheckBox = CheckBox;
	exports.CheckBoxProperty = CheckBoxProperty;
	exports.ColorProperty = ColorProperty;
	exports.Column = Column;
	exports.Confirm = Confirm;
	exports.Content = Content;
	exports.ContextMenu = ContextMenu;
	exports.DataGrid = DataGrid;
	exports.DisplayProperty = DisplayProperty;
	exports.Form = Form;
	exports.FormControl = FormControl;
	exports.HBoxLayout = HBoxLayout;
	exports.Icon = Icon;
	exports.IconButton = IconButton;
	exports.IconMenuButton = IconMenuButton;
	exports.Image = Image;
	exports.ImageButton = ImageButton;
	exports.ImageList = ImageList;
	exports.ImageSelector = ImageSelector;
	exports.ImageUploader = ImageUploader;
	exports.Input = Input;
	exports.IntegerProperty = IntegerProperty;
	exports.Item = Item;
	exports.Label = Label;
	exports.LinkButton = LinkButton;
	exports.LoadMask = LoadMask;
	exports.Menu = Menu;
	exports.MenuBar = MenuBar;
	exports.MenuBarFiller = MenuBarFiller;
	exports.MenuItem = MenuItem;
	exports.MenuItemSeparator = MenuItemSeparator;
	exports.MenuTab = MenuTab;
	exports.Message = Message;
	exports.NumberProperty = NumberProperty;
	exports.Panel = Panel;
	exports.Photo = Photo;
	exports.Prompt = Prompt;
	exports.PropertyGrid = PropertyGrid;
	exports.PropertyGroup = PropertyGroup;
	exports.Radio = Radio;
	exports.Row = Row;
	exports.Rows = Rows;
	exports.SVG = SVG;
	exports.SearchField = SearchField;
	exports.Select = Select;
	exports.SelectProperty = SelectProperty;
	exports.TabLayout = TabLayout;
	exports.Table = Table;
	exports.TableBody = TableBody;
	exports.TableCell = TableCell;
	exports.TableHead = TableHead;
	exports.TableRow = TableRow;
	exports.TextArea = TextArea;
	exports.TextProperty = TextProperty;
	exports.Timeline = Timeline;
	exports.Toast = Toast;
	exports.Toggle = Toggle;
	exports.Toolbar = Toolbar;
	exports.ToolbarFiller = ToolbarFiller;
	exports.ToolbarSeparator = ToolbarSeparator;
	exports.Tree = Tree;
	exports.VBoxLayout = VBoxLayout;
	exports.Video = Video;
	exports.Window = Window;

	Object.defineProperty(exports, '__esModule', { value: true });

})));
