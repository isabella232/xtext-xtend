/*******************************************************************************
 * Copyright (c) 2011 itemis AG (http://www.itemis.eu) and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *******************************************************************************/
package org.eclipse.xtend.core.tests.validation;

import static org.eclipse.xtend.core.validation.IssueCodes.*;
import static org.eclipse.xtend.core.xtend.XtendPackage.Literals.*;
import static org.eclipse.xtext.xbase.validation.IssueCodes.*;

import org.eclipse.xtend.core.tests.AbstractXtendTestCase;
import org.eclipse.xtend.core.xtend.XtendClass;
import org.eclipse.xtext.junit4.validation.ValidationTestHelper;
import org.junit.Ignore;
import org.junit.Test;

import com.google.inject.Inject;

/**
 * @author Jan Koehnlein - Initial contribution and API
 * @author Holger Schill
 * @author Sebastian Zarnekow
 */
public class OverrideValidationTest extends AbstractXtendTestCase {

	@Inject
	private ValidationTestHelper helper;

	//TODO override declarations in interfaces

	@Test public void testDuplicateMethod_0() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def bar(int x) {true} def bar(int x) {false} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, DUPLICATE_METHOD, "duplicate");
	}

	@Test public void testDuplicateMethod_1() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def bar(String x) {true} def bar(int x) {false} }");
		helper.assertNoError(xtendClass, DUPLICATE_METHOD);
	}

	@Test public void testDuplicateMethod_2() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def bar(String x) {true} def bar(String x, int x) {false} }");
		helper.assertNoError(xtendClass, DUPLICATE_METHOD);
	}

	@Test public void testDuplicateMethod_3() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def bar(java.util.List<String> x) {true} def bar(java.util.List<Integer> x) {false} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, DUPLICATE_METHOD, "erasure", "List)",
				"List<String");
		helper.assertError(xtendClass.getMembers().get(1), XTEND_FUNCTION, DUPLICATE_METHOD, "erasure", "List)",
				"List<Integer");
	}

	@Test public void testDuplicateMethod_4() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def <T> bar(T t) { '' } def <T> bar(T t) { 1 } }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, DUPLICATE_METHOD, "duplicate", "bar(T)");
		helper.assertError(xtendClass.getMembers().get(1), XTEND_FUNCTION, DUPLICATE_METHOD, "duplicate", "bar(T)");
	}

	@Test public void testDuplicateMethod_5() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def <T> bar(T t) { '' } def <V> bar(V v) { 1 } }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, DUPLICATE_METHOD, "erasure", "Object)", "T");
		helper.assertError(xtendClass.getMembers().get(1), XTEND_FUNCTION, DUPLICATE_METHOD, "erasure", "Object)", "V");
	}

	@Test public void testDuplicateMethod_6() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def <T> bar(CharSequence seq) { '' } def <V extends CharSequence> bar(V v) { 1 } }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, DUPLICATE_METHOD, "erasure", "CharSequence)");
		helper.assertError(xtendClass.getMembers().get(1), XTEND_FUNCTION, DUPLICATE_METHOD, "erasure",
				"CharSequence)", "bar(V)");
	}

	@Test public void testDuplicateMethod_7() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def <T extends CharSequence> bar(T t) { '' } def <V extends String> bar(V v) { 1 } }");
		helper.assertNoErrors(xtendClass);
	}

	@Test public void testOverrideGenericMethod_1() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <RenamedT1> getValue1(List<RenamedT1> t) {}" +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_2() throws Exception {
		XtendClass xtendClass = clazz(" abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
								    "override <T2> getValue2(T2[] t) {} " +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_3() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T3> getValue3(List<T3> t) {} " +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_4() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
								    "override <T3> getValue4(List<T3[]> t) {} " +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_5() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
								    "override <T3> getValue5(List<List<T3>[]> t) {} " +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_6() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
								    "override <T3> getValue6(List<? extends T3> t) {} " +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_7() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
								    "override <T3> getValue7(List<? super T3> t) {} " +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_8() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T1, T2 extends T1> getValue8(List<T1> t, List<T2> t2) {} " +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	@Test public void testOverrideGenericMethod_9() throws Exception {
		XtendClass xtendClass = clazz(" import java.util.List import java.io.Serializable abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T2, T1 extends Serializable & CharSequence> getValue9(List<T1> t) {}"+
									"}");
		helper.assertNoErrors(xtendClass);
	}

	@Test public void testOverrideGenericMethod_10() throws Exception {
		XtendClass xtendClass = clazz(" abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T extends String> foo1() {}"+
									"}");
		helper.assertError(xtendClass, XTEND_FUNCTION, DUPLICATE_METHOD);
	}

	@Test public void testOverrideGenericMethod_11() throws Exception {
		XtendClass xtendClass = clazz(" abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T extends CharSequence> foo1() {}"+
									"}");
		helper.assertNoErrors(xtendClass);
	}

	@Test public void testOverrideGenericMethod_12() throws Exception {
		XtendClass xtendClass = clazz(" abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <Unused> void foo2(T t, (T)=>void proc){} "+
									"}");
		helper.assertNoErrors(xtendClass);
	}
	
	@Test public void testOverrideGenericMethod_13() throws Exception {
		XtendClass xtendClass = clazz("abstract class Foo extends test.GenericSuperTypeClass<String> {  " +
									"override <C extends Comparable<C>> C getComparable(){ null } "+
									"}");
		helper.assertNoErrors(xtendClass);
	}
	
	@Test public void testOverrideGenericMethod_14() throws Exception {
		XtendClass xtendClass = clazz("abstract class Foo extends test.GenericSuperTypeClass<String> {  " +
									"override <X extends Comparable<X>> void useComparable(X x){} "+
									"}");
		helper.assertNoErrors(xtendClass);
	}
	
	@Test public void testOverrideGenericMethod_15() throws Exception {
		XtendClass xtendClass = clazz(" abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T> void foo3(T t, (T)=>void proc){} "+
									"}");
		helper.assertNoErrors(xtendClass);
	}

	@Test public void testOverrideReturnType() throws Exception {
		XtendClass xtendClass = clazz("abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T> T getSomething(T t){} "+
									"}");
		helper.assertNoErrors(xtendClass);
	}

	@Ignore("Make this one green when https://bugs.eclipse.org/bugs/show_bug.cgi?id=376037 is fixed")
	@Test public void testOverrideReturnType_1() throws Exception {
		XtendClass xtendClass = clazz("import java.util.List import java.io.Serializable abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T1> T1[] getValue1(List<T1> t) {}" +
									"}");
		helper.assertNoErrors(xtendClass);
	}

	@Ignore("Make this one green when https://bugs.eclipse.org/bugs/show_bug.cgi?id=376037 is fixed")
	@Test public void testOverrideReturnType_2() throws Exception {
		XtendClass xtendClass = clazz("import java.util.List import java.io.Serializable abstract class Foo<T> extends test.GenericSuperTypeClass<T> {  " +
									"override <T3> List<T3> getValue3(List<T3> t) {}" +
									"}");
		helper.assertNoErrors(xtendClass);
	}
	
	@Test public void testOverrideReturnType_3() throws Exception {
		XtendClass xtendClass = clazz("abstract class Foo extends test.GenericSuperTypeClass<Comparable<String>> {  " +
									"override String getTypeParamValue(){ null } "+
									"}");
		helper.assertNoErrors(xtendClass);
	}

	@Ignore("This should issue a warning and not an error")
	@Test public void testOverrideReturnType_4() throws Exception {
		XtendClass xtendClass = clazz("abstract class Foo extends test.GenericSuperTypeClass<Integer> {  " +
									"override String getComparable(){ null }" +
									"}");
		helper.assertNoErrors(xtendClass);
	}

	@Test public void testObsoleteOverride_0() throws Exception {
		XtendClass xtendClass = clazz("class Foo { override bar() {true} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, OBSOLETE_OVERRIDE);
	}

	@Test public void testObsoleteOverride_1() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override bar() {true} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, OBSOLETE_OVERRIDE);
	}

	@Test public void testObsoleteOverride_2() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override privateMethod() {true}}");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, OBSOLETE_OVERRIDE);
	}

	@Test public void testMissingOverride_0() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { def string() {null} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, MISSING_OVERRIDE);
	}

	@Test public void testMissingOverride_1() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { def string(int i) { null} }");
		helper.assertNoError(xtendClass.getMembers().get(0), MISSING_OVERRIDE);
	}

	@Test public void testMissingOverride_2() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { def string(String s) {null} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, MISSING_OVERRIDE);
	}

	@Test public void testMissingOverride_3() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { def object(String s) {null} }");
		helper.assertNoError(xtendClass.getMembers().get(0), MISSING_OVERRIDE);
	}

	@Test public void testMissingOverride_4() throws Exception {
		XtendClass xtendClass = clazz("class Foo implements test.SomeInterface { def foo() { true } }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, MISSING_OVERRIDE);
	}

	@Test public void testMissingOverride_5() throws Exception {
		XtendClass xtendClass = clazz("class Foo { def boolean equals(Object x) { return true } }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, MISSING_OVERRIDE);
	}

	@Test public void testIncompatibleReturnType_0() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override Boolean string() {true} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testIncompatibleReturnType_1() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override String object() {''} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testIncompatibleReturnType_2() throws Exception {
		XtendClass xtendClass = clazz("class Foo implements test.SomeInterface { override void foo() {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testIncompatibleGenericReturnType_0() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override java.util.ArrayList<String> returnsListString() {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testIncompatibleGenericReturnType_1() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override java.util.List<Object> returnsListString() {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testIncompatibleGenericReturnType_2() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override java.util.ArrayList<String> returnsListExtendsObject() {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testOverrideVoidFunction() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override voidFunction() {''} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testOverrideVoidFunction_1() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.SuperClass { override String voidFunction() {''} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testOverrideWithTypeParameter() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.GenericClass { override java.util.List<String> foo() {newArrayList} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testOverrideWithTypeParameter_1() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.GenericClass<String> { override java.util.List<String> foo() {newArrayList} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testOverrideWithTypeParameter_2() throws Exception {
		XtendClass xtendClass = clazz("class Foo<S> extends test.GenericClass<S> { override java.util.List<S> foo() {null} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_RETURN_TYPE);
	}

	@Test public void testClassMustBeAbstract_01() throws Exception {
		XtendClass xtendClass = clazz("class Foo<S> implements Comparable<S> { }");
		helper.assertError(xtendClass, XTEND_CLASS, CLASS_MUST_BE_ABSTRACT, "abstract", "not", "implement",
				"compareTo(S)");
	}

	@Test public void testClassMustBeAbstract_02() throws Exception {
		XtendClass xtendClass = clazz("class Foo<S> implements Comparable { }");
		helper.assertError(xtendClass, XTEND_CLASS, CLASS_MUST_BE_ABSTRACT, "abstract", "not", "implement",
				"compareTo(Object)");
	}

	@Test public void testClassMustBeAbstract_03() throws Exception {
		XtendClass xtendClass = clazz("class Foo implements Comparable<String> { }");
		helper.assertError(xtendClass, XTEND_CLASS, CLASS_MUST_BE_ABSTRACT, "abstract", "not", "implement",
				"compareTo(String)");
	}

	@Test public void testClassMustBeAbstract_04() throws Exception {
		XtendClass xtendClass = clazz("class Foo implements Comparable { }");
		helper.assertError(xtendClass, XTEND_CLASS, CLASS_MUST_BE_ABSTRACT, "abstract", "not", "implement",
				"compareTo(Object)");
	}

	@Test
	public void testClassMustBeAbstract_05() throws Exception {
		XtendClass xtendClass = clazz("class MyList<T> extends java.util.ArrayList<T> { }");
		helper.assertNoErrors(xtendClass);
	}
	
	@Test
	public void testClassMustBeAbstract_06() throws Exception {
		XtendClass xtendClass = clazz("class StringList extends java.util.ArrayList<StringList> { }");
		helper.assertNoErrors(xtendClass);
	}

	@Test public void testOverrideFinalClass() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends String { }");
		helper.assertError(xtendClass, XTEND_CLASS, OVERRIDDEN_FINAL, "override", "final");
	}

	@Test public void testOverrideFinalMethod() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ClassWithFinalMembers { def foo() {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, OVERRIDDEN_FINAL, "override", "final");
	}

	@Test public void testOverrideSameVisibility() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.Visibilities { override publicMethod() {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), OVERRIDE_REDUCES_VISIBILITY);
	}

	@Test public void testOverrideReveals() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.Visibilities { override public protectedMethod() {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), OVERRIDE_REDUCES_VISIBILITY);
	}

	@Test public void testOverrideHides() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.Visibilities { override protected publicMethod() {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, OVERRIDE_REDUCES_VISIBILITY, "reduce",
				"visibility");
	}

	@Test public void testDispatchHides() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.Visibilities { def protected dispatch publicMethod() {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, OVERRIDE_REDUCES_VISIBILITY, "reduce",
				"visibility");
	}

	@Test public void testIncompatibleThrowsClause() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override ioException() throws Exception {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_THROWS_CLAUSE,
				"Exception", "not", "compatible", "throws", "clause");
	}
	
	@Test public void testIncompatibleThrowsClause_01() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override runtimeException() throws Exception {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_THROWS_CLAUSE,
				"Exception", "not", "compatible", "throws", "clause");
	}
	
	@Test public void testIncompatibleThrowsClause_02() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override nullPointerException() throws Exception {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_THROWS_CLAUSE,
				"Exception", "not", "compatible", "throws", "clause");
	}
	
	@Test public void testIncompatibleThrowsClause_03() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override noException() throws Exception {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_THROWS_CLAUSE,
				"Exception", "not", "compatible", "throws", "clause");
	}
	
	@Ignore("Fails in old impl")
	@Test public void testIncompatibleThrowsClause_04() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override generifiedIoException() throws java.net.URISyntaxException {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_THROWS_CLAUSE,
				"Exception", "URISyntaxException", "not", "compatible", "throws", "clause");
	}
	
	@Ignore("Fails in old impl")
	@Test public void testIncompatibleThrowsClause_05() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override generifiedRuntimeException() throws java.io.FileNotFoundException {} }");
		helper.assertError(xtendClass.getMembers().get(0), XTEND_FUNCTION, INCOMPATIBLE_THROWS_CLAUSE,
				"Exception", "FileNotFoundException", "not", "compatible", "throws", "clause");
	}
	
	@Test public void testCompatibleThrowsClause() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override ioException() throws java.io.FileNotFoundException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}

	@Test public void testCompatibleThrowsClause_01() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override runtimeException() throws NullPointerException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}

	@Test public void testCompatibleThrowsClause_02() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override nullPointerException() throws RuntimeException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}

	@Test public void testCompatibleThrowsClause_03() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override noException() throws RuntimeException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}

	@Test public void testCompatibleThrowsClause_04() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override throwable() throws RuntimeException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}

	@Test public void testCompatibleThrowsClause_05() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override throwable() throws Exception {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}

	@Test public void testCompatibleThrowsClause_06() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override throwable() throws Throwable {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}

	@Test public void testCompatibleThrowsClause_07() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override ioException() {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}
	
	@Ignore("Fails in old impl")
	@Test public void testCompatibleThrowsClause_08() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override <E extends java.io.IOException> generifiedIoException() throws E {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}
	
	@Ignore("Fails in old impl")
	@Test public void testCompatibleThrowsClause_09() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override <E extends java.io.IOException> generifiedIoException() throws E {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}
	
	@Ignore("Fails in old impl")
	@Test public void testCompatibleThrowsClause_10() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override <E extends java.io.IOException> generifiedIoException() throws E, NullPointerException, OutOfMemoryError {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}
	
	@Test public void testCompatibleThrowsClause_11() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override generifiedIoException() throws java.io.IOException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}
	
	@Test public void testCompatibleThrowsClause_12() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override generifiedRuntimeException() throws NullPointerException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}
	
	@Test public void testCompatibleThrowsClause_13() throws Exception {
		XtendClass xtendClass = clazz("class Foo extends test.ExceptionThrowing { override <E extends RuntimeException> generifiedRuntimeException() throws E, NullPointerException {} }");
		helper.assertNoError(xtendClass.getMembers().get(0), INCOMPATIBLE_THROWS_CLAUSE);
	}
	
}
