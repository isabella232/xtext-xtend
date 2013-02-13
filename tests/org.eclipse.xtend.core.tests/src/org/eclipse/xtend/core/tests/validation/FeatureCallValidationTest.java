/*******************************************************************************
 * Copyright (c) 2011 itemis AG (http://www.itemis.eu) and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *******************************************************************************/
package org.eclipse.xtend.core.tests.validation;

import org.eclipse.xtend.core.tests.AbstractXtendTestCase;
import org.eclipse.xtend.core.xtend.XtendClass;
import org.eclipse.xtext.junit4.validation.ValidationTestHelper;
import org.eclipse.xtext.xbase.XbasePackage;
import org.eclipse.xtext.xbase.validation.IssueCodes;
import org.junit.Ignore;
import org.junit.Test;

import com.google.inject.Inject;

/**
 * @author Moritz Eysholdt - Initial contribution and API
 */
public class FeatureCallValidationTest extends AbstractXtendTestCase {

	@Inject
	private ValidationTestHelper helper;

	/**
	 * see https://bugs.eclipse.org/bugs/show_bug.cgi?id=362240
	 */
	@Test
	public void testBug362240_1() throws Exception {
		XtendClass clazz = clazz("class Bar { def <T> bar(T t) { <Integer>bar(t) }}");
		helper.assertError(clazz, XbasePackage.Literals.XFEATURE_CALL,
				IssueCodes.INCOMPATIBLE_TYPES, "Expected Integer or int but was T");
	}
	
	/**
	 * see https://bugs.eclipse.org/bugs/show_bug.cgi?id=362240
	 */
	@Test
	public void testBug362240_2() throws Exception {
		XtendClass clazz = clazz("class Bar<T> { def <X> void bar(X x) { val T t = null; <Integer>bar(t) }}");
		helper.assertError(clazz, XbasePackage.Literals.XFEATURE_CALL,
				IssueCodes.INCOMPATIBLE_TYPES, "Expected Integer or int but was T");
	}
	
	/**
	 * see https://bugs.eclipse.org/bugs/show_bug.cgi?id=362240
	 */
	@Test
	public void testBug362240_3() throws Exception {
		XtendClass clazz = clazz("class Bar<T extends Integer> { def <X> void bar(X x) { val T t = null; <Integer>bar(t) }}");
		helper.assertNoErrors(clazz);
	}
	
	@Test 
	public void testBug400653() throws Exception {
		XtendClass clazz = clazz("class X { def void m(String x) { x.m2 } def m2(char c) {}}");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				IssueCodes.INCOMPATIBLE_TYPES, "String", "char", "Character", "receiver");
	}
	
	@Test 
	public void testBug400653_02() throws Exception {
		XtendClass clazz = clazz("class X { def void m(String it) { m2 } def m2(char c) {}}");
		helper.assertError(clazz, XbasePackage.Literals.XFEATURE_CALL,
				IssueCodes.INCOMPATIBLE_TYPES, "String", "char", "Character", "implicit first argument");
	}
	
	@Test 
	public void testConstructInstanceOfTypeParameter() throws Exception {
		XtendClass clazz = clazz("class X<T> { def m() { new T } }");
		helper.assertError(clazz, XbasePackage.Literals.XCONSTRUCTOR_CALL,
				IssueCodes.ILLEGAL_CLASS_INSTANTIATION, "Cannot instantiate the type parameter T");
	}
	
	@Test 
	public void testThisInStaticContext() throws Exception {
		XtendClass clazz = clazz("class X { static def meth() { this.toString } }");
		helper.assertError(clazz, XbasePackage.Literals.XFEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}
	
	@Test 
	public void testThisInInstanceContext() throws Exception {
		XtendClass clazz = clazz("class X { def meth() { this.toString } }");
		helper.assertNoErrors(clazz);
	}
	
	@Test 
	public void testSuperInStaticContext() throws Exception {
		XtendClass clazz = clazz("class X { static def meth() { super.toString } }");
		helper.assertError(clazz, XbasePackage.Literals.XFEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}
	
	@Test 
	public void testSuperInInstanceContext() throws Exception {
		XtendClass clazz = clazz("class X { def meth() { super.toString } }");
		helper.assertNoErrors(clazz);
	}
	
	@Test public void testXFeatureCallField1() throws Exception {
		XtendClass clazz = clazz("class X { String foo def meth() { foo.toLowerCase } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXFeatureCallField2() throws Exception {
		XtendClass clazz = clazz("class X { static String foo def meth() { foo.toLowerCase } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXFeatureCallField3() throws Exception {
		XtendClass clazz = clazz("class X { String foo def static meth() { foo.toLowerCase } }");
		helper.assertError(clazz, XbasePackage.Literals.XFEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test public void testXFeatureCallField4() throws Exception {
		XtendClass clazz = clazz("class X { static String foo def static meth() { foo.toLowerCase } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallField1() throws Exception {
		XtendClass clazz = clazz("class X { String foo def meth() { new X().foo.toLowerCase } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallField2() throws Exception {
		XtendClass clazz = clazz("class X { static String foo def meth() { new X().foo.toLowerCase } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.INSTANCE_ACCESS_TO_STATIC_MEMBER);
	}

	@Test public void testXMemberFeatureCallField3() throws Exception {
		XtendClass clazz = clazz("class X { String foo def static meth() { new X().foo.toLowerCase } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallField4() throws Exception {
		XtendClass clazz = clazz("class X { static String foo def static meth() { new X().foo.toLowerCase } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.INSTANCE_ACCESS_TO_STATIC_MEMBER);
	}

	@Test public void testXAssignmentField1() throws Exception {
		XtendClass clazz = clazz("class X { String foo def meth() { foo = '' } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXAssignmentField2() throws Exception {
		XtendClass clazz = clazz("class X { static String foo def meth() { foo = '' } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXAssignmentField3() throws Exception {
		XtendClass clazz = clazz("class X { String foo def static meth() { foo = '' } }");
		helper.assertError(clazz, XbasePackage.Literals.XASSIGNMENT,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test public void testXAssignmentField4() throws Exception {
		XtendClass clazz = clazz("class X { static String foo def static meth() { foo = '' } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXFeatureCallOperation1() throws Exception {
		XtendClass clazz = clazz("class X { def setFoo(String x) {} def meth() { setFoo('') } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXFeatureCallOperation2() throws Exception {
		XtendClass clazz = clazz("class X { def static setFoo(String x) {} def meth() { setFoo('') } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXFeatureCallOperation3() throws Exception {
		XtendClass clazz = clazz("class X { def setFoo(String x) {} def static meth() { setFoo('') } }");
		helper.assertError(clazz, XbasePackage.Literals.XFEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test public void testXFeatureCallOperation4() throws Exception {
		XtendClass clazz = clazz("class X { def static setFoo(String x) {} def static meth() { setFoo('') } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallOperation1() throws Exception {
		XtendClass clazz = clazz("class X { def setFoo(String x) {} def meth() { new X().setFoo('') } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallOperation2() throws Exception {
		XtendClass clazz = clazz("class X { def static setFoo(String x) {} def meth() { new X().setFoo('') } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.INSTANCE_ACCESS_TO_STATIC_MEMBER);
	}

	@Test public void testXMemberFeatureCallOperation3() throws Exception {
		XtendClass clazz = clazz("class X { def setFoo(String x) {} def static meth() { new X().setFoo('') } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallOperation4() throws Exception {
		XtendClass clazz = clazz("class X { def static setFoo(String x) {} def static meth() { new X().setFoo('') } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.INSTANCE_ACCESS_TO_STATIC_MEMBER);
	}

	@Test public void testXAssignmentOperation1() throws Exception {
		XtendClass clazz = clazz("class X { def setFoo(String x) {} def meth() { foo = '' } }");
		helper.assertNoErrors(clazz);
	}

	@Test
	public void testXAssignmentOperation2() throws Exception {
		XtendClass clazz = clazz("class X { def static setFoo(String x) {} def meth() { foo = '' } }");
		helper.assertNoErrors(clazz);
	}

	@Test
	public void testXAssignmentOperation3() throws Exception {
		XtendClass clazz = clazz("class X { def setFoo(String x) {} def static meth() { foo = '' } }");
		helper.assertError(clazz, XbasePackage.Literals.XASSIGNMENT,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test
	public void testXAssignmentOperation4() throws Exception {
		XtendClass clazz = clazz("class X { def static setFoo(String x) {} def static meth() { foo = '' } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallImportedMemberExtension1() throws Exception {
		XtendClass clazz = clazz("class X { extension test.ExtensionMethods def meth() { 'foo'.instanceExtension } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallImportedMemberExtension2() throws Exception {
		XtendClass clazz = clazz("class X { extension test.ExtensionMethods def static meth() { 'foo'.instanceExtension } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test
	@Ignore("static methods from instance extensions are not on the scope")
	public void testXMemberFeatureCallImportedMemberExtension3() throws Exception {
		XtendClass clazz = clazz("class X { extension test.ExtensionMethods def meth() { 'foo'.staticExtension } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test
	@Ignore("static methods from instance extensions are not on the scope")
	public void testXMemberFeatureCallImprotedMemberExtension4() throws Exception {
		XtendClass clazz = clazz("class X { extension test.ExtensionMethods def static meth() { 'foo'.staticExtension } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test public void testXMemberFeatureCallLocalMemberExtension1() throws Exception {
		XtendClass clazz = clazz("class X { def instanceExtension(String foo) { foo + 'inst' } def meth() { 'foo'.instanceExtension } }");
		helper.assertNoErrors(clazz);
	}

	@Test public void testXMemberFeatureCallLocalMemberExtension2() throws Exception {
		XtendClass clazz = clazz("class X { def instanceExtension(String foo) { foo + 'inst' } def static meth() { 'foo'.instanceExtension } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test
	@Ignore("static methods from instance extensions are not on the scope")
	public void testXMemberFeatureCallLocalMemberExtension3() throws Exception {
		XtendClass clazz = clazz("class X { def static staticExtension(String foo) { foo + 'inst' } def meth() { 'foo'.staticExtension } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test
	@Ignore("static methods from instance extensions are not on the scope")
	public void testXMemberFeatureCallLocalMemberExtension4() throws Exception {
		XtendClass clazz = clazz("class X { def static staticExtension(String foo) { foo + 'inst' } def static meth() { 'foo'.staticExtension } }");
		helper.assertError(clazz, XbasePackage.Literals.XMEMBER_FEATURE_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.STATIC_ACCESS_TO_INSTANCE_MEMBER);
	}

	@Test public void testPrivateConstructorCalled() throws Exception {
		XtendClass clazz = clazz("class X { def foo() { new test.Constructor() } }");
		helper.assertError(clazz, XbasePackage.Literals.XCONSTRUCTOR_CALL,
				org.eclipse.xtext.xbase.validation.IssueCodes.FEATURE_NOT_VISIBLE);
	}
}
