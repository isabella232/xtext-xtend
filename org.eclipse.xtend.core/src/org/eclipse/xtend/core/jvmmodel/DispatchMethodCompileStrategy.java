/*******************************************************************************
 * Copyright (c) 2011, 2021 itemis AG (http://www.itemis.eu) and others.
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * SPDX-License-Identifier: EPL-2.0
 *******************************************************************************/
package org.eclipse.xtend.core.jvmmodel;

import static com.google.common.collect.Lists.*;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.eclipse.xtext.common.types.JvmFormalParameter;
import org.eclipse.xtext.common.types.JvmIdentifiableElement;
import org.eclipse.xtext.common.types.JvmOperation;
import org.eclipse.xtext.common.types.JvmType;
import org.eclipse.xtext.common.types.JvmTypeReference;
import org.eclipse.xtext.common.types.util.TypeReferences;
import org.eclipse.xtext.util.Strings;
import org.eclipse.xtext.xbase.compiler.IAppendable;
import org.eclipse.xtext.xbase.compiler.Later;
import org.eclipse.xtext.xbase.compiler.TreeAppendableUtil;
import org.eclipse.xtext.xbase.compiler.output.ITreeAppendable;
import org.eclipse.xtext.xbase.lib.Procedures;
import org.eclipse.xtext.xbase.typesystem.conformance.TypeConformanceComputationArgument;
import org.eclipse.xtext.xbase.typesystem.references.ITypeReferenceOwner;
import org.eclipse.xtext.xbase.typesystem.references.LightweightTypeReference;
import org.eclipse.xtext.xbase.typesystem.references.StandardTypeReferenceOwner;
import org.eclipse.xtext.xbase.typesystem.util.CommonTypeComputationServices;

import com.google.inject.Inject;

public class DispatchMethodCompileStrategy implements Procedures.Procedure1<ITreeAppendable> {
	
	@Inject
	private TypeReferences typeReferences;

	@Inject
	private TreeAppendableUtil treeAppendableUtil;
	
	@Inject
	private CommonTypeComputationServices services;
	
	@Inject
	private DispatchHelper sorter;
	
	private JvmOperation dispatchOperation;

	protected void initialize(JvmOperation dispatchOperation) {
		this.dispatchOperation = dispatchOperation;
	}

	@Override
	public void apply(/* @Nullable */ ITreeAppendable a) {
		if (a == null)
			throw new IllegalArgumentException("a is never null");
		boolean needsElse = false;
		boolean needsLastCase = false;
		int parameterCount = dispatchOperation.getParameters().size();
		List<JvmOperation> sortedDispatchOperations = sorter.getAllDispatchCases(dispatchOperation);
		ITypeReferenceOwner owner = new StandardTypeReferenceOwner(services, dispatchOperation);
		boolean[] allCasesSameType = new boolean[parameterCount];
		boolean[] voidIncluded = new boolean[parameterCount];
		boolean[] notNullIncluded = new boolean[parameterCount];
		for(int i = 0; i < parameterCount; i++) {
			allCasesSameType[i] = true;
			voidIncluded[i] = false;
			notNullIncluded[i] = false;
			JvmFormalParameter dispatchParam = dispatchOperation.getParameters().get(i);
			LightweightTypeReference dispatchParamType = owner.toLightweightTypeReference(dispatchParam.getParameterType());
			JvmTypeReference dispatchParameterType = dispatchParam.getParameterType();
			for (JvmOperation operation : sortedDispatchOperations) {
				JvmFormalParameter caseParam = operation.getParameters().get(i);
				JvmTypeReference caseParameterType = caseParam.getParameterType();
				LightweightTypeReference caseParamType = owner.toLightweightTypeReference(caseParam.getParameterType());
				if (!Strings.equal(dispatchParameterType.getIdentifier(), caseParameterType.getIdentifier())) {
					allCasesSameType[i] = false;
				}
				if (caseParamType.isType(Void.class)) {
					voidIncluded[i] = true;
				}
				TypeConformanceComputationArgument rawNoSynonyms = new TypeConformanceComputationArgument(true, false, true, true, false, false);
				if (caseParamType.isAssignableFrom(dispatchParamType, rawNoSynonyms) && !dispatchParamType.isPrimitive()) {
					notNullIncluded[i] = true;
				}
			}
		}
		for (boolean v : voidIncluded) {
			if (!v) {
				needsElse = true;
				break;
			}
		}
		if (parameterCount == 1 && sortedDispatchOperations.size() == 1)
			needsElse = false;
		for (boolean n : notNullIncluded) {
			if (!n) {
				needsLastCase = true;
				break;
			}
		}
		if (needsElse || (parameterCount == 1 && sortedDispatchOperations.size() == 1))
			needsLastCase = true;
		for (JvmOperation operation : sortedDispatchOperations) {
			ITreeAppendable operationAppendable = treeAppendableUtil.traceSignificant(a, operation, true);
			final List<Later> laters = newArrayList();
			for (int i = 0; i < parameterCount; i++) {
				final JvmFormalParameter dispatchParam = dispatchOperation.getParameters().get(i);
				final LightweightTypeReference dispatchParamType = owner.toLightweightTypeReference(dispatchParam.getParameterType());
				final JvmFormalParameter caseParam = operation.getParameters().get(i);
				final LightweightTypeReference caseParamType = owner.toLightweightTypeReference(caseParam.getParameterType());
				final String name = getVarName(dispatchParam, operationAppendable);
				if (caseParamType.isType(Void.class)) {
					laters.add(new Later() {
						@Override
						public void exec(ITreeAppendable appendable) {
							appendable.append(name).append(" == null");
						}
					});
				} else if (!allCasesSameType[i]) {
					laters.add(new Later() {
						@Override
						public void exec(ITreeAppendable appendable) {
							TypeConformanceComputationArgument rawNoSynonyms = new TypeConformanceComputationArgument(true, false, true, true, false, false);
							if (caseParamType.isAssignableFrom(dispatchParamType, rawNoSynonyms) && !dispatchParamType.isPrimitive()) {
								appendable.append(name).append(" != null");
							} else {
								appendable.append(name).append(" instanceof ");
								JvmType type = caseParamType.getWrapperTypeIfPrimitive().getType();
								if (type == null) {
									throw new IllegalStateException(String.valueOf(caseParamType));
								}
								appendable.append(type);
							}
						}
					});
				}
			}
			boolean isLast = sortedDispatchOperations.get(sortedDispatchOperations.size() - 1) == operation;
			// if it's not the first if append an 'else'
			if (sortedDispatchOperations.get(0) != operation) {
				operationAppendable.append(" else ");
			}
			if (laters.isEmpty()) {
				if (sortedDispatchOperations.size() != 1) {
					operationAppendable.append("{").increaseIndentation();
					operationAppendable.newLine();
				}
			} else {
				if (!isLast || needsLastCase) {
					operationAppendable.append("if (");
					operationAppendable.increaseIndentation().increaseIndentation();
					Iterator<Later> iterator = laters.iterator();
					while (iterator.hasNext()) {
						iterator.next().exec(operationAppendable);
						if (iterator.hasNext()) {
							operationAppendable.newLine().append(" && ");
						}
					}
					operationAppendable.decreaseIndentation().decreaseIndentation();
					operationAppendable.append(") {").increaseIndentation();
					operationAppendable.newLine();
				}
			}
			final boolean isCurrentVoid = typeReferences.is(operation.getReturnType(), Void.TYPE);
			final boolean isDispatchVoid = typeReferences.is(dispatchOperation.getReturnType(), Void.TYPE);
			if (isDispatchVoid) {
				generateActualDispatchCall(dispatchOperation, operation, operationAppendable, owner);
				operationAppendable.append(";");
				// we generate a redundant return statement here to get a better debugging experience
				if (!isLast || needsLastCase) {
					operationAppendable.newLine().append("return;");
				}
			} else {
				if (isCurrentVoid) {
					generateActualDispatchCall(dispatchOperation, operation, operationAppendable, owner);
					operationAppendable.append(";").newLine().append("return null");
				} else {
					operationAppendable.append("return ");
					generateActualDispatchCall(dispatchOperation, operation, operationAppendable, owner);
				}
				operationAppendable.append(";");
			}
			if (sortedDispatchOperations.size() != 1 && (!isLast || needsLastCase)) {
				operationAppendable.decreaseIndentation();
				a.newLine().append("}");
			}
		}
		if (needsElse) {
			a.append(" else {").increaseIndentation();
			a.newLine();
			a.increaseIndentation();
			a.append("throw new IllegalArgumentException(\"Unhandled parameter types: \" +").newLine();
			JvmType jvmType = typeReferences.findDeclaredType("java.util.Arrays", dispatchOperation);
			if (jvmType != null) {
				a.append(jvmType);
			} else {
				a.append(Arrays.class.getSimpleName());
			}
			a.append(".<Object>asList(");
			Iterator<JvmFormalParameter> iterator = dispatchOperation.getParameters().iterator();
			while (iterator.hasNext()) {
				JvmFormalParameter parameter = iterator.next();
				final String name = getVarName(parameter, a);
				a.append(name);
				if (iterator.hasNext()) {
					a.append(", ");
				}
			}
			a.append(").toString());");
			a.decreaseIndentation();
			a.decreaseIndentation().newLine().append("}");
		}
	}

	protected void generateActualDispatchCall(JvmOperation dispatchOperation, JvmOperation actualOperationToCall,
			ITreeAppendable a, ITypeReferenceOwner owner) {
		a.append(actualOperationToCall.getSimpleName()).append("(");
		Iterator<JvmFormalParameter> iter1 = dispatchOperation.getParameters().iterator();
		for (Iterator<JvmFormalParameter> iter2 = actualOperationToCall.getParameters().iterator(); iter2.hasNext();) {
			JvmFormalParameter p1 = iter1.next();
			JvmFormalParameter p2 = iter2.next();
			LightweightTypeReference type1 = owner.toLightweightTypeReference(p1.getParameterType());
			LightweightTypeReference type2 = owner.toLightweightTypeReference(p2.getParameterType());
			if (!type2.isAssignableFrom(type1, new TypeConformanceComputationArgument(true, false, true, true, false, false))) {
				a.append("(").append(type2.getWrapperTypeIfPrimitive()).append(")");
			}
			if (typeReferences.is(p2.getParameterType(), Void.class)) {
				a.append("null");
			} else {
				a.append(getVarName(p1, a));
			}
			if (iter2.hasNext()) {
				a.append(", ");
			}
		}
		a.append(")");
	}

	protected String getVarName(JvmIdentifiableElement ex, IAppendable appendable) {
		return appendable.getName(ex);
	}
}