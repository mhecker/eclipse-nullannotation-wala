/*******************************************************************************
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package com.ibm.wala.core.tests.cfg.exc.intra;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.cfg.exc.ExceptionPruningAnalysis;
import com.ibm.wala.cfg.exc.NullPointerAnalysis;
import com.ibm.wala.cfg.exc.intra.ExplodedCFGNullPointerAnalysis;
import com.ibm.wala.cfg.exc.intra.IntraprocNullPointerAnalysis;
import com.ibm.wala.cfg.exc.intra.MethodState;
import com.ibm.wala.cfg.exc.intra.NullPointerState;
import com.ibm.wala.cfg.exc.intra.NullPointerState.State;
import com.ibm.wala.cfg.exc.intra.ParameterState;
import com.ibm.wala.cfg.exc.intra.SSACFGNullPointerAnalysis;
import com.ibm.wala.classLoader.ClassLoaderFactory;
import com.ibm.wala.classLoader.ClassLoaderFactoryImpl;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.ShrikeCTMethod;
import com.ibm.wala.classLoader.ShrikeClass;
import com.ibm.wala.core.tests.util.WalaTestCase;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.shrikeCT.AnnotationsReader.ArrayElementValue;
import com.ibm.wala.shrikeCT.AnnotationsReader.ElementValue;
import com.ibm.wala.shrikeCT.AnnotationsReader.EnumElementValue;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.shrikeCT.TypeAnnotationsReader.TargetType;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.types.annotations.TypeAnnotation.FormalParameterTarget;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.NullProgressMonitor;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.graph.GraphIntegrity.UnsoundGraphException;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.util.strings.Atom;
import com.ibm.wala.util.strings.StringStuff;
import com.ibm.wala.util.warnings.Warnings;

/**
 * Test validity and precision of intra-procedurel NullpointerException-Analysis {@link IntraprocNullPointerAnalysis}
 * 
 */
public class NonNullIntraTest extends WalaTestCase {

  private static AnalysisScope scope;

  private static ClassHierarchy cha;
  
  private static String NONNULL_TESTDATA = "dat" + File.separator + "eclipse-nullannotation.testdata.txt";

  @BeforeClass
  public static void beforeClass() throws Exception {

    scope = AnalysisScopeReader.readJavaScope(NONNULL_TESTDATA,
        (new FileProvider()).getFile("J2SEClassHierarchyExclusions.txt"), NonNullIntraTest.class.getClassLoader());
    ClassLoaderFactory factory = new ClassLoaderFactoryImpl(scope.getExclusions());

    try {
      cha = ClassHierarchy.make(scope, factory);
    } catch (ClassHierarchyException e) {
      throw new Exception();
    }
  }

  @AfterClass
  public static void afterClass() throws Exception {
    Warnings.clear();
    scope = null;
    cha = null;
  }

  public static void main(String[] args) {
    justThisTest(NonNullIntraTest.class);
  }

  private static final TypeReference NULLABLE = TypeReference.findOrCreate(ClassLoaderReference.Application, "Lorg/eclipse/jdt/annotation/Nullable");
  private static final TypeReference NONNULL = TypeReference.findOrCreate(ClassLoaderReference.Application, "Lorg/eclipse/jdt/annotation/NonNull"); 
  private static final TypeReference NONNULLBYDEFAULT = TypeReference.findOrCreate(ClassLoaderReference.Application, "Lorg/eclipse/jdt/annotation/NonNullByDefault");
  
  private static ParameterState makeNonNullParameterState(IR ir) throws InvalidClassFileException {
    final ShrikeCTMethod m = (ShrikeCTMethod) ir.getMethod();
    final ParameterState state = ParameterState.createDefault(m);
    
    boolean nonNullByDefault = nonNullByDefaultForParameters(m);
    Set<Integer> nullable = new HashSet<>();
    if (nonNullByDefault) {
      m.getTypeAnnotationsAtMethodInfo(true)
      .stream()
      .filter(ta -> ta.getTypeAnnotationTarget().getClass().equals(FormalParameterTarget.class))
      .filter(ta ->
        ta.getAnnotation().getType().equals(NULLABLE)
       )
      .forEach(ta -> {
        final FormalParameterTarget formal = (FormalParameterTarget) ta.getTypeAnnotationTarget();
        final int stateIndex = formal.getIndex() + (m.isStatic() ? 0 : 1);
        state.setState(stateIndex, State.UNKNOWN);
        nullable.add(stateIndex);
      });
      for (int p = 0; p < m.getNumberOfParameters(); p++) {
        final int stateIndex = p + (m.isStatic() ? 0 : 1);
        if (!nullable.contains(stateIndex)) {
          state.setState(stateIndex, State.NOT_NULL);
        }
      }
    } else {
      m.getTypeAnnotationsAtMethodInfo(true)
      .stream()
      .filter(ta -> ta.getTypeAnnotationTarget().getClass().equals(FormalParameterTarget.class))
      .filter(ta ->
        ta.getAnnotation().getType().equals(NONNULL)
       )
      .forEach(ta -> {
        final FormalParameterTarget formal = (FormalParameterTarget) ta.getTypeAnnotationTarget();
        final int stateIndex = formal.getIndex() + (m.isStatic() ? 0 : 1);
        state.setState(stateIndex, State.NOT_NULL);
     });
    }
    return state;
  }
  
  private static IClass packageInfoFor(IClass clazz) {
    final TypeName name = clazz.getName();
    final Atom packge = name.getPackage();
    final TypeName packageInfoName = TypeName.findOrCreateClassName(
        packge.toString(),
        "package-info"
    );
    return clazz.getClassLoader().lookupClass(packageInfoName);
  }
  
  private static boolean nonNullByDefaultForParameters(ShrikeClass clazz) throws InvalidClassFileException {
    ShrikeClass packageInfo;
    boolean nonNullByDefaultFromParent = false;
    if (clazz.isInnerClass()) {
      IMethod enclosingMethod = clazz.getEnclosingMethod();
      if (enclosingMethod != null) {
        nonNullByDefaultFromParent = nonNullByDefaultForParameters(enclosingMethod);
      } else {
        ShrikeClass enclosingClass = (ShrikeClass) clazz.getEnclosingMethodClass();
        nonNullByDefaultFromParent = nonNullByDefaultForParameters(enclosingClass);
      }
    } else if ((packageInfo = (ShrikeClass) packageInfoFor(clazz)) != null) {
      nonNullByDefaultFromParent = nonNullByDefaultForParameters(packageInfo);
    }
    
    return clazz.getAnnotations()
      .stream()
      .filter(a -> a.getType().equals(NONNULLBYDEFAULT))
      .map(a -> {
        final Map<String, ElementValue> namedArguments = a.getNamedArguments();
        boolean isDefault = namedArguments.get("value") == null;
        if (isDefault) {
          return true;
        } else {
          return false; 
        }
      })
      .reduce(nonNullByDefaultFromParent, Boolean::logicalOr);
  }
  
  private static boolean nonNullByDefaultForParameters(IMethod method) throws InvalidClassFileException {
    boolean nonNullByDefaultFromParent = false;
    ShrikeClass enclosingClass = (ShrikeClass) method.getDeclaringClass();
    nonNullByDefaultFromParent = nonNullByDefaultForParameters(enclosingClass);
    return method.getAnnotations()
      .stream()
      .filter(a -> a.getType().equals(NONNULLBYDEFAULT))
      .map(a -> {
        final Map<String, ElementValue> namedArguments = a.getNamedArguments();
        boolean isDefault = namedArguments.get("value") == null;
        if (isDefault) {
          return true;
        } else {
          ArrayElementValue value = (ArrayElementValue) namedArguments.get("value");
          return Arrays.stream(value.vals).map( e -> ((EnumElementValue)e).enumVal).anyMatch("PARAMETER"::equals); 
        }
      })
      .reduce(nonNullByDefaultFromParent, Boolean::logicalOr);
  }

  
  private static MethodState makeNonNullMethodState(final ClassHierarchy cha) {
    return new MethodState() {
      @Override
      public boolean throwsException(SSAAbstractInvokeInstruction node) {
        final MethodReference mref = node.getDeclaredTarget();
        final ShrikeCTMethod m = (ShrikeCTMethod) cha.resolveMethod(mref);
        try {
          return m.getTypeAnnotationsAtMethodInfo(true)
          .stream()
          .filter(ta -> ta.getTargetType().equals(TargetType.METHOD_RETURN))
          .filter(ta -> ta.getAnnotation().getType().equals(NONNULL))
          .findAny()
          .isPresent();
        } catch (InvalidClassFileException e) {
          return true;
        }
      }
    };
  }
  
  private static ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> createNonNullRespectingExplodedCFGAnalysis(IR ir) throws InvalidClassFileException {
    return new ExplodedCFGNullPointerAnalysis(
        NullPointerAnalysis.DEFAULT_IGNORE_EXCEPTIONS,
        ir,
        makeNonNullParameterState(ir),
        makeNonNullMethodState(cha),
        false
    );
  }
  
  private static ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> createNonNullRespectingSSACFGAnalysis(IR ir) throws InvalidClassFileException {
    return new SSACFGNullPointerAnalysis(
        NullPointerAnalysis.DEFAULT_IGNORE_EXCEPTIONS,
        ir,
        makeNonNullParameterState(ir),
        makeNonNullMethodState(cha)
    );
  }
  
  @Test
  public void testParam() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testParam(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testParamNonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testParam(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testDynamicParam() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testParam(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testParam2() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testParam2(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  
  @Test
  public void testParam2NonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testParam2(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  
  public void testDynamicParam2() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testDynamicParam2(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  
  
  @Test
  public void testIf() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testIf(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testIfNonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testIf(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testDynamicIf() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testIf(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testIf2() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testIf2(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testIf2NonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testIf2(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testDynamicIf2() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testIf2(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  
  @Test
  public void testIfContinued() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testIfContinued(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testIfContinuedNonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testIfContinued(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testDynamicIfContinued() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testIfContinued(ZLcfg/exc/intra/B;Lcfg/exc/intra/B;Lcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testIf3() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testIf3(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  @Test
  public void testIf3NonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testIf3(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.BOTH, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.BOTH, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testDynamicIf3() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testIf3(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testWhile() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testWhile(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testWhileNonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testWhile(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testWhileDynamic() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testWhile(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testWhile2() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testWhile2(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testWhile2NonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testWhile2(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testDynamicWhile2() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testWhile2(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertEquals(State.NOT_NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testGet() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccess.testGet(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }    
  }
  
  @Test
  public void testGetNonNullByDefault() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessNonNullByDefault.testGet(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }    
  }

  @Test
  public void testDynamicGet() throws UnsoundGraphException, CancelException, InvalidClassFileException {
    MethodReference mr = StringStuff.makeMethodReference("cfg.exc.intra.FieldAccessDynamic.testGet(ZLcfg/exc/intra/B;)Lcfg/exc/intra/B");

    IMethod m = cha.resolveMethod(mr);
    AnalysisCache cache = new AnalysisCache();
    IR ir = cache.getIR(m);
    final ISSABasicBlock returnNode = returnNode(ir.getControlFlowGraph());
    final int returnVal = returnVal(returnNode);

    {
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
          createNonNullRespectingExplodedCFGAnalysis(ir);
      intraExplodedCFG.compute(new NullProgressMonitor());
        
      final IExplodedBasicBlock returnNodeExploded = returnNodeExploded(returnNode, intraExplodedCFG.getCFG());
      final NullPointerState returnState = intraExplodedCFG.getState(returnNodeExploded);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }
    {
      ExceptionPruningAnalysis<SSAInstruction, ISSABasicBlock> intraSSACFG =
          createNonNullRespectingSSACFGAnalysis(ir);
      intraSSACFG.compute(new NullProgressMonitor());
      
      Assert.assertEquals(ir.getControlFlowGraph().exit(), intraSSACFG.getCFG().exit());
      Assert.assertEquals(returnNode,           returnNode(intraSSACFG.getCFG()));
        
      final NullPointerState returnState = intraSSACFG.getState(returnNode);

      Assert.assertNotEquals(State.NOT_NULL, returnState.getState(returnVal));
      Assert.assertNotEquals(State.NULL, returnState.getState(returnVal));
    }    
  }

  public static ISSABasicBlock returnNode(ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg) {
      Collection<ISSABasicBlock> returnNodes = cfg.getNormalPredecessors(cfg.exit());
      Assert.assertEquals(1, returnNodes.size());
      return (ISSABasicBlock) returnNodes.toArray()[0];
  }
  
  public static int returnVal(ISSABasicBlock returnNode) {
    final SSAReturnInstruction returnInst = (SSAReturnInstruction) returnNode.getLastInstruction();
    Assert.assertEquals(1, returnInst.getNumberOfUses());
    return returnInst.getUse(0);
  }
  
  public static IExplodedBasicBlock returnNodeExploded(ISSABasicBlock returnNode, ControlFlowGraph<SSAInstruction, IExplodedBasicBlock> explodedCfg) {
    final IExplodedBasicBlock exit = explodedCfg.exit();
    for (Iterator<IExplodedBasicBlock> it = explodedCfg.getPredNodes(exit); it.hasNext();) {
      IExplodedBasicBlock candidate  = it.next();
      if (candidate.getInstruction() == returnNode.getLastInstruction()) {
        return candidate;
      }
    }
    Assert.assertTrue(false);
    return null;
  }
}
