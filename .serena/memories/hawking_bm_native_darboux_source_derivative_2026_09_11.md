# HB original Darboux integral and physical source derivative — formalized
Goal ACTIVE; RH and complete physical-current cancellation unproved. Chain literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Previous turn progress verified: native cusp jets. This turn new actual kernel derivative integral and its physical source-radius landing, all source/principal terms retained.

Installed extension formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCharacteristicContact.lean, original declaration prefix unchanged. Six new public theorems namespace RHTower.D4BMNativeCircle:
angularCurrent_integral258: ((Z:complex)^2−1)*argumentFirst=integral1Z angularAction, Z:Ici1.
characteristicFirst def280 = integral0¹ angularAction(1+t(Z−1))/(Z+1).
argumentFirst_volterra284: actual interior derivative equals characteristicFirst.
characteristicFirst_continuousOn314.
characteristicFirst_at_one338: Delta fullSquarePotential/2.
angularKernel_closed_derivative346: actual HasDerivWithinAt onIci1 with characteristicFirst.
angularKernel_source_integral355: fullkernel=originalQ+integral1Z characteristicFirst.
Proof original mean Darboux → weightedcurrent derivative angularAction; original firstcontact yields lowercurrent0; FTCwithendpointlimits; affineintervalsubstitution. Continuous rescaledprimitive via clipped fullangularAction and compactintegral. No scalar eigenvalue substituted.
IMPORTANT search found firstcontact was ALREADY formal: mean_second_at_zero, argumentFirst_tendsto_characteristic, angularKernel_right_derivative. Prior nativecusp card incorrectly framed firstcontactmissing; corrected. Do NOT reproach/reprove old firstcontact.

New formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeSourceDerivative.lean (~160 lines), namespace RHTower.D4BMNativeSourceDerivative, imports CommonSourceGreen + NativeCharacteristicContact.
sourceFirst51 uses original invariant and actual branch slope.
Five publictheorems:
kernelField_source_derivative57: actual HasDerivWithinAt of kernelField(image,q,h,target,![y,X,k]) onsourceIci(characteristic).
sourceFirst_continuousOn73.
kernelField_source_integral107: fullQ+actualintegralfromoriginalsourcecharacteristic reconstructskernel.
kernelField_source_characteristic_derivative125: derivativecontact = DeltaQ/2 * S(1−u_e²).
kernelField_source_derivative_tendsto138: ordinary interior source derivative tends exactsamecontact.
Parameters h:Ici0,target:Iic0,y:Ici originalsourceCharacteristic; both imageBooleans, zero delay included.
Geometry existing kernel_invariant_affine: Z=A−S*radialUnit(y), u'=u²−1, so Z'=S(1−u²). Both static separation and source radius vary atfixedingoingdelay. Originalkernel characteristic sourcefullQ retained.

Validation DONE, DO NOT repeat:
Scratch lake env lean checks. Exact isolated characteristic module build27sec3jobs; source derivative final132sec4jobs clean (earlier attempts failed only interval-membership elaboration).
Eleven NEW publictheorems only #printaxioms via separate scratch, all exactly propext/Classical.choice/Quot.sound. Oldtheorems NOT reaudited.
Audit froze4133 cachedownimports,20521 artifactsymlinks,12source-freeexternaldependencystubs. Only exacttargetlean_lib names declared. No olddependency/fullumbrella build.
Rootoldsource compared byteidentical tosavedoriginal beforeinstall; declarationprefixunchanged. Bothsources10artifactsinstalledbyteidentical. NewSourceDerivative wired onceintoRHTower. index passed3changed; lintpassedwithpreexistinglargefilewarnings; editedlocaldoclinks/importcounts passed. Processcheck noownedLean/Lake. Allowned handles terminal. /tmp/hb-darboux-0911 and4 /tmp/hb-endpoint-*-0911.json removed.
Frontiermap and universalSTATUS untouched. No Git,launch,numericalcomputation,Runpod,subagents.

Card docs/drafts/pipeline/3-formalized/hb-native-darboux-primitive.md (moved from1inprogress). Backlinks updated nativecuspjetcard and common-source-green-transfer. Contains exactresults, completeanalyticalidentity,nextspinTwo target. Goal remainsactive.

NEXT direct hardest attack:
Complete physicalcurrent target 2Omega(B(p,p)/2,B(m,m)/2)=0 stillopen; source transpose needs actual spinTwo-kernel derivative, fullprincipalangularcurrent, physicaladjointpairing.
Minimal nextspinTwo primitive target:
w=Z²−1, Lz=wD²+2ZD. Direct differentiation gives Lz(Lz−2)M=D²(w²M_ZZ).
After actual base-Laplacian commutation LzM=DeltaM, retained R M=−Delta(Delta−2)M=−D²(w²M_ZZ).
Primitive derivative = w*((DeltaM)_Z−2M_Z).
Thus only first invariant characteristic derivative of actual DeltaM is needed to admit both zero primitivejets; no separate global third-invariant-derivative bound needed. Prove actual base/radius derivative commutations on smooth jointnative mean; derive Darboux forDeltaM; generalize private radialcontactargument and show its firstZcontact=Delta²Q/2. Then originalsource spinTwo doubleVolterra identity follows FTC, paralleling existing separated SpinTwoKernelPrimitive.primitive_volterra.
Expected secondendpoint M_ZZ(1)=Delta(Delta−2)Q/8, so retainedsource=−8M_ZZ(1). NOT PROVEDYET.
General candidate recurrence F_n=partialZ^nM:
D[w^(n+1)D F_n]=w^n(Delta−n(n+1))F_n;
F_(n+1)(Z)=integral0¹ t^n(2+t(Z−1))^n/(Z+1)^(n+1)*(Delta−n(n+1))F_n(1+t(Z−1))dt.
Endpoint F_(n+1)(1)=(Delta−n(n+1))F_n(1)/(2(n+1)).
Higher admission NOT theorem, don't assume it.
Actual radialGenerator in CommonRadialSource line34 = derivF/(radialUnit−1)+3F. New derivative predicts interior radialGenerator M=3M−S(1+u)*characteristicFirst; not formalized asgenerator theorem yet. FullPdagger stillhasangularK factor, requires spinTwo/base operatortransfer.

Searches thisturn directresearchtool: broad Darboux endpoint --any; deep mechanismintegrate radialDarboux; principal flux --any --moduleThetaCuspHawkingBM; deep even smooth division --any. Allcachedpartial; broadcoverage~56434files358stale andcompilermostlysourceonly,deepdeadlinefilterandjudgenotcompleted. Inspected candidates/source_arguments/methoddescriptions/proofideas/ingredientsets (last2empty). Useful originalcontact/Goursat endpointFTC; principal search also found CuspFluxReconstruction fullboundarysourceformula but notapplied. Evensearch no smooth-square landing. No searchhelp/implementation/service inspection.
Ownbroadarxiv transmutation/degenerate/Volterra/Fuchsian. Opened primary2606.24700 HouJune2026 positiveFinslerpLaplacianboundary and2607.10483 ZuevskyJuly2026 VOAautomorphiccusps. Neitherfitsactualcomplexcurrent; neitherproofpremise.

Practical nextaudit:
Source-freeowncache under one umbrella lean_lib nameGaloisForLFunctions FAILS becauseLake triesmissingimport. In tempauditdeclare lean_lib name EXACTtargetmodule only; addsecondexactlib ifneeded, leaving other ownimports ascachedoleansoutside declaredroots.
External12packages: pathstubs nameonlylakefile.toml, .lake/build symlinkoriginalpackagebuild, rootmanifestpathrequiresall12. Source-less own .olean/.ilean and optional .olean.hash/.ilean.hash/.trace symlinksat .lake/build/lib/lean; noowncachedsources. Removetargetartifactsymlinks,copyactualtargetsourceandbuildexacttarget. Count imports excludesrebuilttarget.
Lean substype membership with backwardrespectTransparencyfalse: eq_or_lt_of_le needs explicit (show 1≤z.val fromz.property); nearendpoint use subtypeproof by simp or change e≤r; exacttypedhr.le. Do not leave infermetas le_rfl/le_of_lt applied directlyinIci constructors.
Continuous.comp_continuousOn / Tendsto multiplication often need simpa only[Function.comp_def,...] using! to reconcile instance transparency.
For weightedcurrentderivative product normalize id_eq,Pi.pow_apply,Complex.ofReal_one,mul_one before ring.
FTC endpointfilter mono_left needs explicit 𝓝[>]1≤𝓝1.
Affine integral rescale uses smul_integral_comp_add_mul; integral t(z−1) vs (z−1)t normalize mul_comm and add_sub_cancel.
Do not rerun oldaxioms/fullumbrellas. No numericalcomputation. See mem:hawking_bm_native_cusp_jet_transport_2026_09_11.