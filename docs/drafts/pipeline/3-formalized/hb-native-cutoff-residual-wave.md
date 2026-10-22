# HB: exact native cutoff-residual wave

Status: `FORMALISED`: four new public identities extend `ThetaCuspHawkingBMFullNativeWave`. The complete physical inverse comparison, current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, retaining independent SS/SV/VV amplitudes and every physical current. This result proves the actual residual field equation needed to compare the literal theta integral with the constructed physical evolution.

## Exact result

Write `U=fullNullResponse`, `alpha_i=principalExponent q i`, `A_i=principalAmplitude q i`, and

```
P_i(p,r)=A_i radialResponse(-alpha_i,s,amplitude,(p+r)/2,(p-r)/2),
C_i(X,k)=cutoffPower(alpha_i,[X,exp(k)]),
V(p,r;X,k)=U(p,r;X,k)-sum_i P_i(p,r) C_i(X,k),
Delta=exp(2k) partial_X^2+partial_k^2-partial_k,
F(p,r)=oddSource(s,amplitude,(p+r)/2,(p-r)/2).
```

The three indices are the original finite set `Fin 3`. The Weyl amplitudes, including the cross term, are retained. The scalar degree is `-alpha_i`, so its eigenvalue is exactly `alpha_i(alpha_i-1)`.

`fullNullResidual_wave` proves, for `p,r>0`,

```
partial_r partial_p V
 = squareResidual(q,[X,exp(k)]) F/4
   + [Delta V + sum_i P_i cutoffCommutator(alpha_i,[X,exp(k)])]
       /(4 cosh((p-r)/2)^2).
```

All derivatives are actual Lean derivatives of `V`, whose definition subtracts the actual three radial integrals from the actual full theta integral. The source residual and commutators are the original corpus definitions.

`fullNullResidual_goursat` proves the corresponding double integral identity over `[0,p] x [0,r]`, for `p,r>=0`, including the zero-length characteristic edges. `fullNullResidual_boundary` proves `V(p,p;X,k)=0` for every real `p`.

`principalNullResponse_physical_ae` proves that, at `s=physicalRate q branch`, the function `x ↦ P_i(tau+x,tau-x)` represents the constructed `principalTimeResponse q branch amplitude i tau` almost everywhere in the original whole-line radial measure. This follows from the already proved native/physical identification and the actual `MemLp.toLp` representatives. There is no supplied coefficient-identification premise.

## Conjecture and proof

The conjecture was that subtracting the actual principal responses leaves exactly the already constructed cutoff forcing. Direct subtraction of second derivatives requires first-derivative regularity. The proof instead subtracts the actual principal Goursat equations from the full-source Goursat equation. Continuity justifies subtraction, finite summation and scalar multiplication through both source integrals. The resulting residual is a double primitive, so endpoint FTC supplies its mixed null derivative.

The angular calculation uses the existing globally smooth `powerCutoffHeight`. Exponential chain rules give

```
(partial_k^2-partial_k) powerCutoffHeight(alpha,exp(k))
 = exp(2k) partial_y^2 powerCutoffHeight(alpha,exp(k)).
```

The existing `cutoffCommutator_height` identifies this with `cutoffCommutator+alpha(alpha-1)cutoffPower`. Actual full-source angular jets give the derivative of the difference. The three eigenvalue terms cancel exactly against the principal equations. `principalSquare_expansion` identifies the remaining source term with `squareResidual`; it retains the complete original three-term square.

The Dirichlet result uses the already proved full-source reflection cancellation and the actual scalar radial boundary values. No temporal, horizon, cusp or tensor current is discarded by this result; their complete pairing has not been evaluated here.

## Next analytical construction

The [native joint-admission extension](hb-native-residual-joint-admission.md) now proves the actual residual's joint-L2 membership, strong continuity, exact representative and zero before and at onset. Its global source-integral identity and bounded-time majorant cover the complete modular cell and the characteristic edges.

The [time-primitive extension](hb-native-time-primitive-elliptic-equation.md) now proves the actual pointwise elliptic equation for the literal double time primitive, its second time derivative and its exact Dirichlet boundary, including the source characteristic edges. The remaining comparison needs this equation in the actual joint operator domain. The [modular-transport extension](hb-native-modular-transport.md) proves the actual modular side conditions as full closed-cell germ agreement. Membership in the first-derivative energy form domain `jointDomain` remains a construction obligation. The displayed null equation alone does not prove a global static-coordinate classical wave equation for the unintegrated field across the characteristic boundary. The bounded-unit-resolvent energy method on the active inverse-identification card still requires the actual weak operator identity.

## Search evidence

Broad OR cutoff/commutator intake and deep residual-forcing and logarithmic-height searches were inspected in declarations, candidate lemmas, source arguments, proof ideas and ingredient groups. They recovered `cutoffCommutator_height`, `powerCutoffHeight_smooth`, the actual height-Laplacian calculus and the physical cutoff-source constructions. Those exact source statements were read and applied in Lean.

The deep dominated-L2 search recovered the actual dominated continuity theorem and its use in `FokasLenellsSecondTimeForcing`. The joint-admission extension supplies its required common L2 majorant for the literal residual. Generated holomorphy/coefficient groups did not discharge that obligation. Search inventory was complete, while semantic coverage and source refresh were partial; compiler metadata was predominantly source-only. No retrieval proposal was treated as a proof.

## Validation

`lake env lean` passed the completed scratch proof without warnings. Final `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullNativeWave` passed in 93 seconds, three jobs, without warnings. The isolated audit reused 4091 existing project dependency caches and 11 installed dependency packages; no dependency or umbrella build ran.

Only the four new public theorems were checked with `#print axioms`; all report exactly `[propext, Classical.choice, Quot.sound]`. The source and five build artifacts were installed byte-identically to the audit. The existing unique area-umbrella import in `formal/GaloisForLFunctions/RHTower.lean` remains wired.

Formal lint passed with existing large-file warnings. Module-filtered lexical discovery finds all four new public theorems: `fullNullResidual_wave` at line 955, `fullNullResidual_boundary` at line 979, `principalNullResponse_physical_ae` at line 986 and `fullNullResidual_goursat` at line 1003.

No mathematical computations, Git commands or launcher runs were used. The frontier map and route-independent STATUS ledger were not edited.

All owned Lean/Lake, search and lint processes finished. The owned scratch and isolated audit directories were removed.
