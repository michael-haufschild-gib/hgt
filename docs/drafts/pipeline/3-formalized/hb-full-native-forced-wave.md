# HB: the full native theta-source forced wave equation

Status: `FORMALISED`: four public identities passed exact-module build, axiom audit and lint. RH and complete physical-current extinction remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, retaining independent tensor amplitudes and all physical currents. This result supplies the actual differentiated full-source causal field equation needed for the physical inverse comparison.

## Exact field and equation

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullNativeWave`. Namespace: `RHTower.D4BMNativeResponse`.

Let `Q(X,k)=fullSquarePotential q ![X,exp(k)]` and let `F(a,b)=oddSource s amplitude ((a+b)/2) ((a-b)/2)`. The source is the original continuous odd extension of `timeReducedCoefficient`. With the original native kernel `K`, define

```
U(p,r;X,k)=1/4 integral_0^p integral_0^r
  K((p+r-a-b)/2,(p-r)/2,(a-b)/2;X,k) F(a,b) db da,
p,r>=0.
```

The theorem `fullNullResponse_native` identifies the implemented field with this literal integral, including its null-coordinate Jacobian `1/4`. The implementation uses `arcosh(max(1,Z))` as a continuous extension outside the physical cone. Every source point in the displayed rectangle satisfies `Z>=1`, so the extension is removed exactly. It is not an extra source assumption or a replacement angular kernel.

Write `Delta=exp(2k) partial_X^2+partial_k^2-partial_k`. The theorem `fullNullResponse_wave` proves

```
partial_r partial_p U(p,r;X,k)
 = Q(X,k) F(p,r)/4 + Delta U(p,r;X,k)/(4 cosh((p-r)/2)^2),
p,r>0.
```

All displayed derivatives are actual Lean derivatives of the implemented field. The theorem `fullNullResponse_goursat` also proves the closed-rectangle integral equation

```
U(p,r)=1/4 integral_0^p integral_0^r Q F(a,b) db da
       +integral_0^p integral_0^r Delta U(a,b)/(4 cosh((a-b)/2)^2) db da,
p,r>=0.
```

The theorem `fullNullResponse_boundary` proves `U(p,p;X,k)=0`. This is the original radial Dirichlet boundary, since the target radial coordinate is `(p-r)/2`. Both the kernel reflection and the original odd-source cancellation are proved before applying the integral swap.

## Proof mechanism

The corpus's `source_smooth` proves smoothness of the complete theta half-square in circle radius, angle and both base coordinates. Repeated directional Frechet derivatives give the two horizontal and two logarithmic-height derivatives with joint continuity. The proved compact parametric integration rule first passes these derivatives through the original circle average and then through both source integrals. No angular eigenfunction equation is substituted for the full source.

The full-kernel Goursat identity gives a four-variable integral over two nested source/target triangles. Compact continuity justifies the complete Fubini interchange. After the interchange, the integrated kernel action is exactly the actual `Delta U` established above. The field therefore equals a double primitive of its full forcing and angular action. FTC gives the actual mixed null derivative without differentiating a singular radial quotient at the characteristic.

All three cusp powers and the signed Fourier remainder remain inside the original full source. The proof does not use a numerical source approximation, an assigned derivative, or a supplied inverse-identification premise.

## Conjecture and proof status

The conjecture that the full native source integral satisfies the displayed forced null equation is proved by the above Lean theorems. This completes the angular derivative interchange and mixed-null source equation for this field.

The [native cutoff-residual extension](hb-native-cutoff-residual-wave.md) now subtracts the actual three transported principal channels and proves the exact residual forcing equation, closed-rectangle identity and Dirichlet boundary. The [joint-admission extension](hb-native-residual-joint-admission.md) proves the literal residual's joint-L2 membership and strong continuity, including onset. The [modular-transport extension](hb-native-modular-transport.md) proves the actual full-response modular invariance and residual closed-cell germ compatibility. The remaining comparison must establish the actual joint operator identity and its form-domain admission. The three principal coefficients already equal the constructed `principalTimeResponse` in the previously audited native physical identification module. This result does not yet identify the complete angular residual with `causalJointForcedResponse`; it does not prove the full static-coordinate classical second-derivative equation or evaluate the physical current pairing.

## Corpus searches

Broad OR parametric/integral searches found `hasDerivAt_parametric_intervalIntegral`, including its actual proof method and continuity hypotheses. The implementation applies that precise theorem to the full source. Deep angular-integral searches recovered the original weak radial equation and source integration methods; a generated causal-Laplace/generator group did not establish the required angular identification.

Broad transposition/propagation and deep weak-duality searches were also inspected. The former had interrupted retrieval stages. The latter suggested a strong Klein–Gordon uniqueness theorem; its source requires differentiated L2 curves and a specific inverse-frequency equation, so it cannot be applied directly to the native residual. Its conserved energy using a bounded self-adjoint inverse is a concrete candidate method for the remaining joint comparison. A further wave-filtered deep method search hit its deadline without candidates. The joint-resolvent search found the actual `waveSpatialResolvent` and its bound; these do not by themselves prove the native residual's weak equation in that space.

Candidate statements, source arguments, proof ideas and ingredient groups were inspected. Searches reported incomplete semantic coverage and predominantly source-only compiler metadata. No generated proposal was treated as a proof or absence claim.

## Validation

For the initial four-theorem result, `lake env lean` passed the completed scratch proof. Its final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullNativeWave` passed in 108 seconds, three jobs, without warnings. The isolated audit used 4,080 existing own-module caches and 11 package caches; no old dependency, full or umbrella build was run. That source had 683 lines. The [cutoff-residual extension audit](hb-native-cutoff-residual-wave.md) covers the current 1026-line module and its four additional public theorems.

Only the four new public theorems were checked with `#print axioms`; each reports exactly `[propext, Classical.choice, Quot.sound]`. Source and five build artifacts were installed byte-identically to the audit. The module remains wired once into the area umbrella `formal/GaloisForLFunctions/RHTower.lean`; that umbrella was not built.

Formal lint passed with existing large-file warnings. Module-filtered lexical discovery finds `fullNullResponse_native` at line 242, `fullNullResponse_wave` at line 598, `fullNullResponse_goursat` at line 625 and `fullNullResponse_boundary` at line 661. No mathematical computations were run. The frontier map and route-independent STATUS ledger were unchanged.
