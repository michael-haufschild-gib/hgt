# Burnol frame completion: dense prime fibres versus valuation Cayley domains

- ID: ULF-BFCC-001
- Stage: 3-formalized; `[PAPER-PROVED]`, Lean-certified (see the Lean certificate below).
- Type: `[BRIDGE]` / exact audit of a proposed realization; no new-field or priority claim.
- Origin: ULF-VFCA-001.
- Claim: in the literal Burnol synthesis norm, the prime-only frame has full graph closure away
  from neutral grade; the valuation frame has an explicit closed unbounded realization. Its
  attenuated Cayley factors have an exact, compact-perturbation-resistant norm cost.

## 1. Carrier and source fidelity

Let H=L2((0,infinity),dt;C), E=H direct-sum H. For ell>0 and k>=1 put

`f_(ell,k)(t)=t exp(-k ell t)`.

For a prime p set ell=log p. At zero ordinate the actual corpus feature at `(p,k-1)` is
`b_(p,k) f_(log p,k)`, with

`b_(p,k)=sqrt(log(p)/p^k)>0`.

This follows from `RoutePPrimitiveBurnolWindowGramSquare`,
`XiWardCubicBurnolWindowConormalIncidence`, `VonMangoldtGammaDepthOneCauchy`, and
`xiGammaEulerValuationNat (p,k-1)=p^k`. Nonvanishing is certified by
`finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero` in
`RoutePPrimitiveBurnolDeningerSecantGraphCompletion`.

The full synthesis norm is retained, including every cross term:

`<f_(ell,j),f_(ell,k)>=2/((j+k)ell)^3`.

Multiplying each feature by its nonzero b changes neither its finite span nor a statement
quantified over all finite coefficient packets. This does NOT identify coefficient ell2 norm
with synthesis norm, discard arithmetic weights from a trace estimate, or transport the Euler
budget. All conclusions below are about this specified H, not a stronger marked-source topology.

### Density lemma

For every ell>0, the complex span D_ell of these features is dense in H. Finite collections at
distinct positive rates are linearly independent.

Proof. If g is orthogonal to D_ell, define, for 0<x<1,

`v(x)=conj(g(-log(x)/ell))*(-log(x))/ell^2`.

Substitution x=exp(-ell t) gives

`integral_0^1 |v(x)| dx=integral_0^infinity |g(t)| t exp(-ell t) dt < infinity`

by Cauchy--Schwarz, and `integral_0^1 v(x)x^(k-1)dx=0` for all k>=1. The finite complex measure
v(x)dx annihilates polynomials, hence continuous functions on [0,1] by uniform polynomial
approximation, hence is zero. Thus g=0 almost everywhere. Hilbert orthogonal-complement
duality proves density. For independence, an almost-everywhere zero finite exponential sum is
everywhere zero by continuity; divide by t, order the distinct rates, multiply by the slowest
exponential, and let t tend to infinity. Its coefficient vanishes; induction finishes. QED.

Different prime powers have distinct rates by unique factorization. Thus the sum of the two
prime feature spaces is algebraically direct despite both being dense.

## 2. Prime-only frame: exact maximal nonclosability

Write

`U(r)=[[sech(r),-tanh(r)],[tanh(r),sech(r)]]`.

Fix distinct primes p,q and a nonzero real a. On the algebraic span in E of their doubled
features define R_a by

`R_a(f_(log p,k) v)=f_(log p,k) U(a log(p)/2)v`,

and the analogous formula for q, for v in C^2. Independence makes this well-defined. These
are exactly the prime-only blocks of `PrimeBurnolThetaModularHolonomy`, now tested against
the Burnol synthesis completion rather than an orthogonal coefficient norm.

**Theorem A.** The closure of Graph(R_a) is E times E. In particular R_a has no closable
extension on E. For a=0 its closure is the identity graph.

Proof. Let P=I_H tensor U(a log(p)/2) and Q=I_H tensor U(a log(q)/2). Both are bounded.
On the dense doubled p-space R_a=P; on the dense doubled q-space R_a=Q. Therefore the graph
closure contains Graph(P) and Graph(Q). For each x it contains their difference `(0,(P-Q)x)`.
Writing ds=sech(a log(p)/2)-sech(a log(q)/2) and
dt=tanh(a log(p)/2)-tanh(a log(q)/2), the two-dimensional difference matrix has determinant
`ds^2+dt^2>0`: dt is nonzero by strict monotonicity of tanh. Thus P-Q is onto E. The graph
closure contains all `(0,y)` and all `(x,Px)`, hence all `(x,y)`. At a=0 R_a is identity on
a dense subspace. QED.

This is a specific instance of the corpus's existing graph-saturation parent theorem
`HTGeometry.GraphSaturationCore.linearGraphSubmodule_closure_eq_top_iff_annihilator`.
The new audit content is its application to the exact declared frame, not a new closure theory.

## 3. Universal weighted-shift boundary

For h>0 define the bounded operator

`(K_h f)(t)=t/(t+h) f(t+h)`.

The corpus already proves its semigroup, eigenfeature, and contraction laws. Direct substitution
extends the same formula to all L2 classes, gives `K_h K_j=K_(h+j)`, and gives

`K_h f_(ell,k)=exp(-h k ell) f_(ell,k)`.

Its adjoint is zero for 0<t<=h and is `(t-h)/t g(t-h)` for t>h. Both K_h and K_h* strictly
decrease the norm of each nonzero vector: their squared-norm integrals have weights strictly
below one wherever a nonzero input has mass. They nevertheless have operator norm one.

### Singular-sequence lemma

Every eta with |eta|=1 has a weakly-null unit sequence u_N with

`||(K_h-eta I)u_N|| <= sqrt(2/N)+1/N^2`, N>=2.

Proof. Choose theta real with exp(i theta)=eta, R=N^2 h, L=N h, and

`u_N(t)=L^(-1/2) exp(i theta t/h) 1_[R,R+L](t)`.

For the ordinary left shift S_h, the functions S_h u_N and eta u_N agree on the overlap of
their support intervals. Their symmetric difference has length 2h, giving error sqrt(2/N).
On the shifted support t+h>=R, so the difference between K_h and S_h is bounded in norm by
h/R=1/N^2. The supports escape to infinity; Cauchy--Schwarz against the tail of any fixed
L2 vector proves weak convergence to zero. Taking eta=1 also proves ||K_h||=1. QED.

For every compact C, Cu_N tends to zero. Hence this boundary sequence remains singular for
`K_h+C-eta I`. Compact (in particular nuclear) perturbation cannot remove this obstruction.

## 4. Closed Cayley realization and exact essential cost

Let |zeta|=1, V=zeta K_h, and define

`T_(zeta,h)=(I-V)(I+V)^(-1)`, with domain Ran(I+V).

**Theorem B.** T_(zeta,h) is densely defined, closed, unbounded, and maximal accretive.
D_ell is a graph core for every ell>0. For 0<=r<1 the bounded operator

`T_(zeta,h,r)=(I-rV)(I+rV)^(-1)`

has both operator norm and essential norm exactly `(1+r)/(1-r)`.

Proof. Strict norm decrease of K_h and K_h* excludes eigenvalue -1 for V and V*. Thus I+V
is injective with dense range. The graph is parametrized by
`x=(I+V)g`, `y=(I-V)g`; from a convergent pair recover g=(x+y)/2, proving closedness.
The exact graph-norm identity is

`||x||^2+||y||^2=2(||g||^2+||Vg||^2)`.

It lies between 2||g||^2 and 4||g||^2. Since I+V maps D_ell bijectively to D_ell, density
from section 1 and this identity prove the graph-core assertion. Also

`Re <T_(zeta,h)x,x> = ||g||^2-||Vg||^2 >=0`,

and `(I+T_(zeta,h)) (I+V)g=2g`, so I+T is onto. For completeness, maximality follows
directly: if an accretive graph extension contains (x,y), choose (u,Tu) in Graph(T) with
u+Tu=x+y. Subtracting gives `(x-u,y-Tu)=(v,-v)` in the extension. Accretivity forces
-||v||^2>=0, so v=0 and the extension equals T.

Take the singular sequence with eta=-1/zeta. Then `(I+V)u_N->0` and
`||(I-V)u_N||->2`, proving unboundedness. Neumann series gives

`||T_(zeta,h,r)|| <= (1+r)/(1-r)`.

Put alpha=(1+r)/(1-r). The exact identity

`T_(zeta,h,r)-alpha I = -[2r/(1-r)](I+V)(I+rV)^(-1)`

shows `(T_(zeta,h,r)-alpha I)u_N->0` for each fixed r<1. Every compact C has Cu_N->0,
so ||T_(zeta,h,r)-C||>=alpha. This proves the asserted norm and essential norm, including
r=0 (identity on infinite-dimensional H). QED.

No bounded B can satisfy `B(I+V+C)=I-V-C` for compact C: the same u_N makes the left side
tend to zero and the right side have norm tending to two. This excludes a compact additive
repair of this exact Cayley equation, not every possible arithmetic correction.

## 5. Valuation-frame replacement: closed, but not bounded

Define the scalar contrast on D_ell by

`A_(a,ell) f_(ell,k)=tanh(a k ell/2) f_(ell,k)`.

**Theorem C.** This map extends boundedly to H exactly when a=0. For a!=0 its closure is
`sgn(a) T_(1,|a|)`. For h=|a| its forced boundary cost is the exact norm in Theorem B.

Proof. The identity `tanh(h lambda/2)=(1-exp(-h lambda))/(1+exp(-h lambda))` and the
eigenfeature identity identify A with the restriction of the stated T. The graph-core assertion
proves equality of closures. Theorem B gives unboundedness; a=0 gives zero. QED.

Equivalently, for every M and a!=0 some finite packet satisfies

`||sum c_k tanh(a k ell/2)b_k f_(ell,k)|| > M ||sum c_k b_k f_(ell,k)||`.

The input is nonzero by independence; otherwise a uniform bound would give a bounded extension.
Nonzero amplitudes b_k do not change this statement, because finite coefficients are arbitrary.

The full doubled valuation frame is also closable and unbounded. Here is its exact closure,
which distinguishes this statement from an assertion only about one channel. For a=h>0,
diagonalize the constant matrix J=[[0,-1],[1,0]] by a fixed unitary; its eigenvalues are i,-i.
Writing L=K_(h/2), the two scalar feature eigenvalues factor as

`sech(h lambda/2)+i tanh(h lambda/2)=i(1-i exp(-h lambda/2))/(1+i exp(-h lambda/2))`,
`sech(h lambda/2)-i tanh(h lambda/2)=-i(1+i exp(-h lambda/2))/(1-i exp(-h lambda/2))`.

Thus the closure in these circular coordinates is

`i T_(i,h/2) direct-sum -i T_(-i,h/2)`,

with domain `Ran(I+iL) direct-sum Ran(I-iL)`. Each summand is closed and each has D_ell
as a graph core, so the direct-sum assertion follows. For a<0 the two summands are exchanged.
No coefficient-basis orthogonality has been imported into the synthesis space.

## 6. Hostile review, meaning, and remaining gate

All proofs above use explicit feature integrals, polynomial approximation/measure uniqueness,
Hilbert duality, bounded-operator Neumann series, and compactness. No RH, zero location,
prime-density estimate, Diophantine approximation, numerics, or proposed Poisson identity enters.

- **Correctness:** Theorem A concerns the original prime-only frame; Theorem C changes it to a
  valuation frame. Their conclusions are not interchangeable. The norm is full Burnol synthesis
  norm, not coefficient norm and not the entrywise modular correction from the aliasing theorem.
- **Parent theory:** dense graph saturation already exists in Lean. Closed Cayley transforms
  are standard: [Eisner--Zwart, Lemma 2.1 and Corollary 3.2](https://arxiv.org/pdf/0805.2020).
  Our opposite sign convention is resolved by the explicit proof above. Weighted-translation
  analytic models are [Phatak--Sholapurkar](https://arxiv.org/pdf/1804.08981); their
  left-invertibility condition is not asserted for our left shift. No new geometry is claimed.
- **Positive survivor:** exact distinction between full multivalued graph collapse and a closed
  unbounded valuation action, with explicit domains and sharp essential cost. Attenuation is an
  audit control, NOT an RH regularization proposal. It cannot be promoted to a source budget.
- **Interpretation:** failure of the original frame is already forced by incompatible actions
  on two dense prime spans. Failure of boundedness for the replacement occurs for any ell>0,
  including one prime. Neither failure alone supplies mixed-prime arithmetic selection.
- **Scope limit:** a marked coefficient/graph topology can retain data forgotten by H. These
  theorems neither exclude such a topology nor construct its actual theta comparison. They
  also do not establish a modular index, an integer charge, or the Xi/Euler budget identity.

The unchanged open edge is actual pre-divisor Poisson completion on a source-marked domain and
the same-representative escape/budget theorem. Calling either prescribed frame that completion
without proving the identification remains invalid. This exact paper theorem is Lean-certified below;
no route is retired by it.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift`, `GaloisForLFunctions.HTGeometry.BurnolWeightedShiftSingularSequence`, `GaloisForLFunctions.HTGeometry.ContractionCayleyTransform`, `GaloisForLFunctions.HTGeometry.BurnolValuationCayleyFrame`, `GaloisForLFunctions.HTGeometry.BurnolDoubledValuationFrame`, `GaloisForLFunctions.RHTower.PrimeBurnolMatrixFrameSaturation`, `GaloisForLFunctions.HTGeometry.BurnolDepthCompletion`, `GaloisForLFunctions.RHTower.PrimeBurnolDepthCompletion`, `GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift`,
`GaloisForLFunctions.HTGeometry.BurnolWeightedShiftSingularSequence`,
`GaloisForLFunctions.HTGeometry.ContractionCayleyTransform`,
`GaloisForLFunctions.HTGeometry.BurnolValuationCayleyFrame`,
`GaloisForLFunctions.HTGeometry.BurnolDoubledValuationFrame` and
`GaloisForLFunctions.RHTower.PrimeBurnolMatrixFrameSaturation` (new), on the corpus modules
`GaloisForLFunctions.HTGeometry.BurnolDepthCompletion`, `GaloisForLFunctions.RHTower.PrimeBurnolDepthCompletion`
and `GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy`; all `lake env lean` clean, built, axiom audit
`[propext, Classical.choice, Quot.sound]` only.  `H = BurnolHalfLineL2 = L²((0,∞))`,
`f_{ℓ,n+1} = burnolDepthFeatureL2 ℓ n`, `D_ℓ = burnolDepthSpan ℓ`, `K_h = burnolWeightedShift h`,
`T_{ζ,h} = burnolCayley`, `U(a log p/2) = primeBurnolThetaBlock a p`.

| Claim | Lean declaration |
|-|-|
| §1 literal features `b_{p,k} f_{log p,k}`, `b_{p,k} ≠ 0`, same span | corpus `primeBurnolWindowFeatureLp_zero_eq_scaled_depth`, `primeBurnolAmplitude_ne_zero`, `primeBurnolLiteralDepthSpan_eq`, `burnolDepthSpan_eq_span_scaled` |
| §1 Gram entries `⟨f_{ℓ,j}, f_{ℓ,k}⟩ = 2/((j+k)ℓ)³` | `inner_burnolDepthFeatureL2` |
| Density lemma: `D_ℓ` dense | corpus `dense_burnolDepthSpan`, `dense_primeBurnolLiteralDepthSpan` |
| Density lemma: distinct rates independent | `linearIndependent_burnolRateFeature`, `linearIndependent_burnolRateFeature_fintype`, `linearIndependent_burnolDepthFeatureL2` |
| Distinct prime powers have distinct rates; `D_p ∩ D_q = 0` | `pow_ne_pow_of_prime_ne`, `twoPrimeRate_injective`, `linearIndependent_twoPrimeFeature`, `disjoint_primeBurnolLiteralDepthSpan` |
| §2 `R_a` well defined on `D_p² ⊕ D_q²` with blocks `U(a log p/2)` | `matrixAction`, `matrixAction_feature`, `primeOnlyMatrixFrameRelation`, `mem_primeOnlyMatrixFrameRelation_iff`, `primeOnlyMatrixFrameRelation_isGraph`, `primeOnlyMatrixFrame`, `graph_primeOnlyMatrixFrame`, `primeOnlyMatrixFrame_left`, `primeOnlyMatrixFrame_right` |
| Theorem A: `det(U_p - U_q) = ds² + dt² > 0`; closure of `Graph(R_a)` is `E × E`; no closable extension; `a = 0` gives the identity graph | `det_primeBurnolThetaBlock_sub_ne_zero`, `matrixAction_surjective`, `primeOnlyMatrixFrameRelation_closure_eq_top`, `not_isClosable_of_le_primeOnlyMatrixFrame`, `primeOnlyMatrixFrame_not_isClosable`, `primeOnlyMatrixFrameRelation_zero` |
| §3 `K_h` bounded, `(K_h f)(t) = t/(t+h) f(t+h)`, `K_hK_j = K_{h+j}`, `K_h f_{ℓ,k} = e^{-hkℓ} f_{ℓ,k}` | `burnolWeightedShift`, `burnolWeightedShift_coeFn`, `norm_burnolWeightedShift_le`, `burnolWeightedShift_comp`, `burnolWeightedShift_depthFeature` |
| §3 adjoint `(K_h^*g)(s) = 1_{s>h}(s-h)/s g(s-h)` | `adjoint_burnolLeftShift`, `adjoint_halfLineShiftWeightMul`, `adjoint_burnolWeightedShift`, `adjoint_burnolWeightedShift_coeFn` |
| §3 strict norm decrease of `K_h`, `K_h^*` | `norm_sq_burnolWeightedShift`, `norm_sq_adjoint_burnolWeightedShift`, `norm_burnolWeightedShift_lt`, `norm_adjoint_burnolWeightedShift_lt` |
| Singular-sequence lemma: weakly null unit `u_N`, `‖(K_h-η)u_N‖ ≤ √(2/N)+1/N²`; `‖K_h‖ = 1`; compact perturbations | `singularPacket`, `norm_singularPacket`, `tendsto_inner_singularPacket`, `norm_sq_leftShift_sub_singularPacket`, `norm_weightedShift_sub_leftShift_singularPacket_le`, `norm_weightedShift_sub_smul_singularPacket_le`, `exists_singularSequence_burnolWeightedShift`, `norm_burnolWeightedShift`, `tendsto_weightedShift_add_compact_sub_singularSequence` |
| Theorem B (generic Cayley): domain `Ran(I+V)`, closed, dense, graph-norm identity, `Re⟨Tx,x⟩ = ‖g‖²-‖Vg‖²`, `I+T` onto, maximal accretive, graph core, unbounded | `CayleyTransform.cayleyPMap`, `cayleyPMap_apply`, `graph_cayleyPMap`, `cayleyPMap_isClosed`, `dense_domain_cayleyPMap`, `norm_sq_add_norm_sq_graph`, `re_inner_cayley`, `isAccretive_cayleyPMap`, `surjective_one_add_cayleyPMap`, `eq_of_isAccretive_of_le`, `graph_domRestrict_closure`, `not_bounded_cayleyPMap` |
| Theorem B for `V = ζK_h`: no eigenvalue `-1` for `V`, `V^*`; `T_{ζ,h}` closed, dense, accretive, maximal, unbounded; `D_ℓ` graph core | `cayleyShift_eq_neg`, `adjoint_cayleyShift_eq_neg`, `exists_singular_one_add_cayleyShift`, `burnolCayley`, `burnolCayley_isClosed`, `dense_domain_burnolCayley`, `isAccretive_burnolCayley`, `eq_burnolCayley_of_isAccretive_of_le`, `surjective_one_add_burnolCayley`, `not_bounded_burnolCayley`, `map_one_add_cayleyShift_burnolDepthSpan`, `burnolCayley_graph_core`, `burnolCayley_depthFeature` |
| Theorem B: `‖T_{ζ,h,r}‖ = ‖T_{ζ,h,r}‖_ess = (1+r)/(1-r)`; identity `T_r - α = -(2r/(1-r))(I+V)(I+rV)⁻¹`; no bounded `B(I+V+C) = I-V-C` | `attenuatedCayley_sub_smul`, `norm_attenuatedCayley_le`, `le_norm_attenuatedCayley_sub_compact`, `norm_burnolAttenuatedCayley`, `le_norm_burnolAttenuatedCayley_sub_compact`, `essNorm_burnolAttenuatedCayley`, `no_bounded_compact_repair_burnolCayley` |
| Theorem C: `A_{a,ℓ} f_{ℓ,k} = tanh(akℓ/2) f_{ℓ,k}`; `tanh(hλ/2) = (1-e^{-hλ})/(1+e^{-hλ})`; `A = sgn(a)T_{1,∣a∣}` on `D_ℓ`; closure `sgn(a)T_{1,∣a∣}`; bounded extension iff `a = 0`; finite packets with nonzero amplitudes | `valuationContrast`, `valuationContrast_depthFeature`, `one_sub_exp_div_one_add_exp`, `valuationContrast_apply`, `graph_valuationContrast`, `valuationContrast_closure`, `not_bounded_valuationContrast`, `exists_bounded_extension_valuationContrast_iff`, `exists_packet_valuationContrast_gt` |
| Doubled valuation frame: `f_k ⊗ U(akℓ/2)v`; circular coordinates; `sech x ± i tanh x` Cayley factors; closure `iT_{i,h/2} ⊕ -iT_{-i,h/2}` (exchanged for `a<0`) on `Ran(I+iL) ⊕ Ran(I-iL)`; closable and unbounded | `doubledValuationFrame`, `doubledValuationFrame_feature`, `circularCoordinates`, `sech_add_I_tanh`, `plusCore_eq`, `minusCore_eq`, `circularCoordinates_doubledValuationFrame`, `map_graph_doubledValuationFrame`, `closure_map_graph_doubledValuationFrame`, `domain_diagSum_circular`, `doubledValuationFrame_isClosable`, `not_bounded_doubledValuationFrame` |

The card's remaining open edge (actual pre-divisor Poisson completion on a source-marked domain)
is stated there as unproved and is not claimed.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
