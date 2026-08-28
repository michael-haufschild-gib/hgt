# SC rigged-Krein all-prime phase object

- **ID:** SC-RKAP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` candidate SC (`LAND ORIENT COMP`)
- **Statement:** The pre-divisor prime--Gamma shared-reservoir kernels assemble on the nuclear Deninger height--Köthe test source into one seminorm-continuous reflection-odd symmetric form whose every injective finite prime-axis pullback is exactly the existing source reservoir matrix.

## Goal

Construct the literal infinite prime--Gamma phase object demanded by SC without selecting Xi zeros and without forcing a raw positive completion. The object must retain every prime coefficient, reproduce every finite inertia witness, and live in the source test-space/strong-dual direction already forced by the fixed-Köthe-vector no-go. This closes only SC's infinite carrier/compatibility burden; coefficient-faithful Xi determinant landing and a source-selected positive polarization remain.

## Gates

- [x] 0 → 1 in-progress: exact pre-divisor coefficients, source test space, finite pullbacks, reflection, and continuity bound are specified
- [x] 1 → 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem, targeted `lake env lean`, leaf `lake build`, and axiom audit green
- [ ] 3 → 4 publication-ready: standalone proof and completed priority audit

## Internal frontier

- `[CORPUS]` `preDivisorPrimeCarrier`, `preDivisorSharedReservoirMatrix`, and their reflection/specialization laws exist in `XiPreDivisorReflectionDefectStabilization.lean`.
- `[CORPUS]` every finite off-line packet has inertia `(m-1,1)` or `(1,m-1)` according to orientation, and finite Stokes-port capacity is exhausted in `SourceHorizontalSharedReservoirAmplification.lean` and `SourceHorizontalFinitePortStokesCapacity.lean`.
- `[CORPUS]` `DeningerHeightKothe` is nuclear, sequentially complete, has dense finitely supported group algebra, and its zeroth seminorm is the coordinate `ℓ¹` norm.
- `[CORPUS]` fixed nuclear Köthe vectors cannot create the completed Xi logarithmic-derivative poles; the surviving direction is a dual/corona current in `GammaSewnMobiusApertureStokesKotheVectorLandingNoGo.lean` and `GammaSewnMobiusApertureStokesDualCurrent.lean`.
- `[CORPUS]` bilateral infinite-index Krein carriers already exist. Existence of an abstract infinite Krein space is not the claim.

## External frontier

- `[LITERATURE]` rigged/Krein completions of singular indefinite kernels on nuclear test spaces are known, e.g. Schmidt, *Infinite Infrared Regularization and a State Space for the Heisenberg Algebra*, arXiv:math-ph/0105042.
- `[LITERATURE]` Stokes-filtered/wild harmonic objects with compatible pairings are established in Mochizuki's wild harmonic bundle theory, e.g. arXiv:0803.1344 and arXiv:1902.08298.
- `[LITERATURE]` Deninger-type regularized determinant formulas are proved for specific foliated dynamical systems, e.g. Álvarez López--Kim--Morishita, arXiv:2410.20758.
- `[NOVELTY UNVERIFIED]` no checked source yet supplies the exact pre-divisor prime--Gamma shared-reservoir form, reflection-odd finite-packet reconstruction, or its SC application.

## Conjecture loop

### C1 — reuse any bilateral Krein carrier

`[REDISCOVERED]` The corpus already constructs literal bilateral infinite-index carriers. This does not identify source coefficients or finite Stokes restrictions.

### C2 — analytic scalar orientation

`[FALSIFIED]` Corpus quantized-jump law shows raw all-prime orientation has one-sided residues `4` and `-4`; polar completion cancels the jump but does not create an analytic scalar sign. Scalar orientation is the wrong primitive.

### C3 — rigged source form

`[LEAN-PROVED]` Let `a_p` denote the positive-prime-axis coordinate of `a : DeningerHeightKothe`, let `c_s(p)=preDivisorPrimeCarrier s p`, `w_s(p)=|c_s(p)|`, and `o_s=preDivisorOrientation s`. Define

`L_s(a)=sum_p sqrt(w_s(p)) Re(a_p)`

and

`B_s(a,b)=o_s (sum_p w_s(p) Re(a_p) Re(b_p) - L_s(a)L_s(b))`.

For `0 < Re(s) < 1`, all sums converge absolutely and

`|B_s(a,b)| <= 2 p_0(a) p_0(b)`.

Moreover `B_{1-conj(s)}=-B_s`; at the critical wall `B_s=0`; and for every injective `p : Fin m -> Nat.Primes`, the pullback along the finite prime-axis delta embedding is exactly `(preDivisorSharedReservoirMatrix s p).toQuadraticForm'`. Hence off wall the completed form contains finite positive/negative subspaces of every size on the appropriate reflected side while preserving the opposite one-port finite restrictions.

## Hostile attacks

- The claim is not an RH proof and supplies no Xi determinant.
- It is not a fixed Köthe vector response: it is a jointly seminorm-bounded form, equivalently a source-to-dual operator. Therefore the fixed-vector analyticity no-go does not apply.
- It does not claim a Hilbert-space bounded operator or a Fredholm determinant. Those stronger statements may fail because the source coefficients are not summable in the raw Hilbert topology.
- Exact coefficient recovery is through finite prime-axis pullbacks; no divisor data enter the definition.

## Paper-proof obligations

1. Prove `|c_s(p)| <= 1` throughout the open strip from the existing Bockstein magnitude bound.
2. Prove absolute convergence of `L_s` and the diagonal pairing by domination with the zeroth Köthe seminorm.
3. Prove the bilinear `2 p_0(a)p_0(b)` bound.
4. Prove reflection oddness and wall vanishing coefficientwise.
5. Construct the finite delta embedding and prove exact pullback equality.
6. Transfer the existing finite inertia laws to the completed form.

## Complete paper proof

`[PAPER-PROVED]` Fix `s` with `0 < Re(s) < 1` and put `t=2 Re(s)-1`. Then `|t|<1`. The corpus Bockstein bound gives

`|c_s(p)| <= p^(|t|-1) <= 1`

for every prime, since `p>=2` and `|t|-1<=0`. Thus `0<=w_s(p)<=1` and `0<=sqrt(w_s(p))<=1`.

Let `A(p)` be the positive valuation-one prime axis in the Deninger Kummer lattice. It is injective. For every Köthe test vector `a`, nuclear-source membership at seminorm zero says

`sum_m |a_m| = p_0(a) < infinity`.

Restriction along injective `A` therefore gives `sum_p |a_{A(p)}| <= p_0(a)`. Hence

`sum_p |sqrt(w_s(p)) Re(a_{A(p)})| <= p_0(a)`,

so `L_s(a)` is absolutely convergent and `|L_s(a)|<=p_0(a)`.

For the diagonal series, `|Re(a_{A(p)})|<=|a_{A(p)}|<=p_0(a)` and `w_s(p)<=1`; therefore

`sum_p |w_s(p) Re(a_{A(p)}) Re(b_{A(p)})|
 <= p_0(a) sum_p |b_{A(p)}|
 <= p_0(a)p_0(b)`.

Both series are thus absolutely convergent. Since `|o_s|<=1`, triangle and product estimates give

`|B_s(a,b)| <= p_0(a)p_0(b)+p_0(a)p_0(b)=2p_0(a)p_0(b)`.

Termwise linearity of absolutely convergent series makes `B_s` symmetric and real-bilinear. The displayed bound is joint seminorm continuity and identifies `a |-> B_s(a,-)` as a map into the Köthe strong-dual direction.

Under `s |-> 1-conj(s)`, the corpus gives `c -> -c`, hence `w` and both unsigned series are fixed, while `o -> -o`; consequently `B_{1-conj(s)}=-B_s`. If `Re(s)=1/2`, every `c_s(p)=0`, so `w_s(p)=0` and `B_s=0`.

Now let `p : Fin m -> Nat.Primes` be injective and embed `x : Fin m -> R` as `E_p(x)=sum_i x_i delta_{A(p_i)}`. Injectivity of `A o p` gives `(E_p(x))_{A(r)}=x_i` when `r=p_i` and zero otherwise. Both infinite series reduce to the finite sums

`sum_i w_s(p_i)x_i^2` and `sum_i sqrt(w_s(p_i))x_i`.

Therefore

`B_s(E_p(x),E_p(x))
 = o_s (sum_i w_s(p_i)x_i^2-(sum_i sqrt(w_s(p_i))x_i)^2)`,

which is exactly the quadratic form of `preDivisorSharedReservoirMatrix s p` by the corpus weighted-reservoir identity. The existing finite inertia theorem now transfers verbatim to every such pullback. For arbitrarily large `m`, injective prime packets exist, giving unbounded positive or negative finite subspaces on the reflected side; on the opposite side each finite pullback retains its exact one-port index. No Xi zero, RH statement, determinant, or target polarization was used.

Hostile review: the only analytic input is absolute convergence against `p_0`; no exchange of a conditionally convergent sum occurs. The result lives in the rigged source/dual category, so it neither contradicts the fixed-vector pole no-go nor asserts an unavailable Hilbert/Fredholm completion.

## Lean status

`[LEAN-PROVED]` Formalized in `GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinPhaseObject`.

- `abs_preDivisorRiggedPrimeWittPairing_le`: joint `2 p₀(a) p₀(b)` bound.
- `preDivisorRiggedPrimeWittPairing_lineConj`: reflection oddness.
- `preDivisorRiggedPrimeWittGram_eq_sharedReservoirMatrix`: exact coefficient-faithful finite-packet pullback.
- `preDivisorRiggedPrimeWittGram_inertia_of_left` and `preDivisorRiggedPrimeWittGram_inertia_of_right`: exact finite inertia transfer.
- `preDivisorRiggedPrimeWittPairing_unboundedNegativeIndex_right` and `preDivisorRiggedPrimeWittPairing_unboundedPositiveIndex_left`: unbounded reflected index exhaustion.
- `preDivisorRiggedPrimeWittPhaseObject_capstone`: combined closed theorem.

Verification passed:

- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalRiggedKreinPhaseObject.lean`
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinPhaseObject`
- targeted `#print axioms` on five principal theorems: only `propext`, `Classical.choice`, `Quot.sound`
- forbidden-token scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- corpus index resolves new declarations; module is reachable from `GaloisForLFunctions.RHTower`

## Open core after this claim

`[OPEN CORE]` Construct a coefficient-faithful meromorphic Xi determinant/landing from this rigged source form and prove a source-derived positive polarization. The form itself deliberately retains infinite negative index on one reflected side; positivity is not built in.

## Log

- 2026-08-28 — created in Stage 1 after finite-port exhaustion forced an infinite source/dual carrier.
- 2026-08-28 — C3 paper proof closed; promoted to Stage 2.
- 2026-08-28 — C3 formalized and leaf-built; axiom audit clean; promoted to Stage 3.
