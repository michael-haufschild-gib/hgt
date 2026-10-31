# Renormalized Intersection Theory of the Scaling Surface (RIT)

Namespace `GaloisForLFunctions.RenormalizedIntersectionTheory`; umbrella
`RenormalizedIntersectionTheory.lean`. Everything is unconditional. Theorems named
`riemannHypothesis_iff_*` are equivalences and `riemannHypothesis_of_*` are implications into RH;
neither is a proof of RH.

## 1. Motivation

Weil's proof for a curve `C/𝔽_q` uses one object on `C × C`, the graph of Frobenius. Its
intersection with the diagonal counts points, the Hodge index on the plane it spans with the fibres
gives the sign (Castelnuovo–Severi), and the graph is canonical, so no twin of `ζ_C` carries it.

Over `ℤ` the corpus has these ingredients separately: the scaling correspondences and their
intersection numbers (the Weil correlation, AOG, HKT), the local hyperbolic planes at every place
(pole–successor states, AKG), the divergent diagonal and its running counterterm (AIT, RBG, AKLT),
and the localized sign problem of the complete Weil matrix (CACT, CAF, RAPT). RIT puts them on one
object, the **renormalized intersection pairing of scaling correspondences**, and answers with
theorems what this geometry delivers: how local poles glue to the global one, where the Hodge index
lives, what Castelnuovo–Severi says, what a Künneth square adds, and what separates `ℤ` from
`𝔽_q[T]`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Scaling correspondences, intersection matrix | `AdelicKreinGeometry.ratCorr`, `HeckeKreinToeplitz.zetaKernel` | `Γ_u · Γ_v = K_ζ(u⁻¹v)`, `K_ζ(u) = W(B, B(· − log u))` |
| Pole class | `AdelicKreinGeometry.boostMassU` | `ℓ(w) = Σ w_i u_i^{−1/2}`; on integer slopes the pole conductor `v_1` |
| Glued global state | `AdelicKreinGeometry.archGlue`, `weilArchState` | `K(|a|) − c|a|^{−1/2}|b|`: pole class + archimedean successor |
| Hyperplane index | `AdelicKreinGeometry.boostPolarIndex` | negative squares on `ℓ = 0` |
| Renormalized Hodge index | `RenormalizedHodgeIndex` | `boostPolarIndex K = 0` |
| Local boosts | `localBoost`, `archBoost`, `primeUnit` | `χ_p(u) = |u|_p^{1/2}`, `χ_∞(u) = |u|^{1/2}` |
| Weights | `weightChar S t` | `χ^t = ∏_{p∈t} χ_p · ∏_{p∈S∖t} χ_p⁻¹` |
| Separated sum / tensor product of local poles | `sumPole`, `tensorPole` | `Σ_p (χ_p + χ_p⁻¹)`, `∏_p (χ_p + χ_p⁻¹)` |
| `S`-units, separating unit | `sUnit`, `sepUnit` | `∏_{q∈S} q^{n_q}`, `∏_{q∈S} q²` |
| Positive index | `posIndex` | `κ₊(k) = κ(−k)` |
| Tensor (Künneth) kernel | `tensorKernel`, `kunnethZeta` | `(k ⊠ l)(g, h) = k(g) l(h)`; `K_ζ ⊠ K_ζ` |
| Spline series, spline weights | `splineSeries`, `splineWeight` | `F(t) = Σ_ρ e^{t(ρ−1/2)} w_ρ`, `K_ζ(u) = F(−log u)` |
| Integer slopes | `integerSlopes`, `finHorizon` | the atoms `1, …, N` of the complete Weil matrix |
| Glued test index | `gluedTestIndex` | supremum over tests of the index of `K_{λ,g}` glued to the archimedean successor |
| `S`-unit group; renormalized infinite product | `sUnitHom`, `sUnits`, `halfPole`, `infTensorPole` | `∏_p ½(χ_p + χ_p⁻¹)` |

## 3. Language

- **Renormalized pairing**: the pairing of scaling correspondences on families of slopes, with the
  pole class split off by the archimedean glue.
- **Pole-orthogonal hyperplane**: `ℓ = 0`; on the integer slopes `v_1^⊥`.
- **Renormalized Hodge index**: no negative square on the pole-orthogonal hyperplane; equivalently
  the glued global state has exactly one negative square, the successor's.
- **Separated sum, tensor product, extremal component**: the three ways to combine local poles.
- **Weight**: a sign pattern `t ⊆ S`; **extremal** weights are `t = ∅` and `t = S`.
- **Archimedean weight**: one that agrees on the primes of `S` with `u ↦ u^s`.
- **Exponents**: `log |u|` on the `S`-units, the dilation factors of the extremal weight.
- **All-or-nothing**: an index that only takes the values `0` and `∞`.

## 4. Mechanisms

**Gluing.**
1. The archimedean place glues by a hyperplane: `κ(K(|a|) − c|a|^{−1/2}|b|) = κ^{(½)}(K) + 1`. For
   Weil's correlation the hyperplane carries the whole index, `κ^{(½)}(K_ζ) = κ(K_ζ)`. The pole pair
   vanishes on the hyperplane, so the glued index is blind to the pole weight.
2. Local poles expand in weights: `∏_{p∈S}(χ_p + χ_p⁻¹) = Σ_{t⊆S} χ^t`; weights pair as `t ↔ S∖t`; at
   the separating unit `∏ q²` the values `∏_{S∖t} q / ∏_t q` are distinct by unique factorization, so
   every weight pair costs exactly one square.
3. The product formula identifies the archimedean boost with the extremal weight on the `S`-units;
   comparing moduli prime by prime shows that the extremal weights are the only archimedean ones.
4. Dividing every local pole by `2` makes the product over all primes finite at each point; on the
   `S`-units it is `2^{−|S|}` times the product over `S`, so it carries every weight pair of every `S`
   and gives the extremal one weight `2^{−|S|}`.
5. Gluing never loses a square, so a test-uniform index ceiling transfers to the glued state; flip
   twins have no ceiling, `ζ` has the ceiling `κ(K_ζ)` attained by the cubic spline.

**Density.**
6. `log p / log q` is irrational, so with two primes the exponents of the extremal weight are dense;
   with one prime (and over `𝔽_q[T]`) they form a lattice.

**Künneth.**
7. On product families the Gram matrix of `k ⊠ l` is a Kronecker product, on arbitrary families its
   diagonal principal submatrix; Kronecker inertia gives both bounds of the index law.
8. The zero side of `K_ζ` is absolutely summable on the strip, so `F` is continuous and the tensor
   square is the exponential sum over pairs of zeros.
9. A bound on `K_ζ` over `ℚ_{>0}` transfers to all real scales by density of `log ℚ_{>0}` and
   continuity of `F`; a bounded spline orbit has zero width `0`.

**Complete Weil matrix.**
10. On integer slopes the boost functional is `√(log N)⟨·, v_1⟩`.
11. A single eigenvalue below `T` and a floor `L` give `⟨Ax, x⟩ ≥ T‖x‖² − (T − L)⟨x, e⟩²`, and
   orthogonality to `v_1` bounds `⟨x, e⟩` by the projection error of `v_1`.

## 5. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Hodge index = index one of the glued state; hyperplane positivity | `renormalizedHodgeIndex_iff_negIndex_archGlue_eq_one`, `renormalizedHodgeIndex_iff` | unconditional |
| The pole class carries no zero: `κ^{(½)}(K_ζ) = κ(K_ζ)` | `boostPolarIndex_ratCorr` | unconditional |
| RH = renormalized Hodge index = positivity on the pole-orthogonal hyperplane | `riemannHypothesis_iff_renormalizedHodgeIndex`, `riemannHypothesis_iff_hyperplane_nonneg` | equivalences |
| Pole blindness; quantum bound; collision mass reads the hyperplane index | `renormalizedHodgeIndex_add_polePair_iff`, `boostPolarIndex_ratCorr_le_iSup_collisionCharge`, `eventually_two_mul_boostPolarIndex_le_collisionMassAfter`, `tendsto_collisionMassAfter_of_boostPolarIndex_eq_top` | unconditional |
| The glued test index selects ζ: `κ(K_ζ) + 1` for `Λ`, `∞` for every finite flip twin; RH = glued test index one | `gluedTestIndex_vonMangoldt`, `gluedTestIndex_finiteFlip_eq_top`, `riemannHypothesis_iff_gluedTestIndex_eq_one` | unconditional; equivalence |
| Separated sum of `|S|` local poles has `|S|` squares | `negIndex_sumPole` | unconditional |
| Tensor product of `|S|` local poles has `2^{|S|−1}` squares; weight count | `negIndex_tensorPole`, `negIndex_weightPairs`, `tensorPole_eq_sum_pairKernel` | unconditional |
| The extremal pair has one square and is the archimedean pole on the `S`-units | `negIndex_extremalPair`, `archBoost_sUnit_eq_weightChar_empty`, `archPole_sUnit_eq_extremalPair` | unconditional |
| The archimedean weights are exactly the extremal ones | `exists_cpow_weightChar_iff` | unconditional |
| The renormalized infinite product of the local poles has infinite index and gives the global pole weight `2^{−|S|}` on the `S`-units | `infTensorPole_sUnit`, `negIndex_infTensorPole_comp_sUnits`, `negIndex_infTensorPole_eq_top`, `infTensorPole_sUnit_eq_arch_add` | unconditional |
| Exponents: dense for two primes, quantized for one | `irrational_log_div_log`, `dense_exponents_pair`, `not_dense_exponents_single`, `log_norm_archBoost_sUnit` | unconditional |
| Künneth inertia law | `hermIndex_kronecker_le_negIndex_tensor`, `negIndex_tensorKernel_le`, `negIndex_tensorKernel_eq_zero`, `negIndex_tensorKernel_self_eq_zero_or_top`, `negIndex_mul_le_negIndex_tensorKernel` | unconditional |
| A bounded Weil kernel is RH; Castelnuovo–Severi for rational scaling correspondences is RH | `riemannHypothesis_of_norm_zetaKernel_le`, `riemannHypothesis_iff_castelnuovoSeveri` | implication; equivalence |
| `K_ζ` has a positive square unless RH; the Künneth square of `K_ζ` is RH | `riemannHypothesis_of_posIndex_zetaKernel_eq_zero`, `riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero` | implication; equivalence |
| Künneth spectral identity: the diagonal square has the sums `ρ + ρ'` as frequencies | `kunnethZeta_eq_tsum`, `zetaKernel_sq_eq_tsum` | unconditional |
| Pole class on integer slopes = complete-Weil ground conductor | `boostMassU_integerSlopes_eq_inner`, `boostMassU_integerSlopes_eq_zero_iff` | unconditional |
| Hodge index with gap at every fixed overlap | `eventually_completeWeil_floor_on_poleHyperplane` | unconditional |

## 6. Tools

**Developed.**
- Finset form of the Krein–Langer index formula (`negIndex_sum_pairKernel_eq_card`) and its use on
  subgroups (`reflectChar_comp`, `sUnits`).
- Separation of weight pairs at `∏_{q∈S} q²` (`weightPairs_separation`).
- Weight calculus: expansion, reflection `t ↔ S∖t`, separating unit, unique-factorization separation
  (`weightValue_injOn`, `weightValue_ne_one`).
- Positive index and Kronecker inertia for tensor kernels on product groups; diagonal restriction.
- Continuity of zero-side exponential sums on the strip and density transfer from `ℚ_{>0}` to `ℝ`.
- Single-window Rayleigh bound and orthogonal-overlap bound for spectral windows.
- Pole-class identity between the archimedean glue and the complete Weil matrix.

**To build.**
- Index lower bounds for Hadamard powers, graded by weight layers.
- The positive index of `K_ζ` (expected infinite; with it the Künneth square is all-or-nothing).
- Hyperplane positivity of the complete Weil matrix along growing overlap schedules.
- A function-field version of the extremal-weight theorem with the quantized factor `q`.
- The heat flow as a homotopy of Pontryagin spaces: a zero configuration of `H_t` and its glued
  state, with index the nonreal right zeros of `H_t` plus one.

## 7. Questions and answers

| Question | Answer |
|---|---|
| Is the global pole a product-formula coupling of local poles with one square? | Not as a sum (`|S|` squares), nor as a tensor product (`2^{|S|−1}`), nor as the renormalized product over all primes (infinite index, global pole of weight `2^{−|S|} → 0`); exactly as the extremal weight of the tensor product, which the product formula makes the archimedean pole and which is the only archimedean-continuous weight. The one square must be supplied by the archimedean place. |
| Is the renormalized pairing definite on the pole-orthogonal hyperplane? | This is RH (`riemannHypothesis_iff_hyperplane_nonneg`). At every fixed overlap the complete Weil form is positive there with a gap above the pole energy. |
| What is Castelnuovo–Severi for `Γ_u`? | `‖K_ζ(u)‖ ≤ K_ζ(1)` at every rational scale; it is RH, and any uniform bound on `K_ζ` already is. |
| Does the Künneth square soften the sign? | No: it is positive iff RH; its diagonal carries the sums `ρ + ρ'`; with infinitely many positive squares its index is `0` or `∞`. |
| What is the canonical counterterm and finite part? | The running counterterm `log N − γ` (Mertens); over `𝔽_q[T]` the ceiling is exact (`ArithmeticKreinLangerTheory.TheFunctionFieldCeilingIsExact`); no fixed counterterm works (`AdelicKreinGeometry.NoFixedCountertermMakesThePrimeKernelPontryagin`). |
| Is the collision quantum an index? | The hyperplane index is bounded by the largest horizontal collision charge; on the finite stratum the collision mass is twice the index plus the multiplicity excess (HKT). |
| What separates `ℤ` from `𝔽_q[T]`? | Density of the extremal weight: dense exponents for two primes, a lattice over one prime and over `𝔽_q[T]`. |
| Why are negative directions confined to low conductors? | At fixed overlap: the low spectrum lives on the low conductors (`RenormalizedArithmeticPotentialTheory.TheLowCompleteWeilSpectrumLivesOnTheLowConductors`), the pole class carries the bottom and the hyperplane sits a gap above it. At growing overlap: open; it is the logarithmic-reserve question of the complete Weil matrix. |
| Does the pairing select `ζ` among its twins? | The glued index is blind to the pole and to unitary twists, but the glued test index is `κ(K_ζ) + 1` for `ζ` and `∞` for every finite flip twin. |
| What is `h⁰` on the scaling surface? | Outside RIT: the theta log-volume `h⁰` of `Spec ℤ` has exact Riemann–Roch (`ArithmeticOrientationGeometry.TheThetaH0OfSpecZ`); on the scaling surface a sign-free Serre-dual pair with subquadratic degree-zero growth is RH (`SelectivePositivityAndThresholdLaws`). |

## 8. Open research topics

1. Hyperplane positivity of the complete Weil matrix at growing overlap (polynomial confinement).
2. The positive index of `K_ζ` and index laws for Hadamard powers.
3. The heat flow as a homotopy of finite-index glued states, with index jumps at collisions.
4. A selection input on the pole-orthogonal hyperplane for twins that are not finite flips (the
   Liouville twin flips every prime): the glued state is blind to the pole and to unitary twists.
5. A sign-free `h⁰` on the scaling surface with quadratic growth, in the language of the pairing.

## 9. Traps

| Trap | Fact |
|---|---|
| Summing local poles gives the global pole | Separated places keep one square each (`negIndex_sumPole`) |
| The tensor product of local poles is the global pole | It has `2^{|S|−1}` squares; only its extremal weight is global |
| The product over all primes, suitably renormalized, recovers the global pole | It has infinite index and weights the global pole by `2^{−|S|} → 0` |
| An index cannot select because it is twin-blind | Twin-blindness is for unitary twists; the glued test index separates every finite flip twin |
| The pole selects ζ on the hyperplane | The glued index is blind to the pole weight |
| A tensor square softens the sign | `K_ζ ⊠ K_ζ` is positive iff RH |
| Castelnuovo–Severi is weaker than RH | At rational scales it is RH; so is any uniform bound on `K_ζ` |
| The archimedean place is one more place | Its exponents are dense once two primes are present |
| A fixed counterterm renormalizes the diagonal | Only the running counterterm `log N − γ` does |
| Positivity at fixed overlap is a step toward RH | It holds unconditionally, with a gap on the hyperplane; RH needs growing overlap |

## 10. Context

| Neighbour | Interface |
|---|---|
| AdelicKreinGeometry | archimedean gluing formula, boost-polar index, pole pair, local signatures |
| HeckeKreinToeplitz | index formula for hyperbolic pairs, `K_ζ`, index = right zeros, collision charges |
| ArithmeticOrientationGeometry | spline orbit, rate theorem, configuration orbit correlations |
| CriticalArithmeticCorrelationTheory, RenormalizedArithmeticPotentialTheory | complete Weil matrix, ground state, Ramanujan vectors |
| HTGeometry | Hermitian inertia, Kronecker inertia, spectral windows |
| ArithmeticKreinLangerTheory, ArithmeticIntersectionTheory, RenormalizedBiarithmeticGeometry | counterterms, circle intersections, survival cones |
| SquareRootThreshold | zero width, tempered configurations |

In the RH research map RIT sits on the seam of the three wall families: the sign (Σ) is the
hyperplane positivity, the count (Π) enters through the zero width and the running counterterm, and
selection (Γ) is the open input on the pole-blind hyperplane.

## 11. Success criteria

The field is developed when each question of §7 has a Lean theorem that answers it — an equivalence,
a classification or a no-go — and each tool of §6 is used by a pillar. It succeeds when one of its sign
statements on the pole-orthogonal hyperplane is proved at a resolution beyond fixed overlap without
passing through an estimate that its own no-gos exclude.

## 12. What counts as a contribution

- A Lean theorem, unconditional, in this folder, wired into the umbrella.
- It states a property of the renormalized pairing (gluing, hyperplane, weights, Künneth, density,
  counterterm) or builds a tool that another pillar uses.
- Equivalences with RH are labelled as such; every positive theorem says which wall it does not cross.
- New objects are built from integers, adeles and Weil's data, never from zero copies.

## 13. Big picture

The geometry Weil used survives over `ℤ` in renormalized form, and RIT pins down where the missing
sign sits. The global pole is the extremal weight of the product of the local poles — the unique
archimedean-continuous one — and the product formula makes its exponents dense as soon as two primes
are present; that density is what distinguishes `ℤ` from `𝔽_q[T]`. No assembly of local poles —
sum, product, or renormalized product over all primes — has one square: the global pole must be
supplied by the archimedean place, and it is. The archimedean place glues by one
hyperplane, orthogonal to the pole class, which on integer slopes is the ground conductor of the
complete Weil matrix. On that hyperplane positivity holds at every fixed overlap with a gap, and
positivity at every resolution is RH. Castelnuovo–Severi for the rational scaling correspondences, a
uniform bound on `K_ζ`, positivity of the Künneth square and glued test index one are each RH: the
intersection-theoretic reformulations do not soften the problem; they concentrate it on one
hyperplane and one function. The glued index is blind to the pole yet separates `ζ` from every finite
flip twin, so the selection input exists inside the pairing; what is missing is the sign.
