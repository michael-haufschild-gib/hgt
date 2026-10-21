# BAG — Bagchi's criterion on compact sets: RH ⟺ strong recurrence of ζ (joint Pechersky on disc unions)

- **ID:** BAG-strong-recurrence-compact-sets-2026-10-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Receiver `ZetaStronglyRecurrent` (`RHTower/ZetaStrongRecurrenceReceiver`), the disc chain (Pechersky → phased Euler products → Kronecker–Weyl → cutoff uniformity → Carlson tail laws), the all-disc theorem `riemannHypothesis_iff_zetaDiscRecurrent`, the cap-free ray-exponent module `ExponentialTypeNotSummableOnPrimeLogsCapFree`.
- **Statement:** `RiemannHypothesis ↔ ZetaStronglyRecurrent`: RH holds iff for every compact `K ⊂ {1/2 < Re s < 1}` and every `ε > 0` the shifts `τ` with `sup_K |ζ(s+iτ) − ζ(s)| < ε` have positive lower density. Lean: `RHTower.riemannHypothesis_iff_zetaStronglyRecurrent` (`RHTower/ZetaStrongRecurrenceOnCompactSets.lean`), axioms `propext, Classical.choice, Quot.sound`.

## Goal

RH ⟸ was in the corpus (`riemannHypothesis_of_zetaStronglyRecurrent`). RH ⟹ needed a universality
argument on compact sets that are not contained in one disc of the strip: every proved universality
statement lived in the Hardy space of one disc, because Pechersky's density lemma is a Hilbert-space
statement and the prime vectors `p^{−s}` are square-summable only on discs inside `Re s > 1/2`.
The corpus search ruled out polynomial Runge (`HTGeometry/RungeDensity` approximates by
differentially algebraic functions) and fixed the route below.

## Route and Lean modules (all wired into `RHTower.lean`)

Cover `K` by finitely many closed discs `D_i = closedBall (z i) (ρ i r₁)`, `i : ι` finite, whose
enlarged discs `closedBall (z i) (ρ i R₂)` lie in the strip and in a zero-free disc.

1. **Horizontal-extent divergence** (`PrimeSumDivergenceOfHorizontalExtent`,
   `exists_primeLogWeightedSum_gt_of_negRay`): for `Φ ≢ 0` entire of exponential type with
   `‖Φ(−x)‖ ≤ A e^{bx}` on the negative ray and `b < 1 − σ`, the sums `Σ_{p<N} p^{−σ}‖Φ(log p)‖`
   are unbounded. The cap-free ray exponent and Phragmén–Lindelöf thin strip are kept; the floor
   `a ≥ −b` comes from the two-ray theorem applied to `Φ(w)e^{κw}`, `κ = (b − a)/2`. Only the
   horizontal extent of the disc family enters.
2. **Direct sum and joint Pechersky** (`HardyDiscTuplesAndJointPechersky`): `DiscTuple ι =
   PiLp 2 (fun _ : ι => HardyDisk)`, prime tuples `u_p = (primeTerm (z i) (ρ i) p)_i`,
   `Σ‖u_p‖² < ∞`, pairing `⟪u_p, e⟫ = F_e(log p)` with
   `F_e(ξ) = Σ_i exp(−conj(z i) ξ) Φ_{e i}(ξ)` (`tuplePairing`), negative-ray rate
   `b = max_i (Re z_i + ρ_i) < 1`. In the closed span `primeSpan` of the prime tuples Pechersky's
   hypotheses hold (summable pairings ⟹ `F_e ≡ 0` ⟹ `e ⊥ primeSpan`), so every `h ∈ primeSpan`
   is a limit of unimodular prime sums with prescribed initial phases
   (`exists_unimodular_primeTuple_sum_approx_extend`).
3. **Which tuples lie in `primeSpan`** (`ExponentialTuplesAndAnalyticMembershipInPrimeSpan`):
   exponential tuples `E_ξ = (q ↦ e^{−(z i + ρ i q)ξ})_i`, `ξ ∈ ℝ`, pair with `e` to `F_e(ξ)`
   (`inner_expTuple`), hence `E_ξ ∈ primeSpan = primeSpanᗮᗮ` (`expTuple_mem_primeSpan`).
   Scaled finite differences `(−1)^k h^{−k} Σ_j C(k,j)(−1)^{k−j} e^{c₀ j h} E_{jh}` converge to
   the monomial tuple of `(s − c₀)^k` uniformly on circles of radius 2 in the disc coordinate
   (`norm_expDiffQuot_pow_sub_le`), hence in the Hardy norm by Cauchy's coefficient estimate
   (`norm_le_of_hardyFun_eq_of_circle_bound`, `mem_of_forall_exists_circle_approx`):
   `monoTuple_mem_primeSpan`. Taylor polynomials of `F` analytic on `ball c₀ R₀` converge
   uniformly on a smaller disc containing all `closedBall (z i) (ρ i R)`, `R > 1`, so the tuple of
   `F` lies in `primeSpan` (`mem_primeSpan_of_differentiableOn_ball`,
   `exists_mem_primeSpan_of_differentiableOn_ball`). Finitely many closed discs of a half plane lie
   in a disc of that half plane (`exists_ball_re_gt_of_forall_lt`, `exists_ball_re_lt_of_forall_lt`).
4. **Joint phased Euler products** (`PhasedEulerProductsApproximateExponentialsOnDiscUnions`,
   `exists_unimodular_eulerProduct_approx_exp_tuple`): for `L ∈ primeSpan`, one family of phases
   `ω` with `‖exp(L_i(q)) − ∏_{p≤y}(1 − ω_p p^{−(z i + ρ i q)})^{−1}‖ < ε` on all discs. The head
   remainder tuple (primes `≤ y₀`, phases one) is the tuple of a function analytic on `Re s > 0`,
   hence in `primeSpan` by 3.
5. **`log ζ` and the uniform density on the union** (`UniformEulerTargetDensityOnDiscUnions`):
   with `ℓ` an analytic log of `(s−1)ζ(s)` on the zero-free disc and `−log(1−s) + iπ` analytic on a
   disc of `Re s < 1`, `L = t_ℓ + t_{−log(1−s)+iπ} ∈ primeSpan` has `exp L_i = ζ` on the discs
   (`exists_mem_primeSpan_exp_eq_zeta`); Kronecker–Weyl on the compact union gives
   `exists_pos_density_eulerTargetReturnSet_zeta_union`; the cutoff-uniform version runs the
   single-disc proof with the random prime sum in `DiscTuple ι` (Chebyshev on the direct sum
   controls every component) — `exists_uniform_pos_density_eulerTargetReturnSet_zeta_union`.
6. **Tail law on the union and assembly** (`ZetaStrongRecurrenceOnCompactSets`): union bound over
   the per-disc tail law `eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt`
   (`eventually_eventually_volume_iUnion_eulerDiscTailBadSet_le`);
   `zetaDiscStronglyRecurrentOn_iUnion_closedBall_of_zeroFree`; under RH a compact `K` with real
   parts in `[a, b']` is covered by discs of radius `ρ₀/2`, `ρ₀ = min(a − 1/2, 1 − b')/4`, centred
   in `K`, with doubled discs in a disc of `Re s > 1/2`
   (`zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_isCompact`), and
   `riemannHypothesis_iff_zetaStronglyRecurrent`.

## Exact positive statements exposed

- The admissible joint targets on finitely many discs are exactly the tuples of `primeSpan`,
  which contains every tuple of a function analytic on a disc containing the enlarged discs; the
  log of `ζ` is such a function (as a sum of two) exactly when `ζ` has no zero on a disc containing
  the discs — this is where RH enters and nowhere else.
- The prime-sum divergence lemma depends only on the negative-ray rate of the pairing function
  (horizontal extent), not on its vertical extent: tall compacta cost nothing.

## Follow-ups closed the same day

7. **The closed span is the polynomial closure** (`PrimeSpanIsThePolynomialClosure`):
   `primeSpan = expTupleSpan` (closed span of the exponential tuples `E_ξ`, `ξ ∈ ℝ`) `=
   polyTupleSpan c₀` (closed span of the monomial tuples about any centre `c₀`), since the prime
   tuples are `E_{log p}` and the tuples of the entire functions `s ↦ p^{−s}` are limits of their
   Taylor polynomials (`mem_of_differentiableOn_ball_of_monoTuple_mem`, the Taylor step for any
   closed submodule containing the monomial tuples). `primeSpanᗮ = {e : F_e ≡ 0}`
   (`mem_orthogonal_primeSpan_iff_tuplePairing_eq_zero`); for one disc `primeSpan = ⊤`
   (`primeSpan_eq_top_of_unique`). So the joint targets are exactly the limits of diagonal
   restrictions of polynomials (equivalently of entire functions) to the discs.
8. **Voronin universality on compact sets** (`ZetaVoroninUniversalityOnCompactSets`,
   unconditional): for `K` compact in the strip contained in an open disc `ball c₀ R₀` on which
   `g` is analytic and nonvanishing (the disc may leave the strip, `K` may be tall), the shifts
   with `sup_K |ζ(s+iτ) − g(s)| < ε` have positive lower density
   (`exists_pos_density_zetaTargetReturnSet_of_isCompact`); corollaries for nonzero constants and
   nonvanishing entire functions. The density statements of module 5 are proved for any target
   `g` whose logarithm tuple lies in `primeSpan`
   (`exists_pos_density_eulerTargetReturnSet_exp_union`,
   `exists_uniform_pos_density_eulerTargetReturnSet_exp_union`); `ζ` under RH is the case where the
   zero-free disc supplies the logarithm.

9. **Joint value denseness** (`ZetaJointValueDensenessAtFinitelyManyPoints`):
   `exists_pos_density_forall_norm_zeta_sub_lt` — for distinct points `s_j` of the strip and
   nonzero `w_j`, the shifts with `|ζ(s_j + iτ) − w_j| < ε` for all `j` have positive lower density
   (target `exp P`, `P` the Lagrange interpolation polynomial of the logarithms).
10. **Connected-complement compacts** (`ZetaVoroninUniversalityOnConnectedComplementCompacts`, via
   the polynomial Runge theorem `HTGeometry/PolynomialRungeOnConnectedComplement`; card
   `polynomial-runge-connected-complement-voronin-2026-10-21`): targets analytic and nonvanishing
   on a simply connected open neighbourhood of `K`, `ℂ \ K` connected.

Not reached: targets merely continuous on `K` and analytic inside (Mergelyan), and targets with
zeros (excluded by `exists_zero_of_mem_zetaTargetReturnSet`).

## Gates
- [x] 0 → 1  well-posed, route fixed by corpus search
- [x] 1 → 2  paper proof complete (module docstrings)
- [x] 2 → 3  Lean: six modules compiled, wired, axioms standard, lint clean
- [ ] 3 → 4  not pursued (user rule)

## Log
- 2026-10-21 — created after the all-disc theorem; corpus searched; route fixed.
- 2026-10-21 — modules 1–6 compiled (`lake --old env lean -j 1 -o`), wired into `RHTower.lean`;
  `riemannHypothesis_iff_zetaStronglyRecurrent` proved; card moved to 3-formalized.
  Same day: (i) `primeSpan` = closure of the polynomial tuples = closure of the exponential
  tuples (`PrimeSpanIsThePolynomialClosure`); (ii) unconditional Voronin universality on compact
  sets for targets analytic and nonvanishing on a disc containing `K`
  (`ZetaVoroninUniversalityOnCompactSets`); both compiled, wired, standard axioms.
