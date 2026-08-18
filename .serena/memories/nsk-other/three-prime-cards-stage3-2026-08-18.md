# Three "other" prime cards → stage 3 (session 2026-08-18)

1. `prime-wold-accelerated-type-modular-drift-law` — **PROMOTED to stage 3**
2. `prime-valuation-dyadic-fermion-normal-cone-law` — **PROMOTED to stage 3**
3. `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` — advanced, blocked on two classical
   theorems (see §3)

## 1. Wold accelerated type — CLOSED

- `RHTower/GenusOneOccupationCompactBound.lean` — `(14a)`.
  `norm_finitePrimeGenusOnePolarizedPhase_two_sided`: on `‖t‖ ≤ R`, `dist(t, ±ℕ_{≥1}) ≥ δ`,
  `e^{-C} ≤ ‖Φ^(1)_S(t)‖ ≤ e^{C}` **uniformly in the finite prime set `S`**.  Mechanism:
  `reflectedPrimaryLogDefect z = log‖1-z‖ - log‖1+z‖ + 2Re z` is `O(‖z‖³)` for `‖z‖ ≤ 1/4`;
  occupation monomials = reciprocals of distinct `S`-smooth integers (`occupationSmoothIndex`,
  injective) so the majorant is `A/n³`.  Plus `log_blockComparisonGauge_le` `(14c)` and
  `tendsto_mertensProduct_mul_ell2_blockComparisonGauge`.
- `RHTower/SoninDepthApertureRigidity.lean` — `(18e)`.  `(18c)` was ALREADY OWNED as
  `norm_burnolExtendedSoninEvaluationVector_geometric_lower/_upper`.

## 2. Dyadic fermion normal cone — CLOSED (every theorem of the card)

New modules, all axiom-clean and umbrella-wired:

| module | card items |
|---|---|
| `HTGeometry/GeometricHellingerExpansion.lean` | `abs_log_geometricHellingerAffinity_add_le` — the geometric affinity has the parity digit's quadratic expansion (this is *why* `(12)` holds) |
| `HTGeometry/DyadicFisherDecomposition.lean` | `(20)` by telescoping `r/(1-r)² = r/(1+r)² + 4r²/(1-r²)²` |
| `RHTower/PrimeProfileWindowLimit.lean` | REUSABLE: `divProfile`, `tendsto_sum_divProfile` (Mertens window at a profile quotient), `tendsto_finsetSum_Icc_zero` (Tannery on the growing prime window), `tendsto_prod_Icc_of_tendsto_sum_log` |
| `RHTower/SquarefreeCriticalNormalCone.lean` | `radialNome`, `coherentKernel`, `(11)`, `(12)`, `(13)`, `(13b)`, `(22)` |
| `RHTower/CoherentKernelChart.lean` | `primeScaleInner`, `(13c)`–`(13f)`: `K = e^{-Φ(u)}e^{-Φ(v)}e^{⟨F_u,F_v⟩}`, Gram PSD, Schur/Hadamard powers, `coherentKernel_quadForm_nonneg` |
| `RHTower/PrimeProfileFockLimit.lean` | `IsScaleProfile`, `profileNome`, `(13s)`, `(13z)` |
| `RHTower/CriticalDefectMeasure.lean` | `(13aa)`–`(13ac)` (reflection anomaly `4 sinh f (cosh f - 1)`) |
| `RHTower/CoherentEscapeEnds.lean` | `(13g)`–`(13i)`, Cauchy–Schwarz for the Gram form, the rapid end |
| `RHTower/HalfNormalCoherentBoundary.lean` | `(13j)`–`(13n)` with the explicit rate `L/V` |
| `RHTower/WoldNormalScale.lean` | `(17)` |
| `RHTower/HellingerCurvature.lean` | `logAffinityKernel`, `(18)`, `(19)` — one universal kernel read at `a = q^{2^j}` and at `a = -q` |
| `RHTower/DyadicEulerTelescope.lean` | `(23)`–`(27)` |
| `RHTower/EulerMascheroniExponentialIntegral.lean` | NEW ANALYTIC ASSET: `∫₀^∞ e^{-t} log t = -γ` (mathlib's `Γ'(1) = -γ` vs mathlib's Mellin derivative of the Gamma *integral*), `frullani_eq_eulerMascheroni`, `tendsto_ein_sub_log` |
| `RHTower/HalfNormalExactScale.lean` | `(13o)`: `e^{Φ(-V)}/√(e^γ V/2) → 1` |

Reusable takeaways: `tendsto_sum_divProfile` is the one analytic input behind every all-prime
critical limit (it subsumes the card's `(15)`); `IsScaleProfile`'s `|f(t)| ≤ L t` turns
`e^{2f(t_p)}` into `p^{2L/log x}`, so once the cutoff dominates the slope *every* prime below it sits
inside the Taylor window at once — no "finitely many small primes" exception.

## 3. Weyl idealizer card — the exact blockers

`RHTower/XiSamplingIdealizerCollapse.lean` (new, axiom-clean) assembles `(23)` as a one-line
instantiation of Theorem A, and turns §7.1/§7.2 into constructions:
`preservesSamplingIdeal_singleton_firstOrder`, `preservesSamplingIdeal_lattice_shift`,
`not_superlinearSamples_lattice`.  So the sharpness is Lean-proved.

Remaining, both classical and owned nowhere:
1. **Selberg's positive proportion** as `SuperlinearSamples xiRealDivisor`
   (`#{t ∈ [-T,T] : Ξ(t)=0}/T → ∞`).  Hardy's theorem IS owned (`RHTower.exists_Xi_zero_gt`,
   `RHTower/HardyTheorem.lean`) and is NOT enough — the §7.2 lattice shows `N(T) ≍ T` genuinely
   fails.  Corpus raw material that exists: `RHTower/SecondMoment.lean`,
   `RHTower/Sieve/DirichletMVT.lean`, `RHTower/Sieve/InghamCriticalMoment.lean`.
2. **Schwartz kernel + Bochner–Schwartz** for `(27)`.  Both sides are formalized
   (`eq_of_two_dilation_invariance`; `measure_compl_xiRealDivisor_eq_zero`).
