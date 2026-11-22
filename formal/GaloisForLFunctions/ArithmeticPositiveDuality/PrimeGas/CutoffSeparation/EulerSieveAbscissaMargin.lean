import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.MollifiedAlignedCutoffMargin
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeThreshold
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted

/-!
# Zero-free Euler-sieve prime-gas mollifiers and uniform margins across the zero abscissa

Sharp integer-cutoff Möbius polynomials `dirichletSurgPoly M moebiusReal` suffer from Jentzsch zero
condensation on `Re s = 1/2 + zetaZeroWidth` (`jentzsch_moebius_mollified_extinction_near_abscissa`),
creating extraneous mollifier-zero exceptions even where `ζ(w) ≠ 0` and preventing any uniform
lower bound across the zero abscissa.

Replacing integer-size truncation `d ≤ M` with prime-factor truncation `p ≤ y` (`eulerSieveSurgCoeff y`
on `1 ≤ d ≤ eulerPrimorial y`) eliminates **every** mollifier-zero exception across `Re w > 0`:

1. **Exact `y`-rough prime-gas indicator (`dirichletSurgWeight_eulerSieve_eq_coprime_indicator`)**:
   for every `y : ℕ` and every `n ≥ 1`, `dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y) n`
   equals `1` if `gcd(n, y#) = 1` and `0` otherwise, and its Dirichlet polynomial
   `dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w` equals `∏_{p ≤ y} (1 - p^{-w})`,
   which is nonvanishing on all of `Re w > 0` with uniform ordinate-independent two-sided bounds on
   every half-plane `Re w ≥ σ₀ > 0` (`norm_dirichletSurgPoly_eulerSieve_bounds`).
2. **Complete elimination of mollifier-zero exceptions and uniform abscissa-crossing margins
   (`eulerSieve_mollified_margin_iff_zeta_ne_zero`, `uniform_eulerSieve_margin_across_abscissa_on_compact`,
   `abscissaCrossingBox_moebius_zeros_vs_eulerSieve_uniform_margin`)**:
   pointwise across `Re w > 0` (`w ≠ 1`), an Euler-sieve mollified margin holds **if and only if**
   `ζ(w) ≠ 0`; on every `ζ`-zero-free compact set `S ⊂ {Re z > 0} \ {1}` — including boxes that
   straddle `Re z = 1/2 + zetaZeroWidth` where `moebiusReal` provably vanishes for arbitrarily large
   `M`, and across the verified Bohman strip up to height `169/2` — a **single uniform shell depth
   `K₀ ≥ 1`** achieves a uniform positive margin across all `z ∈ S`.
3. **Cofinal Euler attenuation and exact `RH` equivalence of remaining high-ordinate exceptions
   (`tendsto_eulerSieve_limit_zero_on_unit_interval`, `rh_iff_eulerSieve_margin_above_eightyFour_and_half`)**:
   as `y → ∞`, `∏_{p ≤ y} (1 - p^{-σ}) → 0` on `(0, 1]`, ruling out a `y`-uniform unrenormalized
   floor, while at every fixed `y : ℕ`, eliminating all exceptions in
   `{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}` is unconditionally equivalent to `RiemannHypothesis`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter Set Metric
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth)
open scoped Topology ComplexConjugate BigOperators

/-! ### Part 1: Finite Euler-sieve prime-gas mollifiers and uniform half-plane bounds -/

/-- Finite prime aperture `{p ≤ y | p.Prime}` for Euler-sieve prime-gas mollification. -/
def eulerPrimeAperture (y : ℕ) : Finset ℕ :=
  _root_.RHTower.mobiusFinitePrimeAperture y

/-- Primorial cutoff `y# = ∏_{p ≤ y} p` bounding the support of `eulerSieveSurgCoeff y`. -/
def eulerPrimorial (y : ℕ) : ℕ :=
  ∏ p ∈ eulerPrimeAperture y, p

theorem eulerPrimorial_pos (y : ℕ) : 0 < eulerPrimorial y :=
  Finset.prod_pos fun _ hp => (Finset.mem_filter.mp hp).2.pos

theorem one_le_eulerPrimorial (y : ℕ) : 1 ≤ eulerPrimorial y :=
  eulerPrimorial_pos y

/-- Real Euler-sieve surgery coefficients `d ↦ μ(d) · [primeFactors d ⊆ {p ≤ y}]`. -/
def eulerSieveSurgCoeff (y d : ℕ) : ℝ :=
  if d.primeFactors ⊆ eulerPrimeAperture y then (ArithmeticFunction.moebius d : ℝ) else 0

theorem eulerSieveSurgCoeff_one (y : ℕ) : eulerSieveSurgCoeff y 1 = 1 := by
  unfold eulerSieveSurgCoeff
  have hsub : (1 : ℕ).primeFactors ⊆ eulerPrimeAperture y := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact absurd hp.2.1 hp.1.not_dvd_one
  rw [if_pos hsub, ArithmeticFunction.moebius_apply_one]
  norm_num

private theorem dvd_finset_prod_of_subset {T S : Finset ℕ} (hTS : T ⊆ S) :
    (∏ p ∈ T, p) ∣ (∏ p ∈ S, p) := by
  classical
  have hunion : T ∪ (S \ T) = S := Finset.union_sdiff_of_subset hTS
  rw [← hunion, Finset.prod_union Finset.disjoint_sdiff]
  exact dvd_mul_right _ _

private theorem prime_mem_of_dvd_prod_primes {p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hdvd : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty] at hdvd
    exact absurd hdvd hp.not_dvd_one
  | @insert q S hq_not ih =>
    rw [Finset.prod_insert hq_not] at hdvd
    have hq_prime := hS q (Finset.mem_insert_self q S)
    rcases hp.dvd_mul.mp hdvd with hpq | hpS
    · have heq := (hq_prime.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one
      exact heq ▸ Finset.mem_insert_self q S
    · exact Finset.mem_insert_of_mem (ih (fun r hr => hS r (Finset.mem_insert_of_mem hr)) hpS)

/-- **Exact `y`-rough prime-gas indicator:** for every `y : ℕ` and every `n ≥ 1`,
`dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y) n` equals `1` if `n` is coprime to
`eulerPrimorial y` (no prime factor `≤ y`) and `0` otherwise. -/
theorem dirichletSurgWeight_eulerSieve_eq_coprime_indicator (y : ℕ) {n : ℕ} (_hn : 1 ≤ n) :
    dirichletSurgWeight (eulerPrimorial y) (eulerSieveSurgCoeff y) n =
      if Nat.Coprime n (eulerPrimorial y) then 1 else 0 := by
  classical
  set P := eulerPrimorial y
  have hP_pos : 0 < P := eulerPrimorial_pos y
  set g := Nat.gcd n P
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right n hP_pos
  have hg_dvd_n : g ∣ n := Nat.gcd_dvd_left n P
  have hg_dvd_P : g ∣ P := Nat.gcd_dvd_right n P
  have hdiv_sub : g.divisors ⊆ Finset.Icc 1 P := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd.1 hg_pos,
      Nat.le_of_dvd hP_pos (hd.1.trans hg_dvd_P)⟩
  have hzero_out : ∀ d ∈ Finset.Icc 1 P, d ∉ g.divisors →
      (if d ∣ n then eulerSieveSurgCoeff y d else 0) = 0 := by
    intro d _ hd_not
    by_cases hdn : d ∣ n
    · rw [if_pos hdn]
      unfold eulerSieveSurgCoeff
      by_cases hsub : d.primeFactors ⊆ eulerPrimeAperture y
      · rw [if_pos hsub]
        by_cases hsq : Squarefree d
        · have hd_eq : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
          have hd_P : d ∣ P := hd_eq ▸ dvd_finset_prod_of_subset hsub
          exact False.elim (hd_not (Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdn hd_P, hg_pos.ne'⟩))
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
      · rw [if_neg hsub]
    · rw [if_neg hdn]
  unfold dirichletSurgWeight
  rw [← Finset.sum_subset hdiv_sub hzero_out]
  have hcongr : (∑ d ∈ g.divisors, if d ∣ n then eulerSieveSurgCoeff y d else 0) =
      ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdg : d ∣ g := (Nat.mem_divisors.mp hd).1
    rw [if_pos (hdg.trans hg_dvd_n)]
    unfold eulerSieveSurgCoeff
    rw [if_pos]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact prime_mem_of_dvd_prod_primes hp.1 (fun _ hq => (Finset.mem_filter.mp hq).2)
      (hp.2.1.trans (hdg.trans hg_dvd_P))
  rw [hcongr]
  have hmob := _root_.RHTower.sum_divisors_mobCoeff g
  change _ = if g = 1 then (1 : ℝ) else 0
  apply Complex.ofReal_injective
  have h1 : ((∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℝ) : ℝ) : ℂ) =
      ∑ d ∈ g.divisors, _root_.RHTower.mobCoeff d := by
    unfold _root_.RHTower.mobCoeff; push_cast; rfl
  rw [h1, hmob]
  split_ifs <;> simp

/-- Finite Euler-product identity for `dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y)`. -/
theorem dirichletSurgPoly_eulerSieve_eq_prod (y : ℕ) (w : ℂ) :
    dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w =
      ∏ p ∈ eulerPrimeAperture y, (1 - (p : ℂ) ^ (-w)) := by
  have h := _root_.RHTower.pm_finitePrime_coefficient_cpow_sum (eulerPrimeAperture y)
    (fun _ hp => (Finset.mem_filter.mp hp).2) w
  unfold _root_.RHTower.finitePrimeEulerProduct at h
  rw [← h]
  unfold dirichletSurgPoly eulerPrimorial
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  unfold eulerSieveSurgCoeff _root_.RHTower.finitePrimeApertureMobiusCoefficient
    _root_.RHTower.mobiusComplexCoefficient
  split_ifs <;> simp

private theorem norm_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∏ i ∈ s, f i‖ = ∏ i ∈ s, ‖f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.prod_insert ha, norm_mul, ih, Finset.prod_insert ha]

/-- **Uniform ordinate-independent two-sided bounds across `Re w ≥ σ₀ > 0`:** for every `y : ℕ` and
`σ₀ > 0`, `dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w` stays uniformly bounded
away from `0` and `∞` on `{Re w ≥ σ₀}` — right across and left of `1/2 + zetaZeroWidth`. -/
theorem norm_dirichletSurgPoly_eulerSieve_bounds (y : ℕ) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {w : ℂ} (hw : σ₀ ≤ w.re) :
    0 < (∏ p ∈ eulerPrimeAperture y, (1 - (p : ℝ) ^ (-σ₀))) ∧
      (∏ p ∈ eulerPrimeAperture y, (1 - (p : ℝ) ^ (-σ₀))) ≤
        ‖dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w‖ ∧
      ‖dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w‖ ≤
        ∏ p ∈ eulerPrimeAperture y, (1 + (p : ℝ) ^ (-σ₀)) := by
  rw [dirichletSurgPoly_eulerSieve_eq_prod, norm_finset_prod]
  have hfac : ∀ p ∈ eulerPrimeAperture y,
      0 < 1 - (p : ℝ) ^ (-σ₀) ∧
        1 - (p : ℝ) ^ (-σ₀) ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-w)‖ ∧
        ‖(1 : ℂ) - (p : ℂ) ^ (-w)‖ ≤ 1 + (p : ℝ) ^ (-σ₀) := by
    intro p hp
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp_prime.one_lt
    have hp_pos : (0 : ℝ) < p := by positivity
    have hcpow_norm : ‖(p : ℂ) ^ (-w)‖ = (p : ℝ) ^ (-w.re) := by
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp_pos.ne'),
        ← Complex.ofReal_log hp_pos.le, Complex.norm_exp,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
        zero_mul, sub_zero, Real.rpow_def_of_pos hp_pos]
    have hrpow_le : (p : ℝ) ^ (-w.re) ≤ (p : ℝ) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have hrpow_lt1 : (p : ℝ) ^ (-σ₀) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hlo := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-w))
    have hhi := norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-w))
    rw [norm_one, hcpow_norm] at hlo hhi
    exact ⟨by linarith, by linarith, by linarith⟩
  refine ⟨Finset.prod_pos fun p hp => (hfac p hp).1,
    Finset.prod_le_prod (fun p hp => (hfac p hp).1.le) (fun p hp => (hfac p hp).2.1),
    Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp => (hfac p hp).2.2)⟩

/-- **Zero mollifier zeros on `Re w > 0`:** for every `y : ℕ` and every `w` with `0 < w.re`,
`dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w ≠ 0`. -/
theorem dirichletSurgPoly_eulerSieve_ne_zero (y : ℕ) {w : ℂ} (hw : 0 < w.re) :
    dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w ≠ 0 := by
  obtain ⟨hpos, hle, -⟩ := norm_dirichletSurgPoly_eulerSieve_bounds y hw le_rfl
  exact norm_pos_iff.mp (hpos.trans_le hle)

/-! ### Part 2: Complete elimination of mollifier-zero exceptions and uniform abscissa-crossing margins -/

/-- **Complete elimination of mollifier-zero exceptions across `Re w > 0`:** for every `y : ℕ` and
every `w` with `0 < w.re` and `w ≠ 1` (including right on and left of `1/2 + zetaZeroWidth`), a
strict Euler-sieve mollified aligned cutoff margin holds **if and only if** `ζ(w) ≠ 0`. -/
theorem eulerSieve_mollified_margin_iff_zeta_ne_zero (y : ℕ) {w : ℂ}
    (hw : 0 < w.re) (hw1 : w ≠ 1) :
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧
      mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ w <
        ‖mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ w‖) ↔
      riemannZeta w ≠ 0 := by
  constructor
  · rintro ⟨K₀, hK1, hmarg⟩
    exact (mollified_margin_forces_actual_cutoff_margin
      (eulerPrimorial y) (eulerSieveSurgCoeff y) hK1 hw hw1 hmarg).1
  · intro hzeta
    have hQ_ne := dirichletSurgPoly_eulerSieve_ne_zero y hw
    have hZ_ne : _root_.RHTower.zetaPoleUnit w ≠ 0 := by
      rw [_root_.RHTower.zetaPoleUnit_of_ne hw1]
      exact mul_ne_zero (sub_ne_zero.mpr hw1) hzeta
    have hpos : 0 < ‖dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) w *
        _root_.RHTower.zetaPoleUnit w‖ :=
      norm_pos_iff.mpr (mul_ne_zero hQ_ne hZ_ne)
    have hm_lim := (tendsto_mollifiedAlignedReconstructed
      (eulerPrimorial y) (eulerSieveSurgCoeff y) hw).norm
    have herr_lim := tendsto_mollifiedAlignedError_zero
      (eulerPrimorial y) (eulerSieveSurgCoeff y) hw
    obtain ⟨K₀, ⟨hK1, herr_small⟩, hm_large⟩ :=
      (((eventually_ge_atTop 1).and
        (herr_lim.eventually (Iio_mem_nhds (half_pos hpos)))).and
        (hm_lim.eventually (Ioi_mem_nhds (half_lt_self hpos)))).exists
    exact ⟨K₀, hK1, herr_small.trans hm_large⟩

private theorem differentiable_dirichletSurgPoly (M : ℕ) (c : ℕ → ℝ) :
    Differentiable ℂ (dirichletSurgPoly M c) := by
  intro z
  unfold dirichletSurgPoly
  refine DifferentiableAt.fun_sum fun d hd => ?_
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hd).1])
  exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hd0))

/-- **Uniform Euler-sieve margin across the zero abscissa on any `ζ`-zero-free compact set:**
for every compact `S ⊂ {Re z > 0} \ {1}` on which `ζ` has no zeros (regardless of whether `S`
straddles or lies left of `Re z = 1/2 + zetaZeroWidth`) and every `y : ℕ`, there exist `ε > 0` and a
**single uniform shell depth `K₀ ≥ 1`** giving a uniform margin `≥ ε` simultaneously at all `z ∈ S`. -/
theorem uniform_eulerSieve_margin_across_abscissa_on_compact {S : Set ℂ}
    (hS : IsCompact S) (hre : ∀ z ∈ S, 0 < z.re) (h1 : ∀ z ∈ S, z ≠ 1)
    (hzeta : ∀ z ∈ S, riemannZeta z ≠ 0) (y : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ z ∈ S,
      2 * ε ≤ ‖dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) z *
          _root_.RHTower.zetaPoleUnit z‖ ∧
        mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z + ε ≤
          ‖mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z‖ := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨1, one_pos, 1, le_rfl, fun _ hz => False.elim hz⟩
  · -- Step 1: Uniform positive real-part floor `σ₀ > 0` and limit modulus floor `g_min > 0` on `S`.
    obtain ⟨z_re, hz_re_S, hz_re_min⟩ :=
      hS.exists_isMinOn hSne Complex.continuous_re.continuousOn
    set σ₀ : ℝ := z_re.re
    have hσ₀ : 0 < σ₀ := hre z_re hz_re_S
    have hre_ge : ∀ z ∈ S, σ₀ ≤ z.re := fun z hz => hz_re_min hz
    let g (z : ℂ) : ℝ :=
      ‖dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) z *
        _root_.RHTower.zetaPoleUnit z‖
    have hg_cont : Continuous g :=
      ((differentiable_dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y)).mul
        _root_.RHTower.differentiable_zetaPoleUnit).continuous.norm
    obtain ⟨z₀, hz₀_S, hz₀_min⟩ := hS.exists_isMinOn hSne hg_cont.continuousOn
    have hg_pos : 0 < g z₀ := by
      have hQ_ne := dirichletSurgPoly_eulerSieve_ne_zero y (hre z₀ hz₀_S)
      have hZ_ne : _root_.RHTower.zetaPoleUnit z₀ ≠ 0 := by
        rw [_root_.RHTower.zetaPoleUnit_of_ne (h1 z₀ hz₀_S)]
        exact mul_ne_zero (sub_ne_zero.mpr (h1 z₀ hz₀_S)) (hzeta z₀ hz₀_S)
      exact norm_pos_iff.mpr (mul_ne_zero hQ_ne hZ_ne)
    set ε : ℝ := g z₀ / 2
    have hε : 0 < ε := half_pos hg_pos
    -- Step 2: Uniform upper bound on `mollifiedAlignedError` across `z ∈ S`.
    set P_hi : ℝ := ∏ p ∈ eulerPrimeAperture y, (1 + (p : ℝ) ^ (-σ₀))
    have hP_hi_nn : 0 ≤ P_hi := Finset.prod_nonneg fun _ _ => by positivity
    let bClamp (z : ℂ) : ℝ := 3 * ‖z * (z + 1)‖ / max 1 (2 * (z.re + 1))
    have hb_cont : Continuous bClamp := by
      refine (continuous_const.mul ((continuous_id.mul (continuous_id.add continuous_const)).norm)).div
        (continuous_const.max (continuous_const.mul (Complex.continuous_re.add continuous_const)))
        fun _ => ?_
      exact (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'
    obtain ⟨B₀, hB₀⟩ := hS.exists_bound_of_continuousOn hb_cont.continuousOn
    set B_top : ℝ := max B₀ 0
    have hB_nn : 0 ≤ B_top := le_max_right _ _
    have hb_le : ∀ z ∈ S, 3 * ‖z * (z + 1)‖ / (2 * (z.re + 1)) ≤ B_top := by
      intro z hz
      have hmax : max 1 (2 * (z.re + 1)) = 2 * (z.re + 1) :=
        max_eq_right (by have := hre z hz; linarith)
      have h1 : 3 * ‖z * (z + 1)‖ / (2 * (z.re + 1)) = bClamp z := by simp [bClamp, hmax]
      rw [h1]
      exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₀ z hz).trans (le_max_left _ _))
    let trFn (z : ℂ) : ℝ := (‖contrastTransfer 2 z‖ + ‖contrastTransfer 3 z‖) / twoPrimeTransferMass z
    have hct2 : ContinuousOn (contrastTransfer 2) S := fun z hz =>
      (contrastTransfer_analytic ⟨2, by change 1 < (2 : ℕ); norm_num⟩
        ⟨z, hre z hz⟩).continuousAt.continuousWithinAt
    have hct3 : ContinuousOn (contrastTransfer 3) S := fun z hz =>
      (contrastTransfer_analytic ⟨3, by change 1 < (3 : ℕ); norm_num⟩
        ⟨z, hre z hz⟩).continuousAt.continuousWithinAt
    have htm_cont : ContinuousOn twoPrimeTransferMass S :=
      (Complex.continuous_normSq.comp_continuousOn hct2).add
        (Complex.continuous_normSq.comp_continuousOn hct3)
    have htr_cont : ContinuousOn trFn S :=
      ((continuous_norm.comp_continuousOn hct2).add (continuous_norm.comp_continuousOn hct3)).div
        htm_cont fun z hz => (two_prime_transfer_mass_pos ⟨z, hre z hz⟩).ne'
    obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn htr_cont
    set C_tr : ℝ := max C₀ 0
    have hC_nn : 0 ≤ C_tr := le_max_right _ _
    have htr_le : ∀ z ∈ S, trFn z ≤ C_tr := fun z hz =>
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC₀ z hz).trans (le_max_left _ _))
    -- Majorant sequence `U K → 0` bounding `mollifiedAlignedError` on `S`.
    let eChan (B c : ℝ) (K : ℕ) : ℝ :=
      (c * (K : ℝ) + B_top) * B ^ (-(2 * K : ℝ) * σ₀) / (1 - B ^ (-(2 * K : ℝ) * σ₀))
    have hchan_lim : ∀ (B : ℝ), 1 < B → ∀ c : ℝ, Tendsto (eChan B c) atTop (𝓝 0) := by
      intro B hB c
      have hB0 : 0 < B := by linarith
      set rate : ℝ := 2 * σ₀ * Real.log B
      have hrate : 0 < rate := mul_pos (mul_pos zero_lt_two hσ₀) (Real.log_pos hB)
      have hrpow0 : Tendsto (fun K : ℕ => B ^ (-(2 * K : ℝ) * σ₀)) atTop (𝓝 0) := by
        have hlt1 : B ^ (-2 * σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hB (by linarith)
        refine (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hB0.le _) hlt1).congr fun K => ?_
        rw [← Real.rpow_natCast (B ^ (-2 * σ₀)) K, ← Real.rpow_mul hB0.le]; congr 1; ring
      have hK_rpow0 : Tendsto (fun K : ℕ => (K : ℝ) * B ^ (-(2 * K : ℝ) * σ₀)) atTop (𝓝 0) := by
        have hexp := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          (tendsto_natCast_atTop_atTop.const_mul_atTop hrate)).const_mul (1 / rate)
        rw [mul_zero] at hexp
        refine hexp.congr fun K => ?_
        dsimp only [Function.comp_apply]
        rw [pow_one, Real.rpow_def_of_pos hB0]
        have : -(rate * (K : ℝ)) = Real.log B * (-(2 * K : ℝ) * σ₀) := by dsimp only [rate]; ring
        rw [this]; field_simp [hrate.ne']
      have hnum0 : Tendsto (fun K : ℕ => (c * (K : ℝ) + B_top) * B ^ (-(2 * K : ℝ) * σ₀))
          atTop (𝓝 0) := by
        have hc1 := hK_rpow0.const_mul c
        have hc2 := hrpow0.const_mul B_top
        rw [mul_zero] at hc1 hc2
        simpa only [add_zero, add_mul, mul_assoc] using hc1.add hc2
      have hden1 : Tendsto (fun K : ℕ => 1 - B ^ (-(2 * K : ℝ) * σ₀)) atTop (𝓝 1) := by
        simpa only [sub_zero] using tendsto_const_nhds.sub hrpow0
      have hdiv := hnum0.div hden1 one_ne_zero
      rw [zero_div] at hdiv
      exact hdiv.congr fun _ => rfl
    let U (K : ℕ) : ℝ := P_hi * (C_tr * (eChan 2 1 K + eChan 3 2 K))
    have hU_lim : Tendsto U atTop (𝓝 0) := by
      have hsum := (hchan_lim 2 (by norm_num) 1).add (hchan_lim 3 (by norm_num) 2)
      rw [add_zero] at hsum
      have hmul := (hsum.const_mul C_tr).const_mul P_hi
      rw [mul_zero, mul_zero] at hmul
      exact hmul
    obtain ⟨K₀, hK1, hU_small⟩ :=
      ((eventually_ge_atTop 1).and (hU_lim.eventually (Iio_mem_nhds (half_pos hε)))).exists
    refine ⟨ε, hε, K₀, hK1, fun z hz => ?_⟩
    have hz_ge : 2 * ε ≤ g z := by
      have h : g z₀ ≤ g z := hz₀_min hz
      dsimp only [ε]
      linarith
    -- Pointwise domination `mollifiedAlignedError ... K₀ z ≤ U K₀`.
    have herr_dom : mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z ≤ U K₀ := by
      have hQ_hi := (norm_dirichletSurgPoly_eulerSieve_bounds y hσ₀ (hre_ge z hz)).2.2
      have hchan_dom : ∀ (B c : ℝ), 1 < B → 0 ≤ c →
          (c * (K₀ : ℝ) + 3 * ‖z * (z + 1)‖ / (2 * (z.re + 1))) * B ^ (-(2 * K₀ : ℝ) * z.re) /
              (1 - B ^ (-(2 * K₀ : ℝ) * z.re)) ≤
            eChan B c K₀ := by
        intro B c hB hc
        have hB1 : 1 ≤ B := hB.le
        have hK_pos : (0 : ℝ) < 2 * K₀ := by positivity
        have hexp_le : -(2 * K₀ : ℝ) * z.re ≤ -(2 * K₀ : ℝ) * σ₀ := by
          have := hre_ge z hz; nlinarith
        have hr_le : B ^ (-(2 * K₀ : ℝ) * z.re) ≤ B ^ (-(2 * K₀ : ℝ) * σ₀) :=
          Real.rpow_le_rpow_of_exponent_le hB1 hexp_le
        have hr_lt1 : B ^ (-(2 * K₀ : ℝ) * σ₀) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg hB (mul_neg_of_neg_of_pos (by linarith) hσ₀)
        have hden_pos : 0 < 1 - B ^ (-(2 * K₀ : ℝ) * σ₀) := sub_pos.mpr hr_lt1
        have hden_le : 1 - B ^ (-(2 * K₀ : ℝ) * σ₀) ≤ 1 - B ^ (-(2 * K₀ : ℝ) * z.re) := by linarith
        have hnum_le : (c * (K₀ : ℝ) + 3 * ‖z * (z + 1)‖ / (2 * (z.re + 1))) *
              B ^ (-(2 * K₀ : ℝ) * z.re) ≤
            (c * (K₀ : ℝ) + B_top) * B ^ (-(2 * K₀ : ℝ) * σ₀) := by
          refine mul_le_mul (add_le_add le_rfl (hb_le z hz)) hr_le (by positivity) ?_
          positivity
        exact (div_le_div_of_nonneg_right hnum_le (hden_pos.trans_le hden_le).le).trans
          (div_le_div_of_nonneg_left (by positivity) hden_pos hden_le)
      have hK_pos : (0 : ℝ) < 2 * K₀ := by positivity
      have hK_neg : -(2 * K₀ : ℝ) < 0 := by linarith [hK_pos]
      have he2 := hchan_dom 2 1 (by norm_num) (by norm_num)
      rw [one_mul] at he2
      have he3 := hchan_dom 3 2 (by norm_num) (by norm_num)
      have he2_nn : 0 ≤ eChan 2 1 K₀ := by
        have hr_lt1 : (2 : ℝ) ^ (-(2 * K₀ : ℝ) * σ₀) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos hK_neg hσ₀)
        exact div_nonneg (by positivity) (sub_nonneg.mpr hr_lt1.le)
      have he3_nn : 0 ≤ eChan 3 2 K₀ := by
        have hr_lt1 : (3 : ℝ) ^ (-(2 * K₀ : ℝ) * σ₀) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos hK_neg hσ₀)
        exact div_nonneg (by positivity) (sub_nonneg.mpr hr_lt1.le)
      have hal_le : alignedReconstructionError K₀ z ≤ C_tr * (eChan 2 1 K₀ + eChan 3 2 K₀) := by
        unfold alignedReconstructionError
        dsimp only
        have htm_pos : 0 < twoPrimeTransferMass z := two_prime_transfer_mass_pos ⟨z, hre z hz⟩
        have hsum_le : ‖contrastTransfer 2 z‖ *
              (((K₀ : ℝ) + 3 * ‖z * (z + 1)‖ / (2 * (z.re + 1))) * (2 : ℝ) ^ (-(2 * K₀ : ℝ) * z.re) /
                (1 - (2 : ℝ) ^ (-(2 * K₀ : ℝ) * z.re))) +
            ‖contrastTransfer 3 z‖ *
              ((2 * (K₀ : ℝ) + 3 * ‖z * (z + 1)‖ / (2 * (z.re + 1))) * (3 : ℝ) ^ (-(2 * K₀ : ℝ) * z.re) /
                (1 - (3 : ℝ) ^ (-(2 * K₀ : ℝ) * z.re))) ≤
            (‖contrastTransfer 2 z‖ + ‖contrastTransfer 3 z‖) * (eChan 2 1 K₀ + eChan 3 2 K₀) := by
          have h1 := mul_le_mul_of_nonneg_left he2 (norm_nonneg (contrastTransfer 2 z))
          have h2 := mul_le_mul_of_nonneg_left he3 (norm_nonneg (contrastTransfer 3 z))
          nlinarith [norm_nonneg (contrastTransfer 2 z), norm_nonneg (contrastTransfer 3 z),
            he2_nn, he3_nn]
        calc _ ≤ (‖contrastTransfer 2 z‖ + ‖contrastTransfer 3 z‖) *
              (eChan 2 1 K₀ + eChan 3 2 K₀) / twoPrimeTransferMass z :=
              div_le_div_of_nonneg_right hsum_le htm_pos.le
          _ = trFn z * (eChan 2 1 K₀ + eChan 3 2 K₀) := by dsimp only [trFn]; ring
          _ ≤ C_tr * (eChan 2 1 K₀ + eChan 3 2 K₀) :=
              mul_le_mul_of_nonneg_right (htr_le z hz) (add_nonneg he2_nn he3_nn)
      have hal_nn : 0 ≤ alignedReconstructionError K₀ z :=
        (norm_nonneg _).trans (norm_alignedReconstructedCutoff_sub_le hK1 (hre z hz))
      unfold mollifiedAlignedError
      exact mul_le_mul hQ_hi hal_le hal_nn hP_hi_nn
    have herr_lt : mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z < ε / 2 :=
      herr_dom.trans_lt hU_small
    have hsub := norm_mollifiedAlignedReconstructed_sub_le
      (eulerPrimorial y) (eulerSieveSurgCoeff y) hK1 (hre z hz)
    have htri := norm_sub_norm_le
      (dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) z * _root_.RHTower.zetaPoleUnit z)
      (mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z)
    rw [norm_sub_rev] at htri
    exact ⟨hz_ge, by linarith [hz_ge, herr_lt, hsub, htri]⟩

private theorem isCompact_complex_rect (a b c d : ℝ) :
    IsCompact {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d} := by
  have heq : {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d} =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Icc a b ×ˢ Icc c d) := by
    ext z
    simp only [mem_setOf_eq, mem_image, mem_prod, mem_Icc, Prod.exists]
    refine ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨z.re, z.im, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, Complex.re_add_im z⟩, ?_⟩
    rintro ⟨x, y, ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, rfl⟩
    simp [hx1, hx2, hy1, hy2]
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

/-- Unconditional compact box `[1/4, 2] × [1, 3]` straddling `Re z = 1/2 + zetaZeroWidth` in its
interior while lying strictly inside the ordinate-`< 4` zero-free strip of `ζ`. -/
def abscissaCrossingBox : Set ℂ :=
  {z : ℂ | 1 / 4 ≤ z.re ∧ z.re ≤ 2 ∧ 1 ≤ z.im ∧ z.im ≤ 3}

/-- **Sharp Möbius failure vs. Euler-sieve uniform lower bound right across the zero abscissa:**
on `abscissaCrossingBox` (which contains `ball ((1/2 + zetaZeroWidth) + 2i) (1/4)` and has **zero**
zeros of `ζ` unconditionally), `dirichletSurgPoly M moebiusReal` vanishes inside `abscissaCrossingBox`
for arbitrarily large `M` (destroying any uniform lower bound across `Re z = 1/2 + zetaZeroWidth`),
whereas for **every** `y : ℕ`, `mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y)`
achieves a uniform positive margin across the entire `abscissaCrossingBox` at one uniform `K₀ ≥ 1`. -/
theorem abscissaCrossingBox_moebius_zeros_vs_eulerSieve_uniform_margin :
    let s₀ : ℂ := ((1 / 2 + zetaZeroWidth : ℝ) : ℂ) + 2 * Complex.I
    ball s₀ (1 / 4) ⊆ abscissaCrossingBox ∧
      (∀ z ∈ abscissaCrossingBox, z ≠ 1 ∧ riemannZeta z ≠ 0) ∧
      (∀ M₀ : ℕ, ∃ M : ℕ, M₀ ≤ M ∧ ∃ z ∈ abscissaCrossingBox,
        dirichletSurgPoly M moebiusReal z = 0 ∧
        ∀ K : ℕ, mollifiedAlignedReconstructed M moebiusReal K z = 0) ∧
      ∀ y : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ z ∈ abscissaCrossingBox,
        mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z + ε ≤
          ‖mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z‖ := by
  dsimp only
  set s₀ : ℂ := ((1 / 2 + zetaZeroWidth : ℝ) : ℂ) + 2 * Complex.I
  have hw0 : 0 ≤ zetaZeroWidth := GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_nonneg
  have hw_hi : zetaZeroWidth ≤ 1 / 2 :=
    GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_le_half
  have hball_sub : ball s₀ (1 / 4) ⊆ abscissaCrossingBox := by
    intro z hz
    rw [mem_ball_iff_norm] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
    have him := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
    have hs₀_re : s₀.re = 1 / 2 + zetaZeroWidth := by simp [s₀]
    have hs₀_im : s₀.im = 2 := by simp [s₀]
    rw [Complex.sub_re, hs₀_re] at hre
    rw [Complex.sub_im, hs₀_im] at him
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hbox_zf : ∀ z ∈ abscissaCrossingBox, z ≠ 1 ∧ riemannZeta z ≠ 0 := by
    rintro z ⟨hre1, _, him1, him2⟩
    have hne1 : z ≠ 1 := fun he => by have := congrArg Complex.im he; simp at this; linarith
    refine ⟨hne1, ?_⟩
    rcases le_or_gt 1 z.re with hge1 | hlt1
    · exact riemannZeta_ne_zero_of_one_le_re hge1
    · exact _root_.RHTower.riemannZeta_ne_zero_of_abs_im_lt_four (by linarith) hlt1
        (by rw [abs_of_pos (by linarith)]; linarith)
  refine ⟨hball_sub, hbox_zf, fun M₀ => ?_, fun y => ?_⟩
  · obtain ⟨M, hM, z, hz_ball, _, hQ0, hm0, _⟩ :=
      jentzsch_moebius_mollified_extinction_near_abscissa (s₀ := s₀) (by simp [s₀])
        (R := 1 / 4) (by norm_num) M₀
    exact ⟨M, hM, z, hball_sub hz_ball, hQ0, hm0⟩
  · obtain ⟨ε, hε, K₀, hK₀, huni⟩ := uniform_eulerSieve_margin_across_abscissa_on_compact
      (isCompact_complex_rect (1 / 4) 2 1 3)
      (fun z hz => by linarith [hz.1])
      (fun z hz => (hbox_zf z hz).1)
      (fun z hz => (hbox_zf z hz).2) y
    exact ⟨ε, hε, K₀, hK₀, fun z hz => (huni z hz).2⟩

/-- **Uniform Euler-sieve margin across the verified Bohman strip box (`|Im z| ≤ 169/2`):**
for every `0 < δ ≤ 8999 / 24000` and every `y : ℕ`, a single uniform shell cutoff `K₀ ≥ 1` gives a
uniform positive Euler-sieve margin across `{1/2 + δ ≤ Re z ≤ 20999/24000 ∧ |Im z| ≤ 169/2}` — even
if `1/2 + zetaZeroWidth` passes through the box. -/
theorem verified_bohman_box_uniform_eulerSieve_margin {δ : ℝ} (hδ : 0 < δ) (y : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ z : ℂ, 1 / 2 + δ ≤ z.re → z.re ≤ 20999 / 24000 → |z.im| ≤ 169 / 2 →
        mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z + ε ≤
          ‖mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ z‖ := by
  let S : Set ℂ := {z : ℂ | 1 / 2 + δ ≤ z.re ∧ z.re ≤ 20999 / 24000 ∧ -(169 / 2) ≤ z.im ∧ z.im ≤ 169 / 2}
  obtain ⟨ε, hε, K₀, hK₀, huni⟩ := uniform_eulerSieve_margin_across_abscissa_on_compact
    (isCompact_complex_rect (1 / 2 + δ) (20999 / 24000) (-(169 / 2)) (169 / 2))
    (fun z hz => by linarith [hz.1])
    (fun z hz => fun he => by have := hz.2.1; rw [he, Complex.one_re] at this; norm_num at this)
    (fun z hz => riemannZeta_ne_zero_of_strip_abs_im_le_eightyFour_and_half
      (by linarith [hz.1]) (by linarith [hz.2.1]) (abs_le.mpr ⟨hz.2.2.1, hz.2.2.2⟩)) y
  exact ⟨ε, hε, K₀, hK₀, fun z h1 h2 him =>
    (huni z ⟨h1, h2, (abs_le.mp him).1, (abs_le.mp him).2⟩).2⟩

/-! ### Part 3: Cofinal `y → ∞` Euler attenuation and exact `RH` equivalence above `169/2` -/

/-- **Cofinal Euler attenuation on `(0, 1]`:** although each finite Euler-sieve polynomial is
nonvanishing on `Re w > 0`, sending `y → ∞` drives `Q_y^Eul(σ) · zetaPoleUnit(σ) → 0` at every real
`σ ∈ (0, 1]` (including `σ = 1`, where `zetaPoleUnit 1 = 1`), ruling out any `y`-independent
uniform positive floor on `(0, 1]`. -/
theorem tendsto_eulerSieve_limit_zero_on_unit_interval {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    Tendsto (fun y : ℕ =>
      dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) (σ : ℂ) *
        _root_.RHTower.zetaPoleUnit (σ : ℂ)) atTop (𝓝 0) := by
  have hreal := _root_.RHTower.pmCanonicalPrimeEulerProduct_tendsto_zero hσ0 hσ1
  have hcplx : Tendsto (fun y : ℕ =>
      dirichletSurgPoly (eulerPrimorial y) (eulerSieveSurgCoeff y) (σ : ℂ)) atTop (𝓝 0) := by
    have hcast := (Complex.continuous_ofReal.tendsto 0).comp hreal
    rw [Complex.ofReal_zero] at hcast
    refine hcast.congr fun y => ?_
    dsimp only [Function.comp_apply]
    rw [dirichletSurgPoly_eulerSieve_eq_prod, Complex.ofReal_prod]
    unfold eulerPrimeAperture
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
    rw [Complex.ofReal_sub, Complex.ofReal_one, show (p : ℂ) = ((p : ℝ) : ℂ) by simp,
      ← Complex.ofReal_neg, Complex.ofReal_cpow hp_pos.le]
  simpa only [zero_mul] using hcplx.mul_const (_root_.RHTower.zetaPoleUnit (σ : ℂ))

/-- **Exact zero-exception `RH` equivalence for every Euler-sieve prime-gas mollifier `y : ℕ`:**
with all mollifier-zero exceptions eliminated across `Re w > 0`, `RiemannHypothesis` holds if and
only if every remaining point in `{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}` admits a strict
Euler-sieve mollified shell margin. -/
theorem rh_iff_eulerSieve_margin_above_eightyFour_and_half (y : ℕ) :
    RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
        ∃ K₀ : ℕ, 1 ≤ K₀ ∧
          mollifiedAlignedError (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ w <
            ‖mollifiedAlignedReconstructed (eulerPrimorial y) (eulerSieveSurgCoeff y) K₀ w‖ := by
  rw [rh_iff_zetaFree_margin_above_eightyFour_and_half halfTurnClock 0]
  refine forall_congr' fun w => imp_congr_right fun hlo => imp_congr_right fun hhi =>
    imp_congr_right fun _ => ?_
  have hw0 : 0 < w.re := by linarith
  have hw_lt1 : w.re < 1 := by linarith
  have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
  rw [exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw0 hw1,
    eulerSieve_mollified_margin_iff_zeta_ne_zero y hw0 hw1]

#print axioms dirichletSurgWeight_eulerSieve_eq_coprime_indicator
#print axioms norm_dirichletSurgPoly_eulerSieve_bounds
#print axioms eulerSieve_mollified_margin_iff_zeta_ne_zero
#print axioms uniform_eulerSieve_margin_across_abscissa_on_compact
#print axioms abscissaCrossingBox_moebius_zeros_vs_eulerSieve_uniform_margin
#print axioms verified_bohman_box_uniform_eulerSieve_margin
#print axioms tendsto_eulerSieve_limit_zero_on_unit_interval
#print axioms rh_iff_eulerSieve_margin_above_eightyFour_and_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
