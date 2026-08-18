import GaloisForLFunctions.RHTower.SteinhausPrimeUnbounded
import GaloisForLFunctions.RHTower.SteinhausLogTailMoment
import GaloisForLFunctions.HTGeometry.FourthMomentEscape

/-!
# The real part of a prime Dirichlet polynomial escapes its second moment

The Steinhaus characters are *isotropic*: `E[X_n X_m] = 0` for all `n, m ≥ 2`, because `X_n X_m`
is the character of `n m ≠ 1`.  Hence a prime Dirichlet polynomial has vanishing *second* moment
in the unconjugated sense,

```text
E[S_N²] = 0 ,      so      E[(Re S_N)²] = ½ E‖S_N‖² = ½ ∑_{p<N} p^{-2σ} .
```

Together with the prime fourth moment `E‖S_N‖⁴ ≤ 2 (E‖S_N‖²)²` this gives a uniform
Paley–Zygmund bound for the *real part*: with probability at least `1/32` the real part exceeds
half the square root of the second moment.  This is the anti-concentration statement the Helson
seam argument needs, because the boundary estimate constrains only `Re(G + H)`.
-/

noncomputable section

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- **Isotropy of a Dirichlet polynomial with indices above one.** -/
theorem integral_dpoly_sq (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 2 ≤ n) :
    ∫ ω, (∑ n ∈ s, (a n : ℂ) * X n ω) ^ 2 ∂steinhausMeasure = 0 := by
  classical
  have hne : ∀ n ∈ s, n ≠ 0 := fun n hn => by have := hs n hn; omega
  have hprod : ∀ (n m : ℕ), Integrable (fun ω => X n ω * X m ω) steinhausMeasure := by
    intro n m
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_X n).mul (measurable_X m)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_mul, norm_X, norm_X, one_mul]
  have hexp : ∀ ω : Omega, (∑ n ∈ s, (a n : ℂ) * X n ω) ^ 2
      = ∑ n ∈ s, ∑ m ∈ s, ((a n : ℂ) * (a m : ℂ)) * (X n ω * X m ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum (f := fun n (ω : Omega) =>
      ∑ m ∈ s, ((a n : ℂ) * (a m : ℂ)) * (X n ω * X m ω)) _
    fun n _ => integrable_finsetSum _ fun m _ => (hprod n m).const_mul _]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [integral_finsetSum (f := fun m (ω : Omega) => ((a n : ℂ) * (a m : ℂ)) * (X n ω * X m ω)) _
    fun m _ => (hprod n m).const_mul _]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [integral_const_mul]
  have hmul : ∀ ω : Omega, X n ω * X m ω = X (n * m) ω :=
    fun ω => (X_mul (hne n hn) (hne m hm) ω).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hmul)]
  have hnm0 : n * m ≠ 0 := Nat.mul_ne_zero (hne n hn) (hne m hm)
  have hnm1 : n * m ≠ 1 := by
    have h1 := hs n hn
    have h2 := hs m hm
    nlinarith
  rw [integral_X_eq_zero hnm0 hnm1, mul_zero]

/-! ### Real moments of the prime polynomial -/

theorem integrable_steinhausPrimePoly_sq (σ : ℝ) (N : ℕ) :
    Integrable (fun ω => steinhausPrimePoly σ N ω ^ 2) steinhausMeasure := by
  refine Integrable.mono' (integrable_const ((∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))|) ^ 2))
    (((measurable_steinhausPrimePoly σ N).pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_steinhausPrimePoly_le σ N ω) 2

theorem integral_steinhausPrimePoly_sq (σ : ℝ) (N : ℕ) :
    ∫ ω, steinhausPrimePoly σ N ω ^ 2 ∂steinhausMeasure = 0 :=
  integral_dpoly_sq (fun p => ((p : ℝ) ^ (-σ))) (primeSet N)
    fun _ hp => (prime_of_mem_primeSet hp).two_le

/-- **The second moment of the real part is half the diagonal.** -/
theorem integral_re_sq_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    ∫ ω, ((steinhausPrimePoly σ N ω).re) ^ 2 ∂steinhausMeasure
      = (∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))) / 2 := by
  have hpt : ∀ ω : Omega, ((steinhausPrimePoly σ N ω).re) ^ 2
      = (‖steinhausPrimePoly σ N ω‖ ^ 2 + ((steinhausPrimePoly σ N ω) ^ 2).re) / 2 := by
    intro ω
    set z := steinhausPrimePoly σ N ω with hz
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
      rw [sq, Complex.mul_re]
      ring
    rw [hnorm, hsq]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hi1 : Integrable (fun ω => ‖steinhausPrimePoly σ N ω‖ ^ 2) steinhausMeasure :=
    integrable_normSq_steinhausPrimePoly σ N
  have hi2 : Integrable (fun ω => ((steinhausPrimePoly σ N ω) ^ 2).re) steinhausMeasure := by
    have hmeas : Measurable fun ω : Omega => ((steinhausPrimePoly σ N ω) ^ 2).re :=
      Complex.measurable_re.comp ((measurable_steinhausPrimePoly σ N).pow_const 2)
    refine Integrable.mono' (integrable_const ((∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))|) ^ 2))
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : |((steinhausPrimePoly σ N ω) ^ 2).re| ≤ ‖steinhausPrimePoly σ N ω ^ 2‖ :=
      Complex.abs_re_le_norm _
    rw [Real.norm_eq_abs]
    refine le_trans h1 ?_
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_steinhausPrimePoly_le σ N ω) 2


  rw [integral_div, integral_add hi1 hi2, integral_normSq_steinhausPrimePoly]
  have hre : ∫ ω, ((steinhausPrimePoly σ N ω) ^ 2).re ∂steinhausMeasure = 0 := by
    have h := integral_re (𝕜 := ℂ) (integrable_steinhausPrimePoly_sq σ N)
    rw [integral_steinhausPrimePoly_sq] at h
    simpa using h
  rw [hre, add_zero]

/-- The fourth moment of the real part is dominated by the fourth moment of the modulus. -/
theorem integral_re_pow_four_le (σ : ℝ) (N : ℕ) :
    ∫ ω, (((steinhausPrimePoly σ N ω).re) ^ 2) ^ 2 ∂steinhausMeasure
      ≤ 2 * (∑ p ∈ primeSet N, ((p : ℝ) ^ (-σ)) ^ 2) ^ 2 := by
  have hi4 : Integrable (fun ω => (‖steinhausPrimePoly σ N ω‖ ^ 2) ^ 2) steinhausMeasure :=
    integrable_normSq_sq_steinhausPrimePoly σ N
  have hi4' : Integrable (fun ω => (((steinhausPrimePoly σ N ω).re) ^ 2) ^ 2)
      steinhausMeasure := by
    have hmeas4 : Measurable fun ω : Omega => (((steinhausPrimePoly σ N ω).re) ^ 2) ^ 2 :=
      ((Complex.measurable_re.comp (measurable_steinhausPrimePoly σ N)).pow_const 2).pow_const 2
    refine Integrable.mono' (integrable_const ((∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))|) ^ 4))
      hmeas4.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : |(steinhausPrimePoly σ N ω).re| ≤ ∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))| :=
      le_trans (Complex.abs_re_le_norm _) (norm_steinhausPrimePoly_le σ N ω)
    have h0 : (0:ℝ) ≤ |(steinhausPrimePoly σ N ω).re| := abs_nonneg _
    have hsq : ((steinhausPrimePoly σ N ω).re) ^ 2 = |(steinhausPrimePoly σ N ω).re| ^ 2 :=
      (sq_abs _).symm
    rw [hsq, ← pow_mul]
    exact pow_le_pow_left₀ h0 h1 4
  have hmono : ∫ ω, (((steinhausPrimePoly σ N ω).re) ^ 2) ^ 2 ∂steinhausMeasure
      ≤ ∫ ω, (‖steinhausPrimePoly σ N ω‖ ^ 2) ^ 2 ∂steinhausMeasure := by
    refine integral_mono hi4' hi4 fun ω => ?_
    have h1 : |(steinhausPrimePoly σ N ω).re| ≤ ‖steinhausPrimePoly σ N ω‖ :=
      Complex.abs_re_le_norm _
    have hsq : ((steinhausPrimePoly σ N ω).re) ^ 2 = |(steinhausPrimePoly σ N ω).re| ^ 2 :=
      (sq_abs _).symm
    rw [hsq, ← pow_mul, ← pow_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 4
  refine le_trans hmono ?_
  have hfour : ∀ ω : Omega, (‖steinhausPrimePoly σ N ω‖ ^ 2) ^ 2
      = ‖steinhausPrimePoly σ N ω‖ ^ 4 := fun ω => by rw [← pow_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfour),
    integral_normSq_sq_steinhausPrimePoly]
  have hnn : (0:ℝ) ≤ ∑ p ∈ primeSet N, ((p : ℝ) ^ (-σ)) ^ 4 :=
    Finset.sum_nonneg fun p _ => by positivity
  linarith


/-! ### The anti-concentration bound for the real part -/

theorem integrable_re_sq_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    Integrable (fun ω => ((steinhausPrimePoly σ N ω).re) ^ 2) steinhausMeasure := by
  have hmeas : Measurable fun ω : Omega => ((steinhausPrimePoly σ N ω).re) ^ 2 :=
    (Complex.measurable_re.comp (measurable_steinhausPrimePoly σ N)).pow_const 2
  refine Integrable.mono' (integrable_const ((∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))|) ^ 2))
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : |(steinhausPrimePoly σ N ω).re| ≤ ∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))| :=
    le_trans (Complex.abs_re_le_norm _) (norm_steinhausPrimePoly_le σ N ω)
  have hsq : ((steinhausPrimePoly σ N ω).re) ^ 2 = |(steinhausPrimePoly σ N ω).re| ^ 2 :=
    (sq_abs _).symm
  rw [hsq]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

theorem integrable_re_pow_four_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    Integrable (fun ω => (((steinhausPrimePoly σ N ω).re) ^ 2) ^ 2) steinhausMeasure := by
  have hmeas4 : Measurable fun ω : Omega => (((steinhausPrimePoly σ N ω).re) ^ 2) ^ 2 :=
    ((Complex.measurable_re.comp (measurable_steinhausPrimePoly σ N)).pow_const 2).pow_const 2
  refine Integrable.mono' (integrable_const ((∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))|) ^ 4))
    hmeas4.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : |(steinhausPrimePoly σ N ω).re| ≤ ∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))| :=
    le_trans (Complex.abs_re_le_norm _) (norm_steinhausPrimePoly_le σ N ω)
  have hsq : ((steinhausPrimePoly σ N ω).re) ^ 2 = |(steinhausPrimePoly σ N ω).re| ^ 2 :=
    (sq_abs _).symm
  rw [hsq, ← pow_mul]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 4

theorem sum_sq_eq_sum_two (σ : ℝ) (N : ℕ) :
    ∑ p ∈ primeSet N, ((p : ℝ) ^ (-σ)) ^ 2 = ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeSet hp).pos
  rw [sq, ← Real.rpow_add hp0]
  congr 1
  ring

/-- **The real part of a prime Dirichlet polynomial exceeds half the square root of its second
moment with probability at least `1/32`.** -/
theorem measure_re_steinhausPrimePoly_gt (σ : ℝ) (N : ℕ)
    (hpos : 0 < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))) :
    (1 : ℝ) / 32 ≤ (steinhausMeasure {ω | (∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))) / 4
        < ((steinhausPrimePoly σ N ω).re) ^ 2}).toReal := by
  set A : ℝ := ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) with hAdef
  have hmean : ∫ ω, ((steinhausPrimePoly σ N ω).re) ^ 2 ∂steinhausMeasure = A / 2 :=
    integral_re_sq_steinhausPrimePoly σ N
  have hfour : ∫ ω, (((steinhausPrimePoly σ N ω).re) ^ 2) ^ 2 ∂steinhausMeasure
      ≤ 8 * (∫ ω, ((steinhausPrimePoly σ N ω).re) ^ 2 ∂steinhausMeasure) ^ 2 := by
    rw [hmean]
    refine le_trans (integral_re_pow_four_le σ N) ?_
    rw [sum_sq_eq_sum_two, ← hAdef]
    ring_nf
    linarith
  have hposint : 0 < ∫ ω, ((steinhausPrimePoly σ N ω).re) ^ 2 ∂steinhausMeasure := by
    rw [hmean]; linarith
  have hpz := measure_sq_gt_half_ge (μ := steinhausMeasure)
    (g := fun ω => (steinhausPrimePoly σ N ω).re)
    (Complex.measurable_re.comp (measurable_steinhausPrimePoly σ N))
    (integrable_re_sq_steinhausPrimePoly σ N) (integrable_re_pow_four_steinhausPrimePoly σ N)
    (C := 8) (by norm_num) hfour hposint
  rw [hmean] at hpz
  have hset : {ω : Omega | (1 / 2 : ℝ) * (A / 2) < ((steinhausPrimePoly σ N ω).re) ^ 2}
      = {ω : Omega | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hset] at hpz
  norm_num at hpz ⊢
  linarith


/-! ### The second moment is unbounded arbitrarily close to the half line -/

/-- **For every level and every one-sided neighbourhood of the half line there is a point of the
neighbourhood and a cut at which the prime second moment exceeds the level.** -/
theorem exists_sigma_primeSum_gt (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (σ : ℝ) (N : ℕ), 1 / 2 < σ ∧ σ < 1 / 2 + δ ∧
      M < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ)))) := by
    have h := tendsto_sum_primeCoeff_atTop (σ := (1 / 2 : ℝ)) le_rfl
    have h2 : Filter.Tendsto
        (fun N => ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ))))) Filter.atTop
        Filter.atTop := by
      have heq : ∀ N : ℕ, ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ))))
          = ∑ n ∈ Finset.range N, primeCoeff (1 / 2 : ℝ) n := fun N => sum_primeSet_eq _ N
      rw [funext heq]
      exact h
    exact (h2.eventually_gt_atTop M).exists
  have hcont : Continuous fun σ : ℝ => ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) := by
    refine continuous_finsetSum _ fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeSet hp).pos
    exact (Real.continuous_const_rpow (ne_of_gt hp0)).comp (by fun_prop)
  have hopen : {σ : ℝ | M < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))} ∈ nhds (1 / 2 : ℝ) :=
    (isOpen_lt continuous_const hcont).mem_nhds hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hopen
  refine ⟨1 / 2 + min ε δ / 2, N, by
    have : 0 < min ε δ := lt_min hε hδ
    linarith, by
    have h1 : min ε δ ≤ δ := min_le_right _ _
    have h2 : 0 < min ε δ := lt_min hε hδ
    linarith, ?_⟩
  refine hball ?_
  rw [Metric.mem_ball, Real.dist_eq]
  have h2 : 0 < min ε δ := lt_min hε hδ
  have h1 : min ε δ ≤ ε := min_le_left _ _
  rw [show (1 / 2 + min ε δ / 2 - 1 / 2 : ℝ) = min ε δ / 2 by ring,
    abs_of_nonneg (by linarith)]
  linarith


/-- The neighbourhood form: one cut works for a whole right neighbourhood of the half line. -/
theorem exists_primeSum_gt_nhds (M : ℝ) :
    ∃ (η : ℝ) (N : ℕ), 0 < η ∧ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 / 2 + η →
      M < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ)))) := by
    have h := tendsto_sum_primeCoeff_atTop (σ := (1 / 2 : ℝ)) le_rfl
    have h2 : Filter.Tendsto
        (fun N => ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ))))) Filter.atTop
        Filter.atTop := by
      have heq : ∀ N : ℕ, ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ))))
          = ∑ n ∈ Finset.range N, primeCoeff (1 / 2 : ℝ) n := fun N => sum_primeSet_eq _ N
      rw [funext heq]
      exact h
    exact (h2.eventually_gt_atTop M).exists
  have hcont : Continuous fun σ : ℝ => ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) := by
    refine continuous_finsetSum _ fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeSet hp).pos
    exact (Real.continuous_const_rpow (ne_of_gt hp0)).comp (by fun_prop)
  have hopen : {σ : ℝ | M < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))} ∈ nhds (1 / 2 : ℝ) :=
    (isOpen_lt continuous_const hcont).mem_nhds hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hopen
  refine ⟨ε, N, hε, fun σ hσ1 hσ2 => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith


/-! ### The sign symmetry -/

theorem steinhausPrimePoly_rotHalf (σ : ℝ) (N : ℕ) (ω : Omega) :
    steinhausPrimePoly σ N (rotOmegaBy (1 / 2) ω) = -steinhausPrimePoly σ N ω := by
  rw [steinhausPrimePoly, steinhausPrimePoly, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [X_rotOmega_half (prime_of_mem_primeSet hp)]
  ring

/-- **Half the escape probability sits on each side.** -/
theorem measure_re_steinhausPrimePoly_pos (σ : ℝ) (N : ℕ)
    (hpos : 0 < ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))) :
    (1 : ℝ) / 64 ≤ (steinhausMeasure {ω | (∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))) / 4
        < ((steinhausPrimePoly σ N ω).re) ^ 2 ∧ 0 < (steinhausPrimePoly σ N ω).re}).toReal
      ∧ (1 : ℝ) / 64 ≤ (steinhausMeasure {ω | (∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ)))) / 4
        < ((steinhausPrimePoly σ N ω).re) ^ 2 ∧ (steinhausPrimePoly σ N ω).re < 0}).toReal := by
  classical
  set A : ℝ := ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) with hAdef
  set Up : Set Omega := {ω | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2
    ∧ 0 < (steinhausPrimePoly σ N ω).re} with hUpdef
  set Um : Set Omega := {ω | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2
    ∧ (steinhausPrimePoly σ N ω).re < 0} with hUmdef
  have hmeasRe : Measurable fun ω : Omega => (steinhausPrimePoly σ N ω).re :=
    Complex.measurable_re.comp (measurable_steinhausPrimePoly σ N)
  have hUpmeas : MeasurableSet Up :=
    (measurableSet_lt measurable_const (hmeasRe.pow_const 2)).inter
      (measurableSet_lt measurable_const hmeasRe)
  have hUmmeas : MeasurableSet Um :=
    (measurableSet_lt measurable_const (hmeasRe.pow_const 2)).inter
      (measurableSet_lt hmeasRe measurable_const)
  -- the rotation exchanges the two sides
  have hpre : rotOmegaBy (1 / 2) ⁻¹' Up = Um := by
    ext ω
    simp only [Set.mem_preimage, hUpdef, hUmdef, Set.mem_setOf_eq,
      steinhausPrimePoly_rotHalf σ N ω, Complex.neg_re]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [h1], by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [h1], by linarith⟩
  have heq : steinhausMeasure Um = steinhausMeasure Up := by
    rw [← hpre, measure_preimage_rotOmegaBy (by norm_num) (by norm_num) hUpmeas]
  -- the two sides are disjoint and exhaust the escape event
  have hdisj : Disjoint Up Um := by
    refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
    have := h1.2
    have := h2.2
    linarith
  have hunion : Up ∪ Um = {ω : Omega | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2} := by
    ext ω
    simp only [Set.mem_union, hUpdef, hUmdef, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
    · intro h1
      rcases lt_trichotomy ((steinhausPrimePoly σ N ω).re) 0 with hlt | heq0 | hgt
      · exact Or.inr ⟨h1, hlt⟩
      · exfalso
        rw [heq0] at h1
        norm_num at h1
        linarith
      · exact Or.inl ⟨h1, hgt⟩
  have hbase := measure_re_steinhausPrimePoly_gt σ N hpos
  have hsum : steinhausMeasure Up + steinhausMeasure Um
      = steinhausMeasure {ω : Omega | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2} := by
    rw [← hunion, measure_union hdisj hUmmeas]
  have hfin1 : steinhausMeasure Up ≠ ⊤ := measure_ne_top _ _
  have hfin2 : steinhausMeasure Um ≠ ⊤ := measure_ne_top _ _
  have htoReal : (steinhausMeasure Up).toReal + (steinhausMeasure Um).toReal
      = (steinhausMeasure {ω : Omega | A / 4 < ((steinhausPrimePoly σ N ω).re) ^ 2}).toReal := by
    rw [← ENNReal.toReal_add hfin1 hfin2, hsum]
  have hequal : (steinhausMeasure Um).toReal = (steinhausMeasure Up).toReal := by rw [heq]
  constructor <;> [skip; rw [hequal]] <;> linarith [hbase, htoReal, hequal]

end GaloisForLFunctions.RHTower

end
