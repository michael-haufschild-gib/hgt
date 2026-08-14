import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquareExactAFE
import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquareVerticalIntegrability

/-!
# Absolute reflected divisor expansion for Ingham's zeta-square contour

The reflected left contour lies on the absolutely convergent divisor line `Re w = 5/4`.
Gamma decay beats the quadratic growth of the squared zeta functional-equation factor, so the
reflected divisor series may be exchanged with the full vertical integral absolutely.  This gives
an exact symmetric arithmetic carrier, rather than a formal or conditionally convergent AFE.
-/

noncomputable section

open Complex Set Filter Topology MeasureTheory Asymptotics

namespace RHTower.Sieve

/-- Archimedean kernel left after reflecting zeta square to `Re w = 5/4`. -/
def inghamReflectedDivisorKernel (tau x v : ℝ) : ℂ :=
  let z : ℂ := (-3 / 4 : ℂ) + (v : ℂ) * I
  (x : ℂ) ^ (-z) * Complex.Gamma z * zetaChi (linePt tau + z) ^ 2

/-- One divisor-series term of the reflected left contour. -/
def inghamReflectedDivisorTerm (tau x : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  let z : ℂ := (-3 / 4 : ℂ) + (v : ℂ) * I
  inghamReflectedDivisorKernel tau x v *
    LSeries.term (fun m : ℕ => (m.divisors.card : ℂ)) (1 - linePt tau - z) n

/-- Reflected zeta-square integrand is pointwise the full divisor-term series. -/
theorem inghamReflectedZetaSquareMellinIntegrand_eq_tsum
    (tau x v : ℝ) :
    inghamReflectedZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (v : ℂ) * I) =
      ∑' n : ℕ, inghamReflectedDivisorTerm tau x n v := by
  unfold inghamReflectedZetaSquareMellinIntegrand
  rw [show LSeries (fun m : ℕ => (m.divisors.card : ℂ))
      (1 - linePt tau - ((-3 / 4 : ℂ) + (v : ℂ) * I)) =
        ∑' n : ℕ, LSeries.term (fun m : ℕ => (m.divisors.card : ℂ))
          (1 - linePt tau - ((-3 / 4 : ℂ) + (v : ℂ) * I)) n from rfl,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [inghamReflectedDivisorKernel, inghamReflectedDivisorTerm]

/-- Reflection converts the original left integral to the reflected integrand exactly. -/
theorem integral_inghamZetaSquareMellinIntegrand_left_threeQuarter_eq_reflected
    (tau x : ℝ) :
    (∫ v : ℝ, inghamZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, inghamReflectedZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (v : ℂ) * I) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    inghamZetaSquareMellinIntegrand_left_threeQuarter_eq_reflected tau x v

/-- Reflected Archimedean kernel is continuous on the full vertical line. -/
theorem continuous_inghamReflectedDivisorKernel
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Continuous (inghamReflectedDivisorKernel tau x) := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℂ := (-3 / 4 : ℂ) + (t : ℂ) * I
  let w : ℂ := linePt tau + z
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hzPath : ContinuousAt (fun v : ℝ => (-3 / 4 : ℂ) + (v : ℂ) * I) t := by
    fun_prop
  have hpow : ContinuousAt
      (fun v : ℝ => (x : ℂ) ^ (-((-3 / 4 : ℂ) + (v : ℂ) * I))) t := by
    have hout : ContinuousAt (fun q : ℂ => (x : ℂ) ^ q) (-z) :=
      ((hasDerivAt_id (-z)).const_cpow (Or.inl hxC)).continuousAt
    simpa [z, Function.comp_def] using hout.comp_of_eq hzPath.neg (by simp [z])
  have hGamma : ContinuousAt
      (fun v : ℝ => Complex.Gamma ((-3 / 4 : ℂ) + (v : ℂ) * I)) t := by
    have hout : ContinuousAt Complex.Gamma z := by
      apply Complex.continuousAt_Gamma
      intro m hm
      have hre := congrArg Complex.re hm
      dsimp only [z] at hre
      simp at hre
      cases m with
      | zero => norm_num at hre
      | succ m =>
          have hm1 : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
          linarith
    simpa [z, Function.comp_def] using hout.comp_of_eq hzPath (by simp [z])
  have hChi : ContinuousAt
      (fun v : ℝ => zetaChi
        (linePt tau + ((-3 / 4 : ℂ) + (v : ℂ) * I))) t := by
    have hpos : 0 < (1 - w).re := by
      dsimp only [w, z]
      rw [Complex.sub_re, Complex.one_re, Complex.add_re, linePt_re,
        Complex.add_re]
      norm_num
    have hout : ContinuousAt zetaChi w :=
      (zetaChi_analyticAt (Gammaℝ_ne_zero_of_re_pos hpos)).continuousAt
    have hpath : ContinuousAt
        (fun v : ℝ => linePt tau + ((-3 / 4 : ℂ) + (v : ℂ) * I)) t := by
      fun_prop
    simpa [w, z, Function.comp_def] using hout.comp_of_eq hpath (by simp [w, z])
  unfold inghamReflectedDivisorKernel
  exact (hpow.mul hGamma).mul (hChi.pow 2)

/-- Reflected kernel has unconditional inverse-square tails. -/
theorem exists_norm_inghamReflectedDivisorKernel_le_inv_sq
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v : ℝ, max 1 (|tau| + 2) ≤ |v| →
      ‖inghamReflectedDivisorKernel tau x v‖ ≤ D / |v| ^ 2 := by
  obtain ⟨C, hC, hGamma⟩ := exists_uniform_bound_norm_Gamma_ingham_strip 4
  let D : ℝ := x ^ (3 / 4 : ℝ) * C * (Real.exp 2) ^ 2 * (2 + |tau|) ^ 2
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro v hv
  have hv1 : 1 ≤ |v| := le_trans (le_max_left _ _) hv
  have hheight0 : |tau| + 2 ≤ |v| := le_trans (le_max_right _ _) hv
  have hheight : 2 ≤ |tau + v| := by
    have htri : |v| ≤ |tau + v| + |tau| := by
      have := abs_sub_le (tau + v) 0 tau
      simpa only [sub_zero, add_sub_cancel_left, zero_sub, abs_neg] using this
    linarith
  have hChi :
      ‖zetaChi (linePt tau + ((-3 / 4 : ℂ) + (v : ℂ) * I))‖ ≤
        Real.exp 2 * (1 + |tau + v|) := by
    have harg : linePt tau + ((-3 / 4 : ℂ) + (v : ℂ) * I) =
        (-1 / 4 : ℂ) + ((tau + v : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [linePt] <;> ring
    rw [harg]
    simpa only [show (((-1 / 4 : ℝ) : ℂ)) = (-1 / 4 : ℂ) by norm_num] using
      (norm_zetaChi_le_half_strip (σ := (-1 / 4 : ℝ)) (t := tau + v)
        (by norm_num) (by norm_num) hheight)
  have hGamma' :
      ‖Complex.Gamma ((-3 / 4 : ℂ) + (v : ℂ) * I)‖ ≤ C / |v| ^ 4 := by
    simpa only [show (((-3 / 4 : ℝ) : ℂ)) = (-3 / 4 : ℂ) by norm_num] using
      (hGamma (-3 / 4) v (by norm_num) (by norm_num) hv1)
  have hxnorm :
      ‖(x : ℂ) ^ (-((-3 / 4 : ℂ) + (v : ℂ) * I))‖ = x ^ (3 / 4 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    norm_num
  have hlinear : 1 + |tau + v| ≤ (2 + |tau|) * |v| := by
    have hupper : |tau + v| ≤ |tau| + |v| := abs_add_le tau v
    nlinarith [abs_nonneg tau]
  have hv0 : |v| ≠ 0 := ne_of_gt (zero_lt_one.trans_le hv1)
  rw [inghamReflectedDivisorKernel, norm_mul, norm_mul, norm_pow, hxnorm]
  calc
    x ^ (3 / 4 : ℝ) *
          ‖Complex.Gamma ((-3 / 4 : ℂ) + (v : ℂ) * I)‖ *
          ‖zetaChi (linePt tau + ((-3 / 4 : ℂ) + (v : ℂ) * I))‖ ^ 2
        ≤ x ^ (3 / 4 : ℝ) * (C / |v| ^ 4) *
            (Real.exp 2 * (1 + |tau + v|)) ^ 2 := by
      gcongr
    _ ≤ x ^ (3 / 4 : ℝ) * (C / |v| ^ 4) *
          (Real.exp 2 * ((2 + |tau|) * |v|)) ^ 2 := by
      gcongr
    _ = D / |v| ^ 2 := by
      dsimp only [D]
      field_simp

/-- Reflected Archimedean kernel is absolutely integrable on the full vertical line. -/
theorem inghamReflectedDivisorKernel_integrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Integrable (inghamReflectedDivisorKernel tau x) := by
  let f : ℝ → ℂ := inghamReflectedDivisorKernel tau x
  let q : ℝ → ℝ := fun v => 1 / (1 + v ^ 2)
  have hfcont : Continuous f := continuous_inghamReflectedDivisorKernel hx tau
  have hloc : LocallyIntegrable f volume := hfcont.locallyIntegrable
  obtain ⟨D, hD, htail⟩ :=
    exists_norm_inghamReflectedDivisorKernel_le_inv_sq hx tau
  let R : ℝ := max 1 (|tau| + 2)
  have hR1 : 1 ≤ R := le_max_left _ _
  have htop : f =O[atTop] q := by
    refine isBigO_iff.mpr ⟨2 * D, ?_⟩
    filter_upwards [eventually_ge_atTop R] with v hvR
    have hv1 : 1 ≤ v := hR1.trans hvR
    have hv0 : 0 < v := zero_lt_one.trans_le hv1
    have habs : |v| = v := abs_of_pos hv0
    have hraw : ‖f v‖ ≤ D / v ^ 2 := by
      dsimp only [f]
      simpa [R, habs] using htail v (by simpa [R, habs] using hvR)
    have hvSq : (1 : ℝ) ≤ v ^ 2 := by nlinarith
    have hvSqPos : 0 < v ^ 2 := sq_pos_of_pos hv0
    have hdenPos : 0 < 1 + v ^ 2 := by positivity
    have hfrac : 1 / v ^ 2 ≤ 2 / (1 + v ^ 2) := by
      rw [div_le_div_iff₀ hvSqPos hdenPos]
      nlinarith
    have hqnorm : ‖q v‖ = 1 / (1 + v ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_pos]
      exact div_pos one_pos hdenPos
    rw [hqnorm]
    calc
      ‖f v‖ ≤ D / v ^ 2 := hraw
      _ = D * (1 / v ^ 2) := by ring
      _ ≤ D * (2 / (1 + v ^ 2)) := mul_le_mul_of_nonneg_left hfrac hD
      _ = (2 * D) * (1 / (1 + v ^ 2)) := by ring
  have hbot : f =O[atBot] q := by
    refine isBigO_iff.mpr ⟨2 * D, ?_⟩
    filter_upwards [eventually_le_atBot (-R)] with v hvR
    have habsR : R ≤ |v| := by
      have hR0 : 0 ≤ R := zero_le_one.trans hR1
      have hv0 : v ≤ 0 := hvR.trans (neg_nonpos.mpr hR0)
      rw [abs_of_nonpos hv0]
      linarith
    have habs1 : 1 ≤ |v| := hR1.trans habsR
    have hvne : v ≠ 0 := by
      intro h
      subst v
      norm_num at habs1
    have hraw : ‖f v‖ ≤ D / |v| ^ 2 := by
      dsimp only [f]
      exact htail v (by simpa only [R] using habsR)
    have hvSq : (1 : ℝ) ≤ v ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have hvSqPos : 0 < v ^ 2 := sq_pos_of_ne_zero hvne
    have hdenPos : 0 < 1 + v ^ 2 := by positivity
    have hfrac : 1 / v ^ 2 ≤ 2 / (1 + v ^ 2) := by
      rw [div_le_div_iff₀ hvSqPos hdenPos]
      nlinarith
    have hqnorm : ‖q v‖ = 1 / (1 + v ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_pos]
      exact div_pos one_pos hdenPos
    rw [hqnorm]
    calc
      ‖f v‖ ≤ D / |v| ^ 2 := hraw
      _ = D / v ^ 2 := by rw [sq_abs]
      _ = D * (1 / v ^ 2) := by ring
      _ ≤ D * (2 / (1 + v ^ 2)) := mul_le_mul_of_nonneg_left hfrac hD
      _ = (2 * D) * (1 / (1 + v ^ 2)) := by ring
  have hq : Integrable q := by
    simpa only [q, one_div] using integrable_inv_one_add_sq
  exact hloc.integrable_of_isBigO_atBot_atTop
    hbot (hq.integrableAtFilter atBot) htop (hq.integrableAtFilter atTop)

private theorem continuous_inghamReflectedDivisorLSeriesTerm
    (tau : ℝ) (n : ℕ) :
    Continuous (fun v : ℝ =>
      LSeries.term (fun m : ℕ => (m.divisors.card : ℂ))
        (1 - linePt tau - ((-3 / 4 : ℂ) + (v : ℂ) * I)) n) := by
  rcases eq_or_ne n 0 with h | h
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · have heq : (fun v : ℝ =>
        LSeries.term (fun m : ℕ => (m.divisors.card : ℂ))
          (1 - linePt tau - ((-3 / 4 : ℂ) + (v : ℂ) * I)) n) =
        fun v : ℝ => (n.divisors.card : ℂ) *
          (n : ℂ) ^ (-(1 - linePt tau -
            ((-3 / 4 : ℂ) + (v : ℂ) * I))) := by
      funext v
      rw [LSeries.term_of_ne_zero h, Complex.cpow_neg, div_eq_mul_inv]
    rw [heq]
    exact continuous_const.mul
      (Continuous.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast Nat.cast_ne_zero.mpr h)))

/-- Norm of a reflected divisor term separates into a static `Re w=5/4` coefficient and kernel. -/
theorem norm_inghamReflectedDivisorTerm_eq
    (tau x : ℝ) (n : ℕ) (v : ℝ) :
    ‖inghamReflectedDivisorTerm tau x n v‖ =
      ‖LSeries.term (fun m : ℕ => (m.divisors.card : ℂ)) (5 / 4 : ℂ) n‖ *
        ‖inghamReflectedDivisorKernel tau x v‖ := by
  have hre :
      (1 - linePt tau - ((-3 / 4 : ℂ) + (v : ℂ) * I)).re =
        ((5 / 4 : ℂ)).re := by
    rw [Complex.sub_re, Complex.sub_re, Complex.one_re, linePt_re,
      Complex.add_re]
    norm_num
  rw [inghamReflectedDivisorTerm, norm_mul, LSeries.norm_term_eq,
    LSeries.norm_term_eq, hre]
  ring

/-- Each reflected divisor term is absolutely integrable. -/
theorem inghamReflectedDivisorTerm_integrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    Integrable (inghamReflectedDivisorTerm tau x n) := by
  let Cn : ℝ :=
    ‖LSeries.term (fun m : ℕ => (m.divisors.card : ℂ)) (5 / 4 : ℂ) n‖
  have hK := inghamReflectedDivisorKernel_integrable hx tau
  have hmajor : Integrable (fun v : ℝ => Cn * ‖inghamReflectedDivisorKernel tau x v‖) :=
    hK.norm.const_mul Cn
  apply hmajor.mono'
  · exact ((continuous_inghamReflectedDivisorKernel hx tau).mul
      (continuous_inghamReflectedDivisorLSeriesTerm tau n)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      rw [norm_inghamReflectedDivisorTerm_eq]

/-- Integral norms of all reflected divisor terms are summable. -/
theorem summable_integral_norm_inghamReflectedDivisorTerm
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Summable (fun n : ℕ => ∫ v : ℝ, ‖inghamReflectedDivisorTerm tau x n v‖) := by
  let M : ℝ := ∫ v : ℝ, ‖inghamReflectedDivisorKernel tau x v‖
  have hbase : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m : ℕ => (m.divisors.card : ℂ)) (5 / 4 : ℂ) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_card_divisors (w := (5 / 4 : ℂ)) (by norm_num))
  have hmajor := hbase.mul_right M
  refine hmajor.congr (fun n => ?_)
  rw [show (fun v : ℝ => ‖inghamReflectedDivisorTerm tau x n v‖) =
      fun v : ℝ =>
        ‖LSeries.term (fun m : ℕ => (m.divisors.card : ℂ)) (5 / 4 : ℂ) n‖ *
          ‖inghamReflectedDivisorKernel tau x v‖ by
      funext v
      exact norm_inghamReflectedDivisorTerm_eq tau x n v,
    MeasureTheory.integral_const_mul]

/-- Absolute Fubini theorem for Ingham's reflected zeta-square contour. -/
theorem integral_inghamReflectedZetaSquareMellinIntegrand_eq_tsum
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    (∫ v : ℝ, inghamReflectedZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (v : ℂ) * I)) =
      ∑' n : ℕ, ∫ v : ℝ, inghamReflectedDivisorTerm tau x n v := by
  calc
    (∫ v : ℝ, inghamReflectedZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (v : ℂ) * I)) =
        ∫ v : ℝ, ∑' n : ℕ, inghamReflectedDivisorTerm tau x n v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v =>
        inghamReflectedZetaSquareMellinIntegrand_eq_tsum tau x v
    _ = ∑' n : ℕ, ∫ v : ℝ, inghamReflectedDivisorTerm tau x n v := by
      symm
      apply integral_tsum_of_summable_integral_norm
      · exact fun n => inghamReflectedDivisorTerm_integrable hx tau n
      · exact summable_integral_norm_inghamReflectedDivisorTerm hx tau

/-- Exact symmetric arithmetic-carrier AFE for zeta square. -/
theorem inghamZetaSquare_exact_symmetric_divisor_AFE
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    riemannZeta (linePt tau) ^ 2 =
      (∑' n : ℕ, inghamCriticalDivisorCoeff tau n *
          Complex.exp (-((n : ℝ) * x : ℝ))) -
        confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
          (1 - linePt tau) -
        (1 / (2 * Real.pi) : ℂ) *
          ∑' n : ℕ, ∫ v : ℝ, inghamReflectedDivisorTerm tau x n v := by
  rw [inghamZetaSquare_exact_exponential_AFE hx tau,
    show (((-3 / 4 : ℝ) : ℂ)) = (-3 / 4 : ℂ) by norm_num,
    integral_inghamZetaSquareMellinIntegrand_left_threeQuarter_eq_reflected tau x,
    integral_inghamReflectedZetaSquareMellinIntegrand_eq_tsum hx tau]

end RHTower.Sieve
