import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquareHorizontalDecay
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion

/-!
# Vertical integrability for Ingham's zeta-square Mellin contour

Horizontal estimates specialize to inverse-square tails on fixed left line.  Local holomorphy plus
two-sided comparison with Cauchy density gives absolute full-line integrability.
-/

noncomputable section

open Complex Set Filter Topology MeasureTheory Asymptotics

namespace RHTower.Sieve

/-- Fixed left contour has unconditional inverse-square tails. -/
theorem exists_norm_inghamZetaSquareMellinIntegrand_left_threeQuarter_le_inv_sq
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, max 1 (|tau| + 2) ≤ |t| →
      ‖inghamZetaSquareMellinIntegrand (linePt tau) x
          ((-3 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ D / |t| ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_inghamZetaSquareMellinIntegrand_horizontal_le hx tau
  let D : ℝ := C * (2 + |tau|) ^ 4
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro t ht
  have ht1 : 1 ≤ |t| := le_trans (le_max_left _ _) ht
  have hheight0 : |tau| + 2 ≤ |t| := le_trans (le_max_right _ _) ht
  have hheight : 2 ≤ |tau + t| := by
    have htri : |t| ≤ |tau + t| + |tau| := by
      have := abs_sub_le (tau + t) 0 tau
      simpa only [sub_zero, add_sub_cancel_left, zero_sub, abs_neg] using this
    linarith
  have hheightUpper : |tau + t| ≤ |tau| + |t| := abs_add_le tau t
  have hb := hbound (-3 / 4) t (by norm_num) (by norm_num) ht1 hheight
  have hcast : (-3 / 4 : ℂ) = (((-3 / 4 : ℝ) : ℂ)) := by norm_num
  have hlinear : 1 + |tau| + |t| ≤ (2 + |tau|) * |t| := by
    nlinarith [abs_nonneg tau]
  have hp : (1 + |tau + t|) ^ 4 ≤ ((2 + |tau|) * |t|) ^ 4 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc
    ‖inghamZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |tau + t|) ^ 4 / |t| ^ 6 := by
      rw [hcast]
      exact hb
    _ ≤ C * (((2 + |tau|) * |t|) ^ 4) / |t| ^ 6 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (by positivity)
    _ = D / |t| ^ 2 := by
      have ht0 : |t| ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht1)
      dsimp only [D]
      rw [mul_pow]
      field_simp

/-- Left vertical parameterization is continuous. -/
theorem continuous_inghamZetaSquareMellinIntegrand_left_threeQuarter
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Continuous (fun t : ℝ =>
      inghamZetaSquareMellinIntegrand (linePt tau) x
        ((-3 / 4 : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  let z : ℂ := (-3 / 4 : ℂ) + (t : ℂ) * I
  have hzPath : ContinuousAt (fun v : ℝ => (-3 / 4 : ℂ) + (v : ℂ) * I) t := by
    fun_prop
  have hnegPath : ContinuousAt (fun v : ℝ => -((-3 / 4 : ℂ) + (v : ℂ) * I)) t :=
    hzPath.neg
  have hpow : ContinuousAt
      (fun v : ℝ => (x : ℂ) ^ (-((-3 / 4 : ℂ) + (v : ℂ) * I))) t := by
    have hout : ContinuousAt (fun w : ℂ => (x : ℂ) ^ w) (-z) :=
      ((hasDerivAt_id (-z)).const_cpow (Or.inl hxC)).continuousAt
    simpa [z, Function.comp_def] using
      hout.comp_of_eq hnegPath (by simp [z])
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
          have hm1 : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
          linarith
    simpa [z, Function.comp_def] using
      hout.comp_of_eq hzPath (by simp [z])
  have hZeta : ContinuousAt
      (fun v : ℝ => riemannZeta
        (linePt tau + ((-3 / 4 : ℂ) + (v : ℂ) * I))) t := by
    have hw : linePt tau + z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      dsimp only [z] at hre
      rw [Complex.add_re, linePt_re, Complex.one_re] at hre
      norm_num at hre
    have hpath : ContinuousAt
        (fun v : ℝ => linePt tau + ((-3 / 4 : ℂ) + (v : ℂ) * I)) t := by
      fun_prop
    simpa [z, Function.comp_def] using
      (differentiableAt_riemannZeta hw).continuousAt.comp_of_eq hpath (by simp [z])
  unfold inghamZetaSquareMellinIntegrand
  exact (hpow.mul hGamma).mul (hZeta.pow 2)

/-- Ingham zeta-square Mellin integrand is absolutely integrable on full left vertical line. -/
theorem inghamZetaSquareMellinIntegrand_left_threeQuarter_verticalIntegrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Complex.VerticalIntegrable
      (inghamZetaSquareMellinIntegrand (linePt tau) x) (-3 / 4) := by
  rw [Complex.VerticalIntegrable]
  let f : ℝ → ℂ := fun t =>
    inghamZetaSquareMellinIntegrand (linePt tau) x
      ((-3 / 4 : ℂ) + (t : ℂ) * I)
  let q : ℝ → ℝ := fun t => 1 / (1 + t ^ 2)
  have hfcont : Continuous f := by
    exact continuous_inghamZetaSquareMellinIntegrand_left_threeQuarter hx tau
  have hloc : LocallyIntegrable f MeasureTheory.volume := hfcont.locallyIntegrable
  obtain ⟨D, hD, htail⟩ :=
    exists_norm_inghamZetaSquareMellinIntegrand_left_threeQuarter_le_inv_sq hx tau
  let R : ℝ := max 1 (|tau| + 2)
  have hR1 : 1 ≤ R := le_max_left _ _
  have htop : f =O[atTop] q := by
    refine isBigO_iff.mpr ⟨2 * D, ?_⟩
    filter_upwards [eventually_ge_atTop R] with t htR
    have ht1 : 1 ≤ t := hR1.trans htR
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have habs : |t| = t := abs_of_pos ht0
    have hraw : ‖f t‖ ≤ D / t ^ 2 := by
      dsimp only [f]
      simpa [R, habs] using htail t (by simpa [R, habs] using htR)
    have htSq : (1 : ℝ) ≤ t ^ 2 := by nlinarith
    have htSqPos : 0 < t ^ 2 := sq_pos_of_pos ht0
    have hdenPos : 0 < 1 + t ^ 2 := by positivity
    have hfrac : 1 / t ^ 2 ≤ 2 / (1 + t ^ 2) := by
      rw [div_le_div_iff₀ htSqPos hdenPos]
      nlinarith
    have hqnorm : ‖q t‖ = 1 / (1 + t ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_pos]
      exact div_pos one_pos hdenPos
    rw [hqnorm]
    calc
      ‖f t‖ ≤ D / t ^ 2 := hraw
      _ = D * (1 / t ^ 2) := by ring
      _ ≤ D * (2 / (1 + t ^ 2)) := mul_le_mul_of_nonneg_left hfrac hD
      _ = (2 * D) * (1 / (1 + t ^ 2)) := by ring
  have hbot : f =O[atBot] q := by
    refine isBigO_iff.mpr ⟨2 * D, ?_⟩
    filter_upwards [eventually_le_atBot (-R)] with t htR
    have habsR : R ≤ |t| := by
      have htneg : t ≤ -R := htR
      have hR0 : 0 ≤ R := zero_le_one.trans hR1
      have ht0 : t ≤ 0 := htneg.trans (neg_nonpos.mpr hR0)
      rw [abs_of_nonpos ht0]
      linarith
    have habs1 : 1 ≤ |t| := hR1.trans habsR
    have htne : t ≠ 0 := by
      intro h
      subst t
      norm_num at habs1
    have hraw : ‖f t‖ ≤ D / |t| ^ 2 := by
      dsimp only [f]
      exact htail t (by simpa only [R] using habsR)
    have htSq : (1 : ℝ) ≤ t ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have htSqPos : 0 < t ^ 2 := sq_pos_of_ne_zero htne
    have hdenPos : 0 < 1 + t ^ 2 := by positivity
    have hfrac : 1 / t ^ 2 ≤ 2 / (1 + t ^ 2) := by
      rw [div_le_div_iff₀ htSqPos hdenPos]
      nlinarith
    have hqnorm : ‖q t‖ = 1 / (1 + t ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_pos]
      exact div_pos one_pos hdenPos
    rw [hqnorm]
    calc
      ‖f t‖ ≤ D / |t| ^ 2 := hraw
      _ = D / t ^ 2 := by rw [sq_abs]
      _ = D * (1 / t ^ 2) := by ring
      _ ≤ D * (2 / (1 + t ^ 2)) := mul_le_mul_of_nonneg_left hfrac hD
      _ = (2 * D) * (1 / (1 + t ^ 2)) := by ring
  have hq : Integrable q := by
    simpa only [q, one_div] using integrable_inv_one_add_sq
  have hint := hloc.integrable_of_isBigO_atBot_atTop
    hbot (hq.integrableAtFilter atBot)
    htop (hq.integrableAtFilter atTop)
  have hcast : (-3 / 4 : ℂ) = (((-3 / 4 : ℝ) : ℂ)) := by norm_num
  simpa only [f, hcast] using hint

/-- Right vertical parameterization is continuous. -/
theorem continuous_inghamZetaSquareMellinIntegrand_right_two
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Continuous (fun t : ℝ =>
      inghamZetaSquareMellinIntegrand (linePt tau) x
        ((2 : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  let z : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hzPath : ContinuousAt (fun v : ℝ => (2 : ℂ) + (v : ℂ) * I) t := by
    fun_prop
  have hnegPath : ContinuousAt (fun v : ℝ => -((2 : ℂ) + (v : ℂ) * I)) t :=
    hzPath.neg
  have hpow : ContinuousAt
      (fun v : ℝ => (x : ℂ) ^ (-((2 : ℂ) + (v : ℂ) * I))) t := by
    have hout : ContinuousAt (fun w : ℂ => (x : ℂ) ^ w) (-z) :=
      ((hasDerivAt_id (-z)).const_cpow (Or.inl hxC)).continuousAt
    simpa [z, Function.comp_def] using
      hout.comp_of_eq hnegPath (by simp [z])
  have hGamma : ContinuousAt
      (fun v : ℝ => Complex.Gamma ((2 : ℂ) + (v : ℂ) * I)) t := by
    have hout : ContinuousAt Complex.Gamma z := by
      apply Complex.continuousAt_Gamma
      intro m hm
      have hre := congrArg Complex.re hm
      dsimp only [z] at hre
      simp at hre
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    simpa [z, Function.comp_def] using
      hout.comp_of_eq hzPath (by simp [z])
  have hZeta : ContinuousAt
      (fun v : ℝ => riemannZeta
        (linePt tau + ((2 : ℂ) + (v : ℂ) * I))) t := by
    have hw : linePt tau + z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      dsimp only [z] at hre
      rw [Complex.add_re, linePt_re, Complex.one_re] at hre
      norm_num at hre
    have hpath : ContinuousAt
        (fun v : ℝ => linePt tau + ((2 : ℂ) + (v : ℂ) * I)) t := by
      fun_prop
    simpa [z, Function.comp_def] using
      (differentiableAt_riemannZeta hw).continuousAt.comp_of_eq hpath (by simp [z])
  unfold inghamZetaSquareMellinIntegrand
  exact (hpow.mul hGamma).mul (hZeta.pow 2)

/-- Ingham zeta-square Mellin integrand is absolutely integrable on inversion line `Re z=2`. -/
theorem inghamZetaSquareMellinIntegrand_right_two_verticalIntegrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Complex.VerticalIntegrable
      (inghamZetaSquareMellinIntegrand (linePt tau) x) 2 := by
  rw [Complex.VerticalIntegrable]
  let K : ℝ := 4 * Real.exp (2 * |Real.log x|)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hmajor : Integrable (fun t : ℝ =>
      K * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖) :=
    Gamma_verticalIntegrable_two.norm.const_mul K
  apply Integrable.mono' hmajor
  · exact (continuous_inghamZetaSquareMellinIntegrand_right_two hx tau).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      have hxpow := norm_cpow_neg_ingham_horizontal_le hx (by norm_num) (by norm_num)
        (u := 2) (T := t)
      have hxpow' :
          ‖(x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))‖ ≤
            Real.exp (2 * |Real.log x|) := by
        simpa using hxpow
      have hzeta0 := RHTower.Sieve.norm_riemannZeta_le
        (s := linePt tau + ((2 : ℂ) + (t : ℂ) * I)) (by
          rw [Complex.add_re, linePt_re]
          norm_num)
      have hzeta :
          ‖riemannZeta (linePt tau + ((2 : ℂ) + (t : ℂ) * I))‖ ≤ 2 := by
        apply hzeta0.trans
        rw [Complex.add_re, linePt_re]
        norm_num
      rw [inghamZetaSquareMellinIntegrand, norm_mul, norm_mul, norm_pow]
      calc
        ‖(x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))‖ *
              ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ *
              ‖riemannZeta (linePt tau + ((2 : ℂ) + (t : ℂ) * I))‖ ^ 2
            ≤ Real.exp (2 * |Real.log x|) *
                ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ * 2 ^ 2 := by
          gcongr
        _ = K * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ := by
          dsimp only [K]
          ring

end RHTower.Sieve
