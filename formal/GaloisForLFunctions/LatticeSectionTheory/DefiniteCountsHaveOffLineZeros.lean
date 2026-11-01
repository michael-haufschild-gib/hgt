import GaloisForLFunctions.LatticeSectionTheory.TheRectangularLatticeCount

/-!
# Definite counts have off-line zeros

The rectangular lattice `ℤ ⊕ yℤ` has every soft property a section count can have: a positive
Gaussian count, an exact two-dimensional Poisson summation, a completed zeta function `Λ_y`
holomorphic away from two simple poles with a functional equation, and a Dirichlet series with
positive coefficients (`TheRectangularLatticeCount`). Its zeros are not on the critical line.

* **Real form on the strip** (`epsteinLambda_ofReal`). For real `σ ∉ {0, 1}`,
  `Λ_y(σ) = M_y(σ) − 1/σ − y⁻¹/(1 − σ)` with the real Mellin integral
  `M_y(σ) = ∫_0^∞ t^{σ−1} F_y(t) dt`, where `F_y = θ_y − 1` on `(1, ∞)` and
  `F_y = θ_y − y⁻¹ t⁻¹` on `(0, 1)`; both pieces are nonnegative.
* **The dual count at the centre** (`two_log_le_epsteinMellin_half`). Since `θ(t) ≥ t^{−1/2}`,
  on `(y⁻², 1)` the integrand dominates `t⁻¹ − y⁻¹ t^{−3/2}`, so
  `M_y(1/2) ≥ 2 log y − 2 + 2/y` and `Λ_y(1/2) ≥ 2 log y − 4`.
* **Epstein fakes** (`exists_epsteinLambda_eq_zero`). The pole `y⁻¹/(1 − σ)` drives `Λ_y` to
  `−∞` at `1⁻`. For `y > e²` the intermediate value theorem gives `σ ∈ (1/2, 1)` with
  `Λ_y(σ) = 0`: a real zero right of the critical line. The square lattice `ℤ ⊕ 8ℤ` is one
  (`epsteinLambda_eight_has_offLine_zero`).

So positivity, Poisson duality, the functional equation, simple poles and a positive Dirichlet
series together do not place zeros on the line. A definite section count is a fake; whatever
selects `ζ` is not in these properties.
-/

noncomputable section

open Real Complex Filter Topology Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticOrientationGeometry

variable {y : ℝ}

/-! ### The real Mellin integral -/

/-- The modified count `F_y` underlying `Λ₀`: real-valued. -/
def epsteinModif (y : ℝ) (hy : 0 < y) (t : ℝ) : ℝ := ((rectFEPair y hy).f_modif t).re

theorem f_modif_eq_ofReal (hy : 0 < y) (t : ℝ) :
    (rectFEPair y hy).f_modif t = (epsteinModif y hy t : ℂ) := by
  apply Complex.ext
  · simp [epsteinModif]
  · simp only [epsteinModif, Complex.ofReal_im, WeakFEPair.f_modif, Pi.add_apply,
      Set.indicator_apply]
    split_ifs <;> simp [rectFEPair, -Complex.ofReal_one]

theorem epsteinModif_of_one_lt (hy : 0 < y) {t : ℝ} (ht : 1 < t) :
    epsteinModif y hy t = rectTheta y t - 1 := by
  simp [epsteinModif, WeakFEPair.f_modif, ht, rectFEPair,
    show ¬ t < 1 from not_lt.mpr ht.le]

theorem epsteinModif_of_lt_one (hy : 0 < y) {t : ℝ} (ht0 : 0 < t) (ht : t < 1) :
    epsteinModif y hy t = rectTheta y t - 1 / y * t ^ (-1 : ℝ) := by
  have h1 : ¬ 1 < t := not_lt.mpr ht.le
  simp only [epsteinModif, WeakFEPair.f_modif, Pi.add_apply, Set.indicator_apply, Set.mem_Ioi,
    Set.mem_Ioo, h1, if_false, ht0, ht, and_self, if_true, zero_add, rectFEPair]
  rw [← Complex.ofReal_mul, smul_eq_mul, mul_one, ← Complex.ofReal_sub, Complex.ofReal_re]

/-- The base count dominates the inverse square root: `θ(u) ≥ u^{−1/2}`. -/
theorem inv_sqrt_le_thetaSum {u : ℝ} (hu : 0 < u) : (Real.sqrt u)⁻¹ ≤ thetaSum u := by
  have h := thetaSum_inv hu
  rw [← Real.sqrt_eq_rpow] at h
  rw [h]
  have := one_le_thetaSum (inv_pos.mpr hu)
  have hs : 0 < (Real.sqrt u)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hu)
  nlinarith

theorem epsteinModif_nonneg (hy : 0 < y) {t : ℝ} (ht : 0 < t) : 0 ≤ epsteinModif y hy t := by
  rcases lt_trichotomy t 1 with h | h | h
  · rw [epsteinModif_of_lt_one hy ht h]
    have a1 := inv_sqrt_le_thetaSum ht
    have a2 := inv_sqrt_le_thetaSum (show 0 < y ^ 2 * t by positivity)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have e : Real.sqrt (y ^ 2 * t) = y * Real.sqrt t := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
    have hprod : (Real.sqrt t)⁻¹ * (Real.sqrt (y ^ 2 * t))⁻¹ ≤ rectTheta y t :=
      mul_le_mul a1 a2 (by positivity) (thetaSum_pos ht).le
    have hval : (Real.sqrt t)⁻¹ * (Real.sqrt (y ^ 2 * t))⁻¹ = 1 / y * t ^ (-1 : ℝ) := by
      rw [e, Real.rpow_neg_one, mul_inv, ← mul_assoc, mul_comm (Real.sqrt t)⁻¹ y⁻¹, mul_assoc,
        ← mul_inv, Real.mul_self_sqrt ht.le, one_div]
    linarith
  · subst h; simp [epsteinModif, WeakFEPair.f_modif]
  · rw [epsteinModif_of_one_lt hy h]
    linarith [one_le_rectTheta hy.ne' (show 0 < t by linarith)]

/-- The real Mellin integral `M_y(σ) = ∫_0^∞ t^{σ−1} F_y(t) dt`. -/
def epsteinMellin (y : ℝ) (hy : 0 < y) (σ : ℝ) : ℝ :=
  ∫ t in Ioi 0, t ^ (σ - 1) * epsteinModif y hy t

theorem integrableOn_epsteinMellin (hy : 0 < y) (σ : ℝ) :
    IntegrableOn (fun t => t ^ (σ - 1) * epsteinModif y hy t) (Ioi 0) := by
  have h := ((rectFEPair y hy).isStrongFEPair_toStrongFEPair.hasMellin (σ : ℂ)).1
  have hre : IntegrableOn (fun t : ℝ =>
      RCLike.re ((t : ℂ) ^ ((σ : ℂ) - 1) • (rectFEPair y hy).f_modif t)) (Ioi 0) := h.re
  refine hre.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  change ((t : ℂ) ^ ((σ : ℂ) - 1) • (rectFEPair y hy).f_modif t).re = _
  rw [f_modif_eq_ofReal, smul_eq_mul, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht', ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `Λ₀` is real on the real axis and equals the real Mellin integral. -/
theorem Λ₀_ofReal (hy : 0 < y) (σ : ℝ) :
    (rectFEPair y hy).Λ₀ (σ : ℂ) = (epsteinMellin y hy σ : ℂ) := by
  rw [WeakFEPair.Λ₀, mellin, epsteinMellin, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  rw [f_modif_eq_ofReal, smul_eq_mul, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht', Complex.ofReal_mul]

/-- **The completed Epstein function on the real axis**:
`Λ_y(σ) = M_y(σ) − 1/σ − y⁻¹/(1 − σ)`, a real number. -/
theorem epsteinLambda_ofReal (hy : 0 < y) (σ : ℝ) :
    epsteinLambda y hy σ = ((epsteinMellin y hy σ - 1 / σ - 1 / y / (1 - σ) : ℝ) : ℂ) := by
  rw [epsteinLambda, WeakFEPair.Λ, Λ₀_ofReal]
  simp only [rectFEPair, smul_eq_mul, mul_one, Complex.ofReal_one]
  push_cast
  ring

/-! ### The value at the centre -/

/-- The elementary integral `∫_{y⁻²}^1 (t⁻¹ − y⁻¹ t^{−3/2}) dt = 2 log y − 2 + 2/y`. -/
theorem integral_centre_minorant (hy : 1 < y) :
    ∫ t in (1 / y ^ 2)..1, (t⁻¹ - 1 / y * t ^ (-(3 / 2) : ℝ)) = 2 * Real.log y - 2 + 2 / y := by
  have hy0 : 0 < y := by linarith
  have ha : 0 < 1 / y ^ 2 := by positivity
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(3 / 2) : ℝ)) (Set.uIcc (1 / y ^ 2) 1) :=
    fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (by
      have : 0 < t := lt_of_lt_of_le (lt_min ha one_pos) ht.1
      exact this.ne'))).continuousWithinAt
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 / y ^ 2) 1 :=
    intervalIntegral.intervalIntegrable_inv (fun t ht => by
      have : 0 < t := lt_of_lt_of_le (lt_min ha one_pos) ht.1
      exact this.ne') (continuousOn_id)
  rw [intervalIntegral.integral_sub hinv ((hcont.intervalIntegrable).const_mul _),
    intervalIntegral.integral_const_mul, integral_inv_of_pos ha one_pos,
    integral_rpow (Or.inr ⟨by norm_num, fun h0 => by
      have := (Set.mem_uIcc.mp h0)
      rcases this with h | h <;> linarith [h.1, ha]⟩)]
  have e1 : Real.log (1 / (1 / y ^ 2)) = 2 * Real.log y := by
    rw [one_div_one_div, Real.log_pow]; push_cast; ring
  have e2 : (1 / y ^ 2) ^ (-(3 / 2) + 1 : ℝ) = y := by
    rw [show (-(3 / 2) + 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ha.le, one_div,
      Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow, Real.sqrt_sq hy0.le]
  rw [e1, e2, Real.one_rpow]
  field_simp
  ring

/-- **The dual count at the centre**: `M_y(1/2) ≥ 2 log y − 2 + 2/y`. -/
theorem two_log_le_epsteinMellin_half (hy : 1 < y) :
    2 * Real.log y - 2 + 2 / y ≤ epsteinMellin y (by linarith) (1 / 2) := by
  have hy0 : 0 < y := by linarith
  set a := 1 / y ^ 2
  have ha : 0 < a := by positivity
  have ha1 : a < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  set g := fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * epsteinModif y hy0 t
  have hgi := integrableOn_epsteinMellin hy0 (1 / 2)
  have hg_nonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t := fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (epsteinModif_nonneg hy0 ht)
  -- restrict to `(y⁻², 1)`
  have hsub : Ioo a 1 ⊆ Ioi (0 : ℝ) := fun t ht => lt_trans ha ht.1
  have h1 : ∫ t in Ioo a 1, g t ≤ epsteinMellin y hy0 (1 / 2) :=
    setIntegral_mono_set hgi
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hg_nonneg))
      (Eventually.of_forall hsub)
  -- the minorant on `(y⁻², 1)`
  set h := fun t : ℝ => t⁻¹ - 1 / y * t ^ (-(3 / 2) : ℝ)
  have hcontIcc : ContinuousOn h (Icc a 1) := by
    refine (continuousOn_inv₀.mono fun t ht => (lt_of_lt_of_le ha ht.1).ne').sub
      (continuousOn_const.mul fun t ht => (Real.continuousAt_rpow_const _ _
        (Or.inl (lt_of_lt_of_le ha ht.1).ne')).continuousWithinAt)
  have hhi : IntegrableOn h (Ioo a 1) := (hcontIcc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hle : ∀ t ∈ Ioo a 1, h t ≤ g t := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    rw [show g t = t ^ ((1 / 2 : ℝ) - 1) * epsteinModif y hy0 t from rfl,
      epsteinModif_of_lt_one hy0 ht0 ht.2]
    have hθ : (Real.sqrt t)⁻¹ ≤ rectTheta y t := by
      have := inv_sqrt_le_thetaSum ht0
      have h2 := one_le_thetaSum (show 0 < y ^ 2 * t by positivity)
      unfold rectTheta; nlinarith [thetaSum_pos ht0]
    have hp : t ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg ht0.le, Real.sqrt_eq_rpow]
    have hq : t ^ (-(3 / 2) : ℝ) = (Real.sqrt t)⁻¹ * t ^ (-1 : ℝ) := by
      rw [show (-(3 / 2) : ℝ) = -(1 / 2) + -1 by norm_num, Real.rpow_add ht0, Real.rpow_neg ht0.le,
        ← Real.sqrt_eq_rpow]
    have hinv : t⁻¹ = (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt ht0.le]
    simp only [h]
    rw [hp, hq, hinv]
    have hpos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hst
    nlinarith [mul_le_mul_of_nonneg_left hθ hpos.le]
  have h2 : ∫ t in Ioo a 1, h t ≤ ∫ t in Ioo a 1, g t :=
    setIntegral_mono_on hhi (hgi.mono_set hsub) measurableSet_Ioo hle
  have h3 : ∫ t in Ioo a 1, h t = 2 * Real.log y - 2 + 2 / y := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha1.le]
    exact integral_centre_minorant hy
  linarith

/-- **`Λ_y(1/2) ≥ 2 log y − 4`.** -/
theorem epsteinLambda_half_re_ge (hy : 1 < y) :
    2 * Real.log y - 4 ≤ (epsteinLambda y (by linarith) (1 / 2 : ℝ)).re := by
  have hy0 : 0 < y := by linarith
  rw [epsteinLambda_ofReal, Complex.ofReal_re]
  have := two_log_le_epsteinMellin_half hy
  have e : (1 : ℝ) / y / (1 - 1 / 2) = 2 / y := by field_simp; ring
  rw [e]
  norm_num
  linarith

/-! ### The zero -/

/-- **Epstein fakes.** For `y > e²` the completed Epstein function of the rectangular lattice
`ℤ ⊕ yℤ` has a real zero in `(1/2, 1)`. -/
theorem exists_epsteinLambda_eq_zero (hy : Real.exp 2 < y) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      epsteinLambda y (lt_trans (Real.exp_pos 2) hy) σ = 0 := by
  have hy1 : 1 < y := lt_trans (by
    have := Real.add_one_le_exp 2; linarith) hy
  have hy0 : 0 < y := by linarith
  -- the real function whose zero we locate
  set R : ℝ → ℝ := fun σ => (epsteinLambda y hy0 σ).re
  -- positivity at the centre
  have hlog : 2 < Real.log y := by
    rw [Real.lt_log_iff_exp_lt hy0]; exact hy
  have hR0 : 0 < R (1 / 2) := by
    have := epsteinLambda_half_re_ge hy1; simp only [R]; linarith
  -- negativity near `1`
  have hcont1 : ContinuousAt (fun σ : ℝ => ((rectFEPair y hy0).Λ₀ (σ : ℂ)).re) 1 :=
    Complex.continuous_re.continuousAt.comp
      (((rectFEPair y hy0).differentiable_Λ₀ _).continuousAt.comp Complex.continuous_ofReal.continuousAt)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont1 1 one_pos
  set C := |((rectFEPair y hy0).Λ₀ ((1 : ℝ) : ℂ)).re| + 1
  have hC : 0 < C := by positivity
  set m := min (δ / 2) (min (1 / 4) (1 / (y * (C + 1))))
  have hm : 0 < m := lt_min (by linarith) (lt_min (by norm_num) (by positivity))
  set σ₁ := 1 - m
  have hσ₁ : 1 / 2 < σ₁ := by
    have : m ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
    simp only [σ₁]; linarith
  have hσ₁1 : σ₁ < 1 := by simp only [σ₁]; linarith
  have hR1 : R σ₁ < 0 := by
    have hdist : dist σ₁ 1 < δ := by
      rw [Real.dist_eq, show σ₁ - 1 = -m by simp [σ₁], abs_neg, abs_of_pos hm]
      linarith [min_le_left (δ / 2) (min (1 / 4) (1 / (y * (C + 1))))]
    have hb := hball hdist
    rw [Real.dist_eq] at hb
    have hΛ₀ : ((rectFEPair y hy0).Λ₀ (σ₁ : ℂ)).re < C := by
      have := le_abs_self ((rectFEPair y hy0).Λ₀ ((1 : ℝ) : ℂ)).re
      have := (abs_lt.mp hb).2
      simp only [C]; linarith
    have hval : R σ₁ = ((rectFEPair y hy0).Λ₀ (σ₁ : ℂ)).re - 1 / σ₁ - 1 / y / (1 - σ₁) := by
      simp only [R]
      rw [epsteinLambda_ofReal, Complex.ofReal_re, Λ₀_ofReal hy0 σ₁, Complex.ofReal_re]
    have hm' : m ≤ 1 / (y * (C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hpole : C + 1 ≤ 1 / y / (1 - σ₁) := by
      rw [show 1 - σ₁ = m by simp [σ₁], div_div, le_div_iff₀ (by positivity)]
      calc (C + 1) * (y * m) ≤ (C + 1) * (y * (1 / (y * (C + 1)))) := by gcongr
        _ = 1 := by field_simp
    have hσpos : 0 < 1 / σ₁ := by positivity
    linarith
  -- continuity on `[1/2, σ₁]`
  have hcontR : ContinuousOn R (Icc (1 / 2) σ₁) := by
    intro σ hσ
    have hσ0 : (σ : ℂ) ≠ 0 := by
      exact_mod_cast (show σ ≠ 0 by linarith [hσ.1])
    have hσ1 : (σ : ℂ) ≠ 1 := by
      exact_mod_cast (show σ ≠ 1 by linarith [hσ.2])
    exact (Complex.continuous_re.continuousAt.comp
      ((differentiableAt_epsteinLambda hy0 hσ0 hσ1).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  obtain ⟨σ, hσ, hRσ⟩ := intermediate_value_Icc' hσ₁.le hcontR ⟨hR1.le, hR0.le⟩
  have hσhalf : σ ≠ 1 / 2 := by rintro rfl; linarith
  refine ⟨σ, lt_of_le_of_ne hσ.1 (Ne.symm hσhalf), lt_of_le_of_lt hσ.2 hσ₁1, ?_⟩
  rw [epsteinLambda_ofReal]
  simp only [R] at hRσ
  rw [epsteinLambda_ofReal, Complex.ofReal_re] at hRσ
  rw [hRσ, Complex.ofReal_zero]

/-- `e² < 8`. -/
theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [Real.exp_pos 1]

/-- **The lattice `ℤ ⊕ 8ℤ` is a fake**: positive count, two-dimensional Poisson duality,
functional equation, Dirichlet series with positive coefficients — and a zero of its completed
Epstein function at a real `σ ∈ (1/2, 1)`. -/
theorem epsteinLambda_eight_has_offLine_zero :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ epsteinLambda 8 (by norm_num) σ = 0 :=
  exists_epsteinLambda_eq_zero exp_two_lt_eight

end GaloisForLFunctions.LatticeSectionTheory
