import GaloisForLFunctions.RHTower.ZetaNotchScaleMixture

/-!
# Linear and inverse moments of the Gaussian scale mixture

The mixed window `Ω_L` is concentrated on `[L/2, 5L/2]` with total mass `O(1)`. Two consequences:

* `∫ Ω_L(x) (1 + |x|) dx ≤ C (1 + L)` (`exists_integral_mixWindowReal_mul_one_add_le`);
* `∫ Ω_L(x) (1 + |x|)^{−1} dx ≤ C/(2 + L)` (`exists_integral_mixWindowReal_div_one_add_le`).

On the positive half-line both follow from the scale representation
`∫_{x>0} Ω_L f = ∫_{u>0} ρ_L(u) u^{−1} ∫ B(t/u) f(t) dt du`, with the notch profile `B` supported on
`[u/2, 5u/2]`. On the negative half-line `Ω_L = O(e^{−L²})`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower.ZetaNotch

/-- The scale representation of a real moment of the mixed window on the positive half-line. -/
theorem integral_Ioi_mixWindowReal_mul_real (L : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C * (1 + |t|) ^ 2) :
    ∫ x in Ioi 0, mixWindowReal L x * f x =
      ∫ u in Ioi 0, scaleWeight L u / u * ∫ t, notchProfile (t / u) * f t := by
  have h := integral_Ioi_mixWindowReal_mul L (F := fun t => ((f t : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hf) (C := C) (fun t => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hC t)
  have hL : ∫ t in Ioi 0, (mixWindowReal L t : ℂ) * ((f t : ℝ) : ℂ) =
      ((∫ x in Ioi 0, mixWindowReal L x * f x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    rfl
  have hR : ∫ u in Ioi 0, ((scaleWeight L u / u : ℝ) : ℂ) * ∫ t, notchWindow u t * ((f t : ℝ) : ℂ) =
      ((∫ u in Ioi 0, scaleWeight L u / u * ∫ t, notchProfile (t / u) * f t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hin : ∫ t, notchWindow u t * ((f t : ℝ) : ℂ) =
        ((∫ t, notchProfile (t / u) * f t : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext t
      rw [notchWindow_eq_notchProfile hu0]
      push_cast
      ring
    rw [hin]
    push_cast
    ring
  rw [hL, hR] at h
  exact_mod_cast h

theorem abs_mul_exp_neg_sq_le (w : ℝ) :
    |w| * Real.exp (-(1 * w ^ 2)) ≤ Real.exp (-(1 / 2 * w ^ 2)) := by
  have h1 : |w| ≤ Real.exp (1 / 2 * w ^ 2) := by
    have := Real.add_one_le_exp (1 / 2 * w ^ 2)
    nlinarith [sq_abs w, sq_nonneg (|w| - 1), abs_nonneg w]
  calc |w| * Real.exp (-(1 * w ^ 2)) ≤ Real.exp (1 / 2 * w ^ 2) * Real.exp (-(1 * w ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-(1 / 2 * w ^ 2)) := by rw [← Real.exp_add]; ring_nf

/-- `∫ ρ_L(u) (1 + |u − L|) du ≤ A`, uniformly in `L`. -/
theorem exists_integral_scaleWeight_mul_one_add_abs_le :
    ∃ A, 0 ≤ A ∧ ∀ L : ℝ, Integrable (fun u => scaleWeight L u * (1 + |u - L|)) ∧
      ∫ u, scaleWeight L u * (1 + |u - L|) ≤ A := by
  set A₀ : ℝ := ∫ w : ℝ, Real.exp (-(1 * w ^ 2)) with hA₀
  set A₁ : ℝ := ∫ w : ℝ, Real.exp (-(1 / 2 * w ^ 2)) with hA₁
  have hA₀0 : 0 ≤ A₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  have hA₁0 : 0 ≤ A₁ := integral_nonneg fun _ => (Real.exp_pos _).le
  have hi0 := integrable_exp_neg_mul_sq' (b := 1) one_pos
  have hi1 := integrable_exp_neg_mul_sq' (b := 1 / 2) (by norm_num)
  refine ⟨A₀ + A₁, by positivity, fun L => ?_⟩
  set g : ℝ → ℝ := fun w => Real.exp (-(1 * w ^ 2)) + Real.exp (-(1 / 2 * w ^ 2)) with hg
  have hgi : Integrable g := hi0.add hi1
  have hpt : ∀ u, scaleWeight L u * (1 + |u - L|) ≤ g (u - L) := by
    intro u
    have he : scaleWeight L u = Real.exp (-(1 * (u - L) ^ 2)) := by rw [scaleWeight, one_mul]
    have h := abs_mul_exp_neg_sq_le (u - L)
    rw [he, hg]
    simp only
    nlinarith [Real.exp_pos (-(1 * (u - L) ^ 2))]
  have hmeas : AEStronglyMeasurable (fun u => scaleWeight L u * (1 + |u - L|)) volume :=
    (by unfold scaleWeight; fun_prop : Continuous fun u => scaleWeight L u * (1 + |u - L|))
      |>.aestronglyMeasurable
  have hint : Integrable (fun u => scaleWeight L u * (1 + |u - L|)) :=
    (hgi.comp_sub_right L).mono' hmeas (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (scaleWeight_pos L u).le (by positivity))]
      exact hpt u)
  refine ⟨hint, ?_⟩
  calc ∫ u, scaleWeight L u * (1 + |u - L|) ≤ ∫ u, g (u - L) :=
        integral_mono hint (hgi.comp_sub_right L) hpt
    _ = ∫ w, g w := integral_sub_right_eq_self g L
    _ = A₀ + A₁ := by rw [hg, integral_add hi0 hi1]

/-- The positive-half-line moment against a nonnegative weight, bounded through the notch. -/
theorem setIntegral_Ioi_mixWindowReal_mul_le (L : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {C : ℝ} (hC : ∀ t, |f t| ≤ C * (1 + |t|) ^ 2) {K : ℝ → ℝ}
    (hK : ∀ u, 0 < u → ∀ t ∈ Icc (u / 2) (5 / 2 * u), f t ≤ K u)
    (hKi : IntegrableOn (fun u => scaleWeight L u * (2 * K u)) (Ioi 0)) :
    ∫ x in Ioi 0, mixWindowReal L x * f x ≤ ∫ u in Ioi 0, scaleWeight L u * (2 * K u) := by
  rw [integral_Ioi_mixWindowReal_mul_real L hf hC]
  refine integral_mono_of_nonneg ?_ hKi ?_
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    exact mul_nonneg (div_pos (scaleWeight_pos L u) hu0).le
      (integral_nonneg fun t => mul_nonneg (notchProfile_nonneg _) (hf0 t))
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hb := integral_notchProfile_mul_le hu0 hf0 (hK u hu0)
    calc scaleWeight L u / u * ∫ t, notchProfile (t / u) * f t
        ≤ scaleWeight L u / u * (2 * u * K u) :=
          mul_le_mul_of_nonneg_left hb (div_pos (scaleWeight_pos L u) hu0).le
      _ = scaleWeight L u * (2 * K u) := by field_simp

/-- The negative-half-line moment against `f ≤ (1 + |x|)²` is `O(e^{−L²})`. -/
theorem exists_setIntegral_Iic_mixWindowReal_mul_le :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∀ {f : ℝ → ℝ}, Continuous f → (∀ t, 0 ≤ f t) →
      (∀ t, f t ≤ (1 + |t|) ^ 2) → ∫ x in Iic 0, mixWindowReal L x * f x ≤ C * Real.exp (-L ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_Iic_mixWindowReal_mul_sq_le
  refine ⟨C, hC0, fun L hL {f} hf hf0 hf1 => ?_⟩
  refine le_trans ?_ (hC L hL)
  refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
    mul_nonneg (mixWindowReal_nonneg L x) (hf0 x))
    (integrable_mixWindowReal_mul_sq L).integrableOn (Eventually.of_forall fun x => ?_)
  exact mul_le_mul_of_nonneg_left (hf1 x) (mixWindowReal_nonneg L x)

theorem integrable_mixWindowReal_mul_of_le {L : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ (1 + |t|) ^ 2) :
    Integrable (fun x => mixWindowReal L x * f x) :=
  (integrable_mixWindowReal_mul_sq L).mono' ((continuous_mixWindowReal L).mul hf).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mixWindowReal_nonneg L x) (hf0 x))]
      exact mul_le_mul_of_nonneg_left (hf1 x) (mixWindowReal_nonneg L x))

/-- **The linear moment of the mixed window**: `∫ Ω_L(x)(1 + |x|) dx ≤ C (1 + L)`. -/
theorem exists_integral_mixWindowReal_mul_one_add_le :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ x, mixWindowReal L x * (1 + |x|) ≤ C * (1 + L) := by
  obtain ⟨A, hA0, hA⟩ := exists_integral_scaleWeight_mul_one_add_abs_le
  obtain ⟨Cn, hCn0, hCn⟩ := exists_setIntegral_Iic_mixWindowReal_mul_le
  refine ⟨5 * A + Cn, by positivity, fun L hL => ?_⟩
  have hf : Continuous fun t : ℝ => 1 + |t| := by fun_prop
  have hf0 : ∀ t : ℝ, 0 ≤ 1 + |t| := fun t => by positivity
  have hf1 : ∀ t : ℝ, 1 + |t| ≤ (1 + |t|) ^ 2 := fun t => by nlinarith [abs_nonneg t]
  have hi := integrable_mixWindowReal_mul_of_le (L := L) hf hf0 hf1
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hi, compl_Ioi]
  obtain ⟨hAi, hAb⟩ := hA L
  have hKi : IntegrableOn (fun u => scaleWeight L u * (2 * (1 + 5 / 2 * u))) (Ioi 0) := by
    have h := (integrable_scaleWeight_mul_quadratic L 2 5 0).integrableOn (s := Ioi (0 : ℝ))
    refine h.congr_fun (fun u _ => by ring) measurableSet_Ioi
  have hpos := setIntegral_Ioi_mixWindowReal_mul_le L hf hf0 (C := 1)
    (fun t => by rw [abs_of_nonneg (hf0 t), one_mul]; exact hf1 t)
    (K := fun u => 1 + 5 / 2 * u) (fun u hu t ht => by
      have ht0 : 0 ≤ t := by linarith [ht.1]
      rw [abs_of_nonneg ht0]; linarith [ht.2]) hKi
  have hpos' : ∫ u in Ioi 0, scaleWeight L u * (2 * (1 + 5 / 2 * u)) ≤ 5 * A * (1 + L) := by
    have hpt : ∀ u ∈ Ioi (0 : ℝ), scaleWeight L u * (2 * (1 + 5 / 2 * u)) ≤
        5 * (1 + L) * (scaleWeight L u * (1 + |u - L|)) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu
      have h1 : 2 * (1 + 5 / 2 * u) ≤ 5 * (1 + L) * (1 + |u - L|) := by
        have := le_abs_self (u - L)
        nlinarith [abs_nonneg (u - L)]
      exact (mul_le_mul_of_nonneg_left h1 (scaleWeight_pos L u).le).trans (le_of_eq (by ring))
    calc ∫ u in Ioi 0, scaleWeight L u * (2 * (1 + 5 / 2 * u))
        ≤ ∫ u in Ioi 0, 5 * (1 + L) * (scaleWeight L u * (1 + |u - L|)) :=
          setIntegral_mono_on hKi (hAi.const_mul _).integrableOn measurableSet_Ioi hpt
      _ ≤ ∫ u, 5 * (1 + L) * (scaleWeight L u * (1 + |u - L|)) :=
          setIntegral_le_integral (hAi.const_mul _) (Eventually.of_forall fun u => by
            have := scaleWeight_pos L u; positivity)
      _ = 5 * (1 + L) * ∫ u, scaleWeight L u * (1 + |u - L|) := integral_const_mul _ _
      _ ≤ 5 * (1 + L) * A := mul_le_mul_of_nonneg_left hAb (by positivity)
      _ = 5 * A * (1 + L) := by ring
  have hneg := hCn L hL hf hf0 hf1
  have he : Real.exp (-L ^ 2) ≤ 1 + L := by
    have : Real.exp (-L ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg L])
    linarith
  nlinarith [mul_le_mul_of_nonneg_left he hCn0]

/-- **The inverse moment of the mixed window**: `∫ Ω_L(x)(1 + |x|)^{−1} dx ≤ C/(2 + L)`. -/
theorem exists_integral_mixWindowReal_div_one_add_le :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ x, mixWindowReal L x * (1 + |x|)⁻¹ ≤ C / (2 + L) := by
  obtain ⟨A, hA0, hA⟩ := exists_integral_scaleWeight_mul_one_add_abs_le
  obtain ⟨Cn, hCn0, hCn⟩ := exists_setIntegral_Iic_mixWindowReal_mul_le
  refine ⟨16 * A + 3 * Cn, by positivity, fun L hL => ?_⟩
  have hf : Continuous fun t : ℝ => (1 + |t|)⁻¹ :=
    Continuous.inv₀ (by fun_prop) (fun t => by positivity)
  have hf0 : ∀ t : ℝ, 0 ≤ (1 + |t|)⁻¹ := fun t => by positivity
  have hf1 : ∀ t : ℝ, (1 + |t|)⁻¹ ≤ (1 + |t|) ^ 2 := fun t => by
    have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    calc (1 + |t|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      _ ≤ (1 + |t|) ^ 2 := one_le_pow₀ h1
  have hi := integrable_mixWindowReal_mul_of_le (L := L) hf hf0 hf1
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hi, compl_Ioi]
  obtain ⟨hAi, hAb⟩ := hA L
  have hL2 : (0 : ℝ) < 2 + L := by linarith
  -- `1/(2 + u) ≤ 2 (1 + |u − L|)/(2 + L)` for `u ≥ 0`
  have hkey : ∀ u : ℝ, 0 ≤ u → (2 + u)⁻¹ ≤ 2 * (1 + |u - L|) / (2 + L) := by
    intro u hu
    rw [inv_le_comm₀ (by linarith) (by positivity), inv_div, div_le_iff₀ (by positivity)]
    rcases le_or_gt L u with h | h
    · rw [abs_of_nonneg (by linarith)]; nlinarith
    · rw [abs_of_neg (by linarith)]; nlinarith
  have hKmeas : IntegrableOn (fun u => scaleWeight L u * (2 * (2 * (2 + u)⁻¹))) (Ioi 0) := by
    refine ((hAi.const_mul (8 / (2 + L))).integrableOn).mono' ?_ ?_
    · have hc : ContinuousOn (fun u : ℝ => (2 + u)⁻¹) (Ioi 0) :=
        (continuousOn_const.add continuousOn_id).inv₀ fun u hu => by
          have : (0 : ℝ) < u := hu
          show (2 : ℝ) + u ≠ 0
          linarith
      exact ((by unfold scaleWeight; fun_prop : Continuous fun u => scaleWeight L u).continuousOn.mul
        (continuousOn_const.mul (continuousOn_const.mul hc))).aestronglyMeasurable measurableSet_Ioi
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu0 : (0 : ℝ) < u := hu
      have h := hkey u hu0.le
      have hs := scaleWeight_pos L u
      have h2u : 0 < 2 + u := by linarith
      rw [Real.norm_of_nonneg (mul_nonneg hs.le (mul_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr h2u.le))))]
      calc scaleWeight L u * (2 * (2 * (2 + u)⁻¹)) ≤
            scaleWeight L u * (2 * (2 * (2 * (1 + |u - L|) / (2 + L)))) := by gcongr
        _ = 8 / (2 + L) * (scaleWeight L u * (1 + |u - L|)) := by ring
  have hpos := setIntegral_Ioi_mixWindowReal_mul_le L hf hf0 (C := 1)
    (fun t => by rw [abs_of_nonneg (hf0 t), one_mul]; exact hf1 t)
    (K := fun u => 2 * (2 + u)⁻¹) (fun u hu t ht => by
      have ht0 : 0 ≤ t := by linarith [ht.1]
      rw [abs_of_nonneg ht0]
      have h1 : 1 + u / 2 ≤ 1 + t := by linarith [ht.1]
      calc (1 + t)⁻¹ ≤ (1 + u / 2)⁻¹ := inv_anti₀ (by linarith) h1
        _ = 2 * (2 + u)⁻¹ := by field_simp) hKmeas
  have hpos' : ∫ u in Ioi 0, scaleWeight L u * (2 * (2 * (2 + u)⁻¹)) ≤ 8 * A / (2 + L) := by
    calc ∫ u in Ioi 0, scaleWeight L u * (2 * (2 * (2 + u)⁻¹))
        ≤ ∫ u in Ioi 0, 8 / (2 + L) * (scaleWeight L u * (1 + |u - L|)) := by
          refine setIntegral_mono_on hKmeas (hAi.const_mul _).integrableOn measurableSet_Ioi
            fun u hu => ?_
          have hu0 : (0 : ℝ) < u := hu
          have h := hkey u hu0.le
          have hs := scaleWeight_pos L u
          calc scaleWeight L u * (2 * (2 * (2 + u)⁻¹)) ≤
                scaleWeight L u * (2 * (2 * (2 * (1 + |u - L|) / (2 + L)))) := by gcongr
            _ = 8 / (2 + L) * (scaleWeight L u * (1 + |u - L|)) := by ring
      _ ≤ ∫ u, 8 / (2 + L) * (scaleWeight L u * (1 + |u - L|)) :=
          setIntegral_le_integral (hAi.const_mul _) (Eventually.of_forall fun u => by
            have := scaleWeight_pos L u; positivity)
      _ = 8 / (2 + L) * ∫ u, scaleWeight L u * (1 + |u - L|) := integral_const_mul _ _
      _ ≤ 8 / (2 + L) * A := mul_le_mul_of_nonneg_left hAb (by positivity)
      _ = 8 * A / (2 + L) := by ring
  have hneg := hCn L hL hf hf0 hf1
  have he : Real.exp (-L ^ 2) ≤ 3 / (2 + L) := by
    rw [le_div_iff₀ hL2]
    have h1 : 1 + L ^ 2 ≤ Real.exp (L ^ 2) := by linarith [Real.add_one_le_exp (L ^ 2)]
    have h2 : Real.exp (-L ^ 2) * Real.exp (L ^ 2) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 2 + L ≤ 3 * (1 + L ^ 2) := by nlinarith [sq_nonneg (L - 1 / 6)]
    nlinarith [Real.exp_pos (-L ^ 2)]
  have h3 : Cn * Real.exp (-L ^ 2) ≤ 3 * Cn / (2 + L) := by
    calc Cn * Real.exp (-L ^ 2) ≤ Cn * (3 / (2 + L)) := mul_le_mul_of_nonneg_left he hCn0
      _ = 3 * Cn / (2 + L) := by ring
  have h4 : (16 * A + 3 * Cn) / (2 + L) = 16 * A / (2 + L) + 3 * Cn / (2 + L) := by ring
  have h5 : 8 * A / (2 + L) ≤ 16 * A / (2 + L) :=
    div_le_div_of_nonneg_right (by linarith) hL2.le
  linarith

end RHTower.ZetaNotch
