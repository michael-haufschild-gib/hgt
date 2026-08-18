import GaloisForLFunctions.RHTower.PrimeProfileFockLimit

/-!
# The generalized coherent boundary at the half-normal end

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(13j)`–`(13n)`.

At the negative end the coherent vector `F_{-V}(t) = e^{-Vt} - 1` does not converge in the
prime-scale Hilbert space — its norm diverges — but it *does* converge weakly against the profile
test class: for every `f` with `|f(t)| ≤ L t`,

`⟨F_{-V}, f⟩ = ∫₀¹ (e^{-Vt} - 1) f(t) dt/t  →  ℓ_-(f) = -∫₀¹ f(t) dt/t`,

with the explicit rate `|⟨F_{-V}, f⟩ - ℓ_-(f)| ≤ L/V`.  Exponentiating, the exponential vectors
`e(F_{-V})` converge against the exponential test algebra to the generalized coherent boundary
functional `e^{ℓ_-}`.
-/

open Filter Topology Set intervalIntegral MeasureTheory

namespace RHTower

noncomputable section

/-! ## Integrability of bounded profile quotients -/

theorem continuousOn_divProfile_Ioc {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc 0 1)) :
    ContinuousOn (divProfile F) (Set.Ioc (0 : ℝ) 1) := by
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := Set.Ioc_subset_Icc_self
  have hquot : ContinuousOn (fun t : ℝ => F t / t) (Set.Ioc (0 : ℝ) 1) :=
    (hF.mono hsub).div continuousOn_id (fun t ht => ne_of_gt ht.1)
  refine hquot.congr fun t ht => ?_
  rw [divProfile, if_neg (ne_of_gt ht.1)]

theorem intervalIntegrable_divProfile_of_bounded {F : ℝ → ℝ} {C : ℝ}
    (hF : ContinuousOn F (Set.Icc 0 1))
    (hbd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖divProfile F t‖ ≤ C) :
    IntervalIntegrable (divProfile F) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact ⟨(continuousOn_divProfile_Ioc hF).aestronglyMeasurable measurableSet_Ioc,
    MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := C) measure_Ioc_lt_top
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hbd)⟩

/-! ## The half-normal pairing -/

/-- The pairing of the half-normal coherent vector with a prime-scale profile. -/
def halfNormalPairing (f : ℝ → ℝ) (V : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, divProfile (fun s => (Real.exp (-V * s) - 1) * f s) t

/-- **`(13k)`: the generalized coherent boundary functional.** -/
def halfNormalFunctional (f : ℝ → ℝ) : ℝ := -∫ t in (0 : ℝ)..1, divProfile f t

theorem abs_divProfile_le_of_scaleProfile {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) : ‖divProfile f t‖ ≤ L := by
  have ht0 : 0 < t := ht.1
  rw [divProfile, if_neg (ne_of_gt ht0), Real.norm_eq_abs, abs_div, abs_of_pos ht0,
    div_le_iff₀ ht0]
  exact hf.slope t ⟨ht0.le, ht.2⟩

theorem intervalIntegrable_divProfile_scaleProfile {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) :
    IntervalIntegrable (divProfile f) volume 0 1 :=
  intervalIntegrable_divProfile_of_bounded hf.cont
    (fun _ ht => abs_divProfile_le_of_scaleProfile hf ht)

theorem abs_divProfile_damped_le {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) (V : ℝ)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖divProfile (fun s => Real.exp (-V * s) * f s) t‖ ≤ L * Real.exp (-V * t) := by
  have ht0 : 0 < t := ht.1
  rw [divProfile, if_neg (ne_of_gt ht0), Real.norm_eq_abs, abs_div, abs_of_pos ht0,
    div_le_iff₀ ht0, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hfb : |f t| ≤ L * t := hf.slope t ⟨ht0.le, ht.2⟩
  nlinarith [Real.exp_nonneg (-V * t), abs_nonneg (f t)]

theorem abs_divProfile_damped_le' {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) (V : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖divProfile (fun s => Real.exp (-V * s) * f s) t‖ ≤ L * Real.exp (-V * t) := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [divProfile, if_pos h0.symm]
    have := hf.slope_nonneg
    simp only [norm_zero]
    positivity
  · exact abs_divProfile_damped_le hf V ⟨h0, ht.2⟩

theorem intervalIntegrable_divProfile_damped {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L)
    (V : ℝ) :
    IntervalIntegrable (divProfile (fun s => Real.exp (-V * s) * f s)) volume 0 1 := by
  refine intervalIntegrable_divProfile_of_bounded (C := L * Real.exp (|V|)) ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hf.cont
  · intro t ht
    refine le_trans (abs_divProfile_damped_le hf V ht) ?_
    have hL : 0 ≤ L := hf.slope_nonneg
    have : Real.exp (-V * t) ≤ Real.exp |V| := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : -V * t ≤ |V| * t := by nlinarith [neg_le_abs V, ht.1.le]
      have h2 : |V| * t ≤ |V| := by nlinarith [abs_nonneg V, ht.2, ht.1.le]
      linarith
    nlinarith

theorem intervalIntegrable_divProfile_shifted {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L)
    (V : ℝ) :
    IntervalIntegrable (divProfile (fun s => (Real.exp (-V * s) - 1) * f s)) volume 0 1 := by
  have h1 := intervalIntegrable_divProfile_damped hf V
  have h2 := intervalIntegrable_divProfile_scaleProfile hf
  have heq : divProfile (fun s => (Real.exp (-V * s) - 1) * f s)
      = fun t => divProfile (fun s => Real.exp (-V * s) * f s) t - divProfile f t := by
    funext t
    rw [divProfile, divProfile, divProfile]
    split_ifs with ht
    · ring
    · field_simp
  rw [heq]
  exact h1.sub h2

/-- **`(13l)`: the explicit rate of the half-normal weak limit.** -/
theorem abs_halfNormalPairing_sub_le {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) {V : ℝ}
    (hV : 0 < V) : |halfNormalPairing f V - halfNormalFunctional f| ≤ L / V := by
  have hL : 0 ≤ L := hf.slope_nonneg
  have h1 := intervalIntegrable_divProfile_damped hf V
  have h2 := intervalIntegrable_divProfile_scaleProfile hf
  have hsplit : halfNormalPairing f V - halfNormalFunctional f
      = ∫ t in (0 : ℝ)..1, divProfile (fun s => Real.exp (-V * s) * f s) t := by
    rw [halfNormalPairing, halfNormalFunctional, sub_neg_eq_add]
    rw [← intervalIntegral.integral_add (intervalIntegrable_divProfile_shifted hf V) h2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [divProfile, divProfile, divProfile]
    split_ifs with ht
    · ring
    · field_simp
      ring
  rw [hsplit]
  have habs : |∫ t in (0 : ℝ)..1, divProfile (fun s => Real.exp (-V * s) * f s) t|
      ≤ ∫ t in (0 : ℝ)..1, |divProfile (fun s => Real.exp (-V * s) * f s) t| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hexpint : IntervalIntegrable (fun t : ℝ => L * Real.exp (-V * t)) volume 0 1 :=
    (Continuous.intervalIntegrable
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))) 0 1)
  have hcmp : (∫ t in (0 : ℝ)..1, |divProfile (fun s => Real.exp (-V * s) * f s) t|)
      ≤ ∫ t in (0 : ℝ)..1, L * Real.exp (-V * t) := by
    refine intervalIntegral.integral_mono_on (by norm_num) h1.abs hexpint (fun t ht => ?_)
    have := abs_divProfile_damped_le' hf V ht
    rwa [Real.norm_eq_abs] at this
  have hval : (∫ t in (0 : ℝ)..1, L * Real.exp (-V * t)) = L * ((1 - Real.exp (-V)) / V) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hVne : V ≠ 0 := ne_of_gt hV
    rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.exp x) (by linarith : -V ≠ 0)]
    rw [integral_exp]
    simp only [smul_eq_mul, mul_zero, Real.exp_zero]
    field_simp
    ring
  rw [hval] at hcmp
  have hexpV : Real.exp (-V) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexpV0 : 0 < Real.exp (-V) := Real.exp_pos _
  have hfinal : L * ((1 - Real.exp (-V)) / V) ≤ L / V := by
    rw [mul_div_assoc']
    gcongr
    nlinarith
  linarith

/-- **`(13k)`: the boundary functional is continuous for the slope seminorm.** -/
theorem abs_halfNormalFunctional_le {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) :
    |halfNormalFunctional f| ≤ L := by
  have hL : 0 ≤ L := hf.slope_nonneg
  have h2 := intervalIntegrable_divProfile_scaleProfile hf
  have habs : |∫ t in (0 : ℝ)..1, divProfile f t| ≤ ∫ t in (0 : ℝ)..1, |divProfile f t| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hcmp : (∫ t in (0 : ℝ)..1, |divProfile f t|) ≤ ∫ _t in (0 : ℝ)..1, L := by
    refine intervalIntegral.integral_mono_on (by norm_num) h2.abs intervalIntegrable_const
      (fun t ht => ?_)
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [divProfile, if_pos h0.symm]
      simpa using hL
    · have := abs_divProfile_le_of_scaleProfile hf ⟨h0, ht.2⟩
      rwa [Real.norm_eq_abs] at this
  rw [intervalIntegral.integral_const] at hcmp
  simp only [smul_eq_mul] at hcmp
  rw [halfNormalFunctional, abs_neg]
  linarith

/-- **`(13l)`: the half-normal coherent vector converges weakly to the boundary functional.** -/
theorem tendsto_halfNormalPairing {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) :
    Tendsto (fun V : ℝ => halfNormalPairing f V) atTop (nhds (halfNormalFunctional f)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hL : 0 ≤ L := hf.slope_nonneg
  obtain ⟨M, hM⟩ := exists_gt (max ((L + 1) / ε) 1)
  refine ⟨M, fun V hV => ?_⟩
  have hV1 : (1 : ℝ) < V := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hM) hV
  have hV0 : 0 < V := lt_trans zero_lt_one hV1
  have hkey := abs_halfNormalPairing_sub_le hf hV0
  have hVbig : (L + 1) / ε < V := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hM hV)
  have hLV : L / V < ε := by
    rw [div_lt_iff₀ hV0]
    rw [div_lt_iff₀ hε] at hVbig
    linarith
  rw [Real.dist_eq]
  linarith

/-- **`(13n)`: the generalized coherent boundary functional on the exponential test algebra.** -/
theorem tendsto_exp_halfNormalPairing {f : ℝ → ℝ} {L : ℝ} (hf : IsScaleProfile f L) :
    Tendsto (fun V : ℝ => Real.exp (halfNormalPairing f V)) atTop
      (nhds (Real.exp (halfNormalFunctional f))) :=
  (Real.continuous_exp.tendsto _).comp (tendsto_halfNormalPairing hf)

end

end RHTower
