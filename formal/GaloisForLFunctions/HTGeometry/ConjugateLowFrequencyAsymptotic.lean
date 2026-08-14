import GaloisForLFunctions.HTGeometry.VectorLowFrequencyAsymptotic

/-!
# The low-frequency asymptotic on the negative frequency channel

The negative frequency channel carries the conjugate oscillation `η^{-1/2}e^{-iηL}`, and its
Watson constant is the conjugate constant `√π e^{-iπ/4}`:

`∫₀^A f(η) η^{-1/2} e^{-iηL} dη = f(0) √π e^{-iπ/4} L^{-1/2} + O(L^{-1})`.

Conjugation is an isometric real-linear map commuting with the integral, so the whole positive
channel argument transfers verbatim; the two channels then combine into the half-log scattering
map.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The half-power oscillatory integrand on the negative frequency channel. -/
def scaledFresnelConj (L η : ℝ) : ℂ :=
  ((η ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp (-((η * L : ℝ) * I))

theorem conj_scaledFresnel (L η : ℝ) :
    (starRingEnd ℂ) (scaledFresnel L η) = scaledFresnelConj L η := by
  rw [scaledFresnel, scaledFresnelConj, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

theorem norm_scaledFresnelConj (L η : ℝ) :
    ‖scaledFresnelConj L η‖ = ‖scaledFresnel L η‖ := by
  rw [← conj_scaledFresnel, RCLike.norm_conj]

/-- The Watson constant of the negative channel. -/
def watsonConstConj (L : ℝ) : ℂ :=
  ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
    * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp (-((Real.pi/4 : ℝ) * I)))

theorem conj_watsonConst (L : ℝ) :
    (starRingEnd ℂ) (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
        * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)))
      = watsonConstConj L := by
  have hreal : ((Real.pi : ℂ) ^ ((1:ℂ)/2)) = ((Real.pi ^ ((1:ℝ)/2) : ℝ) : ℂ) := by
    have hcast : ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) := by norm_num
    rw [hcast, ← Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
  rw [watsonConstConj, map_mul, Complex.conj_ofReal, map_mul, hreal, Complex.conj_ofReal,
    ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

variable {f f' : ℝ → ℂ} {K : ℝ}

/-- **The scalar low-frequency asymptotic on the negative channel.** -/
theorem norm_lowFrequency_asymptotic_conj {A L : ℝ} (hA : 0 < A) (hL : 0 < L) (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hcont : ContinuousOn (fun η => (starRingEnd ℂ) (f' η)) (Set.Ioi (0:ℝ)))
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η)
    (hbound : ∀ η : ℝ, 0 < η → ‖f' η‖ ≤ K) :
    ‖(∫ η in (0:ℝ)..A, f η * scaledFresnelConj L η) - f 0 * watsonConstConj L‖
      ≤ ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
        + (4 * K * A ^ ((1:ℝ)/2)) / L := by
  have hconjCLM : ∀ {g : ℝ → ℂ} {g' : ℂ} {η : ℝ}, HasDerivAt g g' η →
      HasDerivAt (fun y => (starRingEnd ℂ) (g y)) ((starRingEnd ℂ) g') η := by
    intro g g' η hg
    exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt η hg)
  have hderivC : ∀ η : ℝ, 0 < η →
      HasDerivAt (fun y => (starRingEnd ℂ) (f y)) ((starRingEnd ℂ) (f' η)) η :=
    fun η hη => hconjCLM (hderiv η hη)
  have hlipC : ∀ η : ℝ, 0 ≤ η →
      ‖(starRingEnd ℂ) (f η) - (starRingEnd ℂ) (f 0)‖ ≤ K * η := by
    intro η hη
    rw [← map_sub, RCLike.norm_conj]
    exact hlip η hη
  have hboundC : ∀ η : ℝ, 0 < η → ‖(starRingEnd ℂ) (f' η)‖ ≤ K := by
    intro η hη
    rw [RCLike.norm_conj]
    exact hbound η hη
  have hbase := norm_lowFrequency_asymptotic (f := fun η => (starRingEnd ℂ) (f η))
    (f' := fun η => (starRingEnd ℂ) (f' η)) hA hL hK hderivC hcont hlipC hboundC
  have hint : IntervalIntegrable (fun η => (starRingEnd ℂ) (f η) * scaledFresnel L η)
      volume 0 A := by
    have h2 := intervalIntegrable_centredAmplitude_mul (f := fun η => (starRingEnd ℂ) (f η))
      (f' := fun η => (starRingEnd ℂ) (f' η)) (L := L) hA hK hderivC hlipC
    have hfun : (fun η => (starRingEnd ℂ) (f η) * scaledFresnel L η)
        = fun η => (starRingEnd ℂ) (f 0) * scaledFresnel L η
            + centredAmplitude (fun x => (starRingEnd ℂ) (f x)) η
              * Complex.exp ((η * L : ℝ) * I) := by
      funext η
      rw [scaledFresnel, centredAmplitude]
      ring
    rw [hfun]
    have h1 : IntervalIntegrable (scaledFresnel L) volume 0 A := intervalIntegrable_scaledFresnel
    exact (h1.const_mul _).add h2
  have hcomm : (∫ η in (0:ℝ)..A, (starRingEnd ℂ) ((starRingEnd ℂ) (f η) * scaledFresnel L η))
      = (starRingEnd ℂ) (∫ η in (0:ℝ)..A, (starRingEnd ℂ) (f η) * scaledFresnel L η) :=
    Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint
  have hpt : ∀ η : ℝ, (starRingEnd ℂ) ((starRingEnd ℂ) (f η) * scaledFresnel L η)
      = f η * scaledFresnelConj L η := by
    intro η
    rw [map_mul, Complex.conj_conj, conj_scaledFresnel]
  have hleft : (∫ η in (0:ℝ)..A, f η * scaledFresnelConj L η)
      = (starRingEnd ℂ) (∫ η in (0:ℝ)..A, (starRingEnd ℂ) (f η) * scaledFresnel L η) := by
    rw [← hcomm]
    exact integral_congr fun η _ => (hpt η).symm
  have hnorm : ‖(∫ η in (0:ℝ)..A, f η * scaledFresnelConj L η) - f 0 * watsonConstConj L‖
      = ‖(∫ η in (0:ℝ)..A, (starRingEnd ℂ) (f η) * scaledFresnel L η)
          - (starRingEnd ℂ) (f 0) * (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
            * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)))‖ := by
    rw [hleft, ← conj_watsonConst L, ← Complex.conj_conj (f 0), ← map_mul, ← map_sub,
      RCLike.norm_conj, Complex.conj_conj]
  rw [hnorm]
  refine le_trans hbase (le_of_eq ?_)
  rw [RCLike.norm_conj]

section Vector

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- A half-power oscillatory kernel against a Lipschitz vector amplitude is integrable. -/
theorem intervalIntegrable_halfPowerKernel_smul {w : ℝ → ℂ} {f f' : ℝ → X} {K A : ℝ}
    (hA : 0 < A) (hK : 0 ≤ K)
    (hwn : ∀ η : ℝ, 0 < η → ‖w η‖ = η ^ (-(1:ℝ)/2))
    (hwc : ContinuousOn w (Set.Ioc 0 A))
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η) :
    IntervalIntegrable (fun η => w η • f η) volume 0 A := by
  have hIoc : Set.uIoc (0:ℝ) A = Set.Ioc 0 A := Set.uIoc_of_le hA.le
  have hfc : ContinuousOn f (Set.Ioc 0 A) := by
    intro x hx
    exact (((hderiv x hx.1).continuousAt).continuousWithinAt)
  have hmeas : AEStronglyMeasurable (fun η => w η • f η)
      (volume.restrict (Set.uIoc 0 A)) := by
    rw [hIoc]
    exact (hwc.smul hfc).aestronglyMeasurable measurableSet_Ioc
  have hmajor : IntervalIntegrable
      (fun η : ℝ => ‖f 0‖ * η ^ (-(1:ℝ)/2) + K * η ^ ((1:ℝ)/2)) volume 0 A :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _).add
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
  refine IntervalIntegrable.mono_fun hmajor hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with η hη
  rw [hIoc] at hη
  have hη0 : 0 < η := hη.1
  have hfη : ‖f η‖ ≤ ‖f 0‖ + K * η := by
    have h := hlip η hη0.le
    have := norm_sub_norm_le (f η) (f 0)
    linarith [le_trans this h]
  have hmul : η ^ (-(1:ℝ)/2) * η = η ^ ((1:ℝ)/2) := by
    have h1 : η = η ^ (1:ℝ) := (Real.rpow_one η).symm
    calc η ^ (-(1:ℝ)/2) * η = η ^ (-(1:ℝ)/2) * η ^ (1:ℝ) := by rw [← h1]
      _ = η ^ (-(1:ℝ)/2 + (1:ℝ)) := (Real.rpow_add hη0 _ _).symm
      _ = η ^ ((1:ℝ)/2) := by ring_nf
  rw [norm_smul, hwn η hη0, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖f 0‖ * η ^ (-(1:ℝ)/2) + K * η ^ ((1:ℝ)/2))]
  have hstep : η ^ (-(1:ℝ)/2) * ‖f η‖ ≤ η ^ (-(1:ℝ)/2) * (‖f 0‖ + K * η) :=
    mul_le_mul_of_nonneg_left hfη (Real.rpow_pos_of_pos hη0 _).le
  refine le_trans hstep (le_of_eq ?_)
  rw [mul_add, ← mul_assoc, mul_comm (η ^ (-(1:ℝ)/2)) K, mul_assoc K, hmul]
  ring

omit [CompleteSpace X] in
theorem continuousOn_scaledFresnel {A L : ℝ} : ContinuousOn (scaledFresnel L) (Set.Ioc 0 A) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have h1 : ContinuousAt (fun y : ℝ => ((y ^ (-(1:ℝ)/2) : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const x (-(1:ℝ)/2) (Or.inl hx0))
  have h2 : ContinuousAt (fun y : ℝ => Complex.exp ((y * L : ℝ) * I)) x := by fun_prop
  exact ((h1.mul h2).continuousWithinAt)

omit [CompleteSpace X] in
theorem continuousOn_scaledFresnelConj {A L : ℝ} :
    ContinuousOn (scaledFresnelConj L) (Set.Ioc 0 A) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have h1 : ContinuousAt (fun y : ℝ => ((y ^ (-(1:ℝ)/2) : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const x (-(1:ℝ)/2) (Or.inl hx0))
  have h2 : ContinuousAt (fun y : ℝ => Complex.exp (-((y * L : ℝ) * I))) x := by fun_prop
  exact ((h1.mul h2).continuousWithinAt)

omit [CompleteSpace X] in
theorem norm_scaledFresnel_of_pos {L η : ℝ} (hη : 0 < η) :
    ‖scaledFresnel L η‖ = η ^ (-(1:ℝ)/2) := by
  rw [scaledFresnel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hη _), Complex.norm_exp]
  simp

omit [CompleteSpace X] in
theorem norm_scaledFresnelConj_of_pos {L η : ℝ} (hη : 0 < η) :
    ‖scaledFresnelConj L η‖ = η ^ (-(1:ℝ)/2) := by
  rw [← conj_scaledFresnel, RCLike.norm_conj]
  exact norm_scaledFresnel_of_pos hη

omit [CompleteSpace X] in
/-- The positive channel kernel against a Lipschitz vector amplitude is integrable. -/
theorem intervalIntegrable_scaledFresnel_smul {f f' : ℝ → X} {K A L : ℝ} (hA : 0 < A)
    (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η) :
    IntervalIntegrable (fun η => scaledFresnel L η • f η) volume 0 A :=
  intervalIntegrable_halfPowerKernel_smul (f' := f') hA hK
    (fun _ hη => norm_scaledFresnel_of_pos hη) continuousOn_scaledFresnel hderiv hlip

omit [CompleteSpace X] in
/-- The conjugate half-power kernel against a Lipschitz vector amplitude is integrable. -/
theorem intervalIntegrable_scaledFresnelConj_smul {f f' : ℝ → X} {K A L : ℝ} (hA : 0 < A)
    (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η) :
    IntervalIntegrable (fun η => scaledFresnelConj L η • f η) volume 0 A :=
  intervalIntegrable_halfPowerKernel_smul (f' := f') hA hK
    (fun _ hη => norm_scaledFresnelConj_of_pos hη) continuousOn_scaledFresnelConj hderiv hlip

/-- **The Hilbert-valued low-frequency asymptotic on the negative channel.** -/
theorem norm_vector_lowFrequency_asymptotic_conj {f f' : ℝ → X} {K A L : ℝ}
    (hA : 0 < A) (hL : 0 < L) (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hcont : ∀ v : X, ContinuousOn (fun η : ℝ => (inner ℂ v (f' η) : ℂ)) (Set.Ioi (0:ℝ)))
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η)
    (hbound : ∀ η : ℝ, 0 < η → ‖f' η‖ ≤ K) :
    ‖(∫ η in (0:ℝ)..A, scaledFresnelConj L η • f η) - watsonConstConj L • f 0‖
      ≤ ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
        + (4 * K * A ^ ((1:ℝ)/2)) / L := by
  have hint := intervalIntegrable_scaledFresnelConj_smul (L := L) hA hK hderiv hlip
  set D : X := (∫ η in (0:ℝ)..A, scaledFresnelConj L η • f η) - watsonConstConj L • f 0 with hD
  set M : ℝ := ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
    + (4 * K * A ^ ((1:ℝ)/2)) / L with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have h1 : (0:ℝ) ≤ ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ))) := by positivity
    have h2 : (0:ℝ) ≤ (4 * K * A ^ ((1:ℝ)/2)) / L := by positivity
    linarith
  have hkey : ∀ v : X, ‖v‖ = 1 → ‖(inner ℂ v D : ℂ)‖ ≤ M := by
    intro v hv
    set g : ℝ → ℂ := fun η => (inner ℂ v (f η) : ℂ) with hg
    set g' : ℝ → ℂ := fun η => (inner ℂ v (f' η) : ℂ) with hg'
    have hgderiv : ∀ η : ℝ, 0 < η → HasDerivAt g (g' η) η := by
      intro η hη
      have hconst : HasDerivAt (fun _ : ℝ => v) (0 : X) η := hasDerivAt_const η v
      have hbase := HasDerivAt.inner ℂ hconst (hderiv η hη)
      simpa [hg, hg'] using hbase
    have hglip : ∀ η : ℝ, 0 ≤ η → ‖g η - g 0‖ ≤ K * η := by
      intro η hη
      have hsub : g η - g 0 = (inner ℂ v (f η - f 0) : ℂ) := by
        rw [hg, inner_sub_right]
      rw [hsub]
      calc ‖(inner ℂ v (f η - f 0) : ℂ)‖ ≤ ‖v‖ * ‖f η - f 0‖ :=
            norm_inner_le_norm (𝕜 := ℂ) v (f η - f 0)
        _ = ‖f η - f 0‖ := by rw [hv, one_mul]
        _ ≤ K * η := hlip η hη
    have hgbound : ∀ η : ℝ, 0 < η → ‖g' η‖ ≤ K := by
      intro η hη
      calc ‖(inner ℂ v (f' η) : ℂ)‖ ≤ ‖v‖ * ‖f' η‖ := norm_inner_le_norm (𝕜 := ℂ) v (f' η)
        _ = ‖f' η‖ := by rw [hv, one_mul]
        _ ≤ K := hbound η hη
    have hgcont : ContinuousOn (fun η => (starRingEnd ℂ) (g' η)) (Set.Ioi (0:ℝ)) :=
      Complex.continuous_conj.comp_continuousOn (hcont v)
    have hscalar := norm_lowFrequency_asymptotic_conj (f := g) (f' := g') hA hL hK hgderiv
      hgcont hglip hgbound
    have hcomm : (inner ℂ v D : ℂ)
        = (∫ η in (0:ℝ)..A, g η * scaledFresnelConj L η) - g 0 * watsonConstConj L := by
      rw [hD, inner_sub_right, inner_smul_right, inner_integral_comm v hint]
      congr 1
      · refine intervalIntegral.integral_congr fun η _ => ?_
        show (inner ℂ v (scaledFresnelConj L η • f η) : ℂ) = g η * scaledFresnelConj L η
        rw [inner_smul_right, hg]
        ring
      · rw [hg]
        ring
    rw [hcomm]
    have hg0 : ‖g 0‖ ≤ ‖f 0‖ := by
      calc ‖(inner ℂ v (f 0) : ℂ)‖ ≤ ‖v‖ * ‖f 0‖ := norm_inner_le_norm (𝕜 := ℂ) v (f 0)
        _ = ‖f 0‖ := by rw [hv, one_mul]
    refine le_trans hscalar ?_
    rw [hM]
    have hpos : (0:ℝ) ≤ 2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)) := by positivity
    nlinarith [hg0, hpos]
  rcases eq_or_ne D 0 with hzero | hne
  · rw [hzero, norm_zero]
    exact hM0
  · have hnorm : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    set v : X := ((((‖D‖ : ℝ)⁻¹ : ℝ) : ℂ)) • D with hv
    have hvnorm : ‖v‖ = 1 := by
      rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    have hinner : (inner ℂ v D : ℂ) = ((‖D‖ : ℝ) : ℂ) := by
      have hDne : ((‖D‖ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact hnorm
      have hsq : (inner ℂ D D : ℂ) = ((‖D‖ : ℝ) : ℂ) * ((‖D‖ : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, sq]
        norm_cast
      rw [hv, inner_smul_left, hsq, Complex.conj_ofReal]
      push_cast
      field_simp
    have := hkey v hvnorm
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg D)] at this
    exact this

end Vector

end

end GaloisForLFunctions.HTGeometry
