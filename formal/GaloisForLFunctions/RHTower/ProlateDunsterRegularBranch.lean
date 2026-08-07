import GaloisForLFunctions.RHTower.ProlateDunsterComparisonBridge

/-!
# Regular endpoint branch of the Dunster comparison equation

This file identifies the endpoint normalization of the two exact Bessel comparison solutions.
The regular branch tends to one; the independent branch diverges logarithmically.  It also evaluates
the weighted Wronskian exactly, rather than retaining it as an unspecified positive constant.
-/

noncomputable section

open Filter Set Topology

namespace GaloisForLFunctions.RHTower

/-- The second Bessel solution diverges to negative infinity at the positive origin. -/
theorem besselK_tendsto_atBot_zero :
    Tendsto besselK (nhdsWithin 0 (Ioi 0)) atBot := by
  have hJ : Tendsto besselJ0 (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa only [besselJ0_zero] using continuous_besselJ0.continuousAt.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
  have hlogJ : Tendsto (fun u : ℝ => Real.log u * besselJ0 u)
      (nhdsWithin 0 (Ioi 0)) atBot :=
    Real.tendsto_log_nhdsGT_zero.atBot_mul_pos one_pos hJ
  have hmain : Tendsto (fun u : ℝ => Real.pi / 4 * (Real.log u * besselJ0 u))
      (nhdsWithin 0 (Ioi 0)) atBot := by
    exact hlogJ.const_mul_atBot (by positivity : (0 : ℝ) < Real.pi / 4)
  have hM : Tendsto besselM (nhdsWithin 0 (Ioi 0)) (nhds (besselM 0)) :=
    (hasDerivAt_besselM 0).continuousAt.tendsto.mono_left inf_le_left
  have hsum := hmain.atBot_add hM
  apply hsum.congr'
  filter_upwards with u
  rw [besselK]
  ring

/-- The Bessel weighted Wronskian has the endpoint value `pi/4`. -/
theorem besselWronskian_tendsto_pi_div_four :
    Tendsto besselWronskian (nhdsWithin 0 (Ioi 0)) (nhds (Real.pi / 4)) := by
  let rhs : ℝ → ℝ := fun u => Real.pi / 4 * besselJ0 u ^ 2
    + u * (besselJ0 u * besselMDeriv u - besselJ0Deriv u * besselM u)
  have hrhs : ContinuousAt rhs 0 := by
    dsimp [rhs]
    exact (continuousAt_const.mul (continuous_besselJ0.continuousAt.pow 2)).add
      (continuousAt_id.mul
        ((continuous_besselJ0.continuousAt.mul
          (hasDerivAt_besselMDeriv 0).continuousAt).sub
          ((hasDerivAt_besselJ0Deriv 0).continuousAt.mul
            (hasDerivAt_besselM 0).continuousAt)))
  have hrhs0 : rhs 0 = Real.pi / 4 := by
    dsimp [rhs]
    rw [besselJ0_zero]
    ring
  have ht : Tendsto rhs (nhdsWithin 0 (Ioi 0)) (nhds (Real.pi / 4)) := by
    have h := hrhs.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
    convert h using 1
    exact congrArg nhds hrhs0.symm
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (besselWronskian_eq hu).symm

/-- The weighted Wronskian is exactly `pi/4` on the positive ray. -/
theorem besselWronskian_eq_pi_div_four {u : ℝ} (hu : 0 < u) :
    besselWronskian u = Real.pi / 4 := by
  have hid : Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hle : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), x ≤ u :=
    (hid.eventually (Iio_mem_nhds hu)).mono fun _ h => h.le
  have heq : besselWronskian =ᶠ[nhdsWithin 0 (Ioi 0)] fun _ => besselWronskian u := by
    filter_upwards [self_mem_nhdsWithin, hle] with x hx hxu
    exact (besselWronskian_const (a := x) (b := u) hx hxu).symm
  have hconst : Tendsto (fun _ : ℝ => besselWronskian u)
      (nhdsWithin 0 (Ioi 0)) (nhds (besselWronskian u)) := tendsto_const_nhds
  have hconst' : Tendsto (fun _ : ℝ => besselWronskian u)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.pi / 4)) :=
    besselWronskian_tendsto_pi_div_four.congr' heq
  exact tendsto_nhds_unique hconst hconst'

/-- The Liouville phase vanishes at the singular endpoint from the right. -/
theorem xiEndpointPhase_tendsto_zero_at_endpoint
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Tendsto (xiEndpointPhase s) (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have hd : Tendsto (fun x : ℝ => x ^ 2 - 1)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ 2 - 1) 1 := by fun_prop
    convert hcont.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left) using 1; norm_num
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (x ^ 2 - 1))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (xiEndpointPhase_pos hs0 hs1 hx).le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (xiEndpointPhase_bounds hs0 (by linarith : s ≤ 1) hx.le).2

/-- The regular Dunster comparison branch tends to one at the endpoint. -/
theorem lgBesselModel_tendsto_one_at_endpoint
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Tendsto (lgBesselModel s c) (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have harg : Tendsto (fun x : ℝ => c * xiEndpointPhase s x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul (xiEndpointPhase_tendsto_zero_at_endpoint hs0 hs1)
  change Tendsto (fun x : ℝ => besselJ0 (c * xiEndpointPhase s x))
    (nhdsWithin 1 (Ioi 1)) (nhds 1)
  simpa only [Function.comp_def, besselJ0_zero] using
    continuous_besselJ0.continuousAt.tendsto.comp harg

/-- The independent Dunster comparison branch diverges logarithmically at the endpoint. -/
theorem lgBesselModel2_tendsto_atBot_endpoint
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    Tendsto (lgBesselModel2 s c) (nhdsWithin 1 (Ioi 1)) atBot := by
  have harg0 : Tendsto (fun x : ℝ => c * xiEndpointPhase s x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul (xiEndpointPhase_tendsto_zero_at_endpoint hs0 hs1)
  have hargpos : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1),
      c * xiEndpointPhase s x ∈ Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos hc (xiEndpointPhase_pos hs0 hs1 hx)
  have harg : Tendsto (fun x : ℝ => c * xiEndpointPhase s x)
      (nhdsWithin 1 (Ioi 1)) (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨harg0, hargpos⟩
  change Tendsto (fun x : ℝ => besselK (c * xiEndpointPhase s x))
    (nhdsWithin 1 (Ioi 1)) atBot
  exact besselK_tendsto_atBot_zero.comp harg

/-- A homogeneous comparison solution with finite normalized endpoint value one is exactly the
regular `J₀` branch.  The logarithmic coefficient vanishes, and the remaining coefficient is one. -/
theorem eq_regular_dunster_branch_of_tendsto_one
    {s c A B : ℝ} {U : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hU : Tendsto U (nhdsWithin 1 (Ioi 1)) (nhds 1))
    (hrep : ∀ x : ℝ, 1 < x →
      U x = A * lgBesselModel s c x + B * lgBesselModel2 s c x) :
    A = 1 ∧ B = 0 := by
  have hJ := lgBesselModel_tendsto_one_at_endpoint (s := s) (c := c) hs0 hs1
  have hK := lgBesselModel2_tendsto_atBot_endpoint (s := s) hs0 hs1 hc
  have hfinite : Tendsto (fun x => U x - A * lgBesselModel s c x)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - A)) := by
    simpa only [mul_one] using hU.sub (tendsto_const_nhds.mul hJ)
  have hBKfinite : Tendsto (fun x => B * lgBesselModel2 s c x)
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - A)) := by
    apply hfinite.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hrep x hx]
    ring
  have hB0 : B = 0 := by
    rcases lt_trichotomy B 0 with hB | hB | hB
    · have hinf : Tendsto (fun x => B * lgBesselModel2 s c x)
          (nhdsWithin 1 (Ioi 1)) atTop :=
        tendsto_const_nhds.neg_mul_atBot hB hK
      exact absurd hBKfinite (not_tendsto_nhds_of_tendsto_atTop hinf (1 - A))
    · exact hB
    · have hinf : Tendsto (fun x => B * lgBesselModel2 s c x)
          (nhdsWithin 1 (Ioi 1)) atBot := hK.const_mul_atBot hB
      exact absurd hBKfinite (not_tendsto_nhds_of_tendsto_atBot hinf (1 - A))
  refine ⟨?_, hB0⟩
  have hAJ : Tendsto (fun x => A * lgBesselModel s c x)
      (nhdsWithin 1 (Ioi 1)) (nhds A) := by
    simpa using tendsto_const_nhds.mul hJ
  have hU' : Tendsto U (nhdsWithin 1 (Ioi 1)) (nhds A) := by
    apply hAJ.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hrep x hx, hB0, zero_mul, add_zero]
  exact tendsto_nhds_unique hU' hU

end GaloisForLFunctions.RHTower

end
