import GaloisForLFunctions.HTGeometry.VolterraStrongKernel

/-! Causal support and preserved linear constraints for the actual Volterra solution. -/
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A source zero before the initial time has every Volterra iterate zero there. -/
theorem volterraIterate_zero_of_nonpos (f : ℝ → X) (K : ℝ → ℝ → X →L[ℝ] X)
    (hf : ∀ t : ℝ, t ≤ 0 → f t = 0) (n : ℕ) (t : ℝ) (ht : t ≤ 0) :
    volterraIterate f K n t = 0 := by
  induction n generalizing t with
  | zero => exact hf t ht
  | succ n ih =>
    rw [volterraIterate_succ,hf t ht,zero_add]
    calc
      _ = ∫ s in (0:ℝ)..t, (0:X) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs₀ : s ≤ 0 := by rw [uIcc_of_ge ht] at hs; exact hs.2
        change K t s (volterraIterate f K n s) = 0
        rw [ih s hs₀,map_zero]
      _ = 0 := intervalIntegral.integral_zero

/-- The constructed solution itself retains the source's negative-time support. -/
theorem volterraSolution_zero_of_nonpos (f : ℝ → X) (K : ℝ → ℝ → X →L[ℝ] X)
    (hf : ∀ t : ℝ, t ≤ 0 → f t = 0) (t : ℝ) (ht : t ≤ 0) :
    volterraSolution f K t = 0 := by
  unfold volterraSolution
  simp only [hf t ht,volterraIterate_zero_of_nonpos f K hf _ t ht,sub_self,tsum_zero,add_zero]

variable [CompleteSpace X]

/-- A fixed linear constraint respected by the kernel and source is retained by every iterate. -/
theorem volterraIterate_fixed (f : ℝ → X) (K : ℝ → ℝ → X →L[ℝ] X)
    (hf : Continuous f) (hK : StrongKernel K) (A : X →L[ℝ] X)
    (hAf : ∀ t, A (f t) = f t) (hAK : ∀ t s x, A (K t s x) = K t s (A x))
    (n : ℕ) (t : ℝ) : A (volterraIterate f K n t) = volterraIterate f K n t := by
  induction n generalizing t with
  | zero => exact hAf t
  | succ n ih =>
    rw [volterraIterate_succ,map_add,hAf]
    have hi : IntervalIntegrable (fun s => K t s (volterraIterate f K n s)) volume 0 t :=
      ((hK _ (continuous_volterraIterate_of_strong hf hK n)).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
    rw [← A.intervalIntegral_comp_comm hi]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    change A (K t s (volterraIterate f K n s)) = K t s (volterraIterate f K n s)
    rw [hAK,ih]

/-- The actual continuous solution inherits every source-compatible commuting linear constraint. -/
theorem volterraSolution_fixed (f : ℝ → X) (K : ℝ → ℝ → X →L[ℝ] X)
    (hf : Continuous f) (hK : StrongKernel K) (M F : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hKb : ∀ t s, ‖K t s‖ ≤ M) (hfb : ∀ t, ‖f t‖ ≤ F) (A : X →L[ℝ] X)
    (hAf : ∀ t, A (f t) = f t) (hAK : ∀ t s x, A (K t s x) = K t s (A x))
    (t : ℝ) : A (volterraSolution f K t) = volterraSolution f K t := by
  have h := tendsto_volterraIterate_of_strong hf hK hM hF hKb hfb t
  have ha := A.continuous.continuousAt.tendsto.comp h
  have he : (fun n => A (volterraIterate f K n t)) = (fun n => volterraIterate f K n t) :=
    funext (fun n => volterraIterate_fixed f K hf hK A hAf hAK n t)
  simp only [Function.comp_def] at ha
  rw [he] at ha
  exact tendsto_nhds_unique ha h

end
end GaloisForLFunctions.HTGeometry
