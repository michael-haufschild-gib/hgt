import GaloisForLFunctions.HTGeometry.FokasLenellsRawInteraction
import GaloisForLFunctions.HTGeometry.HolomorphicRightEvolution

/-!
# Original scattering evolution with the zero frequency included

The corpus's Carathéodory/Picard evolution constructs the raw interaction
flow for every real frequency. At exp κ it agrees exactly with the existing
original Fokas–Lenells eigenfunction in its rotating frame. At k = 0 it is
the identity. Thus subsequent low-frequency expansions concern the actual
constructed scattering flow, with its missing endpoint now filled in.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawInteractionEvolution (q : SchwartzMap ℝ ℂ) (k : ℝ) (x : ℝ) : RawOperator :=
  caratheodoryEvolution (rawInteractionOperator q k) x

theorem continuous_rawInteractionEvolution (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    Continuous (rawInteractionEvolution q k) :=
  continuous_caratheodoryEvolution (rawInteractionOperator_integrable q k).locallyIntegrable

theorem rawInteractionEvolution_initial (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    rawInteractionEvolution q k 0 = 1 :=
  caratheodoryEvolution_zero (rawInteractionOperator_integrable q k).locallyIntegrable

theorem rawInteractionEvolution_hasDerivAt (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    HasDerivAt (rawInteractionEvolution q k)
      (rawInteractionOperator q k x*rawInteractionEvolution q k x) x :=
  hasDerivAt_caratheodoryEvolution_of_continuous (continuous_rawInteractionOperator q k) x

theorem rawInteractionEvolution_equation (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    rawInteractionEvolution q k x = 1+
      ∫ s in (0 : ℝ)..x, rawInteractionOperator q k s*rawInteractionEvolution q k s :=
  caratheodoryEvolution_integral_equation (rawInteractionOperator_integrable q k).locallyIntegrable x

def rawInteractionSolution (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawInteractionEvolution q k x v

theorem continuous_rawInteractionSolution (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawInteractionSolution q k v) :=
  (continuous_rawInteractionEvolution q k).clm_apply continuous_const

theorem rawInteractionSolution_initial (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    rawInteractionSolution q k v 0 = v := by
  unfold rawInteractionSolution
  rw [rawInteractionEvolution_initial]
  rfl

theorem rawInteractionSolution_hasDerivAt (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    HasDerivAt (rawInteractionSolution q k v)
      (rawInteractionOperator q k x (rawInteractionSolution q k v x)) x := by
  have hd := ((ContinuousLinearMap.apply ℂ SpectralVector v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (rawInteractionEvolution_hasDerivAt q k x)
  exact hd

theorem rawInteractionSolution_equation (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawInteractionSolution q k v x = v+
      ∫ s in (0 : ℝ)..x, rawInteractionOperator q k s (rawInteractionSolution q k v s) := by
  have hc := (continuous_rawInteractionOperator q k).clm_apply (continuous_rawInteractionSolution q k v)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rawInteractionSolution_hasDerivAt q k v s) (hc.intervalIntegrable 0 x)
  rw [hi,rawInteractionSolution_initial]
  abel

theorem rawInteractionEvolution_zero_frequency (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    rawInteractionEvolution q 0 x = 1 := by
  rw [rawInteractionEvolution_equation]
  simp only [rawInteractionOperator_zero,zero_mul,intervalIntegral.integral_zero,add_zero]

theorem rawInteractionSolution_zero_frequency (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawInteractionSolution q 0 v x = v := by
  unfold rawInteractionSolution
  rw [rawInteractionEvolution_zero_frequency]
  rfl

private theorem continuous_rawKernel (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    Continuous (fun p : ℝ × ℝ => (rawInteractionOperator q k p.2).restrictScalars ℝ) := by
  have hh := (continuous_rawInteractionOperator q k).comp (continuous_snd (X := ℝ) (Y := ℝ))
  exact (ContinuousLinearMap.restrictScalarsIsometry ℂ SpectralVector SpectralVector ℝ ℝ).continuous.comp hh

private theorem rawKernel_bound (q : SchwartzMap ℝ ℂ) (k _t s : ℝ) :
    ‖(rawInteractionOperator q k s).restrictScalars ℝ‖ ≤ |k| * rawInteractionSup q := by
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact rawInteractionOperator_uniform_bound q k s

/-- A literal equality with the earlier globally convergent Volterra construction. -/
theorem rawInteractionSolution_eq_volterra (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    rawInteractionSolution q k v = volterraSolution (fun _ => v)
      (fun _ s => (rawInteractionOperator q k s).restrictScalars ℝ) := by
  have hm := mul_nonneg (abs_nonneg k) (rawInteractionSup_nonneg q)
  exact volterra_eq_of_eq_of_eq (continuous_rawKernel q k) hm (rawKernel_bound q k)
    (continuous_rawInteractionSolution q k v)
    (continuous_volterraSolution continuous_const (continuous_rawKernel q k) hm (norm_nonneg v)
      (rawKernel_bound q k) (fun _ => le_rfl))
    (rawInteractionSolution_equation q k v)
    (volterraSolution_eq continuous_const (continuous_rawKernel q k) hm (norm_nonneg v)
      (rawKernel_bound q k) (fun _ => le_rfl))

/-- The extension agrees with the actual original interaction solution at every positive spectral parameter. -/
theorem rawInteractionSolution_exp_eq (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    rawInteractionSolution q (Real.exp κ) v = interactionSolution q κ v := by
  have hc : Continuous (fun s => rawInteractionOperator q (Real.exp κ) s (interactionSolution q κ v s)) :=
    (continuous_rawInteractionOperator q (Real.exp κ)).clm_apply (interactionSolution_continuous q κ v)
  have he (x : ℝ) : interactionSolution q κ v x = v+
      ∫ s in (0 : ℝ)..x, rawInteractionOperator q (Real.exp κ) s (interactionSolution q κ v s) := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (interactionSolution_hasDerivAt q κ v s).congr_deriv
        (rawInteractionOperator_exp_apply q κ s (interactionSolution q κ v s)).symm)
      (hc.intervalIntegrable 0 x)
    rw [hi,interactionSolution_initial]
    abel
  exact volterra_eq_of_eq_of_eq (continuous_rawKernel q (Real.exp κ))
    (mul_nonneg (abs_nonneg _) (rawInteractionSup_nonneg q)) (rawKernel_bound q (Real.exp κ))
    (continuous_rawInteractionSolution q (Real.exp κ) v) (interactionSolution_continuous q κ v)
    (rawInteractionSolution_equation q (Real.exp κ) v) he

/-- The finite-interval bound is uniform over initial vectors, including at the newly filled spectral origin. -/
theorem rawInteractionSolution_local_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawInteractionSolution q k v x‖ ≤ ‖v‖*Real.exp ((|k| * rawInteractionSup q)*|x|) := by
  rw [rawInteractionSolution_eq_volterra]
  exact norm_volterraSolution_le continuous_const (continuous_rawKernel q k)
    (mul_nonneg (abs_nonneg k) (rawInteractionSup_nonneg q)) (norm_nonneg v)
    (rawKernel_bound q k) (fun _ => le_rfl) x

end
end GaloisForLFunctions.HTGeometry.FokasLenells
