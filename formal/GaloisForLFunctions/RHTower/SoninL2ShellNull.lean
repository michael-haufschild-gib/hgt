/-
Concrete constraint facts for the fixed-cutoff Sonin model on complex `L²(ℝ)`.

The bounded-support Fourier uncertainty theorem makes the physical and Fourier forbidden ranges
transverse.  Finite time-band compactness then sends the explicit orthonormal symmetric shell
sequence to zero under the Fourier-forbidden projection.
-/
import GaloisForLFunctions.RHTower.L2FourierUncertainty
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact
import GaloisForLFunctions.RHTower.SoninL2Model

noncomputable section

open MeasureTheory Set
open Filter Topology

namespace RHTower

/-- The physical and Fourier forbidden subspaces for a bounded symmetric interval have trivial
intersection. -/
theorem physicalForbidden_inf_fourierForbidden_eq_bot (a : ℝ) :
    physicalForbidden (Set.Icc (-a) a) measurableSet_Icc ⊓
        fourierForbidden (Set.Icc (-a) a) measurableSet_Icc = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_bot]
    have hphysical :
        indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc f = f := by
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection_eq_self_iff.mpr
        hf.1
    have hfourier : fourierCutoff (Set.Icc (-a) a) measurableSet_Icc f = f := by
      rw [fourierCutoff_eq_fourierForbidden_starProjection]
      exact (fourierForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection_eq_self_iff.mpr
        hf.2
    have hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc (-a) a → (f : ℝ → ℂ) x = 0 := by
      filter_upwards [indicatorCutoff_ae (Set.Icc (-a) a) measurableSet_Icc f] with x hx
      intro houtside
      rw [hphysical] at hx
      simpa [houtside] using hx
    have hfourierCutoff :
        indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc (fourierUnitary f) =
          fourierUnitary f := by
      have h := congrArg fourierUnitary hfourier
      simpa only [fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply] using h
    have hFsupp : ∀ᵐ w ∂volume, w ∉ Set.Icc (-a) a →
        ((fourierUnitary f : SoninL2) : ℝ → ℂ) w = 0 := by
      filter_upwards [indicatorCutoff_ae (Set.Icc (-a) a) measurableSet_Icc
        (fourierUnitary f)] with w hw
      intro houtside
      rw [hfourierCutoff] at hw
      simpa [houtside] using hw
    exact l2_fourier_uncertainty f hsupp (by simpa [fourierUnitary] using hFsupp)
  · exact bot_le

/-- The Fourier-forbidden projection is norm-null on the explicit orthonormal symmetric shell
sequence. -/
theorem fourierForbidden_starProjection_evenShellVector_tendsto_zero
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n =>
      ‖(fourierForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection
        (evenShellVector a b ha hab n)‖) atTop (𝓝 0) := by
  have hcompact : IsCompactOperator (shellCutoffFourierCutoff a b) :=
    isCompactOperator_shellCutoffFourierCutoff a b ha
  have hnull := IsCompactOperator.norm_apply_tendsto_zero_of_orthonormal
    (shellCutoffFourierCutoff a b) hcompact (evenShellVector_orthonormal a b ha hab)
  apply hnull.congr'
  exact Filter.Eventually.of_forall fun n => by
    rw [← fourierCutoff_eq_fourierForbidden_starProjection]
    change ‖fourierUnitary.symm
        (indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
          (fourierUnitary (evenShellVector a b ha hab n)))‖ =
      ‖indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
        (fourierUnitary
          (indicatorCutoff (closedEvenShell a b) (measurableSet_closedEvenShell a b)
            (evenShellVector a b ha hab n)))‖
    rw [fourierUnitary.symm.norm_map, shellCutoff_evenShellVector]

end RHTower
