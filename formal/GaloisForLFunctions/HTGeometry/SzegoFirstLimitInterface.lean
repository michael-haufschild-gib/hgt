import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Exact interface to the first Szegő limit theorem

The extended first Szegő limit theorem is a classical input, so this module does not reprove it.
It formalizes the theorem's exact statement boundary.  For a finite positive measure `mu` and a
reference measure `m`, its target is the geometric mean of the Radon--Nikodym derivative of the
absolutely continuous part, not the already-specialized value zero.

The source convention

`GM(w) = exp (integral log w)`

assigns value zero when `log w` has integral `-infinity`.  Lean's total real logarithm has
`Real.log 0 = 0`, so the convention must be represented explicitly: the exponential formula is
used exactly when the density is positive almost everywhere and its real logarithm is integrable;
the value is zero otherwise.  For integrable nonnegative densities this is the usual extended
geometric mean.

From the exact classical ratio conclusion, Lean proves the specialization that a measure singular
to the reference measure has determinant ratio tending to zero.  Thus no singular-carrier
conclusion is hidden inside the literature hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MeasureTheory Filter Topology
open scoped ENNReal Topology

noncomputable section

/-- The extended geometric mean used in the first Szegő limit theorem.

For a finite nonnegative density, failure of either almost-everywhere positivity or logarithmic
integrability is precisely the classical `exp (-infinity) = 0` case. -/
noncomputable def szegoGeometricMean {X : Type*} [MeasurableSpace X]
    (m : Measure X) (w : X → ℝ≥0∞) : ℝ := by
  classical
  exact if _h : (∀ᵐ x ∂m, 0 < w x ∧ w x < ∞) ∧
        Integrable (fun x => Real.log (w x).toReal) m then
      Real.exp (∫ x, Real.log (w x).toReal ∂m)
    else 0

/-- In the finite-logarithm case the extended geometric mean is literally the exponential of the
logarithmic integral appearing in the classical statement. -/
theorem szegoGeometricMean_eq_exp_integral {X : Type*} [MeasurableSpace X]
    (m : Measure X) (w : X → ℝ≥0∞)
    (hpos : ∀ᵐ x ∂m, 0 < w x ∧ w x < ∞)
    (hint : Integrable (fun x => Real.log (w x).toReal) m) :
    szegoGeometricMean m w = Real.exp (∫ x, Real.log (w x).toReal ∂m) := by
  rw [szegoGeometricMean, dif_pos ⟨hpos, hint⟩]

/-- The Szegő geometric mean is nonnegative. -/
theorem szegoGeometricMean_nonneg {X : Type*} [MeasurableSpace X]
    (m : Measure X) (w : X → ℝ≥0∞) : 0 ≤ szegoGeometricMean m w := by
  classical
  rw [szegoGeometricMean]
  split_ifs
  · exact Real.exp_pos _ |>.le
  · exact le_rfl

/-- The extended Szegő geometric mean depends only on the almost-everywhere density class. -/
theorem szegoGeometricMean_congr_ae {X : Type*} [MeasurableSpace X]
    (m : Measure X) (w v : X → ℝ≥0∞) (hwv : w =ᵐ[m] v) :
    szegoGeometricMean m w = szegoGeometricMean m v := by
  classical
  have hpos :
      (∀ᵐ x ∂m, 0 < w x ∧ w x < ∞) ↔ (∀ᵐ x ∂m, 0 < v x ∧ v x < ∞) := by
    constructor
    · intro hw
      filter_upwards [hw, hwv] with x hx hxeq
      simpa [← hxeq] using hx
    · intro hv
      filter_upwards [hv, hwv] with x hx hxeq
      simpa [hxeq] using hx
  have hlog : (fun x => Real.log (w x).toReal) =ᵐ[m]
      (fun x => Real.log (v x).toReal) := by
    filter_upwards [hwv] with x hx
    simp [hx]
  have hint : Integrable (fun x => Real.log (w x).toReal) m ↔
      Integrable (fun x => Real.log (v x).toReal) m := by
    constructor
    · intro hw
      exact hw.congr hlog
    · intro hv
      exact hv.congr hlog.symm
  unfold szegoGeometricMean
  by_cases hw : (∀ᵐ x ∂m, 0 < w x ∧ w x < ∞) ∧
      Integrable (fun x => Real.log (w x).toReal) m
  · have hv : (∀ᵐ x ∂m, 0 < v x ∧ v x < ∞) ∧
        Integrable (fun x => Real.log (v x).toReal) m :=
      ⟨hpos.mp hw.1, hint.mp hw.2⟩
    rw [dif_pos hw, dif_pos hv, integral_congr_ae hlog]
  · have hv : ¬ ((∀ᵐ x ∂m, 0 < v x ∧ v x < ∞) ∧
        Integrable (fun x => Real.log (v x).toReal) m) := by
      contrapose! hw
      exact ⟨hpos.mpr hw.1, hint.mpr hw.2⟩
    rw [dif_neg hw, dif_neg hv]

/-- The classical zero convention is recovered when the density vanishes almost everywhere. -/
theorem szegoGeometricMean_eq_zero_of_ae_eq_zero {X : Type*} [MeasurableSpace X]
    (m : Measure X) [NeZero m] (w : X → ℝ≥0∞) (hw : w =ᵐ[m] 0) :
    szegoGeometricMean m w = 0 := by
  classical
  rw [szegoGeometricMean]
  split_ifs with h
  · have hpos : ∀ᵐ x ∂m, 0 < w x := h.1.mono fun x hx => hx.1
    have hfalse : ∀ᵐ x ∂m, False := (hpos.and hw).mono fun x hx => by
      simpa [hx.2] using hx.1
    rcases Filter.Eventually.exists hfalse with ⟨x, hx⟩
    exact hx.elim
  · rfl

/-- For a singular measure, the Radon--Nikodym density occurring in the classical theorem has
zero Szegő geometric mean.  This is a formal deduction from Lebesgue decomposition, not an
external analytic input. -/
theorem szegoGeometricMean_rnDeriv_eq_zero_of_mutuallySingular
    {X : Type*} [MeasurableSpace X] (mu m : Measure X) [NeZero m]
    (hsing : mu ⟂ₘ m) :
    szegoGeometricMean m (mu.rnDeriv m) = 0 :=
  szegoGeometricMean_eq_zero_of_ae_eq_zero m _ hsing.rnDeriv_ae_eq_zero

/-- The consecutive determinant-ratio sequence in the first Szegő limit theorem. -/
def consecutiveGramDeterminantRatio
    (G : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (N : ℕ) : ℝ :=
  (G (N + 1)).det.re / (G N).det.re

/-- Exact conclusion of the classical first Szegő limit theorem for a chosen Toeplitz Gram
tower.  In applications `G N` is definitionally the `(N+1)`-by-`(N+1)` Fourier Toeplitz section
of `mu`; the literature supplies this conclusion and no specialized singular consequence. -/
def HasSzegoFirstLimitConclusion {X : Type*} [MeasurableSpace X]
    (G : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (mu m : Measure X) : Prop :=
  Tendsto (consecutiveGramDeterminantRatio G) atTop
    (𝓝 (szegoGeometricMean m (mu.rnDeriv m)))

/-- **Singular specialization of the exact classical interface.** If the measure is singular to
the reference measure, the classical first Szegő conclusion forces consecutive determinant ratios
to tend to zero. -/
theorem consecutiveGramDeterminantRatio_tendsto_zero_of_szego_of_mutuallySingular
    {X : Type*} [MeasurableSpace X]
    (G : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (mu m : Measure X) [NeZero m] (hsing : mu ⟂ₘ m)
    (hszego : HasSzegoFirstLimitConclusion G mu m) :
    Tendsto (consecutiveGramDeterminantRatio G) atTop (𝓝 0) := by
  have hgm := szegoGeometricMean_rnDeriv_eq_zero_of_mutuallySingular mu m hsing
  simpa only [HasSzegoFirstLimitConclusion, hgm] using hszego

end

end GaloisForLFunctions.HTGeometry
