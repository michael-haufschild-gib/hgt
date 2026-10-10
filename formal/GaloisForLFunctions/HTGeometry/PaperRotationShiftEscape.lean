import GaloisForLFunctions.HTGeometry.PaperRotationCommutatorIdealTrace
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Bilateral shifts escape every compact operator

Every fixed vector translates weakly to zero. The existing bounded-coordinate convergence
criterion on `ℓ²` turns coordinate escape into weak escape, and the native compact-operator
theorem turns it into norm convergence after any compact operator.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- Square summability forces the bilateral coordinates to vanish off finite sets. -/
theorem paperRotationHilbert_coordinate_tendsto (v : PaperRotationHilbert) :
    Tendsto (fun i : ℤ => v i) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (summable_norm_sq_lp v).tendsto_cofinite_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- Every fixed coordinate of a translated vector vanishes. -/
theorem paperRotationShift_coordinate_tendsto (v : PaperRotationHilbert) (i : ℤ) :
    Tendsto (fun n : ℕ => (paperRotationShift (n : ℤ) v : ℤ → ℂ) i)
      atTop (𝓝 0) := by
  have hi : Function.Injective (fun n : ℕ => i - (n : ℤ)) := by
    intro m n h
    change i - (m : ℤ) = i - (n : ℤ) at h
    omega
  have ht := hi.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at ht
  exact (paperRotationHilbert_coordinate_tendsto v).comp ht

/-- Bilateral translates of every vector converge weakly to zero. -/
theorem paperRotationShift_weak_tendsto (v z : PaperRotationHilbert) :
    Tendsto (fun n : ℕ => inner ℂ z (paperRotationShift (n : ℤ) v))
      atTop (𝓝 0) :=
  tendsto_inner_lp_of_coord (fun n : ℕ => paperRotationShift (n : ℤ) v) (norm_nonneg v)
    (fun n => (paperRotationShift_norm (n : ℤ) v).le)
    (paperRotationShift_coordinate_tendsto v) z

/-- Every compact operator kills bilateral translates in norm, for every fixed input vector. -/
theorem paperRotationShift_compact_tendsto
    (K : compactOperatorStarAlgebra PaperRotationHilbert) (v : PaperRotationHilbert) :
    Tendsto (fun n : ℕ => K.1 (paperRotationShift (n : ℤ) v)) atTop (𝓝 0) := by
  let C : ℝ := ‖v‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let u : PaperRotationHilbert := ((C⁻¹ : ℝ) : ℂ) • v
  have hu : ‖u‖ ≤ 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hC]
    rw [inv_mul_le_iff₀ hC, mul_one]
    dsimp [C]
    linarith
  have huv : (C : ℂ) • u = v := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hC.ne',
      Complex.ofReal_one, one_smul]
  have ht := tendsto_norm_compact_of_weaklyNull K.1 K.2
    (fun n : ℕ => paperRotationShift (n : ℤ) u)
    (fun n => (paperRotationShift_norm (n : ℤ) u).le.trans hu)
    (fun z => paperRotationShift_weak_tendsto u z)
  have hs := (tendsto_const_nhds (x := (C : ℂ))).smul ht
  simpa only [← map_smul, huv, smul_zero] using hs

end

end GaloisForLFunctions.HTGeometry
