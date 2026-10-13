import GaloisForLFunctions.HTGeometry.LpSolidDiagonalObservation

/-! # Complete modulus information in diagonal observations

Comparison of every dominated-history response is exactly coefficient-modulus
comparison. Singleton histories witness every strict difference.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {I : Type*}

theorem coordinate_mul_single [DecidableEq I]
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i) (j : I) :
    T (lp.single 2 j (1 : ℂ)) = lp.single 2 j (w j) := by
  ext i
  rw [hT]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h
    rw [mul_one]
  · rw [mul_zero]

theorem lpSolidObservation_coordinate_single [DecidableEq I]
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i) (j : I) :
    lpSolidObservation T (lp.single 2 j (1 : ℂ)) = ‖w j‖ := by
  rw [lpSolidObservation_eq_norm_of_coordinate_mul T w hT, coordinate_mul_single T w hT]
  exact lp.norm_single (E := fun _ : I => ℂ) (by norm_num : (0 : ENNReal) < 2) j (w j)

theorem lpSolidObservation_le_of_coordinate_norm_le
    (T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w v : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i) (hS : ∀ y i, S y i = v i * y i)
    (h : ∀ i, ‖w i‖ ≤ ‖v i‖) (x : lp (fun _ : I => ℂ) 2) :
    lpSolidObservation T x ≤ lpSolidObservation S x := by
  rw [lpSolidObservation_eq_norm_of_coordinate_mul T w hT,
    lpSolidObservation_eq_norm_of_coordinate_mul S v hS]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro i
  rw [hT, hS, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)

theorem forall_lpSolidObservation_le_iff
    (T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w v : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i) (hS : ∀ y i, S y i = v i * y i) :
    (∀ x, lpSolidObservation T x ≤ lpSolidObservation S x) ↔ ∀ i, ‖w i‖ ≤ ‖v i‖ := by
  classical
  constructor
  · intro h i
    simpa only [lpSolidObservation_coordinate_single T w hT,
      lpSolidObservation_coordinate_single S v hS] using h (lp.single 2 i (1 : ℂ))
  · exact fun h => lpSolidObservation_le_of_coordinate_norm_le T S w v hT hS h

theorem forall_lpSolidObservation_eq_iff
    (T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w v : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i) (hS : ∀ y i, S y i = v i * y i) :
    (∀ x, lpSolidObservation T x = lpSolidObservation S x) ↔ ∀ i, ‖w i‖ = ‖v i‖ := by
  constructor
  · intro h i
    exact le_antisymm
      ((forall_lpSolidObservation_le_iff T S w v hT hS).mp (fun x => (h x).le) i)
      ((forall_lpSolidObservation_le_iff S T v w hS hT).mp (fun x => (h x).ge) i)
  · intro h x
    exact le_antisymm
      (lpSolidObservation_le_of_coordinate_norm_le T S w v hT hS (fun i => (h i).le) x)
      (lpSolidObservation_le_of_coordinate_norm_le S T v w hS hT (fun i => (h i).ge) x)

end
end GaloisForLFunctions.HTGeometry
