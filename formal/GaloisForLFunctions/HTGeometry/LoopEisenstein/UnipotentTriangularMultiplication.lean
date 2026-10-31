import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientStream
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientPrefixes

/-!
# Triangular multiplication of unipotent coefficient streams

In the order `b₀,c₁,a₁,b₁,c₂,a₂,…`, each product coefficient is the sum
of the two input coefficients plus a function of their strictly earlier
coefficients. Zero convolution boundaries give this law over every
commutative ring.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {R : Type*} [CommRing R]

@[simp] theorem unipotentStream_upperRight (g : unipotentCoefficientGroup R) (n : ℕ) :
    unipotentCoefficientStreamEquiv R g (3 * n) = PowerSeries.coeff n (g.1 0 1) :=
  unipotentCoordinatesToStream_upperRight R (unipotentCoefficientEquiv R g) n

@[simp] theorem unipotentStream_lowerLeft (g : unipotentCoefficientGroup R) (n : ℕ) :
    unipotentCoefficientStreamEquiv R g (3 * n + 1) = PowerSeries.coeff (n + 1) (g.1 1 0) :=
  unipotentCoordinatesToStream_lowerLeft R (unipotentCoefficientEquiv R g) n

@[simp] theorem unipotentStream_upperLeft (g : unipotentCoefficientGroup R) (n : ℕ) :
    unipotentCoefficientStreamEquiv R g (3 * n + 2) = PowerSeries.coeff (n + 1) (g.1 0 0) :=
  unipotentCoordinatesToStream_upperLeft R (unipotentCoefficientEquiv R g) n

private theorem prefix_upperLeft {g h : unipotentCoefficientGroup R} {N : ℕ}
    (hp : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k)
    (m : ℕ) (hm : 3 * m ≤ N) : PowerSeries.coeff m (g.1 0 0) = PowerSeries.coeff m (h.1 0 0) := by
  cases m with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff,
      ((mem_unipotentCoefficientGroup R g).mp g.property).1,
      ((mem_unipotentCoefficientGroup R h).mp h.property).1]
  | succ m => simpa only [unipotentStream_upperLeft] using hp (3 * m + 2) (by omega)

private theorem prefix_upperRight {g h : unipotentCoefficientGroup R} {N : ℕ}
    (hp : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k)
    (m : ℕ) (hm : 3 * m < N) : PowerSeries.coeff m (g.1 0 1) = PowerSeries.coeff m (h.1 0 1) := by
  simpa only [unipotentStream_upperRight] using hp (3 * m) hm

private theorem prefix_lowerLeft {g h : unipotentCoefficientGroup R} {N : ℕ}
    (hp : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k)
    (m : ℕ) (hm : 3 * m ≤ N + 1) : PowerSeries.coeff m (g.1 1 0) = PowerSeries.coeff m (h.1 1 0) := by
  cases m with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff,
      ((mem_unipotentCoefficientGroup R g).mp g.property).2.1,
      ((mem_unipotentCoefficientGroup R h).mp h.property).2.1]
  | succ m => simpa only [unipotentStream_lowerLeft] using hp (3 * m + 1) (by omega)

private theorem prefix_lowerRight {g h : unipotentCoefficientGroup R} {N : ℕ}
    (hp : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R h k)
    (m : ℕ) (hm : 3 * m ≤ N) : PowerSeries.coeff m (g.1 1 1) = PowerSeries.coeff m (h.1 1 1) := by
  apply unipotentCoefficient_lowerRight_congr g h m
  · exact fun j hj => prefix_upperLeft hp j (by omega)
  · exact fun j hj => prefix_upperRight hp j (by omega)
  · exact fun j hj => prefix_lowerLeft hp j (by omega)

private theorem upperLeft_sub_one_zero (g : unipotentCoefficientGroup R) :
    PowerSeries.constantCoeff (g.1 0 0 - 1) = 0 := by
  rw [map_sub, ((mem_unipotentCoefficientGroup R g).mp g.property).1, map_one, sub_self]

private theorem lowerRight_sub_one_zero (g : unipotentCoefficientGroup R) :
    PowerSeries.constantCoeff (g.1 1 1 - 1) = 0 := by
  rw [map_sub, ((mem_unipotentCoefficientGroup R g).mp g.property).2.2, map_one, sub_self]

private theorem lowerLeft_zero (g : unipotentCoefficientGroup R) :
    PowerSeries.constantCoeff (g.1 1 0) = 0 :=
  ((mem_unipotentCoefficientGroup R g).mp g.property).2.1

/-- The nonlinear part of one actual product coordinate. -/
def unipotentStreamDefect (g h : unipotentCoefficientGroup R) (N : ℕ) : R :=
  unipotentCoefficientStreamEquiv R (g * h) N -
    unipotentCoefficientStreamEquiv R g N - unipotentCoefficientStreamEquiv R h N

private theorem upperRight_defect_prefix (g h g' h' : unipotentCoefficientGroup R) (n : ℕ)
    (hg : ∀ k < 3 * n, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R g' k)
    (hh : ∀ k < 3 * n, unipotentCoefficientStreamEquiv R h k = unipotentCoefficientStreamEquiv R h' k) :
    unipotentStreamDefect g h (3 * n) = unipotentStreamDefect g' h' (3 * n) := by
  simp only [unipotentStreamDefect, unipotentStream_upperRight]
  rw [← map_sub, ← map_sub, ← map_sub, ← map_sub,
    unipotentCoefficient_upperRight_defect, unipotentCoefficient_upperRight_defect]
  simp only [map_add]
  apply congrArg₂ (· + ·)
  · apply coeff_mul_congr_zero_left n (upperLeft_sub_one_zero g) (upperLeft_sub_one_zero g')
    · intro m hm
      rw [map_sub, map_sub, prefix_upperLeft hg m (by omega)]
    · exact fun m hm => prefix_upperRight hh m (by omega)
  · apply coeff_mul_congr_zero_right n (lowerRight_sub_one_zero h) (lowerRight_sub_one_zero h')
    · exact fun m hm => prefix_upperRight hg m (by omega)
    · intro m hm
      rw [map_sub, map_sub, prefix_lowerRight hh m (by omega)]

private theorem lowerLeft_defect_prefix (g h g' h' : unipotentCoefficientGroup R) (n : ℕ)
    (hg : ∀ k < 3 * n + 1, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R g' k)
    (hh : ∀ k < 3 * n + 1, unipotentCoefficientStreamEquiv R h k = unipotentCoefficientStreamEquiv R h' k) :
    unipotentStreamDefect g h (3 * n + 1) = unipotentStreamDefect g' h' (3 * n + 1) := by
  simp only [unipotentStreamDefect, unipotentStream_lowerLeft]
  rw [← map_sub, ← map_sub, ← map_sub, ← map_sub,
    unipotentCoefficient_lowerLeft_defect, unipotentCoefficient_lowerLeft_defect]
  simp only [map_add]
  apply congrArg₂ (· + ·)
  · apply coeff_mul_congr_zero_constants (n + 1) (lowerLeft_zero g) (upperLeft_sub_one_zero h)
      (lowerLeft_zero g') (upperLeft_sub_one_zero h')
    · exact fun m hm => prefix_lowerLeft hg m (by omega)
    · intro m hm
      rw [map_sub, map_sub, prefix_upperLeft hh m (by omega)]
  · apply coeff_mul_congr_zero_constants (n + 1) (lowerRight_sub_one_zero g) (lowerLeft_zero h)
      (lowerRight_sub_one_zero g') (lowerLeft_zero h')
    · intro m hm
      rw [map_sub, map_sub, prefix_lowerRight hg m (by omega)]
    · exact fun m hm => prefix_lowerLeft hh m (by omega)

private theorem upperLeft_defect_formula (g h : unipotentCoefficientGroup R) (n : ℕ) :
    unipotentStreamDefect g h (3 * n + 2) =
      PowerSeries.coeff (n + 1) ((g.1 0 0 - 1) * (h.1 0 0 - 1) + g.1 0 1 * h.1 1 0) := by
  have he := congrArg (PowerSeries.coeff (n + 1) (R := R))
    (unipotentCoefficient_upperLeft_defect g h)
  simpa only [map_add, map_sub, PowerSeries.coeff_one, Nat.add_one_ne_zero,
    if_false, add_zero, unipotentStreamDefect, unipotentStream_upperLeft] using he

private theorem upperLeft_defect_prefix (g h g' h' : unipotentCoefficientGroup R) (n : ℕ)
    (hg : ∀ k < 3 * n + 2, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R g' k)
    (hh : ∀ k < 3 * n + 2, unipotentCoefficientStreamEquiv R h k = unipotentCoefficientStreamEquiv R h' k) :
    unipotentStreamDefect g h (3 * n + 2) = unipotentStreamDefect g' h' (3 * n + 2) := by
  rw [upperLeft_defect_formula, upperLeft_defect_formula]
  simp only [map_add]
  apply congrArg₂ (· + ·)
  · apply coeff_mul_congr_zero_constants (n + 1) (upperLeft_sub_one_zero g) (upperLeft_sub_one_zero h)
      (upperLeft_sub_one_zero g') (upperLeft_sub_one_zero h')
    · intro m hm
      rw [map_sub, map_sub, prefix_upperLeft hg m (by omega)]
    · intro m hm
      rw [map_sub, map_sub, prefix_upperLeft hh m (by omega)]
  · apply coeff_mul_congr_zero_right (n + 1) (lowerLeft_zero h) (lowerLeft_zero h')
    · exact fun m hm => prefix_upperRight hg m (by omega)
    · exact fun m hm => prefix_lowerLeft hh m (by omega)

/-- Every nonlinear product coordinate depends only on the two strict input prefixes. -/
theorem unipotentStreamDefect_prefix_congr (g h g' h' : unipotentCoefficientGroup R) (N : ℕ)
    (hg : ∀ k < N, unipotentCoefficientStreamEquiv R g k = unipotentCoefficientStreamEquiv R g' k)
    (hh : ∀ k < N, unipotentCoefficientStreamEquiv R h k = unipotentCoefficientStreamEquiv R h' k) :
    unipotentStreamDefect g h N = unipotentStreamDefect g' h' N := by
  have hc : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
  rcases hc with hc | hc | hc
  · have he : N = 3 * (N / 3) := by omega
    rw [he] at hg hh ⊢
    exact upperRight_defect_prefix g h g' h' (N / 3) hg hh
  · have he : N = 3 * (N / 3) + 1 := by omega
    rw [he] at hg hh ⊢
    exact lowerLeft_defect_prefix g h g' h' (N / 3) hg hh
  · have he : N = 3 * (N / 3) + 2 := by omega
    rw [he] at hg hh ⊢
    exact upperLeft_defect_prefix g h g' h' (N / 3) hg hh

/-- Complete a finite coordinate prefix with zeros. -/
def unipotentPrefixCompletion {N : ℕ} (x : Fin N → R) : unipotentCoefficientGroup R :=
  (unipotentCoefficientStreamEquiv R).symm (fun k => if hk : k < N then x ⟨k, hk⟩ else 0)

/-- The finite correction in the actual completed group multiplication law. -/
def unipotentTriangularCorrection (N : ℕ) (x y : Fin N → R) : R :=
  unipotentStreamDefect (unipotentPrefixCompletion x) (unipotentPrefixCompletion y) N

/-- Multiplication is triangular in the unrestricted coefficient stream. -/
theorem unipotentStream_mul (g h : unipotentCoefficientGroup R) (N : ℕ) :
    unipotentCoefficientStreamEquiv R (g * h) N =
      unipotentCoefficientStreamEquiv R g N + unipotentCoefficientStreamEquiv R h N +
        unipotentTriangularCorrection N (fun i => unipotentCoefficientStreamEquiv R g i.val)
          (fun i => unipotentCoefficientStreamEquiv R h i.val) := by
  have he := unipotentStreamDefect_prefix_congr g h
    (unipotentPrefixCompletion (fun i : Fin N => unipotentCoefficientStreamEquiv R g i.val))
    (unipotentPrefixCompletion (fun i : Fin N => unipotentCoefficientStreamEquiv R h i.val)) N
    (fun k hk => by simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply, dif_pos hk])
    (fun k hk => by simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply, dif_pos hk])
  change unipotentStreamDefect g h N = unipotentTriangularCorrection N _ _ at he
  rw [← he, unipotentStreamDefect]
  ring

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentStreamDefect_prefix_congr
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentStream_mul
