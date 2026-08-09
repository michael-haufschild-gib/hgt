import GaloisForLFunctions.HTGeometry.PairFamGradient

/-!
# Rescaling the starting vector of an orbit

The shifted operator obeys a Leibniz rule against scalars, so the orbit of a rescaled vector is a
triangular combination of the original orbit with diagonal `f`, and the orbit determinant of `f·u`
is `f^k` times that of `u`.

Nothing here uses the shape of the factors.
-/

namespace GaloisForLFunctions.HTGeometry

namespace PairFam


open GaloisForLFunctions

variable (F : PairFam)

/-! ## The Leibniz rule of the shifted operator -/

/-- **The shifted operator against a scalar combination.** -/
theorem gradShift_sum_smul (m : ℕ) (s : Finset ℕ) (c : ℕ → CascadeField)
    (w : ℕ → ℕ → CascadeField) (k : ℕ) :
    F.gradShift m (fun l => ∑ j ∈ s, c j * w j l) k
      = ∑ j ∈ s, (F.law (c j) * w j k + c j * F.gradShift m (w j) k) := by
  classical
  have h1 : F.law (∑ j ∈ s, c j * w j k)
      = ∑ j ∈ s, (F.law (c j) * w j k + c j * F.law (w j k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  have h2 : ∑ l ∈ Finset.range (m + 1), F.response k l * (∑ j ∈ s, c j * w j l)
      = ∑ j ∈ s, c j * ∑ l ∈ Finset.range (m + 1), F.response k l * w j l := by
    calc ∑ l ∈ Finset.range (m + 1), F.response k l * (∑ j ∈ s, c j * w j l)
        = ∑ l ∈ Finset.range (m + 1), ∑ j ∈ s, F.response k l * (c j * w j l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j ∈ s, ∑ l ∈ Finset.range (m + 1), F.response k l * (c j * w j l) :=
          Finset.sum_comm
      _ = ∑ j ∈ s, c j * ∑ l ∈ Finset.range (m + 1), F.response k l * w j l := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [PairFam.gradShift, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PairFam.gradShift]
  ring

/-! ## The triangular coefficients -/

/-- The coefficients expressing the orbit of `f·u` in the orbit of `u`. -/
noncomputable def shiftCoeff (F : PairFam) (f : CascadeField) : ℕ → ℕ → CascadeField
  | 0, j => if j = 0 then f else 0
  | (i + 1), 0 => F.law (F.shiftCoeff f i 0)
  | (i + 1), (j + 1) => F.law (F.shiftCoeff f i (j + 1)) + F.shiftCoeff f i j

theorem shiftCoeff_eq_zero_of_lt (f : CascadeField) :
    ∀ {i j : ℕ}, i < j → F.shiftCoeff f i j = 0 := by
  intro i
  induction i with
  | zero =>
      intro j hj
      rw [shiftCoeff, if_neg (by omega)]
  | succ i ih =>
      intro j hj
      match j with
      | 0 => omega
      | (j + 1) =>
          rw [shiftCoeff, ih (by omega : i < j + 1), ih (by omega : i < j), map_zero, add_zero]

theorem shiftCoeff_diag (f : CascadeField) : ∀ i : ℕ, F.shiftCoeff f i i = f := by
  intro i
  induction i with
  | zero => rw [shiftCoeff, if_pos rfl]
  | succ i ih =>
      rw [shiftCoeff, F.shiftCoeff_eq_zero_of_lt f (by omega : i < i + 1), ih, map_zero,
        zero_add]

/-! ## The orbit of a rescaled vector -/

/-- **The orbit of `f·u` is a triangular combination of the orbit of `u`.** -/
theorem iterate_gradShift_smul (m : ℕ) (f : CascadeField) (u : ℕ → CascadeField) (i : ℕ) :
    ((F.gradShift m)^[i]) (fun l => f * u l)
      = fun k => ∑ j ∈ Finset.range (i + 1),
          F.shiftCoeff f i j * (((F.gradShift m)^[j]) u k) := by
  induction i with
  | zero =>
      funext k
      simp [shiftCoeff]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      funext k
      rw [gradShift_sum_smul]
      rw [Finset.sum_range_succ' (fun j => F.shiftCoeff f (i + 1) j
        * (((F.gradShift m)^[j]) u k)) (i + 1)]
      have hzero : F.shiftCoeff f i (i + 1) = 0 :=
        F.shiftCoeff_eq_zero_of_lt f (by omega)
      have hsplit : ∀ j : ℕ, F.law (F.shiftCoeff f i j)
            * ((F.gradShift m)^[j]) u k
          + F.shiftCoeff f i j * F.gradShift m (((F.gradShift m)^[j]) u) k
          = F.law (F.shiftCoeff f i j) * ((F.gradShift m)^[j]) u k
            + F.shiftCoeff f i j * ((F.gradShift m)^[j + 1]) u k := by
        intro j
        rw [Function.iterate_succ_apply']
      simp only [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_range_succ' (fun j =>
        F.law (F.shiftCoeff f i j) * ((F.gradShift m)^[j]) u k) i]
      have hhead : F.shiftCoeff f (i + 1) 0
          = F.law (F.shiftCoeff f i 0) := rfl
      have hstep : ∀ j : ℕ, F.shiftCoeff f (i + 1) (j + 1)
          = F.law (F.shiftCoeff f i (j + 1)) + F.shiftCoeff f i j := fun j => rfl
      simp only [hhead, hstep]
      have key : ∑ x ∈ Finset.range (i + 1),
            (F.law (F.shiftCoeff f i (x + 1)) + F.shiftCoeff f i x)
              * ((F.gradShift m)^[x + 1]) u k
          = (∑ x ∈ Finset.range (i + 1),
              F.law (F.shiftCoeff f i (x + 1)) * ((F.gradShift m)^[x + 1]) u k)
            + ∑ x ∈ Finset.range (i + 1),
              F.shiftCoeff f i x * ((F.gradShift m)^[x + 1]) u k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      have key2 : ∑ x ∈ Finset.range (i + 1),
            F.law (F.shiftCoeff f i (x + 1)) * ((F.gradShift m)^[x + 1]) u k
          = ∑ x ∈ Finset.range i,
            F.law (F.shiftCoeff f i (x + 1))
              * ((F.gradShift m)^[x + 1]) u k := by
        rw [Finset.sum_range_succ, hzero, map_zero, zero_mul, add_zero]
      rw [key, key2]
      ring

/-- **The orbit matrix of a rescaled vector factors.** -/
theorem orbitMatrix_smul (m k : ℕ) (f : CascadeField) (u : ℕ → CascadeField) :
    F.orbitMatrix m k (fun l => f * u l)
      = (Matrix.of fun i j : Fin k => F.shiftCoeff f (i : ℕ) (j : ℕ))
        * F.orbitMatrix m k u := by
  classical
  funext i j
  rw [Matrix.mul_apply]
  simp only [PairFam.orbitMatrix, Matrix.of_apply]
  rw [F.iterate_gradShift_smul m f u (i : ℕ)]
  rw [Fin.sum_univ_eq_sum_range (fun j' => F.shiftCoeff f (i : ℕ) j'
    * (((F.gradShift m)^[j']) u ((j : ℕ) + 1))) k]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    have hxi : x < (i : ℕ) + 1 := Finset.mem_range.mp hx
    have hik := i.isLt
    exact Finset.mem_range.mpr (by omega)
  · intro x _ hx
    have hxi : ¬ x < (i : ℕ) + 1 := fun hc => hx (Finset.mem_range.mpr hc)
    rw [F.shiftCoeff_eq_zero_of_lt f (by omega : (i : ℕ) < x), zero_mul]

/-- **Rescaling the starting vector multiplies the orbit determinant by a power.** -/
theorem det_orbitMatrix_smul (m k : ℕ) (f : CascadeField) (u : ℕ → CascadeField) :
    (F.orbitMatrix m k (fun l => f * u l)).det
      = f ^ k * (F.orbitMatrix m k u).det := by
  classical
  rw [F.orbitMatrix_smul, Matrix.det_mul]
  congr 1
  rw [Matrix.det_of_lowerTriangular]
  · have hdiag : ∀ x : Fin k, F.shiftCoeff f (x : ℕ) (x : ℕ) = f :=
      fun x => F.shiftCoeff_diag f (x : ℕ)
    simp only [Matrix.of_apply, hdiag]
    simp
  · intro i j hij
    simp only [Matrix.of_apply]
    exact F.shiftCoeff_eq_zero_of_lt f (by exact hij)

/-- **Rescaling by a nonzero element preserves nonvanishing of the orbit determinant.** -/
theorem det_orbitMatrix_ne_zero_of_smul {m k : ℕ} {f : CascadeField} (hf : f ≠ 0)
    {u : ℕ → CascadeField} (h : (F.orbitMatrix m k u).det ≠ 0) :
    (F.orbitMatrix m k (fun l => f * u l)).det ≠ 0 := by
  rw [F.det_orbitMatrix_smul]
  exact mul_ne_zero (pow_ne_zero _ hf) h

end PairFam

end GaloisForLFunctions.HTGeometry
