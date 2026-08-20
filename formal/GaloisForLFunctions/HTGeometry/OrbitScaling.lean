import GaloisForLFunctions.HTGeometry.ColumnLimitRecursion

/-!
# Rescaling the starting vector of an orbit

The shifted operator obeys a Leibniz rule against scalars, `S(f·u) = (δf)·u + f·(S u)`, so the
orbit of a rescaled vector is a *unitriangular-with-diagonal-`f`* combination of the original orbit:

`Sⁱ(f·u) = ∑_{j ≤ i} c_{i,j}·Sʲ(u)`,  `c_{i,i} = f`,  `c_{i,j} = 0` for `j > i`.

Hence the orbit determinant of `f·u` is `f^k` times that of `u`.

This is what makes the peel's induction uniform.  Each peel produces a starting vector whose newest
entry has degree `deg Q − 1` rather than `−1`; dividing by `Q(X)` restores the original degree
profile, and by the scaling law that division only multiplies the determinant by a nonzero factor.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The orbit matrix of a starting vector under the shifted operator. -/
noncomputable def jetOrbitMatrix (Q v : ℕ → Polynomial ℂ) (m k : ℕ) (u : ℕ → CascadeField) :
    Matrix (Fin k) (Fin k) CascadeField :=
  Matrix.of fun i j => ((gradShift Q v m)^[(i : ℕ)]) u ((j : ℕ) + 1)

/-! ## The Leibniz rule of the shifted operator -/

/-- **The shifted operator against a scalar combination.** -/
theorem gradShift_sum_smul (m : ℕ) (s : Finset ℕ) (c : ℕ → CascadeField)
    (w : ℕ → ℕ → CascadeField) (k : ℕ) :
    gradShift Q v m (fun l => ∑ j ∈ s, c j * w j l) k
      = ∑ j ∈ s, (prodDerivation Q v (c j) * w j k + c j * gradShift Q v m (w j) k) := by
  classical
  have h1 : prodDerivation Q v (∑ j ∈ s, c j * w j k)
      = ∑ j ∈ s, (prodDerivation Q v (c j) * w j k + c j * prodDerivation Q v (w j k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  have h2 : ∑ l ∈ Finset.range (m + 1), jetResponse Q v k l * (∑ j ∈ s, c j * w j l)
      = ∑ j ∈ s, c j * ∑ l ∈ Finset.range (m + 1), jetResponse Q v k l * w j l := by
    calc ∑ l ∈ Finset.range (m + 1), jetResponse Q v k l * (∑ j ∈ s, c j * w j l)
        = ∑ l ∈ Finset.range (m + 1), ∑ j ∈ s, jetResponse Q v k l * (c j * w j l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j ∈ s, ∑ l ∈ Finset.range (m + 1), jetResponse Q v k l * (c j * w j l) :=
          Finset.sum_comm
      _ = ∑ j ∈ s, c j * ∑ l ∈ Finset.range (m + 1), jetResponse Q v k l * w j l := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [gradShift, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gradShift]
  ring

/-! ## The triangular coefficients -/

/-- The coefficients expressing the orbit of `f·u` in the orbit of `u`. -/
noncomputable def orbitScalingShiftCoeff (Q v : ℕ → Polynomial ℂ) (f : CascadeField) :
    ℕ → ℕ → CascadeField
  | 0, j => if j = 0 then f else 0
  | (i + 1), 0 => prodDerivation Q v (orbitScalingShiftCoeff Q v f i 0)
  | (i + 1), (j + 1) => prodDerivation Q v (orbitScalingShiftCoeff Q v f i (j + 1)) + orbitScalingShiftCoeff Q v f i j

theorem shiftCoeff_eq_zero_of_lt (f : CascadeField) :
    ∀ {i j : ℕ}, i < j → orbitScalingShiftCoeff Q v f i j = 0 := by
  intro i
  induction i with
  | zero =>
      intro j hj
      rw [orbitScalingShiftCoeff, if_neg (by omega)]
  | succ i ih =>
      intro j hj
      match j with
      | 0 => omega
      | (j + 1) =>
          rw [orbitScalingShiftCoeff, ih (by omega : i < j + 1), ih (by omega : i < j), map_zero, add_zero]

theorem shiftCoeff_diag (f : CascadeField) : ∀ i : ℕ, orbitScalingShiftCoeff Q v f i i = f := by
  intro i
  induction i with
  | zero => rw [orbitScalingShiftCoeff, if_pos rfl]
  | succ i ih =>
      rw [orbitScalingShiftCoeff, shiftCoeff_eq_zero_of_lt Q v f (by omega : i < i + 1), ih, map_zero, zero_add]

/-! ## The orbit of a rescaled vector -/

/-- **The orbit of `f·u` is a triangular combination of the orbit of `u`.** -/
theorem iterate_gradShift_smul (m : ℕ) (f : CascadeField) (u : ℕ → CascadeField) (i : ℕ) :
    ((gradShift Q v m)^[i]) (fun l => f * u l)
      = fun k => ∑ j ∈ Finset.range (i + 1),
          orbitScalingShiftCoeff Q v f i j * (((gradShift Q v m)^[j]) u k) := by
  induction i with
  | zero =>
      funext k
      simp [orbitScalingShiftCoeff]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      funext k
      rw [gradShift_sum_smul]
      rw [Finset.sum_range_succ' (fun j => orbitScalingShiftCoeff Q v f (i + 1) j
        * (((gradShift Q v m)^[j]) u k)) (i + 1)]
      have hzero : orbitScalingShiftCoeff Q v f i (i + 1) = 0 :=
        shiftCoeff_eq_zero_of_lt Q v f (by omega)
      have hsplit : ∀ j : ℕ, prodDerivation Q v (orbitScalingShiftCoeff Q v f i j)
            * ((gradShift Q v m)^[j]) u k
          + orbitScalingShiftCoeff Q v f i j * gradShift Q v m (((gradShift Q v m)^[j]) u) k
          = prodDerivation Q v (orbitScalingShiftCoeff Q v f i j) * ((gradShift Q v m)^[j]) u k
            + orbitScalingShiftCoeff Q v f i j * ((gradShift Q v m)^[j + 1]) u k := by
        intro j
        rw [Function.iterate_succ_apply']
      simp only [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_range_succ' (fun j =>
        prodDerivation Q v (orbitScalingShiftCoeff Q v f i j) * ((gradShift Q v m)^[j]) u k) i]
      have hhead : orbitScalingShiftCoeff Q v f (i + 1) 0
          = prodDerivation Q v (orbitScalingShiftCoeff Q v f i 0) := rfl
      have hstep : ∀ j : ℕ, orbitScalingShiftCoeff Q v f (i + 1) (j + 1)
          = prodDerivation Q v (orbitScalingShiftCoeff Q v f i (j + 1)) + orbitScalingShiftCoeff Q v f i j := fun j => rfl
      simp only [hhead, hstep]
      have key : ∑ x ∈ Finset.range (i + 1),
            (prodDerivation Q v (orbitScalingShiftCoeff Q v f i (x + 1)) + orbitScalingShiftCoeff Q v f i x)
              * ((gradShift Q v m)^[x + 1]) u k
          = (∑ x ∈ Finset.range (i + 1),
              prodDerivation Q v (orbitScalingShiftCoeff Q v f i (x + 1)) * ((gradShift Q v m)^[x + 1]) u k)
            + ∑ x ∈ Finset.range (i + 1),
              orbitScalingShiftCoeff Q v f i x * ((gradShift Q v m)^[x + 1]) u k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      have key2 : ∑ x ∈ Finset.range (i + 1),
            prodDerivation Q v (orbitScalingShiftCoeff Q v f i (x + 1)) * ((gradShift Q v m)^[x + 1]) u k
          = ∑ x ∈ Finset.range i,
            prodDerivation Q v (orbitScalingShiftCoeff Q v f i (x + 1))
              * ((gradShift Q v m)^[x + 1]) u k := by
        rw [Finset.sum_range_succ, hzero, map_zero, zero_mul, add_zero]
      rw [key, key2]
      ring

/-- **The orbit matrix of a rescaled vector factors.** -/
theorem jetOrbitMatrix_smul (m k : ℕ) (f : CascadeField) (u : ℕ → CascadeField) :
    jetOrbitMatrix Q v m k (fun l => f * u l)
      = (Matrix.of fun i j : Fin k => orbitScalingShiftCoeff Q v f (i : ℕ) (j : ℕ))
        * jetOrbitMatrix Q v m k u := by
  classical
  funext i j
  rw [Matrix.mul_apply]
  simp only [jetOrbitMatrix, Matrix.of_apply]
  rw [iterate_gradShift_smul Q v m f u (i : ℕ)]
  rw [Fin.sum_univ_eq_sum_range (fun j' => orbitScalingShiftCoeff Q v f (i : ℕ) j'
    * (((gradShift Q v m)^[j']) u ((j : ℕ) + 1))) k]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    have hxi : x < (i : ℕ) + 1 := Finset.mem_range.mp hx
    have hik := i.isLt
    exact Finset.mem_range.mpr (by omega)
  · intro x _ hx
    have hxi : ¬ x < (i : ℕ) + 1 := fun hc => hx (Finset.mem_range.mpr hc)
    rw [shiftCoeff_eq_zero_of_lt Q v f (by omega : (i : ℕ) < x), zero_mul]

/-- **Rescaling the starting vector multiplies the orbit determinant by a power.** -/
theorem det_jetOrbitMatrix_smul (m k : ℕ) (f : CascadeField) (u : ℕ → CascadeField) :
    (jetOrbitMatrix Q v m k (fun l => f * u l)).det
      = f ^ k * (jetOrbitMatrix Q v m k u).det := by
  classical
  rw [jetOrbitMatrix_smul, Matrix.det_mul]
  congr 1
  rw [Matrix.det_of_lowerTriangular]
  · have hdiag : ∀ x : Fin k, orbitScalingShiftCoeff Q v f (x : ℕ) (x : ℕ) = f :=
      fun x => shiftCoeff_diag Q v f (x : ℕ)
    simp only [Matrix.of_apply, hdiag]
    simp
  · intro i j hij
    simp only [Matrix.of_apply]
    exact shiftCoeff_eq_zero_of_lt Q v f (by exact hij)

/-- **Rescaling by a nonzero element preserves nonvanishing of the orbit determinant.** -/
theorem det_jetOrbitMatrix_ne_zero_of_smul {m k : ℕ} {f : CascadeField} (hf : f ≠ 0)
    {u : ℕ → CascadeField} (h : (jetOrbitMatrix Q v m k u).det ≠ 0) :
    (jetOrbitMatrix Q v m k (fun l => f * u l)).det ≠ 0 := by
  rw [det_jetOrbitMatrix_smul]
  exact mul_ne_zero (pow_ne_zero _ hf) h

end GaloisForLFunctions.HTGeometry
