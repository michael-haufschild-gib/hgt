import GaloisForLFunctions.HTGeometry.PairBorderRow

/-!
# Rescaling the starting vector of an orbit of the two-coordinate law

The shifted operator obeys a Leibniz rule against scalars, `S(f·u) = (δf)·u + f·(S u)`, so the
orbit of a rescaled vector is a triangular combination of the original orbit with diagonal `f`:

`Sⁱ(f·u) = ∑_(j ≤ i) c_(i,j)·Sʲ(u)`,  `c_(i,i) = f`,  `c_(i,j) = 0` for `j > i`.

Hence the orbit determinant of `f·u` is `f^k` times that of `u`.

Nothing here uses the shape of the law beyond its being a derivation and the response sum being
finite, so the argument is the same one the univariate law runs.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (p : ℕ → MvPolynomial (Fin 2) ℂ)

/-- The orbit matrix of a starting vector under the shifted operator. -/
noncomputable def pairOrbitMatrix (p : ℕ → MvPolynomial (Fin 2) ℂ) (m k : ℕ)
    (u : ℕ → CascadeField) : Matrix (Fin k) (Fin k) CascadeField :=
  Matrix.of fun i j => ((pairGradShift p m)^[(i : ℕ)]) u ((j : ℕ) + 1)

/-! ## The Leibniz rule of the shifted operator -/

/-- **The shifted operator against a scalar combination.** -/
theorem pairGradShift_sum_smul (m : ℕ) (s : Finset ℕ) (c : ℕ → CascadeField)
    (w : ℕ → ℕ → CascadeField) (k : ℕ) :
    pairGradShift p m (fun l => ∑ j ∈ s, c j * w j l) k
      = ∑ j ∈ s, (pairDerivation p (c j) * w j k + c j * pairGradShift p m (w j) k) := by
  classical
  have h1 : pairDerivation p (∑ j ∈ s, c j * w j k)
      = ∑ j ∈ s, (pairDerivation p (c j) * w j k + c j * pairDerivation p (w j k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  have h2 : ∑ l ∈ Finset.range (m + 1), pairResponse p k l * (∑ j ∈ s, c j * w j l)
      = ∑ j ∈ s, c j * ∑ l ∈ Finset.range (m + 1), pairResponse p k l * w j l := by
    calc ∑ l ∈ Finset.range (m + 1), pairResponse p k l * (∑ j ∈ s, c j * w j l)
        = ∑ l ∈ Finset.range (m + 1), ∑ j ∈ s, pairResponse p k l * (c j * w j l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j ∈ s, ∑ l ∈ Finset.range (m + 1), pairResponse p k l * (c j * w j l) :=
          Finset.sum_comm
      _ = ∑ j ∈ s, c j * ∑ l ∈ Finset.range (m + 1), pairResponse p k l * w j l := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [pairGradShift, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairGradShift]
  ring

/-! ## The triangular coefficients -/

/-- The coefficients expressing the orbit of `f·u` in the orbit of `u`. -/
noncomputable def pairShiftCoeff (p : ℕ → MvPolynomial (Fin 2) ℂ) (f : CascadeField) :
    ℕ → ℕ → CascadeField
  | 0, j => if j = 0 then f else 0
  | (i + 1), 0 => pairDerivation p (pairShiftCoeff p f i 0)
  | (i + 1), (j + 1) => pairDerivation p (pairShiftCoeff p f i (j + 1)) + pairShiftCoeff p f i j

theorem pairShiftCoeff_eq_zero_of_lt (f : CascadeField) :
    ∀ {i j : ℕ}, i < j → pairShiftCoeff p f i j = 0 := by
  intro i
  induction i with
  | zero =>
      intro j hj
      rw [pairShiftCoeff, if_neg (by omega)]
  | succ i ih =>
      intro j hj
      match j with
      | 0 => omega
      | (j + 1) =>
          rw [pairShiftCoeff, ih (by omega : i < j + 1), ih (by omega : i < j), map_zero, add_zero]

theorem pairShiftCoeff_diag (f : CascadeField) : ∀ i : ℕ, pairShiftCoeff p f i i = f := by
  intro i
  induction i with
  | zero => rw [pairShiftCoeff, if_pos rfl]
  | succ i ih =>
      rw [pairShiftCoeff, pairShiftCoeff_eq_zero_of_lt p f (by omega : i < i + 1), ih, map_zero,
        zero_add]

/-! ## The orbit of a rescaled vector -/

/-- **The orbit of `f·u` is a triangular combination of the orbit of `u`.** -/
theorem iterate_pairGradShift_smul (m : ℕ) (f : CascadeField) (u : ℕ → CascadeField) (i : ℕ) :
    ((pairGradShift p m)^[i]) (fun l => f * u l)
      = fun k => ∑ j ∈ Finset.range (i + 1),
          pairShiftCoeff p f i j * (((pairGradShift p m)^[j]) u k) := by
  induction i with
  | zero =>
      funext k
      simp [pairShiftCoeff]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      funext k
      rw [pairGradShift_sum_smul]
      rw [Finset.sum_range_succ' (fun j => pairShiftCoeff p f (i + 1) j
        * (((pairGradShift p m)^[j]) u k)) (i + 1)]
      have hzero : pairShiftCoeff p f i (i + 1) = 0 :=
        pairShiftCoeff_eq_zero_of_lt p f (by omega)
      have hsplit : ∀ j : ℕ, pairDerivation p (pairShiftCoeff p f i j)
            * ((pairGradShift p m)^[j]) u k
          + pairShiftCoeff p f i j * pairGradShift p m (((pairGradShift p m)^[j]) u) k
          = pairDerivation p (pairShiftCoeff p f i j) * ((pairGradShift p m)^[j]) u k
            + pairShiftCoeff p f i j * ((pairGradShift p m)^[j + 1]) u k := by
        intro j
        rw [Function.iterate_succ_apply']
      simp only [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_range_succ' (fun j =>
        pairDerivation p (pairShiftCoeff p f i j) * ((pairGradShift p m)^[j]) u k) i]
      have hhead : pairShiftCoeff p f (i + 1) 0
          = pairDerivation p (pairShiftCoeff p f i 0) := rfl
      have hstep : ∀ j : ℕ, pairShiftCoeff p f (i + 1) (j + 1)
          = pairDerivation p (pairShiftCoeff p f i (j + 1)) + pairShiftCoeff p f i j := fun j => rfl
      simp only [hhead, hstep]
      have key : ∑ x ∈ Finset.range (i + 1),
            (pairDerivation p (pairShiftCoeff p f i (x + 1)) + pairShiftCoeff p f i x)
              * ((pairGradShift p m)^[x + 1]) u k
          = (∑ x ∈ Finset.range (i + 1),
              pairDerivation p (pairShiftCoeff p f i (x + 1)) * ((pairGradShift p m)^[x + 1]) u k)
            + ∑ x ∈ Finset.range (i + 1),
              pairShiftCoeff p f i x * ((pairGradShift p m)^[x + 1]) u k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      have key2 : ∑ x ∈ Finset.range (i + 1),
            pairDerivation p (pairShiftCoeff p f i (x + 1)) * ((pairGradShift p m)^[x + 1]) u k
          = ∑ x ∈ Finset.range i,
            pairDerivation p (pairShiftCoeff p f i (x + 1))
              * ((pairGradShift p m)^[x + 1]) u k := by
        rw [Finset.sum_range_succ, hzero, map_zero, zero_mul, add_zero]
      rw [key, key2]
      ring

/-- **The orbit matrix of a rescaled vector factors.** -/
theorem pairOrbitMatrix_smul (m k : ℕ) (f : CascadeField) (u : ℕ → CascadeField) :
    pairOrbitMatrix p m k (fun l => f * u l)
      = (Matrix.of fun i j : Fin k => pairShiftCoeff p f (i : ℕ) (j : ℕ))
        * pairOrbitMatrix p m k u := by
  classical
  funext i j
  rw [Matrix.mul_apply]
  simp only [pairOrbitMatrix, Matrix.of_apply]
  rw [iterate_pairGradShift_smul p m f u (i : ℕ)]
  rw [Fin.sum_univ_eq_sum_range (fun j' => pairShiftCoeff p f (i : ℕ) j'
    * (((pairGradShift p m)^[j']) u ((j : ℕ) + 1))) k]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    have hxi : x < (i : ℕ) + 1 := Finset.mem_range.mp hx
    have hik := i.isLt
    exact Finset.mem_range.mpr (by omega)
  · intro x _ hx
    have hxi : ¬ x < (i : ℕ) + 1 := fun hc => hx (Finset.mem_range.mpr hc)
    rw [pairShiftCoeff_eq_zero_of_lt p f (by omega : (i : ℕ) < x), zero_mul]

/-- **Rescaling the starting vector multiplies the orbit determinant by a power.** -/
theorem det_pairOrbitMatrix_smul (m k : ℕ) (f : CascadeField) (u : ℕ → CascadeField) :
    (pairOrbitMatrix p m k (fun l => f * u l)).det
      = f ^ k * (pairOrbitMatrix p m k u).det := by
  classical
  rw [pairOrbitMatrix_smul, Matrix.det_mul]
  congr 1
  rw [Matrix.det_of_lowerTriangular]
  · have hdiag : ∀ x : Fin k, pairShiftCoeff p f (x : ℕ) (x : ℕ) = f :=
      fun x => pairShiftCoeff_diag p f (x : ℕ)
    simp only [Matrix.of_apply, hdiag]
    simp
  · intro i j hij
    simp only [Matrix.of_apply]
    exact pairShiftCoeff_eq_zero_of_lt p f (by exact hij)

/-- **Rescaling by a nonzero element preserves nonvanishing of the orbit determinant.** -/
theorem det_pairOrbitMatrix_ne_zero_of_smul {m k : ℕ} {f : CascadeField} (hf : f ≠ 0)
    {u : ℕ → CascadeField} (h : (pairOrbitMatrix p m k u).det ≠ 0) :
    (pairOrbitMatrix p m k (fun l => f * u l)).det ≠ 0 := by
  rw [det_pairOrbitMatrix_smul]
  exact mul_ne_zero (pow_ne_zero _ hf) h

end GaloisForLFunctions.HTGeometry
