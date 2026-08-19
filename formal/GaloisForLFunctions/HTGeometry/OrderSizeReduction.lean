import GaloisForLFunctions.HTGeometry.OrderShear

/-!
# Size reduction over an order

Sweeping the superdiagonals outwards, each one can be brought inside a fixed bound at **every**
embedding simultaneously by a single shear over the order: the shear coefficient is chosen by
rounding the vector of the entries at that position, and a shear at offset `k+1` does not disturb the
superdiagonals already reduced.

* `superShear` : the shear supported on one superdiagonal.
* `SizeReducedR` : the superdiagonals of offset at most `k` are reduced at every embedding.
* `exists_orderSizeReduction` : **every family of unipotent factors is size reduced by a single
  matrix over the order.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

/-- The shear supported on the superdiagonal of offset `k+1`. -/
def superShear {S : Type*} [Semiring S] (k : ℕ) (e : Fin nb → S) : Matrix (Fin nb) (Fin nb) S :=
  (1 : Matrix (Fin nb) (Fin nb) S)
    + Matrix.of fun i j : Fin nb => if (j : ℕ) = (i : ℕ) + (k + 1) then e i else 0

theorem superShear_apply {S : Type*} [Semiring S] (k : ℕ) (e : Fin nb → S) (i j : Fin nb) :
    superShear k e i j
      = (if i = j then (1 : S) else 0) + (if (j : ℕ) = (i : ℕ) + (k + 1) then e i else 0) := by
  classical
  rw [superShear, Matrix.add_apply, Matrix.one_apply]
  rfl

theorem superShear_upper {S : Type*} [Semiring S] (k : ℕ) (e : Fin nb → S) (i j : Fin nb)
    (hji : j < i) : superShear k e i j = 0 := by
  rw [superShear_apply]
  have h1 : ¬ (i = j) := fun h => absurd (h ▸ hji) (lt_irrefl _)
  have h2 : ¬ ((j : ℕ) = (i : ℕ) + (k + 1)) := by
    have := Fin.lt_def.1 hji
    omega
  rw [if_neg h1, if_neg h2, add_zero]

theorem superShear_diag {S : Type*} [Semiring S] (k : ℕ) (e : Fin nb → S) (i : Fin nb) :
    superShear k e i i = 1 := by
  rw [superShear_apply, if_pos rfl, if_neg (by omega), add_zero]

theorem isUnipotentUpper_superShear (k : ℕ) (e : Fin nb → ℝ) :
    IsUnipotentUpper (superShear k e) :=
  ⟨superShear_upper k e, superShear_diag k e⟩

theorem det_superShear (k : ℕ) (e : Fin nb → R) : (superShear k e).det = 1 := by
  have hbt : (superShear k e).BlockTriangular id := fun i j hij => superShear_upper k e i j hij
  rw [Matrix.det_of_upperTriangular hbt]
  simp [superShear_diag]

theorem placeMatrix_mul (T : RealOrderData R d) (v : Fin d) (M N : Matrix (Fin nb) (Fin nb) R) :
    placeMatrix T v (M * N) = placeMatrix T v M * placeMatrix T v N :=
  map_mul ((T.emb v).mapMatrix) M N

theorem placeMatrix_one (T : RealOrderData R d) (v : Fin d) :
    placeMatrix T v (1 : Matrix (Fin nb) (Fin nb) R) = 1 :=
  map_one ((T.emb v).mapMatrix)

theorem placeMatrix_superShear (T : RealOrderData R d) (v : Fin d) (k : ℕ) (e : Fin nb → R) :
    placeMatrix T v (superShear k e) = superShear k (fun i => T.emb v (e i)) := by
  classical
  ext i j
  show T.emb v (superShear k e i j) = _
  rw [superShear_apply, superShear_apply, map_add]
  congr 1
  · by_cases hij : i = j <;> simp [hij]
  · by_cases h : (j : ℕ) = (i : ℕ) + (k + 1) <;> simp [h]

/-- The superdiagonals of offset at most `k` are reduced at every embedding. -/
def SizeReducedR (C : ℝ) (k : ℕ) (Uv : Fin d → Matrix (Fin nb) (Fin nb) ℝ) : Prop :=
  ∀ v : Fin d, ∀ i j : Fin nb, i < j → (j : ℕ) ≤ (i : ℕ) + k → |Uv v i j| ≤ C

theorem sizeReducedR_zero (C : ℝ) (Uv : Fin d → Matrix (Fin nb) (Fin nb) ℝ) :
    SizeReducedR C 0 Uv := by
  intro v i j hij hle
  exact absurd hij (by simp only [Nat.add_zero] at hle; exact not_lt.2 hle)

/-- The effect of a superdiagonal shear on a unipotent upper triangular matrix. -/
theorem mul_superShear_apply {V : Matrix (Fin nb) (Fin nb) ℝ} (hV : IsUnipotentUpper V)
    (k : ℕ) (e : Fin nb → ℝ) :
    (∀ i j : Fin nb, i < j → (j : ℕ) ≤ (i : ℕ) + k → (V * superShear k e) i j = V i j)
      ∧ (∀ i j : Fin nb, (j : ℕ) = (i : ℕ) + (k + 1) →
          (V * superShear k e) i j = V i j + e i) := by
  classical
  set E : Matrix (Fin nb) (Fin nb) ℝ :=
    Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + (k + 1) then e i else 0 with hE
  have hEzero : ∀ i j : Fin nb, (j : ℕ) ≠ (i : ℕ) + (k + 1) → E i j = 0 := by
    intro i j hne
    rw [hE]
    simp [hne]
  have hEval : ∀ i j : Fin nb, (j : ℕ) = (i : ℕ) + (k + 1) → E i j = e i := by
    intro i j hij
    rw [hE]
    simp [hij]
  have hprod : ∀ i j : Fin nb, (V * superShear k e) i j = V i j + (V * E) i j := by
    intro i j
    rw [superShear, ← hE, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  constructor
  · intro i j hij hle
    have hlow : (V * E) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hm : (j : ℕ) = (m : ℕ) + (k + 1)
      · have hmi : m < i := Fin.lt_def.2 (by have := Fin.lt_def.1 hij; omega)
        rw [hV.1 i m hmi, zero_mul]
      · rw [hEzero m j hm, mul_zero]
    rw [hprod, hlow, add_zero]
  · intro i j hij
    have hnew : (V * E) i j = e i := by
      rw [Matrix.mul_apply]
      refine (Finset.sum_eq_single i (fun m _ hm => ?_)
        (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
      · by_cases hmj : (j : ℕ) = (m : ℕ) + (k + 1)
        · exact absurd (Fin.ext (by omega) : m = i) hm
        · rw [hEzero m j hmj, mul_zero]
      · rw [hEval i j hij, hV.2 i, one_mul]
    rw [hprod, hnew]

/-- **One sweep over an order**: a single shear reduces one superdiagonal at every embedding and
leaves the smaller offsets alone. -/
theorem exists_orderSweep (T : RealOrderData R d) {C : ℝ}
    (hC : ∀ x : Fin d → ℝ, ∃ α : R, ∀ v, |x v - T.emb v α| ≤ C)
    {Uv : Fin d → Matrix (Fin nb) (Fin nb) ℝ} (hUv : ∀ v, IsUnipotentUpper (Uv v))
    (k : ℕ) (hk : SizeReducedR C k Uv) :
    ∃ e : Fin nb → R,
      SizeReducedR C (k + 1) (fun v => Uv v * superShear k (fun i => T.emb v (e i))) := by
  classical
  set e : Fin nb → R := fun i =>
    if h : (i : ℕ) + (k + 1) < nb then
      Classical.choose (hC (fun v => -(Uv v) i ⟨(i : ℕ) + (k + 1), h⟩))
    else 0 with he
  refine ⟨e, ?_⟩
  intro v i j hij hle
  obtain ⟨hlow, hnew⟩ := mul_superShear_apply (hUv v) k (fun i => T.emb v (e i))
  rcases lt_or_eq_of_le hle with hlt | heq
  · show |(Uv v * superShear k (fun i => T.emb v (e i))) i j| ≤ C
    rw [hlow i j hij (by omega)]
    exact hk v i j hij (by omega)
  · show |(Uv v * superShear k (fun i => T.emb v (e i))) i j| ≤ C
    rw [hnew i j heq]
    have hlt' : (i : ℕ) + (k + 1) < nb := by
      have := j.isLt
      omega
    have hjeq : j = (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin nb) := Fin.ext (by omega)
    have hee : e i = Classical.choose
        (hC (fun w => -(Uv w) i ⟨(i : ℕ) + (k + 1), hlt'⟩)) := by
      rw [he]
      simp only [dif_pos hlt']
    have hespec := Classical.choose_spec
      (hC (fun w => -(Uv w) i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin nb))) v
    rw [hjeq, hee]
    have hEq : (Uv v) (i : Fin nb) (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin nb)
        + T.emb v (Classical.choose (hC (fun w => -(Uv w) i
            (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin nb))))
        = -((-(Uv v) i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin nb))
            - T.emb v (Classical.choose (hC (fun w => -(Uv w) i
              (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin nb))))) := by ring
    rw [hEq, abs_neg]
    exact hespec

/-- **Size reduction over an order.**  A single matrix over the order brings every superdiagonal of
every embedded unipotent factor inside a fixed bound. -/
theorem exists_orderSizeReduction (T : RealOrderData R d) {C : ℝ}
    (hC : ∀ x : Fin d → ℝ, ∃ α : R, ∀ v, |x v - T.emb v α| ≤ C)
    {Uv : Fin d → Matrix (Fin nb) (Fin nb) ℝ} (hUv : ∀ v, IsUnipotentUpper (Uv v)) :
    ∃ N : Matrix (Fin nb) (Fin nb) R, N.det = 1 ∧
      (∀ v, IsUnipotentUpper (placeMatrix T v N)) ∧
      ∀ (v : Fin d) (i j : Fin nb), i < j → |(Uv v * placeMatrix T v N) i j| ≤ C := by
  classical
  have hstep : ∀ k : ℕ, ∃ N : Matrix (Fin nb) (Fin nb) R, N.det = 1 ∧
      (∀ v, IsUnipotentUpper (placeMatrix T v N)) ∧
      SizeReducedR C k (fun v => Uv v * placeMatrix T v N) := by
    intro k
    induction k with
    | zero =>
        refine ⟨1, Matrix.det_one, fun v => ?_, ?_⟩
        · rw [placeMatrix_one]
          exact ⟨fun i j hji => Matrix.one_apply_ne (fun h => absurd (h ▸ hji) (lt_irrefl _)),
            fun i => Matrix.one_apply_eq i⟩
        · intro v i j hij hle
          exact absurd hij (by simp only [Nat.add_zero] at hle; exact not_lt.2 hle)
    | succ k ih =>
        obtain ⟨N, hdet, hunip, hred⟩ := ih
        obtain ⟨e, hsweep⟩ := exists_orderSweep T hC
          (fun v => (hUv v).mul (hunip v)) k hred
        refine ⟨N * superShear k e, ?_, fun v => ?_, ?_⟩
        · rw [Matrix.det_mul, hdet, det_superShear, one_mul]
        · rw [placeMatrix_mul, placeMatrix_superShear]
          exact (hunip v).mul (isUnipotentUpper_superShear k _)
        · intro v i j hij hle
          have h2 := hsweep v i j hij hle
          show |(Uv v * placeMatrix T v (N * superShear k e)) i j| ≤ C
          rw [placeMatrix_mul, placeMatrix_superShear, ← Matrix.mul_assoc]
          exact h2
  obtain ⟨N, hdet, hunip, hred⟩ := hstep nb
  refine ⟨N, hdet, hunip, fun v i j hij => hred v i j hij ?_⟩
  have := j.isLt
  omega

end GaloisForLFunctions.HTGeometry
