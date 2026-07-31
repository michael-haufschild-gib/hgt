import Mathlib

/-!
# Coordinate-minor certificates for linear independence

A family of vectors in a coordinate space `ι → K` over a field is linearly independent exactly when
finitely many coordinates already witness the independence through a nonvanishing square
determinant.

* `coordinateMinor v φ` — the square matrix obtained from the column family `v` by reading the
  coordinates selected by `φ`.
* `linearIndependent_of_coordinateMinor_det_ne_zero` — a nonvanishing minor forces independence.
* `exists_coordinateMinor_det_ne_zero` — a linearly independent finite family admits a
  nonvanishing minor.  The proof adds one column at a time: the determinant with the last row left
  free is a linear functional, so if it killed every coordinate row of the family, its coefficients
  would give a linear relation whose last coefficient is the previous, nonzero, minor.
* `linearIndependent_iff_forall_finset_exists_coordinateMinor_det_ne_zero` — the resulting
  characterisation for an arbitrary index type: independence is decided by the finite minors.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- The square matrix of a column family `v : N → ι → K` read along a selection `φ : N → ι` of
coordinates.  Rows are indexed by the selected coordinates, columns by the family. -/
def coordinateMinor {K ι N : Type*} (v : N → ι → K) (φ : N → ι) : Matrix N N K :=
  Matrix.of fun i j => v j (φ i)

@[simp]
theorem coordinateMinor_apply {K ι N : Type*} (v : N → ι → K) (φ : N → ι) (i j : N) :
    coordinateMinor v φ i j = v j (φ i) := rfl

section EasyDirection

variable {K ι N : Type*} [Field K] [Fintype N] [DecidableEq N]

/-- **A nonvanishing coordinate minor certifies independence.**  A linear relation among the columns
is a vector in the kernel of the minor, which is trivial once its determinant is nonzero. -/
theorem linearIndependent_of_coordinateMinor_det_ne_zero
    (v : N → ι → K) (φ : N → ι) (hdet : (coordinateMinor v φ).det ≠ 0) :
    LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmul : (coordinateMinor v φ).mulVec g = 0 := by
    funext i
    have hi := congrFun hg (φ i)
    simpa [Matrix.mulVec, dotProduct, coordinateMinor, mul_comm] using hi
  have hzero := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  intro i
  exact congrFun hzero i

end EasyDirection

section FinConstruction

variable {K ι : Type*} [Field K]

/-- **Existence of a nonvanishing coordinate minor, for families indexed by `Fin n`.**  Induction on
the number of columns: with the first `n` columns certified by a selection `φ'`, the determinant of
the bordered matrix is a linear functional of its last row.  If that functional vanished at every
coordinate row of the family, its coefficients would give a linear relation whose last coefficient
is the previous minor, which is nonzero. -/
theorem exists_coordinateMinor_det_ne_zero_fin :
    ∀ (n : ℕ) (v : Fin n → ι → K), LinearIndependent K v →
      ∃ φ : Fin n → ι, (coordinateMinor v φ).det ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro v _
      exact ⟨Fin.elim0, by simp⟩
  | succ n IH =>
      classical
      intro v hv
      have hv' : LinearIndependent K (fun i : Fin n => v i.castSucc) :=
        hv.comp Fin.castSucc (Fin.castSucc_injective n)
      obtain ⟨φ', hφ'⟩ := IH _ hv'
      -- rows of the bordered matrix coming from the certified subfamily
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
          ∀ (p : Fin n) (j : Fin (n + 1)), B p.castSucc j = v j (φ' p) :=
        ⟨Matrix.of (Fin.snoc (fun (p : Fin n) (j : Fin (n + 1)) => v j (φ' p))
          (0 : Fin (n + 1) → K)), by intro p j; simp⟩
      have hupd : ∀ r : Fin (n + 1) → K,
          Matrix.of (Fin.snoc (fun (p : Fin n) (j : Fin (n + 1)) => v j (φ' p)) r)
            = B.updateRow (Fin.last n) r := by
        intro r
        ext p j
        induction p using Fin.lastCases with
        | last => simp
        | cast q => simp [hB]
      -- the determinant as a linear functional of the free last row
      let L : (Fin (n + 1) → K) →ₗ[K] K :=
        { toFun := fun r =>
            (Matrix.of (Fin.snoc (fun (p : Fin n) (j : Fin (n + 1)) => v j (φ' p)) r)).det
          map_add' := by
            intro x y
            simp only [hupd]
            exact Matrix.det_updateRow_add _ _ _ _
          map_smul' := by
            intro c x
            simp only [hupd, RingHom.id_apply, smul_eq_mul]
            exact Matrix.det_updateRow_smul _ _ _ _ }
      have hL : ∀ r : Fin (n + 1) → K, L r =
          (Matrix.of (Fin.snoc (fun (p : Fin n) (j : Fin (n + 1)) => v j (φ' p)) r)).det :=
        fun _ => rfl
      have hLrow : ∀ i : ι, L (fun j => v j i) = (coordinateMinor v (Fin.snoc φ' i)).det := by
        intro i
        rw [hL]
        congr 1
        ext p j
        induction p using Fin.lastCases with
        | last => simp [coordinateMinor]
        | cast q => simp [coordinateMinor]
      by_cases hzero : ∀ i : ι, L (fun j => v j i) = 0
      · exfalso
        have hexp : ∀ r : Fin (n + 1) → K, L r = ∑ j, r j * L (Pi.single j 1) := by
          intro r
          have hr : r = ∑ j, r j • (Pi.single j (1 : K)) := by
            funext i
            simp [Finset.sum_apply, Pi.single_apply]
          conv_lhs => rw [hr]
          rw [map_sum]
          simp [smul_eq_mul]
        have hrel : ∑ j, L (Pi.single j 1) • v j = 0 := by
          funext i
          have hi := hzero i
          rw [hexp] at hi
          simpa [Finset.sum_apply, mul_comm] using hi
        have hlam0 := (Fintype.linearIndependent_iff.mp hv) (fun j => L (Pi.single j 1)) hrel
        -- the last coefficient of the functional is the previously certified minor
        have hlast : L (Pi.single (Fin.last n) 1)
            = (coordinateMinor (fun i : Fin n => v i.castSucc) φ').det := by
          rw [hL, Matrix.det_succ_row _ (Fin.last n)]
          have hrow : ∀ j : Fin (n + 1),
              (Matrix.of (Fin.snoc (fun (p : Fin n) (j : Fin (n + 1)) => v j (φ' p))
                  (Pi.single (Fin.last n) (1 : K) : Fin (n + 1) → K))) (Fin.last n) j
                = (Pi.single (Fin.last n) (1 : K) : Fin (n + 1) → K) j := by
            intro j; simp
          rw [Finset.sum_eq_single (Fin.last n)]
          · rw [hrow]
            simp only [Pi.single_eq_same, mul_one]
            have hsign : ((-1 : K) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
              rw [← two_mul, pow_mul]
              norm_num
            rw [hsign, one_mul, Fin.succAbove_last]
            congr 1
            ext p q
            simp [Matrix.submatrix, coordinateMinor]
          · intro j _ hj
            rw [hrow, Pi.single_eq_of_ne hj]
            ring
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [hlam0 (Fin.last n)] at hlast
        exact hφ' hlast.symm
      · push Not at hzero
        obtain ⟨i, hi⟩ := hzero
        exact ⟨Fin.snoc φ' i, by rwa [← hLrow i]⟩

end FinConstruction

section General

variable {K ι N : Type*} [Field K]

/-- **Existence of a nonvanishing coordinate minor for a finite family.** -/
theorem exists_coordinateMinor_det_ne_zero [Fintype N] [DecidableEq N]
    (v : N → ι → K) (hv : LinearIndependent K v) :
    ∃ φ : N → ι, (coordinateMinor v φ).det ≠ 0 := by
  classical
  obtain ⟨e⟩ : Nonempty (N ≃ Fin (Fintype.card N)) := ⟨Fintype.equivFin N⟩
  have hv' : LinearIndependent K (fun p : Fin (Fintype.card N) => v (e.symm p)) :=
    hv.comp e.symm e.symm.injective
  obtain ⟨φ₀, hφ₀⟩ := exists_coordinateMinor_det_ne_zero_fin _ _ hv'
  refine ⟨fun i => φ₀ (e i), ?_⟩
  have hsub : coordinateMinor v (fun i => φ₀ (e i))
      = (coordinateMinor (fun p : Fin (Fintype.card N) => v (e.symm p)) φ₀).submatrix e e := by
    ext i j
    simp [coordinateMinor, Matrix.submatrix]
  rw [hsub, Matrix.det_submatrix_equiv_self]
  exact hφ₀

/-- **Minor certificates decide linear independence.**  A family of vectors in a coordinate space
over a field is linearly independent exactly when every finite subfamily is certified by a
nonvanishing square minor built from finitely many coordinates. -/
theorem linearIndependent_iff_forall_finset_exists_coordinateMinor_det_ne_zero
    [DecidableEq N] (v : N → ι → K) :
    LinearIndependent K v ↔
      ∀ s : Finset N, ∃ φ : {x // x ∈ s} → ι,
        (coordinateMinor (fun j : {x // x ∈ s} => v (j : N)) φ).det ≠ 0 := by
  classical
  constructor
  · intro hv s
    exact exists_coordinateMinor_det_ne_zero _ (hv.comp _ Subtype.val_injective)
  · intro h
    rw [linearIndependent_iff']
    intro s g hg i hi
    obtain ⟨φ, hφ⟩ := h s
    have hsub : LinearIndependent K (fun j : {x // x ∈ s} => v (j : N)) :=
      linearIndependent_of_coordinateMinor_det_ne_zero _ φ hφ
    have hg' : ∑ j : {x // x ∈ s}, g (j : N) • v (j : N) = 0 := by
      rw [← Finset.sum_attach s fun j => g j • v j] at hg
      simpa using hg
    exact (Fintype.linearIndependent_iff.mp hsub) (fun j => g (j : N)) hg' ⟨i, hi⟩

end General

end GaloisForLFunctions.HTGeometry
