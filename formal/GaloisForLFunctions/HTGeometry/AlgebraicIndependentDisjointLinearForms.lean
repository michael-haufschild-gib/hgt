import GaloisForLFunctions.HTGeometry.AlgebraicIndependentLinearForms

/-!
# Algebraic independence of disjoint linear blocks

A family of nonzero linear forms on pairwise disjoint blocks of an algebraically independent
coordinate family is algebraically independent.  The blocks may have different finite shapes.
This is the linear-algebra engine for realizing nonlinear projective law horizons by successive
ordered-derivative layers.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K A τ : Type*} [Field K] [CommRing A] [Algebra K A]
  [Fintype τ] [DecidableEq τ]
  {σ : τ → Type*} [∀ t, Fintype (σ t)] [∀ t, DecidableEq (σ t)]

/-- The rectangular matrix whose `t`-th row is supported only on the `t`-th dependent-sum
block. -/
def disjointBlockMatrix (u : ∀ t, σ t → K) : Matrix τ (Σ t, σ t) K :=
  fun t p ↦ if h : p.1 = t then u t (h ▸ p.2) else 0

omit [Fintype τ] [(t : τ) → Fintype (σ t)] [(t : τ) → DecidableEq (σ t)] in
@[simp]
theorem disjointBlockMatrix_same (u : ∀ t, σ t → K) (t : τ) (s : σ t) :
    disjointBlockMatrix u t ⟨t, s⟩ = u t s := by
  simp [disjointBlockMatrix]

omit [Fintype τ] [(t : τ) → Fintype (σ t)] [(t : τ) → DecidableEq (σ t)] in
@[simp]
theorem disjointBlockMatrix_other (u : ∀ t, σ t → K)
    (t r : τ) (s : σ r) (htr : r ≠ t) :
    disjointBlockMatrix u t ⟨r, s⟩ = 0 := by
  simp [disjointBlockMatrix, htr]

omit [(t : τ) → Fintype (σ t)] [(t : τ) → DecidableEq (σ t)] in
/-- Rows supported on disjoint blocks are linearly independent as soon as every row has a
nonzero coefficient. -/
theorem disjointBlockMatrix_linearIndependent_rows
    (u : ∀ t, σ t → K) (hu : ∀ t, ∃ s, u t s ≠ 0) :
    LinearIndependent K (disjointBlockMatrix u).row := by
  rw [Fintype.linearIndependent_iff]
  intro c hc t
  obtain ⟨s, hs⟩ := hu t
  have hcoord := congrFun hc ⟨t, s⟩
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
    Matrix.row] at hcoord
  have hsingle : c t * u t s = 0 := by
    simpa [disjointBlockMatrix, Finset.sum_eq_single t] using hcoord
  exact (mul_eq_zero.mp hsingle).resolve_right hs

/-- **Disjoint linear-block theorem.**  Nonzero linear forms on separate finite blocks of an
algebraically independent family remain algebraically independent. -/
theorem algebraicIndependent_disjointBlockLinearForms
    (u : ∀ t, σ t → K) (hu : ∀ t, ∃ s, u t s ≠ 0)
    (x : (Σ t, σ t) → A) (hx : AlgebraicIndependent K x) :
    AlgebraicIndependent K
      (fun t ↦ ∑ s, algebraMap K A (u t s) * x ⟨t, s⟩) := by
  have hforms := algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
    (disjointBlockMatrix u) (disjointBlockMatrix_linearIndependent_rows u hu) x hx
  have hpacket : matrixLinearForms (disjointBlockMatrix u) x =
      (fun t ↦ ∑ s, algebraMap K A (u t s) * x ⟨t, s⟩) := by
    funext t
    rw [matrixLinearForms, Fintype.sum_sigma, Finset.sum_eq_single t]
    · simp [disjointBlockMatrix]
    · intro r hr hrt
      simp [disjointBlockMatrix, hrt]
    · simp
  rw [← hpacket]
  exact hforms

section ArbitraryIndex

variable {τ : Type*} {σ : τ → Type*}
  [∀ t, Fintype (σ t)] [∀ t, DecidableEq (σ t)]

/-- The disjoint-block theorem has no global finiteness restriction on the block index.  Every
polynomial relation uses only finitely many blocks, where the finite theorem applies. -/
theorem algebraicIndependent_disjointBlockLinearForms_arbitrary
    (u : ∀ t, σ t → K) (hu : ∀ t, ∃ s, u t s ≠ 0)
    (x : (Σ t, σ t) → A) (hx : AlgebraicIndependent K x) :
    AlgebraicIndependent K
      (fun t ↦ ∑ s, algebraMap K A (u t s) * x ⟨t, s⟩) := by
  classical
  apply algebraicIndependent_of_finite_type
  intro s hs
  letI : Fintype s := hs.fintype
  let σs := fun t : s ↦ σ t.1
  let embed : (Σ t, σs t) → (Σ t, σ t) :=
    Sigma.map Subtype.val (fun _ z ↦ z)
  have hembed : Function.Injective embed :=
    Subtype.val_injective.sigma_map (fun _ ↦ fun _ _ h ↦ h)
  have hxs : AlgebraicIndependent K (x ∘ embed) := hx.comp embed hembed
  have hfinite := algebraicIndependent_disjointBlockLinearForms
    (σ := σs) (fun t ↦ u t.1) (fun t ↦ hu t.1) (x ∘ embed) hxs
  have hforms :
      (fun t : s ↦ ∑ z, algebraMap K A (u t.1 z) * x ⟨t.1, z⟩) =
        (fun t : s ↦ ∑ z, algebraMap K A (u t.1 z) * (x ∘ embed) ⟨t, z⟩) := by
    funext t
    apply Finset.sum_congr rfl
    intro z _
    simp only [Function.comp_apply]
    rw [show embed ⟨t, z⟩ = ⟨t.1, z⟩ by rfl]
  rw [hforms]
  exact hfinite

end ArbitraryIndex

end

end GaloisForLFunctions.HTGeometry
