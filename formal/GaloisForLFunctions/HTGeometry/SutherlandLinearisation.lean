import GaloisForLFunctions.HTGeometry.ThreeParticleLegsRing

/-!
# The Sutherland linearisation of a regular braid family

Differentiating the difference-form braid Yang--Baxter equation in the second spectral parameter
at zero produces, for a regular family `Ř` with `Ř 0 = 1` and `H = Ř′ 0`, the Sutherland identity

```text
legLeft X * legRight X′ − legLeft X′ * legRight X
  = legRight H * legLeft X * legRight X − legLeft X * legRight X * legLeft H,
```

whose left side is linear in `X′`.  At `X = 1` that linear map is `Z ↦ legRight Z − legLeft Z`,
whose kernel is exactly the scalars.  This file gives an *explicit* linear left inverse for it —
so no basis, no rank argument and no choice is needed — and packages the resulting affine
endomorphism `sutherlandOp` which is the identity at `X = 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {κ : Type*} [DecidableEq κ] {R : Type*} [CommRing R]

/-- Explicit left inverse of the identity Sutherland map, anchored at a base label `u₀`.  Entries
off the diagonal are read directly off the two off-diagonal blocks; diagonal entries are recovered
by a two-step chain through the base label. -/
def sutherlandSolve (u₀ : κ) (W : Matrix (TripleIndex κ) (TripleIndex κ) R) :
    Matrix (κ × κ) (κ × κ) R :=
  Matrix.of fun q r =>
    if q.1 = r.1 then
      (if q.2 = r.2 then
        W (u₀, u₀, q.1) (u₀, u₀, q.1) + W (u₀, q.1, q.2) (u₀, q.1, q.2)
      else W (u₀, q.1, q.2) (u₀, r.1, r.2))
    else -W (q.1, q.2, u₀) (r.1, r.2, u₀)

theorem sutherlandSolve_add (u₀ : κ) (W V : Matrix (TripleIndex κ) (TripleIndex κ) R) :
    sutherlandSolve u₀ (W + V) = sutherlandSolve u₀ W + sutherlandSolve u₀ V := by
  ext q r
  by_cases h1 : q.1 = r.1 <;> by_cases h2 : q.2 = r.2 <;>
    simp [sutherlandSolve, h1, h2]
  all_goals ring

theorem sutherlandSolve_smul (u₀ : κ) (c : R)
    (W : Matrix (TripleIndex κ) (TripleIndex κ) R) :
    sutherlandSolve u₀ (c • W) = c • sutherlandSolve u₀ W := by
  ext q r
  by_cases h1 : q.1 = r.1 <;> by_cases h2 : q.2 = r.2 <;>
    simp [sutherlandSolve, h1, h2]
  all_goals ring

/-- **The explicit left inverse.**  Applying `sutherlandSolve` to the identity Sutherland image of
`Z` returns `Z` corrected by its anchor entry — precisely the scalar kernel direction. -/
theorem sutherlandSolve_legRight_sub_legLeft (u₀ : κ)
    (Z : Matrix (κ × κ) (κ × κ) R) :
    sutherlandSolve u₀ (legRight Z - legLeft Z) =
      Z - (Z (u₀, u₀) (u₀, u₀)) • 1 := by
  ext ⟨u, v⟩ ⟨u', v'⟩
  by_cases h1 : u = u'
  · subst h1
    by_cases h2 : v = v'
    · subst h2
      simp [sutherlandSolve, Matrix.one_apply]
    · simp [sutherlandSolve, h2, Matrix.one_apply, Prod.ext_iff]
  · have hne : ((u, v) : κ × κ) ≠ (u', v') := by
      intro h
      exact h1 (congrArg Prod.fst h)
    simp [sutherlandSolve, h1, hne, Matrix.one_apply]

variable [Fintype κ]

/-- The Sutherland endomorphism at `X`, normalised so that it is the identity at `X = 1`. -/
def sutherlandOp (u₀ : κ) (X Z : Matrix (κ × κ) (κ × κ) R) :
    Matrix (κ × κ) (κ × κ) R :=
  sutherlandSolve u₀ (legLeft X * legRight Z - legLeft Z * legRight X)
    + (Z (u₀, u₀) (u₀, u₀)) • 1

theorem sutherlandOp_one (u₀ : κ) (Z : Matrix (κ × κ) (κ × κ) R) :
    sutherlandOp u₀ 1 Z = Z := by
  rw [sutherlandOp, legLeft_one, legRight_one, Matrix.one_mul, Matrix.mul_one,
    sutherlandSolve_legRight_sub_legLeft]
  abel

theorem sutherlandOp_add (u₀ : κ) (X Z W : Matrix (κ × κ) (κ × κ) R) :
    sutherlandOp u₀ X (Z + W) = sutherlandOp u₀ X Z + sutherlandOp u₀ X W := by
  rw [sutherlandOp, sutherlandOp, sutherlandOp, legLeft_add, legRight_add]
  have hexp : legLeft X * (legRight Z + legRight W) - (legLeft Z + legLeft W) * legRight X
      = (legLeft X * legRight Z - legLeft Z * legRight X)
        + (legLeft X * legRight W - legLeft W * legRight X) := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  rw [hexp, sutherlandSolve_add]
  simp only [Matrix.add_apply, add_smul]
  abel

theorem sutherlandOp_smul (u₀ : κ) (c : R) (X Z : Matrix (κ × κ) (κ × κ) R) :
    sutherlandOp u₀ X (c • Z) = c • sutherlandOp u₀ X Z := by
  rw [sutherlandOp, sutherlandOp, legLeft_smul, legRight_smul]
  have hexp : legLeft X * (c • legRight Z) - (c • legLeft Z) * legRight X
      = c • (legLeft X * legRight Z - legLeft Z * legRight X) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  rw [hexp, sutherlandSolve_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, smul_add, smul_smul]

/-- The Sutherland endomorphism as a linear map. -/
def sutherlandLin (u₀ : κ) (X : Matrix (κ × κ) (κ × κ) R) :
    Matrix (κ × κ) (κ × κ) R →ₗ[R] Matrix (κ × κ) (κ × κ) R where
  toFun := sutherlandOp u₀ X
  map_add' := sutherlandOp_add u₀ X
  map_smul' c Z := sutherlandOp_smul u₀ c X Z

@[simp]
theorem sutherlandLin_apply (u₀ : κ) (X Z : Matrix (κ × κ) (κ × κ) R) :
    sutherlandLin u₀ X Z = sutherlandOp u₀ X Z := rfl

/-- The matrix of the Sutherland endomorphism in the standard matrix-unit basis. -/
def sutherlandMatrix (u₀ : κ) (X : Matrix (κ × κ) (κ × κ) R) :
    Matrix ((κ × κ) × (κ × κ)) ((κ × κ) × (κ × κ)) R :=
  Matrix.of fun t s => sutherlandOp u₀ X (Matrix.single s.1 s.2 1) t.1 t.2

theorem sutherlandMatrix_mulVec (u₀ : κ) (X Z : Matrix (κ × κ) (κ × κ) R) :
    (sutherlandMatrix u₀ X) *ᵥ (fun s => Z s.1 s.2) =
      fun t => sutherlandOp u₀ X Z t.1 t.2 := by
  have hZ : Z = ∑ s : (κ × κ) × (κ × κ), Z s.1 s.2 • Matrix.single s.1 s.2 1 := by
    ext a b
    rw [Matrix.sum_apply, Finset.sum_eq_single ((a, b) : (κ × κ) × (κ × κ))]
    · simp
    · rintro ⟨c, d⟩ _ hcd
      have hne : ¬ (c = a ∧ d = b) := fun hc => hcd (by simp [hc.1, hc.2])
      simp [hne]
    · intro h
      simp at h
  have key : sutherlandOp u₀ X Z
      = ∑ s : (κ × κ) × (κ × κ), Z s.1 s.2 • sutherlandOp u₀ X (Matrix.single s.1 s.2 1) := by
    calc sutherlandOp u₀ X Z = sutherlandLin u₀ X Z := rfl
      _ = sutherlandLin u₀ X (∑ s : (κ × κ) × (κ × κ),
            Z s.1 s.2 • Matrix.single s.1 s.2 1) := by rw [← hZ]
      _ = ∑ s : (κ × κ) × (κ × κ),
            Z s.1 s.2 • sutherlandOp u₀ X (Matrix.single s.1 s.2 1) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun s _ => by rw [map_smul]; rfl
  funext t
  simp only [Matrix.mulVec, dotProduct, sutherlandMatrix, Matrix.of_apply, key,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

@[simp]
theorem sutherlandMatrix_one (u₀ : κ) :
    sutherlandMatrix u₀ (1 : Matrix (κ × κ) (κ × κ) R) = 1 := by
  ext t s
  rw [sutherlandMatrix, Matrix.of_apply, sutherlandOp_one]
  by_cases h : t = s
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    exact h (Prod.ext h1.symm h2.symm)

end GaloisForLFunctions.HTGeometry
