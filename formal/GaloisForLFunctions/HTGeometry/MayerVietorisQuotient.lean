import Mathlib

/-!
# The Mayer–Vietoris sequence of two ideals

For ideals `I, J` of a commutative ring there is a short exact sequence

```text
0 → R ⧸ (I ⊓ J) → (R ⧸ I) × (R ⧸ J) → R ⧸ (I ⊔ J) → 0
```

with the diagonal on the left and the difference on the right.

```text
mvPair, mvDiff            the two maps
mvPair_injective          exactness on the left
mvDiff_surjective         exactness on the right
mv_exact                  ** range (mvPair) = ker (mvDiff) **
```

Exactness in the middle is the only step with content: if `α - β ∈ I ⊔ J`, write `α - β = i + j`
with `i ∈ I`, `j ∈ J`; then `α - i = β + j` is a common lift.

Applied to the deletion and star of a vertex — where
`I_Δ = I_{del} ⊓ I_{st}` and `I_{lk} = I_{del} ⊔ I_{st}` — this is the sequence
`0 → K[Δ] → K[del(v)] ⊕ K[st(v)] → K[lk(v)] → 0` on which the depth argument for the
Cohen–Macaulay induction runs.
-/

namespace GaloisForLFunctions.HTGeometry

universe u
variable {R : Type u} [CommRing R]

/-- The Mayer–Vietoris injection `R ⧸ (I ⊓ J) → R ⧸ I × R ⧸ J`. -/
noncomputable def mvPair (I J : Ideal R) : (R ⧸ (I ⊓ J)) →ₗ[R] (R ⧸ I) × (R ⧸ J) :=
  Submodule.liftQ (I ⊓ J) (LinearMap.prod (Submodule.mkQ I) (Submodule.mkQ J)) (by
    intro x hx
    simp
    exact ⟨hx.1, hx.2⟩)

/-- The Mayer–Vietoris difference `R ⧸ I × R ⧸ J → R ⧸ (I ⊔ J)`. -/
noncomputable def mvDiff (I J : Ideal R) : ((R ⧸ I) × (R ⧸ J)) →ₗ[R] R ⧸ (I ⊔ J) :=
  (Submodule.mapQ I (I ⊔ J) LinearMap.id le_sup_left).comp (LinearMap.fst R _ _)
    - (Submodule.mapQ J (I ⊔ J) LinearMap.id le_sup_right).comp (LinearMap.snd R _ _)

theorem mvPair_apply (I J : Ideal R) (x : R) :
    mvPair I J (Submodule.Quotient.mk x) = (Submodule.Quotient.mk x, Submodule.Quotient.mk x) :=
  rfl

theorem mvDiff_apply (I J : Ideal R) (a b : R) :
    mvDiff I J (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
      = Submodule.Quotient.mk a - Submodule.Quotient.mk b := rfl

theorem mvPair_injective (I J : Ideal R) : Function.Injective (mvPair I J) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr ?_
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    have hz' : mvPair I J (Submodule.Quotient.mk x) = 0 := hz
    rw [mvPair_apply, Prod.ext_iff] at hz'
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨?_, ?_⟩
    · have h := hz'.1
      rwa [Prod.fst_zero, Submodule.Quotient.mk_eq_zero] at h
    · have h := hz'.2
      rwa [Prod.snd_zero, Submodule.Quotient.mk_eq_zero] at h

theorem mvDiff_surjective (I J : Ideal R) : Function.Surjective (mvDiff I J) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    refine ⟨(Submodule.Quotient.mk x, 0), ?_⟩
    have h0 : (0 : R ⧸ J) = Submodule.Quotient.mk (0 : R) := by simp
    rw [h0, mvDiff_apply]
    simp

/-- **Exactness in the middle of the Mayer–Vietoris sequence.** -/
theorem mv_exact (I J : Ideal R) :
    LinearMap.range (mvPair I J) = LinearMap.ker (mvDiff I J) := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨z, rfl⟩
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.mem_ker, mvPair_apply, mvDiff_apply, sub_self]
  · rintro ⟨a, b⟩ hw
    induction a using Submodule.Quotient.induction_on with
    | _ α =>
      induction b using Submodule.Quotient.induction_on with
      | _ β =>
        rw [LinearMap.mem_ker, mvDiff_apply, sub_eq_zero] at hw
        have hmem : α - β ∈ I ⊔ J := by
          rw [← Submodule.Quotient.eq]
          exact hw
        obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hmem
        refine ⟨Submodule.Quotient.mk (α - i), ?_⟩
        rw [mvPair_apply]
        refine Prod.ext ?_ ?_
        · show (Submodule.Quotient.mk (α - i) : R ⧸ I) = Submodule.Quotient.mk α
          rw [Submodule.Quotient.eq]
          simpa using I.neg_mem hi
        · show (Submodule.Quotient.mk (α - i) : R ⧸ J) = Submodule.Quotient.mk β
          rw [Submodule.Quotient.eq]
          have : α - i - β = j := by
            have := hij
            linear_combination -this
          rw [this]
          exact hj


end GaloisForLFunctions.HTGeometry
