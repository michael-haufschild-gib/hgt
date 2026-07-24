import GaloisForLFunctions.HTGeometry.KoszulHigherDifferential

/-!
# Difference cohomology groups `H⁰, H¹, H²`

`KoszulCohomology.lean` builds the Koszul differentials `d₀, d₁` of difference cohomology and proves
`d₁ ∘ d₀ = 0`; `KoszulHigherDifferential.lean` adds `d₂` and proves `d₂ ∘ d₁ = 0`.  This file packages
those differentials as additive homomorphisms and defines the honest cohomology groups

```text
H⁰ = ker d₀   (joint invariants),
H¹ = ker d₁ / im d₀,
H² = ker d₂ / im d₁,
```

as genuine subquotients — the `H¹`/`H²` framework left as a draft-side to-do in `KoszulCohomology`.
Well-definedness of each quotient is exactly the composition-zero identity `dₙ₊₁ ∘ dₙ = 0`.
-/

namespace GaloisForLFunctions

noncomputable section

variable {ι M : Type*} [AddCommGroup M]

/-- The first Koszul differential as an additive homomorphism. -/
def koszulD0Hom (act : ι → M →+ M) : M →+ (ι → M) where
  toFun := koszulD0 act
  map_zero' := by ext p; simp [koszulD0]
  map_add' x y := by ext p; simp only [koszulD0, Pi.add_apply, map_add]; abel

/-- The second Koszul differential as an additive homomorphism. -/
def koszulD1Hom (act : ι → M →+ M) : (ι → M) →+ (ι → ι → M) where
  toFun := koszulD1 act
  map_zero' := by ext p q; simp [koszulD1]
  map_add' c d := by ext p q; simp only [koszulD1, Pi.add_apply, map_add]; abel

/-- The third Koszul differential as an additive homomorphism. -/
def koszulD2Hom (act : ι → M →+ M) : (ι → ι → M) →+ (ι → ι → ι → M) where
  toFun := koszulD2 act
  map_zero' := by ext p q r; simp [koszulD2]
  map_add' c d := by ext p q r; simp only [koszulD2, Pi.add_apply, map_add]; abel

@[simp] theorem koszulD0Hom_apply (act : ι → M →+ M) (x : M) :
    koszulD0Hom act x = koszulD0 act x := rfl

@[simp] theorem koszulD1Hom_apply (act : ι → M →+ M) (c : ι → M) :
    koszulD1Hom act c = koszulD1 act c := rfl

@[simp] theorem koszulD2Hom_apply (act : ι → M →+ M) (c : ι → ι → M) :
    koszulD2Hom act c = koszulD2 act c := rfl

/-- The image of `d₀` lies in the kernel of `d₁`: `im d₀ ≤ ker d₁`. -/
theorem koszulD0Hom_range_le_koszulD1Hom_ker {act : ι → M →+ M}
    (hcomm : commutingAdditiveActions act) :
    (koszulD0Hom act).range ≤ (koszulD1Hom act).ker := by
  rintro _ ⟨h, rfl⟩
  rw [AddMonoidHom.mem_ker]
  ext p q
  exact koszulD1_koszulD0_eq_zero hcomm h p q

/-- The image of `d₁` lies in the kernel of `d₂`: `im d₁ ≤ ker d₂`. -/
theorem koszulD1Hom_range_le_koszulD2Hom_ker {act : ι → M →+ M}
    (hcomm : commutingAdditiveActions act) :
    (koszulD1Hom act).range ≤ (koszulD2Hom act).ker := by
  rintro _ ⟨b, rfl⟩
  rw [AddMonoidHom.mem_ker]
  ext p q r
  exact koszulD2_koszulD1_eq_zero hcomm b p q r

/-- **Zeroth difference cohomology** `H⁰ = ker d₀`, the joint-invariant subgroup. -/
def koszulH0 (act : ι → M →+ M) : AddSubgroup M := (koszulD0Hom act).ker

theorem mem_koszulH0_iff_invariant {act : ι → M →+ M} (x : M) :
    x ∈ koszulH0 act ↔ additiveInvariant act x := by
  rw [koszulH0, AddMonoidHom.mem_ker]
  constructor
  · intro h p
    have := congrArg (fun f => f p) h
    simpa [koszulD0, sub_eq_zero] using this
  · intro h
    ext p
    simp [koszulD0, h p]

/-- **First difference cohomology** `H¹ = ker d₁ / im d₀`, a genuine subquotient. -/
def koszulH1 (act : ι → M →+ M) : Type _ :=
  (koszulD1Hom act).ker ⧸ ((koszulD0Hom act).range.addSubgroupOf (koszulD1Hom act).ker)

/-- **Second difference cohomology** `H² = ker d₂ / im d₁`, a genuine subquotient. -/
def koszulH2 (act : ι → M →+ M) : Type _ :=
  (koszulD2Hom act).ker ⧸ ((koszulD1Hom act).range.addSubgroupOf (koszulD2Hom act).ker)

instance (act : ι → M →+ M) : AddCommGroup (koszulH1 act) :=
  QuotientAddGroup.Quotient.addCommGroup _

instance (act : ι → M →+ M) : AddCommGroup (koszulH2 act) :=
  QuotientAddGroup.Quotient.addCommGroup _

end

end GaloisForLFunctions
