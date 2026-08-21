import GaloisForLFunctions.HTGeometry.InvolutionTateCohomology

/-!
# The component group of the real points of a real torus

Let `V` be a real vector space, `Λ ⊆ V` a `σ`-stable `ℤ`-lattice and `σ` an `ℝ`-linear involution
of `V` (for a complex torus `A = V / Λ` with a real structure, `σ` is complex conjugation).  The
group of "real points" of `A = V / Λ` is `A^σ`, and the image of `V^σ` in `A` is its identity
component.

This file proves, purely algebraically,

```
A^σ / image(V^σ)  ≅  Ĥ¹(⟨σ⟩, Λ) ,
```

as `RealTorus.quotEquivTateH1`; equivalently, `W / (V^σ + Λ) ≅ Ĥ¹(σ|Λ)` where
`W = {v ∈ V | σ v - v ∈ Λ}` is the preimage of `A^σ` in `V`.

This is the group-cohomology step behind `π₀(A(ℝ)) ≅ Ĥ¹(⟨c⟩, Λ)` used in the proof of Proposition
5.1 of Suzuki, *Duality invariance of Faltings heights, Hodge line bundles and global periods*
(arXiv:2504.04993), quoted there from Milne, *Arithmetic Duality Theorems*, Chapter I, Remark 3.7.
The mechanism is the vanishing of `H¹(⟨σ⟩, V)`: `V` is uniquely `2`-divisible, so every
`σ`-anti-invariant lattice vector `μ` is `σ v - v` for `v = -μ/2`.

Only the identification of `image(V^σ)` with the *topological* identity component of `A^σ` is left
outside Lean; the component group itself is computed here.
-/

namespace GaloisForLFunctions.HTGeometry.RealTorus

open LinearMap Module Submodule InvolutionTate

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {σ : V →ₗ[R] V} {Λ : Submodule ℤ V}

/-- `σ` regarded as a `ℤ`-linear endomorphism. -/
abbrev sigmaZ (σ : V →ₗ[R] V) : V →ₗ[ℤ] V := σ.restrictScalars ℤ

/-- The involution induced on the lattice. -/
def sigmaLat (σ : V →ₗ[R] V) (Λ : Submodule ℤ V) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) : Λ →ₗ[ℤ] Λ :=
  (sigmaZ σ).restrict hΛ

@[simp] theorem sigmaLat_coe (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) (x : Λ) :
    ((sigmaLat σ Λ hΛ x : Λ) : V) = σ (x : V) := rfl

theorem sigmaLat_involutive (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    ∀ x, sigmaLat σ Λ hΛ (sigmaLat σ Λ hΛ x) = x := by
  intro x
  apply Subtype.ext
  simp [hσ]

/-- The preimage in `V` of the `σ`-fixed points of `V / Λ`. -/
def realLocus (σ : V →ₗ[R] V) (Λ : Submodule ℤ V) : Submodule ℤ V :=
  Λ.comap (sigmaZ σ - LinearMap.id)

theorem mem_realLocus {v : V} : v ∈ realLocus σ Λ ↔ σ v - v ∈ Λ := Iff.rfl

/-- The `σ`-fixed subspace of `V`, a `ℤ`-submodule. -/
def fixedPart (σ : V →ₗ[R] V) : Submodule ℤ V := ker (sigmaZ σ - LinearMap.id)

theorem mem_fixedPart {v : V} : v ∈ fixedPart σ ↔ σ v = v := by
  simp [fixedPart, LinearMap.mem_ker, sub_eq_zero]

theorem fixedPart_le_realLocus : fixedPart σ ≤ realLocus (σ := σ) (Λ := Λ) := by
  intro v hv
  rw [mem_realLocus, mem_fixedPart.mp hv, sub_self]
  exact Λ.zero_mem

theorem lattice_le_realLocus (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) : Λ ≤ realLocus σ Λ := by
  intro v hv
  exact Λ.sub_mem (hΛ v hv) hv


/-! ### The connecting map to `Ĥ¹` -/

/-- `σ - 1`, restricted to a `ℤ`-linear map `realLocus σ Λ → Λ`. -/
def deltaToLat (σ : V →ₗ[R] V) (Λ : Submodule ℤ V) : realLocus σ Λ →ₗ[ℤ] Λ :=
  (sigmaZ σ - LinearMap.id).restrict (fun _ hx => hx)

@[simp] theorem deltaToLat_coe (v : realLocus σ Λ) :
    ((deltaToLat σ Λ v : Λ) : V) = σ (v : V) - (v : V) := rfl

theorem deltaToLat_mem_minusPart (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    (v : realLocus σ Λ) : deltaToLat σ Λ v ∈ minusPart (sigmaLat σ Λ hΛ) := by
  rw [mem_minusPart]
  apply Subtype.ext
  simp only [sigmaLat_coe, deltaToLat_coe, map_sub, hσ, Submodule.coe_neg]
  abel

/-- `σ - 1` as a map into the `-1`-eigenlattice of `Λ`. -/
def deltaToMinus (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    realLocus σ Λ →ₗ[ℤ] minusPart (sigmaLat σ Λ hΛ) :=
  (deltaToLat σ Λ).codRestrict _ (deltaToLat_mem_minusPart hσ hΛ)

@[simp] theorem deltaToMinus_coe (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    (v : realLocus σ Λ) :
    (((deltaToMinus hσ hΛ v : minusPart (sigmaLat σ Λ hΛ)) : Λ) : V) = σ (v : V) - (v : V) := rfl

/-- The connecting map `A^σ → Ĥ¹(⟨σ⟩, Λ)`, written on the preimage `realLocus σ Λ` in `V`. -/
def toTateH1 (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :=
  (Submodule.mkQ (comap (minusPart (sigmaLat σ Λ hΛ)).subtype
    (LinearMap.range (dlt (sigmaLat σ Λ hΛ))))) ∘ₗ (deltaToMinus hσ hΛ)

theorem ker_toTateH1 (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    LinearMap.ker (toTateH1 hσ hΛ) = comap (realLocus σ Λ).subtype (fixedPart σ ⊔ Λ) := by
  ext v
  rw [LinearMap.mem_ker]
  show Submodule.Quotient.mk (deltaToMinus hσ hΛ v) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
  constructor
  · rintro ⟨μ, hμ⟩
    have hμv : σ ((μ : Λ) : V) - ((μ : Λ) : V) = σ (v : V) - (v : V) :=
      congrArg (fun y : Λ => (y : V)) hμ
    refine Submodule.mem_sup.mpr ⟨(v : V) - ((μ : Λ) : V), ?_, ((μ : Λ) : V), μ.2, by abel⟩
    rw [mem_fixedPart, map_sub]
    have hrearr : (σ (v : V) - σ ((μ : Λ) : V)) - ((v : V) - ((μ : Λ) : V))
        = (σ (v : V) - (v : V)) - (σ ((μ : Λ) : V) - ((μ : Λ) : V)) := by abel
    rw [← hμv, sub_self] at hrearr
    exact sub_eq_zero.mp hrearr
  · intro hv
    obtain ⟨a, ha, μ, hμ, hsum⟩ := Submodule.mem_sup.mp hv
    have haσ : σ a = a := mem_fixedPart.mp ha
    refine ⟨⟨μ, hμ⟩, ?_⟩
    apply Subtype.ext
    show σ μ - μ = σ (v : V) - (v : V)
    rw [← hsum, map_add, haσ]
    abel

theorem surjective_toTateH1 [Invertible (2 : R)] (hσ : ∀ x, σ (σ x) = x)
    (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) : Function.Surjective (toTateH1 hσ hΛ) := by
  intro y
  refine Submodule.Quotient.induction_on _ y fun m => ?_
  set w : V := (⅟(2 : R)) • (-((m : Λ) : V)) with hw
  have hmσ : σ ((m : Λ) : V) = -((m : Λ) : V) := by
    have := congrArg (fun y : Λ => (y : V)) (mem_minusPart.mp m.2)
    simpa using this
  have hkey : σ w - w = ((m : Λ) : V) := by
    rw [hw, map_smul, map_neg, hmσ, neg_neg, ← smul_sub, sub_neg_eq_add, ← two_smul R,
      smul_smul, invOf_mul_self, one_smul]
  have hwmem : w ∈ realLocus σ Λ := by
    rw [mem_realLocus, hkey]; exact (m : Λ).2
  refine ⟨⟨w, hwmem⟩, ?_⟩
  have hd : deltaToMinus hσ hΛ ⟨w, hwmem⟩ = m := by
    apply Subtype.ext; apply Subtype.ext; exact hkey
  simp only [toTateH1, LinearMap.coe_comp, Function.comp_apply, hd]
  rfl

/-- **The component group of the real points is `Ĥ¹`.**
`A^σ / image(V^σ) ≅ Ĥ¹(⟨σ⟩, Λ)`, written with the preimage of `A^σ` in `V`. -/
noncomputable def quotEquivTateH1 [Invertible (2 : R)] (hσ : ∀ x, σ (σ x) = x)
    (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    ((realLocus σ Λ) ⧸ comap (realLocus σ Λ).subtype (fixedPart σ ⊔ Λ)) ≃ₗ[ℤ]
      H1 (sigmaLat σ Λ hΛ) :=
  (Submodule.quotEquivOfEq _ _ (ker_toTateH1 hσ hΛ).symm) ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective _ (surjective_toTateH1 hσ hΛ)

/-- Cardinality form of `quotEquivTateH1`. -/
theorem card_quot_eq_card_tateH1 [Invertible (2 : R)] (hσ : ∀ x, σ (σ x) = x)
    (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    Nat.card ((realLocus σ Λ) ⧸ comap (realLocus σ Λ).subtype (fixedPart σ ⊔ Λ))
      = Nat.card (H1 (sigmaLat σ Λ hΛ)) :=
  Nat.card_congr (quotEquivTateH1 hσ hΛ).toEquiv

end GaloisForLFunctions.HTGeometry.RealTorus
