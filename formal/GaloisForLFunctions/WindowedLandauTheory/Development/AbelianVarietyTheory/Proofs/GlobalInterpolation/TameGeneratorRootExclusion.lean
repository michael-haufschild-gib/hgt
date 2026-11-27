import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterPolynomialPowers

/-! A tame generator generates the image of inertia in every finite quotient
killing wild inertia. Root exclusion for a representation and a character
therefore holds for every tame generator once it holds at one inertia element. -/

noncomputable section

open Polynomial
open WindowedLandauTheory.BasicNotions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}

local notation "Γ" => (Ω ≃ₐ[E] Ω)

omit [IsAlgClosure E Ω] in
theorem tameGenAt_inv {A : ValuationSubring Ω} {γ : Γ} (hγ : TameGenAt A γ) :
    TameGenAt A γ⁻¹ := by
  let W : Set Γ := {s | ∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1}
  let H := Subgroup.closure (insert γ⁻¹ W)
  have hinv : γ⁻¹ ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hle : Subgroup.closure (insert γ W) ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · change _ ∈ H
      have hi := H.inv_mem hinv
      rw [inv_inv] at hi
      exact hi
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hs)
  exact ⟨(Ine (F := E) A).inv_mem hγ.1, fun _ hs => closure_mono hle (hγ.2 hs)⟩

/-- In an open-kernel tame representation, any inertia element has the same
image as a nonnegative power of a chosen tame generator. -/
theorem exists_pow_eq_of_tameGen {M : Type*} [Group M]
    (A : ValuationSubring Ω)
    (r : Γ →* M)
    (hr : IsOpen (r.ker : Set (Γ)))
    (hW : ∀ s, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → r s = 1)
    {τ γ : Γ}
    (hτ : τ ∈ Ine (F := E) A) (hγ : TameGenAt A γ) :
    ∃ j : ℕ, (r γ) ^ j = r τ := by
  let H := (Subgroup.zpowers (r γ)).comap r
  have hle : r.ker ≤ H := by
    intro s hs
    change r s ∈ Subgroup.zpowers (r γ)
    rw [MonoidHom.mem_ker.mp hs]
    exact one_mem _
  have hHo : IsOpen (H : Set (Γ)) :=
    H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hr.mem_nhds (one_mem r.ker)) hle)
  have hHH : Subgroup.closure
      (insert γ {s : Γ |
        ∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1}) ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact Subgroup.mem_zpowers _
    · exact hle (MonoidHom.mem_ker.mpr (hW s hs))
  have hz : r τ ∈ Subgroup.zpowers (r γ) :=
    closure_minimal hHH (H.isClosed_of_isOpen hHo) (hγ.2 hτ)
  letI : IsGalois E Ω := {}
  letI : Finite (Γ ⧸ r.ker) := Subgroup.quotient_finite_of_isOpen r.ker hr
  have hquot : IsOfFinOrder ((QuotientGroup.mk' r.ker) γ) := isOfFinOrder_of_finite _
  have hfin : IsOfFinOrder (r γ) := by
    obtain ⟨m, hm, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hquot
    have hpow : (QuotientGroup.kerLift r ((QuotientGroup.mk' r.ker) γ)) ^ m = 1 := by
      rw [← map_pow, he, map_one]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hpow⟩
  exact (hfin.mem_powers_iff_mem_zpowers.mpr hz)

/-- If a character value is excluded at an inertia element, it is excluded
at every tame generator. A hypothetical root would remain a root after
raising the representation and character to the same power. -/
theorem not_isRoot_of_tameGen
    (A : ValuationSubring Ω)
    (ρ : Γ →* GL (Fin n) K)
    (χ : Γ →* Kˣ)
    (hρ : IsOpen (ρ.ker : Set (Γ)))
    (hχ : IsOpen (χ.ker : Set (Γ)))
    (hW : ∀ s, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → ρ s = 1 ∧ χ s = 1)
    {τ γ : Γ}
    (hτ : τ ∈ Ine (F := E) A) (hγ : TameGenAt A γ)
    (hex : ¬ (ρ τ).val.charpoly.IsRoot (χ τ : K)) :
    ¬ (ρ γ).val.charpoly.IsRoot (χ γ : K) := by
  let r := ρ.prod χ
  have hr : IsOpen (r.ker : Set (Γ)) := by
    have he : (r.ker : Set (Γ)) =
        (ρ.ker : Set (Γ)) ∩ χ.ker := by
      ext s
      simp only [SetLike.mem_coe, Set.mem_inter_iff, MonoidHom.mem_ker]
      change (ρ s, χ s) = (1, 1) ↔ ρ s = 1 ∧ χ s = 1
      simp only [Prod.mk.injEq]
    rw [he]
    exact hρ.inter hχ
  obtain ⟨j, hj⟩ := exists_pow_eq_of_tameGen A r hr
    (fun s hs => Prod.ext (hW s hs).1 (hW s hs).2) hτ hγ
  intro hroot
  have hM := congrArg (fun u : GL (Fin n) K × Kˣ => u.1.val) hj
  have hC := congrArg (fun u : GL (Fin n) K × Kˣ => (u.2 : K)) hj
  change ((ρ γ) ^ j).val = (ρ τ).val at hM
  change ((χ γ) ^ j : Kˣ).val = (χ τ : K) at hC
  rw [Units.val_pow_eq_pow_val] at hM hC
  have hmem := (mem_roots (Matrix.charpoly_monic (ρ γ).val).ne_zero).mpr hroot
  have hpow := Multiset.mem_map_of_mem (fun z : K => z ^ j) hmem
  rw [← GlobalTheory.CharpolyPow.roots_charpoly_pow K n j, hM, hC] at hpow
  exact hex ((mem_roots (Matrix.charpoly_monic (ρ τ).val).ne_zero).mp hpow)

end GlobalTheory.TameKummer
