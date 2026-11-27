import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.IrreducibilityOfGoodTuple
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusOnTameInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildResidualUnipotence

/-! The residual inertia polynomials of a good row give irreducibility,
including on open normal subgroups with solvable quotient containing the
designated inertia groups. The two rank-one labels are excluded as roots. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.CyclotomicNorms
open ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (σ : D.what₂.FT) (w : D.what₂.places.Pl)

local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "ℓ" => D.what₂.places.resChar w
local notation "ρ" => D.ntypes.rbar σ w

/-- Once the residual inertia polynomials are known, the good-row conditions
give the irreducibility and root-exclusion clauses at the coefficient place. -/
theorem residual_irreducibility_of_tame_labels (hg : D.nd.goodRow σ)
    (htame : ∀ k, ℓ ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∀ v, (ρ (D.ntypes.tg k v)).val.charpoly =
        ((rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (primeToPart ℓ x))).prod)
    (hwild : ∀ k, ℓ ≠ D.host.g k → ∀ (v : D.nd.PlG k)
      (s : Γ), s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) →
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      (ρ s).val.charpoly = (X - 1) ^ D.R.r) :
    haveI : Fact (ℓ).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IrredOn ρ ⊤ ∧
    (∀ k, ℓ ∉ BB D.R.r (D.host.g k) →
      ∀ (Hs : Subgroup Γ) [Hs.Normal], IsOpen (Hs : Set Γ) →
        IsSolvable (Γ ⧸ Hs) →
        (∀ u ∈ placesOver D.host.E (D.host.g k), Ine (F := D.host.E) (D.nd.plOm.1 u) ≤ Hs) →
        IrredOn ρ Hs) ∧
    (∀ k, ℓ ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (u : (ZMod (D.host.g k))ˣ),
        u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹ →
        ¬ (ρ (D.ntypes.tg k v)).val.charpoly.IsRoot
          (D.ntypes.iota k v w (primeToPart ℓ (algebraMap (ZMod (D.host.g k))
            (Fbar (D.host.g k)) (u : ZMod (D.host.g k)))))) := by
  letI : Fact (ℓ).Prime := ⟨D.what₂.places.resChar_prime w⟩
  letI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  letI := D.nd.acOm
  letI : IsGalois D.host.E D.nd.Om := {}
  have hb := Set.disjoint_iff_inter_eq_empty.mp D.ntypes.BB_disj
  have hne (k : Fin 2) (hk : ℓ ∉ BB D.R.r (D.host.g k)) : ℓ ≠ D.host.g k :=
    fun he => hk (Or.inl he)
  have hφ (k : Fin 2) (hk : ℓ ≠ D.host.g k) (v : D.nd.PlG k) :
      ∃ φ : Γ, ρ (φ * D.ntypes.tg k v * φ⁻¹) = ρ (D.ntypes.tg k v) ^ D.host.g k := by
    apply exists_frobenius_conj_of_wild_trivial D k v ρ
    intro s hs hratio
    have hp : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.host.g k : D.nd.Om) < 1 := by
      simpa using (D.nd.plOm.2 (D.naut.plGw k v) (D.host.g k : 𝓞 D.host.E)).mpr
        (D.naut.plGw_over k v)
    exact eq_one_of_wild_of_unipotent _ hk hp ρ (D.ntypes.rbar_open σ w) hratio
      (hwild k hk v s hs hratio)
  have key (k : Fin 2) (hk : ℓ ∉ BB D.R.r (D.host.g k)) :
      IrredOn ρ ⊤ ∧
      (∀ (Hs : Subgroup Γ) [Hs.Normal], Finite (Γ ⧸ Hs) →
        IsSolvable (Γ ⧸ Hs) → (∀ v, D.ntypes.tg k v ∈ Hs) → IrredOn ρ Hs) := by
    choose φ hconj using fun v => hφ k (hne k hk) v
    obtain ⟨hi, hres, -⟩ := irreducibility_of_good_tuple D.R.r D.host.g D.nd.PlG (Fin D.R.m)
      (fun i v => D.nd.lab i σ v) D.nd.chiT hb (fun i => (hg i).1)
      ℓ k hk Γ ρ (D.ntypes.tg k) φ (fun v => D.ntypes.iota k v w)
      hconj (fun v => D.ntypes.iota_inj k v w) (htame k (hne k hk))
    exact ⟨hi, hres⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases h₀ : ℓ ∈ BB D.R.r (D.host.g 0)
    · exact (key 1 (fun h₁ => Set.disjoint_left.mp D.ntypes.BB_disj h₀ h₁)).1
    · exact (key 0 h₀).1
  · intro k hk Hs _ hopen hsolv hI
    have hfin : Finite (Γ ⧸ Hs) := Subgroup.quotient_finite_of_isOpen Hs hopen
    exact (key k hk).2 Hs hfin hsolv
      (fun v => hI _ (D.naut.plGw_over k v) (D.ntypes.tg_mem k v))
  · intro k hk v j u hu hroot
    have hgood := (hg k).1
    let f := D.nd.lab k σ v
    let c := algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k)) (u : ZMod (D.host.g k))
    let a := D.ntypes.iota k v w
    change IsRoot _ (a (primeToPart ℓ c)) at hroot
    rw [htame k hk v, IsRoot, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at hroot
    obtain ⟨y, hy, he⟩ := Multiset.mem_map.mp hroot
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at he
    have hpoly : CycleTypeFiniteOrder.GoodPoly D.R.r f :=
      ⟨(hgood.1 v).1, (hgood.1 v).2.1, (hgood.1 v).2.2, hgood.2.1 v⟩
    have hpart := primeToPart_eq_of_map_eq a (D.ntypes.iota_inj k v w)
      (CycleTypeFiniteOrder.ne_zero_of_mem hpoly hy) ((_root_.map_ne_zero _).mpr u.ne_zero) he.symm
    rcases hu with rfl | rfl
    · exact hgood.2.2.2.1 ℓ Fact.out hk v j y hy hpart
    · exact ((hg k).2).2.2.2.1 ℓ Fact.out hk v j y hy hpart

end WindowedLandauTheory.NormalizedTypes
