import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodIsobaricParameters
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.IrreducibilityOfGoodTuple
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

/-! Theorem Three Prime follows from the local label laws and the
residual inertia comparison, including the comparison at conjugate places. -/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.MainNotions.ArithmeticCylinders
open WindowedLandauTheory.CyclotomicNorms ReciprocityTheory.Gal

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc)
variable (P : List (Part D.naut.CG)) (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* GL (Fin D.R.r) (D.nd.O i))

local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
private abbrev redAt (i : D.nd.Loc) (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) :=
  mapRep ((D.naut.kFbar i).comp (residue (D.nd.O i))) r

private abbrev labelAt (P : List (Part D.naut.CG)) (k : Fin 2) (v : D.nd.PlG k) :=
  D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut P (D.naut.plGw k v))


/-- The characteristic polynomial and Frobenius action at a designated
tame element, read in terms of the prime-to-characteristic label roots. -/
def ResidualTameLabels (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.nd.l i).Prime := D.nd.lPrime i
  ∃ a : Fbar (D.host.g k) →* Fbar (D.nd.l i),
    (∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
      (orderOf y).Coprime (D.nd.l i) → a x = a y → x = y) ∧
    ((redAt D i r) (D.ntypes.tg k v)).val.charpoly =
      ((rootsBar (labelAt D P k v)).map fun x => X - C (a (primeToPart (D.nd.l i) x))).prod ∧
    ∃ φ : Γ, (redAt D i r) (φ * D.ntypes.tg k v * φ⁻¹) = ((redAt D i r) (D.ntypes.tg k v)) ^ D.host.g k

/-- At all places over the auxiliary primes, a tame generator separates
the rank-one character from the residual representation. -/
def ResidualTameRootExclusion : Prop :=
  ∀ (k : Fin 2), D.nd.l i ≠ D.host.g k →
    ∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
    ¬ ((redAt D i r) (D.nd.gam0 i w)).val.charpoly.IsRoot
      (D.naut.kFbar i (residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))))

private theorem irreducible_of_labels (hg : goodSig D.nd D.naut P)
    (hBB : Disjoint (BB D.R.r (D.host.g 0)) (BB D.R.r (D.host.g 1)))
    (k : Fin 2) (hk : D.nd.l i ∉ BB D.R.r (D.host.g k))
    (ht : ∀ v, ResidualTameLabels D i P r k v) :
    IrredOn (redAt D i r) ⊤ ∧
      (∀ (H : Subgroup Γ) [H.Normal], Finite (Γ ⧸ H) → IsSolvable (Γ ⧸ H) →
        (∀ v, D.ntypes.tg k v ∈ H) → IrredOn (redAt D i r) H) := by
  letI : Fact (D.nd.l i).Prime := D.nd.lPrime i
  letI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  let f := labelAt D P
  have hf : ∀ j, IsGood D.R.r (D.host.g j) (f j) (D.nd.chiT j) := fun j => (hg j).1
  have ht' : ∀ v : D.nd.PlG k, ∃ a : Fbar (D.host.g k) →* Fbar (D.nd.l i),
      (∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
        (orderOf y).Coprime (D.nd.l i) → a x = a y → x = y) ∧
      ((redAt D i r) (D.ntypes.tg k v)).val.charpoly =
        ((rootsBar (f k v)).map fun x => X - C (a (primeToPart (D.nd.l i) x))).prod ∧
      ∃ φ : Γ, (redAt D i r) (φ * D.ntypes.tg k v * φ⁻¹) = ((redAt D i r) (D.ntypes.tg k v)) ^ D.host.g k := ht
  choose a ha hpoly hφ using ht'
  choose φ hconj using hφ
  obtain ⟨h₁, h₂, -⟩ := irreducibility_of_good_tuple D.R.r D.host.g D.nd.PlG (Fin D.R.m)
    f D.nd.chiT (Set.disjoint_iff_inter_eq_empty.mp hBB) hf
    (D.nd.l i) k hk Γ (redAt D i r) (D.ntypes.tg k) φ a hconj ha hpoly
  exact ⟨h₁, h₂⟩

/-- At a designated place of a good signature, neither the positive nor the
negative orientation of the type character survives as a residual root. -/
theorem goodSig_not_isRoot_of_labels (hg : goodSig D.nd D.naut P)
    (k : Fin 2) (hk : D.nd.l i ≠ D.host.g k) (v : D.nd.PlG k) (j : Fin D.R.m)
    [Fact (D.host.g k).Prime] [Fact (D.nd.l i).Prime]
    (a : Fbar (D.host.g k) →* Fbar (D.nd.l i))
    (ha : ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
      (orderOf y).Coprime (D.nd.l i) → a x = a y → x = y)
    (u : (ZMod (D.host.g k))ˣ) (hu : u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹) :
    ¬ (((rootsBar (labelAt D P k v)).map fun x => X - C (a (primeToPart (D.nd.l i) x))).prod).IsRoot
      (a (primeToPart (D.nd.l i)
        (algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k)) (u : ZMod (D.host.g k))))) := by
  obtain ⟨hm, hq, -⟩ := (hg k).1
  have hf : CycleTypeFiniteOrder.GoodPoly D.R.r (labelAt D P k v) :=
    ⟨(hm v).1, (hm v).2.1, (hm v).2.2, hq v⟩
  intro hroot
  rw [IsRoot, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at hroot
  obtain ⟨x, hx, he⟩ := Multiset.mem_map.mp hroot
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at he
  have hpart := primeToPart_eq_of_map_eq a ha (CycleTypeFiniteOrder.ne_zero_of_mem hf hx)
    ((_root_.map_ne_zero _).mpr u.ne_zero) he.symm
  rcases hu with rfl | rfl
  · exact (hg k).1.2.2.2.1 _ Fact.out hk v j x hx hpart
  · exact (hg k).2.2.2.2.1 _ Fact.out hk v j x hx hpart

/-- The two inertia comparisons give the irreducibility and root exclusions
of Theorem Three Prime once the local summands have the label degree bound. -/
theorem theoremThreePrime_of_inertia
    (hTw : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)) (s : ℝ),
      D.naut.items₂ k _ (D.naut.lpTw a s) = D.naut.items₂ k _ a)
    (hdeg : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)),
      (D.naut.items₂ k _ a).natDegree ≤ D.naut.lpDim a)
    (hG : ∀ (i : D.nd.Loc) (P : List (Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x P) →
      (∀ (k : Fin 2) (v : D.nd.PlG k), (labelAt D P k v).natDegree =
        D.naut.lpDim (isoLoc D.nd D.naut P (D.naut.plGw k v))) →
      goodSig D.nd D.naut P →
      IsCuspIso D.nd D.naut P → ∀ r, IsRepOfSig D.nd D.naut i P r →
      (∀ k, D.nd.l i ≠ D.host.g k → ∀ v, ResidualTameLabels D i P r k v) ∧
      ResidualTameRootExclusion D i r) : TheoremThreePrime D := by
  intro hBB loc Sig hx hd hg
  obtain ⟨x, hP⟩ := hx
  obtain ⟨hpos, hrank⟩ := parts_pos_and_rank_of_hasParamX D loc x Sig hP
  have hcusp := isCuspIso_of_goodSig D Sig hpos hrank hg hTw hdeg
  refine ⟨hcusp, fun rep hr => ?_⟩
  letI : Fact (D.nd.l loc).Prime := D.nd.lPrime loc
  letI := D.nd.acOm
  letI : IsGalois D.host.E D.nd.Om := {}
  obtain ⟨ht, he⟩ := hG loc Sig ⟨x, hP⟩ hd hg hcusp rep hr
  have key (k : Fin 2) (hk : D.nd.l loc ∉ BB D.R.r (D.host.g k)) :=
    irreducible_of_labels D loc Sig rep hg hBB k hk (ht k fun e => hk (Or.inl e))
  refine ⟨?_, ?_, he⟩
  · by_cases h₀ : D.nd.l loc ∈ BB D.R.r (D.host.g 0)
    · exact (key 1 (fun h₁ => Set.disjoint_left.mp hBB h₀ h₁)).1
    · exact (key 0 h₀).1
  · intro k hk H _ hopen hsol hI
    have hfin : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hopen
    exact (key k hk).2 H hfin hsol (fun v => hI _ (D.naut.plGw_over k v) (D.ntypes.tg_mem k v))

end WindowedLandauTheory.NormalizedTypes
