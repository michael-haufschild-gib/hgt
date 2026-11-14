import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfALinearCharacter
import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersGiveConvergentLSeries

/-!
# The Artin Euler product of the conjugate representation runs over the inverse characters

Let `L/K` be a Galois extension of number fields with group `G`, `ρ` a representation of `G`
and `ρ*` a representation with the conjugate character.

* **Conjugation** (`artinSymbol_inv`, `inducedFunction_star`). The Artin symbols of the inverse
  of a linear character are the conjugates, `(χ⁻¹, v) = conj (χ, v)`, and induction commutes
  with conjugation.
* **The two products** (`exists_artinEulerProduct_eq_prod_zpow_abelian_conj`). There are
  integers `n_q` on the Brauer pairs `q = (E, χ)` such that for `Re s > 1`

  `L(s, ρ, L/K) = Π_q L(s, χ_q, L/L^{E_q})^{n_q}`,  `L(s, ρ*, L/K) = Π_q L(s, χ_q⁻¹, L/L^{E_q})^{n_q}`,

  with the same integers: conjugate Brauer's relation `χ_ρ = Σ_q n_q Ind χ_q`.
-/

open scoped Classical BigOperators NumberField ComplexConjugate
open NumberField IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-! ### Conjugation -/

/-- The values of the inverse of a character of a finite group are the conjugates. -/
theorem linearCharacter_inv_apply {H : Type u} [Group H] [Finite H] (χ : LinearCharacter H)
    (h : H) : ((χ⁻¹ h : ℂˣ) : ℂ) = conj (χ h : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj (norm_char_eq_one χ h)

/-- **Induction commutes with conjugation.** -/
theorem inducedFunction_star {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ)
    (g : G) : inducedFunction H (fun h => conj (f h)) g = conj (inducedFunction H f g) := by
  have hext : ∀ y : G, extendByZero H (fun h => conj (f h)) y = conj (extendByZero H f y) :=
    fun y => by
      by_cases hy : y ∈ H
      · rw [extendByZero_of_mem H _ hy, extendByZero_of_mem H _ hy]
      · rw [extendByZero_of_notMem H _ hy, extendByZero_of_notMem H _ hy, map_zero]
  rw [inducedFunction, inducedFunction, map_mul, map_inv₀, map_natCast, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun x _ => hext (x * g * x⁻¹))

variable (K L : Type u) {G V : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **The Artin symbols of the inverse character are the conjugates**: `χ⁻¹` and `χ` are
trivial on the same inertia groups. -/
theorem artinSymbol_inv (χ : LinearCharacter G) (v : HeightOneSpectrum (𝓞 K)) :
    artinSymbol K L χ⁻¹ v = conj (artinSymbol K L χ v) := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  haveI := hQmax
  haveI := hQover
  rw [artinSymbol_eq_frobeniusValue K L χ⁻¹ v Q, artinSymbol_eq_frobeniusValue K L χ v Q]
  unfold frobeniusValue
  by_cases h : ∀ τ ∈ Q.inertia G, χ τ = 1
  · rw [if_pos h, if_pos fun τ hτ => by rw [MonoidHom.inv_apply, h τ hτ, inv_one]]
    exact linearCharacter_inv_apply χ _
  · rw [if_neg h, if_neg fun h' => h fun τ hτ =>
      inv_eq_one.mp ((MonoidHom.inv_apply χ τ).symm.trans (h' τ hτ)), map_zero]

/-! ### Euler products of integer combinations of monomial characters -/

/-- If the character of `ρ` is the integer combination `Σ_q n_q Ind χ_q` of functions induced
from linear characters `χ_q` of the subgroups of the Brauer pairs, then for `Re s > 1`
`L(s, ρ, L/K) = Π_q L(s, χ_q, L/L^{E_q})^{n_q}`. -/
theorem artinEulerProduct_eq_prod_zpow_of_character_eq (ρ : Representation ℂ G V)
    (n : brauerElementaryMonomialIndex G →₀ ℤ)
    (χ : ∀ q : brauerElementaryMonomialIndex G, LinearCharacter q.1.subgroup)
    (hρ : ρ.character = ∑ q ∈ n.support,
      n q • inducedFunction q.1.subgroup fun h => (χ q h : ℂ)) {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
      n.prod fun q k => numberFieldFinitePlaceArtinEulerReciprocalProduct
        (K := (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L)) (L := L)
        (linearCharacterLine (χ q)) s ^ k := by
  have hτ : ∀ q : brauerElementaryMonomialIndex G,
      (Representation.ind q.1.subgroup.subtype (linearCharacterLine (χ q))).character =
        inducedFunction q.1.subgroup (linearCharacterLine (χ q)).character :=
    fun q => induced_character_eq_inducedFunction q.1.subgroup (linearCharacterLine (χ q))
  have hchar : ρ.character = ∑ q ∈ n.support, n q •
      (Representation.ind q.1.subgroup.subtype (linearCharacterLine (χ q))).character := by
    rw [hρ]
    exact Finset.sum_congr rfl fun q _ => by rw [hτ q, linearCharacterLine_character]
  rw [numberFieldFinitePlaceArtinEulerReciprocalProduct_eq_prod_zpow n.support n ρ
    (fun q => Representation.ind q.1.subgroup.subtype (linearCharacterLine (χ q))) hchar hs,
    Finsupp.prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  congr 1
  exact numberFieldFinitePlaceArtinEulerReciprocalProduct_induced
    (M := (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L))
    q.1.subgroup _ (linearCharacterLine (χ q)) (hτ q) hs

/-- **The Euler products of a representation and of its conjugate.** There are integers `n_q`
on the Brauer pairs `q = (E, χ)` with `L(s, ρ, L/K) = Π_q L(s, χ_q, L/L^{E_q})^{n_q}` for
`Re s > 1`, and for every representation `ρ*` with the conjugate character
`L(s, ρ*, L/K) = Π_q L(s, χ_q⁻¹, L/L^{E_q})^{n_q}`. -/
theorem exists_artinEulerProduct_eq_prod_zpow_abelian_conj (ρ : Representation ℂ G V) :
    ∃ n : brauerElementaryMonomialIndex G →₀ ℤ,
      (∀ s : ℂ, 1 < s.re →
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
          n.prod fun q k => brauerAbelianEulerProduct K L q s ^ k) ∧
      ∀ {V' : Type u} [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
        (ρ' : Representation ℂ G V'), (∀ g : G, ρ'.character g = conj (ρ.character g)) →
        ∀ s : ℂ, 1 < s.re →
          numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ' s =
            n.prod fun q k => numberFieldFinitePlaceArtinEulerReciprocalProduct
              (K := (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L))
              (L := L) (linearCharacterLine q.2⁻¹) s ^ k := by
  -- Brauer: the character of `ρ` is an integer combination of monomial characters
  have hmem : (⟨ρ.character, AddSubgroup.subset_closure
      (representation_character_mem_fdCharacterSet G ρ)⟩ : VirtualCharacter G) ∈
      AddSubgroup.closure (Set.range (brauerElementaryMonomialVirtualCharacter G)) := by
    rw [brauer_induction]
    exact AddSubgroup.mem_top _
  obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_range_iff.mp hmem
  have hchar : ρ.character = ∑ q ∈ n.support,
      n q • inducedFunction q.1.subgroup fun h => (q.2 h : ℂ) := by
    have h := congrArg (virtualCharacterGroup G).subtype hn
    simp only [Finsupp.sum, map_sum, map_zsmul, AddSubgroup.coe_subtype] at h
    rw [h]
    exact Finset.sum_congr rfl fun q _ =>
      congrArg _ (monomialVirtualCharacter_val q.1.subgroup q.2)
  refine ⟨n, fun s hs =>
    artinEulerProduct_eq_prod_zpow_of_character_eq K L ρ n (fun q => q.2) hchar hs, ?_⟩
  intro V' _ _ _ ρ' hρ' s hs
  -- the conjugate relation: induction commutes with conjugation
  have hchar' : ρ'.character = ∑ q ∈ n.support,
      n q • inducedFunction q.1.subgroup fun h => ((q.2⁻¹ h : ℂˣ) : ℂ) := by
    funext g
    rw [hρ' g, hchar, Finset.sum_apply, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast,
      ← inducedFunction_star]
    exact congrArg (fun f => (n q : ℂ) * inducedFunction q.1.subgroup f g)
      (funext fun h => (linearCharacter_inv_apply q.2 h).symm)
  exact artinEulerProduct_eq_prod_zpow_of_character_eq K L ρ' n (fun q => q.2⁻¹) hchar' hs

end GaloisForLFunctions
