import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOnIntegerRelationsOfCharacters
import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfAnInducedRepresentation
import GaloisForLFunctions.RHTower.Artin.ArtinBrauerInductionTheorem

/-!
# Every Artin Euler product is a product of integer powers of abelian Euler products

Let `L/K` be a Galois extension of number fields with group `G` and `ρ` a representation of
`G`. There are integers `n_q`, for finitely many pairs `q = (E, χ)` of a Brauer-elementary
subgroup `E ≤ G` and a linear character `χ` of `E`, such that for `Re s > 1`

  `L(s, ρ, L/K) = Π_q L(s, χ_q, L/L^{E_q})^{n_q}`

(`exists_artinEulerProduct_eq_prod_zpow_abelian`). Here `L^E` is the fixed field of `E`, whose
Galois group over `L` is `E`, and `L(s, χ, L/L^E)` is the Artin Euler product of the line on
which `E` acts through `χ`.

Proof: by Brauer's induction theorem the character of `ρ` is an integer combination of the
characters induced from the `χ_q`; the Euler product is a homomorphism on integer relations
between characters; and the Euler product of an induced representation is the Euler product
over the fixed field.
-/

open scoped Classical BigOperators NumberField

noncomputable section

universe u

namespace GaloisForLFunctions

/-! ### The line of a linear character -/

/-- The one-dimensional representation of a linear character, on a line in the universe of the
group. -/
def linearCharacterLine {H : Type u} [Group H] (χ : LinearCharacter H) :
    Representation ℂ H (ULift.{u} ℂ) where
  toFun h := (χ h : ℂ) • LinearMap.id
  map_one' := by
    rw [map_one, Units.val_one, one_smul]
    rfl
  map_mul' h k := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, Module.End.mul_apply, map_mul,
      Units.val_mul, mul_smul]

/-- The character of the line of `χ` is `χ`. -/
theorem linearCharacterLine_character {H : Type u} [Group H] (χ : LinearCharacter H) :
    (linearCharacterLine χ).character = fun h => (χ h : ℂ) := by
  funext h
  change LinearMap.trace ℂ (ULift.{u} ℂ) ((χ h : ℂ) • LinearMap.id) = (χ h : ℂ)
  rw [map_smul, LinearMap.trace_id, (ULift.moduleEquiv (R := ℂ) (M := ℂ)).finrank_eq,
    Module.finrank_self, Nat.cast_one, smul_eq_mul, mul_one]

/-! ### The decomposition -/

variable (K L : Type u) {G V : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The abelian Euler product of a Brauer pair `(E, χ)`: the Artin Euler product of the linear
character `χ` of the Brauer-elementary subgroup `E`, over the fixed field of `E`. -/
def brauerAbelianEulerProduct (q : brauerElementaryMonomialIndex G) (s : ℂ) : ℂ :=
  numberFieldFinitePlaceArtinEulerReciprocalProduct
    (K := (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L)) (L := L)
    (linearCharacterLine q.2) s

/-- **Every Artin Euler product is a product of integer powers of abelian Euler products**
over the fixed fields of Brauer-elementary subgroups, for `Re s > 1`. -/
theorem exists_artinEulerProduct_eq_prod_zpow_abelian (ρ : Representation ℂ G V) :
    ∃ n : brauerElementaryMonomialIndex G →₀ ℤ, ∀ s : ℂ, 1 < s.re →
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
        n.prod fun q k => brauerAbelianEulerProduct K L q s ^ k := by
  -- Brauer: the character of `ρ` is an integer combination of monomial characters
  have hmem : (⟨ρ.character, AddSubgroup.subset_closure
      (representation_character_mem_fdCharacterSet G ρ)⟩ : VirtualCharacter G) ∈
      AddSubgroup.closure (Set.range (brauerElementaryMonomialVirtualCharacter G)) := by
    rw [brauer_induction]
    exact AddSubgroup.mem_top _
  obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_range_iff.mp hmem
  refine ⟨n, fun s hs => ?_⟩
  -- the induced representations of the lines
  let τ : ∀ q : brauerElementaryMonomialIndex G, Representation ℂ G
      (Representation.IndV q.1.subgroup.subtype (linearCharacterLine q.2)) :=
    fun q => Representation.ind q.1.subgroup.subtype (linearCharacterLine q.2)
  have hτ : ∀ q, (τ q).character =
      inducedFunction q.1.subgroup (linearCharacterLine q.2).character :=
    fun q => induced_character_eq_inducedFunction q.1.subgroup (linearCharacterLine q.2)
  have hchar : ρ.character = ∑ q ∈ n.support, n q • (τ q).character := by
    have h := congrArg (virtualCharacterGroup G).subtype hn
    simp only [Finsupp.sum, map_sum, map_zsmul, AddSubgroup.coe_subtype] at h
    rw [h]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hτ q, linearCharacterLine_character]
    exact congrArg _ (monomialVirtualCharacter_val q.1.subgroup q.2)
  rw [numberFieldFinitePlaceArtinEulerReciprocalProduct_eq_prod_zpow n.support n ρ τ hchar hs,
    Finsupp.prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  congr 1
  exact numberFieldFinitePlaceArtinEulerReciprocalProduct_induced
    (M := (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L))
    q.1.subgroup (τ q) (linearCharacterLine q.2) (hτ q) hs

end GaloisForLFunctions
