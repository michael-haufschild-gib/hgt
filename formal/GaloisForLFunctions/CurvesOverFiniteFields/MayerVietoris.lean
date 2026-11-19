import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two-subspace Euler characteristics

For subspaces `M ≤ N` and `U` of a vector space `V` with `N/M` finite-dimensional, the sequence
`0 → (N ⊓ U)/(M ⊓ U) → N/M → (N ⊔ U)/(M ⊔ U) → 0` is exact, so
`dim N/M = dim (N ⊓ U)/(M ⊓ U) + dim (N ⊔ U)/(M ⊔ U)` (`finrank_quot_eq_add`).
This is the Mayer–Vietoris step behind the Euler characteristic
`χ = dim (M ⊓ U) − dim V/(M ⊔ U)` of a two-chart cover.
-/

noncomputable section

namespace GaloisForLFunctions.CurvesOverFiniteFields

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The quotient `B/A` of two subspaces of `V`, as a module. -/
abbrev subQuot (A B : Submodule F V) : Type _ := B ⧸ A.comap B.subtype

/-- The inclusion `(N ⊓ U) → N/M`. -/
def infToQuot (M N U : Submodule F V) : ↥(N ⊓ U) →ₗ[F] subQuot M N :=
  (M.comap N.subtype).mkQ.comp (Submodule.inclusion inf_le_left)

/-- The map `N → (N ⊔ U)/(M ⊔ U)`. -/
def toSupQuot (M N U : Submodule F V) : ↥N →ₗ[F] subQuot (M ⊔ U) (N ⊔ U) :=
  ((M ⊔ U).comap (N ⊔ U).subtype).mkQ.comp (Submodule.inclusion le_sup_left)

theorem toSupQuot_surjective (M N U : Submodule F V) : Function.Surjective (toSupQuot M N U) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨n, hn, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
  refine ⟨⟨n, hn⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  change n - (n + u) ∈ M ⊔ U
  rw [show n - (n + u) = -u by abel]
  exact Submodule.neg_mem _ (Submodule.mem_sup_right hu)

theorem ker_toSupQuot {M N U : Submodule F V} (hMN : M ≤ N) :
    LinearMap.ker (toSupQuot M N U) = (M ⊔ (N ⊓ U)).comap N.subtype := by
  ext ⟨x, hx⟩
  simp only [LinearMap.mem_ker, toSupQuot, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, Submodule.coe_inclusion]
  constructor
  · intro h
    obtain ⟨m, hm, u, hu, hmu⟩ := Submodule.mem_sup.mp h
    refine Submodule.mem_sup.mpr ⟨m, hm, u, ⟨?_, hu⟩, hmu⟩
    have : u = x - m := by rw [← hmu]; abel
    rw [this]
    exact Submodule.sub_mem _ hx (hMN hm)
  · intro h
    obtain ⟨m, hm, u, hu, hmu⟩ := Submodule.mem_sup.mp h
    exact Submodule.mem_sup.mpr ⟨m, hm, u, hu.2, hmu⟩

/-- The map `N/M → (N ⊔ U)/(M ⊔ U)`. -/
def quotToSupQuot {M N : Submodule F V} (hMN : M ≤ N) (U : Submodule F V) :
    subQuot M N →ₗ[F] subQuot (M ⊔ U) (N ⊔ U) :=
  (M.comap N.subtype).liftQ (toSupQuot M N U) (by
    rw [ker_toSupQuot hMN]
    exact Submodule.comap_mono le_sup_left)

theorem quotToSupQuot_surjective {M N : Submodule F V} (hMN : M ≤ N) (U : Submodule F V) :
    Function.Surjective (quotToSupQuot hMN U) := by
  intro y
  obtain ⟨x, rfl⟩ := toSupQuot_surjective M N U y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem ker_quotToSupQuot {M N : Submodule F V} (hMN : M ≤ N) (U : Submodule F V) :
    LinearMap.ker (quotToSupQuot hMN U) = LinearMap.range (infToQuot M N U) := by
  ext y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  rw [LinearMap.mem_ker]
  change toSupQuot M N U x = 0 ↔ _
  rw [← LinearMap.mem_ker, ker_toSupQuot hMN, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · intro h
    obtain ⟨m, hm, u, hu, hmu⟩ := Submodule.mem_sup.mp h
    refine ⟨⟨u, hu⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    change u - x.1 ∈ M
    rw [show u - x.1 = -m by rw [← hmu]; abel]
    exact Submodule.neg_mem _ hm
  · rintro ⟨⟨u, hu⟩, hux⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hux
    rw [Submodule.Quotient.eq] at hux
    change u - x.1 ∈ M at hux
    refine Submodule.mem_sup.mpr ⟨-(u - x.1), Submodule.neg_mem _ hux, u, hu, by abel⟩

theorem ker_infToQuot (M N U : Submodule F V) :
    LinearMap.ker (infToQuot M N U) = (M ⊓ U).comap (N ⊓ U).subtype := by
  ext ⟨x, hx⟩
  simp only [LinearMap.mem_ker, infToQuot, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, Submodule.coe_inclusion, Submodule.mem_inf]
  exact ⟨fun h => ⟨h, hx.2⟩, fun h => h.1⟩

/-- `(N ⊓ U)/(M ⊓ U)` is the range of `N ⊓ U → N/M`. -/
def subQuotInfEquivRange (M N U : Submodule F V) :
    subQuot (M ⊓ U) (N ⊓ U) ≃ₗ[F] LinearMap.range (infToQuot M N U) :=
  (Submodule.quotEquivOfEq _ _ (ker_infToQuot M N U).symm).trans
    (infToQuot M N U).quotKerEquivRange

/-- **Mayer–Vietoris step**: `dim N/M = dim (N ⊓ U)/(M ⊓ U) + dim (N ⊔ U)/(M ⊔ U)`. -/
theorem finrank_quot_eq_add {M N : Submodule F V} (hMN : M ≤ N) (U : Submodule F V)
    [FiniteDimensional F (subQuot M N)] :
    Module.finrank F (subQuot M N) =
      Module.finrank F (subQuot (M ⊓ U) (N ⊓ U)) + Module.finrank F (subQuot (M ⊔ U) (N ⊔ U)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (quotToSupQuot hMN U)
  rw [LinearMap.range_eq_top.mpr (quotToSupQuot_surjective hMN U), finrank_top,
    ker_quotToSupQuot] at hrn
  rw [(subQuotInfEquivRange M N U).finrank_eq]
  omega

theorem finiteDimensional_subQuot_inf {M N : Submodule F V} (U : Submodule F V)
    [FiniteDimensional F (subQuot M N)] : FiniteDimensional F (subQuot (M ⊓ U) (N ⊓ U)) :=
  Module.Finite.equiv (subQuotInfEquivRange M N U).symm

theorem finiteDimensional_subQuot_sup {M N : Submodule F V} (hMN : M ≤ N) (U : Submodule F V)
    [FiniteDimensional F (subQuot M N)] : FiniteDimensional F (subQuot (M ⊔ U) (N ⊔ U)) :=
  Module.Finite.of_surjective _ (quotToSupQuot_surjective hMN U)

end GaloisForLFunctions.CurvesOverFiniteFields
