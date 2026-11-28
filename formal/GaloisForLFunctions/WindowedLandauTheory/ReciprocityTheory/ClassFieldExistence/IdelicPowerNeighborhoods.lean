import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDeepRoots
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.CompactIdelicClassQuotient

/-! Open idelic neighbourhoods with integral coordinates away from one
place and prescribed local power classes at finitely many places. -/

noncomputable section

open NumberField IsDedekindDomain Topology Filter
open scoped RestrictedProduct

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K : Type} [Field K] [NumberField K]

/-- The subgroup of n-th powers in the compact idele class quotient. -/
def compactIdelePowers (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Subgroup (CompactIdeleClassQuotient K) :=
  (powMonoidHom (α := CompactIdeleClassQuotient K) n).range

theorem isOpen_range_pow_finiteCompletion (w : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : n ≠ 0) :
    IsOpen ((powMonoidHom n : (w.adicCompletion K)ˣ →* _).range :
      Set (w.adicCompletion K)ˣ) := by
  obtain ⟨s, -, -, hs⟩ := exists_unitsLevel_pow_roots w n hn
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  exact Filter.mem_of_superset ((isOpen_unitsLevel w s).mem_nhds (one_mem _)) fun x hx => by
    obtain ⟨y, -, hy⟩ := hs x hx
    exact ⟨y, hy⟩

theorem isOpen_ord_zero_away (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen {a : IdeleGroup K | ∀ w, w ≠ v → ord w a = 0} := by
  let U : Set (FiniteAdeleRing (𝓞 K) K) := {a | ∀ w, w ≠ v → a w ∈ w.adicCompletionIntegers K}
  have hU : IsOpen U :=
    RestrictedProduct.isOpen_forall_imp_mem (fun w => Valued.isOpen_valuationSubring _)
      (p := fun w => w ≠ v)
  let f (a : IdeleGroup K) : FiniteAdeleRing (𝓞 K) K := (a : AdeleRing (𝓞 K) K).2
  have hf : Continuous f := continuous_snd.comp Units.continuous_val
  have he : {a : IdeleGroup K | ∀ w, w ≠ v → ord w a = 0} = f ⁻¹' U ∩ (fun a => f a⁻¹) ⁻¹' U := by
    ext a
    constructor
    · intro ha
      exact ⟨fun w hw => ((ord_eq_zero_iff w a).mp (ha w hw)).1,
        fun w hw => ((ord_eq_zero_iff w a).mp (ha w hw)).2⟩
    · intro ha w hw
      exact (ord_eq_zero_iff w a).mpr ⟨ha.1 w hw, ha.2 w hw⟩
  rw [he]
  exact (hU.preimage hf).inter (hU.preimage (hf.comp continuous_inv))

theorem exists_diagonal_arch_mul_pow_mem_of_class_mem_closure_powers
    {n : ℕ} {x : IdeleGroup K}
    (hx : toCompactIdeleClassQuotient K x ∈ (compactIdelePowers K n).topologicalClosure)
    {U : Set (IdeleGroup K)} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (a : Kˣ) (c z : IdeleGroup K), c ∈ archPositive K ∧ (diagonal K a * c) * z ^ n ∈ U := by
  let q := toCompactIdeleClassQuotient K
  let P := compactIdelePowers K n
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hcl : x ∈ closure (q ⁻¹' (P : Set (CompactIdeleClassQuotient K))) := by
    rw [← hqo.preimage_closure_eq_closure_preimage hq]
    exact hx
  obtain ⟨y, hyU, hyP⟩ := mem_closure_iff.mp hcl U hU hxU
  change q y ∈ P at hyP
  obtain ⟨z', hz'⟩ := hyP
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective ((diagonal K).range ⊔ archPositive K) z'
  change q z ^ n = q y at hz'
  have h : y / z ^ n ∈ (diagonal K).range ⊔ archPositive K := by
    apply (QuotientGroup.eq_one_iff (y / z ^ n)).mp
    change q (y / z ^ n) = 1
    rw [map_div, map_pow, hz', div_self']
  obtain ⟨_, ⟨a, rfl⟩, c, hc, he⟩ := Subgroup.mem_sup.mp h
  refine ⟨a, c, z, hc, ?_⟩
  rwa [he, div_mul_cancel]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.isOpen_range_pow_finiteCompletion
#print axioms GlobalTheory.Reciprocity.isOpen_ord_zero_away
#print axioms GlobalTheory.Reciprocity.exists_diagonal_arch_mul_pow_mem_of_class_mem_closure_powers
