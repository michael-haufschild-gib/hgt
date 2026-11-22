import GaloisForLFunctions.HeckeLFunctions.EveryRayResidueAndSignHasAnIntegralRepresentative
import GaloisForLFunctions.HeckeLFunctions.ConePointsOfARayClassAreLatticeCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.IntegerModulus

/-! Integral representatives of the native ray class group at an integer modulus. -/

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open GaloisForLFunctions.HeckeLFunctions
open scoped Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.Mem

structure RayData (K : Type) [Field K] [NumberField K] (M : ℕ) where
  ne_zero : M ≠ 0

theorem rayData (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : M ≠ 0) : RayData K M := ⟨hM⟩

namespace RayData

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)

def modulus : Modulus K where
  fin := Ideal.span {(M : 𝓞 K)}
  fin_ne_bot := fun h => (Nat.cast_ne_zero.mpr D.ne_zero) (Ideal.span_singleton_eq_bot.mp h)
  inf := ∅

abbrev G : Type := RayClassGroup D.modulus

noncomputable instance fin : Fintype D.G := Fintype.ofFinite _

def cls (I : Ideal (𝓞 K)) : D.G :=
  if h₀ : I ≠ ⊥ then
    if hI : IsCoprime I (Ideal.span {(M : 𝓞 K)}) then
      rayClass D.modulus ⟨idealUnit h₀, (idealUnit_mem_idealGroup_iff D.modulus h₀).mpr hI.sup_eq⟩
    else 1
  else 1

theorem cls_of {I : Ideal (𝓞 K)} (h₀ : I ≠ ⊥) (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) :
    D.cls I =
      rayClass D.modulus ⟨idealUnit h₀, (idealUnit_mem_idealGroup_iff D.modulus h₀).mpr hI.sup_eq⟩ := by
  simp only [cls, dif_pos h₀, dif_pos hI]

theorem cls_mul (I J : Ideal (𝓞 K)) (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)}))
    (hJ : IsCoprime J (Ideal.span {(M : 𝓞 K)})) (hI₀ : I ≠ ⊥) (hJ₀ : J ≠ ⊥) :
    D.cls (I * J) = D.cls I * D.cls J := by
  rw [D.cls_of (mul_ne_zero hI₀ hJ₀) (hI.mul_left hJ), D.cls_of hI₀ hI, D.cls_of hJ₀ hJ, ← map_mul]
  congr 1
  exact Subtype.ext (idealUnit_mul hI₀ hJ₀)

theorem cls_top : D.cls (⊤ : Ideal (𝓞 K)) = 1 := by
  have hcop : IsCoprime (⊤ : Ideal (𝓞 K)) (Ideal.span {(M : 𝓞 K)}) :=
    Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)
  rw [D.cls_of top_ne_bot hcop, ← (rayClass D.modulus).map_one]
  apply congrArg (rayClass D.modulus)
  apply Subtype.ext
  apply Units.ext
  change (idealUnit (K := K) (I := ⊤) top_ne_bot).val = 1
  rw [coe_idealUnit, coeIdeal_top]

theorem cls_one : D.cls (1 : Ideal (𝓞 K)) = 1 := by rw [Ideal.one_eq_top, D.cls_top]

theorem ne_bot_of_coprime (hM : 2 ≤ M) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  have h := hI.sup_eq
  rw [bot_sup_eq] at h
  exact Ideal.span_natCast_not_top_le K M (by omega) (ge_of_eq h)

theorem cls_mul_of_two_le (hM : 2 ≤ M) {I J : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hJ : IsCoprime J (Ideal.span {(M : 𝓞 K)})) :
    D.cls (I * J) = D.cls I * D.cls J :=
  D.cls_mul I J hI hJ (ne_bot_of_coprime hM hI) (ne_bot_of_coprime hM hJ)

private theorem cls_span_eq {a : 𝓞 K} (ha : algebraMap (𝓞 K) K a ≠ 0)
    (h : Units.mk0 (algebraMap (𝓞 K) K a) ha ∈ primeToUnits D.modulus) :
    D.cls (Ideal.span {a}) =
      rayClassOfElt D.modulus ⟨Units.mk0 (algebraMap (𝓞 K) K a) ha, h⟩ := by
  have hzero : Ideal.span {a} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (fun hz => ha (by simp [hz]))
  have he := idealUnit_span_eq ha hzero
  have hun : idealUnit hzero ∈ idealGroup D.modulus := by
    rw [he, toPrincipalIdeal_mem_idealGroup_iff]
    exact h
  have hcop : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) :=
    Ideal.isCoprime_iff_sup_eq.mpr ((idealUnit_mem_idealGroup_iff D.modulus hzero).mp hun)
  refine (D.cls_of hzero hcop).trans ?_
  exact congrArg (rayClass D.modulus) (Subtype.ext he)

private theorem nonmem_of_prime_to {a : 𝓞 K} {ha : algebraMap (𝓞 K) K a ≠ 0}
    (h : Units.mk0 _ ha ∈ primeToUnits D.modulus) :
    ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ D.modulus.fin → a ∉ v.asIdeal := by
  intro v hv hmem
  have hval := h v hv
  rw [Units.val_mk0, valuation_of_algebraMap] at hval
  exact ((intValuation_lt_one_iff_mem v a).mpr hmem).ne hval

/-- A principal integral ideal lies in the identity ray class precisely when it has a generator
congruent to one at the finite modulus. -/
theorem cls_eq_one_iff {I : Ideal (𝓞 K)} (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)}))
    (hI₀ : I ≠ ⊥) :
    D.cls I = 1 ↔ ∃ a : 𝓞 K, I = Ideal.span {a} ∧ a - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
  constructor
  · intro hr
    rw [D.cls_of hI₀ hI, rayClass, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hr
    obtain ⟨α, ⟨α', hα', rfl⟩, hα⟩ := hr
    have hspan : spanSingleton (𝓞 K)⁰ (α'.val : K) = (I : FractionalIdeal (𝓞 K)⁰ K) := by
      have h := congrArg Units.val hα
      rwa [coe_toPrincipalIdeal, coe_idealUnit] at h
    have hmem : (α'.val : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← hspan]
      exact mem_spanSingleton_self (𝓞 K)⁰ (α'.val : K)
    obtain ⟨a, -, ha⟩ := (mem_coeIdeal (𝓞 K)⁰).mp hmem
    have ha₀ : algebraMap (𝓞 K) K a ≠ 0 := fun h => Units.ne_zero _ (ha.symm.trans h)
    have he : Units.mk0 _ ha₀ = α'.val := Units.ext ha
    have hprime := D.nonmem_of_prime_to (he.symm ▸ α'.2)
    have ht : (⟨Units.mk0 _ ha₀, mk0_mem_primeToUnits D.modulus ha₀ hprime⟩ : primeToUnits D.modulus) = α' :=
      Subtype.ext he
    change rayHom D.modulus α' = 1 at hα'
    rw [← ht, rayHom_algebraMap D.modulus ha₀ hprime] at hα'
    have hmod : Ideal.Quotient.mk D.modulus.fin a = 1 := by
      have h := congrArg (fun u => (u.1 : (𝓞 K) ⧸ D.modulus.fin)) hα'
      simpa only [coe_unitMod, Prod.fst_one, Units.val_one] using h
    refine ⟨a, ?_, ?_⟩
    · apply (coeIdeal_injective (R := 𝓞 K) (K := K))
      change (I : FractionalIdeal (𝓞 K)⁰ K) = ↑(Ideal.span {a})
      rw [coeIdeal_span_singleton, ha, hspan]
    · change a - 1 ∈ D.modulus.fin
      apply Ideal.Quotient.eq.mp
      rw [map_one]
      exact hmod
  · rintro ⟨a, rfl, ha⟩
    have ha₀ : a ≠ 0 := fun h => hI₀ (by simp [h])
    have haK : algebraMap (𝓞 K) K a ≠ 0 := fun h => ha₀ (RingOfIntegers.coe_injective (by simpa using h))
    have hmod : Ideal.Quotient.mk D.modulus.fin a = 1 := by
      rw [← (Ideal.Quotient.mk D.modulus.fin).map_one]
      exact Ideal.Quotient.eq.mpr (show a - 1 ∈ D.modulus.fin from ha)
    have hprime : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ D.modulus.fin → a ∉ v.asIdeal :=
      fun v hv => not_mem_of_isUnit_mk D.modulus (hmod.symm ▸ isUnit_one) v hv
    let α : primeToUnits D.modulus := ⟨_, mk0_mem_primeToUnits D.modulus haK hprime⟩
    have hα : rayHom D.modulus α = 1 := by
      change rayHom D.modulus ⟨_, mk0_mem_primeToUnits D.modulus haK hprime⟩ = 1
      rw [rayHom_algebraMap D.modulus haK hprime]
      apply Prod.ext
      · apply Units.ext
        change (unitMod D.modulus hprime : 𝓞 K ⧸ D.modulus.fin) = 1
        exact (coe_unitMod D.modulus hprime).trans hmod
      · funext w
        exact False.elim w.2
    exact (D.cls_span_eq haK α.2).trans
      (MonoidHom.mem_ker.mp (ker_rayHom_le D.modulus (MonoidHom.mem_ker.mpr hα)))

theorem cls_span {a : 𝓞 K} (ha : a ≠ 0) (h : a - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    D.cls (Ideal.span {a}) = 1 := by
  have hcop : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
    have hone : (1 : 𝓞 K) = a - (a - 1) := by ring
    rw [hone]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right h)
  exact (D.cls_eq_one_iff hcop (Ideal.span_singleton_eq_bot.not.mpr ha)).mpr ⟨a, rfl, h⟩

theorem cls_surj (c : D.G) :
    ∃ I : Ideal (𝓞 K), IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ I ≠ ⊥ ∧ D.cls I = c := by
  obtain ⟨B, hB₀, hBcop, hB⟩ := exists_integral_rep D.modulus (toClassGroup D.modulus c)
  have hBc : IsCoprime B (Ideal.span {(M : 𝓞 K)}) := Ideal.isCoprime_iff_sup_eq.mpr hBcop
  have hBcls : toClassGroup D.modulus (D.cls B) = toClassGroup D.modulus c := by
    rw [D.cls_of hB₀ hBc, toClassGroup_rayClass, hB]
  have hprod : toClassGroup D.modulus (c * (D.cls B)⁻¹) = 1 := by
    rw [map_mul, map_inv, hBcls, mul_inv_cancel]
  obtain ⟨α, hα⟩ := ker_toClassGroup_le D.modulus _ hprod
  obtain ⟨a, h₀, hres, -⟩ := exists_integral_residue_sign D.modulus (rayHom D.modulus α)
  have hprime : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ D.modulus.fin → a ∉ v.asIdeal :=
    fun v hv => not_mem_of_isUnit_mk D.modulus (hres.symm ▸ (rayHom D.modulus α).1.isUnit) v hv
  let β : primeToUnits D.modulus := ⟨_, mk0_mem_primeToUnits D.modulus h₀ hprime⟩
  have hdata : rayHom D.modulus β = rayHom D.modulus α := by
    change rayHom D.modulus ⟨_, mk0_mem_primeToUnits D.modulus h₀ hprime⟩ = _
    rw [rayHom_algebraMap D.modulus h₀ hprime]
    refine Prod.ext (Units.ext ((coe_unitMod D.modulus hprime).trans hres)) ?_
    funext w
    exact False.elim w.2
  have hβ : rayClassOfElt D.modulus β = rayClassOfElt D.modulus α := by
    rw [← rayResidueClass_apply D.modulus β, ← rayResidueClass_apply D.modulus α]
    exact congrArg (rayResidueClass D.modulus) (Subtype.ext hdata)
  have hzero : Ideal.span {a} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (fun h => h₀ (by simp [h]))
  have hcop : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (idealUnit_mem_idealGroup_iff D.modulus hzero).mp
    rw [idealUnit_span_eq h₀ hzero, toPrincipalIdeal_mem_idealGroup_iff]
    exact β.2
  refine ⟨Ideal.span {a} * B, hcop.mul_left hBc, mul_ne_zero hzero hB₀, ?_⟩
  rw [D.cls_mul _ _ hcop hBc hzero hB₀, D.cls_span_eq h₀ β.2, hβ, hα, mul_assoc, inv_mul_cancel, mul_one]

end RayData

end GlobalTheory.Mem
