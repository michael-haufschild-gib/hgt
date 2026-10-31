import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCompletedPoleReduction
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticFiniteApproximation
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticIntegralClosure

/-!
# The simple-pole additive domain of the elliptic adeles

Finite approximation and completed pole reduction give representatives in
the affine pole gap. Finite integrality and the absence of an affine simple
pole make the representative unique.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open IsDedekindDomain
open scoped WithZero WithZeroMulInt
noncomputable section

/-- Constants in the completed infinity field. -/
def infinityConstant : Constants →+ InfinityCompletion :=
  (infinityEmbedding.comp (algebraMap Constants K)).toAddMonoidHom

/-- The constant coefficient of the unique missing affine pole order. -/
def infinitySimplePole : Constants →+ InfinityCompletion where
  toFun c := infinityConstant c * infinityEmbedding ((x / y) ^ (-1 : ℤ))
  map_zero' := by simp only [map_zero, zero_mul]
  map_add' c d := by rw [map_add, add_mul]

theorem infinitySimplePole_valuation {c : Constants} (hc : c ≠ 0) :
    Valued.v (infinitySimplePole c) = WithZero.exp (1 : ℤ) := by
  change Valued.v (infinityEmbedding (algebraMap Constants K c) *
    infinityEmbedding ((x / y) ^ (-1 : ℤ))) = _
  rw [map_mul, completedInfinity_constant_valuation c hc, one_mul,
    infinityEmbedding_valuation, infinityValuation_parameter_zpow]
  rfl

/-- The maximal ideal of the completed infinity integers, as an additive group. -/
def infinitySmall : AddSubgroup InfinityCompletion := Valued.v.ltAddSubgroup 1

/-- A simple-pole coefficient and a strictly positive valuation remainder. -/
def infinityGap : AddSubgroup InfinityCompletion where
  carrier := {z | ∃ c : Constants, z - infinitySimplePole c ∈ infinitySmall}
  zero_mem' := ⟨0, by simpa only [map_zero, sub_zero] using infinitySmall.zero_mem⟩
  add_mem' := by
    rintro z w ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact infinitySmall.add_mem hc hd
  neg_mem' := by
    rintro z ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    rw [map_neg, neg_sub_neg]
    simpa only [neg_sub] using infinitySmall.neg_mem hc

theorem infinityGap_valuation_le {z : InfinityCompletion} (hz : z ∈ infinityGap) :
    Valued.v z ≤ WithZero.exp (1 : ℤ) := by
  obtain ⟨c, hc⟩ := hz
  have hsmall : Valued.v (z - infinitySimplePole c) < 1 := hc
  have hone : (1 : ℤᵐ⁰) < WithZero.exp (1 : ℤ) := by
    change WithZero.exp (0 : ℤ) < WithZero.exp (1 : ℤ)
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hpole : Valued.v (infinitySimplePole c) ≤ WithZero.exp (1 : ℤ) := by
    by_cases hc : c = 0
    · simp only [hc, map_zero]; exact bot_le
    · exact (infinitySimplePole_valuation hc).le
  calc
    Valued.v z = Valued.v ((z - infinitySimplePole c) + infinitySimplePole c) := by
      rw [sub_add_cancel]
    _ ≤ max (Valued.v (z - infinitySimplePole c)) (Valued.v (infinitySimplePole c)) :=
      Valued.v.map_add _ _
    _ ≤ _ := max_le (hsmall.le.trans hone.le) hpole

theorem infinityGap_integral_mem_small {z : InfinityCompletion}
    (hz : z ∈ infinityGap) (hregular : Valued.v z ≤ 1) : z ∈ infinitySmall := by
  obtain ⟨c, hc⟩ := hz
  have hsmall : Valued.v (z - infinitySimplePole c) < 1 := hc
  have hc0 : c = 0 := by
    by_contra hc0
    have hval : Valued.v (infinitySimplePole c) ≤ 1 := by
      calc
        _ = Valued.v (z + -(z - infinitySimplePole c)) := by congr 1; abel
        _ ≤ max (Valued.v z) (Valued.v (-(z - infinitySimplePole c))) := Valued.v.map_add _ _
        _ ≤ 1 := by rw [Valuation.map_neg]; exact max_le hregular hsmall.le
    rw [infinitySimplePole_valuation hc0] at hval
    have : WithZero.exp (1 : ℤ) ≤ WithZero.exp (0 : ℤ) := hval
    have := WithZero.exp_le_exp.mp this
    omega
  simpa only [hc0, map_zero, sub_zero] using hc

/-- All finite local integers as an additive subgroup. -/
def finiteIntegral : AddSubgroup FiniteAdeles where
  carrier := integralFiniteAdeles
  zero_mem' := zero_mem_integralFiniteAdeles
  add_mem' ha hb v := add_mem (ha v) (hb v)
  neg_mem' ha v := neg_mem (ha v)

/-- The additive representatives determined by the simple-pole gap. -/
def ellipticAdditiveDomain : AddSubgroup Adeles := finiteIntegral.prod infinityGap

theorem finiteAdeleEmbedding_affine_mem (a : A) :
    finiteAdeleEmbedding (algebraMap A K a) ∈ finiteIntegral := by
  rw [← coordinateRingEquivRingOfIntegers_algebraMap]
  intro v
  change algebraMap K (v.adicCompletion K)
    (algebraMap RingOfIntegers K (coordinateRingEquivRingOfIntegers a)) ∈ _
  rw [← IsScalarTower.algebraMap_apply]
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v _

/-- Every adelic class has a representative in the explicit gap domain. -/
theorem adele_exists_gap_representative (a : Adeles) :
    ∃ z : K, a - adeleEmbedding z ∈ ellipticAdditiveDomain := by
  obtain ⟨z, hz⟩ := finiteAdele_exists_integral_difference a.1
  obtain ⟨b, c, hc⟩ :=
    completedInfinity_affine_simplePole_remainder (a.2 - infinityEmbedding z)
  refine ⟨z + algebraMap A K b, ?_, c, ?_⟩
  · change a.1 - finiteAdeleEmbedding (z + algebraMap A K b) ∈ finiteIntegral
    rw [map_add, ← sub_sub]
    exact finiteIntegral.sub_mem hz (finiteAdeleEmbedding_affine_mem b)
  · change Valued.v (a.2 - infinityEmbedding (z + algebraMap A K b) -
      infinitySimplePole c) < 1
    rw [map_add, ← sub_sub]
    exact hc

/-- Finite integrality recovers the actual affine coordinate ring. -/
theorem exists_affine_of_finiteAdeleEmbedding_mem {z : K}
    (hz : finiteAdeleEmbedding z ∈ finiteIntegral) :
    ∃ a : A, algebraMap A K a = z := by
  have hv (v : FinitePlace) : v.valuation K z ≤ 1 := by
    have h := hz v
    change Valued.v (algebraMap K (v.adicCompletion K) z) ≤ 1 at h
    have he : Valued.v (algebraMap K (v.adicCompletion K) z) = v.valuation K z :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) z
    rwa [he] at h
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K z hv
  refine ⟨coordinateRingEquivRingOfIntegers.symm b, ?_⟩
  rw [← coordinateRingEquivRingOfIntegers_algebraMap,
    coordinateRingEquivRingOfIntegers.apply_symm_apply]
  exact hb

/-- No nonzero diagonal function lies in the simple-pole domain. -/
theorem adeleEmbedding_mem_gap_eq_zero {z : K}
    (hz : adeleEmbedding z ∈ ellipticAdditiveDomain) : z = 0 := by
  obtain ⟨a, rfl⟩ := exists_affine_of_finiteAdeleEmbedding_mem hz.1
  have hv := infinityGap_valuation_le hz.2
  change Valued.v (infinityEmbedding (algebraMap A K a)) ≤ WithZero.exp (1 : ℤ) at hv
  rw [infinityEmbedding_valuation, infinityValuation_algebraMap] at hv
  have hdegree : poleDegree a ≤ 1 := by
    change (poleDegree a).map (Nat.castAddMonoidHom ℤ) ≤ (↑(1 : ℤ) : WithBot ℤ) at hv
    generalize poleDegree a = d at hv ⊢
    cases d with
    | bot => exact bot_le
    | coe n =>
      change ((n : ℤ) : WithBot ℤ) ≤ ((1 : ℤ) : WithBot ℤ) at hv
      have hn : (n : ℤ) ≤ 1 := WithBot.coe_le_coe.mp hv
      change (↑n : WithBot ℕ) ≤ ((1 : ℕ) : WithBot ℕ)
      apply WithBot.coe_le_coe.mpr
      exact_mod_cast hn
  obtain ⟨c, rfl⟩ := (poleDegree_le_one_iff a).mp hdegree
  rw [← IsScalarTower.algebraMap_apply Constants A K] at hz ⊢
  by_cases hc : c = 0
  · rw [hc, map_zero]
  · have hregular : Valued.v (infinityEmbedding (algebraMap Constants K c)) ≤ 1 :=
      (completedInfinity_constant_valuation c hc).le
    have hsmall := infinityGap_integral_mem_small hz.2 hregular
    change Valued.v (infinityEmbedding (algebraMap Constants K c)) < 1 at hsmall
    rw [completedInfinity_constant_valuation c hc] at hsmall
    exact (lt_irrefl _ hsmall).elim

/-- Every adele has exactly one diagonal translate in the explicit domain. -/
theorem adele_existsUnique_gap_representative (a : Adeles) :
    ∃! z : K, a - adeleEmbedding z ∈ ellipticAdditiveDomain := by
  obtain ⟨z, hz⟩ := adele_exists_gap_representative a
  refine ⟨z, hz, fun w hw => ?_⟩
  have hd := ellipticAdditiveDomain.sub_mem hz hw
  have heq : (a - adeleEmbedding z) - (a - adeleEmbedding w) =
      adeleEmbedding (w - z) := by rw [map_sub]; abel
  rw [heq] at hd
  exact sub_eq_zero.mp (adeleEmbedding_mem_gap_eq_zero hd)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adele_exists_gap_representative
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adele_existsUnique_gap_representative
