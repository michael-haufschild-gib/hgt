import GaloisForLFunctions.HTGeometry.CyclotomicNumberFieldBoxBasis
import GaloisForLFunctions.HTGeometry.CyclotomicTailPhaseHypertranscendence

/-!
# Number-field robust cyclotomic tail freedom

Every finite rational coefficient field preserves bounded-total-degree independence in a
sufficiently high prime-cyclotomic tail.  Required cutoff depends on coefficient-field degree and
degree bound, while conclusion is uniform over every finite relation beyond that cutoff.
-/

open Filter
open scoped IntermediateField Topology

namespace GaloisForLFunctions

noncomputable section

def BoundedTotalDegreeTailFreedomOver
    (k : IntermediateField ℚ ℂ) (u : ℕ → ℂ) : Prop :=
  ∀ D, 0 < D → ∃ M,
    LinearIndependent ↥(k ⊔ HTGeometry.cyclotomicAdjoin (Finset.range M) u)
      (fun ν : BoundedTailExponent M D => atomPhase u ν.1)

def NumberFieldRobustBoundedTotalDegreeTailFreedom (u : ℕ → ℂ) : Prop :=
  ∀ (k : IntermediateField ℚ ℂ),
    ∀ (_ : FiniteDimensional ℚ k), BoundedTotalDegreeTailFreedomOver k u

theorem linearIndependent_boundedTailExponent_prime_over_numberField
    (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    {q : ℕ → ℕ} {u : ℕ → ℂ} (M D : ℕ)
    (hprime : ∀ i, Nat.Prime (q i))
    (hqinj : Function.Injective q)
    (hu : ∀ i, IsPrimitiveRoot (u i) (q i))
    (hlarge : ∀ i, M ≤ i → Module.finrank ℚ k * D + 1 < q i) :
    LinearIndependent ↥(k ⊔ HTGeometry.cyclotomicAdjoin (Finset.range M) u)
      (fun ν : BoundedTailExponent M D => atomPhase u ν.1) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  let S : Finset ℕ := l.support.biUnion fun ν => ν.1.support
  have hSge : ∀ i ∈ S, M ≤ i := by
    intro i hi
    obtain ⟨ν, hνl, hiν⟩ := Finset.mem_biUnion.mp hi
    exact ν.2.1 i hiν
  have hdisj : Disjoint (Finset.range M) S := by
    rw [Finset.disjoint_left]
    intro i hip hiS
    exact (Nat.not_lt_of_ge (hSge i hiS)) (Finset.mem_range.mp hip)
  have hqpos : ∀ i ∈ Finset.range M ∪ S, 0 < q i := by
    intro i hi
    exact (hprime i).pos
  have huall : ∀ i ∈ Finset.range M ∪ S, IsPrimitiveRoot (u i) (q i) := by
    intro i hi
    exact hu i
  have hcop : ∀ i ∈ Finset.range M ∪ S, ∀ j ∈ Finset.range M ∪ S,
      i ≠ j → Nat.Coprime (q i) (q j) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr
      (fun hq => hij (hqinj hq))
  have hlargeTotient : ∀ i ∈ S,
      Module.finrank ℚ k * D < Nat.totient (q i) := by
    intro i hi
    rw [Nat.totient_prime (hprime i)]
    have hiq := hlarge i (hSge i hi)
    omega
  have hbox := HTGeometry.linearIndependent_boundedCyclotomicBox_over_numberField
    k (Finset.range M) S hdisj D q u hqpos huall hcop hlargeTotient
  let encode : {ν // ν ∈ l.support} → HTGeometry.BoundedCyclotomicBox S D := fun ν i =>
    ⟨ν.1.1 i.1, by
      have hcoord := finsupp_coordinate_le_atomTotalDegree ν.1.1 i.1
      have hdegree := ν.1.2.2
      omega⟩
  have hencode : Function.Injective encode := by
    intro ν μ hνμ
    apply Subtype.ext
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ S
    · let iS : {i // i ∈ S} := ⟨i, hi⟩
      have hcoord := congrFun hνμ iS
      exact congrArg Fin.val hcoord
    · have hν0 : ν.1.1 i = 0 := by
        by_contra hne
        apply hi
        apply Finset.mem_biUnion.mpr
        exact ⟨ν.1, ν.2, Finsupp.mem_support_iff.mpr hne⟩
      have hμ0 : μ.1.1 i = 0 := by
        by_contra hne
        apply hi
        apply Finset.mem_biUnion.mpr
        exact ⟨μ.1, μ.2, Finsupp.mem_support_iff.mpr hne⟩
      rw [hν0, hμ0]
  have hphase (ν : {ν // ν ∈ l.support}) :
      HTGeometry.boundedCyclotomicBoxMonomial S D u (encode ν) =
        atomPhase u ν.1.1 := by
    let ν0 : ℕ →₀ ℕ := ν.1.1
    rw [atomPhase, Finsupp.prod]
    change (∏ i : {i // i ∈ S}, u i.1 ^ ν0 i.1) =
      ∏ i ∈ ν0.support, u i ^ ν0 i
    calc
      (∏ i : {i // i ∈ S}, u i.1 ^ ν0 i.1) =
          ∏ i ∈ S, u i ^ ν0 i := Finset.prod_attach S (fun i => u i ^ ν0 i)
      _ = ∏ i ∈ ν0.support, u i ^ ν0 i := by
        symm
        apply Finset.prod_subset
        · intro i hi
          exact Finset.mem_biUnion.mpr ⟨ν.1, ν.2, hi⟩
        · intro i hiS hiNot
          have hi0 : ν0 i = 0 := by
            by_contra hne
            exact hiNot (Finsupp.mem_support_iff.mpr hne)
          simp [hi0]
  have hLI := hbox.comp encode hencode
  change LinearIndependent ↥(k ⊔ HTGeometry.cyclotomicAdjoin (Finset.range M) u)
    (HTGeometry.boundedCyclotomicBoxMonomial S D u ∘ encode) at hLI
  have hsum : ∑ ν : {ν // ν ∈ l.support},
      l ν.1 • HTGeometry.boundedCyclotomicBoxMonomial S D u (encode ν) = 0 := by
    simp_rw [hphase]
    let f : BoundedTailExponent M D → ℂ := fun ν =>
      l ν • atomPhase u ν.1
    change ∑ ν ∈ l.support.attach, f ν.1 = 0
    calc
      ∑ ν ∈ l.support.attach, f ν.1 = ∑ ν ∈ l.support, f ν :=
        Finset.sum_attach l.support f
      _ = 0 := by
        rw [Finsupp.linearCombination_apply] at hl
        exact hl
  have hallzero := (Fintype.linearIndependent_iff.mp hLI)
    (fun ν : {ν // ν ∈ l.support} => l ν.1) hsum
  apply Finsupp.ext
  intro ν
  by_cases hν : ν ∈ l.support
  · exact hallzero ⟨ν, hν⟩
  · by_contra hne
    exact hν (Finsupp.mem_support_iff.mpr hne)

theorem boundedTotalDegreeTailFreedomOver_of_prime_orders
    (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    {q : ℕ → ℕ} {u : ℕ → ℂ}
    (hprime : ∀ i, Nat.Prime (q i))
    (hqinj : Function.Injective q)
    (hu : ∀ i, IsPrimitiveRoot (u i) (q i))
    (hqtop : Filter.Tendsto q Filter.atTop Filter.atTop) :
    BoundedTotalDegreeTailFreedomOver k u := by
  intro D hD
  have hev : ∀ᶠ i in Filter.atTop,
      Module.finrank ℚ k * D + 1 < q i := by
    exact Filter.tendsto_atTop.1 hqtop (Module.finrank ℚ k * D + 2)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  exact ⟨M, linearIndependent_boundedTailExponent_prime_over_numberField
    k M D hprime hqinj hu (fun i hi => hM i hi)⟩

theorem numberFieldRobustBoundedTotalDegreeTailFreedom_of_prime_orders
    {q : ℕ → ℕ} {u : ℕ → ℂ}
    (hprime : ∀ i, Nat.Prime (q i))
    (hqinj : Function.Injective q)
    (hu : ∀ i, IsPrimitiveRoot (u i) (q i))
    (hqtop : Filter.Tendsto q Filter.atTop Filter.atTop) :
    NumberFieldRobustBoundedTotalDegreeTailFreedom u := by
  intro k hk
  letI : FiniteDimensional ℚ k := hk
  exact boundedTotalDegreeTailFreedomOver_of_prime_orders
    k hprime hqinj hu hqtop

theorem NumberFieldRobustBoundedTotalDegreeTailFreedom.rational
    {u : ℕ → ℂ} (h : NumberFieldRobustBoundedTotalDegreeTailFreedom u) :
    BoundedTotalDegreeTailFreedom u := by
  have hQ : FiniteDimensional ℚ (⊥ : IntermediateField ℚ ℂ) := inferInstance
  have hb := h (⊥ : IntermediateField ℚ ℂ) hQ
  intro D hD
  obtain ⟨M, hM⟩ := hb D hD
  refine ⟨M, ?_⟩
  have heq : (⊥ : IntermediateField ℚ ℂ) ⊔
      HTGeometry.cyclotomicAdjoin (Finset.range M) u =
        HTGeometry.cyclotomicAdjoin (Finset.range M) u := by simp
  rw [heq] at hM
  exact hM

/-- Increasing enumeration of odd primes (`3, 5, 7, ...`). -/
noncomputable def canonicalOddPrimeOrder (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1)

/-- Canonical primitive root whose order is `canonicalOddPrimeOrder n`. -/
noncomputable def canonicalOddPrimePhase (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / canonicalOddPrimeOrder n)

theorem canonicalOddPrimeOrder_prime (n : ℕ) :
    Nat.Prime (canonicalOddPrimeOrder n) :=
  Nat.prime_nth_prime (n + 1)

theorem canonicalOddPrimeOrder_injective : Function.Injective canonicalOddPrimeOrder := by
  intro i j hij
  apply Nat.add_right_cancel (m := 1)
  exact Nat.nth_injective Nat.infinite_setOf_prime hij

theorem canonicalOddPrimeOrder_tendsto_atTop :
    Tendsto canonicalOddPrimeOrder atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro i j hij
  apply Nat.nth_strictMono Nat.infinite_setOf_prime
  omega

theorem canonicalOddPrimePhase_isPrimitiveRoot (n : ℕ) :
    IsPrimitiveRoot (canonicalOddPrimePhase n) (canonicalOddPrimeOrder n) := by
  exact Complex.isPrimitiveRoot_exp (canonicalOddPrimeOrder n)
    (canonicalOddPrimeOrder_prime n).ne_zero

/-- Closed canonical realization of number-field-robust bounded-total-degree tail freedom. -/
theorem canonicalOddPrimePhase_numberFieldRobust :
    NumberFieldRobustBoundedTotalDegreeTailFreedom canonicalOddPrimePhase :=
  numberFieldRobustBoundedTotalDegreeTailFreedom_of_prime_orders
    canonicalOddPrimeOrder_prime canonicalOddPrimeOrder_injective
    canonicalOddPrimePhase_isPrimitiveRoot canonicalOddPrimeOrder_tendsto_atTop

theorem canonicalOddPrimePhase_boundedTotalDegreeTailFreedom :
    BoundedTotalDegreeTailFreedom canonicalOddPrimePhase :=
  canonicalOddPrimePhase_numberFieldRobust.rational

/-- Closed exact `β = 3/2` smooth-profile instance of the card's entire
hypertranscendence theorem. -/
theorem hypertranscendental_canonicalOddPrimePhase_threeHalves :
    Hypertranscendental
      (boundedRelationExponentialFunction
        (rationalPowerLogProfile 0 1 (3 / 2 : ℚ)) canonicalOddPrimePhase) := by
  apply hypertranscendental_primePhaseTail_rationalPower
    canonicalOddPrimeOrder_prime canonicalOddPrimeOrder_injective
    canonicalOddPrimePhase_isPrimitiveRoot canonicalOddPrimeOrder_tendsto_atTop
  · exact isAlgebraic_zero
  · exact isAlgebraic_one
  · norm_num
  · norm_num

end
end GaloisForLFunctions
