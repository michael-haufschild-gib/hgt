import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralCharts
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Prime branches of a paired quotient over a prime neutral ideal

For each neutral coordinate that vanishes modulo `J`, choose one of its
paired variables to vanish. Add those chosen variables to the extended
neutral ideal. When `J` is prime, the resulting ideal is exactly the kernel
of its oriented Laurent chart, hence is prime.

The kernel proof uses the relative weight expansion. A weight survives the
chart precisely when it uses none of the chosen variables at zero neutral
coordinates. Every other minimal monomial is divisible by a branch generator.
The branches intersect to the extended neutral ideal, and inclusion of two
branches is exactly agreement of their choices on the zero coordinates.
Every prime containing the extended ideal contains one of these branches.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
open scoped PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- The variable killed by an orientation when its neutral coordinate vanishes. -/
def pairedBranchVariable (ε : ι → Bool) (i : ι) : ι ⊕ ι :=
  if ε i then Sum.inr i else Sum.inl i

/-- A surviving weight uses no killed variable at any zero neutral coordinate. -/
def pairedBranchWeightSurvives (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) (q : ι → ℤ) : Prop :=
  ∀ i, (X i : MvPolynomial ι K) ∈ J → normalWeightExponent q 0 (pairedBranchVariable ε i) = 0

/-- Extend the neutral ideal and impose the selected zero-coordinate branch variables. -/
def pairedBranchIdeal (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    Ideal (MvPolynomial (ι ⊕ ι) K) :=
  J.map (invariantSubstitution K) ⊔ Ideal.span (Set.range
    (fun i : {i : ι // (X i : MvPolynomial ι K) ∈ J} => X (pairedBranchVariable ε i.1)))

omit [Fintype ι] in
/-- Every branch contains the original paired equations. -/
theorem extended_le_pairedBranchIdeal (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    J.map (invariantSubstitution K) ≤ pairedBranchIdeal K J ε := le_sup_left

omit [Fintype ι] in
/-- A selected variable at a zero neutral coordinate belongs to the branch ideal. -/
theorem pairedBranchVariable_mem (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (i : ι) (hi : (X i : MvPolynomial ι K) ∈ J) :
    (X (pairedBranchVariable ε i) : MvPolynomial (ι ⊕ ι) K) ∈ pairedBranchIdeal K J ε := by
  apply (show Ideal.span (Set.range
    (fun j : {j : ι // (X j : MvPolynomial ι K) ∈ J} =>
      (X (pairedBranchVariable ε j.1) : MvPolynomial (ι ⊕ ι) K))) ≤
        pairedBranchIdeal K J ε from le_sup_right)
  exact Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩

/-- The chart factor consists exactly of the neutral powers attached to killed variables. -/
theorem orientedNeutralFactor_eq_prod_branch (J : Ideal (MvPolynomial ι K))
    (ε : ι → Bool) (q : ι → ℤ) :
    orientedNeutralFactor K J ε q = ∏ i, (Ideal.Quotient.mk J (X i)) ^
      normalWeightExponent q 0 (pairedBranchVariable ε i) := by
  rw [orientedNeutralFactor, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases h : ε i <;> simp [pairedBranchVariable, h]

/-- Over a prime neutral quotient, a chart factor is nonzero exactly on surviving weights. -/
theorem orientedNeutralFactor_ne_zero_iff (J : Ideal (MvPolynomial ι K)) [J.IsPrime]
    (ε : ι → Bool) (q : ι → ℤ) :
    orientedNeutralFactor K J ε q ≠ 0 ↔ pairedBranchWeightSurvives K J ε q := by
  rw [orientedNeutralFactor_eq_prod_branch, Finset.prod_ne_zero_iff]
  constructor
  · intro h i hi
    have hn := h i (Finset.mem_univ i)
    by_contra he
    apply hn
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hi, zero_pow he]
  · intro h i _
    by_cases hi : (X i : MvPolynomial ι K) ∈ J
    · rw [h i hi, pow_zero]
      exact one_ne_zero
    · exact pow_ne_zero _ (fun hz => hi ((Ideal.Quotient.eq_zero_iff_mem).mp hz))

/-- A Laurent chart vanishes precisely when every surviving neutral coefficient vanishes. -/
theorem pairedChartMap_eq_zero_iff_surviving (J : Ideal (MvPolynomial ι K)) [J.IsPrime]
    (ε : ι → Bool) (P : MvPolynomial (ι ⊕ ι) K) :
    pairedChartMap K J ε P = 0 ↔
      ∀ q, pairedBranchWeightSurvives K J ε q → pairedWeightExtraction K q P ∈ J := by
  constructor
  · intro h q hq
    have he := congrArg (fun f : NeutralLaurent K J => f.coeff q) h
    change (pairedChartMap K J ε P).coeff q = 0 at he
    rw [pairedChartMap_coeff] at he
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (mul_eq_zero.mp he).resolve_right ((orientedNeutralFactor_ne_zero_iff K J ε q).mpr hq)
  · intro h
    ext q
    change (pairedChartMap K J ε P).coeff q = 0
    rw [pairedChartMap_coeff]
    by_cases hq : pairedBranchWeightSurvives K J ε q
    · rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (h q hq), zero_mul]
    · have hz : orientedNeutralFactor K J ε q = 0 := by
        by_contra hn
        exact hq ((orientedNeutralFactor_ne_zero_iff K J ε q).mp hn)
      rw [hz, mul_zero]

/-- Every branch equation vanishes under its oriented Laurent substitution. -/
theorem pairedBranchIdeal_le_ker (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    pairedBranchIdeal K J ε ≤ RingHom.ker (pairedChartMap K J ε) := by
  apply sup_le
  · intro P hP
    exact RingHom.mem_ker.mpr (pairedChartMap_annihilates K J ε P hP)
  · rw [Ideal.span_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    apply RingHom.mem_ker.mpr
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hi
    cases h : ε i <;>
      simp [pairedChartMap, pairedChartCoordinates, pairedBranchVariable, h, hz]

/-- The selected branch equations generate the entire Laurent kernel over a prime neutral quotient. -/
theorem pairedBranchIdeal_eq_ker (J : Ideal (MvPolynomial ι K)) [J.IsPrime] (ε : ι → Bool) :
    pairedBranchIdeal K J ε = RingHom.ker (pairedChartMap K J ε) := by
  apply le_antisymm (pairedBranchIdeal_le_ker K J ε)
  intro P hP
  have h := (pairedChartMap_eq_zero_iff_surviving K J ε P).mp (RingHom.mem_ker.mp hP)
  rw [pairedNeutralExpansion K P]
  apply (pairedBranchIdeal K J ε).sum_mem
  intro q _
  change pairedNeutralEquiv K P q • minimalPairedMonomial K q ∈ _
  rw [pairedNeutral_smul]
  by_cases hq : pairedBranchWeightSurvives K J ε q
  · apply (pairedBranchIdeal K J ε).mul_mem_right
    apply extended_le_pairedBranchIdeal K J ε
    apply Ideal.mem_map_of_mem
    rw [pairedNeutralEquiv_apply]
    exact h q hq
  · have hex : ∃ i, (X i : MvPolynomial ι K) ∈ J ∧
        normalWeightExponent q 0 (pairedBranchVariable ε i) ≠ 0 := by
      simpa only [pairedBranchWeightSurvives, not_forall, exists_prop] using hq
    obtain ⟨i, hi, he⟩ := hex
    have hx : (X (pairedBranchVariable ε i) : MvPolynomial (ι ⊕ ι) K) ∈
        pairedBranchIdeal K J ε :=
      pairedBranchVariable_mem K J ε i hi
    have hd : (X (pairedBranchVariable ε i) : MvPolynomial (ι ⊕ ι) K) ∣
        minimalPairedMonomial K q := MvPolynomial.X_dvd_monomial.mpr (Or.inr he)
    have hm : minimalPairedMonomial K q ∈ pairedBranchIdeal K J ε := by
      obtain ⟨r, hr⟩ := hd
      rw [hr]
      exact (pairedBranchIdeal K J ε).mul_mem_right r hx
    exact (pairedBranchIdeal K J ε).mul_mem_left _ hm

/-- Each branch is prime because its quotient embeds in a Laurent domain. -/
theorem pairedBranchIdeal_isPrime (J : Ideal (MvPolynomial ι K)) [J.IsPrime] (ε : ι → Bool) :
    (pairedBranchIdeal K J ε).IsPrime := by
  rw [pairedBranchIdeal_eq_ker]
  exact RingHom.ker_isPrime _

/-- The full branch intersection recovers the original extended prime neutral ideal. -/
theorem iInf_pairedBranchIdeal (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    (⨅ ε : ι → Bool, pairedBranchIdeal K J ε) = J.map (invariantSubstitution K) := by
  ext P
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (pairedQuotient_eq_zero_iff_charts K J (Ideal.Quotient.mk _ P)).mpr
    intro ε
    have he := Ideal.mem_iInf.mp h ε
    rw [pairedBranchIdeal_eq_ker] at he
    exact RingHom.mem_ker.mp he
  · intro h
    apply Ideal.mem_iInf.mpr
    intro ε
    exact extended_le_pairedBranchIdeal K J ε h

omit [Fintype ι] in
/-- Choices outside the zero neutral coordinates do not change a branch. -/
theorem pairedBranchIdeal_congr (J : Ideal (MvPolynomial ι K)) (ε δ : ι → Bool)
    (h : ∀ i, (X i : MvPolynomial ι K) ∈ J → ε i = δ i) :
    pairedBranchIdeal K J ε = pairedBranchIdeal K J δ := by
  have he : (fun i : {i : ι // (X i : MvPolynomial ι K) ∈ J} =>
      (X (pairedBranchVariable ε i.1) : MvPolynomial (ι ⊕ ι) K)) =
      (fun i : {i : ι // (X i : MvPolynomial ι K) ∈ J} => X (pairedBranchVariable δ i.1)) := by
    funext i
    simp only [pairedBranchVariable, h i.1 i.2]
  exact congrArg (fun f => J.map (invariantSubstitution K) ⊔ Ideal.span (Set.range f)) he

omit [Fintype ι] in
/-- At a zero neutral coordinate, a chart kills precisely the variable selected by its orientation. -/
theorem pairedChartMap_branchVariable_eq_zero_iff (J : Ideal (MvPolynomial ι K)) [J.IsPrime]
    (ε δ : ι → Bool) (i : ι) (hi : (X i : MvPolynomial ι K) ∈ J) :
    pairedChartMap K J δ (X (pairedBranchVariable ε i)) = 0 ↔ ε i = δ i := by
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hi
  cases he : ε i <;> cases hd : δ i <;>
    simp [pairedChartMap, pairedChartCoordinates, pairedBranchVariable, he, hd, hz]

/-- Branches are incomparable unless their zero-coordinate choices agree. -/
theorem pairedBranchIdeal_le_iff (J : Ideal (MvPolynomial ι K)) [J.IsPrime] (ε δ : ι → Bool) :
    pairedBranchIdeal K J ε ≤ pairedBranchIdeal K J δ ↔
      ∀ i, (X i : MvPolynomial ι K) ∈ J → ε i = δ i := by
  constructor
  · intro h i hi
    apply (pairedChartMap_branchVariable_eq_zero_iff K J ε δ i hi).mp
    apply RingHom.mem_ker.mp
    rw [← pairedBranchIdeal_eq_ker]
    exact h (pairedBranchVariable_mem K J ε i hi)
  · intro h
    exact (pairedBranchIdeal_congr K J ε δ h).le

omit [Fintype ι] in
/-- Primality forces a choice of one vanishing variable from each zero-coordinate pair. -/
theorem exists_pairedBranchIdeal_le (J : Ideal (MvPolynomial ι K))
    (Q : Ideal (MvPolynomial (ι ⊕ ι) K)) [Q.IsPrime]
    (h : J.map (invariantSubstitution K) ≤ Q) :
    ∃ ε : ι → Bool, pairedBranchIdeal K J ε ≤ Q := by
  refine ⟨fun i => decide ((X (Sum.inr i) : MvPolynomial (ι ⊕ ι) K) ∈ Q), ?_⟩
  apply sup_le h
  rw [Ideal.span_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  change (X (pairedBranchVariable
    (fun j => decide ((X (Sum.inr j) : MvPolynomial (ι ⊕ ι) K) ∈ Q)) i) :
      MvPolynomial (ι ⊕ ι) K) ∈ Q
  by_cases hw : (X (Sum.inr i) : MvPolynomial (ι ⊕ ι) K) ∈ Q
  · simp only [pairedBranchVariable, hw, decide_true, if_true]
  · have hp : X (Sum.inl i) * X (Sum.inr i) ∈ Q := by
      have he := h (Ideal.mem_map_of_mem (invariantSubstitution K) hi)
      simpa [invariantSubstitution] using he
    have hz := (Ideal.IsPrime.mem_or_mem (inferInstance : Q.IsPrime) hp).resolve_right hw
    simpa only [pairedBranchVariable, hw, decide_false, Bool.false_eq_true, if_false] using hz

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchIdeal_eq_ker
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchIdeal_isPrime
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iInf_pairedBranchIdeal
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchIdeal_le_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_pairedBranchIdeal_le
