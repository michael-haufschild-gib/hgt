import GaloisForLFunctions.RHTower.RealCoronaCrossedProductSmoothnessFracture

/-!
# Positive local cyclic formulas vanish on the complete-divisor orientation

Local residue/JLO monomials of positive differential degree contain at least one positive iterated
commutator.  This file encodes finite linear combinations of such monomials and proves exact
vanishing for every smooth element obtained from commutation with the Dirac operator.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Product of selected bounded commutator jets.  Index zero is the represented operator and every
positive index is an iterated commutator extension. -/
def LinearPMapSmoothElement.localJetWord
    {D : V →ₗ.[ℂ] V} (S : LinearPMapSmoothElement D)
    (indices : List ℕ) : Module.End ℂ V :=
  (indices.map S.derivative).prod

/-- A jet word has positive differential degree when it contains at least one positive derivative
index. -/
def IsPositiveLocalJetWord (indices : List ℕ) : Prop :=
  ∃ k ∈ indices, 0 < k

theorem linearPMapSmoothElementOfCommutes_derivative_positive
    (D : V →ₗ.[ℂ] V) (a : Module.End ℂ V)
    (haDomain : ∀ x : D.domain, a x ∈ D.domain)
    (haCommutes : ∀ x : D.domain, D ⟨a x, haDomain x⟩ = a (D x))
    (haBounded : HasLinearOperatorBound a) {n : ℕ} (hn : 0 < n) :
    (linearPMapSmoothElementOfCommutes D a haDomain haCommutes haBounded).derivative n = 0 := by
  simp [linearPMapSmoothElementOfCommutes, Nat.ne_of_gt hn]

/-- Every positive local jet word of an exactly commuting smooth element is the zero operator. -/
theorem linearPMapSmoothElementOfCommutes_localJetWord_eq_zero
    (D : V →ₗ.[ℂ] V) (a : Module.End ℂ V)
    (haDomain : ∀ x : D.domain, a x ∈ D.domain)
    (haCommutes : ∀ x : D.domain, D ⟨a x, haDomain x⟩ = a (D x))
    (haBounded : HasLinearOperatorBound a)
    {indices : List ℕ} (hpositive : IsPositiveLocalJetWord indices) :
    (linearPMapSmoothElementOfCommutes D a haDomain haCommutes haBounded).localJetWord
      indices = 0 := by
  rcases hpositive with ⟨k, hk, hkpos⟩
  rcases List.mem_iff_append.mp hk with ⟨before, after, rfl⟩
  rw [LinearPMapSmoothElement.localJetWord, List.map_append,
    List.map_cons, List.prod_append,
    linearPMapSmoothElementOfCommutes_derivative_positive
      D a haDomain haCommutes haBounded hkpos]
  simp

/-- Finite positive local formula built from bounded commutator jets and an arbitrary additive
functional. Cyclicity is not needed for the vanishing theorem, so the conclusion applies to every
cyclic trace, supertrace component, or residue functional of this form. -/
structure PositiveLocalJetFormula
    {D : V →ₗ.[ℂ] V} (S : LinearPMapSmoothElement D) where
  term : Type
  finiteTerm : Fintype term
  decidableTerm : DecidableEq term
  coefficient : term → ℂ
  word : term → List ℕ
  positive : ∀ j, IsPositiveLocalJetWord (word j)
  functional : (Module.End ℂ V) →+ ℂ

attribute [instance] PositiveLocalJetFormula.finiteTerm
attribute [instance] PositiveLocalJetFormula.decidableTerm

def PositiveLocalJetFormula.value
    {D : V →ₗ.[ℂ] V} {S : LinearPMapSmoothElement D}
    (F : PositiveLocalJetFormula S) : ℂ :=
  ∑ j, F.coefficient j * F.functional (S.localJetWord (F.word j))

/-- Every finite positive local formula vanishes for an exactly commuting smooth element. -/
theorem PositiveLocalJetFormula.value_eq_zero_of_commutes
    (D : V →ₗ.[ℂ] V) (a : Module.End ℂ V)
    (haDomain : ∀ x : D.domain, a x ∈ D.domain)
    (haCommutes : ∀ x : D.domain, D ⟨a x, haDomain x⟩ = a (D x))
    (haBounded : HasLinearOperatorBound a)
    (F : PositiveLocalJetFormula
      (linearPMapSmoothElementOfCommutes D a haDomain haCommutes haBounded)) :
    F.value = 0 := by
  rw [PositiveLocalJetFormula.value]
  apply Finset.sum_eq_zero
  intro j hj
  rw [linearPMapSmoothElementOfCommutes_localJetWord_eq_zero
    D a haDomain haCommutes haBounded (F.positive j), map_zero, mul_zero]

end GaloisForLFunctions.RHTower

namespace RHTower

open GaloisForLFunctions.RHTower

/-- A summable reflection-odd family has zero total. -/
theorem tsum_eq_zero_of_equiv_odd
    {ι : Type*} (σ : ι ≃ ι) (f : ι → ℂ)
    (_hsum : Summable f) (hodd : ∀ i, f (σ i) = -f i) :
    ∑' i, f i = 0 := by
  have hreindex : (∑' i, f i) = ∑' i, f (σ i) :=
    (σ.tsum_eq f).symm
  have hneg : (∑' i, f (σ i)) = -(∑' i, f i) := by
    rw [show (fun i => f (σ i)) = fun i => -f i by
      funext i
      exact hodd i]
    exact tsum_neg
  linear_combination (1 / 2 : ℂ) * (hreindex.trans hneg)

/-- Every absolutely summable reflection-invariant degree-zero spectral weight has zero oriented
trace on the complete Xi divisor. -/
theorem tsum_xiCompleteDivisorOrientation_mul_eq_zero
    (weight : XiZeroCopy → ℂ)
    (hsum : Summable fun q => deningerArithmeticFEOrientation q * weight q)
    (hinvariant : ∀ q, weight (xiZeroCopyReflectEquiv q) = weight q) :
    ∑' q, deningerArithmeticFEOrientation q * weight q = 0 := by
  apply tsum_eq_zero_of_equiv_odd xiZeroCopyReflectEquiv
    (fun q => deningerArithmeticFEOrientation q * weight q) hsum
  intro q
  rw [deningerArithmeticFEOrientation_reflect, hinvariant]
  ring

/-- Every finite reflection-invariant truncation has exactly zero oriented trace; no limiting
argument or summability is used. -/
theorem sum_xiCompleteDivisorOrientation_mul_eq_zero
    (s : Finset XiZeroCopy) (weight : XiZeroCopy → ℂ)
    (hmem : ∀ q ∈ s, xiZeroCopyReflectEquiv q ∈ s)
    (hinvariant : ∀ q ∈ s,
      weight (xiZeroCopyReflectEquiv q) = weight q) :
    ∑ q ∈ s, deningerArithmeticFEOrientation q * weight q = 0 := by
  let f : XiZeroCopy → ℂ := fun q =>
    deningerArithmeticFEOrientation q * weight q
  change ∑ q ∈ s, f q = 0
  refine Finset.sum_involution
    (fun q _ => xiZeroCopyReflectEquiv q)
    (fun q hq => ?_) (fun q hq hne => ?_)
    (fun q hq => hmem q hq)
    (fun q hq => xiZeroCopyReflectEquiv_apply_apply q)
  · dsimp [f]
    rw [deningerArithmeticFEOrientation_reflect, hinvariant q hq]
    ring
  · exact xiZeroCopyReflectEquiv_ne q

/-- Every positive commutator-generated local formula vanishes on the signed complete-divisor
Real-corona orientation. -/
theorem xiCompleteDivisorSignedOrientation_positiveLocalFormula_eq_zero
    (F : PositiveLocalJetFormula xiCompleteDivisorSignedOrientationSmooth) :
    F.value = 0 :=
  PositiveLocalJetFormula.value_eq_zero_of_commutes
    xiCompleteDivisorSignedDirac xiCompleteDivisorOrientation
    xiCompleteDivisorOrientation_mem_signedDomain
    xiCompleteDivisorSignedDirac_orientation_commutes
    xiCompleteDivisorOrientation_bounded F

/-- P1 positive-degree no-go: no finite formula generated by positive local commutator jets of the
complete-divisor orientation can reproduce the nonzero graded cyclic charge `2`. -/
theorem not_exists_signedOrientation_positiveLocalFormula_value_two :
    ¬∃ F : PositiveLocalJetFormula xiCompleteDivisorSignedOrientationSmooth,
      F.value = 2 := by
  rintro ⟨F, hF⟩
  rw [xiCompleteDivisorSignedOrientation_positiveLocalFormula_eq_zero F] at hF
  norm_num at hF

/-- Complete local formulas have a reflection-compatible degree-zero spectral term and a finite
positive commutator-jet term. -/
structure CompleteDivisorLocalFormula where
  weight : XiZeroCopy → ℂ
  weight_invariant : ∀ q, weight (xiZeroCopyReflectEquiv q) = weight q
  oriented_summable :
    Summable fun q => deningerArithmeticFEOrientation q * weight q
  positive : PositiveLocalJetFormula xiCompleteDivisorSignedOrientationSmooth

def CompleteDivisorLocalFormula.value (F : CompleteDivisorLocalFormula) : ℂ :=
  (∑' q, deningerArithmeticFEOrientation q * F.weight q) + F.positive.value

/-- Every complete-divisor-compatible local formula vanishes: degree zero cancels orbitwise and
every positive local commutator word contains a zero derivative. -/
theorem CompleteDivisorLocalFormula.value_eq_zero
    (F : CompleteDivisorLocalFormula) : F.value = 0 := by
  rw [CompleteDivisorLocalFormula.value,
    tsum_xiCompleteDivisorOrientation_mul_eq_zero
      F.weight F.oriented_summable F.weight_invariant,
    xiCompleteDivisorSignedOrientation_positiveLocalFormula_eq_zero]
  exact zero_add 0

/-- Full P1 no-go for the canonical complete divisor: no reflection-compatible degree-zero term
plus finite positive local commutator formula can reproduce graded cyclic charge `2`. -/
theorem not_exists_completeDivisorLocalFormula_value_two :
    ¬∃ F : CompleteDivisorLocalFormula, F.value = 2 := by
  rintro ⟨F, hF⟩
  rw [F.value_eq_zero] at hF
  norm_num at hF

end RHTower
