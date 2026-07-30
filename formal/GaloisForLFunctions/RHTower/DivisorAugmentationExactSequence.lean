import GaloisForLFunctions.RHTower.CompactOpenKolchinWardChargeEscape

/-!
# The divisor-augmentation exact sequence

A finite packet of constant-coefficient differential reporters applied to one common
meromorphic mode factors through addition of the reporter symbols.  When the common mode has
a simple pole, the one-channel operator map is injective.  Hence the common-mode packet has
exactly the augmentation kernel: its relative directions lose one and only one marked divisor
mode.

This file isolates that exact sequence from the escaping-Xi construction.  The theorem is local
and applies to every meromorphic simple pole.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Addition of all constant-coefficient differential symbols in a finite packet. -/
def differentialSymbolAugmentation
    {I : Type*} [Fintype I] :
    (I → Polynomial ℂ) →+ Polynomial ℂ where
  toFun L := ∑ i, L i
  map_zero' := by simp
  map_add' L M := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]

/-- One differential symbol acting on one common meromorphic mode. -/
def singleModeDifferentialOperatorHom
    (f : ℂ → ℂ) : Polynomial ℂ →+ (ℂ → ℂ) where
  toFun P := constantCoeffDifferentialOperator P f
  map_zero' := by
    funext z
    simp [constantCoeffDifferentialOperator]
  map_add' P Q :=
    HTGeometry.constantCoeffDifferentialOperator_add_operator P Q f

/-- A finite packet acting on one common mode.  Definitionally, this is the one-channel
operator map after the augmentation of all packet symbols. -/
def commonModeDifferentialOperatorHom
    {I : Type*} [Fintype I] (f : ℂ → ℂ) :
    (I → Polynomial ℂ) →+ (ℂ → ℂ) :=
  (singleModeDifferentialOperatorHom f).comp differentialSymbolAugmentation

theorem commonModeDifferentialOperatorHom_apply
    {I : Type*} [Fintype I] (f : ℂ → ℂ)
    (L : I → Polynomial ℂ) :
    commonModeDifferentialOperatorHom f L =
      commonModeDifferentialCombination L f := by
  change constantCoeffDifferentialOperator (∑ i, L i) f =
    commonModeDifferentialCombination L f
  exact (commonModeDifferentialCombination_eq_operator_sum L f).symm

/-- A simple pole makes the one-channel differential-operator representation faithful:
no nonzero constant-coefficient symbol annihilates the marked mode. -/
theorem singleModeDifferentialOperatorHom_injective_of_simplePole
    {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ)
    (horder : meromorphicOrderAt f ρ = ((-1 : ℤ) : WithTop ℤ)) :
    Function.Injective (singleModeDifferentialOperatorHom f) := by
  intro P Q hPQ
  have hzero :
      singleModeDifferentialOperatorHom f (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  by_contra hne
  have hsub : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hpole :=
    nonzeroDifferentialOperator_detects_simplePole hsub hf horder
  change constantCoeffDifferentialOperator (P - Q) f = 0 at hzero
  rw [hzero] at hpole
  simp at hpole
  exact (WithTop.add_ne_top.mpr
    ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩) hpole.symm

/-- For a nonempty packet, augmentation onto the single common symbol is surjective. -/
theorem differentialSymbolAugmentation_surjective
    {I : Type*} [Fintype I] [Nonempty I] :
    Function.Surjective
      (differentialSymbolAugmentation :
        (I → Polynomial ℂ) →+ Polynomial ℂ) := by
  classical
  let i₀ : I := Classical.choice ‹Nonempty I›
  intro P
  let L : I → Polynomial ℂ := fun i => if i = i₀ then P else 0
  refine ⟨L, ?_⟩
  change (∑ i, L i) = P
  simp [L]

/-- **Divisor-augmentation exactness.**  At a simple pole, the complete kernel of a finite
common-mode differential packet is the augmentation kernel.  Thus relative reporters delete
exactly one marked divisor direction and no additional differential information. -/
theorem ker_commonModeDifferentialOperatorHom_eq_ker_augmentation
    {I : Type*} [Fintype I] {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ)
    (horder : meromorphicOrderAt f ρ = ((-1 : ℤ) : WithTop ℤ)) :
    (commonModeDifferentialOperatorHom f :
      (I → Polynomial ℂ) →+ (ℂ → ℂ)).ker =
        (differentialSymbolAugmentation :
          (I → Polynomial ℂ) →+ Polynomial ℂ).ker := by
  ext L
  simp only [AddMonoidHom.mem_ker, commonModeDifferentialOperatorHom_apply,
    differentialSymbolAugmentation]
  exact commonModeDifferentialCombination_eq_zero_iff_sum_eq_zero
    L hf horder

/-- The common-mode packet has the same image as a single marked channel.  Together with the
kernel theorem, this is the first-isomorphism form of the augmentation-residue law. -/
theorem range_commonModeDifferentialOperatorHom_eq_singleMode
    {I : Type*} [Fintype I] [Nonempty I] (f : ℂ → ℂ) :
    Set.range (commonModeDifferentialOperatorHom f :
      (I → Polynomial ℂ) →+ (ℂ → ℂ)) =
      Set.range (singleModeDifferentialOperatorHom f) := by
  ext g
  constructor
  · rintro ⟨L, rfl⟩
    refine ⟨∑ i, L i, ?_⟩
    change constantCoeffDifferentialOperator (∑ i, L i) f =
      commonModeDifferentialOperatorHom f L
    exact (commonModeDifferentialCombination_eq_operator_sum L f).symm.trans
      (commonModeDifferentialOperatorHom_apply f L).symm
  · rintro ⟨P, rfl⟩
    obtain ⟨L, hL⟩ :=
      differentialSymbolAugmentation_surjective
        (I := I) P
    refine ⟨L, ?_⟩
    change commonModeDifferentialOperatorHom f L =
      constantCoeffDifferentialOperator P f
    rw [commonModeDifferentialOperatorHom_apply,
      commonModeDifferentialCombination_eq_operator_sum]
    change constantCoeffDifferentialOperator
      (differentialSymbolAugmentation L) f =
        constantCoeffDifferentialOperator P f
    rw [hL]

/-- Every positive-multiplicity escaping quartet realizes the same universal augmentation
sequence at its marked off-critical divisor. -/
theorem escapingQuartet_divisorAugmentationExact
    {I : Type*} [Fintype I]
    (a : ℝ) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    (commonModeDifferentialOperatorHom
      (logDeriv (multiplicityEscapingQuartetGauge a N n)) :
        (I → Polynomial ℂ) →+ (ℂ → ℂ)).ker =
      (differentialSymbolAugmentation :
        (I → Polynomial ℂ) →+ Polynomial ℂ).ker := by
  apply ker_commonModeDifferentialOperatorHom_eq_ker_augmentation
    (ρ := quartetPoint a (escapingQuartetHeight n))
  · rw [show logDeriv (multiplicityEscapingQuartetGauge a N n) =
        deriv (multiplicityEscapingQuartetGauge a N n) /
          multiplicityEscapingQuartetGauge a N n by
      funext z
      rw [logDeriv_apply]
      rfl]
    have hAn : AnalyticAt ℂ (multiplicityEscapingQuartetGauge a N n)
        (quartetPoint a (escapingQuartetHeight n)) := by
      have hfun : multiplicityEscapingQuartetGauge a N n =
          fun z => Polynomial.eval z
            (multiplicityEscapingQuartetPolynomial a N n) := by
        funext z
        exact (multiplicityEscapingQuartetPolynomial_eval a N n z).symm
      rw [hfun]
      simpa using
        (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z)
          (quartetPoint a (escapingQuartetHeight n))).aeval_polynomial
            (multiplicityEscapingQuartetPolynomial a N n)
    exact hAn.deriv.meromorphicAt.div hAn.meromorphicAt
  · exact multiplicityEscapingQuartetGauge_logDeriv_addedZero_simplePole
      a hN n

end

end RHTower
