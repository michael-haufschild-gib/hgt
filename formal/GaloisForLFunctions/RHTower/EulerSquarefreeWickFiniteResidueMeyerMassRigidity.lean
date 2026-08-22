import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimeResidueHT
import GaloisForLFunctions.RHTower.XiSelectedBilateralPositiveSourceReceiver
import GaloisForLFunctions.HTGeometry.ChronometricGaugeRigidity

/-!
# Finite-residue rigidity of the EWQ--Meyer mass

The EWQ interaction observes a prime only through its joint modulo-three/modulo-four residue
profile.  By contrast, the Xi-selected Meyer character has mass
`p^(1/2 - Re rho)`.  This file proves the exact compatibility law: the Meyer mass factors through
the finite EWQ residue observation precisely on the critical line.

The forward implication is already detected by the two actual primes `13` and `37`, which have
the same joint EWQ profile.  Equality of their Meyer masses forces the common real exponent to
vanish.  Conversely every prime mass is one on the critical line.  Thus any future
dimension-preserving EWQ descent that is natural for the finite residue quotient and retains the
Meyer mass automatically supplies an RH orientation law; off-line magnitude cannot be hidden in
the finite interaction class.
-/

open Complex

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Prime-dependent mass of the genuine Xi-selected Meyer/Koszul character. -/
def ewqMeyerPrimeMass
    (rho : _root_.RHTower.XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ‖_root_.RHTower.deningerMeyerXiPrimeGammaCharacter rho p‖

/-- The Meyer mass is observable through the finite joint EWQ residue profile. -/
def EWQFiniteResidueMeyerMassNaturalAt
    (rho : _root_.RHTower.XiDivisorSupport) : Prop :=
  FiberConstant finTwoCoprimePrimeResidueProfile (ewqMeyerPrimeMass rho)

private def ewqPrimeThirteen : Nat.Primes := ⟨13, by norm_num⟩

private def ewqPrimeThirtySeven : Nat.Primes := ⟨37, by norm_num⟩

/-- The first two convenient primes congruent to one modulo twelve occupy the same EWQ cell. -/
private theorem ewqPrimeThirteen_profile_eq_thirtySeven :
    finTwoCoprimePrimeResidueProfile ewqPrimeThirteen =
      finTwoCoprimePrimeResidueProfile ewqPrimeThirtySeven := by
  have h13 : primeUnitResidueProfile 12 ewqPrimeThirteen = (1 : (ZMod 12)ˣ) :=
    primeUnitResidueProfile_eq_of_cast_eq 12 ewqPrimeThirteen 1 (by
      change ((13 : ℕ) : ZMod 12) = ((1 : ℕ) : ZMod 12)
      rw [ZMod.natCast_eq_natCast_iff'])
  have h37 : primeUnitResidueProfile 12 ewqPrimeThirtySeven = (1 : (ZMod 12)ˣ) :=
    primeUnitResidueProfile_eq_of_cast_eq 12 ewqPrimeThirtySeven 1 (by
      change ((37 : ℕ) : ZMod 12) = ((1 : ℕ) : ZMod 12)
      rw [ZMod.natCast_eq_natCast_iff'])
  unfold finTwoCoprimePrimeResidueProfile coprimePrimeUnitResidueProfile
  simp only [Function.comp_apply]
  congr 2

/-- Equal real powers of the distinct positive bases `13` and `37` have zero exponent. -/
private theorem centeredExponent_eq_zero_of_thirteen_rpow_eq_thirtySeven
    {a : ℝ} (h : (13 : ℝ) ^ a = (37 : ℝ) ^ a) : a = 0 := by
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 13),
    Real.log_rpow (by norm_num : (0 : ℝ) < 37)] at hlog
  have hne : Real.log (13 : ℝ) - Real.log (37 : ℝ) ≠ 0 := by
    have hlt : Real.log (13 : ℝ) < Real.log (37 : ℝ) :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    linarith
  have hz : a * (Real.log (13 : ℝ) - Real.log (37 : ℝ)) = 0 := by
    linarith
  exact (mul_eq_zero.mp hz).resolve_right hne

/-- **Finite-residue Meyer rigidity.**  Prime magnitude can descend through the finite EWQ
residue quotient exactly when its centered Xi exponent vanishes. -/
theorem ewqFiniteResidueMeyerMassNaturalAt_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    EWQFiniteResidueMeyerMassNaturalAt rho ↔ (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hmass := h ewqPrimeThirteen ewqPrimeThirtySeven
      ewqPrimeThirteen_profile_eq_thirtySeven
    change ‖_root_.RHTower.deningerMeyerXiPrimeGammaCharacter
        rho ewqPrimeThirteen‖ =
      ‖_root_.RHTower.deningerMeyerXiPrimeGammaCharacter
        rho ewqPrimeThirtySeven‖ at hmass
    rw [
      _root_.RHTower.deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
      _root_.RHTower.deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
      _root_.RHTower.norm_deltaS ewqPrimeThirteen.2.pos,
      _root_.RHTower.norm_deltaS ewqPrimeThirtySeven.2.pos] at hmass
    simp only [ewqPrimeThirteen, ewqPrimeThirtySeven] at hmass
    have hz := centeredExponent_eq_zero_of_thirteen_rpow_eq_thirtySeven hmass
    linarith
  · intro hline p q _hpq
    rw [ewqMeyerPrimeMass,
      _root_.RHTower.deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
      (_root_.RHTower.norm_deltaS_eq_one_iff p.2.two_le (rho : ℂ)).2 hline,
      ewqMeyerPrimeMass,
      _root_.RHTower.deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
      (_root_.RHTower.norm_deltaS_eq_one_iff q.2.two_le (rho : ℂ)).2 hline]

/-- Global finite-residue naturality of every Xi-selected Meyer mass. -/
def EveryEWQFiniteResidueMeyerMassNatural : Prop :=
  ∀ rho : _root_.RHTower.XiDivisorSupport,
    EWQFiniteResidueMeyerMassNaturalAt rho

/-- Global finite-residue Meyer-mass descent is exactly RH. -/
theorem everyEWQFiniteResidueMeyerMassNatural_iff_riemannHypothesis :
    EveryEWQFiniteResidueMeyerMassNatural ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (ewqFiniteResidueMeyerMassNaturalAt_iff rho).1 (h rho)
  · intro hRH rho
    exact (ewqFiniteResidueMeyerMassNaturalAt_iff rho).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end GaloisForLFunctions.RHTower
