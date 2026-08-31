import GaloisForLFunctions.HTGeometry.ConstitutiveCompactRecurrenceCharacterDescent
import GaloisForLFunctions.HTGeometry.WeldCircleFaithfulness
import GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularCurrentField

/-!
# Theta-source prime-modular compact recurrence descent

Finite integer prime histories embed faithfully and densely in the archimedean unit circle.  The
real logarithm of the theta-source prime-modular character extends continuously through this
compact recurrence formation exactly when its centered horizontal rate is zero.  Exact recovery
therefore turns compact observer recurrence into tracial selection without erasing finite prime
history.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The prime-circle observer has dense range because it contains the irrational `log 2` orbit. -/
theorem denseRange_primeCircleHom : DenseRange primeCircleHom := by
  let p2 : Nat.Primes := ⟨2, by norm_num⟩
  have hcyclic : DenseRange
      (fun k : ℤ => k • ((Real.log 2 : ℝ) : AddCircle (1 : ℝ))) := by
    apply (AddCircle.denseRange_zsmul_coe_iff).2
    simpa using primeLog_irrational (p := 2) (by norm_num)
  apply Dense.mono (s₁ := Set.range
    (fun k : ℤ => k • ((Real.log 2 : ℝ) : AddCircle (1 : ℝ)))) ?_ hcyclic
  rintro _ ⟨k, rfl⟩
  refine ⟨Finsupp.single p2 k, ?_⟩
  rw [primeCircleHom, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    primeLogHom_apply]
  simp [p2]

/-- Canonical compact recurrent observer of finite integer prime histories.  It is both faithful
and dense; compactness is supplied by the circle rather than by collapsing histories. -/
def primeCircleRecurrenceFormation :
    FaithfulCompactRecurrenceFormation (Nat.Primes →₀ ℤ) where
  History := AddCircle (1 : ℝ)
  historyMap := primeCircleHom
  historyMap_injective := primeCircleHom_injective
  historyMap_dense := denseRange_primeCircleHom

/-- Real logarithm of the group-completed reciprocal prime formation character. -/
def primeModularLogCharacter (t : ℝ) : (Nat.Primes →₀ ℤ) →+ ℝ where
  toFun c := t * primeLogHom c
  map_zero' := by simp
  map_add' c d := by rw [map_add]; ring

/-- One retained prime detects whether the modular log character is neutral. -/
theorem primeModularLogCharacter_eq_zero_iff (t : ℝ) :
    primeModularLogCharacter t = 0 ↔ t = 0 := by
  constructor
  · intro hz
    let p2 : Nat.Primes := ⟨2, by norm_num⟩
    have h := DFunLike.congr_fun hz (Finsupp.single p2 1)
    have h' : t * Real.log 2 = 0 := by
      simpa [primeModularLogCharacter, primeLogHom_apply, p2] using h
    exact (mul_eq_zero.mp h').resolve_right
      (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
  · rintro rfl
    ext c
    simp [primeModularLogCharacter]

/-- A prime modular log extends information-neutrally through compact recurrent completion exactly
on the tracial locus. -/
theorem primeModularCompactRecurrenceDescent_iff (t : ℝ) :
    CompactCharacterDescends primeCircleRecurrenceFormation
        (primeModularLogCharacter t) ↔ t = 0 := by
  rw [compactCharacterDescends_iff, primeModularLogCharacter_eq_zero_iff]

/-- Finite prime histories lifted into the dense prime-log weld lattice. -/
def primeLogFormationLift (c : Nat.Primes →₀ ℤ) : primeLogLattice :=
  ⟨primeLogHom c,
    PrimeIndexedLogExpansion.mem_primeLogLattice
      ⟨c, primeLogHom_apply c |>.symm⟩⟩

@[simp] theorem primeLogFormationLift_coe (c : Nat.Primes →₀ ℤ) :
    (primeLogFormationLift c : ℝ) = primeLogHom c := rfl

end

end GaloisForLFunctions.RHTower

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

/-- The compact-descent character is exactly the logarithmic orbit of the current-compatible theta
prime-modular action on every finite prime history. -/
theorem thetaXiPrimeModularLogOrbit_primeLogFormationLift
    (q : RHTower.XiZeroCopy) (c : Nat.Primes →₀ ℤ) :
    thetaXiPrimeModularLogOrbit q
        (GaloisForLFunctions.RHTower.primeLogFormationLift c) =
      GaloisForLFunctions.RHTower.primeModularLogCharacter
        (RHTower.primeDepthBVWoldXiCenteredRate q.1) c := rfl

/-- Exact recovery of a theta-source modular log through the faithful dense compact prime-circle
observer. -/
def ThetaXiPrimeModularCompactRecurrenceDescent
    (q : RHTower.XiZeroCopy) : Prop :=
  CompactCharacterDescends
    GaloisForLFunctions.RHTower.primeCircleRecurrenceFormation
    (GaloisForLFunctions.RHTower.primeModularLogCharacter
      (RHTower.primeDepthBVWoldXiCenteredRate q.1))

/-- Pointwise selection: compact recurrent descent of the recovered modular log is exactly
critical-line placement. -/
theorem thetaXiPrimeModularCompactRecurrenceDescent_iff
    (q : RHTower.XiZeroCopy) :
    ThetaXiPrimeModularCompactRecurrenceDescent q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [ThetaXiPrimeModularCompactRecurrenceDescent,
    GaloisForLFunctions.RHTower.primeModularCompactRecurrenceDescent_iff,
    RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Functional-equation reflection reverses the modular character but preserves compact descent. -/
theorem thetaXiPrimeModularCompactRecurrenceDescent_lineConj_iff
    (q : RHTower.XiZeroCopy) :
    ThetaXiPrimeModularCompactRecurrenceDescent
        (RHTower.xiZeroCopyLineConjEquiv q) ↔
      ThetaXiPrimeModularCompactRecurrenceDescent q := by
  rw [thetaXiPrimeModularCompactRecurrenceDescent_iff,
    thetaXiPrimeModularCompactRecurrenceDescent_iff]
  change (1 - star (q.1 : ℂ)).re = 1 / 2 ↔ (q.1 : ℂ).re = 1 / 2
  simp
  constructor <;> intro h <;> linarith

/-- Global source-current compact descent is exactly the critical-line condition on every
multiplicity-labelled Xi divisor copy. -/
theorem forall_thetaXiPrimeModularCompactRecurrenceDescent_iff :
    (∀ q : RHTower.XiZeroCopy,
      ThetaXiPrimeModularCompactRecurrenceDescent q) ↔
    ∀ q : RHTower.XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
  simp only [thetaXiPrimeModularCompactRecurrenceDescent_iff]

/-- Global compact recurrence descent is an exact RH selection interface.  Its remaining producer
is source-side continuity at the prime-circle completion boundary. -/
theorem forall_thetaXiPrimeModularCompactRecurrenceDescent_iff_riemannHypothesis :
    (∀ q : RHTower.XiZeroCopy,
      ThetaXiPrimeModularCompactRecurrenceDescent q) ↔
    RiemannHypothesis := by
  constructor
  · intro hdescent
    have hline : ∀ q : RHTower.XiZeroCopy, (q.1 : ℂ).re = 1 / 2 :=
      forall_thetaXiPrimeModularCompactRecurrenceDescent_iff.mp hdescent
    apply RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [RHTower.xiSpectralPoint]
    · simp [RHTower.xiSpectralPoint, hline q]
  · intro hRH q
    apply (thetaXiPrimeModularCompactRecurrenceDescent_iff q).2
    exact RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower.HedenmalmThetaSource
