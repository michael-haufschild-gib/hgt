import GaloisForLFunctions.RHTower.XiPrimeSeamAnchoredCommutatorNormComparison
import GaloisForLFunctions.RHTower.XiPrimeTwoEulerHurwitzMonodromyCalibration
import GaloisForLFunctions.RHTower.HeatAperturePrimeSeamReflection

/-!
# Anchored Calkin critical-line universality

At every point of the open critical strip, four a priori different conditions coincide: critical
line location, cofinal decay of charge-scaled anchored Calkin norms, compactness of every anchored
prime-pair commutator, and vanishing of the calibrated prime-two Hurwitz boundary seam.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Pointwise cofinal charge-scaled Calkin decay, without assuming that the strip point is a Xi
divisor point. -/
def CofinalAnchoredEulerCompressionEssentialNormDecayAt
    (a : ℝ) (rho : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ q : ℕ,
    q.Prime ∧ max N 2 < q ∧
      Real.sqrt (2 * q : ℕ) *
        essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) < ε

/-- Pointwise compactness of every nontrivial anchored prime-pair commutator. -/
def AllAnchoredEulerCompressionCommutatorsCompactAt
    (a : ℝ) (rho : ℂ) : Prop :=
  ∀ q : ℕ, q.Prime → 2 < q →
    IsCompactOperator (firstPrimeAnchoredEulerCompressionCommutator a rho q)

/-- **Anchored Calkin critical-line universality law.**  On the open strip, cofinal quantitative
Calkin decay, exact compactness at every partner prime, calibrated Hurwitz boundary-seam
vanishing, and critical-line location have exactly the same pointwise zero fibre. -/
theorem anchoredCalkin_criticalLineUniversality
    {a : ℝ} (ha : 0 < a) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    (CofinalAnchoredEulerCompressionEssentialNormDecayAt a rho ↔
      rho.re = 1 / 2) ∧
    (AllAnchoredEulerCompressionCommutatorsCompactAt a rho ↔
      rho.re = 1 / 2) ∧
    (xiHurwitzPrimeTwoEulerBoundarySeam rho = 0 ↔
      rho.re = 1 / 2) := by
  have hlineDecay : rho.re = 1 / 2 →
      CofinalAnchoredEulerCompressionEssentialNormDecayAt a rho := by
    intro hline ε hε N
    obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (max N 2 + 1)
    have hmax : max N 2 < q := by omega
    have hq2 : 2 < q := (le_max_right N 2).trans_lt hmax
    have htwo : orbitwiseNatPrimeSeamCharge 2 rho = 0 :=
      (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half
        rho 2 (by norm_num)).2 hline
    have hqzero : orbitwiseNatPrimeSeamCharge q rho = 0 :=
      (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half
        rho q hq).2 hline
    have hcompact : IsCompactOperator
        (firstPrimeAnchoredEulerCompressionCommutator a rho q) := by
      apply (firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff
        ha hq hq2).2
      rw [htwo, hqzero]
    refine ⟨q, hq, hmax, ?_⟩
    rw [essentialNorm_eq_zero_of_isCompactOperator hcompact, mul_zero]
    exact hε
  have hdecayLine :
      CofinalAnchoredEulerCompressionEssentialNormDecayAt a rho →
        rho.re = 1 / 2 := by
    intro hdecay
    have hzero : orbitwiseFirstPrimeSeamCharge rho = 0 :=
      firstPrimeSeamCharge_eq_zero_of_cofinal_anchored_essentialNorm_decay
        ha hstrip hdecay
    exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).1 hzero
  have hcompactLine :
      AllAnchoredEulerCompressionCommutatorsCompactAt a rho →
        rho.re = 1 / 2 := by
    intro hcompact
    apply hdecayLine
    intro ε hε N
    obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (max N 2 + 1)
    have hmax : max N 2 < q := by omega
    have hq2 : 2 < q := (le_max_right N 2).trans_lt hmax
    refine ⟨q, hq, hmax, ?_⟩
    rw [essentialNorm_eq_zero_of_isCompactOperator (hcompact q hq hq2), mul_zero]
    exact hε
  have hlineCompact : rho.re = 1 / 2 →
      AllAnchoredEulerCompressionCommutatorsCompactAt a rho := by
    intro hline q hq hq2
    apply (firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff
      ha hq hq2).2
    have htwo : orbitwiseNatPrimeSeamCharge 2 rho = 0 :=
      (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half
        rho 2 (by norm_num)).2 hline
    have hqzero : orbitwiseNatPrimeSeamCharge q rho = 0 :=
      (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half
        rho q hq).2 hline
    rw [htwo, hqzero]
  exact ⟨⟨hdecayLine, hlineDecay⟩,
    ⟨hcompactLine, hlineCompact⟩,
    xiHurwitzPrimeTwoEulerBoundarySeam_eq_zero_iff hstrip⟩

end

end RHTower
