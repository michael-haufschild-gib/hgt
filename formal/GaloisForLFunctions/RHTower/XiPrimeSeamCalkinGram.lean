import GaloisForLFunctions.RHTower.SoninEulerEssentialNorm
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse

/-!
# Xi prime-seam Calkin Gram criterion

Weight each literal two-prime archimedean Euler Gram entry by the difference of the canonical
FE--Schwarz seam charges at its two primes.  Exact noncompactness of every unweighted entry makes
compactness of the weighted corner equivalent to equality of those two charges.  Requiring this
for all prime pairs on one open-strip fibre is therefore equivalent to the critical-line equation;
requiring it on every Xi divisor fibre is equivalent to RH.

This is an endpoint theorem, not a source-side proof of compactness.  Its positive contradiction
form says that false RH produces an actual Xi divisor fibre and prime pair whose seam-weighted
Gram corner survives nontrivially in the Calkin algebra.
-/

open Complex

namespace RHTower

noncomputable section

/-- The literal two-prime Euler Gram entry weighted by the difference of the two canonical seam
charges. -/
def orbitwisePrimeSeamCalkinGramCorner
    (a : ℝ) (p q : ℕ) (rho : ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  (orbitwiseNatPrimeSeamCharge p rho - orbitwiseNatPrimeSeamCharge q rho) •
    archimedeanPrimeEulerQuadraticCorner a (p : ℝ) (q : ℝ)

/-- Every prime-pair seam Gram corner is compact at this fibre. -/
def OrbitwisePrimeSeamCalkinGramCompact (a : ℝ) (rho : ℂ) : Prop :=
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q →
    IsCompactOperator (orbitwisePrimeSeamCalkinGramCorner a p q rho)

/-- The exact essential norm of a seam-weighted prime Gram corner is the charge difference times
the reciprocal square-root prime weight. -/
theorem essentialNorm_orbitwisePrimeSeamCalkinGramCorner
    (a : ℝ) (p q : ℕ) (rho : ℂ) (ha : 0 < a)
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    essentialNorm (orbitwisePrimeSeamCalkinGramCorner a p q rho) =
      ‖orbitwiseNatPrimeSeamCharge p rho - orbitwiseNatPrimeSeamCharge q rho‖ *
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))⁻¹ := by
  rw [orbitwisePrimeSeamCalkinGramCorner, essentialNorm_smul,
    essentialNorm_archimedeanPrimeEulerQuadraticCorner_natPrime a p q ha hp hq]

/-- Because the underlying two-prime Gram entry is noncompact, its seam-weighted version is
compact exactly when the two seam charges agree. -/
theorem orbitwisePrimeSeamCalkinGramCorner_isCompactOperator_iff
    (a : ℝ) (p q : ℕ) (rho : ℂ) (ha : 0 < a)
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    IsCompactOperator (orbitwisePrimeSeamCalkinGramCorner a p q rho) ↔
      orbitwiseNatPrimeSeamCharge p rho = orbitwiseNatPrimeSeamCharge q rho := by
  constructor
  · intro hcompact
    by_contra hne
    let b : ℂ := orbitwiseNatPrimeSeamCharge p rho - orbitwiseNatPrimeSeamCharge q rho
    let T : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
      archimedeanPrimeEulerQuadraticCorner a (p : ℝ) (q : ℝ)
    have hb : b ≠ 0 := sub_ne_zero.mpr hne
    have hcompact' : IsCompactOperator (b • T) := by
      simpa [orbitwisePrimeSeamCalkinGramCorner, b, T] using hcompact
    have hunscaled : IsCompactOperator (b⁻¹ • (b • T)) := hcompact'.smul b⁻¹
    have heq : b⁻¹ • (b • T) = T := by
      rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    apply archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator
      a (p : ℝ) (q : ℝ) ha (by exact_mod_cast hp.one_lt)
        (by exact_mod_cast hq.one_lt)
    change IsCompactOperator T
    rw [← heq]
    exact hunscaled
  · intro hcharge
    rw [orbitwisePrimeSeamCalkinGramCorner, hcharge, sub_self, zero_smul]
    exact isCompactOperator_zero

/-- On the open strip, compactness of every seam Gram corner is exactly the critical-line
equation. -/
theorem orbitwisePrimeSeamCalkinGramCompact_iff_re_eq_half
    (a : ℝ) (rho : ℂ) (ha : 0 < a) (hstrip : 0 < rho.re ∧ rho.re < 1) :
    OrbitwisePrimeSeamCalkinGramCompact a rho ↔ rho.re = 1 / 2 := by
  rw [← orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip]
  constructor
  · intro hcompact p q hp hq
    exact (orbitwisePrimeSeamCalkinGramCorner_isCompactOperator_iff
      a p q rho ha hp hq).mp (hcompact p q hp hq)
  · intro hcoherent p q hp hq
    exact (orbitwisePrimeSeamCalkinGramCorner_isCompactOperator_iff
      a p q rho ha hp hq).mpr (hcoherent p q hp hq)

/-- Every seam-weighted prime Gram corner is compact on every Xi divisor fibre. -/
def XiPrimeSeamCalkinGramCompact (a : ℝ) : Prop :=
  ∀ rho : XiDivisorSupport, OrbitwisePrimeSeamCalkinGramCompact a (rho : ℂ)

/-- Global seam Gram compactness is equivalent to RH for every positive Sonin cutoff. -/
theorem xiPrimeSeamCalkinGramCompact_iff_riemannHypothesis
    (a : ℝ) (ha : 0 < a) :
    XiPrimeSeamCalkinGramCompact a ↔ RiemannHypothesis := by
  rw [← xiPrimeSeamChargesCoherent_iff_riemannHypothesis]
  constructor
  · intro hcompact rho p q hp hq
    exact (orbitwisePrimeSeamCalkinGramCorner_isCompactOperator_iff
      a p q (rho : ℂ) ha hp hq).mp (hcompact rho p q hp hq)
  · intro hcoherent rho p q hp hq
    exact (orbitwisePrimeSeamCalkinGramCorner_isCompactOperator_iff
      a p q (rho : ℂ) ha hp hq).mpr (hcoherent rho p q hp hq)

/-- **Positive contradiction form.**  If RH is false, one actual Xi divisor fibre and one prime
pair have a seam-weighted Gram corner that is not compact. -/
theorem exists_noncompact_primeSeamCalkinGramCorner_of_not_riemannHypothesis
    (a : ℝ) (ha : 0 < a) (hRH : ¬ RiemannHypothesis) :
    ∃ rho : XiDivisorSupport, ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
      ¬ IsCompactOperator (orbitwisePrimeSeamCalkinGramCorner a p q (rho : ℂ)) := by
  have hnot : ¬ XiPrimeSeamCalkinGramCompact a := by
    exact fun hcompact => hRH
      ((xiPrimeSeamCalkinGramCompact_iff_riemannHypothesis a ha).mp hcompact)
  simp only [XiPrimeSeamCalkinGramCompact, OrbitwisePrimeSeamCalkinGramCompact,
    not_forall] at hnot
  obtain ⟨rho, p, q, hp, hq, hnoncompact⟩ := hnot
  exact ⟨rho, p, q, hp, hq, hnoncompact⟩

end

end RHTower
