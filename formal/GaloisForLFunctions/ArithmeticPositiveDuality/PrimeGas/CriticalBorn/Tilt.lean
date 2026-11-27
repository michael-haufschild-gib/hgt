import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Law
import GaloisForLFunctions.HTGeometry.CircleSingularWitness
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.PSeries

/-! # Persistence of elementary atoms above the critical Born exponent -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter MeasureTheory Finset
open GaloisForLFunctions.HTGeometry
open scoped Topology

def bornWeight (σ : ℝ) (p : ℕ) : ℝ := (p : ℝ)^(-(2*σ))

def bornMass (σ : ℝ) (N : ℕ) := ∑ p ∈ primes N, bornWeight σ p

private theorem weight_ge_zero (σ : ℝ) (p : ℕ) : 0 ≤ bornWeight σ p :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem bornMass_pos (σ : ℝ) (N : ℕ) : 0 < bornMass σ N := by
  apply sum_pos' (fun p _ => weight_ge_zero σ p)
  exact ⟨2,Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩,
    Real.rpow_pos_of_pos (by norm_num) _⟩

/-- Angular law of the elementary heat amplitudes, sampled with their
squared moduli at real part σ. -/
def bornLaw (σ t : ℝ) (N : ℕ) : ProbabilityMeasure Circle :=
  ⟨(normalizedFiniteRealAtomicMeasure (primes N) (phase t) (bornWeight σ) : Measure Circle),
    isProbabilityMeasure_normalizedFiniteRealAtomicMeasure _ _ _ (fun p _ => weight_ge_zero σ p)
      (bornMass_pos σ N)⟩

theorem bornLaw_half (t : ℝ) (N : ℕ) : bornLaw (1/2) t N = phaseLaw t N := by
  have h : bornWeight (1/2) = weight := by
    funext p
    simp only [bornWeight,weight,show (2 : ℝ)*(1/2)=1 by norm_num,Real.rpow_neg_one]
  apply ProbabilityMeasure.toMeasure_injective
  change (normalizedFiniteRealAtomicMeasure (primes N) (phase t) (bornWeight (1/2)) : Measure Circle) =
    (normalizedFiniteRealAtomicMeasure (primes N) (phase t) weight : Measure Circle)
  rw [h]

private def total (σ : ℝ) := ∑' n : ℕ, bornWeight σ n

private theorem mass_le_total {σ : ℝ} (hσ : 1/2 < σ) (N : ℕ) : bornMass σ N ≤ total σ := by
  have hs : Summable (bornWeight σ) := Real.summable_nat_rpow.mpr (by linarith)
  exact hs.sum_le_tsum _ fun n _ => weight_ge_zero σ n

/-- Each represented prime contributes a positive lower bound uniform
in the cutoff, even when different primes give the same phase. -/
theorem persistent_atom {σ : ℝ} (hσ : 1/2 < σ) (t : ℝ) (p : Nat.Primes) :
    ∃ c : ℝ, 0 < c ∧ ∀ N, p.val ∈ primes N →
      c ≤ (bornLaw σ t N : Measure Circle).real {phase t p.val} := by
  classical
  have ht := (bornMass_pos σ 0).trans_le (mass_le_total hσ 0)
  refine ⟨bornWeight σ p.val / total σ,div_pos (Real.rpow_pos_of_pos
    (Nat.cast_pos.mpr p.property.pos) _) ht,?_⟩
  intro N hp
  change _ ≤ (finiteRealAtomicMeasure (primes N) (phase t)
    (fun q => bornWeight σ q / bornMass σ N) : Measure Circle).real _
  rw [real_finiteRealAtomicMeasure_apply _ _ _
    (fun q _ => div_nonneg (weight_ge_zero σ q) (bornMass_pos σ N).le) (measurableSet_singleton _)]
  refine (div_le_div_of_nonneg_left (weight_ge_zero σ p.val) (bornMass_pos σ N)
    (mass_le_total hσ N)).trans ?_
  apply single_le_sum (fun q _ => div_nonneg (weight_ge_zero σ q) (bornMass_pos σ N).le)
  exact mem_filter.mpr ⟨hp, rfl⟩

/-- Above the critical exponent even one elementary atom precludes a
Haar phase law, at every height. -/
theorem supercritical_not_haar {σ : ℝ} (hσ : 1/2 < σ) (t : ℝ) :
    ¬ Tendsto (bornLaw σ t) atTop (𝓝 uniform) := by
  obtain ⟨c,hc,low⟩ := persistent_atom hσ t ⟨2,Nat.prime_two⟩
  intro h
  let F : Set Circle := {phase t 2}
  have bound := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h
    (isClosed_singleton (x := phase t 2))
  change limsup (fun N => (bornLaw σ t N : Measure Circle) F) atTop ≤ circleLebesgue {phase t 2}
    at bound
  rw [circleLebesgue_singleton] at bound
  have lower : ∀ N, ENNReal.ofReal c ≤ (bornLaw σ t N : Measure Circle) F := by
    intro N
    have two : 2 ∈ primes N := Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩
    have hr := low N two
    exact (ENNReal.ofReal_le_ofReal hr).trans (le_of_eq (ENNReal.ofReal_toReal (measure_ne_top _ _)))
  have hlim : ENNReal.ofReal c ≤ limsup (fun N => (bornLaw σ t N : Measure Circle) F) atTop :=
    le_limsup_of_frequently_le (Eventually.of_forall lower).frequently
  exact (ENNReal.ofReal_pos.mpr hc).not_ge (hlim.trans bound)

#print axioms bornLaw_half
#print axioms persistent_atom
#print axioms supercritical_not_haar

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
