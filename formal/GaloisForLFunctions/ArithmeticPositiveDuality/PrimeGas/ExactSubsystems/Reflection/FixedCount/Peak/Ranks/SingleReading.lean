import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Thermometry
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Squarefree.Thermometry

/-! # The two extreme probability ratios in a single outgoing distribution -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks

open Real Finset _root_.HTGeometry
open scoped ComplexConjugate

variable {X : Type*} [Fintype X]

def reciprocalLaw (P : X → ℝ) (x : X) := (P x)⁻¹ / ∑ y, (P y)⁻¹

/-- Entrywise reciprocal normalization reverses the inverse temperature. -/
theorem reciprocal_gibbs (E : X → ℝ) (t : ℝ) :
    reciprocalLaw (finiteGibbsStateWeight t E) = finiteGibbsStateWeight (-t) E := by
  funext x
  letI : Nonempty X := ⟨x⟩
  have hi (y : X) : (finiteGibbsStateWeight t E y)⁻¹ = finiteGibbsPartition t E * exp (t*E y) := by
    rw [finiteGibbsStateWeight,inv_div,div_eq_mul_inv,neg_mul,exp_neg,inv_inv]
  simp only [reciprocalLaw,hi,← mul_sum]
  rw [mul_div_mul_left _ _ (finiteGibbsPartition_pos t E).ne']
  simp only [finiteGibbsStateWeight,finiteGibbsPartition,neg_neg]

/-- For positive entries, the two largest reciprocal weights read the second-smallest
and smallest original probabilities. The common normalization cancels from their ratio. -/
theorem reciprocal_odds_at (P : X → ℝ) (hp : ∀ i, 0 < P i) (u v : X) (hne : u ≠ v)
    (hu : ∀ i, P u ≤ P i) (hv : ∀ i, i ≠ u → P v ≤ P i) :
    logOdds (reciprocalLaw P) = log (P v/P u) := by
  have hz : 0 < ∑ y, (P y)⁻¹ := sum_pos (fun i _ => inv_pos.mpr (hp i)) ⟨u,mem_univ _⟩
  have anti {i j} (h : P i ≤ P j) : reciprocalLaw P j ≤ reciprocalLaw P i :=
    div_le_div_of_nonneg_right ((inv_le_inv₀ (hp j) (hp i)).mpr h) hz.le
  rw [logOdds_at _ u v hne (fun i => anti (hu i)) (fun i hi => anti (hv i hi))]
  simp only [reciprocalLaw,div_div_div_cancel_right₀ hz.ne',inv_div_inv]

/-- The reflected outgoing law of every occupation sector can be read from the original one. -/
theorem reciprocal_outgoing (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) :
    reciprocalLaw (fun x : State c m => outgoingShare s x) = fun x => outgoingShare (1-conj s) x := by
  simp_rw [outgoing_gibbs]
  rw [show 2*(1-conj s).re-1 = -(2*s.re-1) by rw [Complex.sub_re,Complex.one_re,Complex.conj_re]; ring]
  exact reciprocal_gibbs _ _

/-- Log ratio at the top of the measured spectrum minus the log ratio at its bottom. -/
def tailContrast (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) :=
  measuredOdds S c m s - logOdds (reciprocalLaw (fun x : State c m => outgoingShare s x))

theorem tailContrast_eq (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) :
    tailContrast S c m s = measuredOdds S c m s - measuredOdds S c m (1-conj s) := by
  rw [tailContrast,reciprocal_outgoing]
  rfl

theorem single_reading_damping (S : Finset Nat.Primes) (h : 3 ≤ S.card) (n : ℕ) (s : ℂ) :
    tailContrast S (fun _ => n+1) (n+1) s / edgeDifference S h = 2*s.re-1 := by
  rw [tailContrast_eq,recover_damping S h]

theorem single_reading_isometry (S : Finset Nat.Primes) (h : 3 ≤ S.card) (n : ℕ) (s : ℂ) :
    tailContrast S (fun _ => n+1) (n+1) s = 0 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [tailContrast_eq,sub_eq_zero,ranked_match_iff_isometry S h]

theorem single_reading_squarefree (S : Finset Nat.Primes) (k : ℕ) (h : k+1 < S.card) (s : ℂ) :
    tailContrast S (fun _ => 1) (k+1) s = (2*s.re-1)*Squarefree.fillingDifference S k h := by
  rw [tailContrast_eq,Squarefree.signed_filling_contrast S k h]

theorem single_reading_full_match (S : Finset Nat.Primes) (k : ℕ) (h : k+1 < S.card) (s : ℂ) :
    tailContrast S (fun _ => 1) (k+1) s = 0 ↔ Matched S (fun _ => 1) (k+1) s := by
  rw [tailContrast_eq,sub_eq_zero,Squarefree.ranked_match_iff_full_match S k h]

#print axioms reciprocal_gibbs
#print axioms reciprocal_odds_at
#print axioms reciprocal_outgoing
#print axioms single_reading_damping
#print axioms single_reading_isometry
#print axioms single_reading_squarefree
#print axioms single_reading_full_match

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks
