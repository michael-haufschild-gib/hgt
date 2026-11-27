import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Capped.FirstMismatch
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Observable

/-! # First discrepancy in peak-relative probabilities under bounded occupation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped

open Real _root_.HTGeometry
open scoped ComplexConjugate

/-- Logarithmic losses relative to the largest probability; no state labels enter the reading. -/
def losses {X : Type*} (P : X → ℝ) := Set.range fun x => log (sSup (Set.range P)/P x)

def scale (t : ℝ) (A : Set ℝ) := (fun x => t*x) '' A

theorem gibbs_losses {X : Type*} [Fintype X] (E : X → ℝ) (t : ℝ) (u : X)
    (hu : ∀ x, t*E u ≤ t*E x) :
    losses (finiteGibbsStateWeight t E) = Set.range (fun x => t*(E x-E u)) := by
  apply congrArg Set.range
  funext x
  change log (largest E t / finiteGibbsStateWeight t E x) = _
  rw [largest_at u hu,← weight_eq_inv E t u,GaloisForLFunctions.HTGeometry.finiteGibbsStateWeight_ratio,log_exp]

theorem least_scaled {A B : Set ℝ} {z t : ℝ} (ht : 0 < t) (hz : IsLeast (mismatch A B) z) :
    IsLeast (mismatch (scale t A) (scale t B)) (t*z) := by
  have eqv : scale t (mismatch A B) = mismatch (scale t A) (scale t B) :=
    Set.image_symmDiff (mul_right_injective₀ ht.ne') A B
  rw [← eqv]
  exact ⟨⟨z,hz.1,rfl⟩,fun _ ⟨y,hy,he⟩ => he ▸ mul_le_mul_of_nonneg_left (hz.2 hy) ht.le⟩

variable (S : Finset Nat.Primes) (hs : S.card = 3) (k l : ℕ)

private theorem positive_losses (t : ℝ) (ht : 0 ≤ t) :
    losses (finiteGibbsStateWeight t (fun x : Sector S k l => energy (level x))) =
        scale t (lowerSpectrum S hs k l) ∧
    losses (finiteGibbsStateWeight (-t) (fun x : Sector S k l => energy (level x))) =
        scale t (upperSpectrum S hs k l) := by
  obtain ⟨lo,hi⟩ := extrema S hs k l
  obtain ⟨u,hu⟩ := lo.1
  obtain ⟨v,hv⟩ := hi.1
  change energy (level u) = lowerEnergy S hs k l at hu
  change energy (level v) = upperEnergy S hs k l at hv
  constructor
  · rw [gibbs_losses _ t u (fun x => mul_le_mul_of_nonneg_left
      (hu.le.trans (lo.2 (Set.mem_range_self x))) ht),scale,lowerSpectrum,← Set.range_comp]
    rw [← hu]
    rfl
  · rw [gibbs_losses _ (-t) v (fun x => mul_le_mul_of_nonpos_left
      ((hi.2 (Set.mem_range_self x)).trans hv.ge) (neg_nonpos.mpr ht)),scale,upperSpectrum,← Set.range_comp]
    apply congrArg Set.range
    funext x
    change -t*(energy (level x)-energy (level v)) = t*(upperEnergy S hs k l-energy (level x))
    rw [← hv]
    ring

private theorem first_loss_positive (hk : k ≠ l) {t : ℝ} (ht : 0 < t) :
    IsLeast (mismatch (losses (finiteGibbsStateWeight t (fun x : Sector S k l => energy (level x))))
      (losses (finiteGibbsStateWeight (-t) (fun x : Sector S k l => energy (level x)))))
      (t*threshold k l (lowerGap S hs) (upperGap S hs)) := by
  rw [(positive_losses S hs k l t ht.le).1,(positive_losses S hs k l t ht.le).2]
  exact least_scaled ht (first_unpaired_energy S hs k l hk)

def outgoingLosses (s : ℂ) := losses (fun x : Sector S k l => outgoingShare s x)

/-- At every off-line parameter, the first unpaired log loss is the first asymmetric
excitation times absolute damping. This is measured from the actual two-copy output. -/
theorem first_unpaired_loss (hk : k ≠ l) (s : ℂ) (hs' : s.re ≠ 1/2) :
    IsLeast (mismatch (outgoingLosses S k l s) (outgoingLosses S k l (1-conj s)))
      (|2*s.re-1| * threshold k l (lowerGap S hs) (upperGap S hs)) := by
  unfold outgoingLosses
  simp_rw [outgoing_gibbs]
  rw [show 2*(1-conj s).re-1 = -(2*s.re-1) by rw [Complex.sub_re,Complex.one_re,Complex.conj_re]; ring]
  rcases lt_or_gt_of_ne hs' with h | h
  · have ht : 2*s.re-1 < 0 := by linarith only [h]
    have h' := first_loss_positive S hs k l hk (neg_pos.mpr ht)
    simpa only [neg_neg,abs_of_neg ht,mismatch,Set.union_comm] using h'
  · have ht : 0 < 2*s.re-1 := by linarith only [h]
    rw [abs_of_pos ht]
    exact first_loss_positive S hs k l hk ht

#print axioms gibbs_losses
#print axioms first_unpaired_loss

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped
