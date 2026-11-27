import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Noise.Ranks

/-! # Optimal stable reconstruction of signed damping from sorted log probabilities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Noise

open Finset _root_.HTGeometry

variable {X : Type*} [Fintype X]

def discrepancy (E : X → ℝ) (i : Fin (Fintype.card X)) := lowVector E i-highVector E i

def sqDistance {n : ℕ} (v w : Fin n → ℝ) := ∑ i, (v i-w i)^2

def separation (E : X → ℝ) := sqDistance (lowVector E) (highVector E)

theorem separation_nonneg (E : X → ℝ) : 0 ≤ separation E := by
  unfold separation sqDistance
  exact sum_nonneg fun _ _ => sq_nonneg _

def projection (E : X → ℝ) (v : Fin (Fintype.card X) → ℝ) := ∑ i, discrepancy E i*v i

def estimate (E : X → ℝ) (v : Fin (Fintype.card X) → ℝ) := 2*projection E v/separation E

private theorem equal_norms (E : X → ℝ) : (∑ i, (highVector E i)^2) = ∑ i, (lowVector E i)^2 := by
  simp only [highVector,neg_sq]
  exact Equiv.sum_comp Fin.revPerm (fun i => (lowVector E i)^2)

private theorem pairings (E : X → ℝ) : 2*projection E (lowVector E) = separation E ∧
    2*projection E (highVector E) = -separation E := by
  have low (i) : 2*(discrepancy E i*lowVector E i) =
      (lowVector E i-highVector E i)^2+((lowVector E i)^2-(highVector E i)^2) := by
    unfold discrepancy; ring
  have high (i) : 2*(discrepancy E i*highVector E i) =
      -((lowVector E i-highVector E i)^2)+((lowVector E i)^2-(highVector E i)^2) := by
    unfold discrepancy; ring
  constructor
  · simp only [projection,mul_sum,low,sum_add_distrib,sum_sub_distrib,equal_norms,sub_self,add_zero,separation,sqDistance]
  · simp only [projection,mul_sum,high,sum_add_distrib,sum_sub_distrib,equal_norms,sub_self,add_zero,
      sum_neg_distrib,separation,sqDistance]

private theorem projection_scale (E : X → ℝ) (a : ℝ) (v : Fin (Fintype.card X) → ℝ) :
    projection E (fun i => a*v i) = a*projection E v := by
  unfold projection
  rw [mul_sum]
  exact sum_congr rfl fun i _ => mul_left_comm _ _ _

/-- Centering removes the partition function; reflection makes the same linear statistic
recover signed damping on both rays, even at a uniform distribution. -/
theorem projection_gibbs (E : X → ℝ) (t : ℝ) :
    2*projection E (rankedLog (finiteGibbsStateWeight t E)) = t*separation E := by
  rcases le_total 0 t with h | h
  · rw [ranked_positive E h,projection_scale,mul_left_comm,(pairings E).1]
  · rw [ranked_negative E h,projection_scale,mul_left_comm,(pairings E).2,neg_mul_neg]

theorem exact_estimate (E : X → ℝ) (hd : 0 < separation E) (t : ℝ) :
    estimate E (rankedLog (finiteGibbsStateWeight t E)) = t := by
  rw [estimate,projection_gibbs,mul_div_cancel_right₀ _ hd.ne']

/-- A squared Euclidean perturbation bound valid on the entire data space. -/
theorem stability (E : X → ℝ) (hd : 0 < separation E) (v w : Fin (Fintype.card X) → ℝ) :
    (estimate E v-estimate E w)^2 ≤ (4/separation E)*sqDistance v w := by
  have dot : (∑ i, discrepancy E i*(v i-w i)) = projection E v-projection E w := by
    simp only [mul_sub,sum_sub_distrib,projection]
  have cs := sum_mul_sq_le_sq_mul_sq univ (discrepancy E) (fun i => v i-w i)
  rw [dot] at cs
  change (projection E v-projection E w)^2 ≤ separation E*sqDistance v w at cs
  have id : estimate E v-estimate E w = 2*(projection E v-projection E w)/separation E := by
    unfold estimate; ring
  rw [id,div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have cancel : (4/separation E*sqDistance v w)*separation E^2 = 4*(separation E*sqDistance v w) := by
    field_simp
  rw [cancel]
  nlinarith only [cs]

/-- Comparing the two unit dampings gives a matching lower bound for every exact inverse,
including nonlinear estimators. -/
theorem sharp_constant (E : X → ℝ) (hd : 0 < separation E) :
    IsLeast {K : ℝ | ∃ F : (Fin (Fintype.card X) → ℝ) → ℝ,
      (∀ t : ℝ, F (rankedLog (finiteGibbsStateWeight t E)) = t) ∧
      ∀ v w, (F v-F w)^2 ≤ K*sqDistance v w} (4/separation E) := by
  refine ⟨⟨estimate E,exact_estimate E hd,stability E hd⟩,?_⟩
  rintro K ⟨F,hF,hK⟩
  have pos := hF 1
  have neg := hF (-1)
  simp only [ranked_positive E zero_le_one,one_mul] at pos
  simp only [ranked_negative E (show (-1:ℝ) ≤ 0 by norm_num),neg_neg,one_mul] at neg
  have bound := hK (lowVector E) (highVector E)
  rw [pos,neg] at bound
  apply (div_le_iff₀ hd).mpr
  norm_num at bound
  exact bound

theorem zero_separation (E : X → ℝ) : separation E = 0 ↔ lowVector E = highVector E := by
  rw [separation,sqDistance,sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  constructor
  · intro h
    funext i
    have ht := h i (mem_univ _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ht)
  · intro h
    simp only [h,sub_self,zero_pow (by norm_num : 2 ≠ 0),implies_true]

/-- A finite energy list admits an exact scalar inverse on all dampings precisely when
its centered spectrum differs from its reflected spectrum. -/
theorem exact_inverse_iff (E : X → ℝ) :
    (∃ F : (Fin (Fintype.card X) → ℝ) → ℝ,
      ∀ t : ℝ, F (rankedLog (finiteGibbsStateWeight t E)) = t) ↔ 0 < separation E := by
  constructor
  · rintro ⟨F,h⟩
    have nonneg := separation_nonneg E
    by_contra! hd
    have same := (zero_separation E).mp (le_antisymm hd nonneg)
    have plus := h 1
    have minus := h (-1)
    simp only [ranked_positive E zero_le_one,one_mul,same] at plus
    simp only [ranked_negative E (show (-1:ℝ) ≤ 0 by norm_num),neg_neg,one_mul] at minus
    linarith only [plus,minus]
  · exact fun hd => ⟨estimate E,exact_estimate E hd⟩

/-- Exact reconstruction with squared Lipschitz bound K exists exactly above this threshold. -/
theorem stability_iff (E : X → ℝ) (K : ℝ) :
    (∃ F : (Fin (Fintype.card X) → ℝ) → ℝ,
      (∀ t : ℝ, F (rankedLog (finiteGibbsStateWeight t E)) = t) ∧
      ∀ v w, (F v-F w)^2 ≤ K*sqDistance v w) ↔ 0 < separation E ∧ 4 ≤ K*separation E := by
  constructor
  · rintro ⟨F,he,hb⟩
    have hd := (exact_inverse_iff E).mp ⟨F,he⟩
    exact ⟨hd,(div_le_iff₀ hd).mp ((sharp_constant E hd).2 ⟨F,he,hb⟩)⟩
  · rintro ⟨hd,h⟩
    refine ⟨estimate E,exact_estimate E hd,fun v w => (stability E hd v w).trans ?_⟩
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mpr h) (sum_nonneg fun _ _ => sq_nonneg _)

/-- The calibrated linear reading applies directly to the normalized two-copy shell output. -/
theorem outgoing_projection {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ) (s : ℂ) :
    2*projection (fun x : State c m => energy (level x)) (rankedLog (fun x => outgoingShare s x)) =
      (2*s.re-1)*separation (fun x : State c m => energy (level x)) := by
  simp_rw [outgoing_gibbs]
  exact projection_gibbs _ _

#print axioms projection_gibbs
#print axioms exact_estimate
#print axioms stability
#print axioms sharp_constant
#print axioms exact_inverse_iff
#print axioms stability_iff
#print axioms outgoing_projection

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Noise
