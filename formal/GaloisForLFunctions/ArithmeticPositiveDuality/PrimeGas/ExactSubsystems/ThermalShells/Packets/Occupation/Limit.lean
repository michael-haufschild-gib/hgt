import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Sector

/-! # Binomial occupation laws on squarefree prime packets -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Finset Filter Topology Real _root_.RHTower
open Set (Ioi)
open BinaryOrientation.LargestPrime.Bands

/-- Total variation for two readings on the count space {0,...,m}. -/
def countDistance (m : ℕ) (P Q : Finset ℕ → ℝ) :=
  (range (m+1)).powerset.sup' (powerset_nonempty _) fun B => |P B-Q B|

theorem distance_nonneg (m : ℕ) (P Q : Finset ℕ → ℝ) : 0 ≤ countDistance m P Q :=
  (abs_nonneg (P ∅-Q ∅)).trans (le_sup' (fun B => |P B-Q B|) (mem_powerset.mpr (empty_subset _)))

theorem distance_le {m : ℕ} {P Q : Finset ℕ → ℝ} {r : ℝ}
    (h : ∀ B ⊆ range (m+1), |P B-Q B| ≤ r) : countDistance m P Q ≤ r :=
  sup'_le _ _ fun B hB => h B (mem_powerset.mp hB)

theorem continuous_bin (m j : ℕ) : Continuous (bin m j) := by
  change Continuous (fun p : ℝ => (m.choose j:ℝ)*p^j*(1-p)^(m-j))
  fun_prop

theorem bin_sum (m : ℕ) (p : ℝ) : binEvent m (range (m+1)) p = 1 := by
  calc _ = (p+(1-p))^m := by rw [add_pow]; unfold binEvent; apply sum_congr rfl; intro j _; unfold bin; ring
       _ = 1 := by rw [show p+(1-p)=1 by ring,one_pow]

private theorem collision_vanishes {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m : Ioi (0:ℝ) → ℕ)
    (hm : Tendsto (fun h => ((m h).choose 2:ℝ)*scale (c/h.val)) criticalApproach (𝓝 0)) :
    Tendsto (fun h => let t := c/h.val
      ((m h).choose 2:ℝ)*∑ p, draw (added c d h) (both D k t) b t p^2) criticalApproach (𝓝 0) := by
  have H := hm.mul (squared_draw_limit hc hcd hD hk b)
  rw [zero_mul] at H
  apply H.congr
  intro h
  have hs : 0 < scale (c/h.val) := div_pos (sq_pos_of_pos (div_pos hc h.property)) (exp_pos _)
  change _ * scale (c/h.val) * (_ / scale (c/h.val)) = _
  rw [mul_assoc,← mul_div_assoc,mul_div_cancel_left₀ _ hs.ne']

/-- Even a growing count has a binomial approximation in total variation when the birthday
scale times the number of coordinate pairs tends to zero. The parameter is the finite packet share. -/
theorem growing_binomial {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m : Ioi (0:ℝ) → ℕ)
    (hm : Tendsto (fun h => ((m h).choose 2:ℝ)*scale (c/h.val)) criticalApproach (𝓝 0)) :
    Tendsto (fun h => countDistance (m h) (fun B => read c d D k b (m h) B h)
      (fun B => binEvent (m h) B (upper D k b (c/h.val)))) criticalApproach (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun h => distance_nonneg _ _ _) _ (collision_vanishes hc hcd hD hk b m hm)
  filter_upwards [finite_error hc hcd hD hk b] with h hh
  exact distance_le fun B _ => hh (m h) B

/-- The growing-count selection is eventually populated in the same collision regime. -/
theorem eventual_sector {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m : Ioi (0:ℝ) → ℕ)
    (hm : Tendsto (fun h => ((m h).choose 2:ℝ)*scale (c/h.val)) criticalApproach (𝓝 0)) :
    ∀ᶠ h in criticalApproach, (sector (added c d h) (both D k (c/h.val)) (m h)).Nonempty := by
  filter_upwards [finite_error hc hcd hD hk b,(collision_vanishes hc hcd hD hk b m hm).eventually_lt_const zero_lt_one]
    with h hh hs
  by_contra hn
  have he := hh (m h) (range (m h+1))
  dsimp only at he hs
  rw [bin_sum] at he
  simp only [read,countRead,share,not_nonempty_iff_eq_empty.mp hn,mass,sum_empty,div_zero,zero_sub,abs_neg,abs_one] at he
  exact (not_lt_of_ge he) hs

private theorem const_scale {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun h : Ioi (0:ℝ) => (m.choose 2:ℝ)*scale (c/h.val)) criticalApproach (𝓝 0) := by
  simpa only [mul_zero,Function.comp_apply] using (scale_zero.comp (translation_limit hc)).const_mul (m.choose 2:ℝ)

private theorem prob_limit {c D k : ℝ} (hc : 0 < c) (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => upper D k b (c/h.val)) criticalApproach (𝓝 (upperProbability D k b)) :=
  (upper_limit hD hk b).comp (translation_limit hc)

/-- Every count event, including the empty and full alternatives, has its binomial limit. -/
theorem event_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m : ℕ) (B : Finset ℕ) :
    Tendsto (read c d D k b m B) criticalApproach (𝓝 (binEvent m B (upperProbability D k b))) := by
  have hp := prob_limit hc hD hk b
  have lim : Tendsto (fun h => binEvent m B (upper D k b (c/h.val))) criticalApproach
      (𝓝 (binEvent m B (upperProbability D k b))) := tendsto_finsetSum _ fun j _ => (continuous_bin m j).continuousAt.tendsto.comp hp
  have err := collision_vanishes hc hcd hD hk b (fun _ => m) (const_scale hc m)
  have lo := lim.sub err
  have hi := lim.add err
  rw [sub_zero] at lo
  rw [add_zero] at hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi
  · filter_upwards [finite_error hc hcd hD hk b] with h hh
    linarith only [(abs_le.mp (hh m B)).1]
  · filter_upwards [finite_error hc hcd hD hk b] with h hh
    linarith only [(abs_le.mp (hh m B)).2]

theorem cell_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m j : ℕ) : Tendsto (read c d D k b m {j}) criticalApproach (𝓝 (bin m j (upperProbability D k b))) := by
  simpa only [binEvent,sum_singleton] using event_limit hc hcd hD hk b m {j}

/-- Total variation convergence of the physical upper-occupation count to its fixed binomial law. -/
theorem binomial_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m : ℕ) :
    Tendsto (fun h => countDistance m (fun B => read c d D k b m B h)
      (fun B => binEvent m B (upperProbability D k b))) criticalApproach (𝓝 0) := by
  let P := (range (m+1)).powerset
  have each (B : Finset ℕ) := ((event_limit hc hcd hD hk b m B).sub
    (tendsto_const_nhds (x := binEvent m B (upperProbability D k b)))).abs
  have total := tendsto_finsetSum P fun B _ => each B
  simp only [sub_self,abs_zero,sum_const_zero] at total
  apply squeeze_zero' (Eventually.of_forall fun h => distance_nonneg _ _ _) _ total
  exact Eventually.of_forall fun h => distance_le fun B hB =>
    single_le_sum (s := P) (f := fun A => |read c d D k b m A h-binEvent m A (upperProbability D k b)|)
      (fun _ _ => abs_nonneg _) (mem_powerset.mpr hB)

#print axioms eventual_sector
#print axioms growing_binomial
#print axioms event_limit
#print axioms binomial_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
