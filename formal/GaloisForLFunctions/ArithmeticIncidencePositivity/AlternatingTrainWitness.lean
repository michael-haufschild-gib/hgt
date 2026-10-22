import GaloisForLFunctions.ArithmeticIncidencePositivity.ResonantTrainWitness

/-!
# The alternating train: the Liouville-twisted envelope of a tower is attained

The twisted tower law bounds the lag charge at a **negative** ratio `z = −p^{−1/2}`, the ratio of
the Liouville twin of a tower. Its matching witness is the **alternating train**: `M + 1` disjoint
copies of one bump at the spacing `L`, with the signs `(−1)^k`,

    S⁻ = Σ_{k ≤ M} (−1)^k g(· + kL),     A_{S⁻}(mL) = (−1)^m (M + 1 − m) A_g(0),

so its correlation carries the parity of the lag index. Consequently the twisted charge of the
alternating train equals the untwisted charge of the resonant train at the same positive ratio:

    geoLagCharge (−z) L S⁻ = geoLagCharge z L S,

and the sharpness of the Euler envelope transfers verbatim. At `L = log p`, `z = p^{−1/2}` the
extremal test of the Liouville-twisted law is therefore the train on the tower `{1, p, p², …}` with
alternating signs: the parity model's envelope is attained by the parity-signed train, exactly as
the arithmetic envelope is attained by the unsigned one. The twisted law's content, like the
untwisted one's, is its discount.
-/

open MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {g : ℝ → ℝ}

/-- The alternating train: `M + 1` copies of `g` at the spacing `L` with the signs `(−1)^k`. -/
def alternatingTrain (g : ℝ → ℝ) (L : ℝ) (M : ℕ) : ℝ → ℝ :=
  translateComb g (M + 1) (fun k => (-1) ^ k) (fun k => (k : ℝ) * L)

/-- **The autocorrelation of the alternating train.** At the lag `mL` the overlap is the same
`M + 1 − m` copies as for the resonant train, with the sign of the lag parity. -/
theorem autoCorr_alternatingTrain (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M m : ℕ) :
    autoCorr (alternatingTrain g L M) ((m : ℝ) * L)
      = (-1) ^ m * (((M + 1 - m : ℕ) : ℝ) * autoCorr g 0) := by
  have hgn : ContCompact g := ⟨hg, hgc⟩
  have hexp : autoCorr (alternatingTrain g L M) ((m : ℝ) * L)
      = ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
          (-1 : ℝ) ^ j * (-1 : ℝ) ^ k
            * autoCorr g (((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L) := by
    rw [autoCorr_eq_testPairing,
      show alternatingTrain g L M
        = translateComb g (M + 1) (fun k => (-1) ^ k) (fun k => (k : ℝ) * L) from rfl,
      show (fun u => translateComb g (M + 1) (fun k => (-1 : ℝ) ^ k) (fun k => (k : ℝ) * L)
            (u + (m : ℝ) * L))
          = translateComb g (M + 1) (fun k => (-1 : ℝ) ^ k)
              (fun k => (k : ℝ) * L + (m : ℝ) * L) by
        funext u
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show u + (m : ℝ) * L + (k : ℝ) * L = u + ((k : ℝ) * L + (m : ℝ) * L) by ring],
      testPairing_comb hgn]
  have hrow : ∀ j ∈ Finset.range (M + 1),
      ∑ k ∈ Finset.range (M + 1),
          (-1 : ℝ) ^ j * (-1 : ℝ) ^ k
            * autoCorr g (((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L)
        = if m ≤ j then (-1 : ℝ) ^ m * autoCorr g 0 else 0 := by
    intro j hj
    have hterm : ∀ k ∈ Finset.range (M + 1),
        (-1 : ℝ) ^ j * (-1 : ℝ) ^ k
            * autoCorr g (((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L)
          = if j = k + m then (-1 : ℝ) ^ j * (-1 : ℝ) ^ k * autoCorr g 0 else 0 := by
      intro k _
      by_cases h : j = k + m
      · rw [if_pos h, h]
        push_cast
        rw [show ((k : ℝ) * L + (m : ℝ) * L) - ((k : ℝ) + (m : ℝ)) * L = 0 by ring]
      · rw [if_neg h]
        have hne : ((k : ℤ) + (m : ℤ) - (j : ℤ)) ≠ 0 := fun hc => h (by omega)
        have hcast : ((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L
            = (((k : ℤ) + (m : ℤ) - (j : ℤ) : ℤ) : ℝ) * L := by push_cast; ring
        rw [hcast, autoCorr_eq_zero_of_mul_spacing hw hL hsupp hne, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hmj : m ≤ j
    · rw [if_pos hmj]
      have hmem : j - m ∈ Finset.range (M + 1) := by
        rw [Finset.mem_range] at hj ⊢
        omega
      rw [Finset.sum_eq_single_of_mem (j - m) hmem (fun k _ hk => ?_)]
      · rw [if_pos (by omega : j = j - m + m)]
        -- the two signs combine to the parity of the lag index
        have hsplit : j + (j - m) = 2 * (j - m) + m := by omega
        rw [← pow_add, hsplit, pow_add, pow_mul]
        norm_num
      · rw [if_neg (by omega : ¬ j = k + m)]
    · rw [if_neg hmj]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (by omega : ¬ j = k + m)]
  have hfilter : (Finset.range (M + 1)).filter (fun j => m ≤ j) = Finset.Ico m (M + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hexp, Finset.sum_congr rfl hrow, ← Finset.sum_filter, hfilter, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul]
  ring

/-- **The twisted charge of the alternating train is the untwisted charge of the resonant train.**
The parity of the signs cancels the parity of the negative ratio lag by lag. -/
theorem geoLagCharge_alternatingTrain_eq (hg : Continuous g) (hgc : HasCompactSupport g)
    {w L z : ℝ} (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ) :
    geoLagCharge (-z) L (alternatingTrain g L M) = geoLagCharge z L (resonantTrain g L M) := by
  rw [geoLagCharge, geoLagCharge]
  refine tsum_congr fun m => ?_
  have harg : ((m : ℝ) + 1) * L = ((m + 1 : ℕ) : ℝ) * L := by push_cast; ring
  have hsq : ((-1 : ℝ) ^ (m + 1)) * ((-1 : ℝ) ^ (m + 1)) = 1 := by
    rw [← pow_add, show (m + 1) + (m + 1) = 2 * (m + 1) by ring, pow_mul]
    norm_num
  rw [harg, autoCorr_alternatingTrain hg hgc hw hL hsupp M (m + 1),
    autoCorr_resonantTrain hg hgc hw hL hsupp M (m + 1), neg_pow]
  linear_combination (z ^ (m + 1) * (((M + 1 - (m + 1) : ℕ) : ℝ) * autoCorr g 0)) * hsq

/-- **The twisted envelope is attained.** The twisted lag charge of the alternating train matches
the resonant train's untwisted charge, so the Liouville-twisted tower law is sharp: its extremal
test is the alternating train on the tower `{1, p, p², …}`. -/
theorem geoLagCharge_alternatingTrain_ge (hg : Continuous g) (hgc : HasCompactSupport g)
    {w L z : ℝ} (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (hz0 : 0 < z)
    (hz1 : z < 1) (M : ℕ) :
    (((M : ℝ) + 1) * ((z - z ^ (M + 1)) / (1 - z)) - z / (1 - z) ^ 2) * autoCorr g 0
      ≤ geoLagCharge (-z) L (alternatingTrain g L M) := by
  rw [geoLagCharge_alternatingTrain_eq hg hgc hw hL hsupp M]
  exact geoLagCharge_resonantTrain_ge hg hgc hw hL hsupp hz0 hz1 M

/-- The mass of the alternating train is that of the resonant train: `M + 1` bumps. -/
theorem autoCorr_alternatingTrain_zero (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ) :
    autoCorr (alternatingTrain g L M) 0 = ((M : ℝ) + 1) * autoCorr g 0 := by
  have h := autoCorr_alternatingTrain hg hgc hw hL hsupp M 0
  rw [Nat.cast_zero, zero_mul] at h
  rw [h]
  norm_num

end GaloisForLFunctions.ArithmeticIncidencePositivity
