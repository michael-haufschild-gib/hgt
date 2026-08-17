import GaloisForLFunctions.RHTower.ProlateIndexedRatioLimit
import GaloisForLFunctions.RHTower.ProlateIndexedTotalMass

/-!
# From the anchor to the centre

The pair anchor comparison converts the amplitude ratio at the common band point into one at the
centre.  For each rung the quotient `R_k(y₀)/R_k(0)` converges to the nonzero Hermite quotient
`φ_{2k}(x₀)/φ_{2k}(0)`, so eventually it is trapped between half and twice that value, and the two
squared amplitudes at the centre inherit the `c^{-1/2}` comparison with an extra absolute constant.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The Hermite quotient of a rung at the pair anchor. -/
def pairAnchorHermiteQuotient (m n k : ℕ) : ℝ :=
  hermiteFun (2 * k) (prolatePairAnchor m n) / hermiteFun (2 * k) 0

theorem pairAnchorHermiteQuotient_ne_zero (m n : ℕ) (k : ℕ) (hk : k = m ∨ k = n) :
    pairAnchorHermiteQuotient m n k ≠ 0 := by
  have hden : hermiteFun (2 * k) 0 ≠ 0 := by
    have := indexedRungAmplitude_ne_zero k
    rwa [indexedRungAmplitude] at this
  have hnum : hermiteFun (2 * k) (prolatePairAnchor m n) ≠ 0 := by
    rcases hk with h | h
    · rw [h]; exact (prolatePairAnchor_spec m n).2.1
    · rw [h]; exact (prolatePairAnchor_spec m n).2.2
  rw [pairAnchorHermiteQuotient]
  exact div_ne_zero hnum hden

/-- The quotient of the rung at the anchor by its centre value converges to the Hermite quotient. -/
theorem tendsto_pairAnchor_quotient (m n k : ℕ) :
    Tendsto (fun a : ℝ => (signedModeRadialData a k).R (pairAnchorPoint m n a)
        / (signedModeRadialData a k).R 0)
      atTop (𝓝 (pairAnchorHermiteQuotient m n k)) := by
  have hden : hermiteFun (2 * k) 0 ≠ 0 := by
    have := indexedRungAmplitude_ne_zero k
    rwa [indexedRungAmplitude] at this
  have h := tendsto_pairAnchor_ratio m n k
  have hdiv := h.div_const (hermiteFun (2 * k) 0)
  rw [pairAnchorHermiteQuotient]
  refine hdiv.congr fun a => ?_
  rw [pairAnchorPoint]
  field_simp

/-- Eventually the quotient is trapped between half and twice its limit in absolute value. -/
theorem eventually_pairAnchor_quotient_bounds (m n : ℕ) (k : ℕ) (hk : k = m ∨ k = n) :
    ∀ᶠ a : ℝ in atTop,
      |pairAnchorHermiteQuotient m n k| / 2
          ≤ |(signedModeRadialData a k).R (pairAnchorPoint m n a)
            / (signedModeRadialData a k).R 0| ∧
        |(signedModeRadialData a k).R (pairAnchorPoint m n a)
            / (signedModeRadialData a k).R 0| ≤ 2 * |pairAnchorHermiteQuotient m n k| := by
  set q : ℝ := pairAnchorHermiteQuotient m n k with hq
  have hq0 : q ≠ 0 := pairAnchorHermiteQuotient_ne_zero m n k hk
  have hqabs : 0 < |q| := abs_pos.2 hq0
  have habs := (tendsto_pairAnchor_quotient m n k).abs
  have hlow : ∀ᶠ a : ℝ in atTop,
      |q| / 2 < |(signedModeRadialData a k).R (pairAnchorPoint m n a)
        / (signedModeRadialData a k).R 0| :=
    habs.eventually (eventually_gt_nhds (by linarith))
  have hhigh : ∀ᶠ a : ℝ in atTop,
      |(signedModeRadialData a k).R (pairAnchorPoint m n a)
        / (signedModeRadialData a k).R 0| < 2 * |q| :=
    habs.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hlow, hhigh] with a h1 h2
  exact ⟨h1.le, h2.le⟩

/-- The constant of the centre comparison. -/
def centreRatioConst (m n : ℕ) : ℝ :=
  16 * ratioLimitConst m n * pairAnchorHermiteQuotient m n m ^ 2
    / pairAnchorHermiteQuotient m n n ^ 2

theorem centreRatioConst_nonneg (m n : ℕ) : 0 ≤ centreRatioConst m n := by
  have h := ratioLimitConst_nonneg m n
  rw [centreRatioConst]
  positivity

/-- **The centre amplitudes inherit the `c^{-1/2}` comparison.** -/
theorem eventually_centre_sq_ratio_le_div_sqrt (m n : ℕ) (hmn : m < n) :
    ∀ᶠ a : ℝ in atTop,
      (signedModeRadialData a n).R 0 ^ 2
        ≤ centreRatioConst m n / prolateRatioScale a
          * (signedModeRadialData a m).R 0 ^ 2 := by
  have hqn : pairAnchorHermiteQuotient m n n ≠ 0 :=
    pairAnchorHermiteQuotient_ne_zero m n n (Or.inr rfl)
  have hqm : pairAnchorHermiteQuotient m n m ≠ 0 :=
    pairAnchorHermiteQuotient_ne_zero m n m (Or.inl rfl)
  have hqnpos : 0 < pairAnchorHermiteQuotient m n n ^ 2 := by positivity
  filter_upwards [eventually_prolateBand_sq_ratio_le_div_sqrt m n hmn,
    eventually_pairAnchor_quotient_bounds m n n (Or.inr rfl),
    eventually_pairAnchor_quotient_bounds m n m (Or.inl rfl),
    (tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ))]
    with a hratio hbn hbm hc1
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hc0 : (0 : ℝ) < c := by linarith
  have hsq : 0 < prolateRatioScale a := prolateRatioScale_pos (by rw [← hcdef]; exact hc0)
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  -- the centre values are nonzero
  have hRn0 : (signedModeRadialData a n).R 0 ≠ 0 := by
    intro hzero
    have := hbn.1
    rw [hzero, div_zero, abs_zero] at this
    have : 0 < |pairAnchorHermiteQuotient m n n| := abs_pos.2 hqn
    linarith [hbn.1, this]
  have hRm0 : (signedModeRadialData a m).R 0 ≠ 0 := by
    intro hzero
    have := hbm.1
    rw [hzero, div_zero, abs_zero] at this
    have : 0 < |pairAnchorHermiteQuotient m n m| := abs_pos.2 hqm
    linarith [hbm.1, this]
  -- rewrite the anchor values through the quotients
  have hfn : (signedModeRadialData a n).R y₀
      = ((signedModeRadialData a n).R y₀ / (signedModeRadialData a n).R 0)
        * (signedModeRadialData a n).R 0 := by
    field_simp
  have hfm : (signedModeRadialData a m).R y₀
      = ((signedModeRadialData a m).R y₀ / (signedModeRadialData a m).R 0)
        * (signedModeRadialData a m).R 0 := by
    field_simp
  set ρn : ℝ := (signedModeRadialData a n).R y₀ / (signedModeRadialData a n).R 0 with hρn
  set ρm : ℝ := (signedModeRadialData a m).R y₀ / (signedModeRadialData a m).R 0 with hρm
  have hnsq : pairAnchorHermiteQuotient m n n ^ 2 / 4 * (signedModeRadialData a n).R 0 ^ 2
      ≤ (signedModeRadialData a n).R y₀ ^ 2 := by
    have h1 : |pairAnchorHermiteQuotient m n n| / 2 ≤ |ρn| := hbn.1
    have h2 : (|pairAnchorHermiteQuotient m n n| / 2) ^ 2 ≤ |ρn| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have habs1 : |ρn| ^ 2 = ρn ^ 2 := sq_abs ρn
    have habs2 : |pairAnchorHermiteQuotient m n n| ^ 2
        = pairAnchorHermiteQuotient m n n ^ 2 := sq_abs _
    rw [hfn]
    have hR2 : (0 : ℝ) ≤ (signedModeRadialData a n).R 0 ^ 2 := sq_nonneg _
    have hkey : pairAnchorHermiteQuotient m n n ^ 2 / 4 ≤ ρn ^ 2 := by
      rw [div_pow] at h2
      rw [habs1, habs2] at h2
      norm_num at h2
      linarith [h2]
    calc pairAnchorHermiteQuotient m n n ^ 2 / 4 * (signedModeRadialData a n).R 0 ^ 2
        ≤ ρn ^ 2 * (signedModeRadialData a n).R 0 ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hR2
      _ = (ρn * (signedModeRadialData a n).R 0) ^ 2 := by ring
  have hmsq : (signedModeRadialData a m).R y₀ ^ 2
      ≤ 4 * pairAnchorHermiteQuotient m n m ^ 2 * (signedModeRadialData a m).R 0 ^ 2 := by
    have h1 : |ρm| ≤ 2 * |pairAnchorHermiteQuotient m n m| := hbm.2
    have h2 : |ρm| ^ 2 ≤ (2 * |pairAnchorHermiteQuotient m n m|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    have habs1 : |ρm| ^ 2 = ρm ^ 2 := sq_abs ρm
    have habs2 : |pairAnchorHermiteQuotient m n m| ^ 2
        = pairAnchorHermiteQuotient m n m ^ 2 := sq_abs _
    have hkey : ρm ^ 2 ≤ 4 * pairAnchorHermiteQuotient m n m ^ 2 := by
      rw [mul_pow, habs1, habs2] at h2
      norm_num at h2
      linarith [h2]
    rw [hfm]
    have hR2 : (0 : ℝ) ≤ (signedModeRadialData a m).R 0 ^ 2 := sq_nonneg _
    calc (ρm * (signedModeRadialData a m).R 0) ^ 2
        = ρm ^ 2 * (signedModeRadialData a m).R 0 ^ 2 := by ring
      _ ≤ 4 * pairAnchorHermiteQuotient m n m ^ 2 * (signedModeRadialData a m).R 0 ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hR2
  -- assemble
  have hKnn : 0 ≤ ratioLimitConst m n := ratioLimitConst_nonneg m n
  have hchain : pairAnchorHermiteQuotient m n n ^ 2 / 4 * (signedModeRadialData a n).R 0 ^ 2
      ≤ ratioLimitConst m n / prolateRatioScale a
        * (4 * pairAnchorHermiteQuotient m n m ^ 2 * (signedModeRadialData a m).R 0 ^ 2) := by
    refine le_trans hnsq (le_trans hratio ?_)
    refine mul_le_mul_of_nonneg_left hmsq ?_
    positivity
  have h4 : (0 : ℝ) < pairAnchorHermiteQuotient m n n ^ 2 / 4 := by positivity
  have hX : (signedModeRadialData a n).R 0 ^ 2
      ≤ (ratioLimitConst m n / prolateRatioScale a
          * (4 * pairAnchorHermiteQuotient m n m ^ 2 * (signedModeRadialData a m).R 0 ^ 2))
        / (pairAnchorHermiteQuotient m n n ^ 2 / 4) := by
    rw [le_div_iff₀ h4]
    linarith [hchain]
  refine le_trans hX (le_of_eq ?_)
  rw [centreRatioConst]
  field_simp
  ring

end RHTower

end
