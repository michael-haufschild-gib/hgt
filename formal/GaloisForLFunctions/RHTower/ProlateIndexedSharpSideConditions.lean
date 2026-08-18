import GaloisForLFunctions.RHTower.ProlateSharpTransport
import GaloisForLFunctions.RHTower.ProlateIndexedAmplitudeRatio

/-!
# The two scalar side conditions of the sharp ratio, at the canonical family

`prolateBand_sq_ratio_sharp` needs, for each of the two rungs, the doubled turning condition
`2 s_k ≤ a²` and the defect condition `1/a + 9/(1-α) ≤ c P_k(a)` at the matching point.  At the pair
anchor `a = x₀/sqrt c` both are eventual consequences of `c s_k → 4k+1` and `x₀² > 4(4k+1)`:

```text
2 s_k ≤ x₀²/c        ⟺  2 c s_k ≤ x₀² ,           and  2(4k+1) < x₀²/2 ;
c P_k(a) ≥ sqrt c · sqrt(x₀² - c s_k) ≥ sqrt c · x₀/sqrt 2 ,   so the defect condition holds as soon
as  sqrt c (x₀/sqrt 2 - 1/x₀) ≥ 9/(1-α) ,  and  x₀ ≥ 2  makes the bracket at least `9/10`.
```
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

theorem prolatePairAnchor_ge_two (m n : ℕ) : 2 ≤ prolatePairAnchor m n := by
  have h := (prolatePairAnchor_spec m n).1.1
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hone : (1 : ℝ) ≤ Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1) := by
    have : Real.sqrt 1 ≤ Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    simpa using this
  linarith

/-- The doubled turning condition holds eventually at either rung. -/
theorem eventually_two_mul_s_le_pairAnchorPoint_sq (m n : ℕ) (k : ℕ) (hk : k = m ∨ k = n) :
    ∀ᶠ a : ℝ in atTop,
      2 * (signedModeRadialData a k).s ≤ pairAnchorPoint m n a ^ 2 := by
  have hxk : 4 * (4 * (k : ℝ) + 1) < prolatePairAnchor m n ^ 2 :=
    prolatePairAnchor_sq_gt m n k hk
  have hsk := tendsto_signedModeRadialBandwidth_mul_s_atTop k
  have hhalf : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a k).s
        < prolatePairAnchor m n ^ 2 / 2 := by
    refine hsk.eventually (eventually_lt_nhds ?_)
    linarith
  filter_upwards [hhalf, tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ)]
    with a hha hc1
  have hc0 : (0 : ℝ) < signedModeRadialBandwidth a := by linarith
  rw [pairAnchorPoint_sq hc0, le_div_iff₀ hc0]
  linarith [hha]

/-- The defect condition holds eventually at either rung. -/
theorem eventually_pairAnchor_defect_condition (m n : ℕ) (k : ℕ) (hk : k = m ∨ k = n) :
    ∀ᶠ a : ℝ in atTop,
      1 / pairAnchorPoint m n a + 9 / (1 - prolateLeakageCollar)
        ≤ signedModeRadialBandwidth a
          * prolateWKBProfile (signedModeRadialData a k).s (pairAnchorPoint m n a) := by
  set x₀ : ℝ := prolatePairAnchor m n with hx₀def
  have hx2 : 2 ≤ x₀ := prolatePairAnchor_ge_two m n
  have hx0 : 0 < x₀ := by linarith
  have hα0 : (0 : ℝ) < 1 - prolateLeakageCollar := by
    rw [prolateLeakageCollar]; norm_num
  have hsk := tendsto_signedModeRadialBandwidth_mul_s_atTop k
  have hxk : 4 * (4 * (k : ℝ) + 1) < x₀ ^ 2 := prolatePairAnchor_sq_gt m n k hk
  have hhalf : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a k).s < x₀ ^ 2 / 2 := by
    refine hsk.eventually (eventually_lt_nhds ?_)
    linarith
  have hcbig : ∀ᶠ a : ℝ in atTop,
      (11 / (1 - prolateLeakageCollar)) ^ 2 ≤ signedModeRadialBandwidth a :=
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop _
  filter_upwards [hhalf, hcbig,
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ),
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (x₀ ^ 2 + 1),
    eventually_signedModeRadialData_s_nonneg k] with a hha hcb hc1 hcbig2 hs0
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hc0 : (0 : ℝ) < c := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hsc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hy₀0 : 0 < y₀ := pairAnchorPoint_pos hc0
  have hy₀sq : y₀ ^ 2 = x₀ ^ 2 / c := pairAnchorPoint_sq hc0
  have hy₀val : y₀ = x₀ / Real.sqrt c := rfl
  have hs : (signedModeRadialData a k).s < y₀ ^ 2 := by
    rw [hy₀sq, lt_div_iff₀ hc0]
    nlinarith [hha, hx0]
  have hy₀1 : y₀ ^ 2 < 1 := by
    rw [hy₀sq, div_lt_one hc0]
    linarith [hcbig2]
  -- the profile is at least the square root of the gap
  have hPge : Real.sqrt (y₀ ^ 2 - (signedModeRadialData a k).s)
      ≤ prolateWKBProfile (signedModeRadialData a k).s y₀ := by
    rw [prolateWKBProfile]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hy₀1, hs]
  have hsle : (signedModeRadialData a k).s ≤ x₀ ^ 2 / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hha]
  have hhalfid : x₀ ^ 2 / c - x₀ ^ 2 / (2 * c) = x₀ ^ 2 / (2 * c) := by
    field_simp
    ring
  have hgap : x₀ ^ 2 / (2 * c) ≤ y₀ ^ 2 - (signedModeRadialData a k).s := by
    rw [hy₀sq]
    linarith [hsle, hhalfid.le, hhalfid.ge]
  have hsqrtgap : x₀ / (Real.sqrt 2 * Real.sqrt c)
      ≤ Real.sqrt (y₀ ^ 2 - (signedModeRadialData a k).s) := by
    have hle : Real.sqrt (x₀ ^ 2 / (2 * c))
        ≤ Real.sqrt (y₀ ^ 2 - (signedModeRadialData a k).s) := Real.sqrt_le_sqrt hgap
    have hval : Real.sqrt (x₀ ^ 2 / (2 * c)) = x₀ / (Real.sqrt 2 * Real.sqrt c) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq hx0.le, Real.sqrt_mul (by norm_num)]
    rwa [hval] at hle
  -- assemble
  have hkey : 1 / y₀ + 9 / (1 - prolateLeakageCollar) ≤ c * (x₀ / (Real.sqrt 2 * Real.sqrt c)) := by
    have hinv : 1 / y₀ = Real.sqrt c / x₀ := by
      rw [hy₀val, one_div_div]
    rw [hinv]
    have hcprod : c * (x₀ / (Real.sqrt 2 * Real.sqrt c)) = Real.sqrt c * x₀ / Real.sqrt 2 := by
      have hs2p : (0 : ℝ) < Real.sqrt 2 := by positivity
      field_simp
      nlinarith [hsc2, hsc, hx0]
    rw [hcprod]
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hs2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hcge : 11 / (1 - prolateLeakageCollar) ≤ Real.sqrt c := by
      have h := Real.sqrt_le_sqrt hcb
      rwa [Real.sqrt_sq (by positivity)] at h
    have hfrac : 9 / (1 - prolateLeakageCollar) ≤ Real.sqrt c * (5 / 6) := by
      have h := mul_le_mul_of_nonneg_left hcge (by norm_num : (0 : ℝ) ≤ 5 / 6)
      have hid : (5 / 6 : ℝ) * (11 / (1 - prolateLeakageCollar))
          = (55 / 6) / (1 - prolateLeakageCollar) := by
        field_simp
        ring
      have hge : 9 / (1 - prolateLeakageCollar) ≤ (55 / 6) / (1 - prolateLeakageCollar) := by
        rw [div_le_div_iff₀ hα0 hα0]
        nlinarith [hα0]
      linarith [h, hid.le, hid.ge, hge]
    have hxsplit : Real.sqrt c * x₀ / Real.sqrt 2 - Real.sqrt c / x₀
        ≥ Real.sqrt c * (5 / 6) := by
      have hxx : x₀ / Real.sqrt 2 - 1 / x₀ ≥ 5 / 6 := by
        have h1 : x₀ / Real.sqrt 2 ≥ 2 / (3 / 2) := by
          rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hs2pos]
          nlinarith [hx2, hs2, hs2pos]
        have h2 : 1 / x₀ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hx0 (by norm_num)]
          linarith
        linarith [h1, h2]
      have hcnn : (0 : ℝ) ≤ Real.sqrt c := hsc.le
      have hid : Real.sqrt c * x₀ / Real.sqrt 2 - Real.sqrt c / x₀
          = Real.sqrt c * (x₀ / Real.sqrt 2 - 1 / x₀) := by
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_left hxx hcnn
    linarith [hfrac, hxsplit]
  refine le_trans hkey ?_
  have hcnn : (0 : ℝ) ≤ c := hc0.le
  exact mul_le_mul_of_nonneg_left (le_trans hsqrtgap hPge) hcnn

end RHTower

end
