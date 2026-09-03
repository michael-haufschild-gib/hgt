import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicInitialRangeSchedule

/-!
# Subpower measure of Menon's initial exceptional frequencies
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory

noncomputable section

/-- The initial all-blocks-large complement has subpower measure, uniformly in every natural
upper endpoint and every ambient frequency radius below the source scale. -/
theorem eventually_measureReal_menonInitialRange_annulusLarge_le_rpow
    {a c A s : ℝ} (ha : 0 < a) (ha1 : a < 1) (hc : 0 < c) (hA : 0 < A) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, ∀ (hN : ℕ) (W w₀ : ℝ),
      ((highBase a x : ℕ) : ℝ) < (hN : ℝ) → (hN : ℝ) ≤ x →
      0 ≤ W → W ≤ x →
      volume.real (annulusLarge
          (allBlocksSmall (menonInitialRangePrimes a c x hN)
            ((highBase a x : ℕ) : ℝ) (lowEta c x)
            (menonInitialRangeSteps a c x hN)
            (fun j => ((geomBlock (menonInitialRangePrimes a c x hN)
                ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ) *
              lowTheta A x) W) W w₀)
        ≤ x ^ s := by
  let D : ℝ := c + 2 * A + 3
  have hD : 0 ≤ D := by dsimp only [D]; linarith
  have h3D : 0 ≤ 3 * D := mul_nonneg (by norm_num) hD
  have hlimit := tendsto_expSubLinear_div_rpow
    (a₀ := a) (D := 3 * D) (e := c + 3) (s := s) ha ha1 h3D hs
  have hlimit32 :
      Tendsto
        (fun x : ℝ =>
          32 * ((Real.log x) ^ (c + 3) *
            Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x)) /
              x ^ s)) atTop (𝓝 0) := by
    simpa using hlimit.const_mul (32 : ℝ)
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hlimit32
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
    measureReal_menonInitialRange_annulusLarge_le ha ha1 hc hA,
    hsmall] with x hxexp hmeasure hsmallx
  intro hN W w₀ hQh hhx hW hWx
  have hx1 : 1 < x := lt_of_lt_of_le (by have := Real.exp_one_gt_d9; linarith) hxexp
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogx1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxexp
    rwa [Real.log_exp] at h
  have hloglog : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlogx1
  have hQnat : highBase a x ≤ hN := by exact_mod_cast hQh.le
  have hh0 : (0 : ℝ) < (hN : ℝ) := by
    have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
      have hbase := (highBase_bounds (a := a) hx1).1
      exact lt_of_lt_of_le (cardLength_pos a x) hbase
    linarith
  have hlogh : Real.log (hN : ℝ) ≤ Real.log x := Real.log_le_log hh0 hhx
  have hLraw := menonInitialRangeSteps_le hxexp hc hQnat
  have hLc : ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) ≤
      2 * (Real.log x) ^ (c + 1) := by
    calc
      ((menonInitialRangeSteps a c x hN : ℕ) : ℝ)
          ≤ 2 * Real.log (hN : ℝ) * (Real.log x) ^ c := hLraw
      _ ≤ 2 * Real.log x * (Real.log x) ^ c := by
        gcongr
      _ = 2 * (Real.log x) ^ (c + 1) := by
        rw [show c + 1 = 1 + c by ring, Real.rpow_add hlogx, Real.rpow_one]
        ring
  have hp1a : 1 ≤ (Real.log x) ^ (1 - a) := by
    exact Real.one_le_rpow hlogx1 (by linarith)
  have hk := momentOrder_le (a := a) hx1 hp1a
  have hlog2 : Real.log 2 ≤ Real.log x := by
    have h2x : (2 : ℝ) ≤ x := by
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      exact he2.trans hxexp
    exact Real.log_le_log (by norm_num) h2x
  have hnmax : Real.log 2 + Real.log x ≤ 2 * Real.log x := by linarith
  have hrpowStep : (Real.log x) ^ (1 - a) * Real.log x =
      (Real.log x) ^ (2 - a) := by
    calc
      (Real.log x) ^ (1 - a) * Real.log x =
          (Real.log x) ^ (1 - a) * (Real.log x) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (Real.log x) ^ ((1 - a) + 1) :=
        (Real.rpow_add hlogx (1 - a) 1).symm
      _ = (Real.log x) ^ (2 - a) := by congr 1; ring
  have hkn : ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + Real.log x) ≤
      6 * (Real.log x) ^ (2 - a) := by
    calc
      ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + Real.log x)
          ≤ (3 * (Real.log x) ^ (1 - a)) * (2 * Real.log x) :=
        mul_le_mul hk hnmax (by positivity) (by positivity)
      _ = 6 * (Real.log x) ^ (2 - a) := by rw [← hrpowStep]; ring
  have hrpowTwo : (Real.log x) ^ (2 - a) ≤ (Real.log x) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
  have hzone : (1 : ℝ) ≤ (Real.log x) ^ (2 : ℝ) :=
    Real.one_le_rpow hlogx1 (by norm_num)
  have hpoly : 1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + Real.log x) ≤
      7 * (Real.log x) ^ (2 : ℝ) := by
    linarith
  have hexponent : ((momentOrder a x : ℕ) : ℝ) *
      (D * Real.log (Real.log x)) ≤
        (3 * D) * (Real.log x) ^ (1 - a) * Real.log (Real.log x) := by
    have hmul := mul_le_mul_of_nonneg_right hk
      (mul_nonneg hD hloglog)
    calc
      ((momentOrder a x : ℕ) : ℝ) * (D * Real.log (Real.log x))
          ≤ (3 * (Real.log x) ^ (1 - a)) *
              (D * Real.log (Real.log x)) := hmul
      _ = (3 * D) * (Real.log x) ^ (1 - a) * Real.log (Real.log x) := by ring
  have hexp := Real.exp_le_exp.mpr hexponent
  have hexpOne : 1 ≤ Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
      Real.log (Real.log x)) := by
    apply Real.one_le_exp
    positivity
  have hinside :
      2 * W / x +
          2 * (1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + Real.log x)) *
            Real.exp (((momentOrder a x : ℕ) : ℝ) *
              (D * Real.log (Real.log x)))
        ≤ 16 * (Real.log x) ^ (2 : ℝ) *
            Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
              Real.log (Real.log x)) := by
    have hWxdiv : 2 * W / x ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hmain :
        2 * (1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + Real.log x)) *
            Real.exp (((momentOrder a x : ℕ) : ℝ) *
              (D * Real.log (Real.log x)))
          ≤ 14 * (Real.log x) ^ (2 : ℝ) *
            Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
              Real.log (Real.log x)) := by
      nlinarith [mul_le_mul hpoly hexp (by positivity) (by positivity)]
    have htwo : 2 ≤ 2 * (Real.log x) ^ (2 : ℝ) *
        Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
          Real.log (Real.log x)) := by
      have hprod : 1 * 1 ≤ (Real.log x) ^ (2 : ℝ) *
          Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
            Real.log (Real.log x)) :=
        mul_le_mul hzone hexpOne (by norm_num) (by positivity)
      nlinarith
    linarith
  have hbound :
      ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) *
          (2 * W / x +
            2 * (1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + Real.log x)) *
              Real.exp (((momentOrder a x : ℕ) : ℝ) *
                (D * Real.log (Real.log x))))
        ≤ 32 * (Real.log x) ^ (c + 3) *
            Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
              Real.log (Real.log x)) := by
    calc
      _ ≤ (2 * (Real.log x) ^ (c + 1)) *
          (16 * (Real.log x) ^ (2 : ℝ) *
            Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
              Real.log (Real.log x))) :=
        mul_le_mul hLc hinside (by positivity) (by positivity)
      _ = 32 * (Real.log x) ^ (c + 3) *
            Real.exp ((3 * D) * (Real.log x) ^ (1 - a) *
              Real.log (Real.log x)) := by
        have hpowAdd : (Real.log x) ^ (c + 1) * (Real.log x) ^ (2 : ℝ) =
            (Real.log x) ^ (c + 3) := by
          calc
            (Real.log x) ^ (c + 1) * (Real.log x) ^ (2 : ℝ) =
                (Real.log x) ^ ((c + 1) + 2) :=
              (Real.rpow_add hlogx (c + 1) 2).symm
            _ = (Real.log x) ^ (c + 3) := by congr 1; ring
        rw [← hpowAdd]
        ring
  have hxpow : 0 < x ^ s := Real.rpow_pos_of_pos (by linarith) s
  have hsmall' : 32 * (Real.log x) ^ (c + 3) *
        Real.exp ((3 * D) * (Real.log x) ^ (1 - a) * Real.log (Real.log x)) ≤
      x ^ s := by
    rw [← div_le_one₀ hxpow]
    calc
      32 * (Real.log x) ^ (c + 3) *
            Real.exp ((3 * D) * (Real.log x) ^ (1 - a) * Real.log (Real.log x)) /
          x ^ s =
          32 * ((Real.log x) ^ (c + 3) *
            Real.exp ((3 * D) * (Real.log x) ^ (1 - a) * Real.log (Real.log x)) /
              x ^ s) := by ring
      _ ≤ 1 := hsmallx
  exact (hmeasure hN W w₀ hQh hhx hW).trans (hbound.trans hsmall')

end

end RHTower.Sieve
