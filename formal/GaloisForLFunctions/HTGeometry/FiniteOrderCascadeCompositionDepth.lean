import GaloisForLFunctions.HTGeometry.CompositionDepth
import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard

/-!
# Composition depth of finite-order cascades

A finite-order entire outer map raises iterated-exponential growth height by at most one.  Iterating
this bound shows that a cascade of `n` finite-order entire maps has growth height at most `n`.
Combined with the Pólya lower bound already encoded by `growthHeightAtLeast_entireCascade`, this
gives exact positive-lower-order composition depth for an arbitrary finite-order cascade.

This is the growth half shared by the Newton-corner and algebraic exponential-cover cards.  It does
not use their still-separate observability argument.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The identity has growth height at most zero. -/
theorem growthHeightAtMost_id : GrowthHeightAtMost (id : ℂ → ℂ) 0 := by
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr z hz
  rw [iterExp_zero, Real.rpow_one]
  exact hz

/-- A finite cascade depends only on constituents below its length. -/
theorem entireCascade_congr_of_eq_below {f g : ℕ → ℂ → ℂ} {n : ℕ}
    (h : ∀ i, i < n → f i = g i) : entireCascade f n = entireCascade g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [entireCascade, entireCascade, h n (by omega), ih]
      intro i hi
      exact h i (by omega)

/-- **A finite-order outer map raises growth height by at most one.** -/
theorem growthHeightAtMost_comp_of_finiteOrderEnvelope
    {f g : ℂ → ℂ} (hf : FiniteOrderEnvelope f) {k : ℕ}
    (hg : GrowthHeightAtMost g k) :
    GrowthHeightAtMost (fun z => f (g z)) (k + 1) := by
  obtain ⟨C, d, hC, hfbound⟩ := hf
  obtain ⟨A, hgbound⟩ := hg
  set A' : ℝ := max A 1 with hA'def
  have hA' : 0 < A' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hgbound' : ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r →
      ‖g z‖ ≤ iterExp k (r ^ A') := by
    filter_upwards [hgbound, eventually_ge_atTop (1 : ℝ)] with r hr hr1 z hz
    refine le_trans (hr z hz) (iterExp_monotone k ?_)
    exact Real.rpow_le_rpow_of_exponent_le hr1 (le_max_left _ _)
  cases k with
  | zero =>
      set B : ℝ := A' * (d : ℝ) + 1 with hBdef
      refine ⟨B, ?_⟩
      filter_upwards [hgbound', eventually_ge_atTop (max 1 (C * 2 ^ d))]
        with r hgr hr z hz
      have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
      have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
      have hCr : C * 2 ^ d ≤ r := le_trans (le_max_right _ _) hr
      have hinner : ‖g z‖ ≤ r ^ A' := by simpa [iterExp_zero] using hgr z hz
      have hrpow1 : (1 : ℝ) ≤ r ^ A' := Real.one_le_rpow hr1 hA'.le
      have hone : 1 + ‖g z‖ ≤ 2 * (r ^ A') := by linarith
      have hpow : (1 + ‖g z‖) ^ d ≤ (2 * (r ^ A')) ^ d :=
        pow_le_pow_left₀ (by positivity) hone d
      have hpoly : C * (1 + ‖g z‖) ^ d ≤ r ^ B := by
        have hCpow := mul_le_mul_of_nonneg_left hpow hC
        have hsplit : (2 * (r ^ A')) ^ d = 2 ^ d * r ^ (A' * (d : ℝ)) := by
          rw [mul_pow, ← Real.rpow_mul_natCast hr0.le A' d]
        have hbase : C * (1 + ‖g z‖) ^ d
            ≤ (C * 2 ^ d) * r ^ (A' * (d : ℝ)) := by
          rw [hsplit] at hCpow
          nlinarith
        have hmul := mul_le_mul_of_nonneg_right hCr
          (Real.rpow_nonneg (le_of_lt hr0) (A' * (d : ℝ)))
        have htarget : r * r ^ (A' * (d : ℝ)) = r ^ B := by
          rw [hBdef, Real.rpow_add hr0, Real.rpow_one]
          ring
        rw [htarget] at hmul
        exact le_trans hbase hmul
      rw [iterExp_succ, iterExp_zero]
      exact le_trans (hfbound (g z)) (Real.exp_le_exp.mpr hpoly)
  | succ m =>
      set K : ℝ := C * 2 ^ d with hKdef
      set T : ℝ := max (d : ℝ) K + 1 with hTdef
      have hT0 : 0 < T := by
        have hd0 : (0 : ℝ) ≤ d := by positivity
        have : (0 : ℝ) ≤ max (d : ℝ) K := le_trans hd0 (le_max_left _ _)
        rw [hTdef]
        linarith
      refine ⟨A' + 1, ?_⟩
      have habsorb := eventually_iterExp_mul_add_le m hA' T
      have hYnonneg : ∀ᶠ r : ℝ in atTop, (0 : ℝ) ≤ iterExp m (r ^ A') :=
        (tendsto_iterExp_rpow m hA').eventually_ge_atTop 0
      filter_upwards [hgbound', habsorb, hYnonneg] with r hgr habsorb hY0 z hz
      set Y : ℝ := iterExp m (r ^ A') with hYdef
      set X : ℝ := iterExp (m + 1) (r ^ A') with hXdef
      have hX : X = Real.exp Y := by rw [hXdef, iterExp_succ, hYdef]
      have hX1 : (1 : ℝ) ≤ X := by rw [hX]; exact Real.one_le_exp hY0
      have hinner : ‖g z‖ ≤ X := hgr z hz
      have hone : 1 + ‖g z‖ ≤ 2 * X := by linarith
      have hpow : (1 + ‖g z‖) ^ d ≤ (2 * X) ^ d :=
        pow_le_pow_left₀ (by positivity) hone d
      have hK0 : 0 ≤ K := by rw [hKdef]; positivity
      have hKT : K ≤ T := by
        rw [hTdef]
        exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
      have hdT : (d : ℝ) ≤ T := by
        rw [hTdef]
        exact le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
      have hpoly : C * (1 + ‖g z‖) ^ d ≤ Real.exp (T * Y + T) := by
        have hCpow := mul_le_mul_of_nonneg_left hpow hC
        have hrewrite : C * (2 * X) ^ d = K * Real.exp ((d : ℝ) * Y) := by
          rw [mul_pow, hX, ← Real.exp_nat_mul]
          rw [hKdef]
          ring
        rw [hrewrite] at hCpow
        have hKexp : K ≤ Real.exp K := le_trans (by linarith) (Real.add_one_le_exp K)
        have hmul : K * Real.exp ((d : ℝ) * Y)
            ≤ Real.exp K * Real.exp ((d : ℝ) * Y) :=
          mul_le_mul_of_nonneg_right hKexp (Real.exp_nonneg _)
        have hexp : Real.exp K * Real.exp ((d : ℝ) * Y)
            = Real.exp (K + (d : ℝ) * Y) := (Real.exp_add _ _).symm
        have harg : K + (d : ℝ) * Y ≤ T * Y + T := by nlinarith
        exact le_trans hCpow (le_trans hmul (hexp.trans_le (Real.exp_le_exp.mpr harg)))
      have habsorb' : T * Y + T ≤ iterExp m (r ^ (A' + 1)) := by
        simpa [hYdef] using habsorb
      rw [iterExp_succ, iterExp_succ]
      exact le_trans (hfbound (g z))
        (Real.exp_le_exp.mpr (le_trans hpoly (Real.exp_le_exp.mpr habsorb')))

/-- **A cascade of `n` finite-order entire maps has growth height at most `n`.** -/
theorem growthHeightAtMost_entireCascade_of_finiteOrderEnvelope
    {f : ℕ → ℂ → ℂ} (n : ℕ)
    (hfin : ∀ i, i < n → FiniteOrderEnvelope (f i)) :
    GrowthHeightAtMost (entireCascade f n) n := by
  induction n with
  | zero => simpa [entireCascade] using growthHeightAtMost_id
  | succ n ih =>
      simpa [entireCascade] using
        growthHeightAtMost_comp_of_finiteOrderEnvelope (hfin n (by omega))
          (ih (fun i hi => hfin i (by omega)))

/-- **Exact positive-lower-order composition depth for finite-order cascades.**

Every displayed factor contributes one by hypothesis, while the generic finite-order upper-height
bound rules out one more positive-lower-order factor in any alternative decomposition. -/
theorem compositionDepth_finiteOrder_positiveCascade
    {f : ℕ → ℂ → ℂ}
    (n : ℕ)
    (hdiff : ∀ i, i < n → Differentiable ℂ (f i))
    (hnc : ∀ i, i < n → ∃ z₁ z₂ : ℂ, f i z₁ ≠ f i z₂)
    (hfin : ∀ i, i < n → FiniteOrderEnvelope (f i))
    (hpos : ∀ i, i < n → PositiveLowerOrder (f i)) :
    CompositionDepthAtLeast (entireCascade f n) n ∧
      ¬ CompositionDepthAtLeast (entireCascade f n) (n + 1) := by
  let g : ℕ → ℂ → ℂ := fun i => if i < n then f i else Complex.exp
  have hgf : ∀ i, i < n → g i = f i := by
    intro i hi
    simp [g, hi]
  have hcas : entireCascade g n = entireCascade f n :=
    entireCascade_congr_of_eq_below hgf
  have hexpnc : ∃ z₁ z₂ : ℂ, Complex.exp z₁ ≠ Complex.exp z₂ := by
    simpa [affExp] using
      (nonconstant_affExp (a := fun _ => 0) (b := fun _ => 1) (c := fun _ => 1)
        (j := 0) (by simp) (by simp))
  have hgdiff : ∀ i, Differentiable ℂ (g i) := by
    intro i
    by_cases hi : i < n
    · simpa [g, hi] using hdiff i hi
    · simp [g, hi]
  have hgnc : ∀ i, ∃ z₁ z₂ : ℂ, g i z₁ ≠ g i z₂ := by
    intro i
    by_cases hi : i < n
    · simpa [g, hi] using hnc i hi
    · simpa [g, hi] using hexpnc
  constructor
  · exact ⟨n, g, Finset.range n, hgdiff, hgnc, Finset.Subset.rfl,
      fun i hi => by rw [Finset.mem_range] at hi; simpa [g, hi] using hpos i hi,
      by simp, fun z => congrFun hcas.symm z⟩
  · intro hdeep
    exact not_growthHeightAtLeast_succ_of_atMost
      (growthHeightAtMost_entireCascade_of_finiteOrderEnvelope n hfin)
      (growthHeightAtLeast_of_compositionDepth hdeep)

end GaloisForLFunctions.HTGeometry
