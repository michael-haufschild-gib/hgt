import GaloisForLFunctions.RHTower.EvenSectorAbelAveraging
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion

/-!
# Abel pinning of the even Weil cone

**Theorem** (`weilPositiveEvenAt_one_of_abel`).  Let `lam` be Weil-positive on even tests at some
pole weight `β`.  Suppose `Σ |lam(n)| n^{−σ} < ∞` for every `σ > 1`, and that
`F(s) = Σ_{n ≥ 2} lam(n) n^{−1−s}` has no negative double pole at `s = 0`:
`liminf_{s → 0⁺} s² F(s) ≥ 0`.  Then `lam` is Weil-positive on even tests at pole weight `1`, so RH
holds and `lam = Λ` on `n ≥ 2` (`riemannHypothesis_of_weilPositiveEvenAt_of_abel`).

Proof.  Put `X(s) = s F(s)`.  The even log-density ceiling and Abel summation give
`X(s) ≤ 1 + ε` for small `s` (`eventually_le_one_add_of_weilPositiveEvenAt`); with the hypothesis
this gives `s X(s) → 0`.  For a real even test `g` with `P = ∫ g e^{−x/2}` the averaged far-bump
inequality and the factorization of the Laplace transforms give
`W(g) ≥ P² (2 − 4X(s) + 2X(s/2)) − ε` for small `s` (`eventually_realWeil_ge`).  If `W(g) < 0`
then `2X(s) − X(s/2) ≥ 1 + η` near `0`, so along `s_k = s₂/2^k` the defect
`1 + η − X(s_k)` doubles at each step, and `s_k X(s_k)` stays below a negative constant
(`nonneg_of_two_scale`), contradicting the hypothesis.  Hence `W(g) ≥ 0` on real even tests, which
suffices for even Weil positivity at pole weight one (`weilPositiveEvenAt_one_of_real`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight

/-! ## Bounds for the averaged quantities -/

theorem abs_farCrossLaplace_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ}
    (hgs : ∀ x, R < |x| → g x = 0) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 3 / 2) :
    |farCrossLaplace g s| ≤ Real.exp (2 * (R + 1)) * ∫ u, |farCrossKernel g u| := by
  have hgc := hasCompactSupport_of_abs_gt_eq_zero hgs
  have hh := continuous_farCrossKernel hg hgc
  have hhc := hasCompactSupport_farCrossKernel hgs
  have hia : Integrable fun u => |farCrossKernel g u| :=
    hh.abs.integrable_of_hasCompactSupport hhc.abs
  have hi : Integrable fun u => farCrossKernel g u * Real.exp ((1 / 2 + s) * u) :=
    (hh.mul (by fun_prop)).integrable_of_hasCompactSupport hhc.mul_right
  unfold farCrossLaplace
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono hi.abs (hia.const_mul _)
    fun u => ?_)
  show |farCrossKernel g u * Real.exp ((1 / 2 + s) * u)| ≤
    Real.exp (2 * (R + 1)) * |farCrossKernel g u|
  rcases le_or_gt |u| (R + 1) with hu | hu
  · rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    have h1 := le_abs_self u
    have h2 := abs_nonneg u
    nlinarith
  · rw [farCrossKernel_eq_zero hgs hu]; simp

theorem abs_oddDirichlet_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℝ} (hs : 1 ≤ s) :
    |oddDirichlet lam s| ≤ ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) := by
  have hsum := hsl 2 (by norm_num)
  have hle : ∀ n : ℕ, |(if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s)| ≤
      |lam n| / (n : ℝ) ^ (2 : ℝ) := by
    intro n
    split_ifs with hn
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
    · rw [zero_div, abs_zero]; positivity
  have hs' : Summable fun n : ℕ => |(if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s)| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hle hsum
  unfold oddDirichlet
  calc |∑' n : ℕ, (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s)|
      ≤ ∑' n : ℕ, |(if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s)| := by
        have := norm_tsum_le_tsum_norm (f := fun n : ℕ =>
          (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s))
          (by simpa only [Real.norm_eq_abs] using hs')
        simpa only [Real.norm_eq_abs] using this
    _ ≤ _ := hs'.tsum_le_tsum hle hsum

/-- **Bounds on the averaged quantities.**  With `X(s) = s F(s)`, for `0 < s ≤ 1/2` the Laplace
integrals over `a ≥ a₀` reproduce `PJ X(s)`, `0` and `J² X(s/2)` up to `O(s |X| + s)`, and the
exponential masses are `O(s)`. -/
theorem abel_bounds {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgs : ∀ x, R < |x| → g x = 0)
    (hge : ∀ x, g (-x) = g x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 / 2 →
      |s * (∫ a in Ici (R + 1), farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a)) -
          (∫ x, g x * Real.exp (-x / 2)) * farJ * (s * oddDirichlet lam s)| ≤
        C * (s * |s * oddDirichlet lam s|) + C * s ∧
      |s * ∫ a in Ici (R + 1), farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a)| ≤
        C * s ∧
      |s * (∫ a in Ici (R + 1), farSum lam a * Real.exp (-(1 + s) * a)) -
          farJ ^ 2 * (s / 2 * oddDirichlet lam (s / 2))| ≤
        C * (s * |s / 2 * oddDirichlet lam (s / 2)|) + C * s ∧
      |(∫ a in Ici (R + 1), farAbelWeight s a) - 1| ≤ C * s ∧
      (∫ a in Ici (R + 1), Real.exp (-(1 / 2 + s) * a)) +
          (∫ a in Ici (R + 1), Real.exp (-(1 / 2 + (1 + s)) * a)) ≤ 4 ∧
      ∫ a in Ici (R + 1), Real.exp (-(1 + s) * a) ≤ 2 := by
  have hgc := hasCompactSupport_of_abs_gt_eq_zero hgs
  have hh := continuous_farCrossKernel hg hgc
  have hhc := hasCompactSupport_farCrossKernel hgs
  set a₀ := R + 1 with ha₀
  have ha₀0 : 0 ≤ a₀ := by linarith
  -- remainder constants
  have hT0 := (integral_kernelSum_mul_exp hsl hh hhc (show (0 : ℝ) < 1 / 2 by norm_num)).1
  rw [← farCrossSum_eq_kernelSum] at hT0
  have hTD : ∀ a, a < -(R + 1) → farCrossSum lam g a = 0 := fun a ha =>
    kernelSum_eq_zero_of_le lam (by linarith) (fun u hu => farCrossKernel_eq_zero hgs hu) ha.le
  have hS0 : Integrable fun a => farSum lam a * Real.exp (-(1 + 2 * (1 / 4)) * a) :=
    (integral_farSum_mul_exp hsl (show (0 : ℝ) < 1 / 4 by norm_num)).1
  have hSD : ∀ a, a < -0 → farSum lam a = 0 := fun a ha =>
    farSum_eq_zero_of_nonpos lam (by linarith)
  set BT := Real.exp (2 * (R + 1) + 2 * |a₀|) *
    ∫ a, |farCrossSum lam g a * Real.exp (-(1 / 2 + 1 / 2) * a)| with hBT
  set BS := Real.exp (2 * 0 + 2 * |a₀|) *
    ∫ a, |farSum lam a * Real.exp (-(1 + 2 * (1 / 4)) * a)| with hBS
  set CQ := (R + 1) * Real.exp (R + 1) * ∫ u, |farCrossKernel g u| * Real.exp (u / 2) with hCQ
  set CH := Real.exp (2 * (R + 1)) * ∫ u, |farCrossKernel g u| with hCH
  set CF := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) with hCF
  have hBT0 : 0 ≤ BT := by positivity
  have hBS0 : 0 ≤ BS := by positivity
  have hCQ0 : 0 ≤ CQ := by
    have : 0 ≤ ∫ u, |farCrossKernel g u| * Real.exp (u / 2) :=
      integral_nonneg fun u => by positivity
    positivity
  have hCH0 : 0 ≤ CH := by
    have : 0 ≤ ∫ u, |farCrossKernel g u| := integral_nonneg fun u => abs_nonneg _
    positivity
  have hCF0 : 0 ≤ CF := tsum_nonneg fun n => by positivity
  have hJ2 : 0 ≤ farJ ^ 2 := sq_nonneg _
  refine ⟨CQ + BT + CH * CF + BS + farJ ^ 2 + a₀ + 3, by positivity, fun s hs hs2 => ?_⟩
  set C := CQ + BT + CH * CF + BS + farJ ^ 2 + a₀ + 3 with hC
  have hCHCF0 := mul_nonneg hCH0 hCF0
  have hCQle : CQ ≤ C := by linarith
  have hBTle : BT ≤ C := by linarith
  have hCHCFle : CH * CF + BT ≤ C := by linarith
  have hBSle : BS ≤ C := by linarith
  have hJle : farJ ^ 2 ≤ C := by linarith
  have ha₀le : a₀ + 3 ≤ C := by linarith
  -- the three Laplace integrals over the whole line
  obtain ⟨hT1i, hT1v⟩ := integral_kernelSum_mul_exp hsl hh hhc hs
  obtain ⟨hT2i, hT2v⟩ := integral_kernelSum_mul_exp hsl hh hhc (show 0 < 1 + s by linarith)
  rw [← farCrossSum_eq_kernelSum] at hT1i hT1v hT2i hT2v
  obtain ⟨hS3i', hS3v'⟩ := integral_farSum_mul_exp hsl (show 0 < s / 2 by linarith)
  have hS3i : Integrable fun a => farSum lam a * Real.exp (-(1 + s) * a) := by
    refine hS3i'.congr (Eventually.of_forall fun a => ?_)
    show farSum lam a * Real.exp (-(1 + 2 * (s / 2)) * a) = _
    rw [show 1 + 2 * (s / 2) = 1 + s by ring]
  have hS3v : ∫ a, farSum lam a * Real.exp (-(1 + s) * a) =
      farLaplace (s / 2) / 2 * oddDirichlet lam (s / 2) := by
    rw [← hS3v']
    congr 1; funext a; rw [show 1 + 2 * (s / 2) = 1 + s by ring]
  -- splitting off the left half-lines
  have split : ∀ {f : ℝ → ℝ}, Integrable f →
      ∫ a in Ici a₀, f a = (∫ a, f a) - ∫ a in Iio a₀, f a := fun {f} hf => by
    rw [← integral_add_compl measurableSet_Ici hf, compl_Ici]; ring
  have r1 := (abs_setIntegral_Iio_mul_exp_le (by norm_num) (by norm_num) hT0 (by linarith) hTD a₀
    (μ := 1 / 2 + s) (by linarith) (by linarith)).2
  have r2 := (abs_setIntegral_Iio_mul_exp_le (by norm_num) (by norm_num) hT0 (by linarith) hTD a₀
    (μ := 1 / 2 + (1 + s)) (by linarith) (by linarith)).2
  have r3 := (abs_setIntegral_Iio_mul_exp_le (by norm_num) (by norm_num) hS0 le_rfl hSD a₀
    (μ := 1 + s) (by linarith) (by linarith)).2
  rw [← hBT] at r1 r2
  rw [← hBS] at r3
  have hX1 := split hT1i
  have hX2 := split hT2i
  have hX3 := split hS3i
  have hT1v' : ∫ a, farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a) =
      farCrossLaplace g s * oddDirichlet lam s := hT1v
  have hT2v' : ∫ a, farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a) =
      farCrossLaplace g (1 + s) * oddDirichlet lam (1 + s) := hT2v
  rw [hT1v'] at hX1
  rw [hT2v'] at hX2
  rw [hS3v] at hX3
  have hQ : |farCrossLaplace g s - (∫ x, g x * Real.exp (-x / 2)) * farJ| ≤ s * CQ := by
    have h := abs_farCrossLaplace_sub_le hg hR hgs hs.le (by linarith)
    rw [farCrossLaplace_zero hg.continuous hgc hge] at h
    simp only [hCQ]
    linarith
  have hQ2 := abs_farCrossLaplace_le hg hgs (s := 1 + s) (by linarith) (by linarith)
  rw [← hCH] at hQ2
  have hF2 := abs_oddDirichlet_le hsl (s := 1 + s) (by linarith)
  rw [← hCF] at hF2
  have hK := abs_farLaplace_sub_le (σ := s / 2) (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the first window integral
    rw [hX1]
    set X := s * oddDirichlet lam s
    set Q := farCrossLaplace g s
    set P := ∫ x, g x * Real.exp (-x / 2)
    set r := ∫ a in Iio a₀, farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a)
    have e : s * (Q * oddDirichlet lam s - r) - P * farJ * X = (Q - P * farJ) * X - s * r := by
      simp only [X]; ring
    rw [e]
    clear_value X Q P r
    calc |(Q - P * farJ) * X - s * r| ≤ |Q - P * farJ| * |X| + s * |r| :=
          (abs_sub _ _).trans (le_of_eq (by rw [abs_mul (Q - P * farJ) X, abs_mul s r,
            abs_of_pos hs]))
      _ ≤ s * CQ * |X| + s * BT :=
          add_le_add (mul_le_mul_of_nonneg_right hQ (abs_nonneg _))
            (mul_le_mul_of_nonneg_left r1 hs.le)
      _ ≤ C * (s * |X|) + C * s := by
          have h3 := mul_nonneg hs.le (abs_nonneg X)
          linarith [mul_le_mul_of_nonneg_right hCQle h3, mul_le_mul_of_nonneg_left hBTle hs.le]
  · -- the second window integral
    rw [hX2]
    set r := ∫ a in Iio a₀, farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a)
    calc |s * (farCrossLaplace g (1 + s) * oddDirichlet lam (1 + s) - r)|
        ≤ s * (|farCrossLaplace g (1 + s)| * |oddDirichlet lam (1 + s)| + |r|) := by
          rw [abs_mul, abs_of_pos hs]
          refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (le_of_eq ?_)) hs.le
          rw [abs_mul]
      _ ≤ s * (CH * CF + BT) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul hQ2 hF2 (abs_nonneg _) hCH0) r2)
            hs.le
      _ ≤ C * s := by
          have := mul_le_mul_of_nonneg_left hCHCFle hs.le
          linarith
  · -- the far-bump integral
    rw [hX3]
    set Y := s / 2 * oddDirichlet lam (s / 2)
    set K := farLaplace (s / 2)
    set r := ∫ a in Iio a₀, farSum lam a * Real.exp (-(1 + s) * a)
    have e : s * (K / 2 * oddDirichlet lam (s / 2) - r) - farJ ^ 2 * Y =
        (K - farJ ^ 2) * Y - s * r := by
      simp only [Y]; ring
    rw [e]
    clear_value Y K r
    calc |(K - farJ ^ 2) * Y - s * r| ≤ |K - farJ ^ 2| * |Y| + s * |r| :=
          (abs_sub _ _).trans (le_of_eq (by rw [abs_mul (K - farJ ^ 2) Y, abs_mul s r,
            abs_of_pos hs]))
      _ ≤ s / 2 / 3 * farJ ^ 2 * |Y| + s * BS :=
          add_le_add (mul_le_mul_of_nonneg_right hK (abs_nonneg _))
            (mul_le_mul_of_nonneg_left r3 hs.le)
      _ ≤ C * (s * |Y|) + C * s := by
          have h3 := mul_nonneg hs.le (abs_nonneg Y)
          have h4 : s / 2 / 3 * farJ ^ 2 * |Y| ≤ farJ ^ 2 * (s * |Y|) := by
            have := mul_nonneg hJ2 h3
            have e2 : s / 2 / 3 * farJ ^ 2 * |Y| = 1 / 6 * (farJ ^ 2 * (s * |Y|)) := by ring
            rw [e2]; linarith
          linarith [mul_le_mul_of_nonneg_right hJle h3, mul_le_mul_of_nonneg_left hBSle hs.le]
  · have := abs_integral_abelWeight_sub_le hs ha₀0
    calc _ ≤ s * (a₀ + 3) := this
      _ ≤ C * s := by linarith [mul_le_mul_of_nonneg_left ha₀le hs.le]
  · have h1 := integral_exp_neg_Ici_le (μ := 1 / 2 + s) (by linarith) ha₀0
    have h2 := integral_exp_neg_Ici_le (μ := 1 / 2 + (1 + s)) (by linarith) ha₀0
    linarith
  · exact integral_exp_neg_Ici_le (μ := 1 + s) (by linarith) ha₀0

/-! ## The abstract limit -/

theorem tendsto_half_nhdsGT : Tendsto (fun s : ℝ => s / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
  · have h : Tendsto (fun s : ℝ => s / 2) (𝓝 0) (𝓝 (0 / 2)) :=
      (continuous_id.div_const 2).tendsto 0
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · exact mem_Ioi.mpr (half_pos (mem_Ioi.mp hs))

/-- **Abstract Abel limit.**  The averaged inequality together with the bounds of `abel_bounds`
and `s X(s) → 0` give `W ≥ P² (2 − 4X(s) + 2X(s/2)) − ε` for all small `s > 0`. -/
theorem eventually_ge_of_abel_data {W P J M C : ℝ} (hJ : 0 < J) (hM : 0 ≤ M) (hC : 0 ≤ C)
    {I₀ A₁ A₂ A₃ E₁ E₂ X : ℝ → ℝ}
    (hmain : ∀ s, 0 < s → s ≤ 1 / 2 → 0 ≤ (W - 2 * P ^ 2) * I₀ s +
      4 * (P / J) * s * (A₁ s + A₂ s) - 2 * (P / J) ^ 2 * s * A₃ s +
      M * (|P| / J * s * E₁ s + (P / J) ^ 2 * s * E₂ s))
    (hb : ∀ s, 0 < s → s ≤ 1 / 2 →
      |s * A₁ s - P * J * X s| ≤ C * (s * |X s|) + C * s ∧ |s * A₂ s| ≤ C * s ∧
      |s * A₃ s - J ^ 2 * X (s / 2)| ≤ C * (s * |X (s / 2)|) + C * s ∧
      |I₀ s - 1| ≤ C * s ∧ E₁ s ≤ 4 ∧ E₂ s ≤ 2)
    (hX : Tendsto (fun s => s * X s) (𝓝[>] 0) (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), P ^ 2 * (2 - 4 * X s + 2 * X (s / 2)) - ε ≤ W := by
  intro ε hε
  have hX2 : Tendsto (fun s => s / 2 * X (s / 2)) (𝓝[>] 0) (𝓝 0) := hX.comp tendsto_half_nhdsGT
  set K₀ : ℝ := |W - 2 * P ^ 2| * C + 4 * (|P| / J) * (2 * C) + 4 * (|P| / J) * C +
    2 * (P / J) ^ 2 * (3 * C) + M * (4 * (|P| / J) + 2 * (P / J) ^ 2) + 1 with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  set η := ε / K₀ with hη
  have hηpos : 0 < η := div_pos hε hK₀pos
  have e1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have e2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < min η (1 / 2) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min hηpos (by norm_num)))
  have e3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), |s * X s| < η := by
    have := (Metric.tendsto_nhds.mp hX) η hηpos
    filter_upwards [this] with s hs
    rwa [Real.dist_eq, sub_zero] at hs
  have e4 : ∀ᶠ s in 𝓝[>] (0 : ℝ), |s / 2 * X (s / 2)| < η := by
    have := (Metric.tendsto_nhds.mp hX2) η hηpos
    filter_upwards [this] with s hs
    rwa [Real.dist_eq, sub_zero] at hs
  filter_upwards [e1, e2, e3, e4] with s hs0 hs1 hs3 hs4
  have hsη : s < η := hs1.trans_le (min_le_left _ _)
  have hs2 : s ≤ 1 / 2 := (hs1.trans_le (min_le_right _ _)).le
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb s hs0 hs2
  have hm := hmain s hs0 hs2
  have hid : W - P ^ 2 * (2 - 4 * X s + 2 * X (s / 2)) =
      ((W - 2 * P ^ 2) * I₀ s + 4 * (P / J) * s * (A₁ s + A₂ s) - 2 * (P / J) ^ 2 * s * A₃ s +
        M * (|P| / J * s * E₁ s + (P / J) ^ 2 * s * E₂ s)) +
      (W - 2 * P ^ 2) * (1 - I₀ s) + 4 * (P / J) * (P * J * X s - s * A₁ s) -
      4 * (P / J) * (s * A₂ s) + 2 * (P / J) ^ 2 * (s * A₃ s - J ^ 2 * X (s / 2)) -
      M * (|P| / J * s * E₁ s + (P / J) ^ 2 * s * E₂ s) := by
    field_simp
    ring
  have hsX : s * |X s| < η := by
    have : |s * X s| = s * |X s| := by rw [abs_mul, abs_of_pos hs0]
    rw [← this]; exact hs3
  have hsX2 : s * |X (s / 2)| ≤ 2 * η := by
    have : s * |X (s / 2)| = 2 * |s / 2 * X (s / 2)| := by
      rw [abs_mul, abs_of_pos (half_pos hs0)]; ring
    rw [this]; linarith
  have t1 : |(W - 2 * P ^ 2) * (1 - I₀ s)| ≤ |W - 2 * P ^ 2| * C * η := by
    rw [abs_mul, abs_sub_comm (1 : ℝ) (I₀ s)]
    calc |W - 2 * P ^ 2| * |I₀ s - 1| ≤ |W - 2 * P ^ 2| * (C * s) :=
          mul_le_mul_of_nonneg_left b4 (abs_nonneg _)
      _ ≤ |W - 2 * P ^ 2| * (C * η) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsη.le hC) (abs_nonneg _)
      _ = |W - 2 * P ^ 2| * C * η := by ring
  have hPJ : 0 ≤ |P| / J := by positivity
  have t2 : |4 * (P / J) * (P * J * X s - s * A₁ s)| ≤ 4 * (|P| / J) * (2 * C) * η := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hJ, abs_sub_comm (P * J * X s) (s * A₁ s)]
    have h1 : C * (s * |X s|) + C * s ≤ 2 * C * η := by
      have k1 := mul_le_mul_of_nonneg_left hsX.le hC
      have k2 := mul_le_mul_of_nonneg_left hsη.le hC
      linarith
    have : |(4 : ℝ)| = 4 := by norm_num
    rw [this]
    calc 4 * (|P| / J) * |s * A₁ s - P * J * X s| ≤ 4 * (|P| / J) * (2 * C * η) :=
          mul_le_mul_of_nonneg_left (b1.trans h1) (by positivity)
      _ = 4 * (|P| / J) * (2 * C) * η := by ring
  have t3 : |4 * (P / J) * (s * A₂ s)| ≤ 4 * (|P| / J) * C * η := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hJ]
    have : |(4 : ℝ)| = 4 := by norm_num
    rw [this]
    calc 4 * (|P| / J) * |s * A₂ s| ≤ 4 * (|P| / J) * (C * η) :=
          mul_le_mul_of_nonneg_left (b2.trans (mul_le_mul_of_nonneg_left hsη.le hC))
            (by positivity)
      _ = 4 * (|P| / J) * C * η := by ring
  have t4 : |2 * (P / J) ^ 2 * (s * A₃ s - J ^ 2 * X (s / 2))| ≤ 2 * (P / J) ^ 2 * (3 * C) * η := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (P / J))]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    have h1 : C * (s * |X (s / 2)|) + C * s ≤ 3 * C * η := by
      have k1 := mul_le_mul_of_nonneg_left hsX2 hC
      have k2 := mul_le_mul_of_nonneg_left hsη.le hC
      linarith
    calc 2 * (P / J) ^ 2 * |s * A₃ s - J ^ 2 * X (s / 2)| ≤ 2 * (P / J) ^ 2 * (3 * C * η) :=
          mul_le_mul_of_nonneg_left (b3.trans h1) (by positivity)
      _ = 2 * (P / J) ^ 2 * (3 * C) * η := by ring
  have t5 : M * (|P| / J * s * E₁ s + (P / J) ^ 2 * s * E₂ s) ≤
      M * (4 * (|P| / J) + 2 * (P / J) ^ 2) * η := by
    have h1 : |P| / J * s * E₁ s ≤ |P| / J * s * 4 :=
      mul_le_mul_of_nonneg_left b5 (by positivity)
    have h2 : (P / J) ^ 2 * s * E₂ s ≤ (P / J) ^ 2 * s * 2 :=
      mul_le_mul_of_nonneg_left b6 (by positivity)
    have h3 : |P| / J * s * 4 + (P / J) ^ 2 * s * 2 ≤ (4 * (|P| / J) + 2 * (P / J) ^ 2) * η := by
      have h0 : 0 ≤ 4 * (|P| / J) + 2 * (P / J) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hsη.le h0
      linarith
    calc M * (|P| / J * s * E₁ s + (P / J) ^ 2 * s * E₂ s)
        ≤ M * ((4 * (|P| / J) + 2 * (P / J) ^ 2) * η) :=
          mul_le_mul_of_nonneg_left (by linarith) hM
      _ = _ := by ring
  have htot : K₀ * η = ε := by rw [hη]; field_simp
  have hK₀η : (|W - 2 * P ^ 2| * C + 4 * (|P| / J) * (2 * C) + 4 * (|P| / J) * C +
      2 * (P / J) ^ 2 * (3 * C) + M * (4 * (|P| / J) + 2 * (P / J) ^ 2)) * η ≤ ε := by
    rw [← htot, hK₀]; linarith
  have a1 := neg_abs_le ((W - 2 * P ^ 2) * (1 - I₀ s))
  have a2 := neg_abs_le (4 * (P / J) * (P * J * X s - s * A₁ s))
  have a3 := le_abs_self (4 * (P / J) * (s * A₂ s))
  have a4 := neg_abs_le (2 * (P / J) ^ 2 * (s * A₃ s - J ^ 2 * X (s / 2)))
  clear_value K₀ η
  linarith

/-! ## The two-scale iteration -/

/-- **Two-scale iteration.**  If `X(s) ≤ 1 + ε` and `s X(s) ≥ −ε` for small `s`, and
`W ≥ P² (2 − 4X(s) + 2X(s/2)) − ε` for small `s`, then `W ≥ 0`.  Otherwise
`2X(s) − X(s/2) ≥ 1 + η` near `0`, so `1 + η − X(s₂ 2^{−k})` doubles with `k` and
`s₂ 2^{−k} X(s₂ 2^{−k})` stays below `−s₂η/2 + o(1)`. -/
theorem nonneg_of_two_scale {W P : ℝ} {X : ℝ → ℝ}
    (hup : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), X s ≤ 1 + ε)
    (hlow : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * X s)
    (hW : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), P ^ 2 * (2 - 4 * X s + 2 * X (s / 2)) - ε ≤ W) :
    0 ≤ W := by
  by_contra hneg
  push Not at hneg
  rcases eq_or_ne P 0 with hP | hP
  · obtain ⟨s, hs⟩ := (hW (-W / 2) (by linarith)).exists
    rw [hP] at hs
    norm_num at hs
    linarith
  have hP2 : 0 < P ^ 2 := by positivity
  set η := -W / P ^ 2 with hη
  have hηpos : 0 < η := div_pos (by linarith) hP2
  have hWη : W = -(P ^ 2 * η) := by rw [hη]; field_simp
  have hU : ∀ᶠ s in 𝓝[>] (0 : ℝ), 1 + η / 4 ≤ 2 * X s - X (s / 2) := by
    filter_upwards [hW (P ^ 2 * η / 2) (by positivity)] with s hs
    rw [hWη] at hs
    have h1 : P ^ 2 * (2 - 4 * X s + 2 * X (s / 2) + η / 2) ≤ 0 := by nlinarith
    have h2 : 2 - 4 * X s + 2 * X (s / 2) + η / 2 ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    linarith
  obtain ⟨s₁, hs₁pos, hs₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hU
  obtain ⟨s₁', hs₁'pos, hs₁'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hup (η / 8) (by positivity))
  have hs₁pos' : (0 : ℝ) < s₁ := hs₁pos
  have hs₁'pos' : (0 : ℝ) < s₁' := hs₁'pos
  set s₂ := min s₁ s₁' / 2 with hs₂
  have hs₂pos : 0 < s₂ := by positivity
  have hs₂1 : s₂ < s₁ := by
    have := min_le_left s₁ s₁'; rw [hs₂]; linarith [half_lt_self (lt_min hs₁pos' hs₁'pos')]
  have hs₂1' : s₂ < s₁' := by
    have := min_le_right s₁ s₁'; rw [hs₂]; linarith [half_lt_self (lt_min hs₁pos' hs₁'pos')]
  set t : ℕ → ℝ := fun k => s₂ * (1 / 2) ^ k with ht
  have htpos : ∀ k, 0 < t k := fun k => by simp only [ht]; positivity
  have htle : ∀ k, t k ≤ s₂ := fun k => by
    simp only [ht]
    exact mul_le_of_le_one_right hs₂pos.le (pow_le_one₀ (by norm_num) (by norm_num))
  have htsucc : ∀ k, t (k + 1) = t k / 2 := fun k => by simp only [ht]; rw [pow_succ]; ring
  have hgrow : ∀ k : ℕ, 2 ^ k * (η / 8) ≤ 1 + η / 4 - X (t k) := by
    intro k
    induction k with
    | zero =>
      have h0 : X s₂ ≤ 1 + η / 8 := hs₁' ⟨hs₂pos, hs₂1'⟩
      have e : t 0 = s₂ := by simp only [ht, pow_zero, mul_one]
      rw [e, pow_zero, one_mul]
      linarith
    | succ k ih =>
      have hk : 1 + η / 4 ≤ 2 * X (t k) - X (t k / 2) := hs₁ ⟨htpos k, (htle k).trans_lt hs₂1⟩
      rw [htsucc, pow_succ]
      linarith
  have hprod : ∀ k : ℕ, t k * X (t k) ≤ t k * (1 + η / 4) - s₂ * (η / 8) := by
    intro k
    have h1 := mul_le_mul_of_nonneg_left (hgrow k) (htpos k).le
    have h2 : t k * (2 ^ k * (η / 8)) = s₂ * (η / 8) := by
      simp only [ht]
      rw [show s₂ * (1 / 2) ^ k * (2 ^ k * (η / 8)) = s₂ * (η / 8) * ((1 / 2) ^ k * 2 ^ k) by ring,
        ← mul_pow]
      norm_num
    nlinarith
  obtain ⟨s₃, hs₃pos, hs₃⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (hlow (s₂ * η / 32) (by positivity))
  have hs₃pos' : (0 : ℝ) < s₃ := hs₃pos
  set δ := min (s₃ / s₂) (η / (16 * (1 + η / 4))) with hδ
  have hδpos : 0 < δ := lt_min (div_pos hs₃pos' hs₂pos) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδpos (show (1 / 2 : ℝ) < 1 by norm_num)
  have hk1 : t k < s₃ := by
    simp only [ht]
    have := hk.trans_le (min_le_left _ _)
    rw [lt_div_iff₀ hs₂pos] at this
    linarith
  have hk2 : t k * (1 + η / 4) < s₂ * η / 16 := by
    simp only [ht]
    have := hk.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have hlowk := hs₃ ⟨htpos k, hk1⟩
  have := hprod k
  simp only [mem_setOf_eq] at hlowk
  nlinarith

/-! ## The ceiling in Abel form -/

/-- **The log-density ceiling in Abel form.**  If `Σ_{nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)(log N)²` and
the Dirichlet series converges absolutely on `Re s > 1`, then `s F(s) ≤ 1 + ε` for all small
`s > 0`. -/
theorem eventually_le_one_add_of_log_density_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hld : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then lam n / (n * m) else 0) ≤ (1 / 2 + ε) * Real.log N ^ 2) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), s * oddDirichlet lam s ≤ 1 + ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hld (ε / 4) (by positivity)
  set K : ℝ := ∑ N ∈ Finset.range N₀, |logDensitySum lam N| with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK : ∀ N : ℕ, N < N₀ → logDensitySum lam N ≤ K := fun N hN =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun N => |logDensitySum lam N|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hN))
  have hU : ∀ σ : ℝ, 0 < σ → σ * oddDirichlet lam σ * ((σ : ℂ) * riemannZeta (1 + σ)).re ≤
      σ ^ 2 * K + (1 + ε / 2) := by
    intro σ hσ
    have hc := re_LSeries_lamConv_le hsl (c := 1 / 2 + ε / 4) (by positivity)
      (fun N hN => hN₀ N hN) hK hK0 hσ
    rw [LSeries_lamConv hsl hσ, LSeries_lamC_eq_oddDirichlet, Complex.re_ofReal_mul] at hc
    rw [Complex.re_ofReal_mul]
    calc σ * oddDirichlet lam σ * (σ * (riemannZeta (1 + σ)).re)
        = σ ^ 2 * (oddDirichlet lam σ * (riemannZeta (1 + σ)).re) := by ring
      _ ≤ σ ^ 2 * (K + 2 * (1 / 2 + ε / 4) / σ ^ 2) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = σ ^ 2 * K + (1 + ε / 2) := by field_simp; ring
  have hg : Tendsto (fun σ : ℝ => ((σ : ℂ) * riemannZeta (1 + σ)).re) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (Complex.continuous_re.tendsto (1 : ℂ)).comp tendsto_mul_riemannZeta_one_add
    rw [Complex.one_re] at h1
    exact h1
  have hgap : Tendsto (fun σ : ℝ => (1 + ε) * ((σ : ℂ) * riemannZeta (1 + σ)).re -
      (σ ^ 2 * K + (1 + ε / 2))) (𝓝[>] 0) (𝓝 ((1 + ε) * 1 - (0 ^ 2 * K + (1 + ε / 2)))) := by
    refine (hg.const_mul _).sub ?_
    have hc : Continuous fun σ : ℝ => σ ^ 2 * K + (1 + ε / 2) := by fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hgap' : (0 : ℝ) < (1 + ε) * 1 - (0 ^ 2 * K + (1 + ε / 2)) := by norm_num; linarith
  filter_upwards [self_mem_nhdsWithin, hgap.eventually (lt_mem_nhds hgap'),
    hg.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with σ hσ h1 h2
  have hσ' : 0 < σ := hσ
  have hUσ := hU σ hσ'
  by_contra hc
  push Not at hc
  have := mul_lt_mul_of_pos_right hc h2
  nlinarith

theorem eventually_le_one_add_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), s * oddDirichlet lam s ≤ 1 + ε :=
  eventually_le_one_add_of_log_density_le hsl fun _ hε => even_log_density_le h hε

theorem tendsto_mul_of_two_sided {X : ℝ → ℝ}
    (hup : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), X s ≤ 1 + ε)
    (hlow : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * X s) :
    Tendsto (fun s => s * X s) (𝓝[>] 0) (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun η hη => ?_
  filter_upwards [self_mem_nhdsWithin, hup 1 one_pos, hlow (η / 2) (by positivity),
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (show (0 : ℝ) < η / 2 by
      positivity))] with s hs h1 h2 h3
  have hs' : 0 < s := hs
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor
  · linarith
  · nlinarith

end RHTower.EvenSector

end
