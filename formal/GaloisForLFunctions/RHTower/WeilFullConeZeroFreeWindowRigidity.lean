import GaloisForLFunctions.RHTower.RiemannKernelSpectralLocalization

/-!
# Zero-free-window rigidity of the full Weil cone

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_sq_summable_separated`, unconditional).
Let `lam` be full-cone Weil-positive and `v(n) = (Λ(n) − lam(n))/√n`. Suppose that:
- `Σ v(n)² < ∞`;
- the support of `v` has polynomially separated logarithms:
  `|log m − log n| ≥ c(1 + log m + log n)^{−D}` for distinct `m, n` in the support.

Then `lam = Λ` on `n ≥ 2`.

By Baker's theorem on linear forms in logarithms, every finitely generated multiplicative
semigroup `⟨p₁, …, p_r⟩` satisfies the separation hypothesis. Unlike the sparse supports of
`WeilFullConeLacunaryRigidity`, such supports have logarithms that accumulate.

**Proof.**
- On a window of `[T, 2T]` free of zeros of `X = Ξ(2π·)` within `η`,
  `Y(t) = Σ v(n) B(η log n) cos(2πt log n) ≥ 0` (`localized_deviation_nonneg`).
- The windows that are not zero-free have total length `≲ ηT log T`
  (`realZeroSet_multi`, from the local zero count of the corpus).
- The separation gives mean values over `[T, 2T]` with diagonal `(T/2)Σc_n²` and off-diagonal
  errors `O(Q²)` (`abs_integral_windowCosSeries_mul_cos_sub_le`, `abs_integral_windowCosSeries_sq_sub_le`).
- The negative part of `Y` lives on the bad set, so `∫|Y|` is controlled
  (`half_mul_abs_le_of_zeroFree`). Extracting a coefficient then gives `|v(m)B(η log m)| → 0`
  as `η → 0` with `T = η^{−(2J+1)}`.

**Reach.** The argument needs the support's log-gaps at height `X` to be `e^{−o(X)}`. For the full
support `ℕ` the gaps are `e^{−X}`, which exactly balances the zero density `log T/2π`: the
uncertainty-principle form of the `α ≥ 1` barrier.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-! ## Counting the real zeros of `X` -/

/-- The real zeros of `X` in `[a, b]`. -/
def realZeroSet (a b : ℝ) : Set ℝ := {ξ | ξ ∈ Icc a b ∧ phiFourierReal ξ = 0}

theorem re_xiSpectralPoint (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint, Complex.mul_re]

theorem exists_xiZeroCopy_of_phiFourierReal_eq_zero {ξ : ℝ} (h : phiFourierReal ξ = 0) :
    ∃ q : XiZeroCopy, (q.1 : ℂ).im = 2 * π * ξ := by
  have h1 : XiC ((2 * π * ξ : ℝ) : ℂ) = 0 := by
    rw [XiC_ofReal]; unfold phiFourierReal at h; rw [h, Complex.ofReal_zero]
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp h1
  refine ⟨q, ?_⟩
  have := congrArg Complex.re hq
  rwa [re_xiSpectralPoint, Complex.ofReal_re] at this

/-- The zero-count bound on a unit interval. -/
def unitZeroBound (a : ℝ) : ℝ :=
  8 * (1 + π ^ 2) * (xiLineTwoLogDerivConstant + Real.log (|2 * π * (a + 1 / 2)| + 4))

theorem realZeroSet_unit (a : ℝ) :
    (realZeroSet a (a + 1)).Finite ∧ ((realZeroSet a (a + 1)).ncard : ℝ) ≤ unitZeroBound a := by
  set W := xiOrdinateWindow π (2 * π * (a + 1 / 2)) with hW
  have hWf : W.Finite := finite_xiOrdinateWindow _ _
  set g : XiZeroCopy → ℝ := fun q => (q.1 : ℂ).im / (2 * π) with hg
  have hsub : realZeroSet a (a + 1) ⊆ g '' W := by
    rintro ξ ⟨⟨h1, h2⟩, h0⟩
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_phiFourierReal_eq_zero h0
    refine ⟨q, ?_, ?_⟩
    · rw [hW, mem_xiOrdinateWindow_iff, hq,
        show 2 * π * ξ - 2 * π * (a + 1 / 2) = 2 * π * (ξ - (a + 1 / 2)) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have : |ξ - (a + 1 / 2)| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
      nlinarith [Real.pi_pos]
    · simp only [hg, hq]; field_simp
  have hfin : (g '' W).Finite := hWf.image g
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_image_le (f := g) hWf
  have h3 := ncard_xiOrdinateWindow_le_log π (2 * π * (a + 1 / 2))
  unfold unitZeroBound
  calc ((realZeroSet a (a + 1)).ncard : ℝ) ≤ (W.ncard : ℝ) := by exact_mod_cast h1.trans h2
    _ ≤ _ := h3

theorem unitZeroBound_mono {a b : ℝ} (h : |2 * π * (a + 1 / 2)| ≤ |2 * π * (b + 1 / 2)|) :
    unitZeroBound a ≤ unitZeroBound b := by
  unfold unitZeroBound
  gcongr

theorem unitZeroBound_le_of_le {a b : ℝ} (hb : 0 ≤ b) (h : |a| ≤ b) :
    unitZeroBound a ≤ unitZeroBound b := by
  refine unitZeroBound_mono ?_
  rw [abs_mul (2 * π) (a + 1 / 2), abs_mul (2 * π) (b + 1 / 2),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b + 1 / 2)]
  calc |a + 1 / 2| ≤ |a| + |1 / 2| := abs_add_le _ _
    _ ≤ b + 1 / 2 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith

/-- `#(real zeros in [a, a + N + 1]) ≤ (N + 1)·U(|a| + N + 1)`. -/
theorem realZeroSet_multi (a : ℝ) (N : ℕ) :
    (realZeroSet a (a + (N + 1))).Finite ∧
      ((realZeroSet a (a + (N + 1))).ncard : ℝ) ≤ (N + 1) * unitZeroBound (|a| + (N + 1)) := by
  induction N with
  | zero =>
    obtain ⟨h1, h2⟩ := realZeroSet_unit a
    push_cast; simp only [zero_add, one_mul]
    refine ⟨h1, h2.trans (unitZeroBound_le_of_le (by positivity) (by linarith))⟩
  | succ N ih =>
    obtain ⟨hf, hb⟩ := ih
    obtain ⟨hf1, hb1⟩ := realZeroSet_unit (a + (N + 1))
    have hsub : realZeroSet a (a + ((N + 1 : ℕ) + 1)) ⊆
        realZeroSet a (a + (N + 1)) ∪ realZeroSet (a + (N + 1)) (a + (N + 1) + 1) := by
      rintro ξ ⟨⟨h1, h2⟩, h0⟩
      push_cast at h2
      by_cases hξ : ξ ≤ a + (N + 1)
      · exact Or.inl ⟨⟨h1, hξ⟩, h0⟩
      · exact Or.inr ⟨⟨by linarith, by linarith⟩, h0⟩
    have hfu := hf.union hf1
    refine ⟨hfu.subset hsub, ?_⟩
    have hc := (Set.ncard_le_ncard hsub hfu).trans (Set.ncard_union_le _ _)
    have hU1 : unitZeroBound (|a| + (N + 1)) ≤ unitZeroBound (|a| + ((N + 1 : ℕ) + 1)) :=
      unitZeroBound_le_of_le (by positivity) (by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ |a| + (N + 1) by positivity)]; push_cast; linarith)
    have hU2 : unitZeroBound (a + (N + 1)) ≤ unitZeroBound (|a| + ((N + 1 : ℕ) + 1)) :=
      unitZeroBound_le_of_le (by positivity) (by
        calc |a + (N + 1)| ≤ |a| + |(N : ℝ) + 1| := abs_add_le _ _
          _ ≤ |a| + ((N + 1 : ℕ) + 1) := by
            rw [abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)]; push_cast; linarith)
    have hN0 : (0 : ℝ) ≤ N + 1 := by positivity
    have hcast : (((realZeroSet a (a + ((N + 1 : ℕ) + 1))).ncard : ℕ) : ℝ) ≤
        ((realZeroSet a (a + (N + 1))).ncard : ℝ) +
          ((realZeroSet (a + (N + 1)) (a + (N + 1) + 1)).ncard : ℝ) := by exact_mod_cast hc
    calc ((realZeroSet a (a + ((N + 1 : ℕ) + 1))).ncard : ℝ)
        ≤ (N + 1) * unitZeroBound (|a| + (N + 1)) + unitZeroBound (a + (N + 1)) := by
          linarith
      _ ≤ (N + 1) * unitZeroBound (|a| + ((N + 1 : ℕ) + 1)) +
            unitZeroBound (|a| + ((N + 1 : ℕ) + 1)) := by
          gcongr
      _ = ((N + 1 : ℕ) + 1) * unitZeroBound (|a| + ((N + 1 : ℕ) + 1)) := by push_cast; ring


/-! ## Mean values of cosine series -/

theorem abs_integral_cos_le {lA : ℝ} (hlA : lA ≠ 0) (a b : ℝ) :
    |∫ t in a..b, Real.cos (2 * π * t * lA)| ≤ 1 / (π * |lA|) := by
  have hc : 2 * π * lA ≠ 0 := mul_ne_zero (by positivity) hlA
  have e : (fun t => Real.cos (2 * π * t * lA)) = fun t => Real.cos ((2 * π * lA) * t) := by
    funext t; ring_nf
  rw [e, intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hc, integral_cos,
    smul_eq_mul, abs_mul, abs_inv]
  have h2 : |Real.sin (2 * π * lA * b) - Real.sin (2 * π * lA * a)| ≤ 2 := by
    have := abs_sub (Real.sin (2 * π * lA * b)) (Real.sin (2 * π * lA * a))
    linarith [Real.abs_sin_le_one (2 * π * lA * b), Real.abs_sin_le_one (2 * π * lA * a)]
  have hpos : 0 < |2 * π * lA| := abs_pos.mpr hc
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos] at hpos ⊢
  rw [inv_mul_le_iff₀ hpos]
  have : 2 * π * |lA| * (1 / (π * |lA|)) = 2 := by
    field_simp
  linarith

theorem cos_mul_cos_eq_half_add (x y : ℝ) :
    Real.cos x * Real.cos y = (Real.cos (x - y) + Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- The diagonal mean value. -/
theorem abs_integral_cos_sq_sub_le {lA : ℝ} (hlA : 0 < lA) (a b : ℝ) :
    |(∫ t in a..b, Real.cos (2 * π * t * lA) * Real.cos (2 * π * t * lA)) - (b - a) / 2| ≤
      1 / (4 * π * lA) := by
  have e : (fun t => Real.cos (2 * π * t * lA) * Real.cos (2 * π * t * lA)) =
      fun t => (1 + Real.cos (2 * π * t * (2 * lA))) / 2 := by
    funext t; rw [cos_mul_cos_eq_half_add, sub_self, Real.cos_zero]; ring_nf
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun t => Real.cos (2 * π * t * (2 * lA))).intervalIntegrable a b),
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have h := abs_integral_cos_le (lA := 2 * lA) (by positivity) a b
  rw [abs_of_pos (by positivity : 0 < 2 * lA)] at h
  rw [show (b - a + ∫ t in a..b, Real.cos (2 * π * t * (2 * lA))) / 2 - (b - a) / 2 =
    (∫ t in a..b, Real.cos (2 * π * t * (2 * lA))) / 2 by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc |∫ t in a..b, Real.cos (2 * π * t * (2 * lA))| / 2 ≤ 1 / (π * (2 * lA)) / 2 := by gcongr
    _ = 1 / (4 * π * lA) := by field_simp; ring

/-- The off-diagonal mean value. -/
theorem abs_integral_cos_mul_cos_le {lA lB : ℝ} (hlA : 0 < lA) (hlB : 0 < lB) (hne : lA ≠ lB)
    (a b : ℝ) :
    |∫ t in a..b, Real.cos (2 * π * t * lA) * Real.cos (2 * π * t * lB)| ≤
      1 / (2 * π * |lA - lB|) + 1 / (2 * π * (lA + lB)) := by
  have e : (fun t => Real.cos (2 * π * t * lA) * Real.cos (2 * π * t * lB)) =
      fun t => (Real.cos (2 * π * t * (lA - lB)) + Real.cos (2 * π * t * (lA + lB))) / 2 := by
    funext t; rw [cos_mul_cos_eq_half_add]; ring_nf
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun t => Real.cos (2 * π * t * (lA - lB))).intervalIntegrable a b)
    ((by fun_prop : Continuous fun t => Real.cos (2 * π * t * (lA + lB))).intervalIntegrable a b)]
  have h1 := abs_integral_cos_le (lA := lA - lB) (sub_ne_zero.mpr hne) a b
  have h2 := abs_integral_cos_le (lA := lA + lB) (by positivity) a b
  rw [abs_of_pos (by positivity : 0 < lA + lB)] at h2
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h3 := abs_add_le (∫ t in a..b, Real.cos (2 * π * t * (lA - lB)))
    (∫ t in a..b, Real.cos (2 * π * t * (lA + lB)))
  have e1 : 1 / (π * |lA - lB|) / 2 = 1 / (2 * π * |lA - lB|) := by field_simp
  have e2 : 1 / (π * (lA + lB)) / 2 = 1 / (2 * π * (lA + lB)) := by field_simp
  rw [← e1, ← e2]
  linarith

/-- Interval integrals commute with absolutely summable cosine-type series. -/
theorem integral_tsum_mul_of_abs_le {c : ℕ → ℝ} (hc : Summable fun n => |c n|)
    {f : ℕ → ℝ → ℝ} (hf : ∀ n, Continuous (f n)) {M : ℝ} (hf1 : ∀ n t, |f n t| ≤ M) (a b : ℝ) :
    ∫ t in a..b, (∑' n, c n * f n t) = ∑' n, c n * ∫ t in a..b, f n t := by
  have hb : ∀ n t, ‖c n * f n t‖ ≤ |c n| * M := fun n t => by
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hf1 n t) (abs_nonneg _)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := a) (b := b)
    (F := fun n t => c n * f n t) (f := fun t => ∑' n, c n * f n t)
    (fun n _ => |c n| * M) (fun n => ((continuous_const.mul (hf n)).aestronglyMeasurable))
    (fun n => Eventually.of_forall fun t _ => hb n t)
    (Eventually.of_forall fun t _ => hc.mul_right M)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ => ((hc.mul_right M).of_norm_bounded (fun n => hb n t)).hasSum)
  rw [← h.tsum_eq]
  exact tsum_congr fun n => intervalIntegral.integral_const_mul _ _


/-- The cosine series `Y(t) = Σ c_n cos(2πt log n)`. -/
def windowCosSeries (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, c n * Real.cos (2 * π * t * Real.log n)

theorem continuous_windowCosSeries {c : ℕ → ℝ} (hc : Summable fun n => |c n|) :
    Continuous (windowCosSeries c) := by
  unfold windowCosSeries
  refine continuous_tsum (fun n => by fun_prop) hc fun n t => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem abs_windowCosSeries_le {c : ℕ → ℝ} (hc : Summable fun n => |c n|) (t : ℝ) :
    |windowCosSeries c t| ≤ ∑' n, |c n| := by
  unfold windowCosSeries
  have hs : Summable fun n => c n * Real.cos (2 * π * t * Real.log n) :=
    hc.of_norm_bounded fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans (hs.norm.tsum_le_tsum (fun n => ?_) hc)
  rw [Real.norm_eq_abs, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The weight `w(n) = (1 + 2 log n)^D`. -/
def sepLogWeight (D : ℕ) (n : ℕ) : ℝ := (1 + 2 * Real.log n) ^ D

theorem one_le_sepLogWeight (D n : ℕ) : 1 ≤ sepLogWeight D n := by
  unfold sepLogWeight
  exact one_le_pow₀ (by have := Real.log_natCast_nonneg n; linarith)

theorem one_add_add_pow_le (D : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1 + x + y) ^ D ≤ (1 + 2 * x) ^ D * (1 + 2 * y) ^ D := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by nlinarith [mul_nonneg hx hy]) D


/-- A pointwise bound for the mean-value kernel. -/
theorem abs_meanKernel_le {c : ℕ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) {D : ℕ}
    (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n)
    (hgap : ∀ m n, c m ≠ 0 → c n ≠ 0 → m ≠ n →
      c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n|)
    {m : ℕ} (hm : c m ≠ 0) (a b : ℝ) (n : ℕ) :
    |c n * (∫ t in a..b, Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log m)) -
        (if n = m then (b - a) / 2 * c m else 0)| ≤
      (1 / c₀ + 1) * sepLogWeight D m * (|c n| * sepLogWeight D n) := by
  have hπ := Real.pi_gt_three
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlm : Real.log 2 ≤ Real.log m :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hc2 m hm)
  have hwm := one_le_sepLogWeight D m
  have hwn := one_le_sepLogWeight D n
  have hC : 1 ≤ 1 / c₀ + 1 := by have := one_div_pos.mpr hc₀; linarith
  by_cases hn : c n = 0
  · have hnm : n ≠ m := fun h => hm (h ▸ hn)
    rw [hn, zero_mul, if_neg hnm, sub_zero, abs_zero]
    positivity
  by_cases hnm : n = m
  · subst hnm
    rw [if_pos rfl, show c n * (∫ t in a..b, Real.cos (2 * π * t * Real.log n) *
      Real.cos (2 * π * t * Real.log n)) - (b - a) / 2 * c n = c n *
      ((∫ t in a..b, Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log n)) -
        (b - a) / 2) by ring, abs_mul]
    have hlpos : 0 < Real.log n := by linarith
    have h := abs_integral_cos_sq_sub_le (lA := Real.log n) hlpos a b
    have h1 : 1 / (4 * π * Real.log n) ≤ 1 := by
      rw [div_le_one (mul_pos (by positivity) hlpos)]; nlinarith
    calc |c n| * |(∫ t in a..b, Real.cos (2 * π * t * Real.log n) *
          Real.cos (2 * π * t * Real.log n)) - (b - a) / 2| ≤ |c n| * 1 :=
          mul_le_mul_of_nonneg_left (h.trans h1) (abs_nonneg _)
      _ ≤ (1 / c₀ + 1) * sepLogWeight D n * (|c n| * sepLogWeight D n) := by
          have := abs_nonneg (c n)
          nlinarith [mul_le_mul hC hwn zero_le_one (by linarith), mul_nonneg this (by linarith : (0:ℝ) ≤ sepLogWeight D n - 1)]
  · rw [if_neg hnm, sub_zero, abs_mul]
    have hln : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hc2 n hn)
    have hg := hgap n m hn hm hnm
    have hgpos : 0 < c₀ * ((1 + Real.log n + Real.log m) ^ D)⁻¹ := by positivity
    have hne : Real.log n ≠ Real.log m := by
      intro h
      have h0 : |Real.log n - Real.log m| = 0 := by rw [h, sub_self, abs_zero]
      linarith
    have h := abs_integral_cos_mul_cos_le (lA := Real.log n) (lB := Real.log m) (by linarith)
      (by linarith) hne a b
    have hw := one_add_add_pow_le D (Real.log_natCast_nonneg n) (Real.log_natCast_nonneg m)
    have h1 : 1 / (2 * π * |Real.log n - Real.log m|) ≤ 1 / c₀ * (sepLogWeight D n * sepLogWeight D m) := by
      rw [div_le_iff₀ (by positivity)]
      have hdiv : 1 ≤ |Real.log n - Real.log m| * (((1 + Real.log n + Real.log m) ^ D) / c₀) := by
        have := mul_le_mul_of_nonneg_right hg (by positivity :
          (0 : ℝ) ≤ ((1 + Real.log n + Real.log m) ^ D) / c₀)
        rw [show c₀ * ((1 + Real.log n + Real.log m) ^ D)⁻¹ * ((1 + Real.log n + Real.log m) ^ D / c₀)
          = 1 by field_simp] at this
        linarith
      have hpow : ((1 + Real.log n + Real.log m) ^ D) / c₀ ≤ 1 / c₀ * (sepLogWeight D n * sepLogWeight D m) := by
        rw [div_eq_mul_one_div, mul_comm, sepLogWeight, sepLogWeight]
        exact mul_le_mul_of_nonneg_left hw (by positivity)
      have habs := abs_nonneg (Real.log n - Real.log m)
      nlinarith [mul_le_mul_of_nonneg_left hpow habs]
    have h2 : 1 / (2 * π * (Real.log n + Real.log m)) ≤ sepLogWeight D n * sepLogWeight D m := by
      have : 1 / (2 * π * (Real.log n + Real.log m)) ≤ 1 := by
        rw [div_le_one (mul_pos (by positivity) (by linarith))]; nlinarith
      nlinarith [mul_le_mul hwn hwm zero_le_one (by linarith)]
    calc |c n| * |∫ t in a..b, Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log m)|
        ≤ |c n| * (1 / c₀ * (sepLogWeight D n * sepLogWeight D m) + sepLogWeight D n * sepLogWeight D m) :=
          mul_le_mul_of_nonneg_left (h.trans (add_le_add h1 h2)) (abs_nonneg _)
      _ = (1 / c₀ + 1) * sepLogWeight D m * (|c n| * sepLogWeight D n) := by ring

/-- **The mean value of `Y cos(2πt log m)`.** -/
theorem abs_integral_windowCosSeries_mul_cos_sub_le {c : ℕ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) {D : ℕ}
    (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n)
    (hgap : ∀ m n, c m ≠ 0 → c n ≠ 0 → m ≠ n →
      c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n|)
    (hQ : Summable fun n => |c n| * sepLogWeight D n) {m : ℕ} (hm : c m ≠ 0) (a b : ℝ) :
    |(∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) - (b - a) / 2 * c m| ≤
      (1 / c₀ + 1) * sepLogWeight D m * ∑' n, |c n| * sepLogWeight D n := by
  have hc : Summable fun n => |c n| :=
    hQ.of_nonneg_of_le (fun n => abs_nonneg _) fun n =>
      le_mul_of_one_le_right (abs_nonneg _) (one_le_sepLogWeight D n)
  have e1 : (fun t => windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) = fun t =>
      ∑' n, c n * (Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log m)) := by
    funext t; unfold windowCosSeries; rw [← tsum_mul_right]; exact tsum_congr fun n => by ring
  rw [e1, integral_tsum_mul_of_abs_le hc (M := 1) (fun n => by fun_prop) (fun n t => by
    rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))]
  set I : ℕ → ℝ := fun n => ∫ t in a..b, Real.cos (2 * π * t * Real.log n) *
    Real.cos (2 * π * t * Real.log m) with hI
  have hIb : ∀ n, |I n| ≤ |b - a| := fun n => by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
      (f := fun t => Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log m))
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))
    rw [one_mul, Real.norm_eq_abs] at h
    exact h
  have hs1 : Summable fun n => c n * I n := (hc.mul_right |b - a|).of_norm_bounded fun n => by
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hIb n) (abs_nonneg _)
  have hs2 : Summable fun n : ℕ => if n = m then (b - a) / 2 * c m else 0 :=
    summable_of_ne_finset_zero (s := {m}) fun n hn => by
      rw [Finset.mem_singleton] at hn; rw [if_neg hn]
  have hsum : (∑' n, c n * I n) - (b - a) / 2 * c m =
      ∑' n, (c n * I n - if n = m then (b - a) / 2 * c m else 0) := by
    rw [hs1.tsum_sub hs2, tsum_ite_eq]
  rw [hsum]
  have hb := abs_meanKernel_le hc₀ hc2 hgap hm a b
  have hs3 : Summable fun n => (1 / c₀ + 1) * sepLogWeight D m * (|c n| * sepLogWeight D n) :=
    hQ.mul_left _
  have hs4 : Summable fun n => |c n * I n - if n = m then (b - a) / 2 * c m else 0| :=
    hs3.of_nonneg_of_le (fun n => abs_nonneg _) hb
  calc |∑' n, (c n * I n - if n = m then (b - a) / 2 * c m else 0)|
      ≤ ∑' n, |c n * I n - if n = m then (b - a) / 2 * c m else 0| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs4)).trans
          (le_of_eq (tsum_congr fun n => Real.norm_eq_abs _))
    _ ≤ ∑' n, (1 / c₀ + 1) * sepLogWeight D m * (|c n| * sepLogWeight D n) :=
        hs4.tsum_le_tsum hb hs3
    _ = (1 / c₀ + 1) * sepLogWeight D m * ∑' n, |c n| * sepLogWeight D n := tsum_mul_left


/-- **The mean of `Y`.** -/
theorem abs_integral_windowCosSeries_le {c : ℕ → ℝ} (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n)
    (hc : Summable fun n => |c n|) (a b : ℝ) :
    |∫ t in a..b, windowCosSeries c t| ≤ (∑' n, |c n|) / (π * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hπ := Real.pi_pos
  unfold windowCosSeries
  rw [integral_tsum_mul_of_abs_le hc (M := 1) (fun n => by fun_prop)
    (fun n t => Real.abs_cos_le_one _)]
  have hb : ∀ n, |c n * ∫ t in a..b, Real.cos (2 * π * t * Real.log n)| ≤
      |c n| / (π * Real.log 2) := by
    intro n
    by_cases hn : c n = 0
    · rw [hn, zero_mul, abs_zero]; positivity
    have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hc2 n hn)
    have hne : Real.log n ≠ 0 := by linarith
    have h := abs_integral_cos_le hne a b
    rw [abs_of_pos (show 0 < Real.log n by linarith)] at h
    rw [abs_mul, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left (h.trans ?_) (abs_nonneg _)
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hln hπ.le)
  have hs : Summable fun n => |c n| / (π * Real.log 2) := hc.div_const _
  have hs' : Summable fun n => |c n * ∫ t in a..b, Real.cos (2 * π * t * Real.log n)| :=
    hs.of_nonneg_of_le (fun n => abs_nonneg _) hb
  calc |∑' n, c n * ∫ t in a..b, Real.cos (2 * π * t * Real.log n)|
      ≤ ∑' n, |c n * ∫ t in a..b, Real.cos (2 * π * t * Real.log n)| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs')).trans
          (le_of_eq (tsum_congr fun n => Real.norm_eq_abs _))
    _ ≤ ∑' n, |c n| / (π * Real.log 2) := hs'.tsum_le_tsum hb hs
    _ = (∑' n, |c n|) / (π * Real.log 2) := tsum_div_const

/-- **The mean square of `Y`.** -/
theorem abs_integral_windowCosSeries_sq_sub_le {c : ℕ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) {D : ℕ}
    (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n)
    (hgap : ∀ m n, c m ≠ 0 → c n ≠ 0 → m ≠ n →
      c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n|)
    (hQ : Summable fun n => |c n| * sepLogWeight D n) (a b : ℝ) :
    |(∫ t in a..b, windowCosSeries c t ^ 2) - (b - a) / 2 * ∑' n, c n ^ 2| ≤
      (1 / c₀ + 1) * (∑' n, |c n| * sepLogWeight D n) ^ 2 := by
  have hc : Summable fun n => |c n| :=
    hQ.of_nonneg_of_le (fun n => abs_nonneg _) fun n =>
      le_mul_of_one_le_right (abs_nonneg _) (one_le_sepLogWeight D n)
  set Q := ∑' n, |c n| * sepLogWeight D n with hQdef
  set A := ∑' n, |c n| with hAdef
  have hYc := continuous_windowCosSeries hc
  have e1 : (fun t => windowCosSeries c t ^ 2) = fun t =>
      ∑' m, c m * (Real.cos (2 * π * t * Real.log m) * windowCosSeries c t) := by
    funext t
    rw [sq]
    conv_lhs => rw [show windowCosSeries c t * windowCosSeries c t = (∑' m, c m * Real.cos (2 * π * t * Real.log m))
      * windowCosSeries c t from rfl]
    rw [← tsum_mul_right]; exact tsum_congr fun m => by ring
  rw [e1, integral_tsum_mul_of_abs_le hc (M := A) (fun m => by fun_prop) (fun m t => by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans
      (abs_windowCosSeries_le hc t))]
  have hIb : ∀ m, |∫ t in a..b, Real.cos (2 * π * t * Real.log m) * windowCosSeries c t| ≤ A * |b - a| := by
    intro m
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := A)
      (f := fun t => Real.cos (2 * π * t * Real.log m) * windowCosSeries c t)
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans
          (abs_windowCosSeries_le hc t))
    rwa [Real.norm_eq_abs] at h
  have hs1 : Summable fun m => c m * ∫ t in a..b, Real.cos (2 * π * t * Real.log m) * windowCosSeries c t :=
    (hc.mul_right (A * |b - a|)).of_norm_bounded fun m => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hIb m) (abs_nonneg _)
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => abs_nonneg _
  have hs2 : Summable fun m => c m ^ 2 := (hc.mul_left A).of_norm_bounded fun m => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq, ← abs_mul_abs_self]
    exact mul_le_mul_of_nonneg_right (by rw [hAdef]; exact hc.le_tsum m (fun _ _ => abs_nonneg _))
      (abs_nonneg _)
  have hsum : (∑' m, c m * ∫ t in a..b, Real.cos (2 * π * t * Real.log m) * windowCosSeries c t) -
      (b - a) / 2 * ∑' n, c n ^ 2 =
      ∑' m, c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
        (b - a) / 2 * c m) := by
    rw [← tsum_mul_left, ← hs1.tsum_sub (hs2.mul_left _)]
    refine tsum_congr fun m => ?_
    have : (∫ t in a..b, Real.cos (2 * π * t * Real.log m) * windowCosSeries c t) =
        ∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m) := by
      congr 1; funext t; ring
    rw [this]; ring
  rw [hsum]
  have hb : ∀ m, |c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
      (b - a) / 2 * c m)| ≤ (1 / c₀ + 1) * Q * (|c m| * sepLogWeight D m) := by
    intro m
    by_cases hm : c m = 0
    · rw [hm, zero_mul, abs_zero, zero_mul, mul_zero]
    rw [abs_mul]
    have h := abs_integral_windowCosSeries_mul_cos_sub_le hc₀ hc2 hgap hQ hm a b
    calc |c m| * |(∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
          (b - a) / 2 * c m| ≤ |c m| * ((1 / c₀ + 1) * sepLogWeight D m * Q) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = (1 / c₀ + 1) * Q * (|c m| * sepLogWeight D m) := by ring
  have hs3 : Summable fun m => (1 / c₀ + 1) * Q * (|c m| * sepLogWeight D m) := hQ.mul_left _
  have hs4 := hs3.of_nonneg_of_le (fun m => abs_nonneg _) hb
  calc |∑' m, c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
        (b - a) / 2 * c m)|
      ≤ ∑' m, |c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
        (b - a) / 2 * c m)| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs4)).trans
          (le_of_eq (tsum_congr fun n => Real.norm_eq_abs _))
    _ ≤ ∑' m, (1 / c₀ + 1) * Q * (|c m| * sepLogWeight D m) := hs4.tsum_le_tsum hb hs3
    _ = (1 / c₀ + 1) * Q ^ 2 := by rw [tsum_mul_left, ← hQdef]; ring


/-! ## Assembly on `[T, 2T]` -/

theorem integral_indicator_Ioo_le {a b : ℝ} (hab : a ≤ b) (z : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ t in a..b, (Ioo (z - η) (z + η)).indicator (1 : ℝ → ℝ) t ≤ 2 * η := by
  rw [intervalIntegral.integral_of_le hab]
  have hon : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (z - η) (z + η)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hint : Integrable ((Ioo (z - η) (z + η)).indicator (1 : ℝ → ℝ)) :=
    hon.integrable_indicator measurableSet_Ioo
  refine (setIntegral_le_integral hint (Eventually.of_forall fun t => ?_)).trans ?_
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) t
  · rw [integral_indicator_one measurableSet_Ioo, Real.volume_real_Ioo]
    rw [max_eq_left (by linarith)]; linarith

theorem neg_part_le (y : ℝ) {l : ℝ} (hl : 0 < l) : max (-y) 0 ≤ y ^ 2 / (2 * l) + l / 2 := by
  have h : |y| ≤ y ^ 2 / (2 * l) + l / 2 := by
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|y| - l), sq_abs y, abs_nonneg y]
  exact max_le (by linarith [neg_abs_le y]) (by positivity)


theorem integrable_indicator_Ioo (z η : ℝ) :
    Integrable ((Ioo (z - η) (z + η)).indicator (1 : ℝ → ℝ)) := by
  have hon : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (z - η) (z + η)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact hon.integrable_indicator measurableSet_Ioo

/-- **Assembly.** On `[T, 2T]`, positivity of `Y` off the `η`-neighbourhoods of the real zeros of
`X` bounds each coefficient. -/
theorem half_mul_abs_le_of_zeroFree {c : ℕ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) {D : ℕ}
    (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n)
    (hgap : ∀ m n, c m ≠ 0 → c n ≠ 0 → m ≠ n →
      c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n|)
    (hQ : Summable fun n => |c n| * sepLogWeight D n) {T l η : ℝ} (hT : 1 ≤ T) (hl : 0 < l)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hpos : ∀ t, T ≤ t → t ≤ 2 * T → (∀ ξ, |ξ - t| < η → phiFourierReal ξ ≠ 0) →
      0 ≤ windowCosSeries c t)
    {m : ℕ} (hm : c m ≠ 0) :
    T / 2 * |c m| ≤ (∑' n, |c n|) / (π * Real.log 2) +
      2 * (1 / (2 * l) * (T / 2 * ∑' n, c n ^ 2 + (1 / c₀ + 1) * (∑' n, |c n| * sepLogWeight D n) ^ 2)
        + l / 2 * (2 * η * ((((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) *
          unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))))) +
      (1 / c₀ + 1) * sepLogWeight D m * ∑' n, |c n| * sepLogWeight D n := by
  have hc : Summable fun n => |c n| :=
    hQ.of_nonneg_of_le (fun n => abs_nonneg _) fun n =>
      le_mul_of_one_le_right (abs_nonneg _) (one_le_sepLogWeight D n)
  set Y := windowCosSeries c with hYdef
  have hYc : Continuous Y := continuous_windowCosSeries hc
  set N : ℕ := ⌈T⌉₊ + 1 with hN
  obtain ⟨hZf, hZc⟩ := realZeroSet_multi (T - 1) N
  set Zf := hZf.toFinset with hZfdef
  set Sf : ℝ → ℝ := fun t => ∑ z ∈ Zf, (Ioo (z - η) (z + η)).indicator (1 : ℝ → ℝ) t with hSf
  have hab : T ≤ 2 * T := by linarith
  have hNT : T + 1 ≤ (N : ℝ) := by
    rw [hN]; push_cast; linarith [Nat.le_ceil T]
  -- the pointwise bound
  have hpt : ∀ t ∈ Icc T (2 * T), max (-Y t) 0 ≤ Y t ^ 2 / (2 * l) + l / 2 * Sf t := by
    rintro t ⟨ht1, ht2⟩
    have hS0 : 0 ≤ Sf t := Finset.sum_nonneg fun z _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) t
    by_cases hz : ∃ z ∈ Zf, t ∈ Ioo (z - η) (z + η)
    · obtain ⟨z, hzZ, hzt⟩ := hz
      have h1 : 1 ≤ Sf t := by
        have := Finset.single_le_sum (f := fun z => (Ioo (z - η) (z + η)).indicator
          (1 : ℝ → ℝ) t) (fun z _ => Set.indicator_nonneg (fun _ _ => zero_le_one) t) hzZ
        simp only [Set.indicator_of_mem hzt, Pi.one_apply] at this
        exact this
      have := neg_part_le (Y t) hl
      nlinarith
    · push Not at hz
      have hfree : ∀ ξ, |ξ - t| < η → phiFourierReal ξ ≠ 0 := by
        intro ξ hξ h0
        rw [abs_lt] at hξ
        have hmem : ξ ∈ realZeroSet (T - 1) (T - 1 + (N + 1)) :=
          ⟨⟨by linarith, by linarith⟩, h0⟩
        exact hz ξ (hZf.mem_toFinset.mpr hmem) ⟨by linarith, by linarith⟩
      have h0 := hpos t ht1 ht2 hfree
      rw [max_eq_right (by linarith)]
      positivity
  have hSint : Integrable Sf := by
    rw [hSf]
    exact integrable_finsetSum _ fun z _ => integrable_indicator_Ioo z η
  have hSi : IntervalIntegrable Sf volume T (2 * T) := hSint.intervalIntegrable
  have hYi : IntervalIntegrable Y volume T (2 * T) := hYc.intervalIntegrable _ _
  have hY2i : IntervalIntegrable (fun t => Y t ^ 2) volume T (2 * T) :=
    (hYc.pow 2).intervalIntegrable _ _
  have hNi : IntervalIntegrable (fun t => max (-Y t) 0) volume T (2 * T) :=
    (hYc.neg.max continuous_const).intervalIntegrable _ _
  -- (a) the coefficient extraction
  have ha := abs_integral_windowCosSeries_mul_cos_sub_le hc₀ hc2 hgap hQ hm T (2 * T)
  rw [show 2 * T - T = T by ring] at ha
  set Q := ∑' n, |c n| * sepLogWeight D n with hQdef
  set I1 := ∫ t in T..2 * T, windowCosSeries c t * Real.cos (2 * π * t * Real.log m) with hI1
  -- (b) `|I1| ≤ ∫ |Y|`
  have hb : |I1| ≤ ∫ t in T..2 * T, |Y t| := by
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans
      (intervalIntegral.integral_mono_on hab ?_ ((hYc.abs).intervalIntegrable _ _) fun t _ => ?_)
    · exact ((hYc.mul (by fun_prop)).abs).intervalIntegrable _ _
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  -- (c) `∫ |Y| = ∫ Y + 2 ∫ Y⁻`
  have hc' : (∫ t in T..2 * T, |Y t|) = (∫ t in T..2 * T, Y t) +
      2 * ∫ t in T..2 * T, max (-Y t) 0 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hYi (hNi.const_mul 2)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rcases le_or_gt 0 (Y t) with h | h
    · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
    · rw [abs_of_neg h, max_eq_left (by linarith)]; ring
  -- (d) the negative part
  have hd : (∫ t in T..2 * T, max (-Y t) 0) ≤
      1 / (2 * l) * (∫ t in T..2 * T, Y t ^ 2) + l / 2 * ∫ t in T..2 * T, Sf t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hY2i.const_mul _) (hSi.const_mul _)]
    refine intervalIntegral.integral_mono_on hab hNi ((hY2i.const_mul _).add (hSi.const_mul _))
      fun t ht => ?_
    have := hpt t ht
    calc max (-Y t) 0 ≤ Y t ^ 2 / (2 * l) + l / 2 * Sf t := this
      _ = 1 / (2 * l) * Y t ^ 2 + l / 2 * Sf t := by ring
  -- (e) the bad-set mass
  have he : (∫ t in T..2 * T, Sf t) ≤ 2 * η * ((((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) *
      unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))) := by
    rw [hSf, intervalIntegral.integral_finsetSum fun z _ =>
      (integrable_indicator_Ioo z η).intervalIntegrable]
    calc ∑ z ∈ Zf, ∫ t in T..2 * T, (Ioo (z - η) (z + η)).indicator (1 : ℝ → ℝ) t
        ≤ ∑ _z ∈ Zf, 2 * η := Finset.sum_le_sum fun z _ => integral_indicator_Ioo_le hab z hη
      _ = 2 * η * Zf.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hZfdef, ← Set.ncard_eq_toFinset_card _ hZf]
          exact hZc
  -- (f), (g)
  have hf := abs_integral_windowCosSeries_le hc2 hc T (2 * T)
  have hg := abs_integral_windowCosSeries_sq_sub_le hc₀ hc2 hgap hQ T (2 * T)
  rw [show 2 * T - T = T by ring] at hg
  have hl2 : 0 < 1 / (2 * l) := by positivity
  have hfY : (∫ t in T..2 * T, Y t) ≤ (∑' n, |c n|) / (π * Real.log 2) := (le_abs_self _).trans hf
  have hgY : (∫ t in T..2 * T, Y t ^ 2) ≤ T / 2 * ∑' n, c n ^ 2 + (1 / c₀ + 1) * Q ^ 2 := by
    have := (le_abs_self _).trans hg; linarith
  have hTc : T / 2 * |c m| ≤ |I1| + (1 / c₀ + 1) * sepLogWeight D m * Q := by
    have h1 : |T / 2 * c m| ≤ |I1| + |I1 - T / 2 * c m| := by
      have := abs_sub_abs_le_abs_sub (T / 2 * c m) I1
      rw [abs_sub_comm] at this; linarith
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < T / 2)] at h1
    linarith
  have hmono1 := mul_le_mul_of_nonneg_left hgY hl2.le
  have hmono2 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ l / 2)
  linarith


/-! ## Counting a log-separated support -/

/-- A `δ`-separated finite set in a unit interval has at most `1 + 1/δ` points. -/
theorem card_mul_le_of_separated {F : Finset ℝ} {a δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ x ∈ F, x ∈ Icc a (a + 1)) (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x - y|) :
    (F.card : ℝ) * δ ≤ 1 + δ := by
  have hdisj : (↑F : Set ℝ).PairwiseDisjoint fun x => Ioo x (x + δ) := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_iff]
    rintro t ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have := hsep x hx y hy hxy
    have h5 : |x - y| < δ := by rw [abs_lt]; constructor <;> linarith
    exact absurd this (not_le.mpr h5)
  have hmeas := measure_biUnion_finset (μ := volume) hdisj (fun x _ => measurableSet_Ioo)
  have hsub : (⋃ x ∈ F, Ioo x (x + δ)) ⊆ Ioo (a - 0) (a + 1 + δ) := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, h1, h2⟩ := ht
    obtain ⟨h3, h4⟩ := hF x hx
    constructor <;> linarith
  have hle := measure_mono (μ := volume) hsub
  rw [hmeas, Real.volume_Ioo] at hle
  simp only [Real.volume_Ioo, add_sub_cancel_left, Finset.sum_const, nsmul_eq_mul] at hle
  rw [show a + 1 + δ - (a - 0) = 1 + δ by ring] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  exact hle


/-- The fibre count of a log-separated support. -/
theorem card_fibre_le {v : ℕ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) {D : ℕ}
    (hgap : ∀ m n, v m ≠ 0 → v n ≠ 0 → m ≠ n →
      c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n|)
    (hv1 : ∀ n, v n ≠ 0 → 1 ≤ n) (u : Finset ℕ) (j : ℕ) :
    ((u.filter fun n => v n ≠ 0 ∧ ⌊Real.log n⌋₊ = j).card : ℝ) ≤ 1 + (3 + 2 * j) ^ D / c₀ := by
  classical
  set G := u.filter fun n => v n ≠ 0 ∧ ⌊Real.log n⌋₊ = j with hG
  set δ := c₀ * ((3 + 2 * (j : ℝ)) ^ D)⁻¹ with hδ
  have hδ0 : 0 < δ := by positivity
  have hmem : ∀ n ∈ G, v n ≠ 0 ∧ ⌊Real.log n⌋₊ = j := fun n hn => (Finset.mem_filter.mp hn).2
  have hlog : ∀ n ∈ G, Real.log n ∈ Icc (j : ℝ) (j + 1) := by
    intro n hn
    obtain ⟨hv, hj⟩ := hmem n hn
    have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    constructor
    · have := Nat.floor_le h0; rw [hj] at this; exact this
    · have := Nat.lt_floor_add_one (Real.log n); rw [hj] at this; exact this.le
  have hinj : Set.InjOn (fun n : ℕ => Real.log n) ↑G := by
    intro m hm n hn h
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hv1 m (hmem m hm).1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hv1 n (hmem n hn).1
    have := Real.log_injOn_pos (by simp only [Set.mem_Ioi]; linarith)
      (by simp only [Set.mem_Ioi]; linarith) h
    exact_mod_cast this
  set F := G.image fun n : ℕ => Real.log n with hF
  have hcard : F.card = G.card := Finset.card_image_of_injOn hinj
  have hFsub : ∀ x ∈ F, x ∈ Icc (j : ℝ) (j + 1) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact hlog n hn
  have hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    have hmn : m ≠ n := fun h => hxy (by rw [h])
    have hg := hgap m n (hmem m hm).1 (hmem n hn).1 hmn
    refine le_trans ?_ hg
    rw [hδ]
    refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hc₀.le
    refine pow_le_pow_left₀ (by positivity) ?_ D
    have := (hlog m hm).2; have := (hlog n hn).2
    linarith
  have hpack := card_mul_le_of_separated hδ0 hFsub hsep
  rw [hcard] at hpack
  have h1 : (G.card : ℝ) ≤ 1 + 1 / δ := by
    rw [one_add_div hδ0.ne', le_div_iff₀ hδ0]; linarith
  have h2 : 1 / δ = (3 + 2 * (j : ℝ)) ^ D / c₀ := by
    rw [hδ]; field_simp
  rw [h2] at h1
  exact h1


theorem summable_inv_one_add_nat_sq : Summable fun j : ℕ => (((1 : ℝ) + j) ^ 2)⁻¹ := by
  refine (summable_four_div_succ_sq.div_const 4).congr fun j => ?_
  field_simp; ring

/-- **Step 0.** A log-separated support is summable against `(1 + log n)^{−k}`, `k ≥ D + 2`. -/
theorem summable_support_inv_pow {v : ℕ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) {D : ℕ}
    (hgap : ∀ m n, v m ≠ 0 → v n ≠ 0 → m ≠ n →
      c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n|)
    (hv1 : ∀ n, v n ≠ 0 → 1 ≤ n) {k : ℕ} (hk : D + 2 ≤ k) :
    Summable fun n : ℕ => if v n ≠ 0 then ((1 + Real.log n) ^ k)⁻¹ else 0 := by
  classical
  set b : ℕ → ℝ := fun j => (1 + (3 + 2 * (j : ℝ)) ^ D / c₀) * (((1 : ℝ) + j) ^ k)⁻¹ with hb
  have hb0 : ∀ j, 0 ≤ b j := fun j => by positivity
  have hbs : Summable b := by
    refine (summable_inv_one_add_nat_sq.mul_left (1 + 3 ^ D / c₀)).of_nonneg_of_le hb0 fun j => ?_
    have hj1 : (1 : ℝ) ≤ 1 + j := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hp1 : (1 : ℝ) ≤ (1 + j) ^ D := one_le_pow₀ hj1
    have hp3 : (3 + 2 * (j : ℝ)) ^ D ≤ 3 ^ D * (1 + j) ^ D := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) D
    have hk' : ((1 : ℝ) + j) ^ D * ((1 : ℝ) + j) ^ 2 ≤ ((1 : ℝ) + j) ^ k := by
      rw [← pow_add]; exact pow_le_pow_right₀ hj1 hk
    have e1 : 1 + (3 + 2 * (j : ℝ)) ^ D / c₀ ≤ (1 + 3 ^ D / c₀) * (1 + j) ^ D := by
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      exact add_le_add hp1 (div_le_div_of_nonneg_right hp3 hc₀.le)
    calc b j ≤ (1 + 3 ^ D / c₀) * (1 + j) ^ D * (((1 : ℝ) + j) ^ k)⁻¹ :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ ≤ (1 + 3 ^ D / c₀) * (((1 : ℝ) + j) ^ 2)⁻¹ := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div,
            le_div_iff₀ (by positivity)]
          linarith
  refine summable_of_sum_le (c := ∑' j, b j) (fun n => by positivity) fun u => ?_
  set u' := u.filter fun n => v n ≠ 0 with hu'
  have e1 : ∑ n ∈ u, (if v n ≠ 0 then ((1 + Real.log n) ^ k)⁻¹ else 0) =
      ∑ n ∈ u', ((1 + Real.log n) ^ k)⁻¹ := by
    rw [hu', Finset.sum_filter]
  rw [e1]
  set g : ℕ → ℕ := fun n => ⌊Real.log n⌋₊ with hg
  rw [← Finset.sum_fiberwise_of_maps_to (t := u'.image g) (g := g)
    (fun n hn => Finset.mem_image_of_mem g hn)]
  calc ∑ j ∈ u'.image g, ∑ n ∈ u' with g n = j, ((1 + Real.log n) ^ k)⁻¹
      ≤ ∑ j ∈ u'.image g, b j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hfil : (u'.filter fun n => g n = j) = u.filter fun n => v n ≠ 0 ∧ ⌊Real.log n⌋₊ = j := by
          rw [hu', Finset.filter_filter]
        have hcard := card_fibre_le hc₀ hgap hv1 u j
        rw [← hfil] at hcard
        calc ∑ n ∈ u' with g n = j, ((1 + Real.log n) ^ k)⁻¹
            ≤ ∑ n ∈ u' with g n = j, (((1 : ℝ) + j) ^ k)⁻¹ := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hj : g n = j := (Finset.mem_filter.mp hn).2
              have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
              have hfl : (j : ℝ) ≤ Real.log n := by
                have := Nat.floor_le h0; rw [← hj]; exact this
              exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) k)
          _ = ((u'.filter fun n => g n = j).card : ℝ) * (((1 : ℝ) + j) ^ k)⁻¹ := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ b j := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ∑' j, b j := hbs.sum_le_tsum _ fun j _ => hb0 j

/-! ## The rigidity theorem -/

theorem pow_mul_one_add_pow_le {η x : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hx : 0 ≤ x) (J : ℕ) :
    η ^ J * (1 + x) ^ J ≤ (1 + η * x) ^ J := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) J

theorem sepLogWeight_le (D n : ℕ) : sepLogWeight D n ≤ 2 ^ D * (1 + Real.log n) ^ D := by
  unfold sepLogWeight
  rw [← mul_pow]
  have := Real.log_natCast_nonneg n
  exact pow_le_pow_left₀ (by linarith) (by linarith) D

theorem unitZeroBound_five_mul_le {T : ℝ} (hT : 1 ≤ T) :
    unitZeroBound (5 * T) ≤
      8 * (1 + π ^ 2) * (|xiLineTwoLogDerivConstant| + Real.log 50 + Real.log T) := by
  unfold unitZeroBound
  have hπ := Real.pi_lt_d2
  have hT0 : 0 < T := by linarith
  have h1 : |2 * π * (5 * T + 1 / 2)| + 4 ≤ 50 * T := by
    rw [abs_of_pos (by positivity)]; nlinarith [Real.pi_pos]
  have h2 : Real.log (|2 * π * (5 * T + 1 / 2)| + 4) ≤ Real.log 50 + Real.log T := by
    rw [← Real.log_mul (by norm_num) hT0.ne']
    exact Real.log_le_log (by positivity) h1
  have h3 := le_abs_self xiLineTwoLogDerivConstant
  have h4 : xiLineTwoLogDerivConstant + Real.log (|2 * π * (5 * T + 1 / 2)| + 4) ≤
      |xiLineTwoLogDerivConstant| + Real.log 50 + Real.log T := by linarith
  exact mul_le_mul_of_nonneg_left h4 (by positivity)



theorem div_four_mul_add_one_div_le {X ε : ℝ} (hX : 0 ≤ X) (hε : 0 < ε) :
    X / (4 * (X + 1) / ε) ≤ ε / 4 := by
  rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The final real arithmetic of the rigidity argument. -/
theorem le_of_assembly_bounds {x T η ε l CR wm K Q A1 S2 Zc B2V CX a0 P L2 : ℝ}
    (hT : 1 ≤ T) (hl : 0 < l) (hη : 0 < η) (hCR : 0 < CR) (hwm : 0 ≤ wm)
    (hL2 : 0 < L2)
    (hass : T / 2 * x ≤ A1 / L2 +
      2 * (1 / (2 * l) * (T / 2 * S2 + CR * Q ^ 2) + l / 2 * (2 * η * Zc)) + CR * wm * Q)
    (hA1 : A1 ≤ Q) (hQ1 : Q ≤ K * (T * η)) (hQ2 : Q ^ 2 ≤ K ^ 2 * (T * η))
    (hS2 : S2 ≤ B2V) (hB2V : B2V / l ≤ ε / 4)
    (hZc : Zc ≤ 4 * T * (CX * (a0 * 1 - P * Real.log η)))
    (hη3 : 16 * l * (CX * (a0 * η - P * (η * Real.log η))) ≤ ε / 4)
    (hη4 : η * (2 * K / L2 + 2 * CR * K ^ 2 / l + 2 * CR * wm * K) ≤ ε / 2) :
    x ≤ ε := by
  have hT2 : 0 < T / 2 := by linarith
  have e1 : A1 / L2 ≤ T / 2 * (η * (2 * K / L2)) := by
    rw [div_le_iff₀ hL2]
    have : T / 2 * (η * (2 * K / L2)) * L2 = K * (T * η) := by field_simp
    rw [this]; linarith
  have e2 : 2 * (1 / (2 * l) * (T / 2 * S2)) ≤ T / 2 * (ε / 4) := by
    have : 2 * (1 / (2 * l) * (T / 2 * S2)) = T / 2 * (S2 / l) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hS2 hl.le).trans hB2V) hT2.le
  have e3 : 2 * (1 / (2 * l) * (CR * Q ^ 2)) ≤ T / 2 * (η * (2 * CR * K ^ 2 / l)) := by
    have h1 : T / 2 * (η * (2 * CR * K ^ 2 / l)) = CR * (K ^ 2 * (T * η)) / l := by field_simp
    have h2 : 2 * (1 / (2 * l) * (CR * Q ^ 2)) = CR * Q ^ 2 / l := by field_simp
    rw [h1, h2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ2 hCR.le) hl.le
  have e4 : 2 * (l / 2 * (2 * η * Zc)) ≤ T / 2 * (16 * l * (CX * (a0 * η - P * (η * Real.log η)))) := by
    have h := mul_le_mul_of_nonneg_left hZc (by positivity : (0 : ℝ) ≤ 2 * l * η)
    have h1 : T / 2 * (16 * l * (CX * (a0 * η - P * (η * Real.log η)))) =
        2 * l * η * (4 * T * (CX * (a0 * 1 - P * Real.log η))) := by ring
    rw [h1]
    linarith
  have e5 : CR * wm * Q ≤ T / 2 * (η * (2 * CR * wm * K)) := by
    have : T / 2 * (η * (2 * CR * wm * K)) = CR * wm * (K * (T * η)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hQ1 (by positivity)
  have hsum := mul_le_mul_of_nonneg_left hη4 hT2.le
  have hsum2 := mul_le_mul_of_nonneg_left hη3 hT2.le
  have eH : T / 2 * (η * (2 * K / L2 + 2 * CR * K ^ 2 / l + 2 * CR * wm * K)) =
      T / 2 * (η * (2 * K / L2)) + T / 2 * (η * (2 * CR * K ^ 2 / l)) +
        T / 2 * (η * (2 * CR * wm * K)) := by ring
  have ehass : T / 2 * x ≤ A1 / L2 + 2 * (1 / (2 * l) * (T / 2 * S2)) +
      2 * (1 / (2 * l) * (CR * Q ^ 2)) + 2 * (l / 2 * (2 * η * Zc)) + CR * wm * Q := by
    have : 2 * (1 / (2 * l) * (T / 2 * S2 + CR * Q ^ 2) + l / 2 * (2 * η * Zc)) =
        2 * (1 / (2 * l) * (T / 2 * S2)) + 2 * (1 / (2 * l) * (CR * Q ^ 2)) +
          2 * (l / 2 * (2 * η * Zc)) := by ring
    linarith
  have htot : T / 2 * x ≤ T / 2 * ε := by linarith
  exact le_of_mul_le_mul_left htot hT2

/-- **Zero-free-window rigidity.** A full-cone Weil-positive system whose normalized deviation
from `Λ` is square-summable and supported on a set with polynomially separated logarithms is
`Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_sq_summable_separated {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (hsq : Summable fun n => normDeficit lam n ^ 2)
    {c₀ : ℝ} (hc₀ : 0 < c₀) {D : ℕ}
    (hgap : ∀ m n, normDeficit lam m ≠ 0 → normDeficit lam n ≠ 0 → m ≠ n →
      c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n|) :
    ∀ m, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  set v := normDeficit lam with hvdef
  have hv2 : ∀ n, v n ≠ 0 → 2 ≤ n := by
    intro n hn; by_contra h; exact hn (by simp only [hvdef, normDeficit, if_neg h])
  have hv1 : ∀ n, v n ≠ 0 → 1 ≤ n := fun n hn => le_trans (by norm_num) (hv2 n hn)
  set V := ∑' n, v n ^ 2 with hV
  have hV0 : 0 ≤ V := tsum_nonneg fun _ => sq_nonneg _
  have hA : ∀ n, |v n| ≤ V + 1 := by
    intro n
    have h := hsq.le_tsum n (fun _ _ => sq_nonneg _)
    rcases le_or_gt |v n| 1 with h1 | h1
    · linarith
    · have : |v n| ≤ v n ^ 2 := by rw [← sq_abs]; nlinarith
      linarith
  set k := D + 2 with hk
  have hZs := summable_support_inv_pow hc₀ hgap hv1 (k := k) le_rfl
  have hZ : Summable fun n : ℕ => |v n| * ((1 + |Real.log n|) ^ k)⁻¹ := by
    refine (hZs.mul_left (V + 1)).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    by_cases hn : v n = 0
    · rw [hn, abs_zero, zero_mul]; positivity
    rw [if_pos hn, abs_of_nonneg (Real.log_natCast_nonneg n)]
    exact mul_le_mul_of_nonneg_right (hA n) (by positivity)
  -- constants
  have hB0 := bumpCos_zero_pos
  set B0 := bumpCos 0 with hB0def
  set J := 2 * D + 2 with hJ
  obtain ⟨KJ, hKJ0, hKJ⟩ := exists_abs_bumpCos_le J
  set Zk := ∑' n : ℕ, (if v n ≠ 0 then ((1 + Real.log n) ^ k)⁻¹ else 0) with hZk
  have hZk0 : 0 ≤ Zk := tsum_nonneg fun n => by split_ifs <;> positivity
  set K := (V + 1) * KJ * 2 ^ D * Zk with hKdef
  have hK0 : 0 ≤ K := by positivity
  set cf : ℝ → ℕ → ℝ := fun η n => v n * bumpCos (η * Real.log n) with hcf
  have hcfb : ∀ η, 0 < η → η ≤ 1 → ∀ n, |cf η n| * sepLogWeight D n ≤
      (V + 1) * KJ * 2 ^ D * (η ^ J)⁻¹ * (if v n ≠ 0 then ((1 + Real.log n) ^ k)⁻¹ else 0) := by
    intro η hη0 hη1 n
    by_cases hn : v n = 0
    · simp only [hcf, hn, zero_mul, abs_zero, ne_eq, not_true_eq_false, if_false, mul_zero, le_refl]
    rw [if_pos hn]
    have hl := Real.log_natCast_nonneg n
    have h2 := hKJ (η * Real.log n)
    rw [abs_of_nonneg (by positivity : 0 ≤ η * Real.log n)] at h2
    have h3 := pow_mul_one_add_pow_le hη0 hη1 hl J
    have h4 := sepLogWeight_le D n
    have h5 : ((1 + η * Real.log n) ^ J)⁻¹ ≤ (η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (by positivity) h3
    have h6 : (1 + Real.log n) ^ D * ((1 + Real.log n) ^ J)⁻¹ = ((1 + Real.log n) ^ k)⁻¹ := by
      rw [hJ, hk, show 2 * D + 2 = D + (D + 2) by ring, pow_add]
      have : (0 : ℝ) < (1 + Real.log n) ^ D := by positivity
      field_simp
    simp only [hcf]
    rw [abs_mul]
    have hb : |bumpCos (η * Real.log n)| ≤ KJ * ((η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹) :=
      h2.trans (mul_le_mul_of_nonneg_left h5 hKJ0)
    calc |v n| * |bumpCos (η * Real.log n)| * sepLogWeight D n
        ≤ (V + 1) * (KJ * ((η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹)) *
            (2 ^ D * (1 + Real.log n) ^ D) := by
          have hw0 : 0 ≤ sepLogWeight D n := le_trans zero_le_one (one_le_sepLogWeight D n)
          exact mul_le_mul (mul_le_mul (hA n) hb (abs_nonneg _) (by linarith)) h4 hw0
            (by positivity)
      _ = (V + 1) * KJ * 2 ^ D * (η ^ J)⁻¹ *
            ((1 + Real.log n) ^ D * ((1 + Real.log n) ^ J)⁻¹) := by ring
      _ = _ := by rw [h6]
  have hQs : ∀ η, 0 < η → η ≤ 1 → Summable fun n => |cf η n| * sepLogWeight D n :=
    fun η h0 h1 => (hZs.mul_left _).of_nonneg_of_le (fun n => by
      have := one_le_sepLogWeight D n; positivity) (hcfb η h0 h1)
  have hQb : ∀ η, 0 < η → η ≤ 1 → ∑' n, |cf η n| * sepLogWeight D n ≤ K * (η ^ J)⁻¹ := by
    intro η h0 h1
    calc ∑' n, |cf η n| * sepLogWeight D n
        ≤ ∑' n, (V + 1) * KJ * 2 ^ D * (η ^ J)⁻¹ *
            (if v n ≠ 0 then ((1 + Real.log n) ^ k)⁻¹ else 0) :=
          (hQs η h0 h1).tsum_le_tsum (hcfb η h0 h1) (hZs.mul_left _)
      _ = (V + 1) * KJ * 2 ^ D * (η ^ J)⁻¹ * Zk := tsum_mul_left
      _ = K * (η ^ J)⁻¹ := by rw [hKdef]; ring
  have hcs : ∀ η, ∑' n, cf η n ^ 2 ≤ B0 ^ 2 * V := by
    intro η
    have hpt : ∀ n, cf η n ^ 2 ≤ B0 ^ 2 * v n ^ 2 := by
      intro n
      simp only [hcf]
      rw [mul_pow, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [← sq_abs, ← sq_abs B0]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_bumpCos_le _).trans (le_abs_self _)) 2
    calc ∑' n, cf η n ^ 2 ≤ ∑' n, B0 ^ 2 * v n ^ 2 :=
          ((hsq.mul_left _).of_nonneg_of_le (fun _ => sq_nonneg _) hpt).tsum_le_tsum hpt
            (hsq.mul_left _)
      _ = B0 ^ 2 * V := tsum_mul_left
  have hA1 : ∀ η, 0 < η → η ≤ 1 → ∑' n, |cf η n| ≤ ∑' n, |cf η n| * sepLogWeight D n := by
    intro η h0 h1
    exact ((hQs η h0 h1).of_nonneg_of_le (fun _ => abs_nonneg _) fun n =>
      le_mul_of_one_le_right (abs_nonneg _) (one_le_sepLogWeight D n)).tsum_le_tsum
      (fun n => le_mul_of_one_le_right (abs_nonneg _) (one_le_sepLogWeight D n)) (hQs η h0 h1)
  have hU0 : ∀ a, 0 ≤ unitZeroBound a := fun a =>
    le_trans (Nat.cast_nonneg _) (realZeroSet_unit a).2
  have hmain : ∀ m, v m = 0 := by
    intro m
    by_contra hm
    have key : ∀ ε > 0, |v m| * (B0 / 2) ≤ ε := by
      intro ε hε
      set l := 4 * (B0 ^ 2 * V + 1) / ε with hl
      have hl0 : 0 < l := by positivity
      set CR := 1 / c₀ + 1 with hCR
      have hCR0 : 0 < CR := by positivity
      set wm := sepLogWeight D m with hwm
      have hwm0 : 0 ≤ wm := le_trans zero_le_one (one_le_sepLogWeight D m)
      set CX := 8 * (1 + π ^ 2) with hCX
      set a0 := |xiLineTwoLogDerivConstant| + Real.log 50 with ha0
      set p : ℕ := 2 * J + 1 with hp
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      set H := 2 * K / (π * Real.log 2) + 2 * CR * K ^ 2 / l + 2 * CR * wm * K with hH
      have hH0 : 0 ≤ H := by positivity
      have hev1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η ≤ 1 := by
        filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
        exact ⟨hη.1, hη.2⟩
      have hev2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), B0 / 2 < bumpCos (η * Real.log m) := by
        have ht : Tendsto (fun η : ℝ => bumpCos (η * Real.log m)) (𝓝 0) (𝓝 B0) := by
          have hc : Continuous fun η : ℝ => bumpCos (η * Real.log m) :=
            continuous_bumpCos.comp (continuous_id.mul continuous_const)
          have := hc.tendsto 0
          simpa [hB0def] using this
        exact nhdsWithin_le_nhds (ht.eventually_const_lt (by linarith))
      have hev3 : ∀ᶠ η in 𝓝[>] (0 : ℝ),
          16 * l * (CX * (a0 * η - (p : ℝ) * (η * Real.log η))) ≤ ε / 4 := by
        have ht : Tendsto (fun η : ℝ => 16 * l * (CX * (a0 * η - (p : ℝ) * (η * Real.log η))))
            (𝓝 0) (𝓝 0) := by
          have h1 : Tendsto (fun η : ℝ => η * Real.log η) (𝓝 0) (𝓝 0) := by
            have := Real.continuous_mul_log.tendsto 0; simpa using this
          have := (((tendsto_id.const_mul a0).sub (h1.const_mul (p : ℝ))).const_mul CX).const_mul
            (16 * l)
          simpa using this
        exact nhdsWithin_le_nhds (ht.eventually_le_const (by positivity))
      have hev4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η * H ≤ ε / 2 := by
        have ht : Tendsto (fun η : ℝ => η * H) (𝓝 0) (𝓝 0) := by
          have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const H; simpa using this
        exact nhdsWithin_le_nhds (ht.eventually_le_const (by positivity))
      obtain ⟨η, hηall⟩ := (((hev1.and hev2).and hev3).and hev4).exists
      obtain ⟨⟨⟨⟨hη0, hη1⟩, hη2⟩, hη3⟩, hη4⟩ := hηall
      set y := η⁻¹ with hy
      have hy1 : 1 ≤ y := (one_le_inv₀ hη0).mpr hη1
      set T := y ^ p with hT
      have hT1 : 1 ≤ T := one_le_pow₀ hy1
      have hpos : ∀ t, T ≤ t → t ≤ 2 * T → (∀ ξ, |ξ - t| < η → phiFourierReal ξ ≠ 0) →
          0 ≤ windowCosSeries (cf η) t := by
        intro t _ _ hfree
        have := localized_deviation_nonneg hW hA hZ hη0 (ξ₀ := t) hfree
        simpa [windowCosSeries, hcf] using this
      have hbm : 0 < bumpCos (η * Real.log m) := by linarith
      have hcm : cf η m ≠ 0 := by simp only [hcf]; exact mul_ne_zero hm hbm.ne'
      have hc2' : ∀ n, cf η n ≠ 0 → 2 ≤ n := fun n hn => hv2 n (left_ne_zero_of_mul hn)
      have hgap' : ∀ a b, cf η a ≠ 0 → cf η b ≠ 0 → a ≠ b →
          c₀ * ((1 + Real.log a + Real.log b) ^ D)⁻¹ ≤ |Real.log a - Real.log b| :=
        fun a b ha hb hab => hgap a b (left_ne_zero_of_mul ha) (left_ne_zero_of_mul hb) hab
      have hass := half_mul_abs_le_of_zeroFree hc₀ hc2' hgap' (hQs η hη0 hη1) hT1 hl0 hη0 hη1
        hpos hcm
      -- the size of `Q`
      set Q := ∑' n, |cf η n| * sepLogWeight D n with hQdef
      have hQ0 : 0 ≤ Q := tsum_nonneg fun n => by
        have := one_le_sepLogWeight D n; positivity
      have hyJ : (η ^ J)⁻¹ = y ^ J := by rw [hy, inv_pow]
      have hTη : T * η = y ^ (2 * J) := by
        rw [hT, hp, pow_succ, mul_assoc, hy, inv_mul_cancel₀ hη0.ne', mul_one]
      have hQ1 : Q ≤ K * (T * η) := by
        rw [hTη]
        have h := hQb η hη0 hη1
        rw [hyJ] at h
        exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 (by omega)) hK0)
      have hQ2 : Q ^ 2 ≤ K ^ 2 * (T * η) := by
        rw [hTη]
        have h := (hQb η hη0 hη1)
        rw [hyJ] at h
        calc Q ^ 2 ≤ (K * y ^ J) ^ 2 := pow_le_pow_left₀ hQ0 h 2
          _ = K ^ 2 * y ^ (2 * J) := by rw [mul_pow, ← pow_mul, mul_comm J 2]
      have hS2 := hcs η
      -- the zero count
      set N : ℕ := ⌈T⌉₊ + 1 with hN
      have hceil : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      have hN1 : ((N : ℕ) : ℝ) + 1 ≤ 4 * T := by rw [hN]; push_cast; linarith
      have hU1 : unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1)) ≤ unitZeroBound (5 * T) := by
        refine unitZeroBound_le_of_le (by linarith) ?_
        rw [abs_of_nonneg (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)]; positivity)]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)]
        push_cast; linarith
      have hU5 := unitZeroBound_five_mul_le hT1
      have hlogT : Real.log T = -((p : ℝ) * Real.log η) := by
        rw [hT, Real.log_pow, hy, Real.log_inv]; ring
      have hZc : (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
          ≤ 4 * T * (CX * (a0 * 1 - (p : ℝ) * Real.log η)) := by
        have hUpos := hU0 (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
        calc (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
            ≤ 4 * T * unitZeroBound (5 * T) :=
              mul_le_mul hN1 hU1 hUpos (by linarith)
          _ ≤ 4 * T * (CX * (a0 + Real.log T)) := mul_le_mul_of_nonneg_left hU5 (by linarith)
          _ = 4 * T * (CX * (a0 * 1 - (p : ℝ) * Real.log η)) := by rw [hlogT]; ring
      -- final arithmetic
      have hB2V : B0 ^ 2 * V / l ≤ ε / 4 := by
        rw [hl]; exact div_four_mul_add_one_div_le (by positivity) hε
      have hcfm : |cf η m| ≤ ε :=
        le_of_assembly_bounds (x := |cf η m|) (T := T) (η := η) (ε := ε) (l := l) (CR := CR)
          (wm := wm) (K := K) (Q := Q) (A1 := ∑' n, |cf η n|) (S2 := ∑' n, cf η n ^ 2)
          (Zc := (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1)))
          (B2V := B0 ^ 2 * V) (CX := CX) (a0 := a0) (P := (p : ℝ)) (L2 := π * Real.log 2)
          hT1 hl0 hη0 hCR0 hwm0 (by positivity) hass (hA1 η hη0 hη1) hQ1 hQ2 hS2 hB2V hZc hη3 hη4
      calc |v m| * (B0 / 2) ≤ |v m| * |bumpCos (η * Real.log m)| :=
            mul_le_mul_of_nonneg_left (by rw [abs_of_pos hbm]; linarith) (abs_nonneg _)
        _ = |cf η m| := by simp only [hcf, abs_mul]
        _ ≤ ε := hcfm
    have h0 : |v m| * (B0 / 2) ≤ 0 := le_of_forall_pos_le_add fun ε hε => by
      have := key ε hε; linarith
    have : |v m| * (B0 / 2) = 0 := le_antisymm h0 (by positivity)
    rcases mul_eq_zero.mp this with h | h
    · exact hm (abs_eq_zero.mp h)
    · linarith
  intro m hm2
  have hv := hmain m
  simp only [hvdef, normDeficit, if_pos hm2] at hv
  have hsq0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))).ne'
  rw [div_eq_zero_iff, sub_eq_zero] at hv
  rcases hv with hv | hv
  · exact hv.symm
  · exact absurd hv hsq0


/-- **RH as a square-summable separated deformation problem.** -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_sq_summable_separated :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      Summable (fun n => normDeficit lam n ^ 2) ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ D : ℕ,
        ∀ m n, normDeficit lam m ≠ 0 → normDeficit lam n ≠ 0 → m ≠ n →
          c₀ * ((1 + Real.log m + Real.log n) ^ D)⁻¹ ≤ |Real.log m - Real.log n| := by
  constructor
  · intro hRH
    have h0 : ∀ n, normDeficit (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n = 0 := by
      intro n; unfold normDeficit; split_ifs <;> simp
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, ?_, 1, one_pos, 0,
      fun m n hm => absurd (h0 m) hm⟩
    simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; exact summable_zero
  · rintro ⟨lam, hW, hsq, c₀, hc₀, D, hgap⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_sq_summable_separated hW hsq hc₀ hgap
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

end

end RHTower
