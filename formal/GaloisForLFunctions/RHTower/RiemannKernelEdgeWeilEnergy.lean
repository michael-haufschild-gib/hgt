import GaloisForLFunctions.RHTower.RiemannKernelEdgeProfile
import GaloisForLFunctions.RHTower.WeilWorkPBAPPacketEnergy

/-!
# The Weil energy of the edge tail of Riemann's kernel

For the tail `T = Φ(χ_R − χ_L)` of the truncation of Riemann's kernel at `L` (edge width `1/Y`,
`Y = 2πe^{2L}`), the explicit formula splits the zero side `W(T, T)` into the pole term (`≥ 0`,
since `T ≥ 0`), the archimedean term and the prime term.

* **Archimedean term.** `‖T̂(r)‖ ≤ ∫T`, so the band `|r| ≤ M` carries at most `2M(∫T)²` of the mass
  `∫‖T̂‖² = 2π∫T²`. Narrowness `(∫T)² ≤ (C/Y)∫T²` allows `M ≍ Y`, and
  `Re Γ'/Γ(¼ + ir/2) − log π ≥ log(1 + |r|/4) − 10` gives `arch ≥ ½(log(1 + M/4) − 20)∫T²`.
* **Prime term.** The lag function `k(x) = ∫T(u)T(u − x)du` is at most
  `2Ae^{−cx}∫T + A²e^{−c(x − 2L)}max(0, x − 2L)`.
  Using `z e^{−cz} ≤ (2/(ec))e^{−cz/2}`, the prime sum is controlled by decreasing sums
  `Σ_{n ≥ n₀} log n · n^{−s} ≤ log n₀·n₀^{−s} + n₀^{1−s}(log n₀/(s − 1) + 1/(s − 1)²)`.
  The prime term is `O((2L + 1)(e^{−L} + e^{L}/Y))·E(L)²/Y = O(L e^{−L})∫T²`.

Hence `Re W(T, T) ≥ (L − C)∫T² > 0` for all large `L`, uniformly in the outer radius `R ≥ L + 2`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## Decreasing logarithmic sums -/

/-- `g(x) = log x · e^{−s log x}`. -/
def logPowDecay (s x : ℝ) : ℝ := Real.log x * Real.exp (-s * Real.log x)

/-- Its primitive `H(x) = −e^{(1−s) log x}(log x/(s − 1) + 1/(s − 1)²)`. -/
def logPowPrimitive (s x : ℝ) : ℝ :=
  -(Real.exp ((1 - s) * Real.log x) * (Real.log x / (s - 1) + 1 / (s - 1) ^ 2))

theorem hasDerivAt_logPowPrimitive {s x : ℝ} (hs : 1 < s) (hx : 0 < x) :
    HasDerivAt (logPowPrimitive s) (logPowDecay s x) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have he : HasDerivAt (fun y => Real.exp ((1 - s) * Real.log y))
      (Real.exp ((1 - s) * Real.log x) * ((1 - s) * x⁻¹)) x :=
    (hlog.const_mul (1 - s)).exp
  have hq : HasDerivAt (fun y => Real.log y / (s - 1) + 1 / (s - 1) ^ 2) (x⁻¹ / (s - 1)) x := by
    simpa using (hlog.div_const (s - 1)).add_const (1 / (s - 1) ^ 2)
  have h : HasDerivAt (logPowPrimitive s)
      (-(Real.exp ((1 - s) * Real.log x) * ((1 - s) * x⁻¹) *
          (Real.log x / (s - 1) + 1 / (s - 1) ^ 2) +
        Real.exp ((1 - s) * Real.log x) * (x⁻¹ / (s - 1)))) x := (he.mul hq).neg
  refine h.congr_deriv ?_
  unfold logPowDecay
  have hs1 : s - 1 ≠ 0 := by linarith
  have hexp : Real.exp (-s * Real.log x) = Real.exp ((1 - s) * Real.log x) * x⁻¹ := by
    rw [show (1 - s) * Real.log x = -s * Real.log x + Real.log x by ring, Real.exp_add,
      Real.exp_log hx, mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  rw [hexp]
  field_simp
  ring

theorem logPowPrimitive_nonpos {s x : ℝ} (hs : 1 < s) (hx : 1 ≤ x) : logPowPrimitive s x ≤ 0 := by
  unfold logPowPrimitive
  have : 0 ≤ Real.log x := Real.log_nonneg hx
  have : 0 < s - 1 := by linarith
  have : 0 ≤ Real.log x / (s - 1) + 1 / (s - 1) ^ 2 := by positivity
  have := Real.exp_pos ((1 - s) * Real.log x)
  nlinarith

theorem continuousOn_logPowDecay (s : ℝ) : ContinuousOn (logPowDecay s) (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
  exact ((Real.continuousAt_log hx0).mul
    ((Real.continuous_exp.continuousAt).comp ((continuousAt_const.mul
      (Real.continuousAt_log hx0))))).continuousWithinAt

theorem antitoneOn_logPowDecay {s : ℝ} (hs : 2 ≤ s) {a : ℝ} (ha : 2 ≤ a) :
    AntitoneOn (logPowDecay s) (Ici a) := by
  have hcont : ContinuousOn (logPowDecay s) (Ici a) :=
    (continuousOn_logPowDecay s).mono fun x hx => mem_Ioi.mpr (by linarith [mem_Ici.mp hx])
  refine antitoneOn_of_deriv_nonpos (convex_Ici a) hcont ?_ ?_
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
    have h1 : DifferentiableAt ℝ Real.log x := Real.differentiableAt_log hx0.ne'
    exact (h1.mul ((h1.const_mul (-s)).exp)).differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx2 : 2 < x := by have := mem_Ioi.mp hx; linarith
    have hx0 : 0 < x := by linarith
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
    have hd : HasDerivAt (logPowDecay s)
        (x⁻¹ * Real.exp (-s * Real.log x) +
          Real.log x * (Real.exp (-s * Real.log x) * (-s * x⁻¹))) x :=
      hlog.mul ((hlog.const_mul (-s)).exp)
    rw [hd.deriv]
    have hl : 1 / 2 ≤ Real.log x := by
      have : Real.log 2 < Real.log x := Real.log_lt_log (by norm_num) hx2
      linarith [Real.log_two_gt_d9]
    have he := Real.exp_pos (-s * Real.log x)
    have hxi : 0 < x⁻¹ := inv_pos.mpr hx0
    have hsl : 1 ≤ s * Real.log x := by nlinarith
    have : x⁻¹ * Real.exp (-s * Real.log x) +
        Real.log x * (Real.exp (-s * Real.log x) * (-s * x⁻¹)) =
        x⁻¹ * Real.exp (-s * Real.log x) * (1 - s * Real.log x) := by ring
    rw [this]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    nlinarith

/-- `∫_a^b g ≤ −H(a)` for `1 ≤ a ≤ b`. -/
theorem intervalIntegral_logPowDecay_le {s : ℝ} (hs : 1 < s) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, logPowDecay s x ≤ -logPowPrimitive s a := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (logPowPrimitive s) (logPowDecay s x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_logPowPrimitive hs (by linarith [hx.1])
  have hint : IntervalIntegrable (logPowDecay s) volume a b :=
    ((continuousOn_logPowDecay s).mono fun x hx => by
      rw [uIcc_of_le hab] at hx; exact mem_Ioi.mpr (by linarith [hx.1])).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  linarith [logPowPrimitive_nonpos hs (by linarith : 1 ≤ b)]

/-- **Decreasing logarithmic sums.** For `s ≥ 2` and `n₀ ≥ 2`,
`Σ_{n₀ ≤ n < M} log n · n^{−s} ≤ g(n₀) − H(n₀)`. -/
theorem sum_logPowDecay_le {s : ℝ} (hs : 2 ≤ s) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (M : ℕ) :
    ∑ n ∈ Finset.Ico n₀ M, logPowDecay s n ≤ logPowDecay s n₀ - logPowPrimitive s n₀ := by
  have hn₀' : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  rcases le_or_gt M n₀ with hM | hM
  · rw [Finset.Ico_eq_empty_of_le hM, Finset.sum_empty]
    have h1 : 0 ≤ logPowDecay s n₀ := by
      unfold logPowDecay
      exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.exp_pos _).le
    linarith [logPowPrimitive_nonpos (by linarith : (1 : ℝ) < s) (by linarith : (1 : ℝ) ≤ n₀)]
  · have hsplit : ∑ n ∈ Finset.Ico n₀ M, logPowDecay s n =
        logPowDecay s n₀ + ∑ i ∈ Finset.Ico n₀ (M - 1), logPowDecay s ((i + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hM]
      congr 1
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      rw [show M - (n₀ + 1) = M - 1 - n₀ by omega]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2; ring
    rw [hsplit]
    have hmono := antitoneOn_logPowDecay (s := s) hs hn₀'
    have hsum := AntitoneOn.sum_le_integral_Ico (a := n₀) (b := M - 1) (f := logPowDecay s)
      (by omega) (hmono.mono fun x hx => mem_Ici.mpr hx.1)
    have hint := intervalIntegral_logPowDecay_le (s := s) (by linarith)
      (a := n₀) (b := ((M - 1 : ℕ) : ℝ)) (by linarith)
      (by exact_mod_cast (show n₀ ≤ M - 1 by omega))
    have : ∑ i ∈ Finset.Ico n₀ (M - 1), logPowDecay s ((i + 1 : ℕ) : ℝ) =
        ∑ i ∈ Finset.Ico n₀ (M - 1), logPowDecay s (↑i + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_; push_cast; rfl
    rw [this]
    linarith

/-! ## The lag function and the prime term -/

variable {R : ℝ}

/-- The lag function `k(x) = ∫ T(u) T(u − x) du`. -/
def edgeLag (L R x : ℝ) : ℝ := ∫ u, edgeTail L R u * edgeTail L R (u - x)

theorem edgeLag_nonneg {L : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) (x : ℝ) : 0 ≤ edgeLag L R x :=
  integral_nonneg fun u => mul_nonneg (edgeTail_nonneg hL hR u) (edgeTail_nonneg hL hR _)

theorem edgeLag_neg (L R x : ℝ) : edgeLag L R (-x) = edgeLag L R x := by
  unfold edgeLag
  have h := integral_add_right_eq_self (μ := volume)
    (fun u => edgeTail L R u * edgeTail L R (u - x)) x
  simp only [add_sub_cancel_right] at h
  rw [← h]
  congr 1
  funext u
  rw [sub_neg_eq_add, mul_comm]

/-- `max(0, z) e^{−cz} ≤ (2/(ec)) e^{−cz/2}`. -/
theorem max_mul_exp_le {c : ℝ} (hc : 0 < c) (z : ℝ) :
    max 0 z * Real.exp (-c * z) ≤ 2 / (Real.exp 1 * c) * Real.exp (-(c / 2) * z) := by
  rcases le_or_gt z 0 with hz | hz
  · rw [max_eq_left hz, zero_mul]; positivity
  · rw [max_eq_right hz.le]
    set w := c * z / 2 with hw
    have hw1 : w ≤ Real.exp (w - 1) := by linarith [Real.add_one_le_exp (w - 1)]
    have hsplit : Real.exp (-c * z) = Real.exp (-(c / 2) * z) * Real.exp (-w) := by
      rw [← Real.exp_add]; congr 1; rw [hw]; ring
    rw [hsplit]
    have hew : w * Real.exp (-w) ≤ Real.exp (-1) := by
      calc w * Real.exp (-w) ≤ Real.exp (w - 1) * Real.exp (-w) :=
            mul_le_mul_of_nonneg_right hw1 (Real.exp_pos _).le
        _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
    have h1 : z * Real.exp (-w) ≤ 2 / (Real.exp 1 * c) := by
      have hzw : z * Real.exp (-w) = 2 / c * (w * Real.exp (-w)) := by
        rw [hw]; field_simp
      rw [hzw]
      have : 2 / c * Real.exp (-1) = 2 / (Real.exp 1 * c) := by
        rw [Real.exp_neg]; field_simp
      rw [← this]
      exact mul_le_mul_of_nonneg_left hew (by positivity)
    calc z * (Real.exp (-(c / 2) * z) * Real.exp (-w))
        = z * Real.exp (-w) * Real.exp (-(c / 2) * z) := by ring
      _ ≤ 2 / (Real.exp 1 * c) * Real.exp (-(c / 2) * z) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

theorem inv_sqrt_natCast_eq {n : ℕ} (hn : 0 < n) :
    1 / Real.sqrt n = Real.exp (-(1 / 2) * Real.log n) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hn), one_div, ← Real.exp_neg]
  ring_nf

/-- The first threshold integer `⌈e^{2L}⌉`. -/
def edgeThreshold (L : ℝ) : ℕ := ⌈Real.exp (2 * L)⌉₊

theorem two_le_edgeThreshold {L : ℝ} (hL : 1 ≤ L) : 2 ≤ edgeThreshold L := by
  unfold edgeThreshold
  have h : (2 : ℝ) < Real.exp (2 * L) := by
    have := Real.add_one_le_exp (2 * L); linarith
  have := Nat.le_ceil (Real.exp (2 * L))
  exact_mod_cast (show (2 : ℝ) ≤ ⌈Real.exp (2 * L)⌉₊ by linarith)

theorem log_lt_of_lt_edgeThreshold {L : ℝ} {n : ℕ} (hn : 0 < n) (h : n < edgeThreshold L) :
    Real.log n < 2 * L := by
  have h1 : (n : ℝ) < Real.exp (2 * L) := Nat.lt_ceil.mp h
  rw [Real.log_lt_iff_lt_exp (by exact_mod_cast hn)]
  exact h1

/-- **Per-prime bound.** -/
theorem vonMangoldt_mul_edgeLag_le {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L)
    {n : ℕ} (hn : 2 ≤ n) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * edgeLag L R (Real.log n) ≤
      2 * (riemannEnvelopeConst * kernelEnvelope L) * (∫ u, edgeTail L R u) *
          logPowDecay (edgeRate L - 9 / 2 + 1 / 2) n +
        (riemannEnvelopeConst * kernelEnvelope L) ^ 2 * (2 / (Real.exp 1 * (edgeRate L - 9 / 2))) *
          Real.exp ((edgeRate L - 9 / 2) * L) *
          (if edgeThreshold L ≤ n then logPowDecay ((edgeRate L - 9 / 2 + 1) / 2) n else 0) := by
  set A := riemannEnvelopeConst * kernelEnvelope L with hA
  set c := edgeRate L - 9 / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hA0 : 0 ≤ A := mul_nonneg riemannEnvelopeConst_pos.le (kernelEnvelope_pos L).le
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hT0 : 0 ≤ ∫ u, edgeTail L R u := integral_edgeTail_nonneg (by linarith) hR
  set w := Real.log n * Real.exp (-(1 / 2) * Real.log n) with hw
  have hw0 : 0 ≤ w := mul_nonneg hlog0 (Real.exp_pos _).le
  have hΛ : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤ w := by
    rw [div_eq_mul_one_div, inv_sqrt_natCast_eq hn0, hw]
    exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.exp_pos _).le
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hk := integral_edgeTail_lag_le hL hR hY (x := Real.log n) hlog0
  have hk0 := edgeLag_nonneg (by linarith : (0 : ℝ) ≤ L) hR (Real.log n)
  have hmax := max_mul_exp_le hc0 (Real.log n - 2 * L)
  have hfirst : w * (2 * A * Real.exp (-c * Real.log n) * ∫ u, edgeTail L R u) =
      2 * A * (∫ u, edgeTail L R u) * logPowDecay (c + 1 / 2) n := by
    rw [hw]; unfold logPowDecay
    have : Real.exp (-(1 / 2) * Real.log n) * Real.exp (-c * Real.log n) =
        Real.exp (-(c + 1 / 2) * Real.log n) := by rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  have hsecond : w * (A ^ 2 * Real.exp (-c * (Real.log n - 2 * L)) * max 0 (Real.log n - 2 * L)) ≤
      A ^ 2 * (2 / (Real.exp 1 * c)) * Real.exp (c * L) *
        (if edgeThreshold L ≤ n then logPowDecay ((c + 1) / 2) n else 0) := by
    split_ifs with hth
    · have h1 : w * (A ^ 2 * Real.exp (-c * (Real.log n - 2 * L)) * max 0 (Real.log n - 2 * L)) ≤
          w * (A ^ 2 * (2 / (Real.exp 1 * c) * Real.exp (-(c / 2) * (Real.log n - 2 * L)))) := by
        apply mul_le_mul_of_nonneg_left _ hw0
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
        rw [mul_comm]; exact hmax
      refine h1.trans (le_of_eq ?_)
      rw [hw]; unfold logPowDecay
      have : Real.exp (-(1 / 2) * Real.log n) * Real.exp (-(c / 2) * (Real.log n - 2 * L)) =
          Real.exp (c * L) * Real.exp (-((c + 1) / 2) * Real.log n) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      calc Real.log n * Real.exp (-(1 / 2) * Real.log n) *
            (A ^ 2 * (2 / (Real.exp 1 * c) * Real.exp (-(c / 2) * (Real.log n - 2 * L))))
          = A ^ 2 * (2 / (Real.exp 1 * c)) * Real.log n *
            (Real.exp (-(1 / 2) * Real.log n) * Real.exp (-(c / 2) * (Real.log n - 2 * L))) := by
            ring
        _ = _ := by rw [this]; ring
    · push Not at hth
      have hlt := log_lt_of_lt_edgeThreshold hn0 hth
      rw [max_eq_left (by linarith), mul_zero, mul_zero, mul_zero]
  calc ArithmeticFunction.vonMangoldt n / Real.sqrt n * edgeLag L R (Real.log n)
      ≤ w * edgeLag L R (Real.log n) := mul_le_mul_of_nonneg_right hΛ hk0
    _ ≤ w * (2 * A * Real.exp (-c * Real.log n) * (∫ u, edgeTail L R u) +
          A ^ 2 * Real.exp (-c * (Real.log n - 2 * L)) * max 0 (Real.log n - 2 * L)) :=
        mul_le_mul_of_nonneg_left hk hw0
    _ = w * (2 * A * Real.exp (-c * Real.log n) * ∫ u, edgeTail L R u) +
          w * (A ^ 2 * Real.exp (-c * (Real.log n - 2 * L)) * max 0 (Real.log n - 2 * L)) := by
        ring
    _ ≤ _ := by rw [hfirst]; linarith [hsecond]

/-- The bound on the prime term. -/
def edgePrimeBound (L R : ℝ) : ℝ :=
  2 * (2 * (riemannEnvelopeConst * kernelEnvelope L) * (∫ u, edgeTail L R u) *
      (logPowDecay (edgeRate L - 9 / 2 + 1 / 2) 2 - logPowPrimitive (edgeRate L - 9 / 2 + 1 / 2) 2) +
    (riemannEnvelopeConst * kernelEnvelope L) ^ 2 * (2 / (Real.exp 1 * (edgeRate L - 9 / 2))) *
      Real.exp ((edgeRate L - 9 / 2) * L) *
      (logPowDecay ((edgeRate L - 9 / 2 + 1) / 2) (edgeThreshold L) -
        logPowPrimitive ((edgeRate L - 9 / 2 + 1) / 2) (edgeThreshold L)))

/-- **The prime term of the tail.** Every partial sum of the prime atoms is at most
`edgePrimeBound L R`. -/
theorem sum_prime_edgeLag_le {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) (M : ℕ) :
    ∑ n ∈ Finset.range M, (if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) *
        (edgeLag L R (Real.log n) + edgeLag L R (-Real.log n)) ≤ edgePrimeBound L R := by
  obtain ⟨A, hA⟩ : ∃ A, A = riemannEnvelopeConst * kernelEnvelope L := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = edgeRate L - 9 / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; linarith
  have hT0 : 0 ≤ ∫ u, edgeTail L R u := integral_edgeTail_nonneg (by linarith) hR
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg riemannEnvelopeConst_pos.le (kernelEnvelope_pos L).le
  have hpt : ∀ n ∈ Finset.range M,
      (if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) *
        (edgeLag L R (Real.log n) + edgeLag L R (-Real.log n)) ≤
      (if 2 ≤ n then 2 * (2 * A * (∫ u, edgeTail L R u) * logPowDecay (c + 1 / 2) n +
        A ^ 2 * (2 / (Real.exp 1 * c)) * Real.exp (c * L) *
          (if edgeThreshold L ≤ n then logPowDecay ((c + 1) / 2) n else 0)) else 0) := fun n _ => by
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, if_pos h2, edgeLag_neg]
      have := vonMangoldt_mul_edgeLag_le (R := R) hL hR hY h2
      rw [← hA, ← hc] at this
      linarith
    · rw [if_neg h2, if_neg h2, zero_mul]
  refine (Finset.sum_le_sum hpt).trans ?_
  have hfilter : (Finset.range M).filter (fun n => 2 ≤ n) = Finset.Ico 2 M := by
    ext n; simp [Finset.mem_Ico, and_comm]
  have hthr := two_le_edgeThreshold hL
  have hfilter2 : (Finset.Ico 2 M).filter (fun n => edgeThreshold L ≤ n) =
      Finset.Ico (edgeThreshold L) M := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  rw [← Finset.sum_filter, hfilter]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs1 : (2 : ℝ) ≤ c + 1 / 2 := by linarith
  have hs2 : (2 : ℝ) ≤ (c + 1) / 2 := by linarith
  have hsum1 := sum_logPowDecay_le hs1 (le_refl 2) M
  have hsum2 := sum_logPowDecay_le hs2 hthr M
  have hite : ∑ n ∈ Finset.Ico 2 M,
      (if edgeThreshold L ≤ n then logPowDecay ((c + 1) / 2) (n : ℝ) else 0) =
      ∑ n ∈ Finset.Ico (edgeThreshold L) M, logPowDecay ((c + 1) / 2) (n : ℝ) := by
    rw [← Finset.sum_filter, hfilter2]
  rw [hite]
  have hcoef : 0 ≤ A ^ 2 * (2 / (Real.exp 1 * c)) * Real.exp (c * L) := by positivity
  have hcoef1 : 0 ≤ 2 * A * ∫ u, edgeTail L R u := by positivity
  unfold edgePrimeBound
  rw [← hA, ← hc]
  push_cast at hsum1
  have e1 := mul_le_mul_of_nonneg_left hsum1 hcoef1
  have e2 := mul_le_mul_of_nonneg_left hsum2 hcoef
  nlinarith

/-! ## The pole and archimedean terms -/

theorem conj_I_div_two : (starRingEnd ℂ) (I / 2) = -I / 2 := by
  rw [map_div₀, Complex.conj_I, map_ofNat]

theorem conj_neg_I_div_two : (starRingEnd ℂ) (-I / 2) = I / 2 := by
  rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]

theorem paperFT_ofRealFun_I_div_two (f : ℝ → ℝ) :
    paperFT (fun u => (f u : ℂ)) (I / 2) = ((∫ u, f u * Real.exp (-u / 2) : ℝ) : ℂ) := by
  rw [LebesgueAtomWeil.paperFT_I_div_two, ← integral_complex_ofReal]
  push_cast; rfl

theorem paperFT_ofRealFun_neg_I_div_two (f : ℝ → ℝ) :
    paperFT (fun u => (f u : ℂ)) (-I / 2) = ((∫ u, f u * Real.exp (u / 2) : ℝ) : ℂ) := by
  rw [LebesgueAtomWeil.paperFT_neg_I_div_two, ← integral_complex_ofReal]
  push_cast; rfl

/-- **The pole term of a nonnegative test is nonnegative.** -/
theorem re_pole_nonneg {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ (paperFT (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) (I / 2) +
      paperFT (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) (-I / 2)).re := by
  have hc : Continuous (fun u => (f u : ℂ)) := Complex.continuous_ofReal.comp hf
  have hcc : HasCompactSupport (fun u => (f u : ℂ)) :=
    hfc.comp_left (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero
  rw [EF.paperFT_weilTest hc hc hcc hcc, EF.paperFT_weilTest hc hc hcc hcc, conj_I_div_two,
    conj_neg_I_div_two, paperFT_ofRealFun_I_div_two, paperFT_ofRealFun_neg_I_div_two]
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have h1 : 0 ≤ ∫ u, f u * Real.exp (-u / 2) :=
    integral_nonneg fun u => mul_nonneg (hf0 u) (Real.exp_pos _).le
  have h2 : 0 ≤ ∫ u, f u * Real.exp (u / 2) :=
    integral_nonneg fun u => mul_nonneg (hf0 u) (Real.exp_pos _).le
  positivity

theorem paperFT_weilTest_self_eq_normSq {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (r : ℝ) : paperFT (EF.weilTest f f) r = ((‖paperFT f r‖ ^ 2 : ℝ) : ℂ) := by
  rw [EF.paperFT_weilTest hf hf hfc hfc, Complex.conj_ofReal, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

theorem norm_paperFT_real_le_integral_norm {f : ℝ → ℂ} (r : ℝ) : ‖paperFT f r‖ ≤ ∫ u, ‖f u‖ := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [norm_mul, show I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Archimedean lower bound.** With `ℓ = log(1 + M/4)`, the archimedean term of a `C²`
compactly supported test is at least `(ℓ − 10)∫|f|² − (ℓM/π)(∫|f|)²`. -/
theorem re_arch_ge {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ} (hfs : tsupport f ⊆ Icc (-a) a)
    {M : ℝ} (hM : 0 ≤ M) :
    (Real.log (1 + M / 4) - 10) * (∫ u, ‖f u‖ ^ 2) -
        Real.log (1 + M / 4) * M / π * (∫ u, ‖f u‖) ^ 2 ≤
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfs
  set ℓ := Real.log (1 + M / 4) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  set F : ℝ → ℝ := fun r => ‖paperFT f r‖ ^ 2 with hF
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hFint : Integrable F := integrable_normSq_paperFT hf hfs
  have hFγ : Integrable (fun r => F r * EF.gammaBracket r) := by
    have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hf hfc hf hfc
    have h2 : Integrable (fun r : ℝ =>
        (paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re) := h.re
    refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hF]
    rw [paperFT_weilTest_self_eq_normSq hf.continuous hfc, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hcomplex : ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f f) r *
      (EF.gammaBracket r : ℂ)).re = (1 / (2 * π)) * ∫ r, F r * EF.gammaBracket r := by
    have : ∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ) =
        ((∫ r, F r * EF.gammaBracket r : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1; funext r
      rw [paperFT_weilTest_self_eq_normSq hf.continuous hfc, ← Complex.ofReal_mul]
    rw [this, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hcomplex]
  have hind : Integrable ((Icc (-M) M).indicator F) := hFint.indicator measurableSet_Icc
  have hpt : ∀ r, F r * ((ℓ - 10) - ℓ * (Icc (-M) M).indicator (fun _ => (1 : ℝ)) r) ≤
      F r * EF.gammaBracket r := fun r => by
    have hF0 : 0 ≤ F r := sq_nonneg _
    apply mul_le_mul_of_nonneg_left _ hF0
    have hγ := WeilWorkPBAP.gammaBracket_lower r
    by_cases hr : r ∈ Icc (-M) M
    · rw [indicator_of_mem hr]
      have : 0 ≤ Real.log (1 + |r| / 4) := Real.log_nonneg (by have := abs_nonneg r; linarith)
      linarith
    · rw [indicator_of_notMem hr, mul_zero, sub_zero]
      have hrM : M < |r| := by
        rw [Set.mem_Icc, not_and_or] at hr
        rcases hr with h | h
        · push Not at h; exact lt_abs.2 (Or.inr (by linarith))
        · push Not at h; exact lt_abs.2 (Or.inl h)
      have : ℓ ≤ Real.log (1 + |r| / 4) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
  have hlhs_int : Integrable (fun r => F r * ((ℓ - 10) - ℓ *
      (Icc (-M) M).indicator (fun _ => (1 : ℝ)) r)) := by
    have e : (fun r => F r * ((ℓ - 10) - ℓ * (Icc (-M) M).indicator (fun _ => (1 : ℝ)) r)) =
        fun r => (ℓ - 10) * F r - ℓ * (Icc (-M) M).indicator F r := by
      funext r
      by_cases hr : r ∈ Icc (-M) M
      · rw [indicator_of_mem hr, indicator_of_mem hr]; ring
      · rw [indicator_of_notMem hr, indicator_of_notMem hr]; ring
    rw [e]
    exact (hFint.const_mul _).sub (hind.const_mul _)
  have hmono := integral_mono hlhs_int hFγ hpt
  have heval : ∫ r, F r * ((ℓ - 10) - ℓ * (Icc (-M) M).indicator (fun _ => (1 : ℝ)) r) =
      (ℓ - 10) * (∫ r, F r) - ℓ * ∫ r in Icc (-M) M, F r := by
    have e : (fun r => F r * ((ℓ - 10) - ℓ * (Icc (-M) M).indicator (fun _ => (1 : ℝ)) r)) =
        fun r => (ℓ - 10) * F r - ℓ * (Icc (-M) M).indicator F r := by
      funext r
      by_cases hr : r ∈ Icc (-M) M
      · rw [indicator_of_mem hr, indicator_of_mem hr]; ring
      · rw [indicator_of_notMem hr, indicator_of_notMem hr]; ring
    rw [e, integral_sub (hFint.const_mul _) (hind.const_mul _), integral_const_mul,
      integral_const_mul, integral_indicator measurableSet_Icc]
  have hplanch : ∫ r, F r = 2 * π * ∫ u, ‖f u‖ ^ 2 := by
    have h := LebesgueAtomWeil.integral_norm_sq_paperFT_eq hf hfc
    rw [← h, hF]; field_simp
  have hlow : ∫ r in Icc (-M) M, F r ≤ 2 * M * (∫ u, ‖f u‖) ^ 2 := by
    have hb : ∀ r ∈ Icc (-M) M, F r ≤ (∫ u, ‖f u‖) ^ 2 := fun r _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_paperFT_real_le_integral_norm r) 2
    calc ∫ r in Icc (-M) M, F r ≤ ∫ _r in Icc (-M) M, (∫ u, ‖f u‖) ^ 2 :=
          setIntegral_mono_on hFint.integrableOn (integrableOn_const measure_Icc_lt_top.ne)
            measurableSet_Icc hb
      _ = 2 * M * (∫ u, ‖f u‖) ^ 2 := by
          rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
            max_eq_left (by linarith)]; ring
  rw [heval, hplanch] at hmono
  have hπ := Real.pi_pos
  have key : (ℓ - 10) * (∫ u, ‖f u‖ ^ 2) - ℓ * M / π * (∫ u, ‖f u‖) ^ 2 ≤
      1 / (2 * π) * ((ℓ - 10) * (2 * π * ∫ u, ‖f u‖ ^ 2) - ℓ * ∫ r in Icc (-M) M, F r) := by
    have h1 := mul_le_mul_of_nonneg_left hlow hℓ0
    rw [mul_sub, show 1 / (2 * π) * ((ℓ - 10) * (2 * π * ∫ u, ‖f u‖ ^ 2)) =
      (ℓ - 10) * ∫ u, ‖f u‖ ^ 2 by field_simp]
    have h2 : 1 / (2 * π) * (ℓ * ∫ r in Icc (-M) M, F r) ≤ ℓ * M / π * (∫ u, ‖f u‖) ^ 2 := by
      calc 1 / (2 * π) * (ℓ * ∫ r in Icc (-M) M, F r)
          ≤ 1 / (2 * π) * (ℓ * (2 * M * (∫ u, ‖f u‖) ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ℓ * M / π * (∫ u, ‖f u‖) ^ 2 := by field_simp
    linarith
  exact key.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

/-! ## The Weil energy of the tail -/

theorem contDiff_ofReal_edgeTail (L R : ℝ) : ContDiff ℝ 2 (fun u => (edgeTail L R u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_edgeTail L R).of_le (WithTop.coe_le_coe.2 le_top))

theorem tsupport_ofReal_edgeTail {L : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) :
    tsupport (fun u => (edgeTail L R u : ℂ)) ⊆ Icc (-(R + 1)) (R + 1) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hc
  apply hu
  have : R + 1 ≤ |u| := by
    rw [Set.mem_Icc, not_and_or] at hc
    rcases hc with h | h
    · push Not at h; exact le_abs.2 (Or.inr (by linarith))
    · push Not at h; exact le_abs.2 (Or.inl h.le)
  simp [edgeTail_eq_zero_of_ge hL hR this]

theorem weilTest_ofReal_edgeTail (L R x : ℝ) :
    EF.weilTest (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ)) x =
      (edgeLag L R x : ℂ) := by
  rw [WeilSpectral.weilTest_apply, edgeLag, ← integral_complex_ofReal]
  congr 1; funext u
  rw [Complex.conj_ofReal]; push_cast; rfl

/-- **Explicit-formula lower bound for the tail.** -/
theorem re_W_edgeTail_ge {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) {M : ℝ}
    (hM : 0 ≤ M) :
    (Real.log (1 + M / 4) - 10) * (∫ u, edgeTail L R u ^ 2) -
        Real.log (1 + M / 4) * M / π * (∫ u, edgeTail L R u) ^ 2 - edgePrimeBound L R ≤
      (zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ))).re := by
  set Tc : ℝ → ℂ := fun u => (edgeTail L R u : ℂ) with hTc
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hd := contDiff_ofReal_edgeTail L R
  have hs := tsupport_ofReal_edgeTail hL0 hR
  have hc : HasCompactSupport Tc := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hs
  rw [zeta_W_eq_weilFullFunctional hd hc]
  unfold weilFullFunctional
  have hkc : HasCompactSupport (EF.weilTest Tc Tc) := EF.weilTest_hasCompactSupport hc hc
  -- the pole term
  have hpole := re_pole_nonneg (continuous_edgeTail L R) (hasCompactSupport_edgeTail hL0 hR)
    (edgeTail_nonneg hL0 hR)
  -- the archimedean term
  have harch := re_arch_ge hd hs hM
  have hn1 : ∀ u, ‖Tc u‖ = edgeTail L R u := fun u => by
    rw [hTc]; simp only; rw [Complex.norm_real, Real.norm_of_nonneg (edgeTail_nonneg hL0 hR u)]
  have e1 : ∫ u, ‖Tc u‖ ^ 2 = ∫ u, edgeTail L R u ^ 2 := by
    congr 1; funext u; rw [hn1]
  have e2 : ∫ u, ‖Tc u‖ = ∫ u, edgeTail L R u := by
    congr 1; funext u; rw [hn1]
  rw [e1, e2] at harch
  -- the prime term
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hkc
  have hterm : ∀ n : ℕ, ((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0 : ℝ)
      : ℂ) * (EF.weilTest Tc Tc (Real.log n) + EF.weilTest Tc Tc (-Real.log n)) =
      (((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) *
        (edgeLag L R (Real.log n) + edgeLag L R (-Real.log n)) : ℝ) : ℂ) := fun n => by
    rw [hTc, weilTest_ofReal_edgeTail, weilTest_ofReal_edgeTail]; push_cast; ring
  have hsum : ∑' n : ℕ, ((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0 : ℝ)
      : ℂ) * (EF.weilTest Tc Tc (Real.log n) + EF.weilTest Tc Tc (-Real.log n)) =
      ((∑ n ∈ Finset.range N, (if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) *
        (edgeLag L R (Real.log n) + edgeLag L R (-Real.log n)) : ℝ) : ℂ) := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => ?_)]
    · push_cast
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hterm]; push_cast; ring
    · rw [Finset.mem_range, not_lt] at hn
      rw [(hN n hn).1, (hN n hn).2, add_zero, mul_zero]
  have hprime := sum_prime_edgeLag_le hL hR hY N
  rw [hsum]
  rw [Complex.add_re] at hpole
  rw [Complex.add_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re]
  linarith

/-! ## Bounds for the logarithmic remainders -/

theorem logPowDecay_nonneg {s x : ℝ} (hx : 1 ≤ x) : 0 ≤ logPowDecay s x :=
  mul_nonneg (Real.log_nonneg hx) (Real.exp_pos _).le

/-- `g(2) − H(2) ≤ 5 e^{−s/2}` for `s ≥ 2`. -/
theorem logPow_at_two_le {s : ℝ} (hs : 2 ≤ s) :
    logPowDecay s 2 - logPowPrimitive s 2 ≤ 5 * Real.exp (-s / 2) := by
  unfold logPowDecay logPowPrimitive
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlh : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hs1 : 1 ≤ s - 1 := by linarith
  have hq1 : Real.log 2 / (s - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hq2 : 1 / (s - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have he1 : Real.exp (-s * Real.log 2) ≤ Real.exp (-s / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp ((1 - s) * Real.log 2) = 2 * Real.exp (-s * Real.log 2) := by
    rw [show (1 - s) * Real.log 2 = Real.log 2 + -s * Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num)]
  rw [he2]
  have hpos := Real.exp_pos (-s * Real.log 2)
  have hq0 : 0 ≤ Real.log 2 / (s - 1) + 1 / (s - 1) ^ 2 := by positivity
  nlinarith

theorem two_mul_le_log_edgeThreshold {L : ℝ} (hL : 0 ≤ L) :
    2 * L ≤ Real.log (edgeThreshold L) ∧ Real.log (edgeThreshold L) ≤ 2 * L + 1 := by
  have h1 : Real.exp (2 * L) ≤ (edgeThreshold L : ℝ) := Nat.le_ceil _
  have h2 : (edgeThreshold L : ℝ) < Real.exp (2 * L) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hpos : 0 < (edgeThreshold L : ℝ) := lt_of_lt_of_le (Real.exp_pos _) h1
  constructor
  · rw [Real.le_log_iff_exp_le hpos]; exact h1
  · rw [Real.log_le_iff_le_exp hpos, Real.exp_add]
    have he : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
    have hE : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith

/-- `e^{cL}(g − H)(n₁) ≤ (2L + 1)e^{−L} + e^{L}((2L + 1)/(s − 1) + 1/(s − 1)²)`, `s = (c + 1)/2`. -/
theorem exp_mul_logPow_threshold_le {L c : ℝ} (hL : 0 ≤ L) (hc : 1 < c) :
    Real.exp (c * L) * (logPowDecay ((c + 1) / 2) (edgeThreshold L) -
        logPowPrimitive ((c + 1) / 2) (edgeThreshold L)) ≤
      (2 * L + 1) * Real.exp (-L) + Real.exp L * ((2 * L + 1) / ((c + 1) / 2 - 1) +
        1 / ((c + 1) / 2 - 1) ^ 2) := by
  obtain ⟨h1, h2⟩ := two_mul_le_log_edgeThreshold hL
  set ℓ := Real.log (edgeThreshold L) with hℓ
  set s := (c + 1) / 2 with hs
  have hs1 : 0 < s - 1 := by rw [hs]; linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  unfold logPowDecay logPowPrimitive
  rw [← hℓ]
  have hA : Real.exp (c * L) * (ℓ * Real.exp (-s * ℓ)) ≤ (2 * L + 1) * Real.exp (-L) := by
    have e1 : Real.exp (-s * ℓ) ≤ Real.exp (-s * (2 * L)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (c * L) * Real.exp (-s * (2 * L)) = Real.exp (-L) := by
      rw [← Real.exp_add, hs]; congr 1; ring
    calc Real.exp (c * L) * (ℓ * Real.exp (-s * ℓ))
        ≤ Real.exp (c * L) * ((2 * L + 1) * Real.exp (-s * (2 * L))) := by
          gcongr
      _ = (2 * L + 1) * (Real.exp (c * L) * Real.exp (-s * (2 * L))) := by ring
      _ = _ := by rw [e2]
  have hB : Real.exp (c * L) * (Real.exp ((1 - s) * ℓ) * (ℓ / (s - 1) + 1 / (s - 1) ^ 2)) ≤
      Real.exp L * ((2 * L + 1) / (s - 1) + 1 / (s - 1) ^ 2) := by
    have e1 : Real.exp ((1 - s) * ℓ) ≤ Real.exp ((1 - s) * (2 * L)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (c * L) * Real.exp ((1 - s) * (2 * L)) = Real.exp L := by
      rw [← Real.exp_add, hs]; congr 1; ring
    have e3 : ℓ / (s - 1) + 1 / (s - 1) ^ 2 ≤ (2 * L + 1) / (s - 1) + 1 / (s - 1) ^ 2 := by
      gcongr
    have hq : 0 ≤ ℓ / (s - 1) + 1 / (s - 1) ^ 2 := by positivity
    calc Real.exp (c * L) * (Real.exp ((1 - s) * ℓ) * (ℓ / (s - 1) + 1 / (s - 1) ^ 2))
        ≤ Real.exp (c * L) * (Real.exp ((1 - s) * (2 * L)) *
            ((2 * L + 1) / (s - 1) + 1 / (s - 1) ^ 2)) := by
          gcongr
      _ = (Real.exp (c * L) * Real.exp ((1 - s) * (2 * L))) *
            ((2 * L + 1) / (s - 1) + 1 / (s - 1) ^ 2) := by ring
      _ = _ := by rw [e2]
  have : Real.exp (c * L) * (ℓ * Real.exp (-s * ℓ) -
      -(Real.exp ((1 - s) * ℓ) * (ℓ / (s - 1) + 1 / (s - 1) ^ 2))) =
      Real.exp (c * L) * (ℓ * Real.exp (-s * ℓ)) +
        Real.exp (c * L) * (Real.exp ((1 - s) * ℓ) * (ℓ / (s - 1) + 1 / (s - 1) ^ 2)) := by ring
  rw [this]
  linarith

/-! ## Positivity for large `L` -/

/-- The narrowness constant `κ = C₀² e⁶/25`. -/
def narrowConst : ℝ := riemannEnvelopeConst ^ 2 * Real.exp 6 / 25

theorem narrowConst_pos : 0 < narrowConst := by
  unfold narrowConst; have := riemannEnvelopeConst_pos; positivity

/-- The archimedean band `M = πY/(2κ)`. -/
def edgeBand (L : ℝ) : ℝ := π * edgeRate L / (2 * narrowConst)

theorem edgeBand_pos (L : ℝ) : 0 < edgeBand L := by
  unfold edgeBand; have := narrowConst_pos; have := edgeRate_pos L; positivity

/-- **Narrow form of the lower bound.** `Re W(T, T) ≥ (ℓ/2 − 10)∫T² − P` with `ℓ = log(1 + M/4)`. -/
theorem re_W_edgeTail_ge_narrow {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) :
    (Real.log (1 + edgeBand L / 4) / 2 - 10) * (∫ u, edgeTail L R u ^ 2) - edgePrimeBound L R ≤
      (zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ))).re := by
  have hM := (edgeBand_pos L).le
  have h := re_W_edgeTail_ge hL hR hY hM
  have hn := sq_integral_edgeTail_le hL hR hY
  have hℓ0 : 0 ≤ Real.log (1 + edgeBand L / 4) := Real.log_nonneg (by linarith)
  have hY0 := edgeRate_pos L
  have hκ := narrowConst_pos
  have hkey : Real.log (1 + edgeBand L / 4) * edgeBand L / π * (∫ u, edgeTail L R u) ^ 2 ≤
      Real.log (1 + edgeBand L / 4) / 2 * ∫ u, edgeTail L R u ^ 2 := by
    have hc : Real.log (1 + edgeBand L / 4) * edgeBand L / π * (narrowConst / edgeRate L) =
        Real.log (1 + edgeBand L / 4) / 2 := by
      unfold edgeBand; field_simp
    have hn' : (∫ u, edgeTail L R u) ^ 2 ≤ narrowConst / edgeRate L * ∫ u, edgeTail L R u ^ 2 := by
      unfold narrowConst; exact hn
    calc Real.log (1 + edgeBand L / 4) * edgeBand L / π * (∫ u, edgeTail L R u) ^ 2
        ≤ Real.log (1 + edgeBand L / 4) * edgeBand L / π *
            (narrowConst / edgeRate L * ∫ u, edgeTail L R u ^ 2) :=
          mul_le_mul_of_nonneg_left hn' (by have := Real.pi_pos; positivity)
      _ = _ := by rw [← mul_assoc, hc]
  linarith

/-- `u(L) = (2L + 1)e^{−L}`. -/
def edgeDecay (L : ℝ) : ℝ := (2 * L + 1) * Real.exp (-L)

theorem edgeDecay_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ edgeDecay L := by
  unfold edgeDecay; have := Real.exp_pos (-L); positivity

theorem exp_neg_le_edgeDecay {L : ℝ} (hL : 0 ≤ L) : Real.exp (-L) ≤ edgeDecay L := by
  unfold edgeDecay; nlinarith [Real.exp_pos (-L)]

theorem edgeRate_ge {L : ℝ} (hL : 1 ≤ L) :
    12 ≤ edgeRate L ∧ 4 * L ≤ edgeRate L ∧ 6 * Real.exp (2 * L) ≤ edgeRate L := by
  unfold edgeRate
  have he : 1 + 2 * L ≤ Real.exp (2 * L) := by linarith [Real.add_one_le_exp (2 * L)]
  have hπ := Real.pi_gt_three
  have hE : 0 < Real.exp (2 * L) := Real.exp_pos _
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem exp_two_mul_eq_sq (L : ℝ) : Real.exp (2 * L) = Real.exp L ^ 2 := by
  rw [← Real.exp_nat_mul]; push_cast; ring_nf

theorem exp_neg_eq_inv (L : ℝ) : Real.exp (-L) = (Real.exp L)⁻¹ := Real.exp_neg L

/-- `e^L (2L + 1)/(s − 1) ≤ u(L)` with `s − 1 = (Y − 11/2)/2`. -/
theorem threshold_first_le {L Y : ℝ} (hL : 0 ≤ L) (hY6 : 6 * Real.exp (2 * L) ≤ Y)
    (hY12 : 12 ≤ Y) :
    Real.exp L * ((2 * L + 1) / ((Y - 9 / 2 + 1) / 2 - 1)) ≤ edgeDecay L := by
  unfold edgeDecay
  rw [exp_two_mul_eq_sq] at hY6
  rw [exp_neg_eq_inv]
  set t := Real.exp L with ht
  have ht1 : 1 ≤ t := Real.one_le_exp hL
  have hden : (Y - 9 / 2 + 1) / 2 - 1 = (Y - 11 / 2) / 2 := by ring
  rw [hden]
  have hd0 : 0 < (Y - 11 / 2) / 2 := by linarith
  rw [mul_div_assoc', div_le_iff₀ hd0]
  have hL1 : 0 < 2 * L + 1 := by linarith
  -- t (2L+1) ≤ (2L+1) t⁻¹ (Y − 11/2)/2, i.e. t² ≤ (Y − 11/2)/2
  have hkey : t * t ≤ (Y - 11 / 2) / 2 := by nlinarith
  have htinv : t⁻¹ * t = 1 := inv_mul_cancel₀ (by linarith)
  have : t * (2 * L + 1) = (2 * L + 1) * t⁻¹ * (t * t) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hkey (by have := inv_pos.mpr (show 0 < t by linarith); positivity)

/-- `e^L/(s − 1)² ≤ u(L)`. -/
theorem threshold_second_le {L Y : ℝ} (hL : 0 ≤ L) (hY6 : 6 * Real.exp (2 * L) ≤ Y)
    (hY12 : 12 ≤ Y) :
    Real.exp L * (1 / ((Y - 9 / 2 + 1) / 2 - 1) ^ 2) ≤ edgeDecay L := by
  refine le_trans ?_ (exp_neg_le_edgeDecay hL)
  rw [exp_two_mul_eq_sq] at hY6
  rw [exp_neg_eq_inv]
  set t := Real.exp L with ht
  have ht1 : 1 ≤ t := Real.one_le_exp hL
  have hden : (Y - 9 / 2 + 1) / 2 - 1 = (Y - 11 / 2) / 2 := by ring
  rw [hden]
  have hd : t * t ≤ (Y - 11 / 2) / 2 := by nlinarith
  have hd0 : 0 < (Y - 11 / 2) / 2 := by linarith
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  have h2 : t * t * (t * t) ≤ ((Y - 11 / 2) / 2) ^ 2 := by
    rw [sq]; exact mul_le_mul hd hd (by positivity) hd0.le
  have h3 : t ≤ t⁻¹ * (t * t * (t * t)) := by
    rw [show t⁻¹ * (t * t * (t * t)) = t * t * t by field_simp]
    nlinarith
  calc t ≤ t⁻¹ * (t * t * (t * t)) := h3
    _ ≤ t⁻¹ * ((Y - 11 / 2) / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (inv_pos.mpr (by linarith)).le

/-- The first remainder is at most `5 u(L)`. -/
theorem logPow_at_two_le_decay {L Y : ℝ} (hL : 1 ≤ L) (hY4L : 4 * L ≤ Y) (hY12 : 12 ≤ Y) :
    logPowDecay (Y - 9 / 2 + 1 / 2) 2 - logPowPrimitive (Y - 9 / 2 + 1 / 2) 2 ≤
      5 * edgeDecay L := by
  refine (logPow_at_two_le (by linarith)).trans ?_
  have h1 : Real.exp (-(Y - 9 / 2 + 1 / 2) / 2) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
  linarith [exp_neg_le_edgeDecay (L := L) (by linarith)]

/-- The second remainder is at most `3 u(L)`. -/
theorem threshold_remainder_le {L Y : ℝ} (hL : 1 ≤ L) (hY6 : 6 * Real.exp (2 * L) ≤ Y)
    (hY12 : 12 ≤ Y) :
    Real.exp ((Y - 9 / 2) * L) * (logPowDecay ((Y - 9 / 2 + 1) / 2) (edgeThreshold L) -
      logPowPrimitive ((Y - 9 / 2 + 1) / 2) (edgeThreshold L)) ≤ 3 * edgeDecay L := by
  refine (exp_mul_logPow_threshold_le (by linarith) (by linarith)).trans ?_
  have h1 := threshold_first_le (by linarith) hY6 hY12
  have h2 := threshold_second_le (by linarith) hY6 hY12
  unfold edgeDecay at h1 h2 ⊢
  nlinarith

/-- The arithmetic of the explicit prime bound. -/
theorem edgePrimeBound_arith {Y E C d c T Q₁ x Q₂ e : ℝ} (hY0 : 0 < Y) (hE0 : 0 < E)
    (hC0 : 0 < C) (hd0 : 0 ≤ d) (hYc : Y ≤ 2 * c) (he : 1 ≤ e)
    (hT : T ≤ 4 * C * E / Y) (hQ1 : Q₁ ≤ 5 * d) (hQ1nn : 0 ≤ Q₁) (hX : x * Q₂ ≤ 3 * d) :
    2 * (2 * (C * E) * T * Q₁ + (C * E) ^ 2 * (2 / (e * c)) * x * Q₂) ≤
      E ^ 2 / Y * (120 * C ^ 2 * d) := by
  have hc0 : 0 < c := by linarith
  have h2c : 2 / (e * c) ≤ 4 / Y := by
    rw [div_le_div_iff₀ (by positivity) hY0]; nlinarith
  have hfirst : 2 * (C * E) * T * Q₁ ≤ 2 * (C * E) * (4 * C * E / Y) * (5 * d) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hT (by positivity)) hQ1 hQ1nn (by positivity)
  have hcoef : 0 ≤ (C * E) ^ 2 * (2 / (e * c)) := by positivity
  have hsecond : (C * E) ^ 2 * (2 / (e * c)) * x * Q₂ ≤ (C * E) ^ 2 * (4 / Y) * (3 * d) := by
    rw [mul_assoc]
    rcases le_or_gt 0 (x * Q₂) with hX0 | hX0
    · exact mul_le_mul (mul_le_mul_of_nonneg_left h2c (sq_nonneg _)) hX hX0 (by positivity)
    · have : (C * E) ^ 2 * (2 / (e * c)) * (x * Q₂) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoef hX0.le
      have : 0 ≤ (C * E) ^ 2 * (4 / Y) * (3 * d) := by positivity
      linarith
  have e1 : 2 * (2 * (C * E) * (4 * C * E / Y) * (5 * d)) = E ^ 2 / Y * (80 * C ^ 2 * d) := by
    field_simp; ring
  have e2 : 2 * ((C * E) ^ 2 * (4 / Y) * (3 * d)) = E ^ 2 / Y * (24 * C ^ 2 * d) := by
    field_simp; ring
  have hpos : 0 ≤ E ^ 2 / Y * (C ^ 2 * d) := by positivity
  nlinarith

/-- **Explicit prime bound.** For `L ≥ 1`, `P ≤ (E(L)²/Y)·120 C₀² u(L)`. -/
theorem edgePrimeBound_le_decay {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) :
    edgePrimeBound L R ≤
      kernelEnvelope L ^ 2 / edgeRate L * (120 * riemannEnvelopeConst ^ 2 * edgeDecay L) := by
  obtain ⟨hY12, hY4L, hY6⟩ := edgeRate_ge hL
  have hY9 : 9 ≤ edgeRate L := by linarith
  have hY0 := edgeRate_pos L
  have hE0 := kernelEnvelope_pos L
  have hC0 := riemannEnvelopeConst_pos
  have hd0 := edgeDecay_nonneg (L := L) (by linarith)
  have hT := integral_edgeTail_le hL hR hY9
  have hT' : ∫ u, edgeTail L R u ≤ 4 * riemannEnvelopeConst * kernelEnvelope L / edgeRate L := by
    refine hT.trans ?_
    rw [div_le_div_iff₀ (by linarith) hY0]; nlinarith [mul_pos hC0 hE0]
  have hQ1 := logPow_at_two_le_decay hL hY4L hY12
  have hQ1nn : 0 ≤ logPowDecay (edgeRate L - 9 / 2 + 1 / 2) 2 -
      logPowPrimitive (edgeRate L - 9 / 2 + 1 / 2) 2 := by
    have := logPowDecay_nonneg (s := edgeRate L - 9 / 2 + 1 / 2) (x := 2) (by norm_num)
    have := logPowPrimitive_nonpos (s := edgeRate L - 9 / 2 + 1 / 2) (by linarith) (x := 2)
      (by norm_num)
    linarith
  have hQ2 := threshold_remainder_le hL hY6 hY12
  unfold edgePrimeBound
  exact edgePrimeBound_arith hY0 hE0 hC0 hd0 (by linarith) (Real.one_le_exp (by norm_num))
    hT' hQ1 hQ1nn hQ2

theorem tendsto_edgeDecay : Tendsto edgeDecay atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h := (h1.const_mul 2).add h0
  simp only [mul_zero, add_zero, pow_one, pow_zero, one_mul] at h
  refine h.congr fun L => ?_
  unfold edgeDecay; ring

theorem eventually_log_edgeBand_ge (B : ℝ) :
    ∀ᶠ L : ℝ in atTop, B ≤ Real.log (1 + edgeBand L / 4) := by
  have hκ := narrowConst_pos
  have hlim : Tendsto (fun L : ℝ => edgeBand L / 4) atTop atTop := by
    have h : Tendsto (fun L : ℝ => Real.exp (2 * L)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
    have hc : 0 < π * (2 * π) / (2 * narrowConst) / 4 := by have := Real.pi_pos; positivity
    refine (h.const_mul_atTop hc).congr fun L => ?_
    unfold edgeBand edgeRate; ring
  filter_upwards [hlim.eventually_ge_atTop (Real.exp B)] with L hL
  rw [Real.le_log_iff_exp_le (by have := (edgeBand_pos L).le; linarith)]
  linarith

/-- **The edge tail of Riemann's kernel has a uniform Weil margin.** For all large `L` there is
`δ > 0` with `Re W(T_R, T_R) ≥ δ` for every outer radius `R ≥ L + 2`. -/
theorem eventually_exists_margin_edgeTail :
    ∀ᶠ L : ℝ in atTop, ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, L + 2 ≤ R →
      δ ≤ (zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ))).re := by
  have hC := riemannEnvelopeConst_pos
  have hsmall : (0 : ℝ) < 400 * Real.exp (-6) / (120 * riemannEnvelopeConst ^ 2 + 1) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_log_edgeBand_ge 22,
    tendsto_edgeDecay.eventually (gt_mem_nhds hsmall)] with L hL hℓ hu
  have hY0 := edgeRate_pos L
  have hE0 := kernelEnvelope_pos L
  have hu' : 120 * riemannEnvelopeConst ^ 2 * edgeDecay L < 400 * Real.exp (-6) := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 120 * riemannEnvelopeConst ^ 2 + 1)).mp hu
    have hd0 := edgeDecay_nonneg (L := L) (by linarith)
    nlinarith
  refine ⟨kernelEnvelope L ^ 2 / edgeRate L * (400 * Real.exp (-6) -
    120 * riemannEnvelopeConst ^ 2 * edgeDecay L), by have := sub_pos.mpr hu'; positivity, fun R hR => ?_⟩
  obtain ⟨hY12, -, -⟩ := edgeRate_ge hL
  have hY9 : 9 ≤ edgeRate L := by linarith
  have hlow := re_W_edgeTail_ge_narrow hL hR hY9
  have hP := edgePrimeBound_le_decay hL hR
  have hI := integral_edgeTail_sq_ge hL hR (by linarith)
  have hI0 : 0 ≤ ∫ u, edgeTail L R u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcoef : 1 ≤ Real.log (1 + edgeBand L / 4) / 2 - 10 := by linarith
  have h1 : ∫ u, edgeTail L R u ^ 2 ≤
      (Real.log (1 + edgeBand L / 4) / 2 - 10) * ∫ u, edgeTail L R u ^ 2 := by nlinarith
  have e : kernelEnvelope L ^ 2 / edgeRate L * (400 * Real.exp (-6) -
      120 * riemannEnvelopeConst ^ 2 * edgeDecay L) = 400 * Real.exp (-6) * kernelEnvelope L ^ 2 /
        edgeRate L - kernelEnvelope L ^ 2 / edgeRate L * (120 * riemannEnvelopeConst ^ 2 * edgeDecay L) := by
    ring
  rw [e]
  linarith

/-- **The edge tail of Riemann's kernel is Weil-positive.** For all large `L` and every outer
radius `R ≥ L + 2`, `Re W(T, T) > 0` for `T = Φ(χ_R − χ_L)`. -/
theorem eventually_re_W_edgeTail_pos :
    ∀ᶠ L : ℝ in atTop, ∀ R : ℝ, L + 2 ≤ R →
      0 < (zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ))).re := by
  filter_upwards [eventually_exists_margin_edgeTail] with L ⟨δ, hδ, h⟩ R hR
  exact hδ.trans_le (h R hR)

end

end RHTower
