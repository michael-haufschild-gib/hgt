import GaloisForLFunctions.RHTower.RiemannKernelSpikeLag
import GaloisForLFunctions.HTGeometry.SechSquareConvolutionKernel

/-!
# Prime sums of spike lags

Write `w_n = Λ(n)/√n` for `n ≥ 2` (`spikePrimeWeight`), `r_L = ‖P_L‖₂` (`spikeScale`) and
`K = C₀√(2π)e³/20` (`spikeAmpConst`). The layer bound for `combSpike` gives `A_L ≤ K e^L r_L`
(`spikeAmp_le_scale`). Combined with the pairwise lag bound, for levels `L, L' ≥ L₀ ≥ 1`,
`d = L − L'` and `κ = c(L₀) − 1`:

`Σ_{n<N} w_n ∫P_L(u)P_{L'}(u − log n) ≤ K² r_L r_{L'} [π⁻¹ Σ_{n<N} w_n n⁻¹ (e^{−κ|log n − d|} + e^{−κ|log n + d|}) + 2 v_L v_{L'}]`

with `v_L = (L + 1)e^{−L/2}` (`sum_prime_combSpike_lag_le`).

- **Same side.** `e^{L+L'}/(c + c') ≤ e^{−|d|}/π`, and `e^{−|d|}e^{−m|y − d|} ≤ e^{−y}e^{−(m−1)|y−d|}`
  turns the gain into a factor `1/n`.
- **Opposite sides.** About `e^{|d|}` integers lie in the window of width `1/Y` at `e^{L+L'}`. After
  normalization they cost `(L + L' + 2)e^{−(L+L')/2} ≤ v_L v_{L'}`.

If the points of `s` are `σ`-separated, `Σ_{y ∈ s} e^{−κ|z − y|} ≤ 2e^{κσ/2}/(κσ)`
(`sum_exp_neg_abs_le_of_separated`). The proof compares each point with the integral over a
disjoint interval of length `σ`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## Exponential sums over separated points -/

/-- **Separated exponential sums.** -/
theorem sum_exp_neg_abs_le_of_separated {s : Finset ℝ} {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hsep : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → σ ≤ |y - y'|) (z : ℝ) :
    ∑ y ∈ s, Real.exp (-(κ * |z - y|)) ≤ 2 * Real.exp (κ * σ / 2) / (κ * σ) := by
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => Real.exp (-(κ * |z - t|)) := ⟨_, rfl⟩
  have hint : Integrable f := by
    rw [hf]; exact GaloisForLFunctions.HTGeometry.integrable_exp_neg_mul_abs_sub hκ z
  have hval : ∫ t, f t = 2 / κ := by
    rw [hf]; exact GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_abs_sub hκ z
  have hf0 : ∀ t, 0 ≤ f t := fun t => by rw [hf]; exact (Real.exp_pos _).le
  obtain ⟨C, hC⟩ : ∃ C, C = Real.exp (κ * σ / 2) / σ := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hpt : ∀ y ∈ s, Real.exp (-(κ * |z - y|)) ≤
      C * ∫ t in Ioo (y - σ / 2) (y + σ / 2), f t := by
    intro y _
    have hlow : ∀ t ∈ Ioo (y - σ / 2) (y + σ / 2),
        Real.exp (-(κ * |z - y|)) * Real.exp (-(κ * σ / 2)) ≤ f t := by
      intro t ht
      rw [hf, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : |y - t| ≤ σ / 2 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have h2 : |z - t| ≤ |z - y| + |y - t| := by
        calc |z - t| = |(z - y) + (y - t)| := by ring_nf
          _ ≤ |z - y| + |y - t| := abs_add_le _ _
      nlinarith
    have hmeas : ∫ _t in Ioo (y - σ / 2) (y + σ / 2),
        Real.exp (-(κ * |z - y|)) * Real.exp (-(κ * σ / 2)) =
        σ * (Real.exp (-(κ * |z - y|)) * Real.exp (-(κ * σ / 2))) := by
      rw [setIntegral_const, Real.volume_real_Ioo, smul_eq_mul, max_eq_left (by linarith)]
      ring_nf
    have h2 := setIntegral_mono_on (integrableOn_const measure_Ioo_lt_top.ne) hint.integrableOn
      measurableSet_Ioo hlow
    rw [hmeas] at h2
    have he : Real.exp (κ * σ / 2) * Real.exp (-(κ * σ / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-(κ * |z - y|))
        = C * (σ * (Real.exp (-(κ * |z - y|)) * Real.exp (-(κ * σ / 2)))) := by
          rw [hC, ← mul_assoc, div_mul_cancel₀ _ hσ.ne', mul_left_comm, he, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hC0
  have hdisj : (↑s : Set ℝ).Pairwise
      (Function.onFun Disjoint fun y => Ioo (y - σ / 2) (y + σ / 2)) := by
    intro y hy y' hy' hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro t ht ht'
    have h1 := hsep y hy y' hy' hne
    have h2 : |y - y'| < σ := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    linarith
  calc ∑ y ∈ s, Real.exp (-(κ * |z - y|))
      ≤ ∑ y ∈ s, C * ∫ t in Ioo (y - σ / 2) (y + σ / 2), f t := Finset.sum_le_sum hpt
    _ = C * ∫ t in ⋃ y ∈ s, Ioo (y - σ / 2) (y + σ / 2), f t := by
        rw [← Finset.mul_sum, integral_biUnion_finset s (fun y _ => measurableSet_Ioo) hdisj
          (fun y _ => hint.integrableOn)]
    _ ≤ C * ∫ t, f t :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hint (Eventually.of_forall hf0)) hC0
    _ = _ := by rw [hval, hC]; field_simp

/-! ## Amplitude against scale -/

/-- The spike scale `r_L = ‖P_L‖₂`. -/
def spikeScale (L : ℝ) : ℝ := Real.sqrt (∫ u, combSpike L u ^ 2)

/-- The amplitude constant `K = C₀ √(2π) e³/20`. -/
def spikeAmpConst : ℝ := riemannEnvelopeConst * Real.sqrt (2 * π) * Real.exp 3 / 20

theorem spikeScale_nonneg (L : ℝ) : 0 ≤ spikeScale L := Real.sqrt_nonneg _

theorem spikeScale_sq (L : ℝ) : spikeScale L ^ 2 = ∫ u, combSpike L u ^ 2 :=
  Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

theorem spikeAmpConst_pos : 0 < spikeAmpConst := by
  unfold spikeAmpConst
  have := riemannEnvelopeConst_pos
  have : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem spikeScale_pos {L : ℝ} (hL : 1 ≤ L) : 0 < spikeScale L := by
  have hq := integral_combSpike_sq_ge hL (by linarith [(edgeRate_ge hL).1])
  unfold spikeScale
  apply Real.sqrt_pos.mpr
  refine lt_of_lt_of_le ?_ hq
  have := kernelEnvelope_pos L
  have := edgeRate_pos L
  positivity

/-- **Amplitude against scale.** `A_L ≤ K e^L r_L`. -/
theorem spikeAmp_le_scale {L : ℝ} (hL : 1 ≤ L) :
    spikeAmp L ≤ spikeAmpConst * Real.exp L * spikeScale L := by
  have hY := (edgeRate_ge hL).1
  have hq := integral_combSpike_sq_ge hL (by linarith)
  rw [← spikeScale_sq] at hq
  have hC := riemannEnvelopeConst_pos
  have hE := kernelEnvelope_pos L
  have hr := spikeScale_nonneg L
  have ht := Real.exp_pos L
  apply le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (mul_nonneg spikeAmpConst_pos.le ht.le) hr)
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have he3 : Real.exp 3 ^ 2 * Real.exp (-6) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hY' : edgeRate L = 2 * π * Real.exp L ^ 2 := by
    unfold edgeRate; rw [← Real.exp_nat_mul]; ring_nf
  rw [hY'] at hq
  have h1 : 400 * Real.exp (-6) * kernelEnvelope L ^ 2 ≤
      spikeScale L ^ 2 * (2 * π * Real.exp L ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at hq; linarith
  unfold spikeAmp spikeAmpConst
  calc (riemannEnvelopeConst * kernelEnvelope L) ^ 2
      = riemannEnvelopeConst ^ 2 * kernelEnvelope L ^ 2 * (Real.exp 3 ^ 2 * Real.exp (-6)) := by
        rw [he3]; ring
    _ = riemannEnvelopeConst ^ 2 * Real.exp 3 ^ 2 / 400 *
          (400 * Real.exp (-6) * kernelEnvelope L ^ 2) := by ring
    _ ≤ riemannEnvelopeConst ^ 2 * Real.exp 3 ^ 2 / 400 *
          (spikeScale L ^ 2 * (2 * π * Real.exp L ^ 2)) := by gcongr
    _ = _ := by
        rw [show (riemannEnvelopeConst * Real.sqrt (2 * π) * Real.exp 3 / 20 * Real.exp L *
            spikeScale L) ^ 2 = riemannEnvelopeConst ^ 2 * Real.sqrt (2 * π) ^ 2 * Real.exp 3 ^ 2 *
            Real.exp L ^ 2 * spikeScale L ^ 2 / 400 by ring, hs]
        ring

/-! ## Same-side couplings -/

theorem spikeRate_mono {L L' : ℝ} (h : L ≤ L') : spikeRate L ≤ spikeRate L' := by
  unfold spikeRate edgeRate
  have := Real.exp_le_exp.mpr (show 2 * L ≤ 2 * L' by linarith)
  nlinarith [Real.pi_pos]

/-- `e^{−|d|}e^{−m|y − d|} ≤ e^{−y}e^{−κ|y − d|}` for `κ ≤ m − 1`. -/
theorem exp_neg_abs_mul_exp_le {d y m κ : ℝ} (hκ : κ ≤ m - 1) :
    Real.exp (-|d|) * Real.exp (-(m * |y - d|)) ≤ Real.exp (-y) * Real.exp (-(κ * |y - d|)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : y ≤ |d| + |y - d| := by
    calc y = d + (y - d) := by ring
      _ ≤ |d| + |y - d| := add_le_add (le_abs_self _) (le_abs_self _)
  nlinarith [abs_nonneg (y - d)]

theorem seven_le_exp_two_mul {L : ℝ} (hL : 1 ≤ L) : 7 ≤ Real.exp (2 * L) := by
  have he := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 2 ≤ Real.exp (2 * L) := Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- `A_L A_{L'}/(c + c') ≤ K² r r' e^{−|L − L'|}/π`. -/
theorem spikeAmp_mul_div_rate_le {L L' : ℝ} (hL : 1 ≤ L) (hL' : 1 ≤ L') :
    spikeAmp L * spikeAmp L' / (spikeRate L + spikeRate L') ≤
      spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * Real.exp (-|L - L'|) / π := by
  have hA := spikeAmp_le_scale hL
  have hA' := spikeAmp_le_scale hL'
  have hc0 := spikeRate_pos hL
  have hc0' := spikeRate_pos hL'
  have he1 := seven_le_exp_two_mul hL
  have he1' := seven_le_exp_two_mul hL'
  have hcc : π * (Real.exp (2 * L) + Real.exp (2 * L')) ≤ spikeRate L + spikeRate L' := by
    unfold spikeRate edgeRate; nlinarith [Real.pi_gt_three]
  have hmax : Real.exp L * Real.exp L' ≤
      (Real.exp (2 * L) + Real.exp (2 * L')) * Real.exp (-|L - L'|) := by
    rcases le_total L L' with h | h
    · rw [abs_of_nonpos (by linarith)]
      have : Real.exp L * Real.exp L' = Real.exp (2 * L') * Real.exp (-(-(L - L'))) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [this]
      nlinarith [Real.exp_pos (2 * L), Real.exp_pos (-(-(L - L')))]
    · rw [abs_of_nonneg (by linarith)]
      have : Real.exp L * Real.exp L' = Real.exp (2 * L) * Real.exp (-(L - L')) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [this]
      nlinarith [Real.exp_pos (2 * L'), Real.exp_pos (-(L - L'))]
  have hK := spikeAmpConst_pos
  have hr := spikeScale_nonneg L
  have hr' := spikeScale_nonneg L'
  rw [div_le_iff₀ (by linarith)]
  calc spikeAmp L * spikeAmp L'
      ≤ (spikeAmpConst * Real.exp L * spikeScale L) * (spikeAmpConst * Real.exp L' * spikeScale L') :=
        mul_le_mul hA hA' (spikeAmp_pos _).le (by positivity)
    _ = spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (Real.exp L * Real.exp L') := by ring
    _ ≤ spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
          ((Real.exp (2 * L) + Real.exp (2 * L')) * Real.exp (-|L - L'|)) := by gcongr
    _ = spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * Real.exp (-|L - L'|) / π *
          (π * (Real.exp (2 * L) + Real.exp (2 * L'))) := by
        field_simp
    _ ≤ _ := by gcongr

/-! ## Opposite-side couplings -/

/-- The prime weights `w_n = Λ(n)/√n` for `n ≥ 2`. -/
def spikePrimeWeight (n : ℕ) : ℝ := if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0

theorem spikePrimeWeight_nonneg (n : ℕ) : 0 ≤ spikePrimeWeight n := by
  unfold spikePrimeWeight
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_refl 0

/-- **The opposite-side prime sum.** -/
theorem sum_opposite_le {D m : ℝ} (hD : 2 ≤ D) (hm : 3 ≤ m) (N : ℕ) :
    ∑ n ∈ Finset.range N, spikePrimeWeight n *
        (if D ≤ Real.log n then Real.exp (-(m / 2 * (Real.log n - D))) else 0) ≤
      Real.exp (m * (D / 2)) * (logPowDecay ((m + 1) / 2) (edgeThreshold (D / 2)) -
        logPowPrimitive ((m + 1) / 2) (edgeThreshold (D / 2))) := by
  have hn₀ : 2 ≤ edgeThreshold (D / 2) := two_le_edgeThreshold (by linarith)
  have hpt : ∀ n ∈ Finset.range N, spikePrimeWeight n *
      (if D ≤ Real.log n then Real.exp (-(m / 2 * (Real.log n - D))) else 0) ≤
      (if edgeThreshold (D / 2) ≤ n then
        Real.exp (m * (D / 2)) * logPowDecay ((m + 1) / 2) n else 0) := by
    intro n _
    by_cases h : D ≤ Real.log n
    · rw [if_pos h]
      have hn1 : (1 : ℝ) < n := by
        by_contra hc; push Not at hc
        have : Real.log n ≤ 0 := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · rw [h0]; simp
          · exact Real.log_nonpos (Nat.cast_nonneg _) hc
        linarith
      have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
      have hge : edgeThreshold (D / 2) ≤ n := by
        unfold edgeThreshold
        apply Nat.ceil_le.mpr
        rw [show 2 * (D / 2) = D by ring]
        calc Real.exp D ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr h
          _ = n := Real.exp_log (by linarith)
      rw [if_pos hge]
      have h2n : 2 ≤ n := hn₀.trans hge
      unfold spikePrimeWeight
      rw [if_pos h2n]
      have hΛ : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
          Real.log n * Real.exp (-(1 / 2) * Real.log n) := by
        rw [div_eq_mul_one_div, inv_sqrt_natCast_eq hn0]
        exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.exp_pos _).le
      have he : Real.log n * Real.exp (-(1 / 2) * Real.log n) *
          Real.exp (-(m / 2 * (Real.log n - D))) =
          Real.exp (m * (D / 2)) * logPowDecay ((m + 1) / 2) n := by
        unfold logPowDecay
        rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
        congr 2; ring
      rw [← he]
      exact mul_le_mul_of_nonneg_right hΛ (Real.exp_pos _).le
    · rw [if_neg h, mul_zero]
      split_ifs with h2
      · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        exact mul_nonneg (Real.exp_pos _).le (logPowDecay_nonneg h1)
      · exact le_refl 0
  refine (Finset.sum_le_sum hpt).trans ?_
  have hfilter : (Finset.range N).filter (fun n => edgeThreshold (D / 2) ≤ n) =
      Finset.Ico (edgeThreshold (D / 2)) N := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [← Finset.sum_filter, hfilter, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_logPowDecay_le (by linarith) hn₀ N) (Real.exp_pos _).le

/-- The arithmetic of the opposite-side constant. -/
theorem opposite_arith {a b p c' S D x y : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hp : 3 ≤ p)
    (hc' : p * b ^ 4 ≤ c') (hS : p / 2 * a ^ 4 ≤ S) (hD : 0 ≤ D) (hxy : D + 2 ≤ x * y) :
    a ^ 2 * b ^ 2 * (2 / c') * ((D + 1) * (a * b)⁻¹ + a * b * ((D + 2) / S)) ≤
      2 * (x * a⁻¹) * (y * b⁻¹) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab0 : 0 < a * b := mul_pos ha0 hb0
  have hp0 : 0 < p := by linarith
  have hb4 : 0 < p * b ^ 4 := by positivity
  have hc0 : 0 < c' := lt_of_lt_of_le hb4 hc'
  have ha4 : 0 < p / 2 * a ^ 4 := by positivity
  have hS0 : 0 < S := lt_of_lt_of_le ha4 hS
  have hb2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha0.le hab 2
  -- first term
  have hT1 : a ^ 2 * b ^ 2 * (2 / c') * ((D + 1) * (a * b)⁻¹) ≤ 2 / p * (D + 1) * (a * b)⁻¹ := by
    have e1 : a ^ 2 * b ^ 2 * (2 / c') * ((D + 1) * (a * b)⁻¹) = 2 * (D + 1) * (a * b) / c' := by
      field_simp
    rw [e1, div_le_iff₀ hc0]
    have : 2 / p * (D + 1) * (a * b)⁻¹ * c' ≥ 2 / p * (D + 1) * (a * b)⁻¹ * (p * b ^ 4) :=
      mul_le_mul_of_nonneg_left hc' (by positivity)
    have e2 : 2 / p * (D + 1) * (a * b)⁻¹ * (p * b ^ 4) = 2 * (D + 1) * b ^ 3 * a⁻¹ := by
      field_simp
    have e3 : 2 * (D + 1) * (a * b) ≤ 2 * (D + 1) * b ^ 3 * a⁻¹ := by
      rw [show 2 * (D + 1) * b ^ 3 * a⁻¹ = 2 * (D + 1) * (b ^ 3 / a) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ ha0]; nlinarith
    linarith
  -- second term
  have hT2 : a ^ 2 * b ^ 2 * (2 / c') * (a * b * ((D + 2) / S)) ≤
      4 / p ^ 2 * (D + 2) * (a * b)⁻¹ := by
    have e1 : a ^ 2 * b ^ 2 * (2 / c') * (a * b * ((D + 2) / S)) =
        2 * (D + 2) * (a ^ 3 * b ^ 3) / (c' * S) := by
      field_simp
    rw [e1, div_le_iff₀ (mul_pos hc0 hS0)]
    have hcs : p * b ^ 4 * (p / 2 * a ^ 4) ≤ c' * S := mul_le_mul hc' hS ha4.le hc0.le
    have e2 : 4 / p ^ 2 * (D + 2) * (a * b)⁻¹ * (p * b ^ 4 * (p / 2 * a ^ 4)) =
        2 * (D + 2) * (a ^ 3 * b ^ 3) := by
      field_simp
      norm_num
    have : 4 / p ^ 2 * (D + 2) * (a * b)⁻¹ * (p * b ^ 4 * (p / 2 * a ^ 4)) ≤
        4 / p ^ 2 * (D + 2) * (a * b)⁻¹ * (c' * S) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    linarith
  have hsum : 2 / p * (D + 1) * (a * b)⁻¹ + 4 / p ^ 2 * (D + 2) * (a * b)⁻¹ ≤
      2 * (x * a⁻¹) * (y * b⁻¹) := by
    have hinv : 0 < (a * b)⁻¹ := inv_pos.mpr hab0
    have h1 : 2 / p ≤ 2 / 3 := by gcongr
    have h2 : 4 / p ^ 2 ≤ 4 / 9 := by
      have : (9 : ℝ) ≤ p ^ 2 := by nlinarith
      gcongr
    have e : 2 * (x * a⁻¹) * (y * b⁻¹) = 2 * (x * y) * (a * b)⁻¹ := by
      rw [mul_inv]; ring
    rw [e]
    have : 2 / p * (D + 1) + 4 / p ^ 2 * (D + 2) ≤ 2 * (x * y) := by
      have h3 : 2 / p * (D + 1) ≤ 2 / 3 * (D + 1) := mul_le_mul_of_nonneg_right h1 (by linarith)
      have h4 : 4 / p ^ 2 * (D + 2) ≤ 4 / 9 * (D + 2) := mul_le_mul_of_nonneg_right h2 (by linarith)
      nlinarith
    nlinarith
  rw [mul_add]
  linarith

/-- The opposite-side constant for `L ≤ L'`. -/
theorem opposite_const_le_of_le {L L' : ℝ} (hL : 1 ≤ L) (hLL : L ≤ L') :
    spikeAmp L * spikeAmp L' * (2 / max (spikeRate L) (spikeRate L')) *
      (Real.exp (min (spikeRate L) (spikeRate L') * ((L + L') / 2)) *
        (logPowDecay ((min (spikeRate L) (spikeRate L') + 1) / 2) (edgeThreshold ((L + L') / 2)) -
          logPowPrimitive ((min (spikeRate L) (spikeRate L') + 1) / 2)
            (edgeThreshold ((L + L') / 2)))) ≤
      spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
        (2 * ((L + 1) * Real.exp (-(L / 2))) * ((L' + 1) * Real.exp (-(L' / 2)))) := by
  have hL' : 1 ≤ L' := by linarith
  have hmono := spikeRate_mono hLL
  rw [min_eq_left hmono, max_eq_right hmono]
  obtain ⟨c, hc⟩ : ∃ c, c = spikeRate L := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = spikeRate L' := ⟨_, rfl⟩
  rw [← hc, ← hc']
  have hc1 : 1 < c := by rw [hc]; unfold spikeRate; linarith [(edgeRate_ge hL).1]
  obtain ⟨T, hT⟩ : ∃ T, T = Real.exp (c * ((L + L') / 2)) *
      (logPowDecay ((c + 1) / 2) (edgeThreshold ((L + L') / 2)) -
        logPowPrimitive ((c + 1) / 2) (edgeThreshold ((L + L') / 2))) := ⟨_, rfl⟩
  rw [← hT]
  have hThr := exp_mul_logPow_threshold_le (L := (L + L') / 2) (c := c) (by linarith) hc1
  rw [← hT] at hThr
  obtain ⟨S, hS⟩ : ∃ S, S = (c + 1) / 2 - 1 := ⟨_, rfl⟩
  rw [← hS] at hThr
  obtain ⟨a, ha⟩ : ∃ a, a = Real.exp (L / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.exp (L' / 2) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact Real.exp_pos _
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos _
  have ha1 : 1 ≤ a := by rw [ha]; exact Real.one_le_exp (by linarith)
  have hab : a ≤ b := by rw [ha, hb]; exact Real.exp_le_exp.mpr (by linarith)
  have heL : Real.exp L = a ^ 2 := by rw [ha, sq, ← Real.exp_add]; ring_nf
  have heL' : Real.exp L' = b ^ 2 := by rw [hb, sq, ← Real.exp_add]; ring_nf
  have he2L : Real.exp (2 * L) = a ^ 4 := by
    rw [show 2 * L = L + L by ring, Real.exp_add, heL]; ring
  have he2L' : Real.exp (2 * L') = b ^ 4 := by
    rw [show 2 * L' = L' + L' by ring, Real.exp_add, heL']; ring
  have hhalf : Real.exp ((L + L') / 2) = a * b := by
    rw [ha, hb, ← Real.exp_add]; ring_nf
  have hnhalf : Real.exp (-((L + L') / 2)) = (a * b)⁻¹ := by rw [Real.exp_neg, hhalf]
  have hna : Real.exp (-(L / 2)) = a⁻¹ := by rw [Real.exp_neg, ha]
  have hnb : Real.exp (-(L' / 2)) = b⁻¹ := by rw [Real.exp_neg, hb]
  rw [hnhalf, hhalf] at hThr
  have hcY : c = 2 * π * a ^ 4 - 9 / 2 := by rw [hc]; unfold spikeRate edgeRate; rw [he2L]
  have hcY' : c' = 2 * π * b ^ 4 - 9 / 2 := by rw [hc']; unfold spikeRate edgeRate; rw [he2L']
  have ha4 : 7 ≤ a ^ 4 := by rw [← he2L]; exact seven_le_exp_two_mul hL
  have hb4 : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha0.le hab 4
  have hπ := Real.pi_gt_three
  have hπa : π * 7 ≤ π * a ^ 4 := mul_le_mul_of_nonneg_left ha4 Real.pi_pos.le
  have hπb : π * 7 ≤ π * b ^ 4 := mul_le_mul_of_nonneg_left (ha4.trans hb4) Real.pi_pos.le
  have hc'b : π * b ^ 4 ≤ c' := by rw [hcY']; linarith
  have hSa : π / 2 * a ^ 4 ≤ S := by rw [hS, hcY]; linarith
  have hS1 : 1 ≤ S := by linarith
  -- the threshold bound, simplified
  have hT' : T ≤ (L + L' + 1) * (a * b)⁻¹ + a * b * ((L + L' + 2) / S) := by
    refine hThr.trans ?_
    have hSS : S ≤ S ^ 2 := by
      calc S = S * 1 := (mul_one S).symm
        _ ≤ S * S := mul_le_mul_of_nonneg_left hS1 (by linarith)
        _ = S ^ 2 := (sq S).symm
    have hq : 1 / S ^ 2 ≤ 1 / S := one_div_le_one_div_of_le (by linarith) hSS
    have e : 2 * ((L + L') / 2) + 1 = L + L' + 1 := by ring
    rw [e]
    have : (L + L' + 1) / S + 1 / S ^ 2 ≤ (L + L' + 2) / S := by
      rw [show (L + L' + 2) / S = (L + L' + 1) / S + 1 / S by ring]; linarith
    have hab0 : 0 ≤ a * b := by positivity
    have := mul_le_mul_of_nonneg_left this hab0
    linarith
  have hT0 : 0 ≤ T := by
    rw [hT]
    have hn := two_le_edgeThreshold (L := (L + L') / 2) (by linarith)
    have h1 : (1 : ℝ) ≤ edgeThreshold ((L + L') / 2) := by exact_mod_cast (show 1 ≤ _ by omega)
    have := logPowDecay_nonneg (s := (c + 1) / 2) h1
    have := logPowPrimitive_nonpos (s := (c + 1) / 2) (by linarith) h1
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hA := spikeAmp_le_scale hL
  have hA' := spikeAmp_le_scale hL'
  rw [heL] at hA
  rw [heL'] at hA'
  have hK := spikeAmpConst_pos
  have hr := spikeScale_nonneg L
  have hr' := spikeScale_nonneg L'
  have hc'0 : 0 < c' := by linarith
  have hAA : spikeAmp L * spikeAmp L' ≤
      spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (a ^ 2 * b ^ 2) := by
    calc spikeAmp L * spikeAmp L'
        ≤ (spikeAmpConst * a ^ 2 * spikeScale L) * (spikeAmpConst * b ^ 2 * spikeScale L') :=
          mul_le_mul hA hA' (spikeAmp_pos _).le (by positivity)
      _ = _ := by ring
  have hxy : L + L' + 2 ≤ (L + 1) * (L' + 1) := by
    have h := mul_le_mul hL hL' zero_le_one (by linarith : (0 : ℝ) ≤ L)
    linarith
  have harith := opposite_arith (p := π) (c' := c') (S := S) (D := L + L') ha1 hab hπ.le hc'b hSa
    (by linarith) hxy
  rw [hna, hnb]
  have hcoef : 0 ≤ 2 / c' := by positivity
  calc spikeAmp L * spikeAmp L' * (2 / c') * T
      ≤ (spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (a ^ 2 * b ^ 2)) * (2 / c') *
          ((L + L' + 1) * (a * b)⁻¹ + a * b * ((L + L' + 2) / S)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hAA hcoef) hT' hT0 (by positivity)
    _ = spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
          (a ^ 2 * b ^ 2 * (2 / c') * ((L + L' + 1) * (a * b)⁻¹ + a * b * ((L + L' + 2) / S))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left harith (by positivity)

/-- The opposite-side constant. -/
theorem opposite_const_le {L L' : ℝ} (hL : 1 ≤ L) (hL' : 1 ≤ L') :
    spikeAmp L * spikeAmp L' * (2 / max (spikeRate L) (spikeRate L')) *
      (Real.exp (min (spikeRate L) (spikeRate L') * ((L + L') / 2)) *
        (logPowDecay ((min (spikeRate L) (spikeRate L') + 1) / 2) (edgeThreshold ((L + L') / 2)) -
          logPowPrimitive ((min (spikeRate L) (spikeRate L') + 1) / 2)
            (edgeThreshold ((L + L') / 2)))) ≤
      spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
        (2 * ((L + 1) * Real.exp (-(L / 2))) * ((L' + 1) * Real.exp (-(L' / 2)))) := by
  rcases le_total L L' with h | h
  · exact opposite_const_le_of_le hL h
  · have := opposite_const_le_of_le hL' h
    rw [min_comm, max_comm, add_comm L L']
    calc _ = spikeAmp L' * spikeAmp L * (2 / max (spikeRate L') (spikeRate L)) *
          (Real.exp (min (spikeRate L') (spikeRate L) * ((L' + L) / 2)) *
            (logPowDecay ((min (spikeRate L') (spikeRate L) + 1) / 2) (edgeThreshold ((L' + L) / 2)) -
              logPowPrimitive ((min (spikeRate L') (spikeRate L) + 1) / 2)
                (edgeThreshold ((L' + L) / 2)))) := by ring
      _ ≤ _ := this
      _ = _ := by ring

/-! ## The prime sum of one pair -/

/-- **Prime sum of a pair of spikes.** -/
theorem sum_prime_combSpike_lag_le {L₀ L L' : ℝ} (hL₀ : 1 ≤ L₀) (hL : L₀ ≤ L) (hL' : L₀ ≤ L')
    (N : ℕ) :
    ∑ n ∈ Finset.range N, spikePrimeWeight n * ∫ u, combSpike L u * combSpike L' (u - Real.log n) ≤
      spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
        (1 / π * ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
            (Real.exp (-((spikeRate L₀ - 1) * |Real.log n - (L - L')|)) +
              Real.exp (-((spikeRate L₀ - 1) * |Real.log n + (L - L')|))) +
          2 * ((L + 1) * Real.exp (-(L / 2))) * ((L' + 1) * Real.exp (-(L' / 2)))) := by
  have h1L : 1 ≤ L := hL₀.trans hL
  have h1L' : 1 ≤ L' := hL₀.trans hL'
  set m := min (spikeRate L) (spikeRate L') with hm
  set M := max (spikeRate L) (spikeRate L') with hM
  set κ := spikeRate L₀ - 1 with hκ
  have hκm : κ ≤ m - 1 := by
    rw [hκ, hm]; linarith [le_min (spikeRate_mono hL) (spikeRate_mono hL')]
  have hc0 := spikeRate_pos h1L
  have hc0' := spikeRate_pos h1L'
  have hcc : 0 < spikeRate L + spikeRate L' := by linarith
  set B := spikeAmp L * spikeAmp L' with hB
  have hB0 : 0 < B := mul_pos (spikeAmp_pos _) (spikeAmp_pos _)
  -- termwise bound from the lag estimate
  have hterm : ∀ n ∈ Finset.range N,
      spikePrimeWeight n * ∫ u, combSpike L u * combSpike L' (u - Real.log n) ≤
        B / (spikeRate L + spikeRate L') * (spikePrimeWeight n *
            (Real.exp (-(m * |Real.log n - (L - L')|)) + Real.exp (-(m * |Real.log n + (L - L')|)))) +
          B * (2 / M) * (spikePrimeWeight n *
            (if L + L' ≤ Real.log n then Real.exp (-(m / 2 * (Real.log n - (L + L')))) else 0)) := by
    intro n _
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hlag := integral_combSpike_lag_le (x := Real.log n) h1L h1L' hlog
    rw [← hm, ← hM, ← hB] at hlag
    have hw := spikePrimeWeight_nonneg n
    calc spikePrimeWeight n * ∫ u, combSpike L u * combSpike L' (u - Real.log n)
        ≤ spikePrimeWeight n * (B * ((Real.exp (-(m * |Real.log n - (L - L')|)) +
            Real.exp (-(m * |Real.log n + (L - L')|))) / (spikeRate L + spikeRate L') +
            if L + L' ≤ Real.log n then 2 / M * Real.exp (-(m / 2 * (Real.log n - (L + L'))))
            else 0)) := mul_le_mul_of_nonneg_left hlag hw
      _ = _ := by split_ifs <;> ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- same side
  have hsame : B / (spikeRate L + spikeRate L') * ∑ n ∈ Finset.range N, spikePrimeWeight n *
      (Real.exp (-(m * |Real.log n - (L - L')|)) + Real.exp (-(m * |Real.log n + (L - L')|))) ≤
      spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (1 / π *
        ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
          (Real.exp (-(κ * |Real.log n - (L - L')|)) + Real.exp (-(κ * |Real.log n + (L - L')|)))) := by
    have hfac := spikeAmp_mul_div_rate_le h1L h1L'
    rw [← hB] at hfac
    have hS0 : 0 ≤ ∑ n ∈ Finset.range N, spikePrimeWeight n *
        (Real.exp (-(m * |Real.log n - (L - L')|)) + Real.exp (-(m * |Real.log n + (L - L')|))) :=
      Finset.sum_nonneg fun n _ => mul_nonneg (spikePrimeWeight_nonneg n) (by positivity)
    have hgain : Real.exp (-|L - L'|) * ∑ n ∈ Finset.range N, spikePrimeWeight n *
        (Real.exp (-(m * |Real.log n - (L - L')|)) + Real.exp (-(m * |Real.log n + (L - L')|))) ≤
        ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
          (Real.exp (-(κ * |Real.log n - (L - L')|)) +
            Real.exp (-(κ * |Real.log n + (L - L')|))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n _ => ?_
      have e1 := exp_neg_abs_mul_exp_le (d := L - L') (y := Real.log n) hκm
      have e2 := exp_neg_abs_mul_exp_le (d := -(L - L')) (y := Real.log n) hκm
      rw [abs_neg, sub_neg_eq_add] at e2
      have hw := spikePrimeWeight_nonneg n
      calc Real.exp (-|L - L'|) * (spikePrimeWeight n *
            (Real.exp (-(m * |Real.log n - (L - L')|)) + Real.exp (-(m * |Real.log n + (L - L')|))))
          = spikePrimeWeight n * (Real.exp (-|L - L'|) * Real.exp (-(m * |Real.log n - (L - L')|)) +
              Real.exp (-|L - L'|) * Real.exp (-(m * |Real.log n + (L - L')|))) := by ring
        _ ≤ spikePrimeWeight n * (Real.exp (-Real.log n) * Real.exp (-(κ * |Real.log n - (L - L')|)) +
              Real.exp (-Real.log n) * Real.exp (-(κ * |Real.log n + (L - L')|))) := by
            gcongr
        _ = _ := by ring
    calc B / (spikeRate L + spikeRate L') * ∑ n ∈ Finset.range N, spikePrimeWeight n *
          (Real.exp (-(m * |Real.log n - (L - L')|)) + Real.exp (-(m * |Real.log n + (L - L')|)))
        ≤ spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * Real.exp (-|L - L'|) / π *
            ∑ n ∈ Finset.range N, spikePrimeWeight n *
              (Real.exp (-(m * |Real.log n - (L - L')|)) +
                Real.exp (-(m * |Real.log n + (L - L')|))) :=
          mul_le_mul_of_nonneg_right hfac hS0
      _ = spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (1 / π) *
            (Real.exp (-|L - L'|) * ∑ n ∈ Finset.range N, spikePrimeWeight n *
              (Real.exp (-(m * |Real.log n - (L - L')|)) +
                Real.exp (-(m * |Real.log n + (L - L')|)))) := by ring
      _ ≤ spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (1 / π) *
            ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
              (Real.exp (-(κ * |Real.log n - (L - L')|)) +
                Real.exp (-(κ * |Real.log n + (L - L')|))) := by
          have : 0 ≤ spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (1 / π) := by
            have := spikeScale_nonneg L; have := spikeScale_nonneg L'; positivity
          exact mul_le_mul_of_nonneg_left hgain this
      _ = _ := by ring
  -- opposite sides
  have hopp : B * (2 / M) * ∑ n ∈ Finset.range N, spikePrimeWeight n *
      (if L + L' ≤ Real.log n then Real.exp (-(m / 2 * (Real.log n - (L + L')))) else 0) ≤
      spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
        (2 * ((L + 1) * Real.exp (-(L / 2))) * ((L' + 1) * Real.exp (-(L' / 2)))) := by
    have hm3 : 3 ≤ m := by
      rw [hm]
      have h1 := (edgeRate_ge h1L).1
      have h2 := (edgeRate_ge h1L').1
      unfold spikeRate; exact le_min (by linarith) (by linarith)
    have hsum := sum_opposite_le (D := L + L') (m := m) (by linarith) hm3 N
    have hconst := opposite_const_le h1L h1L'
    rw [← hm, ← hM, ← hB] at hconst
    have hM0 : 0 < M := lt_max_of_lt_left hc0
    calc B * (2 / M) * ∑ n ∈ Finset.range N, spikePrimeWeight n *
          (if L + L' ≤ Real.log n then Real.exp (-(m / 2 * (Real.log n - (L + L')))) else 0)
        ≤ B * (2 / M) * (Real.exp (m * ((L + L') / 2)) *
            (logPowDecay ((m + 1) / 2) (edgeThreshold ((L + L') / 2)) -
              logPowPrimitive ((m + 1) / 2) (edgeThreshold ((L + L') / 2)))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := hconst
  calc B / (spikeRate L + spikeRate L') * ∑ n ∈ Finset.range N, spikePrimeWeight n *
        (Real.exp (-(m * |Real.log n - (L - L')|)) + Real.exp (-(m * |Real.log n + (L - L')|))) +
      B * (2 / M) * ∑ n ∈ Finset.range N, spikePrimeWeight n *
        (if L + L' ≤ Real.log n then Real.exp (-(m / 2 * (Real.log n - (L + L')))) else 0)
      ≤ spikeAmpConst ^ 2 * spikeScale L * spikeScale L' * (1 / π *
          ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
            (Real.exp (-(κ * |Real.log n - (L - L')|)) + Real.exp (-(κ * |Real.log n + (L - L')|)))) +
        spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
          (2 * ((L + 1) * Real.exp (-(L / 2))) * ((L' + 1) * Real.exp (-(L' / 2)))) :=
        add_le_add hsame hopp
    _ = _ := by ring

end

end RHTower
