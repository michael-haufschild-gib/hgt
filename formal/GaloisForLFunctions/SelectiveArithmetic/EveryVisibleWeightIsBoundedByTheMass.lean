import GaloisForLFunctions.SelectiveArithmetic.TheSignIsSquareRootCancellationOfTheRieszMean
import GaloisForLFunctions.RHTower.MarkovResolventFaithfulnessAndContinuumSignChangePBAP

/-!
# Every visible weight is bounded by the mass

The feasible set of a conductor at an aperture lies between an `ℓ¹` ball and a box, both of the
size of the mass.

* **The box law of a conductor** (`exists_abs_weight_le_of_feasible`). There is an absolute
  constant `C` such that every system feasible for the conductor `q` at aperture `a` satisfies
  `|w(n)| ≤ √n (log q + log(1 + 4n) + C)` at every `n ≥ 2` with `½ log n + 1/(4n) ≤ a`.
  The test is a pair of narrow bumps at distance `log n`: its only lags are `0` and `log n`, so
  the single contact `n` is isolated; the archimedean energy of a bump of width `r` is
  `log(1/r) + O(1)` times its mass.
* **An `ℓ¹` ball is feasible** (`feasible_of_sum_abs_le`): if
  `A₀ + 2 Σ_{n ≤ e^{2a}} |w(n)| n^{−1/2} ≤ log q`, the system is feasible at aperture `a`.
* **Below the first contact every system is feasible or none**
  (`feasible_iff_of_lt_half_log_two`): for `2a < log 2` feasibility does not depend on the
  weights.

So selectivity starts at the first contact, the aperture `½ log 2`: there the weight at `2` is
confined to an interval of half-length between `(log q − A₀)/√2` and
`√2 (log q + log(1/ε) + C)` at aperture `½ log 2 + ε`. A single weight may be as large as
`√n` times the mass, far beyond `Λ(n)`; what the ladder bounds beyond the trivial aperture is the
Riesz mean of all contacts together (`exists_riesz_le_of_feasible`).
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ

/-! ### A narrow bump -/

/-- The correlation of the cutoff of `[−r, r]` vanishes at lags of size at least `2r`. -/
theorem packetAutocorr_cutoff_eq_zero {r δ : ℝ} (hδ : 0 < δ) {z : ℝ} (hz : 2 * r ≤ |z|) :
    packetAutocorr (cutoff r δ) z = 0 := by
  have h0 : (fun u => cutoff r δ u * cutoff r δ (u + z)) = fun _ => (0 : ℝ) := by
    funext u
    by_contra hne
    have h1 := abs_lt.mp (abs_lt_of_cutoff_ne_zero hδ (left_ne_zero_of_mul hne))
    have h2 := abs_lt.mp (abs_lt_of_cutoff_ne_zero hδ (right_ne_zero_of_mul hne))
    have : |z| < 2 * r := abs_lt.mpr ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
    linarith
  rw [packetAutocorr, h0, integral_zero]

/-- A continuous function bounded by `K` and vanishing off `[−a, a]` has square integral at most
`K² · 2a`. -/
theorem integral_sq_le_of_abs_le {g : ℝ → ℝ} (hg : Continuous g) {a K : ℝ} (ha : 0 ≤ a)
    (hb : ∀ u, |g u| ≤ K) (h0 : ∀ u, a < |u| → g u = 0) : ∫ u, g u ^ 2 ≤ K ^ 2 * (2 * a) := by
  have hzero : ∀ u, u ∉ Set.Icc (-a) a → g u ^ 2 = 0 := fun u hu => by
    have : a < |u| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    rw [h0 u this]
    norm_num
  have hconst : ∫ _u in Set.Icc (-a) a, K ^ 2 = K ^ 2 * (2 * a) := by
    rw [setIntegral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← hconst]
  refine setIntegral_mono_on (hg.pow 2).integrableOn_Icc
    (continuous_const.integrableOn_Icc) measurableSet_Icc fun u _ => ?_
  calc g u ^ 2 = |g u| ^ 2 := (sq_abs _).symm
    _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb u) 2

/-! ### The pair of bumps at a distance -/

/-- Two bumps of half-width `r` at the points `∓h`, with relative sign `s`. -/
def twoBump (s h r u : ℝ) : ℝ := cutoff r (r / 2) (u + h) + s * cutoff r (r / 2) (u - h)

theorem contDiff_twoBump (s h r : ℝ) : ContDiff ℝ 3 (twoBump s h r) :=
  ((contDiff_cutoff r (r / 2)).comp (contDiff_id.add contDiff_const)).add
    (contDiff_const.mul ((contDiff_cutoff r (r / 2)).comp (contDiff_id.sub contDiff_const)))

theorem twoBump_eq_zero {s h r a : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (ha : h + r ≤ a) {u : ℝ}
    (hu : a ≤ |u|) : twoBump s h r u = 0 := by
  have hδ : 0 < r / 2 := by positivity
  have h1 : r ≤ |u + h| := by
    rcases le_abs.mp hu with h' | h'
    · exact le_abs.mpr (Or.inl (by linarith))
    · exact le_abs.mpr (Or.inr (by linarith))
  have h2 : r ≤ |u - h| := by
    rcases le_abs.mp hu with h' | h'
    · exact le_abs.mpr (Or.inl (by linarith))
    · exact le_abs.mpr (Or.inr (by linarith))
  rw [twoBump, cutoff_eq_zero hδ h1, cutoff_eq_zero hδ h2]
  ring

/-- **The correlation of a pair of bumps**: `(1 + s²) Φ(y) + s (Φ(y − 2h) + Φ(y + 2h))`, with `Φ`
the correlation of one bump. -/
theorem packetAutocorr_twoBump (s h : ℝ) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    packetAutocorr (twoBump s h r) y =
      (1 + s * s) * packetAutocorr (cutoff r (r / 2)) y +
        s * (packetAutocorr (cutoff r (r / 2)) (y - 2 * h) +
          packetAutocorr (cutoff r (r / 2)) (y + 2 * h)) := by
  have hδ : 0 < r / 2 := by positivity
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ, b = cutoff r (r / 2) := ⟨_, rfl⟩
  have hI : ∀ z : ℝ, Integrable fun u => b u * b (u + z) := fun z => by
    rw [hb]
    exact integrable_cutoff_mul hδ z
  have hpt : ∀ u : ℝ, twoBump s h r u * twoBump s h r (u + y) =
      b (u + h) * b (u + h + y) + s * (b (u + h) * b (u + h + (y - 2 * h))) +
        s * (b (u - h) * b (u - h + (y + 2 * h))) + s * s * (b (u - h) * b (u - h + y)) := by
    intro u
    have e1 : u + h + y = u + y + h := by ring
    have e2 : u + h + (y - 2 * h) = u + y - h := by ring
    have e3 : u - h + (y + 2 * h) = u + y + h := by ring
    have e4 : u - h + y = u + y - h := by ring
    rw [e1, e2, e3, e4, twoBump, twoBump, ← hb]
    ring
  have hi1 : Integrable fun u => b (u + h) * b (u + h + y) := (hI y).comp_add_right h
  have hi2 : Integrable fun u => b (u + h) * b (u + h + (y - 2 * h)) :=
    (hI (y - 2 * h)).comp_add_right h
  have hi3 : Integrable fun u => b (u - h) * b (u - h + (y + 2 * h)) :=
    (hI (y + 2 * h)).comp_sub_right h
  have hi4 : Integrable fun u => b (u - h) * b (u - h + y) := (hI y).comp_sub_right h
  have ht1 : ∫ u, b (u + h) * b (u + h + y) = packetAutocorr b y :=
    integral_add_right_eq_self (fun u => b u * b (u + y)) h
  have ht2 : ∫ u, b (u + h) * b (u + h + (y - 2 * h)) = packetAutocorr b (y - 2 * h) :=
    integral_add_right_eq_self (fun u => b u * b (u + (y - 2 * h))) h
  have ht3 : ∫ u, b (u - h) * b (u - h + (y + 2 * h)) = packetAutocorr b (y + 2 * h) :=
    integral_sub_right_eq_self (fun u => b u * b (u + (y + 2 * h))) h
  have ht4 : ∫ u, b (u - h) * b (u - h + y) = packetAutocorr b y :=
    integral_sub_right_eq_self (fun u => b u * b (u + y)) h
  rw [← hb]
  calc packetAutocorr (twoBump s h r) y
      = ∫ u, (b (u + h) * b (u + h + y) + s * (b (u + h) * b (u + h + (y - 2 * h))) +
          s * (b (u - h) * b (u - h + (y + 2 * h))) +
          s * s * (b (u - h) * b (u - h + y))) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ u, b (u + h) * b (u + h + y)) + s * (∫ u, b (u + h) * b (u + h + (y - 2 * h))) +
          s * (∫ u, b (u - h) * b (u - h + (y + 2 * h))) +
          s * s * ∫ u, b (u - h) * b (u - h + y) := by
        have hA : Integrable fun u => b (u + h) * b (u + h + y) +
            s * (b (u + h) * b (u + h + (y - 2 * h))) := hi1.add (hi2.const_mul s)
        have hB : Integrable fun u => b (u + h) * b (u + h + y) +
            s * (b (u + h) * b (u + h + (y - 2 * h))) +
            s * (b (u - h) * b (u - h + (y + 2 * h))) := hA.add (hi3.const_mul s)
        rw [integral_add hB (hi4.const_mul (s * s)), integral_add hA (hi3.const_mul s),
          integral_add hi1 (hi2.const_mul s), integral_const_mul, integral_const_mul,
          integral_const_mul]
    _ = _ := by
        rw [ht1, ht2, ht3, ht4]
        ring

/-- The derivative energy of a pair of bumps is at most `128 S²/r`. -/
theorem integral_deriv_twoBump_sq_le {S : ℝ} (hS : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S)
    {s : ℝ} (hs : s * s = 1) (h : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ u, deriv (twoBump s h r) u ^ 2 ≤ 128 * S ^ 2 / r := by
  have hδ : 0 < r / 2 := by positivity
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ, b = cutoff r (r / 2) := ⟨_, rfl⟩
  have hbd : ∀ x : ℝ, HasDerivAt b (deriv b x) x := fun x => by
    rw [hb]
    exact ((contDiff_cutoff r (r / 2)).differentiable (by norm_num) x).hasDerivAt
  have hdc : Continuous (deriv b) := by
    rw [hb]
    exact (contDiff_cutoff r (r / 2)).continuous_deriv (by norm_num)
  have hK : ∀ x, |deriv b x| ≤ 4 * S / r := fun x => by
    have h1 := abs_deriv_cutoff_le hS hδ r x
    rw [hb]
    have e : 2 * S / (r / 2) = 4 * S / r := by
      field_simp
      ring
    rwa [e] at h1
  have hd0 : ∀ u, r < |u| → deriv b u = 0 := fun u hu => by
    rw [hb]
    exact deriv_eq_zero_of_abs_gt (fun v hv => cutoff_eq_zero hδ hv) hu
  have hb2 : ∫ u, deriv b u ^ 2 ≤ (4 * S / r) ^ 2 * (2 * r) :=
    integral_sq_le_of_abs_le hdc hr.le hK hd0
  have hderiv : ∀ u, deriv (twoBump s h r) u = deriv b (u + h) + s * deriv b (u - h) := by
    intro u
    have h1 : HasDerivAt (fun v => b (v + h)) (deriv b (u + h)) u :=
      (hbd (u + h)).comp_add_const u h
    have h2 : HasDerivAt (fun v => b (v - h)) (deriv b (u - h)) u :=
      (hbd (u - h)).comp_sub_const u h
    have e : twoBump s h r = (fun v => b (v + h)) + fun v => s * b (v - h) := by
      funext v
      simp only [Pi.add_apply, twoBump, hb]
    rw [e]
    exact (h1.add (h2.const_mul s)).deriv
  have hsqI : Integrable fun u => deriv b u ^ 2 := by
    refine (hdc.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun u hu => ?_)
    have : r < |u| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h' | h'
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h')
    show deriv b u ^ 2 = 0
    rw [hd0 u this]
    norm_num
  have hi1 : Integrable fun u => deriv b (u + h) ^ 2 := hsqI.comp_add_right h
  have hi2 : Integrable fun u => deriv b (u - h) ^ 2 := hsqI.comp_sub_right h
  have ht1 : ∫ u, deriv b (u + h) ^ 2 = ∫ u, deriv b u ^ 2 :=
    integral_add_right_eq_self (fun u => deriv b u ^ 2) h
  have ht2 : ∫ u, deriv b (u - h) ^ 2 = ∫ u, deriv b u ^ 2 :=
    integral_sub_right_eq_self (fun u => deriv b u ^ 2) h
  have hle : ∫ u, deriv (twoBump s h r) u ^ 2 ≤
      ∫ u, (2 * deriv b (u + h) ^ 2 + 2 * deriv b (u - h) ^ 2) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
      ((hi1.const_mul 2).add (hi2.const_mul 2)) (Eventually.of_forall fun u => ?_)
    show deriv (twoBump s h r) u ^ 2 ≤ 2 * deriv b (u + h) ^ 2 + 2 * deriv b (u - h) ^ 2
    rw [hderiv]
    have e : (deriv b (u + h) + s * deriv b (u - h)) ^ 2 =
        deriv b (u + h) ^ 2 + 2 * s * (deriv b (u + h) * deriv b (u - h)) +
          deriv b (u - h) ^ 2 := by
      linear_combination (deriv b (u - h) ^ 2) * hs
    rw [e]
    have hs1 : -1 ≤ s ∧ s ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (s - 1), sq_nonneg (s + 1)]
    nlinarith [sq_nonneg (deriv b (u + h) - s * deriv b (u - h)),
      sq_nonneg (deriv b (u + h) + s * deriv b (u - h))]
  rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul, integral_const_mul,
    ht1, ht2] at hle
  have e : 4 * ((4 * S / r) ^ 2 * (2 * r)) = 128 * S ^ 2 / r := by
    field_simp
    ring
  linarith

/-! ### The box law -/

/-- `|log m − log n| ≥ 1/(2n)` for distinct positive integers `m`, `n`. -/
theorem abs_log_sub_log_ge {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    1 / (2 * (n : ℝ)) ≤ |Real.log m - Real.log n| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · -- `m < n`: `log n − log m ≥ 1 − m/n ≥ 1/n`
    have h1 := Real.log_le_sub_one_of_pos (div_pos hm0 hn0)
    rw [Real.log_div hm0.ne' hn0.ne'] at h1
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
    have h2 : (m : ℝ) / n ≤ 1 - 1 / n := by
      rw [div_le_iff₀ hn0]
      have : (1 - 1 / (n : ℝ)) * n = n - 1 := by field_simp
      linarith
    have h3 : 1 / (2 * (n : ℝ)) ≤ 1 / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      linarith
    exact le_trans (by linarith) (neg_le_abs _)
  · -- `m > n`: `log m − log n ≥ 1 − n/m ≥ 1/(n + 1)`
    have h1 := Real.log_le_sub_one_of_pos (div_pos hn0 hm0)
    rw [Real.log_div hn0.ne' hm0.ne'] at h1
    have hmn' : (n : ℝ) + 1 ≤ m := by exact_mod_cast hgt
    have h2 : (n : ℝ) / m ≤ 1 - 1 / (2 * n) := by
      rw [div_le_iff₀ hm0]
      have e : (1 - 1 / (2 * (n : ℝ))) * m = m - m / (2 * n) := by ring
      rw [e]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h4 : (m : ℝ) / (2 * n) ≤ m - n := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hmn' (by linarith : (0 : ℝ) ≤ 2 * n - 1)]
      linarith
    exact le_trans (by linarith) (le_abs_self _)

/-- **The box law of a conductor.** There is an absolute constant `C` such that every system
feasible for the conductor `q` at aperture `a` satisfies
`|w(n)| ≤ √n (log q + log(1 + 4n) + C)` at every `n ≥ 2` with `½ log n + 1/(4n) ≤ a`. -/
theorem exists_abs_weight_le_of_feasible :
    ∃ C : ℝ, ∀ {q a : ℝ} {w : ℕ → ℝ} {n : ℕ}, 2 ≤ n →
      Real.log n / 2 + 1 / (4 * (n : ℝ)) ≤ a → Feasible q a w →
      |w n| ≤ Real.sqrt n * (Real.log q + Real.log (1 + 4 * (n : ℝ)) + C) := by
  obtain ⟨S, -, hS⟩ := exists_abs_deriv_smoothTransition_le
  refine ⟨5 + 64 * S ^ 2, fun {q a w n} hn ha hfe => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / (4 * (n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = Real.log n / 2 := ⟨_, rfl⟩
  rw [← hr, ← hh] at ha
  have hr0 : 0 < r := by rw [hr]; positivity
  have hδ : 0 < r / 2 := by positivity
  have hr8 : r ≤ 1 / 8 := by
    rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh0 : 0 ≤ h := by rw [hh]; linarith
  have hrh : 2 * r ≤ 2 * h := by rw [hh]; linarith
  have h1r : 1 / r = 4 * (n : ℝ) := by rw [hr]; field_simp
  obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ₀ : ℝ, Φ₀ = packetAutocorr (cutoff r (r / 2)) 0 := ⟨_, rfl⟩
  have hΦr : r ≤ Φ₀ := by
    have := packetAutocorr_cutoff_ge (a := r) hδ (le_refl (0 : ℝ))
    rw [hΦ₀]
    linarith
  have hΦpos : 0 < Φ₀ := lt_of_lt_of_le hr0 hΦr
  -- the bound for each relative sign
  have key : ∀ s : ℝ, s * s = 1 →
      s * w n ≤ Real.sqrt n * (Real.log q + Real.log (1 + 4 * (n : ℝ)) + (5 + 64 * S ^ 2)) := by
    intro s hs
    have hf := contDiff_twoBump s h r
    have h0 : ∀ u, a ≤ |u| → twoBump s h r u = 0 := fun u hu =>
      twoBump_eq_zero hr0 hh0 ha hu
    have hpos := hfe _ (contDiff_ofReal_packet (hf.of_le (by norm_num)))
      (tsupport_ofReal_subset_of_eq_zero h0)
    have hup := systemForm_le_of_packet_scaled hr0 hf h0 w q
    -- the mass
    have hmass : ∫ u, twoBump s h r u ^ 2 = 2 * Φ₀ := by
      have hA := packetAutocorr_twoBump s h hr0 0
      rw [packetAutocorr_cutoff_eq_zero hδ (z := 0 - 2 * h)
          (by rw [zero_sub, abs_neg, abs_of_nonneg (by linarith)]; exact hrh),
        packetAutocorr_cutoff_eq_zero hδ (z := 0 + 2 * h)
          (by rw [zero_add, abs_of_nonneg (by linarith)]; exact hrh), hs, ← hΦ₀] at hA
      have e : packetAutocorr (twoBump s h r) 0 = ∫ u, twoBump s h r u ^ 2 := by
        rw [packetAutocorr]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show twoBump s h r u * twoBump s h r (u + 0) = twoBump s h r u ^ 2
        rw [add_zero, sq]
      rw [← e, hA]
      ring
    -- the derivative energy at the scale of the bumps
    have hD := integral_deriv_twoBump_sq_le hS hs h hr0
    have hD' : r ^ 2 * (∫ u, deriv (twoBump s h r) u ^ 2) ≤ 128 * S ^ 2 * Φ₀ := by
      have h1 := mul_le_mul_of_nonneg_left hD (sq_nonneg r)
      have e : r ^ 2 * (128 * S ^ 2 / r) = 128 * S ^ 2 * r := by
        field_simp
      rw [e] at h1
      have h2 : 128 * S ^ 2 * r ≤ 128 * S ^ 2 * Φ₀ :=
        mul_le_mul_of_nonneg_left hΦr (by positivity)
      linarith
    -- the contact form: the single contact `n`
    have hcontact : contactForm w (fun u => (twoBump s h r u : ℂ)) ⌊Real.exp (2 * a)⌋₊ =
        w n / Real.sqrt n * (2 * (s * Φ₀)) := by
      have hnN : n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ := by
        rw [Finset.mem_Icc]
        refine ⟨hn, Nat.le_floor ?_⟩
        have h1 : Real.log n ≤ 2 * a := by rw [hh] at ha; linarith
        calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
          _ ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr h1
      rw [contactForm_packet, Finset.sum_eq_single n]
      · -- the lag `log n`
        have hA := packetAutocorr_twoBump s h hr0 (Real.log n)
        have e1 : Real.log n - 2 * h = 0 := by rw [hh]; ring
        have e2 : Real.log n + 2 * h = 2 * Real.log n := by rw [hh]; ring
        rw [e1, e2, ← hΦ₀,
          packetAutocorr_cutoff_eq_zero hδ (z := Real.log n)
            (by rw [abs_of_nonneg (by linarith)]; linarith),
          packetAutocorr_cutoff_eq_zero hδ (z := 2 * Real.log n)
            (by rw [abs_of_nonneg (by linarith)]; linarith)] at hA
        rw [hA]
        ring
      · -- every other contact is invisible
        intro m hm hmn
        have hm2 := (Finset.mem_Icc.mp hm).1
        have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        have hlogm : Real.log 2 ≤ Real.log m :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
        have hsep := abs_log_sub_log_ge (by omega : 1 ≤ m) (by omega : 1 ≤ n) hmn
        have h2r : 2 * r = 1 / (2 * (n : ℝ)) := by
          rw [hr]
          field_simp
          ring
        have hA := packetAutocorr_twoBump s h hr0 (Real.log m)
        have e1 : Real.log m - 2 * h = Real.log m - Real.log n := by rw [hh]; ring
        have e2 : Real.log m + 2 * h = Real.log m + Real.log n := by rw [hh]; ring
        rw [e1, e2,
          packetAutocorr_cutoff_eq_zero hδ (z := Real.log m)
            (by rw [abs_of_nonneg (by linarith)]; linarith),
          packetAutocorr_cutoff_eq_zero hδ (z := Real.log m - Real.log n)
            (by rw [h2r]; exact hsep),
          packetAutocorr_cutoff_eq_zero hδ (z := Real.log m + Real.log n)
            (by rw [abs_of_nonneg (by linarith)]; linarith)] at hA
        rw [hA]
        ring
      · intro hnot
        exact absurd hnN hnot
    rw [hcontact, hmass, h1r] at hup
    -- `0 ≤ (log(1 + 4n) + 5 + log q) · 2Φ₀ + 128 S² Φ₀ − (w n/√n) · 2 s Φ₀`
    have hfin : w n / Real.sqrt n * (2 * (s * Φ₀)) ≤
        (2 * (Real.log (1 + 4 * (n : ℝ)) + 5 + Real.log q) + 128 * S ^ 2) * Φ₀ := by
      linarith
    have hdiv : s * w n / Real.sqrt n ≤
        Real.log (1 + 4 * (n : ℝ)) + 5 + Real.log q + 64 * S ^ 2 := by
      have e : w n / Real.sqrt n * (2 * (s * Φ₀)) = (2 * (s * w n / Real.sqrt n)) * Φ₀ := by
        ring
      rw [e] at hfin
      have := le_of_mul_le_mul_right hfin hΦpos
      linarith
    rw [div_le_iff₀ hsn] at hdiv
    linarith
  have hp := key 1 (by norm_num)
  have hm := key (-1) (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-! ### An `ℓ¹` ball is feasible; below the first contact the weights do not enter -/

/-- **An `ℓ¹` ball of the size of the mass is feasible.** -/
theorem feasible_of_sum_abs_le {q a : ℝ} {w : ℕ → ℝ}
    (h : archConstant + ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * |w n| / Real.sqrt n ≤
      Real.log q) : Feasible q a w := by
  intro F hF hFs
  have hFc : HasCompactSupport F :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hFs
  have hmass : 0 ≤ ∫ x, ‖F x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 := mul_le_mul_of_nonneg_left (integral_arch_ge hF hFs)
    (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e : 1 / (2 * π) * (-archConstant * (2 * π * ∫ x, ‖F x‖ ^ 2)) =
      -archConstant * ∫ x, ‖F x‖ ^ 2 := by
    field_simp
  rw [e] at h1
  have hcontact : contactForm w F ⌊Real.exp (2 * a)⌋₊ ≤
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * |w n| / Real.sqrt n) *
        ∫ x, ‖F x‖ ^ 2 := by
    unfold contactForm
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    have hb := _root_.RHTower.abs_re_weilTest_add_neg_le_two_mul_integral_norm_sq
      ⟨F, hF, hFc⟩ (Real.log n)
    have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    calc w n / Real.sqrt n *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re
        ≤ |w n / Real.sqrt n *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re| := le_abs_self _
      _ = |w n| / Real.sqrt n *
          |(EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re| := by
          rw [abs_mul, abs_div, abs_of_nonneg hs]
      _ ≤ |w n| / Real.sqrt n * (2 * ∫ x, ‖F x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb (div_nonneg (abs_nonneg _) hs)
      _ = 2 * |w n| / Real.sqrt n * ∫ x, ‖F x‖ ^ 2 := by ring
  rw [systemForm_eq hF hFs]
  nlinarith [mul_le_mul_of_nonneg_right h hmass]

/-- **Below the first contact the weights do not enter.** For `2a < log 2` feasibility at
aperture `a` does not depend on the weight system. -/
theorem feasible_iff_of_lt_half_log_two {q a : ℝ} (ha : 2 * a < Real.log 2) (w w' : ℕ → ℝ) :
    Feasible q a w ↔ Feasible q a w' := by
  refine feasible_congr fun n hn hnN => ?_
  have h1 : (n : ℝ) ≤ Real.exp (2 * a) :=
    (Nat.cast_le.mpr hnN).trans (Nat.floor_le (Real.exp_pos _).le)
  have h2 : Real.exp (2 * a) < 2 := by
    calc Real.exp (2 * a) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr ha
      _ = 2 := Real.exp_log two_pos
  have h3 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end GaloisForLFunctions.SelectiveArithmetic
