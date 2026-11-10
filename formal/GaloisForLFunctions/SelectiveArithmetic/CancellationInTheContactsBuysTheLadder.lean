import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture
import GaloisForLFunctions.SelectiveArithmetic.TheHeightOfAPacketIsAMass
import GaloisForLFunctions.RHTower.VonKochChebyshevBound

/-!
# Cancellation in the contacts buys the ladder

The sizes of the contacts pay the sign up to the aperture `log log q` and no further. What pays
beyond is cancellation. A weight system has *cancellation* `(C, γ)` if its partial sums satisfy
`|Σ_{2 ≤ k ≤ n} w(k)| ≤ C n^{1/2 + γ}`; the dominated box has `γ = ½`, a system with the
square-root cancellation of a Riemann hypothesis has every `γ > 0`.

* **The symbol of a system with cancellation** (`abs_sum_contact_cos_le`,
  `weilAtomSymbol_ge_of_cancellation`): summation by parts against `n^{−1/2} cos(τ log n)` gives
  `|2 Σ_{n ≤ N} w(n) n^{−1/2} cos(τ log n)| ≤ 2C N^{γ} (2 + log N)(1 + |τ|)`: the prime part of the
  symbol at the frequency `τ` has the size `N^{γ}`, not `N^{1/2}`.
* **The form of a system with cancellation** (`systemForm_ge_of_cancellation`): on a `C³` packet
  `f` supported in `[−a, a]`,
  `𝔚_{w,q}(f) ≥ (log q − A₀ − 3c) ∫ f² − c ∫ f'²`, `c = C e^{2γa}(2 + 2a)`.
* **The exchange rate of the ladder** (`exists_cancellation_margin`): if `2γκ < 1`, then for
  every conductor with `log q` large, every aperture `a ≤ κ log log q` and every system with
  cancellation `(C, γ)`: `𝔚_{w,q}(f) ≥ ½ log q (∫ f² − ∫ f'²)`.

So a saving `n^{1/2 + γ}` in the contacts buys the sign up to the rung `κ = 1/(2γ)` of the ladder,
on packets of bounded shape. This is the rate at which a zero of depth `γ` becomes visible on the
other side: an isolated pair of depth `δ` shows at `κ = 1/(2δ)`. A source that passes the trivial
aperture of an aspect must deliver a power saving in the contacts on the integers up to
`(log q)^{2κ}`.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ

/-! ### Partial sums and summation by parts -/

/-- The partial sums of a weight system over `2 ≤ k ≤ n`. -/
def partialSum (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 2 n, w k

/-- A weight system has cancellation `(C, γ)` if `|Σ_{2 ≤ k ≤ n} w(k)| ≤ C √n n^{γ}`. -/
def HasCancellation (w : ℕ → ℝ) (C γ : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → |partialSum w n| ≤ C * Real.sqrt n * (n : ℝ) ^ γ

theorem partialSum_succ (w : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n + 1) :
    partialSum w (n + 1) = partialSum w n + w (n + 1) :=
  Finset.sum_Icc_succ_top hn w

/-- Summation by parts. -/
theorem sum_Icc_mul_eq_abel (w g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, w n * g n =
      partialSum w N * g (N + 1) -
        ∑ n ∈ Finset.Icc 2 N, partialSum w n * (g (n + 1) - g n) := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    by_cases h : 2 ≤ N + 1
    · rw [Finset.sum_Icc_succ_top h, Finset.sum_Icc_succ_top h, ih, partialSum_succ w h]
      ring
    · have hN : N = 0 := by omega
      subst hN
      simp [partialSum]

/-- The step of `n^{−1/2} cos(τ log n)` is at most `(1 + |τ|) n^{−3/2}`. -/
theorem abs_cos_div_sqrt_succ_sub_le (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |Real.cos (τ * Real.log ((n + 1 : ℕ) : ℝ)) / Real.sqrt ((n + 1 : ℕ) : ℝ) -
        Real.cos (τ * Real.log (n : ℝ)) / Real.sqrt (n : ℝ)| ≤
      (1 + |τ|) / ((n : ℝ) * Real.sqrt n) := by
  push_cast
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, s₀ = Real.sqrt (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : ℝ, s₁ = Real.sqrt ((n : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = Real.cos (τ * Real.log (n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = Real.cos (τ * Real.log ((n : ℝ) + 1)) := ⟨_, rfl⟩
  rw [← hs₀, ← hs₁, ← hc₀, ← hc₁]
  have hs0 : 0 < s₀ := by rw [hs₀]; exact Real.sqrt_pos.mpr hn0
  have hs1 : 0 < s₁ := by rw [hs₁]; exact Real.sqrt_pos.mpr hn1
  have hsq0 : s₀ * s₀ = n := by rw [hs₀]; exact Real.mul_self_sqrt hn0.le
  have hsq1 : s₁ * s₁ = (n : ℝ) + 1 := by rw [hs₁]; exact Real.mul_self_sqrt hn1.le
  have hle : s₀ ≤ s₁ := by rw [hs₀, hs₁]; exact Real.sqrt_le_sqrt (by linarith)
  -- the cosines move by at most `|τ|/n`
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    have h := Real.log_le_sub_one_of_pos (div_pos hn1 hn0)
    rw [Real.log_div hn1.ne' hn0.ne'] at h
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log hn0 (by linarith))
  have hcos : |c₁ - c₀| ≤ |τ| / n := by
    rw [hc₁, hc₀]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_nonneg hlog0]
    calc |τ| * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ |τ| * (1 / n) :=
          mul_le_mul_of_nonneg_left hlog (abs_nonneg τ)
      _ = |τ| / n := by ring
  have hc0 : |c₀| ≤ 1 := by rw [hc₀]; exact Real.abs_cos_le_one _
  -- the square roots move by at most `1/(n √n)`
  have hinv0 : 0 ≤ 1 / s₀ - 1 / s₁ :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hs0 hle)
  have hinv : 1 / s₀ - 1 / s₁ ≤ 1 / (n * s₀) := by
    have h1 : (s₁ - s₀) * (s₁ + s₀) = 1 := by nlinarith
    have h2 : (s₁ - s₀) * s₀ ≤ 1 := by nlinarith [sub_nonneg.mpr hle]
    have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hs0.le hs0.le)
    have h4 := mul_le_mul_of_nonneg_left hle hs0.le
    rw [div_sub_div _ _ hs0.ne' hs1.ne', div_le_div_iff₀ (mul_pos hs0 hs1) (mul_pos hn0 hs0),
      ← hsq0]
    nlinarith
  have e : c₁ / s₁ - c₀ / s₀ = (c₁ - c₀) / s₁ - c₀ * (1 / s₀ - 1 / s₁) := by
    field_simp
    ring
  rw [e]
  have t1 : |(c₁ - c₀) / s₁| ≤ |τ| / n / s₀ := by
    rw [abs_div, abs_of_pos hs1]
    exact div_le_div₀ (div_nonneg (abs_nonneg τ) hn0.le) hcos hs0 hle
  have t2 : |c₀ * (1 / s₀ - 1 / s₁)| ≤ 1 * (1 / (n * s₀)) := by
    rw [abs_mul, abs_of_nonneg hinv0]
    exact mul_le_mul hc0 hinv hinv0 zero_le_one
  calc |(c₁ - c₀) / s₁ - c₀ * (1 / s₀ - 1 / s₁)|
      ≤ |(c₁ - c₀) / s₁| + |c₀ * (1 / s₀ - 1 / s₁)| := abs_sub _ _
    _ ≤ |τ| / n / s₀ + 1 * (1 / (n * s₀)) := add_le_add t1 t2
    _ = (1 + |τ|) / (n * s₀) := by
        field_simp
        ring

/-! ### The symbol of a system with cancellation -/

/-- **The prime part of the symbol of a system with cancellation.** If
`|Σ_{2 ≤ k ≤ n} w(k)| ≤ C √n n^{γ}`, then
`|Σ_{2 ≤ n ≤ N} w(n) n^{−1/2} cos(τ log n)| ≤ C N^{γ} (2 + log N)(1 + |τ|)`. -/
theorem abs_sum_contact_cos_le {w : ℕ → ℝ} {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hw : HasCancellation w C γ) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    |∑ n ∈ Finset.Icc 2 N, w n * (Real.cos (τ * Real.log n) / Real.sqrt n)| ≤
      C * (N : ℝ) ^ γ * (2 + Real.log N) * (1 + |τ|) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun k : ℕ => Real.cos (τ * Real.log k) / Real.sqrt k :=
    ⟨_, rfl⟩
  have hgk : ∀ k : ℕ, g k = Real.cos (τ * Real.log k) / Real.sqrt k := fun k => by rw [hg]
  have hsum : ∑ n ∈ Finset.Icc 2 N, w n * (Real.cos (τ * Real.log n) / Real.sqrt n) =
      ∑ n ∈ Finset.Icc 2 N, w n * g n :=
    Finset.sum_congr rfl fun n _ => by rw [hgk]
  rw [hsum, sum_Icc_mul_eq_abel w g N]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNγ : 0 ≤ (N : ℝ) ^ γ := Real.rpow_nonneg hN0.le γ
  have hT1 : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  -- the boundary term
  have hb : |partialSum w N * g (N + 1)| ≤ C * (N : ℝ) ^ γ := by
    rw [abs_mul]
    have h2 : |g (N + 1)| ≤ 1 / Real.sqrt N := by
      rw [hgk, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_div₀ zero_le_one (Real.abs_cos_le_one _) hsN
        (Real.sqrt_le_sqrt (by push_cast; linarith))
    calc |partialSum w N| * |g (N + 1)|
        ≤ (C * Real.sqrt N * (N : ℝ) ^ γ) * (1 / Real.sqrt N) :=
          mul_le_mul (hw N hN) h2 (abs_nonneg _) (by positivity)
      _ = C * (N : ℝ) ^ γ := by
          field_simp
  -- the sum
  have hharm : ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
    have h := _root_.RHTower.sum_Icc_one_div_le_one_add_log_max N
    have h' : ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k ≤ 1 + Real.log N := by
      simpa [max_eq_left hNr, max_eq_left hN] using h
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc (by norm_num) le_rfl) fun _ _ _ => by positivity).trans h'
  have hs : |∑ n ∈ Finset.Icc 2 N, partialSum w n * (g (n + 1) - g n)| ≤
      C * (N : ℝ) ^ γ * (1 + Real.log N) * (1 + |τ|) := by
    calc |∑ n ∈ Finset.Icc 2 N, partialSum w n * (g (n + 1) - g n)|
        ≤ ∑ n ∈ Finset.Icc 2 N, |partialSum w n * (g (n + 1) - g n)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 2 N, C * (N : ℝ) ^ γ * (1 + |τ|) * (1 / n) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn2 := (Finset.mem_Icc.mp hn).1
          have hnN := (Finset.mem_Icc.mp hn).2
          have hn1 : 1 ≤ n := by omega
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
          have hpow : (n : ℝ) ^ γ ≤ (N : ℝ) ^ γ :=
            Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN) hγ
          have h1 : |partialSum w n| ≤ C * Real.sqrt n * (N : ℝ) ^ γ :=
            (hw n hn1).trans (mul_le_mul_of_nonneg_left hpow (by positivity))
          have h2 : |g (n + 1) - g n| ≤ (1 + |τ|) / ((n : ℝ) * Real.sqrt n) := by
            rw [hgk, hgk]
            exact abs_cos_div_sqrt_succ_sub_le τ hn1
          rw [abs_mul]
          calc |partialSum w n| * |g (n + 1) - g n|
              ≤ (C * Real.sqrt n * (N : ℝ) ^ γ) * ((1 + |τ|) / ((n : ℝ) * Real.sqrt n)) :=
                mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
            _ = C * (N : ℝ) ^ γ * (1 + |τ|) * (1 / n) := by
                field_simp
      _ = C * (N : ℝ) ^ γ * (1 + |τ|) * ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n := by
          rw [Finset.mul_sum]
      _ ≤ C * (N : ℝ) ^ γ * (1 + |τ|) * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left hharm (by positivity)
      _ = C * (N : ℝ) ^ γ * (1 + Real.log N) * (1 + |τ|) := by ring
  have hP : 0 ≤ C * (N : ℝ) ^ γ := mul_nonneg hC hNγ
  calc |partialSum w N * g (N + 1) -
        ∑ n ∈ Finset.Icc 2 N, partialSum w n * (g (n + 1) - g n)|
      ≤ |partialSum w N * g (N + 1)| +
          |∑ n ∈ Finset.Icc 2 N, partialSum w n * (g (n + 1) - g n)| := abs_sub _ _
    _ ≤ C * (N : ℝ) ^ γ + C * (N : ℝ) ^ γ * (1 + Real.log N) * (1 + |τ|) := add_le_add hb hs
    _ ≤ C * (N : ℝ) ^ γ * (2 + Real.log N) * (1 + |τ|) := by
        nlinarith [mul_le_mul_of_nonneg_left hT1 hP]

/-- **The symbol of a system with cancellation**: the archimedean symbol minus
`2C N^{γ}(2 + log N)(1 + |τ|)`. -/
theorem weilAtomSymbol_ge_of_cancellation {w : ℕ → ℝ} {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hw : HasCancellation w C γ) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) -
        2 * (C * (N : ℝ) ^ γ * (2 + Real.log N)) * (1 + |τ|) ≤
      _root_.RHTower.weilAtomSymbol w N (τ / (2 * π)) := by
  have h := (abs_le.mp (abs_sum_contact_cos_le hC hγ hw hN τ)).2
  have e : ∑ n ∈ Finset.Icc 2 N, w n * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) =
      2 * ∑ n ∈ Finset.Icc 2 N, w n * (Real.cos (τ * Real.log n) / Real.sqrt n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have harg : 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n := by field_simp
    rw [harg]
    ring
  unfold _root_.RHTower.weilAtomSymbol
  rw [e]
  linarith

/-! ### The form of a system with cancellation -/

/-- A symbol bounded below by `α − β τ²` has energy at least `α ∫ f² − β ∫ f'²` on a `C³`
packet. -/
theorem integral_normSq_paperFT_mul_ge {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) {S : ℝ → ℝ}
    (hS : Integrable fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 * S τ) {α β : ℝ}
    (hSb : ∀ τ : ℝ, α - β * τ ^ 2 ≤ S τ) :
    α * (∫ u, f u ^ 2) - β * ∫ u, deriv f u ^ 2 ≤
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 * S τ := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hF : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet hf2
  have hFs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  have hFc : HasCompactSupport fun u => (f u : ℂ) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hFs
  have hG : ContDiff ℝ 2 fun u => ((deriv f u : ℝ) : ℂ) :=
    contDiff_ofReal_packet (contDiff_two_deriv hf)
  have hderiv : deriv (fun u => (f u : ℂ)) = fun u => ((deriv f u : ℝ) : ℂ) := by
    funext u
    exact ((hf2.differentiable (by norm_num) u).hasDerivAt.ofReal_comp).deriv
  have hGs : tsupport (fun u => ((deriv f u : ℝ) : ℂ)) ⊆ Set.Icc (-a) a := by
    rw [← hderiv]
    exact (tsupport_deriv_subset (f := fun u => (f u : ℂ))).trans hFs
  have hnorm : ∀ τ : ℝ, ‖paperFT (fun u => ((deriv f u : ℝ) : ℂ)) τ‖ ^ 2 =
      τ ^ 2 * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 := fun τ => by
    have h := _root_.RHTower.EvenSector.paperFT_deriv_of_compact (hF.of_le (by norm_num)) hFc
      (τ : ℂ)
    rw [hderiv] at h
    rw [h, norm_mul, mul_pow, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hI := _root_.RHTower.integrable_normSq_paperFT hF hFs
  have hI' := _root_.RHTower.integrable_normSq_paperFT hG hGs
  have hmono : ∫ τ : ℝ, (α * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 -
        β * ‖paperFT (fun u => ((deriv f u : ℝ) : ℂ)) τ‖ ^ 2) ≤
      ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 * S τ := by
    refine integral_mono ((hI.const_mul α).sub (hI'.const_mul β)) hS fun τ => ?_
    show α * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 -
        β * ‖paperFT (fun u => ((deriv f u : ℝ) : ℂ)) τ‖ ^ 2 ≤
      ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 * S τ
    rw [hnorm]
    nlinarith [mul_le_mul_of_nonneg_left (hSb τ)
      (sq_nonneg ‖paperFT (fun u => (f u : ℂ)) τ‖)]
  rw [integral_sub (hI.const_mul α) (hI'.const_mul β), integral_const_mul, integral_const_mul,
    _root_.RHTower.integral_norm_paperFT_sq hF hFs,
    _root_.RHTower.integral_norm_paperFT_sq hG hGs, integral_norm_ofReal_sq,
    integral_norm_ofReal_sq] at hmono
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e : 1 / (2 * π) * (α * (2 * π * ∫ u, f u ^ 2) - β * (2 * π * ∫ u, deriv f u ^ 2)) =
      α * (∫ u, f u ^ 2) - β * ∫ u, deriv f u ^ 2 := by
    field_simp
  rwa [e] at h1

/-- **The form of a system with cancellation.** If `|Σ_{2 ≤ k ≤ n} w(k)| ≤ C √n n^{γ}`, then on a
`C³` packet `f` vanishing off `(−a, a)`:
`𝔚_{w,q}(f) ≥ (log q − A₀ − 3c) ∫ f² − c ∫ f'²` with `c = C e^{2γa} (2 + 2a)`. -/
theorem systemForm_ge_of_cancellation {w : ℕ → ℝ} {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hw : HasCancellation w C γ) {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (q : ℝ) :
    (Real.log q - archConstant - 3 * (C * Real.exp (2 * γ * a) * (2 + 2 * a))) *
          (∫ u, f u ^ 2) -
        C * Real.exp (2 * γ * a) * (2 + 2 * a) * ∫ u, deriv f u ^ 2 ≤
      systemForm w q a (fun u => (f u : ℂ)) := by
  have hF : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet (hf.of_le (by norm_num))
  have hFs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
  have hexp1 : (1 : ℝ) ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have hN : 1 ≤ N := Nat.le_floor (by rw [Nat.cast_one]; exact hexp1)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNle : (N : ℝ) ≤ Real.exp (2 * a) := Nat.floor_le (Real.exp_pos _).le
  -- the size of the prime part at aperture `a`
  have hpow : (N : ℝ) ^ γ ≤ Real.exp (2 * γ * a) := by
    have h1 : (N : ℝ) ^ γ ≤ Real.exp (2 * a) ^ γ :=
      Real.rpow_le_rpow (by linarith) hNle hγ
    rw [← Real.exp_mul] at h1
    rwa [show 2 * a * γ = 2 * γ * a by ring] at h1
  have hlog : Real.log N ≤ 2 * a := by
    calc Real.log N ≤ Real.log (Real.exp (2 * a)) := Real.log_le_log (by linarith) hNle
      _ = 2 * a := Real.log_exp _
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  set c := C * Real.exp (2 * γ * a) * (2 + 2 * a) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcN : C * (N : ℝ) ^ γ * (2 + Real.log N) ≤ c := by
    rw [hc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) (by linarith) (by linarith)
      (by positivity)
  -- the symbol is at least `(log q − A₀ − 3c) − c τ²`
  have hSb : ∀ τ : ℝ, (Real.log q - archConstant - 3 * c) - c * τ ^ 2 ≤
      _root_.RHTower.weilAtomSymbol w N (τ / (2 * π)) + Real.log q := by
    intro τ
    have h1 := weilAtomSymbol_ge_of_cancellation hC hγ hw hN τ
    have h2 := neg_archConstant_le_archimedeanWeilSymbol τ
    have h3 : |τ| ≤ (1 + τ ^ 2) / 2 := by
      nlinarith [sq_nonneg (|τ| - 1), sq_abs τ, abs_nonneg τ]
    have h4 : 2 * (C * (N : ℝ) ^ γ * (2 + Real.log N)) * (1 + |τ|) ≤ 2 * c * (1 + |τ|) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [abs_nonneg τ])
    nlinarith [mul_le_mul_of_nonneg_left h3 hc0]
  -- integrability of the symbol energy
  have hS := _root_.RHTower.integrable_normSq_paperFT_mul_weilAtomSymbol_of hF hFs w
  have hB : Integrable fun τ : ℝ => Real.log q * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 :=
    (_root_.RHTower.integrable_normSq_paperFT hF hFs).const_mul _
  have hSint : Integrable fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
      (_root_.RHTower.weilAtomSymbol w N (τ / (2 * π)) + Real.log q) := by
    have e : (fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol w N (τ / (2 * π)) + Real.log q)) =
        fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
            _root_.RHTower.weilAtomSymbol w N (τ / (2 * π)) +
          Real.log q * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 := by
      funext τ
      ring
    rw [e]
    exact hS.add hB
  have h := integral_normSq_paperFT_mul_ge hf h0 hSint hSb
  unfold systemForm
  linarith

/-! ### The exchange rate of the ladder -/

/-- The budget of a rung: for `s < 1`, eventually `A ≤ e^{y}/8` and
`C e^{sy} (2 + 2κy) ≤ e^{y}/8`. -/
theorem eventually_cancellation_budget {C κ s : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hs : s < 1)
    (A : ℝ) :
    ∀ᶠ y : ℝ in atTop, A ≤ Real.exp y / 8 ∧
      C * Real.exp (s * y) * (2 + 2 * κ * y) ≤ Real.exp y / 8 := by
  have hc : 0 < 1 - s := by linarith
  have hcub := (tendsto_id.const_mul_atTop hc).eventually
    (eventually_cubic_lt_exp (C * (2 + 2 * κ / (1 - s))) (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [hcub, Real.tendsto_exp_atTop.eventually_ge_atTop (8 * A),
    eventually_ge_atTop (0 : ℝ)] with y hy hA hy0
  refine ⟨by linarith, ?_⟩
  simp only [id] at hy
  have hcy : 0 ≤ (1 - s) * y := mul_nonneg hc.le hy0
  have h1 : (1 : ℝ) ≤ (1 + (1 - s) * y) ^ 3 := one_le_pow₀ (by linarith)
  have h2 : 1 + (1 - s) * y ≤ (1 + (1 - s) * y) ^ 3 := by
    have : (1 + (1 - s) * y) ^ 3 = (1 + (1 - s) * y) * (1 + (1 - s) * y) ^ 2 := by ring
    rw [this]
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith))
  have hlin : 2 + 2 * κ * y ≤ (2 + 2 * κ / (1 - s)) * (1 + (1 - s) * y) := by
    have e : (2 + 2 * κ / (1 - s)) * (1 + (1 - s) * y) =
        2 + 2 * κ * y + 2 * (1 - s) * y + 2 * κ / (1 - s) := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ 2 * κ / (1 - s) := by positivity
    nlinarith
  have hK : 0 ≤ 2 + 2 * κ / (1 - s) := by positivity
  have h3 : C * (2 + 2 * κ * y) ≤ Real.exp ((1 - s) * y) / 8 := by
    have h4 : C * (2 + 2 * κ * y) ≤ C * (2 + 2 * κ / (1 - s)) * (1 + (1 - s) * y) ^ 3 := by
      calc C * (2 + 2 * κ * y) ≤ C * ((2 + 2 * κ / (1 - s)) * (1 + (1 - s) * y)) :=
            mul_le_mul_of_nonneg_left hlin hC
        _ ≤ C * ((2 + 2 * κ / (1 - s)) * (1 + (1 - s) * y) ^ 3) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK) hC
        _ = C * (2 + 2 * κ / (1 - s)) * (1 + (1 - s) * y) ^ 3 := by ring
    linarith
  have hsplit : Real.exp y = Real.exp (s * y) * Real.exp ((1 - s) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc C * Real.exp (s * y) * (2 + 2 * κ * y)
      = Real.exp (s * y) * (C * (2 + 2 * κ * y)) := by ring
    _ ≤ Real.exp (s * y) * (Real.exp ((1 - s) * y) / 8) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp y / 8 := by rw [hsplit]; ring

/-- **The exchange rate of the ladder.** If `2γκ < 1`, then for every conductor with `log q`
large, every aperture `a ≤ κ log log q`, every system with cancellation `(C, γ)` and every `C³`
packet `f` vanishing off `(−a, a)`: `𝔚_{w,q}(f) ≥ ½ log q (∫ f² − ∫ f'²)`. -/
theorem exists_cancellation_margin {C γ κ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (hγκ : 2 * γ * κ < 1) :
    ∃ M₀ : ℝ, ∀ q : ℝ, M₀ ≤ Real.log q → ∀ a : ℝ, 0 ≤ a → a ≤ κ * Real.log (Real.log q) →
      ∀ {w : ℕ → ℝ}, HasCancellation w C γ → ∀ {f : ℝ → ℝ}, ContDiff ℝ 3 f →
        (∀ u, a ≤ |u| → f u = 0) →
        Real.log q / 2 * ((∫ u, f u ^ 2) - ∫ u, deriv f u ^ 2) ≤
          systemForm w q a (fun u => (f u : ℂ)) := by
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp
    (eventually_cancellation_budget hC hκ hγκ archConstant)
  refine ⟨Real.exp (max y₀ 0), fun q hq a ha0 ha w hw f hf h0 => ?_⟩
  set x := Real.log q with hx
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hq
  set y := Real.log x with hy
  have hyy : max y₀ 0 ≤ y := by
    rw [hy, ← Real.log_exp (max y₀ 0)]
    exact Real.log_le_log (Real.exp_pos _) hq
  have hy0 : 0 ≤ y := (le_max_right _ _).trans hyy
  have hxy : Real.exp y = x := Real.exp_log hx0
  obtain ⟨hA, hbud⟩ := hy₀ y ((le_max_left _ _).trans hyy)
  rw [hxy] at hA hbud
  -- the cost of the contacts at aperture `a ≤ κ log log q`
  have hcost : C * Real.exp (2 * γ * a) * (2 + 2 * a) ≤ x / 8 := by
    have h1 : Real.exp (2 * γ * a) ≤ Real.exp (2 * γ * κ * y) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 2 * γ)])
    have h2 : 2 + 2 * a ≤ 2 + 2 * κ * y := by nlinarith
    calc C * Real.exp (2 * γ * a) * (2 + 2 * a)
        ≤ C * Real.exp (2 * γ * κ * y) * (2 + 2 * κ * y) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 (by linarith) (by positivity)
      _ ≤ x / 8 := hbud
  have hcost0 : 0 ≤ C * Real.exp (2 * γ * a) * (2 + 2 * a) := by positivity
  have hM : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hD : 0 ≤ ∫ u, deriv f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine le_trans ?_ (systemForm_ge_of_cancellation hC hγ hw ha0 hf h0 q)
  have h1 : x / 2 ≤ x - archConstant - 3 * (C * Real.exp (2 * γ * a) * (2 + 2 * a)) := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hM, mul_le_mul_of_nonneg_right hcost hD]

end GaloisForLFunctions.SelectiveArithmetic
