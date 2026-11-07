import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowReadsTheResidueFromAbove
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# The datum region lies left of the residue line

Call `𝒟 = {(β, s) : 𝒜_{β,s}(c) ≠ ∅ for every c}` the **datum region**: the data for which positivity survives at every
window, for some weight system depending on the window. `TheDatumOfTheWindowCone` and `TheWindowReadsTheResidue`
locate its points on the axes. This module bounds it on the right, for every conductor.

* **No conductor rescues a pole above one** (`exists_le_one_add_mul_div_of_datumCone`). There is `K > 0` such that
  for every log-conductor `s`, from a finite window on, every nonempty cone of `(β, s)` has
  `β ≤ 1 + K(1 + |s|)/c`. The conductor enters the archimedean ceiling only additively, `(log 2N + C₀ + |s|)`, while
  the pole weight enters the density floor multiplicatively, `β log N`.
* **The datum region lies left of the residue line** (`datumRegion_subset`). `𝒟 ⊆ {β ≤ 1}`. It contains the
  no-pole ray `{0} × [log π − ψ(¼), ∞)` (`zero_mem_datumRegion`), it is convex (`convex_datumRegion`), and it meets
  the conductor-one axis at most in the residue: `(β, 0) ∈ 𝒟` forces `β = 1`, and `(1, 0) ∈ 𝒟` is RH
  (`mem_datumRegion_axis_iff`).

Below the residue, conductor buys positivity: the zero weights are positive at every window once
`s ≥ log π − ψ(¼)`. Above it, nothing buys positivity. The asymmetry is the one of the two readings: the
zeros read a pole deficit and the conductor can pay it; the archimedean logarithm reads a pole excess through the
density of the weights, and a conductor is a constant, which a logarithm outgrows.

What this does not say about `ζ`: the region is a property of the archimedean datum and the positions `log n`;
`(1, 0) ∈ 𝒟` is RH.
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.OddSector _root_.RHTower.EvenSector
open _root_.RHTower.ResonatorProfile _root_.Zeta23

/-! ### The Weil–Toeplitz bound with a conductor slack -/

/-- Polar positivity with slack: `Re W(f) ≥ −σ` gives `∫ |f̂|² S ≥ −2πσ` for the finite-atom symbol. -/
theorem integral_weilAtomSymbol_ge_of_polar {lam : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (Complex.I / 2) = 0)
    (hm : paperFT f (-(Complex.I / 2)) = 0) {σ : ℝ}
    (hW : -σ ≤ (weilFullFunctional lam (EF.weilTest f f)).re) :
    -(2 * π * σ) ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  obtain ⟨-, -, hks, -, -⟩ := weilTest_self_data hf hfs
  have hkc := EF.weilTest_hasCompactSupport hfc hfc
  set k := EF.weilTest f f with hk
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  rw [integral_weilAtomSymbol_eq_sub hf hfs lam]
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  rw [← hN] at hWf
  have hre : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hWf, Complex.ofReal_re]; field_simp
  rw [hre]
  have hfull := hW
  rw [weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional hf hfc, Complex.sub_re] at hfull
  have hvan : ∀ n : ℕ, N < n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * a) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * a))
      have h2 : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
    have hlog : 2 * a < Real.log n := by rw [Real.lt_log_iff_exp_lt hnpos]; exact hn'
    have hout : ∀ y : ℝ, 2 * a < |y| → k y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hks hmem
      rw [mem_Icc] at this
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0] at hy; linarith [this.2]
      · rw [abs_of_neg h0] at hy; linarith [this.1]
    have hl0 : 0 < Real.log n := by linarith
    exact ⟨hout _ (by rw [abs_of_pos hl0]; exact hlog),
      hout _ (by rw [abs_neg, abs_of_pos hl0]; exact hlog)⟩
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n
      else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re =
      ∑ n ∈ Finset.Icc 2 N, (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
        (k (Real.log n) + k (-Real.log n)).re := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N) (fun n hn => ?_), Complex.re_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).1, Complex.re_ofReal_mul]
    · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · rw [if_neg (by omega), Complex.ofReal_zero, zero_mul]
      · rw [(hvan n h).1, (hvan n h).2, add_zero, mul_zero]
  rw [hsum] at hfull
  have hπ : 0 < π := Real.pi_pos
  nlinarith

/-- **The Weil–Toeplitz bound with slack.** If the finite-atom symbol energy of the resonator is at least
`−σ ∫ |R̂|²`, the bound of `weil_multiplicativeToeplitz_bound_of_profile` holds with `log N` raised by `σ`. -/
theorem toeplitz_bound_of_profile_slack {lam : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (c : ℕ → ℂ) (hc : ∀ m, N < m → c m = 0) {q : ℝ → ℝ} (hq : ContDiff ℝ 3 q)
    (hqv : ∀ u, 1 / ((N : ℝ) + 1) / 4 < |u| → q u = 0) (hq0 : 0 < ∫ u, q u ^ 2) {K : ℝ}
    (hK : (1 / ((N : ℝ) + 1)) ^ 2 * ∫ u, deriv q u ^ 2 ≤ K * ∫ u, q u ^ 2)
    {σ : ℝ}
    (hW : -(σ * ∫ τ : ℝ, ‖paperFT (profileResonator N c q) τ‖ ^ 2) ≤
      ∫ τ : ℝ, ‖paperFT (profileResonator N c q) τ‖ ^ 2 * weilAtomSymbol lam
        ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊ (τ / (2 * π))) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
      (Real.log N + (Real.log 2 + 9 / 2 + K / 2) + σ) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set w : ℝ := 1 / ((N : ℝ) + 1) with hwdef
  have hw : 0 < w := by positivity
  have hwN : w * ((N : ℝ) + 1) = 1 := by rw [hwdef]; field_simp
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  set a : ℝ := Real.log N / 2 + w / 4 with hadef
  have ha : 0 ≤ a := by positivity
  have hqd : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hq2 : ContDiff ℝ 2 q := hq.of_le (by norm_num)
  have hq'2 : ContDiff ℝ 2 (deriv q) := hq.deriv'
  have hqv' : ∀ u, w / 4 < |u| → q u = 0 := hqv
  have hdqv : ∀ u, w / 4 < |u| → deriv q u = 0 := fun u hu => by
    have hev : q =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {x : ℝ | w / 4 < |x|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hu] with x hx
      exact hqv' x hx
    rw [hev.deriv_eq]; simp
  set qC : ℝ → ℂ := fun u => ((q u : ℝ) : ℂ) with hqC
  set dC : ℝ → ℂ := fun u => ((deriv q u : ℝ) : ℂ) with hdC
  set F := profileResonator N c q with hFdef
  set F' := profileResonator N c (deriv q) with hF'def
  have hFvan : ∀ u, a < |u| → F u = 0 := fun u hu =>
    sum_translates_eq_zero (h := qC) (fun v hv => by simp [hqC, hqv' v hv]) hu
  have hF'van : ∀ u, a < |u| → F' u = 0 := fun u hu =>
    sum_translates_eq_zero (h := dC) (fun v hv => by simp [hdC, hdqv v hv]) hu
  have hFs : tsupport F ⊆ Icc (-a) a := tsupport_subset_of_vanish hFvan
  have hF's : tsupport F' ⊆ Icc (-a) a := tsupport_subset_of_vanish hF'van
  have hF2 : ContDiff ℝ 2 F := contDiff_profileResonator N c hq2
  have hF'2 : ContDiff ℝ 2 F' := contDiff_profileResonator N c hq'2
  have hFcs : HasCompactSupport F :=
    hasCompactSupport_of_support_subset_abs (Λ := a) fun u hu => by
      by_contra h; push Not at h; exact hu (hFvan u h)
  have hpos := hW
  rw [integral_weilAtomSymbol_eq_arch_sub hF2 hFs lam] at hpos
  -- the autocorrelation masses
  set k0r : ℝ := ∫ t, q t ^ 2 with hk0r
  set k1r : ℝ := ∫ t, deriv q t ^ 2 with hk1r
  have hk0 : EF.weilTest qC qC 0 = (k0r : ℂ) := weilTest_self_zero_ofReal (g := q)
  have hk1 : EF.weilTest dC dC 0 = (k1r : ℂ) := weilTest_self_zero_ofReal (g := deriv q)
  have hgap : 2 * (w / 4) < 1 / ((N : ℝ) + 1) := by
    rw [← hwdef]; linarith
  have hvan0 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest qC qC Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (r := w / 4) (fun u hu => by simp [hqC, hqv' u hu])
      (by linarith)
  have hvan1 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest dC dC Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (r := w / 4) (fun u hu => by simp [hdC, hdqv u hu])
      (by linarith)
  have hgc0 : Continuous qC := Complex.continuous_ofReal.comp hq2.continuous
  have hgc1 : Continuous dC := Complex.continuous_ofReal.comp hq'2.continuous
  have hgs0 : HasCompactSupport qC := hasCompactSupport_of_support_subset_abs (Λ := w / 4)
    fun u hu => by by_contra h; push Not at h; exact hu (by simp [hqC, hqv' u h])
  have hgs1 : HasCompactSupport dC := hasCompactSupport_of_support_subset_abs (Λ := w / 4)
    fun u hu => by by_contra h; push Not at h; exact hu (by simp [hdC, hdqv u h])
  set S : ℕ → ℂ := fun n => ∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m) with hSdef
  -- the atoms
  have hsel : ∀ n : ℕ, 1 ≤ n →
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re = 2 * k0r * (S n).re := by
    intro n hn
    have h1 := weilTest_translates_log hgc0 hgs0 hvan0 hc hn
    have h2 := weilTest_translates_neg_log hgc0 hgs0 hvan0 hc hn
    rw [sum_conj_swap] at h2
    rw [show F = fun u => ∑ m ∈ Finset.Icc 1 N, c m * qC (u - resPt N m) from rfl, h1, h2, hk0]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re, hSdef]
    ring
  have hS0 : ∀ n, N < n → S n = 0 := by
    intro n hn
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [hc (n * m) (by nlinarith), zero_mul]
  have hM : N ≤ ⌊Real.exp (2 * a)⌋₊ := by
    apply Nat.le_floor
    have : Real.exp (Real.log N) ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by rw [hadef]; linarith)
    rwa [Real.exp_log (by linarith)] at this
  have hatoms : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re =
      2 * k0r * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * (S n).re := by
    calc ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re
        = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * k0r * (lam n / Real.sqrt n * (S n).re) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hsel n (by have := (Finset.mem_Icc.mp hn).1; omega)]; ring
      _ = ∑ n ∈ Finset.Icc 2 N, 2 * k0r * (lam n / Real.sqrt n * (S n).re) := by
          refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hM) fun n hn hnot => ?_).symm
          have hnN : N < n := by
            simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
            rcases hnot with h | h
            · have := (Finset.mem_Icc.mp hn).1; omega
            · exact h
          rw [hS0 n hnN]; simp
      _ = 2 * k0r * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * (S n).re := by
          rw [Finset.mul_sum]
  set sumc : ℝ := ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 with hsumc
  have hsum : 0 ≤ sumc := Finset.sum_nonneg fun m _ => sq_nonneg _
  -- the Plancherel masses
  have hmass0 : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 = 2 * π * k0r * sumc := by
    have h := integral_normSq_paperFT_mul_cos_eq hF2 hFs 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc0 hgs0 hvan0 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F = fun u => ∑ m ∈ Finset.Icc 1 N, c m * qC (u - resPt N m) from rfl, h0, hk0,
      sum_mul_conj_eq]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hmass1 : ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = 2 * π * k1r * sumc := by
    have h := integral_normSq_paperFT_mul_cos_eq hF'2 hF's 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc1 hgs1 hvan1 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F' = fun u => ∑ m ∈ Finset.Icc 1 N, c m * dC (u - resPt N m) from rfl, h0,
      hk1, sum_mul_conj_eq]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  -- the archimedean symbol on the spectrum of the resonator
  have hderiv : ∀ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = τ ^ 2 * ‖paperFT F τ‖ ^ 2 := by
    intro τ
    rw [hF'def, ← deriv_profileResonator N c hqd, paperFT_deriv (hF2.of_le (by norm_num)) hFcs]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_pow, sq_abs]
  set α : ℝ := Real.log ((N : ℝ) + 1) + 9 / 2 with hα
  set β : ℝ := w ^ 2 / 2 with hβ
  have hpt : ∀ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2 := by
    intro τ
    have hA := archimedeanWeilSymbol_le_log_add τ
    have hpos1 : 0 < 1 + w * |τ| := by positivity
    have hle : 1 + |τ| ≤ ((N : ℝ) + 1) * (1 + w * |τ|) := by
      have : ((N : ℝ) + 1) * (1 + w * |τ|) = (N : ℝ) + 1 + |τ| := by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm ((N : ℝ) + 1) w, hwN, one_mul]
      rw [this]; linarith
    have hlog1 : Real.log (1 + |τ|) ≤ Real.log ((N : ℝ) + 1) + w * |τ| := by
      calc Real.log (1 + |τ|) ≤ Real.log (((N : ℝ) + 1) * (1 + w * |τ|)) :=
            Real.log_le_log (by positivity) hle
        _ = Real.log ((N : ℝ) + 1) + Real.log (1 + w * |τ|) :=
            Real.log_mul (by positivity) (by positivity)
        _ ≤ Real.log ((N : ℝ) + 1) + w * |τ| := by
            have := Real.log_le_sub_one_of_pos hpos1; linarith
    have hamgm : w * |τ| ≤ 1 / 2 + w ^ 2 * τ ^ 2 / 2 := by
      have := sq_nonneg (w * |τ| - 1)
      have h2 : (w * |τ|) ^ 2 = w ^ 2 * τ ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith
    have hA' : archimedeanWeilSymbol (τ / (2 * π)) ≤ α + β * τ ^ 2 := by
      rw [hα, hβ]; linarith
    rw [hderiv τ]
    have hnn : 0 ≤ ‖paperFT F τ‖ ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hA' hnn
    linarith
  have hint1 := integrable_normSq_paperFT_mul_arch hF2 hFs
  have hint2 := integrable_normSq_paperFT hF2 hFs
  have hint3 := integrable_normSq_paperFT hF'2 hF's
  have harch : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      α * (2 * π * k0r * sumc) + β * (2 * π * k1r * sumc) := by
    calc ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))
        ≤ ∫ τ : ℝ, (α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2) :=
          integral_mono hint1 ((hint2.const_mul α).add (hint3.const_mul β)) hpt
      _ = α * (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2) + β * ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 := by
          rw [integral_add (hint2.const_mul α) (hint3.const_mul β),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = α * (2 * π * k0r * sumc) + β * (2 * π * k1r * sumc) := by rw [hmass0, hmass1]
  have hratio : β * k1r ≤ K / 2 * k0r := by
    rw [hβ, hk1r, hk0r]; nlinarith
  have hlog2 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith)
  set T : ℝ := ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * (S n).re with hT
  rw [hatoms, hmass0] at hpos
  have hk2 : 0 < 2 * π * k0r := by positivity
  have hmain : 2 * π * k0r * (2 * T) ≤ 2 * π * k0r * ((α + K / 2 + σ) * sumc) := by
    have h1 : β * (2 * π * k1r * sumc) ≤ 2 * π * sumc * (K / 2 * k0r) := by
      have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * π * sumc by positivity)
      linarith
    linarith
  have h2T : 2 * T ≤ (α + K / 2 + σ) * sumc := le_of_mul_le_mul_left hmain hk2
  calc 2 * T ≤ (α + K / 2 + σ) * sumc := h2T
    _ ≤ (Real.log N + (Real.log 2 + 9 / 2 + K / 2) + σ) * sumc := by
        apply mul_le_mul_of_nonneg_right _ hsum
        rw [hα]; linarith

/-! ### The ceiling at every conductor -/

/-- On the cone of `(β, s)` the narrow pole-free resonator at level `L` has symbol energy at least
`−|s| ∫ |R̂|²`. -/
theorem integral_weilAtomSymbol_resonator_ge {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    {L : ℕ} (hLc : Real.log L / 2 + 1 / ((L : ℝ) + 1) / 4 ≤ c) (cf : ℕ → ℂ) :
    -(|s| * ∫ τ : ℝ, ‖paperFT (profileResonator L cf (gR' (1 / ((L : ℝ) + 1)))) τ‖ ^ 2) ≤
      ∫ τ : ℝ, ‖paperFT (profileResonator L cf (gR' (1 / ((L : ℝ) + 1)))) τ‖ ^ 2 *
        weilAtomSymbol lam ⌊Real.exp (2 * (Real.log L / 2 + 1 / ((L : ℝ) + 1) / 4))⌋₊
          (τ / (2 * Real.pi)) := by
  set w : ℝ := 1 / ((L : ℝ) + 1) with hw_def
  have hw : 0 < w := by positivity
  set R := profileResonator L cf (gR' w) with hR
  obtain ⟨hp1, hp2⟩ := paperFT_profileResonator_gR'_pole L cf hw
  have ha : 0 ≤ Real.log L / 2 + w / 4 := by
    have := Real.log_natCast_nonneg L
    positivity
  have hd : ContDiff ℝ 2 R := contDiff_profileResonator L cf (contDiff_gR' w 2)
  have hsupp : tsupport R ⊆ Icc (-(Real.log L / 2 + w / 4)) (Real.log L / 2 + w / 4) :=
    tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (h := fun v => ((gR' w v : ℝ) : ℂ))
      (fun v hv => by
        show ((gR' w v : ℝ) : ℂ) = 0
        rw [gR'_eq_zero hw hv, Complex.ofReal_zero]) hu
  have hRc : HasCompactSupport R :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport R) hsupp
  have hE := h R hd (hsupp.trans (Icc_subset_Icc (by linarith) hLc))
  rw [datumEnergy_eq] at hE
  have hP : (weilPoleTerm (EF.weilTest R R)).re = 0 := by
    rw [weilPoleTerm_weilTest_eq hd.continuous hRc,
      show (-Complex.I / 2 : ℂ) = -(Complex.I / 2) by ring, hp1, hp2]
    simp
  have hm : 0 ≤ ∫ u, ‖R u‖ ^ 2 := integral_nonneg fun _ => by positivity
  rw [hP, mul_zero, add_zero] at hE
  have hslack : -(|s| * ∫ u, ‖R u‖ ^ 2) ≤ (weilFullFunctional lam (EF.weilTest R R)).re := by
    have : s * ∫ u, ‖R u‖ ^ 2 ≤ |s| * ∫ u, ‖R u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self s) hm
    linarith
  have hge := integral_weilAtomSymbol_ge_of_polar ha hd hsupp hp1 hp2 hslack
  rw [RHTower.integral_norm_sq_paperFT_eq hd hsupp]
  have e : -(|s| * (2 * Real.pi * ∫ u, ‖R u‖ ^ 2)) = -(2 * Real.pi * (|s| * ∫ u, ‖R u‖ ^ 2)) := by
    ring
  rw [e]
  exact hge

/-- **The archimedean ceiling at conductor `s`.** On the cone of `(β, s)`, for `N ≥ 1` with
`½ log 2N + 1 ≤ c`, the smoothed Toeplitz sum is at most `(log 2N + C₀ + |s|)(1 + log 2N)`. -/
theorem smoothed_toeplitz_le_conductor {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    {N : ℕ} (hN : 1 ≤ N) (hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c) :
    2 * ∑ m ∈ Finset.Icc 1 (2 * N), 1 / (m : ℝ) * ∑ n ∈ Finset.Icc 2 (2 * N),
        lam n / n * farStep (Real.log n + Real.log m - Real.log N) ≤
      (Real.log (2 * N : ℕ) + (Real.log 2 + 9 / 2 + oddProfileRatio / 2) + |s|) *
        (1 + Real.log (2 * N : ℕ)) := by
  set L : ℕ := 2 * N with hLdef
  have hL : 1 ≤ L := by omega
  have hL1 : (0 : ℝ) < L + 1 := by positivity
  set w : ℝ := 1 / ((L : ℝ) + 1) with hw_def
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw_def, div_le_one hL1]; have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith
  have hc : ∀ m, L < m → stepCoeff N m = 0 := fun m hm => stepCoeff_eq_zero hN hm
  have hq0 : 0 < ∫ u, gR' w u ^ 2 :=
    lt_of_lt_of_le (div_pos integral_d3_sq_pos (by positivity)) (integral_gR'_sq_ge hw)
  have hK : w ^ 2 * ∫ u, deriv (gR' w) u ^ 2 ≤ oddProfileRatio * ∫ u, gR' w u ^ 2 := by
    rw [deriv_gR']; exact sq_mul_integral_gR''_le hw hw1
  have hW := integral_weilAtomSymbol_resonator_ge h (L := L) (by linarith) (stepCoeff N)
  have hb := toeplitz_bound_of_profile_slack hL (stepCoeff N) hc (contDiff_gR' w 3)
    (fun u hu => gR'_eq_zero hw hu) hq0 hK hW
  rw [toeplitz_lhs_stepCoeff] at hb
  have hrhs : ∑ m ∈ Finset.Icc 1 L, ‖stepCoeff N m‖ ^ 2 ≤ 1 + Real.log L :=
    (Finset.sum_le_sum fun m hm => norm_stepCoeff_sq_le (Finset.mem_Icc.mp hm).1).trans
      (RHTower.sum_Icc_inv_le_one_add_log L)
  have hC₀ : 0 ≤ Real.log L + (Real.log 2 + 9 / 2 + oddProfileRatio / 2) + |s| := by
    have := oddProfileRatio_nonneg
    have h2 := Real.log_natCast_nonneg L
    have h3 := Real.log_two_gt_d9
    have := abs_nonneg s
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hrhs hC₀)

/-- **Floor against ceiling at conductor `s`.** -/
theorem floor_le_ceiling_conductor {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) (hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c) :
    β * (Real.log N ^ 2 - 2) - 2 * (4 * β + 2 * localDensityConst s / farJ ^ 2) * (1 + Real.log N) ≤
      (Real.log N + Real.log 2 + (Real.log 2 + 9 / 2 + oddProfileRatio / 2 + |s|)) *
        (1 + Real.log 2 + Real.log N) := by
  have hl2 := log_two_mul_nat hN
  have hNc' : Real.log N / 2 + 1 ≤ c := by
    have := Real.log_two_gt_d9; rw [hl2] at hNc; linarith
  have hT := smoothed_toeplitz_le_conductor h hN hNc
  rw [hl2] at hT
  have hF := floor_le_toeplitz_sum h hβ hN hNc'
  linarith

/-- **No conductor rescues a pole above one.** There is `K > 0` such that for every log-conductor `s` and every
window `c ≥ 11`, every nonempty cone of `(β, s)` has `β ≤ 1 + K(1 + |s|)/c`. -/
theorem exists_le_one_add_mul_div_of_datumCone :
    ∃ K : ℝ, 0 < K ∧ ∀ s c β : ℝ, 11 ≤ c → (datumCone β s c).Nonempty →
      β ≤ 1 + K * (1 + |s|) / c := by
  set C₀ : ℝ := Real.log 2 + 9 / 2 + oddProfileRatio / 2 with hC₀
  have hC0 : 0 ≤ C₀ := by have := oddProfileRatio_nonneg; have := Real.log_two_gt_d9; linarith
  have hJ := farJ_sq_pos
  have hm := farMass_nonneg
  have hl2 := Real.log_two_gt_d9
  set b₀ : ℝ := 2 * localDensityConst 0 / farJ ^ 2 with hb₀
  set κ : ℝ := 4 * farMass / farJ ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hb₀0 : 0 ≤ b₀ := by have := localDensityConst_nonneg 0; positivity
  have hbs : ∀ s : ℝ, 2 * localDensityConst s / farJ ^ 2 = b₀ + κ * |s| := fun s => by
    rw [hb₀, hκ]; unfold localDensityConst; simp only [abs_zero, mul_zero]; ring
  set R₀ : ℝ := (1 + 2 * Real.log 2 + C₀ + 2 * b₀) +
    ((Real.log 2 + C₀) * (1 + Real.log 2) + 2 * b₀) + 18 with hR₀
  set κ' : ℝ := 1 + 2 * κ + (1 + Real.log 2) + 2 * κ with hκ'
  have hκ'0 : 0 ≤ κ' := by rw [hκ']; linarith
  have hR₀0 : 0 ≤ R₀ := by rw [hR₀]; positivity
  refine ⟨2 * (R₀ + κ'), by positivity, fun s c β hc hne => ?_⟩
  have hs := abs_nonneg s
  obtain ⟨lam, hlam⟩ := hne
  rcases le_or_gt β 0 with hβ | hβ
  · have : 0 < 2 * (R₀ + κ') * (1 + |s|) / c := div_pos (by positivity) (by linarith)
    linarith
  set b : ℝ := 2 * localDensityConst s / farJ ^ 2 with hb
  have hb0 : 0 ≤ b := by have := localDensityConst_nonneg s; positivity
  set P : ℝ := 1 + 2 * Real.log 2 + (C₀ + |s|) + 2 * b with hP
  set Q : ℝ := (Real.log 2 + (C₀ + |s|)) * (1 + Real.log 2) + 2 * b with hQ
  have hP0 : 0 ≤ P := by rw [hP]; linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hPQ : P + Q + 18 = R₀ + κ' * |s| := by rw [hP, hQ, hb, hbs s, hR₀, hκ']; ring
  obtain ⟨N, hN, hlo, hNc⟩ := exists_level (c := c) (by linarith)
  have hmain := floor_le_ceiling_conductor hlam hβ.le hN hNc
  rw [← hC₀, ← hb] at hmain
  have key := le_one_add_div_of_quadratic (β := β) (c := c) hP0 hQ0 (X := Real.log N) (by linarith)
    (by linarith) (by linarith) (by rw [hP, hQ]; linarith)
  rw [hPQ] at key
  have hcpos : 0 < c := by linarith
  have hnum : 2 * (R₀ + κ' * |s|) ≤ 2 * (R₀ + κ') * (1 + |s|) := by nlinarith
  calc β ≤ 1 + 2 * (R₀ + κ' * |s|) / c := key
    _ ≤ 1 + 2 * (R₀ + κ') * (1 + |s|) / c := by gcongr

/-! ### The datum region -/

/-- The datum region: data whose cone is nonempty at every window. -/
def datumRegion : Set (ℝ × ℝ) := {p | ∀ c : ℝ, (datumCone p.1 p.2 c).Nonempty}

/-- **The datum region lies left of the residue line.** -/
theorem datumRegion_subset : datumRegion ⊆ {p : ℝ × ℝ | p.1 ≤ 1} := by
  intro p hp
  obtain ⟨K, hK, hup⟩ := exists_le_one_add_mul_div_of_datumCone
  show p.1 ≤ 1
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set M : ℝ := K * (1 + |p.2|) with hM
  have hM0 : 0 < M := by have := abs_nonneg p.2; positivity
  set c : ℝ := max 11 (M / ε + 1) with hc
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have h1 := hup p.2 c p.1 (le_max_left _ _) (hp c)
  have h2 : M / c < ε := by
    rw [div_lt_iff₀ hcpos]
    have : M / ε + 1 ≤ c := le_max_right _ _
    have h3 : M < ε * (M / ε + 1) := by field_simp; linarith
    nlinarith
  rw [← hM] at h1
  linarith

/-- The datum energy is affine in the datum and the weights jointly. -/
theorem datumEnergy_affine {β β' s s' a b : ℝ} (hab : a + b = 1) (x y : ℕ → ℝ) {f : ℝ → ℂ}
    (hfc : HasCompactSupport f) :
    datumEnergy (a * β + b * β') (a * s + b * s') (a • x + b • y) f =
      a * datumEnergy β s x f + b * datumEnergy β' s' y f := by
  have hk := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hk
  rw [datumEnergy_eq, datumEnergy_eq, datumEnergy_eq, re_weilFullFunctional_eq_affine (a • x + b • y) hN,
    re_weilFullFunctional_eq_affine x hN, re_weilFullFunctional_eq_affine y hN]
  have hsum : ∑ n ∈ Finset.range N, (if 2 ≤ n then (a • x + b • y) n / Real.sqrt n else 0) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      a * ∑ n ∈ Finset.range N, (if 2 ≤ n then x n / Real.sqrt n else 0) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re +
      b * ∑ n ∈ Finset.range N, (if 2 ≤ n then y n / Real.sqrt n else 0) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · ring
  rw [hsum]
  have hb' : b = 1 - a := by linarith
  subst hb'
  ring

/-- **The datum region is convex.** -/
theorem convex_datumRegion : Convex ℝ datumRegion := by
  intro p hp q hq a b ha hb hab c
  obtain ⟨x, hx⟩ := hp c
  obtain ⟨y, hy⟩ := hq c
  refine ⟨a • x + b • y, fun f hf hfs => ?_⟩
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have e := datumEnergy_affine (β := p.1) (β' := q.1) (s := p.2) (s' := q.2) hab x y hfc
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [e]
  exact add_nonneg (mul_nonneg ha (hx f hf hfs)) (mul_nonneg hb (hy f hf hfs))

/-- **The no-pole ray.** `(0, s) ∈ 𝒟` for `s ≥ log π − ψ(¼)`: the zero weights work at every window. -/
theorem zero_mem_datumRegion {s : ℝ} (hs : -EF.gammaBracket 0 ≤ s) : ((0 : ℝ), s) ∈ datumRegion :=
  fun c => ⟨_, forall_zero_mem_datumCone_zero_iff.mpr hs c⟩

/-- **The conductor-one axis.** `(β, 0) ∈ 𝒟` iff `β = 1` and RH. -/
theorem mem_datumRegion_axis_iff {β : ℝ} :
    (β, (0 : ℝ)) ∈ datumRegion ↔ β = 1 ∧ RiemannHypothesis := by
  constructor
  · intro hp
    have hle : β ≤ 1 := datumRegion_subset hp
    have hge : 1 ≤ β := by
      obtain ⟨K', c₁, hK', hlow⟩ := exists_one_sub_le_of_datumCone
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have hlim : Tendsto (fun c => K' * marginCeiling c) atTop (𝓝 0) := by
        simpa using tendsto_marginCeiling.const_mul K'
      obtain ⟨c₂, hc₂⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
      have h1 := hlow (max c₁ c₂) β (le_max_left _ _) (hp _)
      have h2 := hc₂ (max c₁ c₂) (le_max_right _ _)
      linarith
    have h1 : β = 1 := le_antisymm hle hge
    refine ⟨h1, riemannHypothesis_iff_forall_datumCone_one_zero_nonempty.mpr fun c _ => ?_⟩
    have := hp c
    rwa [h1] at this
  · rintro ⟨rfl, hRH⟩ c
    rcases le_or_gt (3 / 10) c with hc | hc
    · exact riemannHypothesis_iff_forall_datumCone_one_zero_nonempty.mp hRH c hc
    · obtain ⟨lam, hlam⟩ := riemannHypothesis_iff_forall_datumCone_one_zero_nonempty.mp hRH
        (3 / 10) le_rfl
      exact ⟨lam, datumCone_anti hc.le hlam⟩

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
