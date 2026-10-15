import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound

/-!
# The Weil–Toeplitz bound for an arbitrary narrow profile

**Theorem** (`weil_multiplicativeToeplitz_bound_of_profile`).  Let `N ≥ 1`, `w = 1/(N+1)`, and let
`q` be a real `C³` profile vanishing on `|u| > w/4` with `w² ∫ q'² ≤ K ∫ q²`.  If the finite-atom
Weil symbol with weights `lam` is nonnegative on the single resonator
`Σ_{m ≤ N} c(m) q(· − log m + (log N)/2)`, then
`2 Σ_{2 ≤ n ≤ N} lam(n) n^{-1/2} Re Σ_m c(nm) conj(c m) ≤ (log N + log 2 + 9/2 + K/2) Σ_m |c m|²`.

The proof is the one of `weil_multiplicativeToeplitz_bound_of_resonator`, with the corpus profile
`g_w = ψ_w'' − ψ_w/4` replaced by `q`.  The bumps are `1/(N+1)` narrow, so the autocorrelation of
the resonator meets the atom `log n` only on the multiplicative diagonal `m = n m'`; the
archimedean symbol is at most `log(1/w) + O(1) + w²τ²/2` on the spectrum, and the profile ratio `K`
controls the last term.  The parity of `q` plays no role.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23
open ComplexConjugate

namespace RHTower

noncomputable section

open ResonatorProfile

/-- The resonator with real profile `q`: `Σ_{m ≤ N} c(m) q(u − log m + (log N)/2)`. -/
def profileResonator (N : ℕ) (c : ℕ → ℂ) (q : ℝ → ℝ) (u : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, c m * ((q (u - resPt N m) : ℝ) : ℂ)

theorem contDiff_profileResonator (N : ℕ) (c : ℕ → ℂ) {q : ℝ → ℝ} {n : ℕ}
    (hq : ContDiff ℝ n q) : ContDiff ℝ n (profileResonator N c q) := by
  unfold profileResonator
  exact ContDiff.sum fun m _ => contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (hq.comp (contDiff_id.sub contDiff_const)))

theorem deriv_profileResonator (N : ℕ) (c : ℕ → ℂ) {q : ℝ → ℝ} (hq : Differentiable ℝ q) :
    deriv (profileResonator N c q) = profileResonator N c (deriv q) := by
  funext u
  have h : HasDerivAt (profileResonator N c q) (profileResonator N c (deriv q) u) u := by
    unfold profileResonator
    apply HasDerivAt.fun_sum
    intro m _
    have hd : HasDerivAt q (deriv q (u - resPt N m)) (u - resPt N m) :=
      (hq (u - resPt N m)).hasDerivAt
    exact ((hd.comp_sub_const u (resPt N m)).ofReal_comp).const_mul (c m)
  exact h.deriv

/-- **The Weil–Toeplitz bound for a narrow profile.** -/
theorem weil_multiplicativeToeplitz_bound_of_profile {lam : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (c : ℕ → ℂ) (hc : ∀ m, N < m → c m = 0) {q : ℝ → ℝ} (hq : ContDiff ℝ 3 q)
    (hqv : ∀ u, 1 / ((N : ℝ) + 1) / 4 < |u| → q u = 0) (hq0 : 0 < ∫ u, q u ^ 2) {K : ℝ}
    (hK : (1 / ((N : ℝ) + 1)) ^ 2 * ∫ u, deriv q u ^ 2 ≤ K * ∫ u, q u ^ 2)
    (hW : 0 ≤ ∫ τ : ℝ, ‖paperFT (profileResonator N c q) τ‖ ^ 2 * weilAtomSymbol lam
        ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊ (τ / (2 * π))) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
      (Real.log N + (Real.log 2 + 9 / 2 + K / 2)) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
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
          rw [integral_add (hint2.const_mul α) (hint3.const_mul β), integral_const_mul,
            integral_const_mul]
      _ = α * (2 * π * k0r * sumc) + β * (2 * π * k1r * sumc) := by rw [hmass0, hmass1]
  have hratio : β * k1r ≤ K / 2 * k0r := by
    rw [hβ, hk1r, hk0r]; nlinarith
  have hlog2 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith)
  set T : ℝ := ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * (S n).re with hT
  rw [hatoms] at hpos
  have hk2 : 0 < 2 * π * k0r := by positivity
  have hmain : 2 * π * k0r * (2 * T) ≤ 2 * π * k0r * ((α + K / 2) * sumc) := by
    have h1 : β * (2 * π * k1r * sumc) ≤ 2 * π * sumc * (K / 2 * k0r) := by
      have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * π * sumc by positivity)
      linarith
    nlinarith
  have h2T : 2 * T ≤ (α + K / 2) * sumc := le_of_mul_le_mul_left hmain hk2
  calc 2 * T ≤ (α + K / 2) * sumc := h2T
    _ ≤ (Real.log N + (Real.log 2 + 9 / 2 + K / 2)) * sumc := by
        apply mul_le_mul_of_nonneg_right _ hsum
        rw [hα]; linarith

end

end RHTower
