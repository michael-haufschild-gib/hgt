import GaloisForLFunctions.RHTower.EvenSectorPoleFreeResonatorPositivity
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# The log-density ceiling of even-positive weights at every pole weight

**Theorem** (`even_log_density_le`).  If `lam` is Weil-positive at some pole weight `β` on the
autocorrelations of even compactly supported `C²` tests, then for every `ε > 0` and all large `N`,
`Σ_{n ≥ 2, m ≥ 1, nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)(log N)²`.

In the logarithmic mean `Σ_{k ≤ N} (lam ⋆ 1)(k)/k` an even-positive weight system has density at
most one, the density of `Λ`, whatever the pole weight.  For `β > 1` even positivity does not
imply full positivity (the pole term of a non-even test has no sign), so the full-cone ceiling
does not apply directly.

Proof.  The Weil–Toeplitz bound reads positivity on a single resonator
`R_N = Σ_{m ≤ N} m^{−1/2} g_w(· − log m + (log N)/2)` per level, `w = 1/(N+1)`
(`weil_multiplicativeToeplitz_bound_of_resonator`).  Its profile `g_w = ψ_w'' − ψ_w/4` is even
(`gR_neg`) with `ĝ_w(±i/2) = 0`, and its coefficients are positive, so pole-free even positivity
transfers to it (`re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenAt`).  For a polar
test, nonnegativity of the Weil functional is nonnegativity of the finite-atom symbol
(`integral_weilAtomSymbol_nonneg_of_polar`).  The coefficient vector `m^{−1/2}` turns the bound into
`2 Σ_{nm ≤ N} lam(n)/(nm) ≤ (log N + C₀)(1 + log N)` (`even_unit_toeplitz_bound`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open ResonatorProfile

/-! ## Parity of the resonator profile -/

theorem resonatorBump_neg (v : ℝ) : Ψ (-v) = Ψ v := by
  unfold Ψ; exact weilBump.neg v

theorem resonatorBump_deriv_neg (v : ℝ) : d1 (-v) = -d1 v := by
  have h : (fun y => Ψ (-y)) = Ψ := funext resonatorBump_neg
  have h1 := deriv_comp_neg Ψ (-v)
  rw [h, neg_neg] at h1
  exact h1

theorem resonatorBump_deriv_deriv_neg (v : ℝ) : d2 (-v) = d2 v := by
  have h : (fun y => d1 (-y)) = fun y => -d1 y := funext resonatorBump_deriv_neg
  have h1 := deriv_comp_neg d1 (-v)
  rw [h, deriv.fun_neg, neg_neg] at h1
  exact neg_inj.mp h1

/-- The polar-free profile `g_w = ψ_w'' − ψ_w/4` is even. -/
theorem gR_neg (w u : ℝ) : gR w (-u) = gR w u := by
  unfold gR
  rw [neg_div, resonatorBump_deriv_deriv_neg, resonatorBump_neg]

/-! ## Polar tests: the Weil functional and the finite-atom symbol -/

/-- For a polar test supported in `[−a, a]`, nonnegativity of the Weil functional is
nonnegativity of the finite-atom symbol at level `a`. -/
theorem integral_weilAtomSymbol_nonneg_of_polar {lam : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) (hW : 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re) :
    0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
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

/-! ## The unit resonator -/

/-- The coefficients `m^{−1/2}` on `[1, N]`. -/
def unitResonatorCoeff (N m : ℕ) : ℂ := if m ≤ N then ((1 / Real.sqrt m : ℝ) : ℂ) else 0

theorem resonator_unitResonatorCoeff (N : ℕ) (w : ℝ) :
    resonator N (unitResonatorCoeff N) w =
      fun u => ((∑ m ∈ Finset.Icc 1 N, 1 / Real.sqrt m * gR w (u - resPt N m) : ℝ) : ℂ) := by
  funext u
  unfold resonator
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [unitResonatorCoeff, if_pos (Finset.mem_Icc.mp hm).2, Complex.ofReal_mul]
  rfl

/-- **Even positivity at any pole weight gives the Toeplitz hypothesis on the unit resonator.** -/
theorem integral_weilAtomSymbol_unitResonator_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) (N : ℕ) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (resonator N (unitResonatorCoeff N) (1 / ((N : ℝ) + 1))) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊
        (τ / (2 * π)) := by
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨hp1, hp2⟩ := paperFT_resonator_pole (N := N) (c := unitResonatorCoeff N) hw
  have ha : 0 ≤ Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4 := by
    have := Real.log_natCast_nonneg N
    positivity
  refine integral_weilAtomSymbol_nonneg_of_polar ha (contDiff_resonator N _ _ 2)
    (tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (fun v hv => gC_eq_zero hw hv) hu) hp1 hp2 ?_
  have hgc : HasCompactSupport (gR (1 / ((N : ℝ) + 1))) :=
    (hasCompactSupport_comp_left (g := Complex.ofReal) fun {_} => Complex.ofReal_eq_zero).mp
      (hasCompactSupport_gC hw)
  rw [resonator_unitResonatorCoeff]
  exact re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenAt h (Finset.Icc 1 N)
    (c := fun m => 1 / Real.sqrt m) (fun m _ => by positivity) (resPt N)
    (contDiff_gR _ 2) hgc (gR_neg _) (paperFT_gC_pole hw).1

/-- **The unit Weil–Toeplitz bound for even-positive weights.**  For every `N ≥ 1`,
`2 Σ_{n ≥ 2, m ≥ 1, nm ≤ N} lam(n)/(nm) ≤ (log N + C₀) Σ_{m ≤ N} 1/m`. -/
theorem even_unit_toeplitz_bound {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then lam n / (n * m) else 0) ≤
      (Real.log N + (Real.log 2 + 9 / 2 + profileRatio / 2)) *
        ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
  have hc : ∀ m, N < m → unitResonatorCoeff N m = 0 := fun m hm => by
    simp [unitResonatorCoeff, not_le.mpr hm]
  have hb := weil_multiplicativeToeplitz_bound_of_resonator hN (unitResonatorCoeff N) hc
    (integral_weilAtomSymbol_unitResonator_nonneg h N)
  have hlhs : ∀ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, unitResonatorCoeff N (n * m) * conj (unitResonatorCoeff N m)).re =
      ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then lam n / (n * m) else 0) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    by_cases hnm : n * m ≤ N
    · rw [if_pos hnm]
      simp only [unitResonatorCoeff, if_pos hnm, if_pos hmN, Complex.conj_ofReal,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      have hsq : Real.sqrt ((n * m : ℕ) : ℝ) = Real.sqrt n * Real.sqrt m := by
        push_cast; exact Real.sqrt_mul hn1.le _
      rw [hsq]
      have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn1.le
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn1
      have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
      calc lam n / Real.sqrt n * (1 / (Real.sqrt n * Real.sqrt m) * (1 / Real.sqrt m))
          = lam n / ((Real.sqrt n * Real.sqrt n) * (Real.sqrt m * Real.sqrt m)) := by
            field_simp
        _ = lam n / (n * m) := by rw [hsn, hsm]
    · rw [if_neg hnm]
      simp [unitResonatorCoeff, if_neg hnm]
  have hrhs : ∑ m ∈ Finset.Icc 1 N, ‖unitResonatorCoeff N m‖ ^ 2 =
      ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    simp only [unitResonatorCoeff, if_pos hmN, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_pow, one_pow, Real.sq_sqrt hm0.le]
  rw [Finset.sum_congr rfl hlhs, hrhs] at hb
  exact hb

/-- **The log-density ceiling at every pole weight.**  Weights that are Weil-positive at some pole
weight `β` on all even tests satisfy `Σ_{n ≥ 2, m ≥ 1, nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)(log N)²`
for all large `N`. -/
theorem even_log_density_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then lam n / (n * m) else 0) ≤ (1 / 2 + ε) * Real.log N ^ 2 := by
  set C₀ : ℝ := Real.log 2 + 9 / 2 + profileRatio / 2 with hC₀
  set L₀ : ℝ := 2 * (|C₀| + 1) / ε + |C₀| + 1 with hL₀
  refine ⟨⌈Real.exp L₀⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : L₀ ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNr]
    have h1 : Real.exp L₀ ≤ ⌈Real.exp L₀⌉₊ := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈Real.exp L₀⌉₊ ≤ N by omega)
    linarith
  have hq0 : 0 ≤ 2 * (|C₀| + 1) / ε := by positivity
  have hL1 : 1 ≤ L₀ := by rw [hL₀]; linarith [abs_nonneg C₀]
  set L := Real.log N with hLdef
  have hχ := even_unit_toeplitz_bound h hN1
  have hH := sum_Icc_inv_le_one_add_log N
  have hLC : 0 ≤ L + C₀ := by
    have h1 : |C₀| + 1 ≤ L₀ := by rw [hL₀]; linarith
    linarith [neg_abs_le C₀]
  have hstep : 2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then lam n / (n * m) else 0) ≤ (L + C₀) * (1 + L) :=
    hχ.trans (mul_le_mul_of_nonneg_left hH hLC)
  have hquad : (L + C₀) * (1 + L) ≤ (1 + 2 * ε) * L ^ 2 := by
    have hLpos : 1 ≤ L := hL1.trans hlog
    have hdiv : 2 * (|C₀| + 1) / ε ≤ L := by rw [hL₀] at hlog; linarith [abs_nonneg C₀]
    have hbig : 2 * (|C₀| + 1) ≤ L * ε := (div_le_iff₀ hε).mp hdiv
    have hC : C₀ ≤ |C₀| := le_abs_self C₀
    have h1 : (L + C₀) * (1 + L) ≤ L ^ 2 + 2 * (|C₀| + 1) * L := by nlinarith [abs_nonneg C₀]
    have h2 : 2 * (|C₀| + 1) * L ≤ ε * L ^ 2 := by nlinarith
    nlinarith
  linarith

end RHTower.EvenSector

end
