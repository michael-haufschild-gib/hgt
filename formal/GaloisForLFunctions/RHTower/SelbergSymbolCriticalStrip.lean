import GaloisForLFunctions.RHTower.ClusterRobustHodgeExclusion
import GaloisForLFunctions.RHTower.SelbergTruncatedVonMangoldtKreinCompletion
import Zeta23.ExplicitFormula.Bridge
import Zeta23.GammaFacts.Complete
import Zeta23.WeilEF.Main

/-!
# A Selberg symbol inequality at level `a` forces a critical strip of width `1/a`

For a weight `w` with `w(d) = 1` on `[1, ⌊e^{2a}⌋]` and a cutoff `N ≥ ⌊e^{2a}⌋`, let
`Λ_w = (μw) ⋆ log` be the Selberg-weighted von Mangoldt function and
`weilAtomSymbol(Λ_w, N)(ξ) = Re ψ(¼ + iπξ) - log π - 2 ∑_{2 ≤ n ≤ N} Λ_w(n) n^{-1/2} cos(2πξ log n)`
the finite-cutoff Weil symbol.

* **The symbol represents the zero side** (`zeta_W_eq_integral_selbergSymbol`).  For a `C²` test
  `f` supported in `[-a, a]` with `h_f(±i/2) = 0`, the explicit formula for `ζ` gives
  `∑_ρ m_ρ h_f(γ_ρ) conj(h_f(conj γ_ρ)) = (1/2π) ∫ |h_f(τ)|² weilAtomSymbol(Λ_w, N)(τ/2π) dτ`.
  The pole terms vanish.  The atoms at `n > e^{2a}` sit at invisible frequencies:
  `∫ |h_f|² cos(τ log n) = π(k(log n) + k(-log n)) = 0` for `k = f ⋆ f̃`.
* **Equivalence** (`hodgeIndexAtLevel_iff_selbergSymbolPositive`).  Nonnegativity of the Selberg
  symbol form on polar-constrained tests at level `a` is the level-`a` Hodge index of `ζ`, for
  every admissible completion `(w, N)`.
* **Critical strip** (`zeta_selbergSymbol_forces_critical_strip`).  With the horizon of
  `ClusterRobustHodgeExclusion`: if the symbol form is nonnegative at a level `a ≥ e⁶`, then every
  zero with `|γ| ≥ 2` and `10⁵ A₀ log(|γ| + 306) log² a ≤ a` has `|β - ½| < 1/a`.  The same holds
  for a pointwise nonnegative symbol (`zeta_selbergSymbol_nonneg_forces_critical_strip`).  In the
  height form (`zeta_selbergSymbol_forces_strip_up_to_height`), one level `a` with
  `a ≍ A₀ log T (log log T)²` puts every zero up to height `T` within `1/a` of the critical line.
* **Consistency.**  The Riemann hypothesis gives the symbol inequality at every level
  (`selbergSymbolPositiveAtLevel_of_forall_re_eq_half`).  Conversely, the inequality at all large
  levels gives `β = ½` for every zero with `|γ| ≥ 2`
  (`zeta_re_eq_half_of_selbergSymbol_eventually`).

A single finite-cutoff Selberg symbol inequality at level `a` is therefore a statement about zeros
hugging the critical line, of width `1/a` up to height `exp(a/(10⁵ A₀ log² a))`.  Zero-free regions
of de la Vallée-Poussin or Korobov–Vinogradov type only confine `1 - β`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23

/-! ### The zero side of a polar-constrained test -/

theorem paperFT_weilTest_self_ofReal {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (τ : ℝ) : paperFT (EF.weilTest f f) τ = ((‖paperFT f τ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EF.paperFT_weilTest hf hf hfc hfc, Complex.conj_ofReal, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- For a polar-constrained `C²` test supported in `[-a, a]`, the explicit formula for `ζ` writes
the zero side as `∫ h_{f⋆f̃}(τ)(μ(τ) + P_X(τ)) dτ` with `X = e^{2a}`: the pole terms vanish. -/
theorem zeta_W_eq_integral_mu_add_PX {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) :
    zetaZeroConfig.W f f =
      ∫ τ : ℝ, paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ) := by
  have hfs' : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  set k := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hks : tsupport k ⊆ Icc (-(2 * a)) (2 * a) := EF.tsupport_weilTest_subset hfs' hfs'
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have hμ := EF.integrable_paperFT_mul_mu hkd hkc gammaFacts
  have hPX := EF.integrable_paperFT_mul_PX (2 * a) hFk
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig k hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hk, hfac, mul_assoc]
  have hpole1 : paperFT k (I / 2) = 0 := by rw [hk, hfac, hp, zero_mul]
  have hpole2 : paperFT k (-I / 2) = 0 := by rw [hk, hfac, neg_div, hm, zero_mul]
  rw [ZeroConfig.W, ← hterm, heq, EF.literatureRHS, hpole1, hpole2, zero_add, zero_sub,
    EF.prime_term hkd.continuous hks hFk, EF.gamma_term, ← integral_add hPX hμ]
  congr 1
  ext τ
  push_cast
  ring


/-! ### The Weil symbol of the von Mangoldt weights -/

/-- `weilAtomSymbol Λ ⌊X⌋ (τ/2π) = 2π(μ(τ) + P_X(τ))`: the finite-atom Weil symbol at the
cutoff `⌊X⌋` is the density `μ + P_X` of the explicit formula, in the frequency `τ = 2πξ`. -/
theorem weilAtomSymbol_vonMangoldt_eq (X τ : ℝ) :
    weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊X⌋₊ (τ / (2 * π)) = 2 * π * (mu τ + PX X τ) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold weilAtomSymbol
  rw [archimedeanWeilSymbol_eq]
  have harg : ((1 / 4 : ℝ) : ℂ) + ((π * (τ / (2 * π)) : ℝ) : ℂ) * I = 1 / 4 + I * τ / 2 := by
    have : π * (τ / (2 * π)) = τ / 2 := by field_simp
    rw [this]; push_cast; ring
  rw [harg]
  have hterm : ∀ n : ℕ, (Λ n : ℝ) * (1 / Real.sqrt n) *
      (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) =
      2 * ((Λ n : ℝ) / Real.sqrt n * Real.cos (τ * Real.log n)) := by
    intro n
    have : 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n := by field_simp
    rw [this]; ring
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, (Λ n : ℝ) * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) =
      2 * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n * Real.cos (τ * Real.log n) := by
    rw [Finset.sum_congr rfl (fun n _ => hterm n), ← Finset.mul_sum]
    congr 1
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioc]; omega
    · intro n hn hn'
      simp only [Finset.mem_Ioc] at hn
      simp only [Finset.mem_Icc, not_and, not_le] at hn'
      have h1 : n = 1 := by omega
      subst h1; simp
  rw [hsum]
  unfold mu PX
  field_simp
  ring


/-- The zero side of a polar-constrained level-`a` test is `(1/2π)∫ |h_f(τ)|² S(τ/2π) dτ`, with
`S = weilAtomSymbol Λ ⌊e^{2a}⌋`. -/
theorem zeta_W_eq_integral_weilAtomSymbol_vonMangoldt {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) :
    zetaZeroConfig.W f f = ((1 / (2 * π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) : ℝ) : ℂ) := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  rw [zeta_W_eq_integral_mu_add_PX hf hfs hp hm, ← integral_const_mul, ← integral_complex_ofReal]
  congr 1
  ext τ
  rw [paperFT_weilTest_self_ofReal hf.continuous hfc, weilAtomSymbol_vonMangoldt_eq]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

/-- Data of a polar-constrained level-`a` test: the Weil test `f ⋆ f̃`, its support in
`[-2a, 2a]`, and the integrability of its transform. -/
theorem weilTest_self_data {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    HasCompactSupport f ∧ ContDiff ℝ 2 (EF.weilTest f f) ∧
      tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) ∧
      Integrable (EF.weilTest f f) ∧ Integrable (FourierTransform.fourier (EF.weilTest f f)) := by
  have hfs' : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hkd := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc := EF.weilTest_hasCompactSupport hfc hfc
  exact ⟨hfc, hkd, EF.tsupport_weilTest_subset hfs' hfs',
    hkd.continuous.integrable_of_hasCompactSupport hkc,
    EF.integrable_fourier_of_contDiff_two hkd hkc⟩

/-- `|h_f|²` is integrable on the real line. -/
theorem integrable_normSq_paperFT {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2) := by
  obtain ⟨hfc, -, -, -, hFk⟩ := weilTest_self_data hf hfs
  have h := (EF.integrable_paperFT_ofReal hFk).norm
  refine h.congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [paperFT_weilTest_self_ofReal hf.continuous hfc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- **Invisible frequencies.**  For a `C²` test supported in `[-a, a]` and `|y| > 2a`,
`∫ |h_f(τ)|² cos(τy) dτ = 0`: by inversion it is `π(k(y) + k(-y))` with `k = f ⋆ f̃`. -/
theorem integral_normSq_paperFT_mul_cos_eq_zero {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {y : ℝ} (hy : 2 * a < |y|) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * y) = 0 := by
  obtain ⟨hfc, hkd, hks, hki, hFk⟩ := weilTest_self_data hf hfs
  have hinv := EF.k_add_k_neg hkd.continuous hki hFk y
  have h1 : EF.weilTest f f y = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hks hmem
    rw [mem_Icc] at this
    have := abs_le.mpr ⟨this.1, this.2⟩
    linarith
  have h2 : EF.weilTest f f (-y) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hks hmem
    rw [mem_Icc] at this
    have : |y| ≤ 2 * a := by rw [abs_le]; constructor <;> linarith [this.1, this.2]
    linarith
  rw [h1, h2, add_zero] at hinv
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hint : ∫ τ : ℝ, paperFT (EF.weilTest f f) τ * (Real.cos (τ * y) : ℂ) = 0 := by
    have := hinv.symm
    rw [mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (by simp [hπ])
    · exact h
  have hreal : (fun τ : ℝ => paperFT (EF.weilTest f f) τ * (Real.cos (τ * y) : ℂ)) =
      fun τ : ℝ => ((‖paperFT f τ‖ ^ 2 * Real.cos (τ * y) : ℝ) : ℂ) := by
    ext τ; rw [paperFT_weilTest_self_ofReal hf.continuous hfc]; push_cast; ring
  rw [hreal, integral_complex_ofReal] at hint
  exact_mod_cast hint


theorem integrable_normSq_paperFT_mul_cos {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (y : ℝ) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * Real.cos (τ * y)) := by
  obtain ⟨hfc, -, -, -, hFk⟩ := weilTest_self_data hf hfs
  refine (EF.integrable_paperFT_mul_cos hFk y).re.congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [paperFT_weilTest_self_ofReal hf.continuous hfc, ← Complex.ofReal_mul]
  exact RCLike.ofReal_re _

theorem integrable_normSq_paperFT_mul_weilAtomSymbol {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) := by
  obtain ⟨hfc, hkd, hks, -, hFk⟩ := weilTest_self_data hf hfs
  have hkc := EF.hasCompactSupport_of_tsupport_subset hks
  have hμ := EF.integrable_paperFT_mul_mu hkd hkc gammaFacts
  have hPX := EF.integrable_paperFT_mul_PX (2 * a) hFk
  refine (((hμ.add hPX).re).const_mul (2 * π)).congr (Eventually.of_forall fun τ => ?_)
  simp only [Pi.add_apply]
  rw [paperFT_weilTest_self_ofReal hf.continuous hfc, weilAtomSymbol_vonMangoldt_eq,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  ring

/-- **Completion invariance.**  Any weights `λ` equal to `Λ` on `[0, ⌊e^{2a}⌋]` and any cutoff
`N ≥ ⌊e^{2a}⌋` give the same symbol integral against `|h_f|²` for tests supported in `[-a, a]`:
the atoms at `n > e^{2a}` are invisible frequencies. -/
theorem integral_weilAtomSymbol_completion {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) {lam : ℕ → ℝ} {N : ℕ}
    (hlam : ∀ n, n ≤ ⌊Real.exp (2 * a)⌋₊ → lam n = Λ n) (hN : ⌊Real.exp (2 * a)⌋₊ ≤ N) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * π)) =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
  set X := ⌊Real.exp (2 * a)⌋₊ with hXdef
  have hX1 : 1 ≤ X := Nat.le_floor (by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 2 * a by linarith); exact_mod_cast this)
  have hset : Finset.Icc 2 N = Finset.Icc 2 X ∪ Finset.Ioc X N := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 2 X) (Finset.Ioc X N) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  have hsplit : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * π)) =
      ‖paperFT f τ‖ ^ 2 * weilAtomSymbol (fun n => (Λ n : ℝ)) X (τ / (2 * π)) -
        ∑ n ∈ Finset.Ioc X N, (2 * lam n / Real.sqrt n) *
          (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) := by
    intro τ
    unfold weilAtomSymbol
    rw [hset, Finset.sum_union hdisj]
    have hsame : ∑ n ∈ Finset.Icc 2 X, lam n * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) =
        ∑ n ∈ Finset.Icc 2 X, (Λ n : ℝ) * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) :=
      Finset.sum_congr rfl fun n hn => by rw [hlam n (Finset.mem_Icc.mp hn).2]
    have harg : ∀ n : ℕ, 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n := fun n => by
      field_simp
    rw [hsame]
    simp only [harg]
    have hS2 : ∑ n ∈ Finset.Ioc X N, (2 * lam n / Real.sqrt n) *
        (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) =
        ‖paperFT f τ‖ ^ 2 * ∑ n ∈ Finset.Ioc X N,
          lam n * (1 / Real.sqrt n) * (2 * Real.cos (τ * Real.log n)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    rw [hS2]
    ring
  have hint := integrable_normSq_paperFT_mul_weilAtomSymbol hf hfs
  have hcos := integrable_normSq_paperFT_mul_cos hf hfs
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_sub hint
    (integrable_finsetSum _ fun n _ => (hcos _).const_mul _),
    integral_finsetSum _ fun n _ => (hcos _).const_mul _]
  have hzero : ∀ n ∈ Finset.Ioc X N, ∫ τ : ℝ, (2 * lam n / Real.sqrt n) *
      (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) = 0 := by
    intro n hn
    rw [integral_const_mul]
    have hnX : X < n := (Finset.mem_Ioc.mp hn).1
    have hexp : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hnX
    have hlog : 2 * a < Real.log n := by
      rw [← Real.log_exp (2 * a)]; exact Real.log_lt_log (Real.exp_pos _) hexp
    have habs : 2 * a < |Real.log n| := lt_of_lt_of_le hlog (le_abs_self _)
    rw [integral_normSq_paperFT_mul_cos_eq_zero hf hfs habs, mul_zero]
  rw [Finset.sum_eq_zero hzero, sub_zero]


/-! ### Selberg completions and the Hodge index -/

/-- **The Selberg symbol represents the zero side.**  For every weight `w` with `w(d) = 1` on
`[1, ⌊e^{2a}⌋]` and every cutoff `N ≥ ⌊e^{2a}⌋`, the zero side of a polar-constrained `C²` test
supported in `[-a, a]` is `(1/2π)∫ |h_f(τ)|² weilAtomSymbol(Λ_w, N)(τ/2π) dτ`. -/
theorem zeta_W_eq_integral_selbergSymbol {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) {w : ℕ → ℝ}
    (hw : ∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) {N : ℕ}
    (hN : ⌊Real.exp (2 * a)⌋₊ ≤ N) :
    zetaZeroConfig.W f f = ((1 / (2 * π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (selbergWeightedVonMangoldt w) N (τ / (2 * π)) : ℝ) : ℂ) := by
  rw [zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm,
    integral_weilAtomSymbol_completion ha hf hfs
      (fun n hn => selbergWeightedVonMangoldt_eq_vonMangoldt_of_le hw hn) hN]

/-- Positivity of the level-`a` Selberg symbol form on polar-constrained tests. -/
def SelbergSymbolPositiveAtLevel (a : ℝ) (w : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
    paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (selbergWeightedVonMangoldt w) N (τ / (2 * π))

/-- **Every admissible Selberg completion gives the Hodge index.**  For `a ≥ 0`, `w = 1` on
`[1, ⌊e^{2a}⌋]` and `N ≥ ⌊e^{2a}⌋`, positivity of the Selberg symbol form at level `a` is
equivalent to the level-`a` Hodge index of `ζ`. -/
theorem hodgeIndexAtLevel_iff_selbergSymbolPositive {a : ℝ} (ha : 0 ≤ a) {w : ℕ → ℝ}
    (hw : ∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) {N : ℕ}
    (hN : ⌊Real.exp (2 * a)⌋₊ ≤ N) :
    HodgeIndexAtLevel zetaZeroConfig a ↔ SelbergSymbolPositiveAtLevel a w N := by
  have hπ : 0 < 1 / (2 * π) := by positivity
  constructor
  · intro h f hf hfs hp hm
    have := h f hf hfs hp hm
    rw [zeta_W_eq_integral_selbergSymbol ha hf hfs hp hm hw hN, Complex.ofReal_re] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hπ
  · intro h f hf hfs hp hm
    rw [zeta_W_eq_integral_selbergSymbol ha hf hfs hp hm hw hN, Complex.ofReal_re]
    exact mul_nonneg hπ.le (h f hf hfs hp hm)

/-- A pointwise nonnegative Selberg symbol gives positivity of the symbol form. -/
theorem selbergSymbolPositiveAtLevel_of_symbol_nonneg {a : ℝ} {w : ℕ → ℝ} {N : ℕ}
    (hσ : ∀ ξ : ℝ, 0 ≤ weilAtomSymbol (selbergWeightedVonMangoldt w) N ξ) :
    SelbergSymbolPositiveAtLevel a w N := fun _ _ _ _ _ =>
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (hσ _)

/-- Under the Riemann hypothesis the level-`a` Hodge index of `ζ` holds at every level: the zero
side is `∑ m_ρ |h_f(γ_ρ)|²`. -/
theorem hodgeIndexAtLevel_of_forall_re_eq_half
    (hRH : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) (a : ℝ) :
    HodgeIndexAtLevel zetaZeroConfig a := by
  intro f hf hfs _ _
  obtain ⟨hfc, hkd, hks, -, -⟩ := weilTest_self_data hf hfs
  have hkc := EF.hasCompactSupport_of_tsupport_subset hks
  obtain ⟨hsum, -⟩ := WeilEF.EF_lit_zetaZeroConfig _ hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (EF.weilTest f f) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  rw [hterm] at hsum
  rw [ZeroConfig.W, Complex.re_tsum hsum]
  refine tsum_nonneg fun ρ => ?_
  have hreal : conj (gammaOf (ρ : ℂ)) = gammaOf ρ := by
    apply Complex.conj_eq_iff_im.mpr
    rw [WeilEF.gammaOf_im, hRH ρ ρ.2]; ring
  simp only [ZeroConfig.Wsummand, hreal]
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

/-! ### The critical strip forced by a Selberg symbol inequality -/

/-- **A Selberg symbol inequality at level `a` forces a critical strip of width `1/a`.**  There is
`A₀` such that for every level `a ≥ e⁶`, every weight `w` with `w = 1` on `[1, ⌊e^{2a}⌋]` and every
cutoff `N ≥ ⌊e^{2a}⌋`: if the Selberg symbol form is nonnegative on polar-constrained tests
supported in `[-a, a]`, then every zero of `ζ` with `|γ| ≥ 2` and
`10⁵ A₀ log(|γ| + 306) log² a ≤ a` satisfies `|β - ½| < 1/a`. -/
theorem zeta_selbergSymbol_forces_critical_strip :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (a : ℝ) (w : ℕ → ℝ) (N : ℕ), Real.exp 6 ≤ a →
      (∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) → ⌊Real.exp (2 * a)⌋₊ ≤ N →
      SelbergSymbolPositiveAtLevel a w N →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| →
        10 ^ 5 * A₀ * Real.log (|ρ.im| + 306) * Real.log a ^ 2 ≤ a →
        |ρ.re - 1 / 2| < 1 / a := by
  obtain ⟨A₀, hA₀, H⟩ := zeta_hodge_index_cluster_horizon
  refine ⟨A₀, hA₀, fun a w N ha6 hw hN hsel ρ hρ hγ hsize => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  have hodge := (hodgeIndexAtLevel_iff_selbergSymbolPositive ha0.le hw hN).mpr hsel
  by_contra hge
  push Not at hge
  have hδ : 0 < |ρ.re - 1 / 2| := lt_of_lt_of_le (by positivity) hge
  have h1δ : 1 / |ρ.re - 1 / 2| ≤ a := by
    rw [div_le_iff₀ hδ]
    rw [div_le_iff₀ ha0] at hge
    linarith
  exact H _ hδ ρ hρ le_rfl hγ a ha6 h1δ hsize hodge

/-- The same conclusion from a pointwise nonnegative Selberg symbol (a positive Krein symbol). -/
theorem zeta_selbergSymbol_nonneg_forces_critical_strip :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (a : ℝ) (w : ℕ → ℝ) (N : ℕ), Real.exp 6 ≤ a →
      (∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) → ⌊Real.exp (2 * a)⌋₊ ≤ N →
      (∀ ξ : ℝ, 0 ≤ weilAtomSymbol (selbergWeightedVonMangoldt w) N ξ) →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| →
        10 ^ 5 * A₀ * Real.log (|ρ.im| + 306) * Real.log a ^ 2 ≤ a →
        |ρ.re - 1 / 2| < 1 / a := by
  obtain ⟨A₀, hA₀, H⟩ := zeta_selbergSymbol_forces_critical_strip
  exact ⟨A₀, hA₀, fun a w N ha6 hw hN hσ =>
    H a w N ha6 hw hN (selbergSymbolPositiveAtLevel_of_symbol_nonneg hσ)⟩


/-- **Height form.**  If the Selberg symbol form is nonnegative at a level `a ≥ e⁶` with
`10⁵ A₀ log(T + 306) log² a ≤ a`, then every zero of `ζ` with `2 ≤ |γ| ≤ T` lies in the strip
`|β - ½| < 1/a`. -/
theorem zeta_selbergSymbol_forces_strip_up_to_height :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (T a : ℝ) (w : ℕ → ℝ) (N : ℕ), Real.exp 6 ≤ a →
      10 ^ 5 * A₀ * Real.log (T + 306) * Real.log a ^ 2 ≤ a →
      (∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) → ⌊Real.exp (2 * a)⌋₊ ≤ N →
      SelbergSymbolPositiveAtLevel a w N →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ T → |ρ.re - 1 / 2| < 1 / a := by
  obtain ⟨A₀, hA₀, H⟩ := zeta_selbergSymbol_forces_critical_strip
  refine ⟨A₀, hA₀, fun T a w N ha6 hT hw hN hsel ρ hρ hγ hγT => H a w N ha6 hw hN hsel ρ hρ hγ ?_⟩
  refine le_trans ?_ hT
  have hlog : Real.log (|ρ.im| + 306) ≤ Real.log (T + 306) :=
    Real.log_le_log (by positivity) (by linarith)
  have : 0 ≤ 10 ^ 5 * A₀ := by positivity
  have := sq_nonneg (Real.log a)
  gcongr

/-- **All large levels.**  For every height `T` there is `a₀` such that nonnegativity of any
admissible Selberg symbol form at any level `a ≥ a₀` puts every zero with `2 ≤ |γ| ≤ T` in the strip
`|β - ½| < 1/a`. -/
theorem zeta_selbergSymbol_strip_eventually :
    ∀ T : ℝ, ∃ a₀ : ℝ, ∀ (a : ℝ) (w : ℕ → ℝ) (N : ℕ), a₀ ≤ a →
      (∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) → ⌊Real.exp (2 * a)⌋₊ ≤ N →
      SelbergSymbolPositiveAtLevel a w N →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ T → |ρ.re - 1 / 2| < 1 / a := by
  intro T
  obtain ⟨A₀, hA₀, H⟩ := zeta_selbergSymbol_forces_strip_up_to_height
  set C := 10 ^ 5 * A₀ * Real.log (|T| + 306) with hC
  have hC0 : 0 < C := by
    have : 1 ≤ Real.log (|T| + 306) := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos 1)
      have := Real.exp_one_lt_d9
      linarith [abs_nonneg T]
    positivity
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < 1 / C by positivity)
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp hlo
  refine ⟨max (max a₁ (Real.exp 6)) 1, fun a w N ha hw hN hsel ρ hρ hγ hγT => ?_⟩
  have ha6 : Real.exp 6 ≤ a := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ha)
  have ha1 : a₁ ≤ a := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ha)
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 6) ha6
  have hb := ha₁ a ha1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id,
    abs_of_pos ha0] at hb
  have hsize : 10 ^ 5 * A₀ * Real.log (|T| + 306) * Real.log a ^ 2 ≤ a := by
    rw [← hC]
    calc C * Real.log a ^ 2 ≤ C * (1 / C * a) := mul_le_mul_of_nonneg_left hb hC0.le
      _ = a := by field_simp
  exact H |T| a w N ha6 hsize hw hN hsel ρ hρ hγ (hγT.trans (le_abs_self T))

/-- **Selberg positivity at all large levels gives the Riemann hypothesis above ordinate `2`**,
and conversely the Riemann hypothesis gives Selberg positivity at every level. -/
theorem zeta_re_eq_half_of_selbergSymbol_eventually {a₀ : ℝ}
    (hsel : ∀ a : ℝ, a₀ ≤ a → ∀ (w : ℕ → ℝ) (N : ℕ),
      (∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) → ⌊Real.exp (2 * a)⌋₊ ≤ N →
      SelbergSymbolPositiveAtLevel a w N)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hγ : 2 ≤ |ρ.im|) : ρ.re = 1 / 2 := by
  by_contra hne
  have hδ : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨a₁, ha₁⟩ := zeta_selbergSymbol_strip_eventually |ρ.im|
  set a := max (max a₀ a₁) (2 / |ρ.re - 1 / 2|) with ha
  have ha0 : a₀ ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have ha1 : a₁ ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
  have ha2 : 2 / |ρ.re - 1 / 2| ≤ a := le_max_right _ _
  have hw : ∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → (fun _ : ℕ => (1 : ℝ)) d = 1 :=
    fun _ _ _ => rfl
  have hstrip := ha₁ a (fun _ => 1) ⌊Real.exp (2 * a)⌋₊ ha1 hw le_rfl
    (hsel a ha0 _ _ hw le_rfl) ρ hρ hγ le_rfl
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha2
  rw [div_le_iff₀ hδ] at ha2
  rw [lt_div_iff₀ hapos] at hstrip
  linarith

theorem selbergSymbolPositiveAtLevel_of_forall_re_eq_half
    (hRH : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) {a : ℝ} (ha : 0 ≤ a) {w : ℕ → ℝ}
    (hw : ∀ d, 1 ≤ d → d ≤ ⌊Real.exp (2 * a)⌋₊ → w d = 1) {N : ℕ}
    (hN : ⌊Real.exp (2 * a)⌋₊ ≤ N) : SelbergSymbolPositiveAtLevel a w N :=
  (hodgeIndexAtLevel_iff_selbergSymbolPositive ha hw hN).mp
    (hodgeIndexAtLevel_of_forall_re_eq_half hRH a)

end RHTower
