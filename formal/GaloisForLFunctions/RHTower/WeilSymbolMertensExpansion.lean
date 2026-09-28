import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion

/-!
# The Mertens expansion of a perturbed Weil symbol energy

Replace the von Mangoldt weights `Λ(n)` in the finite-atom Weil symbol of `ζ` by arbitrary real
weights `lam(n)`.  For a polar-constrained `C²` test `f` supported in `[-a, a]`, with
`k = f ⋆ f̃` and `φ(u) = Re(k(u) + k(-u))`, the symbol energy changes by the cosine moments of the
weight difference (`integral_weilAtomSymbol_eq_sub`):
`∫ |h_f|² S_lam = 2π Re W(f) - 2π ∑_{2 ≤ n ≤ e^{2a}} (lam(n) - Λ(n)) n^{-1/2} φ(log n)`,
where `W(f)` is the zero side of the explicit formula for `ζ`.

Abel summation against the summatory function `C(t) = ∑_{2 ≤ n ≤ t} (lam(n) - Λ(n)) n^{-1/2}`
gives, for every pair of real numbers `A, B`, the exact identity
(`integral_weilAtomSymbol_eq_mertens`)

`∫ |h_f|² S_lam = 2π Re W(f) - 2π (A |h_f(0)|² + 2B ‖f‖₂²)`
`                 + 2π ∫₁^{e^{2a+1}} (φ ∘ log)'(t) (C(t) - A log t - B) dt`.

The linear part `A log t + B` integrates exactly: its slope pairs with `∫₀^∞ φ = |h_f(0)|²` and its
constant with `φ(0) = 2‖f‖₂²`.  When `C(t) = A log t + B + o(1)`, the last integral is controlled by
the remainder (`abs_integral_deriv_comp_log_mul_le`), so the constant `B` of the weight difference
enters the symbol energy with the weight `-4π ‖f‖₂²`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23

/-! ### Cosine moments of `|h_f|²` -/

/-- `∫ |h_f(τ)|² cos(τy) dτ = π Re(k(y) + k(-y))` with `k = f ⋆ f̃`. -/
theorem integral_normSq_paperFT_mul_cos_eq {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (y : ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * y) =
      π * (EF.weilTest f f y + EF.weilTest f f (-y)).re := by
  obtain ⟨hfc, hkd, -, hki, hFk⟩ := weilTest_self_data hf hfs
  have hinv := EF.k_add_k_neg hkd.continuous hki hFk y
  have hreal : (fun τ : ℝ => paperFT (EF.weilTest f f) τ * (Real.cos (τ * y) : ℂ)) =
      fun τ : ℝ => ((‖paperFT f τ‖ ^ 2 * Real.cos (τ * y) : ℝ) : ℂ) := by
    ext τ; rw [paperFT_weilTest_self_ofReal hf.continuous hfc]; push_cast; ring
  rw [hreal, integral_complex_ofReal] at hinv
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h1 : (1 / π : ℂ) * ((∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * y) : ℝ) : ℂ) =
      (((1 / π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * y) : ℝ) : ℂ) := by push_cast; ring
  rw [hinv, h1, Complex.ofReal_re, ← mul_assoc, mul_one_div_cancel hπ, one_mul]

/-! ### The symbol of a perturbed weight -/

/-- Changing the prime weights from `Λ` to `lam` changes the symbol energy of a level-`a` test by
the cosine moments of the weight difference. -/
theorem integral_weilAtomSymbol_eq_sub {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (lam : ℕ → ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) -
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (lam n - Λ n) / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  have harg : ∀ (τ : ℝ) (n : ℕ), 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n :=
    fun τ n => by field_simp
  have hpt : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * π)) =
      ‖paperFT f τ‖ ^ 2 * weilAtomSymbol (fun n => (Λ n : ℝ)) N (τ / (2 * π)) -
        ∑ n ∈ Finset.Icc 2 N, (2 * ((lam n - Λ n) / Real.sqrt n)) *
          (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) := by
    intro τ
    unfold weilAtomSymbol
    simp only [harg]
    have hs : ∑ n ∈ Finset.Icc 2 N, (2 * ((lam n - Λ n) / Real.sqrt n)) *
          (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) =
        ‖paperFT f τ‖ ^ 2 * (∑ n ∈ Finset.Icc 2 N,
          lam n * (1 / Real.sqrt n) * (2 * Real.cos (τ * Real.log n)) -
          ∑ n ∈ Finset.Icc 2 N,
          (Λ n : ℝ) * (1 / Real.sqrt n) * (2 * Real.cos (τ * Real.log n))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hs]; ring
  have hint := integrable_normSq_paperFT_mul_weilAtomSymbol hf hfs
  have hcos := integrable_normSq_paperFT_mul_cos hf hfs
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub hint
    (integrable_finsetSum _ fun n _ => (hcos _).const_mul _),
    integral_finsetSum _ fun n _ => (hcos _).const_mul _]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_normSq_paperFT_mul_cos_eq hf hfs]
  ring

/-! ### Abel summation against a Mertens expansion -/

/-- **Exact Mertens expansion of a logarithmic sum.**  Let `φ` be `C¹` and vanish on `[L, ∞)`,
and let `c 0 = c 1 = 0` with summatory function `C(t) = ∑_{n ≤ t} c n`.  For any `A, B`,
`∑_{2 ≤ n ≤ e^L} c n φ(log n) = A ∫₀^L φ + B φ(0) - ∫₁^{e^L} (φ ∘ log)'(t) (C(t) - A log t - B) dt`.
Abel summation turns the sum into `-∫ (φ ∘ log)' C`; the linear part `A log t + B` integrates
exactly. -/
theorem sum_mul_log_eq_mertens {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {L : ℝ} (hL : 0 ≤ L)
    (hφL : ∀ u, L ≤ u → φ u = 0) (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc1 : c 1 = 0) (A B : ℝ) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, c n * φ (Real.log n) =
      A * (∫ u in (0 : ℝ)..L, φ u) + B * φ 0 -
        ∫ t in Ioc 1 (Real.exp L), deriv (fun t => φ (Real.log t)) t *
          ((∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t - B) := by
  set b := Real.exp L with hb
  set F : ℝ → ℝ := fun t => φ (Real.log t) with hF
  have hb1 : 1 ≤ b := Real.one_le_exp hL
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hFd : ∀ t : ℝ, 0 < t → HasDerivAt F (deriv φ (Real.log t) * t⁻¹) t := by
    intro t ht
    exact (hφd (Real.log t)).hasDerivAt.comp t (Real.hasDerivAt_log ht.ne')
  have hFd' : ∀ t : ℝ, 0 < t → deriv F t = deriv φ (Real.log t) * t⁻¹ :=
    fun t ht => (hFd t ht).deriv
  have hF'cont : ContinuousOn (fun t : ℝ => deriv φ (Real.log t) * t⁻¹) (Icc 1 b) := by
    refine (hφc.comp_continuousOn (Real.continuousOn_log.mono ?_)).mul
      (continuousOn_inv₀.mono ?_)
    · intro t ht; exact ne_of_gt (lt_of_lt_of_le one_pos ht.1)
    · intro t ht; exact ne_of_gt (lt_of_lt_of_le one_pos ht.1)
  have hderivEq : EqOn (deriv F) (fun t : ℝ => deriv φ (Real.log t) * t⁻¹) (Icc 1 b) :=
    fun t ht => hFd' t (lt_of_lt_of_le one_pos ht.1)
  have hF'int : IntegrableOn (deriv F) (Icc 1 b) :=
    (hF'cont.integrableOn_compact isCompact_Icc).congr_fun hderivEq.symm measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c (f := F) zero_le_one hb1
    (fun t ht => (hFd t (lt_of_lt_of_le one_pos ht.1)).differentiableAt) hF'int
  have hFb : F b = 0 := by simp only [hF, hb, Real.log_exp]; exact hφL L le_rfl
  have hC1 : ∑ k ∈ Finset.Icc 0 ⌊(1 : ℝ)⌋₊, c k = 0 := by
    rw [Nat.floor_one]
    rw [show Finset.Icc 0 1 = {0, 1} by decide, Finset.sum_pair (by norm_num), hc0, hc1,
      add_zero]
  rw [hFb, hC1, zero_mul, mul_zero, sub_zero, zero_sub, Nat.floor_one] at habel
  have hset : Finset.Ioc 1 ⌊b⌋₊ = Finset.Icc 2 ⌊b⌋₊ := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hset] at habel
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊b⌋₊, c n * φ (Real.log n) =
      ∑ k ∈ Finset.Icc 2 ⌊b⌋₊, F k * c k :=
    Finset.sum_congr rfl fun n _ => by simp only [hF]; ring
  rw [hsum, habel]
  -- integrability of the three pieces on `Ioc 1 b`
  have hIoc : Ioc 1 b ⊆ Icc 1 b := Ioc_subset_Icc_self
  have hint_C : IntegrableOn (fun t => deriv F t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) (Ioc 1 b) :=
    (integrableOn_mul_sum_Icc c zero_le_one hF'int).mono_set hIoc
  have hint_log : IntegrableOn (fun t => deriv F t * (A * Real.log t + B)) (Ioc 1 b) := by
    refine (IntegrableOn.congr_fun ?_ (fun t ht => by rw [hderivEq ht]) measurableSet_Icc).mono_set
      hIoc
    refine ContinuousOn.integrableOn_compact isCompact_Icc (hF'cont.mul ?_)
    exact (continuousOn_const.mul (Real.continuousOn_log.mono fun t ht =>
      ne_of_gt (lt_of_lt_of_le one_pos ht.1))).add continuousOn_const
  have hsplit : ∫ t in Ioc 1 b, deriv F t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
      (∫ t in Ioc 1 b, deriv F t * (A * Real.log t + B)) +
        ∫ t in Ioc 1 b, deriv F t * ((∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t - B) := by
    rw [← integral_add hint_log (by
      refine (hint_C.sub hint_log).congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp only [Pi.sub_apply]; ring)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    ring
  -- the linear part integrates exactly
  have hlin : ∫ t in Ioc 1 b, deriv F t * (A * Real.log t + B) =
      -(A * (∫ u in (0 : ℝ)..L, φ u)) - B * φ 0 := by
    set Φ₀ : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..v, φ u with hΦ₀
    have hΦ₀d : ∀ v : ℝ, HasDerivAt Φ₀ (φ v) v := fun v =>
      intervalIntegral.integral_hasDerivAt_right (hφ.continuous.intervalIntegrable _ _)
        hφ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hφ.continuous.continuousAt
    set Ψ : ℝ → ℝ := fun t => A * (F t * Real.log t - Φ₀ (Real.log t)) + B * F t with hΨ
    have hΨd : ∀ t ∈ uIcc 1 b, HasDerivAt Ψ
        (deriv φ (Real.log t) * t⁻¹ * (A * Real.log t + B)) t := by
      intro t ht
      rw [uIcc_of_le hb1] at ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
      have hlog := Real.hasDerivAt_log ht0.ne'
      have h1 := ((hFd t ht0).mul hlog).sub ((hΦ₀d (Real.log t)).comp t hlog)
      have h2 := (h1.const_mul A).add ((hFd t ht0).const_mul B)
      have hfun : Ψ = (fun y => A * (F * Real.log - Φ₀ ∘ Real.log) y) + fun y => B * F y := by
        funext y; simp only [hΨ, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
      rw [hfun]
      refine h2.congr_deriv ?_
      rw [show F t = φ (Real.log t) from rfl]
      ring
    have hcont : IntervalIntegrable (fun t => deriv φ (Real.log t) * t⁻¹ * (A * Real.log t + B))
        volume 1 b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hb1]
      exact hF'cont.mul ((continuousOn_const.mul (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (lt_of_lt_of_le one_pos ht.1))).add continuousOn_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΨd hcont
    rw [intervalIntegral.integral_of_le hb1] at hftc
    have hcongr : ∫ t in Ioc 1 b, deriv F t * (A * Real.log t + B) =
        ∫ t in Ioc 1 b, deriv φ (Real.log t) * t⁻¹ * (A * Real.log t + B) :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        rw [hFd' t (lt_trans one_pos ht.1)]
    rw [hcongr, hftc]
    simp only [hΨ, hF, hb, Real.log_exp, Real.log_one, hφL L le_rfl, hΦ₀,
      intervalIntegral.integral_same]
    ring
  rw [hsplit, hlin]
  ring

/-! ### The Mertens expansion of a perturbed symbol energy -/

/-- The even real part `φ(u) = Re(k(u) + k(-u))` of the Weil test `k = f ⋆ f̃`. -/
def weilTestEvenPart (f : ℝ → ℂ) (u : ℝ) : ℝ :=
  (EF.weilTest f f u + EF.weilTest f f (-u)).re

/-- The normalized weight difference `(lam(n) - Λ(n))/√n` for `n ≥ 2`, and `0` for `n ≤ 1`. -/
def weilPerturbationWeight (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then (lam n - Λ n) / Real.sqrt n else 0

theorem weilTest_self_zero {f : ℝ → ℂ} :
    EF.weilTest f f 0 = ((∫ x : ℝ, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  unfold EF.weilTest
  rw [convolution_def, ← integral_complex_ofReal]
  congr 1; funext t
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, zero_sub, neg_neg]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem contDiff_weilTestEvenPart {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) : ContDiff ℝ 2 (weilTestEvenPart f) := by
  obtain ⟨-, hkd, -, -, -⟩ := weilTest_self_data hf hfs
  exact Complex.reCLM.contDiff.comp (hkd.add (hkd.comp contDiff_neg))

theorem weilTestEvenPart_eq_zero {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {u : ℝ} (hu : 2 * a < |u|) : weilTestEvenPart f u = 0 := by
  obtain ⟨-, -, hks, -, -⟩ := weilTest_self_data hf hfs
  have hz : ∀ y : ℝ, 2 * a < |y| → EF.weilTest f f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hks hmem
      have : |y| ≤ 2 * a := abs_le.mpr ⟨this.1, this.2⟩
      linarith
  unfold weilTestEvenPart
  rw [hz u hu, hz (-u) (by rwa [abs_neg]), add_zero, Complex.zero_re]

theorem weilTestEvenPart_zero (f : ℝ → ℂ) :
    weilTestEvenPart f 0 = 2 * ∫ x : ℝ, ‖f x‖ ^ 2 := by
  unfold weilTestEvenPart
  rw [neg_zero, weilTest_self_zero, ← Complex.ofReal_add, Complex.ofReal_re]; ring

/-- `∫₀^L φ = |h_f(0)|²` once `L ≥ 2a`. -/
theorem integral_weilTestEvenPart {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {L : ℝ} (hL : 2 * a < L) :
    ∫ u in (0 : ℝ)..L, weilTestEvenPart f u = ‖paperFT f 0‖ ^ 2 := by
  obtain ⟨hfc, hkd, hks, hki, -⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f with hk
  have hkc : Continuous k := hkd.continuous
  have hL0 : 0 ≤ L := by linarith
  have hneg : IntervalIntegrable (fun u => k (-u)) volume 0 L :=
    (hkc.comp continuous_neg).intervalIntegrable _ _
  have hii : IntervalIntegrable (fun u => k u + k (-u)) volume 0 L :=
    (hkc.intervalIntegrable _ _).add hneg
  have hsum : ∫ u in (0 : ℝ)..L, (k u + k (-u)) = ∫ u in (-L)..L, k u := by
    rw [intervalIntegral.integral_add (hkc.intervalIntegrable _ _) hneg,
      intervalIntegral.integral_comp_neg (fun u => k u),
      neg_zero, add_comm, intervalIntegral.integral_add_adjacent_intervals
        (hkc.intervalIntegrable _ _) (hkc.intervalIntegrable _ _)]
  have hfull : ∫ u in (-L)..L, k u = ∫ u, k u := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_)
    refine image_eq_zero_of_notMem_tsupport fun hmem => hu ?_
    have := hks hmem
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hzero : paperFT k (0 : ℝ) = ∫ u, k u := by
    unfold paperFT; congr 1; funext u; simp
  have hre : ∫ u in (0 : ℝ)..L, weilTestEvenPart f u =
      Complex.reCLM (∫ u in (0 : ℝ)..L, (k u + k (-u))) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hii]
    rfl
  rw [hre, hsum, hfull, ← hzero, paperFT_weilTest_self_ofReal hf.continuous hfc,
    Complex.ofReal_zero]
  exact Complex.ofReal_re _

/-- **Exact Mertens expansion of the perturbed symbol energy.**  For a polar-constrained `C²`
test `f` supported in `[-a, a]`, any weights `lam` and any real `A, B`,
`∫ |h_f|² S_lam = 2π Re W(f) - 2π (A |h_f(0)|² + 2B ‖f‖₂²) + 2π ∫₁^{e^{2a+1}} (φ ∘ log)' ε`,
where `W(f)` is the zero side of `ζ`, `φ = Re(k + k(-·))`, and
`ε(t) = ∑_{2 ≤ n ≤ t} (lam(n) - Λ(n))/√n - A log t - B`. -/
theorem integral_weilAtomSymbol_eq_mertens {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) (lam : ℕ → ℝ) (A B : ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (zetaZeroConfig.W f f).re -
        2 * π * (A * ‖paperFT f 0‖ ^ 2 + 2 * B * ∫ x : ℝ, ‖f x‖ ^ 2) +
        2 * π * ∫ t in Ioc 1 (Real.exp (2 * a + 1)),
          deriv (fun t => weilTestEvenPart f (Real.log t)) t *
            ((∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) - A * Real.log t - B) := by
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  have hWre : (zetaZeroConfig.W f f).re = 1 / (2 * π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
    rw [hW, Complex.ofReal_re]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hΛ : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hWre]; field_simp
  rw [integral_weilAtomSymbol_eq_sub hf hfs lam, hΛ]
  -- the prime sum as an Abel sum up to `e^{2a+1}`
  have hφ := contDiff_weilTestEvenPart hf hfs
  have hL : (0 : ℝ) ≤ 2 * a + 1 := by linarith
  have hφL : ∀ u, 2 * a + 1 ≤ u → weilTestEvenPart f u = 0 := fun u hu =>
    weilTestEvenPart_eq_zero hf hfs (by rw [abs_of_nonneg (by linarith)]; linarith)
  have habel := sum_mul_log_eq_mertens (hφ.of_le (by norm_num)) hL hφL
    (weilPerturbationWeight lam) (by simp [weilPerturbationWeight])
    (by simp [weilPerturbationWeight]) A B
  rw [integral_weilTestEvenPart ha hf hfs (by linarith), weilTestEvenPart_zero] at habel
  have hN : ⌊Real.exp (2 * a)⌋₊ ≤ ⌊Real.exp (2 * a + 1)⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (lam n - Λ n) / Real.sqrt n *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a + 1)⌋₊,
        weilPerturbationWeight lam n * weilTestEvenPart f (Real.log n) := by
    apply Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc le_rfl hN)
    · intro n hn
      rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hn
      have hn2 : ⌊Real.exp (2 * a)⌋₊ < n := by omega
      have hexp : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn2
      have hlog : 2 * a < Real.log n := by
        rw [← Real.log_exp (2 * a)]; exact Real.log_lt_log (Real.exp_pos _) hexp
      rw [weilTestEvenPart_eq_zero hf hfs (lt_of_lt_of_le hlog (le_abs_self _)), mul_zero]
    · intro n hn
      rw [Finset.mem_Icc] at hn
      simp only [weilPerturbationWeight, if_pos hn.1, weilTestEvenPart]
  rw [hsum, habel]
  ring

/-- The remainder integral of the Mertens expansion is bounded by the size of the remainder on an
initial range `[1, T]` and beyond it, against `|(φ ∘ log)'(t)| ≤ M/t`. -/
theorem abs_integral_deriv_comp_log_mul_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {M : ℝ}
    (hM : ∀ u, |deriv φ u| ≤ M) {ε : ℝ → ℝ} {T b E η : ℝ} (hT : 1 ≤ T) (hTb : T ≤ b)
    (hE : ∀ t ∈ Icc 1 T, |ε t| ≤ E) (hη : ∀ t, T ≤ t → |ε t| ≤ η)
    (hi : IntegrableOn (fun t => deriv (fun t => φ (Real.log t)) t * ε t) (Ioc 1 b)) :
    |∫ t in Ioc 1 b, deriv (fun t => φ (Real.log t)) t * ε t| ≤
      M * E * Real.log T + M * η * Real.log b := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 1 ⟨le_rfl, hT⟩)
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη T le_rfl)
  have hb1 : 1 ≤ b := hT.trans hTb
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hderiv : ∀ t : ℝ, 0 < t →
      deriv (fun t => φ (Real.log t)) t = deriv φ (Real.log t) * t⁻¹ := fun t ht =>
    ((hφd (Real.log t)).hasDerivAt.comp t (Real.hasDerivAt_log ht.ne')).deriv
  set G : ℝ → ℝ := fun t => deriv (fun t => φ (Real.log t)) t * ε t with hG
  have hpt : ∀ t : ℝ, 0 < t → ∀ K : ℝ, |ε t| ≤ K → ‖G t‖ ≤ M * K * t⁻¹ := by
    intro t ht K hK
    rw [Real.norm_eq_abs, hG]
    simp only
    rw [hderiv t ht, abs_mul, abs_mul, abs_inv, abs_of_pos ht]
    have h1 := hM (Real.log t)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans hK
    have ht' : 0 < t⁻¹ := inv_pos.mpr ht
    calc |deriv φ (Real.log t)| * t⁻¹ * |ε t| ≤ M * t⁻¹ * K := by gcongr
      _ = M * K * t⁻¹ := by ring
  have hi1 : IntervalIntegrable G volume 1 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (hi.mono_set (Ioc_subset_Ioc le_rfl hTb))
  have hi2 : IntervalIntegrable G volume T b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hTb).mpr
      (hi.mono_set (Ioc_subset_Ioc hT le_rfl))
  have hinv : ∀ {x y : ℝ}, 1 ≤ x → x ≤ y → ∀ K : ℝ,
      IntervalIntegrable (fun t : ℝ => M * K * t⁻¹) volume x y := by
    intro x y hx hxy K
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => ?_)
    rw [uIcc_of_le hxy] at ht
    exact ne_of_gt (lt_of_lt_of_le one_pos (hx.trans ht.1))
  have hint : ∀ {x y : ℝ}, 1 ≤ x → x ≤ y → ∀ K : ℝ,
      ∫ t in x..y, M * K * t⁻¹ = M * K * Real.log (y / x) := by
    intro x y hx hxy K
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by linarith) (by linarith)]
  have hb1' : ‖∫ t in (1 : ℝ)..T, G t‖ ≤ M * E * Real.log T := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hT
      (Eventually.of_forall fun t ht => hpt t (lt_trans one_pos ht.1) E
        (hE t ⟨ht.1.le, ht.2⟩)) (hinv le_rfl hT E)
    rwa [hint le_rfl hT, div_one] at h
  have hb2 : ‖∫ t in T..b, G t‖ ≤ M * η * Real.log b := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hTb
      (Eventually.of_forall fun t ht => hpt t (lt_of_lt_of_le one_pos (hT.trans ht.1.le)) η
        (hη t ht.1.le)) (hinv hT hTb η)
    rw [hint hT hTb] at h
    refine h.trans ?_
    have hlog : Real.log (b / T) ≤ Real.log b := by
      rw [Real.log_div (by linarith) (by linarith)]
      linarith [Real.log_nonneg hT]
    exact mul_le_mul_of_nonneg_left hlog (mul_nonneg hM0 hη0)
  rw [← intervalIntegral.integral_of_le hb1,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  refine (abs_add_le _ _).trans ?_
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact add_le_add hb1' hb2

end RHTower
