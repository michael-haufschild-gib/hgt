import GaloisForLFunctions.RHTower.WeilOddConeMinorantRigidity
import GaloisForLFunctions.RHTower.WeilPositivityHalfPoleRigidity
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowConditioning

/-!
# Odd Weil positivity across the `√n` barrier

Fix the archimedean term and the pole of `ζ` and perturb the von Mangoldt weights to `Λ + w`.
Odd tests have `f̂(0) = 0`, so the odd Weil functional does not see an atom of the perturbation
symbol at the origin; the squares `w = c·1_{n = m²}` produce exactly such an atom.

**Theorem** (`vonMangoldt_add_eq_zero_of_symbol_atom_odd`).  Suppose the atoms of `w` pair with the
tests through a continuous symbol `P` of linear growth plus an atom `m |f̂(0)|²` at the origin.  If
`Λ + w` is Weil-positive on the pole-free ODD tests (`WeilPositiveOddPolar`), then `w = 0`.

**Corollaries.**
* `vonMangoldt_add_halfPole_eq_zero_odd`: the same in the half-pole class (partial sums of
  `w − κ(√n − √(n−1))` weighted by `1/(n√n)` summable).
* `vonMangoldt_add_squares_odd_eq_zero`: `Λ + c·1_{n = m²}` is odd Weil-positive only for `c = 0`.
* `weilPositiveOddPolar_of_weilPositiveOdd`: odd Weil positivity with the pole term implies the
  polar symbol form.

Proof.
* The symbol may be replaced by its even part (`hpair` is invariant under `f ↦ f(−·)`).
* Concentrated odd radical tests force `P ≤ 0`.  The test is the odd part of the twisted radical
  test `T_R ⋆ (q(x/S)e^{−iτ₀x})` (`oddTwistTest`).  Its transform keeps the radical factor, because
  the radical test is even, so its zero side is still `O(S¹⁰e^{−S})`.  Its energy against `P` is
  half that of the twisted test up to the cross term between `±τ₀`, which is `O(1/|τ₀|)`, while the
  main term grows like `S` (`integral_cross_le`).
* Probes supported in `[−log 2/4, log 2/4]` see no atoms: zero-mean probes give `P ≡ 0`, and then
  a probe with `f̂(0) ≠ 0` gives `m = 0`.  No positivity is needed for these steps.
* Two-point resonators read off each `w(n)`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

local notation "Φ" => riemannPhiKernel

/-! ### Polar odd positivity -/

/-- Odd Weil positivity in symbol form at every level, on pole-free odd tests. -/
def WeilPositiveOddPolar (lam : ℕ → ℝ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    (∀ x, f (-x) = -f x) → paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
    0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))

/-- For a pole-free test supported in `[−a, a]`, nonnegativity of the full functional gives
nonnegativity of the symbol energy at level `a`. -/
theorem integral_weilAtomSymbol_nonneg_of_re_weilFullFunctional_nonneg {lam : ℕ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0)
    (hfull : 0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re) :
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

/-- Odd Weil positivity with the pole term implies the polar symbol form. -/
theorem weilPositiveOddPolar_of_weilPositiveOdd {lam : ℕ → ℝ} (hW : WeilPositiveOdd lam) :
    WeilPositiveOddPolar lam := by
  intro a ha f hf hfs hodd hp hm
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  exact integral_weilAtomSymbol_nonneg_of_re_weilFullFunctional_nonneg ha hf hfs hp hm
    (hW f hf hfc hodd)

/-! ### The odd part of a test -/

/-- The transform of the odd part `(g − g(−·))/2`. -/
theorem paperFT_oddPart {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (fun x => (g x - g (-x)) / 2) z = (paperFT g z - paperFT g (-z)) / 2 := by
  have h1 : Integrable fun u : ℝ => g u * Complex.exp (I * z * (u : ℂ)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hgc.mul_right)
  have hgc' : HasCompactSupport fun u : ℝ => g (-u) := hgc.comp_homeomorph (Homeomorph.neg ℝ)
  have h2 : Integrable fun u : ℝ => g (-u) * Complex.exp (I * z * (u : ℂ)) :=
    ((hg.comp continuous_neg).mul (by fun_prop)).integrable_of_hasCompactSupport (hgc'.mul_right)
  have e : paperFT g (-z) = ∫ u : ℝ, g (-u) * Complex.exp (I * z * (u : ℂ)) := by
    unfold paperFT
    rw [← integral_neg_eq_self]
    congr 1; funext u
    push_cast; ring_nf
  calc paperFT (fun x => (g x - g (-x)) / 2) z
      = ∫ u : ℝ, (g u * Complex.exp (I * z * (u : ℂ)) -
          g (-u) * Complex.exp (I * z * (u : ℂ))) / 2 := by
        unfold paperFT; congr 1; funext u; ring
    _ = ((∫ u : ℝ, g u * Complex.exp (I * z * (u : ℂ))) -
          ∫ u : ℝ, g (-u) * Complex.exp (I * z * (u : ℂ))) / 2 := by
        rw [integral_div, integral_sub h1 h2]
    _ = (paperFT g z - paperFT g (-z)) / 2 := by rw [e]; rfl

/-- The radical test has an even transform. -/
theorem paperFT_weilRadicalTest_neg (R : ℝ) (z : ℂ) :
    paperFT (weilRadicalTest R) (-z) = paperFT (weilRadicalTest R) z := by
  rw [← paperFT_comp_neg]
  congr 1
  funext u
  exact weilRadicalTest_neg R u

/-! ### The odd twisted radical test -/

/-- The odd part of the twisted radical test `twistTest 0 τ₀ R S`. -/
def oddTwistTest (τ₀ R S : ℝ) (x : ℝ) : ℂ :=
  (twistTest 0 τ₀ R S x - twistTest 0 τ₀ R S (-x)) / 2

theorem oddTwistTest_neg (τ₀ R S x : ℝ) :
    oddTwistTest τ₀ R S (-x) = -oddTwistTest τ₀ R S x := by
  unfold oddTwistTest; rw [neg_neg]; ring

theorem contDiff_oddTwistTest (τ₀ R S : ℝ) : ContDiff ℝ 2 (oddTwistTest τ₀ R S) := by
  unfold oddTwistTest
  exact ((contDiff_twistTest 0 τ₀ R S).sub
    ((contDiff_twistTest 0 τ₀ R S).comp contDiff_neg)).div_const 2

theorem tsupport_oddTwistTest {τ₀ R S : ℝ} (hS : 0 < S) :
    tsupport (oddTwistTest τ₀ R S) ⊆ Icc (-(3 * R + S)) (3 * R + S) := by
  refine tsupport_subset_of_vanish fun u hu => ?_
  unfold oddTwistTest
  rw [twistTest_eq_zero hS hu, twistTest_eq_zero hS (by rwa [abs_neg]), sub_zero, zero_div]

theorem paperFT_oddTwistTest {τ₀ R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (oddTwistTest τ₀ R S) z =
      (paperFT (twistTest 0 τ₀ R S) z - paperFT (twistTest 0 τ₀ R S) (-z)) / 2 := by
  have hc : HasCompactSupport (twistTest 0 τ₀ R S) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (tsupport_twistTest hS)
  exact paperFT_oddPart (contDiff_twistTest 0 τ₀ R S).continuous hc z

/-- The companion of the twisted test at `α = 0`. -/
def twistCompanion (τ₀ R S : ℝ) (z : ℂ) : ℂ :=
  paperFT (weilRadicalTest R) z * paperFT (weilRadicalTest R) z * paperFT (twistProbe τ₀ S) z

theorem paperFT_twistTest_zero_factor {τ₀ R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (twistTest 0 τ₀ R S) z = paperFT (weilRadicalTest R) z * twistCompanion τ₀ R S z := by
  rw [paperFT_twistTest_factor hS]
  simp [twistCompanion]

/-- The odd twisted test keeps the radical factor. -/
theorem paperFT_oddTwistTest_factor {τ₀ R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (oddTwistTest τ₀ R S) z = paperFT (weilRadicalTest R) z *
      ((twistCompanion τ₀ R S z - twistCompanion τ₀ R S (-z)) / 2) := by
  rw [paperFT_oddTwistTest hS, paperFT_twistTest_zero_factor hS, paperFT_twistTest_zero_factor hS,
    paperFT_weilRadicalTest_neg]
  ring

theorem paperFT_oddTwistTest_half_I {τ₀ R S : ℝ} (hS : 0 < S) :
    paperFT (oddTwistTest τ₀ R S) (I / 2) = 0 := by
  rw [paperFT_oddTwistTest_factor hS, paperFT_weilRadicalTest_half_I, zero_mul]

theorem paperFT_oddTwistTest_neg_half_I {τ₀ R S : ℝ} (hS : 0 < S) :
    paperFT (oddTwistTest τ₀ R S) (-(I / 2)) = 0 := by
  rw [paperFT_oddTwistTest_factor hS, paperFT_weilRadicalTest_neg_half_I, zero_mul]

/-- **The zero side of the odd twisted test at `R = log S`.** -/
theorem exists_norm_W_oddTwistTest_log_le (τ₀ : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ S : ℝ, Real.exp 1 ≤ S →
    ‖zetaZeroConfig.W (oddTwistTest τ₀ (Real.log S) S) (oddTwistTest τ₀ (Real.log S) S)‖ ≤
      K * S ^ 10 * Real.exp (-S) := by
  set C := ((∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
    (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖)) ^ 2 * ∫ x : ℝ, ‖twistBump x‖ with hC
  have hC0 : 0 ≤ C := mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨K, hK0, hK⟩ := exists_radical_factor_log_bound C hC0
  refine ⟨K, hK0, fun S hS => ?_⟩
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos 1) hS
  have hcomp : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖twistCompanion τ₀ (Real.log S) S z‖ ≤ C * (Real.exp (S / 2) * S) := by
    intro z hz
    have h := norm_twist_companion_le (R := Real.log S) (τ₀ := τ₀) hS0 (c₁ := 0) (c₂ := 0)
      (c₃ := 0) hz
    simp only [Complex.ofReal_zero, add_zero] at h
    refine h.trans (le_of_eq ?_)
    rw [hC]; ring
  refine hK S hS (fun z => paperFT_oddTwistTest_factor hS0 z) fun z hz => ?_
  have h1 := hcomp z hz
  have h2 := hcomp (-z) (by rw [Complex.neg_im, abs_neg]; exact hz)
  calc ‖(twistCompanion τ₀ (Real.log S) S z - twistCompanion τ₀ (Real.log S) S (-z)) / 2‖
      ≤ (‖twistCompanion τ₀ (Real.log S) S z‖ + ‖twistCompanion τ₀ (Real.log S) S (-z)‖) / 2 := by
        rw [norm_div, Complex.norm_two]
        gcongr
        exact norm_sub_le _ _
    _ ≤ C * (Real.exp (S / 2) * S) := by linarith

/-! ### The cross term between `τ₀` and `−τ₀` -/

theorem integrable_one_div_one_add_abs_sq : Integrable fun u : ℝ => 1 / (1 + |u|) ^ 2 := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), one_div]
  norm_cast

theorem integral_one_div_one_add_mul_abs_sub_sq {S : ℝ} (hS : 0 < S) (τ₀ : ℝ) :
    ∫ τ : ℝ, 1 / (1 + S * |τ - τ₀|) ^ 2 = (∫ u : ℝ, 1 / (1 + |u|) ^ 2) / S := by
  have e : (fun τ : ℝ => 1 / (1 + S * |τ - τ₀|) ^ 2) =
      fun τ => (fun x : ℝ => (fun u : ℝ => 1 / (1 + |u|) ^ 2) (S * x)) (τ - τ₀) := by
    funext τ
    show 1 / (1 + S * |τ - τ₀|) ^ 2 = 1 / (1 + |S * (τ - τ₀)|) ^ 2
    rw [abs_mul, abs_of_pos hS]
  rw [e, integral_sub_right_eq_self (fun x : ℝ => (fun u : ℝ => 1 / (1 + |u|) ^ 2) (S * x)) τ₀,
    Measure.integral_comp_mul_left (fun u : ℝ => 1 / (1 + |u|) ^ 2) S, smul_eq_mul,
    abs_of_pos (inv_pos.mpr hS)]
  field_simp

theorem integrable_one_div_one_add_mul_abs_sub_sq {S : ℝ} (hS : 0 < S) (τ₀ : ℝ) :
    Integrable fun τ : ℝ => 1 / (1 + S * |τ - τ₀|) ^ 2 := by
  have h := (integrable_one_div_one_add_abs_sq.comp_mul_left' hS.ne').comp_sub_right τ₀
  refine h.congr (Eventually.of_forall fun τ => ?_)
  show 1 / (1 + |S * (τ - τ₀)|) ^ 2 = 1 / (1 + S * |τ - τ₀|) ^ 2
  rw [abs_mul, abs_of_pos hS]

/-- The pointwise cross bound: `|H(τ)| |H(−τ)| |D(τ)| ≤ c/(1 + S|τ − τ₀|)²` with
`c = K₁²Cκ⁴C_D S/(2|τ₀|)`. -/
theorem cross_pointwise_le {H : ℝ → ℂ} {D : ℝ → ℝ} {K₁ S Cκ CD τ₀ : ℝ} (hS : 1 ≤ S)
    (hτ₀ : τ₀ ≠ 0) (hK₁ : 0 ≤ K₁) (hCD : 0 ≤ CD)
    (hup : ∀ τ, ‖H τ‖ ≤ K₁ * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2))
    (hD : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|)) (τ : ℝ) :
    ‖H τ‖ * ‖H (-τ)‖ * |D τ| ≤
      K₁ ^ 2 * Cκ ^ 4 * CD * S / (2 * |τ₀|) * (1 / (1 + S * |τ - τ₀|) ^ 2) := by
  have hS0 : 0 < S := by linarith
  have hτ : 0 < |τ₀| := abs_pos.mpr hτ₀
  set a := 1 + S * |τ - τ₀| with ha
  set b := 1 + S * |-τ - τ₀| with hb
  have hu := abs_nonneg (τ - τ₀)
  have hv := abs_nonneg (-τ - τ₀)
  have ha1 : 1 ≤ a := by nlinarith
  have hb1 : 1 ≤ b := by nlinarith
  have htri : 2 * |τ₀| ≤ |τ - τ₀| + |-τ - τ₀| := by
    have h := abs_add_le (τ - τ₀) (-τ - τ₀)
    rw [show τ - τ₀ + (-τ - τ₀) = -(2 * τ₀) by ring, abs_neg, abs_mul, abs_two] at h
    exact h
  have hab : 1 + 2 * S * |τ₀| ≤ a * b := by
    have : 0 ≤ S * |τ - τ₀| * (S * |-τ - τ₀|) := by positivity
    nlinarith
  have h1 : ‖H τ‖ ≤ K₁ * S * Cκ ^ 2 / a ^ 4 := by
    refine (hup τ).trans (le_of_eq ?_)
    rw [← ha]; field_simp
  have h2 : ‖H (-τ)‖ ≤ K₁ * S * Cκ ^ 2 / b ^ 4 := by
    refine (hup (-τ)).trans (le_of_eq ?_)
    rw [← hb]; field_simp
  have h3 : |D τ| ≤ CD * a := by
    refine (hD τ).trans (mul_le_mul_of_nonneg_left ?_ hCD)
    rw [ha]; nlinarith
  have hpos1 : 0 ≤ K₁ * S * Cκ ^ 2 / a ^ 4 := by positivity
  have hb4 : b ≤ b ^ 4 := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ 4 := pow_le_pow_right₀ hb1 (by norm_num)
  have hkey : 2 * |τ₀| * S ≤ a * b ^ 4 := by
    have : a * b ≤ a * b ^ 4 := mul_le_mul_of_nonneg_left hb4 (by linarith)
    nlinarith
  have hK : 0 ≤ K₁ ^ 2 * Cκ ^ 4 * CD * S := by positivity
  calc ‖H τ‖ * ‖H (-τ)‖ * |D τ|
      ≤ (K₁ * S * Cκ ^ 2 / a ^ 4) * (K₁ * S * Cκ ^ 2 / b ^ 4) * (CD * a) := by gcongr
    _ = K₁ ^ 2 * Cκ ^ 4 * CD * S ^ 2 / (a ^ 3 * b ^ 4) := by field_simp
    _ ≤ K₁ ^ 2 * Cκ ^ 4 * CD * S / (2 * |τ₀|) * (1 / a ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [mul_le_mul_of_nonneg_left hkey hK]

/-- **The cross term.**  A profile concentrated at `τ₀ ≠ 0` on the scale `1/S` has a cross term
with its reflection bounded independently of `S`. -/
theorem integral_cross_le {H : ℝ → ℂ} {D : ℝ → ℝ} {K₁ S Cκ CD τ₀ : ℝ} (hS : 1 ≤ S)
    (hτ₀ : τ₀ ≠ 0) (hK₁ : 0 ≤ K₁) (hCD : 0 ≤ CD)
    (hup : ∀ τ, ‖H τ‖ ≤ K₁ * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2))
    (hD : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|)) :
    ∫ τ : ℝ, ‖H τ‖ * ‖H (-τ)‖ * |D τ| ≤
      K₁ ^ 2 * Cκ ^ 4 * CD * (∫ u : ℝ, 1 / (1 + |u|) ^ 2) / (2 * |τ₀|) := by
  have hS0 : 0 < S := by linarith
  have hτ : 0 < |τ₀| := abs_pos.mpr hτ₀
  have hint : Integrable fun τ : ℝ =>
      K₁ ^ 2 * Cκ ^ 4 * CD * S / (2 * |τ₀|) * (1 / (1 + S * |τ - τ₀|) ^ 2) :=
    (integrable_one_div_one_add_mul_abs_sub_sq hS0 τ₀).const_mul _
  calc ∫ τ : ℝ, ‖H τ‖ * ‖H (-τ)‖ * |D τ|
      ≤ ∫ τ : ℝ, K₁ ^ 2 * Cκ ^ 4 * CD * S / (2 * |τ₀|) * (1 / (1 + S * |τ - τ₀|) ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun τ => by positivity) hint
          (Eventually.of_forall (cross_pointwise_le hS hτ₀ hK₁ hCD hup hD))
    _ = K₁ ^ 2 * Cκ ^ 4 * CD * (∫ u : ℝ, 1 / (1 + |u|) ^ 2) / (2 * |τ₀|) := by
        rw [integral_const_mul, integral_one_div_one_add_mul_abs_sub_sq hS0]
        field_simp

/-- `‖(x − y)/2‖² D ≤ ¼(‖x‖² + ‖y‖²) D + ½‖x‖‖y‖|D|`. -/
theorem norm_sub_div_two_sq_mul_le (x y : ℂ) (d : ℝ) :
    ‖(x - y) / 2‖ ^ 2 * d ≤
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 4 * d + ‖x‖ * ‖y‖ * |d| / 2 := by
  have h : ‖(x - y) / 2‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x * conj y).re) / 4 := by
    rw [norm_div, Complex.norm_two, div_pow, Complex.sq_norm, Complex.normSq_sub,
      ← Complex.sq_norm, ← Complex.sq_norm]
    norm_num
  rw [h]
  have hre : |(x * conj y).re| ≤ ‖x‖ * ‖y‖ := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_conj]
  have h1 : -((x * conj y).re * d) ≤ ‖x‖ * ‖y‖ * |d| := by
    calc -((x * conj y).re * d) ≤ |(x * conj y).re * d| := neg_le_abs _
      _ = |(x * conj y).re| * |d| := abs_mul _ _
      _ ≤ ‖x‖ * ‖y‖ * |d| := mul_le_mul_of_nonneg_right hre (abs_nonneg d)
  nlinarith

/-- **The energy of an odd part.**  If `F(τ) = (H(τ) − H(−τ))/2` and `D` is even, then
`∫ |F|² D ≤ ½ ∫ |H|² D` up to the cross term of `integral_cross_le`. -/
theorem integral_oddPart_normSq_mul_le {H F : ℝ → ℂ} {D : ℝ → ℝ} {K₁ S Cκ CD τ₀ : ℝ}
    (hHc : Continuous H) (hDc : Continuous D) (hDe : ∀ τ, D (-τ) = D τ)
    (hint : Integrable fun τ => ‖H τ‖ ^ 2 * D τ) (hintF : Integrable fun τ => ‖F τ‖ ^ 2 * D τ)
    (hF : ∀ τ, F τ = (H τ - H (-τ)) / 2) (hS : 1 ≤ S) (hτ₀ : τ₀ ≠ 0) (hK₁ : 0 ≤ K₁)
    (hCD : 0 ≤ CD) (hup : ∀ τ, ‖H τ‖ ≤ K₁ * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2))
    (hD : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|)) :
    ∫ τ : ℝ, ‖F τ‖ ^ 2 * D τ ≤ (∫ τ : ℝ, ‖H τ‖ ^ 2 * D τ) / 2 +
      K₁ ^ 2 * Cκ ^ 4 * CD * (∫ u : ℝ, 1 / (1 + |u|) ^ 2) / (2 * |τ₀|) / 2 := by
  have hS0 : 0 < S := by linarith
  have hintN : Integrable fun τ : ℝ => ‖H (-τ)‖ ^ 2 * D τ := by
    refine hint.comp_neg.congr (Eventually.of_forall fun τ => ?_)
    simp only [hDe]
  have hintX : Integrable fun τ : ℝ => ‖H τ‖ * ‖H (-τ)‖ * |D τ| :=
    ((integrable_one_div_one_add_mul_abs_sub_sq hS0 τ₀).const_mul
      (K₁ ^ 2 * Cκ ^ 4 * CD * S / (2 * |τ₀|))).mono'
      ((hHc.norm.mul (hHc.comp continuous_neg).norm).mul hDc.abs).aestronglyMeasurable
      (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact cross_pointwise_le hS hτ₀ hK₁ hCD hup hD τ)
  have hpt : ∀ τ : ℝ, ‖F τ‖ ^ 2 * D τ ≤
      ((‖H τ‖ ^ 2 * D τ) / 4 + (‖H (-τ)‖ ^ 2 * D τ) / 4) + (‖H τ‖ * ‖H (-τ)‖ * |D τ|) / 2 :=
    fun τ => by
      rw [hF τ]
      have := norm_sub_div_two_sq_mul_le (H τ) (H (-τ)) (D τ)
      linarith
  have hR : Integrable fun τ : ℝ =>
      ((‖H τ‖ ^ 2 * D τ) / 4 + (‖H (-τ)‖ ^ 2 * D τ) / 4) + (‖H τ‖ * ‖H (-τ)‖ * |D τ|) / 2 :=
    ((hint.div_const 4).add (hintN.div_const 4)).add (hintX.div_const 2)
  have hmono : ∫ τ : ℝ, ‖F τ‖ ^ 2 * D τ ≤ ∫ τ : ℝ,
      (((‖H τ‖ ^ 2 * D τ) / 4 + (‖H (-τ)‖ ^ 2 * D τ) / 4) + (‖H τ‖ * ‖H (-τ)‖ * |D τ|) / 2) :=
    integral_mono hintF hR hpt
  have hA : Integrable fun τ : ℝ => ‖H τ‖ ^ 2 * D τ / 4 := hint.div_const 4
  have hBn : Integrable fun τ : ℝ => ‖H (-τ)‖ ^ 2 * D τ / 4 := hintN.div_const 4
  have hAB : Integrable fun τ : ℝ => ‖H τ‖ ^ 2 * D τ / 4 + ‖H (-τ)‖ ^ 2 * D τ / 4 := hA.add hBn
  have hC : Integrable fun τ : ℝ => ‖H τ‖ * ‖H (-τ)‖ * |D τ| / 2 := hintX.div_const 2
  rw [integral_add hAB hC, integral_add hA hBn, integral_div, integral_div, integral_div] at hmono
  have hN : ∫ τ : ℝ, ‖H (-τ)‖ ^ 2 * D τ = ∫ τ : ℝ, ‖H τ‖ ^ 2 * D τ := by
    rw [← integral_neg_eq_self (fun τ : ℝ => ‖H τ‖ ^ 2 * D τ)]
    congr 1; funext τ; rw [hDe]
  rw [hN] at hmono
  have hX := integral_cross_le hS hτ₀ hK₁ hCD hup hD
  linarith

/-! ### Concentrated odd radical tests -/

/-- **Odd concentration.**  If `P ≥ d₁/2` near `τ₀ ≠ 0`, `P` is even and the radical limit has
size `≥ m/2` there, an odd pole-free test has negative symbol energy against `S_Λ − P`. -/
theorem vonMangoldt_sub_symbol_odd_violation {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) (hPe : ∀ τ, P (-τ) = P τ)
    {τ₀ η m d₁ : ℝ} (hη0 : 0 < η) (hm0 : 0 < m) (hd₁0 : 0 < d₁)
    (hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ P τ ∧ m / 2 ≤ ‖twistLimit 0 τ‖)
    (hτ₀ : τ₀ ≠ 0) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (∀ x, f (-x) = -f x) ∧ paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ)) < 0 := by
  set D : ℝ → ℝ := fun τ => -P τ with hDdef
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_norm_paperFT_weilBumpC_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_oddTwistTest_log_le τ₀
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set Aκ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hAκ
  have hAκ0 : 0 ≤ Aκ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set B := (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) * Aκ with hB
  have hB0 : 0 ≤ B := mul_nonneg (integral_nonneg fun _ => by positivity) hAκ0
  have hMp0 : 0 ≤ Mp := nonneg_of_linear_bound hPb
  obtain ⟨CD, hCD⟩ : ∃ CD : ℝ, CD = Mp * (1 + |τ₀|) := ⟨_, rfl⟩
  have hCD0 : 0 ≤ CD := by rw [hCD]; positivity
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  set c := (Real.cos (1 / 4) / 4) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set I₃ := ∫ τ : ℝ, 1 / (1 + |τ - τ₀|) ^ 3 with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun _ => by positivity
  set I₂ := ∫ u : ℝ, 1 / (1 + |u|) ^ 2 with hI₂
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun _ => by positivity
  set L₀ := m / 4 * c with hL₀
  have hL₀0 : 0 < L₀ := by positivity
  set Ctail := |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / η ^ 4) * I₃ with hCtail
  have hCtail0 : 0 ≤ Ctail := by positivity
  have hτ₀a : 0 < |τ₀| := abs_pos.mpr hτ₀
  set Ccross := (B ^ 3) ^ 2 * Cκ ^ 4 * CD * I₂ / (2 * |τ₀|) with hCcross
  have hCcross0 : 0 ≤ Ccross := by positivity
  set goal := d₁ / 2 * L₀ ^ 2 with hgoal
  have hgoal0 : 0 < goal := by positivity
  have t1 : Tendsto (fun S : ℝ => 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have t3 : Tendsto (fun S : ℝ => Ctail / S ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have t4 : Tendsto (fun S : ℝ => 2 * π * KW * (S ^ 9 * Real.exp (-S))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul (2 * π * KW)
  have t6 : Tendsto (fun S : ℝ => Ccross / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨S, ⟨⟨⟨⟨hE2, hE4⟩, hE5⟩, hE6⟩, hE1⟩⟩ := ((((t1.eventually (ge_mem_nhds (by linarith :
    (0 : ℝ) < m / 4))).and (t3.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 2)))).and
    (t4.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 8)))).and
    (t6.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 8)))).and
    (eventually_ge_atTop (max (max (Real.exp 1) (1 / η)) 1)) |>.exists
  have hSe : Real.exp 1 ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE1
  have hSη : 1 / η ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE1
  have hS1 : 1 ≤ S := le_trans (le_max_right _ _) hE1
  have hS0 : 0 < S := by linarith
  have h1S : 1 / S ≤ η := by
    rw [div_le_iff₀ hS0]; rw [div_le_iff₀ hη0] at hSη; linarith
  set R := Real.log S with hR
  have hR1 : 1 ≤ R := by rw [hR, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hSe
  have hR0 : 0 ≤ R := by linarith
  set g := twistTest 0 τ₀ R S with hg
  have hgd : ContDiff ℝ 2 g := contDiff_twistTest 0 τ₀ R S
  have hgs : tsupport g ⊆ Icc (-(3 * R + S)) (3 * R + S) := tsupport_twistTest hS0
  set f := oddTwistTest τ₀ R S with hf
  have hfd : ContDiff ℝ 2 f := contDiff_oddTwistTest τ₀ R S
  have hfs : tsupport f ⊆ Icc (-(3 * R + S)) (3 * R + S) := tsupport_oddTwistTest hS0
  have hp : paperFT f (I / 2) = 0 := paperFT_oddTwistTest_half_I hS0
  have hm' : paperFT f (-(I / 2)) = 0 := paperFT_oddTwistTest_neg_half_I hS0
  have hεR : (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) ≤
      E₀ * C₆ * Real.exp (1 / 4) / S := by
    refine (riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR1 (by norm_num)).trans (le_of_eq ?_)
    rw [show -(R - 1 / 4) = 1 / 4 + -R by ring, Real.exp_add, Real.exp_neg, hR,
      Real.exp_log hS0]
    field_simp
  have happrox : 3 * B ^ 2 * ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ) ≤
      m / 4 := by
    refine le_trans ?_ hE2
    have : (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ ≤
        E₀ * C₆ * Real.exp (1 / 4) / S * Aκ := mul_le_mul_of_nonneg_right hεR hAκ0
    calc 3 * B ^ 2 * ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ)
        ≤ 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) / S * Aκ) := by gcongr
      _ = 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S := by ring
  have hsed : SuperExpDecay g := ⟨hgd.continuous, fun c' =>
    (hgd.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (a := 3 * R + S) fun u hu =>
        twistTest_eq_zero hS0 hu).norm.mul_right⟩
  have hHc : Continuous fun τ : ℝ => paperFT g τ :=
    hsed.differentiable_paperFT.continuous.comp Complex.continuous_ofReal
  have hHm : AEStronglyMeasurable (fun τ : ℝ => paperFT g τ) volume := hHc.aestronglyMeasurable
  have hDc : Continuous D := hPc.neg
  have hDlin : ∀ τ, |D τ| ≤ Mp * (1 + |τ|) := fun τ => by rw [hDdef, abs_neg]; exact hPb τ
  have hDbd : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|) := fun τ => by
    rw [hCD]; exact linear_bound_shift (hDlin τ) hMp0 τ₀
  have hint : Integrable fun τ : ℝ => ‖paperFT g τ‖ ^ 2 * D τ :=
    integrable_normSq_paperFT_mul_of_linear hgd hgs hDc hDlin
  have hup : ∀ τ : ℝ, ‖paperFT g τ‖ ≤ B ^ 3 * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2) :=
    fun τ => norm_paperFT_twistTest_real_le hS0 hCκ τ
  -- the energy of the twisted test
  have hconc := concentrated_integral_lower (H := fun τ : ℝ => paperFT g τ) (D := D)
    (t := -1) (τ₀ := τ₀) (η := η) (S := S) (d₁ := d₁) (L := L₀ * S) (K₁ := B ^ 3) (Cκ := Cκ)
    (CD := CD) hS1 hη0 h1S hd₁0 (by positivity) hCD0 (by positivity) hCκ0 hHm hint
    (fun τ hτ => by rw [hDdef]; simp only [neg_mul, one_mul, neg_neg]; exact (hnear τ hτ).1)
    (fun τ hτ => by
      have := norm_paperFT_twistTest_real_ge (α := 0) (R := R) hS0 hτ
        (hnear τ (hτ.trans h1S)).2 happrox
      rw [hL₀]; convert this using 1; ring)
    hup hDbd
  have hmain : d₁ / 2 * (2 / S * (L₀ * S) ^ 2) -
      |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) * I₃ =
      2 * goal * S - Ctail / S ^ 2 := by
    rw [hgoal, hCtail]; field_simp
  rw [hmain] at hconc
  have hE4' : Ctail / S ^ 2 ≤ goal / 2 * S := by
    have := mul_le_mul_of_nonneg_right hE4 hS0.le
    calc Ctail / S ^ 2 = Ctail / S ^ 3 * S := by field_simp
      _ ≤ goal / 2 * S := this
  have hDneg : ∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * D τ ≤ -(3 / 2 * goal * S) := by linarith
  -- the energy of the odd test against 
  have hfT : ∀ τ : ℝ, (fun τ : ℝ => paperFT f τ) τ =
      ((fun τ : ℝ => paperFT g τ) τ - (fun τ : ℝ => paperFT g τ) (-τ)) / 2 := fun τ => by
    simp only
    rw [hf, paperFT_oddTwistTest hS0, Complex.ofReal_neg]
  have hDe : ∀ τ, D (-τ) = D τ := fun τ => by simp only [hDdef, hPe]
  have hintF : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * D τ :=
    integrable_normSq_paperFT_mul_of_linear hfd hfs hDc hDlin
  have hodd := integral_oddPart_normSq_mul_le (H := fun τ : ℝ => paperFT g τ)
    (F := fun τ : ℝ => paperFT f τ) hHc hDc hDe hint hintF hfT hS1 hτ₀
    (by positivity : (0 : ℝ) ≤ B ^ 3) hCD0 hup hDbd
  have hodd' : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ ≤
      (∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * D τ) / 2 + Ccross / 2 := by
    refine hodd.trans (le_of_eq ?_)
    rw [hCcross]
  -- the zero side
  have hWS : 2 * π * ‖zetaZeroConfig.W f f‖ ≤ goal / 8 * S := by
    have h := hKW S hSe
    have hπ : 0 < π := Real.pi_pos
    calc 2 * π * ‖zetaZeroConfig.W f f‖ ≤ 2 * π * (KW * S ^ 10 * Real.exp (-S)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * π * KW * (S ^ 9 * Real.exp (-S)) * S := by ring
      _ ≤ goal / 8 * S := mul_le_mul_of_nonneg_right hE5 hS0.le
  have hcrossS : Ccross / 2 ≤ goal / 16 * S := by
    have := mul_le_mul_of_nonneg_right hE6 hS0.le
    have e : Ccross / S * S = Ccross := by field_simp
    rw [e] at this; linarith
  -- assemble
  have ha0 : 0 ≤ 3 * R + S := by linarith
  refine ⟨3 * R + S, ha0, f, hfd, hfs, oddTwistTest_neg τ₀ R S, hp, hm', ?_⟩
  have hΛi := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs (fun n => (Λ n : ℝ))
  have hPi : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * P τ := by
    refine hintF.neg.congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.neg_apply, hDdef]; ring
  have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * (3 * R + S))⌋₊ (τ / (2 * π)) - P τ) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * (3 * R + S))⌋₊ (τ / (2 * π))) -
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ := by
    rw [← integral_sub hΛi hPi]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only; ring
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hfd hfs hp hm'
  have hWre : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * (3 * R + S))⌋₊ (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hW, Complex.ofReal_re]; field_simp
  have hre := Complex.re_le_norm (zetaZeroConfig.W f f)
  have hPD : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ = -∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ := by
    rw [← integral_neg]; congr 1; funext τ; simp only [hDdef]; ring
  have hπ : 0 < π := Real.pi_pos
  have hre2 : 2 * π * (zetaZeroConfig.W f f).re ≤ 2 * π * ‖zetaZeroConfig.W f f‖ :=
    mul_le_mul_of_nonneg_left hre (by positivity)
  have hgS : 0 < goal * S := by positivity
  rw [hsplit, hWre, hPD]
  linarith

/-! ### Two-point resonators -/

/-- **Two-point resonators read off the weights.**  If the pairing of `w` with the
autocorrelation of every test vanishes, then `w(n₀) = 0`. -/
theorem eq_zero_of_pairing_vanishes {w : ℕ → ℝ}
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re = 0)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  set N := n₀ with hNdef
  set c := twoPointCoeff n₀ (1 : ℂ) with hcdef
  have hN : 1 ≤ N := by omega
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set ω : ℝ := 1 / ((N : ℝ) + 1) with hωdef
  have hω : 0 < ω := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  set a : ℝ := Real.log N / 2 + ω / 4 with hadef
  have ha : 0 ≤ a := by positivity
  set F := resonator N c ω with hFdef
  have hc : ∀ m, N < m → c m = 0 := by
    intro m hm; simp only [hcdef, twoPointCoeff]; rw [if_neg (by omega), if_neg (by omega)]
  have hFvan : ∀ u, a < |u| → F u = 0 := fun u hu =>
    sum_translates_eq_zero (fun v hv => gC_eq_zero hω hv) hu
  have hFs : tsupport F ⊆ Icc (-a) a := tsupport_subset_of_vanish hFvan
  have hF2 : ContDiff ℝ 2 F := contDiff_resonator N c ω 2
  set k0r : ℝ := ∫ t, gR ω t ^ 2 with hk0r
  have hk0 : EF.weilTest (gC ω) (gC ω) 0 = (k0r : ℂ) := weilTest_self_zero_ofReal (g := gR ω)
  have hk0pos : 0 < k0r := lt_of_lt_of_le (div_pos integral_d2_sq_pos (by positivity))
    (integral_gR_sq_ge hω)
  have hgap : 2 * (ω / 4) < 1 / ((N : ℝ) + 1) := by rw [← hωdef]; linarith
  have hvan0 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest (gC ω) (gC ω) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hω hu) (by linarith)
  have hgc0 : Continuous (gC ω) := (contDiff_gC ω 0).continuous
  have hgs0 := hasCompactSupport_gC hω
  have hsel : ∀ n : ℕ, 2 ≤ n →
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re =
        2 * k0r * (if n = n₀ then 1 else 0) := by
    intro n hn
    have h1 := weilTest_translates_log hgc0 hgs0 hvan0 hc (show 1 ≤ n by omega)
    have h2 := weilTest_translates_neg_log hgc0 hgs0 hvan0 hc (show 1 ≤ n by omega)
    rw [sum_conj_swap] at h2
    rw [show F = fun u => ∑ m ∈ Finset.Icc 1 N, c m * gC ω (u - resPt N m) from rfl, h1, h2, hk0,
      hcdef, twoPointCoeff_diag hn₀ _ hn]
    split_ifs <;> simp [Complex.add_re]; ring
  have hM : n₀ ≤ ⌊Real.exp (2 * a)⌋₊ := by
    apply Nat.le_floor
    have : Real.exp (Real.log N) ≤ Real.exp (2 * a) :=
      Real.exp_le_exp.mpr (by rw [hadef]; linarith)
    rwa [Real.exp_log (by linarith)] at this
  have hpairF := hpair a ha F hF2 hFs
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re =
      w n₀ / Real.sqrt n₀ * (2 * k0r) := by
    rw [Finset.sum_eq_single n₀]
    · rw [hsel n₀ hn₀, if_pos rfl, mul_one]
    · intro n hn hne
      rw [hsel n (Finset.mem_Icc.mp hn).1, if_neg hne, mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hn₀, hM⟩) h
  rw [hsum] at hpairF
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have hπ : 0 < π := Real.pi_pos
  have h2 : w n₀ / Real.sqrt n₀ * (2 * k0r) = 0 := by
    rcases mul_eq_zero.mp hpairF with h | h
    · exfalso; have : (2 : ℝ) * π ≠ 0 := by positivity
      exact this h
    · exact h
  rcases mul_eq_zero.mp h2 with h | h
  · rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hsq.ne'
  · exfalso; linarith

/-! ### The reflected test -/

theorem tsupport_comp_neg_subset {f : ℝ → ℂ} {a : ℝ} (hfs : tsupport f ⊆ Icc (-a) a) :
    tsupport (fun x => f (-x)) ⊆ Icc (-a) a := by
  refine tsupport_subset_of_vanish fun u hu => image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hfs hmem
  rw [mem_Icc] at this
  rcases le_or_gt 0 u with h0 | h0
  · rw [abs_of_nonneg h0] at hu; linarith [this.1]
  · rw [abs_of_neg h0] at hu; linarith [this.2]

/-- Reflecting a test reflects its autocorrelation. -/
theorem weilTest_comp_neg (f : ℝ → ℂ) (y : ℝ) :
    EF.weilTest (fun x => f (-x)) (fun x => f (-x)) y = EF.weilTest f f (-y) := by
  simp only [EF.weilTest, EF.tilde, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_neg_eq_self]
  congr 1
  funext t
  simp only [neg_neg, neg_sub, sub_neg_eq_add]
  ring_nf

/-- **The pairing identity holds for the even part of the symbol.** -/
theorem pairing_even_part {w : ℕ → ℝ} {P : ℝ → ℝ} (hPc : Continuous P) {Mp : ℝ}
    (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) {m : ℝ}
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ) + m * ‖paperFT f 0‖ ^ 2)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * ((P τ + P (-τ)) / 2)) + m * ‖paperFT f 0‖ ^ 2 := by
  have hf' : ContDiff ℝ 2 fun x => f (-x) := hf.comp contDiff_neg
  have hfs' := tsupport_comp_neg_subset hfs
  have h1 := hpair a ha f hf hfs
  have h2 := hpair a ha (fun x => f (-x)) hf' hfs'
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
      (EF.weilTest (fun x => f (-x)) (fun x => f (-x)) (Real.log n) +
        EF.weilTest (fun x => f (-x)) (fun x => f (-x)) (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [weilTest_comp_neg, weilTest_comp_neg, neg_neg, add_comm]
  rw [hsum] at h2
  have hT : ∀ τ : ℝ, paperFT (fun x => f (-x)) τ = paperFT f ((-τ : ℝ) : ℂ) := fun τ => by
    rw [paperFT_comp_neg, Complex.ofReal_neg]
  have h0 : paperFT (fun x => f (-x)) 0 = paperFT f 0 := by
    rw [paperFT_comp_neg, neg_zero]
  simp only [hT, h0] at h2
  have hPn : Continuous fun τ : ℝ => P (-τ) := hPc.comp continuous_neg
  have hPnb : ∀ τ, |P (-τ)| ≤ Mp * (1 + |τ|) := fun τ => by
    have := hPb (-τ); rwa [abs_neg] at this
  have hi1 := integrable_normSq_paperFT_mul_of_linear hf hfs hPc hPb
  have hi2 := integrable_normSq_paperFT_mul_of_linear hf hfs hPn hPnb
  have hrefl : ∫ τ : ℝ, ‖paperFT f ((-τ : ℝ) : ℂ)‖ ^ 2 * P τ =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P (-τ) := by
    rw [← integral_neg_eq_self (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * P (-τ))]
    congr 1; funext τ; rw [neg_neg]
  rw [hrefl] at h2
  have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * ((P τ + P (-τ)) / 2) =
      ((∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ) + ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P (-τ)) / 2 := by
    rw [← integral_add hi1 hi2, ← integral_div]
    congr 1; funext τ; ring
  rw [hsplit]
  linarith

/-! ### Rigidity with an atom, on odd tests -/

/-- **Rigidity with an atom from odd positivity.**  If the atoms of `w` pair with the tests through
a continuous symbol of linear growth plus `m |f̂(0)|²`, and `Λ + w` is Weil-positive on pole-free
odd tests, then `w = 0`. -/
theorem vonMangoldt_add_eq_zero_of_symbol_atom_odd {w : ℕ → ℝ} {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) {m : ℝ}
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ) + m * ‖paperFT f 0‖ ^ 2)
    (hpos : WeilPositiveOddPolar fun n => (Λ n : ℝ) + w n)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  -- the even part of the symbol
  set Q : ℝ → ℝ := fun τ => (P τ + P (-τ)) / 2 with hQdef
  have hQc : Continuous Q := (hPc.add (hPc.comp continuous_neg)).div_const 2
  have hQb : ∀ τ, |Q τ| ≤ Mp * (1 + |τ|) := fun τ => by
    have h1 := hPb τ
    have h2 := hPb (-τ)
    rw [abs_neg] at h2
    simp only [hQdef]
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le (P τ) (P (-τ))]
  have hQe : ∀ τ, Q (-τ) = Q τ := fun τ => by simp only [hQdef, neg_neg]; ring
  have hpairQ : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Q τ) + m * ‖paperFT f 0‖ ^ 2 :=
    fun a ha f hf hfs => pairing_even_part hPc hPb hpair ha hf hfs
  -- the energy identity on odd tests
  have henergy : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      (∀ x, f (-x) = -f x) →
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - Q τ) := by
    intro a ha f hf hfs hodd
    rw [integral_weilAtomSymbol_eq_sub hf hfs]
    have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, ((Λ n : ℝ) + w n - Λ n) / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
      Finset.sum_congr rfl fun n _ => by ring_nf
    rw [hsum, hpairQ a ha f hf hfs, paperFT_zero_of_odd hodd, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    rw [← integral_sub
      (integrable_normSq_paperFT_mul_weilAtomSymbol_of hf hfs (fun n => (Λ n : ℝ)))
      (integrable_normSq_paperFT_mul_of_linear hf hfs hQc hQb)]
    have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) -
          ‖paperFT f τ‖ ^ 2 * Q τ) = fun τ : ℝ => ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - Q τ) := by
      funext τ; ring
    rw [e]
  -- step 1: `Q ≤ 0` everywhere
  have hle : ∀ τ, Q τ ≤ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨τ₁, hτ₁⟩ := hall
    set d₁ := Q τ₁ with hd₁
    obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
      (hQc.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
    have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ Q τ := by
      intro τ hτ
      have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
      rw [Real.dist_eq] at this
      have := (abs_lt.mp this).1
      linarith
    have hne0 : ∀ᶠ t : ℝ in 𝓝[≠] τ₁, t ≠ 0 := by
      rcases eq_or_ne τ₁ 0 with h | h
      · rw [h]; exact self_mem_nhdsWithin
      · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)
    have hev := ((eventually_radicalLimit_shift_ne_zero 0 τ₁).and
      (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0)))).and hne0
    obtain ⟨τ₀, ⟨h0, hball⟩, hτ₀ne⟩ := hev.exists
    have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
    have hlim0 : twistLimit 0 τ₀ ≠ 0 := by
      unfold twistLimit
      simp only [Complex.ofReal_zero, add_zero, neg_zero] at h0 ⊢
      exact mul_ne_zero (mul_ne_zero h0 h0) h0
    set m' := ‖twistLimit 0 τ₀‖ with hm'
    have hm0 : 0 < m' := norm_pos_iff.mpr hlim0
    obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
      ((continuous_twistLimit_real 0).continuousAt (x := τ₀)) (m' / 2) (by linarith)
    set η := min (η₁ / 2) (η₂ / 2) with hη
    have hη0 : 0 < η := lt_min (by linarith) (by linarith)
    have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ Q τ ∧ m' / 2 ≤ ‖twistLimit 0 τ‖ := by
      intro τ hτ
      constructor
      · refine hnear₁ τ ?_
        have : |τ - τ₁| ≤ |τ - τ₀| + |τ₀ - τ₁| := by
          calc |τ - τ₁| = |(τ - τ₀) + (τ₀ - τ₁)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        have := min_le_left (η₁ / 2) (η₂ / 2)
        linarith
      · have hd : dist τ τ₀ < η₂ := by
          rw [Real.dist_eq]; have := min_le_right (η₁ / 2) (η₂ / 2); linarith
        have := hη₂ hd
        rw [dist_eq_norm] at this
        have := norm_sub_norm_le (twistLimit 0 τ₀) (twistLimit 0 τ)
        rw [norm_sub_rev] at this
        linarith
    obtain ⟨a, ha, f, hfd, hfs, hodd, hp, hm'', hneg⟩ :=
      vonMangoldt_sub_symbol_odd_violation hQc hQb hQe hη0 hm0 hτ₁ hnear hτ₀ne
    have := hpos a ha f hfd hfs hodd hp hm''
    rw [henergy a ha f hfd hfs hodd] at this
    linarith
  -- the probe identity
  have hε : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hprobe : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
      tsupport g ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) →
      (∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * Q τ) + m * ‖paperFT g 0‖ ^ 2 = 0 := by
    intro g hg hgs
    have hint0 := hpairQ (Real.log 2 / 4) (by positivity) g hg hgs
    rw [floor_exp_half_log_two] at hint0
    simp only [Finset.Icc_eq_empty (by norm_num : ¬ (2 ≤ 1)), Finset.sum_empty, mul_zero] at hint0
    exact hint0.symm
  -- step 2a: `Q ≡ 0`
  have hzero' : ∀ t : ℝ, t ≠ 0 → Q t = 0 := by
    intro t ht
    set g := zeroMeanProbe (Real.log 2) t with hgdef
    have hg := contDiff_zeroMeanProbe (Real.log 2) t
    have hgs : tsupport g ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) :=
      tsupport_zeroMeanProbe hε t
    have hint0 := hprobe g hg hgs
    rw [paperFT_zeroMeanProbe_zero hε t, norm_zero] at hint0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] at hint0
    obtain ⟨hgc, -, -, -, -⟩ := weilTest_self_data hg hgs
    have hHc : Continuous fun τ : ℝ => ‖paperFT g τ‖ ^ 2 :=
      (continuous_paperFT_real_of_integrable (hg.continuous.integrable_of_hasCompactSupport
        hgc)).norm.pow 2
    set F : ℝ → ℝ := fun τ => ‖paperFT g τ‖ ^ 2 * -Q τ with hFdef
    have hFc : Continuous F := hHc.mul hQc.neg
    have hF0 : 0 ≤ F := fun τ => mul_nonneg (sq_nonneg _) (by linarith [hle τ])
    have hFi : Integrable F :=
      (integrable_normSq_paperFT_mul_of_linear hg hgs hQc hQb).neg.congr
        (Eventually.of_forall fun τ => by simp only [Pi.neg_apply, hFdef]; ring)
    have hFint : ∫ τ, F τ = 0 := by
      have e : F = fun τ : ℝ => -(‖paperFT g τ‖ ^ 2 * Q τ) := by
        funext τ; simp only [hFdef]; ring
      rw [e, integral_neg, hint0, neg_zero]
    have hae := (integral_eq_zero_iff_of_nonneg hF0 hFi).mp hFint
    have hz : F = 0 := (hFc.ae_eq_iff_eq volume continuous_const).mp hae
    have hτ := congrFun hz t
    simp only [hFdef, Pi.zero_apply] at hτ
    have hne : ‖paperFT g t‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr
      (paperFT_zeroMeanProbe_ne_zero hε ht))
    have := (mul_eq_zero.mp hτ).resolve_left hne
    linarith
  have hQzero : Q = fun _ => 0 :=
    hQc.ext_on (dense_compl_singleton (0 : ℝ)) continuous_const fun t ht => hzero' t ht
  -- step 2b: `m = 0`
  set g₀ := smallProbe (Real.log 2) 0 with hg₀
  have hg₀d := contDiff_smallProbe (Real.log 2) 0
  have hg₀s : tsupport g₀ ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) := tsupport_smallProbe hε 0
  have hg₀0 : 0 < ‖paperFT g₀ 0‖ ^ 2 := by
    have := paperFT_smallProbe_ne_zero hε 0
    push_cast at this
    positivity
  have hmzero : m = 0 := by
    have h1 := hprobe g₀ hg₀d hg₀s
    rw [hQzero] at h1
    simp only [mul_zero, integral_zero, zero_add] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hg₀0.ne'
  -- step 3: the pairing vanishes on every test; two-point resonators read off `w(n₀)`
  have hpair0 : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re = 0 := by
    intro a ha f hf hfs
    rw [hpairQ a ha f hf hfs, hQzero, hmzero]
    simp
  exact eq_zero_of_pairing_vanishes hpair0 hn₀

/-! ### Across the `√n` barrier on odd tests -/

/-- **Odd rigidity across the barrier.**  If the partial sums of `w − κβ`, `β(n) = √n − √(n−1)`,
satisfy `∑ |E(n)|/(n √n) < ∞` for some real `κ`, then Weil positivity of `Λ + w` on pole-free odd
tests forces `w = 0`. -/
theorem vonMangoldt_add_halfPole_eq_zero_odd {w : ℕ → ℝ} {κ : ℝ}
    (hE : Summable (partialSumWeight fun n => w n - κ * sqrtStep n))
    (hpos : WeilPositiveOddPolar fun n => (Λ n : ℝ) + w n)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  set e : ℕ → ℝ := fun n => w n - κ * sqrtStep n with he
  set Zβ := ∑' n : ℕ, halfPoleWeight n with hZβ
  set Ze := ∑' n : ℕ, partialSumWeight e n with hZe
  have hZβ0 : 0 ≤ Zβ := tsum_nonneg halfPoleWeight_nonneg
  have hZe0 : 0 ≤ Ze := tsum_nonneg (partialSumWeight_nonneg e)
  refine vonMangoldt_add_eq_zero_of_symbol_atom_odd (w := w)
    (P := fun τ => κ * halfPoleSymbol τ + oscSymbol e τ)
    ((continuous_const.mul continuous_halfPoleSymbol).add (continuous_oscSymbol_of_weight hE))
    (Mp := |κ| * (2 * Zβ) + 2 * Ze) (fun τ => ?_) (m := π * κ) (fun a ha f hf hfs => ?_) hpos hn₀
  · have h1 := abs_halfPoleSymbol_le τ
    have h2 := abs_oscSymbol_le_of_weight hE τ
    calc |κ * halfPoleSymbol τ + oscSymbol e τ| ≤ |κ| * |halfPoleSymbol τ| + |oscSymbol e τ| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |κ| * (2 * Zβ * (1 + |τ|)) + 2 * Ze * (1 + |τ|) := by gcongr
      _ = (|κ| * (2 * Zβ) + 2 * Ze) * (1 + |τ|) := by ring
  · have hβ := pairing_sqrtStep ha hf hfs
    have he' := pairing_eq_integral_oscSymbol hE hf hfs
    have hsplit : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
        κ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, sqrtStep n / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, e n / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [he]; ring
    have hi1 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs continuous_halfPoleSymbol
        (Mp := 2 * Zβ) fun τ => abs_halfPoleSymbol_le τ
    have hi2 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * oscSymbol e τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs (continuous_oscSymbol_of_weight hE)
        (Mp := 2 * Ze) fun τ => abs_oscSymbol_le_of_weight hE τ
    have hint : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (κ * halfPoleSymbol τ + oscSymbol e τ) =
        κ * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ) +
          ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * oscSymbol e τ := by
      rw [← integral_const_mul, ← integral_add (hi1.const_mul κ) hi2]
      congr 1; funext τ; ring
    rw [hsplit, mul_add, hint, ← he']
    have : 2 * π * (κ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, sqrtStep n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) =
        κ * (2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, sqrtStep n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) := by ring
    rw [this, hβ]
    ring

/-- **Squares cannot be added, even on odd tests.**  The weights `Λ(n) + c·1_{n = m²}` are
Weil-positive on the pole-free odd tests only for `c = 0`, although odd tests do not see the
atom of the squares at the origin. -/
theorem vonMangoldt_add_squares_odd_eq_zero {c : ℝ}
    (hpos : WeilPositiveOddPolar fun n => (Λ n : ℝ) + c * perfectSquareWeight n) : c = 0 := by
  have hE : Summable (partialSumWeight fun n => c * perfectSquareWeight n - c * sqrtStep n) := by
    refine Summable.of_nonneg_of_le (partialSumWeight_nonneg _) (fun n => ?_)
      ((summable_growthWeight (θ := 0) (by norm_num)).mul_left |c|)
    unfold partialSumWeight growthWeight
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [partialFrom2]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [partialFrom2_sub_mul (fun k => c * perfectSquareWeight k) sqrtStep c n]
      have hw : partialFrom2 (fun k => c * perfectSquareWeight k) n =
          c * partialFrom2 perfectSquareWeight n := by
        unfold partialFrom2; rw [Finset.mul_sum]
      rw [hw, partialFrom2_perfectSquareWeight hn, partialFrom2_sqrtStep hn, Real.rpow_zero]
      have h1 := @Real.nat_sqrt_le_real_sqrt n
      have h2 := @Real.real_sqrt_lt_nat_sqrt_succ n
      have hb : |c * ((Nat.sqrt n : ℝ) - 1) - c * (Real.sqrt n - 1)| ≤ |c| := by
        rw [← mul_sub, abs_mul]
        have : |((Nat.sqrt n : ℝ) - 1) - (Real.sqrt n - 1)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        calc |c| * |((Nat.sqrt n : ℝ) - 1) - (Real.sqrt n - 1)| ≤ |c| * 1 :=
              mul_le_mul_of_nonneg_left this (abs_nonneg c)
          _ = |c| := mul_one _
      have hd : 0 < (n : ℝ) * Real.sqrt n := by positivity
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hb hd.le
  have h := vonMangoldt_add_halfPole_eq_zero_odd (w := fun n => c * perfectSquareWeight n) (κ := c)
    hE hpos (n₀ := 4) (by norm_num)
  have hsq : perfectSquareWeight 4 = 1 := by
    unfold perfectSquareWeight
    have : Nat.sqrt 4 = 2 := by
      have h := Nat.sqrt_eq' 2
      rwa [show (2 : ℕ) ^ 2 = 4 by norm_num] at h
    rw [if_pos (by rw [this]; norm_num)]
  rw [hsq, mul_one] at h
  exact h

/-- **Squares and odd Weil positivity.**  If `Λ + c·1_{n = m²}` is Weil-positive (pole term
included) on all odd tests, then `c = 0`. -/
theorem vonMangoldt_add_squares_weilPositiveOdd_eq_zero {c : ℝ}
    (hW : WeilPositiveOdd fun n => (Λ n : ℝ) + c * perfectSquareWeight n) : c = 0 :=
  vonMangoldt_add_squares_odd_eq_zero (weilPositiveOddPolar_of_weilPositiveOdd hW)

/-- **The half-pole class and odd Weil positivity.** -/
theorem vonMangoldt_add_halfPole_weilPositiveOdd_eq_zero {w : ℕ → ℝ} {κ : ℝ}
    (hE : Summable (partialSumWeight fun n => w n - κ * sqrtStep n))
    (hW : WeilPositiveOdd fun n => (Λ n : ℝ) + w n) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 :=
  vonMangoldt_add_halfPole_eq_zero_odd hE (weilPositiveOddPolar_of_weilPositiveOdd hW) hn₀

end RHTower

end
