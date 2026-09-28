import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction
import GaloisForLFunctions.RHTower.WeilPrimeFreeTest
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# Twist rigidity of Weil positivity

Twist the von Mangoldt weights by `n^{±iα}`, keeping the archimedean term of `ζ`:
`λ(n) = Λ(n)(1 + t cos(α log n))`.  With `f₊ = f e^{iαx}`, `f₋ = f e^{-iαx}` and the archimedean
symbol `A(τ) = Re ψ(1/4 + iτ/2) - log π`, the symbol energy of a test `f` for which `f`, `f₊` and
`f₋` are all polar-constrained is exactly (`integral_weilAtomSymbol_twist`)

`∫ |h_f|² S_λ = 2π Re W(f) + πt (Re W(f₊) + Re W(f₋)) - (t/2) ∫ |h_f(τ)|² (A(τ-α) + A(τ+α)) dτ`.

Here `W` is the zero side of `ζ`.  The mechanism is `k_{f±}(y) = e^{±iαy} k_f(y)`: the twisted
prime sum is the ordinary prime sum of the modulated tests.

**Tests.**
- The triple radical `T_R = B_R ⋆ B_R e^{iα·} ⋆ B_R e^{-iα·}` (`B_R` the truncated radical test of
  `ζ`) has transform `B̂(z) B̂(z+α) B̂(z-α)`.  All three modulated tests carry the factor `B̂`, so
  their zero sides are `O(S^{10} e^{-S})` at `R = log S` (`exists_norm_W_twistTest_log_le`).
- The spread probe `q(x/S) e^{-iτ₀x}` with `q = κ ⋆ κ` concentrates `|h|²` at `τ₀` on the scale
  `1/S`.  The mass is `≥ cS` (`norm_paperFT_twistTest_real_ge`) and the tail is `O(S^{-2})`, since
  `κ̂²` decays like `(1+|v|)^{-4}` (`concentrated_integral_lower`).

**Theorems.**
- `twist_weilAtomSymbol_not_nonneg`: if `t (A(τ₁-α) + A(τ₁+α)) > 0` for some `τ₁`, Weil
  positivity fails.
- `twist_pos_weilAtomSymbol_not_nonneg`: every `α`, every `t > 0`.
- `twist_neg_weilAtomSymbol_not_nonneg`: every `t < 0` whenever `A(α) < 0`.
- `exists_twist_isolation`: two-sided isolation of `Λ` along all small twists.
- `scaled_vonMangoldt_weilAtomSymbol_not_nonneg`: `cΛ` fails for every `c ≠ 1`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

local notation "Φ" => riemannPhiKernel

/-! ### Modulated tests -/

/-- The modulation `f(x) e^{iαx}`; its transform is the transform of `f` shifted by `α`. -/
def twistModulate (α : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := f x * Complex.exp (I * α * x)

theorem paperFT_twistModulate (α : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    paperFT (twistModulate α f) z = paperFT f (z + α) := by
  unfold paperFT twistModulate
  congr 1; funext x
  rw [mul_assoc, ← Complex.exp_add]; congr 2; ring

theorem contDiff_twistModulate {α : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (twistModulate α f) := by
  have h : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact hf.mul (contDiff_const.mul h).cexp

theorem twistModulate_eq_zero {α : ℝ} {f : ℝ → ℂ} {x : ℝ} (hx : f x = 0) : twistModulate α f x = 0 := by
  simp [twistModulate, hx]

theorem tsupport_twistModulate_subset (α : ℝ) (f : ℝ → ℂ) : tsupport (twistModulate α f) ⊆ tsupport f :=
  closure_mono fun x hx => by
    simp only [Function.mem_support, twistModulate] at hx ⊢
    exact fun h => hx (by rw [h, zero_mul])

theorem weilTest_twistModulate (α : ℝ) (f : ℝ → ℂ) (y : ℝ) :
    EF.weilTest (twistModulate α f) (twistModulate α f) y =
      Complex.exp (I * α * y) * EF.weilTest f f y := by
  rw [weilTest_apply_eq, weilTest_apply_eq, ← integral_const_mul]
  congr 1; funext t
  have hc : (starRingEnd ℂ) (Complex.exp (I * α * ((t - y : ℝ) : ℂ))) =
      Complex.exp (-(I * α * ((t - y : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have e : Complex.exp (I * α * t) * Complex.exp (-(I * α * ((t - y : ℝ) : ℂ))) =
      Complex.exp (I * α * y) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [twistModulate]
  rw [map_mul, hc]
  calc f t * Complex.exp (I * α * t) * ((starRingEnd ℂ) (f (t - y)) *
        Complex.exp (-(I * α * ((t - y : ℝ) : ℂ))))
      = f t * (starRingEnd ℂ) (f (t - y)) *
          (Complex.exp (I * α * t) * Complex.exp (-(I * α * ((t - y : ℝ) : ℂ)))) := by ring
    _ = _ := by rw [e]; ring

/-- The two modulations reproduce the cosine-twisted even part. -/
theorem weilTestEvenPart_twistModulate_add (α : ℝ) (f : ℝ → ℂ) (y : ℝ) :
    weilTestEvenPart (twistModulate α f) y + weilTestEvenPart (twistModulate (-α) f) y =
      2 * Real.cos (α * y) * weilTestEvenPart f y := by
  unfold weilTestEvenPart
  rw [weilTest_twistModulate, weilTest_twistModulate, weilTest_twistModulate, weilTest_twistModulate]
  have hc : ∀ u : ℝ, Complex.exp (I * α * u) + Complex.exp (I * ((-α : ℝ) : ℂ) * u) =
      ((2 * Real.cos (α * u) : ℝ) : ℂ) := by
    intro u
    rw [show I * ((-α : ℝ) : ℂ) * u = -(I * α * u) by push_cast; ring]
    rw [Complex.ofReal_mul, Complex.ofReal_cos, show ((α * u : ℝ) : ℂ) = α * u by push_cast; ring,
      Complex.cos, show I * (α : ℂ) * u = α * u * I by ring,
      show -((α : ℂ) * u * I) = -(α * u) * I by ring]
    push_cast; ring
  have key : Complex.exp (I * α * y) * EF.weilTest f f y +
      Complex.exp (I * α * ((-y : ℝ) : ℂ)) * EF.weilTest f f (-y) +
      (Complex.exp (I * ((-α : ℝ) : ℂ) * y) * EF.weilTest f f y +
        Complex.exp (I * ((-α : ℝ) : ℂ) * ((-y : ℝ) : ℂ)) * EF.weilTest f f (-y)) =
      ((2 * Real.cos (α * y) : ℝ) : ℂ) * (EF.weilTest f f y + EF.weilTest f f (-y)) := by
    have h1 := hc y
    have h2 := hc (-y)
    rw [show α * -y = -(α * y) by ring, Real.cos_neg] at h2
    calc _ = (Complex.exp (I * α * y) + Complex.exp (I * ((-α : ℝ) : ℂ) * y)) *
            EF.weilTest f f y + (Complex.exp (I * α * ((-y : ℝ) : ℂ)) +
              Complex.exp (I * ((-α : ℝ) : ℂ) * ((-y : ℝ) : ℂ))) * EF.weilTest f f (-y) := by ring
      _ = _ := by rw [h1, h2]; ring
  rw [← Complex.add_re, key, Complex.re_ofReal_mul]

/-! ### The twisted Weil energy -/

/-- The archimedean Weil symbol in the frequency variable: `A(τ) = Re ψ(1/4 + iτ/2) - log π`. -/
def archFreq (τ : ℝ) : ℝ := archimedeanWeilSymbol (τ / (2 * π))

theorem paperFT_twistModulate_ofReal (α : ℝ) (f : ℝ → ℂ) (τ : ℝ) :
    paperFT (twistModulate α f) (τ : ℂ) = paperFT f ((τ + α : ℝ) : ℂ) := by
  rw [paperFT_twistModulate]; push_cast; ring_nf

theorem integral_normSq_paperFT_twist_mul_arch (α : ℝ) (f : ℝ → ℂ) :
    ∫ τ : ℝ, ‖paperFT (twistModulate α f) τ‖ ^ 2 * archFreq τ =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archFreq (τ - α) := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * archFreq (τ - α)) α
  simp only [add_sub_cancel_right] at h
  rw [← h]
  congr 1; funext τ
  rw [paperFT_twistModulate_ofReal]

/-- **Exact energy of the twisted weights.**  Let `f`, `f e^{iαx}` and `f e^{-iαx}` be
polar-constrained `C²` tests supported in `[-a, a]`.  For the weights `Λ(n)(1 + t cos(α log n))`,
`∫ |h_f|² S = 2π Re W(f) + πt (Re W(f₊) + Re W(f₋)) - (t/2) ∫ |h_f(τ)|² (A(τ-α) + A(τ+α)) dτ`. -/
theorem integral_weilAtomSymbol_twist {a α : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) (hpP : paperFT f (I / 2 + α) = 0)
    (hmP : paperFT f (-(I / 2) + α) = 0) (hpM : paperFT f (I / 2 + ((-α : ℝ) : ℂ)) = 0)
    (hmM : paperFT f (-(I / 2) + ((-α : ℝ) : ℂ)) = 0) (t : ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 + t * Real.cos (α * Real.log n)))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (zetaZeroConfig.W f f).re +
        π * t * ((zetaZeroConfig.W (twistModulate α f) (twistModulate α f)).re +
          (zetaZeroConfig.W (twistModulate (-α) f) (twistModulate (-α) f)).re) -
        t / 2 * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (archFreq (τ - α) + archFreq (τ + α)) := by
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  -- the two modulated tests
  have hdP := contDiff_twistModulate (α := α) hf
  have hdM := contDiff_twistModulate (α := -α) hf
  have hsP := (tsupport_twistModulate_subset α f).trans hfs
  have hsM := (tsupport_twistModulate_subset (-α) f).trans hfs
  have hWP := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hdP hsP
    (by rw [paperFT_twistModulate]; exact hpP) (by rw [paperFT_twistModulate]; exact hmP)
  have hWM := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hdM hsM
    (by rw [paperFT_twistModulate]; exact hpM) (by rw [paperFT_twistModulate]; exact hmM)
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  have hre : ∀ {g : ℝ → ℂ} {x : ℝ}, zetaZeroConfig.W g g = ((1 / (2 * π) * x : ℝ) : ℂ) →
      x = 2 * π * (zetaZeroConfig.W g g).re := by
    intro g x h; rw [h, Complex.ofReal_re]; field_simp
  have eW := hre hW
  have eWP := hre hWP
  have eWM := hre hWM
  -- arch-sum forms
  have aP := integral_weilAtomSymbol_eq_arch_sub hdP hsP (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  have aM := integral_weilAtomSymbol_eq_arch_sub hdM hsM (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  rw [eWP] at aP
  rw [eWM] at aM
  -- the perturbation sum
  have hsub := integral_weilAtomSymbol_eq_sub hf hfs
    (fun n => ArithmeticFunction.vonMangoldt n * (1 + t * Real.cos (α * Real.log n)))
  rw [eW] at hsub
  rw [hsub]
  have hsum : ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n *
      (1 + t * Real.cos (α * Real.log n)) - ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      t / 2 * ((∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        (EF.weilTest (twistModulate α f) (twistModulate α f) (Real.log n) +
          EF.weilTest (twistModulate α f) (twistModulate α f) (-Real.log n)).re) +
        ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        (EF.weilTest (twistModulate (-α) f) (twistModulate (-α) f) (Real.log n) +
          EF.weilTest (twistModulate (-α) f) (twistModulate (-α) f) (-Real.log n)).re) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := weilTestEvenPart_twistModulate_add α f (Real.log n)
    unfold weilTestEvenPart at h
    rw [show (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        (EF.weilTest (twistModulate α f) (twistModulate α f) (Real.log n) +
          EF.weilTest (twistModulate α f) (twistModulate α f) (-Real.log n)).re +
        (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        (EF.weilTest (twistModulate (-α) f) (twistModulate (-α) f) (Real.log n) +
          EF.weilTest (twistModulate (-α) f) (twistModulate (-α) f) (-Real.log n)).re =
        (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          (2 * Real.cos (α * Real.log n) * (EF.weilTest f f (Real.log n) +
            EF.weilTest f f (-Real.log n)).re) by rw [← h]; ring]
    ring
  rw [hsum]
  -- express the modulated arch integrals through translates
  have hAP : ∫ τ : ℝ, ‖paperFT (twistModulate α f) τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archFreq (τ - α) :=
    integral_normSq_paperFT_twist_mul_arch α f
  have hAM : ∫ τ : ℝ, ‖paperFT (twistModulate (-α) f) τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archFreq (τ + α) := by
    rw [show (fun τ : ℝ => ‖paperFT (twistModulate (-α) f) τ‖ ^ 2 *
        archimedeanWeilSymbol (τ / (2 * π))) = fun τ : ℝ =>
        ‖paperFT (twistModulate (-α) f) τ‖ ^ 2 * archFreq τ from rfl,
      integral_normSq_paperFT_twist_mul_arch (-α) f]
    simp only [sub_neg_eq_add]
  rw [hAP] at aP
  rw [hAM] at aM
  have hintP : Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * archFreq (τ - α)) := by
    have h := (integrable_normSq_paperFT_mul_arch hdP hsP).comp_add_right (-α)
    refine h.congr (Eventually.of_forall fun τ => ?_)
    show ‖paperFT (twistModulate α f) ((τ + -α : ℝ) : ℂ)‖ ^ 2 *
        archimedeanWeilSymbol ((τ + -α) / (2 * π)) = ‖paperFT f τ‖ ^ 2 * archFreq (τ - α)
    rw [paperFT_twistModulate_ofReal, show τ + -α + α = τ by ring, archFreq, sub_eq_add_neg]
  have hintM : Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * archFreq (τ + α)) := by
    have h := (integrable_normSq_paperFT_mul_arch hdM hsM).comp_add_right α
    refine h.congr (Eventually.of_forall fun τ => ?_)
    show ‖paperFT (twistModulate (-α) f) ((τ + α : ℝ) : ℂ)‖ ^ 2 *
        archimedeanWeilSymbol ((τ + α) / (2 * π)) = ‖paperFT f τ‖ ^ 2 * archFreq (τ + α)
    rw [paperFT_twistModulate_ofReal, show τ + α + -α = τ by ring, archFreq]
  have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (archFreq (τ - α) + archFreq (τ + α)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archFreq (τ - α)) +
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archFreq (τ + α) := by
    rw [← integral_add hintP hintM]; congr 1; funext τ; ring
  rw [hsplit]
  linear_combination (-t / 2) * aP + (-t / 2) * aM

/-! ### Generic convolution facts -/

theorem convolution_mul_eq_zero_of_abs_gt {f g : ℝ → ℂ} {a b x : ℝ}
    (hf : ∀ u, a < |u| → f u = 0) (hg : ∀ u, b < |u| → g u = 0) (hx : a + b < |x|) :
    convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume x = 0 := by
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (f t) (g (x - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : a < |t|
    · rw [hf t ht, zero_mul]
    · push Not at ht
      have : b < |x - t| := by have := abs_sub_abs_le_abs_sub x t; linarith
      rw [hg _ this, mul_zero]
  simp [this]

theorem integrable_mul_cexp_of_continuous {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun x : ℝ => f x * Complex.exp (I * z * x)) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right

theorem paperFT_comp_div {f : ℝ → ℂ} {S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (fun x => f (x / S)) z = S * paperFT f (S * z) := by
  unfold paperFT
  have h := Measure.integral_comp_mul_left (fun y : ℝ => f y * Complex.exp (I * (S * z) * y)) S⁻¹
  rw [inv_inv, abs_of_pos hS, Complex.real_smul] at h
  rw [← h]
  congr 1; funext x
  show f (x / S) * Complex.exp (I * z * x) = f (S⁻¹ * x) * Complex.exp (I * (S * z) * ((S⁻¹ * x : ℝ) : ℂ))
  rw [div_eq_inv_mul]
  congr 2
  have hS0 : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  push_cast
  field_simp

/-! ### The triple radical test -/

theorem continuous_weilRadicalTest (R : ℝ) : Continuous (weilRadicalTest R) :=
  (contDiff_weilRadicalTest R).continuous

theorem weilRadicalTest_eq_zero' {R u : ℝ} (hu : R < |u|) : weilRadicalTest R u = 0 :=
  weilRadicalTest_eq_zero hu

/-- `T_R = B_R ⋆ B_R e^{iα·} ⋆ B_R e^{-iα·}`: its transform `B̂(z) B̂(z+α) B̂(z-α)` vanishes
approximately at the zeros of `ζ(s)`, `ζ(s + iα)` and `ζ(s - iα)` and at their poles. -/
def twistRadical (α R : ℝ) : ℝ → ℂ :=
  convolution (convolution (weilRadicalTest R) (twistModulate α (weilRadicalTest R))
    (ContinuousLinearMap.mul ℝ ℂ) volume) (twistModulate (-α) (weilRadicalTest R))
    (ContinuousLinearMap.mul ℝ ℂ) volume

theorem twistModulate_weilRadicalTest_eq_zero {α R u : ℝ} (hu : R < |u|) :
    twistModulate α (weilRadicalTest R) u = 0 :=
  twistModulate_eq_zero (weilRadicalTest_eq_zero hu)

theorem continuous_twistModulate {α : ℝ} {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (twistModulate α f) := hf.mul (by fun_prop)

theorem twistRadical_inner_eq_zero {α R u : ℝ} (hu : R + R < |u|) :
    convolution (weilRadicalTest R) (twistModulate α (weilRadicalTest R))
      (ContinuousLinearMap.mul ℝ ℂ) volume u = 0 :=
  convolution_mul_eq_zero_of_abs_gt (fun _ h => weilRadicalTest_eq_zero h)
    (fun _ h => twistModulate_weilRadicalTest_eq_zero h) hu

theorem twistRadical_eq_zero {α R x : ℝ} (hx : 3 * R < |x|) : twistRadical α R x = 0 :=
  convolution_mul_eq_zero_of_abs_gt (a := R + R) (b := R)
    (fun _ h => twistRadical_inner_eq_zero h)
    (fun _ h => twistModulate_weilRadicalTest_eq_zero h) (by linarith)

theorem hasCompactSupport_of_abs_gt {f : ℝ → ℂ} {a : ℝ} (hf : ∀ u, a < |u| → f u = 0) :
    HasCompactSupport f :=
  hasCompactSupport_of_support_subset_abs (Λ := a) fun u hu => by
    by_contra h; push Not at h; exact hu (hf u h)

theorem contDiff_twistRadical (α R : ℝ) : ContDiff ℝ 2 (twistRadical α R) := by
  have h1 : ContDiff ℝ 2 (convolution (weilRadicalTest R) (twistModulate α (weilRadicalTest R))
      (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    (hasCompactSupport_weilRadicalTest R).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
      (n := 2) (contDiff_weilRadicalTest R)
      (continuous_twistModulate (continuous_weilRadicalTest R)).locallyIntegrable
  exact (hasCompactSupport_of_abs_gt (a := R + R) fun _ h => twistRadical_inner_eq_zero h)
    |>.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) (n := 2) h1
      (continuous_twistModulate (continuous_weilRadicalTest R)).locallyIntegrable

theorem paperFT_twistRadical (α R : ℝ) (z : ℂ) :
    paperFT (twistRadical α R) z = paperFT (weilRadicalTest R) z *
      paperFT (weilRadicalTest R) (z + α) * paperFT (weilRadicalTest R) (z + ((-α : ℝ) : ℂ)) := by
  have hcB := continuous_weilRadicalTest R
  have hsB := hasCompactSupport_weilRadicalTest R
  have hcP : Continuous (twistModulate α (weilRadicalTest R)) := continuous_twistModulate hcB
  have hsP : HasCompactSupport (twistModulate α (weilRadicalTest R)) :=
    hasCompactSupport_of_abs_gt (a := R) fun _ h => twistModulate_weilRadicalTest_eq_zero h
  have hcM : Continuous (twistModulate (-α) (weilRadicalTest R)) := continuous_twistModulate hcB
  have hsM : HasCompactSupport (twistModulate (-α) (weilRadicalTest R)) :=
    hasCompactSupport_of_abs_gt (a := R) fun _ h => twistModulate_weilRadicalTest_eq_zero h
  have hinner := paperFT_convolution (integrable_mul_cexp_of_continuous hcB hsB z)
    (integrable_mul_cexp_of_continuous hcP hsP z)
  have hcI : Continuous (convolution (weilRadicalTest R) (twistModulate α (weilRadicalTest R))
      (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    ((hsB.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) (n := 2)
      (contDiff_weilRadicalTest R) hcP.locallyIntegrable)).continuous
  have hsI := hasCompactSupport_of_abs_gt (a := R + R) fun _ h =>
    twistRadical_inner_eq_zero (α := α) h
  unfold twistRadical
  rw [paperFT_convolution (integrable_mul_cexp_of_continuous hcI hsI z)
    (integrable_mul_cexp_of_continuous hcM hsM z), hinner, paperFT_twistModulate,
    paperFT_twistModulate]

/-- The probe `q = κ ⋆ κ`, whose transform `κ̂²` decays like `(1+|v|)^{-4}`. -/
def twistBump : ℝ → ℂ := convolution weilBumpC weilBumpC (ContinuousLinearMap.mul ℝ ℂ) volume

theorem twistBump_eq_zero {x : ℝ} (hx : 1 / 2 < |x|) : twistBump x = 0 :=
  convolution_mul_eq_zero_of_abs_gt (a := 1 / 4) (b := 1 / 4)
    (fun _ h => weilBumpC_eq_zero h.le) (fun _ h => weilBumpC_eq_zero h.le) (by linarith)

theorem continuous_twistBump : Continuous twistBump :=
  (hasCompactSupport_weilBumpC.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) (n := 2)
    (contDiff_weilBumpC.of_le (by norm_num)) contDiff_weilBumpC.continuous.locallyIntegrable).continuous

theorem hasCompactSupport_twistBump : HasCompactSupport twistBump :=
  hasCompactSupport_of_abs_gt (a := 1 / 2) fun _ h => twistBump_eq_zero h

theorem paperFT_twistBump (z : ℂ) : paperFT twistBump z = paperFT weilBumpC z ^ 2 := by
  unfold twistBump
  rw [paperFT_convolution (integrable_mul_cexp_of_continuous contDiff_weilBumpC.continuous
    hasCompactSupport_weilBumpC z) (integrable_mul_cexp_of_continuous contDiff_weilBumpC.continuous
    hasCompactSupport_weilBumpC z), sq]

/-- The spread probe `q(x/S) e^{-iτ₀x}`, with transform `S κ̂(S(z - τ₀))²`. -/
def twistProbe (τ₀ S : ℝ) : ℝ → ℂ := twistModulate (-τ₀) (fun x => twistBump (x / S))

theorem twistProbe_eq_zero {τ₀ S x : ℝ} (hS : 0 < S) (hx : S < |x|) : twistProbe τ₀ S x = 0 := by
  apply twistModulate_eq_zero
  apply twistBump_eq_zero
  rw [abs_div, abs_of_pos hS, lt_div_iff₀ hS]; linarith

theorem continuous_twistProbe (τ₀ S : ℝ) : Continuous (twistProbe τ₀ S) :=
  continuous_twistModulate (continuous_twistBump.comp (continuous_id.div_const S))

theorem paperFT_twistProbe {τ₀ S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (twistProbe τ₀ S) z = S * paperFT weilBumpC (S * (z + ((-τ₀ : ℝ) : ℂ))) ^ 2 := by
  unfold twistProbe
  rw [paperFT_twistModulate, paperFT_comp_div hS, paperFT_twistBump]

/-- The test `T_R ⋆ (q(x/S) e^{-iτ₀x})`. -/
def twistTest (α τ₀ R S : ℝ) : ℝ → ℂ :=
  convolution (twistRadical α R) (twistProbe τ₀ S) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem twistTest_eq_zero {α τ₀ R S x : ℝ} (hS : 0 < S) (hx : 3 * R + S < |x|) :
    twistTest α τ₀ R S x = 0 :=
  convolution_mul_eq_zero_of_abs_gt (fun _ h => twistRadical_eq_zero h)
    (fun _ h => twistProbe_eq_zero hS h) hx

theorem tsupport_twistTest {α τ₀ R S : ℝ} (hS : 0 < S) :
    tsupport (twistTest α τ₀ R S) ⊆ Icc (-(3 * R + S)) (3 * R + S) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ 3 * R + S < |x| := fun h => hx (twistTest_eq_zero hS h)
  push Not at h
  exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

theorem contDiff_twistTest (α τ₀ R S : ℝ) : ContDiff ℝ 2 (twistTest α τ₀ R S) :=
  (hasCompactSupport_of_abs_gt (a := 3 * R) fun _ h => twistRadical_eq_zero h)
    |>.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) (n := 2) (contDiff_twistRadical α R)
      (continuous_twistProbe τ₀ S).locallyIntegrable

theorem paperFT_twistTest {α τ₀ R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (twistTest α τ₀ R S) z = paperFT (twistRadical α R) z * paperFT (twistProbe τ₀ S) z :=
  paperFT_convolution
    (integrable_mul_cexp_of_continuous (contDiff_twistRadical α R).continuous
      (hasCompactSupport_of_abs_gt (a := 3 * R) fun _ h => twistRadical_eq_zero h) z)
    (integrable_mul_cexp_of_continuous (continuous_twistProbe τ₀ S)
      (hasCompactSupport_of_abs_gt (a := S) fun _ h => twistProbe_eq_zero hS h) z)

/-! ### Zero sides of the twisted tests -/

theorem norm_paperFT_weilRadicalTest_le_strip (R : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (weilRadicalTest R) z‖ ≤
      (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
        (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) := by
  rw [paperFT_weilRadicalTest, norm_mul]
  exact mul_le_mul (norm_paperFT_riemannPhiCore_le R hz)
    (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _)
    (integral_nonneg fun _ => by positivity)

theorem integral_norm_twistProbe {τ₀ S : ℝ} (hS : 0 < S) :
    ∫ x : ℝ, ‖twistProbe τ₀ S x‖ = S * ∫ x : ℝ, ‖twistBump x‖ := by
  have : (fun x : ℝ => ‖twistProbe τ₀ S x‖) = fun x => ‖twistBump (x / S)‖ := by
    funext x
    simp only [twistProbe, twistModulate, norm_mul, Complex.norm_exp]
    have : (I * ((-τ₀ : ℝ) : ℂ) * (x : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one]
  rw [this, Measure.integral_comp_div (fun y => ‖twistBump y‖) S, abs_of_pos hS, smul_eq_mul]

theorem norm_paperFT_twistProbe_le {τ₀ S : ℝ} (hS : 0 < S) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (twistProbe τ₀ S) z‖ ≤ Real.exp (S / 2) * (S * ∫ x : ℝ, ‖twistBump x‖) := by
  have hi : Integrable (twistProbe τ₀ S) :=
    (continuous_twistProbe τ₀ S).integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (a := S) fun _ h => twistProbe_eq_zero hS h)
  have h := norm_paperFT_le (Λ := S) hi (fun u hu => by
    by_contra h; push Not at h; exact hu (twistProbe_eq_zero hS h)) z
  rw [integral_norm_twistProbe hS] at h
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    (mul_nonneg hS.le (integral_nonneg fun _ => norm_nonneg _)))
  nlinarith [abs_nonneg z.im]

/-- A zero-side bound for any test whose transform carries the radical factor `B̂_R`. -/
theorem norm_W_of_radical_factor_le {K₀ : ℝ}
    (hK : ∀ L : ℝ, 0 ≤ L →
      4 * ((∫ u : ℝ, ‖weilRadicalTest L u‖) + ∫ u : ℝ, ‖deriv (deriv (weilRadicalTest L)) u‖)
        ≤ L * K₀)
    {R : ℝ} (hR : 0 ≤ R) {g : ℝ → ℂ} {Y : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀)
    (hg : ∀ z, paperFT g z = paperFT (weilRadicalTest R) z * Y z)
    (hY : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Y z‖ ≤ M) :
    ‖zetaZeroConfig.W g g‖ ≤ (5 / 4) * (∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) *
      (((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) *
        (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) * M) *
        (Real.exp (R / 2) * (R * K₀) * M)) := by
  have hε0 : 0 ≤ ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) :=
    integral_nonneg fun _ => by positivity
  have hA0 : 0 ≤ Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  refine norm_zeroConfig_W_le_of_pointwise zetaZeroConfig summable_zetaZeroConfig
    (by positivity) (by positivity) (fun ρ => ?_) (fun ρ => ?_)
  · have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    obtain ⟨hc1, -⟩ := paperFT_riemannPhiCore_at_zero hmem R
    rw [hg, norm_mul, paperFT_weilRadicalTest, hc1, norm_mul, norm_neg]
    exact mul_le_mul (mul_le_mul (norm_paperFT_riemannPhiTail_le (by norm_num) hIm)
      (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hε0) (hY _ hIm)
      (norm_nonneg _) (mul_nonneg hε0 hA0)
  · have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact (WeilEF.abs_gammaOf_im_lt hstrip').le
    rw [hg, norm_mul]
    have hv2 : ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
      have h := norm_paperFT_le_decay (contDiff_weilRadicalTest R)
        (fun u hu => by
          by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
        ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))
      have hre : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
        rw [Complex.conj_re, WeilEF.gammaOf_re]
      rw [hre] at h
      refine h.trans ?_
      have he : Real.exp (|((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * R) ≤ Real.exp (R / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hden : 0 < (1 + |(ρ : ℂ).im|) ^ 2 := by positivity
      rw [div_eq_mul_one_div, mul_assoc]
      rw [show Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) =
        Real.exp (R / 2) * (R * K₀ * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) by ring]
      exact mul_le_mul he (mul_le_mul_of_nonneg_right (hK R hR) (by positivity))
        (by positivity) (Real.exp_pos _).le
    calc ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖Y ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * M :=
          mul_le_mul hv2 (hY _ hIm') (norm_nonneg _) (by positivity)
      _ = Real.exp (R / 2) * (R * K₀) * M * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

theorem paperFT_twistTest_factor {α τ₀ R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (twistTest α τ₀ R S) z = paperFT (weilRadicalTest R) z *
      (paperFT (weilRadicalTest R) (z + α) * paperFT (weilRadicalTest R) (z + ((-α : ℝ) : ℂ)) *
        paperFT (twistProbe τ₀ S) z) := by
  rw [paperFT_twistTest hS, paperFT_twistRadical]; ring

theorem paperFT_twistTest_plus_factor {α τ₀ R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (twistModulate α (twistTest α τ₀ R S)) z = paperFT (weilRadicalTest R) z *
      (paperFT (weilRadicalTest R) (z + α) * paperFT (weilRadicalTest R) (z + α + α) *
        paperFT (twistProbe τ₀ S) (z + α)) := by
  rw [paperFT_twistModulate, paperFT_twistTest hS, paperFT_twistRadical]
  rw [show z + (α : ℂ) + ((-α : ℝ) : ℂ) = z by push_cast; ring]; ring

theorem paperFT_twistTest_minus_factor {α τ₀ R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (twistModulate (-α) (twistTest α τ₀ R S)) z = paperFT (weilRadicalTest R) z *
      (paperFT (weilRadicalTest R) (z + ((-α : ℝ) : ℂ)) *
        paperFT (weilRadicalTest R) (z + ((-α : ℝ) : ℂ) + ((-α : ℝ) : ℂ)) *
        paperFT (twistProbe τ₀ S) (z + ((-α : ℝ) : ℂ))) := by
  rw [paperFT_twistModulate, paperFT_twistTest hS, paperFT_twistRadical]
  rw [show z + ((-α : ℝ) : ℂ) + (α : ℂ) = z by push_cast; ring]; ring

theorem im_add_ofReal (z : ℂ) (c : ℝ) : (z + (c : ℂ)).im = z.im := by simp

/-- The companion factor `Y` is bounded on the strip by `(B_Φ A)² e^{S/2} S ‖q‖₁`. -/
theorem norm_twist_companion_le {R S τ₀ : ℝ} (hS : 0 < S) {c₁ c₂ c₃ : ℝ} {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (weilRadicalTest R) (z + (c₁ : ℂ)) * paperFT (weilRadicalTest R) (z + (c₂ : ℂ)) *
        paperFT (twistProbe τ₀ S) (z + (c₃ : ℂ))‖ ≤
      ((∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
        (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖)) ^ 2 *
        (Real.exp (S / 2) * (S * ∫ x : ℝ, ‖twistBump x‖)) := by
  have hB := fun c : ℝ => norm_paperFT_weilRadicalTest_le_strip R
    (z := z + (c : ℂ)) (by rw [im_add_ofReal]; exact hz)
  have hp := norm_paperFT_twistProbe_le (τ₀ := τ₀) hS (z := z + (c₃ : ℂ))
    (by rw [im_add_ofReal]; exact hz)
  have hB0 : 0 ≤ (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
      (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) :=
    mul_nonneg (integral_nonneg fun _ => by positivity)
      (mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _))
  rw [norm_mul, norm_mul, sq]
  exact mul_le_mul (mul_le_mul (hB c₁) (hB c₂) (norm_nonneg _) hB0) hp (norm_nonneg _)
    (mul_nonneg hB0 hB0)

private theorem exp_half_le_two' : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- At truncation level `R = log S`, a radical-factor zero side with companion bound
`C e^{S/2} S` is `O(S^{10} e^{-S})`. -/
theorem exists_radical_factor_log_bound (C : ℝ) (hC : 0 ≤ C) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ S : ℝ, Real.exp 1 ≤ S → ∀ {g : ℝ → ℂ} {Y : ℂ → ℂ},
      (∀ z, paperFT g z = paperFT (weilRadicalTest (Real.log S)) z * Y z) →
      (∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Y z‖ ≤ C * (Real.exp (S / 2) * S)) →
      ‖zetaZeroConfig.W g g‖ ≤ K * S ^ 10 * Real.exp (-S) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  set SZ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hSZ
  have hSZ0 : 0 ≤ SZ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  set Aκ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hAκ
  have hAκ0 : 0 ≤ Aκ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  refine ⟨5 / 4 * SZ * Aκ * E₀ * K₀ * C ^ 2, by positivity, fun S hS g Y hg hY => ?_⟩
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos 1) hS
  set R := Real.log S with hR
  have hR1 : 1 ≤ R := by rw [hR, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hS
  have hR0 : 0 ≤ R := by linarith
  have hexpR : Real.exp R = S := Real.exp_log hS0
  have hS2 : 2 ≤ S := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hS
  have hM0 : 0 ≤ C * (Real.exp (S / 2) * S) := by positivity
  have h := norm_W_of_radical_factor_le hK hR0 hM0 hK₀ hg hY
  rw [← hSZ, ← hAκ] at h
  have hε := integral_norm_riemannPhiTail_mul_exp_le (L := R) (b := 1 / 2) hR1 (by norm_num)
  rw [← hE₀] at hε
  have he6 : Real.exp (6 * (R - 1 / 4)) ≤ S ^ 6 := by
    rw [← hexpR, ← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have he2 : S ^ 2 / 2 ≤ Real.exp (2 * (R - 1 / 4)) := by
    have : Real.exp (2 * (R - 1 / 4)) = S ^ 2 / Real.exp (1 / 2) := by
      rw [show 2 * (R - 1 / 4) = 2 * R - 1 / 2 by ring, Real.exp_sub, ← hexpR,
        ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) exp_half_le_two'
  have hεS : ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) ≤
      E₀ * S ^ 6 * Real.exp (-(π * (S ^ 2 / 2))) := by
    refine hε.trans ?_
    have hexp : Real.exp (-π * Real.exp (2 * (R - 1 / 4))) ≤ Real.exp (-(π * (S ^ 2 / 2))) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    gcongr
  have hD : Real.exp (R / 2) * (R * K₀) ≤ S * (S * K₀) := by
    have : Real.exp (R / 2) ≤ S := by rw [← hexpR]; exact Real.exp_le_exp.mpr (by linarith)
    have hRS : R ≤ S := Real.log_le_self hS0.le
    gcongr
  have hdecay : Real.exp S * Real.exp (-(π * (S ^ 2 / 2))) ≤ Real.exp (-S) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three]
  have hε0 : 0 ≤ ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) :=
    integral_nonneg fun _ => by positivity
  have hsq : (C * (Real.exp (S / 2) * S)) * (C * (Real.exp (S / 2) * S)) =
      C ^ 2 * S ^ 2 * Real.exp S := by
    rw [show Real.exp S = Real.exp (S / 2) * Real.exp (S / 2) by
      rw [← Real.exp_add]; congr 1; ring]; ring
  calc ‖zetaZeroConfig.W g g‖
      ≤ 5 / 4 * SZ * ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ *
          (C * (Real.exp (S / 2) * S)) * (Real.exp (R / 2) * (R * K₀) *
            (C * (Real.exp (S / 2) * S)))) := h
    _ = 5 / 4 * SZ * Aκ * (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) *
          (Real.exp (R / 2) * (R * K₀)) * ((C * (Real.exp (S / 2) * S)) *
            (C * (Real.exp (S / 2) * S))) := by ring
    _ ≤ 5 / 4 * SZ * Aκ * (E₀ * S ^ 6 * Real.exp (-(π * (S ^ 2 / 2)))) * (S * (S * K₀)) *
          (C ^ 2 * S ^ 2 * Real.exp S) := by
        rw [hsq]; gcongr
    _ = 5 / 4 * SZ * Aκ * E₀ * K₀ * C ^ 2 * S ^ 10 *
          (Real.exp S * Real.exp (-(π * (S ^ 2 / 2)))) := by ring
    _ ≤ 5 / 4 * SZ * Aκ * E₀ * K₀ * C ^ 2 * S ^ 10 * Real.exp (-S) := by gcongr

/-- **Zero sides of the three twisted tests at `R = log S`.** -/
theorem exists_norm_W_twistTest_log_le (α τ₀ : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ S : ℝ, Real.exp 1 ≤ S →
    ‖zetaZeroConfig.W (twistTest α τ₀ (Real.log S) S) (twistTest α τ₀ (Real.log S) S)‖ ≤
        K * S ^ 10 * Real.exp (-S) ∧
    ‖zetaZeroConfig.W (twistModulate α (twistTest α τ₀ (Real.log S) S))
        (twistModulate α (twistTest α τ₀ (Real.log S) S))‖ ≤ K * S ^ 10 * Real.exp (-S) ∧
    ‖zetaZeroConfig.W (twistModulate (-α) (twistTest α τ₀ (Real.log S) S))
        (twistModulate (-α) (twistTest α τ₀ (Real.log S) S))‖ ≤ K * S ^ 10 * Real.exp (-S) := by
  set C := ((∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
    (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖)) ^ 2 * ∫ x : ℝ, ‖twistBump x‖ with hC
  have hC0 : 0 ≤ C := mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨K, hK0, hK⟩ := exists_radical_factor_log_bound C hC0
  refine ⟨K, hK0, fun S hS => ?_⟩
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos 1) hS
  have hbound : ∀ {c₁ c₂ c₃ : ℝ} {z : ℂ}, |z.im| ≤ 1 / 2 →
      ‖paperFT (weilRadicalTest (Real.log S)) (z + (c₁ : ℂ)) *
        paperFT (weilRadicalTest (Real.log S)) (z + (c₂ : ℂ)) *
        paperFT (twistProbe τ₀ S) (z + (c₃ : ℂ))‖ ≤ C * (Real.exp (S / 2) * S) := by
    intro c₁ c₂ c₃ z hz
    refine (norm_twist_companion_le hS0 hz).trans (le_of_eq ?_)
    rw [hC]; ring
  refine ⟨hK S hS (fun z => paperFT_twistTest_factor hS0 z) fun z hz => ?_,
    hK S hS (fun z => paperFT_twistTest_plus_factor hS0 z) fun z hz => ?_,
    hK S hS (fun z => paperFT_twistTest_minus_factor hS0 z) fun z hz => ?_⟩
  · have := hbound (c₁ := α) (c₂ := -α) (c₃ := 0) hz
    simpa using this
  · have := hbound (c₁ := α) (c₂ := α + α) (c₃ := α) hz
    simpa [add_assoc] using this
  · have := hbound (c₁ := -α) (c₂ := -α + -α) (c₃ := -α) hz
    simpa [add_assoc] using this

/-! ### The limit transform on the real line -/

/-- `G(z) = Φ̂(z) κ̂₂(z)`: the transform of the untruncated radical test. -/
def radicalLimit (z : ℂ) : ℂ := paperFT Φ z * paperFT weilBumpPolarFree z

theorem differentiable_radicalLimit : Differentiable ℂ radicalLimit := by
  have h1 : Differentiable ℂ (paperFT Φ) := by
    intro z
    have : paperFT Φ = fun z => xi (1 / 2 + I * z) := by
      funext z; rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi]
    rw [this]
    exact (xi_differentiable _).comp z (by fun_prop)
  exact h1.mul superExpDecay_weilBumpPolarFree.differentiable_paperFT

theorem radicalLimit_ne_zero : radicalLimit (-(3 / 2 * I)) ≠ 0 := by
  unfold radicalLimit
  refine mul_ne_zero ?_ (norm_pos_iff.mp (lt_of_lt_of_le (by positivity)
    norm_paperFT_weilBumpPolarFree_three_halves_ge))
  rw [paperFT_riemannPhiKernel]
  have : (1 / 2 : ℂ) + I * -(3 / 2 * I) = 2 := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; exact riemannPhiTransform_two_ne_zero

/-- Near every real point, the shifted limit transform is nonzero at all nearby real points
except possibly the point itself. -/
theorem eventually_radicalLimit_shift_ne_zero (c τ₁ : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[≠] τ₁, radicalLimit ((t : ℂ) + (c : ℂ)) ≠ 0 := by
  have han : AnalyticOnNhd ℂ radicalLimit univ :=
    fun z _ => differentiable_radicalLimit.analyticAt z
  have hG : AnalyticAt ℂ (fun z => radicalLimit (z + c)) ((τ₁ : ℂ)) :=
    (han _ (mem_univ _)).comp_of_eq (analyticAt_id.add analyticAt_const) rfl
  rcases hG.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hall := (differentiable_radicalLimit.comp (differentiable_id.add_const (c : ℂ))
      |>.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ (τ₁ : ℂ)) h
    have := hall (mem_univ (-(3 / 2 * I) - c))
    simp only [Function.comp_apply, id, sub_add_cancel, Pi.zero_apply] at this
    exact radicalLimit_ne_zero this
  · have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] τ₁) (𝓝[≠] (τ₁ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto' τ₁ τ₁ rfl).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
    exact htend.eventually h

theorem norm_radicalLimit_real_le (τ : ℝ) :
    ‖radicalLimit τ‖ ≤ (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
      (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) := by
  unfold radicalLimit
  rw [norm_mul]
  refine mul_le_mul ?_ (norm_paperFT_weilBumpPolarFree_le
    (by simp only [Complex.ofReal_im, abs_zero]; norm_num)) (norm_nonneg _)
    (integral_nonneg fun _ => by positivity)
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _)
    (integrable_norm_riemannPhiKernel_mul_exp (by norm_num)) (Eventually.of_forall fun u => ?_))
  simp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp (b := 1 / 2) (by simp) u) (norm_nonneg _)

/-- The truncated radical transform is uniformly close to the limit on the real line. -/
theorem norm_paperFT_weilRadicalTest_sub_real_le (R τ : ℝ) :
    ‖paperFT (weilRadicalTest R) τ - radicalLimit τ‖ ≤
      (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) *
        (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) := by
  unfold radicalLimit
  rw [paperFT_weilRadicalTest, paperFT_riemannPhiCore_eq, ← paperFT_riemannPhiKernel,
    show (paperFT Φ τ - paperFT (riemannPhiTail R) τ) * paperFT weilBumpPolarFree τ -
      paperFT Φ τ * paperFT weilBumpPolarFree τ =
      -(paperFT (riemannPhiTail R) τ * paperFT weilBumpPolarFree τ) by ring, norm_neg, norm_mul]
  exact mul_le_mul (norm_paperFT_riemannPhiTail_le (by norm_num) (by simp))
    (norm_paperFT_weilBumpPolarFree_le (by simp only [Complex.ofReal_im, abs_zero]; norm_num))
    (norm_nonneg _) (integral_nonneg fun _ => by positivity)

/-- The limit of the triple radical transforms. -/
def twistLimit (α : ℝ) (z : ℂ) : ℂ :=
  radicalLimit z * radicalLimit (z + α) * radicalLimit (z + ((-α : ℝ) : ℂ))

theorem continuous_twistLimit_real (α : ℝ) : Continuous fun τ : ℝ => twistLimit α τ := by
  unfold twistLimit
  have hc := differentiable_radicalLimit.continuous
  fun_prop

/-- A difference-of-products bound: `|abc - a'b'c'| ≤ 3B²δ` when all factors are `≤ B` and
the differences are `≤ δ`. -/
theorem norm_mul3_sub_le {a b c a' b' c' : ℂ} {B δ : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B)
    (hc' : ‖c'‖ ≤ B) (hb' : ‖b'‖ ≤ B)
    (hda : ‖a - a'‖ ≤ δ) (hdb : ‖b - b'‖ ≤ δ) (hdc : ‖c - c'‖ ≤ δ) :
    ‖a * b * c - a' * b' * c'‖ ≤ 3 * B ^ 2 * δ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans ha
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hda
  have e : a * b * c - a' * b' * c' = a * b * (c - c') + a * (b - b') * c' + (a - a') * b' * c' := by
    ring
  rw [e]
  refine (norm_add₃_le).trans ?_
  simp only [norm_mul]
  have h1 : ‖a‖ * ‖b‖ * ‖c - c'‖ ≤ B * B * δ := by gcongr
  have h2 : ‖a‖ * ‖b - b'‖ * ‖c'‖ ≤ B * δ * B := by gcongr
  have h3 : ‖a - a'‖ * ‖b'‖ * ‖c'‖ ≤ δ * B * B := by gcongr
  nlinarith

/-! ### The archimedean symbol and the probe on the real line -/

theorem archFreq_eq (τ : ℝ) : archFreq τ = 2 * gammaHardyPhaseRate τ := by
  unfold archFreq archimedeanWeilSymbol
  congr 2; field_simp

theorem continuous_archFreq : Continuous archFreq := by
  have : archFreq = fun τ => 2 * gammaHardyPhaseRate τ := funext archFreq_eq
  rw [this]; exact continuous_const.mul continuous_gammaHardyPhaseRate

theorem abs_archFreq_le (τ : ℝ) :
    |archFreq τ| ≤ 70 + 2 * |gammaHardyPhaseRate 0| + 2 * |τ| := by
  rw [archFreq_eq]
  have h1 := WeilDeletion.gammaHardyPhaseRate_le_linear τ
  have h2 : gammaHardyPhaseRate 0 ≤ gammaHardyPhaseRate τ := by
    rcases eq_or_ne τ 0 with h | h
    · rw [h]
    · exact (gammaHardyPhaseRate_zero_lt h).le
  rw [abs_le]; constructor
  · nlinarith [neg_abs_le (gammaHardyPhaseRate 0), abs_nonneg τ]
  · nlinarith [abs_nonneg (gammaHardyPhaseRate 0), abs_nonneg τ]

theorem exists_norm_paperFT_weilBumpC_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
    ‖paperFT weilBumpC v‖ ≤ C / (1 + |v|) ^ 2 := by
  refine ⟨4 * ((∫ u, ‖weilBumpC u‖) + ∫ u, ‖deriv (deriv weilBumpC) u‖),
    by positivity, fun v => ?_⟩
  have h := norm_paperFT_le_decay (a := 1 / 4) (contDiff_weilBumpC.of_le (by norm_num))
    (fun u hu => by by_contra h; push Not at h; exact hu (weilBumpC_eq_zero h.le)) (v : ℂ)
  simpa using h

theorem norm_paperFT_weilBumpC_ge {v : ℝ} (hv : |v| ≤ 1) :
    Real.cos (1 / 4) / 4 ≤ ‖paperFT weilBumpC v‖ := by
  have hre : (paperFT weilBumpC v).re = ∫ x : ℝ, weilBump x * Real.cos (v * x) := by
    unfold paperFT weilBumpC
    have hi := integrable_mul_cexp_of_continuous contDiff_weilBumpC.continuous
      hasCompactSupport_weilBumpC v
    have h := integral_re hi
    simp only [RCLike.re_to_complex] at h
    unfold weilBumpC at h
    rw [← h]
    · congr 1; funext x
      rw [show I * (v : ℂ) * (x : ℂ) = ((v * x : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  have hint : Integrable (fun x : ℝ => weilBump x * Real.cos (v * x)) :=
    ((weilBump.contDiff (n := 0)).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      weilBump.hasCompactSupport.mul_right
  have hmono : ∫ x : ℝ, weilBump x * Real.cos (1 / 4) ≤ ∫ x : ℝ, weilBump x * Real.cos (v * x) := by
    refine integral_mono (((weilBump.contDiff (n := 0)).continuous.integrable_of_hasCompactSupport
      weilBump.hasCompactSupport).mul_const _) hint fun x => ?_
    by_cases hx : 1 / 4 ≤ |x|
    · have : weilBump x = 0 := by
        have h := weilBumpC_eq_zero hx
        simp only [weilBumpC, Complex.ofReal_eq_zero] at h
        exact h
      simp [this]
    · push Not at hx
      refine mul_le_mul_of_nonneg_left ?_ weilBump.nonneg
      have habs : |v * x| ≤ 1 / 4 := by
        rw [abs_mul]; nlinarith [abs_nonneg v, abs_nonneg x]
      rw [← Real.cos_abs (v * x)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three]) habs
  rw [integral_mul_const] at hmono
  have hge := integral_weilBump_ge
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  calc Real.cos (1 / 4) / 4 ≤ (∫ x : ℝ, weilBump x) * Real.cos (1 / 4) := by nlinarith
    _ ≤ (paperFT weilBumpC v).re := by rw [hre]; exact hmono
    _ ≤ ‖paperFT weilBumpC v‖ := Complex.re_le_norm _

theorem paperFT_twistProbe_real {τ₀ S : ℝ} (hS : 0 < S) (τ : ℝ) :
    paperFT (twistProbe τ₀ S) τ = S * paperFT weilBumpC ((S * (τ - τ₀) : ℝ) : ℂ) ^ 2 := by
  rw [paperFT_twistProbe hS]; push_cast; ring_nf

/-! ### Concentration of the twisted tests -/

theorem norm_paperFT_twistTest_real_le {α τ₀ R S Cκ : ℝ} (hS : 0 < S)
    (hCκ : ∀ v : ℝ, ‖paperFT weilBumpC v‖ ≤ Cκ / (1 + |v|) ^ 2) (τ : ℝ) :
    ‖paperFT (twistTest α τ₀ R S) τ‖ ≤
      ((∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
        (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖)) ^ 3 *
        (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2) := by
  set B := (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
    (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) with hB
  have hB0 : 0 ≤ B := mul_nonneg (integral_nonneg fun _ => by positivity)
    (mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _))
  have hstrip : ∀ c : ℝ, ‖paperFT (weilRadicalTest R) ((τ : ℂ) + c)‖ ≤ B := fun c =>
    norm_paperFT_weilRadicalTest_le_strip R (by simp)
  have hp : ‖paperFT (twistProbe τ₀ S) τ‖ ≤ S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2 := by
    rw [paperFT_twistProbe_real hS, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hS]
    have h := hCκ (S * (τ - τ₀))
    rw [abs_mul, abs_of_pos hS] at h
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) hS.le
  rw [paperFT_twistTest_factor hS, norm_mul, norm_mul, norm_mul]
  have h0 := hstrip 0
  simp only [Complex.ofReal_zero, add_zero] at h0
  calc ‖paperFT (weilRadicalTest R) τ‖ * (‖paperFT (weilRadicalTest R) ((τ : ℂ) + α)‖ *
        ‖paperFT (weilRadicalTest R) ((τ : ℂ) + ((-α : ℝ) : ℂ))‖ * ‖paperFT (twistProbe τ₀ S) τ‖)
      ≤ B * (B * B * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2)) := by
        gcongr
        · exact hstrip α
        · exact hstrip (-α)
    _ = B ^ 3 * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2) := by ring

theorem norm_paperFT_twistTest_real_ge {α τ₀ R S m : ℝ} (hS : 0 < S) {τ : ℝ}
    (hτ : |τ - τ₀| ≤ 1 / S) (hlim : m / 2 ≤ ‖twistLimit α τ‖)
    (happrox : 3 * ((∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
        (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖)) ^ 2 *
      ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) *
        (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖)) ≤ m / 4) :
    m / 4 * (S * (Real.cos (1 / 4) / 4) ^ 2) ≤ ‖paperFT (twistTest α τ₀ R S) τ‖ := by
  set B := (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) *
    (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) with hB
  set δ := (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) *
    (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) with hδ
  have hT : ‖paperFT (twistRadical α R) τ - twistLimit α τ‖ ≤ 3 * B ^ 2 * δ := by
    rw [paperFT_twistRadical]
    unfold twistLimit
    have hr : ∀ c : ℝ, ‖paperFT (weilRadicalTest R) ((τ : ℂ) + c) - radicalLimit ((τ : ℂ) + c)‖ ≤ δ :=
      fun c => by
        have := norm_paperFT_weilRadicalTest_sub_real_le R (τ + c)
        rw [Complex.ofReal_add] at this; exact this
    have hb : ∀ c : ℝ, ‖paperFT (weilRadicalTest R) ((τ : ℂ) + c)‖ ≤ B := fun c =>
      norm_paperFT_weilRadicalTest_le_strip R (by simp)
    have hl : ∀ c : ℝ, ‖radicalLimit ((τ : ℂ) + c)‖ ≤ B := fun c => by
      have := norm_radicalLimit_real_le (τ + c)
      rw [Complex.ofReal_add] at this; exact this
    have h0 := hr 0; have b0 := hb 0; have l0 := hl 0
    simp only [Complex.ofReal_zero, add_zero] at h0 b0 l0
    exact norm_mul3_sub_le b0 (hb α) (hl (-α)) (hl α) h0 (hr α) (hr (-α))
  have hTlow : m / 4 ≤ ‖paperFT (twistRadical α R) τ‖ := by
    have := norm_sub_norm_le (twistLimit α τ) (paperFT (twistRadical α R) τ)
    rw [norm_sub_rev] at this
    linarith
  have hv : |S * (τ - τ₀)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hS]
    calc S * |τ - τ₀| ≤ S * (1 / S) := mul_le_mul_of_nonneg_left hτ hS.le
      _ = 1 := by field_simp
  have hk := norm_paperFT_weilBumpC_ge hv
  rw [paperFT_twistTest hS, norm_mul, paperFT_twistProbe_real hS, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  exact mul_le_mul hTlow (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hk 2) hS.le)
    (by positivity) (norm_nonneg _)

theorem integrable_normSq_paperFT_mul_twistArch {a α : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (archFreq (τ - α) + archFreq (τ + α))) := by
  have hdP := contDiff_twistModulate (α := α) hf
  have hdM := contDiff_twistModulate (α := -α) hf
  have hsP := (tsupport_twistModulate_subset α f).trans hfs
  have hsM := (tsupport_twistModulate_subset (-α) f).trans hfs
  have hintP : Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * archFreq (τ - α)) := by
    have h := (integrable_normSq_paperFT_mul_arch hdP hsP).comp_add_right (-α)
    refine h.congr (Eventually.of_forall fun τ => ?_)
    show ‖paperFT (twistModulate α f) ((τ + -α : ℝ) : ℂ)‖ ^ 2 *
        archimedeanWeilSymbol ((τ + -α) / (2 * π)) = ‖paperFT f τ‖ ^ 2 * archFreq (τ - α)
    rw [paperFT_twistModulate_ofReal, show τ + -α + α = τ by ring, archFreq, sub_eq_add_neg]
  have hintM : Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * archFreq (τ + α)) := by
    have h := (integrable_normSq_paperFT_mul_arch hdM hsM).comp_add_right α
    refine h.congr (Eventually.of_forall fun τ => ?_)
    show ‖paperFT (twistModulate (-α) f) ((τ + α : ℝ) : ℂ)‖ ^ 2 *
        archimedeanWeilSymbol ((τ + α) / (2 * π)) = ‖paperFT f τ‖ ^ 2 * archFreq (τ + α)
    rw [paperFT_twistModulate_ofReal, show τ + α + -α = τ by ring, archFreq]
  refine (hintP.add hintM).congr (Eventually.of_forall fun τ => ?_)
  simp only [Pi.add_apply]; ring

theorem abs_twistArch_le (α τ₀ τ : ℝ) :
    |archFreq (τ - α) + archFreq (τ + α)| ≤
      (2 * (70 + 2 * |gammaHardyPhaseRate 0|) + 4 * |τ₀| + 4 * |α| + 4) * (1 + |τ - τ₀|) := by
  have h1 := abs_archFreq_le (τ - α)
  have h2 := abs_archFreq_le (τ + α)
  have hA : |τ - α| ≤ |τ - τ₀| + |τ₀| + |α| := by
    calc |τ - α| = |(τ - τ₀) + τ₀ - α| := by ring_nf
      _ ≤ |(τ - τ₀) + τ₀| + |α| := abs_sub _ _
      _ ≤ |τ - τ₀| + |τ₀| + |α| := by gcongr; exact abs_add_le _ _
  have hB : |τ + α| ≤ |τ - τ₀| + |τ₀| + |α| := by
    calc |τ + α| = |(τ - τ₀) + τ₀ + α| := by ring_nf
      _ ≤ |(τ - τ₀) + τ₀| + |α| := abs_add_le _ _
      _ ≤ |τ - τ₀| + |τ₀| + |α| := by gcongr; exact abs_add_le _ _
  have h0 : 0 ≤ |gammaHardyPhaseRate 0| := abs_nonneg _
  have hu : 0 ≤ |τ - τ₀| := abs_nonneg _
  calc |archFreq (τ - α) + archFreq (τ + α)| ≤ |archFreq (τ - α)| + |archFreq (τ + α)| :=
        abs_add_le _ _
    _ ≤ _ := by nlinarith [abs_nonneg τ₀, abs_nonneg α]

/-- Pointwise tail bound away from the concentration point. -/
theorem tail_pointwise_le {X K₁ Cκ CD S η u : ℝ} (hS : 1 ≤ S) (hη : 0 < η) (hu : η < |u|)
    (hCD : 0 ≤ CD) (hX0 : 0 ≤ X)
    (hX : X ≤ K₁ * (S * (Cκ / (1 + S * |u|) ^ 2) ^ 2)) :
    X ^ 2 * (CD * (1 + |u|)) ≤ K₁ ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4) / (1 + |u|) ^ 3 := by
  have hS0 : 0 < S := by linarith
  have hu0 : 0 < |u| := lt_trans hη hu
  have h1 : 1 + |u| ≤ 1 + S * |u| := by nlinarith
  have h2 : S * η ≤ 1 + S * |u| := by nlinarith
  have hpos : 0 < 1 + S * |u| := by positivity
  have hX2 : X ^ 2 ≤ K₁ ^ 2 * S ^ 2 * Cκ ^ 4 / (1 + S * |u|) ^ 8 := by
    have := pow_le_pow_left₀ hX0 hX 2
    refine this.trans (le_of_eq ?_)
    field_simp
  have hden : (1 + |u|) ^ 4 * (S * η) ^ 4 ≤ (1 + S * |u|) ^ 8 := by
    have e : (1 + S * |u|) ^ 8 = (1 + S * |u|) ^ 4 * (1 + S * |u|) ^ 4 := by ring
    rw [e]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 4) (pow_le_pow_left₀ (by positivity) h2 4)
      (by positivity) (by positivity)
  calc X ^ 2 * (CD * (1 + |u|)) ≤ K₁ ^ 2 * S ^ 2 * Cκ ^ 4 / (1 + S * |u|) ^ 8 * (CD * (1 + |u|)) :=
        mul_le_mul_of_nonneg_right hX2 (by positivity)
    _ ≤ K₁ ^ 2 * S ^ 2 * Cκ ^ 4 / ((1 + |u|) ^ 4 * (S * η) ^ 4) * (CD * (1 + |u|)) := by
        gcongr
    _ = K₁ ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4) / (1 + |u|) ^ 3 := by
        field_simp

theorem integrable_inv_one_add_abs_sub_cube (τ₀ : ℝ) :
    Integrable (fun τ : ℝ => 1 / (1 + |τ - τ₀|) ^ 3) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by simp)
  have h' := h.comp_sub_right τ₀
  refine h'.congr (Eventually.of_forall fun τ => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), one_div]
  norm_cast

/-- **Concentration inequality.**  If `tD ≥ d₁/2` near `τ₀`, `|H| ≥ L` on the `1/S`-window, and
`|H|` has the spread-probe profile, then `t ∫ |H|² D ≥ (d₁/2)(2L²/S) - (tail)`. -/
theorem concentrated_integral_lower {H : ℝ → ℂ} {D : ℝ → ℝ} {t τ₀ η S d₁ L K₁ Cκ CD : ℝ}
    (hS : 1 ≤ S) (hη : 0 < η) (hSη : 1 / S ≤ η) (hd₁ : 0 < d₁) (hL : 0 ≤ L) (hCD : 0 ≤ CD)
    (hK₁ : 0 ≤ K₁) (hCκ : 0 ≤ Cκ)
    (hHm : AEStronglyMeasurable H volume) (hint : Integrable (fun τ => ‖H τ‖ ^ 2 * D τ))
    (hnear : ∀ τ, |τ - τ₀| ≤ η → d₁ / 2 ≤ t * D τ)
    (hlow : ∀ τ, |τ - τ₀| ≤ 1 / S → L ≤ ‖H τ‖)
    (hup : ∀ τ, ‖H τ‖ ≤ K₁ * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2))
    (hD : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|)) :
    d₁ / 2 * (2 / S * L ^ 2) - |t| * (K₁ ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) *
        ∫ τ : ℝ, 1 / (1 + |τ - τ₀|) ^ 3 ≤ t * ∫ τ : ℝ, ‖H τ‖ ^ 2 * D τ := by
  have hS0 : 0 < S := by linarith
  set N := Icc (τ₀ - η) (τ₀ + η) with hN
  set F : ℝ → ℝ := fun τ => ‖H τ‖ ^ 2 * (t * D τ) with hF
  have hFint : Integrable F := (hint.const_mul t).congr (Eventually.of_forall fun τ => by
    simp only [hF]; ring)
  have hrw : t * ∫ τ : ℝ, ‖H τ‖ ^ 2 * D τ = ∫ τ : ℝ, F τ := by
    rw [← integral_const_mul]; congr 1; funext τ; simp only [hF]; ring
  rw [hrw, ← integral_add_compl (measurableSet_Icc : MeasurableSet N) hFint]
  -- bounded near part
  have hHbd : ∀ τ, ‖H τ‖ ^ 2 ≤ (K₁ * (S * Cκ ^ 2)) ^ 2 := by
    intro τ
    have h1 : Cκ / (1 + S * |τ - τ₀|) ^ 2 ≤ Cκ := by
      apply div_le_self hCκ
      have : 1 ≤ 1 + S * |τ - τ₀| := by have := abs_nonneg (τ - τ₀); nlinarith
      nlinarith
    have h2 := hup τ
    have h3 : K₁ * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2) ≤ K₁ * (S * Cκ ^ 2) := by
      gcongr
    exact pow_le_pow_left₀ (norm_nonneg _) (h2.trans h3) 2
  have hHsq_meas : AEStronglyMeasurable (fun τ => ‖H τ‖ ^ 2) volume := hHm.norm.pow 2
  have hHsq_intOn : ∀ s : Set ℝ, MeasurableSet s → volume s < ⊤ →
      IntegrableOn (fun τ => ‖H τ‖ ^ 2) s := by
    intro s hs hfin
    exact Measure.integrableOn_of_bounded (M := (K₁ * (S * Cκ ^ 2)) ^ 2) hfin.ne
      hHsq_meas (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hHbd τ)
  have hnearInt : d₁ / 2 * ∫ τ in N, ‖H τ‖ ^ 2 ≤ ∫ τ in N, F τ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((hHsq_intOn N measurableSet_Icc measure_Icc_lt_top).const_mul _)
      hFint.integrableOn measurableSet_Icc fun τ hτ => ?_
    have hτ' : |τ - τ₀| ≤ η := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    simp only [hF]
    have := hnear τ hτ'
    nlinarith [sq_nonneg ‖H τ‖]
  have hwin : 2 / S * L ^ 2 ≤ ∫ τ in N, ‖H τ‖ ^ 2 := by
    have hsub : Icc (τ₀ - 1 / S) (τ₀ + 1 / S) ⊆ N := Icc_subset_Icc (by linarith) (by linarith)
    have hlowInt : ∫ τ in Icc (τ₀ - 1 / S) (τ₀ + 1 / S), L ^ 2 ≤
        ∫ τ in Icc (τ₀ - 1 / S) (τ₀ + 1 / S), ‖H τ‖ ^ 2 := by
      refine setIntegral_mono_on (integrableOn_const (by simp) (by simp))
        (hHsq_intOn _ measurableSet_Icc measure_Icc_lt_top) measurableSet_Icc fun τ hτ => ?_
      have hτ' : |τ - τ₀| ≤ 1 / S := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      exact pow_le_pow_left₀ hL (hlow τ hτ') 2
    have hconst : ∫ τ in Icc (τ₀ - 1 / S) (τ₀ + 1 / S), L ^ 2 = 2 / S * L ^ 2 := by
      rw [setIntegral_const]
      simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by have := one_div_pos.mpr hS0; linarith)]; ring
    rw [← hconst]
    exact hlowInt.trans (setIntegral_mono_set (hHsq_intOn N measurableSet_Icc measure_Icc_lt_top)
      (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall hsub))
  -- far part
  set G : ℝ → ℝ := fun τ => |t| * (K₁ ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) *
    (1 / (1 + |τ - τ₀|) ^ 3) with hG
  have hGint : Integrable G := (integrable_inv_one_add_abs_sub_cube τ₀).const_mul _
  have hfar : -(∫ τ : ℝ, G τ) ≤ ∫ τ in Nᶜ, F τ := by
    have hGnn : ∀ τ, 0 ≤ G τ := fun τ => by simp only [hG]; positivity
    have h1 : ∫ τ in Nᶜ, (-G τ) ≤ ∫ τ in Nᶜ, F τ := by
      refine setIntegral_mono_on hGint.neg.integrableOn hFint.integrableOn
        measurableSet_Icc.compl fun τ hτ => ?_
      have hu : η < |τ - τ₀| := by
        by_contra hc; push Not at hc
        exact hτ ⟨by linarith [(abs_le.mp hc).1], by linarith [(abs_le.mp hc).2]⟩
      have htail := tail_pointwise_le hS hη hu hCD (norm_nonneg _) (hup τ)
      have hFabs : |F τ| ≤ G τ := by
        simp only [hF, hG]
        rw [abs_mul, abs_of_nonneg (by positivity), abs_mul]
        calc ‖H τ‖ ^ 2 * (|t| * |D τ|) ≤ ‖H τ‖ ^ 2 * (|t| * (CD * (1 + |τ - τ₀|))) := by
              gcongr; exact hD τ
          _ = |t| * (‖H τ‖ ^ 2 * (CD * (1 + |τ - τ₀|))) := by ring
          _ ≤ |t| * (K₁ ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4) / (1 + |τ - τ₀|) ^ 3) :=
              mul_le_mul_of_nonneg_left htail (abs_nonneg _)
          _ = _ := by ring
      linarith [neg_abs_le (F τ)]
    have h2 : ∫ τ in Nᶜ, (-G τ) = -∫ τ in Nᶜ, G τ := integral_neg _
    have h3 : ∫ τ in Nᶜ, G τ ≤ ∫ τ : ℝ, G τ :=
      setIntegral_le_integral hGint (Eventually.of_forall hGnn)
    linarith
  have hGeq : ∫ τ : ℝ, G τ = |t| * (K₁ ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) *
      ∫ τ : ℝ, 1 / (1 + |τ - τ₀|) ^ 3 := by
    simp only [hG]; rw [integral_const_mul]
  rw [hGeq] at hfar
  have := mul_le_mul_of_nonneg_left hwin (by linarith : (0 : ℝ) ≤ d₁ / 2)
  linarith

/-- The concentration stage of twist rigidity: given a frequency `τ₀` near which `tD ≥ d₁/2` and
the limit transform has size `≥ m/2`, the spread twisted tests violate Weil positivity. -/
theorem twist_violation_of_concentration {α t τ₀ η m d₁ : ℝ} (hη0 : 0 < η) (hm0 : 0 < m)
    (hd₁0 : 0 < d₁)
    (hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η →
      d₁ / 2 ≤ t * (archFreq (τ - α) + archFreq (τ + α)) ∧ m / 2 ≤ ‖twistLimit α τ‖) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 + t * Real.cos (α * Real.log n)))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  set D : ℝ → ℝ := fun τ => archFreq (τ - α) + archFreq (τ + α) with hDdef
  -- constants
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_norm_paperFT_weilBumpC_le
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_twistTest_log_le α τ₀
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set Aκ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hAκ
  have hAκ0 : 0 ≤ Aκ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set B := (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) * Aκ with hB
  have hB0 : 0 ≤ B := mul_nonneg (integral_nonneg fun _ => by positivity) hAκ0
  set CD := 2 * (70 + 2 * |gammaHardyPhaseRate 0|) + 4 * |τ₀| + 4 * |α| + 4 with hCD
  have hCD0 : 0 ≤ CD := by positivity
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  set c := (Real.cos (1 / 4) / 4) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set I₃ := ∫ τ : ℝ, 1 / (1 + |τ - τ₀|) ^ 3 with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun _ => by positivity
  set L₀ := m / 4 * c with hL₀
  have hL₀0 : 0 < L₀ := by positivity
  set Ctail := |t| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / η ^ 4) * I₃ with hCtail
  have hCtail0 : 0 ≤ Ctail := by positivity
  set goal := d₁ / 2 * L₀ ^ 2 with hgoal
  have hgoal0 : 0 < goal := by positivity
  -- choice of the scale
  have t1 : Tendsto (fun S : ℝ => 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have t2 : Tendsto (fun S : ℝ => (2 * π + 2 * π * |t|) * KW * (S ^ 9 * Real.exp (-S))) atTop
      (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul
      ((2 * π + 2 * π * |t|) * KW)
  have t3 : Tendsto (fun S : ℝ => Ctail / S ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨S, ⟨⟨⟨hE2, hE3⟩, hE4⟩, hE1⟩⟩ := (((t1.eventually (ge_mem_nhds (by linarith :
    (0 : ℝ) < m / 4))).and (t2.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 2)))).and
    (t3.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 2)))).and
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
  set f := twistTest α τ₀ R S with hf
  have hfd : ContDiff ℝ 2 f := contDiff_twistTest α τ₀ R S
  have hfs : tsupport f ⊆ Icc (-(3 * R + S)) (3 * R + S) := tsupport_twistTest hS0
  -- polar conditions
  have hzero : ∀ z : ℂ, paperFT (weilRadicalTest R) z = 0 → paperFT f z = 0 := fun z hz => by
    rw [paperFT_twistTest_factor hS0, hz, zero_mul]
  have hzeroP : ∀ z : ℂ, paperFT (weilRadicalTest R) (z + ((-α : ℝ) : ℂ)) = 0 →
      paperFT f z = 0 := fun z hz => by
    rw [paperFT_twistTest_factor hS0, hz]; ring
  have hzeroM : ∀ z : ℂ, paperFT (weilRadicalTest R) (z + α) = 0 → paperFT f z = 0 :=
    fun z hz => by rw [paperFT_twistTest_factor hS0, hz]; ring
  have hp := hzero _ (paperFT_weilRadicalTest_half_I R)
  have hm' := hzero _ (paperFT_weilRadicalTest_neg_half_I R)
  have hpP : paperFT f (I / 2 + α) = 0 := hzeroP _ (by
    rw [show I / 2 + (α : ℂ) + ((-α : ℝ) : ℂ) = I / 2 by push_cast; ring]
    exact paperFT_weilRadicalTest_half_I R)
  have hmP : paperFT f (-(I / 2) + α) = 0 := hzeroP _ (by
    rw [show -(I / 2) + (α : ℂ) + ((-α : ℝ) : ℂ) = -(I / 2) by push_cast; ring]
    exact paperFT_weilRadicalTest_neg_half_I R)
  have hpM : paperFT f (I / 2 + ((-α : ℝ) : ℂ)) = 0 := hzeroM _ (by
    rw [show I / 2 + ((-α : ℝ) : ℂ) + (α : ℂ) = I / 2 by push_cast; ring]
    exact paperFT_weilRadicalTest_half_I R)
  have hmM : paperFT f (-(I / 2) + ((-α : ℝ) : ℂ)) = 0 := hzeroM _ (by
    rw [show -(I / 2) + ((-α : ℝ) : ℂ) + (α : ℂ) = -(I / 2) by push_cast; ring]
    exact paperFT_weilRadicalTest_neg_half_I R)
  refine ⟨3 * R + S, by linarith, f, hfd, hfs, hp, hm', ?_⟩
  rw [integral_weilAtomSymbol_twist hfd hfs hp hm' hpP hmP hpM hmM t]
  -- the concentration estimate
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
  have hHm : AEStronglyMeasurable (fun τ : ℝ => paperFT f τ) volume := by
    have hsed : SuperExpDecay f := ⟨hfd.continuous, fun c' =>
      (hfd.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_abs_gt (a := 3 * R + S) fun u hu =>
          twistTest_eq_zero hS0 hu).norm.mul_right⟩
    exact (hsed.differentiable_paperFT.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
  have hconc := concentrated_integral_lower (H := fun τ : ℝ => paperFT f τ) (D := D)
    (t := t) (τ₀ := τ₀) (η := η) (S := S) (d₁ := d₁) (L := L₀ * S) (K₁ := B ^ 3) (Cκ := Cκ)
    (CD := CD) hS1 hη0 h1S hd₁0 (by positivity) hCD0 (by positivity) hCκ0 hHm
    (integrable_normSq_paperFT_mul_twistArch hfd hfs)
    (fun τ hτ => (hnear τ hτ).1)
    (fun τ hτ => by
      have := norm_paperFT_twistTest_real_ge (α := α) (R := R) hS0 hτ
        (hnear τ (hτ.trans h1S)).2 happrox
      rw [hL₀]; convert this using 1; ring)
    (fun τ => norm_paperFT_twistTest_real_le hS0 hCκ τ)
    (fun τ => abs_twistArch_le α τ₀ τ)
  -- the three zero sides
  obtain ⟨hW0, hWP, hWM⟩ := hKW S hSe
  have hWre : 2 * π * (zetaZeroConfig.W f f).re + π * t *
      ((zetaZeroConfig.W (twistModulate α f) (twistModulate α f)).re +
        (zetaZeroConfig.W (twistModulate (-α) f) (twistModulate (-α) f)).re) ≤
      (2 * π + 2 * π * |t|) * KW * (S ^ 9 * Real.exp (-S)) * S := by
    have hπ : 0 < π := Real.pi_pos
    set Wb := KW * S ^ 10 * Real.exp (-S) with hWb
    have a1 : (zetaZeroConfig.W f f).re ≤ Wb := (Complex.re_le_norm _).trans hW0
    have a2 := (Complex.abs_re_le_norm _).trans hWP
    have a3 := (Complex.abs_re_le_norm _).trans hWM
    set x := (zetaZeroConfig.W (twistModulate α f) (twistModulate α f)).re
    set y := (zetaZeroConfig.W (twistModulate (-α) f) (twistModulate (-α) f)).re
    have hts : t * (x + y) ≤ |t| * (2 * Wb) := by
      calc t * (x + y) ≤ |t * (x + y)| := le_abs_self _
        _ = |t| * |x + y| := abs_mul _ _
        _ ≤ |t| * (|x| + |y|) := by gcongr; exact abs_add_le _ _
        _ ≤ |t| * (2 * Wb) := by gcongr; linarith
    have e1 : 2 * π * (zetaZeroConfig.W f f).re ≤ 2 * π * Wb :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    have e2 : π * t * (x + y) ≤ π * (|t| * (2 * Wb)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hts hπ.le
    have e3 : 2 * π * Wb + π * (|t| * (2 * Wb)) =
        (2 * π + 2 * π * |t|) * KW * (S ^ 9 * Real.exp (-S)) * S := by
      rw [hWb]; ring
    linarith
  have hmain : d₁ / 2 * (2 / S * (L₀ * S) ^ 2) -
      |t| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) * I₃ = 2 * goal * S - Ctail / S ^ 2 := by
    rw [hgoal, hCtail]; field_simp
  rw [hmain] at hconc
  have hE3' := mul_le_mul_of_nonneg_right hE3 hS0.le
  have hE4' : Ctail / S ^ 2 ≤ goal / 2 * S := by
    have := mul_le_mul_of_nonneg_right hE4 hS0.le
    calc Ctail / S ^ 2 = Ctail / S ^ 3 * S := by field_simp
      _ ≤ goal / 2 * S := this
  have hgoalS : 0 < goal * S := by positivity
  linarith


/-- **Twist rigidity.**  Let `A(τ) = Re ψ(1/4 + iτ/2) - log π` be the archimedean symbol.  If
`t (A(τ₁ - α) + A(τ₁ + α)) > 0` for some real `τ₁`, then the prime weights
`Λ(n)(1 + t cos(α log n))` violate Weil positivity: some polar-constrained `C²` test at some level
has negative finite-atom symbol energy.

The tests are radical for `ζ(s)`, `ζ(s + iα)` and `ζ(s - iα)` (triple radical `T_R` at `R = log S`)
and are spread by `q(x/S) e^{-iτ₀x}` near a frequency `τ₀` close to `τ₁`.  Their zero sides are
`O(S^{10} e^{-S})` and their energy is `-(t/2) ∫ |h|² (A(τ - α) + A(τ + α)) + o(1)`, which
concentrates at `τ₀`. -/
theorem twist_weilAtomSymbol_not_nonneg {α t τ₁ : ℝ}
    (h : 0 < t * (archFreq (τ₁ - α) + archFreq (τ₁ + α))) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 + t * Real.cos (α * Real.log n)))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  set D : ℝ → ℝ := fun τ => archFreq (τ - α) + archFreq (τ + α) with hDdef
  have hDc : Continuous D := (continuous_archFreq.comp (continuous_id.sub continuous_const)).add
    (continuous_archFreq.comp (continuous_id.add continuous_const))
  set d₁ := t * D τ₁ with hd₁
  have hd₁0 : 0 < d₁ := h
  -- a neighbourhood where `tD ≥ d₁/2`
  have htD : Continuous (fun τ => t * D τ) := continuous_const.mul hDc
  obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
    (htD.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
  have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ t * D τ := by
    intro τ hτ
    have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  -- a nearby point where the limit transform does not vanish
  have hev := ((eventually_radicalLimit_shift_ne_zero 0 τ₁).and
    ((eventually_radicalLimit_shift_ne_zero α τ₁).and
      (eventually_radicalLimit_shift_ne_zero (-α) τ₁))).and
    (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0)))
  obtain ⟨τ₀, ⟨h0, h1, h2⟩, hball⟩ := hev.exists
  have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
  have hlim0 : twistLimit α τ₀ ≠ 0 := by
    unfold twistLimit
    simp only [Complex.ofReal_zero, add_zero] at h0
    exact mul_ne_zero (mul_ne_zero h0 h1) h2
  set m := ‖twistLimit α τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hlim0
  obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
    ((continuous_twistLimit_real α).continuousAt (x := τ₀)) (m / 2) (by linarith)
  set η := min (η₁ / 2) (η₂ / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ t * D τ ∧ m / 2 ≤ ‖twistLimit α τ‖ := by
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
      have := norm_sub_norm_le (twistLimit α τ₀) (twistLimit α τ)
      rw [norm_sub_rev] at this
      linarith
  exact twist_violation_of_concentration hη0 hm0 hd₁0 hnear

/-! ### Consequences -/

theorem archFreq_neg (τ : ℝ) : archFreq (-τ) = archFreq τ := by
  rw [archFreq_eq, archFreq_eq, gammaHardyPhaseRate_neg]

theorem archFreq_zero_neg : archFreq 0 < 0 := by
  rw [archFreq_eq]; linarith [gammaHardyPhaseRate_zero_neg]

/-- **Positive twists.**  For every `α` and every `t > 0` the weights `Λ(n)(1 + t cos(α log n))`
violate Weil positivity: the archimedean symbol is eventually positive at high frequency. -/
theorem twist_pos_weilAtomSymbol_not_nonneg (α : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 + t * Real.cos (α * Real.log n)))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  have htend : Tendsto (fun τ : ℝ => archFreq (τ - α) + archFreq (τ + α)) atTop atTop := by
    have h1 : Tendsto (fun τ : ℝ => archFreq (τ - α)) atTop atTop := by
      have := (gammaHardyPhaseRate_tendsto_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).comp
        (tendsto_atTop_add_const_right _ (-α) tendsto_id)
      refine this.congr fun τ => ?_
      simp only [Function.comp_apply, id]; rw [archFreq_eq, sub_eq_add_neg]
    have h2 : Tendsto (fun τ : ℝ => archFreq (τ + α)) atTop atTop := by
      have := (gammaHardyPhaseRate_tendsto_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).comp
        (tendsto_atTop_add_const_right _ α tendsto_id)
      refine this.congr fun τ => ?_
      simp only [Function.comp_apply, id]; rw [archFreq_eq]
    exact h1.atTop_add_atTop h2
  obtain ⟨τ₁, hτ₁⟩ := (htend.eventually_gt_atTop 0).exists
  exact twist_weilAtomSymbol_not_nonneg (mul_pos ht hτ₁)

/-- **Negative twists of low frequency.**  If the archimedean symbol is negative at `α`, then for
every `t < 0` the weights `Λ(n)(1 + t cos(α log n))` violate Weil positivity. -/
theorem twist_neg_weilAtomSymbol_not_nonneg {α t : ℝ} (hα : archFreq α < 0) (ht : t < 0) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 + t * Real.cos (α * Real.log n)))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  refine twist_weilAtomSymbol_not_nonneg (τ₁ := 0) ?_
  rw [zero_sub, archFreq_neg, zero_add]
  nlinarith

/-- **Two-sided isolation along small twists.**  There is `α₀ > 0` such that for every `|α| < α₀`
and every `t ≠ 0` the weights `Λ(n)(1 + t cos(α log n))` violate Weil positivity. -/
theorem exists_twist_isolation : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, |α| < α₀ → ∀ t : ℝ, t ≠ 0 →
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 + t * Real.cos (α * Real.log n)))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  obtain ⟨α₀, hα₀, hα⟩ := Metric.continuousAt_iff.mp continuous_archFreq.continuousAt
    (-(archFreq 0)) (by linarith [archFreq_zero_neg])
  refine ⟨α₀, hα₀, fun α hαα t ht => ?_⟩
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine twist_neg_weilAtomSymbol_not_nonneg ?_ hneg
    have := hα (show dist α 0 < α₀ by rwa [Real.dist_eq, sub_zero])
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).2
    linarith
  · exact twist_pos_weilAtomSymbol_not_nonneg α hpos

/-- **Scaling rigidity.**  For every `c ≠ 1` the weights `c Λ(n)` violate Weil positivity. -/
theorem scaled_vonMangoldt_weilAtomSymbol_not_nonneg {c : ℝ} (hc : c ≠ 1) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => c * ArithmeticFunction.vonMangoldt n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  have hw : (fun n : ℕ => c * ArithmeticFunction.vonMangoldt n) =
      fun n => ArithmeticFunction.vonMangoldt n * (1 + (c - 1) * Real.cos (0 * Real.log n)) := by
    funext n; simp only [zero_mul, Real.cos_zero, mul_one]; ring
  rw [hw]
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hc) with hneg | hpos
  · exact twist_neg_weilAtomSymbol_not_nonneg archFreq_zero_neg hneg
  · exact twist_pos_weilAtomSymbol_not_nonneg 0 hpos

end RHTower
