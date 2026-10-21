import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSum
import GaloisForLFunctions.RHTower.PoissonArithmeticProgressionBound
import GaloisForLFunctions.HTGeometry.FourierIteratedDerivDecay
import GaloisForLFunctions.HTGeometry.SchwartzCompactSupport
import GaloisForLFunctions.HTGeometry.BlockWindowFubini

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 8.4: Fourier decay of smoothings of `|R|²`

For bumps `ψ₁, ψ₂` supported in `[A⁻¹, A]` and `ψ₃` compactly supported, and a scale `B ≥ 1`,
Guth–Maynard (arXiv 2405.20552, Lemma 8.4) consider

`f(u) = ψ₁(u) ∫ B ψ₃(B(u − x)) ψ₂(x) |R(x)|² dx`,

`|R|²` smoothed at scale `1/B` and localised by `ψ₁`, and prove `f̂(ξ) ⪅_j (T/|ξ|)^j sup f`.

Proof.
* **Decay** (`pow_mul_norm_fourier_smoothedDensity_le`). By Fubini, `f̂(ξ) = ∫ g(x) ĥ_x(ξ) dx`
  with `g = ψ₂|R|²` and the localised kernel `h_x(u) = ψ₁(u) B ψ₃(B(u − x))`. Leibniz gives
  `∫|h_x^{(j)}| ≤ D₁ J₃ (1 + B)^j` (`D₁` bounds `ψ₁^{(i)}`, `J₃` bounds `∫|ψ₃^{(i)}|`, `i ≤ j`), and
  `j` integrations by parts `(2π|ξ|)^j |ĥ_x(ξ)| ≤ ∫|h_x^{(j)}|`; hence
  `(2π|ξ|)^j |f̂(ξ)| ≤ D₁ J₃ (1 + B)^j ∫ g`.
* **Size at `1`** (`smoothedDensity_one_ge`). For `W ⊂ [x₀, x₀ + T]` and `|log v| ≤ 1/T` every
  phase `(t − x₀) log v` has modulus `≤ 1`, so `|R(v)| ≥ |W|/2`; with `ψ₁(1) = ψ₂(1) = ψ₃(0) = 1`
  and Lipschitz constants `≤ D`, integrating over `[1, 1 + r]`, `r = 1/((1 + 2D)KT)`, gives
  `f(1) ≥ B |W|² / (16 (1 + 2D) K T)` when `B ≤ KT`.
* **Assembly** (`guthMaynard_lemma84`). `∫ g ≤ |W|² ∫ψ₂` and `|W|² ≤ 16(1 + 2D)KT f(1)/B` turn the
  decay into `|ξ|^j |f̂(ξ)| ≤ C K^j T^j sup f` for `j ≥ 1`; `j = 0` is `|f̂| ≤ ∫ f ≤ 2A sup f`.
-/

open MeasureTheory Set
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-- The density of Lemma 8.4: `f(u) = ψ₁(u) ∫ B ψ₃(B(u − x)) ψ₂(x) |R(x)|² dx`. -/
def smoothedDensity (ψ₁ ψ₂ ψ₃ : ℝ → ℝ) (B : ℝ) (W : Finset ℝ) (u : ℝ) : ℝ :=
  ψ₁ u * ∫ x, B * ψ₃ (B * (u - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2

/-! ### The localised kernel `h_x(u) = ψ₁(u) B ψ₃(B(u − x))` -/

/-- Derivatives of the rescaled translate: `(B ψ(B(· − x)))^{(i)} = B^{i+1} ψ^{(i)}(B(· − x))`. -/
theorem iteratedDeriv_scaledKernel {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (B x : ℝ) (i : ℕ) :
    iteratedDeriv i (fun u => B * ψ (B * (u - x)))
      = fun u => B ^ (i + 1) * iteratedDeriv i ψ (B * (u - x)) := by
  have hfun : (fun u => B * ψ (B * (u - x))) = fun u => B * ψ (-(B * x) + B * u) := by
    funext u
    rw [show B * (u - x) = -(B * x) + B * u by ring]
  rw [hfun]
  funext u
  rw [iteratedDeriv_const_mul_field, RHTower.iteratedDeriv_comp_affine
    (hψ.of_le (by exact_mod_cast le_top)) (-(B * x)) B le_rfl]
  simp only
  rw [show -(B * x) + B * u = B * (u - x) by ring, pow_succ]
  ring

/-- `∫ |G(B(u − x))| du = B⁻¹ ∫ |G|` for `B > 0`. -/
theorem integral_abs_comp_scaled_sub {G : ℝ → ℝ} {B : ℝ} (hB : 0 < B) (x : ℝ) :
    ∫ u, |G (B * (u - x))| = B⁻¹ * ∫ y, |G y| := by
  rw [integral_sub_right_eq_self (fun y => |G (B * y)|) x, Measure.integral_comp_mul_left
    (fun y => |G y|) B, abs_inv, abs_of_pos hB, smul_eq_mul]

/-- **Leibniz bound for the localised kernel.** If `|ψ₁^{(i)}| ≤ D₁` and `∫|ψ₃^{(i)}| ≤ J₃` for
`i ≤ j`, then `∫ |h_x^{(j)}| ≤ D₁ J₃ (1 + B)^j` for `h_x(u) = ψ₁(u) B ψ₃(B(u − x))`. -/
theorem integral_abs_iteratedDeriv_localKernel_le {ψ₁ ψ₃ : ℝ → ℝ}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) ψ₁) (h₃ : ContDiff ℝ (⊤ : ℕ∞) ψ₃) (hs₃ : HasCompactSupport ψ₃)
    {B : ℝ} (hB : 0 < B) {D₁ J₃ : ℝ} {j : ℕ} (hd₁ : ∀ i ≤ j, ∀ u, |iteratedDeriv i ψ₁ u| ≤ D₁)
    (hd₃ : ∀ i ≤ j, ∫ y, |iteratedDeriv i ψ₃ y| ≤ J₃) (x : ℝ) :
    ∫ u, |iteratedDeriv j (fun u => ψ₁ u * (B * ψ₃ (B * (u - x)))) u|
      ≤ D₁ * J₃ * (1 + B) ^ j := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) fun u => B * ψ₃ (B * (u - x)) :=
    contDiff_const.mul (h₃.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))
  have hD₁ : 0 ≤ D₁ := (abs_nonneg _).trans (hd₁ 0 (Nat.zero_le j) 0)
  -- integrability of the derivatives of `ψ₃`
  have hint₃ : ∀ m : ℕ, Integrable fun y => |iteratedDeriv m ψ₃ y| := fun m =>
    ((h₃.continuous_iteratedDeriv m (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
      (GaloisForLFunctions.HTGeometry.hasCompactSupport_iteratedDeriv_vec hs₃ m)).abs
  have hint₃' : ∀ m : ℕ, Integrable fun u => |iteratedDeriv m ψ₃ (B * (u - x))| := fun m =>
    ((hint₃ m).comp_mul_left' hB.ne').comp_sub_right x
  -- the Leibniz expansion
  have hLeib : ∀ u, iteratedDeriv j (fun u => ψ₁ u * (B * ψ₃ (B * (u - x)))) u
      = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * iteratedDeriv i ψ₁ u
          * (B ^ (j - i + 1) * iteratedDeriv (j - i) ψ₃ (B * (u - x))) := by
    intro u
    have h := iteratedDeriv_mul (n := j) (x := u) (f := ψ₁)
      (g := fun u => B * ψ₃ (B * (u - x)))
      ((h₁.of_le (by exact_mod_cast le_top)).contDiffAt)
      ((hk.of_le (by exact_mod_cast le_top)).contDiffAt)
    rw [show (fun u => ψ₁ u * (B * ψ₃ (B * (u - x)))) = ψ₁ * fun u => B * ψ₃ (B * (u - x))
      from rfl, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedDeriv_scaledKernel h₃]
  -- the pointwise majorant
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, Φ = fun u => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * D₁ * (B ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (B * (u - x))|) :=
    ⟨_, rfl⟩
  have hpoint : ∀ u, |iteratedDeriv j (fun u => ψ₁ u * (B * ψ₃ (B * (u - x)))) u| ≤ Φ u := by
    intro u
    rw [hLeib u, hΦ]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j.choose i : ℝ)),
      abs_of_pos (by positivity : (0 : ℝ) < B ^ (j - i + 1))]
    gcongr
    exact hd₁ i hi' u
  have hΦint : Integrable Φ := by
    rw [hΦ]
    exact integrable_finsetSum _ fun i _ => ((hint₃' (j - i)).const_mul _).const_mul _
  have hΦ_int : ∫ u, Φ u ≤ D₁ * J₃ * (1 + B) ^ j := by
    rw [hΦ, integral_finsetSum _ fun i _ => ((hint₃' (j - i)).const_mul _).const_mul _]
    calc ∑ i ∈ Finset.range (j + 1), ∫ u, (j.choose i : ℝ) * D₁
          * (B ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (B * (u - x))|)
        = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D₁ * B ^ (j - i)
            * ∫ y, |iteratedDeriv (j - i) ψ₃ y| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul, integral_const_mul, integral_abs_comp_scaled_sub hB, pow_succ]
          field_simp
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D₁ * B ^ (j - i) * J₃ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : j - i ≤ j := Nat.sub_le j i
          gcongr
          exact hd₃ (j - i) hi'
      _ = D₁ * J₃ * (1 + B) ^ j := by
          rw [add_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [one_pow]
          ring
  calc ∫ u, |iteratedDeriv j (fun u => ψ₁ u * (B * ψ₃ (B * (u - x)))) u|
      ≤ ∫ u, Φ u :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _) hΦint
          (Filter.Eventually.of_forall hpoint)
    _ ≤ D₁ * J₃ * (1 + B) ^ j := hΦ_int

/-- **Fourier decay of the localised kernel.** `(2π|ξ|)^j |ĥ_x(ξ)| ≤ D₁ J₃ (1 + B)^j`. -/
theorem pow_mul_norm_fourier_localKernel_le {ψ₁ ψ₃ : ℝ → ℝ}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) ψ₁) (hs₁ : HasCompactSupport ψ₁) (h₃ : ContDiff ℝ (⊤ : ℕ∞) ψ₃)
    (hs₃ : HasCompactSupport ψ₃) {B : ℝ} (hB : 0 < B) {D₁ J₃ : ℝ} {j : ℕ}
    (hd₁ : ∀ i ≤ j, ∀ u, |iteratedDeriv i ψ₁ u| ≤ D₁)
    (hd₃ : ∀ i ≤ j, ∫ y, |iteratedDeriv i ψ₃ y| ≤ J₃) (x ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ j * ‖𝓕 (fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ)) ξ‖
      ≤ D₁ * J₃ * (1 + B) ^ j := by
  have hh : ContDiff ℝ (⊤ : ℕ∞) fun u => ψ₁ u * (B * ψ₃ (B * (u - x))) :=
    h₁.mul (contDiff_const.mul (h₃.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))))
  have hhj : ContDiff ℝ j fun u => ψ₁ u * (B * ψ₃ (B * (u - x))) :=
    hh.of_le (by exact_mod_cast le_top)
  have hH : ContDiff ℝ j fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hhj
  have hsH : HasCompactSupport fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ) :=
    (hs₁.mul_right (f' := fun u => B * ψ₃ (B * (u - x)))).comp_left Complex.ofReal_zero
  have hint : ∀ i ≤ j, Integrable
      (iteratedDeriv i fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ)) := fun i hi =>
    GaloisForLFunctions.HTGeometry.integrable_iteratedDeriv_of_hasCompactSupport hH hsH hi
  refine (RHTower.pow_mul_norm_fourier_le_of_iteratedDeriv hH hint ξ).trans ?_
  rw [RHTower.iteratedDeriv_ofReal_comp_of_le hhj le_rfl]
  simp_rw [Complex.norm_real, Real.norm_eq_abs]
  exact integral_abs_iteratedDeriv_localKernel_le h₁ h₃ hs₃ hB hd₁ hd₃ x

/-! ### Decay of `f̂` -/

/-- `ψ₂ |R|²` is integrable for continuous compactly supported `ψ₂`. -/
theorem integrable_mul_norm_lagSum_sq {ψ₂ : ℝ → ℝ} (hc₂ : Continuous ψ₂)
    (hs₂ : HasCompactSupport ψ₂) (W : Finset ℝ) :
    Integrable fun x => ψ₂ x * ‖lagSum W x‖ ^ 2 := by
  have hψ₂ : Integrable ψ₂ := hc₂.integrable_of_hasCompactSupport hs₂
  have h := hψ₂.bdd_mul (c := (W.card : ℝ) ^ 2)
    (measurable_norm_lagSum_sq W).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2)
  exact h.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- **Fubini form of `f̂`.** `f̂(ξ) = ∫ g(x) ĥ_x(ξ) dx` with `g = ψ₂|R|²` and
`h_x(u) = ψ₁(u) B ψ₃(B(u − x))`. -/
theorem fourier_smoothedDensity_eq {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} (hc₁ : Continuous ψ₁)
    (hs₁ : HasCompactSupport ψ₁) (hc₂ : Continuous ψ₂) (hs₂ : HasCompactSupport ψ₂)
    (hc₃ : Continuous ψ₃) (hs₃ : HasCompactSupport ψ₃) {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    (ξ : ℝ) :
    𝓕 (fun u => (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ)) ξ
      = ∫ x, ((ψ₂ x * ‖lagSum W x‖ ^ 2 : ℝ) : ℂ)
          * 𝓕 (fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ)) ξ := by
  obtain ⟨S₃, hS₃⟩ := hc₃.bounded_above_of_compact_support hs₃
  have hψ₁i : Integrable ψ₁ := hc₁.integrable_of_hasCompactSupport hs₁
  have hgi := integrable_mul_norm_lagSum_sq hc₂ hs₂ W
  have hdens : ∀ u, smoothedDensity ψ₁ ψ₂ ψ₃ B W u
      = ∫ x, ψ₁ u * (B * ψ₃ (B * (u - x))) * (ψ₂ x * ‖lagSum W x‖ ^ 2) := by
    intro u
    rw [smoothedDensity, ← integral_const_mul]
    congr 1
    funext x
    ring
  have hstep : ∀ u, Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I)
      • ((smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℝ) : ℂ)
      = ∫ x, Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I)
          • ((ψ₁ u * (B * ψ₃ (B * (u - x))) * (ψ₂ x * ‖lagSum W x‖ ^ 2) : ℝ) : ℂ) := by
    intro u
    rw [hdens u, ← integral_complex_ofReal, ← integral_smul]
  have hm₁ := hc₁.measurable
  have hm₂ := hc₂.measurable
  have hm₃ := hc₃.measurable
  have hmR := measurable_lagSum W
  have hmeas : AEStronglyMeasurable (Function.uncurry fun u x =>
      Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I)
        • ((ψ₁ u * (B * ψ₃ (B * (u - x))) * (ψ₂ x * ‖lagSum W x‖ ^ 2) : ℝ) : ℂ))
      (volume.prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    change Measurable fun p : ℝ × ℝ => Complex.exp (↑(-2 * Real.pi * p.1 * ξ) * Complex.I)
      • ((ψ₁ p.1 * (B * ψ₃ (B * (p.1 - p.2))) * (ψ₂ p.2 * ‖lagSum W p.2‖ ^ 2) : ℝ) : ℂ)
    fun_prop
  have hbound : ∀ᵐ p ∂(volume.prod volume), ‖Function.uncurry (fun u x =>
      Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I)
        • ((ψ₁ u * (B * ψ₃ (B * (u - x))) * (ψ₂ x * ‖lagSum W x‖ ^ 2) : ℝ) : ℂ)) p‖
      ≤ (|ψ₁ p.1| * (B * S₃)) * |ψ₂ p.2 * ‖lagSum W p.2‖ ^ 2| := by
    refine Filter.Eventually.of_forall fun p => ?_
    change ‖Complex.exp (↑(-2 * Real.pi * p.1 * ξ) * Complex.I)
      • ((ψ₁ p.1 * (B * ψ₃ (B * (p.1 - p.2))) * (ψ₂ p.2 * ‖lagSum W p.2‖ ^ 2) : ℝ) : ℂ)‖ ≤ _
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_of_pos hB]
    have h3 := hS₃ (B * (p.1 - p.2))
    rw [Real.norm_eq_abs] at h3
    gcongr
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [hstep]
  rw [GaloisForLFunctions.HTGeometry.integral_swap_of_dominated_prod
    (hψ₁i.abs.mul_const (B * S₃)) hgi.abs hmeas hbound]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  congr 1
  funext u
  rw [smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- **Decay of `f̂`.** If `|ψ₁^{(i)}| ≤ D₁` and `∫|ψ₃^{(i)}| ≤ J₃` for `i ≤ j`, then
`(2π|ξ|)^j |f̂(ξ)| ≤ D₁ J₃ (1 + B)^j ∫ |ψ₂| |R|²`. -/
theorem pow_mul_norm_fourier_smoothedDensity_le {ψ₁ ψ₂ ψ₃ : ℝ → ℝ}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) ψ₁) (hs₁ : HasCompactSupport ψ₁) (hc₂ : Continuous ψ₂)
    (hs₂ : HasCompactSupport ψ₂) (h₃ : ContDiff ℝ (⊤ : ℕ∞) ψ₃) (hs₃ : HasCompactSupport ψ₃)
    {B : ℝ} (hB : 0 < B) {D₁ J₃ : ℝ} {j : ℕ} (hd₁ : ∀ i ≤ j, ∀ u, |iteratedDeriv i ψ₁ u| ≤ D₁)
    (hd₃ : ∀ i ≤ j, ∫ y, |iteratedDeriv i ψ₃ y| ≤ J₃) (W : Finset ℝ) (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ j * ‖𝓕 (fun u => (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ)) ξ‖
      ≤ D₁ * J₃ * (1 + B) ^ j * ∫ x, |ψ₂ x| * ‖lagSum W x‖ ^ 2 := by
  obtain ⟨K, hK⟩ : ∃ K, K = D₁ * J₃ * (1 + B) ^ j := ⟨_, rfl⟩
  have hgi := integrable_mul_norm_lagSum_sq hc₂ hs₂ W
  have hmaj : Integrable fun x => |ψ₂ x| * ‖lagSum W x‖ ^ 2 * K := by
    refine (hgi.abs.mul_const K).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖lagSum W x‖ ^ 2)]
  rw [fourier_smoothedDensity_eq h₁.continuous hs₁ hc₂ hs₂ h₃.continuous hs₃ hB W ξ]
  have hc : ‖(((2 * Real.pi * |ξ|) ^ j : ℝ) : ℂ)‖ = (2 * Real.pi * |ξ|) ^ j := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (2 * Real.pi * |ξ|) ^ j * ‖∫ x, ((ψ₂ x * ‖lagSum W x‖ ^ 2 : ℝ) : ℂ)
          * 𝓕 (fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ)) ξ‖
      = ‖∫ x, (((2 * Real.pi * |ξ|) ^ j : ℝ) : ℂ) * (((ψ₂ x * ‖lagSum W x‖ ^ 2 : ℝ) : ℂ)
          * 𝓕 (fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ)) ξ)‖ := by
        rw [integral_const_mul, norm_mul, hc]
    _ ≤ ∫ x, |ψ₂ x| * ‖lagSum W x‖ ^ 2 * K := by
        refine norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall fun x => ?_)
        rw [norm_mul, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖lagSum W x‖ ^ 2), hK]
        have h := pow_mul_norm_fourier_localKernel_le h₁ hs₁ h₃ hs₃ hB hd₁ hd₃ x ξ
        have h0 : 0 ≤ |ψ₂ x| * ‖lagSum W x‖ ^ 2 := by positivity
        calc (2 * Real.pi * |ξ|) ^ j * (|ψ₂ x| * ‖lagSum W x‖ ^ 2
              * ‖𝓕 (fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ)) ξ‖)
            = |ψ₂ x| * ‖lagSum W x‖ ^ 2 * ((2 * Real.pi * |ξ|) ^ j
              * ‖𝓕 (fun u => ((ψ₁ u * (B * ψ₃ (B * (u - x))) : ℝ) : ℂ)) ξ‖) := by ring
          _ ≤ |ψ₂ x| * ‖lagSum W x‖ ^ 2 * (D₁ * J₃ * (1 + B) ^ j) :=
            mul_le_mul_of_nonneg_left h h0
    _ = K * ∫ x, |ψ₂ x| * ‖lagSum W x‖ ^ 2 := by rw [integral_mul_const, mul_comm]
    _ = D₁ * J₃ * (1 + B) ^ j * ∫ x, |ψ₂ x| * ‖lagSum W x‖ ^ 2 := by rw [hK]

/-! ### The size of `f` at `1` -/

/-- **`|R| ≥ |W|/2` near `1`.** For `W ⊂ [x₀, x₀ + T]` and `|log v| ≤ 1/T` every phase
`(t − x₀) log v` has modulus at most `1`, so `|R(v)| ≥ Σ_t cos((t − x₀) log v) ≥ |W|/2`. -/
theorem card_div_two_le_norm_lagSum {W : Finset ℝ} {x₀ T : ℝ} (hT : 0 < T)
    (hW : ∀ t ∈ W, x₀ ≤ t ∧ t ≤ x₀ + T) {v : ℝ} (hv : |Real.log v| ≤ 1 / T) :
    (W.card : ℝ) / 2 ≤ ‖lagSum W v‖ := by
  have hrot : Complex.exp (-(Complex.I * x₀ * Real.log v)) * lagSum W v
      = ∑ t ∈ W, Complex.exp (↑((t - x₀) * Real.log v) * Complex.I) := by
    rw [lagSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hunit : ‖Complex.exp (-(Complex.I * x₀ * Real.log v))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hcos : ∀ t ∈ W, 1 / 2 ≤ Real.cos ((t - x₀) * Real.log v) := by
    intro t ht
    have h1 : |(t - x₀) * Real.log v| ≤ 1 := by
      rw [abs_mul]
      have ha : |t - x₀| ≤ T := by
        rw [abs_le]
        constructor <;> linarith [(hW t ht).1, (hW t ht).2]
      calc |t - x₀| * |Real.log v| ≤ T * (1 / T) := mul_le_mul ha hv (abs_nonneg _) hT.le
        _ = 1 := by field_simp
    have h2 : ((t - x₀) * Real.log v) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg ((t - x₀) * Real.log v)]
    linarith [Real.one_sub_sq_div_two_le_cos (x := (t - x₀) * Real.log v)]
  calc (W.card : ℝ) / 2 = ∑ _t ∈ W, (1 / 2 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ t ∈ W, Real.cos ((t - x₀) * Real.log v) := Finset.sum_le_sum hcos
    _ = (∑ t ∈ W, Complex.exp (↑((t - x₀) * Real.log v) * Complex.I)).re := by
        rw [Complex.re_sum]
        simp_rw [Complex.exp_ofReal_mul_I_re]
    _ ≤ ‖∑ t ∈ W, Complex.exp (↑((t - x₀) * Real.log v) * Complex.I)‖ := Complex.re_le_norm _
    _ = ‖lagSum W v‖ := by rw [← hrot, norm_mul, hunit, one_mul]

/-- A derivative bound `|ψ'| ≤ D` gives the Lipschitz bound `|ψ(a) − ψ(b)| ≤ D|a − b|`. -/
theorem abs_sub_le_of_abs_deriv_le {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) {D : ℝ}
    (hD : ∀ x, |deriv ψ x| ≤ D) (a b : ℝ) : |ψ a - ψ b| ≤ D * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (x := b) (y := a)
    (fun x _ => hψ x) (fun x _ => by rw [Real.norm_eq_abs]; exact hD x) convex_univ trivial
    trivial
  simpa only [Real.norm_eq_abs] using h

/-- **Size of `f` at `1`.** If `ψ₁(1) = ψ₂(1) = ψ₃(0) = 1`, `ψ₂, ψ₃ ≥ 0` have Lipschitz constant
`D`, `B ≤ KT` with `K, T ≥ 1`, and `W ⊂ [x₀, x₀ + T]`, then
`f(1) ≥ B |W|² / (16 (1 + 2D) K T)`. -/
theorem smoothedDensity_one_ge {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} (hc₂ : Continuous ψ₂)
    (hs₂ : HasCompactSupport ψ₂) (hc₃ : Continuous ψ₃) (hs₃ : HasCompactSupport ψ₃)
    (hn₂ : ∀ x, 0 ≤ ψ₂ x) (hn₃ : ∀ x, 0 ≤ ψ₃ x) (h1₁ : ψ₁ 1 = 1) (h1₂ : ψ₂ 1 = 1)
    (h0₃ : ψ₃ 0 = 1) {D : ℝ} (hD : 0 ≤ D) (hL₂ : ∀ a b, |ψ₂ a - ψ₂ b| ≤ D * |a - b|)
    (hL₃ : ∀ a b, |ψ₃ a - ψ₃ b| ≤ D * |a - b|) {B K T x₀ : ℝ} (hB : 0 < B) (hK : 1 ≤ K)
    (hT : 1 ≤ T) (hBT : B ≤ K * T) {W : Finset ℝ} (hW : ∀ t ∈ W, x₀ ≤ t ∧ t ≤ x₀ + T) :
    B * (W.card : ℝ) ^ 2 / (16 * ((1 + 2 * D) * K * T)) ≤ smoothedDensity ψ₁ ψ₂ ψ₃ B W 1 := by
  obtain ⟨r, hr⟩ : ∃ r, r = 1 / ((1 + 2 * D) * K * T) := ⟨_, rfl⟩
  have hKT : 1 ≤ K * T := one_le_mul_of_one_le_of_one_le hK hT
  have hden : 0 < (1 + 2 * D) * K * T := by positivity
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrT : r ≤ 1 / T := by
    rw [hr]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : 1 ≤ (1 + 2 * D) * K := one_le_mul_of_one_le_of_one_le (by linarith) hK
    nlinarith
  have hDr : D * r ≤ 1 / 2 := by
    rw [hr, mul_one_div, div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hKT (by positivity : (0 : ℝ) ≤ 1 + 2 * D)]
  have hDBr : D * B * r ≤ 1 / 2 := by
    rw [hr, mul_one_div, div_le_iff₀ hden]
    have h1 : D * B ≤ D * (K * T) := mul_le_mul_of_nonneg_left hBT hD
    nlinarith
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ,
      F = fun x => B * ψ₃ (B * (1 - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2 := ⟨_, rfl⟩
  have hF0 : ∀ x, 0 ≤ F x := fun x => by
    rw [hF]
    have := hn₂ x
    have := hn₃ (B * (1 - x))
    positivity
  have hFi : Integrable F := by
    obtain ⟨S₃, hS₃⟩ := hc₃.bounded_above_of_compact_support hs₃
    have hψ₂ : Integrable ψ₂ := hc₂.integrable_of_hasCompactSupport hs₂
    have hm₃ := hc₃.measurable
    have hmR := measurable_lagSum W
    have h := hψ₂.bdd_mul (c := B * S₃ * (W.card : ℝ) ^ 2)
      (f := fun x => B * ψ₃ (B * (1 - x)) * ‖lagSum W x‖ ^ 2)
      (by fun_prop : Measurable fun x => B * ψ₃ (B * (1 - x)) * ‖lagSum W x‖ ^ 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        have h3 := hS₃ (B * (1 - x))
        rw [Real.norm_eq_abs] at h3 ⊢
        rw [abs_mul, abs_mul, abs_of_pos hB, abs_of_nonneg (by positivity : (0 : ℝ) ≤
          ‖lagSum W x‖ ^ 2)]
        have h4 : ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2
        have hS0 : 0 ≤ B * S₃ := mul_nonneg hB.le ((abs_nonneg _).trans h3)
        gcongr)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hF]
    ring
  have hFlow : ∀ x ∈ Icc 1 (1 + r), B * (W.card : ℝ) ^ 2 / 16 ≤ F x := by
    intro x hx
    have hx1 : |x - 1| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hψ₂x : 1 / 2 ≤ ψ₂ x := by
      have h := hL₂ x 1
      rw [h1₂] at h
      have h' : |ψ₂ x - 1| ≤ 1 / 2 := h.trans ((mul_le_mul_of_nonneg_left hx1 hD).trans hDr)
      linarith [(abs_le.mp h').1]
    have hψ₃x : 1 / 2 ≤ ψ₃ (B * (1 - x)) := by
      have h := hL₃ (B * (1 - x)) 0
      rw [h0₃, sub_zero, abs_mul, abs_of_pos hB, abs_sub_comm (1 : ℝ) x] at h
      have h' : |ψ₃ (B * (1 - x)) - 1| ≤ 1 / 2 := by
        refine h.trans ?_
        calc D * (B * |x - 1|) ≤ D * (B * r) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx1 hB.le) hD
          _ = D * B * r := by ring
          _ ≤ 1 / 2 := hDBr
      linarith [(abs_le.mp h').1]
    have hRx : (W.card : ℝ) / 2 ≤ ‖lagSum W x‖ := by
      refine card_div_two_le_norm_lagSum (by linarith) hW ?_
      have hx0 : 0 < x := by linarith [hx.1]
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.1
      have hlog1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
      rw [abs_of_nonneg hlog0]
      linarith [hx.2]
    have hR2 : ((W.card : ℝ) / 2) ^ 2 ≤ ‖lagSum W x‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hRx 2
    rw [hF]
    calc B * (W.card : ℝ) ^ 2 / 16 = B * (1 / 2) * (1 / 2) * ((W.card : ℝ) / 2) ^ 2 := by ring
      _ ≤ B * ψ₃ (B * (1 - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2 := by gcongr
  calc B * (W.card : ℝ) ^ 2 / (16 * ((1 + 2 * D) * K * T))
      = r * (B * (W.card : ℝ) ^ 2 / 16) := by
        rw [hr]
        field_simp
    _ = ∫ _x in Icc 1 (1 + r), B * (W.card : ℝ) ^ 2 / 16 := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring
    _ ≤ ∫ x in Icc 1 (1 + r), F x :=
        setIntegral_mono_on continuous_const.integrableOn_Icc hFi.integrableOn measurableSet_Icc
          hFlow
    _ ≤ ∫ x, F x := setIntegral_le_integral hFi (Filter.Eventually.of_forall hF0)
    _ = smoothedDensity ψ₁ ψ₂ ψ₃ B W 1 := by rw [smoothedDensity, h1₁, one_mul, hF]

/-! ### Lemma 8.4 -/

/-- `f ≥ 0` for nonnegative bumps and `B ≥ 0`. -/
theorem smoothedDensity_nonneg {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} (hn₁ : ∀ u, 0 ≤ ψ₁ u) (hn₂ : ∀ u, 0 ≤ ψ₂ u)
    (hn₃ : ∀ u, 0 ≤ ψ₃ u) {B : ℝ} (hB : 0 ≤ B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ smoothedDensity ψ₁ ψ₂ ψ₃ B W u :=
  mul_nonneg (hn₁ u) (integral_nonneg fun x => by
    have := hn₂ x
    have := hn₃ (B * (u - x))
    positivity)

/-- `f` is measurable. -/
theorem measurable_smoothedDensity {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} (hc₁ : Continuous ψ₁) (hc₂ : Continuous ψ₂)
    (hc₃ : Continuous ψ₃) (B : ℝ) (W : Finset ℝ) :
    Measurable (smoothedDensity ψ₁ ψ₂ ψ₃ B W) := by
  have hm₂ := hc₂.measurable
  have hm₃ := hc₃.measurable
  have hmR := measurable_lagSum W
  have hF : StronglyMeasurable fun p : ℝ × ℝ =>
      B * ψ₃ (B * (p.1 - p.2)) * ψ₂ p.2 * ‖lagSum W p.2‖ ^ 2 :=
    (by fun_prop : Measurable fun p : ℝ × ℝ =>
      B * ψ₃ (B * (p.1 - p.2)) * ψ₂ p.2 * ‖lagSum W p.2‖ ^ 2).stronglyMeasurable
  exact hc₁.measurable.mul (hF.integral_prod_right' (ν := volume)).measurable

/-- **Guth–Maynard Lemma 8.4 (Fourier decay of smoothenings of `R`), explicit form.**

Let `ψ₁, ψ₂, ψ₃` be smooth and nonnegative, `ψ₁, ψ₂` supported in `[A⁻¹, A]`, `ψ₃` compactly
supported, `ψ₁(1) = ψ₂(1) = ψ₃(0) = 1`, with `|ψ₁^{(i)}| ≤ D`, `∫|ψ₃^{(i)}| ≤ D` (`i ≤ j`) and
`|ψ₂'|, |ψ₃'| ≤ D`. Let `1 ≤ B ≤ KT` with `K, T ≥ 1`, and `W ⊂ [x₀, x₀ + T]`. If `S₀` bounds
`f(u) = ψ₁(u) ∫ B ψ₃(B(u − x)) ψ₂(x) |R(x)|² dx` from above, then for every `ξ`

`|ξ|^j |f̂(ξ)| ≤ (A + 16 D² (∫ψ₂)(1 + 2D)) K^j T^j S₀`.

With `D, ∫ψ₂, K ⪅ 1` (the paper's bumps and `B ⪅ T`) this is `f̂(ξ) ⪅_j (T/|ξ|)^j sup f`. -/
theorem guthMaynard_lemma84 {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} {A : ℝ} (hA : 1 ≤ A)
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) ψ₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) ψ₂) (h₃ : ContDiff ℝ (⊤ : ℕ∞) ψ₃)
    (hs₁ : ∀ u, u ∉ Icc A⁻¹ A → ψ₁ u = 0) (hs₂ : ∀ u, u ∉ Icc A⁻¹ A → ψ₂ u = 0)
    (hs₃ : HasCompactSupport ψ₃) (hn₁ : ∀ u, 0 ≤ ψ₁ u) (hn₂ : ∀ u, 0 ≤ ψ₂ u)
    (hn₃ : ∀ u, 0 ≤ ψ₃ u) (h1₁ : ψ₁ 1 = 1) (h1₂ : ψ₂ 1 = 1) (h0₃ : ψ₃ 0 = 1) {j : ℕ} {D : ℝ}
    (hd₁ : ∀ i ≤ j, ∀ u, |iteratedDeriv i ψ₁ u| ≤ D) (hd₂ : ∀ u, |deriv ψ₂ u| ≤ D)
    (hd₃ : ∀ i ≤ j, ∫ y, |iteratedDeriv i ψ₃ y| ≤ D) (hd₃' : ∀ u, |deriv ψ₃ u| ≤ D)
    {B K T x₀ : ℝ} (hB : 1 ≤ B) (hK : 1 ≤ K) (hT : 1 ≤ T) (hBT : B ≤ K * T) {W : Finset ℝ}
    (hW : ∀ t ∈ W, x₀ ≤ t ∧ t ≤ x₀ + T) {S₀ : ℝ}
    (hS₀ : ∀ u, smoothedDensity ψ₁ ψ₂ ψ₃ B W u ≤ S₀) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 (fun u => (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ)) ξ‖
      ≤ (A + 16 * D ^ 2 * (∫ x, ψ₂ x) * (1 + 2 * D)) * K ^ j * T ^ j * S₀ := by
  have hA0 : 0 < A := by linarith
  have hD : 0 ≤ D := (abs_nonneg _).trans (hd₂ 0)
  have hcs₁ : HasCompactSupport ψ₁ := HasCompactSupport.intro isCompact_Icc hs₁
  have hcs₂ : HasCompactSupport ψ₂ := HasCompactSupport.intro isCompact_Icc hs₂
  have hB0 : 0 < B := by linarith
  have hf0 : ∀ u, 0 ≤ smoothedDensity ψ₁ ψ₂ ψ₃ B W u :=
    smoothedDensity_nonneg hn₁ hn₂ hn₃ hB0.le W
  have hS0 : 0 ≤ S₀ := (hf0 1).trans (hS₀ 1)
  have hI₂ : 0 ≤ ∫ x, ψ₂ x := integral_nonneg hn₂
  have hC0 : 0 ≤ 16 * D ^ 2 * (∫ x, ψ₂ x) * (1 + 2 * D) := by positivity
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `j = 0`: `|f̂| ≤ ∫ f ≤ (A − A⁻¹) sup f`
    simp only [pow_zero, one_mul, mul_one]
    have hmeas := measurable_smoothedDensity h₁.continuous h₂.continuous h₃.continuous B W
    have hon : IntegrableOn (fun u => (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ)) (Icc A⁻¹ A) :=
      Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
        (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable (M := S₀)
        (Filter.Eventually.of_forall fun u => by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 u)]
          exact hS₀ u)
    have hzero : ∀ u, u ∉ Icc A⁻¹ A → (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ) = 0 := fun u hu => by
      simp [smoothedDensity, hs₁ u hu]
    have hFi : Integrable fun u => (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ) := by
      refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).mp hon
      by_contra hnot
      exact hu (hzero u hnot)
    have hAinv : A⁻¹ ≤ A := (inv_le_one_of_one_le₀ hA).trans hA
    have hL1 := GaloisForLFunctions.HTGeometry.integral_norm_le_of_forall_mem_Icc hAinv hFi
      hzero (M := S₀) fun t _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 t)]
        exact hS₀ t
    calc ‖𝓕 (fun u => (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ)) ξ‖
        ≤ ∫ u, ‖(smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ)‖ :=
          RHTower.norm_fourier_le_integral_norm_real _ ξ
      _ ≤ (A - A⁻¹) * S₀ := hL1
      _ ≤ (A + 16 * D ^ 2 * (∫ x, ψ₂ x) * (1 + 2 * D)) * S₀ := by
          have := inv_nonneg.mpr hA0.le
          exact mul_le_mul_of_nonneg_right (by linarith) hS0
  · -- `j ≥ 1`: the decay against the size of `f` at `1`
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hdec := pow_mul_norm_fourier_smoothedDensity_le h₁ hcs₁ h₂.continuous hcs₂ h₃ hs₃ hB0
      hd₁ hd₃ W ξ
    have hg : ∫ x, |ψ₂ x| * ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 * ∫ x, ψ₂ x := by
      rw [← integral_const_mul]
      refine integral_mono ((integrable_mul_norm_lagSum_sq h₂.continuous hcs₂ W).abs.congr
        (Filter.Eventually.of_forall fun x => ?_))
        ((h₂.continuous.integrable_of_hasCompactSupport hcs₂).const_mul _) fun x => ?_
      · simp only
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖lagSum W x‖ ^ 2)]
      · simp only
        rw [abs_of_nonneg (hn₂ x)]
        have h4 : ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2
        nlinarith [hn₂ x]
    have hdiff₂ : Differentiable ℝ ψ₂ := h₂.differentiable (by simp)
    have hdiff₃ : Differentiable ℝ ψ₃ := h₃.differentiable (by simp)
    have hlow := smoothedDensity_one_ge h₂.continuous hcs₂ h₃.continuous hs₃ hn₂ hn₃ h1₁ h1₂ h0₃
      hD (abs_sub_le_of_abs_deriv_le hdiff₂ hd₂) (abs_sub_le_of_abs_deriv_le hdiff₃ hd₃') hB0 hK
      hT hBT hW
    have hden : 0 < 16 * ((1 + 2 * D) * K * T) := by positivity
    have hW2 : B * (W.card : ℝ) ^ 2 ≤ 16 * ((1 + 2 * D) * K * T) * S₀ := by
      have h := hlow.trans (hS₀ 1)
      rw [div_le_iff₀ hden] at h
      linarith
    -- name the atoms
    obtain ⟨X, hX⟩ : ∃ X, X = ‖𝓕 (fun u => (smoothedDensity ψ₁ ψ₂ ψ₃ B W u : ℂ)) ξ‖ := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G, G = ∫ x, |ψ₂ x| * ‖lagSum W x‖ ^ 2 := ⟨_, rfl⟩
    obtain ⟨I₂, hI⟩ : ∃ I₂, I₂ = ∫ x, ψ₂ x := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = (W.card : ℝ) := ⟨_, rfl⟩
    rw [← hX, ← hG] at hdec
    rw [← hG, ← hI, ← hc] at hg
    rw [← hc] at hW2
    rw [← hX, ← hI]
    rw [← hI] at hI₂ hC0
    have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
    have hG0 : 0 ≤ G := by rw [hG]; exact integral_nonneg fun x => by positivity
    have h2pos : (0 : ℝ) < 2 ^ (j' + 1) := by positivity
    -- `2^j |ξ|^j X ≤ (2π|ξ|)^j X`
    have hstep1 : 2 ^ (j' + 1) * (|ξ| ^ (j' + 1) * X) ≤ (2 * Real.pi * |ξ|) ^ (j' + 1) * X := by
      rw [mul_pow, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hX0
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith [Real.pi_gt_three]) _
    -- `(1 + B)^j ≤ 2^j B^{j-1} B`
    have hstep2 : (1 + B) ^ (j' + 1) ≤ 2 ^ (j' + 1) * (B ^ j' * B) := by
      rw [← pow_succ, ← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hBj : B ^ j' ≤ (K * T) ^ j' := pow_le_pow_left₀ hB0.le hBT _
    have hmain : 2 ^ (j' + 1) * (|ξ| ^ (j' + 1) * X)
        ≤ 2 ^ (j' + 1) * (16 * D ^ 2 * I₂ * (1 + 2 * D) * K ^ (j' + 1) * T ^ (j' + 1) * S₀) := by
      calc 2 ^ (j' + 1) * (|ξ| ^ (j' + 1) * X)
          ≤ D * D * (1 + B) ^ (j' + 1) * G := hstep1.trans hdec
        _ ≤ D * D * (2 ^ (j' + 1) * (B ^ j' * B)) * (c ^ 2 * I₂) := by
            gcongr
        _ = D * D * 2 ^ (j' + 1) * B ^ j' * I₂ * (B * c ^ 2) := by ring
        _ ≤ D * D * 2 ^ (j' + 1) * (K * T) ^ j' * I₂ * (16 * ((1 + 2 * D) * K * T) * S₀) := by
            gcongr
        _ = 2 ^ (j' + 1) * (16 * D ^ 2 * I₂ * (1 + 2 * D) * K ^ (j' + 1) * T ^ (j' + 1) * S₀) := by
            ring
    have hfin := le_of_mul_le_mul_left hmain h2pos
    have hextra : 0 ≤ A * K ^ (j' + 1) * T ^ (j' + 1) * S₀ := by positivity
    calc |ξ| ^ (j' + 1) * X ≤ 16 * D ^ 2 * I₂ * (1 + 2 * D) * K ^ (j' + 1) * T ^ (j' + 1) * S₀ :=
          hfin
      _ ≤ (A + 16 * D ^ 2 * I₂ * (1 + 2 * D)) * K ^ (j' + 1) * T ^ (j' + 1) * S₀ := by
          nlinarith [hextra]

end

end RHTower.GuthMaynard
