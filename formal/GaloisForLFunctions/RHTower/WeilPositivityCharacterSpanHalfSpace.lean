import GaloisForLFunctions.RHTower.WeilPositivityImaginaryQuadraticConductorLaw

/-!
# The character-span half-space law for Weil positivity

With the archimedean term of `ζ`, consider weights in the real span of the von Mangoldt
functions of `ζ` and of two real primitive Dirichlet characters,
`Λ(n)(1 + t₁(χ₁(n) - 1) + t₂(χ₂(n) - 1))`.

* **Kernels** (`AllExpDecay`, `AllExpDecay.convolution`, `paperFT_convolution_of_allExpDecay`).
  Kernels decaying faster than every exponential are closed under convolution, and the transform
  of a convolution is the product of the transforms.  Every real primitive character has such a
  kernel radical for `L(s, χ)`, namely its theta axis kernel, even or odd
  (`exists_dirichlet_radical_kernel`).
* **Two zero configurations** (`weilAtomSymbol_not_nonneg_of_joint_radical₂`).  A kernel radical
  for two configurations turns an energy bound
  `2π(1 - t₁ - t₂) Re W_ζ + 2π t₁ Re W₁ + 2π t₂ Re W₂ - c₀ ∫ |h|²` with `c₀ > 0` into a violation.
* **Theorem** (`twoCharacterMix_weilAtomSymbol_not_nonneg`).  If
  `t₁ log q₁ + t₂ log q₂ > 0` and `t_i ≥ 0` whenever `χ_i` is odd, the weights violate Weil
  positivity.  The coefficients may have opposite signs, so the Weil-positive weights meet this
  span only inside the half-space `t₁ log q₁ + t₂ log q₂ ≤ 0`.  The tests use the kernel `Ψ₁ ⋆ Ψ₂`,
  radical for `ζ`, `L(s, χ₁)` and `L(s, χ₂)` at once.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Kernels decaying faster than every exponential, and their convolutions -/

/-- `Ψ` decays faster than every exponential. -/
def AllExpDecay (Ψ : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖Ψ u‖ ≤ C * Real.exp (-(B * |u|))

variable {Ψ Ψ₁ Ψ₂ : ℝ → ℂ}

theorem AllExpDecay.integrable_mul_exp (hΨ : AllExpDecay Ψ) (hc : Continuous Ψ) (c : ℝ) :
    Integrable fun u : ℝ => ‖Ψ u‖ * Real.exp (c * |u|) := by
  obtain ⟨C, hC0, hC⟩ := hΨ (|c| + 1) (by positivity)
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul C)
    (hc.norm.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖Ψ u‖ * Real.exp (c * |u|)
      ≤ C * Real.exp (-((|c| + 1) * |u|)) * Real.exp (c * |u|) :=
        mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le
    _ = C * Real.exp (-((|c| + 1) * |u|) + c * |u|) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ C * Real.exp (-1 * |u|) := by
        gcongr
        nlinarith [le_abs_self c, abs_nonneg u]

theorem AllExpDecay.superExpDecay (hΨ : AllExpDecay Ψ) (hc : Continuous Ψ) : SuperExpDecay Ψ :=
  ⟨hc, fun c => hΨ.integrable_mul_exp hc c⟩

theorem AllExpDecay.integrable (hΨ : AllExpDecay Ψ) (hc : Continuous Ψ) : Integrable Ψ := by
  have := hΨ.integrable_mul_exp hc 0
  simp only [zero_mul, Real.exp_zero, mul_one] at this
  exact (integrable_norm_iff hc.aestronglyMeasurable).mp this

theorem AllExpDecay.integrable_mul_cexp (hΨ : AllExpDecay Ψ) (hc : Continuous Ψ) (z : ℂ) :
    Integrable fun u : ℝ => Ψ u * Complex.exp (I * z * u) := by
  refine (hΨ.integrable_mul_exp hc |z.im|).mono' (hc.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
  rw [this]
  nlinarith [neg_abs_le (z.im * u), abs_mul z.im u, le_abs_self (z.im * u)]

theorem AllExpDecay.bounded (hΨ : AllExpDecay Ψ) : BddAbove (Set.range fun u => ‖Ψ u‖) := by
  obtain ⟨C, hC0, hC⟩ := hΨ 0 le_rfl
  refine ⟨C, ?_⟩
  rintro _ ⟨u, rfl⟩
  have := hC u
  simpa using this

/-- The convolution of two kernels decaying faster than every exponential does too. -/
theorem AllExpDecay.convolution (h₁ : AllExpDecay Ψ₁) (h₂ : AllExpDecay Ψ₂) :
    AllExpDecay (convolution Ψ₁ Ψ₂ (ContinuousLinearMap.mul ℝ ℂ) volume) := by
  intro B hB
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁ (B + 1) (by linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂ (B + 1) (by linarith)
  have hint := integrable_exp_neg_mul_abs_modSource (a := 1) one_pos
  refine ⟨C₁ * C₂ * ∫ v : ℝ, Real.exp (-1 * |v|), by positivity, fun u => ?_⟩
  rw [convolution_def]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ v : ℝ, ‖(ContinuousLinearMap.mul ℝ ℂ) (Ψ₁ v) (Ψ₂ (u - v))‖ ≤
      C₁ * C₂ * Real.exp (-(B * |u|)) * Real.exp (-1 * |v|) := by
    intro v
    simp only [ContinuousLinearMap.mul_apply', norm_mul]
    have hv := hC₁ v
    have huv := hC₂ (u - v)
    have htri : |u| ≤ |v| + |u - v| := by
      calc |u| = |v + (u - v)| := by congr 1; ring
        _ ≤ |v| + |u - v| := abs_add_le _ _
    calc ‖Ψ₁ v‖ * ‖Ψ₂ (u - v)‖
        ≤ (C₁ * Real.exp (-((B + 1) * |v|))) * (C₂ * Real.exp (-((B + 1) * |u - v|))) :=
          mul_le_mul hv huv (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * Real.exp (-((B + 1) * |v|) + -((B + 1) * |u - v|)) := by
          rw [Real.exp_add]; ring
      _ ≤ C₁ * C₂ * Real.exp (-(B * |u|) + -1 * |v|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            nlinarith [abs_nonneg v, abs_nonneg (u - v), mul_le_mul_of_nonneg_left htri hB]))
            (by positivity)
      _ = C₁ * C₂ * Real.exp (-(B * |u|)) * Real.exp (-1 * |v|) := by
          rw [Real.exp_add]; ring
  calc ∫ v : ℝ, ‖(ContinuousLinearMap.mul ℝ ℂ) (Ψ₁ v) (Ψ₂ (u - v))‖
      ≤ ∫ v : ℝ, C₁ * C₂ * Real.exp (-(B * |u|)) * Real.exp (-1 * |v|) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hint.const_mul _) (Eventually.of_forall hpt)
    _ = C₁ * C₂ * (∫ v : ℝ, Real.exp (-1 * |v|)) * Real.exp (-(B * |u|)) := by
        rw [integral_const_mul]; ring

theorem continuous_convolution_of_allExpDecay (h₁ : AllExpDecay Ψ₁) (h₂ : AllExpDecay Ψ₂)
    (hc₁ : Continuous Ψ₁) (hc₂ : Continuous Ψ₂) :
    Continuous (convolution Ψ₁ Ψ₂ (ContinuousLinearMap.mul ℝ ℂ) volume) :=
  h₁.bounded.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℝ ℂ) hc₁
    (h₂.integrable hc₂)

theorem paperFT_convolution_of_allExpDecay (h₁ : AllExpDecay Ψ₁) (h₂ : AllExpDecay Ψ₂)
    (hc₁ : Continuous Ψ₁) (hc₂ : Continuous Ψ₂) (z : ℂ) :
    paperFT (convolution Ψ₁ Ψ₂ (ContinuousLinearMap.mul ℝ ℂ) volume) z =
      paperFT Ψ₁ z * paperFT Ψ₂ z :=
  paperFT_convolution (h₁.integrable_mul_cexp hc₁ z) (h₂.integrable_mul_cexp hc₂ z)

/-! ### The radical kernel of a real primitive character -/

variable {q : ℕ} [NeZero q]

/-- Every real primitive character mod `q > 1` has a continuous kernel decaying faster than every
exponential whose transform vanishes at the zeros of `L(s, χ)` and not at `-3i/4`. -/
theorem exists_dirichlet_radical_kernel (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : ∃ Ψ : ℝ → ℂ, Continuous Ψ ∧ AllExpDecay Ψ ∧
      (∀ ρ : (dirichletZeros hq hprim).carrier, paperFT Ψ (gammaOf ρ) = 0) ∧
      paperFT Ψ (-(3 / 4 * I)) ≠ 0 := by
  have hχ := ne_one_of_isPrimitive hq hprim
  rcases χ.even_or_odd with heven | hodd
  · exact ⟨dirichletAxisKernel χ, continuous_dirichletAxisKernel χ,
      fun B hB => exists_norm_dirichletAxisKernel_le hq hχ hB,
      fun ρ => paperFT_dirichletAxisKernel_gammaOf_eq_zero hq hχ heven ρ.2,
      paperFT_dirichletAxisKernel_ne_zero hq hχ heven⟩
  · exact ⟨dirichletOddAxisKernel χ, continuous_dirichletOddAxisKernel χ,
      fun B hB => exists_norm_dirichletOddAxisKernel_le χ hB,
      fun ρ => paperFT_dirichletOddAxisKernel_gammaOf_eq_zero hq hodd ρ.2,
      paperFT_dirichletOddAxisKernel_ne_zero hq hodd⟩

theorem strip_dirichletZeros (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive)
    (ρ : (dirichletZeros hq hprim).carrier) : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
  have h : Zeta23.ThmE.IsNontrivialZeroL χ (ρ : ℂ) := ρ.2
  exact ⟨h.2.1, h.2.2⟩

/-- **Twisted energy bound for a real character.**  For `t ≥ 0` when `χ` is odd, the energy of the
twisted weights `Λ Re χ`, scaled by `t`, is at most `t (2π Re W_χ - log q ∫ |h|²)`. -/
theorem mul_integral_weilAtomSymbol_realChar_le (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) {t : ℝ} (ht : χ.Odd → 0 ≤ t)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    t * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re)
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) ≤
      t * (2 * π * ((dirichletZeros hq hprim).W f f).re -
        Real.log q * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) := by
  rcases χ.even_or_odd with heven | hodd
  · rw [integral_weilAtomSymbol_dirichlet hq hprim heven hreal ha hf hfs]
  · rw [integral_weilAtomSymbol_dirichlet_odd hq hprim hodd hreal ha hf hfs]
    have hJ : 0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (π / Real.cosh (π * τ)) :=
      integral_nonneg fun τ => mul_nonneg (sq_nonneg _)
        (div_nonneg Real.pi_pos.le (Real.cosh_pos _).le)
    have := ht hodd
    nlinarith

/-! ### Joint radical tests for two zero configurations -/

/-- **The generic two-tilt violation.**  If a kernel is radical for two zero configurations and the
energy of the weights is at most `2π(1 - t₁ - t₂) Re W_ζ + 2π t₁ Re W₁ + 2π t₂ Re W₂ - c₀ ∫ |h|²`
with `c₀ > 0`, then Weil positivity fails. -/
theorem weilAtomSymbol_not_nonneg_of_joint_radical₂ (Z₁ Z₂ : ZeroConfig)
    (hZs₁ : Summable fun ρ : Z₁.carrier => (Z₁.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))
    (hZs₂ : Summable fun ρ : Z₂.carrier => (Z₂.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))
    (hZstrip₁ : ∀ ρ : Z₁.carrier, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1)
    (hZstrip₂ : ∀ ρ : Z₂.carrier, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1)
    {Ψ : ℝ → ℂ} (hΨs : SuperExpDecay Ψ) {CΨ : ℝ} (hCΨ : 0 ≤ CΨ)
    (hΨd : ∀ u, ‖Ψ u‖ ≤ CΨ * Real.exp (-|u|))
    (hΨz₁ : ∀ ρ : Z₁.carrier, paperFT Ψ (gammaOf ρ) = 0)
    (hΨz₂ : ∀ ρ : Z₂.carrier, paperFT Ψ (gammaOf ρ) = 0) (hΨ0 : paperFT Ψ (-(3 / 4 * I)) ≠ 0)
    (lam : ℕ → ℝ) {t₁ t₂ c₀ : ℝ} (hc₀ : 0 < c₀)
    (henergy : ∀ R : ℝ, 1 ≤ R →
      ∫ τ : ℝ, ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2 * weilAtomSymbol lam
        ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π)) ≤
      2 * π * (1 - t₁ - t₂) * (zetaZeroConfig.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re +
        2 * π * t₁ * (Z₁.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re +
        2 * π * t₂ * (Z₂.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re -
        c₀ * ∫ τ : ℝ, ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  have hΨc : Continuous Ψ := hΨs.1
  obtain ⟨c, R₀, hc, hR₀, hmass⟩ := exists_integral_normSq_jointRadicalTest_ge hΨs hΨ0 hCΨ hΨd
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_zeta_jointRadicalTest_le hΨc hΨd
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_W_jointRadicalTest_le Z₁ hZs₁ hZstrip₁ hΨc hCΨ hΨd hΨz₁
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_W_jointRadicalTest_le Z₂ hZs₂ hZstrip₂ hΨc hCΨ hΨd hΨz₂
  set M := 2 * π * |1 - t₁ - t₂| * KW + 2 * π * |t₁| * K₁ + 2 * π * |t₂| * K₂ with hM
  have hM0 : 0 ≤ M := by positivity
  have hlim : Tendsto (fun R : ℝ => M * (R * Real.exp (-(R / 2)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 := (h.const_mul 2).const_mul M
    simp only [mul_zero] at h2
    refine h2.congr fun R => ?_
    simp only [Function.comp_apply, id, pow_one]; ring
  obtain ⟨R, hRsmall, hRbig⟩ := ((hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < c₀ * c))).and (eventually_ge_atTop R₀)).exists
  have hR1 : 1 ≤ R := hR₀.trans hRbig
  refine ⟨5 * R, by linarith, jointRadicalTest Ψ R, contDiff_jointRadicalTest hΨc R,
    tsupport_jointRadicalTest Ψ R, paperFT_jointRadicalTest_half_I hΨc R,
    paperFT_jointRadicalTest_neg_half_I hΨc R, ?_⟩
  refine lt_of_le_of_lt (henergy R hR1) ?_
  set g := jointRadicalTest Ψ R with hg
  have bnd : ∀ (x : ℝ) (W : ℂ) (K : ℝ), ‖W‖ ≤ K * (R * Real.exp (-(R / 2))) →
      2 * π * x * W.re ≤ 2 * π * |x| * (K * (R * Real.exp (-(R / 2)))) := by
    intro x W K hW
    have hπ : 0 ≤ 2 * π := by positivity
    calc 2 * π * x * W.re ≤ |2 * π * x * W.re| := le_abs_self _
      _ = 2 * π * |x| * |W.re| := by rw [abs_mul, abs_mul, abs_of_nonneg hπ]
      _ ≤ 2 * π * |x| * (K * (R * Real.exp (-(R / 2)))) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hW) (by positivity)
  have e0 := bnd (1 - t₁ - t₂) _ _ (hKW R hR1)
  have e1 := bnd t₁ _ _ (hK₁ R hR1)
  have e2 := bnd t₂ _ _ (hK₂ R hR1)
  have hm := hmass R hRbig
  have hsum : 2 * π * |1 - t₁ - t₂| * (KW * (R * Real.exp (-(R / 2)))) +
      2 * π * |t₁| * (K₁ * (R * Real.exp (-(R / 2)))) +
      2 * π * |t₂| * (K₂ * (R * Real.exp (-(R / 2)))) = M * (R * Real.exp (-(R / 2))) := by
    rw [hM]; ring
  have hcm : c₀ * c ≤ c₀ * ∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 := mul_le_mul_of_nonneg_left hm hc₀.le
  linarith

/-! ### Two real characters -/

omit [NeZero q] in
theorem weilAtomSymbol_twoCharacterMix {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (t₁ t₂ : ℝ) (N : ℕ) (ξ : ℝ) :
    weilAtomSymbol (fun n => ArithmeticFunction.vonMangoldt n *
        (1 + t₁ * ((χ₁ (n : ZMod q₁)).re - 1) + t₂ * ((χ₂ (n : ZMod q₂)).re - 1))) N ξ =
      (1 - t₁ - t₂) * weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N ξ +
        t₁ * weilAtomSymbol (fun n => ArithmeticFunction.vonMangoldt n * (χ₁ (n : ZMod q₁)).re)
          N ξ +
        t₂ * weilAtomSymbol (fun n => ArithmeticFunction.vonMangoldt n * (χ₂ (n : ZMod q₂)).re)
          N ξ := by
  unfold weilAtomSymbol
  rw [mul_sub, mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have : ∀ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n *
      (1 + t₁ * ((χ₁ (n : ZMod q₁)).re - 1) + t₂ * ((χ₂ (n : ZMod q₂)).re - 1)) *
      (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) =
      (1 - t₁ - t₂) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * ξ))) +
      t₁ * (ArithmeticFunction.vonMangoldt n * (χ₁ (n : ZMod q₁)).re * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * ξ))) +
      t₂ * (ArithmeticFunction.vonMangoldt n * (χ₂ (n : ZMod q₂)).re * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * ξ))) := fun n _ => by ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- **The character-span half-space law.**  Let `χ₁, χ₂` be real primitive Dirichlet characters
of moduli `q₁, q₂ > 1`, and let `t₁, t₂` be real with `t₁ log q₁ + t₂ log q₂ > 0` and `t_i ≥ 0`
whenever `χ_i` is odd.  Then the weights `Λ(n)(1 + t₁(χ₁(n) - 1) + t₂(χ₂(n) - 1))` violate Weil
positivity with the archimedean term of `ζ`.

The coefficients may have opposite signs: weighting one quadratic splitting law up and another down
fails as soon as the conductor-weighted balance `t₁ log q₁ + t₂ log q₂` is positive.  The tests are
radical for `ζ`, `L(s, χ₁)` and `L(s, χ₂)` at once (kernel `Ψ₁ ⋆ Ψ₂`), so all three zero sides
vanish in the limit and the energy is `-(t₁ log q₁ + t₂ log q₂) ∫ |h|² + o(1)` or less. -/
theorem twoCharacterMix_weilAtomSymbol_not_nonneg {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hq₁ : 1 < q₁) (hq₂ : 1 < q₂) {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hprim₁ : χ₁.IsPrimitive) (hprim₂ : χ₂.IsPrimitive)
    (hreal₁ : ∀ a : ZMod q₁, (χ₁ a).im = 0) (hreal₂ : ∀ a : ZMod q₂, (χ₂ a).im = 0)
    {t₁ t₂ : ℝ} (hodd₁ : χ₁.Odd → 0 ≤ t₁) (hodd₂ : χ₂.Odd → 0 ≤ t₂)
    (hpos : 0 < t₁ * Real.log q₁ + t₂ * Real.log q₂) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n *
          (1 + t₁ * ((χ₁ (n : ZMod q₁)).re - 1) + t₂ * ((χ₂ (n : ZMod q₂)).re - 1)))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  obtain ⟨Ψ₁, hc₁, hd₁, hz₁, hn₁⟩ := exists_dirichlet_radical_kernel hq₁ hprim₁
  obtain ⟨Ψ₂, hc₂, hd₂, hz₂, hn₂⟩ := exists_dirichlet_radical_kernel hq₂ hprim₂
  set Ψ := convolution Ψ₁ Ψ₂ (ContinuousLinearMap.mul ℝ ℂ) volume with hΨ
  have hΨall : AllExpDecay Ψ := hd₁.convolution hd₂
  have hΨc : Continuous Ψ := continuous_convolution_of_allExpDecay hd₁ hd₂ hc₁ hc₂
  have hΨs : SuperExpDecay Ψ := hΨall.superExpDecay hΨc
  obtain ⟨CΨ, hCΨ, hΨd⟩ := hΨall 1 zero_le_one
  have hΨd' : ∀ u, ‖Ψ u‖ ≤ CΨ * Real.exp (-|u|) := fun u => by simpa using hΨd u
  have hFT : ∀ z, paperFT Ψ z = paperFT Ψ₁ z * paperFT Ψ₂ z :=
    paperFT_convolution_of_allExpDecay hd₁ hd₂ hc₁ hc₂
  refine weilAtomSymbol_not_nonneg_of_joint_radical₂ (dirichletZeros hq₁ hprim₁)
    (dirichletZeros hq₂ hprim₂) (summable_dirichletZeros hq₁ hprim₁)
    (summable_dirichletZeros hq₂ hprim₂) (strip_dirichletZeros hq₁ hprim₁)
    (strip_dirichletZeros hq₂ hprim₂) hΨs hCΨ hΨd'
    (fun ρ => by rw [hFT, hz₁ ρ, zero_mul]) (fun ρ => by rw [hFT, hz₂ ρ, mul_zero])
    (by rw [hFT]; exact mul_ne_zero hn₁ hn₂) _ (t₁ := t₁) (t₂ := t₂) hpos (fun R hR => ?_)
  set f := jointRadicalTest Ψ R with hf
  have hfd : ContDiff ℝ 2 f := contDiff_jointRadicalTest hΨc R
  have hfs : tsupport f ⊆ Icc (-(5 * R)) (5 * R) := tsupport_jointRadicalTest Ψ R
  have ha : (0 : ℝ) ≤ 5 * R := by linarith
  have hp := paperFT_jointRadicalTest_half_I hΨc R
  have hm := paperFT_jointRadicalTest_neg_half_I hΨc R
  have hΛ := integrable_normSq_paperFT_mul_weilAtomSymbol hfd hfs
  have i₁ := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs
    (fun n => ArithmeticFunction.vonMangoldt n * (χ₁ (n : ZMod q₁)).re)
  have i₂ := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs
    (fun n => ArithmeticFunction.vonMangoldt n * (χ₂ (n : ZMod q₂)).re)
  have hpt : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
      (fun n => ArithmeticFunction.vonMangoldt n *
        (1 + t₁ * ((χ₁ (n : ZMod q₁)).re - 1) + t₂ * ((χ₂ (n : ZMod q₂)).re - 1)))
      ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π)) =
      (1 - t₁ - t₂) * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π))) +
      t₁ * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ₁ (n : ZMod q₁)).re)
        ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π))) +
      t₂ * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ₂ (n : ZMod q₂)).re)
        ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π))) := by
    intro τ; rw [weilAtomSymbol_twoCharacterMix]; ring
  have iA : Integrable fun τ : ℝ => (1 - t₁ - t₂) * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π))) +
      t₁ * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ₁ (n : ZMod q₁)).re)
        ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π))) :=
    (hΛ.const_mul _).add (i₁.const_mul _)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add iA (i₂.const_mul _),
    integral_add (hΛ.const_mul _) (i₁.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hfd hfs hp hm
  have hWre : 2 * π * (zetaZeroConfig.W f f).re = ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π)) := by
    rw [hW, Complex.ofReal_re]
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  have b₁ := mul_integral_weilAtomSymbol_realChar_le hq₁ hprim₁ hreal₁ hodd₁ ha hfd hfs
  have b₂ := mul_integral_weilAtomSymbol_realChar_le hq₂ hprim₂ hreal₂ hodd₂ ha hfd hfs
  rw [← hWre]
  nlinarith [b₁, b₂]

end RHTower
