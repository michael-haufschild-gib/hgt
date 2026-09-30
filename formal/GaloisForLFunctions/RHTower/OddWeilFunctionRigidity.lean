import GaloisForLFunctions.RHTower.ZetaMassSublinearRigidity

/-!
# Rigidity of odd Weil functions through Hamburger's theorem

An *odd Weil function* (`OddWeilFunction`) is holomorphic on `Re s > ½`, odd under `s ↦ 1 − s`, and
of polynomial growth at distance between `¼` and `1` from the critical line.  Every atomic or
measure-valued Cauchy transform on the critical line is one.

Let `Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = Φ(s)` on `Re s > 1`, with `Γ̃ = Γ_ℝ'/Γ_ℝ + 1/s`.

* The theta series of `a = 1 ⋆ (lam − Λ)` satisfies
  `θ(x) = −x^{−½} θ(1/x) + β + β x^{−½} + K(x)`, where `β = (Λ₀(1) − Φ(1))/2` and `K` is the
  thin-strip defect of `Λ Φ` between `Re s = ¾` and `Re s = ¼` (`coeffTheta_weil_defect_relation`).
* If a holomorphic continuation `J` of the Laplace transform `τ ∫ K(x) e^{−πτ²x} dx` to `Re τ > 0`
  satisfies `ε J(ε + im) → 0` as `ε → 0⁺` for every `m ≥ 0`, then `lam(n) = Λ(n)` for `n ≥ 2` and the
  Riemann hypothesis holds (`weil_defect_rigidity`).
* Parametric integrals of holomorphic functions with locally integrable bounds are holomorphic
  (`differentiableOn_integral_of_locally_bounded`), via the Cauchy estimate.
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

/-- An odd Weil function: holomorphic on `Re s > ½`, odd under `s ↦ 1 − s`, and of polynomial
growth `B (|Im w| + 1)³` at distance between `¼` and `1` from the critical line. -/
structure OddWeilFunction (Φ : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re}
  one_sub : ∀ s : ℂ, Φ (1 - s) = -Φ s
  growth : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 1 / 4 ≤ |w.re - 1 / 2| → |w.re - 1 / 2| ≤ 1 →
    ‖Φ w‖ ≤ B * (|w.im| + 1) ^ 3

/-- The residue weight `β = (Λ₀(1) − Φ(1))/2`. -/
noncomputable def weilResidue (Φ : ℂ → ℂ) : ℂ :=
  (completedRiemannZeta₀ 1 - Φ 1) / 2

/-- `Λ ξ'/ξ − Λ Φ − β Γ_ℝ(s − 1)`, before removing its singularity at `1`. -/
noncomputable def weilRemainderRaw (Φ : ℂ → ℂ) (s : ℂ) : ℂ :=
  completedZetaXiLogDeriv s - completedRiemannZeta s * Φ s - weilResidue Φ * Gammaℝ (s - 1)

/-- The remainder with its removable singularity at `1` filled. -/
noncomputable def weilRemainder (Φ : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (weilRemainderRaw Φ) 1 (limUnder (𝓝[≠] 1) (weilRemainderRaw Φ))

theorem OddWeilFunction.continuousAt_off_line {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ) {s : ℂ}
    (hs : s.re ≠ 1 / 2) : ContinuousAt Φ s := by
  rcases lt_or_gt_of_ne hs with h | h
  · have h1 : 1 / 2 < (1 - s).re := by simp; linarith
    have hd : ContinuousAt Φ (1 - s) :=
      (hΦ.differentiableOn.differentiableAt ((isOpen_re_gt _).mem_nhds h1)).continuousAt
    have hcomp : ContinuousAt (fun z => -Φ (1 - z)) s :=
      (hd.comp (f := fun z : ℂ => 1 - z) (by fun_prop)).neg
    refine hcomp.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [hΦ.one_sub, neg_neg]
  · exact (hΦ.differentiableOn.differentiableAt ((isOpen_re_gt _).mem_nhds h)).continuousAt

theorem tendsto_sub_one_mul_weilRemainderRaw {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ) :
    Tendsto (fun z => (z - 1) * weilRemainderRaw Φ z) (𝓝[≠] 1) (𝓝 0) := by
  set β := weilResidue Φ with hβ
  set H : ℂ → ℂ := fun z => (z - 1) * (deriv completedRiemannZeta₀ z +
      completedRiemannZeta₀ z * (1 / z)) + completedRiemannZeta₀ z -
      ((z - 1) * (completedRiemannZeta₀ z - 1 / z) + 1) * Φ z -
      β * (2 * ((Real.pi : ℂ) ^ (-(z - 1) / 2) * Gamma ((z - 1) / 2 + 1))) with hHdef
  have hH1 : H 1 = 0 := by
    simp only [hHdef, hβ, weilResidue, sub_self, zero_mul, zero_add, neg_zero, zero_div,
      cpow_zero, one_mul, Complex.Gamma_one]
    ring
  have hG : DifferentiableAt ℂ Gamma (((1 : ℂ) - 1) / 2 + 1) := by
    apply differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    simp at this; linarith
  have hΦc : ContinuousAt Φ 1 :=
    (hΦ.differentiableOn.differentiableAt ((isOpen_re_gt _).mem_nhds (by norm_num))).continuousAt
  have hL0 : Continuous completedRiemannZeta₀ := differentiable_completedZeta₀.continuous
  have hdL0 : Continuous (deriv completedRiemannZeta₀) :=
    differentiable_deriv_completedRiemannZeta₀.continuous
  have hinv : ContinuousAt (fun z : ℂ => 1 / z) 1 :=
    continuousAt_const.div continuousAt_id one_ne_zero
  have hpow : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z - 1) / 2)) 1 :=
    (DifferentiableAt.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))).continuousAt
  have hgam : ContinuousAt (fun z : ℂ => Gamma ((z - 1) / 2 + 1)) 1 :=
    hG.continuousAt.comp (f := fun z : ℂ => (z - 1) / 2 + 1) (by fun_prop)
  have hsub : ContinuousAt (fun z : ℂ => z - 1) 1 := by fun_prop
  have hHc : ContinuousAt H 1 := by
    refine (((hsub.mul (hdL0.continuousAt.add (hL0.continuousAt.mul hinv))).add
      hL0.continuousAt).sub (((hsub.mul (hL0.continuousAt.sub hinv)).add continuousAt_const).mul
      hΦc)).sub (continuousAt_const.mul (continuousAt_const.mul (hpow.mul hgam)))
  have hev : (fun z => (z - 1) * weilRemainderRaw Φ z) =ᶠ[𝓝[≠] 1] H := by
    filter_upwards [self_mem_nhdsWithin] with z hz1
    have hz1' : z ≠ 1 := hz1
    have hΓ := sub_one_mul_Gammaℝ_sub_one hz1'
    have e1 : (z - 1) * (1 / (z - 1)) = 1 := by
      field_simp [sub_ne_zero.mpr hz1']
    have e2 : (z - 1) * (1 / (1 - z)) = -1 := by
      rw [show (1 : ℂ) - z = -(z - 1) by ring, div_neg]
      field_simp [sub_ne_zero.mpr hz1']
    simp only [weilRemainderRaw, completedZetaXiLogDeriv, completedRiemannZeta_eq, hHdef]
    rw [← hβ]
    linear_combination completedRiemannZeta₀ z * e1 + Φ z * e2 - β * hΓ
  have := hHc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  rw [hH1] at this
  exact this.congr' hev.symm

theorem differentiableOn_weilRemainder {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ) :
    DifferentiableOn ℂ (weilRemainder Φ) {s : ℂ | 1 / 2 < s.re} := by
  have hU : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) := (isOpen_re_gt _).mem_nhds (by norm_num)
  refine differentiableOn_update_limUnder_of_isLittleO hU ?_ ?_
  · intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hs0' : 1 / 2 < s.re := hs0
    have hne0 : s ≠ 0 := by intro h0; rw [h0] at hs0'; simp at hs0'; linarith
    have hne1 : s ≠ 1 := by simpa using hs1
    have hreg : s ∈ zetaRegular := by
      simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hne0, hne1⟩
    refine DifferentiableAt.differentiableWithinAt ?_
    have hG := differentiableAt_Gammaℝ_sub_one (by linarith) hne1
    exact ((differentiableAt_completedZetaXiLogDeriv hne0 hne1).sub
      ((differentiableOn_completedRiemannZeta_regular.differentiableAt
        (isOpen_zetaRegular.mem_nhds hreg)).mul
        (hΦ.differentiableOn.differentiableAt ((isOpen_re_gt _).mem_nhds hs0')))).sub
      ((differentiableAt_const _).mul hG)
  · rw [Asymptotics.isLittleO_iff_tendsto']
    · have h1 := tendsto_sub_one_mul_weilRemainderRaw hΦ
      have h2 : Tendsto (fun z : ℂ => (z - 1) * weilRemainderRaw Φ 1) (𝓝[≠] 1) (𝓝 0) := by
        have : Tendsto (fun z : ℂ => (z - 1) * weilRemainderRaw Φ 1) (𝓝 1)
            (𝓝 ((1 - 1) * weilRemainderRaw Φ 1)) :=
          ((continuous_id.sub continuous_const).mul continuous_const).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      have := h1.sub h2
      rw [sub_zero] at this
      refine this.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
      dsimp only
      rw [div_inv_eq_mul]
      ring
    · exact eventually_nhdsWithin_of_forall fun z hz h0 =>
        absurd h0 (inv_ne_zero (sub_ne_zero.mpr hz))

theorem exists_decay_completedRiemannZeta_mul_weil {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 3 / 4 ≤ w.re → w.re ≤ 3 / 2 → 4 ≤ |w.im| →
      ‖completedRiemannZeta w * Φ w‖ ≤ C / (1 + w.im ^ 2) := by
  obtain ⟨CΛ, N, hCΛ, hΛ⟩ := exists_bound_completedRiemannZeta_strip
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (N + 3 + 2)
  obtain ⟨B, hB0, hB⟩ := hΦ.growth
  refine ⟨CΛ * B * K, by positivity, fun w h1 h2 h3 => ?_⟩
  set τ := |w.im| with hτ
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hΛw := hΛ w (by linarith) (by linarith) (by linarith)
  have hΦw := hB w (by rw [abs_of_nonneg (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hK' := pow_mul_exp_neg_le_div hK hτ0
  rw [hτ, sq_abs] at hK'
  have hp1 : τ ^ N ≤ (τ + 4) ^ N := pow_le_pow_left₀ hτ0 (by linarith) N
  have hp2 : (τ + 1) ^ 3 ≤ (τ + 4) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  rw [norm_mul]
  calc ‖completedRiemannZeta w‖ * ‖Φ w‖
      ≤ (CΛ * τ ^ N * Real.exp (-(Real.pi * τ / 4))) * (B * (τ + 1) ^ 3) :=
        mul_le_mul hΛw hΦw (norm_nonneg _) (by positivity)
    _ ≤ (CΛ * (τ + 4) ^ N * Real.exp (-(Real.pi * τ / 4))) * (B * (τ + 4) ^ 3) := by gcongr
    _ = CΛ * B * ((τ + 4) ^ (N + 3) * Real.exp (-(Real.pi * τ / 4))) := by ring
    _ ≤ CΛ * B * (K / (1 + w.im ^ 2)) := by gcongr
    _ = _ := by ring

theorem exists_decay_weilRemainder {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ) :
    ∃ C : ℝ, ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (3 / 4) (3 / 2),
      ‖weilRemainder Φ s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_decay_completedZetaXiLogDeriv
  obtain ⟨C₂, hC₂, h₂⟩ := exists_decay_completedRiemannZeta_mul_weil hΦ
  obtain ⟨C₃, hC₃, h₃⟩ := exists_decay_Gammaℝ_sub_one
  set K : Set ℂ := Set.Icc (3 / 4 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4 with hKdef
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro z hz
    rw [hKdef, Complex.mem_reProdIm] at hz
    show 1 / 2 < z.re
    linarith [hz.1.1]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    ((differentiableOn_weilRemainder hΦ).continuousOn.mono hsub)
  set β := weilResidue Φ
  refine ⟨max (17 * max M 0) (C₁ + C₂ + ‖β‖ * C₃), fun s hs => ?_⟩
  rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hs
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  by_cases hbig : 4 ≤ |s.im|
  · have hs1 : s ≠ 1 := by intro h0; rw [h0] at hbig; norm_num at hbig
    rw [weilRemainder, Function.update_of_ne hs1, weilRemainderRaw]
    calc ‖completedZetaXiLogDeriv s - completedRiemannZeta s * Φ s - β * Gammaℝ (s - 1)‖
        ≤ ‖completedZetaXiLogDeriv s‖ + ‖completedRiemannZeta s * Φ s‖ +
            ‖β‖ * ‖Gammaℝ (s - 1)‖ := by
          rw [← norm_mul]
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ C₁ / (1 + s.im ^ 2) + C₂ / (1 + s.im ^ 2) + ‖β‖ * (C₃ / (1 + s.im ^ 2)) := by
          gcongr
          · exact h₁ s (by linarith [hs.1]) hs.2 hbig
          · exact h₂ s hs.1 hs.2 hbig
          · exact h₃ s (by linarith [hs.1]) hs.2 hbig
      _ = (C₁ + C₂ + ‖β‖ * C₃) / (1 + s.im ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · push Not at hbig
    have hsK : s ∈ K := by
      rw [hKdef, Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, (abs_le.mp hbig.le)⟩
    have hb := (hM s hsK).trans (le_max_left M 0)
    have hsq : s.im ^ 2 ≤ 16 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    calc ‖weilRemainder Φ s‖ ≤ max M 0 := hb
      _ ≤ 17 * max M 0 / (1 + s.im ^ 2) := by
          rw [le_div_iff₀ hden]
          nlinarith [le_max_right M 0]
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- `x^{-w} Λ(2w) Φ(2w)` is integrable along `Re w = 3/8` and `Re w = 1/8`. -/
theorem integrable_cpow_mul_completedRiemannZeta_mul_weil {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ)
    {σ x : ℝ} (hx : 0 < x) (hσ : σ = 3 / 8 ∨ σ = 1 / 8) :
    Integrable fun τ : ℝ => (x : ℂ) ^ (-((σ : ℂ) + τ * I)) *
      (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) * Φ (2 * ((σ : ℂ) + τ * I))) := by
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := exists_bound_completedRiemannZeta_mul_cube
  obtain ⟨B, hB0, hB⟩ := hΦ.growth
  have hre : ∀ τ : ℝ, (2 * ((σ : ℂ) + τ * I)).re = 2 * σ := by intro τ; simp
  have him : ∀ τ : ℝ, (2 * ((σ : ℂ) + τ * I)).im = 2 * τ := by intro τ; simp
  have h2σ : 2 * σ = 3 / 4 ∨ 2 * σ = 1 / 4 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hl1 : 1 / 4 ≤ |2 * σ - 1 / 2| := by
    rcases h2σ with h | h <;> rw [h] <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  have hl2 : |2 * σ - 1 / 2| ≤ 1 := by
    rcases h2σ with h | h <;> rw [h] <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  have hl3 : 1 / 4 ≤ 2 * σ := by rcases h2σ with h | h <;> linarith
  have hl4 : 2 * σ ≤ 3 / 4 := by rcases h2σ with h | h <;> linarith
  have hreg : ∀ τ : ℝ, 2 * ((σ : ℂ) + τ * I) ∈ zetaRegular := by
    intro τ
    simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
    · intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hcont : Continuous fun τ : ℝ => (x : ℂ) ^ (-((σ : ℂ) + τ * I)) *
      (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) * Φ (2 * ((σ : ℂ) + τ * I))) := by
    refine Continuous.mul (Continuous.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast hx.ne'))) (Continuous.mul ?_ ?_)
    · rw [continuous_iff_continuousAt]
      intro τ
      exact (differentiableOn_completedRiemannZeta_regular.differentiableAt
        (isOpen_zetaRegular.mem_nhds (hreg τ))).continuousAt.comp
        (f := fun τ : ℝ => 2 * ((σ : ℂ) + τ * I)) (by fun_prop)
    · rw [continuous_iff_continuousAt]
      intro τ
      have hoff : (2 * ((σ : ℂ) + τ * I)).re ≠ 1 / 2 := by
        rw [hre]; rcases h2σ with h | h <;> rw [h] <;> norm_num
      exact (hΦ.continuousAt_off_line hoff).comp
        (f := fun τ : ℝ => 2 * ((σ : ℂ) + τ * I)) (by fun_prop)
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (x ^ (-σ) * (B * CΛ)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  have hΦb := hB (2 * ((σ : ℂ) + τ * I)) (by rw [hre]; exact hl1) (by rw [hre]; exact hl2)
  have hΛ := hCΛ (2 * ((σ : ℂ) + τ * I)) (by rw [hre]; exact hl3) (by rw [hre]; exact hl4)
  rw [him] at hΦb hΛ
  have hden : 1 + τ ^ 2 ≤ 1 + (2 * τ) ^ 2 := by nlinarith
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre' : (-((σ : ℂ) + τ * I)).re = -σ := by simp
  rw [hre']
  calc x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
        ‖Φ (2 * ((σ : ℂ) + τ * I))‖)
      ≤ x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
          (B * (|2 * τ| + 1) ^ 3)) := by gcongr
    _ = x ^ (-σ) * B *
          (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ * (|2 * τ| + 1) ^ 3) := by ring
    _ ≤ x ^ (-σ) * B * (CΛ / (1 + (2 * τ) ^ 2)) := by gcongr
    _ ≤ x ^ (-σ) * B * (CΛ / (1 + τ ^ 2)) := by gcongr
    _ = x ^ (-σ) * (B * CΛ) * (1 + τ ^ 2)⁻¹ := by ring

/-- The thin-strip defect of an odd Weil function:
`K(x) = −(1/2π)[∫ x^{-(3/8+iτ)} Λ Φ(¾ + 2iτ) dτ − ∫ x^{-(1/8+iτ)} Λ Φ(¼ + 2iτ) dτ]`. -/
noncomputable def weilDefect (Φ : ℂ → ℂ) (x : ℝ) : ℂ :=
  -((1 / (2 * Real.pi) : ℝ) •
      ((∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)))) -
      ∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)))))

/-- **The defect theta relation for an odd Weil function.**  If
`Γ̃ + 1/(s − 1) − Σ lam(n) n^{-s} = Φ` on `Re s > 1`, the theta series of `a = 1 ⋆ (lam − Λ)`
satisfies `θ(x) = −x^{-1/2} θ(1/x) + β + β x^{-1/2} + K(x)` for all `x > 0`. -/
theorem coeffTheta_weil_defect_relation {lam : ℕ → ℝ} {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = Φ s) {x : ℝ} (hx : 0 < x) :
    GaloisForLFunctions.HTGeometry.coeffTheta (crystallineCoeff lam) x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) *
        GaloisForLFunctions.HTGeometry.coeffTheta (crystallineCoeff lam) x⁻¹) +
      weilResidue Φ + weilResidue Φ * (x : ℂ) ^ (-(1 / 2 : ℂ)) + weilDefect Φ x := by
  set a := crystallineCoeff lam with ha_def
  set β := weilResidue Φ with hβ
  obtain ⟨C, hC⟩ := exists_decay_weilRemainder hΦ
  have hdiff := differentiableOn_weilRemainder hΦ
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable
      (lseriesSummable_crystallineCoeff hsl (by simpa using hσ))
  have hθc := GaloisForLFunctions.HTGeometry.continuousOn_coeffTheta a (ha 2 (by norm_num))
  have hθm : MellinConvergent (GaloisForLFunctions.HTGeometry.coeffTheta a) (3 / 4 : ℂ) :=
    GaloisForLFunctions.HTGeometry.mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)
  have hEc : ContinuousOn (weilRemainder Φ)
      (GaloisForLFunctions.HTGeometry.verticalStrip (3 / 4) (3 / 2)) := by
    refine hdiff.continuousOn.mono (fun z hz => ?_)
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hz
    show 1 / 2 < z.re
    linarith [hz.1]
  have hEd : DifferentiableOn ℂ (weilRemainder Φ) {s : ℂ | 3 / 4 < s.re ∧ s.re < 3 / 2} := by
    refine hdiff.mono (fun z hz => ?_)
    show 1 / 2 < z.re
    linarith [hz.1]
  have hR : ∀ s : ℂ, s.re = 3 / 2 → mellin (GaloisForLFunctions.HTGeometry.coeffTheta a) (s / 2) =
      weilRemainder Φ s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h0; rw [h0] at hs; norm_num at hs
    have hs' : 1 < s.re := by rw [hs]; norm_num
    have hlam : LSeries (fun n => (lam n : ℂ)) s =
        zetaArchimedeanDatum s + 1 / (s - 1) - Φ s := by
      linear_combination -(hid s hs')
    rw [GaloisForLFunctions.HTGeometry.mellin_coeffTheta a ha hs', coeffDirichlet_eq_LSeries,
      LSeries_crystallineCoeff hsl hs',
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs', hlam,
      Gammaℝ_mul_riemannZeta_mul_eq hs', weilRemainder, Function.update_of_ne hs1,
      weilRemainderRaw]
    ring
  set G : ℂ → ℂ := fun s => completedZetaXiLogDeriv s - completedRiemannZeta s * Φ s with hGdef
  have hG : ∀ s : ℂ, s.re = 3 / 4 → G s = weilRemainder Φ s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h0; rw [h0] at hs; norm_num at hs
    rw [weilRemainder, Function.update_of_ne hs1, weilRemainderRaw]
    simp only [hGdef, hβ]
    ring
  have hmain := GaloisForLFunctions.HTGeometry.theta_add_dual_eq_of_rightLine hθc hθm hEc hEd hC
    hR hG hx
  have hrefl : ∀ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)) =
      -((x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) +
      (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) := by
    intro τ
    have h1 : 2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I) =
        1 - 2 * (((1 / 8 : ℝ) : ℂ) + τ * I) := by push_cast; ring
    simp only [hGdef]
    rw [h1, completedZetaXiLogDeriv_one_sub, completedRiemannZeta_one_sub, hΦ.one_sub]
    ring
  have hsplit3 : (∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + τ * I))) =
      (∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
        completedZetaXiLogDeriv (2 * (((3 / 8 : ℝ) : ℂ) + τ * I))) -
      ∫ τ : ℝ, (x : ℂ) ^ (-(((3 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((3 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((3 / 8 : ℝ) : ℂ) + τ * I))) := by
    obtain ⟨CG, hCG⟩ := exists_decay_completedZetaXiLogDeriv_strip
    have h1 := GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line
      differentiableOn_completedZetaXiLogDeriv_strip.continuousOn hCG (σ := 3 / 8)
      (by norm_num) (by norm_num) hx
    have h2 := integrable_cpow_mul_completedRiemannZeta_mul_weil hΦ (σ := 3 / 8) hx (Or.inl rfl)
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [hGdef]
    ring
  have hsplit1 : (∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
      G (2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I))) =
      -(∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) +
      ∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
        (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
          Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) := by
    obtain ⟨CG, hCG⟩ := exists_decay_completedZetaXiLogDeriv_strip
    have h1 := GaloisForLFunctions.HTGeometry.integrable_cpow_mul_comp_line
      differentiableOn_completedZetaXiLogDeriv_strip.continuousOn hCG (σ := 1 / 8)
      (by norm_num) (by norm_num) hx
    have h2 := integrable_cpow_mul_completedRiemannZeta_mul_weil hΦ (σ := 1 / 8) hx (Or.inr rfl)
    calc (∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
          G (2 * (((3 / 8 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)))
        = ∫ τ : ℝ, (-((x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) +
          (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
              Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)))) :=
          integral_congr_ae (Eventually.of_forall hrefl)
      _ = (∫ τ : ℝ, -((x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            completedZetaXiLogDeriv (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)))) +
          ∫ τ : ℝ, (x : ℂ) ^ (-(((1 / 8 : ℝ) : ℂ) + τ * I)) *
            (completedRiemannZeta (2 * (((1 / 8 : ℝ) : ℂ) + τ * I)) *
              Φ (2 * (((1 / 8 : ℝ) : ℂ) + τ * I))) := integral_add h1.neg h2
      _ = _ := by rw [integral_neg]
  have hG1 := integral_completedZetaXiLogDeriv_thin_strip hx
  rw [hsplit3, hsplit1, hG1] at hmain
  rw [weilDefect]
  rw [Complex.real_smul] at hmain ⊢
  linear_combination hmain

/-- **Constant crystalline coefficients force `lam = Λ` and RH** (odd Weil function form). -/
theorem vonMangoldt_and_RH_of_weil_coeff_eq {lam : ℕ → ℝ} {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = Φ s)
    (ha : ∀ n : ℕ, crystallineCoeff lam (n + 1) = -(2 * weilResidue Φ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  set β := weilResidue Φ with hβ
  set v : ℕ → ℂ := (fun n => (lam n : ℂ)) - fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
    with hv
  have hvs : ∀ s : ℂ, 1 < s.re → LSeriesSummable v s :=
    fun s hs => (lseriesSummable_of_summable_abs hsl hs).sub
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  have hLv : ∀ s : ℂ, 1 < s.re → LSeries v s = -(2 * β) := by
    intro s hs
    have h0 : LSeries (crystallineCoeff lam) s = -(2 * β) * riemannZeta s := by
      rw [← coeffDirichlet_eq_LSeries, zeta_eq_tsum_one_div_nat_add_one_cpow hs,
        ← tsum_mul_left]
      unfold GaloisForLFunctions.HTGeometry.coeffDirichlet
      refine tsum_congr fun n => ?_
      rw [ha n]
      push_cast
      ring
    rw [LSeries_crystallineCoeff hsl hs, ← LSeries_sub (lseriesSummable_of_summable_abs hsl hs)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs), ← hv] at h0
    have hζ := riemannZeta_ne_zero_of_one_le_re hs.le
    exact mul_right_cancel₀ hζ (by rw [mul_comm]; exact h0)
  have hδs : ∀ s : ℂ, 1 < s.re → LSeriesSummable LSeries.delta s := fun s hs =>
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => by unfold LSeries.delta; split_ifs <;> simp) hs
  set w : ℕ → ℂ := v + (2 * β) • LSeries.delta with hw
  have hLw : ∀ s : ℂ, 1 < s.re → LSeries w s = 0 := by
    intro s hs
    rw [hw, LSeries_add (hvs s hs) ((hδs s hs).smul _), LSeries_smul, LSeries_delta, hLv s hs]
    simp
  refine ⟨?_, ?_⟩
  · have hev : (fun x : ℝ => LSeries w x) =ᶠ[atTop] 0 := by
      filter_upwards [eventually_gt_atTop 1] with x hx
      exact hLw x (by simpa using hx)
    rcases LSeries_eventually_eq_zero_iff'.mp hev with h | h
    · intro n hn
      have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have := h n hn0
      simp only [hw, hv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, LSeries.delta, if_neg hn1,
        smul_eq_mul, mul_zero, add_zero, sub_eq_zero] at this
      exact_mod_cast this
    · exfalso
      have hle := ((hvs 2 (by norm_num)).add ((hδs 2 (by norm_num)).smul (2 * β))).abscissaOfAbsConv_le
      rw [← hw, h] at hle
      simp at hle
  · refine riemannHypothesis_of_completedZetaXiLogDeriv_add_eq_mul (P := Φ)
      (hΦ.differentiableOn.mono fun z hz => ?_) (2 * β) (fun s hs => ?_)
    · exact hz
    have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; norm_num at hs
    have h1 : zetaArchimedeanDatum s + 1 / (s - 1) - Φ s -
        -deriv riemannZeta s / riemannZeta s = -(2 * β) := by
      rw [← hid s hs, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
        ← hLv s hs, hv, LSeries_sub (lseriesSummable_of_summable_abs hsl hs)
          (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
      ring
    have h := Gammaℝ_mul_riemannZeta_mul_eq hs (Φ s)
    rw [h1] at h
    have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
      rw [riemannZeta_def_of_ne_zero hs0]
      field_simp [Gammaℝ_ne_zero_of_re_pos (by linarith : (0 : ℝ) < s.re)]
    rw [hΛ] at h ⊢
    linear_combination -h

theorem crystallineCoeff_eq_of_weil_defect {lam : ℕ → ℝ} {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = Φ s) {J : ℂ → ℂ}
    (hJd : DifferentiableOn ℂ J {τ : ℂ | 0 < τ.re})
    (hJ : ∀ τ : ℝ, 0 < τ → IntegrableOn (fun x : ℝ => weilDefect Φ x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
      J τ = τ * ∫ x in Ioi (0 : ℝ), weilDefect Φ x * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ))
    (hrad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * J ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0))
    (n : ℕ) :
    crystallineCoeff lam (n + 1) = -(2 * weilResidue Φ) := by
  set a := crystallineCoeff lam with ha_def
  set β := weilResidue Φ with hβ
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable
      (lseriesSummable_crystallineCoeff hsl (by simpa using hσ))
  have hL : ∀ τ : ℂ, 0 < τ.re → GaloisForLFunctions.HTGeometry.hamburgerSeries a τ =
      (-1) * ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) +
        β / (Real.pi * τ) + β + J τ := fun τ hτ =>
    GaloisForLFunctions.HTGeometry.hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha
      (fun x hx => coeffTheta_weil_defect_relation hΦ hsl hid hx)
      (fun τ hτ => (hJ τ hτ).1) hJd (fun τ hτ => (hJ τ hτ).2) hτ
  have hper : ∀ τ : ℂ, 0 < τ.re → GaloisForLFunctions.HTGeometry.hamburgerSeries a (τ + I) -
      GaloisForLFunctions.HTGeometry.hamburgerSeries a τ =
        β / Real.pi / (τ + I) - β / Real.pi / τ + (J (τ + I) - J τ) := by
    intro τ hτ
    have hτ' : 0 < (τ + I).re := by simpa using hτ
    rw [hL τ hτ, hL (τ + I) hτ']
    have hexp : ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (τ + I))) =
        ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) := by
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, div_div, div_div]
    ring
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := GaloisForLFunctions.HTGeometry.summable_sq_of_forall_rpow ha
    simpa using this
  have hK : ∀ n₀ : ℕ, Tendsto (fun τ => (τ - (n₀ : ℂ) * I) * (J (τ + I) - J τ))
      (𝓝[{τ : ℂ | 0 < τ.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
    intro n₀
    refine tendsto_sub_mul_defect_of_radial ha2 (β / Real.pi) (fun τ => J (τ + I) - J τ) hper n₀ ?_
    have h1 := hrad (n₀ + 1)
    have h0 := hrad n₀
    have := h1.sub h0
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    push_cast
    ring_nf
  have h := GaloisForLFunctions.HTGeometry.coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect
    ha2 (β / Real.pi) (fun τ => J (τ + I) - J τ) hper hK n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **Rigidity of odd Weil functions with a radially vanishing defect.**  Let `Φ` be an odd Weil
function with `Γ̃ + 1/(s − 1) − Σ lam(n) n^{-s} = Φ` on `Re s > 1`, and let `J` be a holomorphic
continuation to `Re τ > 0` of the Laplace transform `τ ∫ K(x) e^{−πτ²x} dx` of its thin-strip defect.
If `ε J(ε + im) → 0` as `ε → 0⁺` for every `m ≥ 0`, then `lam(n) = Λ(n)` for `n ≥ 2` and RH holds. -/
theorem weil_defect_rigidity {lam : ℕ → ℝ} {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = Φ s) {J : ℂ → ℂ}
    (hJd : DifferentiableOn ℂ J {τ : ℂ | 0 < τ.re})
    (hJ : ∀ τ : ℝ, 0 < τ → IntegrableOn (fun x : ℝ => weilDefect Φ x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
      J τ = τ * ∫ x in Ioi (0 : ℝ), weilDefect Φ x * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ))
    (hrad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * J ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  vonMangoldt_and_RH_of_weil_coeff_eq hΦ hsl hid
    (crystallineCoeff_eq_of_weil_defect hΦ hsl hid hJd hJ hrad)

/-- **Holomorphy of parametric integrals.**  If each `F x` is holomorphic on the open set `U`,
measurable in `x`, and locally bounded by an integrable function, then `z ↦ ∫ F x z dν` is
holomorphic on `U`.  The derivative is dominated through the Cauchy estimate on a smaller ball. -/
theorem differentiableOn_integral_of_locally_bounded {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {U : Set ℂ} (hU : IsOpen U) {F : X → ℂ → ℂ}
    (hF : ∀ x, DifferentiableOn ℂ (F x) U)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun x => F x z) ν)
    (hbound : ∀ z₀ ∈ U, ∃ r > 0, closedBall z₀ r ⊆ U ∧ ∃ g : X → ℝ, Integrable g ν ∧
      ∀ x, ∀ z ∈ closedBall z₀ r, ‖F x z‖ ≤ g x) :
    DifferentiableOn ℂ (fun z => ∫ x, F x z ∂ν) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hsub, g, hg, hgb⟩ := hbound z₀ hz₀
  have hr2 : 0 < r / 2 := half_pos hr
  -- the Cauchy estimate on the ball of radius `r/2`
  have hderiv : ∀ x, ∀ z ∈ ball z₀ (r / 2), ‖deriv (F x) z‖ ≤ g x / (r / 2) := by
    intro x z hz
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2
      ((hF x).diffContOnCl_ball ?_) (fun w hw => hgb x w ?_)
    · intro w hw
      apply hsub
      rw [mem_closedBall] at hw ⊢
      rw [mem_ball] at hz
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ r / 2 + r / 2 := by linarith
        _ = r := by ring
    · rw [mem_sphere] at hw
      rw [mem_ball] at hz
      rw [mem_closedBall]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ r / 2 + r / 2 := by linarith
        _ = r := by ring
  have hball : ball z₀ (r / 2) ⊆ U := fun z hz =>
    hsub (ball_subset_closedBall (ball_subset_ball (by linarith) hz))
  have hdiffAt : ∀ x, ∀ z ∈ ball z₀ (r / 2), HasDerivAt (F x) (deriv (F x) z) z := fun x z hz =>
    ((hF x).differentiableAt (hU.mem_nhds (hball hz))).hasDerivAt
  -- measurability of the derivative at `z₀`: a limit of difference quotients
  have hmeas' : AEStronglyMeasurable (fun x => deriv (F x) z₀) ν := by
    set h : ℕ → ℂ := fun n => ((r / 4 / ((n : ℝ) + 1) : ℝ) : ℂ) with hh
    have hpos : ∀ n : ℕ, 0 < r / 4 / ((n : ℝ) + 1) := fun n => by positivity
    have hh0 : ∀ n, h n ≠ 0 := fun n => by
      simp only [hh]; exact_mod_cast (hpos n).ne'
    have hmem : ∀ n, z₀ + h n ∈ U := by
      intro n
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      simp only [hh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
      have : r / 4 / ((n : ℝ) + 1) ≤ r / 4 := div_le_self (by positivity)
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      linarith
    have hlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => hh0 n⟩
      have : Tendsto (fun n : ℕ => r / 4 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at h2
      exact h2
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n x => (h n)⁻¹ • (F x (z₀ + h n) - F x z₀)) (fun n => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact ((hmeas _ (hmem n)).sub (hmeas _ hz₀)).const_smul ((h n)⁻¹)
    · exact (hdiffAt x z₀ (mem_ball_self hr2)).tendsto_slope_zero.comp hlim
  have hint : Integrable (fun x => F x z₀) ν :=
    Integrable.mono' hg (hmeas _ hz₀)
      (Eventually.of_forall fun x => hgb x z₀ (mem_closedBall_self hr.le))
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun z x => F x z) (F' := fun z x => deriv (F x) z) (x₀ := z₀)
    (bound := fun x => g x / (r / 2)) (ball_mem_nhds z₀ hr2)
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) fun z hz => hmeas z hz) hint hmeas'
    (Eventually.of_forall fun x z hz => hderiv x z hz) (hg.div_const _)
    (Eventually.of_forall fun x z hz => hdiffAt x z hz)
  exact hres.2.differentiableAt.differentiableWithinAt

end RHTower
