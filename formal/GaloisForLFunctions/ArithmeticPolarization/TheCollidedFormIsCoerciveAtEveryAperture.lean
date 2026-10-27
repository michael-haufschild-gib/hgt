import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormSamplesHighFrequencies

/-!
# The collided form is coercive at every aperture

**Theorem** (`exists_collidedForm_coercive`). For every aperture `A > 0` there is `c > 0` with

  `c ‖f‖₂² ≤ D(f) = Σ_ρ m_ρ |f̂(ρ)|²`

for every `C²` test supported in `[−A, A]`. Equivalently, the zeros of `ζ`, with multiplicity, form
a sampling set for every Paley–Wiener space; the constant is not effective.

**Proof.** The Gårding inequality (`collidedForm_ge_sub_lowMass`) gives
`D(f) ≥ 2π‖f‖² − K ∫_{−T₀}^{T₀} |f̂|²`, so a normalized sequence with `D(f_n) → 0` keeps its
low-frequency mass bounded below. The low frequencies are compact:

* mollify, `g_n = f_n ⋆ φ` (`mollify`), with a bump `φ` of width `ε`, `εT₀ ≤ ½`. The `g_n` are
  uniformly bounded, uniformly equicontinuous and supported in a fixed interval, so by
  Arzelà–Ascoli a subsequence converges uniformly to a continuous `G`;
* `ĝ_n = f̂_n φ̂` (`paperFT_mollify`), so `|ĝ_n(ρ)| ≤ e^{ε/2} |f̂_n(ρ)| → 0` at every zero: `G` is
  blind to every zero, hence `G = 0` by faithfulness (`collidedForm_eq_zero_iff`);
* `|φ̂| ≥ ½` on `[−T₀, T₀]`, so `|f̂_n| ≤ 2 |ĝ_n| ≤ 2 ∫ |g_n| → 0` uniformly there, and the
  low-frequency mass tends to `0` along the subsequence (`tendsto_lowMass_subseq`): a contradiction.
-/

open Complex MeasureTheory Set Filter Topology Real BoundedContinuousFunction
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-! ### Mollification -/

/-- Mollification `(f ⋆ φ)(x) = ∫ f(y) φ(x − y) dy`. -/
def mollify (φ : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, f y * (φ (x - y) : ℂ)

theorem integrable_mollify_integrand {φ : ℝ → ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hφ : Continuous φ) (x : ℝ) :
    Integrable fun y => f y * (φ (x - y) : ℂ) := by
  refine (hf.mul (Complex.continuous_ofReal.comp
    (hφ.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport ?_
  exact hfc.mul_right

/-- `∫ |f| ≤ A + ½ ∫ |f|²` for `f` supported in `[−A, A]`. -/
theorem integral_norm_le_of_support {f : ℝ → ℂ} (hf : Continuous f) {A : ℝ} (hA : 0 ≤ A)
    (hfs : tsupport f ⊆ Icc (-A) A) :
    ∫ y, ‖f y‖ ≤ A + (1 / 2) * ∫ y, ‖f y‖ ^ 2 := by
  have hout : ∀ y ∉ Icc (-A) A, f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hfs h)
  have h1 : ∫ y, ‖f y‖ = ∫ y in Icc (-A) A, ‖f y‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hout y hy, norm_zero]).symm
  have h2 : ∫ y, ‖f y‖ ^ 2 = ∫ y in Icc (-A) A, ‖f y‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [hout y hy, norm_zero]; norm_num).symm
  have hcont1 : ContinuousOn (fun y => ‖f y‖) (Icc (-A) A) := hf.norm.continuousOn
  have hcont2 : ContinuousOn (fun y => ‖f y‖ ^ 2) (Icc (-A) A) := (hf.norm.pow 2).continuousOn
  have hi1 : IntegrableOn (fun y => ‖f y‖) (Icc (-A) A) := hcont1.integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun y => ‖f y‖ ^ 2) (Icc (-A) A) :=
    hcont2.integrableOn_compact isCompact_Icc
  have hic : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc (-A) A) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hmono : ∫ y in Icc (-A) A, ‖f y‖ ≤ ∫ y in Icc (-A) A, ((1 / 2 : ℝ) + (1 / 2) * ‖f y‖ ^ 2) :=
    setIntegral_mono_on hi1 (hic.add (hi2.const_mul _)) measurableSet_Icc fun y _ => by
      have := sq_nonneg (‖f y‖ - 1)
      nlinarith
  have hval : ∫ y in Icc (-A) A, ((1 / 2 : ℝ) + (1 / 2) * ‖f y‖ ^ 2) =
      A + (1 / 2) * ∫ y in Icc (-A) A, ‖f y‖ ^ 2 := by
    rw [integral_add hic (hi2.const_mul _), integral_const_mul, setIntegral_const,
      Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [h1, h2]
  linarith

/-- A pointwise bound for the mollification. -/
theorem norm_mollify_le {φ : ℝ → ℝ} {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {M : ℝ} (hM : ∀ x, |φ x| ≤ M) (x : ℝ) : ‖mollify φ f x‖ ≤ M * ∫ y, ‖f y‖ := by
  rw [mollify, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hf.norm.integrable_of_hasCompactSupport hfc.norm).const_mul M)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

/-- The mollification varies with the modulus of continuity of the bump. -/
theorem norm_mollify_sub_le {φ : ℝ → ℝ} {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hφ : Continuous φ) {η : ℝ} {x x' : ℝ} (hη : ∀ y, |φ (x - y) - φ (x' - y)| ≤ η) :
    ‖mollify φ f x - mollify φ f x'‖ ≤ η * ∫ y, ‖f y‖ := by
  rw [mollify, mollify, ← integral_sub (integrable_mollify_integrand hf hfc hφ x)
    (integrable_mollify_integrand hf hfc hφ x'), ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hf.norm.integrable_of_hasCompactSupport hfc.norm).const_mul η)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hη y) (norm_nonneg _)

/-- The mollification vanishes outside `[−A − ε, A + ε]`. -/
theorem mollify_eq_zero {φ : ℝ → ℝ} {f : ℝ → ℂ} {A ε : ℝ} (hfs : tsupport f ⊆ Icc (-A) A)
    (hφs : tsupport φ ⊆ Icc (-ε) ε) {x : ℝ} (hx : A + ε < |x|) : mollify φ f x = 0 := by
  rw [mollify]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ tsupport f
  · have hyA := hfs hy
    have : x - y ∉ tsupport φ := by
      intro h
      have h1 := hφs h
      have : |x| ≤ |x - y| + |y| := by
        have := abs_add_le (x - y) y; rwa [sub_add_cancel] at this
      have h2 : |x - y| ≤ ε := abs_le.mpr ⟨h1.1, h1.2⟩
      have h3 : |y| ≤ A := abs_le.mpr ⟨hyA.1, hyA.2⟩
      linarith
    simp [image_eq_zero_of_notMem_tsupport this]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **The convolution theorem.** `(f ⋆ φ)^ = f̂ φ̂` at every complex frequency. -/
theorem paperFT_mollify {φ : ℝ → ℝ} {f : ℝ → ℂ} (hf : Continuous f) {A ε : ℝ}
    (hfs : tsupport f ⊆ Icc (-A) A) (hφ : Continuous φ) (hφs : tsupport φ ⊆ Icc (-ε) ε)
    (z : ℂ) : paperFT (mollify φ f) z = paperFT f z * paperFT (fun u => (φ u : ℂ)) z := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  set k : ℝ → ℝ → ℂ := fun x y => f y * (φ (x - y) : ℂ) * Complex.exp (I * z * x) with hk
  have hkc : Continuous (Function.uncurry k) := by
    refine ((hf.comp continuous_snd).mul (Complex.continuous_ofReal.comp
      (hφ.comp (continuous_fst.sub continuous_snd)))).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)))
  have hksupp : HasCompactSupport (Function.uncurry k) := by
    refine HasCompactSupport.intro ((isCompact_Icc (a := -(A + ε)) (b := A + ε)).prod
      (isCompact_Icc (a := -A) (b := A))) fun p hp => ?_
    simp only [Function.uncurry, hk]
    by_cases hy : p.2 ∈ tsupport f
    · have hyA := hfs hy
      have hx : p.1 - p.2 ∉ tsupport φ := by
        intro h
        apply hp
        refine ⟨⟨?_, ?_⟩, hyA⟩ <;> linarith [(hφs h).1, (hφs h).2, hyA.1, hyA.2]
      simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hkint : Integrable (Function.uncurry k) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hkc.integrable_of_hasCompactSupport hksupp
  have hinner : ∀ x : ℝ, mollify φ f x * Complex.exp (I * z * x) = ∫ y, k x y := by
    intro x; rw [mollify, ← integral_mul_const]
  have hswap := integral_integral_swap hkint
  have hcol : ∀ y : ℝ, ∫ x, k x y =
      f y * Complex.exp (I * z * y) * paperFT (fun u => (φ u : ℂ)) z := by
    intro y
    have : (fun x : ℝ => k x y) = fun x => (f y * Complex.exp (I * z * y)) *
        ((fun u : ℝ => (φ u : ℂ) * Complex.exp (I * z * u)) (x - y)) := by
      funext x
      simp only [hk]
      rw [show I * z * (x : ℂ) = I * z * (y : ℂ) + I * z * ((x - y : ℝ) : ℂ) by push_cast; ring,
        Complex.exp_add]
      ring
    rw [this, integral_const_mul,
      integral_sub_right_eq_self (fun u : ℝ => (φ u : ℂ) * Complex.exp (I * z * u)) y, paperFT]
  rw [paperFT, integral_congr_ae (Filter.Eventually.of_forall hinner), hswap,
    integral_congr_ae (Filter.Eventually.of_forall hcol), integral_mul_const]
  rfl

/-! ### Facts about the zeros and the bump -/

/-- A single zero is at most the collided form. -/
theorem normSq_tr_le_collidedForm {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ρ : zetaZeroConfig.carrier) : Complex.normSq (tr f ρ) ≤ collidedForm zetaZeroConfig f := by
  have hs := zeta_summable_collided hf hfc
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
    exact_mod_cast zetaZeroConfig.one_le_mult ρ ρ.2
  have h1 : (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ) ≤ collidedForm zetaZeroConfig f :=
    hs.le_tsum ρ fun j _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have h2 : Complex.normSq (tr f ρ) ≤ (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ) :=
    le_mul_of_one_le_left (Complex.normSq_nonneg _) hm
  linarith

/-- The transform of a bump of width `≤ 1` and mass `1` is at most `e` on the critical strip. -/
theorem norm_tr_bump_le {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφcs : HasCompactSupport φ) (hφ1 : ∫ x, φ x = 1) {ε : ℝ} (hε1 : ε ≤ 1)
    (hφs : tsupport φ ⊆ Icc (-ε) ε) (ρ : zetaZeroConfig.carrier) :
    ‖tr (fun u => (φ u : ℂ)) ρ‖ ≤ Real.exp 1 := by
  rw [tr_eq]
  have hstrip := zetaZeroConfig.strip ρ ρ.2
  have hint : Integrable fun u => φ u * Real.exp 1 :=
    (hφ.integrable_of_hasCompactSupport hφcs).mul_const _
  calc ‖∫ u : ℝ, (φ u : ℂ) * Complex.exp (((ρ : ℂ) - 1 / 2) * u)‖ ≤ ∫ u, φ u * Real.exp 1 := by
        refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun u => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 u), Complex.norm_exp]
        by_cases hu : u ∈ tsupport φ
        · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hφ0 u)
          have hu' := hφs hu
          have hre : (((ρ : ℂ) - 1 / 2) * u).re = ((ρ : ℂ).re - 1 / 2) * u := by simp
          rw [hre]
          have h1 : |((ρ : ℂ).re - 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hstrip.1],
            by linarith [hstrip.2]⟩
          have h2 : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
          calc ((ρ : ℂ).re - 1 / 2) * u ≤ |((ρ : ℂ).re - 1 / 2) * u| := le_abs_self _
            _ = |((ρ : ℂ).re - 1 / 2)| * |u| := abs_mul _ _
            _ ≤ 1 / 2 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
            _ ≤ 1 := by norm_num
        · rw [image_eq_zero_of_notMem_tsupport hu, zero_mul, zero_mul]
    _ = Real.exp 1 := by rw [integral_mul_const, hφ1, one_mul]

/-- On `|τ| ≤ T₀` the transform of a bump of width `ε ≤ 1/(2T₀)` stays at least `½`. -/
theorem half_le_norm_paperFT_bump {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφcs : HasCompactSupport φ) (hφ1 : ∫ x, φ x = 1) {ε T₀ : ℝ}
    (hεT : ε * T₀ ≤ 1 / 2) (hφs : tsupport φ ⊆ Icc (-ε) ε) {τ : ℝ} (hτ : |τ| ≤ T₀) :
    1 / 2 ≤ ‖paperFT (fun u => (φ u : ℂ)) τ‖ := by
  have hint : Integrable fun u => (φ u : ℂ) :=
    (Complex.continuous_ofReal.comp hφ).integrable_of_hasCompactSupport
      (hφcs.comp_left Complex.ofReal_zero)
  have hint2 : Integrable fun u => (φ u : ℂ) * Complex.exp (I * τ * u) := by
    refine ((Complex.continuous_ofReal.comp hφ).mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).integrable_of_hasCompactSupport ?_
    exact (hφcs.comp_left Complex.ofReal_zero).mul_right
  have h1 : ∫ u, (φ u : ℂ) = 1 := by rw [integral_complex_ofReal, hφ1, Complex.ofReal_one]
  have hdiff : paperFT (fun u => (φ u : ℂ)) τ - 1 =
      ∫ u, (φ u : ℂ) * (Complex.exp (I * τ * u) - 1) := by
    have e1 : (∫ u, (φ u : ℂ) * (Complex.exp (I * τ * u) - 1)) =
        (∫ u, (φ u : ℂ) * Complex.exp (I * τ * u)) - ∫ u, (φ u : ℂ) := by
      rw [← integral_sub hint2 hint]; congr 1; funext u; ring
    rw [e1, h1, paperFT]
  have hbound : ‖paperFT (fun u => (φ u : ℂ)) τ - 1‖ ≤ 1 / 2 := by
    rw [hdiff]
    have hintb : Integrable fun u => φ u * (ε * T₀) :=
      (hφ.integrable_of_hasCompactSupport hφcs).mul_const _
    calc ‖∫ u, (φ u : ℂ) * (Complex.exp (I * τ * u) - 1)‖ ≤ ∫ u, φ u * (ε * T₀) := by
          refine norm_integral_le_of_norm_le hintb (Filter.Eventually.of_forall fun u => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 u)]
          by_cases hu : u ∈ tsupport φ
          · refine mul_le_mul_of_nonneg_left ?_ (hφ0 u)
            have hu' := hφs hu
            have hexp : ‖Complex.exp (I * ((τ * u : ℝ) : ℂ)) - 1‖ ≤ ‖τ * u‖ :=
              Real.norm_exp_I_mul_ofReal_sub_one_le
            rw [show I * (τ : ℂ) * (u : ℂ) = I * ((τ * u : ℝ) : ℂ) by push_cast; ring]
            refine hexp.trans ?_
            rw [Real.norm_eq_abs, abs_mul, mul_comm ε]
            have hu2 : |u| ≤ ε := abs_le.mpr ⟨hu'.1, hu'.2⟩
            exact mul_le_mul hτ hu2 (abs_nonneg _) (by linarith [abs_nonneg τ])
          · rw [image_eq_zero_of_notMem_tsupport hu, zero_mul, zero_mul]
      _ = ε * T₀ := by rw [integral_mul_const, hφ1, one_mul]
      _ ≤ 1 / 2 := hεT
  have := norm_sub_norm_le (1 : ℂ) (paperFT (fun u => (φ u : ℂ)) τ)
  rw [norm_one, norm_sub_rev] at this
  linarith

/-! ### Arzelà–Ascoli for families on the line with common support -/

/-- **Arzelà–Ascoli on the line.** A uniformly bounded, uniformly equicontinuous family vanishing
outside `[−R′, R′]` has a subsequence converging uniformly to a continuous function vanishing there. -/
theorem exists_uniform_subseq {g : ℕ → ℝ → ℂ} {R' B : ℝ} (hR' : 0 ≤ R')
    (hb : ∀ n x, ‖g n x‖ ≤ B)
    (heq : ∀ e > 0, ∃ δ > 0, ∀ x x', dist x x' < δ → ∀ n, dist (g n x) (g n x') < e)
    (hz : ∀ n x, R' < |x| → g n x = 0) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ G : ℝ → ℂ, Continuous G ∧ (∀ x, R' < |x| → G x = 0) ∧
      ∀ e > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ x, ‖g (ψ k) x - G x‖ < e := by
  set R := R' + 1 with hRdef
  have hR : -R ≤ R := by linarith
  have hcont : ∀ n, Continuous (g n) := fun n =>
    (Metric.uniformContinuous_iff.mpr fun e he => by
      obtain ⟨δ, hδ, h⟩ := heq e he
      exact ⟨δ, hδ, fun {x x'} hxx' => h x x' hxx' n⟩).continuous
  -- the restrictions to `[−R, R]`
  let h : ℕ → (Icc (-R) R →ᵇ ℂ) := fun n =>
    mkOfCompact ⟨fun x => g n x, (hcont n).comp continuous_subtype_val⟩
  have hh : ∀ n (x : Icc (-R) R), h n x = g n x := fun n x => rfl
  -- `g n` is recovered from its restriction through the projection to `[−R, R]`
  have hproj : ∀ n x, g n x = h n (projIcc (-R) R hR x) := by
    intro n x
    rw [hh]
    by_cases hx : x ∈ Icc (-R) R
    · rw [projIcc_of_mem hR hx]
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [projIcc_of_le_left hR hx.le, hz n x (by rw [abs_of_neg (by linarith)]; linarith),
          hz n (-R) (by rw [abs_of_neg (by linarith)]; linarith)]
      · rw [projIcc_of_right_le hR hx.le, hz n x (by rw [abs_of_pos (by linarith)]; linarith),
          hz n R (by rw [abs_of_pos (by linarith)]; linarith)]
  -- Arzelà–Ascoli
  set A := Set.range h with hAdef
  have hin : ∀ (f : Icc (-R) R →ᵇ ℂ) (x : Icc (-R) R), f ∈ A → f x ∈ Metric.closedBall (0 : ℂ) B := by
    rintro f x ⟨n, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hh]
    exact hb n x
  have hequi : Equicontinuous ((↑) : A → Icc (-R) R → ℂ) := by
    refine UniformEquicontinuous.equicontinuous (Metric.uniformEquicontinuous_iff.mpr fun e he => ?_)
    obtain ⟨δ, hδ, hδe⟩ := heq e he
    refine ⟨δ, hδ, fun x y hxy i => ?_⟩
    obtain ⟨_, ⟨n, rfl⟩⟩ := i
    exact hδe x y hxy n
  have hcpt := arzela_ascoli (Metric.closedBall (0 : ℂ) B) (isCompact_closedBall _ _) A hin hequi
  obtain ⟨H, -, ψ, hψ, hlim⟩ :=
    hcpt.tendsto_subseq (x := h) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨ψ, hψ, fun x => H (projIcc (-R) R hR x), H.continuous.comp continuous_projIcc, ?_, ?_⟩
  · -- the limit vanishes outside `[−R′, R′]`
    intro x hx
    have hpt : Tendsto (fun k => h (ψ k) (projIcc (-R) R hR x)) atTop
        (𝓝 (H (projIcc (-R) R hR x))) :=
      ((continuous_eval_const (projIcc (-R) R hR x)).tendsto H).comp hlim
    have h0 : ∀ k, h (ψ k) (projIcc (-R) R hR x) = 0 := fun k => by
      rw [← hproj, hz _ x hx]
    simp only [h0] at hpt
    show H (projIcc (-R) R hR x) = 0
    exact tendsto_nhds_unique hpt tendsto_const_nhds
  · -- uniform convergence
    intro e he
    obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.mp hlim e he
    refine ⟨k₀, fun k hk x => ?_⟩
    rw [hproj, ← dist_eq_norm]
    exact lt_of_le_of_lt (dist_coe_le_dist _) (hk₀ k hk)

/-! ### The low frequencies are compact -/

/-- A bump of mass `1` and width `ε ≤ ½` with `ε T₀ ≤ ½`. -/
theorem exists_bump {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ (φ : ℝ → ℝ) (ε : ℝ), Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧ ∫ x, φ x = 1 ∧ HasCompactSupport φ ∧
      0 < ε ∧ ε ≤ 1 / 2 ∧ ε * T₀ ≤ 1 / 2 ∧ tsupport φ ⊆ Icc (-ε) ε := by
  set ε : ℝ := 1 / (2 * (T₀ + 1)) with hεdef
  have hε0 : 0 < ε := by positivity
  let b : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  refine ⟨b.normed volume, ε, b.continuous_normed, b.nonneg_normed, b.integral_normed,
    b.hasCompactSupport_normed, hε0, ?_, ?_, ?_⟩
  · rw [hεdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · rw [hεdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · rw [b.tsupport_normed_eq, Real.closedBall_eq_Icc]; simp

/-- Transforms of functions vanishing outside `[−R, R]` are bounded by the supremum. -/
theorem norm_tr_le_sup {h : ℝ → ℂ} (hc : Continuous h) {R S : ℝ} (hR : 0 ≤ R)
    (hz : ∀ x, R < |x| → h x = 0) (hS : ∀ x, ‖h x‖ ≤ S) {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    ‖tr h s‖ ≤ 2 * R * S * Real.exp (R / 2) := by
  rw [tr_eq]
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have hbound : Integrable ((Icc (-R) R).indicator fun _ => S * Real.exp (R / 2)) :=
    (integrableOn_const (s := Icc (-R) R) (μ := volume) (C := S * Real.exp (R / 2))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) enorm_ne_top).integrable_indicator
      measurableSet_Icc
  calc ‖∫ u : ℝ, h u * Complex.exp ((s - 1 / 2) * u)‖
      ≤ ∫ u, (Icc (-R) R).indicator (fun _ => S * Real.exp (R / 2)) u := by
        refine norm_integral_le_of_norm_le hbound (Filter.Eventually.of_forall fun u => ?_)
        by_cases hu : u ∈ Icc (-R) R
        · rw [Set.indicator_of_mem hu, norm_mul, Complex.norm_exp]
          refine mul_le_mul (hS u) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hS0
          have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by simp
          rw [hre]
          have hu' : |u| ≤ R := abs_le.mpr ⟨hu.1, hu.2⟩
          calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
            _ = |s.re - 1 / 2| * |u| := abs_mul _ _
            _ ≤ 1 / 2 * R := mul_le_mul hs hu' (abs_nonneg _) (by norm_num)
            _ = R / 2 := by ring
        · rw [Set.indicator_of_notMem hu, hz u (by
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
            rcases hu with hu | hu
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; exact hu), zero_mul, norm_zero]
    _ = 2 * R * S * Real.exp (R / 2) := by
        rw [integral_indicator_const _ measurableSet_Icc, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring

/-- `tr` of a difference of continuous functions vanishing outside `[−R, R]`. -/
theorem tr_sub_of_vanish {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b) {R : ℝ}
    (haz : ∀ x, R < |x| → a x = 0) (hbz : ∀ x, R < |x| → b x = 0) (s : ℂ) :
    tr (fun x => a x - b x) s = tr a s - tr b s := by
  have hcs : ∀ c : ℝ → ℂ, Continuous c → (∀ x, R < |x| → c x = 0) →
      Integrable fun u : ℝ => c u * Complex.exp ((s - 1 / 2) * u) := by
    intro c hc hcz
    refine (hc.mul (Complex.continuous_exp.comp (continuous_const.mul
      Complex.continuous_ofReal))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => ?_
    rw [hcz x (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact hx), zero_mul]
  rw [tr_eq, tr_eq, tr_eq, ← integral_sub (hcs a ha haz) (hcs b hb hbz)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only; ring

end GaloisForLFunctions.ArithmeticPolarization
