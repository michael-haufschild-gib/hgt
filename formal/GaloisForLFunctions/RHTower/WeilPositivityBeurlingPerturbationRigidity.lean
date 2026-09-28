import GaloisForLFunctions.RHTower.WeilPositivitySummablePerturbationRigidity

/-!
# Beurling rigidity of Weil positivity

Fix the archimedean term and the pole of `ζ`, and perturb the von Mangoldt prime measure
`Σ_n Λ(n) n^{-1/2} δ_{log n}` by a finite signed measure `μ₁ - μ₂` carried by `[ε, ∞)`, `ε > 0`.
Prime atoms may be added, removed or moved to arbitrary real positions (generalized primes in the
sense of Beurling), and absolutely continuous mass is allowed.  The perturbed Weil symbol is
`S_Λ(τ) - C_{μ₁}(τ) + C_{μ₂}(τ)` with the cosine symbol `C_μ(τ) = ∫ 2 cos(τu) dμ(u)`.

**Theorem** (`vonMangoldt_sub_measure_weilPositive_eq`).  If the perturbed symbol has nonnegative
energy on every polar-constrained `C²` test at every level, then `μ₁ = μ₂`.

**Corollary** (`vonMangoldt_move_atom_not_weilPositive`).  Moving a single atom of positive mass to
a different position destroys Weil positivity.

This is the continuous-positions strengthening of `vonMangoldt_add_summable_not_weilPositive`.  In the
language of Minkowski's problem (the polar constraint is Minkowski's closure condition for the normals
`(e^{x/2}, e^{-x/2})`), it says the positive completion of the archimedean place of `ζ` admits no
nearby deformation.  The continuity (openness) step of Alexandrov's existence scheme is therefore
unavailable at `ζ`.

## Mechanism

* **Concentration** (`vonMangoldt_sub_symbol_violation_of_concentration`).  For a bounded continuous
  perturbation symbol `P` with `P ≥ d₁/2` near a point, spread radical tests concentrated there have
  zero side `O(S^{10} e^{-S})` for `ζ` and energy `≤ -c S`.
* **Prime-blind extraction** (`cosineSymbol_sub_eq_zero_of_nonpos`).  If `P ≤ 0` everywhere, the probes
  `κ(x/ε) e^{-iτ₀x}`, supported in `[-ε/4, ε/4]`, do not see atoms in `[ε, ∞)`.  So
  `∫ |h|² P = 0` with a nonpositive continuous integrand, and `P(τ₀) = 0` because the probe's transform
  does not vanish at `τ₀`.
* **Fourier uniqueness** (`eq_of_cosineSymbol_eq`).  The symmetrization `μ + (-)_*μ` has characteristic
  function `C_μ`.  Equal cosine symbols give equal symmetrizations, and restricting to `[ε, ∞)` recovers
  `μ`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

/-- The cosine symbol `τ ↦ ∫ 2 cos(τu) dμ(u)` of a measure: the symbol of a family of prime atoms
placed at the points `u` with masses `μ`. -/
def cosineSymbol (μ : Measure ℝ) (τ : ℝ) : ℝ := ∫ u, 2 * Real.cos (τ * u) ∂μ

variable {μ : Measure ℝ}

theorem continuous_cosineSymbol [IsFiniteMeasure μ] : Continuous (cosineSymbol μ) := by
  unfold cosineSymbol
  refine continuous_of_dominated (bound := fun _ => 2) (fun τ => by fun_prop)
    (fun τ => Eventually.of_forall fun u => ?_) (integrable_const _)
    (Eventually.of_forall fun u => by fun_prop)
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  nlinarith [Real.abs_cos_le_one (τ * u)]

theorem abs_cosineSymbol_le [IsFiniteMeasure μ] (τ : ℝ) :
    |cosineSymbol μ τ| ≤ 2 * μ.real univ := by
  unfold cosineSymbol
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u => 2 * Real.cos (τ * u))
    (C := 2) (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul, abs_two]; nlinarith [Real.abs_cos_le_one (τ * u)])
  rw [Real.norm_eq_abs] at h
  linarith

/-- `∫ |h_g|² C_μ = 2π ∫ φ_g dμ`, with `φ_g` the even part of the Weil test of `g`. -/
theorem integral_normSq_mul_cosineSymbol [IsFiniteMeasure μ] {a : ℝ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * cosineSymbol μ τ =
      ∫ u, 2 * π * weilTestEvenPart g u ∂μ := by
  have hF := integrable_normSq_paperFT hg hgs
  obtain ⟨hgc, -, -, -, -⟩ := weilTest_self_data hg hgs
  have hHc : Continuous fun τ : ℝ => ‖paperFT g τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hg.continuous.integrable_of_hasCompactSupport
      hgc)).norm.pow 2
  have hprod : Integrable (Function.uncurry fun (τ : ℝ) (u : ℝ) =>
      ‖paperFT g τ‖ ^ 2 * (2 * Real.cos (τ * u))) (volume.prod μ) := by
    have hcont : Continuous (Function.uncurry fun (τ : ℝ) (u : ℝ) =>
        ‖paperFT g τ‖ ^ 2 * (2 * Real.cos (τ * u))) :=
      (hHc.comp continuous_fst).mul (continuous_const.mul
        (Real.continuous_cos.comp (continuous_fst.mul continuous_snd)))
    refine (Integrable.mul_prod hF (integrable_const (2 : ℝ) (μ := μ))).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    · simp only [Function.uncurry_def, norm_mul, Real.norm_eq_abs, abs_two]
      rw [abs_of_nonneg (sq_nonneg _)]
      have := Real.abs_cos_le_one (p.1 * p.2)
      have h0 : 0 ≤ ‖paperFT g p.1‖ ^ 2 := sq_nonneg _
      nlinarith
  have hswap := integral_integral_swap hprod
  have e1 : (fun τ : ℝ => ‖paperFT g τ‖ ^ 2 * cosineSymbol μ τ) =
      fun τ : ℝ => ∫ u, ‖paperFT g τ‖ ^ 2 * (2 * Real.cos (τ * u)) ∂μ := by
    funext τ; unfold cosineSymbol; exact (integral_const_mul _ _).symm
  rw [e1, hswap]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e2 : (fun τ : ℝ => ‖paperFT g τ‖ ^ 2 * (2 * Real.cos (τ * u))) =
      fun τ : ℝ => 2 * (‖paperFT g τ‖ ^ 2 * Real.cos (τ * u)) := by funext τ; ring
  simp only
  rw [e2, integral_const_mul, integral_normSq_paperFT_mul_cos_eq hg hgs]
  unfold weilTestEvenPart; ring

/-- The small probe `x ↦ κ(x/ε) e^{-iτ₀x}`: supported in `[-ε/4, ε/4]`, transform at `τ₀` nonzero. -/
def smallProbe (ε τ₀ : ℝ) : ℝ → ℂ := twistModulate (-τ₀) (fun x => weilBumpC (x / ε))

theorem contDiff_smallProbe (ε τ₀ : ℝ) : ContDiff ℝ 2 (smallProbe ε τ₀) :=
  contDiff_twistModulate ((contDiff_weilBumpC.of_le (by norm_num)).comp
    (contDiff_id.div_const ε))

theorem tsupport_smallProbe {ε : ℝ} (hε : 0 < ε) (τ₀ : ℝ) :
    tsupport (smallProbe ε τ₀) ⊆ Icc (-(ε / 4)) (ε / 4) := by
  refine (tsupport_twistModulate_subset _ _).trans (tsupport_subset_of_vanish fun x hx => ?_)
  apply weilBumpC_eq_zero
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]; linarith

theorem paperFT_smallProbe_ne_zero {ε : ℝ} (hε : 0 < ε) (τ₀ : ℝ) :
    paperFT (smallProbe ε τ₀) τ₀ ≠ 0 := by
  unfold smallProbe
  rw [paperFT_twistModulate, paperFT_comp_div hε]
  push_cast
  rw [show (τ₀ : ℂ) + -τ₀ = 0 by ring, mul_zero]
  have h := norm_paperFT_weilBumpC_ge (v := 0) (by norm_num)
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  refine mul_ne_zero (by exact_mod_cast hε.ne') fun h0 => ?_
  push_cast at h
  rw [h0, norm_zero] at h
  linarith

/-- **Prime-blind extraction.**  If the atoms of `μ₁, μ₂` lie in `[ε, ∞)` and the difference of their
cosine symbols is nonpositive everywhere, then it vanishes everywhere.  Probes supported in
`[-ε/4, ε/4]` do not see the atoms, so `∫ |h|² (C₁ - C₂) = 0` with a nonpositive integrand. -/
theorem cosineSymbol_sub_eq_zero_of_nonpos {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {ε : ℝ} (hε : 0 < ε) (h₁ : μ₁ (Iio ε) = 0) (h₂ : μ₂ (Iio ε) = 0)
    (hP : ∀ τ, cosineSymbol μ₁ τ - cosineSymbol μ₂ τ ≤ 0) (τ₀ : ℝ) :
    cosineSymbol μ₁ τ₀ - cosineSymbol μ₂ τ₀ = 0 := by
  set g := smallProbe ε τ₀ with hgdef
  have hg := contDiff_smallProbe ε τ₀
  have hgs := tsupport_smallProbe hε τ₀
  have hvan : ∀ {ν : Measure ℝ} [IsFiniteMeasure ν], ν (Iio ε) = 0 →
      ∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * cosineSymbol ν τ = 0 := by
    intro ν _ hν
    rw [integral_normSq_mul_cosineSymbol hg hgs]
    refine integral_eq_zero_of_ae ?_
    have hae : ∀ᵐ u ∂ν, ε ≤ u := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => by simpa using hx) hν
    filter_upwards [hae] with u hu
    have hu2 : 2 * (ε / 4) < |u| := by
      rw [abs_of_pos (by linarith)]; linarith
    simp only [Pi.zero_apply]
    rw [weilTestEvenPart_eq_zero hg hgs hu2, mul_zero]
  obtain ⟨hgc, -, -, -, -⟩ := weilTest_self_data hg hgs
  have hHc : Continuous fun τ : ℝ => ‖paperFT g τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hg.continuous.integrable_of_hasCompactSupport
      hgc)).norm.pow 2
  have hF := integrable_normSq_paperFT hg hgs
  have hint : ∀ {ν : Measure ℝ} [IsFiniteMeasure ν],
      Integrable fun τ : ℝ => ‖paperFT g τ‖ ^ 2 * cosineSymbol ν τ := by
    intro ν _
    refine (hF.mul_const (2 * ν.real univ)).mono' (hHc.mul continuous_cosineSymbol).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_cosineSymbol_le τ) (sq_nonneg _)
  set F : ℝ → ℝ := fun τ => ‖paperFT g τ‖ ^ 2 * -(cosineSymbol μ₁ τ - cosineSymbol μ₂ τ) with hFdef
  have hFc : Continuous F := hHc.mul (continuous_cosineSymbol.sub continuous_cosineSymbol).neg
  have hF0 : 0 ≤ F := fun τ => mul_nonneg (sq_nonneg _) (by linarith [hP τ])
  have hFi : Integrable F := by
    refine ((hint (ν := μ₂)).sub (hint (ν := μ₁))).congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.sub_apply, hFdef]; ring
  have hFint : ∫ τ, F τ = 0 := by
    have e : F = fun τ : ℝ => ‖paperFT g τ‖ ^ 2 * cosineSymbol μ₂ τ -
        ‖paperFT g τ‖ ^ 2 * cosineSymbol μ₁ τ := by funext τ; simp only [hFdef]; ring
    rw [e, integral_sub (hint (ν := μ₂)) (hint (ν := μ₁)), hvan h₁, hvan h₂, sub_zero]
  have hae := (integral_eq_zero_iff_of_nonneg hF0 hFi).mp hFint
  have hzero : F = 0 := (hFc.ae_eq_iff_eq volume continuous_const).mp hae
  have hτ₀ := congrFun hzero τ₀
  simp only [hFdef, Pi.zero_apply] at hτ₀
  have hne : ‖paperFT g τ₀‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr
    (paperFT_smallProbe_ne_zero hε τ₀))
  have := (mul_eq_zero.mp hτ₀).resolve_left hne
  linarith


/-- The characteristic function of the symmetrization `μ + (-)_*μ` is the cosine symbol. -/
theorem charFun_symm_eq_cosineSymbol (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    charFun (μ + μ.map Neg.neg) t = (cosineSymbol μ t : ℂ) := by
  have hmeas : ∀ ν : Measure ℝ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)) ν := fun ν => by fun_prop
  have hint : ∀ ν : Measure ℝ, IsFiniteMeasure ν →
      Integrable (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)) ν := by
    intro ν _
    refine (integrable_const (1 : ℝ)).mono' (hmeas ν) (Eventually.of_forall fun x => ?_)
    rw [show (↑t * ↑x * Complex.I : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply_real, integral_add_measure (hint μ inferInstance) (hint _ inferInstance),
    integral_map measurable_neg.aemeasurable (hmeas _)]
  unfold cosineSymbol
  rw [← integral_add (hint μ inferInstance) (by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [show (↑t * ↑(-x) * Complex.I : ℂ) = ((-(t * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]), ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  push_cast
  rw [Complex.two_cos]
  ring_nf

/-- **Fourier uniqueness for one-sided measures.**  Finite measures carried by `[ε, ∞)` (`ε > 0`) with
the same cosine symbol are equal. -/
theorem eq_of_cosineSymbol_eq {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {ε : ℝ} (hε : 0 < ε) (h₁ : μ₁ (Iio ε) = 0) (h₂ : μ₂ (Iio ε) = 0)
    (h : ∀ τ, cosineSymbol μ₁ τ = cosineSymbol μ₂ τ) : μ₁ = μ₂ := by
  have hsym : μ₁ + μ₁.map Neg.neg = μ₂ + μ₂.map Neg.neg := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_symm_eq_cosineSymbol, charFun_symm_eq_cosineSymbol, h t]
  have hres : ∀ μ : Measure ℝ, μ (Iio ε) = 0 →
      (μ + μ.map Neg.neg).restrict (Ici ε) = μ := by
    intro μ hμ
    rw [Measure.restrict_add]
    have hA : μ.restrict (Ici ε) = μ := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      exact measure_mono_null (fun x hx => by simpa using hx) hμ
    have hB : (μ.map Neg.neg).restrict (Ici ε) = 0 := by
      rw [Measure.restrict_eq_zero, Measure.map_apply measurable_neg measurableSet_Ici]
      refine measure_mono_null (fun x hx => ?_) hμ
      simp only [Set.mem_preimage, Set.mem_Ici] at hx
      simp only [Set.mem_Iio]; linarith
    rw [hA, hB, add_zero]
  rw [← hres μ₁ h₁, hsym, hres μ₂ h₂]

local notation "Φ" => riemannPhiKernel
/-- **Concentration for a bounded continuous perturbation symbol.**  If `P ≥ d₁/2` near `τ₀` and the
radical limit has size `≥ m/2` there, the spread radical tests make the energy of the symbol
`S_Λ - P` negative: their zero side for `ζ` is `O(S^{10} e^{-S})`. -/
theorem vonMangoldt_sub_symbol_violation_of_concentration {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp)
    {τ₀ η m d₁ : ℝ} (hη0 : 0 < η) (hm0 : 0 < m) (hd₁0 : 0 < d₁)
    (hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ P τ ∧ m / 2 ≤ ‖twistLimit 0 τ‖) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ) < 0 := by
  set D : ℝ → ℝ := fun τ => -P τ with hDdef
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_norm_paperFT_weilBumpC_le
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
  have hMp0 : 0 ≤ Mp := (abs_nonneg _).trans (hPb 0)
  set CD := Mp with hCD
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_twistTest_log_le 0 τ₀
  have hCD0 : 0 ≤ CD := by positivity
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  set c := (Real.cos (1 / 4) / 4) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set I₃ := ∫ τ : ℝ, 1 / (1 + |τ - τ₀|) ^ 3 with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun _ => by positivity
  set L₀ := m / 4 * c with hL₀
  have hL₀0 : 0 < L₀ := by positivity
  set Ctail := |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / η ^ 4) * I₃ with hCtail
  have hCtail0 : 0 ≤ Ctail := by positivity
  set goal := d₁ / 2 * L₀ ^ 2 with hgoal
  have hgoal0 : 0 < goal := by positivity
  have t1 : Tendsto (fun S : ℝ => 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have t3 : Tendsto (fun S : ℝ => Ctail / S ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have t4 : Tendsto (fun S : ℝ => 2 * π * KW * (S ^ 9 * Real.exp (-S))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul (2 * π * KW)
  obtain ⟨S, ⟨⟨⟨hE2, hE4⟩, hE5⟩, hE1⟩⟩ := (((t1.eventually (ge_mem_nhds (by linarith :
    (0 : ℝ) < m / 4))).and (t3.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 2)))).and
    (t4.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 4)))).and
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
  set f := twistTest 0 τ₀ R S with hf
  have hfd : ContDiff ℝ 2 f := contDiff_twistTest 0 τ₀ R S
  have hfs : tsupport f ⊆ Icc (-(3 * R + S)) (3 * R + S) := tsupport_twistTest hS0
  have hzero : ∀ z : ℂ, paperFT (weilRadicalTest R) z = 0 → paperFT f z = 0 := fun z hz => by
    rw [paperFT_twistTest_factor hS0, hz, zero_mul]
  have hp := hzero _ (paperFT_weilRadicalTest_half_I R)
  have hm' := hzero _ (paperFT_weilRadicalTest_neg_half_I R)
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
  have hsed : SuperExpDecay f := ⟨hfd.continuous, fun c' =>
    (hfd.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (a := 3 * R + S) fun u hu =>
        twistTest_eq_zero hS0 hu).norm.mul_right⟩
  have hHc : Continuous fun τ : ℝ => paperFT f τ :=
    hsed.differentiable_paperFT.continuous.comp Complex.continuous_ofReal
  have hHm : AEStronglyMeasurable (fun τ : ℝ => paperFT f τ) volume := hHc.aestronglyMeasurable
  have hF := integrable_normSq_paperFT hfd hfs
  have hDc : Continuous D := hPc.neg
  have hDbd : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|) := fun τ => by
    rw [hDdef, abs_neg]
    have h1 := hPb τ
    have h2 : 0 ≤ |τ - τ₀| := abs_nonneg _
    nlinarith
  have hint : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * D τ := by
    refine (hF.mul_const CD).mono' ((hHc.norm.pow 2).mul hDc).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [hDdef, abs_neg]; exact hPb τ
  have hconc := concentrated_integral_lower (H := fun τ : ℝ => paperFT f τ) (D := D)
    (t := -1) (τ₀ := τ₀) (η := η) (S := S) (d₁ := d₁) (L := L₀ * S) (K₁ := B ^ 3) (Cκ := Cκ)
    (CD := CD) hS1 hη0 h1S hd₁0 (by positivity) hCD0 (by positivity) hCκ0 hHm hint
    (fun τ hτ => by rw [hDdef]; simp only [neg_mul, one_mul, neg_neg]; exact (hnear τ hτ).1)
    (fun τ hτ => by
      have := norm_paperFT_twistTest_real_ge (α := 0) (R := R) hS0 hτ
        (hnear τ (hτ.trans h1S)).2 happrox
      rw [hL₀]; convert this using 1; ring)
    (fun τ => norm_paperFT_twistTest_real_le hS0 hCκ τ)
    hDbd
  have hmain : d₁ / 2 * (2 / S * (L₀ * S) ^ 2) -
      |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) * I₃ =
      2 * goal * S - Ctail / S ^ 2 := by
    rw [hgoal, hCtail]; field_simp
  rw [hmain] at hconc
  have hE4' : Ctail / S ^ 2 ≤ goal / 2 * S := by
    have := mul_le_mul_of_nonneg_right hE4 hS0.le
    calc Ctail / S ^ 2 = Ctail / S ^ 3 * S := by field_simp
      _ ≤ goal / 2 * S := this
  have hDneg : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ ≤ -(3 / 2 * goal * S) := by linarith
  have hWS : 2 * π * ‖zetaZeroConfig.W f f‖ ≤ goal / 4 * S := by
    have h := (hKW S hSe).1
    have hπ : 0 < π := Real.pi_pos
    calc 2 * π * ‖zetaZeroConfig.W f f‖ ≤ 2 * π * (KW * S ^ 10 * Real.exp (-S)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * π * KW * (S ^ 9 * Real.exp (-S)) * S := by ring
      _ ≤ goal / 4 * S := mul_le_mul_of_nonneg_right hE5 hS0.le
  have ha0 : 0 ≤ 3 * R + S := by linarith
  refine ⟨3 * R + S, ha0, f, hfd, hfs, hp, hm', ?_⟩
  have hfsa := hfs
  have hΛi := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfsa (fun n => (Λ n : ℝ))
  have hPi : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * P τ := by
    refine hint.neg.congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.neg_apply, hDdef]; ring
  have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * (3 * R + S))⌋₊ (τ / (2 * π)) - P τ) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * (3 * R + S))⌋₊ (τ / (2 * π))) -
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ := by
    rw [← integral_sub hΛi hPi]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only; ring
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hfd hfsa hp hm'
  have hWre : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * (3 * R + S))⌋₊ (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hW, Complex.ofReal_re]; field_simp
  have hre := Complex.re_le_norm (zetaZeroConfig.W f f)
  have hPD : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ = -∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ := by
    rw [← integral_neg]; congr 1; funext τ; simp only [hDdef]; ring
  rw [hsplit, hWre, hPD]
  have hπ : 0 < π := Real.pi_pos
  have hre2 : 2 * π * (zetaZeroConfig.W f f).re ≤ 2 * π * ‖zetaZeroConfig.W f f‖ :=
    mul_le_mul_of_nonneg_left hre (by positivity)
  have hgS : 0 < goal * S := by positivity
  linarith


/-- **Beurling rigidity of Weil positivity.**  Perturb the von Mangoldt prime measure by a finite
signed measure `μ₁ - μ₂` carried by `[ε, ∞)`, `ε > 0`: prime atoms may be added, removed or moved to
arbitrary positions, and continuous mass is allowed.  If the resulting Weil symbol
`S_Λ(τ) - ∫ 2cos(τu) d(μ₁ - μ₂)(u)` has nonnegative energy on every polar-constrained `C²` test at
every level, then `μ₁ = μ₂`.

If the perturbation symbol is positive somewhere, spread radical tests concentrated there have
negative energy.  If it is nonpositive everywhere, probes supported in `[-ε/4, ε/4]` see no atoms and
force it to vanish, and Fourier uniqueness of the symmetrized measures gives `μ₁ = μ₂`. -/
theorem vonMangoldt_sub_measure_weilPositive_eq {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {ε : ℝ} (hε : 0 < ε) (h₁ : μ₁ (Iio ε) = 0) (h₂ : μ₂ (Iio ε) = 0)
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) -
          (cosineSymbol μ₁ τ - cosineSymbol μ₂ τ))) :
    μ₁ = μ₂ := by
  set P : ℝ → ℝ := fun τ => cosineSymbol μ₁ τ - cosineSymbol μ₂ τ with hPdef
  have hPc : Continuous P := continuous_cosineSymbol.sub continuous_cosineSymbol
  have hPb : ∀ τ, |P τ| ≤ 2 * μ₁.real univ + 2 * μ₂.real univ := fun τ => by
    simp only [hPdef]
    have := abs_cosineSymbol_le (μ := μ₁) τ
    have := abs_cosineSymbol_le (μ := μ₂) τ
    exact (abs_sub _ _).trans (by linarith)
  by_cases hall : ∀ τ, P τ ≤ 0
  · have hzero := cosineSymbol_sub_eq_zero_of_nonpos hε h₁ h₂ hall
    exact eq_of_cosineSymbol_eq hε h₁ h₂ fun τ => by linarith [hzero τ]
  push Not at hall
  obtain ⟨τ₁, hτ₁⟩ := hall
  exfalso
  set d₁ := P τ₁ with hd₁
  obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
    (hPc.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
  have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ P τ := by
    intro τ hτ
    have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  have hev := ((eventually_radicalLimit_shift_ne_zero 0 τ₁).and
    (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0))))
  obtain ⟨τ₀, h0, hball⟩ := hev.exists
  have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
  have hlim0 : twistLimit 0 τ₀ ≠ 0 := by
    unfold twistLimit
    simp only [Complex.ofReal_zero, add_zero, neg_zero] at h0 ⊢
    exact mul_ne_zero (mul_ne_zero h0 h0) h0
  set m := ‖twistLimit 0 τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hlim0
  obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
    ((continuous_twistLimit_real 0).continuousAt (x := τ₀)) (m / 2) (by linarith)
  set η := min (η₁ / 2) (η₂ / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ P τ ∧ m / 2 ≤ ‖twistLimit 0 τ‖ := by
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
  obtain ⟨a, ha, f, hfd, hfs, hp, hm', hneg⟩ :=
    vonMangoldt_sub_symbol_violation_of_concentration hPc hPb hη0 hm0 hτ₁ hnear
  linarith [hpos a ha f hfd hfs hp hm']


theorem cosineSymbol_smul_dirac {c : ℝ} (hc : 0 ≤ c) (u τ : ℝ) :
    cosineSymbol (c.toNNReal • Measure.dirac u) τ = 2 * c * Real.cos (τ * u) := by
  unfold cosineSymbol
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, Real.coe_toNNReal _ hc,
    smul_eq_mul]; ring

/-- **No prime atom can be moved.**  Moving an atom of mass `c > 0` of the prime measure from a
position `u₀ > 0` to a different position `u₁ > 0` destroys Weil positivity. -/
theorem vonMangoldt_move_atom_not_weilPositive {u₀ u₁ c : ℝ} (hu₀ : 0 < u₀) (hu₁ : 0 < u₁)
    (hne : u₀ ≠ u₁) (hc : 0 < c) :
    ¬ (∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) -
          (2 * c * Real.cos (τ * u₁) - 2 * c * Real.cos (τ * u₀)))) := by
  intro hpos
  set ε := min u₀ u₁ with hεdef
  have hε : 0 < ε := lt_min hu₀ hu₁
  have hnull : ∀ u : ℝ, ε ≤ u → (c.toNNReal • Measure.dirac u) (Iio ε) = 0 := by
    intro u hu
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (by simpa using hu), smul_zero]
  have h := vonMangoldt_sub_measure_weilPositive_eq (μ₁ := c.toNNReal • Measure.dirac u₁)
    (μ₂ := c.toNNReal • Measure.dirac u₀) hε (hnull u₁ (min_le_right _ _))
    (hnull u₀ (min_le_left _ _)) (by
      intro a ha f hf hfs hp hm
      have := hpos a ha f hf hfs hp hm
      simpa only [cosineSymbol_smul_dirac hc.le] using this)
  have h1 := congrArg (fun μ : Measure ℝ => μ {u₁}) h
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
    Set.indicator_of_mem (Set.mem_singleton u₁), Set.indicator_of_notMem
      (show u₀ ∉ ({u₁} : Set ℝ) from hne), Pi.one_apply, smul_zero] at h1
  have hpos' : (0 : ENNReal) < c.toNNReal • (1 : ENNReal) := by
    rw [ENNReal.smul_def, smul_eq_mul, mul_one]
    exact ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hc)
  exact hpos'.ne' h1

end RHTower
