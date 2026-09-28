import GaloisForLFunctions.RHTower.WeilPositivityBeurlingPerturbationRigidity

/-!
# Regular rigidity of Weil positivity: oscillating perturbations of the prime weights

Fix the archimedean term and the pole of `ζ` and perturb the von Mangoldt weights to `Λ + w`.

**Theorem** (`vonMangoldt_add_eq_zero_of_symbol`).  Suppose the atoms of `w` pair with the tests
through a continuous symbol `P` of linear growth:
`2π ∑_n w(n) n^{-1/2} φ_f(log n) = ∫ |h_f|² P` for every `C²` test of compact support.  If `Λ + w` is
Weil-positive, then `w(n) = 0` for all `n ≥ 2`.  The three steps:
* concentrated radical tests force `P ≤ 0` everywhere
  (`vonMangoldt_sub_symbol_violation_of_concentration_linear`);
* probes supported in `[-log 2/4, log 2/4]` see no atoms, forcing `P ≡ 0`;
* two-point resonators read off each `w(n)`.

**Theorem** (`vonMangoldt_add_oscillating_eq_zero`).  If the partial sums `B(n) = ∑_{2 ≤ k ≤ n} b(k)`
satisfy `|B(n)| ≤ K n^θ` with `θ < 1/2`, then Weil positivity of `Λ + c b` forces `c b(n) = 0` for
`n ≥ 2`.  The symbol is the
Abel-summed series `2 ∑_n B(n)(g_τ(n) - g_τ(n+1))` with `g_τ(x) = x^{-1/2} cos(τ log x)`.  It converges
absolutely because `|g_τ(n) - g_τ(n+1)| ≤ (|τ| + 1/2) n^{-3/2}` and `∑ n^{θ - 3/2} < ∞`, and it is the
boundary value of
`2 Re ∑_{n ≥ 2} b(n) n^{-1/2-iτ}`.  These perturbations are in general not summable against
`n^{-1/2}`; every real non-principal Dirichlet character qualifies.

**Corollary** (`vonMangoldt_add_chiFour_weilPositive_eq_zero`).  Weil positivity of `Λ + c χ₋₄`
forces `c = 0`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

local notation "Φ" => riemannPhiKernel

theorem nonneg_of_linear_bound {P : ℝ → ℝ} {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) :
    0 ≤ Mp := by
  have := (abs_nonneg _).trans (hPb 0)
  simpa using this

theorem linear_bound_shift {x Mp τ : ℝ} (h : |x| ≤ Mp * (1 + |τ|)) (hMp0 : 0 ≤ Mp) (τ₀ : ℝ) :
    |x| ≤ Mp * (1 + |τ₀|) * (1 + |τ - τ₀|) := by
  have h2 : |τ| ≤ |τ₀| + |τ - τ₀| := by
    calc |τ| = |τ₀ + (τ - τ₀)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have h3 : 0 ≤ |τ - τ₀| := abs_nonneg _
  have h4 : 0 ≤ |τ₀| := abs_nonneg _
  calc |x| ≤ Mp * (1 + |τ|) := h
    _ ≤ Mp * (1 + |τ₀| + |τ - τ₀|) := mul_le_mul_of_nonneg_left (by linarith) hMp0
    _ ≤ Mp * (1 + |τ₀|) * (1 + |τ - τ₀|) := by
        nlinarith [mul_nonneg hMp0 (mul_nonneg h4 h3)]

/-- `|h_f|² P` is integrable for a `C²` test of compact support and a continuous `P` of linear
growth: `|h_f(τ)| ≤ K/(1+|τ|)²`. -/
theorem integrable_normSq_paperFT_mul_of_linear {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {P : ℝ → ℝ} (hPc : Continuous P) {Mp : ℝ}
    (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) :
    Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * P τ := by
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => by
    have := hfs (subset_tsupport f hu); exact abs_le.mpr ⟨this.1, this.2⟩
  obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hf hfs
  have hHc : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hf.continuous.integrable_of_hasCompactSupport
      hfc)).norm.pow 2
  set K := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hMp0 : 0 ≤ Mp := nonneg_of_linear_bound hPb
  have hdec : ∀ τ : ℝ, ‖paperFT f τ‖ ≤ K / (1 + |τ|) ^ 2 := fun τ => by
    have := norm_paperFT_le_decay hf hsupp (τ : ℂ)
    simpa using this
  refine ((integrable_inv_one_add_abs_sub_cube 0).const_mul (K ^ 2 * Mp)).mono'
    (hHc.mul hPc).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  have h1 : 0 < 1 + |τ| := by positivity
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sub_zero]
  have hd := hdec τ
  have hd2 : ‖paperFT f τ‖ ^ 2 ≤ (K / (1 + |τ|) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hd 2
  calc ‖paperFT f τ‖ ^ 2 * |P τ| ≤ (K / (1 + |τ|) ^ 2) ^ 2 * (Mp * (1 + |τ|)) :=
        mul_le_mul hd2 (hPb τ) (abs_nonneg _) (by positivity)
    _ = K ^ 2 * Mp * (1 / (1 + |τ|) ^ 3) := by field_simp

/-- **Concentration for a perturbation symbol of linear growth.**  If `P ≥ d₁/2` near `τ₀` and the
radical limit has size `≥ m/2` there, the spread radical tests make the energy of the symbol
`S_Λ - P` negative: their zero side for `ζ` is `O(S^{10} e^{-S})`. -/
theorem vonMangoldt_sub_symbol_violation_of_concentration_linear {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|))
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
  have hMp0 : 0 ≤ Mp := nonneg_of_linear_bound hPb
  obtain ⟨CD, hCD⟩ : ∃ CD : ℝ, CD = Mp * (1 + |τ₀|) := ⟨_, rfl⟩
  have hCD0' : 0 ≤ CD := by rw [hCD]; positivity
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_twistTest_log_le 0 τ₀
  have hCD0 : 0 ≤ CD := hCD0'
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
    rw [hDdef, abs_neg, hCD]; exact linear_bound_shift (hPb τ) hMp0 τ₀
  have hint : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * D τ :=
    integrable_normSq_paperFT_mul_of_linear hfd hfs hDc (Mp := Mp) fun τ => by
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


theorem floor_exp_half_log_two : ⌊Real.exp (2 * (Real.log 2 / 4))⌋₊ = 1 := by
  rw [Nat.floor_eq_iff (Real.exp_pos _).le]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · rw [Nat.cast_one]; exact Real.one_le_exp (by positivity)
  · rw [Nat.cast_one, one_add_one_eq_two]
    calc Real.exp (2 * (Real.log 2 / 4)) < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)

/-- **Regular rigidity of Weil positivity.**  Let `w` be a perturbation of the von Mangoldt weights
whose prime atoms pair with the tests through a continuous symbol `P` of linear growth:
`2π ∑_n w(n) n^{-1/2} φ_f(log n) = ∫ |h_f|² P` for every `C²` test of compact support.  If the
weights `Λ + w` are Weil-positive, then `w(n) = 0` for all `n ≥ 2`.

Concentrated radical tests force `P ≤ 0` everywhere; prime-blind probes supported in
`[-log 2/4, log 2/4]` then force `P ≡ 0`; two-point resonators finally read off each `w(n)`. -/
theorem vonMangoldt_add_eq_zero_of_symbol {w : ℕ → ℝ} {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|))
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ)
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  -- the energy identity
  have henergy : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ) := by
    intro a ha f hf hfs
    rw [integral_weilAtomSymbol_eq_sub hf hfs]
    have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, ((Λ n : ℝ) + w n - Λ n) / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
      Finset.sum_congr rfl fun n _ => by ring_nf
    rw [hsum, hpair a ha f hf hfs, ← integral_sub
      (integrable_normSq_paperFT_mul_weilAtomSymbol_of hf hfs (fun n => (Λ n : ℝ)))
      (integrable_normSq_paperFT_mul_of_linear hf hfs hPc hPb)]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only; ring
  -- step 1: `P ≤ 0` everywhere
  have hle : ∀ τ, P τ ≤ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨τ₁, hτ₁⟩ := hall
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
      vonMangoldt_sub_symbol_violation_of_concentration_linear hPc hPb hη0 hm0 hτ₁ hnear
    have := hpos a ha f hfd hfs hp hm'
    rw [henergy a ha f hfd hfs] at this
    linarith
  -- step 2: `P ≡ 0` from prime-blind probes
  have hzero : ∀ τ₀, P τ₀ = 0 := by
    intro τ₀
    have hε : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    set g := smallProbe (Real.log 2) τ₀ with hgdef
    have hg := contDiff_smallProbe (Real.log 2) τ₀
    have hgs := tsupport_smallProbe hε τ₀
    have hgs' : tsupport g ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) := hgs
    have hint0 := hpair (Real.log 2 / 4) (by positivity) g hg hgs'
    rw [floor_exp_half_log_two] at hint0
    simp only [Finset.Icc_eq_empty (by norm_num : ¬ (2 ≤ 1)), Finset.sum_empty, mul_zero] at hint0
    obtain ⟨hgc, -, -, -, -⟩ := weilTest_self_data hg hgs'
    have hHc : Continuous fun τ : ℝ => ‖paperFT g τ‖ ^ 2 :=
      (continuous_paperFT_real_of_integrable (hg.continuous.integrable_of_hasCompactSupport
        hgc)).norm.pow 2
    set F : ℝ → ℝ := fun τ => ‖paperFT g τ‖ ^ 2 * -P τ with hFdef
    have hFc : Continuous F := hHc.mul hPc.neg
    have hF0 : 0 ≤ F := fun τ => mul_nonneg (sq_nonneg _) (by linarith [hle τ])
    have hFi : Integrable F :=
      (integrable_normSq_paperFT_mul_of_linear hg hgs' hPc hPb).neg.congr
        (Eventually.of_forall fun τ => by simp only [Pi.neg_apply, hFdef]; ring)
    have hFint : ∫ τ, F τ = 0 := by
      have e : F = fun τ : ℝ => -(‖paperFT g τ‖ ^ 2 * P τ) := by funext τ; simp only [hFdef]; ring
      rw [e, integral_neg, ← hint0, neg_zero]
    have hae := (integral_eq_zero_iff_of_nonneg hF0 hFi).mp hFint
    have hz : F = 0 := (hFc.ae_eq_iff_eq volume continuous_const).mp hae
    have hτ₀ := congrFun hz τ₀
    simp only [hFdef, Pi.zero_apply] at hτ₀
    have hne : ‖paperFT g τ₀‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr
      (paperFT_smallProbe_ne_zero hε τ₀))
    have := (mul_eq_zero.mp hτ₀).resolve_left hne
    linarith
  -- step 3: two-point resonators read off `w(n₀)`
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
    have : Real.exp (Real.log N) ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by rw [hadef]; linarith)
    rwa [Real.exp_log (by linarith)] at this
  have hpairF := hpair a ha F hF2 hFs
  have hPint : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * P τ = 0 := by
    simp only [hzero, mul_zero, integral_zero]
  rw [hPint] at hpairF
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
    have := mul_eq_zero.mp hpairF
    rcases this with h | h
    · exfalso; have : (2 : ℝ) * π ≠ 0 := by positivity
      exact this h
    · exact h
  rcases mul_eq_zero.mp h2 with h | h
  · rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hsq.ne'
  · exfalso; linarith

/-- `g_τ(x) = x^{-1/2} cos(τ log x)`. -/
def halfCos (τ x : ℝ) : ℝ := Real.cos (τ * Real.log x) / Real.sqrt x

/-- The Abel kernel `g_τ(n) - g_τ(n+1)`. -/
def halfPowerAbelKernel (τ : ℝ) (n : ℕ) : ℝ := halfCos τ n - halfCos τ (n + 1)

theorem hasDerivAt_halfCos (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (halfCos τ)
      (-(τ * Real.sin (τ * Real.log x)) / x / Real.sqrt x -
        Real.cos (τ * Real.log x) / (2 * Real.sqrt x * x)) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : HasDerivAt (fun y => Real.cos (τ * Real.log y))
      (-Real.sin (τ * Real.log x) * (τ * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul τ).cos
  have h2 := Real.hasDerivAt_sqrt hx.ne'
  have h3 := h1.div h2 hs.ne'
  refine h3.congr_deriv ?_
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  field_simp
  rw [show Real.sqrt x ^ 2 = x by rw [sq]; exact hsq]
  ring

theorem abs_deriv_halfCos_le (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    |-(τ * Real.sin (τ * Real.log x)) / x / Real.sqrt x -
        Real.cos (τ * Real.log x) / (2 * Real.sqrt x * x)| ≤
      (|τ| + 1 / 2) / (x * Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hxs : 0 < x * Real.sqrt x := mul_pos hx hs
  have e : -(τ * Real.sin (τ * Real.log x)) / x / Real.sqrt x -
      Real.cos (τ * Real.log x) / (2 * Real.sqrt x * x) =
      (-(τ * Real.sin (τ * Real.log x)) - Real.cos (τ * Real.log x) / 2) / (x * Real.sqrt x) := by
    field_simp
  rw [e, abs_div, abs_of_pos hxs]
  refine div_le_div_of_nonneg_right ?_ hxs.le
  have h1 := Real.abs_sin_le_one (τ * Real.log x)
  have h2 := Real.abs_cos_le_one (τ * Real.log x)
  calc |-(τ * Real.sin (τ * Real.log x)) - Real.cos (τ * Real.log x) / 2|
      ≤ |τ * Real.sin (τ * Real.log x)| + |Real.cos (τ * Real.log x) / 2| := by
        rw [show -(τ * Real.sin (τ * Real.log x)) - Real.cos (τ * Real.log x) / 2 =
          -(τ * Real.sin (τ * Real.log x) + Real.cos (τ * Real.log x) / 2) by ring, abs_neg]
        exact abs_add_le _ _
    _ ≤ |τ| + 1 / 2 := by
        rw [abs_mul, abs_div, abs_two]
        have := mul_le_mul_of_nonneg_left h1 (abs_nonneg τ)
        linarith

/-- `|g_τ(n) - g_τ(n+1)| ≤ (|τ| + 1/2) n^{-3/2}` for `n ≥ 1`. -/
theorem abs_halfPowerAbelKernel_le (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |halfPowerAbelKernel τ n| ≤ (|τ| + 1 / 2) / ((n : ℝ) * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Icc (n : ℝ) (n + 1))
    (f := halfCos τ) (x := (n : ℝ)) (y := (n : ℝ) + 1)
    (C := (|τ| + 1 / 2) / ((n : ℝ) * Real.sqrt n))
    (fun x hx => (hasDerivAt_halfCos τ (lt_of_lt_of_le hn0 hx.1)).differentiableAt)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
      rw [(hasDerivAt_halfCos τ hx0).deriv, Real.norm_eq_abs]
      refine (abs_deriv_halfCos_le τ hx0).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul hx.1 (Real.sqrt_le_sqrt hx.1) (Real.sqrt_nonneg _) hx0.le))
    (convex_Icc _ _) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show (n : ℝ) + 1 - n = 1 by ring, abs_one, mul_one] at hmvt
  unfold halfPowerAbelKernel
  rw [abs_sub_comm]
  exact_mod_cast hmvt



/-- The partial sums `∑_{2 ≤ k ≤ n} b(k)`. -/
def partialFrom2 (b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 2 n, b k

/-- The Abel-summed symbol `2 ∑_n B(n) (g_τ(n) - g_τ(n+1))` of the weights `b`, with
`B(n) = ∑_{2 ≤ k ≤ n} b(k)`: the boundary value of `2 Re ∑_{n ≥ 2} b(n) n^{-1/2 - iτ}`. -/
def oscSymbol (b : ℕ → ℝ) (τ : ℝ) : ℝ := 2 * ∑' n : ℕ, partialFrom2 b n * halfPowerAbelKernel τ n

theorem partialFrom2_zero (b : ℕ → ℝ) : partialFrom2 b 0 = 0 := by simp [partialFrom2]

/-- The comparison weight `n^θ/(n √n) = n^{θ - 3/2}`. -/
def growthWeight (θ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ θ / ((n : ℝ) * Real.sqrt n)

theorem growthWeight_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ growthWeight θ n := by
  unfold growthWeight; positivity

/-- `∑ n^{θ - 3/2} < ∞` for `θ < 1/2`. -/
theorem summable_growthWeight {θ : ℝ} (hθ : θ < 1 / 2) : Summable (growthWeight θ) := by
  have h := Real.summable_nat_rpow_inv.mpr (show (1 : ℝ) < 3 / 2 - θ by linarith)
  refine h.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [growthWeight, Real.zero_rpow (show (3 / 2 - θ : ℝ) ≠ 0 by linarith)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    unfold growthWeight
    have h1 : (n : ℝ) * Real.sqrt n = (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn0.le (by norm_num)]; norm_num
    rw [h1, ← Real.rpow_sub hn0, ← Real.rpow_neg hn0.le]
    congr 1; ring

theorem abs_partialFrom2_mul_kernel_le {b : ℕ → ℝ} {K θ : ℝ}
    (hB : ∀ n, |partialFrom2 b n| ≤ K * (n : ℝ) ^ θ) (τ : ℝ) (n : ℕ) :
    |partialFrom2 b n * halfPowerAbelKernel τ n| ≤ K * (|τ| + 1 / 2) * growthWeight θ n := by
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hB 1)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [partialFrom2_zero, growthWeight]
  · rw [abs_mul]
    have h := abs_halfPowerAbelKernel_le τ hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    calc |partialFrom2 b n| * |halfPowerAbelKernel τ n|
        ≤ K * (n : ℝ) ^ θ * ((|τ| + 1 / 2) / ((n : ℝ) * Real.sqrt n)) :=
          mul_le_mul (hB n) h (abs_nonneg _) (by positivity)
      _ = K * (|τ| + 1 / 2) * growthWeight θ n := by unfold growthWeight; ring

theorem summable_osc {b : ℕ → ℝ} {K θ : ℝ} (hB : ∀ n, |partialFrom2 b n| ≤ K * (n : ℝ) ^ θ) (hθ : θ < 1 / 2) (τ : ℝ) :
    Summable fun n => partialFrom2 b n * halfPowerAbelKernel τ n :=
  Summable.of_norm_bounded ((summable_growthWeight hθ).mul_left (K * (|τ| + 1 / 2)))
    fun n => by rw [Real.norm_eq_abs]; exact abs_partialFrom2_mul_kernel_le hB τ n

/-- `|oscSymbol b τ| ≤ 2KZ(1 + |τ|)` with `Z = ∑ n^{-3/2}`. -/
theorem abs_oscSymbol_le {b : ℕ → ℝ} {K θ : ℝ} (hB : ∀ n, |partialFrom2 b n| ≤ K * (n : ℝ) ^ θ) (hθ : θ < 1 / 2) (τ : ℝ) :
    |oscSymbol b τ| ≤ 2 * K * (∑' n : ℕ, growthWeight θ n) * (1 + |τ|) := by
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hB 1)
  set Z := ∑' n : ℕ, growthWeight θ n with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => growthWeight_nonneg θ n
  have hs := summable_osc hB hθ τ
  have h1 : |∑' n : ℕ, partialFrom2 b n * halfPowerAbelKernel τ n| ≤
      ∑' n : ℕ, |partialFrom2 b n * halfPowerAbelKernel τ n| := by
    have := norm_tsum_le_tsum_norm hs.norm
    simp only [Real.norm_eq_abs] at this
    exact this
  have h2 : ∑' n : ℕ, |partialFrom2 b n * halfPowerAbelKernel τ n| ≤
      ∑' n : ℕ, K * (|τ| + 1 / 2) * (growthWeight θ n) :=
    Summable.tsum_le_tsum (fun n => abs_partialFrom2_mul_kernel_le hB τ n) hs.abs
      ((summable_growthWeight hθ).mul_left _)
  rw [tsum_mul_left, ← hZ] at h2
  have h3 : K * (|τ| + 1 / 2) * Z ≤ K * Z * (1 + |τ|) := by
    have : |τ| + 1 / 2 ≤ 1 + |τ| := by linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hK0 hZ0)
    linarith
  unfold oscSymbol
  rw [abs_mul, abs_two]
  have h4 := h1.trans (h2.trans h3)
  linarith

theorem continuous_halfPowerAbelKernel (n : ℕ) : Continuous fun τ => halfPowerAbelKernel τ n := by
  unfold halfPowerAbelKernel halfCos; fun_prop

theorem continuous_oscSymbol {b : ℕ → ℝ} {K θ : ℝ} (hB : ∀ n, |partialFrom2 b n| ≤ K * (n : ℝ) ^ θ) (hθ : θ < 1 / 2) :
    Continuous (oscSymbol b) := by
  rw [continuous_iff_continuousAt]
  intro τ₁
  have hOn : ContinuousOn (fun τ => ∑' n : ℕ, partialFrom2 b n * halfPowerAbelKernel τ n)
      (Ioo (τ₁ - 1) (τ₁ + 1)) := by
    refine continuousOn_tsum
      (f := fun (n : ℕ) (τ : ℝ) => partialFrom2 b n * halfPowerAbelKernel τ n)
      (u := fun n : ℕ => K * (|τ₁| + 1 + 1 / 2) * (growthWeight θ n))
      (fun n => (continuous_const.mul (continuous_halfPowerAbelKernel n)).continuousOn)
      ((summable_growthWeight hθ).mul_left _) fun n τ hτ => ?_
    rw [Real.norm_eq_abs]
    refine (abs_partialFrom2_mul_kernel_le hB τ n).trans ?_
    have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hB 1)
    have hτ : |τ| ≤ |τ₁| + 1 := by
      have := abs_sub_abs_le_abs_sub τ τ₁
      have : |τ - τ₁| < 1 := abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK0)
      (growthWeight_nonneg θ n)
  have hAt := hOn.continuousAt (Ioo_mem_nhds (show τ₁ - 1 < τ₁ by linarith)
    (show τ₁ < τ₁ + 1 by linarith))
  exact (continuousAt_const.mul hAt)


theorem abs_halfCos_natCast_le (τ : ℝ) (n : ℕ) : |halfCos τ n| ≤ 1 := by
  unfold halfCos
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs : 1 ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]; exact_mod_cast hn
    have hs0 : (0 : ℝ) < Real.sqrt n := by linarith
    rw [abs_div, abs_of_pos hs0, div_le_one hs0]
    exact (Real.abs_cos_le_one _).trans hs

theorem abs_halfPowerAbelKernel_le_two (τ : ℝ) (n : ℕ) : |halfPowerAbelKernel τ n| ≤ 2 := by
  unfold halfPowerAbelKernel
  have h1 := abs_halfCos_natCast_le τ n
  have h2 := abs_halfCos_natCast_le τ (n + 1)
  push_cast at h2
  exact (abs_sub _ _).trans (by linarith)

/-- `∫ |h_f|² (g_τ(n) - g_τ(n+1)) dτ = π (φ(log n)/√n - φ(log(n+1))/√(n+1))`. -/
theorem integral_normSq_mul_halfPowerAbelKernel {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (n : ℕ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPowerAbelKernel τ n =
      π * (weilTestEvenPart f (Real.log n) / Real.sqrt n -
        weilTestEvenPart f (Real.log ((n : ℝ) + 1)) / Real.sqrt ((n : ℝ) + 1)) := by
  have hc1 := integrable_normSq_paperFT_mul_cos hf hfs (Real.log n)
  have hc2 := integrable_normSq_paperFT_mul_cos hf hfs (Real.log ((n : ℝ) + 1))
  have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * halfPowerAbelKernel τ n) = fun τ : ℝ =>
      (1 / Real.sqrt n) * (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) -
        (1 / Real.sqrt ((n : ℝ) + 1)) *
          (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log ((n : ℝ) + 1))) := by
    funext τ; unfold halfPowerAbelKernel halfCos; ring
  rw [e, integral_sub (hc1.const_mul _) (hc2.const_mul _), integral_const_mul, integral_const_mul,
    integral_normSq_paperFT_mul_cos_eq hf hfs, integral_normSq_paperFT_mul_cos_eq hf hfs]
  unfold weilTestEvenPart; ring

/-- The weight `d(m) = φ(log m)/√m` of the Abel identity. -/
def halfPowerAbelWeight (f : ℝ → ℂ) (m : ℕ) : ℝ := weilTestEvenPart f (Real.log m) / Real.sqrt m

theorem integral_normSq_mul_oscSymbol {b : ℕ → ℝ} {K θ : ℝ} (hB : ∀ n, |partialFrom2 b n| ≤ K * (n : ℝ) ^ θ) (hθ : θ < 1 / 2)
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * oscSymbol b τ =
      2 * π * ∑' n : ℕ, partialFrom2 b n * (halfPowerAbelWeight f n - halfPowerAbelWeight f (n + 1)) := by
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hB 1)
  have hF := integrable_normSq_paperFT hf hfs
  obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hf hfs
  have hHc : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hf.continuous.integrable_of_hasCompactSupport
      hfc)).norm.pow 2
  have hlin := integrable_normSq_paperFT_mul_of_linear hf hfs (P := fun τ => |τ| + 1 / 2)
    (by fun_prop) (Mp := 1) fun τ => by rw [abs_of_nonneg (by positivity)]; linarith
  have hterm : ∀ n : ℕ, Integrable fun τ : ℝ =>
      ‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n) := by
    intro n
    refine (hF.mul_const (K * (n : ℝ) ^ θ * 2)).mono'
      (hHc.mul (continuous_const.mul (continuous_halfPowerAbelKernel n))).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hB n) (abs_halfPowerAbelKernel_le_two τ n)
      (abs_nonneg _) (by positivity)) (sq_nonneg _)
  have hnorm : Summable fun n : ℕ => ∫ τ : ℝ,
      ‖‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (((summable_growthWeight hθ).mul_left K).mul_right
        (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2)))
    calc ∫ τ : ℝ, ‖‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n)‖
        ≤ ∫ τ : ℝ, K * (growthWeight θ n) * (‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2)) :=
          integral_mono (hterm n).norm (hlin.const_mul _) fun τ => by
            rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
            have := abs_partialFrom2_mul_kernel_le hB τ n
            have h0 : 0 ≤ ‖paperFT f τ‖ ^ 2 := sq_nonneg _
            calc ‖paperFT f τ‖ ^ 2 * |partialFrom2 b n * halfPowerAbelKernel τ n|
                ≤ ‖paperFT f τ‖ ^ 2 * (K * (|τ| + 1 / 2) * (growthWeight θ n)) :=
                  mul_le_mul_of_nonneg_left this h0
              _ = K * (growthWeight θ n) * (‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2)) := by
                  ring
      _ = K * (growthWeight θ n) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2) :=
          integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hterm hnorm
  have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * oscSymbol b τ) =
      fun τ : ℝ => 2 * ∑' n : ℕ, ‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n) := by
    funext τ; unfold oscSymbol; rw [tsum_mul_left]; ring
  rw [e, integral_const_mul, ← hswap]
  have hval : ∀ n : ℕ, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n) =
      π * (partialFrom2 b n * (halfPowerAbelWeight f n - halfPowerAbelWeight f (n + 1))) := by
    intro n
    have e2 : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n)) =
        fun τ : ℝ => partialFrom2 b n * (‖paperFT f τ‖ ^ 2 * halfPowerAbelKernel τ n) := by
      funext τ; ring
    rw [e2, integral_const_mul, integral_normSq_mul_halfPowerAbelKernel hf hfs]
    unfold halfPowerAbelWeight; push_cast; ring
  rw [tsum_congr hval, tsum_mul_left]; ring

/-- **Abel summation.**  `∑_{n ≤ N} B(n)(d(n) - d(n+1)) = ∑_{2 ≤ n ≤ N} b(n) d(n) - B(N) d(N+1)`. -/
theorem sum_range_partialFrom2_mul_sub (b d : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), partialFrom2 b n * (d n - d (n + 1)) =
      ∑ n ∈ Finset.Icc 2 N, b n * d n - partialFrom2 b N * d (N + 1) := by
  induction N with
  | zero => simp [partialFrom2]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.lt_or_ge N 1 with hN | hN
    · have hN0 : N = 0 := by omega
      subst hN0
      simp [partialFrom2]
    · have hstep : partialFrom2 b (N + 1) = partialFrom2 b N + b (N + 1) := by
        unfold partialFrom2; rw [Finset.sum_Icc_succ_top (by omega)]
      have hsum : ∑ n ∈ Finset.Icc 2 (N + 1), b n * d n =
          ∑ n ∈ Finset.Icc 2 N, b n * d n + b (N + 1) * d (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
      rw [hsum, hstep]; ring

theorem tsum_partialFrom2_mul_sub {b d : ℕ → ℝ} {N : ℕ} (hd : ∀ m, N < m → d m = 0) :
    ∑' n : ℕ, partialFrom2 b n * (d n - d (n + 1)) = ∑ n ∈ Finset.Icc 2 N, b n * d n := by
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    rw [hd n (by omega), hd (n + 1) (by omega), sub_zero, mul_zero],
    sum_range_partialFrom2_mul_sub, hd (N + 1) (by omega), mul_zero, sub_zero]

/-- **Rigidity against oscillating perturbations.**  If `B(n) = ∑_{2 ≤ k ≤ n} b(k)` satisfies
`|B(n)| ≤ K n^θ` with `θ < 1/2` and the weights `Λ(n) + c b(n)` are Weil-positive, then `c b(n) = 0`
for every `n ≥ 2`.  The perturbation need not be summable against `n^{-1/2}` and may grow: every
real non-principal Dirichlet character qualifies (`θ = 0`), as do its twists by `n^{θ'}`, `θ' < 1/2`. -/
theorem vonMangoldt_add_oscillating_eq_zero {b : ℕ → ℝ} {K θ : ℝ}
    (hB : ∀ n, |partialFrom2 b n| ≤ K * (n : ℝ) ^ θ) (hθ : θ < 1 / 2) {c : ℝ}
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + c * b n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : c * b n₀ = 0 := by
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hB 1)
  set Z := ∑' n : ℕ, growthWeight θ n with hZ
  refine vonMangoldt_add_eq_zero_of_symbol (w := fun n => c * b n)
    (P := fun τ => c * oscSymbol b τ) (continuous_const.mul (continuous_oscSymbol hB hθ))
    (Mp := |c| * (2 * K * Z)) (fun τ => ?_) (fun a ha f hf hfs => ?_) hpos hn₀
  · rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((abs_oscSymbol_le hB hθ τ).trans (le_of_eq (by ring)))
      (abs_nonneg _)
  · have hint : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (c * oscSymbol b τ) =
        c * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * oscSymbol b τ := by
      rw [← integral_const_mul]; congr 1; funext τ; ring
    rw [hint, integral_normSq_mul_oscSymbol hB hθ hf hfs,
      tsum_partialFrom2_mul_sub (N := ⌊Real.exp (2 * a)⌋₊) fun m hm => ?_]
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      unfold halfPowerAbelWeight weilTestEvenPart; ring
    · unfold halfPowerAbelWeight
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      have hexp : Real.exp (2 * a) < m := (Nat.floor_lt (Real.exp_pos _).le).mp hm
      have hlog : 2 * a < Real.log m := by
        rw [← Real.log_exp (2 * a)]; exact Real.log_lt_log (Real.exp_pos _) hexp
      rw [weilTestEvenPart_eq_zero hf hfs (by rw [abs_of_nonneg (Real.log_nonneg hm1)]; exact hlog),
        zero_div]


/-- The non-principal character mod 4: `χ₋₄(n) = 1, -1, 0` for `n ≡ 1, 3`, `n` even. -/
def chiFour (n : ℕ) : ℝ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

theorem partialFrom2_chiFour (n : ℕ) :
    partialFrom2 chiFour n = if n = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 then 0 else -1 := by
  induction n with
  | zero => simp [partialFrom2]
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    · have hn0 : n = 0 := by omega
      subst hn0; simp [partialFrom2]
    · have hstep : partialFrom2 chiFour (n + 1) = partialFrom2 chiFour n + chiFour (n + 1) := by
        unfold partialFrom2; rw [Finset.sum_Icc_succ_top (by omega)]
      rw [hstep, ih]
      unfold chiFour
      split_ifs <;> (try simp only [false_or] at *) <;> first | (exfalso; omega) | norm_num

theorem abs_partialFrom2_chiFour_le (n : ℕ) : |partialFrom2 chiFour n| ≤ 1 := by
  rw [partialFrom2_chiFour]; split_ifs <;> norm_num

/-- **The character mod 4 is not a Weil-positive direction.**  If the weights `Λ(n) + c χ₋₄(n)` are
Weil-positive with the archimedean term of `ζ`, then `c = 0`.  The perturbation is not summable
against `n^{-1/2}`; its Dirichlet series `c (L(s, χ₋₄) - 1)` converges only conditionally on the
critical line. -/
theorem vonMangoldt_add_chiFour_weilPositive_eq_zero {c : ℝ}
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + c * chiFour n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    c = 0 := by
  have h := vonMangoldt_add_oscillating_eq_zero (K := 1) (θ := 0)
    (fun n => by simpa using abs_partialFrom2_chiFour_le n) (by norm_num) hpos (n₀ := 3) (by norm_num)
  have h3 : chiFour 3 = -1 := by norm_num [chiFour]
  rw [h3] at h
  linarith

end RHTower
