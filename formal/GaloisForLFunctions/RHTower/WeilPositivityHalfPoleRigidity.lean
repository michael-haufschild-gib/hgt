import GaloisForLFunctions.RHTower.WeilPositivitySparseWeightsObstruction
import GaloisForLFunctions.RHTower.WeilPositivityRegularPerturbationRigidity

/-!
# Rigidity of Weil positivity across the `√n` barrier

Fix the archimedean term and the pole of `ζ` and perturb the von Mangoldt weights to `Λ + w`.
Earlier rigidity covers perturbations whose partial sums `B(n) = ∑_{2 ≤ k ≤ n} w(k)` are
`O(n^θ)`, `θ < 1/2`.  At `θ = 1/2` the symbol of `w` acquires an atom at the origin: the
perturbation `w(n) = √n − √(n−1)` (partial sums `√n − 1`) is the boundary value of
`ζ(2s)`-type Dirichlet series with a pole at `s = 1/2`.

* **Half-pole pairing** (`pairing_sqrtStep`).  With `β(n) = √n − √(n−1)` and `φ_f` the even Weil
  test of `f`, `2π ∑_n β(n) n^{-1/2} φ_f(log n) = π |ĥ_f(0)|² + ∫ |ĥ_f|² P_β`.  Here
  `β(n)/√n = ∫_{log(n−1)}^{log n} ½ e^{(u − log n)/2} du`, the atom comes from `½ ∫_0^∞ φ_f = ½|ĥ_f(0)|²`,
  and `P_β = 2 ∑_n K_n` with `|K_n(τ)| ≤ (1 + |τ|)/(n − 1)²` is continuous of linear growth.
* **Rigidity with an atom** (`vonMangoldt_add_eq_zero_of_symbol_atom`).  If the atoms of `w` pair
  with the tests through a continuous symbol `P` of linear growth plus `m |ĥ_f(0)|²`, then Weil
  positivity of `Λ + w` forces `w = 0`.
  - Radical tests concentrated away from the origin force `P ≤ 0` (the atom is negligible there,
    `vonMangoldt_sub_symbol_atom_violation`).
  - Probes supported in `[-log 2/4, log 2/4]` force `m ≥ 0`; zero-mean probes force `P ≡ 0`; then
    `m = 0`, and two-point resonators finish.
* **Rigidity across the barrier** (`vonMangoldt_add_halfPole_eq_zero`).  If the partial sums of
  `w − κβ` satisfy `∑ |E(n)|/(n √n) < ∞` for some real `κ`, then Weil positivity of `Λ + w`
  forces `w = 0`.
* **Squares** (`vonMangoldt_add_squares_weilPositive_eq_zero`).  `Λ + c·1_{n = m²}` is
  Weil-positive only for `c = 0`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

local notation "Φ" => riemannPhiKernel

/-- **Concentration for a perturbation symbol of linear growth.**  If `P ≥ d₁/2` near `τ₀` and the
radical limit has size `≥ m/2` there, the spread radical tests make the energy of the symbol
`S_Λ - P` negative: their zero side for `ζ` is `O(S^{10} e^{-S})`. -/
theorem vonMangoldt_sub_symbol_atom_violation {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|))
    {τ₀ η m d₁ : ℝ} (hη0 : 0 < η) (hm0 : 0 < m) (hd₁0 : 0 < d₁)
    (hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ P τ ∧ m / 2 ≤ ‖twistLimit 0 τ‖)
    (hτ₀ : τ₀ ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ)) +
        M * ‖paperFT f 0‖ ^ 2 < 0 := by
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
  have hτ₀a : 0 < |τ₀| := abs_pos.mpr hτ₀
  have t6 : Tendsto (fun S : ℝ => M * ((B ^ 3) ^ 2 * Cκ ^ 4 / |τ₀| ^ 8) / S ^ 7) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨S, ⟨⟨⟨⟨hE2, hE4⟩, hE5⟩, hE6⟩, hE1⟩⟩ := ((((t1.eventually (ge_mem_nhds (by linarith :
    (0 : ℝ) < m / 4))).and (t3.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 2)))).and
    (t4.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 4)))).and
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
  have hval : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * (3 * R + S))⌋₊ (τ / (2 * π)) - P τ) =
      2 * π * (zetaZeroConfig.W f f).re + ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ := by
    rw [hsplit, hWre, hPD]; ring
  have hπ : 0 < π := Real.pi_pos
  have hre2 : 2 * π * (zetaZeroConfig.W f f).re ≤ 2 * π * ‖zetaZeroConfig.W f f‖ :=
    mul_le_mul_of_nonneg_left hre (by positivity)
  have hgS : 0 < goal * S := by positivity
  -- the atom at the origin is negligible: the test is concentrated at `τ₀ ≠ 0`
  have hf0 : ‖paperFT f 0‖ ≤ B ^ 3 * (S * (Cκ / (1 + S * |0 - τ₀|) ^ 2) ^ 2) := by
    have := norm_paperFT_twistTest_real_le (α := 0) (τ₀ := τ₀) (R := R) hS0 hCκ 0
    simpa [hB] using this
  have hden : S * |τ₀| ≤ 1 + S * |0 - τ₀| := by
    rw [zero_sub, abs_neg]; linarith
  have hSτ : 0 < S * |τ₀| := mul_pos hS0 hτ₀a
  have hf0' : ‖paperFT f 0‖ ≤ B ^ 3 * Cκ ^ 2 / (S ^ 3 * |τ₀| ^ 4) := by
    refine hf0.trans ?_
    have hB3 : 0 ≤ B ^ 3 := by positivity
    have h1 : Cκ / (1 + S * |0 - τ₀|) ^ 2 ≤ Cκ / (S * |τ₀|) ^ 2 :=
      div_le_div_of_nonneg_left hCκ0 (by positivity) (pow_le_pow_left₀ hSτ.le hden 2)
    have h2 : (Cκ / (1 + S * |0 - τ₀|) ^ 2) ^ 2 ≤ (Cκ / (S * |τ₀|) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc B ^ 3 * (S * (Cκ / (1 + S * |0 - τ₀|) ^ 2) ^ 2)
        ≤ B ^ 3 * (S * (Cκ / (S * |τ₀|) ^ 2) ^ 2) := by gcongr
      _ = B ^ 3 * Cκ ^ 2 / (S ^ 3 * |τ₀| ^ 4) := by field_simp
  have hf0sq : M * ‖paperFT f 0‖ ^ 2 ≤ M * ((B ^ 3) ^ 2 * Cκ ^ 4 / |τ₀| ^ 8) / S ^ 7 * S := by
    have hsq : ‖paperFT f 0‖ ^ 2 ≤ (B ^ 3 * Cκ ^ 2 / (S ^ 3 * |τ₀| ^ 4)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hf0' 2
    calc M * ‖paperFT f 0‖ ^ 2 ≤ M * (B ^ 3 * Cκ ^ 2 / (S ^ 3 * |τ₀| ^ 4)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hM
      _ = M * ((B ^ 3) ^ 2 * Cκ ^ 4 / |τ₀| ^ 8) / S ^ 7 * S := by field_simp
  have hE6' : M * ((B ^ 3) ^ 2 * Cκ ^ 4 / |τ₀| ^ 8) / S ^ 7 * S ≤ goal / 8 * S :=
    mul_le_mul_of_nonneg_right hE6 hS0.le
  have h2 : 2 * π * (zetaZeroConfig.W f f).re + (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ) +
      M * ‖paperFT f 0‖ ^ 2 < 0 := by
    have a1 := hDneg; have a2 := hWS; have a3 := hre2; have a4 := hf0sq; have a5 := hE6'
    have a6 := hgS
    linarith
  rw [← hval] at h2
  exact h2



/-! ### Zero-mean probes -/

/-- The cosine transform `v ↦ ∫ κ(x) cos(vx) dx` of the smooth bump `κ`. -/
def bumpCosFT (v : ℝ) : ℝ := ∫ x : ℝ, weilBump x * Real.cos (v * x)

theorem hasCompactSupport_weilBump : HasCompactSupport (weilBump : ℝ → ℝ) :=
  weilBump.hasCompactSupport

theorem paperFT_weilBumpC_real (v : ℝ) : paperFT weilBumpC v = (bumpCosFT v : ℂ) := by
  unfold paperFT bumpCosFT weilBumpC
  have hsin : ∫ x : ℝ, weilBump x * Real.sin (v * x) = 0 := by
    have h := integral_neg_eq_self (fun x : ℝ => weilBump x * Real.sin (v * x)) volume
    simp only [weilBump.neg, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  have hc : Integrable (fun x : ℝ => weilBump x * Real.cos (v * x)) :=
    (weilBump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_weilBump.mul_right
  have hs : Integrable (fun x : ℝ => weilBump x * Real.sin (v * x)) :=
    (weilBump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_weilBump.mul_right
  have e : (fun x : ℝ => ((weilBump x : ℝ) : ℂ) * Complex.exp (I * (v : ℂ) * x)) =
      fun x : ℝ => ((weilBump x * Real.cos (v * x) : ℝ) : ℂ) +
        ((weilBump x * Real.sin (v * x) : ℝ) : ℂ) * I := by
    funext x
    rw [show I * (v : ℂ) * (x : ℂ) = ((v * x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have i1 : Integrable (fun x : ℝ => ((weilBump x * Real.cos (v * x) : ℝ) : ℂ)) := hc.ofReal
  have i2 : Integrable (fun x : ℝ => ((weilBump x * Real.sin (v * x) : ℝ) : ℂ) * I) :=
    hs.ofReal.mul_const I
  rw [e, integral_add i1 i2, integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal, hsin]
  simp

theorem one_add_cos_pos_of_small {t : ℝ} (ht : |t| < π) : 0 < 1 + Real.cos t := by
  have h1 : -1 < Real.cos t := by
    have hc : Real.cos t = Real.cos |t| := (Real.cos_abs t).symm
    rw [hc]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t) le_rfl ht
    rw [Real.cos_pi] at this
    linarith
  linarith

theorem one_sub_cos_pos_of_small {t : ℝ} (ht0 : t ≠ 0) (ht : |t| < π) : 0 < 1 - Real.cos t := by
  have hc : Real.cos t = Real.cos |t| := (Real.cos_abs t).symm
  rw [hc]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl ht.le (abs_pos.mpr ht0)
  rw [Real.cos_zero] at this
  linarith

/-- `|κ̂(v)| < κ̂(0)` for `v ≠ 0`: the bump is nonnegative, even, and equal to one near the
origin. -/
theorem abs_bumpCosFT_lt {v : ℝ} (hv : v ≠ 0) : |bumpCosFT v| < bumpCosFT 0 := by
  have hint : ∀ g : ℝ → ℝ, Continuous g →
      Integrable (fun x : ℝ => weilBump x * g x) := fun g hg =>
    (weilBump.continuous.mul hg).integrable_of_hasCompactSupport
      hasCompactSupport_weilBump.mul_right
  have h0 : bumpCosFT 0 = ∫ x : ℝ, weilBump x := by
    unfold bumpCosFT; simp
  have hb1 : Integrable (fun x : ℝ => weilBump x) :=
    weilBump.continuous.integrable_of_hasCompactSupport hasCompactSupport_weilBump
  set x₀ : ℝ := 1 / (8 * (1 + |v|)) with hx₀
  have hx₀pos : 0 < x₀ := by positivity
  have hx₀le : x₀ ≤ 1 / 8 := by
    rw [hx₀]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith [abs_nonneg v]
  have hb₀ : weilBump x₀ = 1 := weilBump.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos hx₀pos]; exact hx₀le)
  have hvx : |v * x₀| < π := by
    rw [abs_mul, abs_of_pos hx₀pos, hx₀]
    have : |v| * (1 / (8 * (1 + |v|))) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; nlinarith [abs_nonneg v]
    linarith [Real.pi_gt_three]
  have hvx0 : v * x₀ ≠ 0 := mul_ne_zero hv hx₀pos.ne'
  have hpos1 : 0 < ∫ x : ℝ, weilBump x * (1 - Real.cos (v * x)) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (weilBump.continuous.mul (by fun_prop)) hasCompactSupport_weilBump.mul_right
      (fun x => mul_nonneg (weilBump.nonneg) (by linarith [Real.cos_le_one (v * x)])) ?_
    rw [hb₀, one_mul]; exact (one_sub_cos_pos_of_small hvx0 hvx).ne'
  have hpos2 : 0 < ∫ x : ℝ, weilBump x * (1 + Real.cos (v * x)) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (weilBump.continuous.mul (by fun_prop)) hasCompactSupport_weilBump.mul_right
      (fun x => mul_nonneg (weilBump.nonneg) (by linarith [Real.neg_one_le_cos (v * x)])) ?_
    have : weilBump (0 : ℝ) = 1 := weilBump.one_of_mem_closedBall
      (Metric.mem_closedBall_self weilBump.rIn_pos.le)
    rw [this]; simp
  have e1 : ∫ x : ℝ, weilBump x * (1 - Real.cos (v * x)) = bumpCosFT 0 - bumpCosFT v := by
    rw [h0]; unfold bumpCosFT
    rw [← integral_sub hb1 (hint _ (by fun_prop))]
    congr 1; funext x; ring
  have e2 : ∫ x : ℝ, weilBump x * (1 + Real.cos (v * x)) = bumpCosFT 0 + bumpCosFT v := by
    rw [h0]; unfold bumpCosFT
    rw [← integral_add hb1 (hint _ (by fun_prop))]
    congr 1; funext x; ring
  rw [abs_lt]; constructor <;> linarith

theorem bumpCosFT_neg (v : ℝ) : bumpCosFT (-v) = bumpCosFT v := by
  unfold bumpCosFT; congr 1; funext x; rw [neg_mul, Real.cos_neg]

theorem bumpCosFT_zero_pos : 0 < bumpCosFT 0 := by
  have := abs_bumpCosFT_lt (v := 1) one_ne_zero
  linarith [abs_nonneg (bumpCosFT 1)]

theorem paperFT_smallProbe_real {ε : ℝ} (hε : 0 < ε) (t τ : ℝ) :
    paperFT (smallProbe ε t) τ = ((ε * bumpCosFT (ε * (τ - t)) : ℝ) : ℂ) := by
  unfold smallProbe
  rw [paperFT_twistModulate, paperFT_comp_div hε]
  have : (ε : ℂ) * ((τ : ℂ) + ((-t : ℝ) : ℂ)) = ((ε * (τ - t) : ℝ) : ℂ) := by push_cast; ring
  rw [this, paperFT_weilBumpC_real]
  push_cast; ring

theorem continuous_smallProbe (ε t : ℝ) : Continuous (smallProbe ε t) :=
  (contDiff_smallProbe ε t).continuous

theorem hasCompactSupport_smallProbe {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasCompactSupport (smallProbe ε t) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (tsupport_smallProbe hε t)

/-- The zero-mean probe `p_t − (κ̂(εt)/κ̂(0)) p_0`, `p_s` the small probe centred at `s`: its
transform vanishes at `0` and not at `t ≠ 0`. -/
def zeroMeanProbe (ε t : ℝ) : ℝ → ℂ := fun x =>
  smallProbe ε t x - ((bumpCosFT (ε * t) / bumpCosFT 0 : ℝ) : ℂ) * smallProbe ε 0 x

theorem contDiff_zeroMeanProbe (ε t : ℝ) : ContDiff ℝ 2 (zeroMeanProbe ε t) :=
  (contDiff_smallProbe ε t).sub (contDiff_const.mul (contDiff_smallProbe ε 0))

theorem tsupport_zeroMeanProbe {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    tsupport (zeroMeanProbe ε t) ⊆ Icc (-(ε / 4)) (ε / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  apply hx
  have h1 : smallProbe ε t x = 0 := image_eq_zero_of_notMem_tsupport
    fun hm => h (tsupport_smallProbe hε t hm)
  have h2 : smallProbe ε 0 x = 0 := image_eq_zero_of_notMem_tsupport
    fun hm => h (tsupport_smallProbe hε 0 hm)
  simp [zeroMeanProbe, h1, h2]

theorem paperFT_zeroMeanProbe_real {ε : ℝ} (hε : 0 < ε) (t τ : ℝ) :
    paperFT (zeroMeanProbe ε t) τ = ((ε * bumpCosFT (ε * (τ - t)) -
      bumpCosFT (ε * t) / bumpCosFT 0 * (ε * bumpCosFT (ε * τ)) : ℝ) : ℂ) := by
  have i1 : Integrable (fun x : ℝ => smallProbe ε t x * cexp (I * (τ : ℂ) * x)) :=
    ((continuous_smallProbe ε t).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_smallProbe hε t).mul_right
  have i2 : Integrable (fun x : ℝ => ((bumpCosFT (ε * t) / bumpCosFT 0 : ℝ) : ℂ) *
      (smallProbe ε 0 x * cexp (I * (τ : ℂ) * x))) :=
    (((continuous_smallProbe ε 0).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_smallProbe hε 0).mul_right).const_mul _
  have e : (fun x : ℝ => zeroMeanProbe ε t x * cexp (I * (τ : ℂ) * x)) =
      fun x => smallProbe ε t x * cexp (I * (τ : ℂ) * x) -
        ((bumpCosFT (ε * t) / bumpCosFT 0 : ℝ) : ℂ) * (smallProbe ε 0 x * cexp (I * (τ : ℂ) * x)) := by
    funext x; simp only [zeroMeanProbe]; ring
  have h1 : paperFT (smallProbe ε t) τ = ∫ x : ℝ, smallProbe ε t x * cexp (I * (τ : ℂ) * x) := rfl
  have h2 : paperFT (smallProbe ε 0) τ = ∫ x : ℝ, smallProbe ε 0 x * cexp (I * (τ : ℂ) * x) := rfl
  rw [paperFT, e, integral_sub i1 i2, integral_const_mul, ← h1, ← h2,
    paperFT_smallProbe_real hε, paperFT_smallProbe_real hε]
  push_cast; ring_nf

theorem paperFT_zeroMeanProbe_zero {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    paperFT (zeroMeanProbe ε t) 0 = 0 := by
  have := paperFT_zeroMeanProbe_real hε t 0
  simp only [Complex.ofReal_zero] at this
  rw [this, zero_sub, mul_zero, mul_neg, bumpCosFT_neg]
  have h0 := bumpCosFT_zero_pos
  field_simp
  simp

theorem paperFT_zeroMeanProbe_ne_zero {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ≠ 0) :
    paperFT (zeroMeanProbe ε t) t ≠ 0 := by
  rw [paperFT_zeroMeanProbe_real hε, sub_self, mul_zero]
  have h0 := bumpCosFT_zero_pos
  have hlt := abs_bumpCosFT_lt (v := ε * t) (mul_ne_zero hε.ne' ht)
  have hsq : bumpCosFT (ε * t) ^ 2 < bumpCosFT 0 ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ hlt (abs_nonneg _) (by norm_num)
  have : ε * bumpCosFT 0 - bumpCosFT (ε * t) / bumpCosFT 0 * (ε * bumpCosFT (ε * t)) ≠ 0 := by
    have e : ε * bumpCosFT 0 - bumpCosFT (ε * t) / bumpCosFT 0 * (ε * bumpCosFT (ε * t)) =
        ε * (bumpCosFT 0 ^ 2 - bumpCosFT (ε * t) ^ 2) / bumpCosFT 0 := by
      field_simp
    rw [e]
    exact div_ne_zero (mul_ne_zero hε.ne' (by linarith)) h0.ne'
  exact_mod_cast this

/-! ### Rigidity with a half-pole atom -/

/-- **Rigidity for a symbol with an atom at the origin.**  Suppose the atoms of `w` pair with the
tests through a continuous symbol `P` of linear growth plus an atom of mass `m` at `τ = 0`:
`2π ∑_n w(n) n^{-1/2} φ_f(log n) = ∫ |h_f|² P + m |h_f(0)|²`.  If `Λ + w` is Weil-positive, then
`w = 0`.  Concentrated radical tests centred away from the origin force `P ≤ 0`; probes supported
in `[-log 2/4, log 2/4]` force `m ≥ 0`, then (with zero mean) `P ≡ 0`, then `m = 0`; two-point
resonators finish. -/
theorem vonMangoldt_add_eq_zero_of_symbol_atom {w : ℕ → ℝ} {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) {m : ℝ}
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ) + m * ‖paperFT f 0‖ ^ 2)
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  -- the energy identity
  have henergy : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ)) -
        m * ‖paperFT f 0‖ ^ 2 := by
    intro a ha f hf hfs
    rw [integral_weilAtomSymbol_eq_sub hf hfs]
    have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, ((Λ n : ℝ) + w n - Λ n) / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
      Finset.sum_congr rfl fun n _ => by ring_nf
    rw [hsum, hpair a ha f hf hfs]
    have hsub : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ)) =
        (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
          weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) -
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ := by
      rw [← integral_sub
        (integrable_normSq_paperFT_mul_weilAtomSymbol_of hf hfs (fun n => (Λ n : ℝ)))
        (integrable_normSq_paperFT_mul_of_linear hf hfs hPc hPb)]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    rw [hsub]; ring
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
    have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ P τ ∧ m' / 2 ≤ ‖twistLimit 0 τ‖ := by
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
    obtain ⟨a, ha, f, hfd, hfs, hp, hm'', hneg⟩ :=
      vonMangoldt_sub_symbol_atom_violation hPc hPb hη0 hm0 hτ₁ hnear hτ₀ne (abs_nonneg m)
    have := hpos a ha f hfd hfs hp hm''
    rw [henergy a ha f hfd hfs] at this
    have hmm : -m * ‖paperFT f 0‖ ^ 2 ≤ |m| * ‖paperFT f 0‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_abs m) (sq_nonneg _)
    linarith
  -- the probe identity
  have hε : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hprobe : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
      tsupport g ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) →
      (∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * P τ) + m * ‖paperFT g 0‖ ^ 2 = 0 := by
    intro g hg hgs
    have hint0 := hpair (Real.log 2 / 4) (by positivity) g hg hgs
    rw [floor_exp_half_log_two] at hint0
    simp only [Finset.Icc_eq_empty (by norm_num : ¬ (2 ≤ 1)), Finset.sum_empty, mul_zero] at hint0
    exact hint0.symm
  have hnonpos : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
      tsupport g ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) →
      ∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * P τ ≤ 0 := fun g _ _ =>
    integral_nonpos fun τ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hle τ)
  -- step 2a: `m ≥ 0`
  set g₀ := smallProbe (Real.log 2) 0 with hg₀
  have hg₀d := contDiff_smallProbe (Real.log 2) 0
  have hg₀s : tsupport g₀ ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) := tsupport_smallProbe hε 0
  have hg₀0 : 0 < ‖paperFT g₀ 0‖ ^ 2 := by
    have := paperFT_smallProbe_ne_zero hε 0
    push_cast at this
    positivity
  have hm0 : 0 ≤ m := by
    have h1 := hprobe g₀ hg₀d hg₀s
    have h2 := hnonpos g₀ hg₀d hg₀s
    by_contra hneg; push Not at hneg
    have : m * ‖paperFT g₀ 0‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hg₀0
    linarith
  -- step 2b: `P ≡ 0`
  have hzero' : ∀ t : ℝ, t ≠ 0 → P t = 0 := by
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
    set F : ℝ → ℝ := fun τ => ‖paperFT g τ‖ ^ 2 * -P τ with hFdef
    have hFc : Continuous F := hHc.mul hPc.neg
    have hF0 : 0 ≤ F := fun τ => mul_nonneg (sq_nonneg _) (by linarith [hle τ])
    have hFi : Integrable F :=
      (integrable_normSq_paperFT_mul_of_linear hg hgs hPc hPb).neg.congr
        (Eventually.of_forall fun τ => by simp only [Pi.neg_apply, hFdef]; ring)
    have hFint : ∫ τ, F τ = 0 := by
      have e : F = fun τ : ℝ => -(‖paperFT g τ‖ ^ 2 * P τ) := by
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
  have hPzero : P = fun _ => 0 :=
    hPc.ext_on (dense_compl_singleton (0 : ℝ)) continuous_const fun t ht => hzero' t ht
  -- step 2c: `m = 0`
  have hmzero : m = 0 := by
    have h1 := hprobe g₀ hg₀d hg₀s
    rw [hPzero] at h1
    simp only [mul_zero, integral_zero, zero_add] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hg₀0.ne'
  -- step 3: the symbol vanishes; apply the continuous-symbol rigidity
  refine vonMangoldt_add_eq_zero_of_symbol (P := fun _ => 0) continuous_const (Mp := 0)
    (fun τ => by simp) (fun a ha f hf hfs => ?_) hpos hn₀
  rw [hpair a ha f hf hfs, hPzero, hmzero]
  simp

/-! ### The Abel symbol under a summable partial-sum weight -/

/-- The weight `|B(n)|/(n √n)` of the partial sums `B(n) = ∑_{2 ≤ k ≤ n} b(k)`. -/
def partialSumWeight (b : ℕ → ℝ) (n : ℕ) : ℝ := |partialFrom2 b n| / ((n : ℝ) * Real.sqrt n)

theorem partialSumWeight_nonneg (b : ℕ → ℝ) (n : ℕ) : 0 ≤ partialSumWeight b n := by
  unfold partialSumWeight; positivity

theorem abs_partialFrom2_mul_kernel_le_weight (b : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    |partialFrom2 b n * halfPowerAbelKernel τ n| ≤ (|τ| + 1 / 2) * partialSumWeight b n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [partialFrom2_zero, partialSumWeight]
  · rw [abs_mul]
    have h := abs_halfPowerAbelKernel_le τ hn
    calc |partialFrom2 b n| * |halfPowerAbelKernel τ n|
        ≤ |partialFrom2 b n| * ((|τ| + 1 / 2) / ((n : ℝ) * Real.sqrt n)) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = (|τ| + 1 / 2) * partialSumWeight b n := by unfold partialSumWeight; ring

theorem summable_osc_of_weight {b : ℕ → ℝ} (hs : Summable (partialSumWeight b)) (τ : ℝ) :
    Summable fun n => partialFrom2 b n * halfPowerAbelKernel τ n :=
  Summable.of_norm_bounded (hs.mul_left (|τ| + 1 / 2))
    fun n => by rw [Real.norm_eq_abs]; exact abs_partialFrom2_mul_kernel_le_weight b τ n

theorem abs_oscSymbol_le_of_weight {b : ℕ → ℝ} (hs : Summable (partialSumWeight b)) (τ : ℝ) :
    |oscSymbol b τ| ≤ 2 * (∑' n : ℕ, partialSumWeight b n) * (1 + |τ|) := by
  set Z := ∑' n : ℕ, partialSumWeight b n with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => partialSumWeight_nonneg b n
  have hso := summable_osc_of_weight hs τ
  have h1 : |∑' n : ℕ, partialFrom2 b n * halfPowerAbelKernel τ n| ≤
      ∑' n : ℕ, |partialFrom2 b n * halfPowerAbelKernel τ n| := by
    have := norm_tsum_le_tsum_norm hso.norm
    simp only [Real.norm_eq_abs] at this
    exact this
  have h2 : ∑' n : ℕ, |partialFrom2 b n * halfPowerAbelKernel τ n| ≤
      ∑' n : ℕ, (|τ| + 1 / 2) * partialSumWeight b n :=
    Summable.tsum_le_tsum (fun n => abs_partialFrom2_mul_kernel_le_weight b τ n) hso.abs
      (hs.mul_left _)
  rw [tsum_mul_left, ← hZ] at h2
  have h3 : (|τ| + 1 / 2) * Z ≤ Z * (1 + |τ|) := by nlinarith [abs_nonneg τ]
  unfold oscSymbol
  rw [abs_mul, abs_two]
  have h4 := h1.trans (h2.trans h3)
  linarith

theorem continuous_oscSymbol_of_weight {b : ℕ → ℝ} (hs : Summable (partialSumWeight b)) :
    Continuous (oscSymbol b) := by
  rw [continuous_iff_continuousAt]
  intro τ₁
  have hOn : ContinuousOn (fun τ => ∑' n : ℕ, partialFrom2 b n * halfPowerAbelKernel τ n)
      (Ioo (τ₁ - 1) (τ₁ + 1)) := by
    refine continuousOn_tsum
      (f := fun (n : ℕ) (τ : ℝ) => partialFrom2 b n * halfPowerAbelKernel τ n)
      (u := fun n : ℕ => (|τ₁| + 1 + 1 / 2) * partialSumWeight b n)
      (fun n => (continuous_const.mul (continuous_halfPowerAbelKernel n)).continuousOn)
      (hs.mul_left _) fun n τ hτ => ?_
    rw [Real.norm_eq_abs]
    refine (abs_partialFrom2_mul_kernel_le_weight b τ n).trans ?_
    have hτ : |τ| ≤ |τ₁| + 1 := by
      have := abs_sub_abs_le_abs_sub τ τ₁
      have : |τ - τ₁| < 1 := abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      linarith
    exact mul_le_mul_of_nonneg_right (by linarith) (partialSumWeight_nonneg b n)
  have hAt := hOn.continuousAt (Ioo_mem_nhds (show τ₁ - 1 < τ₁ by linarith)
    (show τ₁ < τ₁ + 1 by linarith))
  exact (continuousAt_const.mul hAt)

theorem integral_normSq_mul_oscSymbol_of_weight {b : ℕ → ℝ} (hs : Summable (partialSumWeight b))
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * oscSymbol b τ =
      2 * π * ∑' n : ℕ, partialFrom2 b n * (halfPowerAbelWeight f n - halfPowerAbelWeight f (n + 1)) := by
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
    refine (hF.mul_const (|partialFrom2 b n| * 2)).mono'
      (hHc.mul (continuous_const.mul (continuous_halfPowerAbelKernel n))).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (abs_halfPowerAbelKernel_le_two τ n) (abs_nonneg _)) (sq_nonneg _)
  have hnorm : Summable fun n : ℕ => ∫ τ : ℝ,
      ‖‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (hs.mul_right (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2)))
    calc ∫ τ : ℝ, ‖‖paperFT f τ‖ ^ 2 * (partialFrom2 b n * halfPowerAbelKernel τ n)‖
        ≤ ∫ τ : ℝ, partialSumWeight b n * (‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2)) :=
          integral_mono (hterm n).norm (hlin.const_mul _) fun τ => by
            rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
            have := abs_partialFrom2_mul_kernel_le_weight b τ n
            have h0 : 0 ≤ ‖paperFT f τ‖ ^ 2 := sq_nonneg _
            calc ‖paperFT f τ‖ ^ 2 * |partialFrom2 b n * halfPowerAbelKernel τ n|
                ≤ ‖paperFT f τ‖ ^ 2 * ((|τ| + 1 / 2) * partialSumWeight b n) :=
                  mul_le_mul_of_nonneg_left this h0
              _ = partialSumWeight b n * (‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2)) := by ring
      _ = partialSumWeight b n * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (|τ| + 1 / 2) :=
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

/-- **Pairing of a perturbation with summable partial-sum weight.**  If
`∑ |B(n)|/(n √n) < ∞`, the atoms of `b` pair with every test through the Abel symbol. -/
theorem pairing_eq_integral_oscSymbol {b : ℕ → ℝ} (hs : Summable (partialSumWeight b))
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, b n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * oscSymbol b τ := by
  rw [integral_normSq_mul_oscSymbol_of_weight hs hf hfs,
    tsum_partialFrom2_mul_sub (N := ⌊Real.exp (2 * a)⌋₊) fun m hm => ?_]
  · congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold halfPowerAbelWeight weilTestEvenPart; ring
  · unfold halfPowerAbelWeight
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hexp : Real.exp (2 * a) < m := (Nat.floor_lt (Real.exp_pos _).le).mp hm
    have hlog : 2 * a < Real.log m := by
      rw [← Real.log_exp (2 * a)]; exact Real.log_lt_log (Real.exp_pos _) hexp
    rw [weilTestEvenPart_eq_zero hf hfs (by rw [abs_of_nonneg (Real.log_nonneg hm1)]; exact hlog),
      zero_div]

/-! ### The half-pole weights `√n − √(n−1)` -/

/-- The weight `β(n) = √n − √(n−1)`, whose partial sums are `√n − 1`. -/
def sqrtStep (n : ℕ) : ℝ := Real.sqrt n - Real.sqrt ((n : ℝ) - 1)

/-- The normalized half-pole weight `c_n = β(n)/√n`. -/
def halfPoleCoeff (n : ℕ) : ℝ := sqrtStep n / Real.sqrt n

/-- The half-pole kernel `K_n(τ) = c_n cos(τ log n) − ½ ∫_{log(n−1)}^{log n} cos(τu) du`. -/
def halfPoleKernel (τ : ℝ) (n : ℕ) : ℝ :=
  halfPoleCoeff n * Real.cos (τ * Real.log n) -
    (∫ u in Real.log ((n : ℝ) - 1)..Real.log n, Real.cos (τ * u)) / 2

theorem hasDerivAt_exp_half_sub (b u : ℝ) :
    HasDerivAt (fun u => Real.exp ((u - b) / 2)) (Real.exp ((u - b) / 2) / 2) u := by
  have := ((hasDerivAt_id u).sub_const b).div_const 2 |>.exp
  convert this using 1
  · funext x; simp
  · simp; ring

/-- `c_n = ∫_{log(n−1)}^{log n} ½ e^{(u − log n)/2} du`. -/
theorem halfPoleCoeff_eq_integral {n : ℕ} (hn : 2 ≤ n) :
    halfPoleCoeff n = ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, Real.exp ((u - Real.log n) / 2) / 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_exp_half_sub _ u)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_self, zero_div, Real.exp_zero]
  have hsq : ∀ x : ℝ, 0 < x → Real.exp (Real.log x / 2) = Real.sqrt x := by
    intro x hx
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]; congr 1; ring
  have e : (Real.log ((n : ℝ) - 1) - Real.log n) / 2 =
      Real.log ((n : ℝ) - 1) / 2 - Real.log n / 2 := by ring
  rw [e, Real.exp_sub, hsq _ (by linarith), hsq _ hn0]
  unfold halfPoleCoeff sqrtStep
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  field_simp

theorem log_sub_log_pred_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log n - Real.log ((n : ℝ) - 1) ≤ 1 / ((n : ℝ) - 1) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [← Real.log_div (by positivity) (by linarith)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / ((n : ℝ) - 1) by positivity)
  have e : (n : ℝ) / ((n : ℝ) - 1) - 1 = 1 / ((n : ℝ) - 1) := by field_simp; ring
  linarith

theorem log_pred_le_log {n : ℕ} (hn : 2 ≤ n) : Real.log ((n : ℝ) - 1) ≤ Real.log n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact Real.log_le_log (by linarith) (by linarith)

/-- `|K_n(τ)| ≤ (1 + |τ|)/(n − 1)²`. -/
theorem abs_halfPoleKernel_le (τ : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    |halfPoleKernel τ n| ≤ (1 + |τ|) / ((n : ℝ) - 1) ^ 2 := by
  set a := Real.log ((n : ℝ) - 1) with ha
  set b := Real.log (n : ℝ) with hb
  have hab : a ≤ b := log_pred_le_log hn
  have hba : b - a ≤ 1 / ((n : ℝ) - 1) := log_sub_log_pred_le hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hi1 : IntervalIntegrable (fun u => Real.exp ((u - b) / 2) / 2 * Real.cos (τ * b))
      volume a b := by apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun u => Real.cos (τ * u) / 2) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hK : halfPoleKernel τ n = ∫ u in a..b,
      (Real.exp ((u - b) / 2) / 2 * Real.cos (τ * b) - Real.cos (τ * u) / 2) := by
    unfold halfPoleKernel
    rw [halfPoleCoeff_eq_integral hn, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      intervalIntegral.integral_div]
  rw [hK]
  have hbound : ∀ u ∈ Set.uIoc a b,
      ‖Real.exp ((u - b) / 2) / 2 * Real.cos (τ * b) - Real.cos (τ * u) / 2‖ ≤
        (1 + |τ|) * (b - a) := by
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    obtain ⟨hu1, hu2⟩ := hu
    rw [Real.norm_eq_abs]
    have e1 : Real.exp ((u - b) / 2) / 2 * Real.cos (τ * b) - Real.cos (τ * u) / 2 =
        ((Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b) + (Real.cos (τ * b) - Real.cos (τ * u))) / 2 := by
      ring
    rw [e1, abs_div, abs_two]
    have h1 : |Real.exp ((u - b) / 2) - 1| ≤ (b - u) / 2 := by
      have hle : Real.exp ((u - b) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have := Real.add_one_le_exp ((u - b) / 2)
      rw [abs_of_nonpos (by linarith)]; linarith
    have h2 : |Real.cos (τ * b) - Real.cos (τ * u)| ≤ |τ| * (b - u) := by
      have := Real.abs_cos_sub_cos_le (τ * b) (τ * u)
      rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ b - u)] at this
      exact this
    have h3 : |(Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b)| ≤ (b - u) / 2 := by
      rw [abs_mul]
      exact (mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _) (by linarith)).trans
        (by linarith)
    have h4 := abs_add_le ((Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b))
      (Real.cos (τ * b) - Real.cos (τ * u))
    have hbu : b - u ≤ b - a := by linarith
    have : (b - u) / 2 + |τ| * (b - u) ≤ 2 * ((1 + |τ|) * (b - a)) := by
      nlinarith [abs_nonneg τ]
    linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a)] at hnorm
  calc |∫ u in a..b, (Real.exp ((u - b) / 2) / 2 * Real.cos (τ * b) - Real.cos (τ * u) / 2)|
      ≤ (1 + |τ|) * (b - a) * (b - a) := hnorm
    _ ≤ (1 + |τ|) * (1 / ((n : ℝ) - 1)) * (1 / ((n : ℝ) - 1)) := by
        have h0 : 0 ≤ b - a := by linarith
        have h1 : 0 ≤ 1 + |τ| := by positivity
        gcongr
    _ = (1 + |τ|) / ((n : ℝ) - 1) ^ 2 := by field_simp

/-- The comparison weight `1/(n − 1)²` for `n ≥ 2`. -/
def halfPoleWeight (n : ℕ) : ℝ := if 2 ≤ n then 1 / ((n : ℝ) - 1) ^ 2 else 0

theorem halfPoleWeight_nonneg (n : ℕ) : 0 ≤ halfPoleWeight n := by
  unfold halfPoleWeight; split_ifs <;> positivity

theorem summable_halfPoleWeight : Summable halfPoleWeight := by
  have h := (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le halfPoleWeight_nonneg (fun n => ?_) h
  unfold halfPoleWeight
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hh : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
    have hpos : 0 < (n : ℝ) / 2 := by linarith
    calc 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / ((n : ℝ) / 2) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hh 2)
      _ = 4 * (1 / (n : ℝ) ^ 2) := by field_simp; ring
  · positivity

/-- The `n`-th term of the half-pole symbol (zero for `n < 2`). -/
def halfPoleTerm (τ : ℝ) (n : ℕ) : ℝ := if 2 ≤ n then halfPoleKernel τ n else 0

theorem abs_halfPoleTerm_le (τ : ℝ) (n : ℕ) :
    |halfPoleTerm τ n| ≤ (1 + |τ|) * halfPoleWeight n := by
  unfold halfPoleTerm halfPoleWeight
  split_ifs with hn
  · rw [mul_one_div]; exact abs_halfPoleKernel_le τ hn
  · simp

theorem continuous_halfPoleKernel (n : ℕ) : Continuous fun τ => halfPoleKernel τ n := by
  unfold halfPoleKernel
  have h : Continuous fun τ : ℝ => ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, Real.cos (τ * u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun τ u : ℝ => Real.cos (τ * u)) (by fun_prop) _ _
  exact (continuous_const.mul (by fun_prop)).sub (h.div_const 2)

theorem continuous_halfPoleTerm (n : ℕ) : Continuous fun τ => halfPoleTerm τ n := by
  unfold halfPoleTerm
  split_ifs
  · exact continuous_halfPoleKernel n
  · exact continuous_const

/-- The half-pole symbol `P_β(τ) = 2 ∑_{n ≥ 2} K_n(τ)`. -/
def halfPoleSymbol (τ : ℝ) : ℝ := 2 * ∑' n : ℕ, halfPoleTerm τ n

theorem summable_halfPoleTerm (τ : ℝ) : Summable fun n => halfPoleTerm τ n :=
  Summable.of_norm_bounded (summable_halfPoleWeight.mul_left (1 + |τ|))
    fun n => by rw [Real.norm_eq_abs]; exact abs_halfPoleTerm_le τ n

theorem abs_halfPoleSymbol_le (τ : ℝ) :
    |halfPoleSymbol τ| ≤ 2 * (∑' n : ℕ, halfPoleWeight n) * (1 + |τ|) := by
  have hs := summable_halfPoleTerm τ
  have h1 : |∑' n : ℕ, halfPoleTerm τ n| ≤ ∑' n : ℕ, |halfPoleTerm τ n| := by
    have := norm_tsum_le_tsum_norm hs.norm
    simp only [Real.norm_eq_abs] at this
    exact this
  have h2 : ∑' n : ℕ, |halfPoleTerm τ n| ≤ ∑' n : ℕ, (1 + |τ|) * halfPoleWeight n :=
    Summable.tsum_le_tsum (fun n => abs_halfPoleTerm_le τ n) hs.abs
      (summable_halfPoleWeight.mul_left _)
  rw [tsum_mul_left] at h2
  unfold halfPoleSymbol
  rw [abs_mul, abs_two]
  have := h1.trans h2
  have e : (2 * ∑' n : ℕ, halfPoleWeight n) * (1 + |τ|) =
      2 * ((1 + |τ|) * ∑' n : ℕ, halfPoleWeight n) := by ring
  rw [e]
  linarith

theorem continuous_halfPoleSymbol : Continuous halfPoleSymbol := by
  rw [continuous_iff_continuousAt]
  intro τ₁
  have hOn : ContinuousOn (fun τ => ∑' n : ℕ, halfPoleTerm τ n) (Ioo (τ₁ - 1) (τ₁ + 1)) := by
    refine continuousOn_tsum (f := fun (n : ℕ) (τ : ℝ) => halfPoleTerm τ n)
      (u := fun n : ℕ => (1 + (|τ₁| + 1)) * halfPoleWeight n)
      (fun n => (continuous_halfPoleTerm n).continuousOn)
      (summable_halfPoleWeight.mul_left _) fun n τ hτ => ?_
    rw [Real.norm_eq_abs]
    refine (abs_halfPoleTerm_le τ n).trans ?_
    have hτ : |τ| ≤ |τ₁| + 1 := by
      have := abs_sub_abs_le_abs_sub τ τ₁
      have : |τ - τ₁| < 1 := abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      linarith
    exact mul_le_mul_of_nonneg_right (by linarith) (halfPoleWeight_nonneg n)
  have hAt := hOn.continuousAt (Ioo_mem_nhds (show τ₁ - 1 < τ₁ by linarith)
    (show τ₁ < τ₁ + 1 by linarith))
  exact continuousAt_const.mul hAt

/-! ### The pairing of the half-pole weights -/

theorem integral_normSq_mul_halfPoleKernel {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {n : ℕ} (hn : 2 ≤ n) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPoleKernel τ n =
      π * (halfPoleCoeff n * weilTestEvenPart f (Real.log n) -
        (∫ u in Real.log ((n : ℝ) - 1)..Real.log n, weilTestEvenPart f u) / 2) := by
  set A := Real.log ((n : ℝ) - 1) with hA
  set B := Real.log (n : ℝ) with hB
  have hAB : A ≤ B := log_pred_le_log hn
  have hF := integrable_normSq_paperFT hf hfs
  obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hf hfs
  have hHc : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hf.continuous.integrable_of_hasCompactSupport
      hfc)).norm.pow 2
  have hIc : Continuous fun τ : ℝ => ∫ u in A..B, Real.cos (τ * u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun τ u : ℝ => Real.cos (τ * u)) (by fun_prop) _ _
  have hIb : ∀ τ : ℝ, |∫ u in A..B, Real.cos (τ * u)| ≤ B - A := by
    intro τ
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := A) (b := B) (C := 1)
      (f := fun u => Real.cos (τ * u)) fun u _ => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ B - A), one_mul] at this
    exact this
  have hI : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.cos (τ * u) := by
    refine (hF.mul_const (B - A)).mono' (hHc.mul hIc).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hIb τ) (sq_nonneg _)
  have hC := integrable_normSq_paperFT_mul_cos hf hfs B
  -- Fubini on `ℝ × (A, B]`
  have hswap : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.cos (τ * u) =
      ∫ u in A..B, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * u) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc A B)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
    have hprod : Integrable (Function.uncurry fun (τ u : ℝ) => ‖paperFT f τ‖ ^ 2 * Real.cos (τ * u))
        (volume.prod (volume.restrict (Ioc A B))) := by
      refine (hF.mul_prod (integrable_const (1 : ℝ))).mono'
        ((hHc.comp continuous_fst).mul (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      show ‖‖paperFT f p.1‖ ^ 2 * Real.cos (p.1 * p.2)‖ ≤ ‖paperFT f p.1‖ ^ 2 * 1
      rw [mul_one, norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
      exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)
    have e1 : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.cos (τ * u)) =
        fun τ : ℝ => ∫ u in Ioc A B, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * u) := by
      funext τ
      rw [intervalIntegral.integral_of_le hAB, ← integral_const_mul]
    rw [e1, integral_integral_swap hprod, intervalIntegral.integral_of_le hAB]
  have hinner : ∀ u : ℝ, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * u) =
      π * weilTestEvenPart f u := fun u => by
    rw [integral_normSq_paperFT_mul_cos_eq hf hfs u]; rfl
  have e2 : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * halfPoleKernel τ n) = fun τ : ℝ =>
      halfPoleCoeff n * (‖paperFT f τ‖ ^ 2 * Real.cos (τ * B)) -
        (‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.cos (τ * u)) / 2 := by
    funext τ; unfold halfPoleKernel; ring
  rw [e2, integral_sub (hC.const_mul _) (hI.div_const 2), integral_const_mul, integral_div, hswap,
    hinner B]
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The interval integrals over `[log(n−1), log n]` telescope to `∫_0^{log M}`. -/
theorem sum_integral_log_steps {φ : ℝ → ℝ} (hφ : Continuous φ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, φ u =
      ∫ u in (0 : ℝ)..Real.log M, φ u := by
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.lt_or_ge M 1 with hM1 | hM1
    · have : M = 0 := by omega
      subst this
      simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih hM1]
      have e : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
      rw [e, intervalIntegral.integral_add_adjacent_intervals (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)]

/-- `∫_0^L φ_f = |ĥ_f(0)|²` for `L > 2a`. -/
theorem integral_weilTestEvenPart_eq {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {L : ℝ} (hL : 2 * a < L) :
    ∫ u in (0 : ℝ)..L, weilTestEvenPart f u = ‖paperFT f 0‖ ^ 2 := by
  obtain ⟨hfc, hkd, hks, hki, -⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f with hk
  have hkc : Continuous k := hkd.continuous
  have hL0 : 0 < L := by linarith
  have hzero : ∀ x : ℝ, 2 * a < |x| → k x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hks hmem
      have : |x| ≤ 2 * a := abs_le.mpr ⟨this.1, this.2⟩
      linarith
  have hre : ∫ u in (0 : ℝ)..L, weilTestEvenPart f u =
      (∫ u in (0 : ℝ)..L, (k u + k (-u))).re := by
    unfold weilTestEvenPart
    rw [← hk]
    have hii : IntervalIntegrable (fun u => k u + k (-u)) volume 0 L :=
      (hkc.add (hkc.comp continuous_neg)).intervalIntegrable 0 L
    have := Complex.reCLM.intervalIntegral_comp_comm hii
    simp only [Complex.reCLM_apply] at this
    exact this
  have hi1 : IntervalIntegrable k volume 0 L := hkc.intervalIntegrable 0 L
  have hi2 : IntervalIntegrable (fun u => k (-u)) volume 0 L :=
    (hkc.comp continuous_neg).intervalIntegrable 0 L
  rw [hre, intervalIntegral.integral_add hi1 hi2]
  have hneg : ∫ u in (0 : ℝ)..L, k (-u) = ∫ u in (-L)..0, k u := by
    rw [intervalIntegral.integral_comp_neg (fun u => k u), neg_zero]
  rw [hneg, add_comm, intervalIntegral.integral_add_adjacent_intervals
    (hkc.intervalIntegrable _ _) (hkc.intervalIntegrable _ _)]
  have hfull : ∫ u in (-L)..L, k u = ∫ u, k u := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hzero x ?_
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hft : ∫ u, k u = paperFT k 0 := by
    unfold paperFT; simp
  rw [hfull, hft]
  have := paperFT_weilTest_self_ofReal hf.continuous hfc 0
  push_cast at this
  rw [← hk] at this
  rw [this]
  norm_cast

/-- **The pairing of the half-pole weights.**  With `β(n) = √n − √(n−1)` (partial sums `√n − 1`),
`2π ∑_n β(n) n^{-1/2} φ_f(log n) = π |ĥ_f(0)|² + ∫ |ĥ_f|² P_β`: an atom at the origin (the pole of
`ζ(2s)` at `s = 1/2`) plus the continuous half-pole symbol. -/
theorem pairing_sqrtStep {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, sqrtStep n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      π * ‖paperFT f 0‖ ^ 2 + ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ := by
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  set M := N + 1 with hM
  set φ := weilTestEvenPart f with hφ
  have hφc : Continuous φ := (contDiff_weilTestEvenPart hf hfs).continuous
  have hφ0 : ∀ u : ℝ, 2 * a < |u| → φ u = 0 := fun u hu => weilTestEvenPart_eq_zero hf hfs hu
  have hN1 : 1 ≤ N := by
    rw [hN]; apply Nat.le_floor; push_cast
    exact Real.one_le_exp (by linarith)
  have hlogM : 2 * a < Real.log M := by
    have h1 : Real.exp (2 * a) < (M : ℝ) := by
      rw [hM]; push_cast; exact Nat.lt_floor_add_one _
    rw [← Real.log_exp (2 * a)]
    exact Real.log_lt_log (Real.exp_pos _) h1
  have hlogpos : ∀ n : ℕ, M ≤ n → 2 * a < |Real.log n| := by
    intro n hn
    have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
    have hM1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have := Real.log_le_log (by linarith) hMn
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    linarith
  -- (i) extend the sum to `M`
  have hi : ∑ n ∈ Finset.Icc 2 N, sqrtStep n / Real.sqrt n *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 M, halfPoleCoeff n * φ (Real.log n) := by
    rw [hM, Finset.sum_Icc_succ_top (by omega), hφ0 _ (hlogpos _ le_rfl), mul_zero, add_zero]
    rfl
  -- (ii) the kernel identity for each atom
  have hii : ∀ n ∈ Finset.Icc 2 M, halfPoleCoeff n * φ (Real.log n) =
      (1 / π) * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPoleKernel τ n) +
        (∫ u in Real.log ((n : ℝ) - 1)..Real.log n, φ u) / 2 := by
    intro n hn
    rw [integral_normSq_mul_halfPoleKernel hf hfs (Finset.mem_Icc.mp hn).1]
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hi, Finset.sum_congr rfl hii, Finset.sum_add_distrib, ← Finset.sum_div,
    sum_integral_log_steps hφc M (by omega), integral_weilTestEvenPart_eq ha hf hfs hlogM,
    ← Finset.mul_sum]
  -- (iii) the symbol side
  have hHc : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 := by
    obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hf hfs
    exact (continuous_paperFT_real_of_integrable (hf.continuous.integrable_of_hasCompactSupport
      hfc)).norm.pow 2
  have hlin := integrable_normSq_paperFT_mul_of_linear hf hfs (P := fun τ => 1 + |τ|)
    (by fun_prop) (Mp := 1) fun τ => by rw [abs_of_nonneg (by positivity)]; linarith
  have hterm : ∀ n : ℕ, Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * halfPoleTerm τ n := fun n =>
    integrable_normSq_paperFT_mul_of_linear hf hfs (continuous_halfPoleTerm n)
      (Mp := halfPoleWeight n) fun τ => by
        have := abs_halfPoleTerm_le τ n; linarith [halfPoleWeight_nonneg n]
  have hnorm : Summable fun n : ℕ => ∫ τ : ℝ, ‖‖paperFT f τ‖ ^ 2 * halfPoleTerm τ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (summable_halfPoleWeight.mul_right
        (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (1 + |τ|)))
    calc ∫ τ : ℝ, ‖‖paperFT f τ‖ ^ 2 * halfPoleTerm τ n‖
        ≤ ∫ τ : ℝ, halfPoleWeight n * (‖paperFT f τ‖ ^ 2 * (1 + |τ|)) :=
          integral_mono (hterm n).norm (hlin.const_mul _) fun τ => by
            rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
            have := abs_halfPoleTerm_le τ n
            calc ‖paperFT f τ‖ ^ 2 * |halfPoleTerm τ n|
                ≤ ‖paperFT f τ‖ ^ 2 * ((1 + |τ|) * halfPoleWeight n) :=
                  mul_le_mul_of_nonneg_left this (sq_nonneg _)
              _ = halfPoleWeight n * (‖paperFT f τ‖ ^ 2 * (1 + |τ|)) := by ring
      _ = halfPoleWeight n * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (1 + |τ|) := integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hterm hnorm
  have hsym : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ =
      2 * ∑ n ∈ Finset.Icc 2 M, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPoleKernel τ n := by
    have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ) =
        fun τ : ℝ => 2 * ∑' n : ℕ, ‖paperFT f τ‖ ^ 2 * halfPoleTerm τ n := by
      funext τ; unfold halfPoleSymbol; rw [tsum_mul_left]; ring
    rw [e, integral_const_mul, ← hswap]
    congr 1
    rw [tsum_eq_sum (s := Finset.Icc 2 M) fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have h2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      unfold halfPoleTerm; simp only [if_pos h2]
    · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with hn | hn
      · have h2 : ¬ 2 ≤ n := by omega
        unfold halfPoleTerm; simp only [if_neg h2, mul_zero, integral_zero]
      · have h2 : 2 ≤ n := by omega
        unfold halfPoleTerm
        simp only [if_pos h2]
        rw [integral_normSq_mul_halfPoleKernel hf hfs h2]
        have hzero : ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, φ u = 0 := by
          have hM' : M ≤ n - 1 := by omega
          have hlog : 2 * a < Real.log ((n : ℝ) - 1) := by
            have := hlogpos (n - 1) hM'
            have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega)]; push_cast; ring
            rw [hcast] at this
            have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
              have : (M : ℝ) ≤ (n : ℝ) - 1 := by rw [← hcast]; exact_mod_cast hM'
              have hM1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
              linarith
            rwa [abs_of_nonneg (Real.log_nonneg h1)] at this
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
          · simp
          · rw [Set.uIcc_of_le (log_pred_le_log (by omega))] at hu
            exact hφ0 u (by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.1])
        have hz2 : weilTestEvenPart f (Real.log n) = 0 := hφ0 _ (hlogpos n (by omega))
        rw [hzero, hz2]
        simp
  rw [hsym]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### Rigidity across the `√n` barrier -/

/-- **Rigidity across the `√n` barrier.**  Let the partial sums of a perturbation `w` be
`κ(√n − 1)` plus a remainder `E(n)` with `∑ |E(n)|/(n √n) < ∞` (`κ` arbitrary).  If `Λ + w` is
Weil-positive, then `w = 0`.  The main term `κ(√n − 1)` pairs with the tests through an atom
`πκ|ĥ(0)|²` at the origin (the pole of `ζ(2s)` at `s = 1/2`) plus a continuous symbol; the
remainder through its Abel symbol. -/
theorem vonMangoldt_add_halfPole_eq_zero {w : ℕ → ℝ} {κ : ℝ}
    (hE : Summable (partialSumWeight fun n => w n - κ * sqrtStep n))
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  set e : ℕ → ℝ := fun n => w n - κ * sqrtStep n with he
  set Zβ := ∑' n : ℕ, halfPoleWeight n with hZβ
  set Ze := ∑' n : ℕ, partialSumWeight e n with hZe
  have hZβ0 : 0 ≤ Zβ := tsum_nonneg halfPoleWeight_nonneg
  have hZe0 : 0 ≤ Ze := tsum_nonneg (partialSumWeight_nonneg e)
  refine vonMangoldt_add_eq_zero_of_symbol_atom (w := w)
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

/-! ### Squares cannot be added to the prime weights -/

/-- The indicator of the perfect squares. -/
def perfectSquareWeight (n : ℕ) : ℝ := if Nat.sqrt n ^ 2 = n then 1 else 0

theorem sqrt_succ_step (n : ℕ) :
    Nat.sqrt (n + 1) = Nat.sqrt n + (if Nat.sqrt (n + 1) ^ 2 = n + 1 then 1 else 0) := by
  have h1 := Nat.sqrt_le' n
  have h2 := Nat.lt_succ_sqrt' n
  have h3 := Nat.sqrt_le' (n + 1)
  have h4 := Nat.lt_succ_sqrt' (n + 1)
  have hmono : Nat.sqrt n ≤ Nat.sqrt (n + 1) := Nat.sqrt_le_sqrt (by omega)
  have hup : Nat.sqrt (n + 1) ≤ Nat.sqrt n + 1 := Nat.sqrt_succ_le_succ_sqrt n
  split_ifs with h
  · -- `n + 1` is a square: its root exceeds `√n`
    rcases Nat.eq_or_lt_of_le hmono with heq | hlt
    · exfalso
      rw [← heq] at h
      omega
    · omega
  · rcases Nat.eq_or_lt_of_le hup with heq | hlt
    · exfalso
      apply h
      rw [heq] at h3 ⊢
      simp only [Nat.succ_eq_add_one] at h2
      nlinarith
    · omega

theorem partialFrom2_perfectSquareWeight {n : ℕ} (hn : 1 ≤ n) :
    partialFrom2 perfectSquareWeight n = (Nat.sqrt n : ℝ) - 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : n = 0 := by omega
      subst this
      simp [partialFrom2, Nat.sqrt]
    · unfold partialFrom2 at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ih h1]
      unfold perfectSquareWeight
      have hs := sqrt_succ_step n
      split_ifs with h
      · rw [hs, if_pos h]; push_cast; ring
      · rw [hs, if_neg h]; push_cast; ring

theorem partialFrom2_sqrtStep {n : ℕ} (hn : 1 ≤ n) :
    partialFrom2 sqrtStep n = Real.sqrt n - 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : n = 0 := by omega
      subst this
      simp [partialFrom2]
    · unfold partialFrom2 at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ih h1]
      unfold sqrtStep
      push_cast
      ring_nf

theorem partialFrom2_sub_mul (w v : ℕ → ℝ) (κ : ℝ) (n : ℕ) :
    partialFrom2 (fun k => w k - κ * v k) n = partialFrom2 w n - κ * partialFrom2 v n := by
  unfold partialFrom2
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Squares cannot be added.**  The weights `Λ(n) + c·1_{n = m²}`, whose perturbation has partial
sums `c(⌊√n⌋ − 1)`, exactly at the `√n` barrier, are Weil-positive only for `c = 0`. -/
theorem vonMangoldt_add_squares_weilPositive_eq_zero {c : ℝ}
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + c * perfectSquareWeight n) ⌊Real.exp (2 * a)⌋₊
          (τ / (2 * π))) : c = 0 := by
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
  have h := vonMangoldt_add_halfPole_eq_zero (w := fun n => c * perfectSquareWeight n) (κ := c) hE hpos
    (n₀ := 4) (by norm_num)
  have hsq : perfectSquareWeight 4 = 1 := by
    unfold perfectSquareWeight
    have : Nat.sqrt 4 = 2 := by
      have h := Nat.sqrt_eq' 2
      rwa [show (2 : ℕ) ^ 2 = 4 by norm_num] at h
    rw [if_pos (by rw [this]; norm_num)]
  rw [hsq, mul_one] at h
  exact h

end RHTower
