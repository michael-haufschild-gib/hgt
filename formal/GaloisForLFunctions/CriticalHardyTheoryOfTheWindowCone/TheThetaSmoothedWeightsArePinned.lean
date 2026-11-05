import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheTwistedArcFamilyIsNearNull
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure
import GaloisForLFunctions.RHTower.WeilFullConePolarizedRepresentation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity

/-!
# The theta-smoothed weights are pinned doubly exponentially

On a positive form a near-null vector annihilates everything, up to Cauchy–Schwarz. The truncated Riemann kernel
`Φ_L = F₀ χ_L` is near-null for every point of the window cone, and its transform vanishes at the zeros up to the
tail, so the same polarization also holds for `Λ` without any sign. Subtracting, for every `λ ∈ 𝒜(c)` and every
test `Y` of fixed support (`exists_abs_atomPairing_crossCorr_le`):

  `|Σ_n (λ(n) − Λ(n)) n^{−1/2} ((Φ_L ⋆ Y)(log n) + (Φ_L ⋆ Y)(−log n))| ≤ C_Y exp(½(3c − (π/16) e^{2(c−2)}))`,

where `L = c − 1/12`. As `Y` shrinks to a point `x` the reading is the theta transform of the deviation,
`Σ_n (λ(n) − Λ(n)) n^{−1/2} (Φ(x − log n) + Φ(x + log n))`.

This is effective uniqueness in smoothed form: unconditional, with an explicit rate, uniform over the cone. It is
not a reading of one atom: the theta kernel mixes them, and extracting one atom is a deconvolution with kernel
transform `Ξ`, which is the content of the single-atom question.

**The tools.** `coneForm_add_smul` is the exact quadratic expansion of Weil's form in a test,
`sq_polar_coneForm_le` the Cauchy–Schwarz inequality on a window, and `norm_W_le_of_zero_bounds` the mixed bound on
the zero side.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23

local notation "𝔽" => xiShiftedGammaTest

/-! ### The quadratic expansion -/

/-- Weil's real form of the weights `lam` on a test. -/
def coneForm (lam : ℕ → ℝ) (f : ℝ → ℂ) : ℝ := (weilFullFunctional lam (EF.weilTest f f)).re

/-- The polarization of the form. -/
def polarForm (lam : ℕ → ℝ) (f g : ℝ → ℂ) : ℝ :=
  coneForm lam (f + g) - coneForm lam f - coneForm lam g

/-- **The exact quadratic expansion.** -/
theorem coneForm_add_smul (lam : ℕ → ℝ) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : ℝ) :
    coneForm lam (f + (t : ℂ) • g) =
      t ^ 2 * coneForm lam g + t * polarForm lam f g + coneForm lam f := by
  have h₁ := admissible_weilTest hf hfc
  have h₂ : Admissible (EF.weilTest (f + g) (f + g)) := admissible_weilTest (hf.add hg) (hfc.add hgc)
  have h₃ := admissible_weilTest hg hgc
  have hk : EF.weilTest (f + (t : ℂ) • g) (f + (t : ℂ) • g) =
      (((1 - t : ℝ) : ℂ) • EF.weilTest f f + ((t : ℝ) : ℂ) • EF.weilTest (f + g) (f + g)) +
        ((t ^ 2 - t : ℝ) : ℂ) • EF.weilTest g g := by
    funext x
    have e₁ := weilTest_add_smul_self hf.continuous hfc hg.continuous hgc (t : ℂ) x
    have e₂ := weilTest_add_smul_self hf.continuous hfc hg.continuous hgc (1 : ℂ) x
    rw [one_smul] at e₂
    rw [e₁]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e₂]
    simp only [map_one, one_mul, mul_one, Complex.conj_ofReal]
    push_cast
    ring
  unfold polarForm coneForm
  rw [hk, weilFullFunctional_add lam ((h₁.smul _).add (h₂.smul _)) (h₃.smul _),
    weilFullFunctional_add lam (h₁.smul _) (h₂.smul _), weilFullFunctional_smul,
    weilFullFunctional_smul, weilFullFunctional_smul, Complex.add_re, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem tsupport_add_smul_subset {f g : ℝ → ℂ} {c t : ℝ} (hfs : tsupport f ⊆ Icc (-c) c)
    (hgs : tsupport g ⊆ Icc (-c) c) : tsupport (f + (t : ℂ) • g) ⊆ Icc (-c) c := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hmem
  apply hu
  have h₁ : f u = 0 := image_eq_zero_of_notMem_tsupport fun h => hmem (hfs h)
  have h₂ : g u = 0 := image_eq_zero_of_notMem_tsupport fun h => hmem (hgs h)
  simp [h₁, h₂]

/-- **Cauchy–Schwarz on a window.** -/
theorem sq_polar_coneForm_le {lam : ℕ → ℝ} {c : ℝ} (h : WeilPositiveFullUpTo lam c) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-c) c) (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-c) c) :
    polarForm lam f g ^ 2 ≤ 4 * coneForm lam g * coneForm lam f := by
  have hfc : HasCompactSupport f := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hgc : HasCompactSupport g := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport g) hgs
  have hq : ∀ t : ℝ, 0 ≤ coneForm lam g * (t * t) + polarForm lam f g * t + coneForm lam f := by
    intro t
    have h1 := h (f + (t : ℂ) • g) (hf.add (contDiff_const.smul hg))
      (tsupport_add_smul_subset hfs hgs)
    have h2 := coneForm_add_smul lam hf hfc hg hgc t
    unfold coneForm at h2
    rw [h2] at h1
    unfold coneForm
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  linarith

/-! ### The form of a real test, and its polarization -/

theorem coneForm_ofReal (lam : ℕ → ℝ) {Z : ℝ → ℝ} (hZ : ContDiff ℝ 2 Z) (hZc : HasCompactSupport Z) :
    coneForm lam (fun u => (Z u : ℂ)) =
      (zetaZeroConfig.W (fun u => (Z u : ℂ)) (fun u => (Z u : ℂ))).re -
        atomPairing (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) (crossCorr Z Z) := by
  have h := re_weilFullFunctional_add_eq (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
    (F := Z) (Complex.ofRealCLM.contDiff.comp hZ) hZc
  have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) +
      (lam n - (ArithmeticFunction.vonMangoldt n : ℝ))) = lam := funext fun n => by ring
  rw [hfun] at h
  exact h

theorem crossCorr_add_add {X Y : ℝ → ℝ} (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (hYc : HasCompactSupport Y) (y : ℝ) :
    crossCorr (fun t => X t + Y t) (fun t => X t + Y t) y =
      crossCorr X X y + crossCorr X Y y + crossCorr Y X y + crossCorr Y Y y := by
  unfold crossCorr
  have i₁ := integrable_translate_prod hX hXc hX y
  have i₂ := integrable_translate_prod hX hXc hY y
  have i₃ := integrable_translate_prod hY hYc hX y
  have i₄ := integrable_translate_prod hY hYc hY y
  have i₅ : Integrable fun t => X t * X (t - y) + X t * Y (t - y) := i₁.add i₂
  have i₆ : Integrable fun t => X t * X (t - y) + X t * Y (t - y) + Y t * X (t - y) := i₅.add i₃
  rw [← integral_add i₁ i₂, ← integral_add i₅ i₃, ← integral_add i₆ i₄]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  ring

/-- The finite form of the atom pairing of a compactly supported profile. -/
theorem atomPairing_eq_sum (v : ℕ → ℝ) {g : ℝ → ℝ} {N : ℕ}
    (hg : ∀ n : ℕ, N ≤ n → g (Real.log n) = 0 ∧ g (-Real.log n) = 0) :
    atomPairing v g = ∑ n ∈ Finset.range N,
      (if 2 ≤ n then v n / Real.sqrt n else 0) * (g (Real.log n) + g (-Real.log n)) := by
  unfold atomPairing
  refine tsum_eq_sum fun n hn => ?_
  obtain ⟨h₁, h₂⟩ := hg n (by simpa using hn)
  rw [h₁, h₂, add_zero, mul_zero]

/-- The atom pairing sees the polarization of the correlation twice the mixed reading. -/
theorem atomPairing_polar_eq (v : ℕ → ℝ) {X Y : ℝ → ℝ} (hX : Continuous X)
    (hXc : HasCompactSupport X) (hY : Continuous Y) (hYc : HasCompactSupport Y) {R : ℝ}
    (hXs : ∀ t, R < |t| → X t = 0) (hYs : ∀ t, R < |t| → Y t = 0) :
    atomPairing v (crossCorr (fun t => X t + Y t) (fun t => X t + Y t)) -
        atomPairing v (crossCorr X X) - atomPairing v (crossCorr Y Y) =
      2 * atomPairing v (crossCorr X Y) := by
  have hZs : ∀ t, R < |t| → X t + Y t = 0 := fun t ht => by rw [hXs t ht, hYs t ht, add_zero]
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (R + R + 1))
  have hlog : ∀ n : ℕ, N ≤ n → R + R < |Real.log n| ∧ R + R < |-Real.log n| := by
    intro n hn
    have hnr : Real.exp (R + R + 1) ≤ n := hN.trans (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans_le hnr
    have h1 : R + R + 1 ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hnr
    have h2 : R + R < |Real.log n| := by
      calc R + R < R + R + 1 := by linarith
        _ ≤ Real.log n := h1
        _ ≤ |Real.log n| := le_abs_self _
    exact ⟨h2, by rwa [abs_neg]⟩
  have hvan : ∀ {A B : ℝ → ℝ}, (∀ t, R < |t| → A t = 0) → (∀ t, R < |t| → B t = 0) →
      ∀ n : ℕ, N ≤ n → crossCorr A B (Real.log n) = 0 ∧ crossCorr A B (-Real.log n) = 0 :=
    fun hA hB n hn => ⟨crossCorr_eq_zero hA hB (hlog n hn).1, crossCorr_eq_zero hA hB (hlog n hn).2⟩
  rw [atomPairing_eq_sum v (hvan hZs hZs), atomPairing_eq_sum v (hvan hXs hXs),
    atomPairing_eq_sum v (hvan hYs hYs), atomPairing_eq_sum v (hvan hXs hYs),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [crossCorr_add_add hX hXc hY hYc, crossCorr_add_add hX hXc hY hYc,
    crossCorr_swap (X := Y) (Y := X) (Real.log n), crossCorr_swap (X := Y) (Y := X) (-Real.log n),
    neg_neg]
  ring

/-! ### The zero side, mixed -/

/-- The mixed zero-side bound. -/
theorem norm_W_le_of_zero_bounds {f g : ℝ → ℂ} {E₁ E₂ : ℝ} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hv : ∀ ρ : zetaZeroConfig.carrier,
      (1 + |(ρ : ℂ).im|) * ‖paperFT f (gammaOf ρ)‖ ≤ E₁ ∧
        (1 + |(ρ : ℂ).im|) * ‖paperFT g ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E₂) :
    ‖zetaZeroConfig.W f g‖ ≤ (5 / 4) * zetaInvSqSum * (E₁ * E₂) := by
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  have hpt : ∀ ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f g ρ‖ ≤
      (5 / 4) * (E₁ * E₂) * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hstrip := zetaZeroConfig.strip ρ ρ.2
    obtain ⟨hv1, hv2⟩ := hv ρ
    have hq := one_div_one_add_abs_im_sq_le hstrip
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    set x1 := ‖paperFT f (gammaOf ρ)‖
    set x2 := ‖paperFT g ((starRingEnd ℂ) (gammaOf ρ))‖
    have hprod : x1 * x2 ≤ (E₁ * E₂) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
      have h12 : ((1 + |(ρ : ℂ).im|) * x1) * ((1 + |(ρ : ℂ).im|) * x2) ≤ E₁ * E₂ :=
        mul_le_mul hv1 hv2 (by positivity) hE₁
      rw [← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc (zetaZeroConfig.mult ρ : ℝ) * x1 * x2 = (zetaZeroConfig.mult ρ : ℝ) * (x1 * x2) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * ((E₁ * E₂) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod hm
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
            ((E₁ * E₂) * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))))) := by
          gcongr
      _ = (5 / 4) * (E₁ * E₂) * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
          ring
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f g ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left, zetaInvSqSum]
  ring

theorem gammaOf_reflect_eq' (ρ : ℂ) : gammaOf (reflect ρ) = (starRingEnd ℂ) (gammaOf ρ) := by
  unfold gammaOf reflect
  apply Complex.ext
  · simp
  · simp
    ring

/-- `‖F̂_{j,L}‖` at either point of a zero is below the tail bound, relative to the height. -/
theorem zero_bound_truncTest {Λc : ℝ} (hΛ0 : 0 ≤ Λc)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λc) (j : ℕ) (L : ℝ)
    (ρ : zetaZeroConfig.carrier) :
    (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (truncTest (𝔽 j) L u : ℂ)) (gammaOf ρ)‖ ≤
        tailBound (𝔽 j) Λc L ∧
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (truncTest (𝔽 j) L u : ℂ))
        ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ tailBound (𝔽 j) Λc L := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  have hexp := (hF j).expDecayTest (by norm_num : (0 : ℝ) < 1 / 4)
  have hzero := fun ρ => paperFT_xiShiftedGammaTest_gammaOf j ρ
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ⟨hmem.2.1, hmem.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip).le
  have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  constructor
  · have h := one_add_abs_re_mul_norm_paperFT_truncTest_sub_self_le hexp hΛ hΛ0 L hIm
    rwa [hzero ρ, sub_zero, hre] at h
  · set ρ' : zetaZeroConfig.carrier := ⟨reflect (ρ : ℂ), zeta_reflect_zero _ hmem⟩
    have hg : gammaOf (ρ' : ℂ) = (starRingEnd ℂ) (gammaOf (ρ : ℂ)) := gammaOf_reflect_eq' _
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    have h := one_add_abs_re_mul_norm_paperFT_truncTest_sub_self_le hexp hΛ hΛ0 L hIm'
    rw [← hg, hzero ρ', sub_zero, hg, Complex.conj_re, hre] at h
    exact h

/-- The height-weighted size of the transform of a real test, at every point of a zero, is bounded by
its weighted `L¹` norm and that of its derivative. -/
theorem zero_bound_real_test {Y : ℝ → ℝ} (hY : ContDiff ℝ 2 Y) (hYc : HasCompactSupport Y)
    (ρ : zetaZeroConfig.carrier) :
    (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) (gammaOf ρ)‖ ≤
        (∫ u : ℝ, ‖(Y u : ℂ)‖ * Real.exp (1 / 2 * |u|)) +
          ∫ u : ℝ, ‖((deriv Y u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) ∧
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        (∫ u : ℝ, ‖(Y u : ℂ)‖ * Real.exp (1 / 2 * |u|)) +
          ∫ u : ℝ, ‖((deriv Y u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) := by
  have hYc' : Continuous (deriv Y) := hY.continuous_deriv (by norm_num)
  have hYs' : HasCompactSupport (deriv Y) := hYc.deriv
  have hd : ∀ x, HasDerivAt (fun u => (Y u : ℂ)) ((deriv Y x : ℝ) : ℂ) x := fun x =>
    ((hY.differentiable (by norm_num) x).hasDerivAt).ofReal_comp
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ⟨hmem.2.1, hmem.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip).le
  have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  have key := fun {z : ℂ} (hz : |z.im| ≤ 1 / 2) => one_add_abs_re_mul_norm_paperFT_le
    (superExpDecay_ofReal hY.continuous hYc) (superExpDecay_ofReal hYc' hYs') hd hz
  constructor
  · have h := key hIm
    rwa [hre] at h
  · have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    have h := key hIm'
    rwa [Complex.conj_re, hre] at h

/-- The height-weighted size of the transform of a fixed real test, at every point of a zero. -/
theorem exists_zero_bound_real_test {Y : ℝ → ℝ} (hY : ContDiff ℝ 2 Y) (hYc : HasCompactSupport Y) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ ρ : zetaZeroConfig.carrier,
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) (gammaOf ρ)‖ ≤ E ∧
        (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E :=
  ⟨_, add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity),
    zero_bound_real_test hY hYc⟩

/-- The polarization of the zero side of `Φ_L` against a fixed test is bounded by its tail. -/
theorem abs_polar_W_le {Λc : ℝ} (hΛ0 : 0 ≤ Λc)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λc) {Y : ℝ → ℝ} {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ ρ : zetaZeroConfig.carrier,
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) (gammaOf ρ)‖ ≤ E ∧
        (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E)
    (j : ℕ) (L : ℝ) :
    ‖zetaZeroConfig.W (fun u => (truncTest (𝔽 j) L u : ℂ)) (fun u => (Y u : ℂ))‖ ≤
        (5 / 4) * zetaInvSqSum * (tailBound (𝔽 j) Λc L * E) ∧
      ‖zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (truncTest (𝔽 j) L u : ℂ))‖ ≤
        (5 / 4) * zetaInvSqSum * (E * tailBound (𝔽 j) Λc L) := by
  have ht := tailBound_nonneg (𝔽 j) hΛ0 L
  refine ⟨norm_W_le_of_zero_bounds ht hE0 fun ρ => ⟨(zero_bound_truncTest hΛ0 hΛ j L ρ).1, (hE ρ).2⟩,
    norm_W_le_of_zero_bounds hE0 ht fun ρ => ⟨(hE ρ).1, (zero_bound_truncTest hΛ0 hΛ j L ρ).2⟩⟩

/-! ### The polarization of real tests -/

/-- The polarization of real tests: the zero side minus the mixed reading of the weights. -/
theorem polarForm_ofReal (lam : ℕ → ℝ) {X Y : ℝ → ℝ} (hX : ContDiff ℝ 2 X)
    (hXc : HasCompactSupport X) (hY : ContDiff ℝ 2 Y) (hYc : HasCompactSupport Y) {R : ℝ}
    (hXs : ∀ t, R < |t| → X t = 0) (hYs : ∀ t, R < |t| → Y t = 0) :
    polarForm lam (fun u => (X u : ℂ)) (fun u => (Y u : ℂ)) =
      (zetaZeroConfig.W (fun u => (X u : ℂ)) (fun u => (Y u : ℂ)) +
        zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (X u : ℂ))).re -
      2 * atomPairing (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) (crossCorr X Y) := by
  have hf : ContDiff ℝ 2 (fun u => (X u : ℂ)) := Complex.ofRealCLM.contDiff.comp hX
  have hg : ContDiff ℝ 2 (fun u => (Y u : ℂ)) := Complex.ofRealCLM.contDiff.comp hY
  have hfc : HasCompactSupport (fun u => (X u : ℂ)) := hXc.comp_left Complex.ofReal_zero
  have hgc : HasCompactSupport (fun u => (Y u : ℂ)) := hYc.comp_left Complex.ofReal_zero
  have hZ : ContDiff ℝ 2 (fun t => X t + Y t) := hX.add hY
  have hZc : HasCompactSupport (fun t => X t + Y t) := hXc.add hYc
  have hsum : (fun u => (X u : ℂ)) + (fun u => (Y u : ℂ)) = fun u => ((X u + Y u : ℝ) : ℂ) := by
    funext u
    simp
  have hZ0 := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have hW : zetaZeroConfig.W (fun u => ((X u + Y u : ℝ) : ℂ)) (fun u => ((X u + Y u : ℝ) : ℂ)) =
      zetaZeroConfig.W (fun u => (X u : ℂ)) (fun u => (X u : ℂ)) +
        zetaZeroConfig.W (fun u => (X u : ℂ)) (fun u => (Y u : ℂ)) +
        (zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (X u : ℂ)) +
          zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (Y u : ℂ))) := by
    have hfg : ContDiff ℝ 2 ((fun u => (X u : ℂ)) + fun u => (Y u : ℂ)) := hf.add hg
    have hfgc : HasCompactSupport ((fun u => (X u : ℂ)) + fun u => (Y u : ℂ)) := hfc.add hgc
    rw [← hsum, ArithmeticCastelnuovoSeveri.W_add_left _ hZ0 hf hfc hg hgc hfg hfgc,
      ArithmeticCastelnuovoSeveri.W_add_right _ hZ0 hf hfc hf hfc hg hgc,
      ArithmeticCastelnuovoSeveri.W_add_right _ hZ0 hg hgc hf hfc hg hgc]
  have hp := atomPairing_polar_eq (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
    hX.continuous hXc hY.continuous hYc hXs hYs
  unfold polarForm
  rw [hsum, coneForm_ofReal lam hZ hZc, coneForm_ofReal lam hX hXc, coneForm_ofReal lam hY hYc, hW]
  simp only [Complex.add_re]
  linarith

/-- **A fixed test has bounded energy on the cone.** Its correlations see only the integers `n ≤ e^{2R}`,
which lie in the box. -/
/-- The form of a real test on a window is bounded by its zero side, the size of the box, and the number
of atoms its autocorrelation sees. -/
theorem coneForm_le_of_bounds {Y : ℝ → ℝ} (hY : ContDiff ℝ 2 Y) (hYc : HasCompactSupport Y) {R B I : ℝ}
    (hR : 0 ≤ R) (hYs : ∀ t, R < |t| → Y t = 0) (hB : ∀ t, |Y t| ≤ B) (hI : ∫ t, |Y t| ≤ I)
    {c : ℝ} {lam : ℕ → ℝ} (hc : R + 1 / 12 ≤ c) (hlam : WeilPositiveFullUpTo lam c) :
    coneForm lam (fun u => (Y u : ℂ)) ≤
      |(zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (Y u : ℂ))).re| +
        (Real.exp (R + R + 1) + 1) * ((4 * R + boxConst) * (2 * (B * I))) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hYi : Integrable Y := hY.continuous.integrable_of_hasCompactSupport hYc
  have hI0 : 0 ≤ I := (integral_nonneg fun _ => abs_nonneg _).trans hI
  have hcorr : ∀ y, |crossCorr Y Y y| ≤ B * I := fun y => by
    unfold crossCorr
    refine (abs_integral_le_integral_abs).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hI hB0)
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (hYi.abs.const_mul B) (Eventually.of_forall fun t => ?_)
    simp only
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB (t - y)) (abs_nonneg _)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈Real.exp (R + R + 1)⌉₊ := ⟨_, rfl⟩
  have hNge : Real.exp (R + R + 1) ≤ N := by rw [hN]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ Real.exp (R + R + 1) + 1 := by
    rw [hN]; exact (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  have hlog : ∀ n : ℕ, N ≤ n → R + R < |Real.log n| ∧ R + R < |-Real.log n| := by
    intro n hn
    have hnr : Real.exp (R + R + 1) ≤ n := hNge.trans (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans_le hnr
    have h1 : R + R + 1 ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hnr
    have h2 : R + R < |Real.log n| := by
      calc R + R < R + R + 1 := by linarith
        _ ≤ Real.log n := h1
        _ ≤ |Real.log n| := le_abs_self _
    exact ⟨h2, by rwa [abs_neg]⟩
  have hC := boxConst_nonneg
  obtain ⟨V, hV⟩ : ∃ V, V = 4 * R + boxConst := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; linarith
  rw [← hV]
  rw [coneForm_ofReal lam hY hYc, atomPairing_eq_sum _ (N := N) fun n hn =>
    ⟨crossCorr_eq_zero hYs hYs (hlog n hn).1, crossCorr_eq_zero hYs hYs (hlog n hn).2⟩]
  have hterm : ∀ n ∈ Finset.range N,
      -((if 2 ≤ n then (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) / Real.sqrt n else 0) *
        (crossCorr Y Y (Real.log n) + crossCorr Y Y (-Real.log n))) ≤ V * (2 * (B * I)) := by
    intro n _
    have hnon : 0 ≤ V * (2 * (B * I)) := by positivity
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      by_cases hle : (n : ℝ) ≤ Real.exp (2 * R)
      · have h1 := abs_sub_vonMangoldt_div_sqrt_le hlam hc h2 hle
        rw [← hV] at h1
        have h3 : |(lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) / Real.sqrt n| ≤ V := by
          rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact h1
        have h4 : |crossCorr Y Y (Real.log n) + crossCorr Y Y (-Real.log n)| ≤ 2 * (B * I) := by
          have := abs_add_le (crossCorr Y Y (Real.log n)) (crossCorr Y Y (-Real.log n))
          linarith [hcorr (Real.log n), hcorr (-Real.log n)]
        have h5 := mul_le_mul h3 h4 (abs_nonneg _) hV0
        rw [← abs_mul] at h5
        exact (neg_le_abs _).trans h5
      · have hlt : 2 * R < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr (not_le.mp hle)
        have hRR : R + R < |Real.log n| := by
          have := le_abs_self (Real.log n)
          linarith
        rw [crossCorr_eq_zero hYs hYs hRR,
          crossCorr_eq_zero hYs hYs (by rwa [abs_neg] : R + R < |-Real.log n|)]
        simpa using hnon
    · rw [if_neg h2]
      simpa using hnon
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [Finset.sum_neg_distrib, Finset.card_range, nsmul_eq_mul] at hsum
  have h6 := le_abs_self (zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (Y u : ℂ))).re
  have h7 : (N : ℝ) * (V * (2 * (B * I))) ≤ (Real.exp (R + R + 1) + 1) * (V * (2 * (B * I))) :=
    mul_le_mul_of_nonneg_right hNle (by positivity)
  linarith

theorem exists_coneForm_le {Y : ℝ → ℝ} (hY : ContDiff ℝ 2 Y) (hYc : HasCompactSupport Y) {R : ℝ}
    (hR : 0 ≤ R) (hYs : ∀ t, R < |t| → Y t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (lam : ℕ → ℝ), R + 1 / 12 ≤ c → WeilPositiveFullUpTo lam c →
      coneForm lam (fun u => (Y u : ℂ)) ≤ C := by
  obtain ⟨B, hB⟩ := hYc.exists_bound_of_continuous hY.continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hI0 : 0 ≤ ∫ t, |Y t| := integral_nonneg fun _ => abs_nonneg _
  have hC := boxConst_nonneg
  exact ⟨_, by positivity, fun c lam hc hlam =>
    coneForm_le_of_bounds hY hYc hR hYs (fun t => hB t) le_rfl hc hlam⟩

/-! ### The pinning -/

theorem doubleExpTail_le_sqrt_ceiling {c : ℝ} (hc : 0 ≤ c) :
    doubleExpTail (c - 1 / 12 - 1) ≤ Real.sqrt (marginCeiling c) := by
  have hτ0 := (doubleExpTail_pos (c - 1 / 12 - 1)).le
  have hτ1 := doubleExpTail_le_one (c - 1 / 12 - 1)
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : doubleExpTail (c - 1 / 12 - 1) ≤ doubleExpTail (c - 2) :=
    doubleExpTail_anti (by linarith)
  have h2 : (1 : ℝ) ≤ Real.exp (3 * c) := Real.one_le_exp (by linarith)
  have h3 : doubleExpTail (c - 2) ≤ marginCeiling c := by
    rw [← exp_mul_doubleExpTail]
    exact le_mul_of_one_le_left (doubleExpTail_pos _).le h2
  nlinarith

/-- **Pinning with explicit dependence on the second test.** Every real test `Y` on the window, with
form at most `CY` and zero size at most `E`, satisfies
`|Σ_n (λ(n) − Λ(n)) n^{−1/2} ((Φ_L ⋆ Y)(log n) + (Φ_L ⋆ Y)(−log n))| ≤ C₀ (E + √CY) exp(½(3c − (π/16) e^{2(c−2)}))`,
with `L = c − 1/12`, for every `λ ∈ 𝒜(c)`, and `C₀` depends on nothing. -/
theorem exists_uniform_pinning :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (c : ℝ) (lam : ℕ → ℝ) (Y : ℝ → ℝ) (CY E : ℝ), 1 ≤ c →
      WeilPositiveFullUpTo lam c → ContDiff ℝ 2 Y → HasCompactSupport Y →
      (∀ t, c < |t| → Y t = 0) → 0 ≤ CY → coneForm lam (fun u => (Y u : ℂ)) ≤ CY → 0 ≤ E →
      (∀ ρ : zetaZeroConfig.carrier,
        (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) (gammaOf ρ)‖ ≤ E ∧
          (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E) →
      |atomPairing (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (truncTest (𝔽 0) (c - 1 / 12)) Y)| ≤
        C₀ * (E + Real.sqrt CY) * Real.sqrt (marginCeiling c) := by
  obtain ⟨w, hw, K, hK, hmain⟩ := exists_nullWeights_tsum_nullEnergy_le
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hw0 := hw.pos_zero
  have hI := absMass_nonneg
  have hD := decayConst_nonneg
  have hZs : 0 ≤ zetaInvSqSum := zetaInvSqSum_nonneg
  have hg0 := gammaScale_nonneg 0
  obtain ⟨T, hT⟩ : ∃ T, T = (3 + 4 * Λc) * (decayConst * gammaScale 0) * absMass := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Real.sqrt (4 * (K / w 0)) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Real.sqrt_nonneg _
  obtain ⟨P, hP⟩ : ∃ P, P = (5 / 2) * zetaInvSqSum * T := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  refine ⟨(P + Q) / 2, by positivity, fun c lam Y CY E hc hlam hY hYc hYs' hCY0 hCY hE0 hE => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L, L = c - 1 / 12 := ⟨_, rfl⟩
  rw [← hL]
  have hLc : L ≤ c := by rw [hL]; linarith
  obtain ⟨Cd, -, hFd⟩ := exists_decayBound_xiShiftedGammaTest
  have hX : ContDiff ℝ 2 (truncTest (𝔽 0) L) := contDiff_truncTest (hFd 0).1 L
  have hXc : HasCompactSupport (truncTest (𝔽 0) L) := hasCompactSupport_truncTest _ L
  have hc0 : 0 ≤ c := by linarith
  have hXs : ∀ t, c < |t| → truncTest (𝔽 0) L t = 0 := fun t ht =>
    truncTest_eq_zero (hLc.trans ht.le)
  have hf : ContDiff ℝ 2 (fun u => (truncTest (𝔽 0) L u : ℂ)) := Complex.ofRealCLM.contDiff.comp hX
  have hg : ContDiff ℝ 2 (fun u => (Y u : ℂ)) := Complex.ofRealCLM.contDiff.comp hY
  have hfs : tsupport (fun u => (truncTest (𝔽 0) L u : ℂ)) ⊆ Icc (-c) c :=
    tsupport_nullTest_subset 0 hLc
  have hgs : tsupport (fun u => (Y u : ℂ)) ⊆ Icc (-c) c := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hm
    apply hu
    have h1 : c < |u| := by
      by_contra h2
      exact hm (abs_le.mp (not_lt.mp h2))
    simp [hYs' u h1]
  -- the near-nullity of the kernel
  have hEj : ∀ j, 0 ≤ nullEnergy lam j L := fun j =>
    hlam (nullTest j L) (contDiff_nullTest j L) (tsupport_nullTest_subset j hLc)
  obtain ⟨hs, hle⟩ := hmain c lam hc hlam
  rw [← hL] at hs hle
  have h0 : w 0 * nullEnergy lam 0 L ≤ ∑' j, w j * nullEnergy lam j L :=
    hs.le_tsum 0 fun j _ => mul_nonneg (hw.nonneg j) (hEj j)
  have hnull : coneForm lam (fun u => (truncTest (𝔽 0) L u : ℂ)) ≤ K / w 0 * marginCeiling c := by
    have h1 : w 0 * nullEnergy lam 0 L ≤ K * marginCeiling c := h0.trans hle
    have h2 : nullEnergy lam 0 L ≤ K * marginCeiling c / w 0 := by
      rw [le_div_iff₀ hw0]
      linarith
    calc coneForm lam (fun u => (truncTest (𝔽 0) L u : ℂ)) = nullEnergy lam 0 L := rfl
      _ ≤ K * marginCeiling c / w 0 := h2
      _ = _ := by ring
  -- Cauchy–Schwarz
  have hCS := sq_polar_coneForm_le hlam hf hfs hg hgs
  have hM := (marginCeiling_pos c).le
  have hXnon : 0 ≤ coneForm lam (fun u => (truncTest (𝔽 0) L u : ℂ)) := hEj 0
  have hprod : polarForm lam (fun u => (truncTest (𝔽 0) L u : ℂ)) (fun u => (Y u : ℂ)) ^ 2 ≤
      CY * (4 * (K / w 0)) * marginCeiling c := by
    refine hCS.trans ?_
    have hnn : 0 ≤ K / w 0 * marginCeiling c := by positivity
    calc 4 * coneForm lam (fun u => (Y u : ℂ)) * coneForm lam (fun u => (truncTest (𝔽 0) L u : ℂ))
        ≤ 4 * CY * (K / w 0 * marginCeiling c) := by
          have := mul_le_mul hCY hnull hXnon hCY0
          nlinarith
      _ = _ := by ring
  have hpolar : |polarForm lam (fun u => (truncTest (𝔽 0) L u : ℂ)) (fun u => (Y u : ℂ))| ≤
      Real.sqrt CY * Q * Real.sqrt (marginCeiling c) := by
    have h1 := Real.abs_le_sqrt hprod
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_mul hCY0, ← hQ] at h1
  -- the zero side
  obtain ⟨hz₁, hz₂⟩ := abs_polar_W_le hΛ0 hΛ hE0 hE 0 L
  have htail := tailBound_xiShiftedGammaTest_le hΛ0 0 L
  have hτ := doubleExpTail_le_sqrt_ceiling hc0
  rw [← hL] at hτ
  have htail2 : tailBound (𝔽 0) Λc L ≤ T * Real.sqrt (marginCeiling c) := by
    refine htail.trans ?_
    rw [hT]
    exact mul_le_mul_of_nonneg_left hτ (by positivity)
  have hzero : ‖zetaZeroConfig.W (fun u => (truncTest (𝔽 0) L u : ℂ)) (fun u => (Y u : ℂ))‖ +
      ‖zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (truncTest (𝔽 0) L u : ℂ))‖ ≤
      P * E * Real.sqrt (marginCeiling c) := by
    have h3 : (5 / 4) * zetaInvSqSum * (tailBound (𝔽 0) Λc L * E) ≤
        (5 / 4) * zetaInvSqSum * ((T * Real.sqrt (marginCeiling c)) * E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htail2 hE0) (by positivity)
    have e : (5 / 4) * zetaInvSqSum * (E * tailBound (𝔽 0) Λc L) =
        (5 / 4) * zetaInvSqSum * (tailBound (𝔽 0) Λc L * E) := by ring
    rw [e] at hz₂
    rw [hP]
    nlinarith
  -- the reading
  have hread := polarForm_ofReal lam hX hXc hY hYc hXs hYs'
  obtain ⟨A, hA⟩ : ∃ A, A = atomPairing (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
    (crossCorr (truncTest (𝔽 0) L) Y) := ⟨_, rfl⟩
  rw [← hA] at hread ⊢
  have hzre : |(zetaZeroConfig.W (fun u => (truncTest (𝔽 0) L u : ℂ)) (fun u => (Y u : ℂ)) +
      zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (truncTest (𝔽 0) L u : ℂ))).re| ≤
      P * E * Real.sqrt (marginCeiling c) :=
    (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans hzero)
  have hA2 : 2 * A = (zetaZeroConfig.W (fun u => (truncTest (𝔽 0) L u : ℂ)) (fun u => (Y u : ℂ)) +
      zetaZeroConfig.W (fun u => (Y u : ℂ)) (fun u => (truncTest (𝔽 0) L u : ℂ))).re -
      polarForm lam (fun u => (truncTest (𝔽 0) L u : ℂ)) (fun u => (Y u : ℂ)) := by
    rw [hread]
    ring
  have hfin : |2 * A| ≤ (P * E + Real.sqrt CY * Q) * Real.sqrt (marginCeiling c) := by
    rw [hA2, add_mul]
    exact (abs_sub _ _).trans (add_le_add hzre hpolar)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hfin
  have hs0 := Real.sqrt_nonneg CY
  have hsM := Real.sqrt_nonneg (marginCeiling c)
  have hcomp : (P * E + Real.sqrt CY * Q) * Real.sqrt (marginCeiling c) ≤
      (P + Q) * (E + Real.sqrt CY) * Real.sqrt (marginCeiling c) := by
    refine mul_le_mul_of_nonneg_right ?_ hsM
    nlinarith [mul_nonneg hP0 hs0, mul_nonneg hQ0 hE0]
  have e2 : (P + Q) / 2 * (E + Real.sqrt CY) * Real.sqrt (marginCeiling c) =
      (P + Q) * (E + Real.sqrt CY) * Real.sqrt (marginCeiling c) / 2 := by ring
  rw [e2]
  linarith

/-- **The theta-smoothed weights are pinned.** For every fixed test `Y` there is `C` such that every
`λ ∈ 𝒜(c)` satisfies
`|Σ_n (λ(n) − Λ(n)) n^{−1/2} ((Φ_L ⋆ Y)(log n) + (Φ_L ⋆ Y)(−log n))| ≤ C exp(½(3c − (π/16) e^{2(c−2)}))`,
with `L = c − 1/12`. -/
theorem exists_abs_atomPairing_crossCorr_le {Y : ℝ → ℝ} (hY : ContDiff ℝ 2 Y)
    (hYc : HasCompactSupport Y) {R : ℝ} (hR : 0 ≤ R) (hYs : ∀ t, R < |t| → Y t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (lam : ℕ → ℝ), 1 ≤ c → R + 1 / 12 ≤ c →
      WeilPositiveFullUpTo lam c →
      |atomPairing (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (truncTest (𝔽 0) (c - 1 / 12)) Y)| ≤ C * Real.sqrt (marginCeiling c) := by
  obtain ⟨C₀, hC₀, hpin⟩ := exists_uniform_pinning
  obtain ⟨CY, hCY0, hCY⟩ := exists_coneForm_le hY hYc hR hYs
  obtain ⟨E, hE0, hE⟩ := exists_zero_bound_real_test hY hYc
  refine ⟨C₀ * (E + Real.sqrt CY), by positivity, fun c lam hc hRc hlam => ?_⟩
  exact hpin c lam Y CY E hc hlam hY hYc
    (fun t ht => hYs t (lt_of_le_of_lt (by linarith) ht)) hCY0 (hCY c lam hRc hlam) hE0 hE

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
