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
  have h₂ := admissible_weilTest (hf.add hg) (hfc.add hgc)
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
  have hq : ∀ t : ℝ, 0 ≤ coneForm lam g * t * t + polarForm lam f g * t + coneForm lam f := by
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
  rw [← integral_add i₁ i₂, ← integral_add (i₁.add i₂) i₃, ← integral_add ((i₁.add i₂).add i₃) i₄]
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

/-- The height-weighted size of the transform of a fixed real test, at every point of a zero. -/
theorem exists_zero_bound_real_test {Y : ℝ → ℝ} (hY : ContDiff ℝ 2 Y) (hYc : HasCompactSupport Y) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ ρ : zetaZeroConfig.carrier,
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) (gammaOf ρ)‖ ≤ E ∧
        (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E := by
  have hYc' : Continuous (deriv Y) := hY.continuous_deriv (by norm_num)
  have hYs' : HasCompactSupport (deriv Y) := hYc.deriv
  have hd : ∀ x, HasDerivAt (fun u => (Y u : ℂ)) ((deriv Y x : ℝ) : ℂ) x := fun x =>
    ((hY.differentiable (by norm_num) x).hasDerivAt).ofReal_comp
  set E : ℝ := (∫ u : ℝ, ‖(Y u : ℂ)‖ * Real.exp (1 / 2 * |u|)) +
    ∫ u : ℝ, ‖((deriv Y u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) with hE
  have hE0 : 0 ≤ E := add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)
  refine ⟨E, hE0, fun ρ => ?_⟩
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

/-- The polarization of the zero side of `Φ_L` against a fixed test is bounded by its tail. -/
theorem abs_polar_W_le {Λc : ℝ} (hΛ0 : 0 ≤ Λc)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λc) {Y : ℝ → ℝ} (hY : ContDiff ℝ 2 Y)
    (hYc : HasCompactSupport Y) {E : ℝ} (hE0 : 0 ≤ E)
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

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
