import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneSidedLefschetzBoundsAtTwoPrimesAreTheStrip

/-!
# One-sided Lefschetz bounds at one prime are the zero-free strip

Over `𝔽_q` an upper bound on the point counts misses a real outer eigenvalue: the counts are the
orbit correlations of the diagonal alone, its Frobenius weight is fixed, and `Re(W β^m)` keeps one
sign when `β > 0`. Rotating the cycle removes the exception. Over `ℤ` the two-term test
`g + c T_v g` (`twoTermTest`) multiplies the transform by `1 + c e^{izv}`,
keeps every zero that `g` kills killed, and multiplies the weight `X_ρ conj X_{1−ρ̄}` of a kept zero
by `(1 + c e^{iγv}) conj(1 + c e^{iγ̄v})` (`weight_twoTermTest`); with `c = u e^{−i Im ρ}`, `v = 1`
this factor is `(1 + u e^δ)(1 + ū e^{−δ})`, `δ = Re ρ − ½` (`rotation_factor`), which is `1`,
negative, or `2 ± i(e^δ − e^{−δ})` for `u = 0, −1, ±i`. So every nonzero weight is rotated into
the right half-plane (`exists_rotation_re_pos`).

* **One prime** (`deepSparse_exists_test_oneSided`). For a deep-sparse configuration, a right zero
  `ρ` and a sign `ε = ±1`, one test has `ε Re c_m > C R^m` for some `m`, for every `C` and
  `R < |β_ρ|`: if `β_ρ` is not real its phase rotates (`exists_lt_re_of_tendsto_div_pow`); if it is
  real, the rotated weight has `Re(εW) > 0` and the even `m` grow (`exists_lt_re_of_real`).
* **One-sided law** (`deepSparse_oneSided_iff`). Every test has `ε Re c_m = O(R^m)`, `R ≥ 1`, iff
  every outer eigenvalue has modulus at most `R`.
* **For `ζ`** (`zeta_width_le_iff_oneSided_onePrime`,
  `zeta_riemannHypothesis_iff_oneSided_onePrime`).
  At one prime `p` the zero width is at most `θ` iff every test has `ε Re W(T_{p^m} g, g) =
  O(p^{θm})`; RH holds iff every test satisfies the upper one-sided Weil inequality
  `Re W(T_{p^m} g, g) ≤ W(g, g)` for all `m`, and iff it satisfies the lower one.

The real-eigenvalue exception of one-sided bounds is therefore an artefact of constraining a single
cycle: rotating the test rotates Frobenius weights, and positivity of one sign at one prime, for
all tests, is as strong as Hodge index on the towers.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  zetaZeroWidth abs_re_sub_half_le_zetaZeroWidth)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Two-term tests rotate the Frobenius weight -/

/-- The two-term test `g + c T_v g`. -/
def twoTermTest (g : ℝ → ℂ) (c : ℂ) (v : ℝ) : ℝ → ℂ := g + c • translate v g

theorem twoTermTest_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (c : ℂ) (v : ℝ) :
    ContDiff ℝ 2 (twoTermTest g c v) :=
  hg.add ((translate_contDiff hg v).const_smul c)

theorem twoTermTest_hasCompactSupport {g : ℝ → ℂ} (hgc : HasCompactSupport g) (c : ℂ) (v : ℝ) :
    HasCompactSupport (twoTermTest g c v) :=
  hgc.add (translate_hasCompactSupport hgc v).smul_left

/-- The two-term test multiplies the transform by `1 + c e^{izv}`. -/
theorem paperFT_twoTermTest {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (c : ℂ)
    (v : ℝ) (z : ℂ) :
    paperFT (twoTermTest g c v) z = (1 + c * cexp (I * z * v)) * paperFT g z := by
  have ht : Continuous (c • translate v g) :=
    continuous_const.smul (hg.comp (continuous_id.sub continuous_const))
  rw [twoTermTest, paperFT_add hg hgc ht (translate_hasCompactSupport hgc v).smul_left,
    paperFT_smul, paperFT_translate]
  ring

theorem zeroCoord_twoTermTest (Z : ZeroConfig) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (c : ℂ) (v : ℝ) (τ : Z.carrier) :
    zeroCoord Z (twoTermTest g c v) τ = (1 + c * cexp (I * gammaOf τ * v)) * zeroCoord Z g τ := by
  simp only [zeroCoord, paperFT_twoTermTest hg hgc]
  ring

/-- **The weight of a zero under a two-term test** is multiplied by
`(1 + c e^{iγv}) conj(1 + c e^{iγ̄v})`. -/
theorem weight_twoTermTest (Z : ZeroConfig) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (c : ℂ) (v : ℝ) (τ : Z.carrier) :
    zeroCoord Z (twoTermTest g c v) τ *
        conj (zeroCoord Z (twoTermTest g c v) (reflectCarrier Z τ)) =
      zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) *
        ((1 + c * cexp (I * gammaOf τ * v)) *
          conj (1 + c * cexp (I * conj (gammaOf τ) * v))) := by
  rw [zeroCoord_twoTermTest Z hg hgc, zeroCoord_twoTermTest Z hg hgc]
  have e : gammaOf ((reflectCarrier Z τ : Z.carrier) : ℂ) = conj (gammaOf τ) := gammaOf_reflect _
  rw [e, map_mul]
  ring

/-- With `c = u e^{−i Im ρ}` and `v = 1` the factor is `(1 + u e^δ)(1 + ū e^{−δ})`. -/
theorem rotation_factor (ρ u : ℂ) :
    (1 + u * cexp (-(I * ρ.im)) * cexp (I * gammaOf ρ * (1 : ℝ))) *
        conj (1 + u * cexp (-(I * ρ.im)) * cexp (I * conj (gammaOf ρ) * (1 : ℝ))) =
      (1 + u * Real.exp (ρ.re - 1 / 2)) * (1 + conj u * Real.exp (-(ρ.re - 1 / 2))) := by
  have h1 : cexp (-(I * ρ.im)) * cexp (I * gammaOf ρ * (1 : ℝ)) =
      ((Real.exp (ρ.re - 1 / 2) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    apply Complex.ext <;> simp [gammaOf_eq, Complex.mul_re, Complex.mul_im]
  have h2 : cexp (-(I * ρ.im)) * cexp (I * conj (gammaOf ρ) * (1 : ℝ)) =
      ((Real.exp (-(ρ.re - 1 / 2)) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    apply Complex.ext <;> simp [gammaOf_eq, Complex.mul_re, Complex.mul_im]
  rw [mul_assoc u, h1, mul_assoc u, h2, map_add, map_one, map_mul, Complex.conj_ofReal]

/-- **Every nonzero weight rotates into the right half-plane.** For `W ≠ 0` and `δ > 0` some `u`
gives `Re(W (1 + u e^δ)(1 + ū e^{−δ})) > 0`. -/
theorem exists_rotation_re_pos {W : ℂ} (hW : W ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℂ, 0 < (W * ((1 + u * Real.exp δ) * (1 + conj u * Real.exp (-δ)))).re := by
  set a := Real.exp δ with ha
  set b := Real.exp (-δ) with hb
  have hA : 1 < a := Real.one_lt_exp_iff.mpr hδ
  have hB : b < 1 := by
    have h := Real.exp_lt_exp.mpr (show -δ < 0 by linarith)
    rwa [Real.exp_zero] at h
  rcases lt_trichotomy W.re 0 with hre | hre | hre
  · -- `u = −1`: a negative real factor
    refine ⟨-1, ?_⟩
    have key : (W * ((1 + (-1 : ℂ) * a) * (1 + conj (-1 : ℂ) * b))).re =
        W.re * ((1 - a) * (1 - b)) := by
      simp only [map_neg, map_one, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [key]
    exact mul_pos_of_neg_of_neg hre (mul_neg_of_neg_of_pos (by linarith) (by linarith))
  · -- `Re W = 0`: a factor `2 ± i(a − b)`
    have him : W.im ≠ 0 := fun h => hW (Complex.ext hre h)
    rcases lt_or_gt_of_ne him with h | h
    · refine ⟨I, ?_⟩
      have key : (W * ((1 + I * a) * (1 + conj I * b))).re =
          W.re * (1 + a * b) - W.im * (a - b) := by
        simp only [Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [key, hre]
      nlinarith
    · refine ⟨-I, ?_⟩
      have key : (W * ((1 + -I * a) * (1 + conj (-I) * b))).re =
          W.re * (1 + a * b) + W.im * (a - b) := by
        simp only [map_neg, Complex.conj_I, neg_neg, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.neg_re,
          Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [key, hre]
      nlinarith
  · refine ⟨0, ?_⟩
    simp only [zero_mul, add_zero, map_zero, mul_one]
    exact hre

/-! ### 2. Growth along even exponents -/

/-- **Real eigenvalues.** If `c_m/b^m → W` with `Re W > 0` and `b` real, then `Re c_m > C R^m` for
some `m`, for every `C` and `0 ≤ R < |b|`: along even `m`, `b^m = |b|^m`. -/
theorem exists_lt_re_of_real {c : ℕ → ℂ} {b W : ℂ} (hb0 : b ≠ 0)
    (hc : Tendsto (fun m => c m / b ^ m) atTop (𝓝 W)) (hW : 0 < W.re)
    (hb2 : (b / (‖b‖ : ℂ)) ^ 2 = 1) {R : ℝ} (hR : 0 ≤ R) (hRb : R < ‖b‖) (C : ℝ) :
    ∃ m : ℕ, C * R ^ m < (c m).re := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hbc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hbn.ne'
  -- along even exponents
  have h2k : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun n => ⟨n, fun a ha => by omega⟩
  have hc2 : Tendsto (fun k : ℕ => c (2 * k) / b ^ (2 * k)) atTop (𝓝 W) := hc.comp h2k
  have hre : ∀ᶠ k : ℕ in atTop, W.re / 2 < (c (2 * k) / b ^ (2 * k)).re :=
    ((Complex.continuous_re.tendsto _).comp hc2).eventually (lt_mem_nhds (by linarith))
  have ht : Tendsto (fun k : ℕ => C * ((R / ‖b‖) ^ 2) ^ k) atTop (𝓝 0) := by
    have h0 : 0 ≤ (R / ‖b‖) ^ 2 := by positivity
    have h1 : (R / ‖b‖) ^ 2 < 1 := by
      rw [sq_lt_one_iff₀ (div_nonneg hR hbn.le)]
      exact (div_lt_one hbn).mpr hRb
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul C
  have hev : ∀ᶠ k : ℕ in atTop, C * ((R / ‖b‖) ^ 2) ^ k < W.re / 2 :=
    ht.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k, h1, h2⟩ := (hre.and hev).exists
  refine ⟨2 * k, ?_⟩
  have hbpow : b ^ (2 * k) = ((‖b‖ ^ (2 * k) : ℝ) : ℂ) := by
    have e : b = (‖b‖ : ℂ) * (b / (‖b‖ : ℂ)) := by field_simp
    conv_lhs => rw [e]
    rw [mul_pow, pow_mul (b / (‖b‖ : ℂ)), hb2, one_pow, mul_one, Complex.ofReal_pow]
  have hbm : 0 < ‖b‖ ^ (2 * k) := pow_pos hbn _
  have hcm : (c (2 * k)).re = ‖b‖ ^ (2 * k) * (c (2 * k) / b ^ (2 * k)).re := by
    rw [hbpow, div_ofReal_re, mul_div_cancel₀ _ hbm.ne']
  rw [hcm]
  have h3 : C * R ^ (2 * k) = ‖b‖ ^ (2 * k) * (C * ((R / ‖b‖) ^ 2) ^ k) := by
    rw [← pow_mul, div_pow, mul_comm (‖b‖ ^ (2 * k)), mul_assoc,
      div_mul_cancel₀ _ (pow_ne_zero _ hbn.ne')]
  rw [h3]
  exact mul_lt_mul_of_pos_left (h2.trans h1) hbm

/-! ### 3. One prime -/

/-- **One test breaks a one-sided bound at one scale.** For a deep-sparse configuration, a right
zero `ρ`, a scale `ℓ > 0` and a sign `ε = ±1`, one test has `ε Re c_m > C R^m` for some `m`, for
every `C` and `0 ≤ R < |β_ρ|`. -/
theorem deepSparse_exists_test_oneSided (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ρ : ℂ} (hρ : ρ ∈ rightZeros Z) {ℓ : ℝ} (hℓ : 0 < ℓ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ C R : ℝ, 0 ≤ R →
      R < ‖frobEig ℓ ρ‖ → ∃ m : ℕ, C * R ^ m < ε * (towerMoment Z g ℓ m).re := by
  set δ : ℝ := ρ.re - 1 / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith [hρ.2]
  have hσ : 1 / 2 < 1 / 2 + δ / 2 := by linarith
  obtain ⟨g, hg, hgc, hkill, hkeep⟩ :=
    exists_test_killing_deep_zeros Z hsp hσ {ρ} fun τ hτ => by
      rw [Set.mem_singleton_iff.mp hτ]; exact hρ
  set b := frobEig ℓ ρ with hb
  have hb0 : b ≠ 0 := frobEig_ne_zero ℓ ρ
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hrb : Real.exp (ℓ * (δ / 2)) < ‖b‖ := by
    rw [hb, norm_frobEig, Real.exp_lt_exp, ← hδdef]
    exact mul_lt_mul_of_pos_left (half_lt_self hδ) hℓ
  -- every zero killed by `g` stays killed; the asymptotics hold for every test whose transform is
  -- a multiple of that of `g`
  have hsepOf : ∀ G : ℝ → ℂ, ContDiff ℝ 2 G → HasCompactSupport G →
      (∀ τ : Z.carrier, paperFT G (gammaOf τ) ≠ 0 → paperFT g (gammaOf τ) ≠ 0) →
      Tendsto (fun m : ℕ => towerMoment Z G ℓ m / b ^ m) atTop (𝓝 (frobWeight Z G ℓ b)) := by
    intro G hG hGc hGg
    refine tendsto_towerMoment_div_pow Z hZ hG hGc hℓ hb0 (Real.exp_pos _).le hrb
      fun τ hτb hw => ?_
    have hX : paperFT G (gammaOf τ) ≠ 0 := fun h0 => hw (by simp [zeroCoord, h0])
    rw [norm_frobEig, Real.exp_le_exp]
    refine mul_le_mul_of_nonneg_left ?_ hℓ.le
    by_contra hlt
    push Not at hlt
    have hτr : (τ : ℂ) ∈ rightZeros Z := ⟨τ.2, by linarith⟩
    have hτρ : (τ : ℂ) ≠ ρ := fun h => hτb (by rw [h])
    exact hGg τ hX (hkill τ hτr (by linarith) hτρ).1
  -- the weight at `b` is the single term of `ρ`
  have hsingle : ∀ G : ℝ → ℂ,
      (∀ τ : Z.carrier, paperFT G (gammaOf τ) ≠ 0 → paperFT g (gammaOf τ) ≠ 0) →
      frobWeight Z G ℓ b = zeroCoord Z G ⟨ρ, hρ.1⟩ *
        conj (zeroCoord Z G (reflectCarrier Z ⟨ρ, hρ.1⟩)) := by
    intro G hGg
    rw [frobWeight, tsum_eq_single ⟨ρ, hρ.1⟩ fun τ hτ => ?_, if_pos rfl]
    split_ifs with he
    · have hre : (τ : ℂ).re = ρ.re := re_eq_of_norm_frobEig_eq hℓ (congrArg norm he)
      have hτρ : (τ : ℂ) ≠ ρ := fun h => hτ (Subtype.ext h)
      have h0 := (hkill τ ⟨τ.2, by rw [hre]; exact hρ.2⟩ (by rw [hre]; linarith) hτρ).1
      have hG0 : paperFT G (gammaOf τ) = 0 := by
        by_contra hne
        exact hGg τ hne h0
      simp [zeroCoord, hG0]
    · rfl
  have hW : frobWeight Z g ℓ b ≠ 0 := by
    refine frobWeight_ne_zero_of_single Z hρ rfl (hkeep ρ (Set.mem_singleton ρ))
      fun τ hτ hne he => ?_
    have hre : τ.re = ρ.re := re_eq_of_norm_frobEig_eq hℓ (congrArg norm he)
    exact (hkill τ ⟨hτ, by rw [hre]; exact hρ.2⟩ (by rw [hre]; linarith) hne).1
  by_cases hphase : (b / (‖b‖ : ℂ)) ^ 2 = 1
  · -- a real eigenvalue: rotate the weight
    obtain ⟨u, hu⟩ := exists_rotation_re_pos (mul_ne_zero hε0 hW) hδ
    set G := twoTermTest g (u * cexp (-(I * ρ.im))) 1 with hGdef
    have hG := twoTermTest_contDiff hg (u * cexp (-(I * ρ.im))) 1
    have hGc := twoTermTest_hasCompactSupport hgc (u * cexp (-(I * ρ.im))) 1
    have hGg : ∀ τ : Z.carrier, paperFT G (gammaOf τ) ≠ 0 → paperFT g (gammaOf τ) ≠ 0 :=
      fun τ hne h0 => hne (by rw [hGdef, paperFT_twoTermTest hg.continuous hgc, h0, mul_zero])
    have hWG : frobWeight Z G ℓ b =
        frobWeight Z g ℓ b * ((1 + u * Real.exp δ) * (1 + conj u * Real.exp (-δ))) := by
      rw [hsingle G hGg, hsingle g fun τ h => h, hGdef, weight_twoTermTest Z hg.continuous hgc]
      congr 1
      exact rotation_factor ρ u
    refine ⟨G, hG, hGc, fun C R hR hRb => ?_⟩
    have hlim : Tendsto (fun m : ℕ => (ε : ℂ) * towerMoment Z G ℓ m / b ^ m) atTop
        (𝓝 ((ε : ℂ) * frobWeight Z G ℓ b)) := by
      simpa only [mul_div_assoc] using (hsepOf G hG hGc hGg).const_mul (ε : ℂ)
    have hpos : 0 < ((ε : ℂ) * frobWeight Z G ℓ b).re := by rw [hWG, ← mul_assoc]; exact hu
    obtain ⟨m, hm⟩ := exists_lt_re_of_real hb0 hlim hpos hphase hR hRb C
    exact ⟨m, by rwa [Complex.re_ofReal_mul] at hm⟩
  · -- a non-real eigenvalue: its phase rotates
    refine ⟨g, hg, hgc, fun C R hR hRb => ?_⟩
    have hlim : Tendsto (fun m : ℕ => (ε : ℂ) * towerMoment Z g ℓ m / b ^ m) atTop
        (𝓝 ((ε : ℂ) * frobWeight Z g ℓ b)) := by
      simpa only [mul_div_assoc] using (hsepOf g hg hgc fun τ h => h).const_mul (ε : ℂ)
    obtain ⟨m, hm⟩ := exists_lt_re_of_tendsto_div_pow hb0 hlim (mul_ne_zero hε0 hW) hphase hR
      hRb C
    exact ⟨m, by rwa [Complex.re_ofReal_mul] at hm⟩

/-- **The one-sided law at one scale.** For a deep-sparse configuration, `ℓ > 0`, a sign `ε = ±1`
and `R ≥ 1`: every test has `ε Re c_m = O(R^m)` iff every outer eigenvalue has modulus at most
`R`. -/
theorem deepSparse_oneSided_iff (Z : ZeroConfig) (hZ : TemperedConfig Z) (hsp : DeepSparse Z)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {R : ℝ} (hR : 1 ≤ R) :
    (∀ ρ ∈ rightZeros Z, ‖frobEig ℓ ρ‖ ≤ R) ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
      HasCompactSupport g → ∃ C, ∀ m : ℕ, ε * (towerMoment Z g ℓ m).re ≤ C * R ^ m := by
  constructor
  · intro hdom g hg hgc
    obtain ⟨C, hC⟩ := exists_norm_towerMoment_le Z hZ hg hgc hℓ hR hdom
    refine ⟨C, fun m => le_trans ?_ (hC m)⟩
    have h := Complex.abs_re_le_norm (towerMoment Z g ℓ m)
    rcases hε with rfl | rfl
    · rw [one_mul]; exact (le_abs_self _).trans h
    · rw [neg_one_mul]; exact (neg_le_abs _).trans h
  · intro h ρ hρ
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hg, hgc, hgrow⟩ := deepSparse_exists_test_oneSided Z hZ hsp hρ hℓ hε
    obtain ⟨C, hC⟩ := h g hg hgc
    obtain ⟨m, hm⟩ := hgrow C R (by linarith) hlt
    exact absurd (hC m) (not_le.mpr hm)

/-- **One-sided Lefschetz bounds at one prime are the zero-free strip.** For a prime `p`, a sign
`ε = ±1` and `θ ≥ 0`: the zero width of `ζ` is at most `θ` iff every test satisfies
`ε Re W(T_{p^m} g, g) = O(p^{θm})`. -/
theorem zeta_width_le_iff_oneSided_onePrime {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    zetaZeroWidth ≤ θ ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g →
      ∃ C, ∀ m : ℕ, ε * (towerMoment zetaZeroConfig g (Real.log p) m).re ≤
        C * ((p : ℝ) ^ θ) ^ m := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hR : 1 ≤ (p : ℝ) ^ θ := Real.one_le_rpow hp1 hθ
  rw [← deepSparse_oneSided_iff _ temperedConfig_zetaZeroConfig deepSparse_zeta
    (Real.log_pos (by exact_mod_cast hp.one_lt)) hε hR, zeta_forall_norm_frobEig_le_iff hp hR]
  constructor
  · exact fun hw => Real.rpow_le_rpow_of_exponent_le hp1 hw
  · intro h
    by_contra hlt
    push Not at hlt
    have hp1' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact absurd h (not_le.mpr (Real.rpow_lt_rpow_of_exponent_lt hp1' hlt))

/-- **One-sided Weil inequalities at one prime decide RH.** For a prime `p` and a sign `ε = ±1`: RH
holds iff every test satisfies `ε Re W(T_{p^m} g, g) ≤ W(g, g)` for all `m`. -/
theorem zeta_riemannHypothesis_iff_oneSided_onePrime {p : ℕ} (hp : p.Prime) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ m : ℕ,
      ε * (towerMoment zetaZeroConfig g (Real.log p) m).re ≤
        (towerMoment zetaZeroConfig g (Real.log p) 0).re := by
  constructor
  · intro hRH g hg hgc m
    have h := abs_re_towerMoment_le_of_riemannHypothesis hRH hg hgc (Real.log p) m
    rcases hε with rfl | rfl
    · rw [one_mul]; exact (le_abs_self _).trans h
    · rw [neg_one_mul]; exact (neg_le_abs _).trans h
  · intro h
    have hw : zetaZeroWidth ≤ 0 := (zeta_width_le_iff_oneSided_onePrime hp hε le_rfl).mpr
      fun g hg hgc => ⟨(towerMoment zetaZeroConfig g (Real.log p) 0).re, fun m => by
        rw [Real.rpow_zero, one_pow, mul_one]; exact h g hg hgc m⟩
    rw [← rightZeros_zeta_eq_empty_iff]
    refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => ?_
    have := (le_abs_self _).trans (abs_re_sub_half_le_zetaZeroWidth hρ.1)
    linarith [hρ.2]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
