import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest

/-!
# Families of `Ξ`-divisible tests with a jointly prime-blind autocorrelation

Let `F_j` (`j ∈ ℕ`) be real `C²` tests with `|F_j|, |F_j'| ≤ C_j e^{−(1/2+δ)|x|}` for a common
`δ > 0` (`DecayBound`), and let `w_j ≥ 0` be weights with `Σ_j w_j C_j² < ∞`.  Suppose

* every `F̂_j` vanishes at the spectral point of every nontrivial zero of `ζ`;
* the weighted autocorrelation is prime-blind: `Σ_j w_j (F_j ⋆ F̃_j)(log n) = 0` for every `n ≥ 2`;
* for some `j₀` with `w_{j₀} > 0`, the real zeros of `F̂_{j₀}` are ordinates of zeros of `ζ`.

**Theorem** (`eq_vonMangoldt_of_xiDivisibleBlindFamily`).  Every full-cone Weil-positive system is
`Λ` on `n ≥ 2`, and RH is equivalent to prime-blind positivity
(`riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindFamily`).

No single member needs to be blind: only the positive combination of the autocorrelations is.  So the
(N1) premise of route HF only asks for a positive-definite blind spectral density
`Σ_j w_j |F̂_j|²` assembled from `Ξ`-divisible pieces, with no spectral factorization of the density.

**Proof.**  For the truncations `F_{j,L}` the spectral representation gives
`∫ |F̂_{j,L}|² dμ_lam = Re W_ζ(F_{j,L}) − T_{lam−Λ}(F_{j,L} ⋆ F̃_{j,L})`.  Both terms are bounded by
constant multiples of `C_j²`, uniformly in `L` (`abs_re_W_truncTest_le`,
`abs_atomPairing_truncTest_le`).  So the weighted sums converge by dominated convergence:
* the zeta sides tend to `0` because every `F̂_j` vanishes at the zeros;
* the prime sides tend to `Σ_j w_j A(F_j)`, where `A` is the Abel form of the prime pairing; this sum
  vanishes by joint blindness after exchanging the two summations (`tsum_mul_abelPrimePairing_eq_zero`).

Fatou's lemma, applied in `L` and in `j`, gives `Σ_j w_j ∫ |F̂_j|² dμ_lam = 0`.  The member `j₀` then
confines `μ_lam` to the critical zeros, and the critical-zero rigidity gives `lam = Λ`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- `F` is `C²` and `|F|, |F'| ≤ C e^{−(1/2+δ)|x|}`. -/
def DecayBound (F : ℝ → ℝ) (δ C : ℝ) : Prop :=
  ContDiff ℝ 2 F ∧ 0 ≤ C ∧ ∀ x : ℝ,
    |F x| ≤ C * Real.exp (-((1 / 2 + δ) * |x|)) ∧ |deriv F x| ≤ C * Real.exp (-((1 / 2 + δ) * |x|))

theorem DecayBound.expDecayTest {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C) :
    ExpDecayTest F :=
  ⟨hF.1, δ, C, hδ, hF.2.1, hF.2.2⟩

theorem integrable_exp_neg_mul_abs_fam {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun u : ℝ => Real.exp (-(κ * |u|))) := by
  have h := (RHTower.integrable_exp_neg_abs).comp_mul_left' hκ.ne'
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [abs_mul, abs_of_pos hκ]

/-! ### Uniform bounds in terms of the decay constant -/

theorem tailMajorant_le {F : ℝ → ℝ} {δ C : ℝ} (hF : DecayBound F δ C) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (u : ℝ) : tailMajorant F Λ u ≤ (3 + 4 * Λ) * C * Real.exp (-(δ * |u|)) := by
  obtain ⟨h1, h2⟩ := hF.2.2 u
  have he : Real.exp (-((1 / 2 + δ) * |u|)) * Real.exp (1 / 2 * |u|) =
      Real.exp (-(δ * |u|)) := by
    rw [← Real.exp_add]; ring_nf
  have hE := Real.exp_pos (1 / 2 * |u|)
  have hsum : |F u| + 2 * (|deriv F u| + 2 * Λ * |F u|) ≤
      (3 + 4 * Λ) * (C * Real.exp (-((1 / 2 + δ) * |u|))) := by nlinarith
  unfold tailMajorant
  calc (|F u| + 2 * (|deriv F u| + 2 * Λ * |F u|)) * Real.exp (1 / 2 * |u|) ≤
      (3 + 4 * Λ) * (C * Real.exp (-((1 / 2 + δ) * |u|))) * Real.exp (1 / 2 * |u|) :=
        mul_le_mul_of_nonneg_right hsum hE.le
    _ = (3 + 4 * Λ) * C * Real.exp (-(δ * |u|)) := by rw [← he]; ring

theorem tailBound_le {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (L : ℝ) :
    tailBound F Λ L ≤ (3 + 4 * Λ) * C * ∫ u : ℝ, Real.exp (-(δ * |u|)) := by
  have hint := (integrable_exp_neg_mul_abs_fam hδ).const_mul ((3 + 4 * Λ) * C)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun u =>
    Set.indicator_nonneg (fun v _ => tailMajorant_nonneg F hΛ v) u) hint
    (Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ {u : ℝ | L - 1 ≤ |u|}
  · rw [Set.indicator_of_mem hu]; exact tailMajorant_le hF hΛ u
  · rw [Set.indicator_of_notMem hu]
    have := hF.2.1
    positivity

/-- **The zeta side of a truncation is bounded by `C²`, uniformly in the cutoff.** -/
theorem abs_re_W_truncTest_le {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0)
    (L : ℝ) :
    |(zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re| ≤
      C ^ 2 * ((5 / 4) * zetaInvSqSum *
        ((3 + 4 * Λ) * ∫ u : ℝ, Real.exp (-(δ * |u|))) ^ 2) := by
  have h := (Complex.abs_re_le_norm _).trans
    (norm_W_truncTest_le (hF.expDecayTest hδ) hΛ hΛ0 hzero L)
  have hZ : 0 ≤ zetaInvSqSum := zetaInvSqSum_nonneg
  have ht0 := tailBound_nonneg F hΛ0 L
  have ht := tailBound_le hδ hF hΛ0 L
  refine h.trans ?_
  calc (5 / 4) * zetaInvSqSum * tailBound F Λ L ^ 2 ≤
      (5 / 4) * zetaInvSqSum * ((3 + 4 * Λ) * C * ∫ u : ℝ, Real.exp (-(δ * |u|))) ^ 2 := by
        gcongr
    _ = _ := by ring

/-! ### The prime side -/

/-- `κ(δ, Λ) = (1 + (1 + 2Λ) e^{1/2+δ}) ∫ e^{−δ|t|/2} dt`. -/
def primeIncrementConst (δ Λ : ℝ) : ℝ :=
  (1 + (1 + 2 * Λ) * Real.exp (1 / 2 + δ)) * ∫ t : ℝ, Real.exp (-(δ / 2 * |t|))

theorem primeIncrementConst_nonneg (δ : ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ primeIncrementConst δ Λ := by
  unfold primeIncrementConst
  have : 0 ≤ ∫ t : ℝ, Real.exp (-(δ / 2 * |t|)) := integral_nonneg fun t => (Real.exp_pos _).le
  positivity

/-- **Increments of the truncated prime profile, in terms of `C²`.** -/
theorem abs_primeLogProfile_truncTest_sub_le_sq {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (L : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) n -
        primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) (n + 1)| ≤
      2 * (C ^ 2 * primeIncrementConst δ Λ) *
        Real.exp (-((1 / 2 + δ / 2) * Real.log n)) / (n * Real.sqrt n) := by
  obtain ⟨hF2, hC, hb⟩ := hF
  set C₁ : ℝ := (1 + 2 * Λ) * C with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hb' : ∀ x : ℝ, |truncTestDeriv F L x| ≤ C₁ * Real.exp (-((1 / 2 + δ) * |x|)) := by
    intro x
    have h := abs_truncTestDeriv_le (F := F) hΛ L x
    calc |truncTestDeriv F L x| ≤ |deriv F x| + 2 * Λ * |F x| := h
      _ ≤ C * Real.exp (-((1 / 2 + δ) * |x|)) +
            2 * Λ * (C * Real.exp (-((1 / 2 + δ) * |x|))) := by
          gcongr
          · exact (hb x).2
          · exact (hb x).1
      _ = C₁ * Real.exp (-((1 / 2 + δ) * |x|)) := by rw [hC₁def]; ring
  have h := abs_primeLogProfile_truncTest_sub_le hF2 hδ hC hC₁ (fun x => (hb x).1) L hb' hn
  refine h.trans (le_of_eq ?_)
  unfold primeIncrementConst
  rw [hC₁def]
  ring

/-- `|S| ≤ A(n+1)` and `|Δ| ≤ 2K E_n/(n√n)` give `|S Δ| ≤ 4AK n^{−1−δ/2}`. -/
theorem abs_mul_primeIncrement_le {δ A K S Δ : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) {n : ℕ} (hn : 1 ≤ n)
    (hS : |S| ≤ A * (n + 1))
    (hΔ : |Δ| ≤ 2 * K * Real.exp (-((1 / 2 + δ / 2) * Real.log n)) / (n * Real.sqrt n)) :
    |S * Δ| ≤ 4 * A * K * ((n : ℝ) ^ (1 + δ / 2))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  set E := Real.exp (-((1 / 2 + δ / 2) * Real.log n)) with hE
  have hEp : E / Real.sqrt n = ((n : ℝ) ^ (1 + δ / 2))⁻¹ := by
    rw [hE, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0,
      ← Real.exp_sub, ← Real.exp_neg]
    congr 1
    ring
  have hratio : ((n : ℝ) + 1) / n ≤ 2 := by
    rw [div_le_iff₀ hn0]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [abs_mul]
  calc |S| * |Δ| ≤ (A * (n + 1)) * (2 * K * E / (n * Real.sqrt n)) :=
        mul_le_mul hS hΔ (abs_nonneg _) (by positivity)
    _ = 2 * A * K * (((n : ℝ) + 1) / n) * (E / Real.sqrt n) := by field_simp
    _ ≤ 2 * A * K * 2 * (E / Real.sqrt n) := by gcongr
    _ = 4 * A * K * ((n : ℝ) ^ (1 + δ / 2))⁻¹ := by rw [hEp]; ring

theorem summable_rpow_inv_prime {δ : ℝ} (hδ : 0 < δ) :
    Summable fun n : ℕ => ((n : ℝ) ^ (1 + δ / 2))⁻¹ :=
  Real.summable_nat_rpow_inv.mpr (by linarith)

theorem nonneg_of_primeWeightPartialSum_bound {w : ℕ → ℝ} {A : ℝ}
    (hA : ∀ N : ℕ, |primeWeightPartialSum w N| ≤ A * (N + 1)) : 0 ≤ A := by
  have := hA 0
  rw [primeWeightPartialSum_eq_zero w (by norm_num)] at this
  simpa using this

/-- The prime-side constant `4 A κ(δ, Λ) Σ_n n^{−1−δ/2}`. -/
def primeSideConst (δ Λ A : ℝ) : ℝ :=
  4 * A * primeIncrementConst δ Λ * ∑' n : ℕ, ((n : ℝ) ^ (1 + δ / 2))⁻¹

/-- **The prime pairing of a truncation is bounded by `C²`, uniformly in the cutoff.** -/
theorem abs_atomPairing_truncTest_le {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) {w : ℕ → ℝ}
    {A : ℝ} (hA : ∀ N : ℕ, |primeWeightPartialSum w N| ≤ A * (N + 1)) (L : ℝ) :
    |atomPairing w (crossCorr (truncTest F L) (truncTest F L))| ≤ C ^ 2 * primeSideConst δ Λ A := by
  have hA0 := nonneg_of_primeWeightPartialSum_bound hA
  have hκ := primeIncrementConst_nonneg δ hΛ0
  have hK : 0 ≤ C ^ 2 * primeIncrementConst δ Λ := by positivity
  have hrewrite : atomPairing w (crossCorr (truncTest F L) (truncTest F L)) =
      ∑' n : ℕ, primeWeightPartialSum w n *
        (primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) n -
          primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) (n + 1)) := by
    refine atomPairing_eq_tsum_primeWeightPartialSum w _ (N := ⌈Real.exp (2 * L)⌉₊) fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
      exact_mod_cast this
    have hlog : 2 * L < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hn0]
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by
      have : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le _) hn
      exact_mod_cast this)
    unfold primeLogProfile
    rw [crossCorr_truncTest_eq_zero F (by rw [abs_of_nonneg hl0]; linarith),
      crossCorr_truncTest_eq_zero F (by rw [abs_neg, abs_of_nonneg hl0]; linarith)]
    simp
  set T : ℕ → ℝ := fun n => primeWeightPartialSum w n *
      (primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) n -
        primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) (n + 1)) with hT
  set B : ℕ → ℝ := fun n =>
    4 * A * (C ^ 2 * primeIncrementConst δ Λ) * ((n : ℝ) ^ (1 + δ / 2))⁻¹ with hB
  have hterm : ∀ n : ℕ, ‖T n‖ ≤ B n := by
    intro n
    rw [Real.norm_eq_abs]
    rcases lt_or_ge n 2 with hn | hn
    · simp only [hT, hB]
      rw [primeWeightPartialSum_eq_zero w hn, zero_mul, abs_zero]; positivity
    · exact abs_mul_primeIncrement_le hA0 hK (by omega) (hA n)
        (abs_primeLogProfile_truncTest_sub_le_sq hδ hF hΛ0 hΛ L (by omega))
  have hsumm : Summable B := (summable_rpow_inv_prime hδ).mul_left _
  have hs2 : Summable fun n => ‖T n‖ := (hsumm.of_norm_bounded hterm).norm
  rw [hrewrite, ← Real.norm_eq_abs]
  calc ‖∑' n, T n‖ ≤ ∑' n, ‖T n‖ := norm_tsum_le_tsum_norm hs2
    _ ≤ ∑' n, B n := Summable.tsum_le_tsum hterm hs2 hsumm
    _ = C ^ 2 * primeSideConst δ Λ A := by
        simp only [hB]
        rw [tsum_mul_left, primeSideConst]
        ring

/-! ### Untruncated bounds -/

theorem abs_crossCorr_le_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C)
    (y : ℝ) :
    |crossCorr F F y| ≤
      C ^ 2 * (∫ t : ℝ, Real.exp (-(δ / 2 * |t|))) * Real.exp (-((1 / 2 + δ / 2) * |y|)) :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp
    (tendsto_crossCorr_truncTest (hF.expDecayTest hδ) y))
    fun L => abs_crossCorr_truncTest_le hδ hF.2.1 (fun x => (hF.2.2 x).1) L y

theorem tendsto_primeLogProfile_truncTest {F : ℝ → ℝ} (hF : ExpDecayTest F) (m : ℕ) :
    Tendsto (fun L : ℝ => primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) m) atTop
      (𝓝 (primeLogProfile (crossCorr F F) m)) :=
  ((tendsto_crossCorr_truncTest hF (Real.log m)).add
    (tendsto_crossCorr_truncTest hF (-Real.log m))).div_const _

theorem abs_primeLogProfile_sub_le_sq {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) {n : ℕ} (hn : 1 ≤ n) :
    |primeLogProfile (crossCorr F F) n - primeLogProfile (crossCorr F F) (n + 1)| ≤
      2 * (C ^ 2 * primeIncrementConst δ Λ) *
        Real.exp (-((1 / 2 + δ / 2) * Real.log n)) / (n * Real.sqrt n) :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp
    ((tendsto_primeLogProfile_truncTest (hF.expDecayTest hδ) n).sub
      (tendsto_primeLogProfile_truncTest (hF.expDecayTest hδ) (n + 1))))
    fun L => abs_primeLogProfile_truncTest_sub_le_sq hδ hF hΛ0 hΛ L hn

theorem abs_primeLogProfile_le {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C)
    (m : ℕ) :
    |primeLogProfile (crossCorr F F) m| ≤ 2 * (C ^ 2 * ∫ t : ℝ, Real.exp (-(δ / 2 * |t|))) := by
  have hI : 0 ≤ ∫ t : ℝ, Real.exp (-(δ / 2 * |t|)) := integral_nonneg fun t => (Real.exp_pos _).le
  have hb : ∀ y : ℝ, |crossCorr F F y| ≤ C ^ 2 * ∫ t : ℝ, Real.exp (-(δ / 2 * |t|)) := by
    intro y
    refine (abs_crossCorr_le_of_decayBound hδ hF y).trans ?_
    have : Real.exp (-((1 / 2 + δ / 2) * |y|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg y])
    have h0 : 0 ≤ C ^ 2 * ∫ t : ℝ, Real.exp (-(δ / 2 * |t|)) := by positivity
    nlinarith
  unfold primeLogProfile
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, abs_zero]
    have := hb 0
    positivity
  · have hs : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr (by exact_mod_cast hm)
    rw [abs_div, abs_of_pos (a := Real.sqrt m) (by linarith)]
    calc |crossCorr F F (Real.log m) + crossCorr F F (-Real.log m)| / Real.sqrt m ≤
        |crossCorr F F (Real.log m) + crossCorr F F (-Real.log m)| :=
          div_le_self (abs_nonneg _) hs
      _ ≤ |crossCorr F F (Real.log m)| + |crossCorr F F (-Real.log m)| := abs_add_le _ _
      _ ≤ _ := by linarith [hb (Real.log m), hb (-Real.log m)]

/-! ### Joint blindness kills the Abel prime pairings -/

/-- **The weighted Abel prime pairings vanish under joint blindness.** -/
theorem tsum_mul_abelPrimePairing_eq_zero {F : ℕ → ℝ → ℝ} {w C : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ j, DecayBound (F j) δ (C j)) (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * C j ^ 2) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) {v : ℕ → ℝ} {A : ℝ}
    (hA : ∀ N : ℕ, |primeWeightPartialSum v N| ≤ A * (N + 1))
    (hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0) :
    ∑' j, w j * abelPrimePairing v (F j) = 0 := by
  have hA0 := nonneg_of_primeWeightPartialSum_bound hA
  have hκ := primeIncrementConst_nonneg δ hΛ0
  set I₁ := ∫ t : ℝ, Real.exp (-(δ / 2 * |t|)) with hI₁
  have hI : 0 ≤ I₁ := integral_nonneg fun t => (Real.exp_pos _).le
  set ψ : ℕ → ℕ → ℝ := fun j m => primeLogProfile (crossCorr (F j) (F j)) m with hψ
  set g : ℕ → ℕ → ℝ := fun j n =>
    w j * (primeWeightPartialSum v n * (ψ j n - ψ j (n + 1))) with hg
  have hgb : ∀ j n, ‖g j n‖ ≤
      (w j * C j ^ 2) * (4 * A * primeIncrementConst δ Λ * ((n : ℝ) ^ (1 + δ / 2))⁻¹) := by
    intro j n
    rw [Real.norm_eq_abs]
    simp only [hg]
    rw [abs_mul, abs_of_nonneg (hw j)]
    rcases lt_or_ge n 2 with hn | hn
    · rw [primeWeightPartialSum_eq_zero v hn, zero_mul, abs_zero, mul_zero]
      have := hw j
      positivity
    · have hK : 0 ≤ C j ^ 2 * primeIncrementConst δ Λ := by positivity
      have h := abs_mul_primeIncrement_le hA0 hK (by omega) (hA n)
        (abs_primeLogProfile_sub_le_sq hδ (hF j) hΛ0 hΛ (by omega))
      calc w j * |primeWeightPartialSum v n * (ψ j n - ψ j (n + 1))| ≤
          w j * (4 * A * (C j ^ 2 * primeIncrementConst δ Λ) * ((n : ℝ) ^ (1 + δ / 2))⁻¹) :=
            mul_le_mul_of_nonneg_left h (hw j)
        _ = _ := by ring
  have hnn : 0 ≤ fun j => w j * C j ^ 2 := fun j => mul_nonneg (hw j) (sq_nonneg _)
  have hsumB : Summable fun p : ℕ × ℕ =>
      (w p.1 * C p.1 ^ 2) * (4 * A * primeIncrementConst δ Λ * ((p.2 : ℝ) ^ (1 + δ / 2))⁻¹) :=
    hsum.mul_of_nonneg ((summable_rpow_inv_prime hδ).mul_left _) hnn
      (fun n => by have : (0 : ℝ) ≤ ((n : ℝ) ^ (1 + δ / 2))⁻¹ := by positivity
                   simp only [Pi.zero_apply]; positivity)
  have hsg : Summable (Function.uncurry g) :=
    hsumB.of_norm_bounded fun p => hgb p.1 p.2
  have hL : ∑' j, w j * abelPrimePairing v (F j) = ∑' j, ∑' n, g j n := by
    refine tsum_congr fun j => ?_
    unfold abelPrimePairing
    rw [← tsum_mul_left]
  rw [hL, ← hsg.tsum_comm]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases lt_or_ge n 2 with hn | hn
  · refine (tsum_congr fun j => ?_).trans tsum_zero
    simp only [hg]
    rw [primeWeightPartialSum_eq_zero v hn, zero_mul, mul_zero]
  · have hprof0 : ∀ m : ℕ, 2 ≤ m → ∑' j, w j * ψ j m = 0 := by
      intro m hm
      have e : ∀ j, w j * ψ j m = 2 / Real.sqrt m * (w j * crossCorr (F j) (F j) (Real.log m)) := by
        intro j
        simp only [hψ, primeLogProfile]
        rw [crossCorr_self_neg]
        ring
      simp_rw [e]
      rw [tsum_mul_left, hblind m hm, mul_zero]
    have hsψ : ∀ m : ℕ, Summable fun j => w j * ψ j m := by
      intro m
      refine (hsum.mul_right (2 * I₁)).of_norm_bounded fun j => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
      calc w j * |ψ j m| ≤ w j * (2 * (C j ^ 2 * I₁)) :=
            mul_le_mul_of_nonneg_left (abs_primeLogProfile_le hδ (hF j) m) (hw j)
        _ = w j * C j ^ 2 * (2 * I₁) := by ring
    have e : ∀ j, g j n = primeWeightPartialSum v n * (w j * ψ j n) -
        primeWeightPartialSum v n * (w j * ψ j (n + 1)) := fun j => by simp only [hg]; ring
    simp_rw [e]
    rw [Summable.tsum_sub ((hsψ n).mul_left _) ((hsψ (n + 1)).mul_left _), tsum_mul_left,
      tsum_mul_left, hprof0 n hn, hprof0 (n + 1) (by omega), mul_zero, sub_zero]

/-! ### Assembly -/

/-- The zeta-side constant `(5/4) Σ|ρ|^{−2} ((3 + 4Λ) ∫ e^{−δ|u|})²`. -/
def zetaSideConst (δ Λ : ℝ) : ℝ :=
  (5 / 4) * zetaInvSqSum * ((3 + 4 * Λ) * ∫ u : ℝ, Real.exp (-(δ * |u|))) ^ 2

/-- **The weighted zeta sides of the truncations tend to `0`.** -/
theorem tendsto_tsum_W_truncTest {F : ℕ → ℝ → ℝ} {w C : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ j, DecayBound (F j) δ (C j)) (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * C j ^ 2) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hzero : ∀ j, ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F j u : ℂ)) (gammaOf ρ) = 0) :
    Tendsto (fun L : ℝ => ∑' j, w j * (zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
      (fun u => (truncTest (F j) L u : ℂ))).re) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (hsum.mul_right (zetaSideConst δ Λ))
    (f := fun L j => w j * (zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
      (fun u => (truncTest (F j) L u : ℂ))).re) (g := fun _ => 0)
    (fun j => ?_) (Eventually.of_forall fun L j => ?_)
  · simpa using h
  · have hb : Tendsto (fun L => (5 / 4) * zetaInvSqSum * tailBound (F j) Λ L ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_tailBound ((hF j).expDecayTest hδ) hΛ0).pow 2).const_mul
        ((5 / 4) * zetaInvSqSum)
    have hj : Tendsto (fun L : ℝ => (zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
        (fun u => (truncTest (F j) L u : ℂ))).re) atTop (𝓝 0) :=
      squeeze_zero_norm (fun L => (Complex.abs_re_le_norm _).trans
        (norm_W_truncTest_le ((hF j).expDecayTest hδ) hΛ hΛ0 (hzero j) L)) hb
    simpa using hj.const_mul (w j)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
    calc w j * |(zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
          (fun u => (truncTest (F j) L u : ℂ))).re| ≤ w j * (C j ^ 2 * zetaSideConst δ Λ) :=
          mul_le_mul_of_nonneg_left (abs_re_W_truncTest_le hδ (hF j) hΛ hΛ0 (hzero j) L) (hw j)
      _ = w j * C j ^ 2 * zetaSideConst δ Λ := by ring

/-- **The weighted prime sides of the truncations tend to `0` under joint blindness.** -/
theorem tendsto_tsum_atomPairing_truncTest {F : ℕ → ℝ → ℝ} {w C : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ j, DecayBound (F j) δ (C j)) (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * C j ^ 2) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) {v : ℕ → ℝ} {A : ℝ}
    (hA : ∀ N : ℕ, |primeWeightPartialSum v N| ≤ A * (N + 1))
    (hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0) :
    Tendsto (fun L : ℝ => ∑' j, w j *
      atomPairing v (crossCorr (truncTest (F j) L) (truncTest (F j) L))) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (hsum.mul_right (primeSideConst δ Λ A))
    (f := fun L j => w j * atomPairing v (crossCorr (truncTest (F j) L) (truncTest (F j) L)))
    (g := fun j => w j * abelPrimePairing v (F j))
    (fun j => (tendsto_atomPairing_truncTest_abelPrimePairing ((hF j).expDecayTest hδ) hA).const_mul
      (w j)) (Eventually.of_forall fun L j => ?_)
  · rwa [tsum_mul_abelPrimePairing_eq_zero hδ hF hw hsum hΛ0 hΛ hA hblind] at h
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
    calc w j * |atomPairing v (crossCorr (truncTest (F j) L) (truncTest (F j) L))| ≤
        w j * (C j ^ 2 * primeSideConst δ Λ A) :=
          mul_le_mul_of_nonneg_left (abs_atomPairing_truncTest_le hδ (hF j) hΛ0 hΛ hA L) (hw j)
      _ = w j * C j ^ 2 * primeSideConst δ Λ A := by ring

/-- **The weighted spectral energies of a jointly blind `Ξ`-divisible family vanish.** -/
theorem tsum_lintegral_specDensity_eq_zero_of_family {F : ℕ → ℝ → ℝ} {w C : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hF : ∀ j, DecayBound (F j) δ (C j)) (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * C j ^ 2)
    (hzero : ∀ j, ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F j u : ℂ)) (gammaOf ρ) = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∑' j, ENNReal.ofReal (w j) *
      ∫⁻ r, (specDensity (fun u => (F j u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW = 0 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨A, hA⟩ := exists_abs_primeWeightPartialSum_sub_vonMangoldt_le hW
  set μ := boundaryMeasure hW
  set a : ℕ → ℝ → ℝ≥0∞ := fun j L =>
    ∫⁻ r, (specDensity (fun u => (truncTest (F j) L u : ℂ)) r : ℝ≥0∞) ∂μ with ha
  have hrep := fun j L => toReal_lintegral_specDensity_truncTest_eq (hF j).1 hW L
  set ω := zetaSideConst δ Λ
  set β := primeSideConst δ Λ A
  -- the real energies
  have hbd : ∀ j L, |w j * (a j L).toReal| ≤ w j * C j ^ 2 * (ω + β) := by
    intro j L
    rw [abs_mul, abs_of_nonneg (hw j), (hrep j L).2]
    have h1 := abs_re_W_truncTest_le hδ (hF j) hΛ hΛ0 (hzero j) L
    have h2 := abs_atomPairing_truncTest_le hδ (hF j) hΛ0 hΛ hA L
    calc w j * |(zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
          (fun u => (truncTest (F j) L u : ℂ))).re -
          atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
            (crossCorr (truncTest (F j) L) (truncTest (F j) L))| ≤
        w j * (C j ^ 2 * ω + C j ^ 2 * β) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (hw j)
      _ = w j * C j ^ 2 * (ω + β) := by ring
  have hsumE : ∀ L, Summable fun j => w j * (a j L).toReal := fun L =>
    (hsum.mul_right (ω + β)).of_norm_bounded fun j => by rw [Real.norm_eq_abs]; exact hbd j L
  have hsumW : ∀ L : ℝ, Summable fun j => w j * (zetaZeroConfig.W
      (fun u => (truncTest (F j) L u : ℂ)) (fun u => (truncTest (F j) L u : ℂ))).re := fun L =>
    (hsum.mul_right ω).of_norm_bounded fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
      calc w j * |(zetaZeroConfig.W (fun u => (truncTest (F j) L u : ℂ))
            (fun u => (truncTest (F j) L u : ℂ))).re| ≤ w j * (C j ^ 2 * ω) :=
            mul_le_mul_of_nonneg_left (abs_re_W_truncTest_le hδ (hF j) hΛ hΛ0 (hzero j) L) (hw j)
        _ = w j * C j ^ 2 * ω := by ring
  have hsumP : ∀ L : ℝ, Summable fun j => w j * atomPairing
      (fun n => lam n - ArithmeticFunction.vonMangoldt n)
      (crossCorr (truncTest (F j) L) (truncTest (F j) L)) := fun L =>
    (hsum.mul_right β).of_norm_bounded fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
      calc w j * |atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
            (crossCorr (truncTest (F j) L) (truncTest (F j) L))| ≤ w j * (C j ^ 2 * β) :=
            mul_le_mul_of_nonneg_left (abs_atomPairing_truncTest_le hδ (hF j) hΛ0 hΛ hA L) (hw j)
        _ = w j * C j ^ 2 * β := by ring
  have hreal : Tendsto (fun L : ℝ => ∑' j, w j * (a j L).toReal) atTop (𝓝 0) := by
    have h := (tendsto_tsum_W_truncTest hδ hF hw hsum hΛ0 hΛ hzero).sub
      (tendsto_tsum_atomPairing_truncTest hδ hF hw hsum hΛ0 hΛ hA hblind)
    rw [sub_zero] at h
    refine h.congr fun L => ?_
    rw [← Summable.tsum_sub (hsumW L) (hsumP L)]
    refine tsum_congr fun j => ?_
    rw [(hrep j L).2]
    ring
  -- the energies in `ℝ≥0∞`
  have hE : ∀ L, ∑' j, ENNReal.ofReal (w j) * a j L =
      ENNReal.ofReal (∑' j, w j * (a j L).toReal) := by
    intro L
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (hw j) ENNReal.toReal_nonneg)
      (hsumE L)]
    refine tsum_congr fun j => ?_
    rw [ENNReal.ofReal_mul (hw j), ENNReal.ofReal_toReal (hrep j L).1.ne]
  have hlim : Tendsto (fun k : ℕ => ∑' j, ENNReal.ofReal (w j) * a j (k : ℝ)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (hreal.comp tendsto_natCast_atTop_atTop)
    rw [ENNReal.ofReal_zero] at h
    exact h.congr fun k => (hE k).symm
  -- Fatou in the cutoff, for each member
  have hmeas : ∀ j (k : ℕ), Measurable fun r =>
      (specDensity (fun u => (truncTest (F j) (k : ℝ) u : ℂ)) r : ℝ≥0∞) := fun j k =>
    (measurable_specDensity
      ((contDiff_ofReal_truncTest (hF j).1 _).continuous.integrable_of_hasCompactSupport
        ((hasCompactSupport_truncTest (F j) _).comp_left Complex.ofReal_zero))).coe_nnreal_ennreal
  have hpt : ∀ j (r : ℝ), Tendsto (fun k : ℕ =>
      (specDensity (fun u => (truncTest (F j) (k : ℝ) u : ℂ)) r : ℝ≥0∞)) atTop
      (𝓝 (specDensity (fun u => (F j u : ℂ)) r : ℝ≥0∞)) := by
    intro j r
    have hz : |((r : ℂ)).im| ≤ 1 / 2 := by simp
    have h := (tendsto_paperFT_truncTest ((hF j).expDecayTest hδ) hz).comp
      tendsto_natCast_atTop_atTop
    have hc : Continuous fun z : ℂ => ((‖z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.continuous_coe.comp (continuous_nnnorm.pow 2)
    exact (hc.tendsto _).comp h
  have hfatou_j : ∀ j, ENNReal.ofReal (w j) *
      ∫⁻ r, (specDensity (fun u => (F j u : ℂ)) r : ℝ≥0∞) ∂μ ≤
      liminf (fun k : ℕ => ENNReal.ofReal (w j) * a j (k : ℝ)) atTop := by
    intro j
    have hm : ∀ k : ℕ, Measurable fun r => ENNReal.ofReal (w j) *
        (specDensity (fun u => (truncTest (F j) (k : ℝ) u : ℂ)) r : ℝ≥0∞) := fun k =>
      (hmeas j k).const_mul _
    have hf := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hm
    have hpt' : ∀ r, liminf (fun k : ℕ => ENNReal.ofReal (w j) *
        (specDensity (fun u => (truncTest (F j) (k : ℝ) u : ℂ)) r : ℝ≥0∞)) atTop =
        ENNReal.ofReal (w j) * (specDensity (fun u => (F j u : ℂ)) r : ℝ≥0∞) := fun r =>
      (ENNReal.Tendsto.const_mul (hpt j r) (Or.inr ENNReal.ofReal_ne_top)).liminf_eq
    simp_rw [hpt'] at hf
    have hmF : Measurable fun r => (specDensity (fun u => (F j u : ℂ)) r : ℝ≥0∞) := by
      have hint : Integrable fun u => (F j u : ℂ) := by
        have hi := (integrable_exp_neg_mul_abs_fam (κ := 1 / 2 + δ) (by positivity)).const_mul
          (C j)
        refine hi.mono' (Complex.continuous_ofReal.comp (hF j).1.continuous).aestronglyMeasurable
          (Eventually.of_forall fun u => ?_)
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact ((hF j).2.2 u).1
      exact (measurable_specDensity hint).coe_nnreal_ennreal
    rw [lintegral_const_mul _ hmF] at hf
    refine hf.trans (le_of_eq ?_)
    congr 1
    funext k
    rw [lintegral_const_mul _ (hmeas j k)]
  -- Fatou in the index
  have hfatou : ∑' j, liminf (fun k : ℕ => ENNReal.ofReal (w j) * a j (k : ℝ)) atTop ≤
      liminf (fun k : ℕ => ∑' j, ENNReal.ofReal (w j) * a j (k : ℝ)) atTop := by
    have h := lintegral_liminf_le (μ := (Measure.count : Measure ℕ)) (u := (atTop : Filter ℕ))
      (f := fun (k : ℕ) (j : ℕ) => ENNReal.ofReal (w j) * a j (k : ℝ))
      (fun _ => measurable_from_top)
    simpa only [lintegral_count] using h
  have hzero_lim : liminf (fun k : ℕ => ∑' j, ENNReal.ofReal (w j) * a j (k : ℝ)) atTop = 0 :=
    hlim.liminf_eq
  exact le_antisymm ((ENNReal.tsum_le_tsum hfatou_j).trans (hfatou.trans hzero_lim.le)) (zero_le)

/-- **A jointly blind `Ξ`-divisible family confines the boundary measure to the critical zeros.** -/
theorem boundaryMeasure_zeta_ne_zero_of_xiDivisibleBlindFamily {F : ℕ → ℝ → ℝ} {w C : ℕ → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hF : ∀ j, DecayBound (F j) δ (C j)) (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * C j ^ 2)
    (hzero : ∀ j, ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F j u : ℂ)) (gammaOf ρ) = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0)
    {j₀ : ℕ} (hj₀ : 0 < w j₀)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F j₀ u : ℂ)) r = 0 →
      riemannZeta ((1 / 2 : ℂ) + r * I) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    boundaryMeasure hW {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0 := by
  have h0 := tsum_lintegral_specDensity_eq_zero_of_family hδ hF hw hsum hzero hblind hW
  have hj := ENNReal.tsum_eq_zero.mp h0 j₀
  have hw0 : ENNReal.ofReal (w j₀) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hj₀
  have hj' := (mul_eq_zero.mp hj).resolve_left hw0
  have hFint : Integrable fun u => (F j₀ u : ℂ) := by
    have hi := (integrable_exp_neg_mul_abs_fam (κ := 1 / 2 + δ) (by positivity)).const_mul (C j₀)
    refine hi.mono' (Complex.continuous_ofReal.comp (hF j₀).1.continuous).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ((hF j₀).2.2 u).1
  rw [lintegral_eq_zero_iff (measurable_specDensity hFint).coe_nnreal_ennreal] at hj'
  have hnull : boundaryMeasure hW
      {r : ℝ | (specDensity (fun u => (F j₀ u : ℂ)) r : ℝ≥0∞) ≠ 0} = 0 := ae_iff.mp hj'
  refine measure_mono_null (fun r hr => ?_) hnull
  simp only [Set.mem_setOf_eq] at hr ⊢
  intro hs
  apply hr
  apply hreal
  simpa [specDensity] using hs

/-- **Rigidity from a jointly blind `Ξ`-divisible family.** -/
theorem eq_vonMangoldt_of_xiDivisibleBlindFamily {F : ℕ → ℝ → ℝ} {w C : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hF : ∀ j, DecayBound (F j) δ (C j)) (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * C j ^ 2)
    (hzero : ∀ j, ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F j u : ℂ)) (gammaOf ρ) = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0)
    {j₀ : ℕ} (hj₀ : 0 < w j₀)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F j₀ u : ℂ)) r = 0 →
      riemannZeta ((1 / 2 : ℂ) + r * I) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  eq_vonMangoldt_of_boundaryMeasure_criticalZeros hW
    (boundaryMeasure_zeta_ne_zero_of_xiDivisibleBlindFamily hδ hF hw hsum hzero hblind hj₀ hreal hW)

/-- **Given a jointly blind `Ξ`-divisible family, RH is prime-blind positivity.** -/
theorem riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindFamily {F : ℕ → ℝ → ℝ}
    {w C : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hF : ∀ j, DecayBound (F j) δ (C j)) (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable fun j => w j * C j ^ 2)
    (hzero : ∀ j, ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F j u : ℂ)) (gammaOf ρ) = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (F j) (F j) (Real.log n) = 0)
    {j₀ : ℕ} (hj₀ : 0 < w j₀)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F j₀ u : ℂ)) r = 0 →
      riemannZeta ((1 / 2 : ℂ) + r * I) = 0) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive :=
  ⟨fun hRH => WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mp
      ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH⟩,
    fun hP => by
      obtain ⟨lam, hW⟩ := WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mpr hP
      exact riemannHypothesis_of_boundaryMeasure_criticalZeros hW
        (boundaryMeasure_zeta_ne_zero_of_xiDivisibleBlindFamily hδ hF hw hsum hzero hblind hj₀
          hreal hW)⟩

end RHTower.WeilSpectral
