import GaloisForLFunctions.RHTower.EvenSectorSechRepresentation
import GaloisForLFunctions.RHTower.TwistedArcNullLaplacePositivity
import GaloisForLFunctions.RHTower.XiWideStripDecay
import GaloisForLFunctions.RHTower.WeilPrimeBlindZeroSideIdentity
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound

/-!
# The twisted-arc null family kills the imaginary spectrum

Let `lam` be Weil-positive at pole weight `1` on all even compactly supported tests, so that
`|lam_n| ≤ C √n (1 + log n)` (`exists_abs_le_of_weilPositiveEvenAt`), and let `ν_S` be the
cosine-shift measure of `S(z) = sech(z/2)`.  For a twisted-arc probability measure (twisted
minimum principle) put `w_j = arcGammaWeight m_j j` and `Φ_j = Ξ Q_j` (`xiShiftedGamma`).

**Null identity** (`tsum_mul_evenWeilDensity_xiShiftedGamma_eq_zero`).
`Σ_j w_j L(Φ_j Φ_j^#) = 0`.  The pole and archimedean energy of `F_j = stripTest Φ_j` is its Abel
prime pairing with `Λ`, because `F̂_j` vanishes at every zero of `ζ`; these vanish jointly
(`tsum_mul_abelPrimePairing_eq_zero`).  The prime part vanishes by joint blindness after exchanging
the sums, which converge absolutely: `Φ_j` decays uniformly on `|Im z| ≤ 5/4`
(`exists_stripDecay_xiShiftedGamma_wide`), so the `n`-th prime term is `O(j!² (9/4)^j n^{−5/4})`.

**Theorem** (`measure_sq_le_two_eq_zero`).  `ν_S({ρ : ρ² ≤ 2}) = 0`.

Proof.  `L(Φ_j Φ_j^#) = ∫ g_j dν_S` with `g_j = Re T̃_j`, `T_j = Φ_j Φ_j^# cosh²(z/2)`
(`evenWeilDensity_specSq_eq_integral_sechHalf`).  Where `ρ² > 2`, `g_j ≥ 0`.  Where `ρ² ≤ 2`, with
`y = (2 − ρ²)^{1/2}`, `g_j(ρ) = Ξ(iy)² p_j(y) cos²(y/2)`, `p_j(y) = Π_k ((k + ¼)² − y²/4)`.  Here
`|p_j| ≤ (j!)²` and `Σ_j w_j p_j(y) ≥ √2 m₀ > 0` for `|y| ≤ 3/2`
(`sqrt_two_mul_le_tsum_arcGammaWeight_mul_prod`), and `Ξ(iy) > 0`.  So
`0 = Σ_j w_j ∫ g_j ≥ ∫_{ρ² ≤ 2} Σ_j w_j g_j dν_S`, with a strictly positive integrand.

**Corollary** (`evenWeilDensity_specSq_nonneg_of_multiplier_sechWeight`).  For every `Ψ` such
that `Ψ Ψ^# cosh²(z/2)` is a multiplier, `L(Ψ Ψ^#) ≥ 0`.  No parity is required of `Ψ`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry

/-! ## Uniform strip decay of `Ξ Q_j` on `|Im z| ≤ 5/4` -/

theorem exists_stripDecay_xiShiftedGamma_wide :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      StripDecay (xiShiftedGamma j) (5 / 4) xiShiftedGammaRate
        (C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) := by
  have hpi : 2 * (3 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
  obtain ⟨CΞ, hCΞ, hΞ⟩ := RHTower.exists_norm_XiC_horizontal_le_wide (A := 5 / 4) (δ := 3 / 4)
    (by norm_num) (by norm_num) hpi
  refine ⟨3 * CΞ, by positivity, fun j => ⟨fun z _ => ?_, fun z hz => ?_⟩⟩
  · unfold xiShiftedGamma shiftedGammaPoly
    exact (RHTower.XiC_differentiable z).mul (by fun_prop)
  · have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have hX : ‖RHTower.XiC z‖ ≤ CΞ * Real.exp (-(3 / 4 * |z.re|)) := by
      have := hΞ z.re z.im hz
      rwa [← hz'] at this
    have hQ := norm_shiftedGammaPoly_le_factorial j (z := z) (by linarith)
    unfold xiShiftedGamma
    rw [norm_mul]
    calc ‖RHTower.XiC z‖ * ‖shiftedGammaPoly j z‖ ≤
        (CΞ * Real.exp (-(3 / 4 * |z.re|))) *
          (3 * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (Real.log 3 / 2 * |z.re|)) :=
          mul_le_mul hX hQ (norm_nonneg _) (by positivity)
      _ = 3 * CΞ * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) *
            (Real.exp (-(3 / 4 * |z.re|)) * Real.exp (Real.log 3 / 2 * |z.re|)) := by ring
      _ = 3 * CΞ * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) *
            Real.exp (-(xiShiftedGammaRate * |z.re|)) := by
          rw [← Real.exp_add]; unfold xiShiftedGammaRate; ring_nf

/-- `Φ_j(−z) = conj Φ_j(z̄)` on the whole plane. -/
theorem xiShiftedGamma_neg_conj (j : ℕ) (z : ℂ) :
    xiShiftedGamma j (-z) = conj (xiShiftedGamma j (conj z)) := by
  unfold xiShiftedGamma shiftedGammaPoly
  rw [map_mul, map_prod, RHTower.XiC_even, RHTower.XiC_conj, Complex.conj_conj]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [map_add, map_natCast, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I,
    Complex.conj_conj]
  ring

theorem specSq_neg_of_neg_conj {Φ : ℂ → ℂ} (h : ∀ z, Φ (-z) = conj (Φ (conj z))) (z : ℂ) :
    specSq Φ (-z) = specSq Φ z := by
  unfold specSq
  rw [h z, map_neg, h (conj z), Complex.conj_conj, Complex.conj_conj, mul_comm]

theorem goodDensity_specSq_of_neg_conj {Φ : ℂ → ℂ} {ε C : ℝ} (hε : 0 < ε)
    (hΦ : StripDecay Φ (5 / 4) ε C) (h : ∀ z, Φ (-z) = conj (Φ (conj z))) :
    GoodDensity (specSq Φ) :=
  ⟨⟨2 * ε, C ^ 2, by linarith, fun z hz => differentiableAt_specSq hΦ hz,
    fun z hz => norm_specSq_le hΦ hz⟩, specSq_neg_of_neg_conj h, fun r => specSq_im_ofReal r⟩


/-! ## The null identity -/

/-- The even functional of a spectral square, as pole and archimedean energy minus prime part. -/
theorem evenWeilDensity_specSq_eq_sub {lam : ℕ → ℝ} {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 1 / 2 < b)
    (hε : 0 < ε) (hΦ : StripDecay Φ b ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) :
    evenWeilDensity lam (specSq Φ) =
      archPoleEnergy (stripTest Φ) - evenPrimePart lam (specSq Φ) := by
  rw [archPoleEnergy_stripTest hb hε hΦ hsym]
  unfold evenWeilDensity evenPrimePart
  simp_rw [specSq_re_ofReal]

theorem integrable_exp_neg_mul_abs_gammaBracket {a : ℝ} (ha : 0 < a) :
    Integrable fun r : ℝ => Real.exp (-(a * |r|)) * |EF.gammaBracket r| := by
  have hi := (integrable_exp_neg_rate_abs (half_pos ha)).const_mul
    ((|gammaLogConst| + 2) * (1 + 2 / a))
  refine hi.mono' ((by fun_prop : Continuous fun r : ℝ => Real.exp (-(a * |r|))).mul
    (continuous_abs.comp WeilHerglotz.continuous_gammaBracket)).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_abs_gammaBracket_le_linear r
  rw [abs_abs] at h1
  have h2 := mul_exp_neg_le (t := |r|) ha
  have he : Real.exp (-(a * |r|)) ≤ Real.exp (-(a / 2 * |r|)) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg r])
  have hM : 0 ≤ |gammaLogConst| + 2 := by positivity
  calc Real.exp (-(a * |r|)) * |EF.gammaBracket r|
      ≤ Real.exp (-(a * |r|)) * ((|gammaLogConst| + 2) * (1 + |r|)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (|gammaLogConst| + 2) * (Real.exp (-(a * |r|)) + |r| * Real.exp (-(a * |r|))) := by ring
    _ ≤ (|gammaLogConst| + 2) * (Real.exp (-(a / 2 * |r|)) + 2 / a * Real.exp (-(a / 2 * |r|))) :=
        by gcongr
    _ = _ := by ring

/-- The pole and archimedean energy of a strip test is `O(C²)`. -/
theorem abs_archPoleEnergy_stripTest_le {Φ : ℂ → ℂ} {ε C : ℝ} (hε : 0 < ε)
    (hΦ : StripDecay Φ (5 / 4) ε C) (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) :
    |archPoleEnergy (stripTest Φ)| ≤ C ^ 2 * (2 + 1 / (2 * Real.pi) *
      ∫ r : ℝ, Real.exp (-(2 * ε * |r|)) * |EF.gammaBracket r|) := by
  rw [archPoleEnergy_stripTest (by norm_num) hε hΦ hsym]
  have h1 : ‖specSq Φ (I / 2)‖ ≤ C ^ 2 := by
    have := norm_specSq_le hΦ (z := I / 2) (by norm_num)
    simpa using this
  have h2 : ‖specSq Φ (-I / 2)‖ ≤ C ^ 2 := by
    have := norm_specSq_le hΦ (z := -I / 2) (by norm_num)
    simpa using this
  have hint := integrable_exp_neg_mul_abs_gammaBracket (a := 2 * ε) (by linarith)
  have h3 : |∫ r : ℝ, ‖Φ r‖ ^ 2 * EF.gammaBracket r| ≤
      C ^ 2 * ∫ r : ℝ, Real.exp (-(2 * ε * |r|)) * |EF.gammaBracket r| := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have := norm_specSq_le hΦ (z := r) (by norm_num)
    rw [specSq] at this
    simpa [Complex.conj_ofReal, norm_mul, sq] using this
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have hre : |(specSq Φ (I / 2) + specSq Φ (-I / 2)).re| ≤ 2 * C ^ 2 :=
    (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by linarith))
  calc |(specSq Φ (I / 2) + specSq Φ (-I / 2)).re +
        1 / (2 * Real.pi) * ∫ r : ℝ, ‖Φ r‖ ^ 2 * EF.gammaBracket r|
      ≤ |(specSq Φ (I / 2) + specSq Φ (-I / 2)).re| +
        1 / (2 * Real.pi) * |∫ r : ℝ, ‖Φ r‖ ^ 2 * EF.gammaBracket r| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_pos hpi]
    _ ≤ 2 * C ^ 2 + 1 / (2 * Real.pi) *
        (C ^ 2 * ∫ r : ℝ, Real.exp (-(2 * ε * |r|)) * |EF.gammaBracket r|) := by gcongr
    _ = _ := by ring

/-- The `n`-th prime term of a spectral square is `O(C² n^{−5/4})`. -/
theorem abs_primeTerm_specSq_le {Φ : ℂ → ℂ} {ε C : ℝ} (hε : 0 < ε)
    (hΦ : StripDecay Φ (5 / 4) ε C) (h : ∀ z, Φ (-z) = conj (Φ (conj z))) {n : ℕ} (hn : 1 ≤ n) :
    |1 / Real.pi * ∫ r : ℝ, (specSq Φ r).re * Real.cos (r * Real.log n)| ≤
      C ^ 2 * (2 * ((∫ r : ℝ, Real.exp (-(2 * ε * |r|))) / (2 * Real.pi))) *
        (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have hs : StripDecay (specSq Φ) (5 / 4) (2 * ε) (C ^ 2) :=
    ⟨fun z hz => differentiableAt_specSq hΦ hz, fun z hz => norm_specSq_le hΦ hz⟩
  refine (abs_prime_le_of_strip (by linarith) hs (goodDensity_specSq_of_neg_conj hε hΦ h)
    hn).trans (le_of_eq ?_)
  ring

theorem abs_evenPrimePart_specSq_le {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    {ε C : ℝ} (hε : 0 < ε) (hΦ : StripDecay Φ (5 / 4) ε C)
    (h : ∀ z, Φ (-z) = conj (Φ (conj z))) (n : ℕ) :
    |(if 2 ≤ n then lam n / Real.sqrt n else 0) *
      (1 / Real.pi * ∫ r : ℝ, (specSq Φ r).re * Real.cos (r * Real.log n))| ≤
      C ^ 2 * (Cg * (2 * ((∫ r : ℝ, Real.exp (-(2 * ε * |r|))) / (2 * Real.pi))) *
        ((1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ)))) := by
  have hCg := growthConst_nonneg hg
  have hI : 0 ≤ ∫ r : ℝ, Real.exp (-(2 * ε * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [abs_mul]
  calc |(if 2 ≤ n then lam n / Real.sqrt n else 0)| *
        |1 / Real.pi * ∫ r : ℝ, (specSq Φ r).re * Real.cos (r * Real.log n)|
      ≤ (Cg * (1 + Real.log n)) * (C ^ 2 * (2 * ((∫ r : ℝ, Real.exp (-(2 * ε * |r|))) /
          (2 * Real.pi))) * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
        mul_le_mul (abs_weight_le hg n) (abs_primeTerm_specSq_le hε hΦ h hn) (abs_nonneg _)
          (by have := Real.log_natCast_nonneg n; positivity)
    _ = _ := by ring

/-- **The null identity of the twisted-arc family.** -/
theorem tsum_mul_evenWeilDensity_xiShiftedGamma_eq_zero {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2)
    (hblind : ∀ n : ℕ, 2 ≤ n →
      ∑' j, w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n) = 0) :
    Summable (fun j => w j * evenWeilDensity lam (specSq (xiShiftedGamma j))) ∧
      ∑' j, w j * evenWeilDensity lam (specSq (xiShiftedGamma j)) = 0 := by
  obtain ⟨C, hC, hs⟩ := exists_stripDecay_xiShiftedGamma_wide
  have hε := xiShiftedGammaRate_pos
  set ε := xiShiftedGammaRate
  set c : ℕ → ℝ := fun j => C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) with hc
  have hcsum : Summable fun j => w j * c j ^ 2 :=
    (hsum.mul_left (C ^ 2)).congr fun j => by simp only [hc]; ring
  have hsym := xiShiftedGamma_neg_ofReal
  have hcj := xiShiftedGamma_neg_conj
  -- the archimedean and pole energies
  set Iγ := ∫ r : ℝ, Real.exp (-(2 * ε * |r|)) * |EF.gammaBracket r|
  have hA : Summable fun j => w j * archPoleEnergy (stripTest (xiShiftedGamma j)) := by
    refine Summable.of_norm_bounded (hcsum.mul_right (2 + 1 / (2 * Real.pi) * Iγ)) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j), mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_archPoleEnergy_stripTest_le hε (hs j) (hsym j)) (hw j)
  have hA0 : ∑' j, w j * archPoleEnergy (stripTest (xiShiftedGamma j)) = 0 := by
    obtain ⟨C', hC', hF⟩ := exists_decayBound_xiShiftedGammaTest
    obtain ⟨Λ₀, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
    have hsum' : Summable fun j => w j * (C' * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 :=
      (hsum.mul_left (C' ^ 2)).congr fun j => by ring
    have hblind' : ∀ n : ℕ, 2 ≤ n →
        ∑' j, w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) (Real.log n) = 0 := by
      intro n hn
      simp_rw [crossCorr_xiShiftedGammaTest]
      have e : ∀ j, w j * (1 / (2 * Real.pi) *
          ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) =
          1 / (2 * Real.pi) * (w j *
            ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by ring
      simp_rw [e]
      rw [tsum_mul_left, hblind n hn, mul_zero]
    have hab := tsum_mul_abelPrimePairing_eq_zero (by norm_num : (0 : ℝ) < 1 / 4) hF hw hsum'
      hΛ0 hΛ (fun N => abs_primeWeightPartialSum_vonMangoldt_le N) hblind'
    rw [← hab]
    refine tsum_congr fun j => ?_
    congr 1
    rw [show stripTest (xiShiftedGamma j) = xiShiftedGammaTest j from rfl,
      archPoleEnergy_eq_re_W_add_abelPrimePairing ((hF j).expDecayTest (by norm_num))]
    have hW : zetaZeroConfig.W (fun u => (xiShiftedGammaTest j u : ℂ))
        (fun u => (xiShiftedGammaTest j u : ℂ)) = 0 := by
      unfold Zeta23.ZeroConfig.W Zeta23.ZeroConfig.Wsummand
      simp [paperFT_xiShiftedGammaTest_gammaOf]
    rw [hW, Complex.zero_re, zero_add]
  -- the prime parts
  set D := Cg * (2 * ((∫ r : ℝ, Real.exp (-(2 * ε * |r|))) / (2 * Real.pi))) with hD
  have hCg := growthConst_nonneg hg
  have hD0 : 0 ≤ D := by
    have : 0 ≤ ∫ r : ℝ, Real.exp (-(2 * ε * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
    positivity
  set u : ℕ → ℝ := fun n => (1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ)) with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => by
    have := Real.log_natCast_nonneg n
    have : 0 ≤ (n : ℝ) ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  have husum : Summable u := summable_one_add_log_mul_rpow (b₁ := 5 / 4) (by norm_num)
  set X : ℕ → ℕ → ℝ := fun j n => (if 2 ≤ n then lam n / Real.sqrt n else 0) *
    (1 / Real.pi * ∫ r : ℝ, (specSq (xiShiftedGamma j) r).re * Real.cos (r * Real.log n)) with hX
  have hXb : ∀ j n, |X j n| ≤ c j ^ 2 * (D * u n) := fun j n =>
    abs_evenPrimePart_specSq_le hg hε (hs j) (hcj j) n
  have hjoint : Summable (Function.uncurry fun j n => w j * X j n) := by
    refine Summable.of_norm_bounded ((hcsum.mul_of_nonneg (husum.mul_left D)
      (fun j => mul_nonneg (hw j) (sq_nonneg _)) (fun n => mul_nonneg hD0 (hu0 n)))) fun p => ?_
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw p.1)]
    have := hXb p.1 p.2
    calc w p.1 * |X p.1 p.2| ≤ w p.1 * (c p.1 ^ 2 * (D * u p.2)) :=
          mul_le_mul_of_nonneg_left this (hw p.1)
      _ = w p.1 * c p.1 ^ 2 * (D * u p.2) := by ring
  have hrow : ∀ j, Summable fun n => X j n := fun j =>
    Summable.of_norm_bounded (husum.mul_left (c j ^ 2 * D)) fun n => by
      rw [Real.norm_eq_abs]; refine (hXb j n).trans (le_of_eq ?_); ring
  have hP : Summable fun j => w j * evenPrimePart lam (specSq (xiShiftedGamma j)) := by
    refine Summable.of_norm_bounded (hcsum.mul_right (D * ∑' n, u n)) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hw j)
    unfold evenPrimePart
    calc |∑' n, X j n| ≤ ∑' n, |X j n| := by
          rw [← Real.norm_eq_abs]
          refine (norm_tsum_le_tsum_norm (hrow j).norm).trans (le_of_eq ?_)
          simp [Real.norm_eq_abs]
      _ ≤ ∑' n, c j ^ 2 * (D * u n) :=
          (hrow j).abs.tsum_le_tsum (hXb j) ((husum.mul_left D).mul_left _)
      _ = c j ^ 2 * (D * ∑' n, u n) := by rw [tsum_mul_left, tsum_mul_left]
  have hP0 : ∑' j, w j * evenPrimePart lam (specSq (xiShiftedGamma j)) = 0 := by
    have e1 : ∀ j, w j * evenPrimePart lam (specSq (xiShiftedGamma j)) =
        ∑' n, w j * X j n := fun j => by
      unfold evenPrimePart; rw [tsum_mul_left]
    simp_rw [e1]
    rw [← hjoint.tsum_comm]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases lt_or_ge n 2 with hn | hn
    · refine (tsum_congr fun j => ?_).trans tsum_zero
      simp [hX, show ¬ 2 ≤ n by omega]
    · have e2 : ∀ j, w j * X j n = (lam n / Real.sqrt n) * (1 / Real.pi) *
          (w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by
        simp only [hX, if_pos hn]
        simp_rw [specSq_re_ofReal]
        ring
      simp_rw [e2]
      rw [tsum_mul_left, hblind n hn, mul_zero]
  have e : ∀ j, w j * evenWeilDensity lam (specSq (xiShiftedGamma j)) =
      w j * archPoleEnergy (stripTest (xiShiftedGamma j)) -
        w j * evenPrimePart lam (specSq (xiShiftedGamma j)) := fun j => by
    rw [evenWeilDensity_specSq_eq_sub (by norm_num) hε (hs j) (hsym j)]; ring
  simp_rw [e]
  exact ⟨hA.sub hP, by rw [hA.tsum_sub hP, hA0, hP0, sub_zero]⟩


/-! ## The weights `Φ_j Φ_j^# cosh²(z/2)` are multipliers -/

theorem real_cosh_le_exp_abs (u : ℝ) : Real.cosh u ≤ Real.exp |u| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp u ≤ Real.exp |u| := Real.exp_le_exp.mpr (le_abs_self u)
  have h2 : Real.exp (-u) ≤ Real.exp |u| := Real.exp_le_exp.mpr (neg_le_abs u)
  linarith

theorem norm_cosh_half_sq_le (z : ℂ) : ‖Complex.cosh (z / 2) ^ 2‖ ≤ Real.exp |z.re| := by
  rw [norm_pow]
  have h := norm_cosh_le_real_cosh_re (z / 2)
  have hre : (z / 2).re = z.re / 2 := by simp
  rw [hre] at h
  have hc := (h.trans (real_cosh_le_exp_abs (z.re / 2)))
  calc ‖Complex.cosh (z / 2)‖ ^ 2 ≤ Real.exp |z.re / 2| ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hc 2
    _ = Real.exp |z.re| := by
        rw [← Real.exp_nat_mul, abs_div, abs_two]; push_cast; ring_nf

/-- `Ψ Ψ^# cosh²(z/2)` is a multiplier once `Ψ` decays faster than `e^{−|Re z|/2}` on
`|Im z| ≤ 9/4` and `Ψ Ψ^#` is even. -/
theorem multiplier_sechWeight {Ψ : ℂ → ℂ} {ε C : ℝ} (hε : 1 / 2 < ε)
    (hΨ : StripDecay Ψ (9 / 4) ε C) (heven : ∀ z, specSq Ψ (-z) = specSq Ψ z) :
    Multiplier (sechWeight Ψ) := by
  refine ⟨⟨2 * ε - 1, C ^ 2, by linarith, fun z hz => ?_, fun z hz => ?_⟩, fun z => ?_,
    fun z => ?_⟩
  · exact (differentiableAt_specSq hΨ hz).mul
      ((Complex.differentiable_cosh.differentiableAt.comp z
        (differentiableAt_id.div_const 2)).pow 2)
  · unfold sechWeight
    rw [norm_mul]
    calc ‖specSq Ψ z‖ * ‖Complex.cosh (z / 2) ^ 2‖
        ≤ (C ^ 2 * Real.exp (-(2 * ε * |z.re|))) * Real.exp |z.re| :=
          mul_le_mul (norm_specSq_le hΨ hz) (norm_cosh_half_sq_le z) (norm_nonneg _)
            (by positivity)
      _ = C ^ 2 * Real.exp (-((2 * ε - 1) * |z.re|)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  · unfold sechWeight; rw [heven, neg_div, Complex.cosh_neg]
  · unfold sechWeight specSq
    rw [Complex.conj_conj, map_mul, map_mul, map_pow, Complex.conj_conj,
      show conj z / 2 = conj (z / 2) by rw [map_div₀, map_ofNat], Complex.cosh_conj]
    ring

theorem norm_shiftedGammaPoly_factor_le_wide (k : ℕ) {z : ℂ} (hz : |z.im| ≤ 9 / 4) :
    ‖(k : ℂ) + 1 / 4 + I * z / 2‖ ≤ (k : ℝ) + 2 + |z.re| / 2 := by
  have e : (k : ℂ) + 1 / 4 + I * z / 2 =
      (((k : ℝ) + 1 / 4 - z.im / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.mul_re]; ring
    · simp [Complex.mul_im]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_two]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : |(k : ℝ) + 1 / 4 - z.im / 2| ≤ (k : ℝ) + 2 := by
    rw [abs_le]; constructor <;> linarith [abs_le.mp hz |>.1, abs_le.mp hz |>.2]
  linarith

theorem norm_shiftedGammaPoly_le_wide (j : ℕ) {z : ℂ} (hz : |z.im| ≤ 9 / 4) :
    ‖shiftedGammaPoly j z‖ ≤
      16 ^ j * (j ! : ℝ) * Real.exp (((j : ℝ) + 2) / 16) * Real.exp (|z.re| / 32) := by
  have hprod : ‖shiftedGammaPoly j z‖ ≤ ((j : ℝ) + 2 + |z.re| / 2) ^ j := by
    unfold shiftedGammaPoly
    rw [norm_prod]
    calc ∏ k ∈ Finset.range j, ‖(k : ℂ) + 1 / 4 + I * z / 2‖
        ≤ ∏ _k ∈ Finset.range j, ((j : ℝ) + 2 + |z.re| / 2) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k hk => by
            have hkj : (k : ℝ) ≤ j := by exact_mod_cast (Finset.mem_range.mp hk).le
            exact (norm_shiftedGammaPoly_factor_le_wide k hz).trans (by linarith)
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  have h0 : 0 ≤ ((j : ℝ) + 2 + |z.re| / 2) / 16 := by positivity
  have hexp := Real.pow_div_factorial_le_exp _ h0 j
  rw [div_le_iff₀ (by positivity)] at hexp
  refine hprod.trans ?_
  calc ((j : ℝ) + 2 + |z.re| / 2) ^ j = 16 ^ j * (((j : ℝ) + 2 + |z.re| / 2) / 16) ^ j := by
        rw [div_pow]; field_simp
    _ ≤ 16 ^ j * (Real.exp (((j : ℝ) + 2 + |z.re| / 2) / 16) * (j ! : ℝ)) := by gcongr
    _ = _ := by
        rw [show ((j : ℝ) + 2 + |z.re| / 2) / 16 = ((j : ℝ) + 2) / 16 + |z.re| / 32 by ring,
          Real.exp_add]
        ring

theorem exists_stripDecay_xiShiftedGamma_nine_quarters (j : ℕ) :
    ∃ C : ℝ, StripDecay (xiShiftedGamma j) (9 / 4) (23 / 32) C := by
  have hpi : 2 * (3 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
  obtain ⟨CΞ, hCΞ, hΞ⟩ := RHTower.exists_norm_XiC_horizontal_le_wide (A := 9 / 4) (δ := 3 / 4)
    (by norm_num) (by norm_num) hpi
  refine ⟨CΞ * (16 ^ j * (j ! : ℝ) * Real.exp (((j : ℝ) + 2) / 16)), fun z _ => ?_,
    fun z hz => ?_⟩
  · unfold xiShiftedGamma shiftedGammaPoly
    exact (RHTower.XiC_differentiable z).mul (by fun_prop)
  · have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have hX : ‖RHTower.XiC z‖ ≤ CΞ * Real.exp (-(3 / 4 * |z.re|)) := by
      have := hΞ z.re z.im hz
      rwa [← hz'] at this
    have hQ := norm_shiftedGammaPoly_le_wide j hz
    unfold xiShiftedGamma
    rw [norm_mul]
    calc ‖RHTower.XiC z‖ * ‖shiftedGammaPoly j z‖ ≤
        (CΞ * Real.exp (-(3 / 4 * |z.re|))) * (16 ^ j * (j ! : ℝ) *
          Real.exp (((j : ℝ) + 2) / 16) * Real.exp (|z.re| / 32)) :=
          mul_le_mul hX hQ (norm_nonneg _) (by positivity)
      _ = CΞ * (16 ^ j * (j ! : ℝ) * Real.exp (((j : ℝ) + 2) / 16)) *
            (Real.exp (-(3 / 4 * |z.re|)) * Real.exp (|z.re| / 32)) := by ring
      _ = _ := by rw [← Real.exp_add]; ring_nf

theorem multiplier_sechWeight_xiShiftedGamma (j : ℕ) :
    Multiplier (sechWeight (xiShiftedGamma j)) := by
  obtain ⟨C, hs⟩ := exists_stripDecay_xiShiftedGamma_nine_quarters j
  exact multiplier_sechWeight (by norm_num) hs (specSq_neg_of_neg_conj (xiShiftedGamma_neg_conj j))


/-! ## The weights on the imaginary segment -/

theorem rhoLift_of_sq_le_two {T : ℂ → ℂ} (heven : ∀ z, T (-z) = T z) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 2) :
    rhoLift T ρ = T (I * ((Real.sqrt (2 - ρ ^ 2) : ℝ) : ℂ)) := by
  unfold rhoLift
  have hsq : sqrtPrincipal ((ρ : ℂ) ^ 2 - 2) ^ 2 =
      (I * ((Real.sqrt (2 - ρ ^ 2) : ℝ) : ℂ)) ^ 2 := by
    rw [sqrtPrincipal_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow (Real.sqrt (2 - ρ ^ 2)) 2,
      Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 - ρ ^ 2)]
    push_cast; ring
  rcases sqrtPrincipal_eq_or_neg hsq with h1 | h1
  · rw [h1]
  · rw [h1, heven]

theorem shiftedGammaPoly_neg_I_mul (j : ℕ) (y : ℝ) :
    shiftedGammaPoly j (-(I * y)) =
      ((∏ k ∈ Finset.range j, ((k : ℝ) + 1 / 4 + y / 2) : ℝ) : ℂ) := by
  unfold shiftedGammaPoly
  push_cast
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
  ring

/-- On the imaginary axis, `T_j(iy) = Ξ(iy)² p_j(y) cos²(y/2)`. -/
theorem sechWeight_xiShiftedGamma_I_mul (j : ℕ) (y : ℝ) :
    sechWeight (xiShiftedGamma j) (I * y) =
      ((thetaSourceLaplace y ^ 2 * shiftedGammaLaplaceFactor j y * Real.cos (y / 2) ^ 2 : ℝ) :
        ℂ) := by
  unfold sechWeight specSq xiShiftedGamma
  have hc : conj (I * (y : ℂ)) = -(I * y) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [hc, RHTower.XiC_even, RHTower.XiC_I_mul, shiftedGammaPoly_I_mul, shiftedGammaPoly_neg_I_mul,
    show I * (y : ℂ) / 2 = ((y / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.cosh_mul_I,
    ← Complex.ofReal_cos]
  simp only [map_mul, Complex.conj_ofReal]
  unfold shiftedGammaLaplaceFactor
  rw [Finset.prod_mul_distrib]
  push_cast
  ring

theorem continuous_thetaSourceLaplace : Continuous thetaSourceLaplace := by
  have e : thetaSourceLaplace = fun y : ℝ => (RHTower.XiC (I * y)).re := funext fun y => by
    rw [RHTower.XiC_I_mul, Complex.ofReal_re]
  rw [e]
  exact Complex.continuous_re.comp (RHTower.XiC_differentiable.continuous.comp (by fun_prop))

theorem exists_sq_thetaSourceLaplace_le :
    ∃ M : ℝ, ∀ y : ℝ, |y| ≤ 3 / 2 → thetaSourceLaplace y ^ 2 ≤ M := by
  have hpi : 2 * (3 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
  obtain ⟨CΞ, hCΞ, hΞ⟩ := RHTower.exists_norm_XiC_horizontal_le_wide (A := 3 / 2) (δ := 3 / 4)
    (by norm_num) (by norm_num) hpi
  refine ⟨CΞ ^ 2, fun y hy => ?_⟩
  have h := hΞ 0 y hy
  rw [show ((0 : ℝ) : ℂ) + (y : ℂ) * I = I * y by push_cast; ring, RHTower.XiC_I_mul,
    Complex.norm_real, Real.norm_eq_abs] at h
  simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2


/-! ## The imaginary segment carries no mass -/

/-- The clamp `ρ ↦ max(−√2, min(√2, ρ))`. -/
def clampSqrtTwo (ρ : ℝ) : ℝ := max (-Real.sqrt 2) (min (Real.sqrt 2) ρ)

theorem continuous_clampSqrtTwo : Continuous clampSqrtTwo := by
  unfold clampSqrtTwo; fun_prop

theorem sq_clampSqrtTwo_le (ρ : ℝ) : clampSqrtTwo ρ ^ 2 ≤ 2 := by
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : |clampSqrtTwo ρ| ≤ Real.sqrt 2 := by
    unfold clampSqrtTwo
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  calc clampSqrtTwo ρ ^ 2 = |clampSqrtTwo ρ| ^ 2 := (sq_abs _).symm
    _ ≤ Real.sqrt 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = 2 := hs

theorem clampSqrtTwo_eq {ρ : ℝ} (hρ : ρ ^ 2 ≤ 2) : clampSqrtTwo ρ = ρ := by
  have h := Real.abs_le_sqrt hρ
  rw [abs_le] at h
  unfold clampSqrtTwo
  rw [min_eq_right h.2, max_eq_right h.1]

theorem sqrt_two_sub_sq_clamp_le (ρ : ℝ) : |Real.sqrt (2 - clampSqrtTwo ρ ^ 2)| ≤ 3 / 2 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : Real.sqrt (2 - clampSqrtTwo ρ ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (clampSqrtTwo ρ)])
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- **The twisted-arc null family kills the segment `ρ² ≤ 2`.** -/
theorem measure_sq_le_two_eq_zero {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = (cosineShiftFn lam sechHalf y : ℂ)) :
    ν {ρ : ℝ | ρ ^ 2 ≤ 2} = 0 := by
  -- the twisted-arc weights
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν₀ : Measure ArcParam := (μ : Measure ArcParam) with hν₀
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν₀ (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind0 : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν₀ = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν₀ (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν₀) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  have hblind := shiftedGamma_blind_of_twistedArc (B := 1) measurable_const
    (fun _ => by norm_num) hblind0 hmom
  obtain ⟨hLsum, hL0⟩ := tsum_mul_evenWeilDensity_xiShiftedGamma_eq_zero hg hw hsum hblind
  -- the representation through `ν`
  set g : ℕ → ℝ → ℝ := fun j ρ => (rhoLift (sechWeight (xiShiftedGamma j)) ρ).re with hg_def
  have hrep : ∀ j, evenWeilDensity lam (specSq (xiShiftedGamma j)) = ∫ ρ, g j ρ ∂ν := fun j =>
    evenWeilDensity_specSq_eq_integral_sechHalf hg hν (multiplier_sechWeight_xiShiftedGamma j)
  have hgi : ∀ j, Integrable (g j) ν := by
    intro j
    obtain ⟨ε, C, hε, hs⟩ := stripDecay_rhoLift (multiplier_sechWeight_xiShiftedGamma j)
    have hC := hs.const_nonneg (by norm_num)
    have hc := continuous_ofReal_comp_of_stripDecay hs (by norm_num)
    refine (integrable_const C).mono' (Complex.continuous_re.comp hc).aestronglyMeasurable
      (Eventually.of_forall fun ρ => ?_)
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ((hs.bound ρ (by norm_num)).trans ?_)
    exact mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by
      have := abs_nonneg (ρ : ℂ).re; nlinarith))
  set A := {ρ : ℝ | ρ ^ 2 ≤ 2} with hA_def
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hle : ∀ j, ∫ ρ in A, g j ρ ∂ν ≤ ∫ ρ, g j ρ ∂ν := fun j => by
    rw [← integral_add_compl hA (hgi j)]
    have : 0 ≤ ∫ ρ in Aᶜ, g j ρ ∂ν := setIntegral_nonneg hA.compl fun ρ hρ =>
      re_rhoLift_sechWeight_nonneg _ (by
        simp only [hA_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hρ; linarith)
    linarith
  -- on `A`, the weights in the variable `y`
  set Y : ℝ → ℝ := fun ρ => Real.sqrt (2 - clampSqrtTwo ρ ^ 2) with hY_def
  set G : ℕ → ℝ → ℝ := fun j ρ => thetaSourceLaplace (Y ρ) ^ 2 *
    shiftedGammaLaplaceFactor j (Y ρ) * Real.cos (Y ρ / 2) ^ 2 with hG_def
  have hgG : ∀ j, ∀ ρ ∈ A, g j ρ = G j ρ := by
    intro j ρ hρ
    simp only [hg_def, hG_def, hY_def, clampSqrtTwo_eq hρ]
    rw [rhoLift_of_sq_le_two (multiplier_sechWeight_xiShiftedGamma j).even hρ,
      sechWeight_xiShiftedGamma_I_mul, Complex.ofReal_re]
  obtain ⟨Mθ, hMθ⟩ := exists_sq_thetaSourceLaplace_le
  have hYb := sqrt_two_sub_sq_clamp_le
  have hGb : ∀ j ρ, |G j ρ| ≤ Mθ * (j ! : ℝ) ^ 2 := by
    intro j ρ
    have h1 := hMθ (Y ρ) (hYb ρ)
    have h2 := abs_shiftedGammaLaplaceFactor_le (hYb ρ) j
    have h3 : Real.cos (Y ρ / 2) ^ 2 ≤ 1 := by
      rw [← Real.cos_sq_add_sin_sq (Y ρ / 2)]; nlinarith [sq_nonneg (Real.sin (Y ρ / 2))]
    simp only [hG_def]
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg (Real.cos _))]
    have hM0 : 0 ≤ Mθ := (sq_nonneg _).trans h1
    calc thetaSourceLaplace (Y ρ) ^ 2 * |shiftedGammaLaplaceFactor j (Y ρ)| *
          Real.cos (Y ρ / 2) ^ 2 ≤ Mθ * (j ! : ℝ) ^ 2 * 1 :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hM0) h3 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hYc : Continuous Y := by
    simp only [hY_def]; exact (continuous_const.sub (continuous_clampSqrtTwo.pow 2)).sqrt
  have hGc : ∀ j, Continuous (G j) := fun j => by
    simp only [hG_def, shiftedGammaLaplaceFactor]
    exact ((continuous_thetaSourceLaplace.comp hYc).pow 2).mul
      (continuous_finsetProd _ fun k _ => by fun_prop) |>.mul
      ((Real.continuous_cos.comp (hYc.div_const 2)).pow 2)
  have hwM : Summable fun j => w j * (Mθ * (j ! : ℝ) ^ 2) := by
    have hfac : ∀ j, (j ! : ℝ) ^ 2 ≤ ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 := fun j => by
      have : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hf : (0 : ℝ) ≤ j ! := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left this hf]
    have hM0 : 0 ≤ Mθ := (sq_nonneg _).trans (hMθ 0 (by norm_num))
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hw j) (by positivity))
      (fun j => ?_) (hsum.mul_left Mθ)
    calc w j * (Mθ * (j ! : ℝ) ^ 2) = Mθ * (w j * (j ! : ℝ) ^ 2) := by ring
      _ ≤ Mθ * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hfac j) (hw j)) hM0
  -- the positive combination
  set S : ℝ → ℝ := fun ρ => ∑' j, w j * G j ρ with hS_def
  have hSc : Continuous S := continuous_tsum (fun j => continuous_const.mul (hGc j)) hwM
    (fun j ρ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
      exact mul_le_mul_of_nonneg_left (hGb j ρ) (hw j))
  have hSpos : ∀ ρ, 0 < S ρ := by
    intro ρ
    have e : S ρ = thetaSourceLaplace (Y ρ) ^ 2 * Real.cos (Y ρ / 2) ^ 2 *
        ∑' j, w j * shiftedGammaLaplaceFactor j (Y ρ) := by
      simp only [hS_def, hG_def]
      rw [← tsum_mul_left]
      congr 1; funext j; ring
    rw [e]
    have h1 := sqrt_two_mul_le_tsum_arcGammaWeight_mul_prod ν₀ (hYb ρ)
    have h2 := twArcEvenMoment_one_zero_pos μ
    have h3 := thetaSourceLaplace_pos (Y ρ)
    have h4 := cos_half_pos (y := Y ρ) (by linarith [hYb ρ])
    have h5 : 0 < ∑' j, w j * shiftedGammaLaplaceFactor j (Y ρ) :=
      lt_of_lt_of_le (by positivity) h1
    positivity
  have hSb : ∀ ρ, |S ρ| ≤ ∑' j, w j * (Mθ * (j ! : ℝ) ^ 2) := fun ρ => by
    rw [abs_of_pos (hSpos ρ)]
    refine Summable.tsum_le_tsum (fun j => ?_) ?_ hwM
    · exact (le_abs_self _).trans (by
        rw [abs_mul, abs_of_nonneg (hw j)]; exact mul_le_mul_of_nonneg_left (hGb j ρ) (hw j))
    · exact Summable.of_norm_bounded hwM fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left (hGb j ρ) (hw j)
  -- exchange on `A`
  have hGi : ∀ j, Integrable (fun ρ => w j * G j ρ) (ν.restrict A) := fun j =>
    (integrable_const (w j * (Mθ * (j ! : ℝ) ^ 2))).mono'
      (continuous_const.mul (hGc j)).aestronglyMeasurable (Eventually.of_forall fun ρ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left (hGb j ρ) (hw j))
  have hGn : Summable fun j => ∫ ρ, ‖w j * G j ρ‖ ∂(ν.restrict A) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (hwM.mul_right ((ν.restrict A).real univ))
    calc ∫ ρ, ‖w j * G j ρ‖ ∂(ν.restrict A) ≤ ∫ _ρ, w j * (Mθ * (j ! : ℝ) ^ 2) ∂(ν.restrict A) :=
          integral_mono (hGi j).norm (integrable_const _) fun ρ => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw j)]
            exact mul_le_mul_of_nonneg_left (hGb j ρ) (hw j)
      _ = _ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hex : ∑' j, w j * ∫ ρ in A, g j ρ ∂ν = ∫ ρ in A, S ρ ∂ν := by
    have e : ∀ j, w j * ∫ ρ in A, g j ρ ∂ν = ∫ ρ in A, w j * G j ρ ∂ν := fun j => by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun hA fun ρ hρ => by simp only [hgG j ρ hρ]
    simp_rw [e]
    exact integral_tsum_of_summable_integral_norm hGi hGn
  have hsumA : Summable fun j => w j * ∫ ρ in A, g j ρ ∂ν := by
    have e : ∀ j, w j * ∫ ρ in A, g j ρ ∂ν = ∫ ρ in A, w j * G j ρ ∂ν := fun j => by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun hA fun ρ hρ => by simp only [hgG j ρ hρ]
    simp_rw [e]
    exact hGn.of_norm_bounded fun j => norm_integral_le_integral_norm _
  have hLsum' : Summable fun j => w j * ∫ ρ, g j ρ ∂ν := by
    simpa only [hrep] using hLsum
  have hint0 : ∫ ρ in A, S ρ ∂ν ≤ 0 := by
    rw [← hex, ← hL0]
    simp_rw [hrep]
    exact hsumA.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hle j) (hw j)) hLsum'
  by_contra hne
  have hSi : IntegrableOn S A ν :=
    (integrable_const (∑' j, w j * (Mθ * (j ! : ℝ) ^ 2))).mono' hSc.aestronglyMeasurable
      (Eventually.of_forall fun ρ => by rw [Real.norm_eq_abs]; exact hSb ρ)
  have hpos : 0 < ∫ ρ in A, S ρ ∂ν := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun ρ => (hSpos ρ).le) hSi]
    have hsupp : Function.support S = univ :=
      Set.eq_univ_of_forall fun ρ => (hSpos ρ).ne'
    rw [hsupp, Set.univ_inter]
    exact pos_iff_ne_zero.mpr hne
  linarith

/-- **Positivity of the even functional on every admissible spectral square.**  If
`Ψ Ψ^# cosh²(z/2)` is a multiplier, then `L(Ψ Ψ^#) ≥ 0`. -/
theorem evenWeilDensity_specSq_nonneg_of_multiplier_sechWeight {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt 1 lam) {Ψ : ℂ → ℂ} (hT : Multiplier (sechWeight Ψ)) :
    0 ≤ evenWeilDensity lam (specSq Ψ) := by
  obtain ⟨Cg, -, hg⟩ := exists_abs_le_of_weilPositiveEvenAt h
  obtain ⟨ν, hfin, hν⟩ := exists_cosineShift_measure h hg evenStrip_sechHalf
  have hA := measure_sq_le_two_eq_zero hg hν
  rw [evenWeilDensity_specSq_eq_integral_sechHalf hg hν hT]
  refine integral_nonneg_of_ae ?_
  have hc : ∀ᵐ ρ ∂ν, ρ ∉ {ρ : ℝ | ρ ^ 2 ≤ 2} := measure_eq_zero_iff_ae_notMem.mp hA
  filter_upwards [hc] with ρ hρ
  simp only [not_le] at hρ
  exact re_rhoLift_sechWeight_nonneg Ψ hρ.le

end RHTower.EvenSector

end
