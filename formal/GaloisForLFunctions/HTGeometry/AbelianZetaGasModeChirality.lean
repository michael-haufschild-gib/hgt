import GaloisForLFunctions.HTGeometry.AbelianZetaGasChemicalPotentialShift
import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationProperness

/-!
# Log-weighted mode summability for the abelian zeta gas

Every convergent parameter point admits the log-weighted majorant

`∑_{p,j} (log p) · p^{−(jσ+τ)} < ∞`,

obtained by absorbing `log p ≤ p^ε/ε` into a slightly smaller Euler exponent that is still in the
first-depth convergence chamber.  This is the finiteness input needed to read the socle expectation
as a real sum of geometric-mode first responses.
-/

open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Every mode ratio is at most one half, because the least exponent already exceeds one. -/
theorem ratio_le_half (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) :
    θ.toAbelianZetaParameters.ratio m ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.two_le
  have hp1 : (1 : ℝ) ≤ ((m.1 : ℕ) : ℝ) := by linarith
  have hd : (1 : ℝ) ≤ (AbelianZetaMode.depth m : ℝ) := by
    exact_mod_cast AbelianZetaMode.depth_pos m
  have hexp : (1 : ℝ) ≤ θ.toAbelianZetaParameters.exponent m := by
    have h1 : θ.sigma ≤ (AbelianZetaMode.depth m : ℝ) * θ.sigma := by
      nlinarith [θ.sigma_pos]
    have := θ.firstDepth
    simp only [AbelianZetaParameters.exponent]
    linarith
  calc θ.toAbelianZetaParameters.ratio m
      = ((m.1 : ℕ) : ℝ) ^ (-θ.toAbelianZetaParameters.exponent m) := rfl
    _ ≤ ((m.1 : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / ((m.1 : ℕ) : ℝ) := by
        rw [Real.rpow_neg_one, inv_eq_one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

/-- The smaller Euler exponent used to absorb one logarithm. -/
private noncomputable def shrinkSigma (θ : AbelianZetaConvergentParameters) : ℝ :=
  min (θ.sigma / 2) ((θ.sigma + θ.tau - 1) / 2)

private theorem shrinkSigma_pos (θ : AbelianZetaConvergentParameters) : 0 < shrinkSigma θ :=
  lt_min (by linarith [θ.sigma_pos]) (by linarith [θ.firstDepth])

/-- Shrinking the Euler exponent keeps the point in the first-depth chamber. -/
private noncomputable def shrunk (θ : AbelianZetaConvergentParameters) : AbelianZetaConvergentParameters where
  sigma := θ.sigma - shrinkSigma θ
  tau := θ.tau
  sigma_pos := by
    have h := min_le_left (θ.sigma / 2) ((θ.sigma + θ.tau - 1) / 2)
    have := θ.sigma_pos
    simp only [shrinkSigma]
    linarith
  tau_nonneg := θ.tau_nonneg
  firstDepth := by
    have h := min_le_right (θ.sigma / 2) ((θ.sigma + θ.tau - 1) / 2)
    have := θ.firstDepth
    simp only [shrinkSigma]
    linarith

/-- **The log-weighted mode ratios are summable at every convergent parameter point.** -/
theorem summable_log_mul_ratio (θ : AbelianZetaConvergentParameters) :
    Summable fun m : AbelianZetaMode =>
      Real.log ((m.1 : ℕ) : ℝ) * θ.toAbelianZetaParameters.ratio m := by
  set ε : ℝ := shrinkSigma θ with hεdef
  have hεpos : 0 < ε := shrinkSigma_pos θ
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    (((shrunk θ).summable_ratio).mul_left (1 / ε))
  · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast m.1.prop.one_lt.le))
      (θ.toAbelianZetaParameters.ratio_nonneg m)
  · have hp1 : (1 : ℝ) ≤ ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.one_lt.le
    have hp0 : (0 : ℝ) ≤ ((m.1 : ℕ) : ℝ) := by linarith
    have hd : (1 : ℝ) ≤ (AbelianZetaMode.depth m : ℝ) := by
      exact_mod_cast AbelianZetaMode.depth_pos m
    have hlog : Real.log ((m.1 : ℕ) : ℝ) ≤ ((m.1 : ℕ) : ℝ) ^ ε / ε :=
      Real.log_le_rpow_div hp0 hεpos
    have hratio : (0 : ℝ) < θ.toAbelianZetaParameters.ratio m :=
      θ.toAbelianZetaParameters.ratio_pos m
    have hppos : (0 : ℝ) < ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.pos
    have hstep : ((m.1 : ℕ) : ℝ) ^ ε * θ.toAbelianZetaParameters.ratio m
        ≤ (shrunk θ).toAbelianZetaParameters.ratio m := by
      show ((m.1 : ℕ) : ℝ) ^ ε * ((m.1 : ℕ) : ℝ) ^ (-(θ.toAbelianZetaParameters.exponent m))
          ≤ ((m.1 : ℕ) : ℝ) ^ (-((shrunk θ).toAbelianZetaParameters.exponent m))
      rw [← Real.rpow_add hppos]
      refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
      simp only [AbelianZetaParameters.exponent, shrunk, ← hεdef]
      nlinarith [hd, hεpos]
    calc Real.log ((m.1 : ℕ) : ℝ) * θ.toAbelianZetaParameters.ratio m
        ≤ (((m.1 : ℕ) : ℝ) ^ ε / ε) * θ.toAbelianZetaParameters.ratio m := by
          exact mul_le_mul_of_nonneg_right hlog hratio.le
      _ = (1 / ε) * (((m.1 : ℕ) : ℝ) ^ ε * θ.toAbelianZetaParameters.ratio m) := by
          field_simp
      _ ≤ (1 / ε) * (shrunk θ).toAbelianZetaParameters.ratio m := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)

/-- The log-weighted geometric mode means are summable at every convergent parameter point. -/
theorem summable_log_mul_modeMean (θ : AbelianZetaConvergentParameters) :
    Summable fun m : AbelianZetaMode =>
      Real.log ((m.1 : ℕ) : ℝ) * (θ.toAbelianZetaParameters.ratio m /
        (1 - θ.toAbelianZetaParameters.ratio m)) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((summable_log_mul_ratio θ).mul_left 2)
  · have h0 : (0 : ℝ) ≤ θ.toAbelianZetaParameters.ratio m :=
      θ.toAbelianZetaParameters.ratio_nonneg m
    have h1 : (0 : ℝ) < 1 - θ.toAbelianZetaParameters.ratio m :=
      sub_pos.mpr (θ.toAbelianZetaParameters.ratio_lt_one m)
    have hlog : (0 : ℝ) ≤ Real.log ((m.1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast m.1.prop.one_lt.le)
    positivity
  · have h0 : (0 : ℝ) ≤ θ.toAbelianZetaParameters.ratio m :=
      θ.toAbelianZetaParameters.ratio_nonneg m
    have hhalf := ratio_le_half θ m
    have h1 : (1 : ℝ) / 2 ≤ 1 - θ.toAbelianZetaParameters.ratio m := by linarith
    have h1pos : (0 : ℝ) < 1 - θ.toAbelianZetaParameters.ratio m := by linarith
    have hlog : (0 : ℝ) ≤ Real.log ((m.1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast m.1.prop.one_lt.le)
    have hdiv : θ.toAbelianZetaParameters.ratio m / (1 - θ.toAbelianZetaParameters.ratio m)
        ≤ 2 * θ.toAbelianZetaParameters.ratio m := by
      rw [div_le_iff₀ h1pos]
      nlinarith
    calc Real.log ((m.1 : ℕ) : ℝ) * (θ.toAbelianZetaParameters.ratio m /
          (1 - θ.toAbelianZetaParameters.ratio m))
        ≤ Real.log ((m.1 : ℕ) : ℝ) * (2 * θ.toAbelianZetaParameters.ratio m) :=
          mul_le_mul_of_nonneg_left hdiv hlog
      _ = 2 * (Real.log ((m.1 : ℕ) : ℝ) * θ.toAbelianZetaParameters.ratio m) := by ring

/-- **The socle expectation is a finite real number**, namely the log-weighted sum of the geometric
mode means over all prime-depth modes. -/
theorem socleExpectation_eq_ofReal (θ : AbelianZetaConvergentParameters) :
    AbelianZetaParameters.socleExpectation θ.toAbelianZetaParameters
      = ENNReal.ofReal (∑' m : AbelianZetaMode, Real.log ((m.1 : ℕ) : ℝ) *
          (θ.toAbelianZetaParameters.ratio m / (1 - θ.toAbelianZetaParameters.ratio m))) := by
  classical
  set F : AbelianZetaMode → ℝ := fun m => Real.log ((m.1 : ℕ) : ℝ) *
    (θ.toAbelianZetaParameters.ratio m / (1 - θ.toAbelianZetaParameters.ratio m)) with hF
  have hFnn : ∀ m, 0 ≤ F m := by
    intro m
    have h0 : (0 : ℝ) ≤ θ.toAbelianZetaParameters.ratio m :=
      θ.toAbelianZetaParameters.ratio_nonneg m
    have h1 : (0 : ℝ) < 1 - θ.toAbelianZetaParameters.ratio m :=
      sub_pos.mpr (θ.toAbelianZetaParameters.ratio_lt_one m)
    have hlog : (0 : ℝ) ≤ Real.log ((m.1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast m.1.prop.one_lt.le)
    simp only [hF]
    positivity
  have hFsum : Summable F := summable_log_mul_modeMean θ
  have hslice : ∀ p : Nat.Primes, Summable fun j : ℕ => F (p, j) :=
    fun p => hFsum.prod_factor p
  have hkey : AbelianZetaParameters.socleExpectation θ.toAbelianZetaParameters
      = ENNReal.ofReal (∑' m : AbelianZetaMode, F m) := by
    rw [AbelianZetaParameters.socleExpectation_eq,
      ENNReal.ofReal_tsum_of_nonneg hFnn hFsum]
    have hprod : (∑' n : AbelianZetaMode, ENNReal.ofReal (F n))
        = ∑' (p : Nat.Primes) (j : ℕ), ENNReal.ofReal (F (p, j)) :=
      ENNReal.tsum_prod (f := fun p j => ENNReal.ofReal (F (p, j)))
    rw [hprod]
    refine tsum_congr fun p => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [← ENNReal.ofReal_mul (Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le))]
  exact hkey

theorem socleExpectation_ne_top (θ : AbelianZetaConvergentParameters) :
    AbelianZetaParameters.socleExpectation θ.toAbelianZetaParameters ≠ ⊤ := by
  rw [socleExpectation_eq_ofReal]
  exact ENNReal.ofReal_ne_top

/-- **The socle expectation in real form.** -/
theorem toReal_socleExpectation (θ : AbelianZetaConvergentParameters) :
    (AbelianZetaParameters.socleExpectation θ.toAbelianZetaParameters).toReal
      = ∑' m : AbelianZetaMode, Real.log ((m.1 : ℕ) : ℝ) *
          (θ.toAbelianZetaParameters.ratio m / (1 - θ.toAbelianZetaParameters.ratio m)) := by
  have hFnn : ∀ m : AbelianZetaMode, 0 ≤ Real.log ((m.1 : ℕ) : ℝ) *
      (θ.toAbelianZetaParameters.ratio m / (1 - θ.toAbelianZetaParameters.ratio m)) := by
    intro m
    have h0 : (0 : ℝ) ≤ θ.toAbelianZetaParameters.ratio m :=
      θ.toAbelianZetaParameters.ratio_nonneg m
    have h1 : (0 : ℝ) < 1 - θ.toAbelianZetaParameters.ratio m :=
      sub_pos.mpr (θ.toAbelianZetaParameters.ratio_lt_one m)
    have hlog : (0 : ℝ) ≤ Real.log ((m.1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast m.1.prop.one_lt.le)
    positivity
  rw [socleExpectation_eq_ofReal, ENNReal.toReal_ofReal (tsum_nonneg hFnn)]

/-! ## The gas as a sum of geometric formation modes -/

/-- The gas first response is the sum of the geometric-mode first responses. -/
theorem toReal_socleExpectation_fugacityShift (θ : AbelianZetaConvergentParameters)
    (u : ℝ) (hu : 0 ≤ u) :
    (AbelianZetaParameters.socleExpectation
        (fugacityShiftConv θ u hu).toAbelianZetaParameters).toReal
      = ∑' m : AbelianZetaMode,
          modeFirstMoment (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) u := by
  rw [toReal_socleExpectation]
  refine tsum_congr fun m => ?_
  rw [modeFirstMoment, ← ratio_fugacityShiftParameters θ.toAbelianZetaParameters u hu m]
  rfl

/-- Log partition of the gas at shifted chemical potential. -/
noncomputable def gasLogPartition (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) : ℝ :=
  -Real.log (((fugacityShiftConv θ u hu).nnNormalizer : ℝ≥0) : ℝ)

/-- First response of the gas at shifted chemical potential. -/
noncomputable def gasFirstMoment (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) : ℝ :=
  (AbelianZetaParameters.socleExpectation
    (fugacityShiftConv θ u hu).toAbelianZetaParameters).toReal

/-- **Directed information commutator of the gas** between two admitted chemical potentials. -/
noncomputable def gasChirality (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : ℝ :=
  2 * (gasLogPartition θ t ht - gasLogPartition θ s hs)
    + (t - s) * (gasFirstMoment θ s hs + gasFirstMoment θ t ht)

theorem summable_modeLogPartition (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) :
    Summable fun m : AbelianZetaMode =>
      modeLogPartition (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) u := by
  have h : Summable fun m : AbelianZetaMode =>
      Real.log (1 - (fugacityShiftConv θ u hu).toAbelianZetaParameters.ratio m) := by
    simpa only [sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable (fugacityShiftConv θ u hu).summable_ratio.neg
  refine h.neg.congr fun m => ?_
  rw [modeLogPartition, ← ratio_fugacityShiftParameters θ.toAbelianZetaParameters u hu m]
  rfl

theorem summable_modeFirstMoment (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) :
    Summable fun m : AbelianZetaMode =>
      modeFirstMoment (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) u := by
  refine (summable_log_mul_modeMean (fugacityShiftConv θ u hu)).congr fun m => ?_
  rw [modeFirstMoment, ← ratio_fugacityShiftParameters θ.toAbelianZetaParameters u hu m]
  rfl

/-- **The gas commutator is the sum of the geometric-mode commutators.** -/
theorem gasChirality_eq_tsum (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    gasChirality θ s t hs ht
      = ∑' m : AbelianZetaMode,
          modeChirality (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) s t := by
  have hFt := summable_modeLogPartition θ t ht
  have hFs := summable_modeLogPartition θ s hs
  have hms := summable_modeFirstMoment θ s hs
  have hmt := summable_modeFirstMoment θ t ht
  have hL : gasLogPartition θ t ht - gasLogPartition θ s hs
      = ∑' m : AbelianZetaMode,
          (modeLogPartition (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) t
            - modeLogPartition (θ.toAbelianZetaParameters.ratio m)
                (Real.log ((m.1 : ℕ) : ℝ)) s) := by
    rw [hFt.tsum_sub hFs, gasLogPartition, gasLogPartition,
      neg_log_nnNormalizer_eq_tsum_modeLogPartition θ t ht,
      neg_log_nnNormalizer_eq_tsum_modeLogPartition θ s hs]
  have hM : gasFirstMoment θ s hs + gasFirstMoment θ t ht
      = ∑' m : AbelianZetaMode,
          (modeFirstMoment (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) s
            + modeFirstMoment (θ.toAbelianZetaParameters.ratio m)
                (Real.log ((m.1 : ℕ) : ℝ)) t) := by
    rw [hms.tsum_add hmt, gasFirstMoment, gasFirstMoment,
      toReal_socleExpectation_fugacityShift θ s hs,
      toReal_socleExpectation_fugacityShift θ t ht]
  rw [gasChirality, hL, hM, ← (hFt.sub hFs).tsum_mul_left, ← (hms.add hmt).tsum_mul_left,
    ← Summable.tsum_add ((hFt.sub hFs).mul_left 2) ((hms.add hmt).mul_left (t - s))]
  exact tsum_congr fun m => rfl

theorem summable_modeChirality (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Summable fun m : AbelianZetaMode =>
      modeChirality (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) s t := by
  have hFt := summable_modeLogPartition θ t ht
  have hFs := summable_modeLogPartition θ s hs
  have hms := summable_modeFirstMoment θ s hs
  have hmt := summable_modeFirstMoment θ t ht
  exact ((hFt.sub hFs).mul_left 2).add ((hms.add hmt).mul_left (t - s))

private theorem modeRatio_shift_mem (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u)
    (m : AbelianZetaMode) :
    0 < modeRatio (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) u ∧
      modeRatio (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) u < 1 := by
  rw [← ratio_fugacityShiftParameters θ.toAbelianZetaParameters u hu m]
  exact ⟨AbelianZetaParameters.ratio_pos _ m, AbelianZetaParameters.ratio_lt_one _ m⟩

/-- **(FCRM.20), (FCRM.22b)  Strict source chirality of the abelian zeta gas.**  Every ordered pair
of admitted chemical potentials is oriented by the directed information commutator. -/
theorem gasChirality_pos (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s < t) :
    0 < gasChirality θ s t hs ht := by
  have hpos : ∀ m : AbelianZetaMode,
      0 < modeChirality (θ.toAbelianZetaParameters.ratio m)
        (Real.log ((m.1 : ℕ) : ℝ)) s t := by
    intro m
    obtain ⟨hs0, hs1⟩ := modeRatio_shift_mem θ s hs m
    obtain ⟨ht0, ht1⟩ := modeRatio_shift_mem θ t ht m
    exact modeChirality_pos (θ.toAbelianZetaParameters.ratio_pos m)
      (Real.log_pos (by exact_mod_cast m.1.prop.one_lt)) hs0 hs1 ht0 ht1 hst
  rw [gasChirality_eq_tsum]
  exact Summable.tsum_pos (summable_modeChirality θ s t hs ht)
    (fun m => (hpos m).le) (⟨2, Nat.prime_two⟩, 0) (hpos _)

/-- **Information chronology of the gas.**  The directed commutator reconstructs the complete
order of the chemical potential. -/
theorem gasChirality_lt_iff (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s < t ↔ 0 < gasChirality θ s t hs ht := by
  constructor
  · exact gasChirality_pos θ s t hs ht
  · intro h
    rcases lt_trichotomy s t with hst | hst | hst
    · exact hst
    · subst hst
      simp only [gasChirality, sub_self, zero_mul, mul_zero, add_zero] at h
      exact absurd h (lt_irrefl 0)
    · have hneg : gasChirality θ s t hs ht = -gasChirality θ t s ht hs := by
        simp only [gasChirality]; ring
      rw [hneg] at h
      have := gasChirality_pos θ t s ht hs hst
      linarith

end GaloisForLFunctions.HTGeometry
