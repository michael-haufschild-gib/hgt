import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FiniteEigenvalueCertificatesAndExceptionDensity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.IntrinsicDirichletCutoffMargin
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightOneHundredFifty

/-!
# Zero-exception finite-eigenvalue coverage through height 150, witness-surplus supremum, and canonical `hotEdge` reduction

Combining the coupled Bohman height verification `rhVerifiedThrough_oneHundredFifty`
(`TheVerifiedHeightOneHundredFifty`) with the finite surviving-eigenvalue framework
(`FiniteEigenvalueCertificatesAndExceptionDensity`) establishes three unconditional results:

1. **Zero-exception coverage through height `150` and frontier advance above `150`
   (`riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredFifty`,
   `zero_exception_finite_witness_through_oneHundredFifty`,
   `zero_exception_band_eightyFour_and_half_to_oneHundredFifty`,
   `strip_div_nat_zeta_ne_zero_below_scaled_oneHundredFifty`,
   `rh_iff_exists_finite_eigenvalue_witness_above_oneHundredFifty`)**:
   Every off-line strip point `s` (`0 < Re s < 1`, `Re s ≠ 1/2`) with `|Im s| ≤ 150` — and in
   particular **every point in `{3001 / 24000 ≤ Re s < 1 / 2 ∧ 169 / 2 < |Im s| ≤ 150}` with zero
   exceptions (zero isolated zeros permitted)** — carries an explicit rank-one omission
   `v : MissingWave` and finite prefix `K : ℕ` (`2 K` surviving eigenvalues) simultaneously beating
   both the UV-capped fourth-power threshold plus `triadTailBound K s` and the uncapped
   `(2 / Re s)`-power threshold plus `triadTailBound K s`. This closes the `(84.5, 101]` Speiser
   blind zone completely, advances right-strip `renormalizedCutoff` margins through `|Im w| ≤ 150`
   (and integer-ray dilations `ζ(w / k) ≠ 0` up to `150 k`, reaching `900` at `k = 6`), and shrinks
   the residual open `RiemannHypothesis` witness domain strictly from `|Im s| > 169 / 2` to
   `|Im s| > 150`.

2. **Exact witness-surplus supremum law (`capped_witness_surplus_le_norm_continued`,
   `uncapped_witness_surplus_le_norm_continued`,
   `exists_simultaneous_witness_surplus_gt_norm_continued_sub`)**:
   At every `s` with `0 < Re s < 1` and for **every** conserving rank-one omission `v : MissingWave`
   and prefix `K : ℕ`, the net witness margin
   `‖finiteTriadReading (missingWaveSpectrum v) K s‖ - (threshold(v) + triadTailBound K s)`
   is bounded above by `‖continued s‖ = ‖(2^s - 1) ζ(s)‖` (both under `uvRegularRankOne` at power
   `4` and without any UV cap at power `2 / Re s`), and approaches `‖continued s‖` arbitrarily
   closely as `lineLoss v → 0^+` and `K → ∞`. No choice of `v : MissingWave` can ever create
   surplus exceeding `‖(2^s - 1) ζ(s)‖`.

3. **Canonical `hotEdge 1` Dirichlet-eta reduction (`dyadicSpectralTriad_hotEdge_eq`,
   `exists_finite_witness_iff_hotEdge_beats_tail`)**:
   On `hotEdge 1`, `dyadicSpectralTriad (hotEdge 1) s k = (2k + 1)^{-s} - (2k + 2)^{-s}`. Existence
   of **any** finite-eigenvalue rank-one witness `(v, K)` at `s` (`0 < Re s < 1`, capped or
   uncapped) is pointwise equivalent (`↔`) — with no search over `v : MissingWave` — to existence of
   `K : ℕ` such that
   `(4 * ‖s‖ / s.re) * ((2 * K + 1 : ℝ)⁻¹) ^ s.re < ‖∑ k ∈ Finset.range K, (((2 * k + 1 : ℝ)⁻¹ : ℂ) ^ s - ((2 * k + 2 : ℝ)⁻¹ : ℂ) ^ s)‖`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open InverseSpectrum.ShellMixing

/-! ### Part 1: Exact witness-surplus supremum law -/

/-- **Universal UV-capped witness-surplus ceiling:** at every `s` (`0 < Re s < 1`), for every
`v : MissingWave` in `uvRegularRankOne s hs0 Λ` and every prefix `K : ℕ`, both the infinite-series
surplus and the `2 K`-eigenvalue finite-prefix surplus are bounded above by
`‖continued s‖ = ‖((2 : ℂ)^s - 1) * riemannZeta s‖`. -/
theorem capped_witness_surplus_le_norm_continued {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {Λ : ℝ} (hΛ : 0 < Λ) {v : MissingWave} (huv : uvRegularRankOne s hs0 Λ v) (K : ℕ) :
    ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ -
        (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) ≤ ‖continued s‖ ∧
      ‖finiteTriadReading (missingWaveSpectrum v) K s‖ -
        ((uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s) ≤
        ‖continued s‖ := by
  let b := missingWaveSpectrum v
  let β : GibbsExponent := ⟨s.re, hs0⟩
  have hll_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
  have hrp_le : ‖relativePartition b s‖ ≤ (‖s‖ / s.re) * relativeReading (powerResponse β) b :=
    relativePartition_norm_le b β le_rfl
  have huv_rpow : relativeReading (powerResponse β) b ≤ (Λ * lineLoss v.val) ^ (1 / 4 : ℝ) := by
    have hp := Real.rpow_le_rpow (pow_nonneg (relativeReading_bounds _ _).1 4) huv (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_natCast (relativeReading (powerResponse β) b) 4,
      ← Real.rpow_mul (relativeReading_bounds _ _).1,
      show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at hp
  have hbase_nn : 0 ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re) := by positivity
  have hthr_eq : (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) =
      ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re) * (Λ * lineLoss v.val) ^ (1 / 4 : ℝ) := by
    unfold uvZeroThresholdFactor
    rw [show ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * Λ * lineLoss v.val =
        (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re)) ^ 4 * (Λ * lineLoss v.val) by ring,
      Real.mul_rpow (pow_nonneg hbase_nn 4) (by positivity),
      ← Real.rpow_natCast _ 4, ← Real.rpow_mul hbase_nn,
      show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]
  have hpert_le : ‖((2 : ℂ) ^ s - 1) * relativePartition b s‖ ≤
      (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) := by
    rw [norm_mul, hthr_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (hrp_le.trans (mul_le_mul_of_nonneg_left huv_rpow (by positivity))) (norm_nonneg _)
  have hjsp_le : ‖jointSurvivingPartition b s‖ ≤
      ‖continued s‖ + ‖((2 : ℂ) ^ s - 1) * relativePartition b s‖ := by
    rw [jointSurvivingPartition_eq_continued_sub]
    exact norm_sub_le _ _
  have h1 : ‖jointSurvivingPartition b s‖ -
      (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) ≤ ‖continued s‖ := by
    linarith
  have htail := norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne
  have hfin_le : ‖finiteTriadReading b K s‖ ≤ ‖jointSurvivingPartition b s‖ + triadTailBound K s := by
    have h := norm_add_le (jointSurvivingPartition b s)
      (finiteTriadReading b K s - jointSurvivingPartition b s)
    rw [add_sub_cancel, norm_sub_rev] at h
    linarith
  exact ⟨h1, by linarith⟩

/-- **Universal cap-free witness-surplus ceiling:** at every `s` (`0 < Re s < 1`), for **every**
`v : MissingWave` (with no UV cap) and every prefix `K : ℕ`, both the infinite-series surplus and
the `2 K`-eigenvalue finite-prefix surplus at the sharp exponent `2 / Re s` are bounded above by
`‖continued s‖ = ‖((2 : ℂ)^s - 1) * riemannZeta s‖`. -/
theorem uncapped_witness_surplus_le_norm_continued {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (v : MissingWave) (K : ℕ) :
    ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ -
        (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) ≤ ‖continued s‖ ∧
      ‖finiteTriadReading (missingWaveSpectrum v) K s‖ -
        ((chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s) ≤
        ‖continued s‖ := by
  let b := missingWaveSpectrum v
  have hll_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
  have hctrl := matched_trace_control 1 hs0 (by linarith : s.re ≤ 2)
    (omitLine v.val) ((missingDimension_one_iff _).mpr ⟨v.val, missingWave_ne_zero v, rfl⟩)
    ((nonzero_line_conserves_iff v.val).mpr v.property).2
  rw [Nat.cast_one, Real.one_rpow, mul_one, traceLoss_omitLine] at hctrl
  change ‖relativePartition b s‖ ^ (2 / s.re) ≤ (‖s‖ / s.re) ^ (2 / s.re) * lineLoss v.val at hctrl
  have hbase_nn : 0 ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re) := by positivity
  have hrp_rpow := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hctrl (by positivity : 0 ≤ s.re / 2)
  rw [← Real.rpow_mul (norm_nonneg _), show (2 / s.re) * (s.re / 2) = 1 by field_simp [hs0.ne'],
    Real.rpow_one, Real.mul_rpow (Real.rpow_nonneg (by positivity) _) hll_pos.le,
    ← Real.rpow_mul (by positivity), show (2 / s.re) * (s.re / 2) = 1 by field_simp [hs0.ne'],
    Real.rpow_one] at hrp_rpow
  have hthr_eq : (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) =
      ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re) * lineLoss v.val ^ (s.re / 2) := by
    unfold chordZeroThresholdFactor
    rw [Real.mul_rpow (Real.rpow_nonneg hbase_nn _) hll_pos.le, ← Real.rpow_mul hbase_nn,
      show (2 / s.re) * (s.re / 2) = 1 by field_simp [hs0.ne'], Real.rpow_one]
  have hpert_le : ‖((2 : ℂ) ^ s - 1) * relativePartition b s‖ ≤
      (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) := by
    rw [norm_mul, hthr_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left hrp_rpow (norm_nonneg _)
  have hjsp_le : ‖jointSurvivingPartition b s‖ ≤
      ‖continued s‖ + ‖((2 : ℂ) ^ s - 1) * relativePartition b s‖ := by
    rw [jointSurvivingPartition_eq_continued_sub]
    exact norm_sub_le _ _
  have h1 : ‖jointSurvivingPartition b s‖ -
      (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) ≤ ‖continued s‖ := by
    linarith
  have htail := norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne
  have hfin_le : ‖finiteTriadReading b K s‖ ≤ ‖jointSurvivingPartition b s‖ + triadTailBound K s := by
    have h := norm_add_le (jointSurvivingPartition b s)
      (finiteTriadReading b K s - jointSurvivingPartition b s)
    rw [add_sub_cancel, norm_sub_rev] at h
    linarith
  exact ⟨h1, by linarith⟩

/-- **Simultaneous attainment of the `‖continued s‖` witness-surplus supremum:**
at every `s` (`0 < Re s < 1`), for every UV cap `Λ > 0` and tolerance `ε > 0`, there exist a
conserving rank-one omission `v : MissingWave` in `uvRegularRankOne s hs0 Λ` and a prefix `K : ℕ`
such that **both** the UV-capped and uncapped finite-eigenvalue surpluses exceed `‖continued s‖ - ε`. -/
theorem exists_simultaneous_witness_surplus_gt_norm_continued_sub
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {Λ ε : ℝ} (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ (v : MissingWave) (K : ℕ),
      uvRegularRankOne s hs0 Λ v ∧
      ‖continued s‖ - ε <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ -
          ((uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s) ∧
      ‖continued s‖ - ε <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ -
          ((chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s) := by
  set σ : ℝ := s.re
  set C_fac : ℝ := ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) + 1
  have hC_pos : 0 < C_fac := by dsimp only [C_fac]; positivity
  set η : ℝ := ε / (4 * C_fac)
  have hη_pos : 0 < η := div_pos hε (by positivity)
  set δ : ℝ := min (1 / 4) (min ((Λ / 4) ^ ((1 : ℝ) / 3))
    (min (η / 2) (min (η ^ 4 / (2 * Λ)) ((min (1 / 2) η) ^ (2 / σ) / 2))))
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    refine lt_min (by norm_num) (lt_min (Real.rpow_pos_of_pos (by positivity) _)
      (lt_min (by positivity) (lt_min (by positivity)
        (div_pos (Real.rpow_pos_of_pos (lt_min (by norm_num) hη_pos) _) two_pos))))
  have hδ_le_q : δ ≤ 1 / 4 := min_le_left _ _
  have hδ_lt_η : δ < η := by
    have hd : δ ≤ η / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith
  have hcap_δ : (2 * Λ * δ) ^ (1 / 4 : ℝ) ≤ η := by
    have hd : δ ≤ η ^ 4 / (2 * Λ) :=
      (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hm : 2 * Λ * δ ≤ η ^ 4 := by
      calc 2 * Λ * δ ≤ 2 * Λ * (η ^ 4 / (2 * Λ)) := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = η ^ 4 := by field_simp [hΛ.ne']
    calc (2 * Λ * δ) ^ (1 / 4 : ℝ) ≤ (η ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hm (by norm_num)
      _ = η := by
          rw [← Real.rpow_natCast η 4, ← Real.rpow_mul hη_pos.le,
            show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]
  have huncap_δ : (2 * δ) ^ (σ / 2) ≤ η := by
    set m1 : ℝ := min (1 / 2) η
    have hm1_pos : 0 < m1 := lt_min (by norm_num) hη_pos
    have hd : δ ≤ m1 ^ (2 / σ) / 2 :=
      (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
    calc (2 * δ) ^ (σ / 2) ≤ (m1 ^ (2 / σ)) ^ (σ / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = m1 := by
          rw [← Real.rpow_mul hm1_pos.le, show (2 / σ) * (σ / 2) = 1 by field_simp [hs0.ne'],
            Real.rpow_one]
      _ ≤ η := min_le_right _ _
  have hδ_uv : δ < (Λ * (δ / 2)) ^ (1 / 4 : ℝ) := by
    have hd : δ ≤ (Λ / 4) ^ ((1 : ℝ) / 3) := (min_le_right _ _).trans (min_le_left _ _)
    have hp3 : δ ^ 3 ≤ Λ / 4 := by
      have h1 := pow_le_pow_left₀ hδ_pos.le hd 3
      rwa [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity),
        show ((1 : ℝ) / 3) * (3 : ℕ) = 1 by norm_num, Real.rpow_one] at h1
    have hp4 : δ ^ 4 < ((Λ * (δ / 2)) ^ (1 / 4 : ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity),
        show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
      have hlt3 : δ ^ 3 < Λ / 2 := by linarith
      calc δ ^ 4 = δ ^ 3 * δ := by ring
        _ < (Λ / 2) * δ := mul_lt_mul_of_pos_right hlt3 hδ_pos
        _ = Λ * (δ / 2) := by ring
    by_contra! hge
    exact hp4.not_ge (pow_le_pow_left₀ (by positivity) hge 4)
  set τ₀ : ℝ := Real.sqrt (1 - δ)
  have hτ₀_pos : 0 < τ₀ := Real.sqrt_pos.mpr (by linarith)
  have hτ₀_lt1 : τ₀ < 1 := by
    have hsq : τ₀ ^ 2 < 1 ^ 2 := by rw [Real.sq_sqrt (by linarith)]; linarith
    exact (sq_lt_sq₀ hτ₀_pos.le zero_le_one).mp hsq
  have h1mτ₀2 : 1 - τ₀ ^ 2 = δ := by rw [Real.sq_sqrt (by linarith)]; ring
  obtain ⟨b₀, hb₀_cl, hb₀_eq⟩ := exists_ground_attenuation 0 ⟨τ₀, hτ₀_pos, hτ₀_lt1.le⟩
  let β : GibbsExponent := ⟨σ, hs0⟩
  have hb₀_q : relativeReading quadraticResponse b₀ = δ := by
    have h := hb₀_eq (z := 2) (by norm_num)
    rw [partition_at_two, show (τ₀ : ℂ) ^ (2 : ℂ) = ((τ₀ ^ 2 : ℝ) : ℂ) by
      rw [Complex.ofReal_pow, ← Complex.cpow_natCast]; rfl,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, h1mτ₀2] at h
    exact Complex.ofReal_injective h
  have hb₀_σ_le : relativeReading (powerResponse β) b₀ ≤ δ := by
    have h := hb₀_eq (z := (σ : ℂ)) (by simpa using hs0)
    have hrp := relativePartition_real b₀ β
    dsimp only [β] at hrp
    rw [hrp, ← Complex.ofReal_cpow hτ₀_pos.le, ← Complex.ofReal_one, ← Complex.ofReal_sub] at h
    have hval : relativeReading (powerResponse β) b₀ = 1 - τ₀ ^ σ := Complex.ofReal_injective h
    rw [hval, ← h1mτ₀2]
    have hle1 : τ₀ ^ (1 : ℝ) ≤ τ₀ ^ σ :=
      Real.rpow_le_rpow_of_exponent_ge hτ₀_pos hτ₀_lt1.le hs1.le
    rw [Real.rpow_one] at hle1
    have hle2 : τ₀ ^ 2 ≤ τ₀ := by nlinarith [hτ₀_pos, hτ₀_lt1]
    linarith
  set r_cap : ℝ := min ((Λ * (δ / 2)) ^ (1 / 4 : ℝ)) η
  let U : Set (SpectralBand 1) :=
    {c | δ / 2 < relativeReading quadraticResponse c ∧
      relativeReading quadraticResponse c < 2 * δ ∧
      relativeReading (powerResponse β) c < r_cap}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const (continuous_relativeReading quadraticResponse 1)).inter
      ((isOpen_lt (continuous_relativeReading quadraticResponse 1) continuous_const).inter
        (isOpen_lt (continuous_relativeReading (powerResponse β) 1) continuous_const))
  have hb₀_in_U : b₀ ∈ U := by
    refine ⟨?_, ?_, hb₀_σ_le.trans_lt (lt_min hδ_uv hδ_lt_η)⟩ <;> rw [hb₀_q] <;> linarith
  obtain ⟨_, hb_U, ⟨P, hd, hc_proj, rfl⟩⟩ := mem_closure_iff.mp hb₀_cl U hU_open hb₀_in_U
  obtain ⟨w_vec, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
  let v : MissingWave := ⟨w_vec, (nonzero_line_conserves_iff w_vec).mp ⟨hw_ne, hc_proj⟩⟩
  have hspec : physicalSpectrum (omitLine w_vec) hd hc_proj = missingWaveSpectrum v := rfl
  rw [hspec, Set.mem_setOf_eq, relativeReading_quadratic_missingWaveSpectrum] at hb_U
  obtain ⟨hL_lo, hL_hi, hR_lt⟩ := hb_U
  have huv : uvRegularRankOne s hs0 Λ v := by
    unfold uvRegularRankOne
    have hp4 := pow_le_pow_left₀ (relativeReading_bounds _ _).1
      (hR_lt.le.trans (min_le_left _ _)) 4
    have hrhs4 : ((Λ * (δ / 2)) ^ (1 / 4 : ℝ)) ^ 4 = Λ * (δ / 2) := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity),
        show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
    rw [hrhs4] at hp4
    exact hp4.trans (mul_le_mul_of_nonneg_left hL_lo.le hΛ.le)
  obtain ⟨K, hK_lt⟩ := ((tendsto_triadTailBound_zero hs0).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  have hpert_lt : ‖((2 : ℂ) ^ s - 1) * relativePartition (missingWaveSpectrum v) s‖ < ε / 4 := by
    have hrp := relativePartition_norm_le (missingWaveSpectrum v) β (z := s) le_rfl
    have hR_η : relativeReading (powerResponse β) (missingWaveSpectrum v) ≤ η :=
      hR_lt.le.trans (min_le_right _ _)
    calc ‖((2 : ℂ) ^ s - 1) * relativePartition (missingWaveSpectrum v) s‖
        = ‖(2 : ℂ) ^ s - 1‖ * ‖relativePartition (missingWaveSpectrum v) s‖ := norm_mul _ _
      _ ≤ ‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / σ) * η) :=
          mul_le_mul_of_nonneg_left (hrp.trans (mul_le_mul_of_nonneg_left hR_η (by positivity)))
            (norm_nonneg _)
      _ = (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) * η := by ring
      _ < C_fac * η := mul_lt_mul_of_pos_right (by dsimp only [C_fac]; linarith) hη_pos
      _ = ε / 4 := by dsimp only [η]; field_simp [hC_pos.ne']
  have hjsp_ge : ‖continued s‖ - ε / 4 < ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ := by
    rw [jointSurvivingPartition_eq_continued_sub]
    have h := norm_sub_norm_le (continued s)
      (((2 : ℂ) ^ s - 1) * relativePartition (missingWaveSpectrum v) s)
    linarith
  have htail := norm_jointSurviving_sub_finiteTriadReading_le (missingWaveSpectrum v) K hs0 hs1.ne
  have htri : ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ≤
      ‖finiteTriadReading (missingWaveSpectrum v) K s‖ +
        ‖jointSurvivingPartition (missingWaveSpectrum v) s -
          finiteTriadReading (missingWaveSpectrum v) K s‖ := by
    have h := norm_add_le (finiteTriadReading (missingWaveSpectrum v) K s)
      (jointSurvivingPartition (missingWaveSpectrum v) s -
        finiteTriadReading (missingWaveSpectrum v) K s)
    simpa only [add_sub_cancel] using h
  have hbase_nn : 0 ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) := by positivity
  have hll_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
  have hcap_lt : (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) < ε / 4 := by
    have hrew : (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) =
        (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) * (Λ * lineLoss v.val) ^ (1 / 4 : ℝ) := by
      unfold uvZeroThresholdFactor
      rw [show ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * Λ * lineLoss v.val =
          (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) ^ 4 * (Λ * lineLoss v.val) by ring,
        Real.mul_rpow (pow_nonneg hbase_nn 4) (by positivity),
        ← Real.rpow_natCast _ 4, ← Real.rpow_mul hbase_nn,
        show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]
    rw [hrew]
    have hr4 : (Λ * lineLoss v.val) ^ (1 / 4 : ℝ) ≤ η :=
      (Real.rpow_le_rpow (by positivity)
        (by linarith [mul_le_mul_of_nonneg_left hL_hi.le hΛ.le] : Λ * lineLoss v.val ≤ 2 * Λ * δ)
        (by norm_num)).trans hcap_δ
    calc (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) * (Λ * lineLoss v.val) ^ (1 / 4 : ℝ)
        ≤ (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) * η := mul_le_mul_of_nonneg_left hr4 hbase_nn
      _ < C_fac * η := mul_lt_mul_of_pos_right (by dsimp only [C_fac]; linarith) hη_pos
      _ = ε / 4 := by dsimp only [η]; field_simp [hC_pos.ne']
  have huncap_lt : (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) < ε / 4 := by
    have hrew : (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) =
        (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) * lineLoss v.val ^ (σ / 2) := by
      unfold chordZeroThresholdFactor
      rw [Real.mul_rpow (Real.rpow_nonneg hbase_nn _) hll_pos.le, ← Real.rpow_mul hbase_nn,
        show (2 / s.re) * (s.re / 2) = 1 by field_simp [hs0.ne'], Real.rpow_one]
    rw [hrew]
    have hr_un : lineLoss v.val ^ (σ / 2) ≤ η :=
      (Real.rpow_le_rpow hll_pos.le hL_hi.le (by positivity)).trans huncap_δ
    calc (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) * lineLoss v.val ^ (σ / 2)
        ≤ (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) * η := mul_le_mul_of_nonneg_left hr_un hbase_nn
      _ < C_fac * η := mul_lt_mul_of_pos_right (by dsimp only [C_fac]; linarith) hη_pos
      _ = ε / 4 := by dsimp only [η]; field_simp [hC_pos.ne']
  refine ⟨v, K, huv, ?_, ?_⟩ <;> linarith

/-! ### Part 2: Canonical `hotEdge 1` Dirichlet-eta reduction -/

/-- Exact evaluation of `dyadicSpectralTriad` on `hotEdge 1`: each triad collapses to the
alternating Dirichlet-eta pair `(2k + 1)^{-s} - (2k + 2)^{-s}`. -/
theorem dyadicSpectralTriad_hotEdge_eq (s : ℂ) (k : ℕ) :
    dyadicSpectralTriad (hotEdge 1) s k =
      (occupationWeight (2 * k) : ℂ) ^ s - (occupationWeight (2 * k + 1) : ℂ) ^ s := by
  have h2_scale : (2 : ℂ) ^ (1 - s) * (occupationWeight k : ℂ) ^ s =
      2 * (occupationWeight (2 * k + 1) : ℂ) ^ s := by
    have hmul : (occupationWeight (2 * k + 1) : ℂ) ^ s * (2 : ℂ) ^ s =
        (occupationWeight k : ℂ) ^ s := by
      have h := (Complex.mul_cpow_ofReal_nonneg (occupationWeight_pos (2 * k + 1)).le
        zero_le_two s).symm
      rw [Complex.ofReal_ofNat] at h
      refine h.trans ?_
      congr 1
      have hocc : occupationWeight (2 * k + 1) * 2 = occupationWeight k := by
        simp only [occupationWeight_eq]; push_cast; field_simp; ring
      exact_mod_cast hocc
    have h2s_ne : (2 : ℂ) ^ s ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero two_ne_zero]; exact Complex.exp_ne_zero _
    rw [Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one, ← hmul]
    field_simp [h2s_ne]
  unfold dyadicSpectralTriad hotEdge
  dsimp only
  rw [h2_scale]
  ring

/-- **Canonical `hotEdge 1` Dirichlet-eta reduction (eliminating the search over `MissingWave`):**
for every `s` with `0 < Re s < 1` and `Λ > 0`, the following are unconditionally equivalent:
1. Existence of a UV-capped finite-eigenvalue witness `(v, K)` beating
   `(uvZeroThresholdFactor s Λ * lineLoss v.val)^{1/4} + triadTailBound K s`;
2. Existence of an uncapped finite-eigenvalue witness `(v, K)` beating
   `(chordZeroThresholdFactor s * lineLoss v.val)^{s.re / 2} + triadTailBound K s`;
3. Existence of `K : ℕ` where `finiteTriadReading (hotEdge 1) K s` beats `triadTailBound K s`;
4. Existence of `K : ℕ` where the `v`-free `K`-pair Dirichlet-eta partial sum beats its tail:
   `(4 * ‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re < ‖∑ k ∈ Finset.range K, ((occupationWeight (2 * k) : ℂ) ^ s - (occupationWeight (2 * k + 1) : ℂ) ^ s)‖`. -/
theorem exists_finite_witness_iff_hotEdge_beats_tail
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {Λ : ℝ} (hΛ : 0 < Λ) :
    ((∃ (v : MissingWave) (K : ℕ), uvRegularRankOne s hs0 Λ v ∧
        (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
          ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ↔
      ∃ K : ℕ, triadTailBound K s < ‖finiteTriadReading (hotEdge 1) K s‖) ∧
    ((∃ (v : MissingWave) (K : ℕ),
        (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
          ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ↔
      ∃ K : ℕ,
        (4 * ‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re <
          ‖∑ k ∈ Finset.range K,
            ((occupationWeight (2 * k) : ℂ) ^ s - (occupationWeight (2 * k + 1) : ℂ) ^ s)‖) := by
  have hhot_iff_cs : (∃ K : ℕ, triadTailBound K s < ‖finiteTriadReading (hotEdge 1) K s‖) ↔
      continued s ≠ 0 := by
    constructor
    · rintro ⟨K, hK⟩ hcs0
      have htail := norm_jointSurviving_sub_finiteTriadReading_le (hotEdge 1) K hs0 hs1.ne
      rw [jointSurvivingPartition_hot, hcs0, zero_sub, norm_neg] at htail
      linarith
    · intro hcs
      have hpos : 0 < ‖continued s‖ / 2 := div_pos (norm_pos_iff.mpr hcs) two_pos
      obtain ⟨K, hK⟩ := ((tendsto_triadTailBound_zero hs0).eventually (gt_mem_nhds hpos)).exists
      have htail := norm_jointSurviving_sub_finiteTriadReading_le (hotEdge 1) K hs0 hs1.ne
      rw [jointSurvivingPartition_hot] at htail
      have htri : ‖continued s‖ ≤
          ‖finiteTriadReading (hotEdge 1) K s‖ +
            ‖continued s - finiteTriadReading (hotEdge 1) K s‖ := by
        have h := norm_add_le (finiteTriadReading (hotEdge 1) K s)
          (continued s - finiteTriadReading (hotEdge 1) K s)
        simpa only [add_sub_cancel] using h
      exact ⟨K, by linarith⟩
  have hpre_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ s.re - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two hs0)
    have h12 : (0 : ℝ) < (2 : ℝ) ^ (1 - s.re) - 1 :=
      sub_pos.mpr (Real.one_lt_rpow one_lt_two (sub_pos.mpr hs1))
    have hn1 : 0 < ‖(2 : ℂ) ^ s - 1‖ := by
      have h := norm_sub_norm_le ((2 : ℂ) ^ s) 1
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos, norm_one] at h
      linarith
    have hn2 : 0 < ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
      rw [norm_sub_rev]
      have h := norm_sub_norm_le ((2 : ℂ) ^ (1 - s)) 1
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.sub_re, Complex.one_re, norm_one] at h
      linarith
    exact div_pos hn1 hn2
  have heta_iff : (∃ K : ℕ, triadTailBound K s < ‖finiteTriadReading (hotEdge 1) K s‖) ↔
      ∃ K : ℕ, (4 * ‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re <
        ‖∑ k ∈ Finset.range K,
          ((occupationWeight (2 * k) : ℂ) ^ s - (occupationWeight (2 * k + 1) : ℂ) ^ s)‖ := by
    refine exists_congr fun K => ?_
    unfold triadTailBound finiteTriadReading
    rw [norm_mul, norm_div]
    simp_rw [dyadicSpectralTriad_hotEdge_eq]
    exact mul_lt_mul_iff_right₀ hpre_pos
  refine ⟨?_, ?_⟩
  · rw [exists_finite_capped_witness_iff_integral_ne_zero halfTurnClock 0 hs0 hs1 hΛ,
      (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero halfTurnClock 0 hs0 hs1.ne).not,
      hhot_iff_cs]
  · rw [exists_finite_uncapped_witness_iff_integral_ne_zero halfTurnClock 0 hs0 hs1,
      (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero halfTurnClock 0 hs0 hs1.ne).not,
      ← heta_iff, hhot_iff_cs]

/-! ### Part 3: Zero-exception coverage through height `150` and frontier advance above `150` -/

/-- **Off-line nonvanishing of `riemannZeta` and `continued` across `|Im s| ≤ 150`:**
every strip point `s` (`0 < Re s < 1`, `Re s ≠ 1/2`) with `|Im s| ≤ 150` satisfies
`riemannZeta s ≠ 0` and `continued s ≠ 0` unconditionally. -/
theorem riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredFifty
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hne_half : s.re ≠ 1 / 2) (him : |s.im| ≤ 150) :
    riemannZeta s ≠ 0 ∧ continued s ≠ 0 := by
  have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
  have hζ : riemannZeta s ≠ 0 := by
    intro h0
    have hxi : _root_.RHTower.xi s = 0 := (_root_.RHTower.xi_eq_zero_iff hs0 hs_ne1).mpr h0
    have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
      VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_oneHundredFifty hxi hs0 hs1 hne_half
    linarith
  have h2_ne : (2 : ℂ) ^ s - 1 ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := (factor_zero_iff s).mp h0
    exact hs0.ne' ((congrArg Complex.re hk).trans (frequency_re k))
  exact ⟨hζ, mul_ne_zero h2_ne hζ⟩

/-- **Zero-exception simultaneous finite-eigenvalue witness coverage through height `150`:**
for **every** `s` with `0 < Re s < 1`, `Re s ≠ 1/2`, and `|Im s| ≤ 150`, and every UV cap `Λ > 0`,
there exists a **single** pair `(v : MissingWave, K : ℕ)` in `uvRegularRankOne s hs0 Λ` whose
`2 K`-eigenvalue reading strictly beats **both** the UV-capped fourth-power threshold plus
`triadTailBound K s` **and** the uncapped `(2 / Re s)`-power threshold plus `triadTailBound K s`. -/
theorem zero_exception_finite_witness_through_oneHundredFifty
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hne_half : s.re ≠ 1 / 2) (him : |s.im| ≤ 150)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ (v : MissingWave) (K : ℕ),
      uvRegularRankOne s hs0 Λ v ∧
      (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ ∧
      (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ := by
  have hcs := (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredFifty hs0 hs1 hne_half him).2
  have hpos : 0 < ‖continued s‖ / 2 := div_pos (norm_pos_iff.mpr hcs) two_pos
  obtain ⟨v, K, huv, h1, h2⟩ :=
    exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 hΛ hpos
  exact ⟨v, K, huv, by linarith, by linarith⟩

/-- **Complete zero-exception elimination across `{3001/24000 ≤ Re s < 1/2 ∧ 84.5 < |Im s| ≤ 150}`
(closing the `(84.5, 101]` Speiser gap with zero isolated zeros permitted):**
every single point in this band carries a simultaneous UV-capped and uncapped finite-eigenvalue
witness `(v, K)`, a `hotEdge 1` Dirichlet-eta margin, and a reflected right-strip `renormalizedCutoff`
margin on every prime clock. -/
theorem zero_exception_band_eightyFour_and_half_to_oneHundredFifty
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2)
    (_him_lo : 169 / 2 < |s.im|) (him_hi : |s.im| ≤ 150) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ (hs0 : 0 < s.re) (v : MissingWave) (K K_eta : ℕ),
      uvRegularRankOne s hs0 Λ v ∧
      (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ ∧
      (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ ∧
      triadTailBound K_eta s < ‖finiteTriadReading (hotEdge 1) K_eta s‖ ∧
      ∀ (t : ExceptionalTime) (j : ℕ),
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧
          CutoffSeparation.zetaFreeTruncationBound t j X₀ (1 - conj s) <
            ‖CutoffSeparation.renormalizedCutoff t j X₀ (1 - conj s)‖ := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  obtain ⟨v, K, huv, hcap, huncap⟩ :=
    zero_exception_finite_witness_through_oneHundredFifty hs0 hs1 hhi.ne him_hi hΛ
  obtain ⟨K_eta, hK_eta⟩ :=
    (exists_finite_witness_iff_hotEdge_beats_tail hs0 hs1 hΛ).1.mp ⟨v, K, huv, hcap⟩
  refine ⟨hs0, v, K, K_eta, huv, hcap, huncap, hK_eta, fun t j => ?_⟩
  set w : ℂ := 1 - conj s
  have hw0 : 0 < w.re := by simp [w]; linarith
  have hw_lt1 : w.re < 1 := by simp [w]; linarith
  have hw_gt_half : 1 / 2 < w.re := by simp [w]; linarith
  have hw_ne1 : w ≠ 1 := fun h => hw_lt1.ne (by rw [h, Complex.one_re])
  have hw_im : |w.im| ≤ 150 := by
    have : w.im = s.im := by simp [w]
    rwa [this]
  have hw_zeta := (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredFifty
    hw0 hw_lt1 hw_gt_half.ne' hw_im).1
  exact (CutoffSeparation.exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw_ne1).mpr hw_zeta

/-- **Upgraded integer-ray dilation elimination below `150 k` (`k ≥ 2`, reaching `900` at `k = 6`):**
for every `k ≥ 2` and every open-strip point `0 < Re w < 1` with `|Im w| ≤ 150 k`, `ζ(w / k) ≠ 0`
unconditionally and its reflected right-strip partner carries a strict `renormalizedCutoff` margin. -/
theorem strip_div_nat_zeta_ne_zero_below_scaled_oneHundredFifty {k : ℕ} (hk : 2 ≤ k)
    {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ (150 : ℝ) * (k : ℝ)) :
    let z := w / (k : ℂ)
    let wRefl := 1 - conj z
    riemannZeta z ≠ 0 ∧
      1 / 2 < wRefl.re ∧ wRefl.re < 1 ∧
      riemannZeta wRefl ≠ 0 ∧
      ∀ (t : ExceptionalTime) (j : ℕ),
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧
          CutoffSeparation.zetaFreeTruncationBound t j X₀ wRefl <
            ‖CutoffSeparation.renormalizedCutoff t j X₀ wRefl‖ := by
  dsimp only
  set z := w / (k : ℂ)
  set wRefl := 1 - conj z
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hz_re : z.re = w.re / (k : ℝ) := by
    have hkeq : z = w * (((k : ℝ)⁻¹ : ℝ) : ℂ) := by
      dsimp only [z]; rw [Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
    rw [hkeq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hz_im : z.im = w.im / (k : ℝ) := by
    have hkeq : z = w * (((k : ℝ)⁻¹ : ℝ) : ℂ) := by
      dsimp only [z]; rw [Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
    rw [hkeq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, div_eq_mul_inv]
  have hz_re_pos : 0 < z.re := by rw [hz_re]; exact div_pos h0 hk_pos
  have hz_re_lt_half : z.re < 1 / 2 := by rw [hz_re, div_lt_iff₀ hk_pos]; linarith
  have hz_re_lt1 : z.re < 1 := by linarith
  have hz_im_le : |z.im| ≤ 150 := by
    rw [hz_im, abs_div, abs_of_pos hk_pos, div_le_iff₀ hk_pos]; exact him
  have hz_zeta := (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredFifty
    hz_re_pos hz_re_lt1 hz_re_lt_half.ne hz_im_le).1
  have hwR_re : wRefl.re = 1 - z.re := by simp [wRefl]
  have hwR_im : |wRefl.im| ≤ 150 := by
    have : wRefl.im = z.im := by simp [wRefl]
    rwa [this]
  have hwR_lo : 1 / 2 < wRefl.re := by linarith
  have hwR_hi : wRefl.re < 1 := by linarith
  have hwR_ne1 : wRefl ≠ 1 := fun h => hwR_hi.ne (by rw [h, Complex.one_re])
  have hwR_zeta := (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredFifty
    (by linarith) hwR_hi hwR_lo.ne' hwR_im).1
  exact ⟨hz_zeta, hwR_lo, hwR_hi, hwR_zeta, fun t j =>
    (CutoffSeparation.exists_zetaFree_margin_iff_zeta_ne_zero t j (by linarith) hwR_ne1).mpr hwR_zeta⟩

/-- **Unconditional advance of the `RiemannHypothesis` finite-eigenvalue witness frontier from
`|Im s| > 169/2` (`84.5`) strictly to `|Im s| > 150`:** -/
theorem rh_iff_exists_finite_eigenvalue_witness_above_oneHundredFifty
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 150 < |s.im| →
        ∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne s hs0 Λ v ∧
            (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
              ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 150 < |s.im| →
        ∃ (v : MissingWave) (K : ℕ),
          (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
            ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 150 < |s.im| →
        ∃ K : ℕ,
          (4 * ‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re <
            ‖∑ k ∈ Finset.range K,
              ((occupationWeight (2 * k) : ℂ) ^ s - (occupationWeight (2 * k + 1) : ℂ) ^ s)‖) := by
  obtain ⟨hcap84, huncap84⟩ := rh_iff_exists_finite_eigenvalue_witness_above_eightyFour_and_half hΛ
  have hcap150 : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 150 < |s.im| →
        ∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne s hs0 Λ v ∧
            (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
              ‖finiteTriadReading (missingWaveSpectrum v) K s‖ := by
    rw [hcap84]
    constructor
    · intro hall s hlo hhi him150
      exact hall s hlo hhi (by linarith)
    · intro hall s hlo hhi him84
      rcases le_or_gt |s.im| 150 with hle150 | hgt150
      · have hs0 : 0 < s.re := by linarith
        have hs1 : s.re < 1 := by linarith
        obtain ⟨v, K, huv, hcap, _⟩ :=
          zero_exception_finite_witness_through_oneHundredFifty hs0 hs1 hhi.ne hle150 hΛ
        exact ⟨hs0, v, K, huv, hcap⟩
      · exact hall s hlo hhi hgt150
  have huncap150 : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 150 < |s.im| →
        ∃ (v : MissingWave) (K : ℕ),
          (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
            ‖finiteTriadReading (missingWaveSpectrum v) K s‖ := by
    rw [huncap84]
    constructor
    · intro hall s hlo hhi him150
      exact hall s hlo hhi (by linarith)
    · intro hall s hlo hhi him84
      rcases le_or_gt |s.im| 150 with hle150 | hgt150
      · have hs0 : 0 < s.re := by linarith
        have hs1 : s.re < 1 := by linarith
        obtain ⟨v, K, _, _, huncap⟩ :=
          zero_exception_finite_witness_through_oneHundredFifty hs0 hs1 hhi.ne hle150 hΛ
        exact ⟨v, K, huncap⟩
      · exact hall s hlo hhi hgt150
  refine ⟨hcap150, huncap150, huncap150.trans ?_⟩
  refine forall₄_congr fun s hlo hhi _ => ?_
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  exact (exists_finite_witness_iff_hotEdge_beats_tail hs0 hs1 hΛ).2

#print axioms capped_witness_surplus_le_norm_continued
#print axioms uncapped_witness_surplus_le_norm_continued
#print axioms exists_simultaneous_witness_surplus_gt_norm_continued_sub
#print axioms dyadicSpectralTriad_hotEdge_eq
#print axioms exists_finite_witness_iff_hotEdge_beats_tail
#print axioms riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredFifty
#print axioms zero_exception_finite_witness_through_oneHundredFifty
#print axioms zero_exception_band_eightyFour_and_half_to_oneHundredFifty
#print axioms strip_div_nat_zeta_ne_zero_below_scaled_oneHundredFifty
#print axioms rh_iff_exists_finite_eigenvalue_witness_above_oneHundredFifty

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
