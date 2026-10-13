import GaloisForLFunctions.RHTower.XiLogDerivReLocality
import GaloisForLFunctions.RHTower.XiRightDiscSeamContractionInghamHuxley

/-!
# Hadamard positivity on every vertical line off a power-saving set of heights

RH is equivalent to `Re (ξ'/ξ)(s) ≥ 0` on `Re s > ½`.  Fix an abscissa `½ < σ ≤ 1`.

**Theorem** (`exists_volume_hadamardFailure_le_inghamHuxley`).  For every `0 < ε ≤ 1` there are
`C, B, T₀` such that for `T ≥ T₀` the heights `t ∈ [T, 2T]` at which `ξ(σ + it) = 0` or
`Re (ξ'/ξ)(σ + it) < 0` have Lebesgue measure at most `C (1 + log T)^B T^{(A(σ) + ε)(1 − σ)}`,
where `A` is the Ingham–Huxley exponent.

**Corollary** (`exists_volume_hadamardFailure_le_rpow_lt_one`).  There is `θ < 1` with failure
measure at most `T^θ` in `[T, 2T]` for large `T`.  So on every vertical line right of the critical
line, the Hadamard receiver holds at all heights outside a power-saving exceptional set.

**Proof.**  A zero `ρ` obstructs at `s = σ + it` only inside the disc
`(Re ρ − ½)² ≥ (σ − ½)² + (t − Im ρ)²` (`re_logDeriv_xi_nonneg_of_disk_bound`); such a zero, or its
reflection `1 − ρ̄`, has real part `≥ σ` and ordinate within `½` of `t`.  The failure heights lie in
the unit intervals around the ordinates of zero copies with real part `≥ σ`, which the cumulative
Ingham–Huxley count bounds (`exists_ncard_zeroCopyRange_le`).
-/

noncomputable section

open Complex MeasureTheory Filter

namespace RHTower

/-- Heights `t` at which the Hadamard receiver fails on the line `Re s = σ`. -/
def hadamardFailureHeights (σ : ℝ) : Set ℝ :=
  {t | ¬ (xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧ 0 ≤ (logDeriv xi ((σ : ℂ) + (t : ℂ) * I)).re)}

/-- A failure height lies within `½` of the ordinate of a zero copy with real part `≥ σ`. -/
theorem exists_copy_of_mem_hadamardFailureHeights {σ t : ℝ} (hσ : 1 / 2 < σ)
    (ht : t ∈ hadamardFailureHeights σ) :
    ∃ q : XiZeroCopy, σ ≤ ((q.1 : ℂ)).re ∧ |t - ((q.1 : ℂ)).im| < 1 / 2 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  by_contra hno
  push Not at hno
  -- every copy satisfies the strict disc bound
  have hdisk : ∀ q : XiZeroCopy, (((q.1 : ℂ)).re - 1 / 2) ^ 2 <
      (s.re - 1 / 2) ^ 2 + (s.im - ((q.1 : ℂ)).im) ^ 2 := by
    intro q
    rw [hsre, hsim]
    by_contra hge
    push Not at hge
    have hquarter := xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hsq : (σ - 1 / 2) ^ 2 ≤ (((q.1 : ℂ)).re - 1 / 2) ^ 2 := by nlinarith
    have himsq : (t - ((q.1 : ℂ)).im) ^ 2 < 1 / 4 := by nlinarith
    have him : |t - ((q.1 : ℂ)).im| < 1 / 2 :=
      abs_lt_of_sq_lt_sq (by nlinarith) (by norm_num)
    have habs : σ - 1 / 2 ≤ |((q.1 : ℂ)).re - 1 / 2| := by
      have h := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - 1 / 2)] at h
    rcases le_or_gt (1 / 2 : ℝ) ((q.1 : ℂ)).re with hhalf | hhalf
    · have := hno q (by rw [abs_of_nonneg (by linarith)] at habs; linarith)
      linarith
    · -- the reflected copy
      set q' := xiZeroCopyLineConjEquiv q with hq'
      have hq'eq := xiZero_lineConj_eq q
      have hre' : ((q'.1 : ℂ)).re = 1 - ((q.1 : ℂ)).re := by
        rw [hq', hq'eq]; simp
      have him' : ((q'.1 : ℂ)).im = ((q.1 : ℂ)).im := by
        rw [hq', hq'eq]; simp
      rw [abs_of_neg (by linarith)] at habs
      have := hno q' (by rw [hre']; linarith)
      rw [him'] at this
      linarith
  have hxi : xi s ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
    have := hdisk q
    rw [hq] at this
    simp at this
  have hpos := re_logDeriv_xi_nonneg_of_disk_bound (by rw [hsre]; exact hσ) hxi hdisk
  exact ht ⟨hxi, hpos⟩

/-- **The Hadamard receiver fails on a set of heights of Ingham–Huxley size.** -/
theorem exists_volume_hadamardFailure_le_inghamHuxley {σ ε : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℕ, ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      volume (hadamardFailureHeights σ ∩ Set.Icc T (2 * T)) ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ B *
          T ^ ((inghamHuxleyExponent σ + ε) * (1 - σ))) := by
  classical
  obtain ⟨D, hD, B, T₀, hT₀, hcount⟩ := exists_ncard_zeroCopyRange_le hσ hσ1 hε hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 - σ) with hE
  have hE0 : 0 ≤ E := by
    have hA := (inghamHuxleyExponent_mem hσ).1
    rw [hE]; exact mul_nonneg (by linarith) (by linarith)
  have hEle : E ≤ 2 := by
    have hA := (inghamHuxleyExponent_mem hσ).2
    rw [hE]; nlinarith
  refine ⟨2 * D * 3 ^ (B + 1) * 9, by positivity, B + 1, T₀ + 1, by linarith, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT₀0 : 0 < T₀ := by linarith
  set Y : ℝ := 2 * T + 1 with hY
  have hfin := zeroCopyRange_finite σ T₀ Y hT₀0
  set F : Finset XiZeroCopy := hfin.toFinset with hF
  -- the failure set lies in unit intervals around the copies of `F`
  have hsub : hadamardFailureHeights σ ∩ Set.Icc T (2 * T) ⊆
      ⋃ q ∈ F, Set.Icc (((q.1 : ℂ)).im - 1 / 2) (((q.1 : ℂ)).im + 1 / 2) := by
    rintro t ⟨ht, htT⟩
    obtain ⟨q, hqre, hqim⟩ := exists_copy_of_mem_hadamardFailureHeights hσ ht
    have habs := abs_lt.mp hqim
    refine Set.mem_iUnion₂.mpr ⟨q, hfin.mem_toFinset.mpr ⟨hqre, ?_, ?_⟩, ?_, ?_⟩
    · linarith [htT.1]
    · linarith [htT.2]
    · linarith
    · linarith
  have hvol : volume (hadamardFailureHeights σ ∩ Set.Icc T (2 * T)) ≤ F.card := by
    calc volume (hadamardFailureHeights σ ∩ Set.Icc T (2 * T))
        ≤ volume (⋃ q ∈ F, Set.Icc (((q.1 : ℂ)).im - 1 / 2) (((q.1 : ℂ)).im + 1 / 2)) :=
          measure_mono hsub
      _ ≤ ∑ q ∈ F, volume (Set.Icc (((q.1 : ℂ)).im - 1 / 2) (((q.1 : ℂ)).im + 1 / 2)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ _q ∈ F, (1 : ENNReal) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Real.volume_Icc]; norm_num
      _ = F.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (F.card : ℝ) = (zeroCopyRange σ T₀ Y).ncard := by
    rw [hF, Set.ncard_eq_toFinset_card _ hfin]
  have hYT : T₀ ≤ Y := by rw [hY]; linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hYpos : (0 : ℝ) < Y := by rw [hY]; linarith
  have hlogY : 1 + Real.log Y ≤ 3 * (1 + Real.log T) := by
    have h3T : Y ≤ 3 * T := by rw [hY]; linarith
    have := Real.log_le_log hYpos h3T
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  have hpowY : Y ^ E ≤ 9 * T ^ E := by
    calc Y ^ E ≤ (3 * T) ^ E := Real.rpow_le_rpow hYpos.le (by rw [hY]; linarith) hE0
      _ = 3 ^ E * T ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 9 * T ^ E := by
          gcongr
          calc (3 : ℝ) ^ E ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hEle
            _ = 9 := by norm_num
  have hlogY0 : 0 ≤ 1 + Real.log Y := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Y by rw [hY]; linarith); linarith
  have hreal : (F.card : ℝ) ≤ 2 * D * 3 ^ (B + 1) * 9 * (1 + Real.log T) ^ (B + 1) * T ^ E := by
    rw [hcard]
    calc ((zeroCopyRange σ T₀ Y).ncard : ℝ)
        ≤ 2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ E := hcount Y hYT
      _ ≤ 2 * D * (3 * (1 + Real.log T)) ^ (B + 1) * (9 * T ^ E) := by gcongr
      _ = 2 * D * 3 ^ (B + 1) * 9 * (1 + Real.log T) ^ (B + 1) * T ^ E := by
          rw [mul_pow]; ring
  calc volume (hadamardFailureHeights σ ∩ Set.Icc T (2 * T)) ≤ F.card := hvol
    _ = ENNReal.ofReal (F.card : ℝ) := by rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * D * 3 ^ (B + 1) * 9 * (1 + Real.log T) ^ (B + 1) * T ^ E) :=
        ENNReal.ofReal_le_ofReal hreal

/-- **Power saving.**  For `½ < σ ≤ 1` there is `θ < 1` such that for large `T` the heights in
`[T, 2T]` where the Hadamard receiver fails on `Re s = σ` have measure at most `T^θ`. -/
theorem exists_volume_hadamardFailure_le_rpow_lt_one {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume (hadamardFailureHeights σ ∩ Set.Icc T (2 * T)) ≤ ENNReal.ofReal (T ^ θ) := by
  set g : ℝ := 1 - inghamHuxleyExponent σ * (1 - σ) with hg
  have hg0 : 0 < g := by rw [hg]; linarith [inghamHuxleyExponent_mul_lt_one hσ]
  set ε : ℝ := min 1 g with hε
  have hε0 : 0 < ε := lt_min one_pos hg0
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨C, hC, B, T₁, hT₁, hbound⟩ :=
    exists_volume_hadamardFailure_le_inghamHuxley hσ hσ1 hε0 hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 - σ) with hE
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε ≤ g := min_le_right _ _
    have h12 : 1 - σ ≤ 1 / 2 := by linarith
    have h0 : 0 ≤ 1 - σ := by linarith
    rw [hE]
    have : ε * (1 - σ) ≤ g / 2 := by nlinarith
    nlinarith
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := g / 4) (by positivity) C)
  refine ⟨1 - g / 4, by linarith, max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := hT₁.trans hTT₁
  refine (hbound T hTT₁).trans (ENNReal.ofReal_le_ofReal ?_)
  calc C * (1 + Real.log T) ^ B * T ^ E ≤ T ^ (g / 4) * T ^ (1 - g / 2) :=
        mul_le_mul (hT₂ T hTT₂) (Real.rpow_le_rpow_of_exponent_le hT1 hEg) (by positivity)
          (by positivity)
    _ = T ^ (1 - g / 4) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

end RHTower

end
