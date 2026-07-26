import GaloisForLFunctions.HTGeometry.GeometricCDDConstraint
import GaloisForLFunctions.HTGeometry.HausdorffPositiveCddCone
import GaloisForLFunctions.HTGeometry.HausdorffShellTailProjectiveAttractor

/-!
# The deep geometric CDD tail has a flat projective limit

Fix `0 < q < 1` and `C > 1`.  The geometric paired-shell divisor has thresholds
`B_j = C q^{-j} = cosh η_j` and radii `r_j = B_j - sqrt(B_j² - 1) = exp(-η_j) ∈ (0,1)`.  Its
Hausdorff coupling measure is the purely atomic measure `ν = ∑_j r_j δ_{r_j²}`, and the tail
obtained by deleting the first `N` shells has finite positive mass `M_N = ∑_{j ≥ N} r_j`.

The geometric shell data is a `PositiveShellFamily`, so the zero-shell projective attractor of
`HausdorffShellTailProjectiveAttractor` applies verbatim: the normalized tail collapses weak-* to
`δ_0`, every higher-spin coupling except the spin-one value `8` vanishes, and the normalized phase
converges to the flat direction `8 sinh θ` with modulus `(8/3) r_N² cosh 3θ`.

What is specific to the geometric law and proved here is the shell geometry itself — `0 < r_j < 1`,
`1 + r_j² = 2 B_j r_j`, the decay `r_j ≤ q^j/C` and the resulting geometric decay of `M_N` — the
identification of the weighted kernel with the shell phase of `geometricCDDTruncationPhase`,

```
r_j · K(r_j², θ) = 4 arctan(q^j sinh θ / C),
```

the sharp geometric decay of the unnormalized tail phase, and the exact decimation identity
`∏_{k<M} step_q(t, N+k) = P_q(q^N t)`.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The geometric shell radii -/

/-- The paired-shell threshold `B_j = C q^{-j}` of the geometric CDD divisor. -/
def cddShellThreshold (q C : ℝ) (j : ℕ) : ℝ := C / q ^ j

/-- The shell radius `r_j = B_j - sqrt(B_j² - 1)`.  Writing `B_j = cosh η_j` with `η_j > 0` this is
`exp(-η_j)`. -/
def cddShellRadius (q C : ℝ) (j : ℕ) : ℝ :=
  cddShellThreshold q C j - Real.sqrt (cddShellThreshold q C j ^ 2 - 1)

/-- The conjugate radius `B_j + sqrt(B_j² - 1) = exp(η_j)`. -/
def cddShellConjugate (q C : ℝ) (j : ℕ) : ℝ :=
  cddShellThreshold q C j + Real.sqrt (cddShellThreshold q C j ^ 2 - 1)

variable {q C : ℝ}

theorem one_lt_cddShellThreshold (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    1 < cddShellThreshold q C j := by
  have hpow : (0 : ℝ) < q ^ j := pow_pos hq0 j
  have hle : q ^ j ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hCle : C ≤ C / q ^ j := by
    rw [le_div_iff₀ hpow]
    nlinarith
  exact lt_of_lt_of_le hC hCle

theorem cddShellThreshold_pos (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    0 < cddShellThreshold q C j :=
  lt_trans zero_lt_one (one_lt_cddShellThreshold hq0 hq1 hC j)

theorem sq_sqrt_cddShellThreshold (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    Real.sqrt (cddShellThreshold q C j ^ 2 - 1) ^ 2 = cddShellThreshold q C j ^ 2 - 1 := by
  refine Real.sq_sqrt ?_
  nlinarith [one_lt_cddShellThreshold hq0 hq1 hC j]

/-- The radius and its conjugate are reciprocal: `r_j (B_j + sqrt(B_j² - 1)) = 1`. -/
theorem cddShellRadius_mul_conjugate (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    cddShellRadius q C j * cddShellConjugate q C j = 1 := by
  have hs := sq_sqrt_cddShellThreshold hq0 hq1 hC j
  simp only [cddShellRadius, cddShellConjugate]
  nlinarith [hs]

theorem cddShellRadius_pos (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    0 < cddShellRadius q C j := by
  have hB := cddShellThreshold_pos hq0 hq1 hC j
  have h1 := one_lt_cddShellThreshold hq0 hq1 hC j
  have hlt : Real.sqrt (cddShellThreshold q C j ^ 2 - 1) < cddShellThreshold q C j := by
    have hstep := Real.sqrt_lt_sqrt (by nlinarith : (0 : ℝ) ≤ cddShellThreshold q C j ^ 2 - 1)
      (by nlinarith : cddShellThreshold q C j ^ 2 - 1 < cddShellThreshold q C j ^ 2)
    rwa [Real.sqrt_sq hB.le] at hstep
  simpa [cddShellRadius, sub_pos] using hlt

theorem cddShellConjugate_pos (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    0 < cddShellConjugate q C j :=
  add_pos_of_pos_of_nonneg (cddShellThreshold_pos hq0 hq1 hC j) (Real.sqrt_nonneg _)

theorem cddShellRadius_lt_one (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    cddShellRadius q C j < 1 := by
  have h1 := one_lt_cddShellThreshold hq0 hq1 hC j
  have hlt : cddShellThreshold q C j - 1
      < Real.sqrt (cddShellThreshold q C j ^ 2 - 1) := by
    refine (Real.lt_sqrt (by linarith)).mpr ?_
    nlinarith
  simp only [cddShellRadius]
  linarith

/-- The exact shell relation `1 + r_j² = 2 B_j r_j`, i.e. `B_j = cosh η_j` for `r_j = exp(−η_j)`. -/
theorem one_add_cddShellRadius_sq (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    1 + cddShellRadius q C j ^ 2 = 2 * cddShellThreshold q C j * cddShellRadius q C j := by
  have hs := sq_sqrt_cddShellThreshold hq0 hq1 hC j
  simp only [cddShellRadius]
  nlinarith [hs]

/-- The elementary decay estimate `r_j ≤ q^j / C`. -/
theorem cddShellRadius_le_pow_div (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) :
    cddShellRadius q C j ≤ q ^ j / C := by
  have hr := cddShellRadius_pos hq0 hq1 hC j
  have hr1 := cddShellRadius_lt_one hq0 hq1 hC j
  have hkey := one_add_cddShellRadius_sq hq0 hq1 hC j
  have hmul : cddShellRadius q C j * cddShellThreshold q C j ≤ 1 := by nlinarith
  have hpow : (0 : ℝ) < q ^ j := pow_pos hq0 j
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  rw [le_div_iff₀ hCpos]
  have hscaled : cddShellRadius q C j * (C / q ^ j) ≤ 1 := by
    simpa [cddShellThreshold] using hmul
  have hexpand : cddShellRadius q C j * C
      = (cddShellRadius q C j * (C / q ^ j)) * q ^ j := by
    field_simp
  rw [hexpand]
  nlinarith

theorem cddShellThreshold_mono (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) {i j : ℕ} (hij : i ≤ j) :
    cddShellThreshold q C i ≤ cddShellThreshold q C j := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  have hpi : (0 : ℝ) < q ^ i := pow_pos hq0 i
  have hpj : (0 : ℝ) < q ^ j := pow_pos hq0 j
  have hle : q ^ j ≤ q ^ i := pow_le_pow_of_le_one hq0.le hq1.le hij
  simp only [cddShellThreshold]
  rw [div_le_div_iff₀ hpi hpj]
  nlinarith

theorem cddShellThreshold_strictMono (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    StrictMono (cddShellThreshold q C) := by
  intro i j hij
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  have hpi : (0 : ℝ) < q ^ i := pow_pos hq0 i
  have hpj : (0 : ℝ) < q ^ j := pow_pos hq0 j
  have hlt : q ^ j < q ^ i := pow_lt_pow_right_of_lt_one₀ hq0 hq1 hij
  simp only [cddShellThreshold]
  rw [div_lt_div_iff₀ hpi hpj]
  nlinarith

/-- The shell thresholds `B_j = C q^{-j}` are unbounded. -/
theorem tendsto_cddShellThreshold_atTop (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    Tendsto (cddShellThreshold q C) atTop atTop := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  have hinv : (1 : ℝ) < q⁻¹ := (one_lt_inv₀ hq0).mpr hq1
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hinv
  refine (hpow.const_mul_atTop hCpos).congr fun j => ?_
  simp only [cddShellThreshold, inv_pow]
  field_simp

/-- The shell radii are antitone: deeper shells are smaller. -/
theorem cddShellRadius_antitone (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) {i j : ℕ} (hij : i ≤ j) :
    cddShellRadius q C j ≤ cddShellRadius q C i := by
  have hBi := cddShellThreshold_pos hq0 hq1 hC i
  have hmono := cddShellThreshold_mono hq0 hq1 hC hij
  have hsq : Real.sqrt (cddShellThreshold q C i ^ 2 - 1)
      ≤ Real.sqrt (cddShellThreshold q C j ^ 2 - 1) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hconj : cddShellConjugate q C i ≤ cddShellConjugate q C j := by
    simp only [cddShellConjugate]; linarith
  have hci := cddShellConjugate_pos hq0 hq1 hC i
  have hri := cddShellRadius_mul_conjugate hq0 hq1 hC i
  have hrj := cddShellRadius_mul_conjugate hq0 hq1 hC j
  nlinarith [cddShellRadius_pos hq0 hq1 hC i, cddShellRadius_pos hq0 hq1 hC j]

/-- The shell radii are strictly decreasing. -/
theorem cddShellRadius_strictAnti (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    StrictAnti (cddShellRadius q C) := by
  intro i j hij
  have hBi := cddShellThreshold_pos hq0 hq1 hC i
  have hmono := cddShellThreshold_strictMono hq0 hq1 hC hij
  have hsq : Real.sqrt (cddShellThreshold q C i ^ 2 - 1)
      ≤ Real.sqrt (cddShellThreshold q C j ^ 2 - 1) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hconj : cddShellConjugate q C i < cddShellConjugate q C j := by
    simp only [cddShellConjugate]; linarith
  have hci := cddShellConjugate_pos hq0 hq1 hC i
  have hri := cddShellRadius_mul_conjugate hq0 hq1 hC i
  have hrj := cddShellRadius_mul_conjugate hq0 hq1 hC j
  nlinarith [cddShellRadius_pos hq0 hq1 hC i, cddShellRadius_pos hq0 hq1 hC j]

theorem summable_cddShellRadius_shift (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    Summable fun j : ℕ => cddShellRadius q C (N + j) := by
  have hgeom : Summable fun j : ℕ => q ^ N / C * q ^ j :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  refine Summable.of_nonneg_of_le (fun j => (cddShellRadius_pos hq0 hq1 hC _).le)
    (fun j => ?_) hgeom
  calc cddShellRadius q C (N + j) ≤ q ^ (N + j) / C := cddShellRadius_le_pow_div hq0 hq1 hC _
    _ = q ^ N / C * q ^ j := by rw [pow_add]; ring

theorem summable_cddShellRadius (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    Summable (cddShellRadius q C) := by
  refine (summable_cddShellRadius_shift hq0 hq1 hC 0).congr fun j => ?_
  rw [Nat.zero_add]

theorem tendsto_cddShellRadius (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    Tendsto (fun N => cddShellRadius q C N) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => q ^ N / C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).div_const C
  exact squeeze_zero (fun N => (cddShellRadius_pos hq0 hq1 hC N).le)
    (fun N => cddShellRadius_le_pow_div hq0 hq1 hC N) hb

/-- **The geometric CDD divisor is a positive Hausdorff shell family.**  This single fact imports
the whole zero-shell projective attractor. -/
theorem positiveShellFamily_cddShellRadius (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    PositiveShellFamily (cddShellRadius q C) (fun j => cddShellRadius q C j ^ 2) where
  weight_pos j := cddShellRadius_pos hq0 hq1 hC j
  weight_summable := summable_cddShellRadius hq0 hq1 hC
  radius_nonneg _ := sq_nonneg _
  radius_le_one j := by
    nlinarith [cddShellRadius_pos hq0 hq1 hC j, cddShellRadius_lt_one hq0 hq1 hC j]
  radius_antitone := by
    intro i j hij
    have hle := cddShellRadius_antitone hq0 hq1 hC hij
    nlinarith [cddShellRadius_pos hq0 hq1 hC i, cddShellRadius_pos hq0 hq1 hC j]
  radius_tendsto := by simpa using (tendsto_cddShellRadius hq0 hq1 hC).pow 2

/-! ## The tail coupling mass -/

/-- The total coupling mass of the tail obtained by deleting the first `N` shells. -/
def cddTailMass (q C : ℝ) (N : ℕ) : ℝ := shellTailMass (cddShellRadius q C) N

theorem cddTailMass_pos (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    0 < cddTailMass q C N :=
  shellTailMass_pos (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

/-- The geometric tail mass decays at the shell rate. -/
theorem cddTailMass_le (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddTailMass q C N ≤ q ^ N / (C * (1 - q)) := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  have hgeom : Summable fun j : ℕ => q ^ N / C * q ^ j :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  have hle : cddTailMass q C N ≤ ∑' j : ℕ, q ^ N / C * q ^ j := by
    refine Summable.tsum_le_tsum (fun j => ?_) (summable_cddShellRadius_shift hq0 hq1 hC N) hgeom
    calc cddShellRadius q C (N + j) ≤ q ^ (N + j) / C := cddShellRadius_le_pow_div hq0 hq1 hC _
      _ = q ^ N / C * q ^ j := by rw [pow_add]; ring
  have hval : (∑' j : ℕ, q ^ N / C * q ^ j) = q ^ N / C * (1 - q)⁻¹ := by
    rw [(summable_geometric_of_lt_one hq0.le hq1).tsum_mul_left,
      tsum_geometric_of_lt_one hq0.le hq1]
  rw [hval] at hle
  refine hle.trans (le_of_eq ?_)
  field_simp

theorem tendsto_cddTailMass (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    Tendsto (fun N => cddTailMass q C N) atTop (𝓝 0) :=
  tendsto_shellTailMass (cddShellRadius q C)

/-- The normalized weight of the `j`-th surviving shell in the tail beyond level `N`. -/
def cddTailWeight (q C : ℝ) (N j : ℕ) : ℝ := shellTailWeight (cddShellRadius q C) N j

theorem cddTailWeight_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N j : ℕ) :
    0 ≤ cddTailWeight q C N j :=
  shellTailWeight_nonneg (positiveShellFamily_cddShellRadius hq0 hq1 hC) N j

theorem summable_cddTailWeight (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    Summable fun j : ℕ => cddTailWeight q C N j :=
  summable_shellTailWeight (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

theorem tsum_cddTailWeight (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    ∑' j : ℕ, cddTailWeight q C N j = 1 :=
  tsum_shellTailWeight (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

/-! ## The normalized tail measure -/

/-- The unnormalized coupling measure of the tail beyond level `N`:
`ν_{≥N} = ∑_{j ≥ N} r_j δ_{r_j²}`. -/
def cddTailMeasure (q C : ℝ) (N : ℕ) : Measure ℝ :=
  shellTailMeasure (cddShellRadius q C) (fun j => cddShellRadius q C j ^ 2) N

/-- The normalized tail measure `ν̂_N = M_N⁻¹ ν_{≥N}`. -/
def cddNormalizedTailMeasure (q C : ℝ) (N : ℕ) : Measure ℝ :=
  shellNormalizedTailMeasure (cddShellRadius q C) (fun j => cddShellRadius q C j ^ 2) N

theorem cddNormalizedTailMeasure_eq_smul (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddNormalizedTailMeasure q C N
      = ENNReal.ofReal (cddTailMass q C N)⁻¹ • cddTailMeasure q C N :=
  shellNormalizedTailMeasure_eq_smul (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

theorem cddTailMeasure_univ (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddTailMeasure q C N Set.univ = ENNReal.ofReal (cddTailMass q C N) :=
  shellTailMeasure_univ (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

theorem cddNormalizedTailMeasure_univ (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddNormalizedTailMeasure q C N Set.univ = 1 :=
  shellNormalizedTailMeasure_univ (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

theorem isProbabilityMeasure_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    IsProbabilityMeasure (cddNormalizedTailMeasure q C N) :=
  isProbabilityMeasure_shellNormalizedTailMeasure
    (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

/-- The normalized tail measure as a bundled probability law. -/
def cddTailProbability (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    ProbabilityMeasure ℝ :=
  shellTailProbability (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

@[simp]
theorem cddTailProbability_toMeasure (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    (cddTailProbability hq0 hq1 hC N : Measure ℝ) = cddNormalizedTailMeasure q C N := rfl

/-- Every atom of the tail beyond level `N` lies below `r_N²`. -/
theorem cddTailAtom_le (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N j : ℕ) :
    cddShellRadius q C (N + j) ^ 2 ≤ cddShellRadius q C N ^ 2 :=
  (positiveShellFamily_cddShellRadius hq0 hq1 hC).atom_le N j

/-- Every atom of the tail lies in the unit interval. -/
theorem cddTailAtom_mem_Icc (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N j : ℕ) :
    cddShellRadius q C (N + j) ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
  (positiveShellFamily_cddShellRadius hq0 hq1 hC).atom_mem_Icc N j

/-! ## Theorem A: the normalized tail collapses to the zero-shell ray -/

/-- Outside any ball strictly larger than `r_N²` the normalized tail carries no mass. -/
theorem cddNormalizedTailMeasure_compl_ball
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {ε : ℝ}
    (hε : cddShellRadius q C N ^ 2 < ε) :
    cddNormalizedTailMeasure q C N (Metric.ball (0 : ℝ) ε)ᶜ = 0 :=
  shellNormalizedTailMeasure_compl_ball (positiveShellFamily_cddShellRadius hq0 hq1 hC) N hε

/-- The normalized tail measure is carried by `[0, r_N²]`. -/
theorem cddNormalizedTailMeasure_compl_Icc
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddNormalizedTailMeasure q C N (Set.Icc 0 (cddShellRadius q C N ^ 2))ᶜ = 0 :=
  shellNormalizedTailMeasure_compl_Icc (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

/-- **Theorem A.**  The normalized tail laws converge weak-* to the Dirac law at the zero shell. -/
theorem tendsto_cddTailProbability_diracProba
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    Tendsto (fun N => cddTailProbability hq0 hq1 hC N) atTop (𝓝 (diracProba (0 : ℝ))) :=
  tendsto_shellTailProbability_diracProba (positiveShellFamily_cddShellRadius hq0 hq1 hC)

/-! ## Integration against the normalized tail -/

theorem summable_cddTailWeight_mul_abs
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Summable fun j : ℕ =>
      cddTailWeight q C N j * |f (cddShellRadius q C (N + j) ^ 2)| :=
  summable_shellTailWeight_mul_abs (positiveShellFamily_cddShellRadius hq0 hq1 hC) N hf

theorem summable_cddTailWeight_mul
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Summable fun j : ℕ =>
      cddTailWeight q C N j * f (cddShellRadius q C (N + j) ^ 2) :=
  summable_shellTailWeight_mul (positiveShellFamily_cddShellRadius hq0 hq1 hC) N hf

theorem integrable_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (cddNormalizedTailMeasure q C N) :=
  integrable_shellNormalizedTailMeasure (positiveShellFamily_cddShellRadius hq0 hq1 hC) N hf

theorem integral_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ t, f t ∂(cddNormalizedTailMeasure q C N)
      = ∑' j : ℕ, cddTailWeight q C N j * f (cddShellRadius q C (N + j) ^ 2) :=
  integral_shellNormalizedTailMeasure (positiveShellFamily_cddShellRadius hq0 hq1 hC) N hf

/-- **Theorem A, test-function form.**  Equations (7)–(8): the normalized tail integrates every
continuous function to its zero-shell value. -/
theorem tendsto_integral_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun N => ∫ t, f t ∂(cddNormalizedTailMeasure q C N)) atTop (𝓝 (f 0)) :=
  tendsto_integral_shellNormalizedTailMeasure
    (positiveShellFamily_cddShellRadius hq0 hq1 hC) hf

/-! ## Theorem B: all normalized higher-spin directions except spin one vanish -/

/-- The `m`-th moment of the normalized tail measure. -/
def cddTailMoment (q C : ℝ) (N m : ℕ) : ℝ :=
  shellTailMoment (cddShellRadius q C) (fun j => cddShellRadius q C j ^ 2) N m

@[simp]
theorem cddTailMoment_zero (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddTailMoment q C N 0 = 1 :=
  shellTailMoment_zero (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

theorem cddTailMoment_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N m : ℕ) :
    0 ≤ cddTailMoment q C N m :=
  shellTailMoment_nonneg (positiveShellFamily_cddShellRadius hq0 hq1 hC) N m

/-- **Theorem B, bound.**  The `m`-th normalized tail moment is at most `r_N^{2m}`. -/
theorem cddTailMoment_le (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N m : ℕ) :
    cddTailMoment q C N m ≤ (cddShellRadius q C N ^ 2) ^ m :=
  shellTailMoment_le (positiveShellFamily_cddShellRadius hq0 hq1 hC) N m

/-- **Theorem B, collapse.**  Every moment of positive order tends to zero along the shell tail. -/
theorem tendsto_cddTailMoment (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N => cddTailMoment q C N m) atTop (𝓝 0) :=
  tendsto_shellTailMoment (positiveShellFamily_cddShellRadius hq0 hq1 hC) hm

/-- Equation (9): the moments are the integrals of the monomials. -/
theorem integral_pow_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N m : ℕ) :
    ∫ t, t ^ m ∂(cddNormalizedTailMeasure q C N) = cddTailMoment q C N m :=
  integral_pow_shellNormalizedTailMeasure (positiveShellFamily_cddShellRadius hq0 hq1 hC) N m

/-- The normalized odd higher-spin coupling `α̂_{2m+1} = 8(-1)^m b_m/(2m+1)`. -/
def cddNormalizedSpinCoupling (q C : ℝ) (N m : ℕ) : ℝ :=
  shellNormalizedSpinCoupling (cddShellRadius q C) (fun j => cddShellRadius q C j ^ 2) N m

/-- The spin-one coupling is the fixed `T T̄` value `8` at every truncation level. -/
@[simp]
theorem cddNormalizedSpinCoupling_zero (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddNormalizedSpinCoupling q C N 0 = 8 :=
  shellNormalizedSpinCoupling_zero (positiveShellFamily_cddShellRadius hq0 hq1 hC) N

/-- **Theorem B, projective direction.**  Every higher-spin coupling collapses; only the spin-one
current–current direction survives. -/
theorem tendsto_cddNormalizedSpinCoupling (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N => cddNormalizedSpinCoupling q C N m) atTop (𝓝 0) :=
  tendsto_shellNormalizedSpinCoupling (positiveShellFamily_cddShellRadius hq0 hq1 hC) hm

/-! ## Theorem C: the normalized phase converges to the flat direction -/

/-- **Shell identity.**  The kernel weighted by its shell radius is the shell phase
`4 arctan(q^j sinh θ / C)` — the `j`-th summand of `geometricCDDTruncationPhase`. -/
theorem cddShellRadius_mul_cddPhaseKernel
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (j : ℕ) (θ : ℝ) :
    cddShellRadius q C j * cddPhaseKernel (cddShellRadius q C j ^ 2) θ
      = 4 * Real.arctan (q ^ j * Real.sinh θ / C) := by
  have hr := cddShellRadius_pos hq0 hq1 hC j
  have hkey := one_add_cddShellRadius_sq hq0 hq1 hC j
  have hB := cddShellThreshold_pos hq0 hq1 hC j
  rw [cddPhaseKernel_sq hr]
  congr 2
  rw [hkey]
  have hBval : cddShellThreshold q C j = C / q ^ j := rfl
  rw [hBval]
  have hpow : (0 : ℝ) < q ^ j := pow_pos hq0 j
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  field_simp

/-- The unnormalized tail phase `Σ_{≥N}(θ) = ∫ K dν_{≥N}`. -/
def cddTailPhase (q C : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  shellTailPhase (cddShellRadius q C) (fun j => cddShellRadius q C j ^ 2) N θ

/-- The normalized tail phase `Σ̂_N(θ) = ∫ K dν̂_N`. -/
def cddNormalizedTailPhase (q C : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  shellNormalizedTailPhase (cddShellRadius q C) (fun j => cddShellRadius q C j ^ 2) N θ

/-- **Theorem C, sharp estimate.**  The normalized tail phase differs from the flat direction
`8 sinh θ` by at most `(8/3) r_N² cosh 3θ`. -/
theorem abs_cddNormalizedTailPhase_sub_flat_le
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    |cddNormalizedTailPhase q C N θ - 8 * Real.sinh θ|
      ≤ 8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ) :=
  abs_shellNormalizedTailPhase_sub_flat_le
    (positiveShellFamily_cddShellRadius hq0 hq1 hC) N θ

/-- Pointwise convergence of the normalized tail phase to the flat direction. -/
theorem tendsto_cddNormalizedTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => cddNormalizedTailPhase q C N θ) atTop (𝓝 (8 * Real.sinh θ)) :=
  tendsto_shellNormalizedTailPhase (positiveShellFamily_cddShellRadius hq0 hq1 hC) θ

/-- **Theorem C, locally uniform convergence.**  On every bounded rapidity window the normalized
tail phase converges uniformly to the flat `T T̄` direction `8 sinh θ`. -/
theorem tendstoUniformlyOn_cddNormalizedTailPhase
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (T : ℝ) :
    TendstoUniformlyOn (fun N θ => cddNormalizedTailPhase q C N θ)
      (fun θ => 8 * Real.sinh θ) atTop (Set.Icc (-T) T) :=
  tendstoUniformlyOn_shellNormalizedTailPhase
    (positiveShellFamily_cddShellRadius hq0 hq1 hC) T

/-- **Theorem C, exponentiated form.**  The normalized tail scattering factor converges to the
universal flat dressing `exp(8 i sinh θ)`. -/
theorem tendsto_exp_cddNormalizedTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => Complex.exp (Complex.I * (cddNormalizedTailPhase q C N θ : ℂ))) atTop
      (𝓝 (Complex.exp (Complex.I * ((8 * Real.sinh θ : ℝ) : ℂ)))) :=
  tendsto_exp_shellNormalizedTailPhase (positiveShellFamily_cddShellRadius hq0 hq1 hC) θ

/-- Equation (14): the normalized phase is the kernel integral against the normalized tail. -/
theorem integral_cddPhaseKernel_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    ∫ t, cddPhaseKernel t θ ∂(cddNormalizedTailMeasure q C N)
      = cddNormalizedTailPhase q C N θ :=
  integral_cddPhaseKernel_shellNormalizedTailMeasure
    (positiveShellFamily_cddShellRadius hq0 hq1 hC) N θ

/-! ### The unnormalized tail is asymptotically trivial -/

/-- The unnormalized tail phase is the sum of the surviving shell phases. -/
theorem cddTailPhase_eq_shellSum (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    cddTailPhase q C N θ = ∑' j : ℕ, 4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C) :=
  tsum_congr fun j => cddShellRadius_mul_cddPhaseKernel hq0 hq1 hC (N + j) θ

theorem summable_cddTailPhaseTerm (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    Summable fun j : ℕ => 4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C) := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hq0.le hq1).mul_left
      (4 * |Real.sinh θ| * q ^ N / C)) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  have hat := abs_arctan_le_abs (q ^ (N + j) * Real.sinh θ / C)
  have habs : |q ^ (N + j) * Real.sinh θ / C| = q ^ N * q ^ j * |Real.sinh θ| / C := by
    rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt (pow_pos hq0 _)),
      abs_of_nonneg hCpos.le, pow_add]
  rw [habs] at hat
  have hchain : 4 * |Real.arctan (q ^ (N + j) * Real.sinh θ / C)|
      ≤ 4 * (q ^ N * q ^ j * |Real.sinh θ| / C) := by linarith
  refine hchain.trans (le_of_eq ?_)
  field_simp

/-- Sharp geometric decay of the unnormalized tail phase. -/
theorem abs_cddTailPhase_le (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    |cddTailPhase q C N θ| ≤ 4 * |Real.sinh θ| * q ^ N / (C * (1 - q)) := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  have hterm : ∀ j : ℕ, ‖4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C)‖
      ≤ 4 * |Real.sinh θ| * q ^ N / C * q ^ j := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    have hat := abs_arctan_le_abs (q ^ (N + j) * Real.sinh θ / C)
    have habs : |q ^ (N + j) * Real.sinh θ / C| = q ^ N * q ^ j * |Real.sinh θ| / C := by
      rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt (pow_pos hq0 _)),
        abs_of_nonneg hCpos.le, pow_add]
    rw [habs] at hat
    have hchain : 4 * |Real.arctan (q ^ (N + j) * Real.sinh θ / C)|
        ≤ 4 * (q ^ N * q ^ j * |Real.sinh θ| / C) := by linarith
    refine hchain.trans (le_of_eq ?_)
    field_simp
    ring
  rw [cddTailPhase_eq_shellSum hq0 hq1 hC N θ]
  have hgeom : Summable fun j : ℕ => 4 * |Real.sinh θ| * q ^ N / C * q ^ j :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  have hnorm : Summable fun j : ℕ => ‖4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C)‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm hgeom
  have hle := norm_tsum_le_tsum_norm hnorm
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hcmp : ∑' j : ℕ, ‖4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C)‖
      ≤ ∑' j : ℕ, 4 * |Real.sinh θ| * q ^ N / C * q ^ j :=
    Summable.tsum_le_tsum hterm hnorm hgeom
  refine hcmp.trans (le_of_eq ?_)
  rw [(summable_geometric_of_lt_one hq0.le hq1).tsum_mul_left,
    tsum_geometric_of_lt_one hq0.le hq1]
  field_simp

/-- The unnormalized tail phase vanishes in the deep-shell limit. -/
theorem tendsto_cddTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => cddTailPhase q C N θ) atTop (𝓝 0) :=
  tendsto_shellTailPhase (positiveShellFamily_cddShellRadius hq0 hq1 hC) θ

/-- The unnormalized tail scattering factor becomes trivial. -/
theorem tendsto_exp_cddTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => Complex.exp (Complex.I * (cddTailPhase q C N θ : ℂ))) atTop (𝓝 1) :=
  tendsto_exp_shellTailPhase (positiveShellFamily_cddShellRadius hq0 hq1 hC) θ

/-! ### The tail phase as the deleted-shell increment of the finite CDD phase -/

/-- Deleting the first `N` shells from a finite truncation leaves exactly the surviving shell
phases. -/
theorem geometricCDDTruncationPhase_add_sub (q C θ : ℝ) (N M : ℕ) :
    geometricCDDTruncationPhase q C θ (N + M) - geometricCDDTruncationPhase q C θ N
      = ∑ j ∈ Finset.range M, 4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C) := by
  unfold geometricCDDTruncationPhase
  rw [Finset.sum_range_add (fun k : ℕ => Real.arctan (q ^ k * Real.sinh θ / C)) N M, mul_add,
    Finset.mul_sum, Finset.mul_sum]
  ring

theorem hasSum_cddTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    HasSum (fun j : ℕ => 4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C))
      (cddTailPhase q C N θ) := by
  rw [cddTailPhase_eq_shellSum hq0 hq1 hC N θ]
  exact (summable_cddTailPhaseTerm hq0 hq1 hC N θ).hasSum

/-- The tail phase is the limit of the deleted-shell increments of the finite CDD phase. -/
theorem tendsto_geometricCDDTruncationPhase_sub
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    Tendsto (fun M => geometricCDDTruncationPhase q C θ (N + M)
        - geometricCDDTruncationPhase q C θ N) atTop (𝓝 (cddTailPhase q C N θ)) := by
  refine ((hasSum_cddTailPhase hq0 hq1 hC N θ).tendsto_sum_nat).congr fun M => ?_
  exact (geometricCDDTruncationPhase_add_sub q C θ N M).symm

/-! ## The exact decimation orbit of the geometric CDD product -/

/-- Shifting the shell index by `N` is the same as scaling the crossing coordinate by `q^N`. -/
theorem geometricCDDStep_add_eq_scale {K : Type*} [Field K] (q t : K) (N k : ℕ) :
    geometricCDDStep q t (N + k) = geometricCDDStep q (q ^ N * t) k := by
  simp only [geometricCDDStep, pow_add]
  congr 2 <;> ring

/-- Equation (18): the tail interaction factor is the decimated product
`P_{≥N}(t) = P_q(q^N t)` at every finite truncation depth. -/
theorem geometricCDDTail_prod_eq {K : Type*} [Field K] (q t : K) (N M : ℕ) :
    (∏ k ∈ Finset.range M, geometricCDDStep q t (N + k))
      = geometricCDDTruncation q (q ^ N * t) M := by
  rw [geometricCDDTruncation]
  exact Finset.prod_congr rfl fun k _ => geometricCDDStep_add_eq_scale q t N k

/-! ## Connection to the Hausdorff positivity cone -/

/-- The finite shell truncations of the normalized tail coupling sequence are completely monotone:
they lie in the Hausdorff cone generated by the shell radii. -/
theorem cddTailFiniteCoupling_completelyMonotone
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N M m k : ℕ) :
    0 ≤ (-1) ^ k * ((fwdDiff 1)^[k] (fun n : ℕ => ∑ j ∈ Finset.range M,
      cddTailWeight q C N j * cddShellRadius q C (N + j) ^ (2 * n)) m) :=
  cddCoupling_completelyMonotone (Finset.range M) (cddTailWeight q C N)
    (fun j => cddShellRadius q C (N + j))
    (fun j _ => cddTailWeight_nonneg hq0 hq1 hC N j)
    (fun _ _ => (cddShellRadius_pos hq0 hq1 hC _).le)
    (fun _ _ => (cddShellRadius_lt_one hq0 hq1 hC _).le) m k

end

end GaloisForLFunctions.HTGeometry
