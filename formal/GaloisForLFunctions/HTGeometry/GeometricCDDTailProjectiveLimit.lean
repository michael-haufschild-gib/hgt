import GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac
import GaloisForLFunctions.HTGeometry.GeometricCDDConstraint
import GaloisForLFunctions.HTGeometry.HausdorffPositiveCddCone
import GaloisForLFunctions.HTGeometry.SectorPowerMassLower

/-!
# The deep geometric CDD tail has a flat projective limit

Fix `0 < q < 1` and `C > 1`.  The geometric paired-shell divisor has thresholds
`B_j = C q^{-j} = cosh η_j` and radii `r_j = B_j - sqrt(B_j² - 1) = exp(-η_j) ∈ (0,1)`.  Its
Hausdorff coupling measure is the purely atomic measure `ν = ∑_j r_j δ_{r_j²}`, and the tail
obtained by deleting the first `N` shells has finite positive mass `M_N = ∑_{j ≥ N} r_j`.

This module proves, unconditionally:

* **A.** the normalized tail `ν̂_N = M_N⁻¹ ν_{≥N}` converges weak-* to `δ_0`;
* **B.** its moments satisfy `b_0 = 1` and `0 ≤ b_m ≤ r_N^{2m} → 0` for `m ≥ 1`, so every
  normalized odd higher-spin coupling `8(-1)^m b_m/(2m+1)` except the spin-one coupling `8`
  collapses to zero;
* **C.** with the phase kernel `K(y,θ) = 4(arctan(√y e^θ) − arctan(√y e^{−θ}))/√y`, extended by
  `K(0,θ) = 8 sinh θ`, the normalized tail phase obeys the explicit estimate
  `|Σ̂_N(θ) − 8 sinh θ| ≤ (8/3) r_N² cosh 3θ`, hence converges to `8 sinh θ` uniformly on every
  bounded rapidity set, while the *unnormalized* tail phase converges to `0`;
* the exact decimation identity `∏_{k<M} step_q(t, N+k) = ∏_{k<M} step_q(q^N t, k)` for the
  geometric CDD factors.

The single shell atom reproduces the shell phase of `geometricCDDTruncationPhase`:
`r_j · K(r_j², θ) = 4 arctan(q^j sinh θ / C)`.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Cubic control of the arctangent -/

/-- On the nonnegative half-line the arctangent lies below the identity. -/
theorem arctan_le_self {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  have h := abs_arctan_le_abs t
  rwa [abs_of_nonneg ht, abs_of_nonneg (Real.arctan_nonneg.mpr ht)] at h

/-- **Cubic Taylor control of the arctangent.**  For `t ≥ 0` the defect `t - arctan t` is at most
`t³/3`.  The proof is monotonicity of `w ↦ w³/3 - w + arctan w`, whose derivative is
`w⁴/(1+w²) ≥ 0`. -/
theorem sub_arctan_le_cube_div_three {t : ℝ} (ht : 0 ≤ t) :
    t - Real.arctan t ≤ t ^ 3 / 3 := by
  have hmono : MonotoneOn (fun w : ℝ => w ^ 3 / 3 - w + Real.arctan w) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (((continuous_pow 3).div_const 3).sub continuous_id).add
        Real.continuous_arctan |>.continuousOn
    · intro u _
      exact ((((differentiable_pow 3).div_const 3).sub differentiable_id).add
        Real.differentiable_arctan u).differentiableWithinAt
    · intro u _
      have h1 : HasDerivAt (fun w : ℝ => w ^ 3 / 3) (u ^ 2) u := by
        have h := (hasDerivAt_pow 3 u).div_const 3
        convert h using 1
        push_cast
        ring
      have h2 : HasDerivAt (fun w : ℝ => w) 1 u := hasDerivAt_id u
      have h3 := Real.hasDerivAt_arctan u
      have hd : deriv (fun w : ℝ => w ^ 3 / 3 - w + Real.arctan w) u
          = u ^ 2 - 1 + 1 / (1 + u ^ 2) := ((h1.sub h2).add h3).deriv
      rw [hd]
      have hkey : u ^ 2 - 1 + 1 / (1 + u ^ 2) = u ^ 4 / (1 + u ^ 2) := by
        have hpos : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
        field_simp
        ring
      rw [hkey]
      positivity
  have h0 := hmono Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  simp only [Real.arctan_zero] at h0
  norm_num at h0
  linarith

/-- Two-sided cubic Taylor control of the arctangent. -/
theorem abs_arctan_sub_self_le_cube (t : ℝ) : |Real.arctan t - t| ≤ |t| ^ 3 / 3 := by
  rcases le_total 0 t with ht | ht
  · have h1 : Real.arctan t - t ≤ 0 := by linarith [arctan_le_self ht]
    have h2 := sub_arctan_le_cube_div_three ht
    rw [abs_of_nonpos h1, abs_of_nonneg ht]
    linarith
  · have ht' : 0 ≤ -t := by linarith
    have h1 : Real.arctan (-t) ≤ -t := arctan_le_self ht'
    have h2 := sub_arctan_le_cube_div_three ht'
    rw [Real.arctan_neg] at h1 h2
    have habs : |t| = -t := abs_of_nonpos ht
    rw [habs]
    have hge : 0 ≤ Real.arctan t - t := by linarith
    rw [abs_of_nonneg hge]
    linarith

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

/-- The exact shell relation `1 + r_j² = 2 B_j r_j`, i.e. `B_j = cosh η_j` for `r_j = exp(-η_j)`. -/
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

/-! ## The tail coupling mass -/

theorem summable_cddShellRadius_shift (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    Summable fun j : ℕ => cddShellRadius q C (N + j) := by
  have hgeom : Summable fun j : ℕ => q ^ N / C * q ^ j :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  refine Summable.of_nonneg_of_le (fun j => (cddShellRadius_pos hq0 hq1 hC _).le)
    (fun j => ?_) hgeom
  calc cddShellRadius q C (N + j) ≤ q ^ (N + j) / C := cddShellRadius_le_pow_div hq0 hq1 hC _
    _ = q ^ N / C * q ^ j := by rw [pow_add]; ring

/-- The total coupling mass of the tail obtained by deleting the first `N` shells. -/
def cddTailMass (q C : ℝ) (N : ℕ) : ℝ := ∑' j : ℕ, cddShellRadius q C (N + j)

theorem cddTailMass_pos (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    0 < cddTailMass q C N := by
  have hsum := summable_cddShellRadius_shift hq0 hq1 hC N
  have h0 : cddShellRadius q C (N + 0) ≤ cddTailMass q C N :=
    hsum.le_tsum 0 fun j _ => (cddShellRadius_pos hq0 hq1 hC _).le
  have hpos := cddShellRadius_pos hq0 hq1 hC (N + 0)
  linarith

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
    Tendsto (fun N => cddTailMass q C N) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => q ^ N / (C * (1 - q))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).div_const (C * (1 - q))
  exact squeeze_zero (fun N => (cddTailMass_pos hq0 hq1 hC N).le)
    (fun N => cddTailMass_le hq0 hq1 hC N) hb

theorem tendsto_cddShellRadius (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    Tendsto (fun N => cddShellRadius q C N) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => q ^ N / C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).div_const C
  exact squeeze_zero (fun N => (cddShellRadius_pos hq0 hq1 hC N).le)
    (fun N => cddShellRadius_le_pow_div hq0 hq1 hC N) hb

/-! ## The normalized tail measure -/

/-- The normalized weight of the `j`-th surviving shell in the tail beyond level `N`. -/
def cddTailWeight (q C : ℝ) (N j : ℕ) : ℝ :=
  cddShellRadius q C (N + j) / cddTailMass q C N

theorem cddTailWeight_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N j : ℕ) :
    0 ≤ cddTailWeight q C N j :=
  div_nonneg (cddShellRadius_pos hq0 hq1 hC _).le (cddTailMass_pos hq0 hq1 hC N).le

theorem summable_cddTailWeight (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    Summable fun j : ℕ => cddTailWeight q C N j := by
  simpa [cddTailWeight, div_eq_inv_mul] using
    (summable_cddShellRadius_shift hq0 hq1 hC N).mul_left (cddTailMass q C N)⁻¹

theorem tsum_cddTailWeight (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    ∑' j : ℕ, cddTailWeight q C N j = 1 := by
  have hM := (cddTailMass_pos hq0 hq1 hC N).ne'
  have hrw : ∑' j : ℕ, cddTailWeight q C N j
      = (cddTailMass q C N)⁻¹ * ∑' j : ℕ, cddShellRadius q C (N + j) := by
    simp only [cddTailWeight, div_eq_inv_mul]
    exact (summable_cddShellRadius_shift hq0 hq1 hC N).tsum_mul_left _
  rw [hrw, ← cddTailMass, inv_mul_cancel₀ hM]

/-- The unnormalized coupling measure of the tail beyond level `N`:
`ν_{≥N} = ∑_{j ≥ N} r_j δ_{r_j²}`. -/
def cddTailMeasure (q C : ℝ) (N : ℕ) : Measure ℝ :=
  _root_.HTGeometry.countableWeightedDirac (fun j => cddShellRadius q C (N + j))
    (fun j => cddShellRadius q C (N + j) ^ 2)

/-- The normalized tail measure `ν̂_N = M_N⁻¹ ν_{≥N}`. -/
def cddNormalizedTailMeasure (q C : ℝ) (N : ℕ) : Measure ℝ :=
  _root_.HTGeometry.countableWeightedDirac (cddTailWeight q C N)
    (fun j => cddShellRadius q C (N + j) ^ 2)

/-- The normalized tail measure is the tail measure rescaled by its own total mass. -/
theorem cddNormalizedTailMeasure_eq_smul (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddNormalizedTailMeasure q C N
      = ENNReal.ofReal (cddTailMass q C N)⁻¹ • cddTailMeasure q C N := by
  have hinv : (0 : ℝ) ≤ (cddTailMass q C N)⁻¹ :=
    inv_nonneg.mpr (cddTailMass_pos hq0 hq1 hC N).le
  rw [cddTailMeasure, ← _root_.HTGeometry.countableWeightedDirac_const_mul hinv,
    cddNormalizedTailMeasure]
  congr 1
  funext j
  simp [cddTailWeight, div_eq_inv_mul]

/-- The total mass of the unnormalized tail measure is `M_N`. -/
theorem cddTailMeasure_univ (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddTailMeasure q C N Set.univ = ENNReal.ofReal (cddTailMass q C N) :=
  _root_.HTGeometry.countableWeightedDirac_univ_ofReal
    (fun j => (cddShellRadius_pos hq0 hq1 hC _).le)
    (summable_cddShellRadius_shift hq0 hq1 hC N) _

theorem cddNormalizedTailMeasure_univ (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddNormalizedTailMeasure q C N Set.univ = 1 := by
  rw [cddNormalizedTailMeasure,
    _root_.HTGeometry.countableWeightedDirac_univ_ofReal
      (fun j => cddTailWeight_nonneg hq0 hq1 hC N j) (summable_cddTailWeight hq0 hq1 hC N),
    tsum_cddTailWeight hq0 hq1 hC N, ENNReal.ofReal_one]

theorem isProbabilityMeasure_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    IsProbabilityMeasure (cddNormalizedTailMeasure q C N) :=
  ⟨cddNormalizedTailMeasure_univ hq0 hq1 hC N⟩

/-- The normalized tail measure as a bundled probability law. -/
def cddTailProbability (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨cddNormalizedTailMeasure q C N, isProbabilityMeasure_cddNormalizedTailMeasure hq0 hq1 hC N⟩

@[simp]
theorem cddTailProbability_toMeasure (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    (cddTailProbability hq0 hq1 hC N : Measure ℝ) = cddNormalizedTailMeasure q C N := rfl

/-- Every atom of the tail beyond level `N` lies in `[0, r_N²]`. -/
theorem cddTailAtom_le (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N j : ℕ) :
    cddShellRadius q C (N + j) ^ 2 ≤ cddShellRadius q C N ^ 2 := by
  have h1 := cddShellRadius_antitone hq0 hq1 hC (Nat.le_add_right N j)
  have h2 := (cddShellRadius_pos hq0 hq1 hC (N + j)).le
  nlinarith

/-! ## Theorem A: the normalized tail collapses to the zero-shell ray -/

/-- Outside any ball strictly larger than `r_N²` the normalized tail carries no mass. -/
theorem cddNormalizedTailMeasure_compl_ball
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {ε : ℝ}
    (hε : cddShellRadius q C N ^ 2 < ε) :
    cddNormalizedTailMeasure q C N (Metric.ball (0 : ℝ) ε)ᶜ = 0 := by
  rw [cddNormalizedTailMeasure,
    _root_.HTGeometry.countableWeightedDirac_apply _ _
      (measurableSet_ball (x := (0 : ℝ)) (ε := ε)).compl]
  refine ENNReal.tsum_eq_zero.mpr fun j => ?_
  have hmem : cddShellRadius q C (N + j) ^ 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg (sq_nonneg (cddShellRadius q C (N + j)))]
    exact lt_of_le_of_lt (cddTailAtom_le hq0 hq1 hC N j) hε
  rw [Set.indicator_of_notMem (by simpa using hmem), mul_zero]

/-- **Theorem A.**  The normalized tail laws converge weak-* to the Dirac law at the zero shell. -/
theorem tendsto_cddTailProbability_diracProba
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) :
    Tendsto (fun N => cddTailProbability hq0 hq1 hC N) atTop (𝓝 (diracProba (0 : ℝ))) := by
  refine GaloisForLFunctions.HTGeometry.tendsto_diracProba_of_eventually_measure_nhds_eq_one
    _ _ ?_
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  have hsq : Tendsto (fun N => cddShellRadius q C N ^ 2) atTop (𝓝 0) := by
    have := (tendsto_cddShellRadius hq0 hq1 hC).pow 2
    simpa using this
  filter_upwards [hsq.eventually (eventually_lt_nhds hε)] with N hN
  haveI := isProbabilityMeasure_cddNormalizedTailMeasure hq0 hq1 hC N
  have hzero := cddNormalizedTailMeasure_compl_ball hq0 hq1 hC N hN
  have hball : cddNormalizedTailMeasure q C N (Metric.ball (0 : ℝ) ε) = 1 := by
    have hadd := measure_add_measure_compl
      (μ := cddNormalizedTailMeasure q C N)
      (measurableSet_ball (x := (0 : ℝ)) (ε := ε))
    rw [hzero, add_zero, measure_univ] at hadd
    exact hadd
  have hle : (1 : ENNReal) ≤ cddNormalizedTailMeasure q C N U := by
    rw [← hball]
    exact measure_mono hsub
  exact le_antisymm (prob_le_one) hle

/-! ## Theorem B: all normalized higher-spin directions except spin one vanish -/

/-- The `m`-th moment of the normalized tail measure. -/
def cddTailMoment (q C : ℝ) (N m : ℕ) : ℝ :=
  ∑' j : ℕ, cddTailWeight q C N j * (cddShellRadius q C (N + j) ^ 2) ^ m

theorem summable_cddTailMomentTerm (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N m : ℕ) :
    Summable fun j : ℕ => cddTailWeight q C N j * (cddShellRadius q C (N + j) ^ 2) ^ m := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (summable_cddTailWeight hq0 hq1 hC N)
  · exact mul_nonneg (cddTailWeight_nonneg hq0 hq1 hC N j) (pow_nonneg (sq_nonneg _) m)
  · have hle : (cddShellRadius q C (N + j) ^ 2) ^ m ≤ 1 := by
      refine pow_le_one₀ (sq_nonneg _) ?_
      nlinarith [cddShellRadius_pos hq0 hq1 hC (N + j), cddShellRadius_lt_one hq0 hq1 hC (N + j)]
    nlinarith [cddTailWeight_nonneg hq0 hq1 hC N j]

@[simp]
theorem cddTailMoment_zero (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddTailMoment q C N 0 = 1 := by
  simpa [cddTailMoment] using tsum_cddTailWeight hq0 hq1 hC N

theorem cddTailMoment_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N m : ℕ) :
    0 ≤ cddTailMoment q C N m :=
  tsum_nonneg fun j =>
    mul_nonneg (cddTailWeight_nonneg hq0 hq1 hC N j) (pow_nonneg (sq_nonneg _) m)

/-- **Theorem B, bound.**  The `m`-th normalized tail moment is at most `r_N^{2m}`. -/
theorem cddTailMoment_le (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N m : ℕ) :
    cddTailMoment q C N m ≤ (cddShellRadius q C N ^ 2) ^ m := by
  have hbound : Summable fun j : ℕ =>
      cddTailWeight q C N j * (cddShellRadius q C N ^ 2) ^ m :=
    (summable_cddTailWeight hq0 hq1 hC N).mul_right _
  have hcmp : cddTailMoment q C N m
      ≤ ∑' j : ℕ, cddTailWeight q C N j * (cddShellRadius q C N ^ 2) ^ m := by
    refine Summable.tsum_le_tsum (fun j => ?_) (summable_cddTailMomentTerm hq0 hq1 hC N m) hbound
    have hatom := cddTailAtom_le hq0 hq1 hC N j
    have := pow_le_pow_left₀ (sq_nonneg (cddShellRadius q C (N + j))) hatom m
    nlinarith [cddTailWeight_nonneg hq0 hq1 hC N j]
  have hval : (∑' j : ℕ, cddTailWeight q C N j * (cddShellRadius q C N ^ 2) ^ m)
      = (cddShellRadius q C N ^ 2) ^ m := by
    rw [(summable_cddTailWeight hq0 hq1 hC N).tsum_mul_right, tsum_cddTailWeight hq0 hq1 hC N,
      one_mul]
  linarith [hcmp, hval.le, hval.ge]

/-- **Theorem B, collapse.**  Every moment of positive order tends to zero along the shell tail. -/
theorem tendsto_cddTailMoment (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N => cddTailMoment q C N m) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => (cddShellRadius q C N ^ 2) ^ m) atTop (𝓝 0) := by
    have hpow := (tendsto_cddShellRadius hq0 hq1 hC).pow (2 * m)
    have hzero : (0 : ℝ) ^ (2 * m) = 0 := zero_pow (by omega)
    rw [hzero] at hpow
    refine hpow.congr fun N => ?_
    rw [← pow_mul]
  exact squeeze_zero (fun N => cddTailMoment_nonneg hq0 hq1 hC N m)
    (fun N => cddTailMoment_le hq0 hq1 hC N m) hb

/-- The normalized odd higher-spin coupling `α̂_{2m+1} = 8(-1)^m b_m/(2m+1)`. -/
def cddNormalizedSpinCoupling (q C : ℝ) (N m : ℕ) : ℝ :=
  8 * (-1) ^ m * cddTailMoment q C N m / (2 * m + 1)

/-- The spin-one coupling is the fixed `T T̄` value `8` at every truncation level. -/
@[simp]
theorem cddNormalizedSpinCoupling_zero (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) :
    cddNormalizedSpinCoupling q C N 0 = 8 := by
  simp [cddNormalizedSpinCoupling, cddTailMoment_zero hq0 hq1 hC N]

/-- **Theorem B, projective direction.**  Every higher-spin coupling collapses; only the spin-one
current–current direction survives. -/
theorem tendsto_cddNormalizedSpinCoupling (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N => cddNormalizedSpinCoupling q C N m) atTop (𝓝 0) := by
  have h := (tendsto_cddTailMoment hq0 hq1 hC hm).const_mul (8 * (-1) ^ m)
  have h2 := h.div_const ((2 : ℝ) * m + 1)
  simpa [cddNormalizedSpinCoupling] using h2

/-! ## The Hausdorff phase kernel -/

/-- The Hausdorff phase kernel `K(y,θ) = 4(arctan(√y e^θ) − arctan(√y e^{−θ}))/√y`, extended by its
limiting value `K(0,θ) = 8 sinh θ` at the zero shell. -/
def cddPhaseKernel (y θ : ℝ) : ℝ :=
  if 0 < y then
    4 * (Real.arctan (Real.sqrt y * Real.exp θ)
      - Real.arctan (Real.sqrt y * Real.exp (-θ))) / Real.sqrt y
  else 8 * Real.sinh θ

@[simp]
theorem cddPhaseKernel_zero (θ : ℝ) : cddPhaseKernel 0 θ = 8 * Real.sinh θ := by
  simp [cddPhaseKernel]

/-- The arctangent difference of a reciprocal exponential pair is a single arctangent. -/
theorem arctan_sub_arctan_exp (u θ : ℝ) :
    Real.arctan (u * Real.exp θ) - Real.arctan (u * Real.exp (-θ))
      = Real.arctan (2 * u * Real.sinh θ / (1 + u ^ 2)) := by
  have hexp : Real.exp θ * Real.exp (-θ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hprod : (u * Real.exp θ) * (-(u * Real.exp (-θ))) = -u ^ 2 := by
    have : (u * Real.exp θ) * (u * Real.exp (-θ)) = u ^ 2 * (Real.exp θ * Real.exp (-θ)) := by
      ring
    nlinarith [this, hexp]
  have hlt : (u * Real.exp θ) * (-(u * Real.exp (-θ))) < 1 := by
    rw [hprod]; nlinarith [sq_nonneg u]
  have h := Real.arctan_add hlt
  rw [Real.arctan_neg] at h
  have hden : 1 - (u * Real.exp θ) * (-(u * Real.exp (-θ))) = 1 + u ^ 2 := by
    rw [hprod]; ring
  have hnum : u * Real.exp θ + -(u * Real.exp (-θ)) = 2 * u * Real.sinh θ := by
    rw [Real.sinh_eq]; ring
  rw [hden, hnum] at h
  linarith [h]

/-- Closed form of the kernel at a positive shell radius. -/
theorem cddPhaseKernel_sq {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r * cddPhaseKernel (r ^ 2) θ = 4 * Real.arctan (2 * r * Real.sinh θ / (1 + r ^ 2)) := by
  have hpos : 0 < r ^ 2 := by positivity
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  rw [cddPhaseKernel, if_pos hpos, hsqrt, arctan_sub_arctan_exp]
  field_simp

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

/-- **Uniform kernel estimate.**  `|K(y,θ) − 8 sinh θ| ≤ (8/3)|y| cosh 3θ`, so the kernel is
continuous at the zero shell with an explicit modulus. -/
theorem abs_cddPhaseKernel_sub_flat_le (y θ : ℝ) :
    |cddPhaseKernel y θ - 8 * Real.sinh θ| ≤ 8 / 3 * |y| * Real.cosh (3 * θ) := by
  rcases le_or_gt y 0 with hy | hy
  · rw [cddPhaseKernel, if_neg (not_lt.mpr hy), sub_self, abs_zero]
    have := Real.cosh_pos (3 * θ)
    positivity
  · have hu : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hu2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hexppos : ∀ x : ℝ, 0 < Real.exp x := Real.exp_pos
    have hsinh : 8 * Real.sinh θ = 4 * (Real.exp θ - Real.exp (-θ)) := by
      rw [Real.sinh_eq]; ring
    have hsplit : cddPhaseKernel y θ - 8 * Real.sinh θ
        = 4 / Real.sqrt y *
          ((Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ)
            - (Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ))) := by
      rw [cddPhaseKernel, if_pos hy, hsinh]
      field_simp
      ring
    have hA := abs_arctan_sub_self_le_cube (Real.sqrt y * Real.exp θ)
    have hB := abs_arctan_sub_self_le_cube (Real.sqrt y * Real.exp (-θ))
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt y * Real.exp θ)] at hA
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt y * Real.exp (-θ))] at hB
    have htri :
        |(Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ)
          - (Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ))|
        ≤ (Real.sqrt y * Real.exp θ) ^ 3 / 3 + (Real.sqrt y * Real.exp (-θ)) ^ 3 / 3 := by
      calc _ ≤ |Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ|
              + |Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ)| :=
            abs_sub _ _
        _ ≤ _ := by linarith
    have hcube : (Real.sqrt y * Real.exp θ) ^ 3 / 3 + (Real.sqrt y * Real.exp (-θ)) ^ 3 / 3
        = Real.sqrt y ^ 3 / 3 * (Real.exp (3 * θ) + Real.exp (-(3 * θ))) := by
      have h1 : Real.exp θ ^ 3 = Real.exp (3 * θ) := by
        rw [← Real.exp_nat_mul]; norm_num
      have h2 : Real.exp (-θ) ^ 3 = Real.exp (-(3 * θ)) := by
        rw [← Real.exp_nat_mul]; norm_num; ring_nf
      rw [mul_pow, mul_pow, h1, h2]
      ring
    have hcosh : Real.exp (3 * θ) + Real.exp (-(3 * θ)) = 2 * Real.cosh (3 * θ) := by
      rw [Real.cosh_eq]; ring
    rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 / Real.sqrt y)]
    have hfinal : 4 / Real.sqrt y * (Real.sqrt y ^ 3 / 3 * (2 * Real.cosh (3 * θ)))
        = 8 / 3 * y * Real.cosh (3 * θ) := by
      field_simp
      nlinarith [hu2, hu.le, Real.cosh_pos (3 * θ)]
    calc 4 / Real.sqrt y *
        |(Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ)
          - (Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ))|
        ≤ 4 / Real.sqrt y * (Real.sqrt y ^ 3 / 3 * (2 * Real.cosh (3 * θ))) := by
          have := htri
          rw [hcube, hcosh] at this
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 8 / 3 * y * Real.cosh (3 * θ) := hfinal
      _ = 8 / 3 * |y| * Real.cosh (3 * θ) := by rw [abs_of_pos hy]

/-- The phase kernel is continuous in the shell variable, including at the zero shell. -/
theorem continuous_cddPhaseKernel (θ : ℝ) : Continuous fun y => cddPhaseKernel y θ := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_trichotomy y 0 with h | h | h
  · have heq : ∀ᶠ z in 𝓝 y, cddPhaseKernel z θ = 8 * Real.sinh θ := by
      filter_upwards [Iio_mem_nhds h] with z hz
      rw [cddPhaseKernel, if_neg (not_lt.mpr (le_of_lt hz))]
    exact continuousAt_const.congr heq.symm
  · subst h
    have hbound : ∀ z : ℝ, ‖cddPhaseKernel z θ - 8 * Real.sinh θ‖
        ≤ 8 / 3 * |z| * Real.cosh (3 * θ) := fun z =>
      abs_cddPhaseKernel_sub_flat_le z θ
    have hg : Tendsto (fun z : ℝ => 8 / 3 * |z| * Real.cosh (3 * θ)) (𝓝 0) (𝓝 0) := by
      have : Continuous fun z : ℝ => 8 / 3 * |z| * Real.cosh (3 * θ) := by
        exact (continuous_const.mul continuous_abs).mul continuous_const
      simpa using this.tendsto 0
    have hlim : Tendsto (fun z : ℝ => cddPhaseKernel z θ - 8 * Real.sinh θ) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm hbound hg
    have := hlim.add_const (8 * Real.sinh θ)
    simp only [sub_add_cancel, zero_add] at this
    rw [ContinuousAt, cddPhaseKernel_zero]
    exact this
  · have hg : ContinuousAt (fun z : ℝ =>
        4 * (Real.arctan (Real.sqrt z * Real.exp θ)
          - Real.arctan (Real.sqrt z * Real.exp (-θ))) / Real.sqrt z) y := by
      refine ContinuousAt.div ?_ (Real.continuous_sqrt.continuousAt)
        (ne_of_gt (Real.sqrt_pos.mpr h))
      exact continuousAt_const.mul
        (((Real.continuous_arctan.comp
            (Real.continuous_sqrt.mul continuous_const)).continuousAt).sub
          ((Real.continuous_arctan.comp
            (Real.continuous_sqrt.mul continuous_const)).continuousAt))
    refine hg.congr ?_
    filter_upwards [Ioi_mem_nhds h] with z hz
    rw [cddPhaseKernel, if_pos (Set.mem_Ioi.mp hz)]

/-! ## Theorem C: the normalized phase converges to the flat direction -/

/-- The unnormalized tail phase `Σ_{≥N}(θ) = ∫ K dν_{≥N}`. -/
def cddTailPhase (q C : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, cddShellRadius q C (N + j) * cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ

/-- The normalized tail phase `Σ̂_N(θ) = ∫ K dν̂_N`. -/
def cddNormalizedTailPhase (q C : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, cddTailWeight q C N j * cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ

/-- The unnormalized tail phase is the sum of the surviving shell phases. -/
theorem cddTailPhase_eq_shellSum (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    cddTailPhase q C N θ = ∑' j : ℕ, 4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C) := by
  refine tsum_congr fun j => ?_
  exact cddShellRadius_mul_cddPhaseKernel hq0 hq1 hC (N + j) θ

theorem summable_cddNormalizedTailPhaseTerm
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    Summable fun j : ℕ =>
      cddTailWeight q C N j * (cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ
        - 8 * Real.sinh θ) := by
  refine Summable.of_norm_bounded
    ((summable_cddTailWeight hq0 hq1 hC N).mul_right
      (8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ))) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (cddTailWeight_nonneg hq0 hq1 hC N j)]
  have hker := abs_cddPhaseKernel_sub_flat_le (cddShellRadius q C (N + j) ^ 2) θ
  rw [abs_of_nonneg (sq_nonneg (cddShellRadius q C (N + j)))] at hker
  have hatom := cddTailAtom_le hq0 hq1 hC N j
  have hcosh := (Real.cosh_pos (3 * θ)).le
  have hstep : 8 / 3 * cddShellRadius q C (N + j) ^ 2 * Real.cosh (3 * θ)
      ≤ 8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ) := by nlinarith
  nlinarith [cddTailWeight_nonneg hq0 hq1 hC N j, abs_nonneg
    (cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ - 8 * Real.sinh θ)]

theorem summable_cddNormalizedTailPhaseKernel
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    Summable fun j : ℕ =>
      cddTailWeight q C N j * cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ := by
  have h1 := summable_cddNormalizedTailPhaseTerm hq0 hq1 hC N θ
  have h2 := (summable_cddTailWeight hq0 hq1 hC N).mul_right (8 * Real.sinh θ)
  have := h1.add h2
  refine this.congr fun j => ?_
  ring

/-- **Theorem C, sharp estimate.**  The normalized tail phase differs from the flat direction
`8 sinh θ` by at most `(8/3) r_N² cosh 3θ`. -/
theorem abs_cddNormalizedTailPhase_sub_flat_le
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    |cddNormalizedTailPhase q C N θ - 8 * Real.sinh θ|
      ≤ 8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ) := by
  have hflat : (∑' j : ℕ, cddTailWeight q C N j * (8 * Real.sinh θ)) = 8 * Real.sinh θ := by
    rw [(summable_cddTailWeight hq0 hq1 hC N).tsum_mul_right, tsum_cddTailWeight hq0 hq1 hC N,
      one_mul]
  have hdiff : (∑' j : ℕ, cddTailWeight q C N j *
        (cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ - 8 * Real.sinh θ))
      = cddNormalizedTailPhase q C N θ - 8 * Real.sinh θ := by
    have hsplit : (fun j : ℕ => cddTailWeight q C N j *
          (cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ - 8 * Real.sinh θ))
        = fun j : ℕ => cddTailWeight q C N j *
            cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ
          - cddTailWeight q C N j * (8 * Real.sinh θ) := by
      funext j; ring
    rw [hsplit, Summable.tsum_sub (summable_cddNormalizedTailPhaseKernel hq0 hq1 hC N θ)
      ((summable_cddTailWeight hq0 hq1 hC N).mul_right (8 * Real.sinh θ)), hflat,
      cddNormalizedTailPhase]
  rw [← hdiff]
  have hnormsum : Summable fun j : ℕ =>
      ‖cddTailWeight q C N j *
        (cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ - 8 * Real.sinh θ)‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((summable_cddTailWeight hq0 hq1 hC N).mul_right
        (8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ)))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cddTailWeight_nonneg hq0 hq1 hC N j)]
    have hker := abs_cddPhaseKernel_sub_flat_le (cddShellRadius q C (N + j) ^ 2) θ
    rw [abs_of_nonneg (sq_nonneg (cddShellRadius q C (N + j)))] at hker
    have hatom := cddTailAtom_le hq0 hq1 hC N j
    have hcosh := (Real.cosh_pos (3 * θ)).le
    have hstep : 8 / 3 * cddShellRadius q C (N + j) ^ 2 * Real.cosh (3 * θ)
        ≤ 8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ) := by nlinarith
    nlinarith [cddTailWeight_nonneg hq0 hq1 hC N j]
  have hle := norm_tsum_le_tsum_norm hnormsum
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hbnd : ∑' j : ℕ, ‖cddTailWeight q C N j *
      (cddPhaseKernel (cddShellRadius q C (N + j) ^ 2) θ - 8 * Real.sinh θ)‖
      ≤ ∑' j : ℕ, cddTailWeight q C N j *
        (8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ)) := by
    refine Summable.tsum_le_tsum (fun j => ?_) hnormsum
      ((summable_cddTailWeight hq0 hq1 hC N).mul_right _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cddTailWeight_nonneg hq0 hq1 hC N j)]
    have hker := abs_cddPhaseKernel_sub_flat_le (cddShellRadius q C (N + j) ^ 2) θ
    rw [abs_of_nonneg (sq_nonneg (cddShellRadius q C (N + j)))] at hker
    have hatom := cddTailAtom_le hq0 hq1 hC N j
    have hcosh := (Real.cosh_pos (3 * θ)).le
    have hstep : 8 / 3 * cddShellRadius q C (N + j) ^ 2 * Real.cosh (3 * θ)
        ≤ 8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ) := by nlinarith
    nlinarith [cddTailWeight_nonneg hq0 hq1 hC N j]
  refine hbnd.trans (le_of_eq ?_)
  rw [(summable_cddTailWeight hq0 hq1 hC N).tsum_mul_right, tsum_cddTailWeight hq0 hq1 hC N,
    one_mul]

/-- Pointwise convergence of the normalized tail phase to the flat direction. -/
theorem tendsto_cddNormalizedTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => cddNormalizedTailPhase q C N θ) atTop (𝓝 (8 * Real.sinh θ)) := by
  have hb : Tendsto
      (fun N : ℕ => 8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun N : ℕ => cddShellRadius q C N ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_cddShellRadius hq0 hq1 hC).pow 2
    simpa using (hsq.const_mul (8 / 3 : ℝ)).mul_const (Real.cosh (3 * θ))
  have hlim : Tendsto (fun N => cddNormalizedTailPhase q C N θ - 8 * Real.sinh θ)
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun N => abs_cddNormalizedTailPhase_sub_flat_le hq0 hq1 hC N θ) hb
  have := hlim.add_const (8 * Real.sinh θ)
  simpa using this

/-- The hyperbolic cosine is dominated by the exponential of the absolute value. -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- **Theorem C, locally uniform convergence.**  On every bounded rapidity window the normalized
tail phase converges uniformly to the flat `T T̄` direction `8 sinh θ`. -/
theorem tendstoUniformlyOn_cddNormalizedTailPhase
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (T : ℝ) :
    TendstoUniformlyOn (fun N θ => cddNormalizedTailPhase q C N θ)
      (fun θ => 8 * Real.sinh θ) atTop (Set.Icc (-T) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hb : Tendsto (fun N : ℕ => 8 / 3 * cddShellRadius q C N ^ 2 * Real.exp (3 * T))
      atTop (𝓝 0) := by
    have hsq : Tendsto (fun N : ℕ => cddShellRadius q C N ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_cddShellRadius hq0 hq1 hC).pow 2
    simpa using (hsq.const_mul (8 / 3 : ℝ)).mul_const (Real.exp (3 * T))
  filter_upwards [hb.eventually (eventually_lt_nhds hε)] with N hN θ hθ
  have hbound := abs_cddNormalizedTailPhase_sub_flat_le hq0 hq1 hC N θ
  have habs : |3 * θ| ≤ 3 * T := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    have := abs_le.mpr ⟨hθ.1, hθ.2⟩
    linarith
  have hcosh : Real.cosh (3 * θ) ≤ Real.exp (3 * T) :=
    (cosh_le_exp_abs (3 * θ)).trans (Real.exp_le_exp.mpr habs)
  have hstep : 8 / 3 * cddShellRadius q C N ^ 2 * Real.cosh (3 * θ)
      ≤ 8 / 3 * cddShellRadius q C N ^ 2 * Real.exp (3 * T) := by
    have := sq_nonneg (cddShellRadius q C N)
    nlinarith
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- **Theorem C, exponentiated form.**  The normalized tail scattering factor converges to the
universal flat dressing `exp(8 i sinh θ)`. -/
theorem tendsto_exp_cddNormalizedTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => Complex.exp (Complex.I * (cddNormalizedTailPhase q C N θ : ℂ))) atTop
      (𝓝 (Complex.exp (Complex.I * ((8 * Real.sinh θ : ℝ) : ℂ)))) := by
  have hreal := tendsto_cddNormalizedTailPhase hq0 hq1 hC θ
  have hcast : Tendsto (fun N => ((cddNormalizedTailPhase q C N θ : ℝ) : ℂ)) atTop
      (𝓝 ((8 * Real.sinh θ : ℝ) : ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact (Complex.continuous_exp.continuousAt.tendsto).comp
    ((continuous_const.mul continuous_id).continuousAt.tendsto.comp hcast)

/-! ### The unnormalized tail is asymptotically trivial -/

theorem summable_cddTailPhaseTerm (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    Summable fun j : ℕ => 4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C) := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  refine Summable.of_norm_bounded
    (((summable_geometric_of_lt_one hq0.le hq1).mul_left
      (4 * |Real.sinh θ| * q ^ N / C))) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  have hat := abs_arctan_le_abs (q ^ (N + j) * Real.sinh θ / C)
  have habs : |q ^ (N + j) * Real.sinh θ / C| = q ^ N * q ^ j * |Real.sinh θ| / C := by
    rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt (pow_pos hq0 _)),
      abs_of_nonneg hCpos.le, pow_add]
  rw [habs] at hat
  have : 4 * |Real.arctan (q ^ (N + j) * Real.sinh θ / C)|
      ≤ 4 * (q ^ N * q ^ j * |Real.sinh θ| / C) := by linarith
  refine this.trans (le_of_eq ?_)
  field_simp

/-- Uniform decay of the unnormalized tail phase. -/
theorem abs_cddTailPhase_le (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    |cddTailPhase q C N θ| ≤ 4 * |Real.sinh θ| * q ^ N / (C * (1 - q)) := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  rw [cddTailPhase_eq_shellSum hq0 hq1 hC N θ]
  have hnorm : Summable fun j : ℕ => ‖4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C)‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((summable_geometric_of_lt_one hq0.le hq1).mul_left (4 * |Real.sinh θ| * q ^ N / C))
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
  have hle := norm_tsum_le_tsum_norm hnorm
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hcmp : ∑' j : ℕ, ‖4 * Real.arctan (q ^ (N + j) * Real.sinh θ / C)‖
      ≤ ∑' j : ℕ, 4 * |Real.sinh θ| * q ^ N / C * q ^ j := by
    refine Summable.tsum_le_tsum (fun j => ?_) hnorm
      ((summable_geometric_of_lt_one hq0.le hq1).mul_left _)
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
  refine hcmp.trans (le_of_eq ?_)
  rw [(summable_geometric_of_lt_one hq0.le hq1).tsum_mul_left,
    tsum_geometric_of_lt_one hq0.le hq1]
  field_simp

/-- The unnormalized tail phase vanishes in the deep-shell limit. -/
theorem tendsto_cddTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => cddTailPhase q C N θ) atTop (𝓝 0) := by
  have hCpos : (0 : ℝ) < C := lt_trans zero_lt_one hC
  have hb : Tendsto (fun N : ℕ => 4 * |Real.sinh θ| * q ^ N / (C * (1 - q))) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
    simpa using ((hpow.const_mul (4 * |Real.sinh θ|)).div_const (C * (1 - q)))
  exact squeeze_zero_norm (fun N => abs_cddTailPhase_le hq0 hq1 hC N θ) hb

/-- The unnormalized tail scattering factor becomes trivial. -/
theorem tendsto_exp_cddTailPhase (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (θ : ℝ) :
    Tendsto (fun N => Complex.exp (Complex.I * (cddTailPhase q C N θ : ℂ))) atTop (𝓝 1) := by
  have hreal := tendsto_cddTailPhase hq0 hq1 hC θ
  have hcast : Tendsto (fun N => ((cddTailPhase q C N θ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have := (Complex.continuous_exp.continuousAt.tendsto).comp
    ((continuous_const.mul continuous_id).continuousAt.tendsto.comp hcast)
  simpa using this

/-! ## Integral representations -/

theorem integrable_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (cddNormalizedTailMeasure q C N) := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine _root_.HTGeometry.integrable_countableWeightedDirac
    (fun j => cddTailWeight_nonneg hq0 hq1 hC N j) hf.aestronglyMeasurable ?_
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (cddTailWeight_nonneg hq0 hq1 hC N j) (abs_nonneg _))
    (fun j => ?_) ((summable_cddTailWeight hq0 hq1 hC N).mul_right K)
  have hmem : cddShellRadius q C (N + j) ^ 2 ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [cddShellRadius_pos hq0 hq1 hC (N + j), cddShellRadius_lt_one hq0 hq1 hC (N + j)]
  have := hK _ hmem
  rw [Real.norm_eq_abs] at this
  nlinarith [cddTailWeight_nonneg hq0 hq1 hC N j]

theorem integral_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂(cddNormalizedTailMeasure q C N)
      = ∑' j : ℕ, cddTailWeight q C N j * f (cddShellRadius q C (N + j) ^ 2) :=
  _root_.HTGeometry.integral_countableWeightedDirac
    (fun j => cddTailWeight_nonneg hq0 hq1 hC N j)
    (integrable_cddNormalizedTailMeasure hq0 hq1 hC N hf)

/-- Equation (9): the moments are the integrals of the monomials. -/
theorem integral_pow_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N m : ℕ) :
    ∫ y, y ^ m ∂(cddNormalizedTailMeasure q C N) = cddTailMoment q C N m :=
  integral_cddNormalizedTailMeasure hq0 hq1 hC N (continuous_pow m)

/-- Equation (14): the normalized phase is the kernel integral against the normalized tail. -/
theorem integral_cddPhaseKernel_cddNormalizedTailMeasure
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 < C) (N : ℕ) (θ : ℝ) :
    ∫ y, cddPhaseKernel y θ ∂(cddNormalizedTailMeasure q C N)
      = cddNormalizedTailPhase q C N θ :=
  integral_cddNormalizedTailMeasure hq0 hq1 hC N (continuous_cddPhaseKernel θ)

/-! ## The exact decimation orbit of the geometric CDD product -/

/-- Shifting the shell index by `N` is the same as scaling the crossing coordinate by `q^N`. -/
theorem geometricCDDStep_add_eq_scale {K : Type*} [Field K] (q t : K) (N k : ℕ) :
    geometricCDDStep q t (N + k) = geometricCDDStep q (q ^ N * t) k := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show N + 1 + k = (N + k) + 1 by ring, geometricCDDStep_succ_eq_scale, ih]
      simp only [geometricCDDStep, pow_succ]
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
    (fun j _ => (cddShellRadius_pos hq0 hq1 hC _).le)
    (fun j _ => (cddShellRadius_lt_one hq0 hq1 hC _).le) m k

end

end GaloisForLFunctions.HTGeometry
