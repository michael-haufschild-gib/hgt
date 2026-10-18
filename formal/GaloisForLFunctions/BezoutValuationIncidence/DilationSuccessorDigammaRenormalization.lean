import GaloisForLFunctions.BezoutValuationIncidence.DilationSuccessorSectorHarmonicClassification
import GaloisForLFunctions.HTGeometry.GammaDigammaShiftAnchor
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# Explicit digamma finite parts of dilation successor sectors

The existing finite Gauss-series identity supplies the reciprocal-progression
constant, and the existing digamma shift anchor supplies its inverse-horizon
error bound. Applying these to the complete successor fiber yields an explicit
constant and convergence rate. The finite-horizon boundary correction contributes
`-successorSectorMean / (p*q)` to that constant.
-/

open Finset RHTower Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- The finite part of a reciprocal progression, expressed using the existing Gauss series. -/
def progressionDigammaConstant (L d : ℕ) : ℝ :=
  -((Complex.digamma (((d : ℝ) / (L : ℝ) : ℝ) : ℂ)).re +
    Real.eulerMascheroniConstant) / (L : ℝ)

/-- A direct coordinate form of the corpus's exact finite Gauss-series identity. -/
theorem progressionHarmonicSum_sub_harmonic_eq_digamma_shift
    {L d : ℕ} (hL : 0 < L) (hd : 0 < d) (N : ℕ) :
    progressionHarmonicSum L d N - (harmonic N : ℝ) / (L : ℝ) -
      progressionDigammaConstant L d =
      (Complex.digamma ((((d : ℝ) / (L : ℝ) : ℝ) : ℂ) + N) -
        Complex.digamma ((N : ℂ) + 1)).re / (L : ℝ) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hz : 0 < ((((d : ℝ) / (L : ℝ) : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    positivity
  have hsum :
      (∑ k ∈ range N,
        gaussDigammaSeriesTerm ((((d : ℝ) / (L : ℝ) : ℝ) : ℂ)) k) =
      (((harmonic N : ℝ) : ℂ) -
        (L : ℂ) * ((progressionHarmonicSum L d N : ℝ) : ℂ)) := by
    rw [RHTower.harmonic_cast_eq]
    simp only [gaussDigammaSeriesTerm, progressionHarmonicSum, Complex.ofReal_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hdenr : (k : ℝ) * L + d ≠ 0 := by positivity
    have hargr : (d : ℝ) / L + k ≠ 0 := by positivity
    have hrec : (1 : ℝ) / ((d : ℝ) / L + k) =
        (L : ℝ) * (1 / ((k : ℝ) * L + d)) := by
      field_simp [hLr.ne', hdenr, hargr]
      ring
    have hrecC := congrArg (fun x : ℝ => (x : ℂ)) hrec
    push_cast at hrecC
    push_cast
    rw [hrecC]
  have hbase := congrArg Complex.re
    (sum_gaussDigammaSeriesTerm_eq_digamma_shift hz N)
  rw [hsum] at hbase
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero,
    sub_zero] at hbase
  rw [progressionDigammaConstant]
  simp only [Complex.sub_re]
  field_simp [hLr.ne']
  nlinarith [hbase]

/-- The existing digamma anchor gives an explicit progression-tail bound. -/
theorem abs_progressionHarmonicSum_sub_harmonic_sub_digamma_le
    {L d N : ℕ} (hL : 0 < L) (hd : 0 < d) (hN : 1 ≤ N) :
    |progressionHarmonicSum L d N - (harmonic N : ℝ) / (L : ℝ) -
      progressionDigammaConstant L d| ≤
      ‖((((d : ℝ) / (L : ℝ) : ℝ) : ℂ) - 1)‖ / ((L : ℝ) * N) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hz : 0 ≤ ((((d : ℝ) / (L : ℝ) : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    positivity
  have hanchor := GaloisForLFunctions.HTGeometry.norm_digamma_shift_sub_le hz hN
  rw [add_comm (1 : ℂ) (N : ℂ)] at hanchor
  rw [progressionHarmonicSum_sub_harmonic_eq_digamma_shift hL hd N,
    abs_div, abs_of_pos hLr]
  calc
    _ ≤ ‖Complex.digamma ((((d : ℝ) / (L : ℝ) : ℝ) : ℂ) + N) -
          Complex.digamma ((N : ℂ) + 1)‖ / (L : ℝ) :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hLr.le
    _ ≤ (‖((((d : ℝ) / (L : ℝ) : ℝ) : ℂ) - 1)‖ / (N : ℝ)) / (L : ℝ) :=
      div_le_div_of_nonneg_right hanchor hLr.le
    _ = _ := by ring

/-- The explicit finite part of the complete successor sector. -/
def successorSectorDigammaConstant (r p q a b : ℕ) : ℝ :=
  (∑ t ∈ range r, successorFiberAmplitude r p q a b t *
    progressionDigammaConstant (p * q * r) (p * (a + q * t))) -
    successorSectorMean r p q / ((p : ℝ) * q)

/-- The finite coefficient controlling the digamma tail of this sector. -/
def successorSectorDigammaTailMass (r p q a b : ℕ) : ℝ :=
  ∑ t ∈ range r, |successorFiberAmplitude r p q a b t| *
    ‖(((((p * (a + q * t) : ℕ) : ℝ) / ((p * q * r : ℕ) : ℝ) : ℝ) : ℂ) - 1)‖

private theorem successor_sector_centered_remainder
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) (N : ℕ) :
    ramanujanDilationLagSector Q.value p q (p * q * (Q.value * N)) 1 -
        successorSectorMean Q.value p q / ((p : ℝ) * q) * (harmonic N : ℝ) -
        successorSectorDigammaConstant Q.value p q a b =
      (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t *
        (progressionHarmonicSum (p * q * Q.value) (p * (a + q * t)) N -
          (harmonic N : ℝ) / ((p * q * Q.value : ℕ) : ℝ) -
          progressionDigammaConstant (p * q * Q.value) (p * (a + q * t)))) +
      successorSectorMean Q.value p q /
        ((p : ℝ) * q * (((p * q * (Q.value * N) : ℕ) : ℝ) + 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr0 : (Q.value : ℝ) ≠ 0 := by exact_mod_cast Q.positive.ne'
  have hden : (p : ℝ) * q * (Q.value * N) + 1 ≠ 0 := by positivity
  rw [ramanujanDilationLagSector_one_eq_period_blocks Q hp hq ha haq hb hab N,
    successorSectorDigammaConstant]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [successorFiberAmplitude_sum_range_selected Q hab]
  push_cast
  field_simp [hp0, hq0, hr0, hden]
  ring

/-- Exact successor-sector renormalization, using the existing finite Gauss identity. -/
theorem successor_sector_sub_harmonic_eq_digamma_tail
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) (N : ℕ) :
    ramanujanDilationLagSector Q.value p q (p * q * (Q.value * N)) 1 -
        successorSectorMean Q.value p q / ((p : ℝ) * q) * (harmonic N : ℝ) -
        successorSectorDigammaConstant Q.value p q a b =
      (∑ t ∈ range Q.value, successorFiberAmplitude Q.value p q a b t *
        (Complex.digamma
            (((((p * (a + q * t) : ℕ) : ℝ) / ((p * q * Q.value : ℕ) : ℝ) : ℝ) : ℂ) + N) -
          Complex.digamma ((N : ℂ) + 1)).re / ((p * q * Q.value : ℕ) : ℝ)) +
      successorSectorMean Q.value p q /
        ((p : ℝ) * q * (((p * q * (Q.value * N) : ℕ) : ℝ) + 1)) := by
  rw [successor_sector_centered_remainder Q hp hq ha haq hb hab N]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [progressionHarmonicSum_sub_harmonic_eq_digamma_shift
    (Nat.mul_pos (Nat.mul_pos hp hq) Q.positive) (by positivity) N]
  ring

/-- An explicit inverse-horizon bound for the complete centered successor sector. -/
theorem abs_successor_sector_sub_harmonic_sub_digamma_le
    (Q : CGLPositiveModulus) {p q a b N : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) (hN : 1 ≤ N) :
    |ramanujanDilationLagSector Q.value p q (p * q * (Q.value * N)) 1 -
        successorSectorMean Q.value p q / ((p : ℝ) * q) * (harmonic N : ℝ) -
        successorSectorDigammaConstant Q.value p q a b| ≤
      successorSectorDigammaTailMass Q.value p q a b /
        (((p * q * Q.value : ℕ) : ℝ) * N) +
      |successorSectorMean Q.value p q| /
        ((p : ℝ) * q * (((p * q * (Q.value * N) : ℕ) : ℝ) + 1)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [successor_sector_centered_remainder Q hp hq ha haq hb hab N]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ t ∈ range Q.value, |successorFiberAmplitude Q.value p q a b t| *
          |progressionHarmonicSum (p * q * Q.value) (p * (a + q * t)) N -
            (harmonic N : ℝ) / ((p * q * Q.value : ℕ) : ℝ) -
            progressionDigammaConstant (p * q * Q.value) (p * (a + q * t))| := by
          simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
            (fun t => successorFiberAmplitude Q.value p q a b t *
              (progressionHarmonicSum (p * q * Q.value) (p * (a + q * t)) N -
                (harmonic N : ℝ) / ((p * q * Q.value : ℕ) : ℝ) -
                progressionDigammaConstant (p * q * Q.value) (p * (a + q * t))))
            (range Q.value)
      _ ≤ ∑ t ∈ range Q.value, |successorFiberAmplitude Q.value p q a b t| *
          (‖(((((p * (a + q * t) : ℕ) : ℝ) / ((p * q * Q.value : ℕ) : ℝ) : ℝ) : ℂ) - 1)‖ /
            (((p * q * Q.value : ℕ) : ℝ) * N)) := by
          apply Finset.sum_le_sum
          intro t _
          exact mul_le_mul_of_nonneg_left
            (abs_progressionHarmonicSum_sub_harmonic_sub_digamma_le
              (Nat.mul_pos (Nat.mul_pos hp hq) Q.positive) (by positivity) hN)
            (abs_nonneg _)
      _ = _ := by
          simp only [successorSectorDigammaTailMass, Finset.sum_div, mul_div_assoc]
  · rw [abs_div, abs_of_pos (by positivity :
      0 < (p : ℝ) * q * (((p * q * (Q.value * N) : ℕ) : ℝ) + 1))]

/-- The centered complete sector converges to its explicit digamma finite part. -/
theorem tendsto_successor_sector_sub_harmonic
    (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ha : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (hab : p * a = q * b + 1) :
    Tendsto (fun K : ℕ =>
      ramanujanDilationLagSector Q.value p q (p * q * (Q.value * (K + 1))) 1 -
        successorSectorMean Q.value p q / ((p : ℝ) * q) * (harmonic (K + 1) : ℝ))
      atTop (nhds (successorSectorDigammaConstant Q.value p q a b)) := by
  have hprod : 1 ≤ p * q * Q.value := Nat.mul_pos (Nat.mul_pos hp hq) Q.positive
  have hH : Tendsto (fun K : ℕ => p * q * (Q.value * (K + 1))) atTop atTop := by
    apply tendsto_atTop_mono (f := fun K : ℕ => K) _ tendsto_id
    intro K
    calc
      K ≤ K + 1 := by omega
      _ ≤ (p * q * Q.value) * (K + 1) := by nlinarith
      _ = _ := by ring
  have hH1 : Tendsto (fun K : ℕ => p * q * (Q.value * (K + 1)) + 1)
      atTop atTop := (tendsto_add_atTop_nat 1).comp hH
  have ht1 := (tendsto_const_div_atTop_nhds_zero_nat
    (successorSectorDigammaTailMass Q.value p q a b)).comp hH
  have ht2 := (tendsto_const_div_atTop_nhds_zero_nat
    (|successorSectorMean Q.value p q| / ((p : ℝ) * q))).comp hH1
  have ht : Tendsto (fun K : ℕ =>
      successorSectorDigammaTailMass Q.value p q a b /
          (((p * q * Q.value : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ)) +
        |successorSectorMean Q.value p q| /
          ((p : ℝ) * q * (((p * q * (Q.value * (K + 1)) : ℕ) : ℝ) + 1)))
      atTop (nhds 0) := by
    convert ht1.add ht2 using 1
    · funext K
      simp only [Function.comp_def, div_div, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, mul_assoc]
    · simp
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  exact squeeze_zero (fun K => abs_nonneg _)
    (fun K => abs_successor_sector_sub_harmonic_sub_digamma_le
      Q hp hq ha haq hb hab (by omega : 1 ≤ K + 1)) ht

/-- No-hypothesis capstone: consecutive scales have an explicit sector constant and rate. -/
theorem consecutive_scale_successor_digamma_coupling (r n K : ℕ) :
    |ramanujanDilationLagSector (r + 2) (n + 2) (n + 3)
        ((n + 2) * (n + 3) * ((r + 2) * (K + 1))) 1 -
      successorSectorMean (r + 2) (n + 2) (n + 3) /
          (((n + 2 : ℕ) : ℝ) * (n + 3 : ℕ)) * (harmonic (K + 1) : ℝ) -
      successorSectorDigammaConstant (r + 2) (n + 2) (n + 3) (n + 2) (n + 1)| ≤
      successorSectorDigammaTailMass (r + 2) (n + 2) (n + 3) (n + 2) (n + 1) /
        ((((n + 2) * (n + 3) * (r + 2) : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ)) +
      |successorSectorMean (r + 2) (n + 2) (n + 3)| /
        (((n + 2 : ℕ) : ℝ) * (n + 3 : ℕ) *
          (((((n + 2) * (n + 3) * ((r + 2) * (K + 1))) : ℕ) : ℝ) + 1)) := by
  exact abs_successor_sector_sub_harmonic_sub_digamma_le
    ⟨r + 2, by omega⟩ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by ring : (n + 2) * (n + 2) = (n + 3) * (n + 1) + 1) (by omega)

/-- Consecutive scales supply an unconditional family of explicit centered-sector limits. -/
theorem tendsto_consecutive_scale_successor_sub_harmonic (r n : ℕ) :
    Tendsto (fun K : ℕ =>
      ramanujanDilationLagSector (r + 2) (n + 2) (n + 3)
          ((n + 2) * (n + 3) * ((r + 2) * (K + 1))) 1 -
        successorSectorMean (r + 2) (n + 2) (n + 3) /
          (((n + 2 : ℕ) : ℝ) * (n + 3 : ℕ)) * (harmonic (K + 1) : ℝ))
      atTop (nhds (successorSectorDigammaConstant
        (r + 2) (n + 2) (n + 3) (n + 2) (n + 1))) := by
  exact tendsto_successor_sector_sub_harmonic
    ⟨r + 2, by omega⟩ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by ring : (n + 2) * (n + 2) = (n + 3) * (n + 1) + 1)

end
end GaloisForLFunctions.BezoutValuationIncidence
