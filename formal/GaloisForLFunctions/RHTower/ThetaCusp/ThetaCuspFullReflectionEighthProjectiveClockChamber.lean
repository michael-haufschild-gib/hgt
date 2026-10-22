import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthModularSeam
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A rational physical chamber for the rank-three projective clock

The positive theta trajectory has normalized modular-lambda clock

`z(x) = -(thetaCuspModularODEState Z x).re`.

This module proves `z(x) < 3/10` throughout `0 < x < 137/2000`, the compact interval left open
by the rank-three reflected eighth-curvature route.  Proof is source-only and computation-free.

Key improvement over earlier seam enclosure is geometric majorant

`exp (-pi * (n+1)^(2 : ℕ)) <= q^(3n+1)`,

which gives `theta_3(i) < 2173/2000` and hence
`R(0)^(2 : ℕ) < (600/137)^(2 : ℕ)`.  Decrease of modular discriminant gap bounds absolute derivative of
`Z` by `600/137`; mean-value theorem then gives desired rational clock cap.

This chamber theorem does not assert positivity of rank-three projective drift.  It removes
trajectory-localization premise needed by subsequent exact polynomial argument.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial HurwitzZeta

namespace RHTower

noncomputable section

/-- Sharpened exact upper enclosure for self-dual theta mass. -/
theorem thetaCuspSelfDualThetaMass_lt_2173_div_2000 :
    thetaCuspSelfDualThetaMass < (2173 / 2000 : ℝ) := by
  let q : ℝ := (0.0432139182638 : ℝ)
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hqexp : Real.exp (-Real.pi) ≤ q := by
    simpa [q] using exp_neg_pi_rationalEnclosure_upper
  have hterm (n : ℕ) :
      Real.exp (-Real.pi * (n + 1) ^ (2 : ℕ)) ≤ q ^ (3 * n + 1) := by
    calc
      Real.exp (-Real.pi * (n + 1) ^ (2 : ℕ)) =
          Real.exp (-Real.pi) ^ ((n + 1) ^ (2 : ℕ)) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
      _ ≤ q ^ ((n + 1) ^ (2 : ℕ)) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hqexp _
      _ ≤ q ^ (3 * n + 1) :=
        pow_le_pow_of_le_one hq0 hq1.le (by
          rcases n with _ | n
          · norm_num
          · have hself : n + 1 ≤ (n + 1) ^ (2 : ℕ) :=
              Nat.le_self_pow (by norm_num : 2 ≠ 0) (n + 1)
            nlinarith)
  have hs0 := hasSum_nat_cosKernel₀ 0 (by norm_num : (0 : ℝ) < 1)
  have hs : HasSum (fun n : ℕ =>
      2 * Real.exp (-Real.pi * (n + 1) ^ (2 : ℕ)))
      (thetaCuspSelfDualThetaMass - 1) := by
    have hs' : HasSum (fun n : ℕ =>
        2 * Real.exp (-Real.pi * (n + 1) ^ (2 : ℕ) * 1))
        (cosKernel (0 : UnitAddCircle) 1 - 1) := by
      simpa using hs0
    rw [← congrFun evenKernel_eq_cosKernel_of_zero (1 : ℝ)] at hs'
    simpa [thetaCuspSelfDualThetaMass] using hs'
  have hq3_0 : 0 ≤ q ^ (3 : ℕ) := pow_nonneg hq0 _
  have hq3_1 : q ^ (3 : ℕ) < 1 := pow_lt_one₀ hq0 hq1 (by norm_num)
  have hgeom : Summable (fun n : ℕ => 2 * q ^ (3 * n + 1)) := by
    have hbase : Summable (fun n : ℕ => (2 * q) * (q ^ (3 : ℕ)) ^ n) :=
      (summable_geometric_of_lt_one hq3_0 hq3_1).mul_left (2 * q)
    convert hbase using 1
    funext n
    rw [← pow_mul, pow_add]
    ring
  have hsum : thetaCuspSelfDualThetaMass - 1 ≤
      ∑' n : ℕ, 2 * q ^ (3 * n + 1) := by
    rw [← hs.tsum_eq]
    exact hs.summable.tsum_le_tsum (fun n => by
      gcongr
      exact hterm n) hgeom
  rw [show (∑' n : ℕ, 2 * q ^ (3 * n + 1)) = 2 * q / (1 - q ^ (3 : ℕ)) by
    rw [show (fun n : ℕ => 2 * q ^ (3 * n + 1)) =
        fun n => (2 * q) * (q ^ (3 : ℕ)) ^ n by
      funext n
      rw [← pow_mul, pow_add]
      ring,
      tsum_mul_left, tsum_geometric_of_lt_one hq3_0 hq3_1]
    ring] at hsum
  norm_num [q] at hsum ⊢
  linarith

/-- Squared self-dual modular scale is below exact derivative threshold `(600/137)^(2 : ℕ)`. -/
theorem thetaCuspSelfDualModularScale_sq_lt_projectiveClockThreshold :
    thetaCuspSelfDualModularScale ^ (2 : ℕ) < (360000 / 18769 : ℝ) := by
  have hp : Real.pi < (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have hm := thetaCuspSelfDualThetaMass_lt_2173_div_2000
  have hm0 : 0 ≤ thetaCuspSelfDualThetaMass := by
    have hlow :=
      thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
    linarith
  rw [thetaCuspSelfDualModularScale]
  calc
    (Real.pi * thetaCuspSelfDualThetaMass ^ (4 : ℕ)) ^ (2 : ℕ) =
        Real.pi ^ (2 : ℕ) * thetaCuspSelfDualThetaMass ^ (8 : ℕ) := by ring
    _ < (31416 / 10000 : ℝ) ^ (2 : ℕ) * (2173 / 2000 : ℝ) ^ (8 : ℕ) := by gcongr
    _ < (360000 / 18769 : ℝ) := by norm_num

/-- Modular-lambda clock speed is uniformly bounded on positive physical half-line. -/
theorem norm_deriv_thetaCuspModularODEState_Z_re_le_600_div_137
    {x : ℝ} (hx : 0 ≤ x) :
    ‖deriv
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re) x‖ ≤
      (600 / 137 : ℝ) := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let Z := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re
  let A := 1 - Z ^ (2 : ℕ)
  have hR : 0 < R := by
    simpa [R] using thetaCuspModularODEState_R_re_pos x
  have hZ := thetaCuspModularODEState_Z_re_mem_Ioo x
  have hA : 0 < A := by
    have hprod : 0 < (1 - Z) * (1 + Z) := by
      apply mul_pos
      · dsimp [Z]
        linarith [hZ.2]
      · dsimp [Z]
        linarith [hZ.1]
    dsimp [A]
    nlinarith
  have hA_le : A ≤ 1 := by
    dsimp [A]
    nlinarith [sq_nonneg Z]
  have hgap_pos := thetaCuspModularGapAmplitude_pos x
  have hgap_le :
      thetaCuspModularGapAmplitude x ≤ thetaCuspSelfDualModularScale ^ (2 : ℕ) := by
    rcases hx.eq_or_lt with rfl | hxpos
    · rw [thetaCuspModularGapAmplitude_zero]
    · exact (thetaCuspModularGapAmplitude_lt_selfDual_of_pos hxpos).le
  have hgap_eq : thetaCuspModularGapAmplitude x = R ^ (2 : ℕ) * A := by
    rfl
  have hd_sq_lt : (R * A) ^ (2 : ℕ) < (360000 / 18769 : ℝ) := by
    have hscale := thetaCuspSelfDualModularScale_sq_lt_projectiveClockThreshold
    rw [hgap_eq] at hgap_pos hgap_le
    nlinarith [mul_nonneg (sq_nonneg R) hA.le]
  rw [(hasDerivAt_thetaCuspModularODEState_Z_re x).deriv,
    Real.norm_eq_abs]
  change |(-R) * A| ≤ (600 / 137 : ℝ)
  rw [abs_mul, abs_neg, abs_of_pos hR, abs_of_pos hA]
  nlinarith

/-- On full missing compact interval, positive normalized modular-lambda clock lies below `3/10`. -/
theorem neg_thetaCuspModularODEState_Z_re_lt_three_tenths
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    -(thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re <
      (3 / 10 : ℝ) := by
  let z : ℝ → ℝ := fun y =>
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re
  have hmv : ‖z x - z 0‖ ≤
      (600 / 137 : ℝ) * ‖x - 0‖ := by
    exact (convex_Icc 0 x).norm_image_sub_le_of_norm_deriv_le
      (fun y _ => by
        dsimp [z]
        exact (hasDerivAt_thetaCuspModularODEState_Z_re y).differentiableAt)
      (fun y hy => by
        dsimp [z]
        exact norm_deriv_thetaCuspModularODEState_Z_re_le_600_div_137 hy.1)
      (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩)
  have hZ := thetaCuspModularODEState_Z_re_mem_Ioo_neg_zero hx0
  have hz0 : z 0 = 0 := by simp [z]
  rw [hz0, sub_zero, Real.norm_eq_abs, abs_of_neg hZ.2] at hmv
  simp only [sub_zero, Real.norm_eq_abs, abs_of_pos hx0] at hmv
  nlinarith

end

end RHTower
