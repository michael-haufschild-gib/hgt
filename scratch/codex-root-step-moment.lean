import GaloisForLFunctions.HTGeometry.StepProfileMellinTransform
import GaloisForLFunctions.HTGeometry.MellinAntiderivativeStep

noncomputable section
open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- A summable bound on unit-window masses makes a weighted step profile integrable. -/
theorem integrableOn_floor_mul_of_summable
    (R : ℕ → ℝ) (w : ℝ → ℝ) (B : ℕ → ℝ)
    (hw : ContinuousOn w (Ici (1 : ℝ)))
    (hB : ∀ k : ℕ, ∀ x ∈ Ico ((k : ℝ) + 1) ((k : ℝ) + 2), |w x| ≤ B k)
    (hs : Summable (fun k : ℕ => |R (k + 1)| * B k)) :
    IntegrableOn (fun x : ℝ => R ⌊x⌋₊ * w x) (Ioi (1 : ℝ)) := by
  have hcell : ∀ k : ℕ, IntegrableOn (fun x : ℝ => R ⌊x⌋₊ * w x)
      (Ico ((k : ℝ) + 1) ((k : ℝ) + 2)) := by
    intro k
    have hsub : Icc ((k : ℝ) + 1) ((k : ℝ) + 2) ⊆ Ici (1 : ℝ) := by
      intro x hx
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact (show (1 : ℝ) ≤ x by linarith [hx.1])
    have hc : ContinuousOn (fun x : ℝ => R (k + 1) * w x)
        (Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) :=
      continuousOn_const.mul (hw.mono hsub)
    have hi := (hc.integrableOn_Icc (μ := volume)).mono_set Ico_subset_Icc_self
    exact hi.congr_fun (by
      intro x hx
      change R (k + 1) * w x = R ⌊x⌋₊ * w x
      rw [floor_eq_of_mem_unitWindow hx]) measurableSet_Ico
  have hmass : ∀ k : ℕ,
      (∫ x in Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
          ‖R ⌊x⌋₊ * w x‖) ≤ |R (k + 1)| * B k := by
    intro k
    have hconst : IntegrableOn (fun _ : ℝ => |R (k + 1)| * B k)
        (Ico ((k : ℝ) + 1) ((k : ℝ) + 2)) := by
      exact integrableOn_const (hs := by simp [Real.volume_Ico]) (hC := enorm_ne_top)
    have hbnd : ∀ x ∈ Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
        ‖R ⌊x⌋₊ * w x‖ ≤ |R (k + 1)| * B k := by
      intro x hx
      rw [floor_eq_of_mem_unitWindow hx]
      simpa [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_left (hB k x hx) (abs_nonneg (R (k + 1)))
    calc
      _ ≤ ∫ x in Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
          (|R (k + 1)| * B k) :=
        setIntegral_mono_on (hcell k).norm hconst measurableSet_Ico hbnd
      _ = |R (k + 1)| * B k := by
        simp
        ring
  have hmasssum : Summable (fun k : ℕ =>
      ∫ x in Ico ((k : ℝ) + 1) ((k : ℝ) + 2), ‖R ⌊x⌋₊ * w x‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
      hmass hs
  have hIci : IntegrableOn (fun x : ℝ => R ⌊x⌋₊ * w x) (Ici (1 : ℝ)) := by
    rw [← iUnion_unitWindow]
    exact integrableOn_iUnion_of_summable_integral_norm hcell hmasssum
  exact hIci.mono_set (by intro x hx; exact (Set.mem_Ioi.mp hx).le)

/-- Exact logarithmic boundary weight for a summatory step profile. -/
theorem integrableOn_floor_log_weight_of_summable (R : ℕ → ℝ) (j : ℕ)
    (hs : Summable (fun k : ℕ =>
      |R (k + 1)| * (1 + Real.log ((k : ℝ) + 2)) ^ j /
        (((k : ℝ) + 1) ^ (2 : ℕ)))) :
    IntegrableOn (fun x : ℝ => R ⌊x⌋₊ *
      ((1 + Real.log x) ^ j / x ^ (2 : ℕ))) (Ioi (1 : ℝ)) := by
  have hcont : ContinuousOn
      (fun x : ℝ => (1 + Real.log x) ^ j / x ^ (2 : ℕ)) (Ici (1 : ℝ)) := by
    have hlog : ContinuousOn Real.log (Ici (1 : ℝ)) :=
      Real.continuousOn_log.mono (by
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx))
    exact ((continuousOn_const.add hlog).pow j).div (continuousOn_id.pow 2)
      (by intro x hx; exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
  have hbound : ∀ k : ℕ, ∀ x ∈ Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
      |(1 + Real.log x) ^ j / x ^ (2 : ℕ)| ≤
        (1 + Real.log ((k : ℝ) + 2)) ^ j /
          (((k : ℝ) + 1) ^ (2 : ℕ)) := by
    intro k x hx
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hxpos : (0 : ℝ) < x := hk1.trans_le hx.1
    have hlognon : 0 ≤ 1 + Real.log x := by
      have : 1 ≤ x := by linarith [hx.1]
      linarith [Real.log_nonneg this]
    have hnum : (1 + Real.log x) ^ j ≤
        (1 + Real.log ((k : ℝ) + 2)) ^ j := by
      have hlog := Real.log_le_log hxpos hx.2.le
      gcongr
    have hden : ((k : ℝ) + 1) ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by
      gcongr
      exact hx.1
    rw [abs_of_nonneg (by positivity)]
    calc
      (1 + Real.log x) ^ j / x ^ (2 : ℕ) ≤
          (1 + Real.log x) ^ j / (((k : ℝ) + 1) ^ (2 : ℕ)) :=
        div_le_div_of_nonneg_left (pow_nonneg hlognon _) (by positivity) hden
      _ ≤ (1 + Real.log ((k : ℝ) + 2)) ^ j /
          (((k : ℝ) + 1) ^ (2 : ℕ)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
  refine integrableOn_floor_mul_of_summable R
      (fun x : ℝ => (1 + Real.log x) ^ j / x ^ (2 : ℕ))
      (fun k : ℕ => (1 + Real.log ((k : ℝ) + 2)) ^ j /
        (((k : ℝ) + 1) ^ (2 : ℕ))) hcont hbound ?_
  simpa only [mul_div_assoc] using hs

/-- The one-cell logarithmic shift costs only a fixed factor at every power. -/
theorem summable_shifted_log_weight_of_log_power (R : ℕ → ℝ) (j : ℕ)
    (hzero : Summable (fun k : ℕ =>
      |R (k + 1)| / (((k : ℝ) + 1) ^ (2 : ℕ))))
    (hpow : Summable (fun k : ℕ =>
      |R (k + 1)| * Real.log ((k : ℝ) + 1) ^ j /
        (((k : ℝ) + 1) ^ (2 : ℕ)))) :
    Summable (fun k : ℕ =>
      |R (k + 1)| * (1 + Real.log ((k : ℝ) + 2)) ^ j /
        (((k : ℝ) + 1) ^ (2 : ℕ))) := by
  let C : ℝ := 2 ^ (2 * j)
  have hmaj : Summable (fun k : ℕ => C *
      (|R (k + 1)| / (((k : ℝ) + 1) ^ (2 : ℕ)) +
        |R (k + 1)| * Real.log ((k : ℝ) + 1) ^ j /
          (((k : ℝ) + 1) ^ (2 : ℕ)))) :=
    (hzero.add hpow).mul_left C
  apply (summable_nat_add_iff 1).1
  refine Summable.of_nonneg_of_le (fun k => by
      have hlog : 0 ≤ Real.log (((k + 1 : ℕ) : ℝ) + 2) :=
        Real.log_nonneg (by
          have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith)
      positivity) (fun k => ?_)
    ((summable_nat_add_iff 1).2 hmaj)
  let n : ℝ := ((k + 2 : ℕ) : ℝ)
  have hn2 : (2 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast (show 2 ≤ k + 2 by omega)
  have hnpos : 0 < n := by linarith
  have hlognon : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hsq : n + 1 ≤ n ^ (2 : ℕ) := by nlinarith
  have hlogshift : Real.log (n + 1) ≤ 2 * Real.log n := by
    have h := Real.log_le_log (by linarith : 0 < n + 1) hsq
    simpa [Real.log_pow] using h
  have hbase : 1 + Real.log (n + 1) ≤ 2 * (1 + Real.log n) := by
    linarith
  have hfirst : (1 + Real.log (n + 1)) ^ j ≤
      (2 * (1 + Real.log n)) ^ j := by
    have hnon : 0 ≤ 1 + Real.log (n + 1) := by
      have hlog1 : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
      linarith
    gcongr
  have hadd : (1 + Real.log n) ^ j ≤
      (2 : ℝ) ^ (j - 1) * (1 + Real.log n ^ j) := by
    simpa using add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hlognon j
  have hcoeff : (2 : ℝ) ^ (j - 1) ≤ 2 ^ j :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)
  have hlogpow : (1 + Real.log (n + 1)) ^ j ≤
      C * (1 + Real.log n ^ j) := by
    calc
      _ ≤ (2 * (1 + Real.log n)) ^ j := hfirst
      _ = (2 : ℝ) ^ j * (1 + Real.log n) ^ j := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ (j - 1) *
          (1 + Real.log n ^ j)) :=
        mul_le_mul_of_nonneg_left hadd (by positivity)
      _ ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ j *
          (1 + Real.log n ^ j)) := by
        gcongr
      _ = C * (1 + Real.log n ^ j) := by
        dsimp [C]
        calc
          (2 : ℝ) ^ j * ((2 : ℝ) ^ j * (1 + Real.log n ^ j)) =
              ((2 : ℝ) ^ j * (2 : ℝ) ^ j) * (1 + Real.log n ^ j) := by ring
          _ = (2 : ℝ) ^ (j + j) * (1 + Real.log n ^ j) := by rw [← pow_add]
          _ = (2 : ℝ) ^ (2 * j) * (1 + Real.log n ^ j) := by
            rw [show j + j = 2 * j by omega]
  have hscale := mul_le_mul_of_nonneg_left hlogpow
    (show 0 ≤ |R (k + 2)| / n ^ (2 : ℕ) by positivity)
  have htarget : |R (k + 2)| * (1 + Real.log (n + 1)) ^ j /
        n ^ (2 : ℕ) ≤ C *
          (|R (k + 2)| / n ^ (2 : ℕ) +
            |R (k + 2)| * Real.log n ^ j / n ^ (2 : ℕ)) := by
    calc
      _ = (|R (k + 2)| / n ^ (2 : ℕ)) *
          (1 + Real.log (n + 1)) ^ j := by ring
      _ ≤ (|R (k + 2)| / n ^ (2 : ℕ)) *
          (C * (1 + Real.log n ^ j)) := hscale
      _ = _ := by ring
  simpa [n, Nat.cast_add, Nat.add_assoc, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num,
    show (1 : ℝ) + 2 = 3 by norm_num,
    show (2 : ℝ) + 1 = 3 by norm_num] using htarget

theorem integrableOn_floor_log_weight_of_log_power (R : ℕ → ℝ) (j : ℕ)
    (hzero : Summable (fun k : ℕ =>
      |R (k + 1)| / (((k : ℝ) + 1) ^ (2 : ℕ))))
    (hpow : Summable (fun k : ℕ =>
      |R (k + 1)| * Real.log ((k : ℝ) + 1) ^ j /
        (((k : ℝ) + 1) ^ (2 : ℕ)))) :
    IntegrableOn (fun x : ℝ => R ⌊x⌋₊ *
      ((1 + Real.log x) ^ j / x ^ (2 : ℕ))) (Ioi (1 : ℝ)) :=
  integrableOn_floor_log_weight_of_summable R j
    (summable_shifted_log_weight_of_log_power R j hzero hpow)

end GaloisForLFunctions.HTGeometry
