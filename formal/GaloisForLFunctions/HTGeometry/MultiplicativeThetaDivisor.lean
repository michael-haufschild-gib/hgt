import GaloisForLFunctions.HTGeometry.QPochhammerAnalytic

/-!
# Simple divisor of multiplicative theta
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Product with the selected `n`-th q-Pochhammer factor removed. -/
def qPochhammerPuncturedAt (q : EulerNome) (n : ℕ) (z : ℂ) : ℂ :=
  qPochhammer z q n * qPochhammerInf (z * (q : ℂ) ^ (n + 1)) q

/-- Exact factorization isolating the selected q-Pochhammer factor. -/
theorem qPochhammerInf_eq_factor_mul_puncturedAt
    (q : EulerNome) (n : ℕ) (z : ℂ) :
    qPochhammerInf z q =
      (1 - z * (q : ℂ) ^ n) * qPochhammerPuncturedAt q n z := by
  rw [qPochhammerInf_iterate_shift z q n,
    qPochhammerInf_shift (z * (q : ℂ) ^ n) q]
  simp only [qPochhammerPuncturedAt, pow_succ]
  ring

/-- The punctured q-Pochhammer product is entire in its parameter. -/
theorem analyticAt_qPochhammerPuncturedAt (q : EulerNome) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (qPochhammerPuncturedAt q n) z := by
  have hfinite : AnalyticAt ℂ (fun w : ℂ => qPochhammer w q n) z := by
    unfold qPochhammer
    have h := Finset.analyticAt_prod (𝕜 := ℂ) (E := ℂ) (A := ℂ)
      (f := fun j : ℕ => fun w : ℂ => 1 - w * (q : ℂ) ^ j)
      (c := z) (Finset.range n) (fun j hj =>
        analyticAt_const.sub (analyticAt_id.mul analyticAt_const))
    have hfun : (fun w : ℂ => ∏ j ∈ Finset.range n, (1 - w * (q : ℂ) ^ j)) =
        ∏ j ∈ Finset.range n, (fun w : ℂ => 1 - w * (q : ℂ) ^ j) := by
      funext w
      simp
    rw [hfun]
    exact h
  have hinfinite : AnalyticAt ℂ
      (fun w : ℂ => qPochhammerInf (w * (q : ℂ) ^ (n + 1)) q) z :=
    (analyticAt_qPochhammerInf q _).comp_of_eq
      (analyticAt_id.mul analyticAt_const) rfl
  exact hfinite.mul hinfinite

/-- Removing the unique vanishing factor leaves a nonzero q-Pochhammer product. -/
theorem qPochhammerPuncturedAt_ne_zero
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) (n : ℕ) (a : ℂ)
    (ha : a * (q : ℂ) ^ n = 1) :
    qPochhammerPuncturedAt q n a ≠ 0 := by
  have ha0 : a ≠ 0 := by
    intro haz
    simp [haz] at ha
  have hfinite : qPochhammer a q n ≠ 0 := by
    unfold qPochhammer
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    simp only [Finset.mem_range] at hj
    apply sub_ne_zero.mpr
    intro heq
    have hjone : a * (q : ℂ) ^ j = 1 := heq.symm
    have hpow : (q : ℂ) ^ j = (q : ℂ) ^ n :=
      mul_left_cancel₀ ha0 (hjone.trans ha.symm)
    have hnorm := congrArg norm hpow
    simp only [norm_pow] at hnorm
    have hqnormpos : 0 < ‖(q : ℂ)‖ := norm_pos_iff.mpr hq
    have hjn : (j : ℤ) < (n : ℤ) := by exact_mod_cast hj
    have hstrict := zpow_lt_zpow_right_of_lt_one₀ hqnormpos q.norm_lt_one hjn
    have hnormz : ‖(q : ℂ)‖ ^ (j : ℤ) = ‖(q : ℂ)‖ ^ (n : ℤ) := by
      simpa only [zpow_natCast] using hnorm
    exact (ne_of_lt hstrict) hnormz.symm
  have htailArg : a * (q : ℂ) ^ (n + 1) = (q : ℂ) := by
    rw [pow_succ, ← mul_assoc, ha, one_mul]
  let d : EulerPochhammerDatum :=
    { a := (q : ℂ), q := q, a_norm_lt_one := q.norm_lt_one }
  have htail : qPochhammerInf (a * (q : ℂ) ^ (n + 1)) q ≠ 0 := by
    rw [htailArg]
    exact qPochhammerInf_ne_zero d
  exact mul_ne_zero hfinite htail

/-- Every zero of a q-Pochhammer infinite product is simple. -/
theorem analyticOrderAt_qPochhammerInf_eq_one
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) (n : ℕ) (a : ℂ)
    (ha : a * (q : ℂ) ^ n = 1) :
    analyticOrderAt (fun z : ℂ => qPochhammerInf z q) a = 1 := by
  have hlinear : AnalyticAt ℂ (fun z : ℂ => 1 - z * (q : ℂ) ^ n) a :=
    analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hlinearOrder :
      analyticOrderAt (fun z : ℂ => 1 - z * (q : ℂ) ^ n) a = 1 := by
    rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by norm_num,
      hlinear.analyticOrderAt_eq_natCast]
    refine ⟨fun _ : ℂ => -((q : ℂ) ^ n), analyticAt_const,
      neg_ne_zero.mpr (pow_ne_zero n hq), ?_⟩
    filter_upwards with z
    simp only [pow_one, smul_eq_mul]
    rw [← ha]
    ring
  have hpunct := analyticAt_qPochhammerPuncturedAt q n a
  have hpunctNe := qPochhammerPuncturedAt_ne_zero q hq n a ha
  have hfun : (fun z : ℂ => qPochhammerInf z q) =
      (fun z : ℂ => 1 - z * (q : ℂ) ^ n) * qPochhammerPuncturedAt q n := by
    funext z
    exact qPochhammerInf_eq_factor_mul_puncturedAt q n z
  rw [hfun, analyticOrderAt_mul hlinear hpunct, hlinearOrder,
    hpunct.analyticOrderAt_eq_zero.mpr hpunctNe]
  norm_num

/-- Multiplicative theta is analytic away from the puncture. -/
theorem analyticAt_multiplicativeTheta (q : EulerNome) {y : ℂ} (hy : y ≠ 0) :
    AnalyticAt ℂ (multiplicativeTheta q) y := by
  have hfirst := analyticAt_qPochhammerInf q y
  have hinner : AnalyticAt ℂ (fun z : ℂ => (q : ℂ) / z) y :=
    analyticAt_const.div analyticAt_id hy
  have hsecond : AnalyticAt ℂ
      (fun z : ℂ => qPochhammerInf ((q : ℂ) / z) q) y :=
    (analyticAt_qPochhammerInf q _).comp_of_eq hinner rfl
  exact hfirst.mul hsecond

/-- The two q-Pochhammer factors of theta cannot vanish simultaneously for a nonzero nome. -/
theorem not_both_qPochhammerInf_theta_factors_zero
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) {y : ℂ} (hy : y ≠ 0) :
    ¬ (qPochhammerInf y q = 0 ∧ qPochhammerInf ((q : ℂ) / y) q = 0) := by
  rintro ⟨hfirst, hsecond⟩
  obtain ⟨n, hn⟩ := (qPochhammerInf_eq_zero_iff y q).mp hfirst
  obtain ⟨m, hm⟩ := (qPochhammerInf_eq_zero_iff ((q : ℂ) / y) q).mp hsecond
  have hpow : (q : ℂ) ^ (n + m + 1) = 1 := by
    calc
      (q : ℂ) ^ (n + m + 1) =
          (y * (q : ℂ) ^ n) * (((q : ℂ) / y) * (q : ℂ) ^ m) := by
        rw [show n + m + 1 = n + (m + 1) by omega, pow_add, pow_succ]
        field_simp [hy]
      _ = 1 := by rw [hn, hm, one_mul]
  have hnorm := congrArg norm hpow
  simp only [norm_pow, norm_one] at hnorm
  have hlt : ‖(q : ℂ)‖ ^ (n + m + 1) < 1 :=
    pow_lt_one₀ (norm_nonneg _) q.norm_lt_one (by omega)
  linarith

/-- The reciprocal-argument q-Pochhammer factor also has a simple zero. -/
theorem analyticOrderAt_qPochhammerInf_div_eq_one
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) (n : ℕ) {y : ℂ} (hy : y ≠ 0)
    (ha : ((q : ℂ) / y) * (q : ℂ) ^ n = 1) :
    analyticOrderAt (fun z : ℂ => qPochhammerInf ((q : ℂ) / z) q) y = 1 := by
  have hinner : AnalyticAt ℂ (fun z : ℂ => (q : ℂ) / z) y :=
    analyticAt_const.div analyticAt_id hy
  have hlinear : AnalyticAt ℂ
      (fun z : ℂ => 1 - ((q : ℂ) / z) * (q : ℂ) ^ n) y :=
    analyticAt_const.sub (hinner.mul analyticAt_const)
  have hqy : (q : ℂ) ^ (n + 1) = y := by
    rw [pow_succ]
    field_simp [hy] at ha
    simpa [mul_comm] using ha
  have hlinearOrder :
      analyticOrderAt (fun z : ℂ => 1 - ((q : ℂ) / z) * (q : ℂ) ^ n) y = 1 := by
    rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by norm_num,
      hlinear.analyticOrderAt_eq_natCast]
    refine ⟨fun z : ℂ => z⁻¹, analyticAt_id.inv hy, inv_ne_zero hy, ?_⟩
    filter_upwards [eventually_ne_nhds hy] with z hz
    simp only [pow_one, smul_eq_mul]
    rw [div_eq_mul_inv,
      show (q : ℂ) * z⁻¹ * (q : ℂ) ^ n = (q : ℂ) ^ (n + 1) * z⁻¹ by
        rw [pow_succ]
        ring,
      hqy]
    field_simp [hz]
  have hpunct : AnalyticAt ℂ
      (fun z : ℂ => qPochhammerPuncturedAt q n ((q : ℂ) / z)) y :=
    (analyticAt_qPochhammerPuncturedAt q n _).comp_of_eq hinner rfl
  have hpunctNe : qPochhammerPuncturedAt q n ((q : ℂ) / y) ≠ 0 :=
    qPochhammerPuncturedAt_ne_zero q hq n ((q : ℂ) / y) ha
  have hfun : (fun z : ℂ => qPochhammerInf ((q : ℂ) / z) q) =
      (fun z : ℂ => 1 - ((q : ℂ) / z) * (q : ℂ) ^ n) *
        (fun z : ℂ => qPochhammerPuncturedAt q n ((q : ℂ) / z)) := by
    funext z
    exact qPochhammerInf_eq_factor_mul_puncturedAt q n ((q : ℂ) / z)
  rw [hfun, analyticOrderAt_mul hlinear hpunct, hlinearOrder,
    hpunct.analyticOrderAt_eq_zero.mpr hpunctNe]
  norm_num

/-- Every multiplicative-theta zero on `ℂˣ` is simple. -/
theorem analyticOrderAt_multiplicativeTheta_eq_one
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) {y : ℂ} (hy : y ≠ 0)
    (hzero : multiplicativeTheta q y = 0) :
    analyticOrderAt (multiplicativeTheta q) y = 1 := by
  have hfirstAn := analyticAt_qPochhammerInf q y
  have hinner : AnalyticAt ℂ (fun z : ℂ => (q : ℂ) / z) y :=
    analyticAt_const.div analyticAt_id hy
  have hsecondAn : AnalyticAt ℂ
      (fun z : ℂ => qPochhammerInf ((q : ℂ) / z) q) y :=
    (analyticAt_qPochhammerInf q _).comp_of_eq hinner rfl
  have hexclusive := not_both_qPochhammerInf_theta_factors_zero q hq hy
  rw [multiplicativeTheta_eq_zero_iff] at hzero
  change analyticOrderAt
      ((fun z : ℂ => qPochhammerInf z q) *
        (fun z : ℂ => qPochhammerInf ((q : ℂ) / z) q)) y = 1
  rw [analyticOrderAt_mul hfirstAn hsecondAn]
  rcases hzero with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hfirstZero : qPochhammerInf y q = 0 :=
      (qPochhammerInf_eq_zero_iff y q).mpr ⟨n, hn⟩
    have hsecondNe : qPochhammerInf ((q : ℂ) / y) q ≠ 0 := by
      intro hsecondZero
      exact hexclusive ⟨hfirstZero, hsecondZero⟩
    rw [analyticOrderAt_qPochhammerInf_eq_one q hq n y hn,
      hsecondAn.analyticOrderAt_eq_zero.mpr hsecondNe]
    norm_num
  · have hsecondZero : qPochhammerInf ((q : ℂ) / y) q = 0 :=
      (qPochhammerInf_eq_zero_iff ((q : ℂ) / y) q).mpr ⟨n, hn⟩
    have hfirstNe : qPochhammerInf y q ≠ 0 := by
      intro hfirstZero
      exact hexclusive ⟨hfirstZero, hsecondZero⟩
    rw [hfirstAn.analyticOrderAt_eq_zero.mpr hfirstNe,
      analyticOrderAt_qPochhammerInf_div_eq_one q hq n hy hn]
    norm_num

/-- Away from its nome orbit, multiplicative theta has analytic order zero. -/
theorem analyticOrderAt_multiplicativeTheta_eq_zero
    (q : EulerNome) {y : ℂ} (hy : y ≠ 0) (hne : multiplicativeTheta q y ≠ 0) :
    analyticOrderAt (multiplicativeTheta q) y = 0 :=
  (analyticAt_multiplicativeTheta q hy).analyticOrderAt_eq_zero.mpr hne

end

end GaloisForLFunctions.HTGeometry
