import GaloisForLFunctions.TransThresholdPairCorrelation.OddStabilizerPoissonHorizon
import Mathlib.NumberTheory.AbelSummation

/-!
# The logarithmic square moment of the odd stabilizer mass

Finite Abel summation expresses the logarithmic square moment as a positive
integral of the ordinary odd-conductor mass. Its logarithmic mean one half
then gives the exact square-moment coefficient one sixth. The proof includes
uniform floor interpolation and both elementary logarithmic integral moments.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset intervalIntegral
open RHTower.Sieve
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private def oddMass (Q : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), sqfreeTotientInv q

private theorem oddMass_nonneg (Q : ℕ) : 0 ≤ oddMass Q :=
  sum_nonneg (fun q _ => sqfreeTotientInv_nonneg q)

private theorem oddMass_mono {M N : ℕ} (h : M ≤ N) : oddMass M ≤ oddMass N :=
  sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Icc_subset_Icc le_rfl h))
    (fun q _ _ => sqfreeTotientInv_nonneg q)

private theorem oddMass_affine_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t| ≤ ε * Real.log t + C := by
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp tendsto_sum_odd_sqfreeTotientInv_div_log_half ε hε
  let M := max K 2
  have hM : 2 ≤ M := le_max_right _ _
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlarge (k : ℕ) (hk : M ≤ k) :
      |oddMass k - (1 / 2 : ℝ) * Real.log k| ≤ ε * Real.log k := by
    have hk2 : 2 ≤ k := hM.trans hk
    have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have h := hK k ((le_max_left K 2).trans hk)
    rw [Real.dist_eq] at h
    calc
      _ = |oddMass k / Real.log k - (1 / 2 : ℝ)| * Real.log k := by
        have he : oddMass k - (1 / 2 : ℝ) * Real.log k =
            (oddMass k / Real.log k - (1 / 2 : ℝ)) * Real.log k := by
          field_simp [hlog.ne']
        rw [he, abs_mul, abs_of_pos hlog]
      _ ≤ _ := mul_le_mul_of_nonneg_right h.le hlog.le
  have hlogM0 : 0 ≤ Real.log (M + 1 : ℝ) := Real.log_nonneg (by linarith only [hMr])
  have hlog20 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨oddMass M + Real.log (M + 1) + Real.log 2,
    add_nonneg (add_nonneg (oddMass_nonneg M) hlogM0) hlog20, ?_⟩
  intro t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hk1 : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0.le).mpr (by exact_mod_cast ht)
  have hkr : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
  have hkt := Nat.floor_le ht0.le
  have hlogkt := Real.log_le_log hkr hkt
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  by_cases hk : M ≤ ⌊t⌋₊
  · have ht2 : t ≤ 2 * (⌊t⌋₊ : ℝ) := by
      have hh := Nat.lt_floor_add_one t
      have hk1r : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hk1
      linarith
    have hlogs : Real.log t - Real.log (⌊t⌋₊ : ℝ) ≤ Real.log 2 := by
      have hh := Real.log_le_log ht0 ht2
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkr.ne'] at hh
      linarith only [hh]
    have hdiff : |(1 / 2 : ℝ) * (Real.log (⌊t⌋₊ : ℝ) - Real.log t)| ≤ Real.log 2 / 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonpos (sub_nonpos.mpr hlogkt)]
      linarith only [hlogs]
    have hb := (abs_add_le (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log (⌊t⌋₊ : ℝ))
      ((1 / 2 : ℝ) * (Real.log (⌊t⌋₊ : ℝ) - Real.log t))).trans
      (add_le_add (hlarge ⌊t⌋₊ hk) hdiff)
    have he := mul_le_mul_of_nonneg_left hlogkt hε.le
    have hlogM : 0 ≤ Real.log (M + 1 : ℝ) := Real.log_nonneg (by linarith only [hMr])
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have heq : oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log (⌊t⌋₊ : ℝ) +
        (1 / 2 : ℝ) * (Real.log (⌊t⌋₊ : ℝ) - Real.log t) =
        oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t := by ring
    rw [heq] at hb
    linarith only [hb, he, oddMass_nonneg M, hlogM, hlog2]
  · have hsmall : ⌊t⌋₊ ≤ M := by omega
    have htM : t ≤ (M : ℝ) + 1 := by
      have hh := Nat.lt_floor_add_one t
      have hcast : (⌊t⌋₊ : ℝ) ≤ M := by exact_mod_cast hsmall
      linarith
    have hlogM := Real.log_le_log ht0 htM
    have hb : |oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t| ≤
        oddMass ⌊t⌋₊ + (1 / 2 : ℝ) * Real.log t := by
      simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg (oddMass_nonneg _),
        abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hlogt)] using
        abs_add_le (oddMass ⌊t⌋₊) (-((1 / 2 : ℝ) * Real.log t))
    have hm := oddMass_mono hsmall
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have he : 0 ≤ ε * Real.log t := mul_nonneg hε.le hlogt
    linarith only [hb, hm, hlogM, hlogt, hlog2, he]

private def oddCoefficient (q : ℕ) : ℝ :=
  if q % 2 = 1 then sqfreeTotientInv q else 0

private theorem sum_oddCoefficient (f : ℕ → ℝ) (Q : ℕ) :
    (∑ q ∈ Icc 0 Q, f q * oddCoefficient q) =
      ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), f q * sqfreeTotientInv q := by
  simp only [oddCoefficient, mul_ite, mul_zero, ← sum_filter]
  congr 1

private theorem oddPartial_eq (Q : ℕ) :
    (∑ q ∈ Icc 0 Q, oddCoefficient q) = oddMass Q := by
  simpa only [one_mul, oddMass] using sum_oddCoefficient (fun _ => 1) Q

/-- The logarithmic square moment of the odd squarefree reciprocal-totient
mass at a finite cutoff. -/
def oddStabilizerLogSquareMass (Q : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1),
    sqfreeTotientInv q * (Real.log ((Q : ℝ) / q))^2

/-- Finite Abel summation expresses the logarithmic square moment as a
positive logarithmic average of the ordinary odd-conductor mass. -/
theorem oddStabilizerLogSquareMass_eq_integral {Q : ℕ} (hQ : 1 ≤ Q) :
    oddStabilizerLogSquareMass Q =
      2 * ∫ t in (1 : ℝ)..(Q : ℝ),
        (Real.log Q - Real.log t) / t *
          (∑ q ∈ (Icc 1 ⌊t⌋₊).filter (fun q => q % 2 = 1), sqfreeTotientInv q) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  have hd (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) :
      HasDerivAt (fun x : ℝ => (Real.log Q - Real.log x)^2)
        (-2 * ((Real.log Q - Real.log t) / t)) t := by
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    have hh := ((hasDerivAt_const t (Real.log Q)).sub (Real.hasDerivAt_log ht0)).pow 2
    exact hh.congr_deriv (by
      change (2 : ℝ) * (Real.log Q - Real.log t) ^ (2 - 1) * (0 - t⁻¹) = _
      ring)
  have hcont : ContinuousOn (fun t : ℝ => -2 * ((Real.log Q - Real.log t) / t))
      (Set.Icc (1 : ℝ) Q) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
    exact (continuousAt_const.mul
      ((continuousAt_const.sub (Real.continuousAt_log ht0)).div continuousAt_id ht0)).continuousWithinAt
  have hi : IntegrableOn (deriv (fun x : ℝ => (Real.log Q - Real.log x)^2))
      (Set.Icc (1 : ℝ) Q) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_integral_mul₀ (c := oddCoefficient)
    (by norm_num [oddCoefficient]) (Q : ℝ) (fun t ht => (hd t ht).differentiableAt) hi
  simp only [Nat.floor_natCast, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, zero_sub] at ha
  have hsum : (∑ q ∈ Icc 0 Q, (Real.log Q - Real.log (q : ℝ))^2 * oddCoefficient q) =
      oddStabilizerLogSquareMass Q := by
    rw [sum_oddCoefficient]
    apply sum_congr rfl
    intro q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 from
      ne_of_gt (mem_Icc.mp (mem_filter.mp hq).1).1)
    rw [Real.log_div hQ0 hq0]
    ring
  rw [hsum] at ha
  rw [ha]
  have hpoint : (∫ t in Set.Ioc (1 : ℝ) Q,
      deriv (fun x : ℝ => (Real.log Q - Real.log x)^2) t *
        ∑ q ∈ Icc 0 ⌊t⌋₊, oddCoefficient q) =
      ∫ t in (1 : ℝ)..(Q : ℝ), -2 * ((Real.log Q - Real.log t) / t * oddMass ⌊t⌋₊) := by
    rw [intervalIntegral.integral_of_le hQr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, oddPartial_eq]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  dsimp only [oddMass]
  change -(-2 * _) = 2 * _
  ring

private theorem log_kernel_continuous (X : ℝ) :
    ContinuousOn (fun t : ℝ => (Real.log X - Real.log t) / t) (Set.Icc 1 X) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht.1)
  exact ((continuousAt_const.sub (Real.continuousAt_log ht0)).div
    continuousAt_id ht0).continuousWithinAt

private theorem log_kernel_integrals {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in (1 : ℝ)..X, (Real.log X - Real.log t) / t) = (Real.log X)^2 / 2 ∧
    (∫ t in (1 : ℝ)..X, (Real.log X - Real.log t) / t * Real.log t) = (Real.log X)^3 / 6 := by
  have hlog : ContinuousOn Real.log (Set.Icc 1 X) := by
    intro t ht
    exact (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans_le ht.1))).continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ => (Real.log X - Real.log t) / t) volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr (log_kernel_continuous X).integrableOn_Icc
  have hiL : IntervalIntegrable (fun t : ℝ => (Real.log X - Real.log t) / t * Real.log t) volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
      ((log_kernel_continuous X).mul hlog).integrableOn_Icc
  constructor
  · have hd (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) X) :
        HasDerivAt (fun y : ℝ => Real.log X * Real.log y - (Real.log y)^2 / 2)
          ((Real.log X - Real.log t) / t) t := by
      rw [Set.uIcc_of_le hX] at ht
      have hl := Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans_le ht.1))
      have hh := (hl.const_mul (Real.log X)).sub ((hl.pow 2).div_const 2)
      exact hh.congr_deriv (by ring)
    calc
      _ = (Real.log X * Real.log X - (Real.log X)^2 / 2) -
          (Real.log X * Real.log 1 - (Real.log 1)^2 / 2) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
      _ = _ := by rw [Real.log_one]; ring
  · have hd (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) X) :
        HasDerivAt (fun y : ℝ => Real.log X * (Real.log y)^2 / 2 - (Real.log y)^3 / 3)
          (((Real.log X - Real.log t) / t) * Real.log t) t := by
      rw [Set.uIcc_of_le hX] at ht
      have hl := Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans_le ht.1))
      have hh := (((hl.pow 2).const_mul (Real.log X)).div_const 2).sub ((hl.pow 3).div_const 3)
      exact hh.congr_deriv (by ring)
    calc
      _ = (Real.log X * (Real.log X)^2 / 2 - (Real.log X)^3 / 3) -
          (Real.log X * (Real.log 1)^2 / 2 - (Real.log 1)^3 / 3) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd hiL
      _ = _ := by rw [Real.log_one]; ring

private theorem logSquare_error_of_affine {ε C : ℝ}
    (hbound : ∀ t : ℝ, 1 ≤ t →
      |oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t| ≤ ε * Real.log t + C)
    {Q : ℕ} (hQ : 1 ≤ Q) :
    |oddStabilizerLogSquareMass Q - (Real.log Q)^3 / 6| ≤
      ε / 3 * (Real.log Q)^3 + C * (Real.log Q)^2 := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  let k : ℝ → ℝ := fun t => (Real.log Q - Real.log t) / t
  have hk : ContinuousOn k (Set.Icc 1 Q) := log_kernel_continuous Q
  have hlog : ContinuousOn Real.log (Set.Icc 1 Q) := by
    intro t ht
    exact (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans_le ht.1))).continuousWithinAt
  have hi : IntervalIntegrable k volume 1 Q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hQr).mpr hk.integrableOn_Icc
  have hiL : IntervalIntegrable (fun t => k t * Real.log t) volume 1 Q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hQr).mpr (hk.mul hlog).integrableOn_Icc
  have hiO : IntervalIntegrable (fun t => k t * oddMass ⌊t⌋₊) volume 1 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQr]
    have hh := integrableOn_mul_sum_Icc (c := oddCoefficient) (m := 0)
      (by norm_num : (0 : ℝ) ≤ 1) hk.integrableOn_Icc
    simpa only [oddPartial_eq] using hh
  have hie : IntervalIntegrable (fun t => k t * (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t)) volume 1 Q := by
    have he : (fun t => k t * (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t)) =
        (fun t => k t * oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * (k t * Real.log t)) := by funext t; ring
    rw [he]
    exact hiO.sub (hiL.const_mul (1 / 2 : ℝ))
  have hib : IntervalIntegrable (fun t => k t * (ε * Real.log t + C)) volume 1 Q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hQr).mpr
      (hk.mul ((continuousOn_const.mul hlog).add continuousOn_const)).integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) :
      |k t * (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t)| ≤ k t * (ε * Real.log t + C) := by
    have ht0 := zero_lt_one.trans_le ht.1
    have hkn : 0 ≤ k t := div_nonneg
      (sub_nonneg.mpr (Real.log_le_log ht0 ht.2)) ht0.le
    rw [abs_mul, abs_of_nonneg hkn]
    exact mul_le_mul_of_nonneg_left (hbound t ht.1) hkn
  have hidentity : oddStabilizerLogSquareMass Q - (Real.log Q)^3 / 6 =
      2 * ∫ t in (1 : ℝ)..(Q : ℝ), k t * (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t) := by
    have he : (fun t => k t * (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t)) =
        (fun t => k t * oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * (k t * Real.log t)) := by funext t; ring
    rw [he, intervalIntegral.integral_sub hiO (hiL.const_mul (1 / 2 : ℝ)),
      intervalIntegral.integral_const_mul]
    have hs := oddStabilizerLogSquareMass_eq_integral hQ
    have hL := (log_kernel_integrals hQr).2
    change oddStabilizerLogSquareMass Q = 2 * ∫ t in (1 : ℝ)..(Q : ℝ), k t * oddMass ⌊t⌋₊ at hs
    change (∫ t in (1 : ℝ)..(Q : ℝ), k t * Real.log t) = _ at hL
    rw [hs, hL]
    ring
  rw [hidentity, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have habs : |∫ t in (1 : ℝ)..(Q : ℝ), k t * (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t)| ≤
      ∫ t in (1 : ℝ)..(Q : ℝ), |k t * (oddMass ⌊t⌋₊ - (1 / 2 : ℝ) * Real.log t)| := by
    rw [intervalIntegral.integral_of_le hQr, intervalIntegral.integral_of_le hQr]
    exact abs_integral_le_integral_abs
  have hm := intervalIntegral.integral_mono_on hQr hie.abs hib hpoint
  calc
    _ ≤ 2 * ∫ t in (1 : ℝ)..(Q : ℝ), k t * (ε * Real.log t + C) :=
      mul_le_mul_of_nonneg_left (habs.trans hm) (by norm_num)
    _ = ε / 3 * (Real.log Q)^3 + C * (Real.log Q)^2 := by
      have he : (fun t => k t * (ε * Real.log t + C)) =
          (fun t => ε * (k t * Real.log t) + C * k t) := by funext t; ring
      rw [he, intervalIntegral.integral_add (hiL.const_mul ε) (hi.const_mul C),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      dsimp only [k]
      rw [(log_kernel_integrals hQr).1, (log_kernel_integrals hQr).2]
      ring

/-- The odd-conductor square logarithmic moment has exact leading coefficient
one sixth. Abel summation transfers the ordinary logarithmic mean one half. -/
theorem tendsto_oddStabilizerLogSquareMass_div_log_cube :
    Tendsto (fun Q : ℕ => oddStabilizerLogSquareMass Q / (Real.log Q)^3)
      atTop (𝓝 (1 / 6 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨C, _, hCb⟩ := oddMass_affine_error hε
  have hlog : Tendsto (fun Q : ℕ => Real.log Q) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun Q : ℕ => C / Real.log Q) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hlog
  have he : ∀ᶠ Q : ℕ in atTop, C / Real.log Q < ε / 2 :=
    hz.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨M, hM⟩ := eventually_atTop.mp (he.and (eventually_ge_atTop (2 : ℕ)))
  refine ⟨M, ?_⟩
  intro Q hQM
  obtain ⟨hCe, hQ⟩ := hM Q hQM
  have hL : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hraw := logSquare_error_of_affine hCb (show 1 ≤ Q by omega)
  have hscaled : |oddStabilizerLogSquareMass Q / (Real.log Q)^3 - (1 / 6 : ℝ)| ≤
      ε / 3 + C / Real.log Q := by
    calc
      _ = |oddStabilizerLogSquareMass Q - (Real.log Q)^3 / 6| / (Real.log Q)^3 := by
        have he : oddStabilizerLogSquareMass Q / (Real.log Q)^3 - (1 / 6 : ℝ) =
            (oddStabilizerLogSquareMass Q - (Real.log Q)^3 / 6) / (Real.log Q)^3 := by
          field_simp [hL.ne']
        rw [he, abs_div, abs_of_pos (pow_pos hL 3)]
      _ ≤ (ε / 3 * (Real.log Q)^3 + C * (Real.log Q)^2) / (Real.log Q)^3 :=
        div_le_div_of_nonneg_right hraw (pow_pos hL 3).le
      _ = _ := by field_simp [hL.ne']
  rw [Real.dist_eq]
  linarith only [hscaled, hCe, hε]

end GaloisForLFunctions.TransThresholdPairCorrelation
