import GaloisForLFunctions.HTGeometry.BhattacharyyaRealOverlap
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticAffinityGeometry
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticLikelihoodRigidity

/-! Actual finite Weil tilted-law affinities converge to the precision kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilQuadraticLikelihood_half_eq_affinity (s S : {s : ℝ // s < 2}) :
    finiteWeilQuadraticLikelihoodFiniteLimit s S (-1 / 2) =
      finiteWeilQuadraticTiltAffinity s S := by
  let x : ℝ := 2 - s.val
  let y : ℝ := 2 - S.val
  have hx : 0 < x := sub_pos.mpr s.property
  have hy : 0 < y := sub_pos.mpr S.property
  have hsum : 0 < x + y := add_pos hx hy
  have hmid : 2 - (s.val + (-1 / 2) * (s.val - S.val)) = (x + y) / 2 := by
    dsimp [x, y]
    ring
  have hlog : (4 : ℝ) * (-1 / 2 *
      (Real.log (Real.sqrt (2 / y)) - Real.log (Real.sqrt (2 / x)))) =
        Real.log y - Real.log x := by
    rw [Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
      Real.log_div (by norm_num) hy.ne', Real.log_div (by norm_num) hx.ne']
    ring
  have hsqrt : Real.sqrt (x / ((x + y) / 2)) ^ 4 = (x / ((x + y) / 2)) ^ 2 := by
    calc
      _ = (Real.sqrt (x / ((x + y) / 2)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have hfour : finiteWeilQuadraticLikelihoodFiniteLimit s S (-1 / 2) ^ 4 =
      4 * x * y / (x + y) ^ 2 := by
    unfold finiteWeilQuadraticLikelihoodFiniteLimit
    rw [mul_pow, ← Real.exp_nat_mul]
    change Real.exp ((4 : ℝ) * (-1 / 2 *
      (Real.log (Real.sqrt (2 / y)) - Real.log (Real.sqrt (2 / x))))) *
        Real.sqrt (x / (2 - (s.val + (-1 / 2) * (s.val - S.val)))) ^ 4 = _
    rw [hlog, hmid, Real.exp_sub, Real.exp_log hy, Real.exp_log hx, hsqrt]
    field_simp [hx.ne', hsum.ne']
    ring
  have hnonneg : 0 ≤ finiteWeilQuadraticLikelihoodFiniteLimit s S (-1 / 2) :=
    mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  apply (pow_left_inj₀ hnonneg (finiteWeilQuadraticTiltAffinity_pos s S).le
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [hfour]
  exact (positivePrecisionOverlap_fourth
    ⟨x, hx⟩ ⟨y, hy⟩).symm

theorem finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_eq
    (r k : ℕ) (a b d A B D : ℝ) :
    bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) =
        ENNReal.ofReal (finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D (-1 / 2)) := by
  rw [finiteWeilCanonicalQuadraticLikelihoodMoment_half_eq_overlap]
  exact bhattacharyya_eq_ofReal_integral_sqrt_rnDeriv _ _

theorem finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_toReal
    (r k : ℕ) (a b d A B D : ℝ) :
    (bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E)).toReal =
        finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D (-1 / 2) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_eq,
    ENNReal.toReal_ofReal (finiteWeilCanonicalQuadraticLikelihoodMoment_pos r k a b d A B D _).le]

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_toReal
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r =>
      (bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E)).toReal)
      atTop (𝓝 (finiteWeilQuadraticTiltAffinity
        ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩)) := by
  simp_rw [finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_toReal]
  simpa only [finiteWeilQuadraticLikelihood_half_eq_affinity] using
    tendsto_finiteWeilCanonicalQuadraticLikelihood_interval t a b d A B D
      ⟨-1 / 2, by constructor <;> norm_num⟩

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r =>
      bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))
      atTop (𝓝 (ENNReal.ofReal (finiteWeilQuadraticTiltAffinity
        ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩))) := by
  have h := (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_toReal t a b d A B D)
  exact h.congr fun r => by
    simp only [Function.comp_apply, finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_toReal,
      ← finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_eq]

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_one_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r =>
      bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))
      atTop (𝓝 1) ↔ a + 2 * b + d.val = A + 2 * B + D.val := by
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya t a b d A B D
  constructor
  · intro h
    exact (finiteWeilQuadraticTiltAffinity_eq_one_iff _ _).mp
      (ENNReal.ofReal_eq_one.mp (tendsto_nhds_unique hlim h))
  · intro h
    have he := (finiteWeilQuadraticTiltAffinity_eq_one_iff
      ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩).mpr h
    simpa only [he, ENNReal.ofReal_one] using hlim

end RHTower
