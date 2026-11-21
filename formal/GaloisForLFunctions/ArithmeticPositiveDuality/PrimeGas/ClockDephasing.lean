import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoherentShiftReadings

/-!
# Hamiltonian time averages of coherent states

Averaging a pure square-root Gibbs state over the logarithmic Hamiltonian
recovers the Gibbs trace on every bounded observable. Finite shell
truncations approximate the quadratic readings uniformly over all times.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology ContinuousLinearMap MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

/-- Unitary shell phases of the logarithmic Hamiltonian. -/
def clockEvolution (t : ℝ) : Gas →L[ℂ] Gas :=
  lpDiagonalCLM (fun n => (clockPhase t n : ℂ)) zero_le_one fun _ => (Circle.norm_coe _).le

private theorem clock_contract (t : ℝ) (x : Gas) : ‖clockEvolution t x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (norm_lpDiagonalCLM_le _ _ _) (norm_nonneg x))

private def cut (x : Gas) (S : Finset ℕ+) : Gas := ∑ n ∈ S, lp.single 2 n (x n)

private theorem cut_limit (x : Gas) : Tendsto (cut x) atTop (𝓝 x) :=
  lp.hasSum_single (by norm_num) x

private theorem orbit_cut (t : ℝ) (x : Gas) (S : Finset ℕ+) :
    clockEvolution t (cut x S) = ∑ n ∈ S, (clockPhase t n : ℂ) • lp.single 2 n (x n) := by
  rw [cut, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply lp.ext
  funext k
  change (clockPhase t k : ℂ) * (lp.single 2 n (x n) : Gas) k =
    (clockPhase t n : ℂ) * (lp.single 2 n (x n) : Gas) k
  by_cases h : k = n
  · rw [h]
  · rw [lp.single_apply_ne _ _ _ h, mul_zero, mul_zero]

private theorem continuous_orbit (x : Gas) : Continuous (fun t => clockEvolution t x) := by
  have hu : TendstoUniformly (fun S t => clockEvolution t (cut x S))
      (fun t => clockEvolution t x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp (cut_limit x) ε hε)] with S hS t
    rw [dist_eq_norm, ← map_sub]
    exact (clock_contract t _).trans_lt (by simpa [dist_eq_norm, norm_sub_rev] using hS)
  apply hu.continuous (Eventually.frequently (Eventually.of_forall fun S => ?_))
  simp only [orbit_cut]
  apply continuous_finsetSum
  intro n _
  have hc : Continuous (fun t : ℝ => (clockPhase t n : ℂ)) :=
    continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_id.mul continuous_const))
  exact hc.smul continuous_const

/-- Pure-state expectation after rotating all shell phases by the Hamiltonian clock. -/
def orbitExpectation (A : Gas →L[ℂ] Gas) (x : Gas) (t : ℝ) : ℂ :=
  inner ℂ (clockEvolution t x) (A (clockEvolution t x))

private theorem continuous_reading (A : Gas →L[ℂ] Gas) (x : Gas) : Continuous (orbitExpectation A x) :=
  (continuous_orbit x).inner (A.continuous.comp (continuous_orbit x))

/-- Truncation error depends on the shell tail alone, uniformly along the clock orbit. -/
private theorem reading_error (A : Gas →L[ℂ] Gas) (x y : Gas) (t : ℝ) :
    ‖orbitExpectation A x t - orbitExpectation A y t‖ ≤ ‖A‖ * (‖x‖+‖y‖) * ‖x-y‖ := by
  let U := clockEvolution t
  have hsub : orbitExpectation A x t - orbitExpectation A y t =
      inner ℂ (U (x-y)) (A (U x)) + inner ℂ (U y) (A (U (x-y))) := by
    simp only [orbitExpectation, U, map_sub, inner_sub_left, inner_sub_right]
    abel
  rw [hsub]
  apply (norm_add_le _ _).trans
  have bound (z : Gas) := (A.le_opNorm (U z)).trans
    (mul_le_mul_of_nonneg_left (clock_contract t z) (norm_nonneg A))
  have h₁ := (norm_inner_le_norm (𝕜 := ℂ) (U (x-y)) (A (U x))).trans
    (mul_le_mul (clock_contract t _) (bound _) (norm_nonneg _) (norm_nonneg _))
  have h₂ := (norm_inner_le_norm (𝕜 := ℂ) (U y) (A (U (x-y)))).trans
    (mul_le_mul (clock_contract t _) (bound _) (norm_nonneg _) (norm_nonneg _))
  exact (add_le_add h₁ h₂).trans_eq (by ring)

private theorem window_error (A : Gas →L[ℂ] Gas) (x y : Gas) (T : ℝ) :
    ‖windowAverage (orbitExpectation A x) T - windowAverage (orbitExpectation A y) T‖ ≤
      ‖A‖ * (‖x‖+‖y‖) * ‖x-y‖ := by
  let B := ‖A‖ * (‖x‖+‖y‖) * ‖x-y‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [windowAverage, windowAverage, ← smul_sub, ← intervalIntegral.integral_sub
    ((continuous_reading A x).intervalIntegrable _ _) ((continuous_reading A y).intervalIntegrable _ _),
    norm_smul, Real.norm_eq_abs, abs_inv]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
    (fun t _ => reading_error A x y t)
  rw [sub_zero] at h
  by_cases hT : T = 0
  · simpa [hT] using hB
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (abs_nonneg _))).trans_eq (by
    rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr hT), mul_one])

private theorem clock_gap (t : ℝ) (i j : ℕ+) :
    conj (clockPhase t i : ℂ) * (clockPhase t j : ℂ) =
      Complex.exp ((energy j - energy i : ℝ) * Complex.I * (t : ℂ)) := by
  change conj (Complex.exp (((t*energy i : ℝ) : ℂ)*Complex.I)) *
    Complex.exp (((t*energy j : ℝ) : ℂ)*Complex.I) = _
  rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  congr 1
  ring

private theorem energy_gap_zero (a b : ℕ+) : energy b - energy a = 0 ↔ b = a := by
  rw [sub_eq_zero]
  constructor
  · intro h
    have h' := congrArg Real.exp h
    rw [energy, energy, Real.exp_log (Nat.cast_pos.mpr b.pos), Real.exp_log (Nat.cast_pos.mpr a.pos)] at h'
    exact PNat.coe_injective (Nat.cast_injective (R := ℝ) h')
  · rintro rfl
    rfl

/-- Matrix coefficient between the two occupied shell components of x. -/
def shellMatrixTerm (A : Gas →L[ℂ] Gas) (x : Gas) (i j : ℕ+) : ℂ :=
  inner ℂ (lp.single 2 i (x i) : Gas) (A (lp.single 2 j (x j)))

private theorem finite_mean (A : Gas →L[ℂ] Gas) (x : Gas) (S : Finset ℕ+) :
    Tendsto (windowAverage (orbitExpectation A (cut x S))) atTop (𝓝 (∑ n ∈ S, shellMatrixTerm A x n n)) := by
  let θ (p : ℕ+ × ℕ+) := energy p.2 - energy p.1
  let c (p : ℕ+ × ℕ+) := shellMatrixTerm A x p.1 p.2
  have hex (t : ℝ) : orbitExpectation A (cut x S) t =
      ∑ p ∈ S ×ˢ S, c p * Complex.exp (θ p * Complex.I * (t : ℂ)) := by
    rw [orbitExpectation, orbit_cut, map_sum, Finset.sum_product, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, inner_smul_left, inner_smul_right]
    change conj (clockPhase t i : ℂ) * ((clockPhase t j : ℂ) * shellMatrixTerm A x i j) = _
    rw [← mul_assoc, clock_gap, mul_comm]
  have hc : (∑ p ∈ (S ×ˢ S).filter (fun p => θ p = 0), c p) = ∑ i ∈ S, shellMatrixTerm A x i i := by
    simp only [Finset.sum_filter, Finset.sum_product, θ, energy_gap_zero, c, Finset.sum_ite_eq',
      Finset.mem_product]
    exact Finset.sum_congr rfl fun i hi => if_pos hi
  have h := _root_.RHTower.Weyl.trig_time_average (S ×ˢ S) θ c
  rw [hc] at h
  simpa only [windowAverage, Complex.real_smul, Complex.ofReal_inv, hex] using h

private theorem diagonal_summable (A : Gas →L[ℂ] Gas) (x : Gas) :
    Summable (fun i => shellMatrixTerm A x i i) := by
  apply Summable.of_norm
  have hs : Summable (fun i => ‖x i‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp x).summable (show 0 < (2 : ENNReal).toReal by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left ‖A‖)
  intro i
  let e : Gas := lp.single 2 i (x i)
  have h := (norm_inner_le_norm (𝕜 := ℂ) e (A e)).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _))
  simpa only [e, lp.norm_single (by norm_num : (0 : ENNReal) < 2), sq, mul_left_comm] using h

/-- The mean of any pure-state orbit is its occupation-basis diagonal ensemble. -/
theorem clock_mean_diagonal (A : Gas →L[ℂ] Gas) (x : Gas) :
    Tendsto (windowAverage (orbitExpectation A x)) atTop (𝓝 (∑' n, shellMatrixTerm A x n n)) := by
  have hy := cut_limit x
  have he : Tendsto (fun S => ‖A‖ * (‖x‖+‖cut x S‖) * ‖x-cut x S‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      ((tendsto_const_nhds.mul (tendsto_const_nhds.add hy.norm)).mul (tendsto_const_nhds.sub hy).norm)
  have hu : TendstoUniformly (fun S => windowAverage (orbitExpectation A (cut x S)))
      (windowAverage (orbitExpectation A x)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [he.eventually_lt_const hε] with S hS T
    rw [dist_eq_norm]
    exact (window_error A x (cut x S) T).trans_lt hS
  exact hu.tendsto_of_eventually_tendsto (Eventually.of_forall (finite_mean A x))
    (diagonal_summable A x).hasSum

/-- Clock dephasing of a normalized Gibbs square root recovers the trace of
every bounded observable, for arbitrary initial shell phases. -/
theorem coherent_clock_mean (u : ℕ+ → Circle) (β : TraceTemperature) (A : Gas →L[ℂ] Gas) :
    Tendsto (windowAverage (fun t => coherentReading (fun n => u n * clockPhase t n) β A))
      atTop (𝓝 (gibbsMean A β)) := by
  let x := coherentVector u β
  let s : {s : ℂ // 1 < s.re} := ⟨β.val, β.property⟩
  have horbit (t : ℝ) : coherentVector (fun n => u n * clockPhase t n) β = clockEvolution t x := by
    apply lp.ext
    funext n
    change coherentFactor _ _ n / _ = (clockPhase t n : ℂ) * (coherentFactor u _ n / _)
    rw [coherentFactor, coherentFactor, Circle.coe_mul]
    ring
  have hentry (n : ℕ+) : shellMatrixTerm A x n n =
      (A ∘L gibbsOperator s) (lp.single 2 n (1 : ℂ)) n / riemannZeta β.val := by
    let e : Gas := lp.single 2 n 1
    have hsingle : lp.single 2 n (x n) = x n • e := by rw [← lp.single_smul]; simp
    have hg : gibbsOperator s e = heat s.val n • e := by
      apply lp.ext
      funext j
      rw [gibbsOperator_apply]
      change heat s.val j * e j = heat s.val n * e j
      by_cases hj : j=n
      · rw [hj]
      · simp only [e, lp.single_apply_ne _ _ _ hj, mul_zero]
    have hz := thermalWeight_partition β
    have hw : (thermalWeight β n : ℂ) = heat s.val n := by
      simp only [s, thermalWeight, heat, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
    change shellMatrixTerm A x n n = (A (gibbsOperator s e)) n / _
    rw [shellMatrixTerm, hsingle, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      mul_comm (conj (x n)), Complex.mul_conj, Complex.normSq_eq_norm_sq, hg, map_smul]
    rw [show ‖x n‖^2 = _ from coherentVector_shell u β n, Complex.ofReal_div,
      ← hz, Complex.ofReal_re, hw]
    change _ * inner ℂ (lp.single 2 n (1 : ℂ) : Gas) (A e) = (heat s.val n * (A e) n) / _
    rw [lp.inner_single_left]
    simp only [RCLike.inner_apply, map_one, mul_one]
    ring
  have hlim := clock_mean_diagonal A x
  rw [gibbsMean, traceIdeal_shell_diagonal (hsTraceIdeal_comp_left (gibbs_mem_traceIdeal s) A),
    partition_eq_zeta, ← tsum_div_const, ← funext hentry]
  simpa only [coherentReading, horbit, orbitExpectation] using hlim

private theorem rotating_shift_reading (χ : ℕ+ →* Circle) (β : TraceTemperature)
    (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (a b : ℕ+) (t : ℝ) :
    coherentReading (χ * clockPhase t : ℕ+ →* Circle) β (shiftObservable a b (residueObservable m F)) =
      coherentReading χ β (shiftObservable a b (residueObservable m F)) *
        Complex.exp ((energy b-energy a : ℝ) * Complex.I * (t : ℂ)) := by
  have hf (n : ℕ+) : coherentFactor (χ * clockPhase t : ℕ+ →* Circle) β.val n =
      (clockPhase t n : ℂ) * coherentFactor χ β.val n := by
    simp only [coherentFactor, MonoidHom.mul_apply, Circle.coe_mul]
    ring
  rw [coherentReading_shift (χ * clockPhase t), coherentReading_shift χ,
    coherentReading_residue, coherentReading_residue, hf, hf, map_mul, ← clock_gap]
  ring

/-- For fixed shift words, the partition-pole limit and the long-window limit
hold jointly, with no restriction on their relative speeds. -/
theorem shift_word_joint_dephasing (χ : ℕ+ →* Circle) (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (a b : ℕ+) :
    Tendsto (fun q : TraceTemperature × ℝ => windowAverage (fun t =>
      coherentReading (χ * clockPhase t : ℕ+ →* Circle) q.1
        (shiftObservable a b (residueObservable m F))) q.2) (atPartitionPole ×ˢ atTop)
      (𝓝 (if a = b then ((a : ℕ) : ℂ)⁻¹ * ((∑ j, F j) / (m : ℕ)) else 0)) := by
  let W := shiftObservable a b (residueObservable m F)
  let g := energy b-energy a
  have hf := _root_.RHTower.Weyl.char_term_time_average_tendsto
    (ι := Unit) (fun _ => g) (fun _ => (1 : ℂ)) ()
  simp only [one_mul] at hf
  have h := ((coherent_shift_boundary χ m F a b).comp
    (tendsto_fst : Tendsto Prod.fst (atPartitionPole ×ˢ (atTop : Filter ℝ)) _)).mul
    (hf.comp (tendsto_snd : Tendsto Prod.snd (atPartitionPole ×ˢ (atTop : Filter ℝ)) _))
  have hk : conj (singletonAmplitude χ a) * singletonAmplitude χ b * ((∑ j, F j)/(m : ℕ)) *
      (if g = 0 then 1 else 0) =
      (if a = b then ((a : ℕ) : ℂ)⁻¹ * ((∑ j, F j)/(m : ℕ)) else 0) := by
    by_cases he : a=b
    · subst b
      simp only [g, sub_self, if_true, mul_one]
      congr 1
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hnorm := refinement_born_weight χ 1 a
      have hone : singletonAmplitude χ 1 = 1 := by
        rw [← coherentFactor_one_temperature]
        simp [coherentFactor, energy]
      simp only [refinementAmplitude, hone, div_one, PNat.one_coe, Nat.cast_one, one_div] at hnorm
      rw [hnorm, Complex.ofReal_inv, Complex.ofReal_natCast]
    · rw [if_neg he, if_neg (fun hz => he ((energy_gap_zero a b).mp hz).symm), mul_zero]
  rw [hk] at h
  apply h.congr'
  filter_upwards with q
  change coherentReading χ q.1 W *
    ((q.2 : ℂ)⁻¹ * ∫ t in (0:ℝ)..q.2, Complex.exp ((g : ℂ) * Complex.I * ↑t)) = _
  simp only [rotating_shift_reading, windowAverage, intervalIntegral.integral_const_mul,
    Complex.real_smul, Complex.ofReal_inv, W, g]
  ring

#print axioms clock_mean_diagonal
#print axioms coherent_clock_mean
#print axioms shift_word_joint_dephasing

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
