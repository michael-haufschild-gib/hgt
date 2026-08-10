import GaloisForLFunctions.HTGeometry.AbelianZetaGas.VacuumWeightBound
import GaloisForLFunctions.HTGeometry.QGammaAnalytic

/-!
# The realization defect of one depth mode

The logarithm of the modulus of `1 − x e^{−iθ}` expands into the harmonic ladder
`−∑_r x^r cos(rθ)/r`, so the *defect* of a single depth mode — the loss of modulus caused by the
phase `θ` — is the manifestly nonnegative statistic `∑_r x^r (1 − cos(rθ))/r`.  This is the local
form of the modulus budget: each depth `j` contributes with `x = q^j`, and each harmonic `r`
contributes the weight `q^{jr}/r`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- The phase factor of a mode. -/
noncomputable def modePhase (θ : ℝ) : ℂ := Complex.exp ((-θ : ℝ) * Complex.I)

theorem norm_modePhase (θ : ℝ) : ‖modePhase θ‖ = 1 := by
  rw [modePhase, Complex.norm_exp]
  simp

theorem re_pow_ofReal_mul_modePhase (x θ : ℝ) (n : ℕ) :
    (((x : ℂ) * modePhase θ) ^ n).re = x ^ n * Real.cos ((n : ℝ) * θ) := by
  have hpow : ((x : ℂ) * modePhase θ) ^ n
      = ((x ^ n : ℝ) : ℂ) * Complex.exp (((-((n : ℝ) * θ) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, modePhase, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hpow, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Complex.ofReal_im,
    Real.cos_neg]
  ring

theorem div_natCast_re (w : ℂ) (n : ℕ) : (w / (n : ℂ)).re = w.re / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp

/-- **The harmonic expansion of the log-modulus.** -/
theorem hasSum_log_norm_one_sub (x θ : ℝ) (hx : ‖(x : ℂ) * modePhase θ‖ < 1) :
    HasSum (fun n : ℕ => x ^ n * Real.cos ((n : ℝ) * θ) / (n : ℝ))
      (-Real.log ‖1 - (x : ℂ) * modePhase θ‖) := by
  have h := Complex.hasSum_taylorSeries_neg_log hx
  have hre := Complex.hasSum_re h
  rw [Complex.neg_re, Complex.log_re] at hre
  refine hre.congr_fun fun n => ?_
  rw [div_natCast_re, re_pow_ofReal_mul_modePhase]

theorem norm_ofReal_mul_modePhase (x θ : ℝ) : ‖(x : ℂ) * modePhase θ‖ = |x| := by
  rw [norm_mul, norm_modePhase, mul_one, Complex.norm_real, Real.norm_eq_abs]

@[simp] theorem modePhase_zero : modePhase 0 = 1 := by
  rw [modePhase]
  simp

/-- **The defect of one depth mode.**  The phase `θ` costs exactly the harmonic ladder
`∑_r x^r (1 − cos rθ)/r`, whose terms are all nonnegative. -/
theorem hasSum_modeDefect {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    HasSum (fun n : ℕ => x ^ n * (1 - Real.cos ((n : ℝ) * θ)) / (n : ℝ))
      (Real.log ‖1 - (x : ℂ) * modePhase θ‖ - Real.log (1 - x)) := by
  have hnorm : ∀ φ : ℝ, ‖(x : ℂ) * modePhase φ‖ < 1 := by
    intro φ
    rw [norm_ofReal_mul_modePhase, abs_of_nonneg hx0]
    exact hx1
  have h0 := hasSum_log_norm_one_sub x 0 (hnorm 0)
  have hθ := hasSum_log_norm_one_sub x θ (hnorm θ)
  have hzero : Real.log ‖1 - (x : ℂ) * modePhase 0‖ = Real.log (1 - x) := by
    rw [modePhase_zero, mul_one]
    congr 1
    rw [show (1 : ℂ) - (x : ℂ) = (((1 - x : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hzero] at h0
  have hsub := h0.sub hθ
  have hval : -Real.log (1 - x) - -Real.log ‖1 - (x : ℂ) * modePhase θ‖
      = Real.log ‖1 - (x : ℂ) * modePhase θ‖ - Real.log (1 - x) := by ring
  rw [hval] at hsub
  refine hsub.congr_fun fun n => ?_
  rw [mul_zero, Real.cos_zero]
  ring

theorem modeDefect_term_nonneg {x : ℝ} (hx0 : 0 ≤ x) (θ : ℝ) (n : ℕ) :
    0 ≤ x ^ n * (1 - Real.cos ((n : ℝ) * θ)) / (n : ℝ) := by
  have h1 : (0 : ℝ) ≤ 1 - Real.cos ((n : ℝ) * θ) := by
    have := Real.cos_le_one ((n : ℝ) * θ)
    linarith
  positivity

/-- The defect of one depth mode is nonnegative. -/
theorem modeDefect_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    0 ≤ Real.log ‖1 - (x : ℂ) * modePhase θ‖ - Real.log (1 - x) :=
  (hasSum_modeDefect hx0 hx1 θ).nonneg (modeDefect_term_nonneg hx0 θ)

/-! ## The `(depth, harmonic)` ladder -/

/-- The `(j, r)`-term of the defect ladder: depth `j+1`, harmonic `r+1`, weight `q^{(j+1)(r+1)}`. -/
noncomputable def ladderTerm (q θ : ℝ) (jr : ℕ × ℕ) : ℝ :=
  q ^ ((jr.1 + 1) * (jr.2 + 1)) * (1 - Real.cos (((jr.2 : ℝ) + 1) * θ)) / ((jr.2 : ℝ) + 1)

theorem ladderTerm_nonneg {q : ℝ} (hq0 : 0 ≤ q) (θ : ℝ) (jr : ℕ × ℕ) :
    0 ≤ ladderTerm q θ jr := by
  have h1 : (0 : ℝ) ≤ 1 - Real.cos (((jr.2 : ℝ) + 1) * θ) := by
    have := Real.cos_le_one (((jr.2 : ℝ) + 1) * θ)
    linarith
  rw [ladderTerm]
  positivity

/-- **The defect ladder is summable.**  Each term is at most `2 q^{j+r+1}`. -/
theorem summable_ladderTerm {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (θ : ℝ) :
    Summable (ladderTerm q θ) := by
  have hgeom : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq0.le hq1
  have hprod : Summable fun jr : ℕ × ℕ => q ^ jr.1 * q ^ jr.2 :=
    hgeom.mul_of_nonneg hgeom (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_nonneg_of_le (fun jr => ladderTerm_nonneg hq0.le θ jr) (fun jr => ?_)
    (hprod.mul_left (2 * q))
  have hexp : jr.1 + jr.2 + 1 ≤ (jr.1 + 1) * (jr.2 + 1) := by nlinarith [Nat.zero_le (jr.1 * jr.2)]
  have hpow : q ^ ((jr.1 + 1) * (jr.2 + 1)) ≤ q ^ (jr.1 + jr.2 + 1) :=
    pow_le_pow_of_le_one hq0.le hq1.le hexp
  have hcos2 : 1 - Real.cos (((jr.2 : ℝ) + 1) * θ) ≤ 2 := by
    have := Real.neg_one_le_cos (((jr.2 : ℝ) + 1) * θ)
    linarith
  have hcos0 : (0 : ℝ) ≤ 1 - Real.cos (((jr.2 : ℝ) + 1) * θ) := by
    have := Real.cos_le_one (((jr.2 : ℝ) + 1) * θ)
    linarith
  have hden : (1 : ℝ) ≤ (jr.2 : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (jr.2 : ℝ) := Nat.cast_nonneg _
    linarith
  have hqpow : (0 : ℝ) < q ^ ((jr.1 + 1) * (jr.2 + 1)) := by positivity
  have hstep : ladderTerm q θ jr ≤ q ^ ((jr.1 + 1) * (jr.2 + 1)) * 2 := by
    rw [ladderTerm, div_le_iff₀ (by linarith)]
    nlinarith
  have hsplit : q ^ (jr.1 + jr.2 + 1) = q * (q ^ jr.1 * q ^ jr.2) := by
    rw [pow_add, pow_add, pow_one]
    ring
  nlinarith [hstep, hpow, hsplit]

/-- **The defect ladder of a single depth.** -/
theorem hasSum_depthLadder {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (θ : ℝ) (j : ℕ) :
    HasSum (fun r : ℕ => ladderTerm q θ (j, r))
      (Real.log ‖1 - ((q ^ (j + 1) : ℝ) : ℂ) * modePhase θ‖ - Real.log (1 - q ^ (j + 1))) := by
  have hx0 : (0 : ℝ) ≤ q ^ (j + 1) := by positivity
  have hx1 : q ^ (j + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have h := hasSum_modeDefect hx0 hx1 θ
  have hshift := (hasSum_nat_add_iff' (f := fun n : ℕ =>
    (q ^ (j + 1)) ^ n * (1 - Real.cos ((n : ℝ) * θ)) / (n : ℝ)) 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, div_zero, sub_zero] at hshift
  refine hshift.congr_fun fun r => ?_
  rw [ladderTerm, ← pow_mul]
  push_cast
  ring_nf

/-- **(GAS3.1).**  The depth-wise defects sum to the `(depth, harmonic)` ladder
`∑_{j,r} q^{jr}(1 − cos rθ)/r`. -/
theorem hasSum_defectLadder {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (θ : ℝ) :
    HasSum (fun j : ℕ =>
        Real.log ‖1 - ((q ^ (j + 1) : ℝ) : ℂ) * modePhase θ‖ - Real.log (1 - q ^ (j + 1)))
      (∑' jr : ℕ × ℕ, ladderTerm q θ jr) :=
  (summable_ladderTerm hq0 hq1 θ).hasSum.prod_fiberwise (hasSum_depthLadder hq0 hq1 θ)

/-! ## The ladder attached to the `q`-Pochhammer products -/

/-- The phase-twisted `q`-Pochhammer product `(q e^{−iθ}; q)_∞`. -/
noncomputable def defectProduct (q : RealEulerNome) (θ : ℝ) : ℂ :=
  ∏' j : ℕ, (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ)

theorem summable_norm_defectFactor (q : RealEulerNome) (θ : ℝ) :
    Summable (fun j : ℕ => ‖((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ‖) := by
  have hgeom : Summable fun j : ℕ => q.val ^ (j + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one q.pos.le q.lt_one)
  refine hgeom.congr fun j => ?_
  rw [norm_ofReal_mul_modePhase, abs_of_nonneg (pow_nonneg q.pos.le _)]

theorem multipliable_defectFactor (q : RealEulerNome) (θ : ℝ) :
    Multipliable (fun j : ℕ => 1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ) := by
  have h := Complex.multipliable_one_add_of_summable
    (f := fun j : ℕ => -(((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ))
    ((summable_norm_defectFactor q θ).of_norm.neg)
  refine h.congr fun j => ?_
  ring

theorem defectFactor_ne_zero (q : RealEulerNome) (θ : ℝ) (j : ℕ) :
    (1 : ℂ) - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ ≠ 0 := by
  intro h
  have hnorm : ‖((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ‖ = 1 := by
    have : ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ = 1 := by
      have := sub_eq_zero.mp h
      exact this.symm
    rw [this, norm_one]
  rw [norm_ofReal_mul_modePhase, abs_of_nonneg (pow_nonneg q.pos.le _)] at hnorm
  have hlt : q.val ^ (j + 1) < 1 := pow_lt_one₀ q.pos.le q.lt_one (by omega)
  linarith

theorem defectProduct_ne_zero (q : RealEulerNome) (θ : ℝ) : defectProduct q θ ≠ 0 := by
  have hval : defectProduct q θ
      = ∏' j : ℕ, (1 + -(((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ)) := by
    refine tprod_congr fun j => ?_
    ring
  rw [hval]
  refine tprod_one_add_ne_zero_of_summable ?_
    ((summable_norm_defectFactor q θ).congr fun j => (norm_neg _).symm)
  intro j
  have h := defectFactor_ne_zero q θ j
  intro hcon
  exact h (by rw [← hcon]; ring)

/-- **(GAS3.1), attached form.**  The log-modulus defect of the phase-twisted `q`-Pochhammer
product against the untwisted one is exactly the `(depth, harmonic)` ladder. -/
theorem log_norm_defectProduct (q : RealEulerNome) (θ : ℝ) :
    Real.log ‖defectProduct q θ‖ - Real.log (realQFactorialInf q)
      = ∑' jr : ℕ × ℕ, ladderTerm q.val θ jr := by
  have hP : Filter.Tendsto
      (fun n => ∏ j ∈ Finset.range n, (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ))
      Filter.atTop (nhds (defectProduct q θ)) :=
    (multipliable_defectFactor q θ).hasProd.tendsto_prod_nat
  have hR := realQFactorial_tendsto q
  have hlogP : Filter.Tendsto
      (fun n => Real.log ‖∏ j ∈ Finset.range n,
        (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ)‖)
      Filter.atTop (nhds (Real.log ‖defectProduct q θ‖)) := by
    have hcont : ContinuousAt (fun z : ℂ => Real.log ‖z‖) (defectProduct q θ) :=
      (Real.continuousAt_log
        (norm_ne_zero_iff.mpr (defectProduct_ne_zero q θ))).comp continuous_norm.continuousAt
    exact hcont.tendsto.comp hP
  have hlogR : Filter.Tendsto (fun n => Real.log (realQFactorial q n))
      Filter.atTop (nhds (Real.log (realQFactorialInf q))) :=
    (Real.continuousAt_log (realQFactorialInf_ne_zero q)).tendsto.comp hR
  have heq : ∀ n : ℕ,
      Real.log ‖∏ j ∈ Finset.range n, (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ)‖
          - Real.log (realQFactorial q n)
        = ∑ j ∈ Finset.range n,
          (Real.log ‖1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase θ‖
            - Real.log (1 - q.val ^ (j + 1))) := by
    intro n
    rw [norm_prod, Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (defectFactor_ne_zero q θ j)),
      realQFactorial, Real.log_prod (fun j _ => (realQFactorial_factor_pos q j).ne'),
      Finset.sum_sub_distrib]
  have hlimit := hlogP.sub hlogR
  rw [Filter.tendsto_congr heq] at hlimit
  exact tendsto_nhds_unique hlimit
    (hasSum_defectLadder q.pos q.lt_one θ).tendsto_sum_nat

/-! ## The characteristic function of one prime -/

/-- The phase angle of the mode at imaginary argument `t`:  `θ = −t log q = t σ log p`. -/
noncomputable def phaseAngle (q : RealEulerNome) (t : ℝ) : ℝ := -(t * Real.log q.val)

theorem qcpow_mul_I (q : RealEulerNome) (t : ℝ) :
    (q.val : ℂ) ^ ((t : ℂ) * Complex.I) = modePhase (phaseAngle q t) := by
  rw [Complex.cpow_def_of_ne_zero q.complex_ne_zero, modePhase, phaseAngle]
  congr 1
  rw [← Complex.ofReal_log q.pos.le]
  push_cast
  ring

theorem qDenomFactor_eq_defectFactor (q : RealEulerNome) (t : ℝ) (k : ℕ) :
    qDenomFactor q k (1 + (t : ℂ) * Complex.I)
      = 1 - ((q.val ^ (k + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t) := by
  rw [qDenomFactor]
  congr 1
  have hsplit : (1 : ℂ) + (t : ℂ) * Complex.I + (k : ℂ)
      = ((k + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.cpow_add _ _ q.complex_ne_zero, Complex.cpow_natCast, qcpow_mul_I]
  congr 1
  push_cast
  ring

theorem qDenomProduct_eq_defectProduct (q : RealEulerNome) (t : ℝ) :
    qDenomProduct q (1 + (t : ℂ) * Complex.I) = defectProduct q (phaseAngle q t) := by
  rw [qDenomProduct, defectProduct]
  exact tprod_congr fun k => qDenomFactor_eq_defectFactor q t k

/-- **Theorem 2.1 (GAS3.1).**  The realization defect of the characteristic function
`φ(t) = Γ_q(1 + it)` is the `(depth, harmonic)` ladder `∑_{j,r} q^{jr}(1 − cos rθ)/r`. -/
theorem neg_log_norm_qGammaOn (q : RealEulerNome) (t : ℝ) :
    -Real.log ‖qGammaOn q (1 + (t : ℂ) * Complex.I)‖
      = ∑' jr : ℕ × ℕ, ladderTerm q.val (phaseAngle q t) jr := by
  have hbase : (0 : ℝ) < 1 - q.val := by
    have := q.lt_one
    linarith
  have hnormcpow : ‖((1 - q.val : ℝ) : ℂ) ^ (1 - (1 + (t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
    have hre : (1 - (1 + (t : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.rpow_zero]
  have hQpos : 0 < realQFactorialInf q := realQFactorialInf_pos q
  have hDne : defectProduct q (phaseAngle q t) ≠ 0 := defectProduct_ne_zero q _
  have hnorm : ‖qGammaOn q (1 + (t : ℂ) * Complex.I)‖
      = realQFactorialInf q / ‖defectProduct q (phaseAngle q t)‖ := by
    rw [qGammaOn, norm_mul, hnormcpow, one_mul, norm_div,
      qDenomProduct_eq_defectProduct, Complex.norm_real, Real.norm_of_nonneg hQpos.le]
  rw [hnorm, Real.log_div hQpos.ne' (norm_ne_zero_iff.mpr hDne), neg_sub,
    log_norm_defectProduct]

/-! ## The leading term and the bounded remainder -/

@[simp] theorem ladderTerm_zero (q θ : ℝ) : ladderTerm q θ (0, 0) = q * (1 - Real.cos θ) := by
  rw [ladderTerm]
  norm_num

theorem hasSum_majorant (q : RealEulerNome) :
    HasSum (fun jr : ℕ × ℕ => q.val ^ (jr.1 + 1) * q.val ^ jr.2)
      (q.val / (1 - q.val) ^ 2) := by
  have hden : (0 : ℝ) < 1 - q.val := by have := q.lt_one; linarith
  have hgeom : Summable fun n : ℕ => q.val ^ n :=
    summable_geometric_of_lt_one q.pos.le q.lt_one
  have hgeom1 : Summable fun n : ℕ => q.val ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hgeom
  have hprod : Summable fun jr : ℕ × ℕ => q.val ^ (jr.1 + 1) * q.val ^ jr.2 :=
    hgeom1.mul_of_nonneg hgeom (fun n => by positivity) (fun n => by positivity)
  have hmul := hgeom1.tsum_mul_tsum hgeom hprod
  have hval1 : ∑' n : ℕ, q.val ^ (n + 1) = q.val / (1 - q.val) := by
    rw [tsum_eq_zero_add hgeom]
    · rw [tsum_geometric_of_lt_one q.pos.le q.lt_one]
      field_simp
    · exact hgeom
  have hval2 : ∑' n : ℕ, q.val ^ n = (1 - q.val)⁻¹ :=
    tsum_geometric_of_lt_one q.pos.le q.lt_one
  rw [hval1, hval2] at hmul
  have hfinal : q.val / (1 - q.val) * (1 - q.val)⁻¹ = q.val / (1 - q.val) ^ 2 := by
    field_simp
    ring
  rw [hfinal] at hmul
  rw [← hmul]
  exact hprod.hasSum

/-- **The remainder of the defect ladder is quadratically small.**  Only the depth-one,
harmonic-one term `q(1 − cos θ)` is of first order; all other `(j,r)` contribute `O(q²)`. -/
theorem abs_tsum_ladder_sub_leading_le (q : RealEulerNome) (θ : ℝ) :
    |(∑' jr : ℕ × ℕ, ladderTerm q.val θ jr) - q.val * (1 - Real.cos θ)|
      ≤ 4 * q.val ^ 2 / (1 - q.val) ^ 2 := by
  classical
  have hq0 := q.pos
  have hq1 := q.lt_one
  have hden : (0 : ℝ) < 1 - q.val := by linarith
  have hlad := summable_ladderTerm hq0 hq1 θ
  have hMaj := hasSum_majorant q
  have hMsum : Summable (fun jr : ℕ × ℕ => 2 * (q.val ^ (jr.1 + 1) * q.val ^ jr.2)) :=
    (hMaj.summable).mul_left 2
  have hbound : ∀ jr : ℕ × ℕ,
      ladderTerm q.val θ jr ≤ 2 * (q.val ^ (jr.1 + 1) * q.val ^ jr.2) := by
    intro jr
    have hexp : jr.1 + jr.2 + 1 ≤ (jr.1 + 1) * (jr.2 + 1) := by
      nlinarith [Nat.zero_le (jr.1 * jr.2)]
    have hpow : q.val ^ ((jr.1 + 1) * (jr.2 + 1)) ≤ q.val ^ (jr.1 + jr.2 + 1) :=
      pow_le_pow_of_le_one hq0.le hq1.le hexp
    have hcos2 : 1 - Real.cos (((jr.2 : ℝ) + 1) * θ) ≤ 2 := by
      have := Real.neg_one_le_cos (((jr.2 : ℝ) + 1) * θ)
      linarith
    have hcos0 : (0 : ℝ) ≤ 1 - Real.cos (((jr.2 : ℝ) + 1) * θ) := by
      have := Real.cos_le_one (((jr.2 : ℝ) + 1) * θ)
      linarith
    have hd : (1 : ℝ) ≤ (jr.2 : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (jr.2 : ℝ) := Nat.cast_nonneg _
      linarith
    have hqpow : (0 : ℝ) < q.val ^ ((jr.1 + 1) * (jr.2 + 1)) := by positivity
    have hsplit : q.val ^ (jr.1 + jr.2 + 1) = q.val ^ (jr.1 + 1) * q.val ^ jr.2 := by
      rw [← pow_add]
      ring_nf
    rw [ladderTerm, div_le_iff₀ (by linarith)]
    nlinarith
  -- split off the leading term on both sides
  have hsplitL := hlad.tsum_eq_add_tsum_ite (0, 0)
  have hsplitM := hMsum.tsum_eq_add_tsum_ite (0, 0)
  have hiteL : Summable (fun jr : ℕ × ℕ => ite (jr = (0, 0)) 0 (ladderTerm q.val θ jr)) := by
    refine Summable.of_nonneg_of_le (fun jr => ?_) (fun jr => ?_) hlad
    · split
      · exact le_rfl
      · exact ladderTerm_nonneg hq0.le θ jr
    · split
      · exact ladderTerm_nonneg hq0.le θ jr
      · exact le_rfl
  have hiteM : Summable
      (fun jr : ℕ × ℕ => ite (jr = (0, 0)) 0 (2 * (q.val ^ (jr.1 + 1) * q.val ^ jr.2))) := by
    refine Summable.of_nonneg_of_le (fun jr => ?_) (fun jr => ?_) hMsum
    · split
      · exact le_rfl
      · positivity
    · split
      · positivity
      · exact le_rfl
  have hle : ∑' jr : ℕ × ℕ, ite (jr = (0, 0)) 0 (ladderTerm q.val θ jr)
      ≤ ∑' jr : ℕ × ℕ, ite (jr = (0, 0)) 0 (2 * (q.val ^ (jr.1 + 1) * q.val ^ jr.2)) := by
    refine hiteL.tsum_le_tsum (fun jr => ?_) hiteM
    split
    · exact le_rfl
    · exact hbound jr
  have hnn : 0 ≤ ∑' jr : ℕ × ℕ, ite (jr = (0, 0)) 0 (ladderTerm q.val θ jr) := by
    refine hiteL.tsum_nonneg fun jr => ?_
    split
    · exact le_rfl
    · exact ladderTerm_nonneg hq0.le θ jr
  have hMval : ∑' jr : ℕ × ℕ, (2 : ℝ) * (q.val ^ (jr.1 + 1) * q.val ^ jr.2)
      = 2 * (q.val / (1 - q.val) ^ 2) := by
    rw [tsum_mul_left, hMaj.tsum_eq]
  have hMlead : (2 : ℝ) * (q.val ^ ((0 : ℕ) + 1) * q.val ^ (0 : ℕ)) = 2 * q.val := by
    norm_num
  rw [hsplitM, hMlead, hMval] at *
  rw [hsplitL, ladderTerm_zero]
  simp only [add_sub_cancel_left]
  rw [abs_of_nonneg hnn]
  have hrest : ∑' jr : ℕ × ℕ, ite (jr = (0, 0)) 0 (2 * (q.val ^ (jr.1 + 1) * q.val ^ jr.2))
      = 2 * (q.val / (1 - q.val) ^ 2) - 2 * q.val := by linarith
  rw [hrest] at hle
  have hfinal : 2 * (q.val / (1 - q.val) ^ 2) - 2 * q.val ≤ 4 * q.val ^ 2 / (1 - q.val) ^ 2 := by
    rw [div_sub' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg q.val, sq_nonneg (1 - q.val), hq0, hq1]
  linarith

end GaloisForLFunctions.HTGeometry
