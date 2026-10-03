import GaloisForLFunctions.HTGeometry.LocalExponentialPhaseFusion
import GaloisForLFunctions.HTGeometry.EulerShellTiltInformation

/-!
# The Euler-shell realization of local-exponential test closure

The marked high-exponent shell gives the finite atomic source
`μ_{m,σ} = S_m(σ)^{-1} Σ_{n ∈ A_m} n^{-σ} δ_{log n}` (**(LEF.20)**), supported in `[log 2, ∞)`, with
`∫ e^{ax} dμ_{m,σ} = S_m(σ - a)/S_m(σ)` (**(LEF.21)**).  Hence:

* **Theorem 6.1 (LEF.22).**  For a bounded Hermitian packet `J_n` on the shell, positivity of every
  `J_n`, positivity of every block Hankel section `[Σ_n n^{-σ} (log n)^{i+j} J_n]` and positivity of
  every rational phase test are equivalent.
* **Theorem 7.1 (LEF.23)–(LEF.25).**  For every depth `N` there is a bounded scalar packet, negative at
  one atom, whose Hankel sections of order at most `N` are all positive definite: the detecting depth
  has no uniform bound.
* **§8 (LEF.26).**  The exponential chart `∫ e^{tx} dμ_{m,σ} < ∞` holds exactly for `t < σ - 1`, and
  the shell sum diverges for every exponent `≤ 1`, so the half-density value `σ = 1/m ≤ 1` lies outside
  the normalized positive chart.
-/

namespace HTGeometry

open MeasureTheory Complex Filter Topology Set
open scoped Matrix ComplexOrder ENNReal
open GaloisForLFunctions.HTGeometry

variable {m : ℕ} {σ : ℝ}

/-! ## The Euler-shell source measure -/

/-- The normalized shell weight `n^{-σ}/S_m(σ)`. -/
noncomputable def eulerShellAtomWeight (m : ℕ) (σ : ℝ) (n : EulerShell m) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ

/-- **(LEF.20)** `μ_{m,σ} = S_m(σ)^{-1} Σ_{n ∈ A_m} n^{-σ} δ_{log n}`. -/
noncomputable def eulerShellMeasure (m : ℕ) (σ : ℝ) : Measure ℝ :=
  Measure.sum fun n : EulerShell m => ENNReal.ofReal (eulerShellAtomWeight m σ n) • Measure.dirac (Real.log (n : ℕ))

theorem eulerShellAtomWeight_pos (hm : 1 ≤ m) (hσ : 1 < σ) (n : EulerShell m) : 0 < eulerShellAtomWeight m σ n :=
  div_pos (Real.rpow_pos_of_pos (eulerShell_cast_pos n) _) (eulerShellSum_pos hm hσ)

theorem hasSum_eulerShellAtomWeight (hm : 1 ≤ m) (hσ : 1 < σ) : HasSum (eulerShellAtomWeight m σ) 1 := by
  have h := ((summable_shell m hσ).hasSum).div_const (eulerShellSum m σ)
  rw [show (∑' b : EulerShell m, ((b : ℕ) : ℝ) ^ (-σ)) = eulerShellSum m σ from rfl,
    div_self (eulerShellSum_pos hm hσ).ne'] at h
  exact h

theorem lintegral_eulerShellMeasure (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂eulerShellMeasure m σ = ∑' n : EulerShell m, ENNReal.ofReal (eulerShellAtomWeight m σ n) * f (Real.log (n : ℕ)) := by
  rw [eulerShellMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem eulerShellMeasure_univ (hm : 1 ≤ m) (hσ : 1 < σ) : eulerShellMeasure m σ univ = 1 := by
  rw [← setLIntegral_one, Measure.restrict_univ, lintegral_eulerShellMeasure]
  simp only [mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (eulerShellAtomWeight_pos hm hσ n).le) (hasSum_eulerShellAtomWeight hm hσ).summable,
    (hasSum_eulerShellAtomWeight hm hσ).tsum_eq, ENNReal.ofReal_one]

theorem isFiniteMeasure_eulerShellMeasure (hm : 1 ≤ m) (hσ : 1 < σ) :
    IsFiniteMeasure (eulerShellMeasure m σ) :=
  ⟨by rw [eulerShellMeasure_univ hm hσ]; exact ENNReal.one_lt_top⟩

/-- Almost-everywhere statements for `μ_{m,σ}` are statements about every atom. -/
theorem ae_eulerShellMeasure_iff (hm : 1 ≤ m) (hσ : 1 < σ) {P : ℝ → Prop} :
    (∀ᵐ x ∂eulerShellMeasure m σ, P x) ↔ ∀ n : EulerShell m, P (Real.log (n : ℕ)) := by
  rw [eulerShellMeasure, Filter.Eventually, Measure.ae_sum_eq, Filter.mem_iSup]
  refine forall_congr' fun n => ?_
  rw [Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 (eulerShellAtomWeight_pos hm hσ n)).ne', ae_dirac_eq]
  rfl

theorem aestronglyMeasurable_eulerShellMeasure {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] (f : ℝ → E) :
    AEStronglyMeasurable f (eulerShellMeasure m σ) := by
  rw [eulerShellMeasure, aestronglyMeasurable_sum_measure_iff]
  intro n
  refine AEStronglyMeasurable.smul_measure ?_ _
  refine (aestronglyMeasurable_const (b := f (Real.log (n : ℕ)))).congr ?_
  rw [Filter.EventuallyEq, ae_dirac_eq]
  rfl

theorem integral_eulerShellMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f (eulerShellMeasure m σ)) (hσ' : ∀ n : EulerShell m, 0 ≤ eulerShellAtomWeight m σ n) :
    ∫ x, f x ∂eulerShellMeasure m σ = ∑' n : EulerShell m, eulerShellAtomWeight m σ n • f (Real.log (n : ℕ)) := by
  rw [eulerShellMeasure, integral_sum_measure hf]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hσ' n)]

theorem eulerShellAtomWeight_mul_exp (n : EulerShell m) (a : ℝ) :
    eulerShellAtomWeight m σ n * Real.exp (a * Real.log (n : ℕ)) = ((n : ℕ) : ℝ) ^ (-(σ - a)) / eulerShellSum m σ := by
  have hn := eulerShell_cast_pos n
  rw [eulerShellAtomWeight, mul_comm a, ← Real.rpow_def_of_pos hn, div_mul_eq_mul_div, ← Real.rpow_add hn]
  ring_nf

/-- **(LEF.21)** `∫ e^{ax} dμ_{m,σ} = S_m(σ - a)/S_m(σ)` for `σ - a > 1`. -/
theorem integral_exp_eulerShellMeasure (hm : 1 ≤ m) (hσ : 1 < σ) {a : ℝ} (ha : 1 < σ - a) :
    Integrable (fun x => Real.exp (a * x)) (eulerShellMeasure m σ) ∧
    ∫ x, Real.exp (a * x) ∂eulerShellMeasure m σ = eulerShellSum m (σ - a) / eulerShellSum m σ := by
  have hS := eulerShellSum_pos hm hσ
  have hsum : HasSum (fun n : EulerShell m => eulerShellAtomWeight m σ n * Real.exp (a * Real.log (n : ℕ)))
      (eulerShellSum m (σ - a) / eulerShellSum m σ) := by
    simp_rw [eulerShellAtomWeight_mul_exp]
    exact (summable_shell m ha).hasSum.div_const _
  have hint : Integrable (fun x => Real.exp (a * x)) (eulerShellMeasure m σ) := by
    refine ⟨aestronglyMeasurable_eulerShellMeasure _, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le),
      lintegral_eulerShellMeasure]
    have : ∀ n : EulerShell m, ENNReal.ofReal (eulerShellAtomWeight m σ n) * ENNReal.ofReal (Real.exp (a * Real.log (n : ℕ))) =
        ENNReal.ofReal (eulerShellAtomWeight m σ n * Real.exp (a * Real.log (n : ℕ))) := fun n =>
      (ENNReal.ofReal_mul (eulerShellAtomWeight_pos hm hσ n).le).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (eulerShellAtomWeight_pos hm hσ n).le (Real.exp_pos _).le)
      hsum.summable]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eulerShellMeasure hint fun n => (eulerShellAtomWeight_pos hm hσ n).le]
  simp_rw [smul_eq_mul]
  exact hsum.tsum_eq

/-- **(LEF.1) on the Euler shell.**  For `0 < a < σ - 1` the source has the bilateral exponential
window: it is supported in `[log 2, ∞)`. -/
theorem integrable_exp_abs_eulerShellMeasure (hm : 1 ≤ m) (hσ : 1 < σ) {a : ℝ} (ha : 1 < σ - a) :
    Integrable (fun x => Real.exp (a * |x|)) (eulerShellMeasure m σ) := by
  refine (integral_exp_eulerShellMeasure hm hσ ha).1.congr ?_
  rw [Filter.EventuallyEq, ae_eulerShellMeasure_iff hm hσ]
  intro n
  rw [abs_of_nonneg (log_eulerShell_nonneg n)]

/-! ## Theorem 6.1: Euler-shell complete test closure -/

section TestClosure

variable {d : ℕ}

theorem log_eulerShell_injective : Function.Injective fun n : EulerShell m => Real.log (n : ℕ) :=
  fun a b h => Subtype.ext (by exact_mod_cast Real.log_injOn_pos (eulerShell_cast_pos a) (eulerShell_cast_pos b) h)

/-- A packet on the shell, extended to the line: `J̃(log n) = J_n`, zero off the atoms. -/
noncomputable def shellExtend {E : Type*} [Zero E] (J : EulerShell m → E) : ℝ → E :=
  Function.extend (fun n : EulerShell m => Real.log (n : ℕ)) J 0

theorem shellExtend_log {E : Type*} [Zero E] (J : EulerShell m → E) (n : EulerShell m) :
    shellExtend J (Real.log (n : ℕ)) = J n :=
  log_eulerShell_injective.extend_apply J 0 n

/-- **(LEF.22)** The unnormalized Euler-shell block Hankel section
`[Σ_n n^{-σ} (log n)^{i+j} J_n]_{i,j < N}`. -/
noncomputable def eulerShellHankel (m : ℕ) (σ : ℝ) (J : EulerShell m → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℂ :=
  Matrix.of fun p q => ∑' n : EulerShell m,
    ((((n : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * ((Real.log (n : ℕ) : ℝ) : ℂ) ^ ((p.1 : ℕ) + (q.1 : ℕ)) * J n p.2 q.2

/-- **(LEF.22)** The unnormalized phase test `Σ_n n^{-σ} p(log n)* J_n p(log n)`. -/
noncomputable def eulerShellPhaseForm (m : ℕ) (σ : ℝ) (J : EulerShell m → Matrix (Fin d) (Fin d) ℂ) {r : ℕ}
    (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) : ℂ :=
  ∑' n : EulerShell m, ((((n : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * matQuad (J n) (phasePacket q v (Real.log (n : ℕ)))

theorem matQuad_smul_matrix {n : Type*} [Fintype n] (c : ℂ) (M : Matrix n n ℂ) (v : n → ℂ) :
    matQuad (c • M) v = c * matQuad M v := by
  simp only [matQuad, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem re_ofReal_mul_nonneg_iff {c : ℝ} (hc : 0 < c) (z : ℂ) : 0 ≤ ((c : ℂ) * z).re ↔ 0 ≤ z.re := by
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg_iff_of_pos_left hc

variable (hm : 1 ≤ m) (hσ : 1 < σ)
include hm hσ

theorem shellExtend_bound {J : EulerShell m → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hJ : ∀ n k l, ‖J n k l‖ ≤ C) :
    ∀ᵐ x ∂eulerShellMeasure m σ, ∀ k l, ‖shellExtend J x k l‖ ≤ C := by
  rw [ae_eulerShellMeasure_iff hm hσ]
  intro n
  rw [shellExtend_log]
  exact hJ n

theorem blockHankel_eulerShellMeasure {J : EulerShell m → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ n k l, ‖J n k l‖ ≤ C) (N : ℕ) :
    blockHankel (eulerShellMeasure m σ) (shellExtend J) N =
      (((eulerShellSum m σ)⁻¹ : ℝ) : ℂ) • eulerShellHankel m σ J N := by
  haveI := isFiniteMeasure_eulerShellMeasure hm hσ
  have ha : 1 < σ - (σ - 1) / 2 := by linarith
  have hexp := integrable_exp_abs_eulerShellMeasure hm hσ ha
  ext p q
  simp only [blockHankel, matrixMoment, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, eulerShellHankel]
  rw [integral_eulerShellMeasure (integrable_pow_mul_entry (by linarith) hexp hC
    (fun k l => aestronglyMeasurable_eulerShellMeasure _) (shellExtend_bound hm hσ hJ) _ _ _)
    fun n => (eulerShellAtomWeight_pos hm hσ n).le, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [shellExtend_log, Complex.real_smul, eulerShellAtomWeight]
  push_cast
  ring

theorem phaseForm_eulerShellMeasure {J : EulerShell m → Matrix (Fin d) (Fin d) ℂ} {C : ℝ}
    (hJ : ∀ n k l, ‖J n k l‖ ≤ C) {r : ℕ} (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ) :
    phaseForm (eulerShellMeasure m σ) (shellExtend J) q v =
      (((eulerShellSum m σ)⁻¹ : ℝ) : ℂ) * eulerShellPhaseForm m σ J q v := by
  haveI := isFiniteMeasure_eulerShellMeasure hm hσ
  rw [phaseForm, integral_eulerShellMeasure (integrable_matQuad_phasePacket
    (fun k l => aestronglyMeasurable_eulerShellMeasure _) (shellExtend_bound hm hσ hJ) q v)
    fun n => (eulerShellAtomWeight_pos hm hσ n).le, eulerShellPhaseForm, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [shellExtend_log, Complex.real_smul, eulerShellAtomWeight]
  push_cast
  ring

/-- **Theorem 6.1 (LEF.22) Euler-shell complete test closure.**  For a bounded Hermitian packet on
the active shell, positivity of every atom, positivity of every unnormalized block Hankel section and
positivity of every rational phase test are equivalent. -/
theorem eulerShell_complete_test_closure (J : EulerShell m → Matrix (Fin d) (Fin d) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ n k l, ‖J n k l‖ ≤ C) (hherm : ∀ n, (J n).IsHermitian) :
    ((∀ n, (J n).PosSemidef) ↔
      ∀ (N : ℕ) (v : Fin N × Fin d → ℂ), 0 ≤ (matQuad (eulerShellHankel m σ J N) v).re) ∧
    ((∀ n, (J n).PosSemidef) ↔
      ∀ (r : ℕ) (q : Fin r → ℚ) (v : Fin r → Fin d → ℂ), 0 ≤ (eulerShellPhaseForm m σ J q v).re) := by
  haveI := isFiniteMeasure_eulerShellMeasure hm hσ
  have ha : 1 < σ - (σ - 1) / 2 := by linarith
  have hfus := phase_hankel_source_fusion (J := shellExtend J) (C := C) (by linarith : 0 < (σ - 1) / 2)
    (integrable_exp_abs_eulerShellMeasure hm hσ ha) hC (fun k l => aestronglyMeasurable_eulerShellMeasure _)
    (shellExtend_bound hm hσ hJ)
    (by rw [ae_eulerShellMeasure_iff hm hσ]; intro n; rw [shellExtend_log]; exact hherm n)
  have hsrc : (∀ᵐ x ∂eulerShellMeasure m σ, (shellExtend J x).PosSemidef) ↔ ∀ n, (J n).PosSemidef := by
    rw [ae_eulerShellMeasure_iff hm hσ]
    simp only [shellExtend_log]
  have hSinv : 0 < (eulerShellSum m σ)⁻¹ := inv_pos.2 (eulerShellSum_pos hm hσ)
  refine ⟨hsrc.symm.trans (hfus.1.trans (forall_congr' fun N => forall_congr' fun v => ?_)),
    hsrc.symm.trans (hfus.2.trans (forall_congr' fun r => forall_congr' fun q => forall_congr' fun v => ?_))⟩
  · rw [blockHankel_eulerShellMeasure hm hσ hC hJ, matQuad_smul_matrix]
    exact re_ofReal_mul_nonneg_iff hSinv _
  · rw [phaseForm_eulerShellMeasure hm hσ hJ]
    exact re_ofReal_mul_nonneg_iff hSinv _

end TestClosure

/-! ## Theorem 7.1: no uniform finite depth -/

section NoUniformDepth

/-- The unnormalized scalar Hankel section `[Σ_n n^{-σ} (log n)^{i+j} J_n]_{i,j < N}`. -/
noncomputable def eulerShellScalarHankel (m : ℕ) (σ : ℝ) (J : EulerShell m → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ∑' n : EulerShell m, ((n : ℕ) : ℝ) ^ (-σ) * Real.log (n : ℕ) ^ ((i : ℕ) + (j : ℕ)) * J n

/-- The polynomial `p_v(x) = Σ_i v_i x^i` of a coefficient vector. -/
def hankelCoeffPoly {N : ℕ} (v : Fin N → ℝ) (x : ℝ) : ℝ := ∑ i, v i * x ^ (i : ℕ)

theorem summable_hankel_term (hσ : 1 < σ) {J : EulerShell m → ℝ} (hJ : ∀ n, |J n| ≤ 1) (k : ℕ) :
    Summable fun n : EulerShell m => ((n : ℕ) : ℝ) ^ (-σ) * Real.log (n : ℕ) ^ k * J n := by
  refine (summable_eulerShellMoment m k hσ).of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    abs_of_nonneg (pow_nonneg (log_eulerShell_nonneg n) _)]
  calc ((n : ℕ) : ℝ) ^ (-σ) * Real.log (n : ℕ) ^ k * |J n| ≤ ((n : ℕ) : ℝ) ^ (-σ) * Real.log (n : ℕ) ^ k * 1 :=
        mul_le_mul_of_nonneg_left (hJ n) (by have := log_eulerShell_nonneg n; positivity)
    _ = Real.log (n : ℕ) ^ k * ((n : ℕ) : ℝ) ^ (-σ) := by ring

/-- The Hankel quadratic form is the source integral of `J p_v²`. -/
theorem quadForm_eulerShellScalarHankel (hσ : 1 < σ) {J : EulerShell m → ℝ} (hJ : ∀ n, |J n| ≤ 1) {N : ℕ}
    (v : Fin N → ℝ) :
    v ⬝ᵥ (eulerShellScalarHankel m σ J N *ᵥ v) =
      ∑' n : EulerShell m, ((n : ℕ) : ℝ) ^ (-σ) * J n * hankelCoeffPoly v (Real.log (n : ℕ)) ^ 2 := by
  have hsum : ∀ i j : Fin N, Summable fun n : EulerShell m =>
      v i * (((n : ℕ) : ℝ) ^ (-σ) * Real.log (n : ℕ) ^ ((i : ℕ) + (j : ℕ)) * J n) * v j := fun i j =>
    ((summable_hankel_term hσ hJ _).mul_left (v i)).mul_right (v j)
  simp only [dotProduct, Matrix.mulVec, eulerShellScalarHankel, Matrix.of_apply, Finset.mul_sum]
  have h1 : ∀ i : Fin N, ∑ j : Fin N, v i * ((∑' n : EulerShell m, ((n : ℕ) : ℝ) ^ (-σ) *
      Real.log (n : ℕ) ^ ((i : ℕ) + (j : ℕ)) * J n) * v j) =
      ∑' n : EulerShell m, ∑ j : Fin N, v i * (((n : ℕ) : ℝ) ^ (-σ) * Real.log (n : ℕ) ^ ((i : ℕ) + (j : ℕ)) * J n) * v j :=
    fun i => by
      rw [Summable.tsum_finsetSum fun j _ => hsum i j]
      exact Finset.sum_congr rfl fun j _ => by rw [tsum_mul_right, tsum_mul_left]; ring
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsum i j]
  refine tsum_congr fun n => ?_
  simp only [hankelCoeffPoly, sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

theorem hankelCoeffPoly_eq_eval {N : ℕ} (v : Fin N → ℝ) (x : ℝ) :
    hankelCoeffPoly v x = Polynomial.eval x (∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)) := by
  simp [hankelCoeffPoly, Polynomial.eval_finsetSum]

theorem hankelCoeffPolynomial_ne_zero {N : ℕ} {v : Fin N → ℝ} (hv : v ≠ 0) :
    (∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)) ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hv
  intro h
  have := congrArg (fun P : Polynomial ℝ => P.coeff (i₀ : ℕ)) h
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i₀ (fun j _ hj => if_neg fun h => hj (Fin.ext h.symm)) (by simp)] at this
  exact hi₀ (by simpa using this)

/-- The positive source detects every nonzero coefficient vector: the shell has infinitely many
distinct clock values, so a nonzero polynomial does not vanish on all of them. -/
theorem exists_hankelCoeffPoly_ne_zero (hm : 1 ≤ m) {N : ℕ} {v : Fin N → ℝ} (hv : v ≠ 0) :
    ∃ n : EulerShell m, hankelCoeffPoly v (Real.log (n : ℕ)) ≠ 0 := by
  haveI := infinite_eulerShell hm
  by_contra hall
  push Not at hall
  have hfin := Polynomial.finite_setOf_isRoot (hankelCoeffPolynomial_ne_zero hv)
  have hsub : Set.range (fun n : EulerShell m => Real.log (n : ℕ)) ⊆
      {x | (∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)).IsRoot x} := by
    rintro _ ⟨n, rfl⟩
    show Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot.def, ← hankelCoeffPoly_eq_eval]
    exact hall n
  exact Set.infinite_range_of_injective log_eulerShell_injective (hfin.subset hsub)

theorem sum_sq_padded {N k : ℕ} (v : Fin N → ℝ) :
    (∑ i, (Fin.append v (0 : Fin k → ℝ) i) ^ 2) = ∑ i, v i ^ 2 := by
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem hankelCoeffPoly_padded {N k : ℕ} (v : Fin N → ℝ) (x : ℝ) :
    hankelCoeffPoly (Fin.append v (0 : Fin k → ℝ)) x = hankelCoeffPoly v x := by
  rw [hankelCoeffPoly, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, hankelCoeffPoly]

theorem quadTerm_eq {N : ℕ} (v : Fin N → ℝ) (w x Jn : ℝ) :
    w * Jn * hankelCoeffPoly v x ^ 2 = ∑ i : Fin N, ∑ j : Fin N, v i * (w * x ^ ((i : ℕ) + (j : ℕ)) * Jn) * v j := by
  simp only [hankelCoeffPoly, sq, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

theorem summable_quadTerm (hσ : 1 < σ) {J : EulerShell m → ℝ} (hJ : ∀ n, |J n| ≤ 1) {N : ℕ} (v : Fin N → ℝ) :
    Summable fun n : EulerShell m => ((n : ℕ) : ℝ) ^ (-σ) * J n * hankelCoeffPoly v (Real.log (n : ℕ)) ^ 2 := by
  simp_rw [quadTerm_eq]
  exact summable_sum fun i _ => summable_sum fun j _ =>
    ((summable_hankel_term hσ hJ _).mul_left (v i)).mul_right (v j)

theorem isHermitian_eulerShellScalarHankel (J : EulerShell m → ℝ) (N : ℕ) :
    (eulerShellScalarHankel m σ J N).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, eulerShellScalarHankel, add_comm]

theorem scalarHankel_quadForm_smul {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) (v : Fin N → ℝ) :
    (c • v) ⬝ᵥ (M *ᵥ (c • v)) = c ^ 2 * (v ⬝ᵥ (M *ᵥ v)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- **Theorem 7.1 (LEF.23)–(LEF.25) No uniform finite depth.**  For every depth `N` there is a scalar
packet with values `±1`, negative at one active atom, whose unnormalized Hankel sections of every
order at most `N` are positive definite. -/
theorem no_uniform_finite_depth (hm : 1 ≤ m) (hσ : 1 < σ) (N : ℕ) :
    ∃ J : EulerShell m → ℝ, (∀ n, |J n| ≤ 1) ∧ (∃ n₀, J n₀ < 0) ∧
      ∀ N' ≤ N, (eulerShellScalarHankel m σ J N').PosDef := by
  classical
  haveI := infinite_eulerShell hm
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨fun _ => -1, fun _ => by simp, ⟨⟨2 ^ m * 3, two_pow_mul_prime_mem hm Nat.prime_three (by norm_num)⟩,
      by norm_num⟩, fun N' hN' => ?_⟩
    have : N' = 0 := by omega
    subst this
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    exact ⟨isHermitian_eulerShellScalarHankel _ 0, fun x hx => absurd (funext fun i => i.elim0) hx⟩
  set H1 := eulerShellScalarHankel m σ (fun _ => (1 : ℝ)) N with hH1
  set Q : (Fin N → ℝ) → ℝ := fun v => v ⬝ᵥ (H1 *ᵥ v) with hQdef
  have hone : ∀ n : EulerShell m, |(fun _ : EulerShell m => (1 : ℝ)) n| ≤ 1 := fun _ => by simp
  have hQform : ∀ v, Q v = ∑' n : EulerShell m, ((n : ℕ) : ℝ) ^ (-σ) * 1 * hankelCoeffPoly v (Real.log (n : ℕ)) ^ 2 :=
    fun v => quadForm_eulerShellScalarHankel hσ hone v
  have hQpos : ∀ v : Fin N → ℝ, v ≠ 0 → 0 < Q v := fun v hv => by
    rw [hQform]
    obtain ⟨n, hn⟩ := exists_hankelCoeffPoly_ne_zero hm hv
    refine (summable_quadTerm hσ hone v).tsum_pos (fun n => ?_) n ?_
    · have := Real.rpow_pos_of_pos (eulerShell_cast_pos n) (-σ)
      positivity
    · have := Real.rpow_pos_of_pos (eulerShell_cast_pos n) (-σ)
      have h2 : 0 < hankelCoeffPoly v (Real.log (n : ℕ)) ^ 2 := by positivity
      positivity
  -- coercivity on the unit sphere of the `ℓ²` coefficient norm
  set K : Set (Fin N → ℝ) := {v | ∑ i, v i ^ 2 = 1} with hKdef
  have hKcpt : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq (by fun_prop) continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : Fin N → ℝ)) (r := 1)).subset fun v hv => ?_)
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : v i ^ 2 ≤ 1 := by
      rw [← hv]
      exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (v i), sq_abs (v i)]
  have hKne : K.Nonempty := by
    set e₀ : Fin N → ℝ := fun i => if i = ⟨0, hN⟩ then 1 else 0 with he₀
    refine ⟨e₀, ?_⟩
    show ∑ i, e₀ i ^ 2 = 1
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N) (fun j _ hj => by simp [he₀, hj]) (by simp)]
    simp [he₀]
  have hQcont : Continuous Q := by
    simp only [hQdef, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨v₀, hv₀K, hmin⟩ := hKcpt.exists_isMinOn hKne hQcont.continuousOn
  set lam := Q v₀ with hlam
  have hv₀ne : v₀ ≠ 0 := fun h => by
    have : ∑ i, v₀ i ^ 2 = 1 := hv₀K
    simp [h] at this
  have hlampos : 0 < lam := hQpos v₀ hv₀ne
  have hcoer : ∀ v : Fin N → ℝ, lam * ∑ i, v i ^ 2 ≤ Q v := fun v => by
    by_cases hv : v = 0
    · simp [hv, hQdef]
    set t := Real.sqrt (∑ i, v i ^ 2) with ht
    have hS : 0 < ∑ i, v i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
      exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
        (Finset.single_le_sum (f := fun i => v i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    have htpos : 0 < t := Real.sqrt_pos.2 hS
    have huK : t⁻¹ • v ∈ K := by
      show ∑ i, (t⁻¹ • v) i ^ 2 = 1
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow, ht,
        Real.sq_sqrt hS.le]
      exact inv_mul_cancel₀ hS.ne'
    have h1 : lam ≤ Q (t⁻¹ • v) := hmin huK
    have h2 : Q (t⁻¹ • v) = t⁻¹ ^ 2 * Q v := scalarHankel_quadForm_smul H1 t⁻¹ v
    have h3 : t ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hS.le
    have h4 : lam ≤ t⁻¹ ^ 2 * Q v := h1.trans_eq h2
    rw [← h3]
    calc lam * t ^ 2 ≤ t⁻¹ ^ 2 * Q v * t ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg t)
      _ = Q v := by field_simp
  -- choose the far atom
  set f : EulerShell m → ℝ := fun n => ((n : ℕ) : ℝ) ^ (-σ) * ∑ i : Fin N, Real.log (n : ℕ) ^ (2 * (i : ℕ)) with hfdef
  have hfsum : Summable f := by
    simp only [hfdef, Finset.mul_sum]
    exact summable_sum fun i _ => (summable_eulerShellMoment m (2 * (i : ℕ)) hσ).congr fun n => by ring
  obtain ⟨n₀, hn₀⟩ := ((hfsum.tendsto_cofinite_zero).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < lam / 2))).exists
  refine ⟨fun n => if n = n₀ then -1 else 1, fun n => by dsimp only; split_ifs <;> simp, ⟨n₀, by simp⟩, fun N' hN' => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN'
  have hJb : ∀ n : EulerShell m, |(fun n => if n = n₀ then (-1 : ℝ) else 1) n| ≤ 1 := fun n => by
    dsimp only
    split_ifs <;> simp
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_eulerShellScalarHankel _ _, fun v' hv' => ?_⟩
  set v : Fin (N' + k) → ℝ := Fin.append v' 0 with hvdef
  have hvne : v ≠ 0 := fun h => hv' (funext fun i => by
    have := congrFun h (Fin.castAdd k i)
    simpa [hvdef, Fin.append_left] using this)
  have hS : 0 < ∑ i, v' i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv'
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
      (Finset.single_le_sum (f := fun i => v' i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  have hpoly : ∀ x, hankelCoeffPoly v' x = hankelCoeffPoly v x := fun x => (hankelCoeffPoly_padded v' x).symm
  have hsq : ∑ i, v i ^ 2 = ∑ i, v' i ^ 2 := sum_sq_padded v'
  -- the quadratic form of the perturbed packet
  have hform : star v' ⬝ᵥ (eulerShellScalarHankel m σ (fun n => if n = n₀ then -1 else 1) N' *ᵥ v') =
      Q v - 2 * (((n₀ : ℕ) : ℝ) ^ (-σ) * hankelCoeffPoly v (Real.log (n₀ : ℕ)) ^ 2) := by
    rw [show star v' = v' from funext fun i => by simp, quadForm_eulerShellScalarHankel hσ hJb, hQform]
    simp_rw [hpoly]
    have hB : ∑' n : EulerShell m, (if n = n₀ then 2 * (((n : ℕ) : ℝ) ^ (-σ) *
        hankelCoeffPoly v (Real.log (n : ℕ)) ^ 2) else 0) =
        2 * (((n₀ : ℕ) : ℝ) ^ (-σ) * hankelCoeffPoly v (Real.log (n₀ : ℕ)) ^ 2) := by
      rw [tsum_eq_single n₀ (fun n hn => if_neg hn), if_pos rfl]
    rw [← hB, ← Summable.tsum_sub (summable_quadTerm hσ hone v) (summable_of_ne_finset_zero (s := {n₀})
        fun n hn => by rw [Finset.mem_singleton] at hn; exact if_neg hn)]
    refine tsum_congr fun n => ?_
    by_cases hn : n = n₀
    · subst hn
      simp only [if_true]
      ring
    · simp only [hn, if_false]
      ring
  have hcs : hankelCoeffPoly v (Real.log (n₀ : ℕ)) ^ 2 ≤
      (∑ i, v i ^ 2) * ∑ i : Fin (N' + k), Real.log (n₀ : ℕ) ^ (2 * (i : ℕ)) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v fun i => Real.log (n₀ : ℕ) ^ (i : ℕ)
    simp only [hankelCoeffPoly]
    refine this.trans_eq ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
  have hfn₀ : f n₀ < lam / 2 := hn₀
  have hw : 0 < ((n₀ : ℕ) : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (eulerShell_cast_pos n₀) _
  rw [hform]
  have hc := hcoer v
  rw [hsq] at hc hcs
  have hfv : ((n₀ : ℕ) : ℝ) ^ (-σ) * hankelCoeffPoly v (Real.log (n₀ : ℕ)) ^ 2 ≤ f n₀ * ∑ i, v' i ^ 2 := by
    calc ((n₀ : ℕ) : ℝ) ^ (-σ) * hankelCoeffPoly v (Real.log (n₀ : ℕ)) ^ 2
        ≤ ((n₀ : ℕ) : ℝ) ^ (-σ) * ((∑ i, v' i ^ 2) * ∑ i : Fin (N' + k), Real.log (n₀ : ℕ) ^ (2 * (i : ℕ))) :=
          mul_le_mul_of_nonneg_left hcs hw.le
      _ = f n₀ * ∑ i, v' i ^ 2 := by rw [hfdef]; ring
  nlinarith

/-- **Consequence of Theorem 7.1.**  For the packet of depth `N`, every negative Hankel witness has
order larger than `N`. -/
theorem witness_order_gt (hm : 1 ≤ m) (hσ : 1 < σ) (N : ℕ) :
    ∃ J : EulerShell m → ℝ, (∀ n, |J n| ≤ 1) ∧ (∃ n₀, J n₀ < 0) ∧
      ∀ (N' : ℕ) (v : Fin N' → ℝ), v ⬝ᵥ (eulerShellScalarHankel m σ J N' *ᵥ v) < 0 → N < N' := by
  obtain ⟨J, hJ, hneg, hpd⟩ := no_uniform_finite_depth hm hσ N
  refine ⟨J, hJ, hneg, fun N' v hv => ?_⟩
  by_contra hle
  push Not at hle
  have h := (Matrix.posDef_iff_dotProduct_mulVec.1 (hpd N' hle)).2
  by_cases hv0 : v = 0
  · simp [hv0] at hv
  · have := h hv0
    rw [show star v = v from funext fun i => by simp] at this
    linarith

end NoUniformDepth

/-! ## §8 The normalization wall -/

section NormalizationWall

/-- The shell sum diverges at every exponent `s ≤ 1`: it contains `Σ_{p odd} (2^m p)^{-s}`, which
dominates `2^{-m} Σ_p 1/p`. -/
theorem not_summable_eulerShell_of_le_one (hm : 1 ≤ m) {s : ℝ} (hs : s ≤ 1) :
    ¬ Summable fun n : EulerShell m => ((n : ℕ) : ℝ) ^ (-s) := by
  intro hsum
  set ψ : {p : Nat.Primes | (p : ℕ) ≠ 2} → EulerShell m :=
    fun p => ⟨2 ^ m * (p.1 : ℕ), two_pow_mul_prime_mem hm p.1.2 p.2⟩ with hψdef
  have hψ : Function.Injective ψ := fun p q h => by
    have h1 : 2 ^ m * (p.1 : ℕ) = 2 ^ m * (q.1 : ℕ) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Nat.eq_of_mul_eq_mul_left (by positivity) h1))
  have hcomp := (hsum.comp_injective hψ).mul_left ((2 : ℝ) ^ m)
  have hodd : Summable fun p : {p : Nat.Primes | (p : ℕ) ≠ 2} => (1 / ((p.1 : ℕ) : ℝ) : ℝ) := by
    refine hcomp.of_nonneg_of_le (fun p => by positivity) fun p => ?_
    have hp : (1 : ℝ) ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast p.1.2.one_lt.le
    have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ m * ((p.1 : ℕ) : ℝ) := by nlinarith
    simp only [Function.comp_apply, hψdef]
    push_cast
    have hle : ((2 : ℝ) ^ m * ((p.1 : ℕ) : ℝ)) ^ (-(1 : ℝ)) ≤ ((2 : ℝ) ^ m * ((p.1 : ℕ) : ℝ)) ^ (-s) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    rw [Real.rpow_neg_one] at hle
    have hpos : (0 : ℝ) < (2 : ℝ) ^ m * ((p.1 : ℕ) : ℝ) := by positivity
    calc 1 / ((p.1 : ℕ) : ℝ) = (2 : ℝ) ^ m * ((2 : ℝ) ^ m * ((p.1 : ℕ) : ℝ))⁻¹ := by
          field_simp
      _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * ((p.1 : ℕ) : ℝ)) ^ (-s) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
  apply Nat.Primes.not_summable_one_div
  rw [← summable_subtype_and_compl (s := {p : Nat.Primes | (p : ℕ) ≠ 2})]
  refine ⟨hodd, ?_⟩
  have hfin : ({p : Nat.Primes | (p : ℕ) ≠ 2}ᶜ).Finite :=
    (Set.finite_singleton (⟨2, Nat.prime_two⟩ : Nat.Primes)).subset fun p hp => by
      have hp' : (p : ℕ) = 2 := by
        by_contra hne
        exact hp hne
      exact Set.mem_singleton_iff.2 (Subtype.ext hp')
  haveI := hfin.to_subtype
  exact Summable.of_finite

/-- **§8 Exact lifetime.**  The exponential chart of the Euler-shell source is exactly
`{t : t < σ - 1}`. -/
theorem integrable_exp_eulerShellMeasure_iff (hm : 1 ≤ m) (hσ : 1 < σ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * x)) (eulerShellMeasure m σ) ↔ t < σ - 1 := by
  refine ⟨fun hint => ?_, fun ht => (integral_exp_eulerShellMeasure hm hσ (by linarith)).1⟩
  by_contra hge
  push Not at hge
  have hfin := hint.2
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le),
    lintegral_eulerShellMeasure] at hfin
  have hterm : ∀ n : EulerShell m, ENNReal.ofReal (eulerShellAtomWeight m σ n) * ENNReal.ofReal (Real.exp (t * Real.log (n : ℕ))) =
      ENNReal.ofReal (((n : ℕ) : ℝ) ^ (-(σ - t)) / eulerShellSum m σ) := fun n => by
    rw [← ENNReal.ofReal_mul (eulerShellAtomWeight_pos hm hσ n).le, eulerShellAtomWeight_mul_exp]
  simp_rw [hterm] at hfin
  have hs := ENNReal.summable_toReal hfin.ne
  have hs' : Summable fun n : EulerShell m => ((n : ℕ) : ℝ) ^ (-(σ - t)) := by
    have h2 := hs.mul_left (eulerShellSum m σ)
    refine h2.congr fun n => ?_
    rw [ENNReal.toReal_ofReal (by have := eulerShellSum_pos hm hσ; positivity)]
    field_simp [(eulerShellSum_pos hm hσ).ne']
  exact not_summable_eulerShell_of_le_one hm (by linarith) hs'

/-- **§8 (LEF.26) The normalization wall.**  The complete phase/Hankel order holds on every normalized
fibre `σ > 1` (Theorem 6.1), whose exponential chart is exactly `t < σ - 1`; at the half-density value
`σ = 1/m ≤ 1` the shell sum diverges, so that fibre lies outside the normalized positive chart. -/
theorem eulerShell_normalization_wall (hm : 1 ≤ m) :
    (∀ σ : ℝ, 1 < σ → ∀ t : ℝ,
      Integrable (fun x => Real.exp (t * x)) (eulerShellMeasure m σ) ↔ t < σ - 1) ∧
    ¬ Summable fun n : EulerShell m => ((n : ℕ) : ℝ) ^ (-(1 / (m : ℝ))) := by
  refine ⟨fun σ hσ t => integrable_exp_eulerShellMeasure_iff hm hσ t, not_summable_eulerShell_of_le_one hm ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [div_le_one (by linarith)]
  exact hm'

end NormalizationWall

end HTGeometry
