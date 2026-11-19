import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.LogCellPositionGaussianKL
import GaloisForLFunctions.HTGeometry.UnitIntervalRiemannLimit
import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Gaussian projections on a uniformly refined position cell

Subdivide a unit position interval into N equal pieces and give each piece
its unique moment-matched Gaussian. Their equal mixture converges weakly to
the original position law. At the reciprocal mesh frequency its characteristic
function is always −exp(−π²/6), whereas the uniform characteristic function
vanishes.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.GaussianGrid
open MeasureTheory ProbabilityTheory InformationTheory Filter Set HTGeometry
open scoped ENNReal Topology NNReal

def width (n : ℕ) : ℝ := 1/((n:ℝ)+1)
private theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

def center (n i : ℕ) : ℝ := ((i:ℝ)+1/2)*width n

def component (n i : ℕ) := gaussianReal (center n i) (Real.toNNReal ((width n)^2/12))

instance (n i : ℕ) : IsProbabilityMeasure (component n i) := inferInstanceAs
  (IsProbabilityMeasure (gaussianReal _ _))

/-- The component assigned to each true subcell attains its Gaussian KL minimum. -/
theorem cell_projection (n i : ℕ) :
    let t := (i:ℝ)*width n
    2*(klDiv (positionLaw t (Real.log (width n))) (component n i)).toReal =
      Real.log (2*Real.pi)-Real.log 12+1 := by
  intro t
  have hw := width_pos n
  have hv : 0 < width n^2/12 := by positivity
  have h := (position_projection_exact t (Real.log (width n)) (center n i)
    (Real.log (width n^2/12))).2
  rw [Real.exp_log hw] at h
  have he := h.mpr ⟨by unfold center; dsimp [t]; ring,rfl⟩
  simpa only [positionGaussian,Real.exp_log hv,component] using he

/-- Equal mixture of the N = n+1 Gaussian projections. -/
def mixture (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (width n) • ∑ i ∈ Finset.range (n+1), component n i

instance (n : ℕ) : IsProbabilityMeasure (mixture n) where
  measure_univ := by
    rw [mixture,Measure.smul_apply,Measure.finsetSum_apply _ _ MeasurableSet.univ]
    simp only [measure_univ,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,
      smul_eq_mul]
    have h : 0 < (n:ℝ)+1 := by positivity
    rw [show ((n+1:ℕ):ℝ≥0∞) = ENNReal.ofReal ((n:ℝ)+1) by norm_cast; simp,
      ← ENNReal.ofReal_mul (width_pos n).le]
    simp [width,h.ne']

def probability (n : ℕ) : ProbabilityMeasure ℝ := ⟨mixture n,inferInstance⟩

private def phase (t x : ℝ) := Complex.exp ((t:ℂ)*x*Complex.I)

private theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by
  rw [phase,Complex.norm_exp]
  simp

private theorem phase_int (t : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (phase t) μ := by
  refine (integrable_const (1:ℝ)).mono' (by unfold phase; fun_prop) ?_
  exact Eventually.of_forall fun x => (phase_norm t x).le

private theorem phase_lipschitz (t : ℝ) : LipschitzWith (Real.toNNReal |t|) (phase t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : phase t x - phase t y = phase t y *
      (Complex.exp (Complex.I * ((t*(x-y):ℝ):ℂ))-1) := by
    unfold phase
    rw [mul_sub,← Complex.exp_add,mul_one]
    push_cast
    congr 2
    ring
  rw [dist_eq_norm,he,norm_mul,phase_norm,one_mul,Real.dist_eq,Real.coe_toNNReal _ (abs_nonneg _)]
  simpa only [Real.norm_eq_abs,abs_mul] using
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*(x-y))

/-- The grid characteristic function is the left Riemann sum times an exact
midpoint translation and Gaussian attenuation. -/
theorem mixture_characteristic (n : ℕ) (t : ℝ) :
    charFun (mixture n) t = Complex.exp ((t:ℂ)*width n/2*Complex.I-
      (width n:ℂ)^2*t^2/24)*unitRiemannSum (phase t) n := by
  have hcast : ((Real.toNNReal ((width n)^2/12):ℝ≥0):ℝ) = (width n)^2/12 :=
    Real.coe_toNNReal _ (by positivity)
  let E := Complex.exp ((t:ℂ)*width n/2*Complex.I-(width n:ℂ)^2*t^2/24)
  have hc (i : ℕ) : charFun (component n i) t = E * phase t ((i:ℝ)/((n:ℝ)+1)) := by
    rw [component,charFun_gaussianReal]
    dsimp only [E,phase]
    rw [← Complex.exp_add]
    congr 1
    change _ - (((Real.toNNReal _ : ℝ≥0):ℝ):ℂ)*_/2 = _
    rw [hcast]
    unfold center width
    push_cast
    ring
  rw [charFun_apply_real]
  change (∫ x, phase t x ∂mixture n) = _
  rw [mixture,integral_smul_measure,ENNReal.toReal_ofReal (width_pos _).le,
    integral_finsetSum_measure (fun i _ => phase_int t (component n i))]
  have hci (i : ℕ) : (∫ x, phase t x ∂component n i) = E*phase t ((i:ℝ)/((n:ℝ)+1)) := by
    simpa only [charFun_apply_real,phase] using hc i
  simp_rw [hci]
  rw [← Finset.mul_sum]
  change width n • (E*_) = E*(width n • _)
  exact (mul_smul_comm _ _ _).symm

/-- Weak convergence of the actual probability measures. -/
theorem weak_convergence : Tendsto probability atTop (𝓝 unitIntervalProbabilityMeasure) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  have hw : Tendsto width atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    simpa only [Nat.cast_add,Nat.cast_one,Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hwc := (Complex.continuous_ofReal.tendsto 0).comp hw
  have hE : Tendsto (fun n => Complex.exp ((t:ℂ)*width n/2*Complex.I-
      (width n:ℂ)^2*t^2/24)) atTop (𝓝 1) := by
    convert Complex.continuous_exp.continuousAt.tendsto.comp
      ((((tendsto_const_nhds.mul hwc).div_const 2).mul_const Complex.I).sub
        (((hwc.pow 2).mul_const ((t:ℂ)^2)).div_const 24)) using 1 <;> simp
  have hP : charFun (unitIntervalProbabilityMeasure : Measure ℝ) t = ∫ x in (0:ℝ)..1, phase t x := by
    rw [charFun_apply_real,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rfl
  change Tendsto (fun n => charFun (mixture n) t) _ _
  simp_rw [mixture_characteristic]
  rw [hP]
  simpa only [one_mul] using hE.mul (tendsto_unitRiemannSum (phase_lipschitz t))

/-- The first reciprocal mesh frequency. -/
def reciprocal (n : ℕ) : ℝ := 2*Real.pi*((n:ℝ)+1)

/-- A single mesh-scale test separates the mixture and the source by the
same nonzero amount at every subdivision depth. -/
theorem mesh_characteristic (n : ℕ) :
    charFun (unitIntervalProbabilityMeasure : Measure ℝ) (reciprocal n) = 0 ∧
    charFun (mixture n) (reciprocal n) = -(Real.exp (-Real.pi^2/6):ℂ) := by
  have hn : ((n:ℝ)+1) ≠ 0 := by positivity
  have hnc : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast hn
  have hs : Real.sinc ((1/2)*(reciprocal n)) = 0 := by
    rw [show 1/2*reciprocal n = ((n+1:ℕ):ℝ)*Real.pi by simp [reciprocal]; ring,
      Real.sinc_of_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) Real.pi_ne_zero),
      Real.sin_nat_mul_pi,zero_div]
  have hcenter : (centeredUniformClockProbabilityMeasure (1/2) : Measure ℝ) =
      (unitIntervalProbabilityMeasure : Measure ℝ).map (· + (-(1/2):ℝ)) := by
    rw [centeredUniformClockProbabilityMeasure,ProbabilityMeasure.toMeasure_map]
    congr 1
    funext x
    ring
  have hU := charFun_centeredUniformClockProbabilityMeasure (1/2) (reciprocal n)
  rw [hs,hcenter,charFun_map_add_const] at hU
  refine ⟨(mul_eq_zero.mp (by simpa using hU)).resolve_right (Complex.exp_ne_zero _),?_⟩
  have hphase (j : ℕ) : phase (reciprocal n) ((j:ℝ)/((n:ℝ)+1)) = 1 := by
    unfold phase reciprocal
    convert Complex.exp_nat_mul_two_pi_mul_I j using 1
    push_cast
    field_simp
    ring
  have hsum : unitRiemannSum (phase (reciprocal n)) n = 1 := by
    simp only [unitRiemannSum,hphase,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,
      Complex.real_smul]
    push_cast
    field_simp
  rw [mixture_characteristic,hsum,mul_one]
  have he : ((reciprocal n:ℝ):ℂ)*width n/2*Complex.I-(width n:ℂ)^2*(reciprocal n:ℝ)^2/24 =
      (Real.pi:ℂ)*Complex.I+((-Real.pi^2/6:ℝ):ℂ) := by
    unfold reciprocal width
    push_cast
    field_simp
    ring
  rw [he,Complex.exp_add,Complex.exp_pi_mul_I,← Complex.ofReal_exp,neg_one_mul]

#print axioms cell_projection
#print axioms mixture_characteristic
#print axioms weak_convergence
#print axioms mesh_characteristic
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.GaussianGrid
