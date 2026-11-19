import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.LogCellPositionGaussianKL
import GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle

/-!
# Correlated Gaussian fits to independent logarithmic positions

A bivariate Gaussian is parametrized by its first marginal and the mean,
slope and residual variance of the second coordinate given the first.
For independent uniform positions on two intervals, an imposed slope adds
exactly slope² times the first variance to the optimal residual variance.
After refitting both marginals its KL price is half the logarithm of the
ratio between this inflated variance and the second interval's variance.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.Rectangle
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory

def mid (t w : ℝ) := t+Real.exp w/2
def variance (w : ℝ) := (Real.exp w)^2/12
def effectiveVariance (w v k : ℝ) := variance v+k^2*variance w

private theorem var_pos (w : ℝ) : 0 < variance w := by unfold variance; positivity
private theorem effective_pos (w v k : ℝ) : 0 < effectiveVariance w v k :=
  add_pos_of_pos_of_nonneg (var_pos v) (mul_nonneg (sq_nonneg _) (var_pos w).le)

/-- The second position conditioned on the first coordinate of the fitted Gaussian. -/
def regression (b m k l : ℝ) : Kernel ℝ ℝ where
  toFun x := positionGaussian (m+k*(x-b)) l
  measurable' := measurable_gaussianReal.comp (show Measurable (fun x : ℝ =>
    (m+k*(x-b),Real.toNNReal (Real.exp l))) by fun_prop)

instance (b m k l : ℝ) : IsMarkovKernel (regression b m k l) :=
  ⟨fun x => inferInstanceAs (IsProbabilityMeasure (positionGaussian _ _))⟩

def source (t w s v : ℝ) := (positionLaw t w).prod (positionLaw s v)

def target (b m l h k j : ℝ) := positionGaussian m l ⊗ₘ regression b h k j

private theorem continuous_int (t w : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (positionLaw t w) := by
  have he := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show t ≤ t+Real.exp w by linarith only [Real.exp_pos w])).mp
    (hf.intervalIntegrable (μ := volume) t (t+Real.exp w))
  apply he.smul_measure
  rw [Real.volume_Ioc,add_sub_cancel_left]
  exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- An affine residual has exactly its squared midpoint value plus its slope
squared times the cell variance. -/
theorem affine_square (t w β k : ℝ) :
    (∫ x, (β+k*(x-mid t w))^2 ∂positionLaw t w) = β^2+k^2*variance w := by
  by_cases hk : k=0
  · simp [hk]
  let m := mid t w-β/k
  have hsq (x : ℝ) : (β+k*(x-mid t w))^2=k^2*(x-m)^2 := by dsimp [m]; field_simp; ring
  simp_rw [hsq]
  rw [integral_const_mul,positionLaw,ProbabilityTheory.cond,integral_smul_measure,
    Real.volume_Ioc,add_sub_cancel_left,ENNReal.toReal_inv,ENNReal.toReal_ofReal (Real.exp_pos w).le,
    smul_eq_mul,← intervalIntegral.integral_of_le (show t ≤ t+Real.exp w by linarith only [Real.exp_pos w]),
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^2) m,integral_pow]
  dsimp only [m,mid,variance]
  push_cast
  field_simp [Real.exp_ne_zero w]
  ring

private def offset (s v h k b x : ℝ) := mid s v-h+(-k)*(x-b)
private def fibreScore (s v h k b j x : ℝ) :=
  (Real.log (2*Real.pi)+j-2*v+variance v/Real.exp j)/2 +
    (1/(2*Real.exp j))*(offset s v h k b x)^2

private theorem fibre (s v h k b j x : ℝ) :
    klDiv (positionLaw s v) (regression b h k j x) =
      ENNReal.ofReal (fibreScore s v h k b j x) := by
  have H := position_gaussian_kl s v (h+k*(x-b)) j
  rw [← ENNReal.ofReal_toReal H.1]
  apply congrArg ENNReal.ofReal
  unfold fibreScore offset mid variance
  linear_combination H.2/2

/-- Exact relative entropy against the full nonsingular regression family. -/
theorem joint_loss (t w s v m l h k j : ℝ) :
    let D := klDiv (source t w s v) (target (mid t w) m l h k j)
    D ≠ ⊤ ∧ 2*D.toReal = 2*(klDiv (positionLaw t w) (positionGaussian m l)).toReal +
      Real.log (2*Real.pi)+j-2*v+
      (effectiveVariance w v k+(mid s v-h)^2)/Real.exp j := by
  let μ := positionLaw t w
  let κ : Kernel ℝ ℝ := Kernel.const ℝ (positionLaw s v)
  let η := regression (mid t w) h k j
  let f := fibreScore s v h k (mid t w) j
  have hfin := (position_gaussian_kl t w m l).1
  have hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η := Measure.absolutelyContinuous_compProd_right_iff.mpr <|
    Filter.Eventually.of_forall fun x => (klDiv_ne_top_iff.mp
      (position_gaussian_kl s v (h+k*(x-mid t w)) j).1).1
  have hf : Integrable f μ := continuous_int t w (by dsimp [f,fibreScore,offset]; fun_prop)
  have hnon (x : ℝ) : 0 ≤ f x := by
    have H := (position_gaussian_kl s v (h+k*(x-mid t w)) j).2
    have hn := ENNReal.toReal_nonneg (a := klDiv (positionLaw s v)
      (positionGaussian (h+k*(x-mid t w)) j))
    have he : f x = (klDiv (positionLaw s v) (positionGaussian (h+k*(x-mid t w)) j)).toReal := by
      dsimp [f,fibreScore,offset,mid,variance]
      linear_combination -H/2
    rw [he]
    exact hn
  have he : klDiv (source t w s v) (target (mid t w) m l h k j) =
      klDiv μ (positionGaussian m l) + ENNReal.ofReal (∫ x, f x ∂μ) := by
    rw [source,← Measure.compProd_const,target,klDiv_compProd_eq_add,
      GaloisForLFunctions.HTGeometry.klDiv_compProd_right μ κ η hac]
    congr 1
    simp_rw [show ∀ x, klDiv (κ x) (η x) = ENNReal.ofReal (f x) from fibre s v h k (mid t w) j]
    exact (ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hnon)).symm
  dsimp only
  rw [he]
  refine ⟨ENNReal.add_ne_top.mpr ⟨hfin,ENNReal.ofReal_ne_top⟩,?_⟩
  have havg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hnon
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal havg]
  have hi := continuous_int t w (f := fun x => (offset s v h k (mid t w) x)^2)
    (by unfold offset; fun_prop)
  dsimp only [f,fibreScore]
  rw [integral_add (integrable_const _) (hi.const_mul _),integral_const,integral_const_mul]
  simp only [probReal_univ,one_smul,offset,affine_square,neg_sq]
  unfold effectiveVariance
  ring

/-- The effective variance is the unique conditional variance after the
regression slope has been fixed. The four remaining parameters have an
exact, nonnegative divergence gap. -/
theorem fixed_slope_projection (t w s v m l h k j : ℝ) :
    let V := effectiveVariance w v k
    let P := source t w s v
    let D := fun m l h j => 2*(klDiv P (target (mid t w) m l h k j)).toReal
    let opt := D (mid t w) (Real.log (variance w)) (mid s v) (Real.log V)
    opt ≤ D m l h j ∧ (D m l h j = opt ↔
      m=mid t w ∧ l=Real.log (variance w) ∧ h=mid s v ∧ j=Real.log V) ∧
      opt = 2*(Real.log (2*Real.pi)-Real.log 12+1)+Real.log (V/variance v) := by
  intro V P D opt
  have hV : 0 < V := effective_pos w v k
  let B := Real.log (2*Real.pi)-Real.log 12+1
  have h₁ := position_projection_exact t w m l
  have h₀ := (position_projection_exact t w (mid t w) (Real.log (variance w))).2.mpr ⟨rfl,rfl⟩
  have hfit : opt = B+Real.log (2*Real.pi)+Real.log V-2*v+1 := by
    have e := (joint_loss t w s v (mid t w) (Real.log (variance w)) (mid s v) k (Real.log V)).2
    change _ = _+_+_-_+(V+_)/_ at e
    simpa only [h₀,Real.exp_log hV,sub_self,zero_pow (by norm_num : 2≠0),add_zero,div_self hV.ne'] using e
  let z := Real.log V-j
  have hZ : Real.exp z=V/Real.exp j := by
    dsimp only [z]
    rw [Real.exp_sub,Real.exp_log hV]
  have hL : 0 ≤ Real.exp z-1-z := by linarith only [Real.add_one_le_exp z]
  have hX : 0 ≤ (mid s v-h)^2/Real.exp j := div_nonneg (sq_nonneg _) (Real.exp_pos _).le
  let L := 2*(klDiv (positionLaw t w) (positionGaussian m l)).toReal
  have gap : D m l h j-opt = (L-B)+(Real.exp z-1-z)+(mid s v-h)^2/Real.exp j := by
    rw [hfit,hZ]
    dsimp only [D,P,L,z]
    rw [(joint_loss t w s v m l h k j).2]
    unfold V
    ring
  have hLB : B ≤ L := h₁.1
  refine ⟨by linarith only [gap,hLB,hL,hX],⟨?_,?_⟩,?_⟩
  · intro e
    obtain ⟨em,el⟩ := h₁.2.mp (show L=B by linarith only [gap,e,hLB,hL,hX])
    have ez : z=0 := by
      by_contra hn
      linarith only [gap,e,hLB,hX,Real.add_one_lt_exp hn]
    have ex : mid s v=h := sub_eq_zero.mp (sq_eq_zero_iff.mp
      ((div_eq_zero_iff.mp (show (mid s v-h)^2/Real.exp j=0 by linarith only [gap,e,hLB,hL,hX])).resolve_right
        (Real.exp_ne_zero _)))
    exact ⟨em,el,ex.symm,(sub_eq_zero.mp ez).symm⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl
  · rw [hfit,Real.log_div hV.ne' (var_pos v).ne',variance,Real.log_div
      (pow_ne_zero _ (Real.exp_ne_zero v)) (by norm_num),Real.log_pow,Real.log_exp]
    unfold B
    ring

#print axioms affine_square
#print axioms joint_loss
#print axioms fixed_slope_projection
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.Rectangle
