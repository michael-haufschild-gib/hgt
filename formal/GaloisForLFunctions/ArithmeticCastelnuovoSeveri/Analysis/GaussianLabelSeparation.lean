import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.NoisyHaarGaussianProjection
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianLimitOfProbeDephasing

/-!
# Gaussian overlap and loss of a logarithmic cell label

The overlap of two equal-variance Gaussian densities factors pointwise into
a midpoint Gaussian and the weak-probe coherence. This bounds the conditional
label entropy and identifies the constant term in the small-noise divergence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
open ExclusionOfTheCriticalState.ProbeWalk

def overlap (a b l : ℝ) := Real.exp (-gapCost a b/Real.exp l)

/-- Pointwise, the geometric mean of the two densities is a constant
multiple of the density centered at their midpoint. -/
theorem midpoint_density (a b l x : ℝ) :
    Real.sqrt (positionGaussianDensity (a,l) x*positionGaussianDensity (b,l) x) =
      overlap a b l*positionGaussianDensity ((a+b)/2,l) x := by
  let f := fun t : ℝ => positionGaussianDensity (t,l) x
  have hp (t : ℝ) : 0 < f t := positionGaussianDensity_pos _ _
  have ho : 0 < overlap a b l := Real.exp_pos _
  have hh : Real.log (f a*f b)=Real.log ((overlap a b l*f ((a+b)/2))^2) := by
    rw [Real.log_mul (hp _).ne' (hp _).ne',Real.log_pow,Real.log_mul ho.ne' (hp _).ne']
    simp only [f,positionGaussianDensity,gaussian_log_pdf,overlap,Real.log_exp,gapCost]
    field_simp [Real.exp_ne_zero]
    ring
  have he := congrArg Real.exp hh
  rw [Real.exp_log (mul_pos (hp _) (hp _)),Real.exp_log (sq_pos_of_pos (mul_pos ho (hp _)))] at he
  change Real.sqrt (f a*f b)=overlap a b l*f ((a+b)/2)
  rw [he,Real.sqrt_sq (mul_pos ho (hp _)).le]

/-- The posterior log loss of one component lies between zero and twice
the geometric mean of the two weighted densities. -/
theorem density_loss_bounds {A B : ℝ} (ha : 0<A) (hb : 0<B) :
    0 ≤ A*(Real.log (A+B)-Real.log A) ∧
      A*(Real.log (A+B)-Real.log A) ≤ 2*Real.sqrt (A*B) := by
  let r := Real.sqrt (A*B)/A
  have hr : 0≤r := div_nonneg (Real.sqrt_nonneg _) ha.le
  have hr2 : A*r^2=B := by
    dsimp only [r]
    rw [div_pow,Real.sq_sqrt (mul_pos ha hb).le]
    field_simp
  have hr1 : A*r=Real.sqrt (A*B) := mul_div_cancel₀ _ ha.ne'
  have hprod : A+B ≤ A*(1+r)^2 := by
    rw [← hr2]
    nlinarith only [mul_nonneg ha.le hr]
  have hlog := Real.log_le_log (add_pos ha hb) hprod
  have hor : 0 < 1+r := by linarith only [hr]
  rw [Real.log_mul ha.ne' (sq_pos_of_pos hor).ne',Real.log_pow] at hlog
  have hscalar : Real.log (A+B)-Real.log A ≤ 2*r := by
    norm_num at hlog
    have hl : Real.log (1+r) ≤ r := (Real.log_le_sub_one_of_pos hor).trans_eq (by ring)
    linarith only [hlog,mul_le_mul_of_nonneg_left hl (show (0:ℝ) ≤ 2 by norm_num)]
  refine ⟨mul_nonneg ha.le (sub_nonneg.mpr (Real.log_le_log ha (le_add_of_nonneg_right hb.le))),?_⟩
  calc
    _ ≤ A*(2*r) := mul_le_mul_of_nonneg_left hscalar ha.le
    _ = 2*Real.sqrt (A*B) := by rw [← hr1]; ring

/-- The entropy still missing from a noisy binary label decays at least
as fast as the Gaussian probe coherence at inverse variance. -/
theorem missing_label_bound (u v a b l : ℝ) :
    let p := lengthRatio u v
    let q := lengthRatio v u
    0 ≤ labelEntropy u v-labelInformation u v a b l ∧
      labelEntropy u v-labelInformation u v a b l ≤ 4*Real.sqrt (p*q)*overlap a b l := by
  intro p q
  have hp : 0<p := lengthRatio_pos _ _
  have hq : 0<q := lengthRatio_pos _ _
  let A := fun x => p*positionGaussianDensity (a,l) x
  let B := fun x => q*positionGaussianDensity (b,l) x
  let C := Real.sqrt (p*q)*overlap a b l
  let f := positionGaussianDensity ((a+b)/2,l)
  have hab (x) : Real.sqrt (A x*B x) = C*f x := by
    change Real.sqrt ((p*_)*(q*_)) = _
    rw [show (p*positionGaussianDensity (a,l) x)*(q*positionGaussianDensity (b,l) x) =
      (p*q)*(positionGaussianDensity (a,l) x*positionGaussianDensity (b,l) x) by ring,
      Real.sqrt_mul (mul_pos hp hq).le,midpoint_density]
    exact (mul_assoc _ _ _).symm
  have upper (U V : ℝ → ℝ) (hU : ∀ x, 0<U x) (hV : ∀ x, 0<V x)
      (hUV : ∀ x, Real.sqrt (U x*V x)=C*f x) :
      (∫ x, U x*(Real.log (U x+V x)-Real.log (U x))) ≤ 2*C := by
    have hu := integral_mono_of_nonneg (ae_of_all volume fun x => (density_loss_bounds (hU x) (hV x)).1)
      ((integrable_gaussianPDFReal ((a+b)/2) (Real.toNNReal (Real.exp l))).const_mul (2*C))
      (ae_of_all volume fun x => calc
        U x*(Real.log (U x+V x)-Real.log (U x)) ≤ 2*Real.sqrt (U x*V x) :=
          (density_loss_bounds (hU x) (hV x)).2
        _ = (2*C)*f x := by rw [hUV]; ring)
    rw [integral_const_mul,integral_gaussianPDFReal_eq_one _ (Real.toNNReal_pos.mpr (Real.exp_pos l)).ne',
      mul_one] at hu
    exact hu
  have pa (x) : 0<A x := mul_pos hp (positionGaussianDensity_pos _ _)
  have pb (x) : 0<B x := mul_pos hq (positionGaussianDensity_pos _ _)
  have ua := upper A B pa pb hab
  have ub := upper B A pb pa (fun x => (congrArg Real.sqrt (mul_comm _ _)).trans (hab x))
  simp_rw [add_comm (B _) (A _)] at ub
  have ga := component_label_loss u v a b l a (Real.log p)
  have gb := component_label_loss u v a b l b (Real.log q)
  dsimp only at ga gb
  rw [Real.exp_log hp] at ga
  rw [Real.exp_log hq] at gb
  change -p*Real.log p-p*_ = ∫ x, A x*(Real.log (A x+B x)-Real.log (A x)) at ga
  change -q*Real.log q-q*_ = ∫ x, B x*(Real.log (A x+B x)-Real.log (B x)) at gb
  refine ⟨sub_nonneg.mpr (label_bounds u v a b l).2,?_⟩
  change -(p*Real.log p)-q*Real.log q-(p*_+q*_) ≤ 4*Real.sqrt (p*q)*overlap a b l
  dsimp only [C] at ua ub
  linarith only [ga,gb,ua,ub]

private theorem overlap_vanishes {a b : ℝ} (h : a≠b) :
    Tendsto (overlap a b) atBot (𝓝 0) := by
  have hc : 0 < gapCost a b := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (by norm_num)
  have hlarge := (Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop).const_mul_atTop hc
  apply (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlarge).congr
  intro l
  simp only [Function.comp_apply,overlap,Real.exp_neg,div_eq_mul_inv,neg_mul]

/-- A nonconstant binary cell recovers its full discrete label entropy in
the zero-noise limit; the convergence has an explicit overlap bound. -/
theorem label_information_limit (u v a b : ℝ) :
    a=b ∨ Tendsto (labelInformation u v a b) atBot (𝓝 (labelEntropy u v)) := by
  by_cases h : a=b
  · exact Or.inl h
  right
  have hd : Tendsto (fun l => labelEntropy u v-labelInformation u v a b l) atBot (𝓝 0) := by
    apply squeeze_zero (fun l => (missing_label_bound u v a b l).1) (fun l => (missing_label_bound u v a b l).2)
    simpa only [mul_zero] using (overlap_vanishes h).const_mul
      (4*Real.sqrt (lengthRatio u v*lengthRatio v u))
  simpa only [sub_sub_cancel,sub_zero] using (tendsto_const_nhds (x:=labelEntropy u v)).sub hd

/-- Exact constant after subtracting the logarithmic small-noise divergence. -/
theorem small_noise_constant (u v a b : ℝ) :
    a=b ∨ Tendsto (fun l => (optimalLoss u v a b l).toReal+l/2) atBot
      (𝓝 (Real.log (signalVariance u v a b)/2-labelEntropy u v)) := by
  by_cases hab : a=b
  · exact Or.inl hab
  right
  have hv : 0<signalVariance u v a b := mul_pos (mul_pos (lengthRatio_pos _ _) (lengthRatio_pos _ _))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hab))
  have hs : Tendsto (fun l => Real.exp l+signalVariance u v a b) atBot (𝓝 (signalVariance u v a b)) := by
    simpa only [zero_add] using Real.tendsto_exp_atBot.add_const (signalVariance u v a b)
  apply (((hs.log hv.ne').div_const 2).sub ((label_information_limit _ _ _ _).resolve_left hab)).congr
  intro l
  linarith only [(optimum u v a b l).2]

#print axioms midpoint_density
#print axioms missing_label_bound
#print axioms label_information_limit
#print axioms small_noise_constant
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
