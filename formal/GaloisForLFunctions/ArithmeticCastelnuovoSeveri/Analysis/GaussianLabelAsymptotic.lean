import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.GaussianLabelBoundaryLayer
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The exact leading loss of a binary Gaussian label

At common variance v and distinct locations a,b, the residual label
entropy is asymptotic to
2√(2πpqv) exp(−(a−b)²/(8v)) / |a−b|, with p,q the cell weights.
The change of variables to log posterior odds gives an identity at every
positive variance, including unequal prior weights.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair

private def weightedDensity (p a l x : ℝ) := p*positionGaussianDensity (a,l) x

private theorem sqrt_weighted {p q : ℝ} (hp : 0<p) (hq : 0<q) (a b l x : ℝ) :
    sqrt (weightedDensity p a l x*weightedDensity q b l x) =
      (sqrt (p*q)*overlap a b l)*positionGaussianDensity ((a+b)/2,l) x := by
  unfold weightedDensity
  rw [show (p*positionGaussianDensity (a,l) x)*(q*positionGaussianDensity (b,l) x) =
    (p*q)*(positionGaussianDensity (a,l) x*positionGaussianDensity (b,l) x) by ring,
    sqrt_mul (mul_pos hp hq).le,midpoint_density,mul_assoc]

private theorem odds_coordinate {p q : ℝ} (hp : 0<p) (hq : 0<q) (a b l x : ℝ) :
    log (weightedDensity q b l x)-log (weightedDensity p a l x) =
      log q-log p+(b-a)/exp l*(x-(a+b)/2) := by
  rw [weightedDensity,weightedDensity,log_mul hq.ne' (positionGaussianDensity_pos _ _).ne',
    log_mul hp.ne' (positionGaussianDensity_pos _ _).ne']
  simp only [positionGaussianDensity,gaussian_log_pdf]
  ring

private theorem density_loss_int {p q : ℝ} (hp : 0<p) (hq : 0<q) (a b l : ℝ) :
    let A := weightedDensity p a l
    let B := weightedDensity q b l
    Integrable (fun x => A x*(log (A x+B x)-log (A x))) := by
  intro A B
  have hA : Continuous A := continuous_const.mul (positionGaussianDensity_cont _)
  have hB : Continuous B := continuous_const.mul (positionGaussianDensity_cont _)
  have pa (x) : 0<A x := mul_pos hp (positionGaussianDensity_pos _ _)
  have pb (x) : 0<B x := mul_pos hq (positionGaussianDensity_pos _ _)
  have hc := hA.mul (((hA.add hB).log (fun x => (add_pos (pa x) (pb x)).ne')).sub
    (hA.log fun x => (pa x).ne'))
  apply ((integrable_gaussianPDFReal ((a+b)/2) (Real.toNNReal (exp l))).const_mul
    (2*(sqrt (p*q)*overlap a b l))).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro x
  obtain ⟨hn,he⟩ := density_loss_bounds (pa x) (pb x)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  calc
    _ ≤ 2*sqrt (A x*B x) := he
    _ = _ := by rw [sqrt_weighted hp hq]; ring

private theorem loss_as_midpoint_expectation (u v a b l : ℝ) :
    let p := lengthRatio u v
    let q := lengthRatio v u
    labelEntropy u v-labelInformation u v a b l =
      (sqrt (p*q)*overlap a b l)*∫ x, positionGaussianDensity ((a+b)/2,l) x*
        oddsKernel (log q-log p+(b-a)/exp l*(x-(a+b)/2)) := by
  intro p q
  have hp : 0<p := lengthRatio_pos _ _
  have hq : 0<q := lengthRatio_pos _ _
  let A := weightedDensity p a l
  let B := weightedDensity q b l
  let L (U V : ℝ → ℝ) (x : ℝ) := U x*(log (U x+V x)-log (U x))
  have ga := component_label_loss u v a b l a (log p)
  have gb := component_label_loss u v a b l b (log q)
  dsimp only at ga gb
  rw [exp_log hp] at ga
  rw [exp_log hq] at gb
  change -p*log p-p*_ = ∫ x, L A B x at ga
  change -q*log q-q*_ = ∫ x, B x*(log (A x+B x)-log (B x)) at gb
  simp_rw [add_comm (A _) (B _)] at gb
  change -q*log q-q*_ = ∫ x, L B A x at gb
  have hsum : labelEntropy u v-labelInformation u v a b l=(∫ x, L A B x)+(∫ x, L B A x) := by
    change -(p*log p)-q*log q-(p*_+q*_)=_
    linarith only [ga,gb]
  rw [hsum,← integral_add (density_loss_int hp hq a b l) (density_loss_int hq hp b a l),
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have h := log_odds_loss ⟨A x,mul_pos hp (positionGaussianDensity_pos _ _)⟩
    ⟨B x,mul_pos hq (positionGaussianDensity_pos _ _)⟩
  change A x*(log (A x+B x)-log (A x))+B x*(log (A x+B x)-log (B x)) =
    sqrt (A x*B x)*oddsKernel (log (B x)-log (A x)) at h
  change A x*(log (A x+B x)-log (A x))+B x*(log (B x+A x)-log (B x))=_
  rw [add_comm (B x) (A x),h,sqrt_weighted hp hq,odds_coordinate hp hq,mul_assoc]

private theorem affine_integral (f : ℝ → ℝ) (h k c : ℝ) :
    (∫ x, f (h+k*(x-c)))=|k⁻¹|*(∫ z, f z) := by
  calc
    _ = ∫ x, (fun y => f (h+k*y)) (x+(-c)) :=
      integral_congr_ae (ae_of_all _ fun _ => by rw [sub_eq_add_neg])
    _ = ∫ x, (fun y => f (h+y)) (k*x) := integral_add_right_eq_self _ _
    _ = |k⁻¹| • ∫ x, f (h+x) := Measure.integral_comp_mul_left _ _
    _ = _ := by rw [integral_add_left_eq_self,smul_eq_mul]

private theorem scaled_midpoint (a b l h : ℝ) (hd : b-a≠0) :
    (∫ x, positionGaussianDensity ((a+b)/2,l) x*oddsKernel (h+(b-a)/exp l*(x-(a+b)/2))) =
      sqrt (exp l)/(sqrt (2*π)*|b-a|) *
        ∫ z, oddsKernel z*exp (-(exp l)*(z-h)^2/(2*(b-a)^2)) := by
  let d := b-a
  let c := (a+b)/2
  let V := exp l
  have hv : 0<V := exp_pos _
  have hs := sqrt_pos.mpr hv
  have ht : 0<sqrt (2*π) := sqrt_pos.mpr (by positivity)
  let F := fun z => oddsKernel z*exp (-V*(z-h)^2/(2*d^2))
  have density (x : ℝ) : positionGaussianDensity (c,l) x*oddsKernel (h+d/V*(x-c)) =
      (sqrt (2*π*V))⁻¹*F (h+d/V*(x-c)) := by
    have he : -V*(h+d/V*(x-c)-h)^2/(2*d^2)= -(x-c)^2/(2*V) := by
      field_simp [hd,hv.ne'] <;> ring
    simp only [F,he,positionGaussianDensity,gaussianPDFReal,Real.coe_toNNReal _ hv.le]
    change (_*exp _)*_= _*(_*exp _)
    ring
  change (∫ x, positionGaussianDensity (c,l) x*oddsKernel (h+d/V*(x-c)))= _*∫ z, F z
  simp_rw [density]
  rw [integral_const_mul,affine_integral,← mul_assoc]
  congr 1
  rw [inv_div,abs_div,abs_of_pos hv,sqrt_mul (by positivity : 0≤2*π)]
  change (_*sqrt V)⁻¹*(V/|d|)=sqrt V/(sqrt (2*π)*|d|)
  field_simp [ht.ne',hs.ne',abs_ne_zero.mpr hd]
  nlinarith only [sq_sqrt hv.le]

/-- Exact conditional entropy at every positive noise variance, in the
posterior log-odds coordinate. -/
theorem exact_boundary_layer (u v a b l : ℝ) (hab : a≠b) :
    let p := lengthRatio u v
    let q := lengthRatio v u
    labelEntropy u v-labelInformation u v a b l =
      (sqrt (p*q)*overlap a b l)*(sqrt (exp l)/(sqrt (2*π)*|b-a|))*
      ∫ z, oddsKernel z*exp (-(exp l)*(z-(log q-log p))^2/(2*(b-a)^2)) := by
  intro p q
  rw [loss_as_midpoint_expectation,scaled_midpoint a b l _ (sub_ne_zero.mpr hab.symm),mul_assoc]

/-- The missing label entropy divided by the coherence and the noise
standard deviation has a finite, strictly positive sharp limit. -/
theorem sharp_entropy_prefactor (u v a b : ℝ) :
    a=b ∨ Tendsto (fun l => (labelEntropy u v-labelInformation u v a b l)/
      (overlap a b l*sqrt (exp l))) atBot
      (𝓝 (2*sqrt (2*π)*sqrt (lengthRatio u v*lengthRatio v u)/|b-a|)) := by
  by_cases hab : a=b
  · exact Or.inl hab
  right
  let p := lengthRatio u v
  let q := lengthRatio v u
  let k := sqrt (p*q)/(sqrt (2*π)*|b-a|)
  have hd := abs_ne_zero.mpr (sub_ne_zero.mpr hab.symm)
  have hs : 0<sqrt (2*π) := sqrt_pos.mpr (by positivity)
  have lim := (damped_odds_limit (log q-log p) (b-a)).const_mul k
  have he : k*(4*π)=2*sqrt (2*π)*sqrt (p*q)/|b-a| := by
    unfold k
    field_simp [hs.ne',hd]
    linear_combination -2*sqrt (p*q)*(sq_sqrt (show 0≤2*π by positivity))
  rw [he] at lim
  apply lim.congr
  intro l
  rw [exact_boundary_layer _ _ _ _ _ hab]
  have ho : 0<overlap a b l := exp_pos _
  have hv := sqrt_pos.mpr (exp_pos l)
  dsimp only [k,p,q,Function.comp_apply]
  field_simp [ho.ne',hv.ne',hs.ne',hd] <;> ring

#print axioms exact_boundary_layer
#print axioms sharp_entropy_prefactor
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
