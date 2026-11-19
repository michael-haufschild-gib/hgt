import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.BinaryGaussianLogLoss
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.CompleteCellGaussianFit
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.HaarCellNonlinearReadouts
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.EveryHaarCellHasPositiveWeilEnergy

/-!
# Information projection of a noisy logarithmic Haar pair

A sampled left or right value receives independent Gaussian noise of
variance exp l. Its best Gaussian has the original mean and the sum of
the Haar variance and the noise variance. For every nonzero detail the
optimal divergence grows like minus the logarithm of the noise standard
deviation, with a bounded error controlled by the entropy of the cell label.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology NNReal
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
open BiarithmeticGaugeGeometry

/-- Arithmetic mean of the two profile values under their length weights. -/
def center (u v a b : ℝ) := lengthRatio u v*a+lengthRatio v u*b

/-- Variance of the two possible values before measurement noise. -/
def signalVariance (u v a b : ℝ) := lengthRatio u v*lengthRatio v u*(a-b)^2

def labelEntropy (u v : ℝ) := -(lengthRatio u v*Real.log (lengthRatio u v))-
  lengthRatio v u*Real.log (lengthRatio v u)

/-- Information retained about which half supplied the noisy value. -/
def labelInformation (u v a b l : ℝ) :=
  let M := splitGaussian u v (a,l) (b,l)
  lengthRatio u v*(klDiv (positionGaussian a l) M).toReal+
    lengthRatio v u*(klDiv (positionGaussian b l) M).toReal

private theorem variance_nonneg (u v a b : ℝ) : 0 ≤ signalVariance u v a b :=
  mul_nonneg (mul_pos (lengthRatio_pos _ _) (lengthRatio_pos _ _)).le (sq_nonneg _)

private theorem variance_pos {u v a b : ℝ} (h : a ≠ b) : 0 < signalVariance u v a b :=
  mul_pos (mul_pos (lengthRatio_pos _ _) (lengthRatio_pos _ _)) (sq_pos_of_ne_zero (sub_ne_zero.mpr h))

/-- Exact cost at any Gaussian target. Only the conditional label information
is missing from the component-averaged Gaussian divergence. -/
theorem noisy_loss (u v a b l m j : ℝ) :
    let D := klDiv (splitGaussian u v (a,l) (b,l)) (positionGaussian m j)
    D ≠ ⊤ ∧ 2*(D.toReal+labelInformation u v a b l) =
      j-l-1+(Real.exp l+signalVariance u v a b+(center u v a b-m)^2)/Real.exp j := by
  obtain ⟨hf,_,_,he,_,_⟩ := mixture_decomposition u v a b l m j
  let p := lengthRatio u v
  let q := lengthRatio v u
  have hq : q=1-p := by linarith only [show p+q=1 from lengthRatio_sum _ _]
  have h := (gaussian_kl a l m j).2
  have hh := (gaussian_kl b l m j).2
  refine ⟨hf,?_⟩
  rw [labelInformation,← add_assoc,he]
  change 2*(p*_+q*_) = j-l-1+(Real.exp l+p*q*(a-b)^2+(p*a+q*b-m)^2)/Real.exp j
  rw [hq]
  linear_combination p*h + (1-p)*hh

/-- The binary label can contribute at most its discrete entropy. -/
theorem label_bounds (u v a b l : ℝ) :
    0 ≤ labelInformation u v a b l ∧ labelInformation u v a b l ≤ labelEntropy u v := by
  obtain ⟨_,_,_,_,ha,hb⟩ := mixture_decomposition u v a b l 0 0
  constructor
  · exact add_nonneg (mul_nonneg (lengthRatio_pos _ _).le ENNReal.toReal_nonneg)
      (mul_nonneg (lengthRatio_pos _ _).le ENNReal.toReal_nonneg)
  · have h := add_le_add (mul_le_mul_of_nonneg_left ha (lengthRatio_pos u v).le)
      (mul_le_mul_of_nonneg_left hb (lengthRatio_pos v u).le)
    simpa only [labelInformation,labelEntropy,mul_neg,sub_eq_add_neg] using h

/-- Divergence at the Gaussian with matching mean and variance. -/
def optimalLoss (u v a b l : ℝ) :=
  klDiv (splitGaussian u v (a,l) (b,l))
    (positionGaussian (center u v a b) (Real.log (Real.exp l+signalVariance u v a b)))

/-- Exact loss at the moment-matched Gaussian, including the retained label information. -/
theorem optimum (u v a b l : ℝ) :
    optimalLoss u v a b l ≠ ⊤ ∧
    2*((optimalLoss u v a b l).toReal+labelInformation u v a b l) =
      Real.log (Real.exp l+signalVariance u v a b)-l := by
  let V := Real.exp l+signalVariance u v a b
  have hv : 0 < V := add_pos_of_pos_of_nonneg (Real.exp_pos _) (variance_nonneg _ _ _ _)
  obtain ⟨hf,he⟩ := noisy_loss u v a b l (center u v a b) (Real.log V)
  refine ⟨hf,?_⟩
  rw [sub_self,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.exp_log hv,div_self hv.ne'] at he
  simpa only [sub_add_cancel] using he

/-- Exact excess and uniqueness of the Gaussian information projection. -/
theorem noisy_projection (u v a b l m j : ℝ) :
    let v₀ := Real.exp l+signalVariance u v a b
    let z := Real.log v₀-j
    let D := klDiv (splitGaussian u v (a,l) (b,l)) (positionGaussian m j)
    2*(D.toReal-(optimalLoss u v a b l).toReal) =
      Real.exp z-1-z+(center u v a b-m)^2/Real.exp j ∧
      (optimalLoss u v a b l ≤ D) ∧
      (D = optimalLoss u v a b l ↔ m=center u v a b ∧ j=Real.log v₀) := by
  intro V z D
  have hv : 0 < V := add_pos_of_pos_of_nonneg (Real.exp_pos _) (variance_nonneg _ _ _ _)
  obtain ⟨hd,h⟩ := noisy_loss u v a b l m j
  obtain ⟨ho,ho'⟩ := optimum u v a b l
  have he : 2*(D.toReal-(optimalLoss u v a b l).toReal) =
      Real.exp z-1-z+(center u v a b-m)^2/Real.exp j := by
    dsimp only [z,V,D]
    rw [Real.exp_sub,Real.exp_log hv]
    linear_combination h-ho'
  have hscale : 0 ≤ Real.exp z-1-z := by linarith only [Real.add_one_le_exp z]
  have hloc : 0 ≤ (center u v a b-m)^2/Real.exp j := div_nonneg (sq_nonneg _) (Real.exp_pos _).le
  refine ⟨he,(ENNReal.toReal_le_toReal ho hd).mp (by linarith only [he,hscale,hloc]),?_⟩
  constructor
  · intro eq
    rw [eq,sub_self,mul_zero] at he
    have hz : z=0 := by by_contra hn; linarith only [Real.add_one_lt_exp hn,he,hloc]
    have hzero : (center u v a b-m)^2/Real.exp j=0 := by linarith only [he,hscale,hloc]
    exact ⟨(sub_eq_zero.mp (sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hzero).resolve_right
      (Real.exp_ne_zero _)))).symm,(sub_eq_zero.mp hz).symm⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- For noise standard deviation exp(−s), the divergence at nonzero signal
has a uniform two-sided additive error around s. -/
theorem small_noise_bounds (u v : ℝ) (a b : ℝ) (s : ℝ≥0) :
    let V := signalVariance u v a b
    let D := (optimalLoss u v a b (-2*(s:ℝ))).toReal
    a=b ∨ (Real.log V/2-labelEntropy u v ≤ D-s ∧ D-s ≤ Real.log (1+V)/2) := by
  by_cases he : a=b
  · exact Or.inl he
  right
  have hv := variance_pos (u := u) (v := v) he
  have ht : Real.exp (-2*(s:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [s.2])
  have hl := Real.log_le_log hv (le_add_of_nonneg_left (Real.exp_pos (-2*(s:ℝ))).le)
  have hh := Real.log_le_log (add_pos (Real.exp_pos (-2*(s:ℝ))) hv)
    (add_le_add ht (le_refl (signalVariance u v a b)))
  have ho := (optimum u v a b (-2*(s:ℝ))).2
  obtain ⟨h0,h1⟩ := label_bounds u v a b (-2*(s:ℝ))
  constructor <;> linarith only [hl,hh,ho,h0,h1]

/-- The ratio to log inverse noise standard deviation tends exactly to one
at every nonconstant binary cell. A constant smoothed cell is itself Gaussian. -/
theorem small_noise_slope (u v a b : ℝ) :
    (a=b ∧ ∀ l, optimalLoss u v a b l=0) ∨
      Tendsto (fun s : ℝ => (optimalLoss u v a b (-2*s)).toReal/s) atTop (𝓝 1) := by
  by_cases he : a=b
  · left
    subst b
    refine ⟨rfl,fun l => ?_⟩
    have hc : center u v a a = a := by unfold center; rw [← add_mul,lengthRatio_sum,one_mul]
    have hM : splitGaussian u v (a,l) (a,l) = positionGaussian a l := by
      rw [splitGaussian_components,← add_smul,← ENNReal.ofReal_add (lengthRatio_pos _ _).le
        (lengthRatio_pos _ _).le,lengthRatio_sum,ENNReal.ofReal_one,one_smul]
    simp [optimalLoss,hM,hc,signalVariance]
  right
  let D := fun s : ℝ => (optimalLoss u v a b (-2*s)).toReal
  have bounds : ∀ᶠ s : ℝ in atTop,
      Real.log (signalVariance u v a b)/2-labelEntropy u v ≤ D s-s ∧
      D s-s ≤ Real.log (1+signalVariance u v a b)/2 :=
    (eventually_ge_atTop (0:ℝ)).mono fun s hs => (small_noise_bounds u v a b ⟨s,hs⟩).resolve_left he
  have lim := tendsto_bdd_div_atTop_nhds_zero (bounds.mono fun _ h => h.1)
    (bounds.mono fun _ h => h.2) (show Tendsto (fun s : ℝ => s) atTop atTop from tendsto_id)
  have hsum := lim.add (tendsto_const_nhds (x := (1:ℝ)))
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  change (D s-s)/s+1 = D s/s
  field_simp [hs.ne']

private def logLeft (i : ℕ) := Real.log (logCellWidth (2*(i+1)))
private def logRight (i : ℕ) := Real.log (logCellWidth (2*(i+1)+1))
private def leftValue (q d : ℕ → ℝ) (i : ℕ) := q (i+1)+d (i+1)*haarLeftCoeff (i+1)
private def rightValue (q d : ℕ → ℝ) (i : ℕ) := q (i+1)-d (i+1)*haarRightCoeff (i+1)

/-- Distribution of a noisy profile value under uniform sampling on a complete pair. -/
def noisyHaarLaw (q d : ℕ → ℝ) (i : ℕ) (l : ℝ) :=
  splitGaussian (logLeft i) (logRight i) (leftValue q d i,l) (rightValue q d i,l)

private theorem cell_weights (i : ℕ) :
    lengthRatio (logLeft i) (logRight i) = haarRightCoeff (i+1) ∧
    lengthRatio (logRight i) (logLeft i) = haarLeftCoeff (i+1) := by
  have hl := logCellWidth_pos (show 1 ≤ 2*(i+1) by omega)
  have hr := logCellWidth_pos (show 1 ≤ 2*(i+1)+1 by omega)
  simp only [lengthRatio,logLeft,logRight,Real.exp_log hl,Real.exp_log hr,haarRightCoeff,haarLeftCoeff]
  exact ⟨True.intro,by rw [add_comm (logCellWidth (2*(i+1)+1)) (logCellWidth (2*(i+1)))]⟩

private theorem cell_gap (q d : ℕ → ℝ) (i : ℕ) :
    leftValue q d i-rightValue q d i=d (i+1) := by
  unfold leftValue rightValue
  linear_combination d (i+1)*haarCoeff_sum (show 1 ≤ i+1 by omega)

private theorem cell_parameters (q d : ℕ → ℝ) (i : ℕ) :
    center (logLeft i) (logRight i) (leftValue q d i) (rightValue q d i) = q (i+1) ∧
    signalVariance (logLeft i) (logRight i) (leftValue q d i) (rightValue q d i) = pairVariance d (i+1) := by
  obtain ⟨hp,hq⟩ := cell_weights i
  constructor
  · rw [center,hp,hq,leftValue,rightValue]
    linear_combination q (i+1)*haarCoeff_sum (show 1 ≤ i+1 by omega)
  · rw [signalVariance,hp,hq,cell_gap,pairVariance,← logCellWidth_pair_sum (show 1 ≤ i+1 by omega)]
    unfold haarMass haarLeftCoeff haarRightCoeff
    ring

/-- Probability of each noisy event from the actual spatial readout, including
the zero-detail baseline subtracted in the definition of detailReadout. -/
theorem physical_event_law (q d : ℕ → ℝ) (i k : ℕ) (l : ℝ) (S : Set ℝ) :
    let a := i+1
    detailReadout (fun z => (positionGaussian (q a+z) l).real S) d (a+k) a =
      logCellWidth a*((noisyHaarLaw q d i l).real S-(positionGaussian (q a) l).real S) := by
  intro a
  have hl := logCellWidth_pos (show 1 ≤ 2*a by dsimp [a]; omega)
  have hr := logCellWidth_pos (show 1 ≤ 2*a+1 by dsimp [a]; omega)
  obtain ⟨hp,hq⟩ := cell_weights i
  have hm : (noisyHaarLaw q d i l).real S =
      haarRightCoeff a*(positionGaussian (leftValue q d i) l).real S+
      haarLeftCoeff a*(positionGaussian (rightValue q d i) l).real S := by
    rw [noisyHaarLaw,measureReal_def,splitGaussian_components,Measure.add_apply,Measure.smul_apply,
      Measure.smul_apply]
    simp only [smul_eq_mul,ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (lengthRatio_pos (logLeft i) (logRight i)).le,
      ENNReal.toReal_ofReal (lengthRatio_pos (logRight i) (logLeft i)).le,measureReal_def]
    rw [hp,hq]
  have hlen := logCellWidth_pair_sum (show 1 ≤ a by dsimp [a]; omega)
  have hleft : logCellWidth a * haarRightCoeff a = logCellWidth (2*a) := by
    rw [← hlen, haarRightCoeff]
    field_simp [(add_pos hl hr).ne']
  have hright : logCellWidth a * haarLeftCoeff a = logCellWidth (2*a+1) := by
    rw [← hlen, haarLeftCoeff]
    field_simp [(add_pos hl hr).ne']
  have weighted (A B C : ℝ) :
      (A-C)*logCellWidth (2*a)+(B-C)*logCellWidth (2*a+1) =
        logCellWidth a*(haarRightCoeff a*A+haarLeftCoeff a*B-C) := by
    rw [mul_sub,mul_add,← mul_assoc (logCellWidth a) _ A,← mul_assoc (logCellWidth a) _ B,
      hleft,hright,← hlen]
    ring
  rw [detailReadout_law _ d i k,hm]
  simpa only [leftValue,rightValue,add_zero,sub_eq_add_neg] using
    weighted ((positionGaussian (leftValue q d i) l).real S)
      ((positionGaussian (rightValue q d i) l).real S) ((positionGaussian (q a) l).real S)

/-- Unique Gaussian fit of the smoothed profile has its actual coarse value
as mean, and its Haar variance plus the smoothing variance as variance. -/
theorem physical_projection (q d : ℕ → ℝ) (i : ℕ) (l m j : ℝ) :
    let v := Real.exp l+pairVariance d (i+1)
    let P := noisyHaarLaw q d i l
    let D := klDiv P (positionGaussian m j)
    D ≠ ⊤ ∧ klDiv P (positionGaussian (q (i+1)) (Real.log v)) ≤ D ∧
      (D=klDiv P (positionGaussian (q (i+1)) (Real.log v)) ↔ m=q (i+1) ∧ j=Real.log v) := by
  obtain ⟨hc,hv⟩ := cell_parameters q d i
  have h := (noisy_projection (logLeft i) (logRight i) (leftValue q d i) (rightValue q d i) l m j).2
  simp only [optimalLoss,hc,hv] at h
  exact ⟨(noisy_loss _ _ _ _ _ _ _).1,h⟩

/-- For nonzero detail, the fitted KL grows with unit slope in minus log noise
standard deviation. Every zero-detail cell has zero fitted divergence at all scales. -/
theorem physical_small_noise (q d : ℕ → ℝ) (i : ℕ) :
    let loss := fun l => klDiv (noisyHaarLaw q d i l)
      (positionGaussian (q (i+1)) (Real.log (Real.exp l+pairVariance d (i+1))))
    (d (i+1)=0 ∧ ∀ l, loss l=0) ∨
      Tendsto (fun s : ℝ => (loss (-2*s)).toReal/s) atTop (𝓝 1) := by
  obtain ⟨hc,hv⟩ := cell_parameters q d i
  have h := small_noise_slope (logLeft i) (logRight i) (leftValue q d i) (rightValue q d i)
  simp only [optimalLoss,hc,hv] at h
  rcases h with ⟨he,h⟩|h
  · exact Or.inl ⟨by simpa only [he,sub_self] using (cell_gap q d i).symm,h⟩
  · exact Or.inr h

#print axioms physical_event_law
#print axioms physical_projection
#print axioms physical_small_noise
#print axioms noisy_loss
#print axioms label_bounds
#print axioms noisy_projection
#print axioms small_noise_bounds
#print axioms small_noise_slope
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
