import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.LogCellMixtureMomentDefect

/-!
# Gaussian smoothing of a two-valued logarithmic cell

Adding a common Gaussian error to both profile values gives a positive
density. The weighted divergence of the two components splits into the
mixture divergence and the information on the hidden cell label. The latter
is at most the entropy of the two lengths. At the moment-matched target
this gives a two-sided logarithmic law as the smoothing variance vanishes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair

private abbrev law (z : ℝ × ℝ) := positionGaussian z.1 z.2
private def logG (z : ℝ × ℝ) (x : ℝ) := Real.log (positionGaussianDensity z x)
private def logM (u v a b l x : ℝ) := Real.log (splitGaussianDensity u v (a,l) (b,l) x)

private theorem law_density (z : ℝ × ℝ) :
    law z = volume.withDensity (fun x => ENNReal.ofReal (positionGaussianDensity z x)) :=
  gaussianReal_of_var_ne_zero _ (Real.toNNReal_pos.mpr (Real.exp_pos _)).ne'

private theorem logG_formula (z : ℝ × ℝ) (x : ℝ) :
    logG z x = -(Real.log (2*Real.pi)+z.2)/2 -(x-z.1)^2/(2*Real.exp z.2) :=
  gaussian_log_pdf _ _ _

private theorem logG_int (p q : ℝ × ℝ) : Integrable (logG q) (law p) := by
  have h : Integrable (fun x : ℝ => (x-q.1)^2) (law p) :=
    gauss_offset_integrable _ _ _ _
  exact ((integrable_const (-(Real.log (2*Real.pi)+q.2)/2)).sub (h.div_const _)).congr
    (ae_of_all _ fun x => (logG_formula q x).symm)

private theorem logG_mean (p q : ℝ × ℝ) :
    (∫ x, logG q x ∂law p) =
      -(Real.log (2*Real.pi)+q.2)/2 - (Real.exp p.2+(p.1-q.1)^2)/(2*Real.exp q.2) := by
  let σ := Real.toNNReal (Real.exp p.2)
  have h2 : (∫ x : ℝ, x^2 ∂gaussianReal 0 σ) = (σ:ℝ) := by
    simpa using HTGeometry.integral_pow_gaussianReal_succ_succ σ 0
  have h : (∫ x, (x-q.1)^2 ∂law p) = Real.exp p.2+(p.1-q.1)^2 := by
    rw [show law p = gaussianReal p.1 σ from rfl,gauss_shifted_moment]
    norm_num [Finset.sum_range_succ,h2,HTGeometry.integral_pow_one_gaussianReal,
      HTGeometry.integral_pow_zero_gaussianReal,σ,Real.coe_toNNReal _ (Real.exp_pos _).le] <;> ring
  simp_rw [logG_formula]
  rw [integral_sub (integrable_const _) ((gauss_offset_integrable _ _ _ _).div_const _),
    integral_const,integral_div,h]
  simp

private theorem density_kl {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : ℝ → ℝ} (cp : Continuous p) (cq : Continuous q) (pp : ∀ x, 0 < p x) (pq : ∀ x, 0 < q x)
    (hp : P = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hq : Q = volume.withDensity (fun x => ENNReal.ofReal (q x)))
    (hi : Integrable (fun x => Real.log (p x)-Real.log (q x)) P) :
    klDiv P Q ≠ ⊤ ∧ (klDiv P Q).toReal = ∫ x, Real.log (p x)-Real.log (q x) ∂P := by
  have hpv : P ≪ volume := by rw [hp]; exact withDensity_absolutelyContinuous _ _
  have hqv : Q ≪ volume := by rw [hq]; exact withDensity_absolutelyContinuous _ _
  have hpq : P ≪ Q := by
    apply hpv.trans
    rw [hq]
    exact HTGeometry.ReflectedExponentialFamily.absolutelyContinuous_withDensity_of_pos
      (ENNReal.measurable_ofReal.comp cq.measurable) (fun x => (ENNReal.ofReal_pos.mpr (pq x)).ne')
  have hrp : P.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (p x) := by
    rw [hp]
    exact Measure.rnDeriv_withDensity _ (ENNReal.measurable_ofReal.comp cp.measurable)
  have hrq : Q.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (q x) := by
    rw [hq]
    exact Measure.rnDeriv_withDensity _ (ENNReal.measurable_ofReal.comp cq.measurable)
  have hl : llr P Q =ᵐ[P] fun x => Real.log (p x)-Real.log (q x) := by
    filter_upwards [hpq.ae_le (Measure.rnDeriv_eq_div hpv hqv),hpv.ae_le hrp,hpv.ae_le hrq]
      with x hx hy hz
    simp only [llr,hx,hy,hz,ENNReal.toReal_div,ENNReal.toReal_ofReal (pp x).le,
      ENNReal.toReal_ofReal (pq x).le,Real.log_div (pp x).ne' (pq x).ne']
  exact ⟨klDiv_ne_top hpq (hi.congr hl.symm),
    (toReal_klDiv_of_measure_eq hpq (by simp)).trans (integral_congr_ae hl)⟩

/-- Exact location and log-variance divergence of two nondegenerate Gaussians. -/
theorem gaussian_kl (a l b j : ℝ) :
    let D := klDiv (positionGaussian a l) (positionGaussian b j)
    D ≠ ⊤ ∧ 2*D.toReal = j-l-1+(Real.exp l+(a-b)^2)/Real.exp j := by
  obtain ⟨hf,he⟩ := density_kl (positionGaussianDensity_cont (a,l)) (positionGaussianDensity_cont (b,j))
    (positionGaussianDensity_pos _) (positionGaussianDensity_pos _) (law_density _) (law_density _)
    ((logG_int _ _).sub (logG_int _ _))
  refine ⟨hf,?_⟩
  change (klDiv _ _).toReal = ∫ x, logG (a,l) x-logG (b,j) x ∂law (a,l) at he
  rw [he,integral_sub (logG_int _ _) (logG_int _ _),logG_mean,logG_mean]
  dsimp only
  field_simp [Real.exp_ne_zero] <;> ring

private theorem logM_lower (u v a b l x : ℝ) :
    Real.log (lengthRatio u v)+logG (a,l) x ≤ logM u v a b l x ∧
    Real.log (lengthRatio v u)+logG (b,l) x ≤ logM u v a b l x := by
  let A := lengthRatio u v*positionGaussianDensity (a,l) x
  let B := lengthRatio v u*positionGaussianDensity (b,l) x
  have ha : 0 < A := mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos _ _)
  have hb : 0 < B := mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos _ _)
  have h (s t : ℝ) (z : ℝ × ℝ) : Real.log (lengthRatio s t)+logG z x =
      Real.log (lengthRatio s t*positionGaussianDensity z x) :=
    (Real.log_mul (lengthRatio_pos _ _).ne' (positionGaussianDensity_pos _ _).ne').symm
  rw [h,h]
  exact ⟨Real.log_le_log ha (le_add_of_nonneg_right hb.le),Real.log_le_log hb (le_add_of_nonneg_left ha.le)⟩

private theorem logM_upper (u v a b l x : ℝ) :
    logM u v a b l x ≤ -(Real.log (2*Real.pi)+l)/2 := by
  let C := -(Real.log (2*Real.pi)+l)/2
  have h (t : ℝ) : positionGaussianDensity (t,l) x ≤ Real.exp C := by
    apply (Real.log_le_iff_le_exp (positionGaussianDensity_pos _ _)).mp
    change logG (t,l) x ≤ C
    rw [logG_formula]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))
  apply (Real.log_le_iff_le_exp (splitGaussianDensity_pos _ _ _ _ _)).mpr
  calc
    _ ≤ lengthRatio u v*Real.exp C+lengthRatio v u*Real.exp C :=
      add_le_add (mul_le_mul_of_nonneg_left (h a) (lengthRatio_pos _ _).le)
        (mul_le_mul_of_nonneg_left (h b) (lengthRatio_pos _ _).le)
    _ = _ := by rw [← add_mul,lengthRatio_sum,one_mul]

private theorem logM_int (u v a b l : ℝ) (z : ℝ × ℝ) : Integrable (logM u v a b l) (law z) := by
  let f := fun x => Real.log (lengthRatio u v)+logG (a,l) x
  let C := -(Real.log (2*Real.pi)+l)/2
  have hi : Integrable f (law z) := (integrable_const _).add (logG_int _ _)
  apply (hi.norm.add (integrable_const |C|)).mono'
  · exact ((splitGaussianDensity_cont _ _ _ _).log fun x => (splitGaussianDensity_pos _ _ _ _ x).ne').aestronglyMeasurable
  · apply ae_of_all
    intro x
    change |logM u v a b l x| ≤ |f x|+|C|
    apply abs_le.mpr
    have hl : f x ≤ logM u v a b l x := (logM_lower _ _ _ _ _ _).1
    have hh : logM u v a b l x ≤ C := logM_upper _ _ _ _ _ _
    constructor <;> linarith only [hl,hh,neg_abs_le (f x),le_abs_self C,abs_nonneg C,abs_nonneg (f x)]

/-- One component's posterior label loss as an ordinary density integral.
The positive weight is written in logarithmic coordinates. -/
theorem component_label_loss (u v a b l t w : ℝ) :
    let p := Real.exp w
    let D := (klDiv (positionGaussian t l) (splitGaussian u v (a,l) (b,l))).toReal
    -p*w-p*D = ∫ x, (p*positionGaussianDensity (t,l) x) *
      (Real.log (splitGaussianDensity u v (a,l) (b,l) x)-Real.log (p*positionGaussianDensity (t,l) x)) := by
  intro p D
  have hM := logM_int u v a b l (t,l)
  have hG := logG_int (t,l) (t,l)
  have hD : D = ∫ x, logG (t,l) x-logM u v a b l x ∂law (t,l) :=
    (density_kl (positionGaussianDensity_cont (t,l)) (splitGaussianDensity_cont u v (a,l) (b,l))
      (positionGaussianDensity_pos _) (splitGaussianDensity_pos _ _ _ _) (law_density _) rfl (hG.sub hM)).2
  have score : -w-D = ∫ x, logM u v a b l x-logG (t,l) x-w ∂law (t,l) := by
    rw [hD,integral_sub hG hM,integral_sub (hM.sub hG) (integrable_const _),integral_sub hM hG]
    simp only [integral_const,probReal_univ,one_smul]
    ring
  change -p*w-p*D = _
  rw [show -p*w-p*D=p*(-w-D) by ring,score]
  change p*(∫ x, _ ∂gaussianReal t (Real.toNNReal (Real.exp l))) = _
  rw [integral_gaussianReal_eq_integral_smul (Real.toNNReal_pos.mpr (Real.exp_pos l)).ne',← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  rw [Real.log_mul (Real.exp_ne_zero _) (positionGaussianDensity_pos _ _).ne',show Real.log p=w from Real.log_exp _]
  change p*(positionGaussianDensity (t,l) x*(_-_ - w)) = _
  unfold logG logM
  ring

/-- Divergence of the common-noise mixture splits exactly. The component
label contributes a weighted sum of divergences to the output mixture. -/
theorem mixture_decomposition (u v a b l m j : ℝ) :
    let p := lengthRatio u v
    let q := lengthRatio v u
    let A := positionGaussian a l
    let B := positionGaussian b l
    let M := splitGaussian u v (a,l) (b,l)
    let G := positionGaussian m j
    klDiv M G ≠ ⊤ ∧ klDiv A M ≠ ⊤ ∧ klDiv B M ≠ ⊤ ∧
      (klDiv M G).toReal+p*(klDiv A M).toReal+q*(klDiv B M).toReal =
        p*(klDiv A G).toReal+q*(klDiv B G).toReal ∧
      (klDiv A M).toReal ≤ -Real.log p ∧ (klDiv B M).toReal ≤ -Real.log q := by
  intro p q A B M G
  let f := logM u v a b l
  let g := logG (m,j)
  have h (t : ℝ) : Integrable (fun x => f x-g x) (positionGaussian t l) :=
    (logM_int _ _ _ _ _ _).sub (logG_int _ _)
  have hM : Integrable (fun x => f x-g x) M := by
    change Integrable _ (splitGaussian _ _ _ _)
    rw [splitGaussian_components,integrable_add_measure]
    exact ⟨(h a).smul_measure ENNReal.ofReal_ne_top,(h b).smul_measure ENNReal.ofReal_ne_top⟩
  obtain ⟨hm,em⟩ := density_kl (splitGaussianDensity_cont u v (a,l) (b,l)) (positionGaussianDensity_cont (m,j))
    (splitGaussianDensity_pos _ _ _ _) (positionGaussianDensity_pos _) (P := M) rfl (law_density _) hM
  have split (t : ℝ) :
      klDiv (positionGaussian t l) M ≠ ⊤ ∧
      (klDiv (positionGaussian t l) M).toReal =
        (∫ x, logG (t,l) x ∂positionGaussian t l)-(∫ x, f x ∂positionGaussian t l) := by
    obtain ⟨hf,he⟩ := density_kl (positionGaussianDensity_cont (t,l)) (splitGaussianDensity_cont u v (a,l) (b,l))
      (positionGaussianDensity_pos _) (splitGaussianDensity_pos _ _ _ _) (law_density _) (Q := M) rfl
      ((logG_int _ _).sub (logM_int _ _ _ _ _ _))
    exact ⟨hf,he.trans (integral_sub (logG_int _ _) (logM_int _ _ _ _ _ _))⟩
  have single (t : ℝ) : (klDiv (positionGaussian t l) G).toReal =
      (∫ x, logG (t,l) x ∂positionGaussian t l)-(∫ x, g x ∂positionGaussian t l) := by
    have he := (density_kl (positionGaussianDensity_cont (t,l)) (positionGaussianDensity_cont (m,j))
      (positionGaussianDensity_pos _) (positionGaussianDensity_pos _) (law_density _) (law_density _)
      ((logG_int _ _).sub (logG_int _ _))).2
    exact he.trans (integral_sub (logG_int _ _) (logG_int _ _))
  have ub (t w : ℝ) (hl : ∀ x, Real.log w+logG (t,l) x ≤ f x) :
      (klDiv (positionGaussian t l) M).toReal ≤ -Real.log w := by
    have he := integral_mono ((integrable_const _).add (logG_int (t,l) (t,l))) (logM_int _ _ _ _ _ (t,l)) hl
    rw [integral_add (integrable_const _) (logG_int _ _),integral_const] at he
    simp only [probReal_univ,one_smul] at he
    rw [(split t).2]
    linarith only [he]
  refine ⟨hm,(split a).1,(split b).1,?_,ub a p (fun x => (logM_lower _ _ _ _ _ x).1),
    ub b q (fun x => (logM_lower _ _ _ _ _ x).2)⟩
  change (klDiv M G).toReal = ∫ x, f x-g x ∂M at em
  have em' : (∫ x, f x-g x ∂M) = p*(∫ x, f x-g x ∂A)+q*(∫ x, f x-g x ∂B) := by
    rw [show M = _ from splitGaussian_components u v (a,l) (b,l),
      integral_add_measure ((h a).smul_measure ENNReal.ofReal_ne_top) ((h b).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure,integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (lengthRatio_pos _ _).le,smul_eq_mul,p,q,A,B]
  rw [em,em',(split a).2,(split b).2,single a,single b,integral_sub (logM_int _ _ _ _ _ _) (logG_int _ _),
    integral_sub (logM_int _ _ _ _ _ _) (logG_int _ _)]
  ring

#print axioms gaussian_kl
#print axioms mixture_decomposition
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
