import GaloisForLFunctions.RHTower.WeilWorkExposingRayUniformPolarTail
import GaloisForLFunctions.RHTower.WeilPolarConeExposedDuality

/-!
# An actual odd polar source and its shorter complementary residual

The fixed four-translate filter of Riemann's full kernel has exact half-pole and
Weil-zero cancellation. At every lag, its autocorrelation plus the leading
polar exposing kernel equals the autocorrelation of a source of translation
width three-halves. The same identity holds for every literal smooth cutoff.

Cutoffs are actual compact C² polar tests. Their Fourier densities and signed
archimedean energies satisfy the exact complementary identity. No positivity
or smallness of the residual energy is asserted. The full source is not compact.
The separate tail leaf proves the literal opposite exposing-tail proportion;
finite-head matching and the universal WP02 lower inequality remain open.

Paper: docs/reports/weil-work/results/02-exposing-ray/CRITICAL-WIDTH-ODD-PROOF.md.
-/

open MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayCriticalOdd


private def positions : Fin 5 → ℝ := ![-1,-(1/2),0,1/2,1]
private def synthesis (U : ℝ → ℝ) (c : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  ∑ j, c j * U (t-positions j)
private def evenCoeff (q : ℝ) : Fin 5 → ℝ := ![-q,0,1,0,-q]
private def oddCoeff (q h : ℝ) : Fin 5 → ℝ := ![-q,2*h*q,0,-2*h*q,q]
private def residualCoeff (q h : ℝ) : Fin 5 → ℝ := ![0,-2*h*q,1,2*h*q,-2*q]

private theorem synthesis_corr (U : ℝ → ℝ)
    (hi : ∀ a b : ℝ, Integrable (fun t => U (t-a)*U (t-b)))
    (c : Fin 5 → ℝ) (y : ℝ) :
    crossCorr (synthesis U c) (synthesis U c) y =
      ∑ i, ∑ j, c i*c j*crossCorr U U (y-(positions i-positions j)) := by
  have hint (i j : Fin 5) : Integrable (fun t =>
      c i*U (t-positions i)*(c j*U (t-y-positions j))) := by
    have := (hi (positions i) (y+positions j)).const_mul (c i*c j)
    refine this.congr (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [show t-(y+positions j)=t-y-positions j by ring]
    ring
  unfold crossCorr synthesis
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ fun j _ => hint i j]
  apply Finset.sum_congr rfl; intro j _
  rw [← integral_const_mul,
    ← integral_add_right_eq_self (μ:=volume)
      (fun t => c i*U (t-positions i)*(c j*U (t-y-positions j))) (positions i)]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [add_sub_cancel_right,
    show t+positions i-y-positions j=t-(y-(positions i-positions j)) by ring]
  ring

private theorem complementary_corr (U : ℝ → ℝ)
    (hi : ∀ a b : ℝ, Integrable (fun t => U (t-a)*U (t-b))) (q h y : ℝ) :
    crossCorr (synthesis U (evenCoeff q)) (synthesis U (evenCoeff q)) y +
      crossCorr (synthesis U (oddCoeff q h)) (synthesis U (oddCoeff q h)) y =
      crossCorr (synthesis U (residualCoeff q h)) (synthesis U (residualCoeff q h)) y := by
  rw [synthesis_corr U hi,synthesis_corr U hi,synthesis_corr U hi]
  simp only [Fin.sum_univ_succ,evenCoeff,oddCoeff,residualCoeff,positions,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  ring_nf

/-- Odd width-two filter, balanced by the exact half-step hyperbolic moment. -/
def oddFilter (U : ℝ → ℝ) (t : ℝ) : ℝ :=
  polarWeight 1*(U (t-1)-U (t+1)-2*cosh (1/4)*(U (t-1/2)-U (t+1/2)))

/-- The complementary filter has translation width three-halves. -/
def residualFilter (U : ℝ → ℝ) (t : ℝ) : ℝ :=
  U t-2*cosh (1/4)*polarWeight 1*U (t+1/2)+
    2*cosh (1/4)*polarWeight 1*U (t-1/2)-2*polarWeight 1*U (t-1)

/-- Actual full odd Riemann source. -/
def source (t : ℝ) : ℂ := oddFilter riemannKernelReal t
/-- Actual shorter residual source. -/
def residual (t : ℝ) : ℂ := residualFilter riemannKernelReal t
/-- Literal smooth truncation, retaining the full odd polar filter. -/
def compactSource (L t : ℝ) : ℂ := oddFilter (truncatedRiemannKernelReal L) t
/-- The compact shorter residual. -/
def compactResidual (L t : ℝ) : ℂ := residualFilter (truncatedRiemannKernelReal L) t

private theorem synthesis_even (U : ℝ → ℝ) :
    synthesis U (evenCoeff (polarWeight 1)) = polarShift 1 U := by
  funext t
  simp [synthesis,evenCoeff,positions,Fin.sum_univ_succ,polarShift]
  ring

private theorem synthesis_odd (U : ℝ → ℝ) :
    synthesis U (oddCoeff (polarWeight 1) (cosh (1/4))) = oddFilter U := by
  funext t
  simp [synthesis,oddCoeff,positions,Fin.sum_univ_succ,oddFilter]
  ring

private theorem synthesis_residual (U : ℝ → ℝ) :
    synthesis U (residualCoeff (polarWeight 1) (cosh (1/4))) = residualFilter U := by
  funext t
  simp [synthesis,residualCoeff,positions,Fin.sum_univ_succ,residualFilter]
  ring

private theorem filters_corr (U : ℝ → ℝ)
    (hi : ∀ a b : ℝ, Integrable (fun t => U (t-a)*U (t-b))) (y : ℝ) :
    crossCorr (polarShift 1 U) (polarShift 1 U) y +
      crossCorr (oddFilter U) (oddFilter U) y =
      crossCorr (residualFilter U) (residualFilter U) y := by
  simpa only [synthesis_even,synthesis_odd,synthesis_residual] using
    complementary_corr U hi (polarWeight 1) (cosh (1/4)) y

private theorem phi_pair_integrable (a b : ℝ) :
    Integrable (fun t => riemannKernelReal (t-a)*riemannKernelReal (t-b)) := by
  obtain ⟨B,hB,h⟩ := exists_riemannKernelReal_le
  have hi : Integrable (fun t => riemannKernelReal (t-a)) := by
    simpa only [sub_eq_add_neg] using WeilExcess.integrable_riemannKernelReal.comp_add_right (-a)
  refine hi.mul_bdd (c:=B)
    (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs,abs_of_pos (riemannKernelReal_pos _)]
  exact (h _).trans ((mul_le_mul_of_nonneg_left
    (exp_le_one_iff.mpr (by linarith [abs_nonneg (t-b)])) hB).trans_eq (mul_one B))

private theorem compact_pair_integrable (L a b : ℝ) :
    Integrable (fun t => truncatedRiemannKernelReal L (t-a)*truncatedRiemannKernelReal L (t-b)) := by
  exact ((continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const) |>.mul
    ((continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    (((hasCompactSupport_truncatedRiemannKernelReal L).comp_homeomorph (Homeomorph.subRight a)).mul_right)

private theorem weilTest_ofReal (U : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun t => (U t : ℂ)) (fun t => (U t : ℂ)) y = (crossCorr U U y : ℂ) := by
  rw [weilTest_apply,crossCorr]
  simp only [Complex.conj_ofReal,← Complex.ofReal_mul]
  exact integral_ofReal

/-- Complete all-lag complementary identity for the actual full source. -/
theorem source_correlation (y : ℝ) :
    EF.weilTest source source y + (polarExposingKernel 1 y : ℂ) =
      EF.weilTest residual residual y := by
  unfold source residual
  rw [weilTest_ofReal,weilTest_ofReal,
    ExposingRaySmallShift.polarExposingKernel_eq_corr,← Complex.ofReal_add]
  congr 1
  linarith [filters_corr riemannKernelReal phi_pair_integrable y]

/-- Actual atom normalization, with the whole shorter residual retained. -/
theorem source_atom (n : ℕ) :
    atomCoeff source n + (polarExposingKernel 1 (log n)+polarExposingKernel 1 (-log n)) =
      atomCoeff residual n := by
  have h1 := congrArg Complex.re (source_correlation (log n))
  have h2 := congrArg Complex.re (source_correlation (-log n))
  simp only [Complex.add_re,Complex.ofReal_re] at h1 h2
  unfold atomCoeff
  simp only [Complex.add_re]
  linarith

/-- The same exact identity holds at every cutoff and every real lag. -/
theorem compact_correlation (L y : ℝ) :
    EF.weilTest (compactSource L) (compactSource L) y +
      EF.weilTest (polarRiemannDifference L 1) (polarRiemannDifference L 1) y =
      EF.weilTest (compactResidual L) (compactResidual L) y := by
  have he : polarRiemannDifference L 1 = fun t => (polarShift 1 (truncatedRiemannKernelReal L) t : ℂ) := by
    funext t
    rw [polarRiemannDifference_eq]
    simp [polarRiemannDifferenceReal,polarShift,sub_neg_eq_add]
  unfold compactSource compactResidual
  rw [he,weilTest_ofReal,weilTest_ofReal,weilTest_ofReal,
    ← Complex.ofReal_add]
  congr 1
  linarith [filters_corr (truncatedRiemannKernelReal L) (compact_pair_integrable L) y]


/-- Entire multiplier of the fixed odd filter. -/
def multiplier (z : ℂ) : ℂ :=
  (polarWeight 1 : ℂ)*(Complex.exp (Complex.I*z)-Complex.exp (-Complex.I*z)-
    (2*cosh (1/4) : ℝ)*(Complex.exp (Complex.I*z/2)-Complex.exp (-Complex.I*z/2)))

private theorem synthesis_fourier (U : ℝ → ℝ)
    (hi : ∀ (a : ℝ) (z : ℂ), Integrable (fun t => (U (t-a) : ℂ)*Complex.exp (Complex.I*z*t)))
    (c : Fin 5 → ℝ) (z : ℂ) :
    paperFT (fun t => (synthesis U c t : ℂ)) z =
      (∑ j,(c j : ℂ)*Complex.exp (Complex.I*z*(positions j)))*paperFT (fun t => (U t : ℂ)) z := by
  unfold synthesis paperFT
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  have hint (j : Fin 5) : Integrable (fun t =>
      (c j : ℂ)*(U (t-positions j) : ℂ)*Complex.exp (Complex.I*z*t)) := by
    simpa only [mul_assoc] using (hi (positions j) z).const_mul (c j : ℂ)
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl; intro j _
  simp_rw [mul_assoc (c j : ℂ)]
  rw [integral_const_mul]
  change (c j : ℂ)*paperFT (fun t => (U (t-positions j) : ℂ)) z = _
  rw [paperFT_translate' (fun t => (U t : ℂ)) (positions j) z]
  rfl

private theorem odd_fourier (U : ℝ → ℝ)
    (hi : ∀ (a : ℝ) (z : ℂ), Integrable (fun t => (U (t-a) : ℂ)*Complex.exp (Complex.I*z*t)))
    (z : ℂ) : paperFT (fun t => (oddFilter U t : ℂ)) z =
      multiplier z*paperFT (fun t => (U t : ℂ)) z := by
  rw [← synthesis_odd,synthesis_fourier U hi]
  congr 1
  simp [multiplier,oddCoeff,positions,Fin.sum_univ_succ]
  ring_nf

private theorem multiplier_half_poles :
    multiplier (Complex.I/2) = 0 ∧ multiplier (-(Complex.I/2)) = 0 := by
  have hc : (2*cosh (1/4) : ℝ) = exp (1/4)+exp (-(1/4)) := by
    rw [Real.cosh_eq]; ring
  have ep : exp (1/2:ℝ) = exp (1/4)*exp (1/4) := by
    rw [← exp_add]; congr 1; ring
  have em : exp (-(1/2):ℝ) = exp (-(1/4))*exp (-(1/4)) := by
    rw [← exp_add]; congr 1; ring
  have hp : Complex.I*(Complex.I/2) = (-(1/2):ℂ) := by
    rw [mul_div,show Complex.I*Complex.I = -1 by simpa only [pow_two] using Complex.I_sq]
    ring
  have hm : -Complex.I*(Complex.I/2) = (1/2:ℂ) := by rw [neg_mul,hp]; ring
  have hp' : Complex.I*(-(Complex.I/2)) = (1/2:ℂ) := by rw [mul_neg,hp]; ring
  have hm' : -Complex.I*(-(Complex.I/2)) = (-(1/2):ℂ) := by rw [mul_neg,hm]
  have hreal : exp (-(1/2:ℝ))-exp (1/2)-(2*cosh (1/4))*(exp (-(1/4))-exp (1/4)) = 0 := by
    rw [hc,ep,em]; ring
  have hreal' : exp (1/2:ℝ)-exp (-(1/2))-(2*cosh (1/4))*(exp (1/4)-exp (-(1/4))) = 0 := by
    rw [hc,ep,em]; ring
  constructor
  · rw [multiplier,hp,hm]
    have he : Complex.exp (-(1/2:ℂ))-Complex.exp (1/2)-(2*cosh (1/4):ℝ)*
        (Complex.exp ((-(1/2:ℂ))/2)-Complex.exp ((1/2:ℂ)/2)) = 0 := by
      convert congrArg (fun x : ℝ => (x : ℂ)) hreal using 1 <;>
        push_cast <;> norm_num
    rw [he,mul_zero]
  · rw [multiplier,hp',hm']
    have he : Complex.exp (1/2:ℂ)-Complex.exp (-(1/2))-(2*cosh (1/4):ℝ)*
        (Complex.exp ((1/2:ℂ)/2)-Complex.exp ((-(1/2:ℂ))/2)) = 0 := by
      convert congrArg (fun x : ℝ => (x : ℂ)) hreal' using 1 <;>
        push_cast <;> norm_num
    rw [he,mul_zero]

private theorem phi_translate_exp_integrable (a : ℝ) (z : ℂ) :
    Integrable (fun t => (riemannKernelReal (t-a) : ℂ)*Complex.exp (Complex.I*z*t)) := by
  have h := (integrable_riemannPhiKernel_mul_exp z).comp_add_right (-a) |>.mul_const
    (Complex.exp (Complex.I*z*a))
  refine h.congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [riemannPhiKernel_eq_ofReal,mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact entire transform of the full source. -/
theorem source_fourier (z : ℂ) : paperFT source z = multiplier z*paperFT riemannPhiKernel z := by
  have h := odd_fourier riemannKernelReal phi_translate_exp_integrable z
  unfold source
  rw [show riemannPhiKernel = (fun t => (riemannKernelReal t : ℂ)) from
    funext riemannPhiKernel_eq_ofReal]
  exact h

/-- Both half-poles vanish exactly for the actual full source. -/
theorem source_half_poles :
    paperFT source (Complex.I/2) = 0 ∧ paperFT source (-(Complex.I/2)) = 0 := by
  constructor
  · rw [source_fourier,multiplier_half_poles.1,zero_mul]
  · rw [source_fourier,multiplier_half_poles.2,zero_mul]

/-- Every literal Weil-zero evaluation vanishes, without RH. -/
theorem source_zero_evaluations (ρ : Zeta23.zetaZeroConfig.carrier) :
    paperFT source (Zeta23.gammaOf ρ) = 0 ∧
      paperFT source ((starRingEnd ℂ) (Zeta23.gammaOf ρ)) = 0 := by
  have h := paperFT_riemannKernelDeriv_at_zero 0 ρ.property
  rw [riemannKernelDeriv_zero] at h
  constructor
  · rw [source_fourier,h.1,mul_zero]
  · rw [source_fourier,h.2,mul_zero]

private theorem compact_translate_exp_integrable (L a : ℝ) (z : ℂ) :
    Integrable (fun t => (truncatedRiemannKernelReal L (t-a) : ℂ)*Complex.exp (Complex.I*z*t)) := by
  simpa only [truncatedRiemannKernel_eq] using integrable_translate_mul_cexp L a z

/-- Exact compact transform; cutoff does not disturb pole cancellation. -/
theorem compact_fourier (L : ℝ) (z : ℂ) :
    paperFT (compactSource L) z = multiplier z*paperFT (truncatedRiemannKernel L) z := by
  unfold compactSource
  rw [show truncatedRiemannKernel L = (fun t => (truncatedRiemannKernelReal L t : ℂ)) from
    funext (truncatedRiemannKernel_eq L)]
  exact odd_fourier (truncatedRiemannKernelReal L) (compact_translate_exp_integrable L) z

private theorem compact_source_expression (L : ℝ) : compactSource L = fun t =>
    (polarWeight 1 : ℂ)*(truncatedRiemannKernel L (t-1)-truncatedRiemannKernel L (t+1)-
      (2*cosh (1/4) : ℝ)*(truncatedRiemannKernel L (t-1/2)-truncatedRiemannKernel L (t+1/2))) := by
  funext t
  simp only [compactSource,oddFilter,truncatedRiemannKernel_eq]
  push_cast
  rfl

private theorem compact_source_contDiff (L : ℝ) : ContDiff ℝ 2 (compactSource L) := by
  rw [compact_source_expression]
  have h : ContDiff ℝ 2 (truncatedRiemannKernel L) := contDiff_nearRadicalTest L _
  exact contDiff_const.mul (((h.comp (contDiff_id.sub contDiff_const)).sub
    (h.comp (contDiff_id.add contDiff_const))).sub (contDiff_const.mul
      ((h.comp (contDiff_id.sub contDiff_const)).sub (h.comp (contDiff_id.add contDiff_const)))))

private theorem compact_source_support (L : ℝ) :
    tsupport (compactSource L) ⊆ Icc (-(L+1)) (L+1) := by
  rw [compact_source_expression]
  apply tsupport_subset_of_vanish
  intro t ht
  have hp : ∀ s : ℝ, |s| ≤ 1 → truncatedRiemannKernel L (t-s) = 0 := by
    intro s hs
    apply truncatedRiemannKernel_eq_zero
    have := abs_sub_abs_le_abs_sub t s
    linarith
  simp only [hp 1 (by norm_num),show t+1=t-(-1) by ring,hp (-1) (by norm_num),
    hp (1/2) (by norm_num),show t+1/2=t-(-(1/2)) by ring,hp (-(1/2)) (by norm_num),
    sub_zero,mul_zero]

/-- Every nonnegative cutoff produces a genuine compact C² polar test. -/
theorem compact_polar {L : ℝ} (hL : 0 ≤ L) : IsPolarTest (L+1) (compactSource L) := by
  refine ⟨by linarith,compact_source_contDiff L,compact_source_support L,?_,?_⟩
  · rw [compact_fourier,multiplier_half_poles.1,zero_mul]
  · rw [compact_fourier,multiplier_half_poles.2,zero_mul]

private theorem compact_residual_expression (L : ℝ) :
    compactResidual L = fun t => polarRiemannDifference L 1 t-compactSource L t := by
  funext t
  simp only [compactResidual,compactSource,residualFilter,oddFilter,
    polarRiemannDifference_eq,polarRiemannDifferenceReal,sub_neg_eq_add]
  push_cast
  ring

private theorem compact_even_polar {L : ℝ} (hL : 0 ≤ L) :
    IsPolarTest (L+1) (polarRiemannDifference L 1) :=
  ⟨by linarith,contDiff_polarRiemannDifference L 1,
    tsupport_polarRiemannDifference (by norm_num),paperFT_polarRiemannDifference_pole L 1⟩

private theorem compact_of_polar {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f) :
    HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hf.2.2.1

private theorem fourier_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (fun t => f t-g t) z = paperFT f z-paperFT g z := by
  have hi : Integrable (fun t => f t*Complex.exp (Complex.I*z*t)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hj : Integrable (fun t => g t*Complex.exp (Complex.I*z*t)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  unfold paperFT
  simp_rw [sub_mul]
  exact integral_sub hi hj

/-- The complementary shorter cutoff source is also an actual polar test. -/
theorem compact_residual_polar {L : ℝ} (hL : 0 ≤ L) :
    IsPolarTest (L+1) (compactResidual L) := by
  have he := compact_even_polar hL
  have ho := compact_polar hL
  rw [compact_residual_expression]
  refine ⟨he.1,he.2.1.sub ho.2.1,?_,?_,?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra h
    have he0 := image_eq_zero_of_notMem_tsupport (fun hx => h (he.2.2.1 hx))
    have ho0 := image_eq_zero_of_notMem_tsupport (fun hx => h (ho.2.2.1 hx))
    exact ht (by simp only [he0,ho0,sub_self])
  · rw [fourier_sub he.2.1.continuous ho.2.1.continuous (compact_of_polar he) (compact_of_polar ho),
      he.2.2.2.1,ho.2.2.2.1,sub_self]
  · rw [fourier_sub he.2.1.continuous ho.2.1.continuous (compact_of_polar he) (compact_of_polar ho),
      he.2.2.2.2,ho.2.2.2.2,sub_self]

private theorem fourier_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (fun t => f t+g t) z = paperFT f z+paperFT g z := by
  have hi : Integrable (fun t => f t*Complex.exp (Complex.I*z*t)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hj : Integrable (fun t => g t*Complex.exp (Complex.I*z*t)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  unfold paperFT
  simp_rw [add_mul]
  exact integral_add hi hj

/-- Pointwise real-frequency energy identity, retaining the whole residual. -/
theorem compact_density_identity {L : ℝ} (hL : 0 ≤ L) (τ : ℝ) :
    ‖paperFT (compactSource L) τ‖^2+‖paperFT (polarRiemannDifference L 1) τ‖^2 =
      ‖paperFT (compactResidual L) τ‖^2 := by
  have he := compact_even_polar hL
  have ho := compact_polar hL
  have hr := compact_residual_polar hL
  have hec := compact_of_polar he
  have hoc := compact_of_polar ho
  have hrc := compact_of_polar hr
  have heq := funext (compact_correlation L)
  have h := congrArg (fun f => paperFT f (τ : ℂ)) heq
  rw [fourier_add (EF.weilTest_contDiff ho.2.1 ho.2.1.continuous hoc).continuous
    (EF.weilTest_contDiff he.2.1 he.2.1.continuous hec).continuous
    (EF.weilTest_hasCompactSupport hoc hoc) (EF.weilTest_hasCompactSupport hec hec),
    paperFT_weilTest_self_ofReal ho.2.1.continuous hoc,
    paperFT_weilTest_self_ofReal he.2.1.continuous hec,
    paperFT_weilTest_self_ofReal hr.2.1.continuous hrc,← Complex.ofReal_add] at h
  exact Complex.ofReal_injective h

/-- Exact signed archimedean accounting. No sign for the residual is assumed. -/
theorem compact_energy_identity {L : ℝ} (hL : 0 ≤ L) :
    archEnergy (compactSource L)+archEnergy (polarRiemannDifference L 1) =
      archEnergy (compactResidual L) := by
  have he := compact_even_polar hL
  have ho := compact_polar hL
  unfold archEnergy
  rw [← integral_add (integrable_normSq_paperFT_mul_arch ho.2.1 ho.2.2.1)
    (integrable_normSq_paperFT_mul_arch he.2.1 he.2.2.1)]
  apply integral_congr_ae (Eventually.of_forall fun τ => ?_)
  rw [← add_mul,compact_density_identity hL τ]

private theorem odd_filter_neg (U : ℝ → ℝ) (hu : ∀ t, U (-t)=U t) (t : ℝ) :
    oddFilter U (-t) = -oddFilter U t := by
  unfold oddFilter
  rw [show -t-1=-(t+1) by ring,show -t+1=-(t-1) by ring,
    show -t-1/2=-(t+1/2) by ring,show -t+1/2=-(t-1/2) by ring,hu,hu,hu,hu]
  ring

/-- The full source is literally odd. -/
theorem source_odd (t : ℝ) : source (-t) = -source t := by
  unfold source
  rw [odd_filter_neg riemannKernelReal WeilExcess.riemannKernelReal_neg,Complex.ofReal_neg]

/-- The exact smooth cutoff retains odd parity. -/
theorem compact_source_odd (L t : ℝ) : compactSource L (-t) = -compactSource L t := by
  have he (u : ℝ) : truncatedRiemannKernelReal L (-u)=truncatedRiemannKernelReal L u := by
    unfold truncatedRiemannKernelReal bulkCutoff
    rw [WeilExcess.riemannKernelReal_neg]
    simp only [sub_neg_eq_add,← sub_eq_add_neg]
    ring
  unfold compactSource
  rw [odd_filter_neg _ he,Complex.ofReal_neg]

end RHTower.ExposingRayCriticalOdd
