import GaloisForLFunctions.RHTower.ChiCubicMellinTrace
import GaloisForLFunctions.RHTower.ChiRamanujanSubpowerSourceEnvelope
import GaloisForLFunctions.RHTower.ChiRamanujanSignedSourceTransfer

/-!
# Complete arithmetic pairing of the actual BAG Mellin profiles

The original complete arithmetic source, evaluated at the native Mellin
frequencies `2*pi*xi` and divided by `log N`, has a uniform operator bound
on differences of localized profiles in H^(5/4). Common compact log support
supplies the trace estimate along both shrinking arithmetic axes; weighted
Cauchy–Schwarz admits the remaining background term.

For arbitrary Schwartz tests, the same complete source has H² dual norm at
most a constant times `sqrt (1+log N)`. Exact axis dilation retains both
frequency Jacobians. The actual selected Mellin exterior has arbitrary
power energy decay, so its full arithmetic pairing tends to zero uniformly
throughout the moving Mellin parameter square.

These are estimates and exterior cancellation for the literal source.
Signed cancellation against the remaining moving local test is separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ENNReal ContDiff BigOperators
namespace RHTower.BAGTrace
private abbrev E := HTGeometry.QuadrantLogSpace
private def weight (x : E) : ℝ := 1+|x 0|+|x 1|
private theorem weight_pos (x : E) : 0<weight x := by dsimp only [weight]; positivity
private theorem norm_le_weight (x : E) : 1+‖x‖ ≤ weight x := by
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) x
  simp only [Fin.sum_univ_two,Real.norm_eq_abs] at hh
  dsimp only [weight]
  nlinarith [norm_nonneg x,abs_nonneg (x 0),abs_nonneg (x 1),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

private theorem weight_inverse_integrable (p : {r : ℝ // 2<r}) :
    Integrable (fun x : E => weight x^(-p.1)) := by
  have hi : Integrable (fun x : E => (1+‖x‖)^(-p.1)) :=
    integrable_one_add_norm (by simpa only [E,HTGeometry.QuadrantLogSpace,
      finrank_euclideanSpace_fin,Nat.cast_ofNat] using p.2)
  refine hi.mono' ?_ (Eventually.of_forall (fun x => ?_))
  · apply Measurable.aestronglyMeasurable
    dsimp only [weight]
    fun_prop
  · rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (weight_pos x).le _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (norm_le_weight x) (by linarith [p.2])

private def axisWeight (x : ℝ) : ℝ := 1/(1+|x|)^2
private theorem axisWeight_integrable : Integrable axisWeight := by
  have hh := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  convert hh using 1
  funext x
  rw [Real.norm_eq_abs,Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+|x|),Real.rpow_two]
  simp only [axisWeight,one_div]


private theorem weight_ge_one (x : E) : 1 ≤ weight x := by dsimp only [weight]; linarith [abs_nonneg (x 0),abs_nonneg (x 1)]

private theorem weight_rpow_bound (s : {r : ℝ // r∈Icc (0 : ℝ) 2}) (x : E) :
    weight x^(2*s.1) ≤ 81*(1+‖x‖^4) := by
  have hx0 : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have hx1 : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
  let M := max 1 ‖x‖
  have hM1 : 1 ≤ M := le_max_left _ _
  have hxM : ‖x‖ ≤ M := le_max_right _ _
  have hw : weight x ≤ 3*M := by dsimp only [weight]; linarith
  have hM : M^4 ≤ 1+‖x‖^4 := by
    by_cases hx : ‖x‖ ≤ 1
    · rw [show M=1 from max_eq_left hx]
      nlinarith [pow_nonneg (norm_nonneg x) 4]
    · rw [show M=‖x‖ from max_eq_right (le_of_not_ge hx)]
      linarith
  calc weight x^(2*s.1) ≤ weight x^(4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (weight_ge_one x) (by linarith [s.2.2])
    _ = weight x^4 := Real.rpow_ofNat _ _
    _ ≤ (3*M)^4 := pow_le_pow_left₀ (weight_pos x).le hw 4
    _ = 81*M^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (by norm_num)

private theorem weighted_square_integrable (s : {r : ℝ // r∈Icc (0 : ℝ) 2})
    (g : SchwartzMap E ℂ) : Integrable (fun x : E => weight x^(2*s.1)*‖g x‖^2) := by
  obtain ⟨C,hC,hCb⟩ := g.decay 0 0
  have hg (x : E) : ‖g x‖ ≤ C := by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using hCb x
  have hi : Integrable (fun x : E => 81*C*(‖g x‖+‖x‖^4*‖g x‖)) :=
    (g.integrable.norm.add (g.integrable_pow_mul volume 4)).const_mul (81*C)
  refine hi.mono' ?_ (Eventually.of_forall (fun x => ?_))
  · have hg := g.continuous.measurable
    apply Measurable.aestronglyMeasurable
    dsimp only [weight]
    fun_prop
  · rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (weight_pos x).le _) (sq_nonneg _))]
    have hsq : ‖g x‖^2 ≤ C*‖g x‖ := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hg x) (norm_nonneg _)
    calc weight x^(2*s.1)*‖g x‖^2 ≤ (81*(1+‖x‖^4))*(C*‖g x‖) :=
        mul_le_mul (weight_rpow_bound s x) hsq (sq_nonneg _) (by positivity)
      _ = _ := by ring

private def weightedNorm (s : ℝ) (g : SchwartzMap E ℂ) (x : E) : ℝ :=
  weight x^s*‖g x‖

private theorem weightedNorm_square (s : ℝ) (g : SchwartzMap E ℂ) (x : E) :
    (weightedNorm s g x)^2=weight x^(2*s)*‖g x‖^2 := by
  simp only [weightedNorm,mul_pow]
  rw [←Real.rpow_mul_natCast (weight_pos x).le]
  congr 2
  ring

private theorem weightedNorm_memLp (s : {r : ℝ // r∈Icc (0 : ℝ) 2}) (g : SchwartzMap E ℂ) :
    MemLp (weightedNorm s.1 g) 2 := by
  have hm : AEStronglyMeasurable (weightedNorm s.1 g) := by
    have hg := g.continuous.measurable
    apply Measurable.aestronglyMeasurable
    change Measurable (fun x : E => (1+|x 0|+|x 1|)^s.1*‖g x‖)
    fun_prop
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [weightedNorm_square] using weighted_square_integrable s g


private def coords : E≃ᵐℝ×ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).symm.trans MeasurableEquiv.finTwoArrow
private theorem coords_preserving : MeasurePreserving coords :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
private def axisTail (x : ℝ) : ℝ := (1+|x|)^(-(9/8 : ℝ))
private theorem axisTail_integrable : Integrable axisTail := by
  change Integrable (fun x : ℝ => (1+|x|)^(-(9/8 : ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (9/8 : ℝ)) (by norm_num))
private def axisKernel (L x : ℝ) : ℝ := L*axisWeight (L*x)
private theorem axisKernel_integrable (L : {r : ℝ // 0<r}) :
    Integrable (axisKernel L.1) :=
  (axisWeight_integrable.comp_mul_left' L.2.ne').const_mul L.1
private theorem axisKernel_mass (L : {r : ℝ // 0<r}) :
    (∫ x : ℝ, axisKernel L.1 x)=∫ x : ℝ, axisWeight x := by
  simp only [axisKernel,integral_const_mul,Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr L.2),smul_eq_mul]
  field_simp [L.2.ne']
private theorem product_integrable (f g : ℝ→ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x : E => f (x 0)*g (x 1)) := by
  exact coords_preserving.integrable_comp_of_integrable (hf.mul_prod hg)
private theorem product_integral (f g : ℝ→ℝ) :
    (∫ x : E, f (x 0)*g (x 1))=(∫a : ℝ, f a)*(∫b : ℝ, g b) := by
  have hp := coords_preserving.symm coords
  rw [←hp.integral_comp coords.symm.measurableEmbedding (fun x : E => f (x 0)*g (x 1))]
  exact integral_prod_mul f g

private theorem background_bound (g : SchwartzMap E ℂ) :
    Integrable (fun x : E => weight x^(1/8 : ℝ)*‖g x‖) ∧
    (∫x : E, weight x^(1/8 : ℝ)*‖g x‖) ≤
      Real.sqrt (∫x : E, weight x^(5/2 : ℝ)*‖g x‖^2)*
      Real.sqrt (∫x : E, weight x^(-(9/4 : ℝ))) := by
  let s : {r : ℝ // r∈Icc (0 : ℝ) 2} := ⟨5/4,by norm_num⟩
  let a := weightedNorm s.1 g
  let b := fun x : E => weight x^(-(9/8 : ℝ))
  have ha : MemLp a 2 := weightedNorm_memLp s g
  have hb : MemLp b 2 := by
    apply (memLp_two_iff_integrable_sq ?_).2
    · convert weight_inverse_integrable ⟨9/4,by norm_num⟩ using 1
      funext x
      dsimp only [b]
      rw [←Real.rpow_mul_natCast (weight_pos x).le]
      norm_num
    · apply Measurable.aestronglyMeasurable
      dsimp only [b,weight]
      fun_prop
  have he (x : E) : a x*b x=weight x^(1/8 : ℝ)*‖g x‖ := by
    dsimp only [a,b,weightedNorm,s]
    rw [mul_right_comm,←Real.rpow_add (weight_pos x)]
    norm_num
  have hab : Integrable (fun x : E => a x*b x) := ha.integrable_mul hb
  constructor
  · simpa only [he] using hab
  · have hc := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (volume : Measure E)) (p := (2 : ℝ)) (q := (2 : ℝ)) (f := a) (g := b)
      (by rw [Real.holderConjugate_iff]; norm_num)
      (Eventually.of_forall (fun x => mul_nonneg (Real.rpow_nonneg (weight_pos x).le s.1) (norm_nonneg (g x))))
      (Eventually.of_forall (fun x => Real.rpow_nonneg (weight_pos x).le (-(9/8 : ℝ)))) (by simpa using ha) (by simpa using hb)
    simp only [he] at hc
    have hb2 (x : E) : b x^(2 : ℝ)=weight x^(-(9/4 : ℝ)) := by
      dsimp only [b]
      rw [←Real.rpow_mul (weight_pos x).le]
      norm_num
    have ha2 (x : E) : a x^(2 : ℝ)=weight x^(5/2 : ℝ)*‖g x‖^2 := by
      rw [Real.rpow_two]
      change (weightedNorm s.1 g x)^2=_
      rw [weightedNorm_square]
      dsimp only [s]
      norm_num
    simpa only [ha2,hb2,Real.sqrt_eq_rpow] using hc

private def pairAxisMajorant (L : ℝ) (x : E) : ℝ :=
  axisKernel L (x 0)*axisTail (x 1)+axisTail (x 0)*axisKernel L (x 1)
private theorem pairAxisMajorant_integrable (L : {r : ℝ // 0<r}) :
    Integrable (pairAxisMajorant L.1) :=
  (product_integrable _ _ (axisKernel_integrable L) axisTail_integrable).add
    (product_integrable _ _ axisTail_integrable (axisKernel_integrable L))
private theorem pairAxisMajorant_mass (L : {r : ℝ // 0<r}) :
    (∫x : E, pairAxisMajorant L.1 x)=
      2*(∫x : ℝ,axisWeight x)*(∫x : ℝ,axisTail x) := by
  rw [show pairAxisMajorant L.1=(fun x : E => axisKernel L.1 (x 0)*axisTail (x 1))+
    (fun x : E => axisTail (x 0)*axisKernel L.1 (x 1)) from rfl]
  simp only [Pi.add_apply]
  rw [integral_add (product_integrable _ _ (axisKernel_integrable L) axisTail_integrable)
    (product_integrable _ _ axisTail_integrable (axisKernel_integrable L))]
  simp only [product_integral,axisKernel_mass]
  ring
private theorem axisKernel_nonneg (L : {r : ℝ // 0<r}) (x : ℝ) :
    0 ≤ axisKernel L.1 x := by
  dsimp only [axisKernel,axisWeight]
  exact mul_nonneg L.2.le (by positivity)
private theorem weight_axis_le (x : E) (i : Fin 2) : 1+|x i| ≤ weight x := by
  fin_cases i
  · change 1+|x 0| ≤ 1+|x 0|+|x 1|
    linarith [abs_nonneg (x 1)]
  · change 1+|x 1| ≤ 1+|x 0|+|x 1|
    linarith [abs_nonneg (x 0)]
private theorem trace_axis_bound (g : SchwartzMap E ℂ) (D : ℝ) (hD : 0≤D)
    (htrace : ∀x : E, weight x^(5/4 : ℝ)*‖g x‖≤D) (x : E) (i : Fin 2) :
    weight x^(1/8 : ℝ)*‖g x‖ ≤ D*axisTail (x i) := by
  have he : weight x^(1/8 : ℝ)*‖g x‖=
      (weight x^(5/4 : ℝ)*‖g x‖)*weight x^(-(9/8 : ℝ)) := by
    rw [mul_right_comm,←Real.rpow_add (weight_pos x)]
    norm_num
  rw [he]
  apply (mul_le_mul_of_nonneg_right (htrace x)
    (Real.rpow_nonneg (weight_pos x).le _)).trans
  apply mul_le_mul_of_nonneg_left _ hD
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (weight_axis_le x i) (by norm_num)

private def envelope (L : ℝ) (x : E) : ℝ :=
  weight x^(1/8 : ℝ)*(1+axisKernel L (x 0)+axisKernel L (x 1))
private def energyRoot (g : SchwartzMap E ℂ) : ℝ :=
  Real.sqrt (∫x : E,weight x^(5/2 : ℝ)*‖g x‖^2)
private def backgroundMass : ℝ := Real.sqrt (∫x : E,weight x^(-(9/4 : ℝ)))
private def axesMass : ℝ := 2*(∫x : ℝ,axisWeight x)*(∫x : ℝ,axisTail x)

private theorem envelope_pairing_bound (L : {r : ℝ // 0<r})
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (Z : E→ℂ) (g : SchwartzMap E ℂ)
    (hZ : Measurable Z) (hbound : ∀x : E, ‖Z x‖≤C*envelope L.1 x)
    (htrace : ∀x : E, weight x^(5/4 : ℝ)*‖g x‖≤D) :
    Integrable (fun x : E => Z x*g x) ∧
    ‖∫x : E,Z x*g x‖ ≤ C*(energyRoot g*backgroundMass+D*axesMass) := by
  let a := fun x : E => weight x^(1/8 : ℝ)*‖g x‖
  let B := fun x : E => C*(a x+D*pairAxisMajorant L.1 x)
  have hbg := background_bound g
  have hi : Integrable B := (hbg.1.add ((pairAxisMajorant_integrable L).const_mul D)).const_mul C
  have hb (x : E) : ‖Z x*g x‖ ≤ B x := by
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)).trans
    have h0 := mul_le_mul_of_nonneg_left (trace_axis_bound g D hD htrace x 1) (axisKernel_nonneg L (x 0))
    have h1 := mul_le_mul_of_nonneg_left (trace_axis_bound g D hD htrace x 0) (axisKernel_nonneg L (x 1))
    change axisKernel L.1 (x 0)*a x ≤ _ at h0
    change axisKernel L.1 (x 1)*a x ≤ _ at h1
    change C*envelope L.1 x*‖g x‖ ≤ C*(a x+D*pairAxisMajorant L.1 x)
    calc
      C*envelope L.1 x*‖g x‖=C*(a x+axisKernel L.1 (x 0)*a x+axisKernel L.1 (x 1)*a x) := by
        dsimp only [envelope,a]; ring
      _ ≤ C*(a x+axisKernel L.1 (x 0)*(D*axisTail (x 1))+axisKernel L.1 (x 1)*(D*axisTail (x 0))) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right h0 _) h1) hC
      _ = _ := by dsimp only [pairAxisMajorant]; ring
  constructor
  · exact hi.mono' ((hZ.mul g.continuous.measurable).aestronglyMeasurable) (Eventually.of_forall hb)
  · apply (norm_integral_le_of_norm_le hi (Eventually.of_forall hb)).trans
    change (∫x : E,C*(a x+D*pairAxisMajorant L.1 x)) ≤ _
    rw [integral_const_mul,integral_add hbg.1 ((pairAxisMajorant_integrable L).const_mul D),
      integral_const_mul,pairAxisMajorant_mass L]
    exact mul_le_mul_of_nonneg_left (add_le_add_left hbg.2 (D*axesMass)) hC

private def line (ρ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  1+((ρ/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I

private theorem line_re (ρ : ℝ) (N : ℕ) (t : ℝ) : (line ρ N t).re=1+ρ/Real.log N := by
  simp only [line,Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]

private theorem line_measurable (ρ : ℝ) (N : ℕ) : Measurable (line ρ N) := by
  unfold line
  fun_prop

private theorem base_measurable (p : Nat.Primes) : Measurable (cubicPrimeBase p) := by
  unfold cubicPrimeBase
  fun_prop

private theorem weighted_measurable (P : Finset Nat.Primes) :
    Measurable (fun w : ℂ × ℂ => criticalWeightedConeEuler P w.1 w.2) := by
  classical
  unfold criticalWeightedConeEuler criticalWeightedLabelEuler
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro p _
  apply Finset.measurable_sum
  intro q _
  by_cases h : p=r ∨ q=r
  · simp only [if_pos h]; fun_prop
  · simp only [if_neg h]
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro ℓ _
    have hx : Measurable (fun w : ℂ × ℂ => cubicPrimeBase ℓ w.1) :=
      (base_measurable ℓ).comp measurable_fst
    have hy : Measurable (fun w : ℂ × ℂ => cubicPrimeBase ℓ w.2) :=
      (base_measurable ℓ).comp measurable_snd
    unfold weightedConeEuler
    split_ifs <;>
      simp only [weightedConeEulerMinusTwo,weightedConeEulerMinusOne,weightedEuler] <;>
      fun_prop

private theorem cofactor_line_measurable (P : Finset Nat.Primes)
    (ρ : {r : ℝ // 0<r}) {N : ℕ} (hN : 2≤N) :
    Measurable (fun t => criticalCofactor P (line ρ N t)) := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have he (t : ℝ) : criticalCofactor P (line ρ N t)=
      ∑' n : ℕ,criticalCofactorTerm P (line ρ N t) n := by
    apply (criticalCofactor_hasSum P _).tsum_eq.symm
    rw [line_re]
    exact lt_add_of_pos_right _ (div_pos ρ.property hL)
  simp_rw [he]
  apply Measurable.tsum
  intro n
  simp_rw [criticalCofactorTerm_eq]
  split_ifs with hn
  · fun_prop
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (not_or.mp hn).1
    unfold line
    fun_prop

private def source (ρ₁ ρ₂ : {r : ℝ // 0<r}) (N : ℕ) (w : ℝ × ℝ) : ℂ :=
  criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (line ρ₁ N w.1) (line ρ₂ N w.2)

private theorem source_measurable (ρ₁ ρ₂ : {r : ℝ // 0<r})
    {N : ℕ} (hN : 2≤N) : Measurable (source ρ₁ ρ₂ N) := by
  unfold source criticalCompletedConeEuler
  exact ((weighted_measurable _).comp
    (((line_measurable ρ₁ N).comp measurable_fst).prodMk
      ((line_measurable ρ₂ N).comp measurable_snd))).mul
    (((cofactor_line_measurable _ ρ₁ hN).comp measurable_fst).mul
      ((cofactor_line_measurable _ ρ₂ hN).comp measurable_snd))


/-- Complete growing arithmetic source on the native Fourier-normalized Mellin
lines, including both cofactors, with the critical logarithmic normalization. -/
def bagMellinNormalizedArithmeticSource (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (N : ℕ) (x : E) : ℂ :=
  criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (1+(((ρ₁ : ℝ)/Real.log N : ℝ) : ℂ)+((2*Real.pi*x 0 : ℝ) : ℂ)*Complex.I)
    (1+(((ρ₂ : ℝ)/Real.log N : ℝ) : ℂ)+((2*Real.pi*x 1 : ℝ) : ℂ)*Complex.I)/
      (Real.log N : ℂ)

private theorem normalized_source_measurable (ρ₁ ρ₂ : {r : ℝ // 0<r})
    {N : ℕ} (hN : 2≤N) : Measurable (bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N) := by
  have hm : Measurable (fun x : E => (2*Real.pi*x 0,2*Real.pi*x 1)) := by fun_prop
  exact ((source_measurable ρ₁ ρ₂ hN).comp hm).div_const _

private theorem normalized_source_envelope (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, 1≤Real.log N ∧ 2≤N ∧
      ∀x : E, ‖bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N x‖ ≤
        C*envelope (Real.log N) x := by
  obtain ⟨C,hC,hb⟩ := criticalCompletedConeEuler_uniform_saturated_axes_bound ρ₁ ρ₂ ⟨1/8,by norm_num⟩
  let κ : ℝ := 2*Real.pi
  have hκ : 1≤κ := by dsimp only [κ]; linarith [Real.pi_gt_three]
  have hκp : 0<κ := by linarith
  refine ⟨C*κ^(1/8 : ℝ),mul_pos hC (Real.rpow_pos_of_pos hκp _),?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, 1≤Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hb,hlog,eventually_ge_atTop 2] with N hb hlog hN
  refine ⟨hlog,hN,?_⟩
  intro x
  let L : ℝ := Real.log N
  have hL : 0<L := by dsimp only [L]; linarith
  have hnorm : ‖(Real.log N : ℂ)‖=L := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have ht : 1+|κ*x 0|+|κ*x 1|≤κ*weight x := by
    rw [abs_mul κ (x 0),abs_mul κ (x 1),abs_of_pos hκp]
    dsimp only [weight]
    nlinarith
  have hp : (1+|κ*x 0|+|κ*x 1|)^(1/8 : ℝ)≤κ^(1/8 : ℝ)*weight x^(1/8 : ℝ) := by
    rw [←Real.mul_rpow hκp.le (weight_pos x).le]
    exact Real.rpow_le_rpow (by positivity) ht (by norm_num)
  have hax (t : ℝ) : L^2/(1+L*|κ*t|)^2 ≤ L*axisKernel L t := by
    have ht : |t|≤|κ*t| := by rw [abs_mul,abs_of_pos hκp]; nlinarith [abs_nonneg t]
    have hd : (1+L*|t|)^2≤(1+L*|κ*t|)^2 := by gcongr
    calc
      L^2/(1+L*|κ*t|)^2 ≤ L^2/(1+L*|t|)^2 :=
        div_le_div_of_nonneg_left (sq_nonneg L) (by positivity) hd
      _ = L*axisKernel L t := by
        dsimp only [axisKernel,axisWeight]
        rw [abs_mul,abs_of_pos hL]
        ring
  have haxes : (1+L^2/(1+L*|κ*x 0|)^2+L^2/(1+L*|κ*x 1|)^2)/L ≤
      1+axisKernel L (x 0)+axisKernel L (x 1) := by
    apply (div_le_iff₀ hL).2
    have h0 := hax (x 0)
    have h1 := hax (x 1)
    change 1≤L at hlog
    nlinarith
  change ‖criticalCompletedConeEuler _ _ _/(Real.log N : ℂ)‖ ≤ _
  rw [norm_div,hnorm]
  have hs := div_le_div_of_nonneg_right (hb (κ*x 0) (κ*x 1)) hL.le
  apply hs.trans
  change C*(1+|κ*x 0|+|κ*x 1|)^(1/8 : ℝ)*
    (1+L^2/(1+L*|κ*x 0|)^2+L^2/(1+L*|κ*x 1|)^2)/L ≤ _
  calc
    _ = C*(1+|κ*x 0|+|κ*x 1|)^(1/8 : ℝ)*
      ((1+L^2/(1+L*|κ*x 0|)^2+L^2/(1+L*|κ*x 1|)^2)/L) := by ring
    _ ≤ (C*(κ^(1/8 : ℝ)*weight x^(1/8 : ℝ)))*
      (1+axisKernel L (x 0)+axisKernel L (x 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) haxes (by positivity)
          (mul_nonneg hC.le (mul_nonneg (Real.rpow_nonneg hκp.le _) (Real.rpow_nonneg (weight_pos x).le _)))
    _ = _ := by dsimp only [envelope,L]; ring


/-- Uniform complete arithmetic pairing on every exact difference of localized
Mellin profiles. Both moving-line parameters may vary. The source is evaluated
at the native frequencies `2*pi*xi`, with both growing cofactors retained;
all integrability and trace control are derived, not assumed. -/
theorem bagLocalizedMellin_difference_arithmetic_pairing_bound
    (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀q r : {q : E // ∀i, q i∈Icc (1 : ℝ) 2}, ∀f g : SchwartzMap E ℂ,
        let h := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
          GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz r g
        Integrable (fun ξ : E => bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 h) ξ) ∧
        ‖∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*(𝓕 h) ξ‖ ≤
          C*Real.sqrt (∫ξ : E,(1+|ξ 0|+|ξ 1|)^(5/2 : ℝ)*‖(𝓕 h) ξ‖^2) := by
  obtain ⟨S,hS,hsource⟩ := normalized_source_envelope ρ₁ ρ₂
  obtain ⟨T,hT,htrace⟩ := bagLocalizedMellin_difference_weighted_trace ⟨5/4,by norm_num⟩
  have hB : 0≤backgroundMass := Real.sqrt_nonneg _
  have hA : 0≤axesMass := by
    unfold axesMass
    have h1 : 0≤∫x : ℝ,axisWeight x := integral_nonneg (fun x => by dsimp only [axisWeight]; positivity)
    have h2 : 0≤∫x : ℝ,axisTail x := integral_nonneg (fun x => by dsimp only [axisTail]; positivity)
    positivity
  refine ⟨S*(backgroundMass+T*axesMass)+1,by positivity,?_⟩
  filter_upwards [hsource] with N hN
  intro q r f g
  let h := GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz q f-
    GaloisForLFunctions.HTGeometry.compactLocalizedMellinSchwartz r g
  let G := 𝓕 h
  have hE : 0≤energyRoot G := Real.sqrt_nonneg _
  have ht (x : E) : weight x^(5/4 : ℝ)*‖G x‖≤T*energyRoot G := by
    have hh := htrace q r f g x
    convert hh using 1 <;> norm_num [energyRoot,weight,G,h]
  have hh := envelope_pairing_bound ⟨Real.log N,by linarith [hN.1]⟩
    S (T*energyRoot G) hS.le (mul_nonneg hT.le hE)
    (bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N) G
    (normalized_source_measurable ρ₁ ρ₂ hN.2.1) hN.2.2 ht
  refine ⟨hh.1,hh.2.trans ?_⟩
  change S*(energyRoot G*backgroundMass+(T*energyRoot G)*axesMass) ≤
    (S*(backgroundMass+T*axesMass)+1)*energyRoot G
  nlinarith

private theorem axisKernel_le (L : {r : ℝ // 0<r}) (t : ℝ) :
    axisKernel L.1 t ≤ L.1 := by
  have h : axisWeight (L.1*t) ≤ 1 := by
    unfold axisWeight
    apply (div_le_iff₀ (by positivity : 0<(1+|L.1*t|)^2)).2
    nlinarith [abs_nonneg (L.1*t)]
  simpa only [axisKernel,mul_one] using mul_le_mul_of_nonneg_left h L.2.le

private def dualMajorant (L : ℝ) (x : E) : ℝ :=
  3*(weight x^(-(15/4 : ℝ))+L*pairAxisMajorant L x)
private theorem dualMajorant_integrable (L : {r : ℝ // 0<r}) :
    Integrable (dualMajorant L.1) :=
  ((weight_inverse_integrable ⟨15/4,by norm_num⟩).add
    ((pairAxisMajorant_integrable L).const_mul L.1)).const_mul 3
private theorem dualMajorant_mass (L : {r : ℝ // 0<r}) :
    (∫x : E,dualMajorant L.1 x)=
      3*((∫x : E,weight x^(-(15/4 : ℝ)))+L.1*axesMass) := by
  change (∫x : E,3*(weight x^(-(15/4 : ℝ))+L.1*pairAxisMajorant L.1 x))=_
  rw [integral_const_mul,integral_add (weight_inverse_integrable ⟨15/4,by norm_num⟩)
    ((pairAxisMajorant_integrable L).const_mul L.1),integral_const_mul,pairAxisMajorant_mass L]
  rfl

private theorem dual_axis_bound (x : E) (i : Fin 2) :
    weight x^(-(15/4 : ℝ))≤axisTail (x i) := by
  calc
    weight x^(-(15/4 : ℝ))≤weight x^(-(9/8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (weight_ge_one x) (by norm_num)
    _ ≤ axisTail (x i) := Real.rpow_le_rpow_of_nonpos (by positivity) (weight_axis_le x i) (by norm_num)

private theorem envelope_dual_square (L : {r : ℝ // 0<r}) (x : E) :
    (weight x^(-(2 : ℝ))*envelope L.1 x)^2 ≤ dualMajorant L.1 x := by
  let a := axisKernel L.1 (x 0)
  let b := axisKernel L.1 (x 1)
  let W := weight x^(-(15/4 : ℝ))
  have ha : 0≤a := axisKernel_nonneg L (x 0)
  have hb : 0≤b := axisKernel_nonneg L (x 1)
  have hW : 0≤W := Real.rpow_nonneg (weight_pos x).le _
  have haL : a^2≤L.1*a := by nlinarith [axisKernel_le L (x 0)]
  have hbL : b^2≤L.1*b := by nlinarith [axisKernel_le L (x 1)]
  have hsum : (1+a+b)^2≤3*(1+a^2+b^2) := by
    nlinarith [sq_nonneg (1-a),sq_nonneg (1-b),sq_nonneg (a-b)]
  have haa : W*a^2≤L.1*a*axisTail (x 1) := by
    apply (mul_le_mul_of_nonneg_left haL hW).trans
    calc
      W*(L.1*a)=(L.1*a)*W := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (dual_axis_bound x 1) (mul_nonneg L.2.le ha)
  have hbb : W*b^2≤L.1*b*axisTail (x 0) := by
    apply (mul_le_mul_of_nonneg_left hbL hW).trans
    calc
      W*(L.1*b)=(L.1*b)*W := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (dual_axis_bound x 0) (mul_nonneg L.2.le hb)
  have he : (weight x^(-(2 : ℝ))*envelope L.1 x)^2=W*(1+a+b)^2 := by
    dsimp only [envelope,a,b,W]
    rw [←mul_assoc,←Real.rpow_add (weight_pos x),mul_pow,
      ←Real.rpow_mul_natCast (weight_pos x).le]
    norm_num
  rw [he]
  apply (mul_le_mul_of_nonneg_left hsum hW).trans
  change W*(3*(1+a^2+b^2))≤3*(W+L.1*(a*axisTail (x 1)+axisTail (x 0)*b))
  nlinarith

private def dualNorm (Z : E→ℂ) (x : E) : ℝ := weight x^(-(2 : ℝ))*‖Z x‖
private theorem envelope_dual_bound (L : {r : ℝ // 0<r}) (C : ℝ)
    (Z : E→ℂ) (hZ : Measurable Z) (hbound : ∀x : E,‖Z x‖≤C*envelope L.1 x) :
    MemLp (dualNorm Z) 2 ∧
    (∫x : E,(dualNorm Z x)^2)≤C^2*(∫x : E,dualMajorant L.1 x) := by
  have hm : Measurable (dualNorm Z) := by
    change Measurable (fun x : E => (1+|x 0|+|x 1|)^(-(2 : ℝ))*‖Z x‖)
    fun_prop
  have hi : Integrable (fun x : E => C^2*dualMajorant L.1 x) :=
    (dualMajorant_integrable L).const_mul (C^2)
  have hb (x : E) : (dualNorm Z x)^2≤C^2*dualMajorant L.1 x := by
    have hh := mul_le_mul_of_nonneg_left (hbound x) (Real.rpow_nonneg (weight_pos x).le (-(2 : ℝ)))
    have hn : 0≤dualNorm Z x := mul_nonneg (Real.rpow_nonneg (weight_pos x).le _) (norm_nonneg _)
    have he : weight x^(-(2 : ℝ))*(C*envelope L.1 x)=C*(weight x^(-(2 : ℝ))*envelope L.1 x) := by ring
    rw [he] at hh
    have hh2 := pow_le_pow_left₀ hn hh 2
    rw [mul_pow] at hh2
    exact hh2.trans (mul_le_mul_of_nonneg_left (envelope_dual_square L x) (sq_nonneg C))
  have hs : Integrable (fun x : E => (dualNorm Z x)^2) := hi.mono'
    (hm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (dualNorm Z x))] using hb x))
  refine ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hs,?_⟩
  have hh := integral_mono hs hi hb
  simpa only [integral_const_mul] using hh

private theorem dual_pairing_bound (Z : E→ℂ) (hZ : Measurable Z)
    (hd : MemLp (dualNorm Z) 2) (g : SchwartzMap E ℂ) :
    Integrable (fun x : E => Z x*g x) ∧
    ‖∫x : E,Z x*g x‖≤Real.sqrt (∫x : E,(dualNorm Z x)^2)*
      Real.sqrt (∫x : E,weight x^(4 : ℝ)*‖g x‖^2) := by
  let a := dualNorm Z
  let b := weightedNorm 2 g
  have hb : MemLp b 2 := weightedNorm_memLp ⟨2,by norm_num⟩ g
  have ha0 (x : E) : 0≤a x := mul_nonneg (Real.rpow_nonneg (weight_pos x).le _) (norm_nonneg _)
  have hb0 (x : E) : 0≤b x := mul_nonneg (Real.rpow_nonneg (weight_pos x).le _) (norm_nonneg _)
  have he (x : E) : a x*b x=‖Z x*g x‖ := by
    dsimp only [a,b,dualNorm,weightedNorm]
    rw [norm_mul]
    calc
      _ = (weight x^(-(2 : ℝ))*weight x^(2 : ℝ))*(‖Z x‖*‖g x‖) := by ring
      _ = _ := by rw [←Real.rpow_add (weight_pos x)]; norm_num
  have hi : Integrable (fun x : E => a x*b x) := hd.integrable_mul hb
  refine ⟨hi.mono' (hZ.mul g.continuous.measurable).aestronglyMeasurable
    (Eventually.of_forall (fun x => (he x).symm.le)),?_⟩
  apply (norm_integral_le_of_norm_le hi (Eventually.of_forall (fun x => (he x).symm.le))).trans
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure E)) (p := (2 : ℝ)) (q := (2 : ℝ)) (f := a) (g := b)
    (by rw [Real.holderConjugate_iff]; norm_num)
    (Eventually.of_forall ha0) (Eventually.of_forall hb0)
    (by simpa only [ENNReal.ofReal_ofNat] using hd) (by simpa only [ENNReal.ofReal_ofNat] using hb)
  have hb2 (x : E) : b x^(2 : ℝ)=weight x^(4 : ℝ)*‖g x‖^2 := by
    rw [Real.rpow_two]
    change (weightedNorm 2 g x)^2=_
    rw [weightedNorm_square]
    norm_num
  simpa only [hb2,Real.rpow_two,Real.sqrt_eq_rpow] using hc


/-- The complete normalized arithmetic source acts continuously on full H²
frequency tests with at most square-root logarithmic cost. No support or trace
hypothesis is imposed on the Schwartz input. -/
theorem bagMellinNormalizedArithmeticSource_H2_pairing_bound
    (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀g : SchwartzMap E ℂ,
      Integrable (fun ξ : E => bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*g ξ) ∧
      ‖∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*g ξ‖ ≤
        C*Real.sqrt (1+Real.log N)*
          Real.sqrt (∫ξ : E,(1+|ξ 0|+|ξ 1|)^(4 : ℝ)*‖g ξ‖^2) := by
  obtain ⟨S,hS,hsource⟩ := normalized_source_envelope ρ₁ ρ₂
  let B : ℝ := ∫x : E,weight x^(-(15/4 : ℝ))
  have hB : 0≤B := integral_nonneg (fun x => Real.rpow_nonneg (weight_pos x).le _)
  have hA : 0≤axesMass := by
    unfold axesMass
    have h1 : 0≤∫x : ℝ,axisWeight x := integral_nonneg (fun x => by dsimp only [axisWeight]; positivity)
    have h2 : 0≤∫x : ℝ,axisTail x := integral_nonneg (fun x => by dsimp only [axisTail]; positivity)
    positivity
  let D : ℝ := 3*S^2*(B+axesMass+1)
  have hD : 0≤D := by dsimp only [D]; positivity
  refine ⟨Real.sqrt D+1,by positivity,?_⟩
  filter_upwards [hsource] with N hN
  intro g
  let L : {r : ℝ // 0<r} := ⟨Real.log N,by linarith [hN.1]⟩
  let Z := bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N
  have hm : Measurable Z := normalized_source_measurable ρ₁ ρ₂ hN.2.1
  have hd := envelope_dual_bound L S Z hm hN.2.2
  have hp := dual_pairing_bound Z hm hd.1 g
  refine ⟨hp.1,hp.2.trans ?_⟩
  have hmass : (∫x : E,(dualNorm Z x)^2)≤D*(1+Real.log N) := by
    apply hd.2.trans
    rw [dualMajorant_mass L]
    have he : B+L.1*axesMass ≤ (B+axesMass+1)*(1+L.1) := by
      nlinarith [L.2,mul_nonneg hB L.2.le]
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0≤3*S^2)
    dsimp only [D,L,B] at hh ⊢
    nlinarith only [hh]
  have hs : Real.sqrt (∫x : E,(dualNorm Z x)^2)≤(Real.sqrt D+1)*Real.sqrt (1+Real.log N) := by
    apply (Real.sqrt_le_sqrt hmass).trans
    rw [Real.sqrt_mul hD]
    exact mul_le_mul_of_nonneg_right (by linarith : Real.sqrt D≤Real.sqrt D+1) (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)

/-- The literal selected physical exterior has an admitted full arithmetic
pairing and a uniform vanishing bound over every moving Mellin parameter. -/
theorem bagCubicSelectedExteriorMellin_arithmetic_pairing_decay
    (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀q : {q : E // ∀i, q i∈Icc (1 : ℝ) 2},
        Integrable (fun ξ : E => bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
          (𝓕 (bagCubicSelectedExteriorMellin q N)) ξ) ∧
        ‖∫ξ : E,bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
          (𝓕 (bagCubicSelectedExteriorMellin q N)) ξ‖ ≤ C/(N : ℝ) := by
  obtain ⟨A,hA,hAb⟩ := bagMellinNormalizedArithmeticSource_H2_pairing_bound ρ₁ ρ₂
  obtain ⟨B,hB,hBb⟩ := bagCubicSelectedExteriorMellin_energy_decay 2
  refine ⟨A*Real.sqrt B,mul_pos hA (Real.sqrt_pos.2 hB),?_⟩
  filter_upwards [hAb,(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hBb,
    eventually_ge_atTop 2] with N hArow hBrow hN
  intro q
  let G := 𝓕 (bagCubicSelectedExteriorMellin q N)
  have hn : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hnpos : (0 : ℝ)<N := by linarith
  have henergy : (∫ξ : E,weight ξ^(4 : ℝ)*‖G ξ‖^2)≤B/(N : ℝ)^4 := by
    have hi : Integrable (fun ξ : E => weight ξ^(4 : ℝ)*‖G ξ‖^2) := by
      convert weighted_square_integrable ⟨2,by norm_num⟩ G using 1
      norm_num
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun ξ => mul_nonneg (Real.rpow_nonneg (weight_pos ξ).le _) (sq_nonneg _)))
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤B/(N : ℝ)^4)).mp
    rw [he]
    simpa only [weight,Nat.reduceMul] using hBrow q
  have hs : Real.sqrt (∫ξ : E,weight ξ^(4 : ℝ)*‖G ξ‖^2)≤Real.sqrt B/(N : ℝ)^2 := by
    apply (Real.sqrt_le_sqrt henergy).trans_eq
    rw [Real.sqrt_div hB.le,show (N : ℝ)^4=((N : ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hlog : Real.sqrt (1+Real.log N)≤(N : ℝ) := by
    apply Real.sqrt_le_iff.2
    exact ⟨hnpos.le,by nlinarith [Real.log_le_sub_one_of_pos hnpos]⟩
  refine ⟨(hArow G).1,((hArow G).2).trans ?_⟩
  change A*Real.sqrt (1+Real.log N)*Real.sqrt (∫ξ : E,weight ξ^(4 : ℝ)*‖G ξ‖^2) ≤ _
  calc
    _ ≤ (A*(N : ℝ))*(Real.sqrt B/(N : ℝ)^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog hA.le) hs (Real.sqrt_nonneg _) (mul_nonneg hA.le hnpos.le)
    _ = _ := by field_simp


/-- Vanishing of the complete arithmetic exterior pairing for every choice of
moving Mellin parameters in the admitted square. -/
theorem bagCubicSelectedExteriorMellin_arithmetic_pairing_tendsto
    (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (q : ℕ→{q : E // ∀i, q i∈Icc (1 : ℝ) 2}) :
    Tendsto (fun N : ℕ => ∫ξ : E,
      bagMellinNormalizedArithmeticSource ρ₁ ρ₂ N ξ*
        (𝓕 (bagCubicSelectedExteriorMellin (q N) N)) ξ) atTop (𝓝 0) := by
  obtain ⟨C,_hC,hb⟩ := bagCubicSelectedExteriorMellin_arithmetic_pairing_decay ρ₁ ρ₂
  exact squeeze_zero_norm' (hb.mono (fun N hN => (hN (q N)).2))
    (tendsto_const_div_atTop_nhds_zero_nat C)

end RHTower.BAGTrace