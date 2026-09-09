import GaloisForLFunctions.RHTower.SelbergThetaDilationRows
import GaloisForLFunctions.RHTower.SelbergThetaTotientHankel
/-!
# The full native theta Gram kernel

For the actual modular dilation source `Q(L)`, the native inner product is exactly
`K(M-L) + H(L+M)`. Here `K` is the literal autocorrelation and `H` contains every
totient-weighted reflected row. Exponential substitution, row rescaling, Fubini, and the
infinite denominator interchange are justified by absolute theta envelopes. The result is
identified with the actual native Hilbert vectors and their squared norms.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergThetaDilationGram
open SelbergThetaDilationTransform SelbergThetaDilationRows D4BMGlobalAngularResponse
noncomputable section

private theorem profile_continuous (rho : ℂ) : Continuous (profile rho) := by
  have ht := contDiff_thetaCuspFullSource.continuous
  unfold profile baseProfile
  fun_prop

private theorem integral_exp_substitution (f : ℝ → ℂ) :
    (∫ y in Ioi (0:ℝ), f y) = ∫ t : ℝ, Real.exp t • f (Real.exp t) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := univ) MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn f
  simpa only [image_univ, Real.range_exp, setIntegral_univ, abs_of_pos (Real.exp_pos _)] using h

private theorem integrable_exp_substitution (f : ℝ → ℂ) :
    IntegrableOn f (Ioi (0:ℝ)) ↔ Integrable (fun t => Real.exp t • f (Real.exp t)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := univ) MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn f
  simpa only [image_univ, Real.range_exp, integrableOn_univ, abs_of_pos (Real.exp_pos _)] using h

private def rowShift (c : ℕ+) (x : ℝ) : ℝ :=
  2*Real.log (c:ℕ)+Real.log (1+x^2)

private def logRow (rho : ℂ) (L M : ℝ) (c : ℕ+) (t x : ℝ) : ℂ :=
  (Real.exp (-rowShift c x/2):ℂ)*conj (profile rho (t+L))*
    profile rho (M-t-rowShift c x)

private def tiltedNorm (rho : ℂ) (L t : ℝ) : ℝ :=
  ‖profile rho (t+L)‖*Real.exp (-(3/2:ℝ)*(t+L))

private theorem tiltedNorm_integrable (rho : ℂ) (L : ℝ) :
    Integrable (tiltedNorm rho L) := by
  have h := ((profile_integrable rho (I*(-(3/2:ℂ)))).norm).comp_add_right L
  have he (t : ℝ) : ‖fourierIntegrand (profile rho) (I*(-(3/2:ℂ))) (t+L)‖ =
      tiltedNorm rho L t := by
    unfold fourierIntegrand tiltedNorm
    rw [norm_mul, Complex.norm_exp]
    have hr : (-I*(I*(-(3/2:ℂ)))*((t+L:ℝ):ℂ)).re = -(3/2:ℝ)*(t+L) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hr,mul_comm]
  exact h.congr (ae_of_all _ he)

private def unitMajorant (x : ℝ) : ℝ := (1+x^2)^(-(2:ℝ))

private theorem unitMajorant_integrable : Integrable unitMajorant := by
  have h := (integrable_d4BMCauchyPowerKernel ⟨0,1,by norm_num⟩ ⟨2,by norm_num⟩).norm
  change Integrable (fun x : ℝ => (1+x^2)^(-(2:ℝ)))
  simpa [norm_d4BMCauchyPowerKernel] using h

private theorem logRow_bound (rho : ℂ) (L M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ+) (t x : ℝ),
      ‖logRow rho L M c t x‖ ≤
        (C*((c:ℕ):ℝ)^(-(4:ℝ)))*(tiltedNorm rho L t*unitMajorant x) := by
  obtain ⟨C,hC,hb⟩ := profile_exp_bound rho (3/2)
  refine ⟨C*Real.exp ((3/2:ℝ)*(M+L)),by positivity,fun c t x => ?_⟩
  have hc : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hx : 0 < 1+x^2 := by positivity
  rw [logRow,norm_mul,norm_mul,norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-rowShift c x/2)*‖profile rho (t+L)‖*
        (C*Real.exp ((3/2:ℝ)*(M-t-rowShift c x))) := by gcongr; exact hb _
    _ = _ := by
      unfold tiltedNorm unitMajorant rowShift
      rw [Real.rpow_def_of_pos hc,Real.rpow_def_of_pos hx]
      have he : -(2*Real.log (c:ℕ)+Real.log (1+x^2))/2+
          (3/2:ℝ)*(M-t-(2*Real.log (c:ℕ)+Real.log (1+x^2))) =
          (3/2:ℝ)*(M+L)+Real.log (c:ℕ)*(-4)+
            (-(3/2:ℝ)*(t+L)+Real.log (1+x^2)*(-2)) := by ring
      calc
        _ = C*‖profile rho (t+L)‖*(Real.exp (-(2*Real.log (c:ℕ)+Real.log (1+x^2))/2)*
          Real.exp ((3/2:ℝ)*(M-t-(2*Real.log (c:ℕ)+Real.log (1+x^2))))) := by ring
        _ = _ := by rw [← Real.exp_add,he]; simp only [Real.exp_add]; ring

private theorem logRow_measurable (rho : ℂ) (L M : ℝ) (c : ℕ+) :
    Measurable (Function.uncurry (logRow rho L M c)) := by
  have hp := (profile_continuous rho).measurable
  unfold Function.uncurry logRow rowShift
  fun_prop

private theorem logRow_integrable (rho : ℂ) (L M : ℝ) (c : ℕ+) :
    Integrable (Function.uncurry (logRow rho L M c)) (volume.prod volume) := by
  obtain ⟨C,_,hb⟩ := logRow_bound rho L M
  exact (((tiltedNorm_integrable rho L).mul_prod unitMajorant_integrable).const_mul
    (C*((c:ℕ):ℝ)^(-(4:ℝ)))).mono'
      (logRow_measurable rho L M c).aestronglyMeasurable (ae_of_all _ (fun p => hb c p.1 p.2))

private theorem logRow_integral (rho : ℂ) (L M : ℝ) (c : ℕ+) :
    ((c:ℕ).totient:ℂ)*(∫ t, ∫ x, logRow rho L M c t x) =
      SelbergThetaTotientHankel.row rho c (L+M) := by
  rw [integral_integral_swap (logRow_integrable rho L M c)]
  unfold SelbergThetaTotientHankel.row
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  unfold logRow
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have he : (∫ t, conj (profile rho (t+L))*profile rho (M-t-rowShift c x)) =
      hankelCorrelation rho (L+M-rowShift c x) := by
    unfold hankelCorrelation
    have ht := (measurePreserving_add_right volume L).integral_comp
      (MeasurableEquiv.addRight L).measurableEmbedding
        (fun u => conj (profile rho u)*profile rho (L+M-rowShift c x-u))
    convert ht using 1
    congr 1
    funext t
    congr 2
    ring
  rw [he]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rfl


private theorem exp_rowShift (c : ℕ+) (x : ℝ) :
    Real.exp (rowShift c x) = ((c:ℕ):ℝ)^2*(1+x^2) := by
  have hc : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  unfold rowShift
  rw [show 2*Real.log (c:ℕ) = Real.log (c:ℕ)+Real.log (c:ℕ) by ring,
    Real.exp_add,Real.exp_add,Real.exp_log hc,Real.exp_log (by positivity : 0 < 1+x^2)]
  ring

private theorem scaled_height (c : ℕ+) (t x : ℝ) :
    Real.exp t / (((c:ℕ):ℝ)^2*((Real.exp t)^2+(Real.exp t*x)^2)) =
      Real.exp (-t-rowShift c x) := by
  rw [sub_eq_add_neg,Real.exp_add,Real.exp_neg,Real.exp_neg,exp_rowShift]
  have ht := Real.exp_pos t
  have hc : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hx : 0 < 1+x^2 := by positivity
  field_simp

private theorem logRow_height (rho : ℂ) (L M : ℝ) (c : ℕ+) (t x : ℝ) :
    logRow rho L M c t x = conj (heightProfile rho L (Real.exp t))*
      archProfile rho M (Real.exp t) c (Real.exp t*x) := by
  unfold archProfile
  rw [scaled_height]
  unfold heightProfile
  rw [Real.log_exp,Real.log_exp]
  rw [map_mul, Complex.conj_ofReal]
  have he : -t-rowShift c x+M = M-t-rowShift c x := by ring
  rw [he]
  unfold logRow
  have hf : (Real.exp (t/2):ℂ)*(Real.exp ((-t-rowShift c x)/2):ℂ) =
      (Real.exp (-rowShift c x/2):ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  calc
    _ = ((Real.exp (t/2):ℂ)*(Real.exp ((-t-rowShift c x)/2):ℂ))*
        conj (profile rho (t+L))*profile rho (M-t-rowShift c x) := by rw [hf]
    _ = _ := by ring

private def rowDensity (rho : ℂ) (L M : ℝ) (c : ℕ+) (y : ℝ) : ℂ :=
  ((y^2)⁻¹:ℝ) • (conj (heightProfile rho L y) * ∫ x, archProfile rho M y c x)

private theorem rowDensity_exp (rho : ℂ) (L M : ℝ) (c : ℕ+) (t : ℝ) :
    Real.exp t • rowDensity rho L M c (Real.exp t) =
      ∫ x, logRow rho L M c t x := by
  simp_rw [logRow_height]
  rw [integral_const_mul,Measure.integral_comp_mul_left]
  unfold rowDensity
  rw [abs_of_pos (inv_pos.mpr (Real.exp_pos t))]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  field_simp

private theorem rowDensity_integrable (rho : ℂ) (L M : ℝ) (c : ℕ+) :
    IntegrableOn (rowDensity rho L M c) (Ioi (0:ℝ)) := by
  rw [integrable_exp_substitution]
  simpa only [rowDensity_exp, Function.uncurry] using! (logRow_integrable rho L M c).integral_prod_left

private theorem rowDensity_integral (rho : ℂ) (L M : ℝ) (c : ℕ+) :
    ((c:ℕ).totient:ℂ)*(∫ y in Ioi (0:ℝ), rowDensity rho L M c y) =
      SelbergThetaTotientHankel.row rho c (L+M) := by
  rw [integral_exp_substitution]
  simp_rw [rowDensity_exp]
  exact logRow_integral rho L M c


private theorem rowDensity_norm_bound (rho : ℂ) (L M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℕ+,
      (∫ y in Ioi (0:ℝ), ‖rowDensity rho L M c y‖) ≤ C*((c:ℕ):ℝ)^(-(4:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := logRow_bound rho L M
  let A := ∫ t, tiltedNorm rho L t
  let B := ∫ x, unitMajorant x
  have hA : 0 ≤ A := integral_nonneg (fun _ => by unfold tiltedNorm; positivity)
  have hB : 0 ≤ B := integral_nonneg (fun _ => by unfold unitMajorant; positivity)
  refine ⟨C*A*B,by positivity,fun c => ?_⟩
  have hi := logRow_integrable rho L M c
  have he : (∫ y in Ioi (0:ℝ), ‖rowDensity rho L M c y‖) =
      ∫ t, ‖∫ x, logRow rho L M c t x‖ := by
    have h := integral_image_eq_integral_abs_deriv_smul
      (f := Real.exp) (f' := Real.exp) (s := univ) MeasurableSet.univ
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
      (fun y => ‖rowDensity rho L M c y‖)
    simp only [image_univ,Real.range_exp,setIntegral_univ,abs_of_pos (Real.exp_pos _)] at h
    rw [h]
    apply integral_congr_ae
    filter_upwards with t
    rw [← rowDensity_exp,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    rfl
  rw [he]
  calc
    _ ≤ ∫ t, ∫ x, ‖logRow rho L M c t x‖ :=
      integral_mono hi.integral_prod_left.norm hi.integral_norm_prod_left
        (fun _ => norm_integral_le_integral_norm _)
    _ = ∫ p : ℝ × ℝ, ‖logRow rho L M c p.1 p.2‖ := (integral_prod _ hi.norm).symm
    _ ≤ ∫ p : ℝ × ℝ, (C*((c:ℕ):ℝ)^(-(4:ℝ)))*(tiltedNorm rho L p.1*unitMajorant p.2) :=
      integral_mono hi.norm
        (((tiltedNorm_integrable rho L).mul_prod unitMajorant_integrable).const_mul _)
        (fun p => hb c p.1 p.2)
    _ = _ := by rw [integral_const_mul,Measure.volume_eq_prod,integral_prod_mul]; dsimp [A,B]; ring

private theorem rowDensity_norm_summable (rho : ℂ) (L M : ℝ) :
    Summable (fun c : ℕ+ => ∫ y in Ioi (0:ℝ),
      ‖((c:ℕ).totient:ℂ)*rowDensity rho L M c y‖) := by
  obtain ⟨C,hC,hb⟩ := rowDensity_norm_bound rho L M
  have hn := Real.summable_nat_rpow_inv.mpr (by norm_num : 1 < (3:ℝ))
  have hn' : Summable (fun n : ℕ => (n:ℝ)^(-(3:ℝ))) :=
    hn.congr (fun n => by rw [Real.rpow_neg (by positivity)])
  have hc : Summable (fun c : ℕ+ => ((c:ℕ):ℝ)^(-(3:ℝ))) :=
    hn'.comp_injective (fun _ _ h => PNat.coe_injective h)
  refine Summable.of_nonneg_of_le (fun c => integral_nonneg (fun _ => norm_nonneg _)) ?_ (hc.mul_left C)
  intro c
  have hcpos : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  simp only [norm_mul,Complex.norm_natCast,integral_const_mul]
  calc
    _ ≤ ((c:ℕ):ℝ)*(C*((c:ℕ):ℝ)^(-(4:ℝ))) :=
      mul_le_mul (by exact_mod_cast Nat.totient_le (c:ℕ)) (hb c)
        (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hcpos.le,Real.rpow_neg hcpos.le]
      norm_num
      field_simp

private def parabolicDensity (rho : ℂ) (L M y : ℝ) : ℂ :=
  ((y^2)⁻¹:ℝ) • (conj (heightProfile rho L y)*heightProfile rho M y)

private theorem parabolicDensity_exp (rho : ℂ) (L M t : ℝ) :
    Real.exp t • parabolicDensity rho L M (Real.exp t) =
      conj (profile rho (t+L))*profile rho (t+M) := by
  unfold parabolicDensity heightProfile
  rw [Real.log_exp,map_mul,Complex.conj_ofReal]
  have he : (Real.exp (t/2):ℂ)^2 = (Real.exp t:ℂ) := by
    rw [pow_two,← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  have ht : (Real.exp t:ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos t).ne'
  field_simp
  linear_combination (conj (profile rho (t+L))*profile rho (t+M))*he

private theorem translated_product_integrable (rho : ℂ) (L M : ℝ) :
    Integrable (fun t => conj (profile rho (t+L))*profile rho (t+M)) := by
  have hg : Integrable (profile rho) := by
    have h := profile_integrable rho 0
    change Integrable (fun t => fourierIntegrand (profile rho) 0 t) at h
    simpa [fourierIntegrand] using h
  obtain ⟨C,_,hb⟩ := profile_exp_bound rho 0
  have hp := (profile_continuous rho).measurable
  have hm : Measurable (fun t => conj (profile rho (t+L))*profile rho (t+M)) := by fun_prop
  apply ((hg.comp_add_right L).norm.mul_const C).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  simp only [norm_mul,norm_conj]
  exact mul_le_mul_of_nonneg_left (by simpa using hb (t+M)) (norm_nonneg _)

private theorem parabolicDensity_integrable (rho : ℂ) (L M : ℝ) :
    IntegrableOn (parabolicDensity rho L M) (Ioi (0:ℝ)) := by
  rw [integrable_exp_substitution]
  simpa only [parabolicDensity_exp] using translated_product_integrable rho L M

private theorem parabolicDensity_integral (rho : ℂ) (L M : ℝ) :
    (∫ y in Ioi (0:ℝ), parabolicDensity rho L M y) = autocorrelation rho (M-L) := by
  rw [integral_exp_substitution]
  simp_rw [parabolicDensity_exp]
  unfold autocorrelation
  have h := (measurePreserving_add_right volume L).integral_comp
    (MeasurableEquiv.addRight L).measurableEmbedding
      (fun t => conj (profile rho t)*profile rho (t+(M-L)))
  convert h using 1
  congr 1
  funext t
  congr 2
  ring

/-- The complete native Gram kernel of the literal theta dilation family. -/
theorem source_pairing_gram (rho : ℂ) (L M : ℝ) :
    (∫ z, conj (source rho L z)*source rho M z ∂D4BMGlobalAngularResponse.angularMeasure) =
      autocorrelation rho (M-L)+SelbergThetaTotientHankel.kernel rho (L+M) := by
  rw [source_pairing_height]
  have hi := fun c : ℕ+ => (rowDensity_integrable rho L M c).const_mul ((c:ℕ).totient:ℂ)
  have hs := rowDensity_norm_summable rho L M
  have hsum := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hi hs
  have he (y : ℝ) : ((y^2)⁻¹:ℝ) •
      (conj (heightProfile rho L y)*(heightProfile rho M y+∑' c : ℕ+,
        ((c:ℕ).totient:ℂ)*(∫ x,archProfile rho M y c x))) =
      parabolicDensity rho L M y+∑' c : ℕ+,((c:ℕ).totient:ℂ)*rowDensity rho L M c y := by
    unfold parabolicDensity rowDensity
    simp only [Complex.real_smul,mul_add]
    rw [← tsum_mul_left,← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro c
    ring
  simp_rw [he]
  rw [integral_add (parabolicDensity_integrable rho L M) hsum,parabolicDensity_integral,
    GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm hi hs]
  simp_rw [integral_const_mul,rowDensity_integral]
  rfl


/-- The literal theta dilation source as an element of the original native Hilbert space. -/
def vector (rho : ℂ) (L : ℝ) : Lp ℂ 2 angularMeasure :=
  (source_memLp rho L).toLp (source rho L)

/-- The Hilbert vector is represented almost everywhere by the full modular source. -/
theorem vector_coe (rho : ℂ) (L : ℝ) :
    (vector rho L : UpperHalfPlane → ℂ) =ᵐ[angularMeasure] source rho L :=
  (source_memLp rho L).coeFn_toLp

/-- Exact inner product of actual native Hilbert vectors, retaining the entire reflected kernel. -/
theorem vector_inner (rho : ℂ) (L M : ℝ) :
    inner ℂ (vector rho L) (vector rho M) =
      autocorrelation rho (M-L)+SelbergThetaTotientHankel.kernel rho (L+M) := by
  rw [L2.inner_def]
  have he : (∫ z, inner ℂ ((vector rho L : UpperHalfPlane → ℂ) z)
      ((vector rho M : UpperHalfPlane → ℂ) z) ∂angularMeasure) =
      ∫ z, conj (source rho L z)*source rho M z ∂angularMeasure := by
    apply integral_congr_ae
    filter_upwards [vector_coe rho L,vector_coe rho M] with z hL hM
    rw [hL,hM,RCLike.inner_apply']
  exact he.trans (source_pairing_gram rho L M)

/-- The complete native squared norm, expressed in the proved correlation kernel. -/
theorem vector_norm_sq (rho : ℂ) (L : ℝ) :
    ‖vector rho L‖^2 =
      (autocorrelation rho 0+SelbergThetaTotientHankel.kernel rho (2*L)).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (vector rho L)
  rw [vector_inner] at h
  simpa only [sub_self,← two_mul L,RCLike.re_to_complex] using h.symm

end
end RHTower.SelbergThetaDilationGram
