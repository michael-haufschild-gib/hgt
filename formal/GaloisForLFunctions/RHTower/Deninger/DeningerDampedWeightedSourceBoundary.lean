import GaloisForLFunctions.RHTower.Deninger.DeningerDampedHalfDensitySourceLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Same damped source: weighted Mellin admission and original prime-circle boundary

The literal prime-prefix sources converge in exponentially weighted L1 for
`1-a<c<a`. Two almost-everywhere subsequence limits identify these completions
with C43's original half-density source, without continuity of an unbounded weight.
Literal Mellin integrals therefore pass to that same limit. The original finite
Euler products give `M(g_a)(s)=M(g_0)(s)/(zeta(a+s)*zeta(a+1-s))` on its admitted
strip. Every actual Xi reading survives at damping one.

At damping two, both endpoint weights are integrable. The exact original
prime-circle Fourier coefficients are all nonzero, and no integrable primitive
of the original undamped translation defect can produce this source. These are
admission and boundary results for the actual limit, not an RH proof.

The remaining chain is complete Green/BV admission and fixed physical-reader
agreement, then conormal vanishing and RH. Full Mellin jets, the complete Xi
packet and its original Tate/Gamma transport, and damping continuation remain
separate obligations; none is supplied as a premise here.
-/

open Complex Filter Topology SchwartzMap MeasureTheory FourierTransform
noncomputable section
namespace RHTower

abbrev DeningerWeightedSourceL1 := Lp (α := ℝ) ℂ 1

def deningerOriginalTranslationL1 (b : ℝ) : DeningerWeightedSourceL1 ≃ₗᵢ[ℂ] DeningerWeightedSourceL1 :=
  MellinL2.lpCompMeasurePreservingEquiv (MellinL2.realTranslationEquiv b)
    (MellinL2.realTranslation_measurePreserving b)

theorem deningerOriginalTranslationL1_toLp (b : ℝ) (f : 𝓢(ℝ,ℂ)) :
    deningerOriginalTranslationL1 b (f.toLp 1 volume) =
      (MellinL2.schwartzTranslate b f).toLp 1 volume := by
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv b)
    (MellinL2.realTranslation_measurePreserving b) (f.toLp 1 volume) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (f.toLp 1 volume)
    (MellinL2.realTranslation_measurePreserving b),
    (MellinL2.schwartzTranslate b f).coeFn_toLp (p:=1) (μ:=volume),
    (f.coeFn_toLp (p:=1) (μ:=volume)).comp_tendsto
      (MellinL2.realTranslation_measurePreserving b).quasiMeasurePreserving.tendsto_ae]
    with t hl hr hf
  rw [hl,hr]
  simpa [MellinL2.realTranslationEquiv,Function.comp_apply] using hf

def deningerStrongLogWeightedL1LM (c : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerWeightedSourceL1 :=
  (SchwartzMap.toLpCLM ℂ ℂ 1 (volume : Measure ℝ)).toLinearMap.comp
    (deningerStrongLogWeightedSchwartzLM c)

theorem deningerStrongLogWeightedL1LM_flow (c d : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL1LM c (deningerMeyerStrongLogFlow d g) =
      (Real.exp (c*d) : ℂ) • deningerOriginalTranslationL1 (-d) (deningerStrongLogWeightedL1LM c g) := by
  change (deningerStrongLogWeightedSchwartzLM c (deningerMeyerStrongLogFlow d g)).toLp 1 volume = _
  rw [show deningerStrongLogWeightedL1LM c g =
    (deningerStrongLogWeightedSchwartzLM c g).toLp 1 volume by rfl, deningerOriginalTranslationL1_toLp]
  change (SchwartzMap.toLpCLM ℂ ℂ 1 volume) _ =
    (Real.exp (c*d) : ℂ) • (SchwartzMap.toLpCLM ℂ ℂ 1 volume) _
  rw [← map_smul]
  congr 1
  ext t
  simp only [deningerStrongLogWeightedSchwartzLM_apply,deningerMeyerStrongLogFlow_apply,
    smul_apply,MellinL2.schwartzTranslate_apply,smul_eq_mul]
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp only [sub_eq_add_neg]
  rw [show c*d+c*(t + -d)=c*t by ring]

def deningerWeightedL1PrimeFactor (L a c : ℝ) : DeningerWeightedSourceL1 →L[ℂ] DeningerWeightedSourceL1 :=
  ContinuousLinearMap.id ℂ _ - (Real.exp (-(a+c)*L) : ℂ) •
    (deningerOriginalTranslationL1 L).toLinearIsometry.toContinuousLinearMap

def deningerWeightedL1PrimeMate (L a c : ℝ) : DeningerWeightedSourceL1 →L[ℂ] DeningerWeightedSourceL1 :=
  ContinuousLinearMap.id ℂ _ - (Real.exp (-(a+1-c)*L) : ℂ) •
    (deningerOriginalTranslationL1 (-L)).toLinearIsometry.toContinuousLinearMap

def deningerWeightedL1PairedPrime (L a c : ℝ) : DeningerWeightedSourceL1 →L[ℂ] DeningerWeightedSourceL1 :=
  (deningerWeightedL1PrimeFactor L a c).comp (deningerWeightedL1PrimeMate L a c)

theorem deningerStrongLogWeightedL1_factor (L a c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL1LM c (deningerDampedStrongLogDefect L a g) =
      deningerWeightedL1PrimeFactor L a c (deningerStrongLogWeightedL1LM c g) := by
  change deningerStrongLogWeightedL1LM c
    (g - (deningerDampedPrimeWeight L a : ℂ) • deningerMeyerStrongLogFlow (-L) g) = _
  rw [map_sub,map_smul,deningerStrongLogWeightedL1LM_flow,smul_smul]
  simp only [deningerWeightedL1PrimeFactor,sub_apply,ContinuousLinearMap.id_apply,smul_apply,neg_neg]
  congr 2
  rw [deningerDampedPrimeWeight,← Complex.ofReal_mul,← Real.exp_add]
  congr 2
  ring

theorem deningerStrongLogWeightedL1_mate (L a c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL1LM c
      (deningerMeyerStrongLogJ (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ g))) =
      deningerWeightedL1PrimeMate L a c (deningerStrongLogWeightedL1LM c g) := by
  rw [deningerDampedStrongLogDefect_J_mate,map_sub,map_smul,deningerStrongLogWeightedL1LM_flow,smul_smul]
  simp only [deningerWeightedL1PrimeMate,sub_apply,ContinuousLinearMap.id_apply,smul_apply]
  congr 2
  rw [deningerDampedPrimeWeight,← Complex.ofReal_mul,← Complex.ofReal_mul,← Real.exp_add,← Real.exp_add]
  congr 2
  ring

theorem deningerStrongLogWeightedL1_paired (L a c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL1LM c (deningerDampedPairedStrongLogDefect L a g) =
      deningerWeightedL1PairedPrime L a c (deningerStrongLogWeightedL1LM c g) := by
  change deningerStrongLogWeightedL1LM c (deningerDampedStrongLogDefect L a
    (deningerMeyerStrongLogJ (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ g)))) = _
  rw [deningerStrongLogWeightedL1_factor,deningerStrongLogWeightedL1_mate]
  rfl

theorem deningerStrongLogWeightedL2LM_injective (c : ℝ) :
    Function.Injective (deningerStrongLogWeightedL2LM c) := by
  intro g h heq
  have hae : (deningerStrongLogWeightedSchwartzLM c g : ℝ → ℂ) =ᵐ[volume]
      deningerStrongLogWeightedSchwartzLM c h := by
    filter_upwards [(deningerStrongLogWeightedSchwartzLM c g).coeFn_toLp (p:=2) (μ:=volume),
      (deningerStrongLogWeightedSchwartzLM c h).coeFn_toLp (p:=2) (μ:=volume)] with t hg hh
    change (deningerStrongLogWeightedL2LM c g) t = _ at hg
    change (deningerStrongLogWeightedL2LM c h) t = _ at hh
    rw [heq,hh] at hg
    exact hg.symm
  have heq' := MeasureTheory.Measure.eq_of_ae_eq hae
    (deningerStrongLogWeightedSchwartzLM c g).continuous (deningerStrongLogWeightedSchwartzLM c h).continuous
  apply Subtype.ext
  funext t
  have ht := congrFun heq' t
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) ht

theorem deningerDampedOriginalPrimePrefix_source_step (a : ℝ) (n : ℕ) :
    deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE (n+1)).toList =
      if (n+1).Prime then deningerDampedPairedStrongLogDefect (Real.log ((n+1 : ℕ) : ℝ)) a
        (deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE n).toList)
      else deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE n).toList := by
  apply deningerStrongLogWeightedL2LM_injective (1/2)
  have h := deningerDampedHalfDensityPrefix_step a n
  unfold deningerDampedHalfDensityPrefix at h
  split_ifs with hn
  · rw [if_pos hn] at h
    simpa only [deningerStrongLogHalfDensity_paired] using h
  · rw [if_neg hn] at h
    exact h

private theorem deningerL1UnitaryDefect_norm_le (U : DeningerWeightedSourceL1 ≃ₗᵢ[ℂ] DeningerWeightedSourceL1)
    {w : ℝ} (hw : 0 ≤ w) (f : DeningerWeightedSourceL1) :
    ‖f - (w : ℂ) • U f‖ ≤ (1+w)*‖f‖ := by
  have heq : ‖(w : ℂ) • U f‖ = w*‖f‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw,LinearIsometryEquiv.norm_map]
  have h := norm_sub_le f ((w : ℂ) • U f)
  rw [heq] at h
  nlinarith

theorem deningerWeightedL1PairedPrime_norm_le (L a c : ℝ) (f : DeningerWeightedSourceL1) :
    ‖deningerWeightedL1PairedPrime L a c f‖ ≤
      Real.exp (Real.exp (-(a+c)*L)+Real.exp (-(a+1-c)*L))*‖f‖ := by
  let u := Real.exp (-(a+c)*L)
  let v := Real.exp (-(a+1-c)*L)
  have hm := deningerL1UnitaryDefect_norm_le (deningerOriginalTranslationL1 (-L)) (w:=v) (Real.exp_pos _).le f
  change ‖deningerWeightedL1PrimeMate L a c f‖ ≤ (1+v)*‖f‖ at hm
  have hd := deningerL1UnitaryDefect_norm_le (deningerOriginalTranslationL1 L) (w:=u) (Real.exp_pos _).le
    (deningerWeightedL1PrimeMate L a c f)
  change ‖deningerWeightedL1PairedPrime L a c f‖ ≤ (1+u)*‖deningerWeightedL1PrimeMate L a c f‖ at hd
  have hu : 1+u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hv : 1+v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  calc
    ‖deningerWeightedL1PairedPrime L a c f‖ ≤ (1+u)*((1+v)*‖f‖) :=
      hd.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ ≤ Real.exp u*(Real.exp v*‖f‖) := by gcongr
    _ = _ := by rw [← mul_assoc,← Real.exp_add]

theorem deningerWeightedL1PairedPrime_increment (L a c : ℝ)
    (hv : Real.exp (-(a+1-c)*L) ≤ 1) (f : DeningerWeightedSourceL1) :
    ‖deningerWeightedL1PairedPrime L a c f-f‖ ≤
      2*(Real.exp (-(a+c)*L)+Real.exp (-(a+1-c)*L))*‖f‖ := by
  let u := Real.exp (-(a+c)*L)
  let v := Real.exp (-(a+1-c)*L)
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hv0 : 0 ≤ v := (Real.exp_pos _).le
  have hm := deningerL1UnitaryDefect_norm_le (deningerOriginalTranslationL1 (-L)) hv0 f
  change ‖deningerWeightedL1PrimeMate L a c f‖ ≤ (1+v)*‖f‖ at hm
  have hd : ‖deningerWeightedL1PairedPrime L a c f - deningerWeightedL1PrimeMate L a c f‖ =
      u*‖deningerWeightedL1PrimeMate L a c f‖ := by
    change ‖(deningerWeightedL1PrimeMate L a c f - (u : ℂ) •
      deningerOriginalTranslationL1 L (deningerWeightedL1PrimeMate L a c f)) -
        deningerWeightedL1PrimeMate L a c f‖ = _
    rw [sub_sub_cancel_left,norm_neg,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hu0,LinearIsometryEquiv.norm_map]
  have hm' : ‖deningerWeightedL1PrimeMate L a c f-f‖ = v*‖f‖ := by
    change ‖(f-(v : ℂ) • deningerOriginalTranslationL1 (-L) f)-f‖ = _
    rw [sub_sub_cancel_left,norm_neg,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hv0,LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖deningerWeightedL1PairedPrime L a c f-deningerWeightedL1PrimeMate L a c f‖ +
      ‖deningerWeightedL1PrimeMate L a c f-f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = u*‖deningerWeightedL1PrimeMate L a c f‖+v*‖f‖ := by rw [hd,hm']
    _ ≤ u*((1+v)*‖f‖)+v*‖f‖ := by gcongr
    _ ≤ 2*(u+v)*‖f‖ := by
      nlinarith [mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hv)) (norm_nonneg f),
        mul_nonneg hv0 (norm_nonneg f)]

def deningerWeightedPrimeStepWeight (a c : ℝ) (n : ℕ) : ℝ :=
  deningerHalfDensityPrimeStepWeight (a+c-1/2) n +
    deningerHalfDensityPrimeStepWeight (a+1/2-c) n

theorem deningerWeightedPrimeStepWeight_nonneg (a c : ℝ) (n : ℕ) :
    0 ≤ deningerWeightedPrimeStepWeight a c n :=
  add_nonneg (deningerHalfDensityPrimeStepWeight_nonneg _ _) (deningerHalfDensityPrimeStepWeight_nonneg _ _)

theorem deningerWeightedPrimeStepWeight_summable {a c : ℝ} (hc0 : 1-a<c) (hc1 : c<a) :
    Summable (deningerWeightedPrimeStepWeight a c) :=
  (deningerHalfDensityPrimeStepWeight_summable (by linarith : 1/2<a+c-1/2)).add
    (deningerHalfDensityPrimeStepWeight_summable (by linarith : 1/2<a+1/2-c))

theorem deningerWeightedPrimeStepWeight_eq_exp (a c : ℝ) (p : Nat.Primes) :
    deningerWeightedPrimeStepWeight a c p =
      Real.exp (-(a+c)*Real.log (p : ℕ))+Real.exp (-(a+1-c)*Real.log (p : ℕ)) := by
  rw [deningerWeightedPrimeStepWeight,deningerHalfDensityPrimeStepWeight_eq_exp,
    deningerHalfDensityPrimeStepWeight_eq_exp]
  congr 2 <;> ring

private theorem deningerWeightedPrimeMate_weight_lt_one {a c : ℝ} (hc1 : c<a) (p : Nat.Primes) :
    Real.exp (-(a+1-c)*Real.log (p : ℕ)) < 1 := by
  have h := deningerHalfDensityPrimeStepWeight_lt_one (by linarith : 1/2<a+1/2-c) (p : ℕ)
  rw [deningerHalfDensityPrimeStepWeight_eq_exp] at h
  convert h using 1
  congr 2
  ring

def deningerDampedWeightedL1Prefix (a c : ℝ) (n : ℕ) : DeningerWeightedSourceL1 :=
  deningerStrongLogWeightedL1LM c (deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE n).toList)

theorem deningerDampedWeightedL1Prefix_step (a c : ℝ) (n : ℕ) :
    deningerDampedWeightedL1Prefix a c (n+1) =
      if (n+1).Prime then deningerWeightedL1PairedPrime (Real.log ((n+1 : ℕ) : ℝ)) a c
        (deningerDampedWeightedL1Prefix a c n)
      else deningerDampedWeightedL1Prefix a c n := by
  unfold deningerDampedWeightedL1Prefix
  rw [deningerDampedOriginalPrimePrefix_source_step]
  split_ifs <;> simp only [deningerStrongLogWeightedL1_paired]

private theorem deningerDampedWeightedL1Prefix_step_bound (a c : ℝ) (n : ℕ) :
    ‖deningerDampedWeightedL1Prefix a c (n+1)‖ ≤
      Real.exp (deningerWeightedPrimeStepWeight a c (n+1))*‖deningerDampedWeightedL1Prefix a c n‖ := by
  rw [deningerDampedWeightedL1Prefix_step]
  split_ifs with hn
  · let p : Nat.Primes := ⟨n+1,hn⟩
    have hw := deningerWeightedPrimeStepWeight_eq_exp a c p
    change deningerWeightedPrimeStepWeight a c (n+1) = _ at hw
    rw [hw]
    exact deningerWeightedL1PairedPrime_norm_le _ _ _ _
  · simp [deningerWeightedPrimeStepWeight,deningerHalfDensityPrimeStepWeight,hn]

private theorem deningerDampedWeightedL1Prefix_step_increment {a c : ℝ} (hc1 : c<a) (n : ℕ) :
    ‖deningerDampedWeightedL1Prefix a c (n+1)-deningerDampedWeightedL1Prefix a c n‖ ≤
      2*deningerWeightedPrimeStepWeight a c (n+1)*‖deningerDampedWeightedL1Prefix a c n‖ := by
  rw [deningerDampedWeightedL1Prefix_step]
  split_ifs with hn
  · let p : Nat.Primes := ⟨n+1,hn⟩
    have hw := deningerWeightedPrimeStepWeight_eq_exp a c p
    change deningerWeightedPrimeStepWeight a c (n+1) = _ at hw
    rw [hw]
    exact deningerWeightedL1PairedPrime_increment _ _ _ (deningerWeightedPrimeMate_weight_lt_one hc1 p).le _
  · simp [deningerWeightedPrimeStepWeight,deningerHalfDensityPrimeStepWeight,hn]

theorem deningerDampedWeightedL1Prefix_norm_le (a c : ℝ) (n : ℕ) :
    ‖deningerDampedWeightedL1Prefix a c n‖ ≤
      Real.exp (∑ k ∈ Finset.range n, deningerWeightedPrimeStepWeight a c (k+1))*
        ‖deningerDampedWeightedL1Prefix a c 0‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ Real.exp (deningerWeightedPrimeStepWeight a c (n+1))*‖deningerDampedWeightedL1Prefix a c n‖ :=
        deningerDampedWeightedL1Prefix_step_bound a c n
      _ ≤ Real.exp (deningerWeightedPrimeStepWeight a c (n+1))*
          (Real.exp (∑ k ∈ Finset.range n, deningerWeightedPrimeStepWeight a c (k+1))*
            ‖deningerDampedWeightedL1Prefix a c 0‖) := by gcongr
      _ = _ := by rw [← mul_assoc,← Real.exp_add,Finset.sum_range_succ]; congr 2; ring

def deningerDampedWeightedL1NormBound (a c : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, deningerWeightedPrimeStepWeight a c (k+1))*‖deningerDampedWeightedL1Prefix a c 0‖

theorem deningerDampedWeightedL1Prefix_uniform_bound {a c : ℝ} (hc0 : 1-a<c) (hc1 : c<a) (n : ℕ) :
    ‖deningerDampedWeightedL1Prefix a c n‖ ≤ deningerDampedWeightedL1NormBound a c := by
  apply (deningerDampedWeightedL1Prefix_norm_le a c n).trans
  unfold deningerDampedWeightedL1NormBound
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact ((deningerWeightedPrimeStepWeight_summable hc0 hc1).comp_injective
    (fun _ _ h => Nat.add_right_cancel h)).sum_le_tsum _ (fun _ _ => deningerWeightedPrimeStepWeight_nonneg a c _)

theorem deningerDampedWeightedL1Prefix_cauchy {a c : ℝ} (hc0 : 1-a<c) (hc1 : c<a) :
    CauchySeq (deningerDampedWeightedL1Prefix a c) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => 2*deningerWeightedPrimeStepWeight a c (n+1)*deningerDampedWeightedL1NormBound a c)
  · intro n
    rw [dist_comm,dist_eq_norm]
    apply (deningerDampedWeightedL1Prefix_step_increment hc1 n).trans
    exact mul_le_mul_of_nonneg_left (deningerDampedWeightedL1Prefix_uniform_bound hc0 hc1 n)
      (mul_nonneg (by norm_num) (deningerWeightedPrimeStepWeight_nonneg a c _))
  · exact (((deningerWeightedPrimeStepWeight_summable hc0 hc1).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left 2).mul_right _

def deningerDampedWeightedL1Limit (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) : DeningerWeightedSourceL1 :=
  Classical.choose (cauchySeq_tendsto_of_complete (deningerDampedWeightedL1Prefix_cauchy c.property.1 c.property.2))

theorem deningerDampedWeightedL1Prefix_tendsto (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) :
    Tendsto (deningerDampedWeightedL1Prefix a.val c.val) atTop (𝓝 (deningerDampedWeightedL1Limit a c)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (deningerDampedWeightedL1Prefix_cauchy c.property.1 c.property.2))


theorem deningerDampedWeightedL1Prefix_halfDensity_ae (a c : ℝ) (n : ℕ) :
    (deningerDampedWeightedL1Prefix a c n : ℝ → ℂ) =ᵐ[volume]
      fun t => (Real.exp ((c-1/2)*t) : ℂ)*deningerDampedHalfDensityPrefix a n t := by
  let g := deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE n).toList
  filter_upwards [(deningerStrongLogWeightedSchwartzLM c g).coeFn_toLp (p:=1) (μ:=volume),
    (deningerStrongLogWeightedSchwartzLM (1/2) g).coeFn_toLp (p:=2) (μ:=volume)] with t hc hh
  change deningerDampedWeightedL1Prefix a c n t = _ at hc
  change deningerDampedHalfDensityPrefix a n t = _ at hh
  rw [hc,hh,deningerStrongLogWeightedSchwartzLM_apply,deningerStrongLogWeightedSchwartzLM_apply,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show (c-1/2)*t+(1/2)*t=c*t by ring]

theorem deningerDampedWeightedL1Limit_halfDensity_ae (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) :
    (deningerDampedWeightedL1Limit a c : ℝ → ℂ) =ᵐ[volume]
      fun t => (Real.exp ((c.val-1/2)*t) : ℂ)*deningerDampedHalfDensityLimit a t := by
  obtain ⟨phi,hphi,hhalf⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (deningerDampedHalfDensityPrefix_tendsto a)).exists_seq_tendsto_ae
  obtain ⟨psi,hpsi,hweighted⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      ((deningerDampedWeightedL1Prefix_tendsto a c).comp hphi.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n : ℕ,
      deningerDampedWeightedL1Prefix a.val c.val n t =
        (Real.exp ((c.val-1/2)*t) : ℂ)*deningerDampedHalfDensityPrefix a.val n t :=
    ae_all_iff.mpr (deningerDampedWeightedL1Prefix_halfDensity_ae a.val c.val)
  filter_upwards [hhalf,hweighted,hall] with t hh hw heq
  have hh' := hh.comp hpsi.tendsto_atTop
  have ht : Tendsto (fun k => deningerDampedWeightedL1Prefix a.val c.val (phi (psi k)) t) atTop
      (𝓝 ((Real.exp ((c.val-1/2)*t) : ℂ)*deningerDampedHalfDensityLimit a t)) :=
    (tendsto_const_nhds.mul hh').congr' (Filter.Eventually.of_forall fun k => (heq (phi (psi k))).symm)
  exact tendsto_nhds_unique hw ht

/-- The actual logarithmic source representative from C43's half-density limit. -/
def deningerDampedLogSource (a : {a : ℝ // 1/2<a}) (t : ℝ) : ℂ :=
  (Real.exp (-(1/2)*t) : ℂ)*deningerDampedHalfDensityLimit a t

theorem deningerDampedLogSource_weighted_ae (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) :
    (fun t => (Real.exp (c.val*t) : ℂ)*deningerDampedLogSource a t) =ᵐ[volume]
      deningerDampedWeightedL1Limit a c := by
  filter_upwards [deningerDampedWeightedL1Limit_halfDensity_ae a c] with t ht
  rw [ht,deningerDampedLogSource,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show c.val*t+(-(1/2))*t=(c.val-1/2)*t by ring]

theorem deningerDampedLogSource_weighted_memLp (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) :
    MemLp (fun t => (Real.exp (c.val*t) : ℂ)*deningerDampedLogSource a t) 1 (volume : Measure ℝ) :=
  (memLp_congr_ae (deningerDampedLogSource_weighted_ae a c)).mpr (Lp.memLp _)

theorem deningerDampedLogSource_weighted_integrable (a : {a : ℝ // 1/2<a})
    (c : {c : ℝ // 1-a.val<c ∧ c<a.val}) :
    Integrable (fun t => (Real.exp (c.val*t) : ℂ)*deningerDampedLogSource a t) :=
  memLp_one_iff_integrable.mp (deningerDampedLogSource_weighted_memLp a c)

theorem deningerDampedLogSource_aestronglyMeasurable (a : {a : ℝ // 1/2<a}) :
    AEStronglyMeasurable (deningerDampedLogSource a) (volume : Measure ℝ) := by
  unfold deningerDampedLogSource
  exact (by fun_prop : Continuous (fun t : ℝ => (Real.exp (-(1/2)*t) : ℂ))).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable _)

theorem deningerDampedLogSource_mellin_integrable (a : {a : ℝ // 1/2<a})
    (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    Integrable (deningerMeyerStrongLogMellinJet 0 s (deningerDampedLogSource a)) := by
  let c : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re,hs0,hs1⟩
  apply memLp_one_iff_integrable.mp
  apply (deningerDampedLogSource_weighted_memLp a c).congr_norm
  · have heq : deningerMeyerStrongLogMellinJet 0 s (deningerDampedLogSource a) =
        (fun t : ℝ => Complex.exp (s*(t : ℂ))*deningerDampedLogSource a t) := by
      funext t
      simp [deningerMeyerStrongLogMellinJet]
    rw [heq]
    exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (s*(t : ℂ)))).aestronglyMeasurable.mul
      (deningerDampedLogSource_aestronglyMeasurable a)
  · filter_upwards with t
    simp only [norm_deningerMeyerStrongLogMellinJet,pow_zero,one_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    rfl

/-- Literal Mellin reading on one admitted exponential-weight L1 space. -/
def deningerWeightedL1MellinCLM (tau : ℝ) : DeningerWeightedSourceL1 →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ (-tau/(2*Real.pi))).comp (Real.Lp.fourierTransformCLM ℝ ℂ)

theorem deningerWeightedL1MellinCLM_eq_integral (s : ℂ) (g : ℝ → ℂ) (f : DeningerWeightedSourceL1)
    (hf : (fun t => (Real.exp (s.re*t) : ℂ)*g t) =ᵐ[volume] f) :
    deningerWeightedL1MellinCLM s.im f = deningerMeyerStrongLogMellin g s := by
  change (𝓕 (f : ℝ → ℂ)) (-s.im/(2*Real.pi)) = _
  rw [Real.fourier_real_eq_integral_exp_smul,deningerMeyerStrongLogMellin]
  apply integral_congr_ae
  filter_upwards [hf] with t ht
  rw [← ht]
  simp only [smul_eq_mul,deningerMeyerStrongLogMellinJet,pow_zero,one_mul,Complex.ofReal_exp]
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  conv_rhs => rw [← Complex.re_add_im s]
  field_simp [Real.pi_ne_zero]
  ring

theorem deningerWeightedL1MellinCLM_source (s : ℂ) (g : DeningerMeyerStrongLogTarget) :
    deningerWeightedL1MellinCLM s.im (deningerStrongLogWeightedL1LM s.re g) =
      deningerMeyerStrongLogMellin g s := by
  apply deningerWeightedL1MellinCLM_eq_integral
  exact (deningerStrongLogWeightedSchwartzLM s.re g).coeFn_toLp (p:=1) (μ:=volume) |>.symm

theorem deningerDampedLogSource_mellin_tendsto (a : {a : ℝ // 1/2<a})
    (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    Tendsto (fun n => deningerMeyerStrongLogMellin
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) s) atTop
      (𝓝 (deningerMeyerStrongLogMellin (deningerDampedLogSource a) s)) := by
  let c : {c : ℝ // 1-a.val<c ∧ c<a.val} := ⟨s.re,hs0,hs1⟩
  have h := ((deningerWeightedL1MellinCLM s.im).continuous.tendsto
    (deningerDampedWeightedL1Limit a c)).comp (deningerDampedWeightedL1Prefix_tendsto a c)
  rw [deningerWeightedL1MellinCLM_eq_integral s _ _ (deningerDampedLogSource_weighted_ae a c)] at h
  exact h.congr' (Filter.Eventually.of_forall fun n =>
    deningerWeightedL1MellinCLM_source s (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList))

/-- Every actual Xi reading of the damping-one source is an admitted literal integral and limit. -/
theorem deningerDampingOne_source_xi_admission (rho : XiDivisorSupport) :
    Integrable (deningerMeyerStrongLogMellinJet 0 (rho : ℂ)
      (deningerDampedLogSource ⟨1,by norm_num⟩)) ∧
    Tendsto (fun n => deningerMeyerStrongLogMellin
      (deningerDampedPrimeListSource 1 (GaloisForLFunctions.primesLE n).toList) (rho : ℂ)) atTop
      (𝓝 (deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨1,by norm_num⟩) (rho : ℂ))) := by
  let a : {a : ℝ // 1/2<a} := ⟨1,by norm_num⟩
  have hs0 : 1-a.val<(rho : ℂ).re := by
    simpa [a] using (xi_divisor_support_re_mem_open_unit rho).1
  have hs1 : (rho : ℂ).re<a.val := (xi_divisor_support_re_mem_open_unit rho).2
  exact ⟨deningerDampedLogSource_mellin_integrable a rho hs0 hs1,
    deningerDampedLogSource_mellin_tendsto a rho hs0 hs1⟩

/-- The concrete original prime prefixes are cofinal among finite prime sets. -/
theorem deningerOriginalPrimePrefix_tendsto :
    Tendsto GaloisForLFunctions.primesLE atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro n m hnm p hp
    exact (GaloisForLFunctions.mem_primesLE m p).mpr
      (((GaloisForLFunctions.mem_primesLE n p).mp hp).trans hnm)
  · intro p
    exact ⟨p.val,(GaloisForLFunctions.mem_primesLE p.val p).mpr le_rfl⟩

private theorem damped_prime_amplitude_cpow (p : Nat.Primes) (a : ℝ) (s : ℂ) :
    (deningerDampedPrimeWeight (Real.log (p : ℕ)) a : ℂ) *
      Complex.exp ((-Real.log (p : ℕ) : ℂ)*s) =
        (p : ℂ)^(-((a : ℂ)+s)) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [Complex.cpow_def_of_ne_zero hp]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_log (by exact_mod_cast p.property.pos.le)]
  simp only [deningerDampedPrimeWeight,Complex.ofReal_exp,Complex.ofReal_mul,
    Complex.ofReal_neg,← Complex.exp_add]
  congr 1
  ring

theorem deningerDampedPairedMultiplier_cpow (p : Nat.Primes) (a : ℝ) (s : ℂ) :
    deningerDampedPairedMultiplier (Real.log (p : ℕ)) a s =
      (1-(p : ℂ)^(-((a : ℂ)+s)))*(1-(p : ℂ)^(-((a : ℂ)+1-s))) := by
  rw [deningerDampedPairedMultiplier,damped_prime_amplitude_cpow,damped_prime_amplitude_cpow]
  congr 3
  ring

private theorem one_sub_prime_cpow_hasProd (s : ℂ) (hs : 1<s.re) :
    HasProd (fun p : Nat.Primes => 1-(p : ℂ)^(-s)) (riemannZeta s)⁻¹ := by
  have h := (riemannZeta_eulerProduct_hasProd hs).inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)
  simpa only [HasProd,Finset.prod_inv_distrib,inv_inv] using h

/-- Original paired prime factors have the Euler product in the actual admission strip. -/
theorem deningerDampedPairedMultiplier_hasProd (a : ℝ) (s : ℂ)
    (hs0 : 1-a<s.re) (hs1 : s.re<a) :
    HasProd (fun p : Nat.Primes => deningerDampedPairedMultiplier (Real.log (p : ℕ)) a s)
      ((riemannZeta ((a : ℂ)+s)*riemannZeta ((a : ℂ)+1-s))⁻¹) := by
  have h0 : 1<((a : ℂ)+s).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
  have h1 : 1<((a : ℂ)+1-s).re := by
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.one_re]; linarith
  simpa only [deningerDampedPairedMultiplier_cpow,mul_inv] using
    (one_sub_prime_cpow_hasProd ((a : ℂ)+s) h0).mul
      (one_sub_prime_cpow_hasProd ((a : ℂ)+1-s) h1)

/-- The Mellin formula is proved by the limit of the actual source integrals. -/
theorem deningerDampedLogSource_mellin_eq (a : {a : ℝ // 1/2<a})
    (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    deningerMeyerStrongLogMellin (deningerDampedLogSource a) s =
      deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s /
        (riemannZeta ((a.val : ℂ)+s)*riemannZeta ((a.val : ℂ)+1-s)) := by
  have hp := (deningerDampedPairedMultiplier_hasProd a.val s hs0 hs1).comp
    deningerOriginalPrimePrefix_tendsto
  have hm := hp.mul_const (deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s)
  have hm' : Tendsto (fun n => deningerMeyerStrongLogMellin
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) s) atTop
      (𝓝 (deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s /
        (riemannZeta ((a.val : ℂ)+s)*riemannZeta ((a.val : ℂ)+1-s)))) := by
    simpa only [deningerDampedPrimeListSource_mellin,deningerDampedPrimeListMultiplier,
      ← Finset.prod_map_toList,div_eq_mul_inv,mul_comm,Function.comp_apply] using hm
  exact tendsto_nhds_unique (deningerDampedLogSource_mellin_tendsto a s hs0 hs1) hm'

theorem deningerDampedLogSource_mellin_ne_zero (a : {a : ℝ // 1/2<a})
    (s : ℂ) (hs0 : 1-a.val<s.re) (hs1 : s.re<a.val) :
    deningerMeyerStrongLogMellin (deningerDampedLogSource a) s ≠ 0 := by
  rw [deningerDampedLogSource_mellin_eq a s hs0 hs1]
  apply div_ne_zero (deningerMeyerReflectedLogGaussianSource_mellin_ne_zero s)
  apply mul_ne_zero
  · apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.add_re,Complex.ofReal_re]; linarith
  · apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.one_re]; linarith

/-- Every actual Xi reading survives in the damping-one source. -/
theorem deningerDampingOne_source_xi_ne_zero (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨1,by norm_num⟩) (rho : ℂ) ≠ 0 := by
  apply deningerDampedLogSource_mellin_ne_zero
  · simpa using (xi_divisor_support_re_mem_open_unit rho).1
  · exact (xi_divisor_support_re_mem_open_unit rho).2

/-- Both original endpoint weights are admitted at the fixed damping value two. -/
theorem deningerDampingTwo_source_endpoint_integrable :
    Integrable (deningerDampedLogSource ⟨2,by norm_num⟩) ∧
    Integrable (fun t => (Real.exp t : ℂ)*deningerDampedLogSource ⟨2,by norm_num⟩ t) := by
  constructor
  · simpa using deningerDampedLogSource_weighted_integrable ⟨2,by norm_num⟩ ⟨0,by norm_num⟩
  · simpa using deningerDampedLogSource_weighted_integrable ⟨2,by norm_num⟩ ⟨1,by norm_num⟩

/-- The admitted source retains a nonzero original total mass. -/
theorem deningerDampingTwo_source_total_mass_ne_zero :
    (∫ t, deningerDampedLogSource ⟨2,by norm_num⟩ t) ≠ 0 := by
  have h := deningerDampedLogSource_mellin_ne_zero ⟨2,by norm_num⟩ 0 (by norm_num) (by norm_num)
  simpa only [deningerMeyerStrongLogMellin,deningerMeyerStrongLogMellinJet,pow_zero,
    zero_mul,Complex.exp_zero,one_mul] using h

/-- Fourier readings are literal imaginary-axis Mellin integrals, with the original scale. -/
theorem deningerDampedLogSource_fourier_eq (a : {a : ℝ // 1/2<a}) (w : ℝ) :
    𝓕 (deningerDampedLogSource a) w =
      deningerMeyerStrongLogMellin (deningerDampedLogSource a)
        ((-(2*Real.pi*w) : ℝ)*Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul,deningerMeyerStrongLogMellin]
  apply integral_congr_ae
  filter_upwards with t
  simp only [deningerMeyerStrongLogMellinJet,pow_zero,one_mul,smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- Every ordinary Fourier reading of the admitted damping-two source is nonzero. -/
theorem deningerDampingTwo_source_fourier_ne_zero (w : ℝ) :
    𝓕 (deningerDampedLogSource ⟨2,by norm_num⟩) w ≠ 0 := by
  rw [deningerDampedLogSource_fourier_eq]
  apply deningerDampedLogSource_mellin_ne_zero <;> simp

/-- Every mode on every original prime circle retains its exact Mellin value. -/
theorem deningerDampingTwo_source_primeCircle_coefficient (p : Nat.Primes) (k : ℤ) :
    fourierCoeffOn (Real.log_pos (show (1 : ℝ)<(p : ℕ) by exact_mod_cast p.property.one_lt))
      (GaloisForLFunctions.HTGeometry.l1PeriodizationAtScale
        (deningerDampedLogSource ⟨2,by norm_num⟩) (Real.log (p : ℕ))) k =
      (1/Real.log (p : ℕ)) •
        deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨2,by norm_num⟩)
          ((-(2*Real.pi*((1/Real.log (p : ℕ))*(k : ℝ))) : ℝ)*Complex.I) := by
  rw [GaloisForLFunctions.HTGeometry.fourierCoeffOn_l1PeriodizationAtScale
    deningerDampingTwo_source_endpoint_integrable.1,deningerDampedLogSource_fourier_eq]

/-- The damped source retains every original-prime Fourier mode, including the constant mode. -/
theorem deningerDampingTwo_source_primeCircle_coefficient_ne_zero (p : Nat.Primes) (k : ℤ) :
    fourierCoeffOn (Real.log_pos (show (1 : ℝ)<(p : ℕ) by exact_mod_cast p.property.one_lt))
      (GaloisForLFunctions.HTGeometry.l1PeriodizationAtScale
        (deningerDampedLogSource ⟨2,by norm_num⟩) (Real.log (p : ℕ))) k ≠ 0 := by
  rw [GaloisForLFunctions.HTGeometry.fourierCoeffOn_l1PeriodizationAtScale
    deningerDampingTwo_source_endpoint_integrable.1]
  exact smul_ne_zero (one_div_ne_zero (Real.log_pos (show (1 : ℝ)<(p : ℕ) by exact_mod_cast p.property.one_lt)).ne')
    (deningerDampingTwo_source_fourier_ne_zero _)

/-- No original prime circle vanishes even almost everywhere on its full fundamental cell. -/
theorem deningerDampingTwo_source_primeCircle_not_ae_zero (p : Nat.Primes) :
    ¬ (GaloisForLFunctions.HTGeometry.l1PeriodizationAtScale
        (deningerDampedLogSource ⟨2,by norm_num⟩) (Real.log (p : ℕ)))
      =ᵐ[volume.restrict (Set.Ioc 0 (Real.log (p : ℕ)))] (fun _ => 0) := by
  intro h
  have he := congrFun (fourierCoeffOn_congr_ae
    (Real.log_pos (show (1 : ℝ)<(p : ℕ) by exact_mod_cast p.property.one_lt)) h) 0
  apply deningerDampingTwo_source_primeCircle_coefficient_ne_zero p 0
  simpa [fourierCoeffOn_eq_integral] using he

/-- The original undamped translation defect cannot produce this source from any L1 primitive. -/
theorem deningerDampingTwo_source_no_integrable_primeGreen (p : Nat.Primes) :
    ¬ ∃ h : ℝ → ℂ, Integrable h ∧
      (fun t => h t-h (t+Real.log (p : ℕ))) =ᵐ[volume]
        deningerDampedLogSource ⟨2,by norm_num⟩ := by
  rintro ⟨h,hi,he⟩
  have hI := integral_congr_ae he
  rw [integral_sub hi (hi.comp_add_right (Real.log (p : ℕ))),
    integral_add_right_eq_self,sub_self] at hI
  exact deningerDampingTwo_source_total_mass_ne_zero hI.symm

end RHTower
