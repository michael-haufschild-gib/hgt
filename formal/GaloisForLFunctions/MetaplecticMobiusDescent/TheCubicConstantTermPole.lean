/-
The cubic constant-term pole adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicConstantDirichletSeries
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# A nonzero arithmetic residue at four thirds

Reindex the ideal sum by absolute norm to identify the full Dedekind
zeta function. Removing the ramified Euler factor identifies the
unramified series. The positive class-number residue, together with
nonvanishing at two, gives the nonzero constant-term residue at `4/3`.
-/
noncomputable section
open MeasureTheory Set Filter UniqueFactorizationMonoid
open scoped BigOperators Classical Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

def fullIdealWeight (s : ℂ) (I : Ideal O) : ℂ :=
  if I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)

lemma fullIdealWeight_good (s : ℂ) (I : GoodIdeal) : fullIdealWeight s I.1=unramifiedNormWeight s I.1 := by
  rw [fullIdealWeight,if_neg (primaryIdealGenerator_ne_zero_ideal _ I.2),unramifiedNormWeight_of_good _ _ I.2]

lemma norm_fullIdealWeight (s : ℂ) (I : NonzeroIdeal) :
    ‖fullIdealWeight s I.1‖=‖ringComplex (cubicIdealGenerator I.1)‖^(-2*s.re) := by
  rw [fullIdealWeight,if_neg I.2]
  have hn : 0<‖ringComplex (cubicIdealGenerator I.1)‖ :=
    norm_pos_iff.mpr (ringComplex_ne_zero (cubicIdealGenerator_ne_zero _ I.2))
  have hnorm : ‖ringComplex (cubicIdealGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [ringComplex_norm_sq_eq_absNorm_span,span_cubicIdealGenerator]
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖ringComplex (cubicIdealGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn),← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem fullIdealWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖fullIdealWeight s I‖) := by
  have hinj : Function.Injective (fun I : NonzeroIdeal => cubicIdealGenerator I.1) :=
    cubicIdealGenerator_injective.comp Subtype.val_injective
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective hinj
  have hsub : Summable (fun I : NonzeroIdeal => ‖fullIdealWeight s I.1‖) := by
    simpa only [Function.comp_def,norm_fullIdealWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | I ≠ 0})
    (f := fun I => ‖fullIdealWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : I=0
  · subst I
    simp [Set.indicator,fullIdealWeight]
  · have hIbot : I ≠ ⊥ := hI
    simp [Set.indicator,hIbot,fullIdealWeight]

def fullIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O,fullIdealWeight s I

lemma fullIdealWeight_norm_fiber (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1)=
      LSeries.term (fun n => (Nat.card {I : Ideal O // Ideal.absNorm I=n}:ℂ)) s n := by
  by_cases hn : n=0
  · subst n
    have hzero (I : {I : Ideal O // Ideal.absNorm I=0}) : fullIdealWeight s I.1=0 := by
      have hz : I.1=(0:Ideal O) := Ideal.absNorm_eq_zero_iff.mp I.2
      rw [fullIdealWeight,if_pos hz]
    simp only [hzero,tsum_zero,LSeries.term_zero]
  · let : Fintype {I : Ideal O // Ideal.absNorm I=n} :=
      (Ideal.finite_setOf_absNorm_eq (S := O) n).fintype
    have hterm (I : {I : Ideal O // Ideal.absNorm I=n}) : fullIdealWeight s I.1=(n:ℂ)^(-s) := by
      have hI : I.1 ≠ 0 := fun h => hn (by rw [← I.2,h,map_zero])
      rw [fullIdealWeight,if_neg hI,I.2]
    simp only [hterm,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      LSeries.term_of_ne_zero hn,Nat.card_eq_fintype_card,Complex.cpow_neg,div_eq_mul_inv]

theorem fullIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    fullIdealZeta s=NumberField.dedekindZeta K s := by
  have h := (fullIdealWeight_summable_norm s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ =>
    ∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1) (fullIdealZeta s) at h
  simp_rw [fullIdealWeight_norm_fiber] at h
  exact h.tsum_eq.symm

lemma fullIdealWeight_lambdaFactor (s : ℂ) (n : ℕ) (I : GoodIdeal) :
    fullIdealWeight s (lambdaFactorMap (n,I)).1=((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
  rw [fullIdealWeight,if_neg (lambdaFactorMap (n,I)).2]
  change (Ideal.absNorm (ramifiedIdeal^n*I.1):ℂ)^(-s)=_
  rw [map_mul,map_pow,ramifiedIdeal_absNorm,Nat.cast_mul,
    unramifiedNormWeight_of_good _ _ I.2]
  rw [Complex.natCast_mul_natCast_cpow]
  congr 1
  have h := (Complex.natCast_cpow_natCast_mul 3 n (-s)).symm.trans (Complex.cpow_nat_mul 3 n (-s))
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

theorem unramifiedIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    unramifiedIdealZeta s=(1-(3:ℂ)^(-s))*NumberField.dedekindZeta K s := by
  have hnorm : ‖(3:ℂ)^(-s)‖<1 := by
    change ‖((3:ℝ):ℂ)^(-s)‖<1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.neg_re]
    linarith
  have hne : 1-(3:ℂ)^(-s) ≠ 0 := by
    intro h
    have hz : (3:ℂ)^(-s)=1 := (sub_eq_zero.mp h).symm
    rw [hz,norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hsub : Summable (fun I : NonzeroIdeal => fullIdealWeight s I.1) :=
    (fullIdealWeight_summable_norm s hs).of_norm.subtype _
  have hp := lambdaFactorEquiv.summable_iff.mpr hsub
  change Summable (fun p : ℕ × GoodIdeal => fullIdealWeight s (lambdaFactorMap p).1) at hp
  have hfull : fullIdealZeta s=(1-(3:ℂ)^(-s))⁻¹*unramifiedIdealZeta s := by
    calc
      _ = ∑' I : NonzeroIdeal,fullIdealWeight s I.1 := by
        symm
        apply tsum_subtype_eq_of_support_subset
        intro I hI
        change I ≠ 0
        intro hz
        exact hI (by simp [fullIdealWeight,hz])
      _ = ∑' p : ℕ × GoodIdeal,fullIdealWeight s (lambdaFactorMap p).1 :=
        (lambdaFactorEquiv.tsum_eq _).symm
      _ = ∑' n : ℕ,∑' I : GoodIdeal,((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
        rw [hp.tsum_prod]
        apply tsum_congr; intro n
        exact tsum_congr (fun I => fullIdealWeight_lambdaFactor s n I)
      _ = ∑' n : ℕ,((3:ℂ)^(-s))^n*unramifiedIdealZeta s := by
        apply tsum_congr; intro n
        rw [tsum_mul_left]
        apply congrArg (fun z : ℂ => ((3:ℂ)^(-s))^n*z)
        apply tsum_subtype_eq_of_support_subset (f := unramifiedNormWeight s)
          (s := {I : Ideal O | primaryIdealGenerator I ≠ 0})
        intro I hI
        change primaryIdealGenerator I ≠ 0
        intro hz
        exact hI (unramifiedNormWeight_of_bad s I hz)
      _ = _ := by rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hnorm]
  rw [← fullIdealZeta_eq_dedekindZeta s hs,hfull,← mul_assoc,mul_inv_cancel₀ hne,one_mul]


lemma constantDirichletTerm_differentiable (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s 0 c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc]
    exact differentiable_const _
  · have hq : ((‖ringComplex c.1‖^2:ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc)))
    simp only [arithmeticDirichletTerm,if_neg hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma constantDirichletTerm_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s 0 c‖ ≤ ‖arithmeticDirichletTerm (a:ℂ) 0 c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc,norm_zero,le_refl]
  · have hpos : 0<‖ringComplex c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (ringComplex_ne_zero hc))
    have hq : 1≤‖ringComplex c.1‖^2 := by
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,if_neg hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_zero_differentiableAt (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z 0) s := by
  let a : ℝ := ((4:ℝ)/3+s.re)/2
  have ha : (4:ℝ)/3<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := constantDirichlet_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z 0) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (constantDirichletTerm_differentiable c).differentiableOn) hopen
    intro c z hz
    exact constantDirichletTerm_norm_mono a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

lemma unramifiedNormWeight_differentiable (I : Ideal O) :
    Differentiable ℂ (fun s : ℂ => unramifiedNormWeight s I) := by
  by_cases hI : primaryIdealGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI]
    exact differentiable_const _
  · have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal I hI))
    simp only [unramifiedNormWeight_of_good _ I hI]
    exact differentiable_id.neg.const_cpow (Or.inl hn)

lemma unramifiedNormWeight_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (I : Ideal O) :
    ‖unramifiedNormWeight s I‖≤‖unramifiedNormWeight (a:ℂ) I‖ := by
  by_cases hI : primaryIdealGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI,norm_zero,le_refl]
  · have hn : Ideal.absNorm I ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal I hI)
    have hpos : (0:ℝ)<Ideal.absNorm I := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hq : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    simp only [unramifiedNormWeight_of_good _ I hI]
    change ‖((Ideal.absNorm I:ℝ):ℂ)^(-s)‖≤‖((Ideal.absNorm I:ℝ):ℂ)^(-(a:ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    exact Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha)

theorem unramifiedIdealZeta_differentiableAt (s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ unramifiedIdealZeta s := by
  let a : ℝ := (1+s.re)/2
  have ha : 1<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := unramifiedNormWeight_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ unramifiedIdealZeta {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun I => (unramifiedNormWeight_differentiable I).differentiableOn) hopen
    intro I z hz
    exact unramifiedNormWeight_norm_mono a z hz.le I
  exact (hd s has).differentiableAt (hopen.mem_nhds has)


def unramifiedZetaResidue : ℂ :=
  (2/3:ℂ)*(NumberField.dedekindZeta_residue K:ℂ)

lemma unramifiedZetaResidue_ne_zero : unramifiedZetaResidue ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  exact Complex.ofReal_ne_zero.mpr
    (NumberField.dedekindZeta_residue_pos K).ne'

theorem unramifiedIdealZeta_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-1)*unramifiedIdealZeta (x:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) := by
  have hcont : Continuous (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) :=
    continuous_const.sub (Complex.continuous_ofReal.neg.const_cpow (Or.inl (by norm_num)))
  have heuler : Tendsto (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) (𝓝[>] (1:ℝ)) (𝓝 (2/3:ℂ)) := by
    apply (hcont.tendsto' 1 (2/3:ℂ) ?_).mono_left nhdsWithin_le_nhds
    norm_num [Complex.cpow_neg]
  have h := heuler.mul (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  change Tendsto (fun x : ℝ => (1-(3:ℂ)^(-(x:ℂ)))*
    (((x:ℂ)-1)*NumberField.dedekindZeta K (x:ℂ)))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [unramifiedIdealZeta_eq_dedekindZeta (x:ℂ) hx']
  ring

lemma cusp_volume_ne_zero : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  positivity

def constantArithmeticResidue : ℂ := unramifiedZetaResidue /
  (3*((9*Real.sqrt 3/2:ℝ):ℂ)*unramifiedIdealZeta 2)

lemma constantArithmeticResidue_ne_zero : constantArithmeticResidue ≠ 0 := by
  apply div_ne_zero unramifiedZetaResidue_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num) cusp_volume_ne_zero)
    (unramifiedIdealZeta_ne_zero 2 (by norm_num))

lemma tendsto_three_mul_sub_three_four_thirds :
    Tendsto (fun x : ℝ => 3*x-3) (𝓝[>] ((4:ℝ)/3)) (𝓝[>] (1:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply ((continuous_const.mul continuous_id).sub continuous_const).tendsto' _ _ (by norm_num)
      |>.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx ⊢
    linarith

theorem scatteringCoefficient_zero_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*scatteringCoefficient (x:ℂ) 0)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 constantArithmeticResidue) := by
  have hn0 := unramifiedIdealZeta_oneSidedResidue.comp tendsto_three_mul_sub_three_four_thirds
  have hn : Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*unramifiedIdealZeta (3*(x:ℂ)-3))
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (unramifiedZetaResidue/3)) := by
    convert hn0.div_const (3:ℂ) using 1
    ext x
    dsimp only [Function.comp_def]
    push_cast
    ring
  have harg : Tendsto (fun x : ℝ => 3*(x:ℂ)-2) (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).tendsto' _ _ ?_).mono_left
      nhdsWithin_le_nhds
    norm_num
  have hz := (unramifiedIdealZeta_differentiableAt 2 (by norm_num)).continuousAt.tendsto.comp harg
  have hdncont : Continuous (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1) :=
    (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).const_cpow
      (Or.inl (by norm_num))).sub continuous_const
  have hdn : Tendsto (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (hdncont.tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
    norm_num
  have hp := ((hdn.inv₀ (by norm_num)).const_mul
    (2/((9*Real.sqrt 3/2:ℝ):ℂ))).mul
      (hn.div hz (unramifiedIdealZeta_ne_zero 2 (by norm_num)))
  have hlimit : (2/((9*Real.sqrt 3/2:ℝ):ℂ))*(2:ℂ)⁻¹*
      ((unramifiedZetaResidue/3)/unramifiedIdealZeta 2)=constantArithmeticResidue := by
    unfold constantArithmeticResidue
    ring
  rw [hlimit] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (4:ℝ)/3<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [scatteringCoefficient_zero_zeta (x:ℂ) hx']
  dsimp only [Pi.div_apply,Function.comp_def]
  ring


#print axioms unramifiedIdealZeta_eq_dedekindZeta
#print axioms constantArithmeticResidue_ne_zero
#print axioms scatteringCoefficient_zero_oneSidedResidue
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
