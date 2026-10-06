import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicFourierLattice
import GaloisForLFunctions.RHTower.ChiCompactLatticePoisson

/-!
# Complete physical Schwartz Poisson matching

Every physical Schwartz input has an absolutely convergent twisted
three-dimensional Poisson identity at every real shift. A product lattice
majorant uniform on bounded translation regions proves normal
periodization and pays the full integration exchange. No compact support
is required; summability and Fourier interchange are proved.
-/

open MeasureTheory
noncomputable section
open scoped FourierTransform ContDiff Topology
namespace RHTower.BAGTrace

namespace FullPoisson
open scoped FourierTransform

private def triples : Z ≃ ℤ × ℤ × ℤ where
  toFun n := (n 0,n 1,n 2)
  invFun n := ![n.1,n.2.1,n.2.2]
  left_inv n := by ext i; fin_cases i <;> rfl
  right_inv n := rfl

private lemma triples_point (n : Z) : WithLp.toLp 2 (ip n)=bagIntegerTriple (triples n) := by
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> rfl

private lemma character (k : Z) (x : X) :
    UnitAddTorus.mFourier (-k) (q x) =
      Complex.exp ((-2*Real.pi*inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (ip k)) : ℝ)*Complex.I) := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,q,fourier_coe_apply,
    Pi.neg_apply,Int.cast_neg,Complex.ofReal_one,div_one,PiLp.inner_apply,
    ip]
  simp only [Fin.prod_univ_succ,Fin.sum_univ_succ,Fin.prod_univ_zero,Fin.sum_univ_zero,
    mul_one,add_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  simp only [Real.inner_apply]
  push_cast
  ring

private def twist (f : BAGPhysicalSpace → ℂ) (a : BAGPhysicalSpace) (x : X) : ℂ :=
  Complex.exp ((2*Real.pi*inner ℝ (WithLp.toLp 2 x) a : ℝ)*Complex.I)*f (WithLp.toLp 2 x)

private lemma twist_continuous (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) :
    Continuous (twist f a) := by
  unfold twist
  have ht : Continuous (WithLp.toLp 2 : X → BAGPhysicalSpace) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.continuous
  exact ((Complex.continuous_ofReal.comp (continuous_const.mul
    (ht.inner continuous_const))).mul continuous_const).cexp.mul (f.continuous.comp ht)

private lemma twist_coefficient (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) (k : Z) :
    (∫ x, UnitAddTorus.mFourier (-k) (q x)*twist f a x) =
      (𝓕 f) (WithLp.toLp 2 (ip k)-a) := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 X).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [character]
  simp only [twist,smul_eq_mul,← mul_assoc,← Complex.exp_add]
  congr 2
  rw [inner_sub_right]
  push_cast
  ring


private def weight (n : Z) : ℝ := (1+|(n 0 : ℝ)|)*(1+|(n 1 : ℝ)|)*(1+|(n 2 : ℝ)|)
private theorem weight_pos (n : Z) : 0 < weight n := by unfold weight; positivity

private theorem reciprocal_summable : Summable (fun n : Z => 1/(weight n)^2) := by
  have hn : Summable (fun n : ℕ => 1/(1+(n : ℝ))^2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    simpa only [Real.rpow_two,sq_abs,add_comm] using h
  have hz : Summable (fun n : ℤ => 1/(1+|(n : ℝ)|)^2) := by
    rw [summable_int_iff_summable_nat_and_neg]
    simpa using And.intro hn hn
  let b : ℤ → ℝ := fun n => 1/(1+|(n : ℝ)|)^2
  have hb : Summable b := hz
  have hb0 : 0 ≤ b := fun n => by dsimp only [b]; positivity
  have hbb := hb.mul_of_nonneg hb hb0 hb0
  have ht := hb.mul_of_nonneg hbb hb0 (fun n => mul_nonneg (hb0 _) (hb0 _))
  have he := ht.comp_injective triples.injective
  apply he.congr
  intro n
  change b (n 0)*(b (n 1)*b (n 2))=1/(weight n)^2
  dsimp only [weight,b]
  simp only [mul_pow,one_div,mul_inv_rev]
  ring

private theorem translated_bound (f : SchwartzMap BAGPhysicalSpace ℂ)
    (R : ℝ) (hR : 0 ≤ R) (x : X) (hx : ‖x‖ ≤ R) (n : Z) :
    ‖f (WithLp.toLp 2 (x+ip n))‖ ≤
      ((1+R)^6 * (2^6 * (Finset.Iic (6,0)).sup
        (schwartzSeminormFamily ℂ BAGPhysicalSpace ℂ) f))/(weight n)^2 := by
  let y : BAGPhysicalSpace := WithLp.toLp 2 (x+ip n)
  have hi (i : Fin 3) : 1+|(n i : ℝ)| ≤ (1+R)*(1+‖y‖) := by
    have hiX : ‖x i‖ ≤ R := (norm_le_pi_norm x i).trans hx
    have hiY : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
    have he : |(n i : ℝ)|=‖y i-x i‖ := by simp [y,ip]
    have hh : |(n i : ℝ)| ≤ ‖y‖+R := by
      rw [he]; exact (norm_sub_le _ _).trans (add_le_add hiY hiX)
    nlinarith [norm_nonneg y]
  have hw : weight n ≤ ((1+R)*(1+‖y‖))^3 := by
    calc
      _ ≤ ((1+R)*(1+‖y‖))*((1+R)*(1+‖y‖))*((1+R)*(1+‖y‖)) := by
        dsimp only [weight]
        exact mul_le_mul (mul_le_mul (hi 0) (hi 1) (by positivity) (by positivity))
          (hi 2) (by positivity) (by positivity)
      _ = _ := by ring
  have hw2 : (weight n)^2 ≤ (1+R)^6*(1+‖y‖)^6 := by
    calc
      _ ≤ (((1+R)*(1+‖y‖))^3)^2 := pow_le_pow_left₀ (weight_pos n).le hw 2
      _ = _ := by ring
  have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (6,0)) (k := 6) (n := 0) le_rfl le_rfl f y
  simp only [norm_iteratedFDeriv_zero] at hd
  apply (le_div_iff₀ (pow_pos (weight_pos n) 2)).mpr
  calc
    _ = (weight n)^2*‖f y‖ := by ring
    _ ≤ ((1+R)^6*(1+‖y‖)^6)*‖f y‖ := mul_le_mul_of_nonneg_right hw2 (norm_nonneg _)
    _ = (1+R)^6*((1+‖y‖)^6*‖f y‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

private theorem twist_norm (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) (x : X) :
    ‖twist f a x‖ = ‖f (WithLp.toLp 2 x)‖ := by
  simp [twist,Complex.norm_exp]

private theorem twist_integrable (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) :
    Integrable (twist f a) := by
  have hi : Integrable (fun x : X => f (WithLp.toLp 2 x)) :=
    ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 X).measurableEmbedding).mpr f.integrable
  exact hi.mono (twist_continuous f a).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (twist_norm f a x).le))

private theorem twist_normal (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) :
    ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ n : Z, ‖twist f a (x+ip n)‖ ≤ u n := by
  intro R hR
  let C := (1+R)^6*(2^6*(Finset.Iic (6,0)).sup
    (schwartzSeminormFamily ℂ BAGPhysicalSpace ℂ) f)
  refine ⟨fun n => C/(weight n)^2,?_,fun x hx n => ?_⟩
  · simpa only [mul_one_div] using reciprocal_summable.mul_left C
  · rw [twist_norm]
    exact translated_bound f R hR x hx n

/-- Full twisted Poisson identity for EVERY physical Schwartz input.
Absolute periodization, integration and every Fourier lift are proved;
no compact support or summability premise is accepted. -/
theorem full_schwartz_poisson (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) :
    (∑' k : ℤ × ℤ × ℤ, (𝓕 f) (bagIntegerTriple k-a)) =
      ∑' n : ℤ × ℤ × ℤ,
        Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple n) a : ℝ)*Complex.I)*f (bagIntegerTriple n) := by
  have hs : Summable (fun k : Z => (𝓕 f) (WithLp.toLp 2 (ip k)-a)) := by
    have h := (summable_norm_bagFourierIntegerTriple f (-a)).of_norm
    simpa only [Function.comp_def,triples_point,sub_eq_add_neg] using h.comp_injective triples.injective
  have h := poisson_of_summable_translates (twist_continuous f a) (twist_integrable f a)
    (twist_normal f a) (by simpa only [twist_coefficient] using hs)
  simp only [twist_coefficient] at h
  calc
    _ = ∑' k : Z, (𝓕 f) (bagIntegerTriple (triples k)-a) :=
      (triples.tsum_eq (fun k => (𝓕 f) (bagIntegerTriple k-a))).symm
    _ = ∑' n : Z, Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple (triples n)) a : ℝ)*Complex.I)*
        f (bagIntegerTriple (triples n)) := by
      simpa only [twist,triples_point] using h
    _ = _ := triples.tsum_eq (fun n : ℤ × ℤ × ℤ =>
      Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple n) a : ℝ)*Complex.I)*
        f (bagIntegerTriple n))
end FullPoisson
end RHTower.BAGTrace
