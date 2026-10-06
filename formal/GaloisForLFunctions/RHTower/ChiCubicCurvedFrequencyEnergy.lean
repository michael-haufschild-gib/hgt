import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Uniform energy of the curved physical height phase

The exact physical Fourier multiplier exposes the curved frequency
`a*v + b*u + lam*a*b`. On the full strip `|lam*a| ≤ 1/4`, its coefficient
in `b` remains bounded away from zero for `u,v ∈ [1,2]`.

Partitioning by the smallest of `1+|a|`, `1+|b|`, and the curved frequency
size bounds the weighted energy by three integrable products. An affine
slice substitution controls the third uniformly. This proves all orders
`0 ≤ s < 3/2`, in particular an order strictly above one.

This is the scalar energy ingredient for the actual moving physical
profile. Exact multiplier transfer, cutoff derivative budgets and tails
remain separate obligations; no physical saving or RH conclusion follows.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower.BAGTrace

private theorem comparable_energy {T X Y Z e : ℝ}
    (hT : 0<T) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (he : 0≤e)
    (hTX : T≤7*X) (hXZ : X≤6*Z) :
    T^e/(X^2*Y^2*Z^2)≤36*(7 : ℝ)^e*Y^(-2 : ℝ)*X^(e-4) := by
  have hp : T^e≤(7 : ℝ)^e*X^e := by
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ)≤7) hX.le] using
      Real.rpow_le_rpow hT.le hTX he
  have hz : (1 : ℝ)/Z^2≤36/X^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hZ) (sq_pos_of_pos hX)).mpr
    have hh := pow_le_pow_left₀ hX.le hXZ 2
    nlinarith only [hh]
  calc T^e/(X^2*Y^2*Z^2) = (T^e/X^2/Y^2)*(1/Z^2) := by ring
       _ ≤ (((7 : ℝ)^e*X^e)/X^2/Y^2)*(36/X^2) := by
         apply mul_le_mul
         · exact div_le_div_of_nonneg_right
             (div_le_div_of_nonneg_right hp (sq_nonneg _)) (sq_nonneg _)
         · exact hz
         · positivity
         · positivity
       _ = _ := by
         rw [Real.rpow_neg hY.le,Real.rpow_two,Real.rpow_sub hX]
         norm_num only [Real.rpow_ofNat]
         field_simp

private def frequencySize (a : ℝ) : ℝ := 1+|a|

private theorem frequencySize_pos (a : ℝ) : 0<frequencySize a := by
  unfold frequencySize
  positivity

private def curvedFrequency (lam u v a b : ℝ) : ℝ := a*v+b*u+lam*a*b

private theorem curved_comparisons {lam u v a b : ℝ}
    (hu : u∈Icc (1 : ℝ) 2) (hv : v∈Icc (1 : ℝ) 2) (ha : |lam*a| ≤1/4) :
    frequencySize a≤3*(frequencySize b+frequencySize (curvedFrequency lam u v a b)) ∧
    frequencySize b≤3*(frequencySize a+frequencySize (curvedFrequency lam u v a b)) ∧
    3/4≤u+lam*a ∧ u+lam*a≤9/4 := by
  let U := u+lam*a
  let D := curvedFrequency lam u v a b
  have hUlo : 3/4≤U := by dsimp [U]; linarith [(abs_le.mp ha).1,hu.1]
  have hUhi : U≤9/4 := by dsimp [U]; linarith [(abs_le.mp ha).2,hu.2]
  have hU : 0<U := by linarith only [hUlo]
  have hV : 0<v := by linarith only [hv.1]
  have he : D=a*v+b*U := by dsimp [D,U,curvedFrequency]; ring
  have ha' : |a| *v≤|D|+|b| *U := by
    calc |a| *v = |a*v| := by rw [abs_mul,abs_of_pos hV]
         _ = |D-b*U| := by rw [he]; ring_nf
         _ ≤ |D|+|b*U| := abs_sub _ _
         _ = _ := by rw [abs_mul,abs_of_pos hU]
  have hb' : |b| *U≤|D|+|a| *v := by
    calc |b| *U = |b*U| := by rw [abs_mul,abs_of_pos hU]
         _ = |D-a*v| := by rw [he]; ring_nf
         _ ≤ |D|+|a*v| := abs_sub _ _
         _ = _ := by rw [abs_mul,abs_of_pos hV]
  have hamin : |a| ≤|a| *v := by nlinarith only [hv.1,abs_nonneg a]
  have hbmax := mul_le_mul_of_nonneg_left hUhi (abs_nonneg b)
  have hbmin := mul_le_mul_of_nonneg_left hUlo (abs_nonneg b)
  have hamax := mul_le_mul_of_nonneg_left hv.2 (abs_nonneg a)
  refine ⟨?_,?_,hUlo,hUhi⟩
  · change 1+|a| ≤3*((1+|b|)+(1+|D|))
    linarith only [ha',hamin,hbmax,abs_nonneg b,abs_nonneg D]
  · change 1+|b| ≤3*((1+|a|)+(1+|D|))
    linarith only [hb',hbmin,hamax,abs_nonneg a,abs_nonneg D]

private theorem three_term_energy {T A B C e : ℝ}
    (hT : 0<T) (hA : 0<A) (hB : 0<B) (hC : 0<C) (he : 0≤e)
    (hTsum : T≤A+B) (hAB : A≤3*(B+C)) (hBA : B≤3*(A+C)) :
    T^e/(A^2*B^2*C^2) ≤ 36*(7 : ℝ)^e *
      (A^(-2 : ℝ)*B^(e-4)+A^(e-4)*B^(-2 : ℝ)+A^(e-4)*C^(-2 : ℝ)) := by
  have hK : 0≤36*(7 : ℝ)^e := by positivity
  have h1 : 0≤A^(-2 : ℝ)*B^(e-4) := by positivity
  have h2 : 0≤A^(e-4)*B^(-2 : ℝ) := by positivity
  have h3 : 0≤A^(e-4)*C^(-2 : ℝ) := by positivity
  rcases le_total A B with hab | hba
  · rcases le_total A C with hac | hca
    · have h := comparable_energy hT hB hA hC he
        (by linarith only [hTsum,hab,hB]) (by linarith only [hBA,hac])
      have hd : B^2*A^2*C^2=A^2*B^2*C^2 := by ring
      rw [hd] at h
      nlinarith only [h,hK,h2,h3]
    · have h := comparable_energy hT hA hC hB he
        (by linarith only [hTsum,hBA,hca]) (by linarith only [hAB,hca,hab])
      have hd : A^2*C^2*B^2=A^2*B^2*C^2 := by ring
      rw [hd] at h
      nlinarith only [h,hK,h1,h2]
  · rcases le_total B C with hbc | hcb
    · have h := comparable_energy hT hA hB hC he
        (by linarith only [hTsum,hba,hA]) (by linarith only [hAB,hbc])
      nlinarith only [h,hK,h1,h3]
    · have h := comparable_energy hT hA hC hB he
        (by linarith only [hTsum,hba,hA]) (by linarith only [hAB,hcb])
      have hd : A^2*C^2*B^2=A^2*B^2*C^2 := by ring
      rw [hd] at h
      nlinarith only [h,hK,h1,h2]

private theorem frequencySize_continuous : Continuous frequencySize := by
  unfold frequencySize
  fun_prop

private def frequencyPower (e a : ℝ) : ℝ := frequencySize a ^ e

private theorem frequencyPower_pos (e a : ℝ) : 0<frequencyPower e a :=
  Real.rpow_pos_of_pos (frequencySize_pos a) _

private theorem frequencyPower_continuous (e : ℝ) : Continuous (frequencyPower e) :=
  frequencySize_continuous.rpow_const (fun a => Or.inl (frequencySize_pos a).ne')

private theorem frequencyPower_integrable {e : ℝ} (he : e< -1) :
    Integrable (frequencyPower e) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := -e) (by simpa using (show (1 : ℝ)< -e by linarith))
  change Integrable (fun x : ℝ => (1+|x|)^e)
  simpa only [neg_neg,Real.norm_eq_abs] using h

private theorem affine_power_integrable (d U : ℝ) (hU : 0<U) :
    Integrable (fun b => frequencyPower (-2) (d+U*b)) :=
  ((frequencyPower_integrable (by norm_num : (-2 : ℝ)< -1)).comp_add_left d).comp_mul_left' hU.ne'

private theorem affine_power_integral (d U : ℝ) :
    (∫ b : ℝ, frequencyPower (-2) (d+U*b)) =
      |U⁻¹| *(∫ b : ℝ, frequencyPower (-2) b) := by
  rw [Measure.integral_comp_mul_left (fun b => frequencyPower (-2) (d+b)) U,
    integral_add_left_eq_self]
  rfl

private theorem affine_energy_integrable_bound {e : ℝ} (he : e< -1)
    (U : ℝ→ℝ) (hUc : Continuous U) (hU : ∀a, (3 : ℝ)/4≤U a) (v : ℝ) :
    Integrable (fun w : ℝ×ℝ => frequencyPower e w.1 *
      frequencyPower (-2) (w.1*v+U w.1*w.2)) ∧
    (∫ w : ℝ×ℝ, frequencyPower e w.1 *
      frequencyPower (-2) (w.1*v+U w.1*w.2)) ≤
      (4/3)*(∫ a : ℝ, frequencyPower e a)*(∫ b : ℝ, frequencyPower (-2) b) := by
  let J := ∫ b : ℝ, frequencyPower (-2) b
  let f := fun w : ℝ×ℝ => frequencyPower e w.1 *
    frequencyPower (-2) (w.1*v+U w.1*w.2)
  have hJ : 0≤J := integral_nonneg (fun b => (frequencyPower_pos _ b).le)
  have hUp (a : ℝ) : 0<U a := lt_of_lt_of_le (by norm_num) (hU a)
  have hi (a : ℝ) : |(U a)⁻¹| ≤ (4 : ℝ)/3 := by
    rw [abs_of_pos (inv_pos.mpr (hUp a))]
    apply (inv_le_comm₀ (hUp a) (by norm_num)).mpr
    norm_num
    exact hU a
  have hfc : Continuous f := by
    exact ((frequencyPower_continuous e).comp continuous_fst).mul
      ((frequencyPower_continuous (-2)).comp
        ((continuous_fst.mul continuous_const).add
          ((hUc.comp continuous_fst).mul continuous_snd)))
  have hfi (a : ℝ) : Integrable (fun b : ℝ => f (a,b)) :=
    (affine_power_integrable (a*v) (U a) (hUp a)).const_mul (frequencyPower e a)
  have hfn (w : ℝ×ℝ) : 0≤f w :=
    mul_nonneg (frequencyPower_pos _ _).le (frequencyPower_pos _ _).le
  have heq (a : ℝ) : (∫ b : ℝ, f (a,b)) = frequencyPower e a * |(U a)⁻¹| * J := by
    dsimp only [f]
    rw [integral_const_mul,affine_power_integral,mul_assoc]
  have hbound (a : ℝ) : frequencyPower e a * |(U a)⁻¹| * J ≤
      ((4/3)*J)*frequencyPower e a := by
    nlinarith only [hi a,(frequencyPower_pos e a).le,hJ,
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hi a) (frequencyPower_pos e a).le) hJ]
  have houter : Integrable (fun a : ℝ => ∫ b : ℝ, ‖f (a,b)‖) := by
    have hc : Continuous (fun a : ℝ => frequencyPower e a * |(U a)⁻¹| * J) :=
      ((frequencyPower_continuous e).mul ((hUc.inv₀ (fun a => (hUp a).ne')).abs)).mul continuous_const
    have hh := ((frequencyPower_integrable he).const_mul ((4/3)*J)).mono'
      hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun a => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg
          (frequencyPower_pos e a).le (abs_nonneg _)) hJ)]
        exact hbound a))
    refine hh.congr (Filter.Eventually.of_forall (fun a => ?_))
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hfn _),heq]
  have hIf : Integrable f := by
    exact (integrable_prod_iff hfc.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hfi,houter⟩
  refine ⟨hIf,?_⟩
  change (∫ w : ℝ×ℝ, f w ∂volume.prod volume) ≤ _
  rw [integral_prod _ hIf]
  calc (∫ a : ℝ, ∫ b : ℝ, f (a,b))
      ≤ ∫ a : ℝ, ((4/3)*J)*frequencyPower e a := by
        apply integral_mono_ae hIf.integral_prod_left
          ((frequencyPower_integrable he).const_mul _)
        exact Filter.Eventually.of_forall (fun a => by dsimp only; rw [heq]; exact hbound a)
    _ = _ := by rw [integral_const_mul]; dsimp [J]; ring

/-- The curved height-phase energy is uniformly integrable on its full nondegenerate
frequency strip, including zero curvature. The constant is independent of curvature
and of both physical frequencies in the original unit height band. -/
theorem bagCubicCurvedFrequency_uniform_strip_energy (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)}) :
    ∃ C : ℝ, 0<C ∧ ∀ lam : ℝ, ∀ u v : {r : ℝ // r∈Icc (1 : ℝ) 2},
      IntegrableOn (fun w : ℝ×ℝ =>
        (1+|w.1|+|w.2|)^(2*s.1) /
          ((1+|w.1|)^2*(1+|w.2|)^2*
            (1+|w.1*v.1+w.2*u.1+lam*w.1*w.2|)^2))
        {w : ℝ×ℝ | |lam*w.1|≤1/4} ∧
      (∫ w : ℝ×ℝ in {w : ℝ×ℝ | |lam*w.1|≤1/4},
        (1+|w.1|+|w.2|)^(2*s.1) /
          ((1+|w.1|)^2*(1+|w.2|)^2*
            (1+|w.1*v.1+w.2*u.1+lam*w.1*w.2|)^2)) ≤ C := by
  let e := 2*s.1-4
  let I := ∫ a : ℝ, frequencyPower e a
  let J := ∫ a : ℝ, frequencyPower (-2) a
  let K := 36*(7 : ℝ)^(2*s.1)
  have he : e< -1 := by dsimp [e]; linarith only [s.2.2]
  have hpI := frequencyPower_integrable he
  have hpJ := frequencyPower_integrable (by norm_num : (-2 : ℝ)< -1)
  have hI : 0≤I := integral_nonneg (fun a => (frequencyPower_pos _ a).le)
  have hJ : 0≤J := integral_nonneg (fun a => (frequencyPower_pos _ a).le)
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨1+K*(I*J+I*J+(4/3)*I*J),by positivity,?_⟩
  intro lam u v
  let U := fun a : ℝ => max (3/4) (u.1+lam*a)
  let D := fun w : ℝ×ℝ => curvedFrequency lam u.1 v.1 w.1 w.2
  let S := {w : ℝ×ℝ | |lam*w.1|≤1/4}
  let f := fun w : ℝ×ℝ => (1+|w.1|+|w.2|)^(2*s.1) /
    (frequencySize w.1^2*frequencySize w.2^2*frequencySize (D w)^2)
  let g1 := fun w : ℝ×ℝ => frequencyPower (-2) w.1*frequencyPower e w.2
  let g2 := fun w : ℝ×ℝ => frequencyPower e w.1*frequencyPower (-2) w.2
  let g3 := fun w : ℝ×ℝ => frequencyPower e w.1*
    frequencyPower (-2) (w.1*v.1+U w.1*w.2)
  let g := fun w => g1 w+g2 w+g3 w
  have hU : ∀ a : ℝ, (3 : ℝ)/4≤U a := fun a => le_max_left _ _
  have hUc : Continuous U := by dsimp [U]; fun_prop
  obtain ⟨hg3,hg3bound⟩ := affine_energy_integrable_bound he U hUc hU v.1
  have hg1 : Integrable g1 := hpJ.mul_prod hpI
  have hg2 : Integrable g2 := hpI.mul_prod hpJ
  have hg : Integrable g := (hg1.add hg2).add hg3
  have hgn (w : ℝ×ℝ) : 0≤g w := by
    dsimp [g,g1,g2,g3]
    exact add_nonneg (add_nonneg
      (mul_nonneg (frequencyPower_pos _ _).le (frequencyPower_pos _ _).le)
      (mul_nonneg (frequencyPower_pos _ _).le (frequencyPower_pos _ _).le))
      (mul_nonneg (frequencyPower_pos _ _).le (frequencyPower_pos _ _).le)
  have hS : MeasurableSet S := by
    exact measurableSet_le (by fun_prop) measurable_const
  have hfc : Continuous f := by
    have htop : Continuous (fun w : ℝ×ℝ => 1+|w.1|+|w.2|) := by fun_prop
    have hnum := htop.rpow_const (p := 2*s.1) (fun w => Or.inl (by positivity))
    refine hnum.div ?_ ?_
    · dsimp [frequencySize,D,curvedFrequency]
      fun_prop
    · intro w
      exact ne_of_gt (mul_pos (mul_pos (sq_pos_of_pos (frequencySize_pos _))
        (sq_pos_of_pos (frequencySize_pos _))) (sq_pos_of_pos (frequencySize_pos _)))
  have hfn (w : ℝ×ℝ) : 0≤f w := by
    dsimp [f]
    apply div_nonneg (Real.rpow_nonneg (by positivity) _)
    positivity
  have hpoint (w : ℝ×ℝ) (hw : w∈S) : f w≤K*g w := by
    obtain ⟨hAB,hBA,hUlo,_⟩ := curved_comparisons u.2 v.2 hw
    have hclip : U w.1=u.1+lam*w.1 := max_eq_right hUlo
    have hD : w.1*v.1+U w.1*w.2=D w := by
      rw [hclip]; dsimp [D,curvedFrequency]; ring
    have hh := three_term_energy (by positivity : (0 : ℝ)<1+|w.1|+|w.2|)
      (frequencySize_pos w.1) (frequencySize_pos w.2) (frequencySize_pos (D w))
      (by linarith only [s.2.1] : 0≤2*s.1)
      (by dsimp [frequencySize]; linarith : 1+|w.1|+|w.2|≤frequencySize w.1+frequencySize w.2)
      hAB hBA
    dsimp [f,g,g1,g2,g3,frequencyPower,K,e]
    rw [hD]
    exact hh
  have hindn (w : ℝ×ℝ) : 0≤S.indicator f w := by
    by_cases hw : w∈S
    · rw [Set.indicator_of_mem hw]; exact hfn w
    · rw [Set.indicator_of_notMem hw]
  have hind (w : ℝ×ℝ) : S.indicator f w≤K*g w := by
    by_cases hw : w∈S
    · rw [Set.indicator_of_mem hw]; exact hpoint w hw
    · rw [Set.indicator_of_notMem hw]; exact mul_nonneg hK.le (hgn w)
  have hfI : Integrable (S.indicator f) :=
    (hg.const_mul K).mono' (hfc.aestronglyMeasurable.indicator hS)
      (Filter.Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hindn w)]; exact hind w))
  have hg1int : (∫ w : ℝ×ℝ, g1 w)=I*J := by
    change (∫ w : ℝ×ℝ, frequencyPower (-2) w.1*frequencyPower e w.2
      ∂volume.prod volume)=I*J
    rw [integral_prod_mul]; exact mul_comm _ _
  have hg2int : (∫ w : ℝ×ℝ, g2 w)=I*J := by
    exact integral_prod_mul (frequencyPower e) (frequencyPower (-2))
  refine ⟨(integrable_indicator_iff hS).mp hfI,?_⟩
  change (∫ w : ℝ×ℝ in S, f w)≤_
  rw [← integral_indicator hS]
  calc (∫ w : ℝ×ℝ, S.indicator f w) ≤ ∫ w : ℝ×ℝ, K*g w :=
      integral_mono_ae hfI (hg.const_mul K) (Filter.Eventually.of_forall hind)
    _ = K*((∫ w : ℝ×ℝ, g1 w)+(∫ w : ℝ×ℝ, g2 w)+(∫ w : ℝ×ℝ, g3 w)) := by
      rw [integral_const_mul]
      change K*(∫ w : ℝ×ℝ, (g1+g2) w+g3 w)=_
      rw [integral_add (hg1.add hg2) hg3]
      simp only [Pi.add_apply]
      rw [integral_add hg1 hg2]
    _ ≤ 1+K*(I*J+I*J+(4/3)*I*J) := by
      rw [hg1int,hg2int]
      have hh := mul_le_mul_of_nonneg_left hg3bound hK.le
      change K*(∫ w : ℝ×ℝ, g3 w)≤K*((4/3)*I*J) at hh
      linarith only [hh]

end RHTower.BAGTrace
