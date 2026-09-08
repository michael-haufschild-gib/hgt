import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Quadratic variation of the symmetric square-root clock

A convex reciprocal-root odd part gives an explicit slope in the squared
symmetric displacement. This retains the cancellation lost by bounding the
two square-root clock branches separately.
-/

noncomputable section
open Filter Topology
namespace RHTower

private lemma reciprocal_three_halves_odd_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/3) :
    (1-t)^(-(3:ℝ)/2)-(1+t)^(-(3:ℝ)/2) ≤ 4*t := by
  let f := fun u : ℝ => (1-u)^(-(3:ℝ)/2)-(1+u)^(-(3:ℝ)/2)
  let f' := fun u : ℝ => (3/2:ℝ)*((1-u)^(-(5:ℝ)/2)+(1+u)^(-(5:ℝ)/2))
  let f'' := fun u : ℝ => (15/4:ℝ)*((1-u)^(-(7:ℝ)/2)-(1+u)^(-(7:ℝ)/2))
  have hd (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (1/3)) : HasDerivAt f (f' u) u := by
    have hm : 1-u≠0 := by linarith [hu.2]
    have hp : 1+u≠0 := by linarith [hu.1]
    have h1 := ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).rpow_const (p:=(-(3:ℝ)/2)) (Or.inl hm)
    have h2 := ((hasDerivAt_id u).const_add 1).rpow_const (p:=(-(3:ℝ)/2)) (Or.inl hp)
    convert h1.sub h2 using 1 <;>
      first
      | rfl
      | norm_num [f,f',id_eq]
        ring
  have hdd (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (1/3)) : HasDerivAt f' (f'' u) u := by
    have hm : 1-u≠0 := by linarith [hu.2]
    have hp : 1+u≠0 := by linarith [hu.1]
    have h1 := ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).rpow_const (p:=(-(5:ℝ)/2)) (Or.inl hm)
    have h2 := ((hasDerivAt_id u).const_add 1).rpow_const (p:=(-(5:ℝ)/2)) (Or.inl hp)
    convert (h1.add h2).const_mul (3/2:ℝ) using 1 <;>
      first
      | rfl
      | norm_num [f',f'',id_eq]
        ring
  have hc : ConvexOn ℝ (Set.Icc (0:ℝ) (1/3)) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 (1/3))
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu; exact (hdd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      have hu' := interior_subset hu
      have h := Real.rpow_le_rpow_of_nonpos (by linarith [hu'.2] : (0:ℝ)<1-u)
        (by linarith [hu'.1] : 1-u ≤ 1+u) (by norm_num : (-(7:ℝ)/2) ≤ 0)
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr h)
  have hpow (x : ℝ) (hx : 0<x) : (x^(-(3:ℝ)/2))^2=(x^3)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg,Real.rpow_ofNat]
    first
    | exact Real.rpow_ofNat x 3
    | exact (Real.rpow_ofNat x 3).symm
    | rfl
  have hA := hpow (2/3) (by norm_num)
  have hB := hpow (4/3) (by norm_num)
  norm_num at hA hB
  have hpA := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2/3) (-(3:ℝ)/2)
  have hpB := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<4/3) (-(3:ℝ)/2)
  have he : f (1/3) ≤ (4/3:ℝ) := by
    dsimp [f]
    norm_num only
    have h1 : (2/3:ℝ)^(-(3:ℝ)/2) ≤ 37/20 := by nlinarith only [hA,hpA]
    have h2 : (3/5:ℝ) ≤ (4/3:ℝ)^(-(3:ℝ)/2) := by nlinarith only [hB,hpB]
    linarith only [h1,h2]
  have h := hc.2 (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) (1/3))
    (by norm_num : (1/3:ℝ) ∈ Set.Icc (0:ℝ) (1/3))
    (by linarith : 0 ≤ 1-3*t) (by positivity : 0 ≤ 3*t) (by ring : 1-3*t+3*t=1)
  simp only [smul_eq_mul,mul_zero,zero_add] at h
  rw [show 3*t*(1/3)=t by ring] at h
  have hz : f 0=0 := by simp [f]
  rw [hz,mul_zero,zero_add] at h
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 3*t by positivity)
  exact h.trans (by nlinarith only [hmul])

private lemma scaled_reciprocal_odd_le {x t : ℝ} (hx : 0<x) (ht0 : 0 ≤ t)
    (htx : t ≤ x/3) :
    (x-t)^(-(3:ℝ)/2)-(x+t)^(-(3:ℝ)/2) ≤ 4*t*x^(-(5:ℝ)/2) := by
  have h := reciprocal_three_halves_odd_le (t:=t/x) (by positivity)
    (by rw [div_le_iff₀ hx]; linarith)
  have hm : 0 ≤ 1-t/x := by rw [sub_nonneg,div_le_one hx]; linarith
  have hp : 0 ≤ 1+t/x := by positivity
  have h1 : x-t=x*(1-t/x) := by field_simp
  have h2 : x+t=x*(1+t/x) := by field_simp
  have he : x^(-(3:ℝ)/2)/x=x^(-(5:ℝ)/2) := by
    rw [div_eq_mul_inv,← Real.rpow_neg_one,← Real.rpow_add hx]
    norm_num
  rw [h1,h2,Real.mul_rpow hx.le hm,Real.mul_rpow hx.le hp]
  have hh := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le (-(3:ℝ)/2))
  have hh' : x^(-(3:ℝ)/2)*(4*(t/x))=4*t*x^(-(5:ℝ)/2) := by
    rw [← he]
    ring
  nlinarith only [hh,hh']

private def evenReciprocalRoot (x t : ℝ) : ℝ :=
  ((x-t)^(-(1:ℝ)/2)+(x+t)^(-(1:ℝ)/2))/2

private lemma even_reciprocal_root_lipschitz {x i j : ℝ} (hx : 0<x)
    (hi : 0 ≤ i) (hij : i ≤ j) (hj : j ≤ x/3) :
    evenReciprocalRoot x j-evenReciprocalRoot x i ≤
      (j^2-i^2)*x^(-(5:ℝ)/2)/2 := by
  let f := fun t : ℝ => evenReciprocalRoot x t-t^2*x^(-(5:ℝ)/2)/2
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (x/3)) :
      HasDerivAt f (((x-t)^(-(3:ℝ)/2)-(x+t)^(-(3:ℝ)/2))/4-
        t*x^(-(5:ℝ)/2)) t := by
    have hm : x-t≠0 := by linarith [ht.2]
    have hp : x+t≠0 := by linarith [ht.1]
    have h1 := ((hasDerivAt_const t x).sub (hasDerivAt_id t)).rpow_const (p:=(-(1:ℝ)/2)) (Or.inl hm)
    have h2 := ((hasDerivAt_id t).const_add x).rpow_const (p:=(-(1:ℝ)/2)) (Or.inl hp)
    have h3 := (((hasDerivAt_id t).pow 2).mul_const (x^(-(5:ℝ)/2))).div_const 2
    convert ((h1.add h2).div_const 2).sub h3 using 1 <;>
      first
      | rfl
      | norm_num [f,evenReciprocalRoot,id_eq]
        ring
  have hm : AntitoneOn f (Set.Icc (0:ℝ) (x/3)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (x/3))
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hd t ht').deriv]
      have h := scaled_reciprocal_odd_le hx ht'.1 ht'.2
      linarith only [h]
  have h := hm ⟨hi,hij.trans hj⟩ ⟨hi.trans hij,hj⟩ hij
  dsimp [f] at h
  nlinarith only [h]

private def evenRoot (x t : ℝ) : ℝ :=
  ((x-t)^((1:ℝ)/2)+(x+t)^((1:ℝ)/2))/2

private lemma evenRoot_deriv {x t : ℝ} (ht : |t|<x) :
    HasDerivAt (fun u => evenRoot u t) (evenReciprocalRoot x t/2) x := by
  have hm : x-t≠0 := by have := le_abs_self t; linarith
  have hp : x+t≠0 := by have := neg_le_abs t; linarith
  have h1 := ((hasDerivAt_id x).sub_const t).rpow_const (p:=((1:ℝ)/2)) (Or.inl hm)
  have h2 := ((hasDerivAt_id x).add_const t).rpow_const (p:=((1:ℝ)/2)) (Or.inl hp)
  convert (h1.add h2).div_const 2 using 1 <;>
    first
    | rfl
    | norm_num [evenRoot,evenReciprocalRoot,id_eq]
      ring

/-- The even square-root clock changes by at most the stated quadratic
slope on the central third of its positive domain. -/
theorem symmetricSqrtStep_quadratic_lipschitz {c i j : ℝ} (hc : 0<c)
    (hi : 0 ≤ i) (hij : i ≤ j) (hj : j ≤ c/3) :
    ((Real.sqrt (c-j+1)-Real.sqrt (c-j))+(Real.sqrt (c+j+1)-Real.sqrt (c+j)))/2-
      ((Real.sqrt (c-i+1)-Real.sqrt (c-i))+(Real.sqrt (c+i+1)-Real.sqrt (c+i)))/2 ≤
        (j^2-i^2)*c^(-(5:ℝ)/2)/4 := by
  let L := (j^2-i^2)*c^(-(5:ℝ)/2)/4
  let f := fun x => evenRoot x j-evenRoot x i-L*x
  have hsq : 0 ≤ j^2-i^2 := by nlinarith
  have hd (x : ℝ) (hx : c ≤ x) :
      HasDerivAt f ((evenReciprocalRoot x j-evenReciprocalRoot x i)/2-L) x := by
    have hjx : |j|<x := by rw [abs_of_nonneg (hi.trans hij)]; linarith
    have hix : |i|<x := by rw [abs_of_nonneg hi]; linarith
    convert ((evenRoot_deriv hjx).sub (evenRoot_deriv hix)).sub
      ((hasDerivAt_id x).const_mul L) using 1 <;>
      first
      | rfl
      | ring
  have hm : AntitoneOn f (Set.Ici c) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici c)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have hx0 : 0<x := hc.trans_le hx'
      rw [(hd x hx').deriv]
      have h := even_reciprocal_root_lipschitz hx0 hi hij (by have hxle : c ≤ x := hx'; linarith)
      have hp := Real.rpow_le_rpow_of_nonpos hc hx' (by norm_num : (-(5:ℝ)/2) ≤ 0)
      have hh := mul_le_mul_of_nonneg_left hp hsq
      dsimp [L]
      nlinarith only [h,hh]
  have h := hm (show c ∈ Set.Ici c by simp) (show c+1 ∈ Set.Ici c by simp) (by linarith)
  dsimp [f,evenRoot,L] at h
  simp only [← Real.sqrt_eq_rpow] at h
  rw [show c+1-j=c-j+1 by ring,show c+1+j=c+j+1 by ring,
    show c+1-i=c-i+1 by ring,show c+1+i=c+i+1 by ring] at h
  nlinarith only [h]

end RHTower
