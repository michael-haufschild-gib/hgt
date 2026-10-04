import GaloisForLFunctions.RHTower.ChiRamanujanSchwartzSourceDecay
import GaloisForLFunctions.RHTower.ChiRamanujanCubicCompensatedBoundary

/-!
# Uniform integrable envelopes for the actual BAG cubic quotients

Short-segment cancellation preserves transverse Schwartz decay. A four-region
argument controls the product principal value, including both unbounded strips.
Exact reflection extends both estimates to the full plane, with one finite
Schwartz seminorm and the integrable Cauchy product density.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff SchwartzMap
namespace RHTower.BAGTrace

private theorem norm_rectangular_difference_le
    {f : (Fin 3 → ℝ) → ℂ} {S : Set (Fin 3 → ℝ)} {C : ℝ}
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hdf : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hb : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C)
    (hS : Convex ℝ S) (x h k : Fin 3 → ℝ)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, x+t•k ∈ S ∧ x+t•k+h ∈ S) :
    ‖f (x+k+h)-f (x+k)-f (x+h)+f x‖ ≤ C*‖h‖*‖k‖ := by
  let g : ℝ → ℂ := fun t => f (x+t•k+h)-f (x+t•k)
  let d : ℝ → ℂ := fun t => (fderiv ℝ f (x+t•k+h)-fderiv ℝ f (x+t•k)) k
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (d t) t := by
    have hpath : HasDerivAt (fun s : ℝ => x+s•k) k t := by
      simpa using ((hasDerivAt_id t).smul_const k).const_add x
    have ha := (hf _ (hp t ht).2).hasFDerivAt.comp_hasDerivAt t (hpath.add_const h)
    have hb' := (hf _ (hp t ht).1).hasFDerivAt.comp_hasDerivAt t hpath
    convert ha.sub hb' using 1 <;> rfl
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖d t‖ ≤ C*‖h‖*‖k‖ := by
    have hdiff := hS.norm_image_sub_le_of_norm_fderiv_le hdf hb (hp t ht).1 (hp t ht).2
    simp only [add_sub_cancel_left] at hdiff
    exact (ContinuousLinearMap.le_opNorm _ k).trans
      (mul_le_mul_of_nonneg_right hdiff (norm_nonneg k))
  have hres := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hd
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simp only [g, one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one] at hres
  convert hres using 1
  congr 1
  abel

private theorem norm_u_vector_le {u : ℝ} (hu : 0 ≤ u) : ‖(![0,u,0] : Fin 3 → ℝ)‖ ≤ u := by
  apply (pi_norm_le_iff_of_nonneg hu).2
  intro i
  fin_cases i <;> simp [Real.norm_eq_abs, abs_of_nonneg hu, hu]

private theorem norm_v_vector_le {v : ℝ} (hv : 0 ≤ v) : ‖(![0,0,v] : Fin 3 → ℝ)‖ ≤ v := by
  apply (pi_norm_le_iff_of_nonneg hv).2
  intro i
  fin_cases i <;> simp [Real.norm_eq_abs, abs_of_nonneg hv, hv]


private theorem norm_second_eq (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  simpa only [norm_iteratedFDeriv_one] using (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := f) (x := x))

private theorem norm_central_difference_fixed_transverse
    {f : (Fin 3 → ℝ) → ℂ} {σ u v C : ℝ} (hu : 0 ≤ u) (hC : 0 ≤ C)
    (hf : ∀ a b : ℝ, ContDiffAt ℝ ∞ f ![σ,a,b])
    (hb : ∀ a ∈ Icc (-u) u, ‖fderiv ℝ (fderiv ℝ f) ![σ,a,v]‖ ≤ C)
    (hzero : f ![σ,0,v]=0) : ‖f ![σ,u,v]+f ![σ,-u,v]‖ ≤ C*u^2 := by
  let S : Set (Fin 3 → ℝ) := Icc ![σ,-u,v] ![σ,u,v]
  have hcoords {x : Fin 3 → ℝ} (hx : x ∈ S) : x=![σ,x 1,v] ∧ x 1 ∈ Icc (-u) u := by
    have h0 : x 0=σ := le_antisymm (hx.2 0) (hx.1 0)
    have h2 : x 2=v := le_antisymm (hx.2 2) (hx.1 2)
    refine ⟨?_,⟨hx.1 1,hx.2 1⟩⟩
    ext i
    fin_cases i <;> simp_all
  have hfs (x : Fin 3 → ℝ) (hx : x ∈ S) : ContDiffAt ℝ ∞ f x := by
    rw [(hcoords hx).1]
    exact hf _ _
  have hbs (x : Fin 3 → ℝ) (hx : x ∈ S) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
    rw [(hcoords hx).1]
    exact hb _ (hcoords hx).2
  have hmem (a : ℝ) (ha : a ∈ Icc (-u) u) : (![σ,a,v] : Fin 3 → ℝ) ∈ S := by
    constructor
    · intro i; fin_cases i
      · exact le_rfl
      · exact ha.1
      · exact le_rfl
    · intro i; fin_cases i
      · exact le_rfl
      · exact ha.2
      · exact le_rfl
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ![σ,-u,v]+t•![0,u,0] ∈ S ∧ ![σ,-u,v]+t•![0,u,0]+![0,u,0] ∈ S := by
    have ht0 : 0 ≤ t*u := mul_nonneg ht.1 hu
    have ht1 : t*u ≤ u := mul_le_of_le_one_left hu ht.2
    have e1 : (![σ,-u,v]+t•![0,u,0] : Fin 3 → ℝ) = ![σ,-u+t*u,v] := by
      ext i; fin_cases i <;> simp
    have e2 : (![σ,-u,v]+t•![0,u,0]+![0,u,0] : Fin 3 → ℝ) = ![σ,t*u,v] := by
      ext i; fin_cases i <;> simp
    rw [e2,e1]
    exact ⟨hmem _ ⟨by linarith,by linarith⟩,hmem _ ⟨by linarith,ht1⟩⟩
  have h := norm_rectangular_difference_le
    (fun x hx => (hfs x hx).differentiableAt (by simp))
    (fun x hx => ((hfs x hx).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    hbs (convex_Icc _ _) ![σ,-u,v] ![0,u,0] ![0,u,0] hpath
  have e1 : (![σ,-u,v]+![0,u,0]+![0,u,0] : Fin 3 → ℝ) = ![σ,u,v] := by
    ext i; fin_cases i <;> simp
  have e2 : (![σ,-u,v]+![0,u,0] : Fin 3 → ℝ) = ![σ,0,v] := by
    ext i; fin_cases i <;> simp
  rw [e1,e2,hzero,sub_zero,sub_zero] at h
  have he := mul_le_mul (mul_le_mul_of_nonneg_left (norm_u_vector_le hu) hC)
    (norm_u_vector_le hu) (norm_nonneg _) (mul_nonneg hC hu)
  exact h.trans (by simpa only [pow_two,mul_assoc] using he)

private theorem cauchy_product_denominator_le (u v : ℝ) :
    (1+u^2)*(1+v^2) ≤ (1+|u|+|v|)^4 := by
  have hu : 1+u^2 ≤ (1+|u|)^2 := by nlinarith [sq_abs u,abs_nonneg u]
  have hv : 1+v^2 ≤ (1+|v|)^2 := by nlinarith [sq_abs v,abs_nonneg v]
  have hTu : (1+|u|)^2 ≤ (1+|u|+|v|)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg v]) 2
  have hTv : (1+|v|)^2 ≤ (1+|u|+|v|)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg u]) 2
  calc
    _ ≤ (1+|u|+|v|)^2*(1+|u|+|v|)^2 :=
      mul_le_mul (hu.trans hTu) (hv.trans hTv) (by positivity) (by positivity)
    _ = _ := by ring

private theorem density_eq_inv_denominator (u v : ℝ) :
    cubicIntersectionDensity (u,v) = ((1+u^2)*(1+v^2))⁻¹ := by
  simp only [cubicIntersectionDensity,mul_inv]

private theorem norm_axis_quotient_le_density
    {f : (Fin 3 → ℝ) → ℂ} {σ B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ u v : ℝ, ContDiffAt ℝ ∞ f ![σ,u,v])
    (h0 : ∀ u v : ℝ, (1+|u|+|v|)^4*‖f ![σ,u,v]‖ ≤ B)
    (h2 : ∀ u v : ℝ, (1+|u|+|v|)^4*‖iteratedFDeriv ℝ 2 f ![σ,u,v]‖ ≤ B)
    (hz : ∀ v : ℝ, f ![σ,0,v]=0) {u v : ℝ} (hu : 0 ≤ u) :
    ‖(f ![σ,u,v]+f ![σ,-u,v])/((u^2 : ℝ) : ℂ)‖ ≤ 2*B*cubicIntersectionDensity (u,v) := by
  have hden : 0 < (1+u^2)*(1+v^2) := by positivity
  have hP : 0 < (1+|v|)^4 := by positivity
  by_cases hu0 : u=0
  · simp only [hu0,zero_pow (by decide : 2 ≠ 0),Complex.ofReal_zero,div_zero,norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hB) (by unfold cubicIntersectionDensity; positivity)
  have huP : 0 < u^2 := sq_pos_of_ne_zero hu0
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos huP,density_eq_inv_denominator,
    ← div_eq_mul_inv]
  by_cases hsmall : u ≤ 1
  · have hb2 (a : ℝ) (_ha : a ∈ Icc (-u) u) :
        ‖fderiv ℝ (fderiv ℝ f) ![σ,a,v]‖ ≤ B/(1+|v|)^4 := by
      rw [norm_second_eq]
      apply (le_div_iff₀ hP).mpr
      have hp : (1+|v|)^4 ≤ (1+|a|+|v|)^4 :=
        pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg a]) 4
      have hh := (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (h2 a v)
      simpa only [mul_comm] using hh
    have hc := norm_central_difference_fixed_transverse hu (div_nonneg hB hP.le) hf hb2 (hz v)
    have he : (1+u^2)*(1+v^2) ≤ 2*(1+|v|)^4 := by
      have hv : 1+v^2 ≤ (1+|v|)^2 := by nlinarith [sq_abs v,abs_nonneg v]
      have hp : (1+|v|)^2 ≤ (1+|v|)^4 := pow_le_pow_right₀ (by linarith [abs_nonneg v]) (by norm_num)
      have hu2 : 1+u^2 ≤ 2 := by nlinarith
      exact (mul_le_mul hu2 (hv.trans hp) (by positivity) (by norm_num))
    calc
      _ ≤ B/(1+|v|)^4 := (div_le_iff₀ huP).mpr hc
      _ ≤ 2*B/((1+u^2)*(1+v^2)) := by
        apply (div_le_div_iff₀ hP hden).mpr
        simpa only [mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left he hB
  · have hlarge : 1 ≤ u^2 := by have := lt_of_not_ge hsmall; nlinarith
    have hT : 0 < (1+|u|+|v|)^4 := by positivity
    have hp := (le_div_iff₀ hT).mpr (by simpa only [mul_comm] using h0 u v)
    have hm : ‖f ![σ,-u,v]‖ ≤ B/(1+|u|+|v|)^4 := by
      apply (le_div_iff₀ hT).mpr
      simpa only [abs_neg,mul_comm] using h0 (-u) v
    have hs : ‖f ![σ,u,v]+f ![σ,-u,v]‖ ≤ 2*B/(1+|u|+|v|)^4 :=
      (norm_add_le _ _).trans (by simpa only [← two_mul,mul_div_assoc] using add_le_add hp hm)
    calc
      _ ≤ ‖f ![σ,u,v]+f ![σ,-u,v]‖ := div_le_self (norm_nonneg _) hlarge
      _ ≤ 2*B/(1+|u|+|v|)^4 := hs
      _ ≤ 2*B/((1+u^2)*(1+v^2)) :=
        div_le_div₀ (mul_nonneg zero_le_two hB) (le_refl _) hden (cauchy_product_denominator_le u v)

/-- The actual first finite-part quotient has a uniform integrable product-density envelope
for every Schwartz test, controlled by one fixed finite family of seminorms. -/
theorem exists_schwartz_cubicAxisQuotient_bound :
    ∃ C > 0, ∀ Φ : 𝓢(ℝ × ℝ, ℂ), ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Ici (0 : ℝ), ∀ v : ℝ,
      ‖cubicAxisQuotient Φ σ (u,v)‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity (u,v) := by
  obtain ⟨C,hC,hb⟩ := exists_cubicTestedSource_uniform_schwartz_bound 4 2
  refine ⟨2*C,mul_pos zero_lt_two hC,?_⟩
  intro Φ σ hσ u hu v
  let B := C*cubicSchwartzSeminorm 76 2 Φ
  have hB : 0 ≤ B := mul_nonneg hC.le (apply_nonneg _ _)
  have hf (a b : ℝ) : ContDiffAt ℝ ∞ (cubicTestedAxisNumerator Φ) ![σ,a,b] :=
    contDiffAt_cubicTestedAxisNumerator (Φ.smooth (⊤ : ℕ∞)) hσ.1
  have h0 (a b : ℝ) : (1+|a|+|b|)^4*‖cubicTestedAxisNumerator Φ ![σ,a,b]‖ ≤ B := by
    simpa [B] using (hb Φ 0 (by norm_num) ![σ,a,b] hσ).2
  have h2 (a b : ℝ) :
      (1+|a|+|b|)^4*‖iteratedFDeriv ℝ 2 (cubicTestedAxisNumerator Φ) ![σ,a,b]‖ ≤ B := by
    simpa [B] using (hb Φ 2 le_rfl ![σ,a,b] hσ).2
  have hz (b : ℝ) : cubicTestedAxisNumerator Φ ![σ,0,b]=0 := by
    change (realCubicSource σ 0 b-realAxisSource σ 0)*Φ (0,b)=0
    rw [realCubicSource_axis_left hσ.1,zero_mul]
  have hh := norm_axis_quotient_le_density hB hf h0 h2 hz hu (v := v)
  simpa only [cubicAxisQuotient,cubicAxisDifference,B,mul_assoc] using hh

private theorem norm_line_reflection_le
    {f : (Fin 3 → ℝ) → ℂ} {x k : Fin 3 → ℝ} {C : ℝ}
    (hf : ∀ t ∈ Icc (-1 : ℝ) 1, DifferentiableAt ℝ f (x+t•k))
    (hb : ∀ t ∈ Icc (-1 : ℝ) 1, ‖fderiv ℝ f (x+t•k)‖ ≤ C) :
    ‖f (x+k)-f (x-k)‖ ≤ 2*C*‖k‖ := by
  have hd (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => f (x+s•k)) ((fderiv ℝ f (x+t•k)) k) t :=
    (hf t ht).hasFDerivAt.comp_hasDerivAt t
      (by simpa using (((hasDerivAt_id t).smul_const k).const_add x))
  have hn (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ‖(fderiv ℝ f (x+t•k)) k‖ ≤ C*‖k‖ :=
    (ContinuousLinearMap.le_opNorm _ k).trans
      (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg k))
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hn
    (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
  simpa only [one_smul,neg_one_smul,← sub_eq_add_neg,sub_neg_eq_add,
    one_add_one_eq_two,Real.norm_ofNat,mul_comm,mul_left_comm,mul_assoc] using h

private theorem norm_u_reflection_le
    {f : (Fin 3 → ℝ) → ℂ} {σ u v C : ℝ} (hu : 0 ≤ u) (hC : 0 ≤ C)
    (hf : ∀ a b : ℝ, ContDiffAt ℝ ∞ f ![σ,a,b])
    (hb : ∀ a : ℝ, ‖fderiv ℝ f ![σ,a,v]‖ ≤ C) :
    ‖f ![σ,u,v]-f ![σ,-u,v]‖ ≤ 2*C*u := by
  have he (t : ℝ) : (![σ,0,v]+t•![0,u,0] : Fin 3 → ℝ)=![σ,t*u,v] := by
    ext i; fin_cases i <;> simp
  have hp : (![σ,0,v]+![0,u,0] : Fin 3 → ℝ)=![σ,u,v] := by
    ext i; fin_cases i <;> simp
  have hm : (![σ,0,v]-![0,u,0] : Fin 3 → ℝ)=![σ,-u,v] := by
    ext i; fin_cases i <;> simp
  have hh := norm_line_reflection_le
    (x := ![σ,0,v]) (k := ![0,u,0])
    (fun t _ => by rw [he]; exact (hf _ _).differentiableAt (by simp))
    (fun t _ => by rw [he]; exact hb _)
  rw [hp,hm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (norm_u_vector_le hu) (mul_nonneg zero_le_two hC))

private theorem norm_v_reflection_le
    {f : (Fin 3 → ℝ) → ℂ} {σ u v C : ℝ} (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hf : ∀ a b : ℝ, ContDiffAt ℝ ∞ f ![σ,a,b])
    (hb : ∀ b : ℝ, ‖fderiv ℝ f ![σ,u,b]‖ ≤ C) :
    ‖f ![σ,u,v]-f ![σ,u,-v]‖ ≤ 2*C*v := by
  have he (t : ℝ) : (![σ,u,0]+t•![0,0,v] : Fin 3 → ℝ)=![σ,u,t*v] := by
    ext i; fin_cases i <;> simp
  have hp : (![σ,u,0]+![0,0,v] : Fin 3 → ℝ)=![σ,u,v] := by
    ext i; fin_cases i <;> simp
  have hm : (![σ,u,0]-![0,0,v] : Fin 3 → ℝ)=![σ,u,-v] := by
    ext i; fin_cases i <;> simp
  have hh := norm_line_reflection_le
    (x := ![σ,u,0]) (k := ![0,0,v])
    (fun t _ => by rw [he]; exact (hf _ _).differentiableAt (by simp))
    (fun t _ => by rw [he]; exact hb _)
  rw [hp,hm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (norm_v_vector_le hv) (mul_nonneg zero_le_two hC))

private theorem norm_mixed_difference_global
    {f : (Fin 3 → ℝ) → ℂ} {σ u v C : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hf : ∀ a b : ℝ, ContDiffAt ℝ ∞ f ![σ,a,b])
    (hb : ∀ a b : ℝ, ‖fderiv ℝ (fderiv ℝ f) ![σ,a,b]‖ ≤ C) :
    ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v]‖ ≤ 4*C*u*v := by
  let S : Set (Fin 3 → ℝ) := {x | x 0=σ}
  have hcoords (x : Fin 3 → ℝ) (hx : x ∈ S) : x=![σ,x 1,x 2] := by
    ext i; fin_cases i
    · exact hx
    · rfl
    · rfl
  have hfs (x : Fin 3 → ℝ) (hx : x ∈ S) : ContDiffAt ℝ ∞ f x := by
    rw [hcoords x hx]; exact hf _ _
  have hbs (x : Fin 3 → ℝ) (hx : x ∈ S) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
    rw [hcoords x hx]; exact hb _ _
  have hS : Convex ℝ S := by
    intro x hx y hy a b _ _ hab
    change a*x 0+b*y 0=σ
    rw [hx,hy,← add_mul,hab,one_mul]
  have hp' (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) :
      ![σ,-u,-v]+t•![0,0,2*v] ∈ S ∧
      ![σ,-u,-v]+t•![0,0,2*v]+![0,2*u,0] ∈ S := by
    constructor
    · change σ+t*0=σ; ring
    · change σ+t*0+0=σ; ring
  have hh := norm_rectangular_difference_le
    (fun x hx => (hfs x hx).differentiableAt (by simp))
    (fun x hx => ((hfs x hx).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    hbs hS ![σ,-u,-v] ![0,2*u,0] ![0,0,2*v] hp'
  have e1 : (![σ,-u,-v]+![0,0,2*v]+![0,2*u,0] : Fin 3 → ℝ)=![σ,u,v] := by
    ext i; fin_cases i <;> simp <;> ring
  have e2 : (![σ,-u,-v]+![0,0,2*v] : Fin 3 → ℝ)=![σ,-u,v] := by
    ext i; fin_cases i <;> simp
    ring
  have e3 : (![σ,-u,-v]+![0,2*u,0] : Fin 3 → ℝ)=![σ,u,-v] := by
    ext i; fin_cases i <;> simp
    ring
  rw [e1,e2,e3] at hh
  calc
    _ ≤ C*‖(![0,2*u,0] : Fin 3 → ℝ)‖*‖(![0,0,2*v] : Fin 3 → ℝ)‖ := hh
    _ ≤ C*(2*u)*(2*v) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (norm_u_vector_le (by positivity)) hC)
        (norm_v_vector_le (by positivity)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem norm_mixed_quotient_le_density
    {f : (Fin 3 → ℝ) → ℂ} {σ B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ u v : ℝ, ContDiffAt ℝ ∞ f ![σ,u,v])
    (h0 : ∀ u v : ℝ, (1+|u|+|v|)^4*‖f ![σ,u,v]‖ ≤ B)
    (h1 : ∀ u v : ℝ, (1+|u|+|v|)^4*‖iteratedFDeriv ℝ 1 f ![σ,u,v]‖ ≤ B)
    (h2 : ∀ u v : ℝ, (1+|u|+|v|)^4*‖iteratedFDeriv ℝ 2 f ![σ,u,v]‖ ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ‖(f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v])/((u*v : ℝ) : ℂ)‖ ≤
      16*B*cubicIntersectionDensity (u,v) := by
  have hden : 0 < (1+u^2)*(1+v^2) := by positivity
  by_cases hz : u*v=0
  · simp only [hz,Complex.ofReal_zero,div_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hB) (by unfold cubicIntersectionDensity; positivity)
  have huv : 0 < u*v := lt_of_le_of_ne (mul_nonneg hu hv) (Ne.symm hz)
  have huP : 0 < u := lt_of_le_of_ne hu (by intro h; exact hz (by rw [← h,zero_mul]))
  have hvP : 0 < v := lt_of_le_of_ne hv (by intro h; exact hz (by rw [← h,mul_zero]))
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos huv,density_eq_inv_denominator,
    ← div_eq_mul_inv]
  have hglobal (a b : ℝ) : ‖fderiv ℝ (fderiv ℝ f) ![σ,a,b]‖ ≤ B := by
    rw [norm_second_eq]
    have ht : 1 ≤ (1+|a|+|b|)^4 := one_le_pow₀ (by linarith [abs_nonneg a,abs_nonneg b])
    exact (le_mul_of_one_le_left (norm_nonneg _) ht).trans (h2 a b)
  have hdu (a b : ℝ) : ‖fderiv ℝ f ![σ,a,b]‖ ≤ B/(1+|b|)^4 := by
    apply (le_div_iff₀ (by positivity : 0 < (1+|b|)^4)).mpr
    have ht : (1+|b|)^4 ≤ (1+|a|+|b|)^4 :=
      pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg a]) 4
    have hh := (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (h1 a b)
    simpa only [norm_iteratedFDeriv_one,mul_comm] using hh
  have hdv (a b : ℝ) : ‖fderiv ℝ f ![σ,a,b]‖ ≤ B/(1+|a|)^4 := by
    apply (le_div_iff₀ (by positivity : 0 < (1+|a|)^4)).mpr
    have ht : (1+|a|)^4 ≤ (1+|a|+|b|)^4 :=
      pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg b]) 4
    have hh := (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (h1 a b)
    simpa only [norm_iteratedFDeriv_one,mul_comm] using hh
  by_cases hus : u ≤ 1
  · by_cases hvs : v ≤ 1
    · have hn := norm_mixed_difference_global hu hv hB hf hglobal
      have he : (1+u^2)*(1+v^2) ≤ 4 := by
        have he1 : 1+u^2 ≤ 2 := by nlinarith
        have he2 : 1+v^2 ≤ 2 := by nlinarith
        nlinarith [mul_le_mul he1 he2 (by positivity : 0 ≤ 1+v^2) (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ 4*B := (div_le_iff₀ huv).mpr (by simpa only [mul_assoc] using hn)
        _ ≤ 16*B/((1+u^2)*(1+v^2)) := by
          apply (le_div_iff₀ hden).mpr
          nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4*B)]
    · have hv1 : 1 ≤ v := le_of_lt (lt_of_not_ge hvs)
      have hP : 0 < (1+|v|)^4 := by positivity
      have hn1 := norm_u_reflection_le hu (div_nonneg hB hP.le) hf (fun a => hdu a v)
      have hn2 : ‖f ![σ,u,-v]-f ![σ,-u,-v]‖ ≤ 2*(B/(1+|v|)^4)*u := by
        simpa only [abs_neg] using
          norm_u_reflection_le (u := u) (v := -v) hu (div_nonneg hB (by positivity)) hf (fun a => hdu a (-v))
      have hn : ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v]‖ ≤
          4*(B/(1+|v|)^4)*u := by
        rw [show f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v] =
          (f ![σ,u,v]-f ![σ,-u,v])-(f ![σ,u,-v]-f ![σ,-u,-v]) by abel]
        exact (norm_sub_le _ _).trans (by nlinarith [add_le_add hn1 hn2])
      have he : (1+u^2)*(1+v^2) ≤ 4*((1+|v|)^4*v) := by
        have he1 : 1+u^2 ≤ 2 := by nlinarith
        have he2 : 1+v^2 ≤ (1+|v|)^4 := by
          exact (show 1+v^2 ≤ (1+|v|)^2 by nlinarith [sq_abs v,abs_nonneg v]).trans
            (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (by norm_num))
        have he3 := mul_le_mul he1 he2 (by positivity : 0 ≤ 1+v^2) (by norm_num : (0 : ℝ) ≤ 2)
        have he4 := le_mul_of_one_le_right hP.le hv1
        nlinarith
      calc
        _ ≤ 4*B/((1+|v|)^4*v) := (div_le_iff₀ huv).mpr (by
          rw [show 4*B/((1+|v|)^4*v)*(u*v)=4*(B/(1+|v|)^4)*u by
            field_simp [hP.ne',hvP.ne']]
          exact hn)
        _ ≤ 16*B/((1+u^2)*(1+v^2)) := by
          apply (div_le_div_iff₀ (mul_pos hP hvP) hden).mpr
          nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4*B)]
  · by_cases hvs : v ≤ 1
    · have hu1 : 1 ≤ u := le_of_lt (lt_of_not_ge hus)
      have hP : 0 < (1+|u|)^4 := by positivity
      have hn1 := norm_v_reflection_le hv (div_nonneg hB hP.le) hf (fun b => hdv u b)
      have hn2 : ‖f ![σ,-u,v]-f ![σ,-u,-v]‖ ≤ 2*(B/(1+|u|)^4)*v := by
        simpa only [abs_neg] using
          norm_v_reflection_le (u := -u) (v := v) hv (div_nonneg hB (by positivity)) hf (fun b => hdv (-u) b)
      have hn : ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v]‖ ≤
          4*(B/(1+|u|)^4)*v := by
        rw [show f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v] =
          (f ![σ,u,v]-f ![σ,u,-v])-(f ![σ,-u,v]-f ![σ,-u,-v]) by abel]
        exact (norm_sub_le _ _).trans (by nlinarith [add_le_add hn1 hn2])
      have he : (1+u^2)*(1+v^2) ≤ 4*((1+|u|)^4*u) := by
        have he1 : 1+v^2 ≤ 2 := by nlinarith
        have he2 : 1+u^2 ≤ (1+|u|)^4 := by
          exact (show 1+u^2 ≤ (1+|u|)^2 by nlinarith [sq_abs u,abs_nonneg u]).trans
            (pow_le_pow_right₀ (by linarith [abs_nonneg u]) (by norm_num))
        have he3 := mul_le_mul he2 he1 (by positivity : 0 ≤ 1+v^2) (by positivity : 0 ≤ (1+|u|)^4)
        have he4 := le_mul_of_one_le_right hP.le hu1
        nlinarith
      calc
        _ ≤ 4*B/((1+|u|)^4*u) := (div_le_iff₀ huv).mpr (by
          rw [show 4*B/((1+|u|)^4*u)*(u*v)=4*(B/(1+|u|)^4)*v by
            field_simp [hP.ne',huP.ne']]
          exact hn)
        _ ≤ 16*B/((1+u^2)*(1+v^2)) := by
          apply (div_le_div_iff₀ (mul_pos hP huP) hden).mpr
          nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4*B)]
    · have hT : 0 < (1+|u|+|v|)^4 := by positivity
      have hlarge : 1 ≤ u*v := by
        have hu1 : 1 ≤ u := le_of_lt (lt_of_not_ge hus)
        have hv1 : 1 ≤ v := le_of_lt (lt_of_not_ge hvs)
        exact one_le_mul_of_one_le_of_one_le hu1 hv1
      have hn (a b : ℝ) : ‖f ![σ,a,b]‖ ≤ B/(1+|a|+|b|)^4 :=
        (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h0 a b)
      have hn0 := hn u v
      have hn1 := hn (-u) v
      have hn2 := hn u (-v)
      have hn3 := hn (-u) (-v)
      simp only [abs_neg] at hn1 hn2 hn3
      have hn4 : ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v]‖ ≤
          4*B/(1+|u|+|v|)^4 := by
        have he : ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v]‖ ≤
            ((‖f ![σ,u,v]‖+‖f ![σ,-u,v]‖)+‖f ![σ,u,-v]‖)+‖f ![σ,-u,-v]‖ := by
          calc
            _ ≤ ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]‖+‖f ![σ,-u,-v]‖ := norm_add_le _ _
            _ ≤ (‖f ![σ,u,v]-f ![σ,-u,v]‖+‖f ![σ,u,-v]‖)+‖f ![σ,-u,-v]‖ :=
              add_le_add (norm_sub_le _ _) le_rfl
            _ ≤ _ := add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
        apply he.trans
        have hh := add_le_add (add_le_add (add_le_add hn0 hn1) hn2) hn3
        convert hh using 1; ring
      calc
        _ ≤ ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v]‖ := div_le_self (norm_nonneg _) hlarge
        _ ≤ 4*B/(1+|u|+|v|)^4 := hn4
        _ ≤ 4*B/((1+u^2)*(1+v^2)) :=
          div_le_div₀ (by positivity) le_rfl hden (cauchy_product_denominator_le u v)
        _ ≤ 16*B/((1+u^2)*(1+v^2)) := div_le_div_of_nonneg_right (by linarith) hden.le

/-- The actual product-PV quotient has a uniform integrable product-density envelope
for every Schwartz test, with no growth or cancellation premise. -/
theorem exists_schwartz_cubicMixedQuotient_bound :
    ∃ C > 0, ∀ Φ : 𝓢(ℝ × ℝ, ℂ), ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Ici (0 : ℝ), ∀ v ∈ Ici (0 : ℝ),
      ‖cubicMixedQuotient Φ σ (u,v)‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity (u,v) := by
  obtain ⟨C,hC,hb⟩ := exists_cubicTestedSource_uniform_schwartz_bound 4 2
  refine ⟨16*C,mul_pos (by norm_num) hC,?_⟩
  intro Φ σ hσ u hu v hv
  let B := C*cubicSchwartzSeminorm 76 2 Φ
  have hB : 0 ≤ B := mul_nonneg hC.le (apply_nonneg _ _)
  have hf (a b : ℝ) : ContDiffAt ℝ ∞ (cubicTestedSource Φ) ![σ,a,b] :=
    contDiffAt_cubicTestedSource (Φ.smooth (⊤ : ℕ∞)) hσ.1
  have h0 (a b : ℝ) : (1+|a|+|b|)^4*‖cubicTestedSource Φ ![σ,a,b]‖ ≤ B := by
    simpa [B] using (hb Φ 0 (by norm_num) ![σ,a,b] hσ).1
  have h1 (a b : ℝ) :
      (1+|a|+|b|)^4*‖iteratedFDeriv ℝ 1 (cubicTestedSource Φ) ![σ,a,b]‖ ≤ B := by
    simpa [B] using (hb Φ 1 (by norm_num) ![σ,a,b] hσ).1
  have h2 (a b : ℝ) :
      (1+|a|+|b|)^4*‖iteratedFDeriv ℝ 2 (cubicTestedSource Φ) ![σ,a,b]‖ ≤ B := by
    simpa [B] using (hb Φ 2 le_rfl ![σ,a,b] hσ).1
  have hh := norm_mixed_quotient_le_density hB hf h0 h1 h2 hu hv
  simpa only [cubicMixedQuotient,cubicMixedDifference,B,mul_assoc] using hh

private theorem cubicAxisQuotient_abs (Φ : ℝ × ℝ → ℂ) (σ u v : ℝ) :
    cubicAxisQuotient Φ σ (|u|,v)=cubicAxisQuotient Φ σ (u,v) := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu]
    simp only [cubicAxisQuotient,cubicAxisDifference,neg_neg,neg_sq]
    rw [add_comm]

private theorem cubicMixedQuotient_neg_left (Φ : ℝ × ℝ → ℂ) (σ u v : ℝ) :
    cubicMixedQuotient Φ σ (-u,v)=cubicMixedQuotient Φ σ (u,v) := by
  simp only [cubicMixedQuotient,cubicMixedDifference,neg_neg,neg_mul,Complex.ofReal_neg]
  rw [div_neg,← neg_div]
  congr 1
  abel

private theorem cubicMixedQuotient_neg_right (Φ : ℝ × ℝ → ℂ) (σ u v : ℝ) :
    cubicMixedQuotient Φ σ (u,-v)=cubicMixedQuotient Φ σ (u,v) := by
  simp only [cubicMixedQuotient,cubicMixedDifference,neg_neg,mul_neg,Complex.ofReal_neg]
  rw [div_neg,← neg_div]
  congr 1
  abel

private theorem cubicMixedQuotient_abs (Φ : ℝ × ℝ → ℂ) (σ u v : ℝ) :
    cubicMixedQuotient Φ σ (|u|,|v|)=cubicMixedQuotient Φ σ (u,v) := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hu,abs_of_nonneg hv]
  · rw [abs_of_nonneg hu,abs_of_nonpos hv,cubicMixedQuotient_neg_right]
  · rw [abs_of_nonpos hu,abs_of_nonneg hv,cubicMixedQuotient_neg_left]
  · rw [abs_of_nonpos hu,abs_of_nonpos hv,cubicMixedQuotient_neg_left,cubicMixedQuotient_neg_right]

/-- Uniform integrable control over the whole frequency plane, with both quotients
bounded by one finite Schwartz seminorm. -/
theorem exists_schwartz_cubicQuotients_global_bound :
    ∃ C > 0, ∀ Φ : 𝓢(ℝ × ℝ, ℂ), ∀ σ ∈ Icc (1 : ℝ) 2, ∀ w : ℝ × ℝ,
      ‖cubicAxisQuotient Φ σ w‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w ∧
      ‖cubicMixedQuotient Φ σ w‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w := by
  obtain ⟨C,hC,hc⟩ := exists_schwartz_cubicAxisQuotient_bound
  obtain ⟨D,hD,hd⟩ := exists_schwartz_cubicMixedQuotient_bound
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro Φ σ hσ w
  have hS : 0 ≤ cubicSchwartzSeminorm 76 2 Φ := apply_nonneg _ _
  have hρ : 0 ≤ cubicIntersectionDensity w := by
    change 0 ≤ (1+w.1^2)⁻¹*(1+w.2^2)⁻¹
    exact mul_nonneg (inv_nonneg.mpr (le_add_of_nonneg_right (sq_nonneg w.1) |>.trans' zero_le_one))
      (inv_nonneg.mpr (le_add_of_nonneg_right (sq_nonneg w.2) |>.trans' zero_le_one))
  have ha := hc Φ σ hσ |w.1| (show |w.1| ∈ Ici (0 : ℝ) from abs_nonneg w.1) w.2
  have hm := hd Φ σ hσ |w.1| (show |w.1| ∈ Ici (0 : ℝ) from abs_nonneg w.1)
    |w.2| (show |w.2| ∈ Ici (0 : ℝ) from abs_nonneg w.2)
  rw [cubicAxisQuotient_abs] at ha
  rw [cubicMixedQuotient_abs] at hm
  simp only [cubicIntersectionDensity,sq_abs] at ha hm
  exact ⟨ha.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hS) hρ),
    hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hS) hρ)⟩

/-- The actual tested sources themselves have the same full-plane integrable envelope. -/
theorem exists_schwartz_testedSources_density_bound :
    ∃ C > 0, ∀ Φ : 𝓢(ℝ × ℝ, ℂ), ∀ σ ∈ Icc (1 : ℝ) 2, ∀ w : ℝ × ℝ,
      ‖cubicTestedSource Φ ![σ,w.1,w.2]‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w ∧
      ‖cubicTestedAxisNumerator Φ ![σ,w.1,w.2]‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w := by
  obtain ⟨C,hC,hb⟩ := exists_cubicTestedSource_uniform_schwartz_bound 4 2
  refine ⟨C,hC,?_⟩
  intro Φ σ hσ w
  have hh := hb Φ 0 (by norm_num) ![σ,w.1,w.2] hσ
  have hH :
      (1+|w.1|+|w.2|)^4*‖cubicTestedSource Φ ![σ,w.1,w.2]‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ ∧
      (1+|w.1|+|w.2|)^4*‖cubicTestedAxisNumerator Φ ![σ,w.1,w.2]‖ ≤ C*cubicSchwartzSeminorm 76 2 Φ := by
    simpa using hh
  have hB : 0 ≤ C*cubicSchwartzSeminorm 76 2 Φ := mul_nonneg hC.le (apply_nonneg _ _)
  have ht : 0 < (1+|w.1|+|w.2|)^4 := by positivity
  have hd : 0 < (1+w.1^2)*(1+w.2^2) := by positivity
  have hnorm (x : ℝ) (hx : (1+|w.1|+|w.2|)^4*x ≤ C*cubicSchwartzSeminorm 76 2 Φ) :
      x ≤ C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w := by
    rw [density_eq_inv_denominator,← div_eq_mul_inv]
    exact ((le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hx)).trans
      (div_le_div₀ hB le_rfl hd (cauchy_product_denominator_le w.1 w.2))
  exact ⟨hnorm _ hH.1,hnorm _ hH.2⟩

end RHTower.BAGTrace
