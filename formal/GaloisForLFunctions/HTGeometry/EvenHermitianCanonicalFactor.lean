import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.Reflection

/-!
# Reflection-compatible splitting of an even Hermitian divisor

An even Schwarz-real divisor with even multiplicity on both coordinate axes
splits into two conjugate divisors, each invariant under negation. The selected
divisor takes quadrants I and III and half of each axis multiplicity.
-/

open Complex Filter Topology Set RHTower
open scoped ComplexConjugate
open GaloisForLFunctions.CountableDivisor GaloisForLFunctions.EntireZeroDivisor

noncomputable section
namespace GaloisForLFunctions.HTGeometry.EvenHermitianFactor

def multiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  ((MeromorphicOn.divisor f Set.univ) z).toNat

def selectedMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  if 0 < z.re * z.im then multiplicity f z
  else if z.re * z.im < 0 then 0 else multiplicity f z / 2

theorem selectedMultiplicity_le (f : ℂ → ℂ) (z : ℂ) :
    selectedMultiplicity f z ≤ multiplicity f z := by
  unfold selectedMultiplicity
  split_ifs <;> omega

theorem multiplicity_neg {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (he : ∀ z, f (-z)=f z) (z : ℂ) : multiplicity f (-z)=multiplicity f z := by
  unfold multiplicity
  rw [RHTower.OrderOneHadamard.divisor_neg_of_even hf he]

theorem multiplicity_conj {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hr : ∀ z, f (conj z)=conj (f z)) (z : ℂ) :
    multiplicity f (conj z)=multiplicity f z := by
  unfold multiplicity
  rw [divisor_univ_eq_analyticOrder hf, divisor_univ_eq_analyticOrder hf,
    RHTower.analyticOrderAt_conj_of_conjEquivariant hr (hf z (mem_univ _))
      (hf (conj z) (mem_univ _))]

theorem selectedMultiplicity_neg {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (he : ∀ z, f (-z)=f z) (z : ℂ) :
    selectedMultiplicity f (-z)=selectedMultiplicity f z := by
  simp only [selectedMultiplicity, Complex.neg_re, Complex.neg_im, neg_mul_neg,
    multiplicity_neg hf he]

theorem selectedMultiplicity_add_conj {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hr : ∀ z, f (conj z)=conj (f z))
    (ha : ∀ z, z.re=0 ∨ z.im=0 → Even (multiplicity f z)) (z : ℂ) :
    selectedMultiplicity f z + selectedMultiplicity f (conj z)=multiplicity f z := by
  have hm := multiplicity_conj hf hr z
  simp only [selectedMultiplicity, Complex.conj_re, Complex.conj_im]
  by_cases hp : 0 < z.re*z.im
  · have hn : z.re * -z.im < 0 := by nlinarith
    rw [if_pos hp,if_neg (show ¬0<z.re * -z.im by nlinarith),if_pos hn,add_zero]
  by_cases hn : z.re*z.im < 0
  · have hp' : 0 < z.re * -z.im := by nlinarith
    rw [if_neg hp,if_pos hn,if_pos hp',zero_add,hm]
  have hz : z.re*z.im=0 := by linarith
  obtain ⟨k,hk⟩ := ha z (mul_eq_zero.mp hz)
  have hz' : z.re * -z.im=0 := by nlinarith
  simp only [hz,hz',lt_self_iff_false,if_false,hm]
  omega

abbrev SelectedCopy (f : ℂ → ℂ) : Type :=
  {q : ZeroCopy f // q.2.val < selectedMultiplicity f (zeroCopyPoint f q)}

def selectedPoint (f : ℂ → ℂ) (q : SelectedCopy f) : ℂ := zeroCopyPoint f q.1

theorem selectedPoint_ne_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (h0 : f 0 ≠ 0) (q : SelectedCopy f) : selectedPoint f q ≠ 0 :=
  zeroCopyPoint_ne_zero hf h0 q.1

theorem selectedPoint_locallyFinite {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    LocallyFiniteDivisor (selectedPoint f) := by
  intro r
  apply Set.Finite.of_finite_image (f := Subtype.val)
  · exact (locallyFinite_zeroCopyPoint hf r).subset (by
      rintro _ ⟨q,hq,rfl⟩
      exact hq)
  · exact Subtype.val_injective.injOn

theorem summable_selectedPoint_inv_sq {f : ℂ → ℂ}
    (hs : Summable fun q : ZeroCopy f => 1/‖zeroCopyPoint f q‖^2) :
    Summable fun q : SelectedCopy f => 1/‖selectedPoint f q‖^2 :=
  hs.subtype _

theorem ncard_selectedPoint_fibre (f : ℂ → ℂ) (z : ℂ) :
    {q : SelectedCopy f | selectedPoint f q=z}.ncard=selectedMultiplicity f z := by
  classical
  by_cases hz : selectedMultiplicity f z=0
  · have he : {q : SelectedCopy f | selectedPoint f q=z}=∅ := by
      ext q
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      have hh := q.2
      change q.1.2.val < selectedMultiplicity f (selectedPoint f q) at hh
      rw [h,hz] at hh
      omega
    rw [he,Set.ncard_empty,hz]
  have hm : (MeromorphicOn.divisor f Set.univ) z ≠ 0 := by
    intro h
    have hh := selectedMultiplicity_le f z
    simp only [multiplicity,h,Int.toNat_zero] at hh
    exact hz (Nat.eq_zero_of_le_zero hh)
  let g : Fin (selectedMultiplicity f z) → SelectedCopy f := fun k =>
    ⟨⟨⟨z,hm⟩,⟨k.val,k.isLt.trans_le (selectedMultiplicity_le f z)⟩⟩,k.isLt⟩
  have hgi : Function.Injective g := by
    intro i j hij
    exact Fin.ext (congrArg (fun q : SelectedCopy f => q.1.2.val) hij)
  have hg : Set.range g={q : SelectedCopy f | selectedPoint f q=z} := by
    ext q
    constructor
    · rintro ⟨k,rfl⟩
      rfl
    · rcases q with ⟨⟨⟨w,hw⟩,k⟩,hk⟩
      intro h
      change w=z at h
      subst w
      exact ⟨⟨k.val,hk⟩,rfl⟩
  rw [← hg,Set.ncard_range_of_injective hgi]
  simp

def factor (f : ℂ → ℂ) : ℂ → ℂ := canonicalProductE1Indexed (selectedPoint f)

theorem factor_zero (f : ℂ → ℂ) : factor f 0=1 := canonicalProductE1Indexed_zero

theorem factor_analytic {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (h0 : f 0≠0)
    (hs : Summable fun q : ZeroCopy f => 1/‖zeroCopyPoint f q‖^2) :
    AnalyticOnNhd ℂ (factor f) Set.univ :=
  canonicalProductE1Indexed_analytic _ (selectedPoint_ne_zero hf h0)
    (summable_selectedPoint_inv_sq hs)

theorem factor_order {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (h0 : f 0≠0)
    (hs : Summable fun q : ZeroCopy f => 1/‖zeroCopyPoint f q‖^2) {z : ℂ} (hz : z≠0) :
    analyticOrderAt (factor f) z=(selectedMultiplicity f z : ℕ∞) := by
  rw [factor,analyticOrderAt_canonicalProductE1Indexed (selectedPoint_ne_zero hf h0)
    (selectedPoint_locallyFinite hf) (summable_selectedPoint_inv_sq hs) hz,
    ncard_selectedPoint_fibre]

private theorem fin_cast_val {m n : ℕ} (h : Fin m=Fin n) (i : Fin m) :
    (cast h i).val=i.val := by
  have hmn : m=n := by simpa using congrArg Nat.card h
  subst n
  rfl

def selectedReflect {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (he : ∀ z, f (-z)=f z) : SelectedCopy f ≃ SelectedCopy f :=
  (RHTower.OrderOneHadamard.zeroCopyReflect hf he).subtypeEquiv (fun q => by
    rw [RHTower.OrderOneHadamard.zeroCopyPoint_reflect,selectedMultiplicity_neg hf he]
    change _ ↔ (cast _ q.2 : Fin (multiplicity f (-zeroCopyPoint f q))).val < _
    rw [fin_cast_val])

theorem selectedPoint_reflect {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (he : ∀ z, f (-z)=f z) (q : SelectedCopy f) :
    selectedPoint f (selectedReflect hf he q) = -selectedPoint f q := rfl

theorem factor_even {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (he : ∀ z, f (-z)=f z) (z : ℂ) : factor f (-z)=factor f z := by
  change (∏' q : SelectedCopy f,weierstrassE1 (-z/selectedPoint f q)) =
    ∏' q : SelectedCopy f,weierstrassE1 (z/selectedPoint f q)
  rw [← (selectedReflect hf he).tprod_eq (fun q => weierstrassE1 (-z/selectedPoint f q))]
  apply tprod_congr
  intro q
  rw [selectedPoint_reflect hf he,neg_div_neg_eq]

def sharpFactor (f : ℂ → ℂ) (z : ℂ) : ℂ := conj (factor f (conj z))

theorem sharpFactor_eq_product {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (h0 : f 0≠0) (hs : Summable fun q : ZeroCopy f => 1/‖zeroCopyPoint f q‖^2)
    (z : ℂ) : sharpFactor f z=canonicalProductE1Indexed (fun q => conj (selectedPoint f q)) z := by
  have hm := multipliable_canonicalProductE1Indexed (selectedPoint_ne_zero hf h0)
    (summable_selectedPoint_inv_sq hs) (conj z)
  change conj (∏' q : SelectedCopy f,weierstrassE1 (conj z/selectedPoint f q)) = _
  rw [hm.map_tprod (starRingEnd ℂ) Complex.continuous_conj]
  apply tprod_congr
  intro q
  simp only [weierstrassE1,map_mul,map_sub,map_one,map_div₀,← Complex.exp_conj,
    Complex.conj_conj]

theorem multiplicity_cast_eq_order {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hfin : ∀ z,analyticOrderAt f z≠⊤) (z : ℂ) :
    (multiplicity f z : ℕ∞)=analyticOrderAt f z := by
  have hn := ENat.coe_toNat (hfin z)
  unfold multiplicity
  rw [divisor_univ_eq_analyticOrder hf,← hn]
  simp

theorem factor_mul_sharp_order {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (h0 : f 0≠0) (hfin : ∀ z,analyticOrderAt f z≠⊤)
    (hr : ∀ z,f (conj z)=conj (f z))
    (ha : ∀ z,z.re=0 ∨ z.im=0 → Even (multiplicity f z))
    (hs : Summable fun q : ZeroCopy f => 1/‖zeroCopyPoint f q‖^2) (z : ℂ) :
    analyticOrderAt (factor f * sharpFactor f) z=analyticOrderAt f z := by
  have hQ := factor_analytic hf h0 hs
  have hQr : Differentiable ℂ (sharpFactor f) :=
    RHTower.differentiable_conj_reflect (fun z => (hQ z (mem_univ _)).differentiableAt)
  by_cases hz : z=0
  · subst z
    rw [((hQ 0 (mem_univ _)).mul (hQr.analyticAt 0)).analyticOrderAt_eq_zero.mpr
      (by simp [sharpFactor,factor_zero]),(hf 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr h0]
  rw [analyticOrderAt_mul (hQ z (mem_univ _)) (hQr.analyticAt z)]
  have hsharp : analyticOrderAt (sharpFactor f) z=analyticOrderAt (factor f) (conj z) := by
    change analyticOrderAt (fun w => conj (factor f (conj w))) z = _
    have hh := RHTower.analyticOrderAt_conj_conj
      (fun z => (hQ z (mem_univ _)).differentiableAt) (conj z)
    rw [Complex.conj_conj] at hh
    exact hh
  rw [hsharp,factor_order hf h0 hs hz,factor_order hf h0 hs
    (by simpa using hz : conj z≠0),← Nat.cast_add,selectedMultiplicity_add_conj hf hr ha,
    multiplicity_cast_eq_order hf hfin]

open ValueDistribution Asymptotics in
theorem factor_mul_sharp_proximity {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (h0 : f 0≠0) (hs : Summable fun q : ZeroCopy f => 1/‖zeroCopyPoint f q‖^2) :
    proximity (factor f * sharpFactor f) ⊤ =o[Filter.atTop] fun r : ℝ => r^2 := by
  have hQ := factor_analytic hf h0 hs
  have hQr : Differentiable ℂ (sharpFactor f) :=
    RHTower.differentiable_conj_reflect (fun z => (hQ z (mem_univ _)).differentiableAt)
  have hp := canonicalProductE1Indexed_proximity_isLittleO_sq _
    (selectedPoint_ne_zero hf h0) (summable_selectedPoint_inv_sq hs)
  have hs' : Summable fun q : SelectedCopy f => 1/‖conj (selectedPoint f q)‖^2 := by
    simpa only [Complex.norm_conj] using summable_selectedPoint_inv_sq hs
  have hpr := canonicalProductE1Indexed_proximity_isLittleO_sq _
    (fun q => by simpa using selectedPoint_ne_zero hf h0 q : ∀ q,conj (selectedPoint f q)≠0) hs'
  have he : sharpFactor f=canonicalProductE1Indexed (fun q => conj (selectedPoint f q)) :=
    funext (sharpFactor_eq_product hf h0 hs)
  rw [← he] at hpr
  have hsum := hp.add hpr
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [isLittleO_iff.mp hsum hc] with r hr
  rw [Real.norm_eq_abs,abs_of_nonneg (proximity_nonneg r)]
  calc
    proximity (factor f * sharpFactor f) ⊤ r ≤
        proximity (factor f) ⊤ r + proximity (sharpFactor f) ⊤ r :=
      proximity_mul_top_le (fun z => (hQ z (mem_univ _)).meromorphicAt)
        (fun z => (hQr.analyticAt z).meromorphicAt) r
    _ ≤ c*‖r^2‖ := by
      simpa only [factor,Pi.add_apply,Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (proximity_nonneg r) (proximity_nonneg r))] using hr

open ValueDistribution Asymptotics in
/-- The selected divisor gives an exact even Hermitian factorization. The
axis multiplicities are the only divisor condition beyond the two symmetries. -/
theorem eq_origin_mul_factor_mul_sharp {f : ℂ → ℂ} {C : ℝ} (hC : 0≤C)
    (hf : AnalyticOnNhd ℂ f Set.univ) (h0 : f 0≠0)
    (he : ∀ z,f (-z)=f z) (hr : ∀ z,f (conj z)=conj (f z))
    (ha : ∀ z,z.re=0 ∨ z.im=0 → Even (multiplicity f z))
    (hb : ∀ z,‖f z‖≤Real.exp (C*(1+‖z‖)*Real.log (2+‖z‖))) (z : ℂ) :
    f z=f 0*(factor f z*sharpFactor f z) := by
  have hfin (w : ℂ) : analyticOrderAt f w≠⊤ := by
    intro ht
    have hz : f=(fun _ => 0) := hf.eq_of_eventuallyEq (fun _ _ => analyticAt_const)
      (analyticOrderAt_eq_top.mp ht)
    exact h0 (congrFun hz 0)
  have hs := RHTower.OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf h0 hb
  have hQ := factor_analytic hf h0 hs
  have hQr : Differentiable ℂ (sharpFactor f) :=
    RHTower.differentiable_conj_reflect (fun z => (hQ z (mem_univ _)).differentiableAt)
  let G := factor f * sharpFactor f
  have hGa : AnalyticOnNhd ℂ G Set.univ :=
    fun w _ => (hQ w (mem_univ _)).mul (hQr.analyticAt w)
  have hG0 : G 0=1 := by simp [G,sharpFactor,factor_zero]
  have hGe (w : ℂ) : G (-w)=G w := by
    simp only [G,Pi.mul_apply,sharpFactor,map_neg,factor_even hf he]
  have hord (w : ℂ) : analyticOrderAt G w=analyticOrderAt f w :=
    factor_mul_sharp_order hf h0 hfin hr ha hs w
  obtain ⟨H,hHd,hHne,hfac⟩ :=
    GaloisForLFunctions.EntireQuotient.exists_entire_nonvanishing_quotient hf hGa hfin
      (fun w => (hord w).symm) (by rw [hG0]; exact one_ne_zero)
  have hHae : (fun w => H (-w)) =ᶠ[𝓝 0] H := by
    have hGne : ∀ᶠ w in 𝓝 0,G w≠0 :=
      (hGa 0 (mem_univ _)).continuousAt.eventually_ne (by rw [hG0]; exact one_ne_zero)
    filter_upwards [hGne] with w hw
    have hn := hfac (-w)
    rw [he,hGe] at hn
    exact mul_right_cancel₀ hw (hn.symm.trans (hfac w))
  have hHe (w : ℂ) : H (-w)=H w := by
    have hHa : AnalyticOnNhd ℂ H univ := fun w _ => hHd.analyticAt w
    have hHna : AnalyticOnNhd ℂ (fun w => H (-w)) univ := fun w _ =>
      (hHd.analyticAt (-w)).comp (by fun_prop)
    exact congrFun (hHna.eq_of_eventuallyEq hHa hHae) w
  have hconst := RHTower.OrderOneRigidity.exists_const_of_even_entire_quotient
    (fun w => (hGa w (mem_univ _)).differentiableAt)
    (fun w => (hf w (mem_univ _)).differentiableAt) hHd
    (fun w => by rw [(hGa w (mem_univ _)).meromorphicOrderAt_eq,hord]; simp [hfin w])
    (fun w => by rw [(hf w (mem_univ _)).meromorphicOrderAt_eq]; simp [hfin w])
    hHne hfac hHe (factor_mul_sharp_proximity hf h0 hs)
    (RHTower.OrderOneRigidity.proximity_isLittleO_sq_of_growth hC
      (fun w => (hf w (mem_univ _)).differentiableAt) hb)
  have hH0 : H 0=f 0 := by simpa only [hG0,mul_one] using (hfac 0).symm
  rw [hfac z,hconst z,hH0]
  rfl

end GaloisForLFunctions.HTGeometry.EvenHermitianFactor
