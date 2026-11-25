import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder.DominantTerms

/-! # Rational leading orders of continuous algebraic contacts in real time -/

open Set Filter Topology Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
open BudgetComparisons
noncomputable section

/-- An upper bound by a power of the remaining time gives a lower bound
on the rational order of any positive leading term. -/
theorem order_ge_of_power_bound {f : ℝ → ℝ} {v c K : ℝ} {q p m : ℕ}
    (hc : 0 < c) (hlim : Tendsto (fun t => f t^q/(v-t)^p) (𝓝[<] v) (𝓝 c))
    (hpos : ∀ᶠ t in 𝓝[<] v, 0 ≤ f t) (hb : ∀ᶠ t in 𝓝[<] v, f t ≤ K*(v-t)^m) :
    m*q ≤ p := by
  by_contra! h
  have hx : Tendsto (fun t : ℝ => v-t) (𝓝[<] v) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => v-t) := continuous_const.sub continuous_id
    simpa only [sub_self] using (hcont.tendsto v).mono_left
      (nhdsWithin_le_nhds : 𝓝[<] v ≤ 𝓝 v)
  have hz : Tendsto (fun t => K^q*(v-t)^(m*q-p)) (𝓝[<] v) (𝓝 0) := by
    simpa only [zero_pow (Nat.sub_pos_of_lt h).ne',mul_zero] using (hx.pow (m*q-p)).const_mul (K^q)
  apply hc.not_ge (le_of_tendsto_of_tendsto hlim hz ?_)
  filter_upwards [hpos,hb,self_mem_nhdsWithin] with t ht hK htv
  apply (div_le_iff₀ (pow_pos (sub_pos.mpr htv) p)).mpr
  calc
    f t^q ≤ (K*(v-t)^m)^q := pow_le_pow_left₀ ht hK q
    _ = K^q*(v-t)^(m*q-p)*(v-t)^p := by
      rw [mul_pow,←pow_mul,mul_assoc,←pow_add,Nat.sub_add_cancel h.le]

/-- A positive one-sided branch meeting zero has an exact leading power.
The difference of two monomial degrees gives the denominator of its order;
the difference of the corresponding analytic vanishing orders gives the numerator. -/
theorem algebraic_contact_order {f : ℝ → ℝ} (hf : Continuous f) (ha : IsAlgebraic coefficients f)
    (v : ℝ) (hv : f v=0) (hpos : ∀ᶠ t in 𝓝[<] v, 0<f t) :
    ∃ q p : ℕ, 0<q ∧ 0<p ∧ ∃ c>0, Tendsto (fun t => f t^q/(v-t)^p) (𝓝[<] v) (𝓝 c) := by
  obtain ⟨P,hP,hroot⟩ := ha
  let a (i : ℕ) (t : ℝ) := atTime t (P.coeff i)
  let u (i : ℕ) (t : ℝ) := a i t*f t^i
  let M := (P.support.card:ℝ)
  obtain ⟨i,hi,j,hj,hij,hbal⟩ := frequent_balance P hP hroot v hpos
  have hM : 0<M := Nat.cast_pos.mpr (Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP))
  have hct (i : ℕ) : Continuous (fun t => (u i t)^2) :=
    ((continuous_coefficient _).mul (hf.pow i)).pow 2
  have hat (i : ℕ) : IsAlgebraic coefficients (fun t => (u i t)^2) :=
    ((show IsAlgebraic coefficients (a i) from isAlgebraic_algebraMap (P.coeff i)).mul
      ((show IsAlgebraic coefficients f from ⟨P,hP,hroot⟩).pow i)).pow 2
  obtain ⟨r,A,hA,hAi⟩ := coefficient_order _ (mem_support_iff.mp hi) v
  obtain ⟨s,B,hB,hBj⟩ := coefficient_order _ (mem_support_iff.mp hj) v
  have hn (k : ℕ) (m : ℕ) (C : ℝ) (hC : 0<C)
      (hc : Tendsto (fun t => |a k t|/(v-t)^m) (𝓝[<] v) (𝓝 C)) :
      ∀ᶠ t in 𝓝[<] v, a k t≠0 := (hc.eventually_const_lt hC).mono fun _ ht hz => by
    simpa only [hz,abs_zero,zero_div,lt_self_iff_false] using ht
  have hni := hn i r A hA hAi
  have hnj := hn j s B hB hBj
  have hden : ∀ᶠ t in 𝓝[<] v, 0<(u i t)^2 := (hni.and hpos).mono fun t h =>
    sq_pos_of_ne_zero (mul_ne_zero h.1 (pow_ne_zero _ h.2.ne'))
  have hrange : ∃ᶠ t in 𝓝[<] v, (u j t)^2/(u i t)^2∈Icc (1/M^2) (M^2) := by
    apply (hbal.and_eventually hden).mono
    intro t ht
    obtain ⟨⟨h₁,h₂⟩,hd⟩ := ht
    change |u i t|≤M*|u j t| at h₁
    change |u j t|≤M*|u i t| at h₂
    have hi₂ := pow_le_pow_left₀ (abs_nonneg _) h₁ 2
    have hj₂ := pow_le_pow_left₀ (abs_nonneg _) h₂ 2
    simp only [mul_pow,sq_abs] at hi₂ hj₂
    exact ⟨(div_le_div_iff₀ (sq_pos_of_pos hM) hd).mpr (by simpa only [one_mul,mul_comm] using hi₂),
      (div_le_iff₀ hd).mpr hj₂⟩
  obtain ⟨C,hC,hlim⟩ := algebraic_ratio_limit (hct j) (hat j) (hct i) (hat i) v hden hrange
  have hC₀ := (one_div_pos.mpr (sq_pos_of_pos hM)).trans_le hC.1
  let q := 2*(j-i)
  have hq : 0<q := Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hij)
  let c := C*(A/B)^2
  have hc : 0<c := mul_pos hC₀ (sq_pos_of_pos (div_pos hA hB))
  have hnorm : Tendsto (fun t => f t^q*(v-t)^(2*s)/(v-t)^(2*r)) (𝓝[<] v) (𝓝 c) := by
    apply (hlim.mul ((hAi.div hBj hB.ne').pow 2)).congr'
    filter_upwards [hni,hnj,hpos,self_mem_nhdsWithin] with t hi' hj' hf' ht
    change (u j t)^2/(u i t)^2*( (|a i t|/(v-t)^r)/(|a j t|/(v-t)^s) )^2=_
    dsimp only [u,q]
    rw [show f t^j=f t^i*f t^(j-i) by
      rw [←pow_add,show i+(j-i)=j by omega]]
    rw [Nat.mul_comm 2 (j-i),Nat.mul_comm 2 s,Nat.mul_comm 2 r]
    simp only [pow_mul,div_pow,mul_pow,sq_abs]
    field_simp [hi',hj',hf'.ne',(sub_pos.mpr ht).ne']
    ring
  have hx : Tendsto (fun t : ℝ => v-t) (𝓝[<] v) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => v-t) := continuous_const.sub continuous_id
    simpa only [sub_self] using (hcont.tendsto v).mono_left
      (nhdsWithin_le_nhds : 𝓝[<] v≤𝓝 v)
  have hsr : s<r := by
    by_contra! hh
    have hf₀ : Tendsto f (𝓝[<] v) (𝓝 0) := hv ▸ hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Tendsto (fun t => f t^q*(v-t)^(2*(s-r))) (𝓝[<] v) (𝓝 0) := by
      simpa only [zero_pow hq.ne',zero_mul] using (hf₀.pow q).mul (hx.pow (2*(s-r)))
    have heq : (fun t => f t^q*(v-t)^(2*s)/(v-t)^(2*r)) =ᶠ[𝓝[<] v] (fun t => f t^q*(v-t)^(2*(s-r))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [show 2*s=2*(s-r)+2*r by omega,pow_add]
      field_simp [(sub_pos.mpr ht).ne']
    exact hc.ne' (tendsto_nhds_unique (hnorm.congr' heq) hzero)
  refine ⟨q,2*(r-s),hq,Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hsr),c,hc,hnorm.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [show 2*r=2*(r-s)+2*s by omega,pow_add]
  field_simp [(sub_pos.mpr ht).ne']

#print axioms algebraic_contact_order
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
