import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.SimpleContacts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius

/-! # Centering a spectral packet at a simple empty-circuit contact -/
open Set Real Matrix
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
open EmptyVisitFlux SharpOccupation

private theorem strict_lifts {I : Type*} (E : I → ℝ) (hi : Function.Injective E)
    {x t : ℝ} (ht : 0 < t) (hp : AvoidsTie E x) (hn : AvoidsTie E (-x))
    {i j : I} (h : pairFace (forwardUnitArc x) (fun k => E k/(2*π)) x t i j) :
    ∃ y : I → ℝ, y i=0 ∧ y j=x ∧ (∀ k, k≠i → k≠j → y k ∈ Ioo 0 x) ∧
      ∀ k, flow (fun l => E l/(2*π)) t k-flow (fun l => E l/(2*π)) t i=(y k:UnitAddCircle) := by
  classical
  let f := flow (fun l => E l/(2*π)) t
  have hij : i≠j := by rintro rfl; exact h.1.false
  have hh (k : I) (hki : k≠i) (hkj : k≠j) : ∃ y ∈ Ioo (0:ℝ) x, f k-f i=(y:UnitAddCircle) := by
    obtain ⟨y,hy,he⟩ := h.2.2 k hki hkj
    have h0 := simple_contact E hi hp ht i k j hki.symm hij.symm hkj.symm h.2.1
    have hx : f i-f j=((-x:ℝ):UnitAddCircle) := by rw [AddCircle.coe_neg,←h.2.1,neg_sub]; rfl
    have h1 := simple_contact E hi hn ht j k i hkj.symm hij hki.symm hx
    refine ⟨y,⟨hy.1.lt_of_ne (fun hz => h0 (sub_eq_zero.mp (by rw [←he,←hz]; simp))),?_⟩,he.symm⟩
    refine hy.2.lt_of_ne (fun hz => h1 ?_)
    exact sub_left_injective (f i) (he.symm.trans ((congrArg (fun z : ℝ => (z:UnitAddCircle)) hz).trans h.2.1.symm))
  let y (k : I) := if hk : k=i then 0 else if hk' : k=j then x else (hh k hk hk').choose
  refine ⟨y,by simp [y],by simp [y,hij.symm],?_,?_⟩
  · intro k hki hkj
    simpa only [y,dif_neg hki,dif_neg hkj] using (hh k hki hkj).choose_spec.1
  · intro k
    by_cases hki : k=i
    · subst k; simp [y]
    by_cases hkj : k=j
    · subst k; simpa [y,hij.symm] using h.2.1
    simpa only [y,dif_neg hki,dif_neg hkj] using (hh k hki hkj).choose_spec.2

/-- Up to a common phase, the two contacts are complex conjugates at
real part 1−ε²/2. Every remaining eigenvalue has strictly larger real part. -/
theorem face_packet {I : Type*} (E : I → ℝ) (hi : Function.Injective E)
    {ε t : ℝ} (hε : 0 < ε) (hs : ε < sqrt 2) (ht : 0 < t)
    (hp : AvoidsTie E (physicalArc ε)) (hn : AvoidsTie E (-(physicalArc ε)))
    {i j : I} (h : pairFace (forwardUnitArc (physicalArc ε)) (fun k => E k/(2*π)) (physicalArc ε) t i j) :
    ∃ (w : ℂ) (u : I → ℂ), ‖w‖=1 ∧ (∀ k, ‖u k‖=1) ∧
      (∀ k, Complex.exp (((t*E k:ℝ):ℂ)*Complex.I)=w*u k) ∧
      u i=star (u j) ∧ 0 < (u j).im ∧ (u j).re=1-ε^2/2 ∧
      ∀ k, k≠j → k≠i → (u j).re < (u k).re := by
  let x := physicalArc ε
  obtain ⟨hx,htol⟩ := physicalArc_spec hε hs
  change x ∈ Ioo (0:ℝ) (1/2) at hx
  change 2*sin (π*x/2)=ε at htol
  obtain ⟨y,hy0,hyx,hyint,hyl⟩ := strict_lifts E hi ht hp hn h
  let α := π*x
  let β (k : I) := 2*π*y k-α
  let c := t*E i+α
  let p (a : ℝ) := Complex.exp ((a:ℂ)*Complex.I)
  have hα : 0 < α := mul_pos pi_pos hx.1
  have hπ : α < π := by simpa only [mul_one] using mul_lt_mul_of_pos_left (hx.2.trans (by norm_num : (1/2:ℝ)<1)) pi_pos
  have hpos : β j=α := by dsimp only [β,α]; rw [hyx]; ring
  have hneg : β i= -α := by simp only [β,hy0,mul_zero,zero_sub]
  refine ⟨p c,fun k => p (β k),by simp [p,Complex.norm_exp],fun k => by simp [p,Complex.norm_exp],?_,?_,?_,?_,?_⟩
  · intro k
    obtain ⟨m,hm⟩ := lift_gap E t i k (hyl k)
    have he := (div_eq_iff (by positivity : 2*π≠0)).mp hm
    have hh := norm_expI_sub_expI_le (t*E k) (c+β k) m
    have hz : t*E k-(c+β k)-2*π*(m:ℝ)=0 := by dsimp only [c,β]; linarith only [he]
    rw [hz,abs_zero] at hh
    have heq := sub_eq_zero.mp (norm_le_zero_iff.mp hh)
    rw [heq]
    dsimp only [p]
    rw [←Complex.exp_add,Complex.ofReal_add,add_mul]
  · rw [hpos,hneg]
    apply Complex.ext <;> simp [p,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
  · rw [hpos]
    simpa only [p,Complex.exp_ofReal_mul_I_im] using Real.sin_pos_of_pos_of_lt_pi hα hπ
  · rw [hpos]
    change (p α).re=_
    rw [show (p α).re=cos α from Complex.exp_ofReal_mul_I_re _,show α=2*(π*x/2) by dsimp [α]; ring,
      Real.cos_two_mul_eq_one_sub,←htol]
    ring
  · intro k hkj hki
    have hkg := hyint k hki hkj
    have hβ : |β k| < α := by
      apply abs_lt.mpr
      have hl := mul_pos (by positivity : 0 < 2*π) hkg.1
      have hr := mul_lt_mul_of_pos_left hkg.2 (by positivity : 0 < 2*π)
      dsimp only [β,α]
      constructor <;> linarith only [hl,hr]
    rw [hpos]
    simpa only [p,Complex.exp_ofReal_mul_I_re,Real.cos_abs] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (β k)) hπ.le hβ

#print axioms face_packet
end
end GaloisForLFunctions.HTGeometry.FirstGate
