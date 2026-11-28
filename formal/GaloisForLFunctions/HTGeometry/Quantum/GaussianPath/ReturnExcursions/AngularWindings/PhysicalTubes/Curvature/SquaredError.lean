import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Laboratory

/-! # Convexity of squared operator error along a lifted phase segment -/

open Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open private fill_interval from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Chart
open private frame_distance from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Laboratory
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Below the semicircle threshold, unequal squared errors interpolate linearly
as an upper bound along the entire angular segment. -/
theorem segment_square (W : unitary (Mat I)) (a b : I → ℝ) (hspan : ∀ i, |b i-a i|≤π)
    (ha : ‖(anglePacket a).val-W.val‖^2<2) (hb : ‖(anglePacket b).val-W.val‖^2<2) :
    ∀ t∈Icc (0:ℝ) 1, ‖(anglePacket fun i => a i+t*(b i-a i)).val-W.val‖^2≤
      (1-t)*‖(anglePacket a).val-W.val‖^2+t*‖(anglePacket b).val-W.val‖^2 := by
  let A := ‖(anglePacket a).val-W.val‖^2
  let B := ‖(anglePacket b).val-W.val‖^2
  let f (t : ℝ) (i : I) := a i+t*(b i-a i)
  let F (t : ℝ) := ‖(anglePacket (f t)).val-W.val‖^2
  let L (t : ℝ) := (1-t)*A+t*B
  have hL (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : L t<2 := by
    calc
      _ ≤ (1-t)*max A B+t*max A B := add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left ..) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (le_max_right ..) ht.1)
      _ = max A B := by ring
      _ < 2 := max_lt_iff.mpr ⟨ha,hb⟩
  let S := {t | F t≤L t}
  have hc : IsClosed S := by
    apply isClosed_le
    · unfold F anglePacket f
      fun_prop
    · unfold L
      fun_prop
  have hf₁ : f 1=b := funext fun i => by dsimp only [f]; ring
  apply fill_interval S hc (by simp [S,F,f,L,A]) (by simp [S,F,hf₁,L,B])
  intro p hp q hq hpi hqi
  have hδ (i) : |f q i-f p i|≤π := by
    rw [show f q i-f p i=(q-p)*(b i-a i) by dsimp only [f]; ring,abs_mul]
    have ht : |q-p|≤1 := abs_le.mpr ⟨by linarith only [hpi.2,hqi.1],by linarith only [hqi.2,hpi.1]⟩
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans ((one_mul _).le.trans (hspan i))
  have hs : F p+F q<4 := by linarith only [show F p≤L p from hp,show F q≤L q from hq,hL p hpi,hL q hqi]
  have hm := angle_midpoint_square W (f p) (f q) hs hδ le_rfl le_rfl
  have hf : (fun i => (f p i+f q i)/2)=f ((p+q)/2) := funext fun i => by dsimp only [f]; ring
  rw [hf] at hm
  change 2*F ((p+q)/2)≤F p+F q at hm
  have heq : 2*L ((p+q)/2)=L p+L q := by dsimp only [L]; ring
  change F ((p+q)/2)≤L ((p+q)/2)
  linarith only [hm,heq,show F p≤L p from hp,show F q≤L q from hq]

/-- Between two true fits on the same winding a single interpolated global
phase achieves the chord joining their squared errors. The circuit stays fixed
in the laboratory basis throughout the interval. -/
theorem laboratory_winding_secant (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (m : I → ℤ)
    {u v x e₀ e₁ : ℝ} (hx : x≤1/2) (he₀ : e₀^2<2) (he₁ : e₁^2<2) :
    let V := H.2.isHermitian.eigenvectorUnitary
    let Y := V⁻¹*W*V
    let A (i : I) := -H.2.isHermitian.eigenvalues i/(2*π)
    u∈wordDates Y A (circuitTurns Y) m x e₀ → v∈wordDates Y A (circuitTurns Y) m x e₁ →
      ∀ r∈Icc (0:ℝ) 1, ∃ z : ℂ, ‖z‖=1 ∧
        ‖unitaryEvolution H.val (u+r*(v-u))-z • W.val‖^2≤(1-r)*e₀^2+r*e₁^2 := by
  rintro V Y A ⟨p,hp,h₀⟩ ⟨q,hq,h₁⟩ r hr
  let a (i : I) := 2*π*(u*A i-(m i:ℝ)-p)
  let b (i : I) := 2*π*(v*A i-(m i:ℝ)-q)
  let t := u+r*(v-u)
  let P := p+r*(q-p)
  have hspan (i) : |b i-a i|≤π := by
    have hL := abs_le.mp (hp i)
    have hR := abs_le.mp (hq i)
    have hh : |(v*A i-(m i:ℝ)-q)-(u*A i-(m i:ℝ)-p)|≤x :=
      abs_le.mpr ⟨by linarith only [hL.2,hR.1],by linarith only [hL.1,hR.2]⟩
    dsimp only [a,b]
    rw [←mul_sub,abs_mul,abs_of_pos two_pi_pos]
    linarith only [mul_le_mul_of_nonneg_left (hh.trans hx) two_pi_pos.le]
  have ha := pow_le_pow_left₀ (norm_nonneg _) h₀ 2
  have hb := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have hh := segment_square Y a b hspan (ha.trans_lt he₀) (hb.trans_lt he₁) r hr
  have hbound := hh.trans (add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hr.2))
    (mul_le_mul_of_nonneg_left hb hr.1))
  have hi (i) : a i+r*(b i-a i)=2*π*(t*A i-(m i:ℝ)-P) := by dsimp only [a,b,t,P]; ring
  simp only [hi,packet_lift] at hbound
  rw [frame_distance H W t P] at hbound
  exact ⟨_,Complex.norm_exp_ofReal_mul_I _,hbound⟩

#print axioms segment_square
#print axioms laboratory_winding_secant
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
