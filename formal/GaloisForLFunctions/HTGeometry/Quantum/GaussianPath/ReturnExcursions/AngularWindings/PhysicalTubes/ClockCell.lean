import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Chart
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.EndpointWord

/-! # Full operator fit at all dates on a single circuit winding -/

open Set Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The full operator error and the chosen lifted angular ranges, in turns.
The scalar phase may depend on the date. -/
def wordDates (W : unitary (Mat I)) (A d : I → ℝ) (m : I → ℤ) (x ε : ℝ) : Set ℝ :=
  {t | ∃ p : ℝ, (∀ i, |t*A i-(d i+(m i:ℝ))-p|≤x/2) ∧
    ‖(anglePacket fun i => 2*π*(t*A i-(m i:ℝ)-p)).val-W.val‖≤ε}

/-- For one complete winding, all true operator fits to a fixed circuit form one
interval. The proof interpolates the two fitting global phases together with time. -/
theorem wordDates_convex (W : unitary (Mat I)) (A d : I → ℝ) (m : I → ℤ) {x ε : ℝ}
    (hx : x≤1/2) (hε : ε^2<2) : Convex ℝ (wordDates W A d m x ε) := by
  rintro s ⟨p,hp,hs⟩ t ⟨q,hq,ht⟩ a c ha hc hac
  let v (s p : ℝ) (i : I) := s*A i-(m i:ℝ)-p
  have hlin (i : I) : v (a*s+c*t) (a*p+c*q) i=a*v s p i+c*v t q i := by
    dsimp only [v]
    linear_combination (m i:ℝ)*hac
  refine ⟨a*p+c*q,?_,?_⟩
  · intro i
    have hmem (s p : ℝ) (h : |s*A i-(d i+(m i:ℝ))-p|≤x/2) : v s p i∈Icc (d i-x/2) (d i+x/2) := by
      obtain ⟨hl,hu⟩ := abs_le.mp h
      dsimp only [v]
      constructor <;> linarith only [hl,hu]
    have hh : a*v s p i+c*v t q i∈Icc (d i-x/2) (d i+x/2) :=
      convex_Icc _ _ (hmem s p (hp i)) (hmem t q (hq i)) ha hc hac
    rw [←hlin] at hh
    change |(a*s+c*t)*A i-(d i+(m i:ℝ))-(a*p+c*q)|≤x/2
    dsimp only [v] at hh
    exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  · let f (s p : ℝ) (i : I) := 2*π*v s p i
    have hspan (i : I) : |f t q i-f s p i|≤π := by
      have h₁ := abs_le.mp (hp i)
      have h₂ := abs_le.mp (hq i)
      have hd : |v t q i-v s p i|≤x := by
        dsimp only [v]
        exact abs_le.mpr ⟨by linarith only [h₁.2,h₂.1],by linarith only [h₂.2,h₁.1]⟩
      dsimp only [f]
      rw [←mul_sub,abs_mul,abs_of_pos two_pi_pos]
      calc
        _ ≤ (2*π)*(1/2) := mul_le_mul_of_nonneg_left (hd.trans hx) two_pi_pos.le
        _ = _ := by ring
    have he : f (a*s+c*t) (a*p+c*q)=(fun i => f s p i+c*(f t q i-f s p i)) := by
      funext i
      dsimp only [f]
      rw [hlin]
      linear_combination (2*π*v s p i)*hac
    change ‖(anglePacket (f (a*s+c*t) (a*p+c*q))).val-W.val‖≤ε
    rw [he]
    exact segment_fit W _ _ hε hspan hs ht c ⟨hc,by linarith only [ha,hac]⟩

/-- Every actual clock and global phase satisfying one lift also satisfy the
canonical word reconstructed from its extremal winding, at the exact same error. -/
theorem canonical_word_date (W : unitary (Mat I)) (A d : I → ℝ) (m : I → ℤ) (l u : I)
    {x ε t : ℝ} (hx : x<1/2) (hg : A l<A u) (hext : ∀ i, A i∈Icc (A l) (A u))
    (h : t∈wordDates W A d m x ε) :
    let N := m u-m l
    |t*(A u-A l)-(d u-d l)-(N:ℝ)|≤x ∧
    t∈wordDates W A d (fun i => ⌊targetWord A d l u N i+1/2⌋) x ε := by
  intro N
  obtain ⟨p,hp,hfit⟩ := h
  have hr (i : I) := endpoint_word_round A d m l u t p x hx hg hext hp i
  refine ⟨(endpoint_word A d m l u t p x hg hext hp).1,p+(m l:ℝ),?_,?_⟩
  · intro i
    change |t*A i-(d i+(⌊targetWord A d l u N i+1/2⌋:ℝ))-(p+(m l:ℝ))|≤x/2
    rw [hr,Int.cast_sub]
    convert hp i using 2
    ring
  · have hai (i : I) : t*A i-(⌊targetWord A d l u N i+1/2⌋:ℝ)-(p+(m l:ℝ))=t*A i-(m i:ℝ)-p := by
      rw [hr,Int.cast_sub]
      ring
    simpa only [hai] using hfit

#print axioms wordDates_convex
#print axioms canonical_word_date
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
