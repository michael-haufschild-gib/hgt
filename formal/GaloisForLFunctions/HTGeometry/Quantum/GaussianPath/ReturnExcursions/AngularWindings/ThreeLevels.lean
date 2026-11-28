import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.InverseTime
import Mathlib.Analysis.Convex.Radon

/-! # Three eigenlevels certify failure of an entire lifted winding -/

open Set Finset
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
noncomputable section

/-- The date and common phase range over a plane. On a fixed winding, Helly's
theorem reduces infeasibility throughout a time window to at most three levels.
Different triples may initially choose different dates and common phases. -/
theorem winding_iff_three_levels {J : Type*} [Fintype J] [Nonempty J]
    (A b : J → ℝ) (x T U : ℝ) :
    windingWindow A b x T U ↔ ∀ F : Finset J, F.card≤3 →
      ∃ t ∈ Icc T U, ∃ p : ℝ, ∀ i ∈ F, |t*A i-b i-p|≤x/2 := by
  classical
  constructor
  · rintro ⟨t,ht,p,hp⟩ F _
    exact ⟨t,ht,p,fun i _ => hp i⟩
  intro h
  let S (i : J) : Set (ℝ × ℝ) := {y | y.1∈Icc T U ∧ |y.1*A i-b i-y.2|≤x/2}
  have hc (i : J) : Convex ℝ (S i) := by
    rintro y ⟨hy,he⟩ z ⟨hz,hf⟩ a c ha hc hac
    change a*y.1+c*z.1 ∈ Icc T U ∧ |(a*y.1+c*z.1)*A i-b i-(a*y.2+c*z.2)|≤x/2
    refine ⟨(convex_Icc T U) hy hz ha hc hac,?_⟩
    have hid : (a*y.1+c*z.1)*A i-b i-(a*y.2+c*z.2)=
        a*(y.1*A i-b i-y.2)+c*(z.1*A i-b i-z.2) := by
      calc
        _ = (a*y.1+c*z.1)*A i-(a+c)*b i-(a*y.2+c*z.2) := by rw [hac,one_mul]
        _ = _ := by ring
    rw [hid]
    calc
      _ ≤ |a*(y.1*A i-b i-y.2)|+|c*(z.1*A i-b i-z.2)| := abs_add_le ..
      _ ≤ a*(x/2)+c*(x/2) := by
        rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hc]
        exact add_le_add (mul_le_mul_of_nonneg_left he ha) (mul_le_mul_of_nonneg_left hf hc)
      _ = _ := by rw [←add_mul,hac,one_mul]
  obtain ⟨y,hy⟩ := Convex.helly_theorem' (s:=univ) (fun i _ => hc i) (by
    intro F _ hF
    have hcard : F.card≤3 := by simpa only [Module.finrank_prod,Module.finrank_self] using hF
    obtain ⟨t,ht,p,hp⟩ := h F hcard
    exact ⟨(t,p),mem_iInter₂.mpr fun i hi => ⟨ht,hp i hi⟩⟩)
  have hh (i : J) : y∈S i := mem_iInter₂.mp hy i (mem_univ i)
  exact ⟨y.1,(hh (Classical.arbitrary J)).1,y.2,fun i => (hh i).2⟩

#print axioms winding_iff_three_levels
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
