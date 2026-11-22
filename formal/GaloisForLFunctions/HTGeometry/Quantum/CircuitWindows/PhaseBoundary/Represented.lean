import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteEquations
import Mathlib.Data.Complex.Basic

/-! # Real and complex expressions in the polynomial incidence ring -/
open Set
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A X : Type*} [CommRing A] (ρ : X → A →+* ℝ)

/-- A real coordinate given by one element of the parameter ring. -/
def Represents (f : X → ℝ) : Prop := ∃ a : A, ∀ x, ρ x a = f x

variable {ρ}
theorem Represents.zero : Represents ρ (fun _ => 0) := ⟨0,fun x => (ρ x).map_zero⟩
theorem Represents.one : Represents ρ (fun _ => 1) := ⟨1,fun x => (ρ x).map_one⟩

theorem Represents.add {f g : X → ℝ} (hf : Represents ρ f) (hg : Represents ρ g) :
    Represents ρ (fun x => f x + g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨a+b,fun x => by rw [map_add,ha,hb]⟩

theorem Represents.sub {f g : X → ℝ} (hf : Represents ρ f) (hg : Represents ρ g) :
    Represents ρ (fun x => f x - g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨a-b,fun x => by rw [map_sub,ha,hb]⟩

theorem Represents.mul {f g : X → ℝ} (hf : Represents ρ f) (hg : Represents ρ g) :
    Represents ρ (fun x => f x * g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨a*b,fun x => by rw [map_mul,ha,hb]⟩

theorem Represents.neg {f : X → ℝ} (hf : Represents ρ f) : Represents ρ (fun x => -f x) := by
  obtain ⟨a,ha⟩ := hf
  exact ⟨-a,fun x => by rw [map_neg,ha]⟩

theorem Represents.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ} (h : ∀ i ∈ s, Represents ρ (f i)) :
    Represents ρ (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Represents.zero (ρ := ρ))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h _ (Finset.mem_insert_self ..)).add (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

/-- Both real coordinates of a complex entry are polynomial. -/
def ComplexRep (ρ : X → A →+* ℝ) (f : X → ℂ) : Prop :=
  Represents ρ (fun x => (f x).re) ∧ Represents ρ (fun x => (f x).im)

theorem ComplexRep.zero : ComplexRep ρ (fun _ => 0) := ⟨Represents.zero,Represents.zero⟩
theorem ComplexRep.one : ComplexRep ρ (fun _ => 1) := ⟨Represents.one,Represents.zero⟩

theorem ComplexRep.add {f g : X → ℂ} (hf : ComplexRep ρ f) (hg : ComplexRep ρ g) :
    ComplexRep ρ (fun x => f x + g x) := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
theorem ComplexRep.sub {f g : X → ℂ} (hf : ComplexRep ρ f) (hg : ComplexRep ρ g) :
    ComplexRep ρ (fun x => f x - g x) := ⟨hf.1.sub hg.1,hf.2.sub hg.2⟩
theorem ComplexRep.mul {f g : X → ℂ} (hf : ComplexRep ρ f) (hg : ComplexRep ρ g) :
    ComplexRep ρ (fun x => f x * g x) :=
  ⟨(hf.1.mul hg.1).sub (hf.2.mul hg.2),(hf.1.mul hg.2).add (hf.2.mul hg.1)⟩
theorem ComplexRep.star {f : X → ℂ} (hf : ComplexRep ρ f) :
    ComplexRep ρ (fun x => star (f x)) := ⟨hf.1,hf.2.neg⟩

theorem ComplexRep.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℂ} (h : ∀ i ∈ s, ComplexRep ρ (f i)) :
    ComplexRep ρ (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (ComplexRep.zero (ρ := ρ))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h _ (Finset.mem_insert_self ..)).add (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
