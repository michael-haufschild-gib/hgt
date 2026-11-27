import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! # Sharp simultaneous error for finitely many prescribed odd lifts -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers

open Finset

variable {I : Type*} [Fintype I] [Nonempty I]

def peak (f : I → ℝ) := univ.sup' univ_nonempty f

theorem to_peak (f : I → ℝ) (i : I) : f i ≤ peak f := le_sup' _ (mem_univ i)

theorem peak_le {f : I → ℝ} {a : ℝ} : peak f ≤ a ↔ ∀ i, f i ≤ a := by
  simp only [peak,sup'_le_iff,mem_univ,true_implies]

theorem peak_value (f : I → ℝ) : ∃ i, peak f=f i := by
  obtain ⟨i,_,h⟩ := exists_mem_eq_sup' univ_nonempty f
  exact ⟨i,h⟩

/-- Largest separation of two centers divided by the sum of their
reciprocal slopes, expressed without dividing either center by its slope. -/
def fitRadius (k : I → ℕ+) (a : I → ℝ) := peak fun ij : I × I =>
  |(k ij.2 : ℝ)*a ij.1-(k ij.1 : ℝ)*a ij.2| / ((k ij.1 : ℝ)+(k ij.2 : ℝ))

/-- Intersecting the intervals of admissible phases is equivalent to a
pairwise determinant bound. The largest lower endpoint attains the radius. -/
theorem fit_iff (k : I → ℕ+) (a : I → ℝ) (e : ℝ) :
    (∃ u : ℝ, ∀ i, |(k i : ℝ)*u-a i| ≤ e) ↔ fitRadius k a ≤ e := by
  have pos (i : I) : 0<(k i : ℝ) := Nat.cast_pos.mpr (k i).pos
  have pair (i j : I) :
      (a i-e)/(k i : ℝ) ≤ (a j+e)/(k j : ℝ) ↔
        (k j : ℝ)*a i-(k i : ℝ)*a j ≤ e*((k i : ℝ)+(k j : ℝ)) := by
    rw [div_le_div_iff₀ (pos i) (pos j)]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · rintro ⟨u,hu⟩
    have ends (i : I) : (a i-e)/(k i : ℝ) ≤ u ∧ u ≤ (a i+e)/(k i : ℝ) := by
      obtain ⟨lo,hi⟩ := abs_le.mp (hu i)
      rw [div_le_iff₀ (pos i),le_div_iff₀ (pos i)]
      constructor <;> linarith only [lo,hi]
    apply peak_le.mpr
    rintro ⟨i,j⟩
    apply (div_le_iff₀ (add_pos (pos i) (pos j))).mpr
    apply abs_le.mpr
    have ij := (pair i j).mp ((ends i).1.trans (ends j).2)
    have ji := (pair j i).mp ((ends j).1.trans (ends i).2)
    constructor <;> linarith only [ij,ji]
  · intro h
    let u := peak fun i => (a i-e)/(k i : ℝ)
    refine ⟨u,fun j => ?_⟩
    have lo := to_peak (fun i => (a i-e)/(k i : ℝ)) j
    change (a j-e)/(k j : ℝ) ≤ u at lo
    have hi : u ≤ (a j+e)/(k j : ℝ) := by
      apply peak_le.mpr
      intro i
      apply (pair i j).mpr
      have bound := peak_le.mp h (i,j)
      exact (le_abs_self _).trans ((div_le_iff₀ (add_pos (pos i) (pos j))).mp bound)
    rw [div_le_iff₀ (pos j)] at lo
    rw [le_div_iff₀ (pos j)] at hi
    exact abs_le.mpr ⟨by linarith only [lo],by linarith only [hi]⟩

/-- One odd center for each occupation in a full phase period. -/
abbrev Centers (k : I → ℕ+) := ∀ i, Fin (k i : ℕ)

instance centersFintype (k : I → ℕ+) : Fintype (Centers k) := by
  classical
  unfold Centers
  infer_instance

instance centersNonempty (k : I → ℕ+) : Nonempty (Centers k) :=
  ⟨fun i => ⟨0,(k i).pos⟩⟩

def oddCenter (k : I → ℕ+) (a : Centers k) (i : I) : ℝ := 2*(a i : ℕ)+1

/-- Finite arithmetic formula for the smallest simultaneous phase error. -/
def defect (k : I → ℕ+) :=
  (@univ (Centers k) _).inf' univ_nonempty (fun a => fitRadius k (oddCenter k a))

theorem defect_le (k : I → ℕ+) (a : Centers k) : defect k ≤ fitRadius k (oddCenter k a) :=
  inf'_le _ (mem_univ a)

theorem defect_witness (k : I → ℕ+) :
    ∃ a : Centers k, ∃ u : ℝ, ∀ i, |(k i : ℝ)*u-oddCenter k a i| ≤ defect k := by
  obtain ⟨a,_,h⟩ := exists_mem_eq_inf' (univ_nonempty (α := Centers k))
    (fun a => fitRadius k (oddCenter k a))
  exact ⟨a,(fit_iff _ _ _).mpr h.ge⟩

theorem defect_range (k : I → ℕ+) : 0 ≤ defect k ∧ defect k ≤ 1 := by
  obtain ⟨a,u,hit⟩ := defect_witness k
  let i : I := Classical.choice inferInstance
  refine ⟨(abs_nonneg _).trans (hit i),?_⟩
  let zero : Centers k := fun j => ⟨0,(k j).pos⟩
  apply (defect_le k zero).trans
  apply (fit_iff _ _ _).mp
  exact ⟨0,by intro j; norm_num [zero,oddCenter]⟩

#print axioms to_peak
#print axioms peak_le
#print axioms peak_value
#print axioms fit_iff
#print axioms defect_le
#print axioms defect_witness
#print axioms defect_range

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers
