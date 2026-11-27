import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Spectrum

/-! # Universal two-order calibration over any countable energy alphabet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family

open Set

variable {L I : Type*} [Fintype I]

/-- Finite lists encode multiplicities. The exceptional set uses only ratios
from pairs of temperatures belonging to the same list. -/
def exceptional (h : L → ℝ) : Set ℝ :=
  ⋃ p : Σ n : ℕ, Fin n → L, ratios (fun i => h (p.2 i))

theorem countable_exceptional [Countable L] (h : L → ℝ) : (exceptional h).Countable :=
  Set.countable_iUnion fun p => (finite_ratios (fun i => h (p.2 i))).countable

/-- Exact criterion for simultaneous calibration over arbitrary finite lists,
with repetitions of any label allowed. -/
theorem alphabet_iff (h : L → ℝ) {r : ℝ} (hr : 0 < r) :
    (∀ n (a : Fin n → L) (d : ℝ),
      (agrees (h ∘ a) d ∧ agrees (h ∘ a) (r*d) ↔ d=0 ∨ Reflects (h ∘ a))) ↔
      r ∉ exceptional h := by
  constructor
  · intro all mem
    obtain ⟨p,hp⟩ := mem_iUnion.mp mem
    exact (pair_iff (h ∘ p.2) hr).mp (all p.1 p.2) hp
  · intro good n a
    exact (pair_iff (h ∘ a) hr).mpr fun m => good (mem_iUnion.mpr ⟨⟨n,a⟩,m⟩)

/-- The calibration depends on the alphabet alone and applies to every finite carrier. -/
theorem calibrated (h : L → ℝ) (a : I → L) {r : ℝ} (hr : 0 < r) (good : r ∉ exceptional h) (d : ℝ) :
    (agrees (h ∘ a) d ∧ agrees (h ∘ a) (r*d) ↔ d=0 ∨ Reflects (h ∘ a)) := by
  let e := Fintype.equivFin I
  let b := a ∘ e.symm
  have pair : Matches (h ∘ a) (h ∘ b) := ⟨e,fun i => by simp [b]⟩
  rw [agrees_congr pair,agrees_congr pair,reflects_congr pair]
  exact (alphabet_iff h hr).mpr good _ b d

theorem good_between [Countable L] (h : L → ℝ) {a b : ℝ} (ab : a < b) :
    ∃ r ∈ Ioo a b, r ∉ exceptional h := by
  obtain ⟨r,g,m⟩ := ((countable_exceptional h).dense_compl ℝ).exists_between ab
  exact ⟨r,m,g⟩

#print axioms countable_exceptional
#print axioms alphabet_iff
#print axioms calibrated
#print axioms good_between

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family
