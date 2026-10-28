import GaloisForLFunctions.ArtinMertens.TheFrobeniusDensityTheoremInMertensForm
import GaloisForLFunctions.ArtinMertens.TheMertensTheoremForPrimeIdealsHasABoundedError

/-!
# Mertens' theorem for rational Artin characters

Let `G` be a Galois group of a number field `L` over `ℚ` and `Frob_p` any choice of Frobenius
elements at the primes `p ∤ disc L`. For every division-constant `φ : G → ℝ` (in particular every
character of a representation over `ℚ`),
`Σ_{p ≤ x, p ∤ disc L} φ(Frob_p) log p/p = ⟨φ, 1⟩ log x + O(1)` (`exists_abs_frobMertens_sub_le`).
For the indicator of a division `Δ`: `Σ_{Frob_p ∈ Δ} log p/p = (|Δ|/|G|) log x + O(1)`
(`exists_abs_frobMertens_divisionIndicator_sub_le`).

The bounded error passes along the chain of the soft theorem: Mertens with bounded error for prime
ideals (`exists_abs_primeMertens_sub_log_le`), the bounded difference to the degree-one primes
(`primeMertens_sub_degreeOneMertens_le`), the bounded ramified part
(`degreeOneMertens_eq`, `ramifiedMertens_le`), and linearity over `span_ℝ {π_H}` with Artin
induction (`mem_permSpan_of_isDivisionConstant`).
-/

noncomputable section

open NumberField Finset Filter Topology Module
open scoped Classical

namespace GaloisForLFunctions.ArtinMertens

/-- **Degree-one primes with bounded error**: `Σ_{p ≤ x} n_K(p) log p/p = log x + O(1)`. -/
theorem exists_abs_degreeOneMertens_sub_log_le (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → |degreeOneMertens K x - Real.log x| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_primeMertens_sub_log_le (K := K)
  refine ⟨C + (finrank ℤ (𝓞 K) : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail), fun x hx => ?_⟩
  have h := primeMertens_sub_degreeOneMertens_le (K := K) x
  have h' := abs_le.mp (hC x hx)
  rw [abs_le]
  constructor <;> linarith [h.1, h.2, h'.1, h'.2]

variable {L : Type*} [Field L] [NumberField L] {G : Type*} [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G ℚ L]

/-- **Permutation characters with bounded error**:
`Σ_{p ≤ x, p ∤ disc L} π_H(Frob_p) log p/p = log x + O(1)`. -/
theorem exists_abs_frobMertens_permChar_sub_log_le {frob : ℕ → G}
    (hfrob : IsFrobeniusChoice L frob) (H : Subgroup G) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → |frobMertens L frob (permChar H) x - Real.log x| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_degreeOneMertens_sub_log_le (invariantField L H)
  refine ⟨C + ramifiedMertens (L := L) H (discr L).natAbs, fun x hx => ?_⟩
  have h := degreeOneMertens_eq hfrob H x
  have h₁ := ramifiedMertens_nonneg (L := L) H x
  have h₂ := ramifiedMertens_le (L := L) H x
  have h' := abs_le.mp (hC x hx)
  rw [abs_le]
  constructor <;> linarith [h'.1, h'.2]

/-- **Bounded error on the span of the permutation characters**. -/
theorem exists_abs_frobMertens_sub_le_of_mem {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob)
    {φ : G → ℝ} (hφ : φ ∈ permSpan G) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → |frobMertens L frob φ x - classMean φ * Real.log x| ≤ C := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨H, rfl⟩ := hφ
    obtain ⟨C, hC⟩ := exists_abs_frobMertens_permChar_sub_log_le hfrob H
    exact ⟨C, fun x hx => by rw [classMean_permChar, one_mul]; exact hC x hx⟩
  | zero =>
    exact ⟨0, fun x _ => by simp [frobMertens, classMean]⟩
  | add φ ψ _ _ hφ hψ =>
    obtain ⟨C₁, hC₁⟩ := hφ
    obtain ⟨C₂, hC₂⟩ := hψ
    refine ⟨C₁ + C₂, fun x hx => ?_⟩
    rw [frobMertens_add, classMean_add,
      show frobMertens L frob φ x + frobMertens L frob ψ x - (classMean φ + classMean ψ) *
        Real.log x = (frobMertens L frob φ x - classMean φ * Real.log x) +
          (frobMertens L frob ψ x - classMean ψ * Real.log x) by ring]
    exact (abs_add_le _ _).trans (add_le_add (hC₁ x hx) (hC₂ x hx))
  | smul c φ _ hφ =>
    obtain ⟨C, hC⟩ := hφ
    refine ⟨|c| * C, fun x hx => ?_⟩
    rw [frobMertens_smul, classMean_smul,
      show c * frobMertens L frob φ x - c * classMean φ * Real.log x =
        c * (frobMertens L frob φ x - classMean φ * Real.log x) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg c)

/-- **Mertens' theorem for rational Artin characters**: for every division-constant `φ` and every
choice of Frobenius elements, `Σ_{p ≤ x, p ∤ disc L} φ(Frob_p) log p/p = ⟨φ, 1⟩ log x + O(1)`. -/
theorem exists_abs_frobMertens_sub_le {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob)
    {φ : G → ℝ} (hφ : IsDivisionConstant φ) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → |frobMertens L frob φ x - classMean φ * Real.log x| ≤ C :=
  exists_abs_frobMertens_sub_le_of_mem hfrob (mem_permSpan_of_isDivisionConstant hφ)

/-- **The Frobenius density theorem with bounded error**: the primes whose Frobenius lies in the
division `Δ` of `g₀` satisfy `Σ_{Frob_p ∈ Δ} log p/p = (|Δ|/|G|) log x + O(1)`. -/
theorem exists_abs_frobMertens_divisionIndicator_sub_le {frob : ℕ → G}
    (hfrob : IsFrobeniusChoice L frob) (g₀ : G) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |frobMertens L frob (divisionIndicator g₀) x -
        classMean (divisionIndicator g₀) * Real.log x| ≤ C :=
  exists_abs_frobMertens_sub_le hfrob (isDivisionConstant_divisionIndicator g₀)

end GaloisForLFunctions.ArtinMertens
