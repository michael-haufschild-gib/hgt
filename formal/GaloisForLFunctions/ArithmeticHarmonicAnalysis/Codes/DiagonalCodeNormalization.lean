import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.OddCharacteristicEuclidean
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.TriplyEvenOrthogonality

/-!
# Diagonal normalization of divisible codes

Multiplication by coordinate units is a linear Hamming isometry. Inverting
a full-support codeword turns it into the constant word, so the divisibility
criteria apply after an explicit diagonal equivalence. This realizes the
monomial-equivalence conclusion of Heng–Xie, Corollary 22 (arXiv:2611.13963),
and extends the same normalization to twisted and cubic pairings.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
variable {K ι : Type*} [Field K]

/-- Multiplication by one unit in each coordinate. -/
def diagonalWordEquiv (u : ι → Kˣ) : (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.piCongrRight (fun i => LinearEquiv.smulOfUnit (M := K) (u i))

theorem diagonalWordEquiv_apply (u : ι → Kˣ) (c : ι → K) (i : ι) :
    diagonalWordEquiv u c i = (u i : K) * c i := rfl

/-- The image code under an invertible diagonal coordinate transformation. -/
def diagonalCode (u : ι → Kˣ) (C : Submodule K (ι → K)) : Submodule K (ι → K) :=
  C.map (diagonalWordEquiv u).toLinearMap

/-- Diagonal coordinate scaling restricts to a linear equivalence of the two codes. -/
def diagonalCodeEquiv (u : ι → Kˣ) (C : Submodule K (ι → K)) :
    C ≃ₗ[K] diagonalCode u C :=
  Submodule.equivMapOfInjective (diagonalWordEquiv u).toLinearMap
    (diagonalWordEquiv u).injective C

/-- Invertible diagonal scaling preserves code dimension. -/
theorem diagonalCode_finrank (u : ι → Kˣ) (C : Submodule K (ι → K)) :
    Module.finrank K (diagonalCode u C) = Module.finrank K C :=
  (diagonalCodeEquiv u C).finrank_eq.symm

/-- Inverting the coordinates of a codeword of units sends it to the constant word. -/
theorem one_mem_inverse_diagonalCode (u : ι → Kˣ) (C : Submodule K (ι → K))
    (hu : (fun i => (u i : K)) ∈ C) :
    (fun _ => (1 : K)) ∈ diagonalCode (fun i => (u i)⁻¹) C := by
  refine ⟨(fun i => (u i : K)), hu, ?_⟩
  funext i
  exact (u i).inv_val

section Finite
variable [Fintype ι]

/-- Diagonal units preserve every word's Hamming weight. -/
theorem weight_diagonalWordEquiv (u : ι → Kˣ) (c : ι → K) :
    weight (diagonalWordEquiv u c) = weight c := by
  unfold weight
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [diagonalWordEquiv_apply]
  exact ⟨fun h => (mul_ne_zero_iff.mp h).2, fun h => mul_ne_zero (u i).ne_zero h⟩

/-- Every weight-divisibility condition is invariant under diagonal coordinate scaling. -/
theorem diagonalCode_divisible_iff (Δ : ℕ) (u : ι → Kˣ) (C : Submodule K (ι → K)) :
    Divisible Δ (diagonalCode u C) ↔ Divisible Δ C := by
  constructor
  · intro h c hc
    simpa only [weight_diagonalWordEquiv] using
      h (diagonalWordEquiv u c) ⟨c, hc, rfl⟩
  · rintro h c ⟨d, hd, rfl⟩
    change Δ ∣ weight (diagonalWordEquiv u d)
    rw [weight_diagonalWordEquiv]
    exact h d hd

/-- Full Hamming weight means that every coordinate is nonzero. -/
theorem weight_eq_card_iff (c : ι → K) :
    weight c = Fintype.card ι ↔ ∀ i, c i ≠ 0 := by
  change (Finset.univ.filter (fun i => c i ≠ 0)).card =
    (Finset.univ : Finset ι).card ↔ _
  rw [Finset.card_filter_eq_iff]
  simp only [Finset.mem_univ, forall_true_left]

/-- A full-support word determines one unit at each coordinate. -/
def fullWeightUnits (c : ι → K) (hc : weight c = Fintype.card ι) : ι → Kˣ :=
  fun i => Units.mk0 (c i) ((weight_eq_card_iff c).mp hc i)

/-- Diagonal scaling inserts the corresponding norm factors into the twisted pairing. -/
theorem twistedPair_diagonal (σ : K →+* K) (u : ι → Kˣ) (c d : ι → K) :
    twistedPair σ (diagonalWordEquiv u c) (diagonalWordEquiv u d) =
      ∑ i, ((u i : K) * σ (u i : K)) * (c i * σ (d i)) := by
  simp only [twistedPair, diagonalWordEquiv_apply, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Norm-one coordinate units preserve the full twisted pairing. -/
theorem twistedPair_diagonal_of_norm_one (σ : K →+* K) (u : ι → Kˣ)
    (hu : ∀ i, (u i : K) * σ (u i : K) = 1) (c d : ι → K) :
    twistedPair σ (diagonalWordEquiv u c) (diagonalWordEquiv u d) = twistedPair σ c d := by
  rw [twistedPair_diagonal]
  simp only [hu, one_mul, twistedPair]

/-- Norm-one diagonal transformations carry self-orthogonal codes to self-orthogonal codes. -/
theorem diagonalCode_selfOrthogonal_of_norm_one (σ : K →+* K) (u : ι → Kˣ)
    (hu : ∀ i, (u i : K) * σ (u i : K) = 1)
    (C : Submodule K (ι → K)) (hC : SelfOrthogonal σ C) :
    SelfOrthogonal σ (diagonalCode u C) := by
  rintro c ⟨a, ha, rfl⟩ d ⟨b, hb, rfl⟩
  change twistedPair σ (diagonalWordEquiv u a) (diagonalWordEquiv u b) = 0
  rw [twistedPair_diagonal_of_norm_one σ u hu]
  exact hC a ha b hb

section FiniteField
variable [Fintype K]

/-- A full-support word replaces the constant-word condition in the nonidentity-twist criterion. -/
theorem inverse_diagonalCode_twisted_selfOrthogonal (p : ℕ) [CharP K p]
    (σ : K →+* K) (hσ : σ ≠ RingHom.id K) (u : ι → Kˣ)
    (C : Submodule K (ι → K)) (hu : (fun i => (u i : K)) ∈ C)
    (hC : Divisible p C) : SelfOrthogonal σ (diagonalCode (fun i => (u i)⁻¹) C) :=
  divisible_selfOrthogonal p σ hσ _ (one_mem_inverse_diagonalCode u C hu)
    ((diagonalCode_divisible_iff p _ C).mpr hC)

/-- Odd-characteristic Euclidean orthogonality after normalization by a full-support word. -/
theorem inverse_diagonalCode_odd_selfOrthogonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p ≠ 2) (u : ι → Kˣ) (C : Submodule K (ι → K))
    (hu : (fun i => (u i : K)) ∈ C) (hC : Divisible p C) :
    SelfOrthogonal (RingHom.id K) (diagonalCode (fun i => (u i)⁻¹) C) :=
  oddCharacteristic_divisible_selfOrthogonal p hp _ (one_mem_inverse_diagonalCode u C hu)
    ((diagonalCode_divisible_iff p _ C).mpr hC)

variable [CharP K 2]

/-- Four-divisibility gives Euclidean orthogonality after diagonal normalization. -/
theorem inverse_diagonalCode_fourDivisible_selfOrthogonal (u : ι → Kˣ)
    (C : Submodule K (ι → K)) (hu : (fun i => (u i : K)) ∈ C)
    (hC : Divisible 4 C) : SelfOrthogonal (RingHom.id K) (diagonalCode (fun i => (u i)⁻¹) C) :=
  fourDivisible_selfOrthogonal _ (one_mem_inverse_diagonalCode u C hu)
    ((diagonalCode_divisible_iff 4 _ C).mpr hC)

/-- Heng–Xie's full-support corollary, with an actual invertible diagonal transformation. -/
theorem exists_diagonal_selfOrthogonal_of_full_weight (C : Submodule K (ι → K))
    (hC : Divisible 4 C) (w : ι → K) (hw : w ∈ C) (hweight : weight w = Fintype.card ι) :
    ∃ u : ι → Kˣ, SelfOrthogonal (RingHom.id K) (diagonalCode u C) := by
  let v := fullWeightUnits w hweight
  refine ⟨(fun i => (v i)⁻¹), inverse_diagonalCode_fourDivisible_selfOrthogonal v C ?_ hC⟩
  exact hw

/-- Eight-divisibility likewise gives cubic orthogonality after normalization. -/
theorem inverse_diagonalCode_eightDivisible_triorthogonal (u : ι → Kˣ)
    (C : Submodule K (ι → K)) (hu : (fun i => (u i : K)) ∈ C)
    (hC : Divisible 8 C) : Triorthogonal (diagonalCode (fun i => (u i)⁻¹) C) :=
  eightDivisible_triorthogonal _ (one_mem_inverse_diagonalCode u C hu)
    ((diagonalCode_divisible_iff 8 _ C).mpr hC)

end FiniteField
end Finite

#print axioms diagonalCode_divisible_iff
#print axioms diagonalCode_finrank
#print axioms diagonalCode_selfOrthogonal_of_norm_one
#print axioms inverse_diagonalCode_twisted_selfOrthogonal
#print axioms inverse_diagonalCode_odd_selfOrthogonal
#print axioms exists_diagonal_selfOrthogonal_of_full_weight
#print axioms inverse_diagonalCode_eightDivisible_triorthogonal
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
