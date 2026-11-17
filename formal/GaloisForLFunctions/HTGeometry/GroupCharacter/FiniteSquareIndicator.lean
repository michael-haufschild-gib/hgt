import GaloisForLFunctions.HTGeometry.StokesResistance.SymmetricTensorCharacter
import GaloisForLFunctions.HTGeometry.StokesResistance.FiniteGroupCharacter
import Mathlib.Tactic

/-!
# Square-character averages and invariant tensor parity

Finite-group averaging commutes with exchange of the two tensor factors.
Their joint projections identify invariant symmetric and alternating tensors.
The average of `χ(g²)` is their dimension difference; the average of `χ(g)²`
is their dimension sum. This interprets the finite square-power character
term appearing in Aoki, arXiv:2611.20592, through actual invariant subspaces.
-/

open scoped BigOperators Kronecker
noncomputable section
namespace GaloisForLFunctions.HTGeometry.GroupCharacter
open StokesResistance
variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- Coordinate tensor square of a matrix representation. -/
def tensorSquareRepresentation (ρ : G →* Matrix ι ι ℂ) :
    Representation ℂ G ((ι × ι) → ℂ) where
  toFun g := (ρ g ⊗ₖ ρ g).toLin'
  map_one' := by simp only [map_one, Matrix.one_kronecker_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    simp only [map_mul, Matrix.mul_kronecker_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

/-- Factor exchange on the coordinate tensor square. -/
def tensorFlip : Module.End ℂ ((ι × ι) → ℂ) := tensorSwap.toLin'

private theorem tensorFlip_sq : tensorFlip (ι := ι) * tensorFlip = 1 := by
  change tensorSwap.toLin'.comp tensorSwap.toLin' = 1
  rw [← Matrix.toLin'_mul, tensorSwap_mul_self, Matrix.toLin'_one]
  rfl

omit [Fintype G] in
private theorem tensorFlip_commutes (ρ : G →* Matrix ι ι ℂ) (g : G) :
    tensorFlip * tensorSquareRepresentation ρ g = tensorSquareRepresentation ρ g * tensorFlip := by
  change tensorSwap.toLin' * (ρ g ⊗ₖ ρ g).toLin' =
    (ρ g ⊗ₖ ρ g).toLin' * tensorSwap.toLin'
  simp only [Module.End.mul_eq_comp, ← Matrix.toLin'_mul]
  exact congrArg Matrix.toLin' (tensorSwap_commutes_kronecker_self (ρ g))

/-- The symmetric or alternating tensor projector for sign `1` or `-1`. -/
def tensorSector (ε : ℂ) : Module.End ℂ ((ι × ι) → ℂ) :=
  (1 / 2 : ℂ) • (1 + ε • tensorFlip)

private theorem tensorSector_idempotent (ε : ℂ) (hε : ε ^ 2 = 1) :
    tensorSector (ι := ι) ε * tensorSector ε = tensorSector ε := by
  have he : ε * ε = 1 := by simpa only [pow_two] using hε
  have hεS : (ε • tensorFlip (ι := ι)) * (ε • tensorFlip) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, tensorFlip_sq, he, one_smul]
  have hs : (1 + ε • tensorFlip (ι := ι)) * (1 + ε • tensorFlip) =
      (2 : ℂ) • (1 + ε • tensorFlip) := by
    simp only [add_mul, mul_add, one_mul, mul_one, hεS]
    module
  simp only [tensorSector, smul_mul_assoc, mul_smul_comm]
  rw [hs]
  module

private theorem tensorFlip_commutes_average (ρ : G →* Matrix ι ι ℂ) :
    tensorFlip * finiteGroupAverage (tensorSquareRepresentation ρ) =
      finiteGroupAverage (tensorSquareRepresentation ρ) * tensorFlip := by
  simp only [finiteGroupAverage, smul_mul_assoc, mul_smul_comm,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun g _ => tensorFlip_commutes ρ g

private theorem tensorSector_commutes_average (ρ : G →* Matrix ι ι ℂ) (ε : ℂ) :
    tensorSector ε * finiteGroupAverage (tensorSquareRepresentation ρ) =
      finiteGroupAverage (tensorSquareRepresentation ρ) * tensorSector ε := by
  simp only [tensorSector, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    one_mul, mul_one, tensorFlip_commutes_average]

/-- Project onto invariant tensors of the chosen exchange parity. -/
def invariantTensorSector (ρ : G →* Matrix ι ι ℂ) (ε : ℂ) :
    Module.End ℂ ((ι × ι) → ℂ) :=
  tensorSector ε * finiteGroupAverage (tensorSquareRepresentation ρ)

/-- Averaging and selecting exchange parity commute, so their product is a projection. -/
theorem invariantTensorSector_idempotent (ρ : G →* Matrix ι ι ℂ)
    (ε : ℂ) (hε : ε ^ 2 = 1) : IsIdempotentElem (invariantTensorSector ρ ε) := by
  let A := finiteGroupAverage (tensorSquareRepresentation ρ)
  let P := tensorSector (ι := ι) ε
  change (P * A) * (P * A) = P * A
  have hcomm : P * A = A * P := tensorSector_commutes_average ρ ε
  calc
    (P * A) * (P * A) = P * (A * P) * A := by simp only [mul_assoc]
    _ = P * (P * A) * A := by rw [← hcomm]
    _ = (P * P) * (A * A) := by simp only [mul_assoc]
    _ = P * A := by rw [tensorSector_idempotent ε hε, finiteGroupAverage_idempotent]

omit [Fintype G] in
private theorem trace_tensorSector_action (ρ : G →* Matrix ι ι ℂ) (ε : ℂ) (g : G) :
    LinearMap.trace ℂ ((ι × ι) → ℂ) (tensorSector ε * tensorSquareRepresentation ρ g) =
      (Matrix.trace (ρ g) ^ 2 + ε * Matrix.trace (ρ (g * g))) / 2 := by
  have ht : LinearMap.trace ℂ ((ι × ι) → ℂ) (tensorSquareRepresentation ρ g) =
      Matrix.trace (ρ g) ^ 2 := by
    change LinearMap.trace ℂ _ (ρ g ⊗ₖ ρ g).toLin' = _
    rw [Matrix.trace_toLin'_eq, Matrix.trace_kronecker, pow_two]
  have hs : LinearMap.trace ℂ ((ι × ι) → ℂ)
      (tensorFlip * tensorSquareRepresentation ρ g) = Matrix.trace (ρ (g * g)) := by
    change LinearMap.trace ℂ _ (tensorSwap.toLin' * (ρ g ⊗ₖ ρ g).toLin') = _
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq,
      trace_tensorSwap_mul_kronecker_self, map_mul]
  rw [tensorSector, smul_mul_assoc, add_mul, one_mul, smul_mul_assoc,
    map_smul, map_add, map_smul, ht, hs]
  simp only [smul_eq_mul]
  ring

/-- The projection image consists exactly of invariant tensors with the chosen exchange sign. -/
theorem mem_range_invariantTensorSector_iff (ρ : G →* Matrix ι ι ℂ)
    (ε : ℂ) (hε : ε ^ 2 = 1) (v : (ι × ι) → ℂ) :
    v ∈ LinearMap.range (invariantTensorSector ρ ε) ↔
      v ∈ (tensorSquareRepresentation ρ).invariants ∧ tensorFlip v = ε • v := by
  let A := finiteGroupAverage (tensorSquareRepresentation ρ)
  let Q := tensorSector (ι := ι) ε
  have he : ε * ε = 1 := by simpa only [pow_two] using hε
  have hSQ : tensorFlip * Q = ε • Q := by
    have hi : tensorFlip (ι := ι) + ε • (1 : Module.End ℂ ((ι × ι) → ℂ)) =
        ε • (1 + ε • tensorFlip) := by
      simp only [smul_add, smul_smul, he, one_smul]
      abel
    change tensorFlip * tensorSector ε = ε • tensorSector ε
    rw [tensorSector, mul_smul_comm, mul_add, mul_one, mul_smul_comm, tensorFlip_sq, hi]
    exact smul_comm _ _ _
  have hAQ : A * (Q * A) = Q * A := by
    rw [← mul_assoc, ← tensorSector_commutes_average ρ ε, mul_assoc,
      finiteGroupAverage_idempotent]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(mem_invariants_iff_finiteGroupAverage_eq_self _ _).mpr ?_, ?_⟩
    · exact congrArg (fun L : Module.End ℂ ((ι × ι) → ℂ) => L w) hAQ
    · have h : tensorFlip * (Q * A) = ε • (Q * A) := by
        rw [← mul_assoc, hSQ, smul_mul_assoc]
      exact congrArg (fun L : Module.End ℂ ((ι × ι) → ℂ) => L w) h
  · rintro ⟨hinv, hsign⟩
    have hAv : A v = v := (mem_invariants_iff_finiteGroupAverage_eq_self _ _).mp hinv
    refine ⟨v, ?_⟩
    change Q (A v) = v
    rw [hAv]
    change ((1 / 2 : ℂ) • (1 + ε • tensorFlip)) v = v
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
      hsign, smul_smul, he, one_smul]
    module

/-- Exact character formula for invariant symmetric and alternating tensors. -/
theorem invariantTensorSector_rank (ρ : G →* Matrix ι ι ℂ) (ε : ℂ) (hε : ε ^ 2 = 1) :
    (Module.finrank ℂ (LinearMap.range (invariantTensorSector ρ ε)) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
        (Matrix.trace (ρ g) ^ 2 + ε * Matrix.trace (ρ (g * g))) / 2 := by
  rw [← (LinearMap.IsIdempotentElem.isProj_range _
    (invariantTensorSector_idempotent ρ ε hε)).trace]
  rw [invariantTensorSector, finiteGroupAverage, mul_smul_comm, Finset.mul_sum,
    map_smul, map_sum]
  simp only [smul_eq_mul, trace_tensorSector_action]

/-- The square-character average is the symmetric invariant dimension minus the alternating one. -/
theorem square_character_average_eq_signed_rank (ρ : G →* Matrix ι ι ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, Matrix.trace (ρ (g * g)) =
      (Module.finrank ℂ (LinearMap.range (invariantTensorSector ρ 1)) : ℂ) -
        (Module.finrank ℂ (LinearMap.range (invariantTensorSector ρ (-1))) : ℂ) := by
  rw [invariantTensorSector_rank ρ 1 (by norm_num),
    invariantTensorSector_rank ρ (-1) (by norm_num), ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  ring

/-- The ordinary square-character average counts both invariant exchange sectors together. -/
theorem character_square_average_eq_total_rank (ρ : G →* Matrix ι ι ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, Matrix.trace (ρ g) ^ 2 =
      (Module.finrank ℂ (LinearMap.range (invariantTensorSector ρ 1)) : ℂ) +
        (Module.finrank ℂ (LinearMap.range (invariantTensorSector ρ (-1))) : ℂ) := by
  rw [invariantTensorSector_rank ρ 1 (by norm_num),
    invariantTensorSector_rank ρ (-1) (by norm_num), ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  ring

#print axioms mem_range_invariantTensorSector_iff
#print axioms invariantTensorSector_rank
#print axioms square_character_average_eq_signed_rank
#print axioms character_square_average_eq_total_rank

end GaloisForLFunctions.HTGeometry.GroupCharacter
