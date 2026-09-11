import GaloisForLFunctions.HTGeometry.PureBipartiteEntanglementEntropy

/-!
# Normalized rectangular pure states for information-reserve experiments

The reserve log(d)-S in arXiv:2608.06941 equations (1)--(6) applies to normalized
states. This module constructs one from every raw finite coefficient vector,
including zero, and proves that both actual Gram reductions have trace one.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators ComplexOrder

/-- Total squared coefficient mass of a rectangular pure-state vector. -/
def bipartitePureMass (n m : ℕ) (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (ψ (i, j))

/-- A canonical normalized product state, used at the zero input. -/
def bipartiteProductBasis (n m : ℕ) : Fin (n + 1) × Fin (m + 1) → ℂ :=
  fun ij => if ij = (0, 0) then 1 else 0

/-- Normalize the actual coefficient vector; the zero vector maps to a product state. -/
def normalizedBipartitePureState (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) : Fin (n + 1) × Fin (m + 1) → ℂ :=
  if bipartitePureMass n m ψ = 0 then bipartiteProductBasis n m
  else fun ij => ψ ij / (Real.sqrt (bipartitePureMass n m ψ) : ℂ)

/-- Coefficient mass is nonnegative for every raw vector. -/
theorem bipartitePureMass_nonneg (n m : ℕ) (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    0 ≤ bipartitePureMass n m ψ := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- Zero coefficient mass identifies exactly the zero vector. -/
theorem bipartitePureMass_zero_iff (n m : ℕ) (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    bipartitePureMass n m ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext ij
    rcases ij with ⟨i, j⟩
    have hrow : Complex.normSq (ψ (i, j)) ≤ ∑ b, Complex.normSq (ψ (i, b)) :=
      Finset.single_le_sum (f := fun b => Complex.normSq (ψ (i, b)))
        (fun b _ => Complex.normSq_nonneg (ψ (i, b))) (Finset.mem_univ j)
    have hall : (∑ b, Complex.normSq (ψ (i, b))) ≤ bipartitePureMass n m ψ :=
      Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq (ψ (a, b)))
        (fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg (ψ (a, b)))
        (Finset.mem_univ i)
    apply Complex.normSq_eq_zero.mp
    have hz := Complex.normSq_nonneg (ψ (i, j))
    rw [h] at hall
    linarith
  · intro h
    simp [h, bipartitePureMass]

/-- Every nonzero raw vector has positive coefficient mass, and conversely. -/
theorem bipartitePureMass_pos_iff (n m : ℕ) (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    0 < bipartitePureMass n m ψ ↔ ψ ≠ 0 := by
  have hn := bipartitePureMass_nonneg n m ψ
  have hz := bipartitePureMass_zero_iff n m ψ
  constructor
  · intro hp hψ
    have := hz.2 hψ
    linarith
  · intro hψ
    have hm : bipartitePureMass n m ψ ≠ 0 := fun h => hψ (hz.1 h)
    exact lt_of_le_of_ne hn (Ne.symm hm)

/-- The fallback product state has unit mass in every pair of nonempty dimensions. -/
theorem bipartiteProductBasis_mass (n m : ℕ) :
    bipartitePureMass n m (bipartiteProductBasis n m) = 1 := by
  have hr (i : Fin (n + 1)) :
      (∑ j, Complex.normSq (bipartiteProductBasis n m (i, j))) = if i = 0 then 1 else 0 := by
    by_cases hi : i = 0
    · subst i
      simp [bipartiteProductBasis, Prod.mk.injEq]
    · simp [bipartiteProductBasis, Prod.mk.injEq, hi]
  unfold bipartitePureMass
  simp_rw [hr]
  simp

/-- The constructed state is normalized for every input, with no nonzero premise. -/
theorem normalizedBipartitePureState_mass (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    bipartitePureMass n m (normalizedBipartitePureState n m ψ) = 1 := by
  unfold normalizedBipartitePureState
  by_cases h : bipartitePureMass n m ψ = 0
  · rw [if_pos h]
    exact bipartiteProductBasis_mass n m
  · rw [if_neg h]
    have hs : Real.sqrt (bipartitePureMass n m ψ) * Real.sqrt (bipartitePureMass n m ψ) =
        bipartitePureMass n m ψ := by
      simpa only [pow_two] using Real.sq_sqrt (bipartitePureMass_nonneg n m ψ)
    calc
      _ = ∑ i, ∑ j, Complex.normSq (ψ (i, j)) / bipartitePureMass n m ψ := by
        change (∑ i, ∑ j, Complex.normSq
          (ψ (i, j) / (Real.sqrt (bipartitePureMass n m ψ) : ℂ))) = _
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Complex.normSq_div, Complex.normSq_ofReal, hs]
      _ = bipartitePureMass n m ψ / bipartitePureMass n m ψ := by
        simp only [← Finset.sum_div]
        rfl
      _ = 1 := div_self h

private theorem normalized_of_mass_one (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) (h : bipartitePureMass n m ψ = 1) :
    normalizedBipartitePureState n m ψ = ψ := by
  simp [normalizedBipartitePureState, h]

/-- Normalization fixes exactly the unit-mass coefficient vectors. -/
theorem normalizedBipartitePureState_fixed_iff (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    normalizedBipartitePureState n m ψ = ψ ↔ bipartitePureMass n m ψ = 1 := by
  constructor
  · intro h
    simpa only [h] using normalizedBipartitePureState_mass n m ψ
  · exact normalized_of_mass_one n m ψ

/-- Repeated normalization preserves the actual state. -/
theorem normalizedBipartitePureState_idempotent (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    normalizedBipartitePureState n m (normalizedBipartitePureState n m ψ) =
      normalizedBipartitePureState n m ψ :=
  normalized_of_mass_one n m _ (normalizedBipartitePureState_mass n m ψ)

/-- The actual normalized state is always nonzero. -/
theorem normalizedBipartitePureState_ne_zero (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    normalizedBipartitePureState n m ψ ≠ 0 := by
  intro h
  have hz := (bipartitePureMass_zero_iff n m _).2 h
  rw [normalizedBipartitePureState_mass] at hz
  norm_num at hz

/-- The left Gram trace is exactly the raw coefficient mass. -/
theorem bipartitePureReducedLeft_trace (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    Matrix.trace (pureStateReducedLeft ψ) = (bipartitePureMass n m ψ : ℂ) := by
  change (∑ i, pureStateReducedLeft ψ i i) = _
  simp only [pureStateReducedLeft_apply, Complex.star_def, Complex.mul_conj,
    bipartitePureMass, Complex.ofReal_sum]

/-- The right Gram trace is the same raw coefficient mass. -/
theorem bipartitePureReducedRight_trace (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    Matrix.trace (pureStateReducedRight ψ) = (bipartitePureMass n m ψ : ℂ) := by
  change (∑ j, pureStateReducedRight ψ j j) = _
  simp only [pureStateReducedRight_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, bipartitePureMass, Complex.ofReal_sum]
  exact Finset.sum_comm

/-- Both actual reductions of the constructed pure state have trace one. -/
theorem normalizedBipartitePureState_reduced_traces (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    Matrix.trace (pureStateReducedLeft (normalizedBipartitePureState n m ψ)) = 1 ∧
      Matrix.trace (pureStateReducedRight (normalizedBipartitePureState n m ψ)) = 1 := by
  rw [bipartitePureReducedLeft_trace, bipartitePureReducedRight_trace,
    normalizedBipartitePureState_mass]
  norm_num

/-- Both actual reductions are positive semidefinite. -/
theorem normalizedBipartitePureState_reduced_positive (n m : ℕ)
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    (pureStateReducedLeft (normalizedBipartitePureState n m ψ)).PosSemidef ∧
      (pureStateReducedRight (normalizedBipartitePureState n m ψ)).PosSemidef :=
  ⟨Matrix.posSemidef_self_mul_conjTranspose _, Matrix.posSemidef_conjTranspose_mul_self _⟩

end
end GaloisForLFunctions.HTGeometry
