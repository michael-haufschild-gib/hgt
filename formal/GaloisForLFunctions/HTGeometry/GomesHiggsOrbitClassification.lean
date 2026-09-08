import GaloisForLFunctions.HTGeometry.AIIIGramFibreTorsor
import GaloisForLFunctions.HTGeometry.AbelianHiggsMechanism

/-!
# Radial weak orbits and the actual Higgs vacuum comparison

Gomes, arXiv:2509.25276v7, Proposition 1, uses the norm to classify geometric
rank-two Higgs orbits. The existing rectangular Gram-fibre theorem proves the
fibre statement for SU(n) in every dimension at least two. Its doublet instance
merges the two previously phase-inequivalent vacua, yields canonical nonnegative
radial representatives, and identifies the exact weak stabilizer including zero.
The section statement is pointwise and set-theoretic, with no claim of smooth
bundle gauge fixing.
-/

open scoped Matrix ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A spinor as a rectangular frame with one column. -/
def spinorColumn {n : ℕ} (H : Fin n → ℂ) : Matrix (Fin n) (Fin 1) ℂ := fun i _ => H i

/-- The existing rectangular Gram record reduces to the Hermitian spinor norm. -/
theorem spinorColumn_gram {n : ℕ} (H : Fin n → ℂ) (i j : Fin 1) :
    ((spinorColumn H)ᴴ * spinorColumn H) i j = rootHermitianNormSq H := by
  simp [Matrix.mul_apply, spinorColumn, rootHermitianNormSq, dotProduct]

theorem spinorColumn_mul {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (H : Fin n → ℂ) :
    U * spinorColumn H = spinorColumn (U.mulVec H) := by
  ext i j
  rfl

/-- Equal norm is the complete special-unitary orbit invariant in every dimension at least two. -/
theorem spinor_norm_eq_iff_specialUnitary_orbit (n : ℕ) (H K : Fin (n+2) → ℂ) :
    rootHermitianNormSq H = rootHermitianNormSq K ↔
      ∃ U : Matrix (Fin (n+2)) (Fin (n+2)) ℂ,
        U ∈ Matrix.specialUnitaryGroup (Fin (n+2)) ℂ ∧ U.mulVec H = K := by
  have hg : (spinorColumn H)ᴴ * spinorColumn H = (spinorColumn K)ᴴ * spinorColumn K ↔
      rootHermitianNormSq H = rootHermitianNormSq K := by
    constructor
    · intro h
      have hh := congrFun (congrFun h 0) 0
      simpa only [spinorColumn_gram] using hh
    · intro h
      ext i j
      simpa only [spinorColumn_gram] using h
  rw [← hg, gram_eq_iff_exists_left_specialUnitary
    (show 1 < n+2 from Nat.succ_lt_succ (Nat.zero_lt_succ n))]
  constructor
  · rintro ⟨U, hU, hUK⟩
    refine ⟨U, hU, ?_⟩
    funext i
    exact congrFun (congrFun hUK i) 0
  · rintro ⟨U, hU, hUK⟩
    exact ⟨U, hU, by rw [spinorColumn_mul, hUK]⟩

/-- The Abelian model's radial coordinate is the existing Hermitian norm record. -/
theorem higgs_rootHermitianNormSq (H : Fin 2 → ℂ) :
    rootHermitianNormSq H = (abelianHiggsSpinorNormSq H : ℂ) := by
  simp [rootHermitianNormSq, dotProduct, Fin.sum_univ_two,
    abelianHiggsSpinorNormSq, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]

/-- Enlarging phase gauge to weak SU(2) removes every equal-radius doublet modulus. -/
theorem higgs_norm_eq_iff_specialUnitary_orbit (H K : Fin 2 → ℂ) :
    abelianHiggsSpinorNormSq H = abelianHiggsSpinorNormSq K ↔
      ∃ U : Matrix (Fin 2) (Fin 2) ℂ,
        U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ U.mulVec H = K := by
  have h := spinor_norm_eq_iff_specialUnitary_orbit 0 H K
  rw [higgs_rootHermitianNormSq H, higgs_rootHermitianNormSq K] at h
  simpa only [Complex.ofReal_inj] using h

/-- Pointwise section orbits on an arbitrary base are classified by their radial functions.
This is a set-theoretic statement; no continuity or bundle trivialization is asserted. -/
theorem higgs_section_norm_eq_iff_pointwise_specialUnitary {B : Type*}
    (H K : B → Fin 2 → ℂ) :
    (∀ x, abelianHiggsSpinorNormSq (H x) = abelianHiggsSpinorNormSq (K x)) ↔
      ∃ U : B → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ x, U x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
        ∀ x, (U x).mulVec (H x) = K x := by
  constructor
  · intro h
    have hh := fun x => (higgs_norm_eq_iff_specialUnitary_orbit (H x) (K x)).mp (h x)
    choose U hU hUK using hh
    exact ⟨U, hU, hUK⟩
  · rintro ⟨U, hU, hUK⟩ x
    exact (higgs_norm_eq_iff_specialUnitary_orbit (H x) (K x)).mpr ⟨U x, hU x, hUK x⟩

/-- The two known phase-inequivalent vacua merge into a single weak gauge orbit. -/
theorem abelianHiggs_vacua_same_specialUnitary_orbit :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ,
      U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
        U.mulVec abelianHiggsSpinorVacuum = abelianHiggsSpinorOrthogonalVacuum := by
  apply (higgs_norm_eq_iff_specialUnitary_orbit _ _).mp
  simp [abelianHiggsSpinorNormSq, abelianHiggsSpinorVacuum,
    abelianHiggsSpinorOrthogonalVacuum]

/-- Weak gauge invariance follows for the actual Abelian model's radial potential. -/
theorem higgs_radial_potential_specialUnitary (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (H : Fin 2 → ℂ) :
    abelianHiggsSpinorPotential ((U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H) =
      abelianHiggsSpinorPotential H := by
  have h := (higgs_norm_eq_iff_specialUnitary_orbit H ((U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H)).mpr
    ⟨U, U.property, rfl⟩
  simp only [abelianHiggsSpinorPotential, h]

/-- A one-column frame is regular exactly when its spinor is nonzero. -/
theorem spinorColumn_gramRegular_iff {n : ℕ} (H : Fin n → ℂ) :
    GramRegular (spinorColumn H) ↔ H ≠ 0 := by
  rw [gramRegular_iff_mulVec_injective]
  constructor
  · intro h hH
    subst H
    have he : (1 : Fin 1 → ℂ) = 0 := h (by ext i; simp [spinorColumn, Matrix.mulVec, dotProduct])
    exact one_ne_zero (congrFun he 0)
  · intro hH v w hvw
    obtain ⟨i, hi⟩ : ∃ i, H i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hH (funext hn)
    have hh := congrFun hvw i
    simp [spinorColumn, Matrix.mulVec, dotProduct, hi] at hh
    have hv : v 0 = w 0 := hh
    funext j
    simpa only [Subsingleton.elim j 0] using hv

/-- The weak stabilizer is trivial away from the zero doublet, with the zero case retained. -/
theorem higgs_specialUnitary_stabilizer (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (H : Fin 2 → ℂ) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H = H ↔ H = 0 ∨ U = 1 := by
  constructor
  · intro h
    by_cases hH : H = 0
    · exact Or.inl hH
    · right
      apply Subtype.ext
      exact specialUnitary_fix_regular_eq_one (spinorColumn H)
        ((spinorColumn_gramRegular_iff H).mpr hH) U U.property
        (by rw [spinorColumn_mul, h])
  · rintro (rfl | rfl) <;> simp

/-- For a nonzero doublet, the transporting special unitary is determined by its action. -/
theorem higgs_specialUnitary_action_eq_iff
    (U V : Matrix.specialUnitaryGroup (Fin 2) ℂ) (H : Fin 2 → ℂ) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H =
      (V : Matrix (Fin 2) (Fin 2) ℂ).mulVec H ↔ H = 0 ∨ U = V := by
  constructor
  · intro h
    by_cases hH : H = 0
    · exact Or.inl hH
    · right
      apply Subtype.ext
      refine specialUnitary_eq_of_mul_eq (spinorColumn H)
        (fun W hW hfix => specialUnitary_fix_regular_eq_one (spinorColumn H)
          ((spinorColumn_gramRegular_iff H).mpr hH) W hW hfix) U V U.property V.property ?_
      rw [spinorColumn_mul, spinorColumn_mul, h]
  · rintro (rfl | rfl) <;> simp

/-- Nonnegative radial coordinate, including the singular zero orbit. -/
def higgsRadialRepresentative (H : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ), 0]

/-- Canonical radial reduction preserves the entire norm record. -/
theorem higgsRadialRepresentative_norm (H : Fin 2 → ℂ) :
    abelianHiggsSpinorNormSq (higgsRadialRepresentative H) = abelianHiggsSpinorNormSq H := by
  have hn : 0 ≤ abelianHiggsSpinorNormSq H :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  simp only [higgsRadialRepresentative, abelianHiggsSpinorNormSq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.normSq_ofReal,
    map_zero, add_zero, ← pow_two]
  exact Real.sq_sqrt hn

/-- Every doublet has a canonical nonnegative radial representative in its weak orbit. -/
theorem higgs_specialUnitary_radial_representative (H : Fin 2 → ℂ) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ,
      U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ U.mulVec H = higgsRadialRepresentative H := by
  exact (higgs_norm_eq_iff_specialUnitary_orbit _ _).mp
    (higgsRadialRepresentative_norm H).symm

/-- Canonical radial representatives identify exactly the weak gauge orbits. -/
theorem higgsRadialRepresentative_eq_iff (H K : Fin 2 → ℂ) :
    higgsRadialRepresentative H = higgsRadialRepresentative K ↔
      abelianHiggsSpinorNormSq H = abelianHiggsSpinorNormSq K := by
  constructor
  · intro h
    have hh := congrArg abelianHiggsSpinorNormSq h
    simpa only [higgsRadialRepresentative_norm] using hh
  · intro h
    simp only [higgsRadialRepresentative, h]

end GaloisForLFunctions.HTGeometry
