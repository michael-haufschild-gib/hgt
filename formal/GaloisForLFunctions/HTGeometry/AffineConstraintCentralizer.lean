import GaloisForLFunctions.HTGeometry.AffineHypertranscendenceHorizon
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Affine period-shear constraint centralizer

The affine vector fields commuting with every period shear are classified exactly.  Their
translation coefficient over the rational period field then feeds the affine hypertranscendence
horizon without adding a restatement hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- Coordinates consisting of one distinguished variable and finitely many period variables. -/
abbrev PeriodCoordinates (k ι : Type*) := k × (ι → k)

/-- The period shear `(z, ω) ↦ (z + ωᵢ, ω)`. -/
def periodShear (i : ι) (q : PeriodCoordinates k ι) : PeriodCoordinates k ι :=
  (q.1 + q.2 i, q.2)

/-- An arbitrary affine vector field in block coordinates. -/
@[ext]
structure AffineBlockVectorField (k ι : Type*) [Field k] [Fintype ι] where
  alpha : k
  beta : ι → k
  gamma : ι → k
  matrix : ι → ι → k
  constantZ : k
  constantOmega : ι → k

/-- Evaluation of a block affine vector field. -/
def AffineBlockVectorField.eval
    (V : AffineBlockVectorField k ι) (q : PeriodCoordinates k ι) :
    PeriodCoordinates k ι :=
  (V.alpha * q.1 + ∑ i, V.beta i * q.2 i + V.constantZ,
    fun j => V.gamma j * q.1 + ∑ i, V.matrix j i * q.2 i + V.constantOmega j)

/-- Exact compatibility of an affine vector field with every period shear. -/
def AffineBlockVectorField.PeriodShearCompatible
    (V : AffineBlockVectorField k ι) : Prop :=
  ∀ (i : ι) (q : PeriodCoordinates k ι),
    V.eval (periodShear i q) = periodShear i (V.eval q)

/-- The period-shear centralizer normal form. -/
def normalAffineConstraintField (lambda c : k) (beta : ι → k) :
    AffineBlockVectorField k ι where
  alpha := lambda
  beta := beta
  gamma := 0
  matrix i j := if i = j then lambda else 0
  constantZ := c
  constantOmega := 0

@[simp]
theorem normalAffineConstraintField_eval
    (lambda c : k) (beta : ι → k) (q : PeriodCoordinates k ι) :
    (normalAffineConstraintField lambda c beta).eval q =
      (lambda * q.1 + c + ∑ i, beta i * q.2 i,
        fun i => lambda * q.2 i) := by
  ext <;> simp [normalAffineConstraintField, AffineBlockVectorField.eval,
    add_assoc, add_comm]

theorem normalAffineConstraintField_compatible
    (lambda c : k) (beta : ι → k) :
    (normalAffineConstraintField lambda c beta).PeriodShearCompatible := by
  intro i q
  ext <;> simp [normalAffineConstraintField_eval, periodShear]
  ring

/-- Compatibility kills all translation-to-period and constant-period blocks. -/
theorem periodShearCompatible_gamma_constantOmega
    [Nonempty ι]
    (V : AffineBlockVectorField k ι) (hV : V.PeriodShearCompatible) :
    V.gamma = 0 ∧ V.constantOmega = 0 := by
  constructor
  · funext j
    let i : ι := Classical.choice inferInstance
    let omega : ι → k := fun l => if l = i then 1 else 0
    have h := congrArg (fun q : PeriodCoordinates k ι => q.2 j)
      (hV i (0, omega))
    simp only [AffineBlockVectorField.eval, periodShear] at h
    simpa [omega] using h
  · funext i
    have h := congrArg (fun q : PeriodCoordinates k ι => q.1)
      (hV i (0, 0))
    simp only [AffineBlockVectorField.eval, periodShear] at h
    simpa using h.symm

/-- Compatibility forces the period block to be the scalar matrix `alpha I`. -/
theorem periodShearCompatible_matrix
    [Nonempty ι]
    (V : AffineBlockVectorField k ι) (hV : V.PeriodShearCompatible) :
    ∀ i j, V.matrix i j = if i = j then V.alpha else 0 := by
  obtain ⟨hgamma, homega⟩ := periodShearCompatible_gamma_constantOmega V hV
  intro i j
  let omega : ι → k := fun l => if l = j then 1 else 0
  have h := congrArg (fun q : PeriodCoordinates k ι => q.1)
    (hV i (0, omega))
  simp only [AffineBlockVectorField.eval, periodShear] at h
  simp [hgamma, homega, omega] at h
  by_cases hij : i = j
  · subst j
    simp at h ⊢
    linear_combination h.symm
  · simp [hij] at h ⊢
    exact h

/-- Exact classification of the affine-regular period-shear centralizer. -/
theorem periodShearCompatible_iff_existsUnique_normalForm
    [Nonempty ι]
    (V : AffineBlockVectorField k ι) :
    V.PeriodShearCompatible ↔
      ∃! p : k × k × (ι → k),
        V = normalAffineConstraintField p.1 p.2.1 p.2.2 := by
  constructor
  · intro hV
    refine ⟨(V.alpha, V.constantZ, V.beta), ?_, ?_⟩
    · obtain ⟨hgamma, homega⟩ := periodShearCompatible_gamma_constantOmega V hV
      ext <;> simp [normalAffineConstraintField, hgamma, homega,
        periodShearCompatible_matrix V hV]
    · rintro ⟨lambda, c, beta⟩ hp
      apply Prod.ext
      · simpa [normalAffineConstraintField] using
          (congrArg AffineBlockVectorField.alpha hp).symm
      · apply Prod.ext
        · simpa [normalAffineConstraintField] using
            (congrArg AffineBlockVectorField.constantZ hp).symm
        · simpa [normalAffineConstraintField] using
            (congrArg AffineBlockVectorField.beta hp).symm
  · rintro ⟨p, rfl, -⟩
    exact normalAffineConstraintField_compatible p.1 p.2.1 p.2.2

omit [DecidableEq ι] in
/-- The parameter space of the centralizer has the asserted dimension `|ι| + 2`. -/
theorem centralizerParameter_finrank :
    Module.finrank k (k × k × (ι → k)) = Fintype.card ι + 2 := by
  simp
  omega

/-- The canonical rational parameter field `k(ωᵢ)`. -/
abbrev AffineParameterField (k ι : Type*) [Field k] :=
  FractionRing (MvPolynomial ι k)

/-- The translation coefficient `c + ∑ βᵢ ωᵢ` in the canonical parameter field. -/
def affineTranslationCoefficient (c : k) (beta : ι → k) :
    AffineParameterField k ι :=
  algebraMap (MvPolynomial ι k) (AffineParameterField k ι)
    (MvPolynomial.C c + ∑ i, MvPolynomial.C (beta i) * MvPolynomial.X i)

/-- Algebraic independence of the period coordinates makes the affine translation coefficient
vanish exactly when every constant coefficient vanishes. -/
theorem affineTranslationCoefficient_eq_zero_iff (c : k) (beta : ι → k) :
    affineTranslationCoefficient c beta = 0 ↔ c = 0 ∧ beta = 0 := by
  constructor
  · intro h
    have hpoly :
        MvPolynomial.C c + ∑ i, MvPolynomial.C (beta i) * MvPolynomial.X i = 0 := by
      apply IsFractionRing.injective (MvPolynomial ι k) (AffineParameterField k ι)
      simpa [affineTranslationCoefficient] using h
    constructor
    · have h0 := congrArg (fun P : MvPolynomial ι k => P.coeff 0) hpoly
      simpa [MvPolynomial.X, MvPolynomial.coeff_sum] using h0
    · funext j
      have hj := congrArg
        (fun P : MvPolynomial ι k => P.coeff (Finsupp.single j 1)) hpoly
      have hinj : Function.Injective (fun i : ι => Finsupp.single i (1 : ℕ)) :=
        Finsupp.single_left_injective one_ne_zero
      have hsingle : Finsupp.single j (1 : ℕ) ≠ 0 :=
        Finsupp.single_eq_zero.not.mpr one_ne_zero
      have hsingle' : (0 : ι →₀ ℕ) ≠ Finsupp.single j 1 := Ne.symm hsingle
      simpa [MvPolynomial.X, MvPolynomial.coeff_sum, hinj.eq_iff, hsingle,
        hsingle'] using hj
  · rintro ⟨rfl, rfl⟩
    simp [affineTranslationCoefficient]

/-- Full affine-centralizer horizon over the canonical parameter field: a mixed direction has an
algebraically independent jet tower exactly when its translation coefficient is not identically
zero, equivalently when at least one affine translation parameter is nonzero. -/
theorem fullAffineCentralizer_jet_algebraicIndependent_iff
    (T E : Derivation (AffineParameterField k ι)
      (AffineParameterField k ι) (AffineParameterField k ι))
    (w lambda : AffineParameterField k ι) (c : k) (beta : ι → k)
    (x : AffineParameterField k ι)
    (hET : ∀ y, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0)
    (hT : AlgebraicIndependent (AffineParameterField k ι)
      (fun n : ℕ => ((T : AffineParameterField k ι → AffineParameterField k ι)^[n] x))) :
    AlgebraicIndependent (AffineParameterField k ι)
        (fun n : ℕ =>
          ((affineLawDerivation T E (affineTranslationCoefficient c beta) lambda :
            AffineParameterField k ι → AffineParameterField k ι)^[n] x)) ↔
      ¬ (c = 0 ∧ beta = 0) := by
  rw [affineLaw_jet_algebraicIndependent_iff T E w
    (affineTranslationCoefficient c beta) lambda x hET hEx hT]
  exact not_congr (affineTranslationCoefficient_eq_zero_iff c beta)

/-- Full affine-centralizer horizon over a genuine ambient extension.  The canonical period
parameter field is the coefficient field, while the observable and its jets live in an arbitrary
ambient field `L`.  Thus the source-jet independence hypothesis is no longer the impossible
same-field hypothesis of `fullAffineCentralizer_jet_algebraicIndependent_iff`.

The variable translation symbol `c + ∑ᵢ βᵢωᵢ` is a scalar in the coefficient field, so the exact
affine horizon applies directly over that field: the mixed jet tower is algebraically independent
exactly away from the pure-dilation locus `c = 0` and `β = 0`. -/
theorem fullAffineCentralizer_jet_algebraicIndependent_iff_of_extension
    {L : Type*} [Field L] [Algebra (AffineParameterField k ι) L]
    (T E : Derivation (AffineParameterField k ι) L L)
    (w lambda : AffineParameterField k ι) (c : k) (beta : ι → k) (x : L)
    (hET : ∀ y, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0)
    (hT : AlgebraicIndependent (AffineParameterField k ι)
      (fun n : ℕ => ((T : L → L)^[n] x))) :
    AlgebraicIndependent (AffineParameterField k ι)
        (fun n : ℕ =>
          ((affineLawDerivation T E (affineTranslationCoefficient c beta) lambda :
            L → L)^[n] x)) ↔
      ¬ (c = 0 ∧ beta = 0) := by
  rw [affineLaw_jet_algebraicIndependent_iff T E w
    (affineTranslationCoefficient c beta) lambda x hET hEx hT]
  exact not_congr (affineTranslationCoefficient_eq_zero_iff c beta)

end

end GaloisForLFunctions.HTGeometry
