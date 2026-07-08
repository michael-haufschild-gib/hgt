import GaloisForLFunctions.RHTower.FittingSeamBoundary

/-!
# A torsion seam presentation layer for `M+`

The bare completed `(sigma_p, partial_s)` category has only regular finite-free lanes.
This file isolates the minimal extra layer needed for a `{sigma_p}`-graded divisor
refinement at one pinned annulus: a p-labelled torsion seam presentation
`R[X]^n --A--> R[X]^n`, with `det A = X^m`, and sigma defects `Delta_p`.

The layer is deliberately parametric over the already-existing regular `M+` object.
It adds a constraint datum; it does not construct a carrier or introduce a flow.
-/

noncomputable section

namespace RHTower

open Matrix Polynomial

variable {n R Sigma : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A p-labelled torsion seam presentation supported at the local divisor `X^m`. -/
structure TorsionSeamPresentation (Sigma n R : Type*) [Fintype n] [DecidableEq n]
    [CommRing R] (m : ℕ) where
  /-- The local presentation matrix.  Its determinant cuts out the divisor. -/
  A : Matrix n n (Polynomial R)
  /-- The sigma-labelled defects to be tested against the presentation. -/
  Delta : Sigma → Matrix n n (Polynomial R)
  /-- The seam is supported exactly at the pinned divisor `X^m`. -/
  det_eq : A.det = (Polynomial.X : Polynomial R) ^ m

/-- The seam extension of a regular `M+` object.  `Base` is a placeholder for the
regular finite-free `(sigma_p, partial_s)` object already present in the paper category. -/
structure MPlusTorsionSeamObject (Base Sigma n R : Type*) [Fintype n] [DecidableEq n]
    [CommRing R] (m : ℕ) where
  base : Base
  seam : TorsionSeamPresentation Sigma n R m

namespace TorsionSeamPresentation

variable {m : ℕ} (S T : TorsionSeamPresentation Sigma n R m)

/-- The boundary trace of the sigma defect at `p`. -/
def boundaryTrace (p : Sigma) : Polynomial R :=
  fittingBoundaryTrace S.A (S.Delta p)

/-- The boundary class of the sigma defect at `p`. -/
def boundaryClass (p : Sigma) : LocalDivisorJet R m :=
  fittingBoundaryClass m S.A (S.Delta p)

/-- A fake defect factors through the presentation modulo the local zero ideal. -/
def DefectFactorsThrough (p : Sigma) : Prop :=
  ∃ H K : Matrix n n (Polynomial R),
    S.Delta p = S.A * H + ((Polynomial.X : Polynomial R) ^ m) • K

/-- A source-side fake defect factors through the presentation on the left modulo
the local zero ideal. -/
def DefectFactorsThroughLeft (p : Sigma) : Prop :=
  ∃ H K : Matrix n n (Polynomial R),
    S.Delta p = H * S.A + ((Polynomial.X : Polynomial R) ^ m) • K

/-- The desired nonmembership statement, named as a proposition. -/
def DefectNonmember (p : Sigma) : Prop :=
  ¬ S.DefectFactorsThrough p

/-- The left-sided nonmembership statement. -/
def DefectLeftNonmember (p : Sigma) : Prop :=
  ¬ S.DefectFactorsThroughLeft p

/-- A non-circular witness for a boundary class: one coefficient below the divisor
order survives. -/
def BoundaryCoeffWitness (p : Sigma) : Prop :=
  ∃ j : ℕ, j < m ∧ (S.boundaryTrace p).coeff j ≠ 0

/-- Determinant-compatible defects have boundary trace still divisible by the local
divisor equation.  Such defects cannot carry the seam boundary. -/
def BoundaryTraceDivisible (p : Sigma) : Prop :=
  (Polynomial.X : Polynomial R) ^ m ∣ S.boundaryTrace p

/-- Some sigma label has a surviving low-coefficient boundary witness. -/
def HasBoundaryCoeffWitness : Prop :=
  ∃ p : Sigma, S.BoundaryCoeffWitness p

/-- Some sigma label is determinant-transverse to the pinned divisor modulo `X^m`. -/
def HasDeterminantTransverseDefect : Prop :=
  ∃ p : Sigma, ¬ S.BoundaryTraceDivisible p

/-- Morphisms in the torsion seam layer preserve the presentation square and identify
sigma defects modulo fake target defects.  This is the extra morphism law missing from
the bare finite-free `M+` layer. -/
structure Hom where
  left : Matrix n n (Polynomial R)
  right : Matrix n n (Polynomial R)
  chain : right * S.A = T.A * left
  defect_compat : ∀ p : Sigma, ∃ H K : Matrix n n (Polynomial R),
    right * S.Delta p - T.Delta p * left =
      T.A * H + ((Polynomial.X : Polynomial R) ^ m) • K

/-- The identity morphism in the torsion seam layer. -/
def Hom.id : Hom S S where
  left := 1
  right := 1
  chain := by simp
  defect_compat := by
    intro p
    refine ⟨0, 0, ?_⟩
    simp

/-- Composition of torsion seam morphisms.  The defect condition is stable because
fake target defects form the right-factor-plus-`X^m` class. -/
def Hom.comp {U : TorsionSeamPresentation Sigma n R m}
    (g : T.Hom U) (f : S.Hom T) : S.Hom U where
  left := g.left * f.left
  right := g.right * f.right
  chain := by
    calc
      (g.right * f.right) * S.A = g.right * (f.right * S.A) := by
        rw [Matrix.mul_assoc]
      _ = g.right * (T.A * f.left) := by
        rw [f.chain]
      _ = (g.right * T.A) * f.left := by
        rw [Matrix.mul_assoc]
      _ = (U.A * g.left) * f.left := by
        rw [g.chain]
      _ = U.A * (g.left * f.left) := by
        rw [Matrix.mul_assoc]
  defect_compat := by
    intro p
    rcases f.defect_compat p with ⟨Hf, Kf, hf⟩
    rcases g.defect_compat p with ⟨Hg, Kg, hg⟩
    refine ⟨g.left * Hf + Hg * f.left, g.right * Kf + Kg * f.left, ?_⟩
    calc
      (g.right * f.right) * S.Delta p - U.Delta p * (g.left * f.left)
          = g.right * (f.right * S.Delta p - T.Delta p * f.left) +
              (g.right * T.Delta p - U.Delta p * g.left) * f.left := by
            noncomm_ring
      _ = g.right * (T.A * Hf + ((Polynomial.X : Polynomial R) ^ m) • Kf) +
              (U.A * Hg + ((Polynomial.X : Polynomial R) ^ m) • Kg) * f.left := by
            rw [hf, hg]
      _ = U.A * (g.left * Hf + Hg * f.left) +
              ((Polynomial.X : Polynomial R) ^ m) • (g.right * Kf + Kg * f.left) := by
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
            rw [← Matrix.mul_assoc, g.chain, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc]
            rw [Matrix.mul_add, Matrix.mul_assoc]
            rw [Matrix.mul_assoc]
            abel_nf

end TorsionSeamPresentation

/-- Multiples of `X^m` have zero coefficients below `m`. -/
theorem coeff_eq_zero_of_X_pow_dvd (m j : ℕ) {P : Polynomial R}
    (hdiv : (Polynomial.X : Polynomial R) ^ m ∣ P) (hj : j < m) :
    P.coeff j = 0 := by
  rcases hdiv with ⟨Q, hQ⟩
  rw [hQ, Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rcases x with ⟨a, b⟩
  simp only [Finset.mem_antidiagonal] at hx
  simp [Polynomial.coeff_X_pow]
  intro ha
  omega

/-- A surviving coefficient below `m` gives a nonzero local divisor-jet class. -/
theorem jetClass_ne_zero_of_coeff_lt (m j : ℕ) {P : Polynomial R}
    (hj : j < m) (hcoeff : P.coeff j ≠ 0) :
    jetClass R m P ≠ 0 := by
  intro hzero
  have hmem : P ∈ jetIdeal R m := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hdiv : (Polynomial.X : Polynomial R) ^ m ∣ P := by
    simpa [jetIdeal] using (Ideal.mem_span_singleton.mp hmem)
  exact hcoeff (coeff_eq_zero_of_X_pow_dvd (R := R) m j hdiv hj)

/-- A surviving coefficient of the adjugate trace gives a nonzero Fitting boundary. -/
theorem fittingBoundaryClass_ne_zero_of_coeff_lt (m j : ℕ)
    {A Delta : Matrix n n (Polynomial R)}
    (hj : j < m) (hcoeff : (fittingBoundaryTrace A Delta).coeff j ≠ 0) :
    fittingBoundaryClass m A Delta ≠ 0 := by
  exact jetClass_ne_zero_of_coeff_lt (R := R) m j hj hcoeff

/-- The coefficient witness proves the advertised nonmembership
`Delta_p ∉ A End + (X^m)`. -/
theorem coeff_obstructs_right_factor_mod_X_pow (m j : ℕ)
    {A Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hj : j < m) (hcoeff : (fittingBoundaryTrace A Delta).coeff j ≠ 0) :
    ¬ ∃ H K : Matrix n n (Polynomial R),
      Delta = A * H + ((Polynomial.X : Polynomial R) ^ m) • K := by
  exact nonzero_fittingBoundaryClass_obstructs_right_factor_mod_X_pow m hdet
    (fittingBoundaryClass_ne_zero_of_coeff_lt (R := R) m j hj hcoeff)

/-- The coefficient witness also rules out left-factor fake defects. -/
theorem coeff_obstructs_left_factor_mod_X_pow (m j : ℕ)
    {A Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hj : j < m) (hcoeff : (fittingBoundaryTrace A Delta).coeff j ≠ 0) :
    ¬ ∃ H K : Matrix n n (Polynomial R),
      Delta = H * A + ((Polynomial.X : Polynomial R) ^ m) • K := by
  exact nonzero_fittingBoundaryClass_obstructs_left_factor_mod_X_pow m hdet
    (fittingBoundaryClass_ne_zero_of_coeff_lt (R := R) m j hj hcoeff)

namespace TorsionSeamPresentation

variable {m : ℕ} (S : TorsionSeamPresentation Sigma n R m)

/-- The coefficient witness is exactly nonvanishing of the boundary class. -/
theorem boundaryClass_ne_zero_iff_coeffWitness {p : Sigma} :
    S.boundaryClass p ≠ 0 ↔ S.BoundaryCoeffWitness p := by
  exact fittingBoundaryClass_ne_zero_iff_exists_coeff_lt_ne_zero m S.A (S.Delta p)

/-- The coefficient witness is exactly determinant transversality modulo `X^m`. -/
theorem boundaryCoeffWitness_iff_not_traceDivisible {p : Sigma} :
    S.BoundaryCoeffWitness p ↔ ¬ S.BoundaryTraceDivisible p := by
  rw [← S.boundaryClass_ne_zero_iff_coeffWitness]
  exact fittingBoundaryClass_ne_zero_iff_not_trace_X_pow_dvd m S.A (S.Delta p)

/-- A coefficient witness at `p` gives nonzero boundary class value at `p`. -/
theorem boundaryClass_ne_zero_of_coeffWitness {p : Sigma}
    (h : S.BoundaryCoeffWitness p) :
    S.boundaryClass p ≠ 0 := by
  exact S.boundaryClass_ne_zero_iff_coeffWitness.mpr h

/-- A determinant-compatible defect has zero boundary class. -/
theorem boundaryClass_eq_zero_of_traceDivisible {p : Sigma}
    (h : S.BoundaryTraceDivisible p) :
    S.boundaryClass p = 0 := by
  exact fittingBoundaryClass_eq_zero_of_trace_X_pow_dvd m h

/-- A determinant-compatible defect has no low-coefficient boundary witness. -/
theorem not_boundaryCoeffWitness_of_traceDivisible {p : Sigma}
    (h : S.BoundaryTraceDivisible p) :
    ¬ S.BoundaryCoeffWitness p := by
  exact mt S.boundaryCoeffWitness_iff_not_traceDivisible.mp (not_not.mpr h)

/-- A determinant-transverse defect has a coefficient witness. -/
theorem boundaryCoeffWitness_of_not_traceDivisible {p : Sigma}
    (h : ¬ S.BoundaryTraceDivisible p) :
    S.BoundaryCoeffWitness p :=
  S.boundaryCoeffWitness_iff_not_traceDivisible.mpr h

/-- A seam has a surviving coefficient witness exactly when some sigma defect is
determinant-transverse modulo `X^m`. -/
theorem hasBoundaryCoeffWitness_iff_hasDeterminantTransverseDefect :
    S.HasBoundaryCoeffWitness ↔ S.HasDeterminantTransverseDefect := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, S.boundaryCoeffWitness_iff_not_traceDivisible.mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, S.boundaryCoeffWitness_iff_not_traceDivisible.mpr hp⟩

/-- If every sigma defect is determinant-compatible, the seam has no surviving
coefficient witness. -/
theorem noBoundaryCoeffWitness_of_forall_traceDivisible
    (h : ∀ p : Sigma, S.BoundaryTraceDivisible p) :
    ¬ S.HasBoundaryCoeffWitness := by
  rintro ⟨p, hp⟩
  exact S.not_boundaryCoeffWitness_of_traceDivisible (h p) hp

/-- Nontrivial Fitting boundary for the sigma family is exactly determinant
transversality of one sigma-labelled defect. -/
theorem hasNontrivialFittingBoundary_iff_hasDeterminantTransverseDefect :
    HasNontrivialFittingBoundary m S.A S.Delta ↔ S.HasDeterminantTransverseDefect := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (fittingBoundaryClass_ne_zero_iff_not_trace_X_pow_dvd m S.A (S.Delta p)).mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (fittingBoundaryClass_ne_zero_iff_not_trace_X_pow_dvd m S.A (S.Delta p)).mpr hp⟩

/-- A coefficient witness at `p` proves the seam defect is not fake. -/
theorem defectNonmember_of_coeffWitness {p : Sigma}
    (h : S.BoundaryCoeffWitness p) :
    S.DefectNonmember p := by
  rcases h with ⟨j, hj, hcoeff⟩
  exact coeff_obstructs_right_factor_mod_X_pow (R := R) m j S.det_eq hj hcoeff

/-- A coefficient witness at `p` proves the seam defect is not left-fake. -/
theorem defectLeftNonmember_of_coeffWitness {p : Sigma}
    (h : S.BoundaryCoeffWitness p) :
    S.DefectLeftNonmember p := by
  rcases h with ⟨j, hj, hcoeff⟩
  exact coeff_obstructs_left_factor_mod_X_pow (R := R) m j S.det_eq hj hcoeff

/-- Determinant transversality at `p` directly proves the advertised
nonmembership `Delta_p ∉ A End + (X^m)`. -/
theorem defectNonmember_of_not_traceDivisible {p : Sigma}
    (h : ¬ S.BoundaryTraceDivisible p) :
    S.DefectNonmember p :=
  S.defectNonmember_of_coeffWitness (S.boundaryCoeffWitness_of_not_traceDivisible h)

/-- Determinant transversality at `p` also rules out left-factor fake defects. -/
theorem defectLeftNonmember_of_not_traceDivisible {p : Sigma}
    (h : ¬ S.BoundaryTraceDivisible p) :
    S.DefectLeftNonmember p :=
  S.defectLeftNonmember_of_coeffWitness (S.boundaryCoeffWitness_of_not_traceDivisible h)

/-- A determinant-transverse sigma family contains an actual nonmember defect. -/
theorem exists_defectNonmember_of_hasDeterminantTransverseDefect
    (h : S.HasDeterminantTransverseDefect) :
    ∃ p : Sigma, S.DefectNonmember p := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, S.defectNonmember_of_not_traceDivisible hp⟩

/-- A determinant-transverse sigma family contains an actual left-nonmember defect. -/
theorem exists_defectLeftNonmember_of_hasDeterminantTransverseDefect
    (h : S.HasDeterminantTransverseDefect) :
    ∃ p : Sigma, S.DefectLeftNonmember p := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, S.defectLeftNonmember_of_not_traceDivisible hp⟩

/-- A nontrivial Fitting boundary in the sigma family produces the desired
presentation nonmembership for some sigma defect. -/
theorem exists_defectNonmember_of_hasNontrivialFittingBoundary
    (h : HasNontrivialFittingBoundary m S.A S.Delta) :
    ∃ p : Sigma, S.DefectNonmember p :=
  S.exists_defectNonmember_of_hasDeterminantTransverseDefect
    (S.hasNontrivialFittingBoundary_iff_hasDeterminantTransverseDefect.mp h)

end TorsionSeamPresentation

end RHTower
