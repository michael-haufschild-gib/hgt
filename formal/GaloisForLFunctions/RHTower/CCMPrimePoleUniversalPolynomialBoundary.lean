import GaloisForLFunctions.RHTower.CCMPrimePolePolynomialBoundary

/-!
# Universal algebraic boundary for arbitrary CCM pole families

A free polynomial contains only finitely many generators.  This module proves
that fact internally, with repetitions allowed, and transports the finite CCM
joint-boundary theorem to an arbitrary family of positive local scales.

Thus the entire all-prime free polynomial algebra has a canonical character
after quotienting by compact evaluations.  The theorem is algebraic: it does
not assert a common Weyl sequence for an infinite family or continuity on a
completed all-prime operator algebra.
-/

noncomputable section

namespace RHTower

/-- Every free polynomial has a presentation using finitely many, possibly
repeated, generators. -/
theorem operatorPolynomial_exists_fin_presentation
    {ι : Type*} (Q : OperatorPolynomial ι) :
    ∃ d : ℕ, ∃ σ : Fin d → ι, ∃ R : OperatorPolynomial (Fin d),
      FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σ i)) R = Q := by
  induction Q using FreeAlgebra.induction with
  | grade0 c =>
      refine ⟨0, Fin.elim0, algebraMap ℂ (OperatorPolynomial (Fin 0)) c, ?_⟩
      simp
  | grade1 x =>
      refine ⟨1, fun _ => x, FreeAlgebra.ι ℂ (0 : Fin 1), ?_⟩
      simp
  | add A B hA hB =>
      obtain ⟨dA, σA, RA, hRA⟩ := hA
      obtain ⟨dB, σB, RB, hRB⟩ := hB
      let σ : Fin (dA + dB) → ι := Fin.append σA σB
      let eA : OperatorPolynomial (Fin dA) →ₐ[ℂ]
          OperatorPolynomial (Fin (dA + dB)) :=
        FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (Fin.castAdd dB i))
      let eB : OperatorPolynomial (Fin dB) →ₐ[ℂ]
          OperatorPolynomial (Fin (dA + dB)) :=
        FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (Fin.natAdd dA i))
      refine ⟨dA + dB, σ, eA RA + eB RB, ?_⟩
      let F : OperatorPolynomial (Fin (dA + dB)) →ₐ[ℂ] OperatorPolynomial ι :=
        FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σ i))
      have hFA : F.comp eA =
          FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σA i)) := by
        apply FreeAlgebra.hom_ext
        funext i
        simp [F, eA, σ]
      have hFB : F.comp eB =
          FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σB i)) := by
        apply FreeAlgebra.hom_ext
        funext i
        simp [F, eB, σ]
      change F (eA RA + eB RB) = A + B
      rw [map_add, ← AlgHom.comp_apply, hFA, ← AlgHom.comp_apply, hFB, hRA, hRB]
  | mul A B hA hB =>
      obtain ⟨dA, σA, RA, hRA⟩ := hA
      obtain ⟨dB, σB, RB, hRB⟩ := hB
      let σ : Fin (dA + dB) → ι := Fin.append σA σB
      let eA : OperatorPolynomial (Fin dA) →ₐ[ℂ]
          OperatorPolynomial (Fin (dA + dB)) :=
        FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (Fin.castAdd dB i))
      let eB : OperatorPolynomial (Fin dB) →ₐ[ℂ]
          OperatorPolynomial (Fin (dA + dB)) :=
        FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (Fin.natAdd dA i))
      refine ⟨dA + dB, σ, eA RA * eB RB, ?_⟩
      let F : OperatorPolynomial (Fin (dA + dB)) →ₐ[ℂ] OperatorPolynomial ι :=
        FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σ i))
      have hFA : F.comp eA =
          FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σA i)) := by
        apply FreeAlgebra.hom_ext
        funext i
        simp [F, eA, σ]
      have hFB : F.comp eB =
          FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σB i)) := by
        apply FreeAlgebra.hom_ext
        funext i
        simp [F, eB, σ]
      change F (eA RA * eB RB) = A * B
      rw [map_mul, ← AlgHom.comp_apply, hFA, ← AlgHom.comp_apply, hFB, hRA, hRB]

variable {ι : Type*}

/-- Evaluate a free polynomial at an arbitrary family of positive CCM pole projections. -/
def ccmPrimePoleFamilyOperatorPolynomialEval
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    OperatorPolynomial ι →ₐ[ℂ]
      (CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert) :=
  operatorPolynomialEval fun i =>
    (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection

/-- The arbitrary-index scalar boundary evaluation sending each generator to one. -/
def ccmPrimePoleFamilyOperatorPolynomialBoundary :
    OperatorPolynomial ι →ₐ[ℂ] ℂ :=
  operatorPolynomialBoundary

/-- **Universal algebraic essential-boundary inequality.** For an arbitrary
family of positive scales, every polynomial sees only a finite subfamily and
its boundary value is bounded by the essential norm of its operator evaluation. -/
theorem norm_ccmPrimePoleFamilyOperatorPolynomialBoundary_le_essentialNorm_eval
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) (Q : OperatorPolynomial ι) :
    ‖ccmPrimePoleFamilyOperatorPolynomialBoundary Q‖ ≤
      essentialNorm (ccmPrimePoleFamilyOperatorPolynomialEval L hL Q) := by
  obtain ⟨d, σ, R, hR⟩ := operatorPolynomial_exists_fin_presentation Q
  let Ld : Fin d → ℝ := fun i => L (σ i)
  have hLd : ∀ i, 0 < Ld i := fun i => hL (σ i)
  let S : OperatorPolynomial (Fin d) →ₐ[ℂ] OperatorPolynomial ι :=
    FreeAlgebra.lift ℂ (fun i => FreeAlgebra.ι ℂ (σ i))
  have hevalComp : (ccmPrimePoleFamilyOperatorPolynomialEval L hL).comp S =
      ccmPrimePoleOperatorPolynomialEval Ld hLd := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [ccmPrimePoleFamilyOperatorPolynomialEval,
      ccmPrimePoleOperatorPolynomialEval, operatorPolynomialEval, S, Ld]
  have hboundaryComp : ccmPrimePoleFamilyOperatorPolynomialBoundary.comp S =
      ccmPrimePoleOperatorPolynomialBoundary := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [ccmPrimePoleFamilyOperatorPolynomialBoundary,
      ccmPrimePoleOperatorPolynomialBoundary, operatorPolynomialBoundary, S]
  have heval : ccmPrimePoleFamilyOperatorPolynomialEval L hL Q =
      ccmPrimePoleOperatorPolynomialEval Ld hLd R := by
    rw [← hR]
    change ((ccmPrimePoleFamilyOperatorPolynomialEval L hL).comp S) R = _
    rw [hevalComp]
  have hboundary : ccmPrimePoleFamilyOperatorPolynomialBoundary Q =
      ccmPrimePoleOperatorPolynomialBoundary R := by
    rw [← hR]
    change (ccmPrimePoleFamilyOperatorPolynomialBoundary.comp S) R = _
    rw [hboundaryComp]
  rw [heval, hboundary]
  exact norm_ccmPrimePoleOperatorPolynomialBoundary_le_essentialNorm_eval Ld hLd R

/-- A compactly evaluated polynomial from an arbitrary CCM pole family vanishes
at the universal algebraic boundary. -/
theorem ccmPrimePoleFamilyOperatorPolynomialBoundary_eq_zero_of_compact
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) (Q : OperatorPolynomial ι)
    (hQ : IsCompactOperator (ccmPrimePoleFamilyOperatorPolynomialEval L hL Q)) :
    ccmPrimePoleFamilyOperatorPolynomialBoundary Q = 0 := by
  have hess : essentialNorm (ccmPrimePoleFamilyOperatorPolynomialEval L hL Q) = 0 := by
    apply le_antisymm
    · simpa using essentialNorm_le
        (ccmPrimePoleFamilyOperatorPolynomialEval L hL Q)
        (ccmPrimePoleFamilyOperatorPolynomialEval L hL Q) hQ
    · exact essentialNorm_nonneg _
  have hbound :=
    norm_ccmPrimePoleFamilyOperatorPolynomialBoundary_le_essentialNorm_eval L hL Q
  rw [hess] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

/-- The two-sided ideal of arbitrary-index polynomials with compact CCM evaluation. -/
def ccmPrimePoleFamilyPolynomialCompactIdeal
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) : Ideal (OperatorPolynomial ι) where
  carrier := {Q | IsCompactOperator (ccmPrimePoleFamilyOperatorPolynomialEval L hL Q)}
  zero_mem' := by
    simpa using (isCompactOperator_zero : IsCompactOperator
      (0 : CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert))
  add_mem' := by
    intro Q R hQ hR
    simpa using hQ.add hR
  smul_mem' := by
    intro Q R hR
    change IsCompactOperator (ccmPrimePoleFamilyOperatorPolynomialEval L hL (Q * R))
    rw [map_mul]
    exact hR.clm_comp (ccmPrimePoleFamilyOperatorPolynomialEval L hL Q)

instance ccmPrimePoleFamilyPolynomialCompactIdeal_isTwoSided
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    (ccmPrimePoleFamilyPolynomialCompactIdeal L hL).IsTwoSided where
  mul_mem_of_left {Q} R hQ := by
    change IsCompactOperator (ccmPrimePoleFamilyOperatorPolynomialEval L hL (Q * R))
    rw [map_mul]
    exact hQ.comp_clm (ccmPrimePoleFamilyOperatorPolynomialEval L hL R)

/-- Algebraic Calkin image of an arbitrary CCM pole-projection family. -/
abbrev CCMPrimePoleFamilyPolynomialCalkinAlgebra
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :=
  OperatorPolynomial ι ⧸ ccmPrimePoleFamilyPolynomialCompactIdeal L hL

/-- **Universal algebraic Calkin boundary character.** Every positive CCM pole
family, of arbitrary cardinality, has a character sending every projection
generator to one after quotienting polynomial relations by compact evaluation. -/
def ccmPrimePoleFamilyPolynomialCalkinCharacter
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    CCMPrimePoleFamilyPolynomialCalkinAlgebra L hL →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (ccmPrimePoleFamilyPolynomialCompactIdeal L hL)
    ccmPrimePoleFamilyOperatorPolynomialBoundary
    (fun Q hQ => ccmPrimePoleFamilyOperatorPolynomialBoundary_eq_zero_of_compact
      L hL Q hQ)

@[simp]
theorem ccmPrimePoleFamilyPolynomialCalkinCharacter_mk
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) (Q : OperatorPolynomial ι) :
    ccmPrimePoleFamilyPolynomialCalkinCharacter L hL
      (Ideal.Quotient.mk (ccmPrimePoleFamilyPolynomialCompactIdeal L hL) Q) =
      ccmPrimePoleFamilyOperatorPolynomialBoundary Q := by
  simp [ccmPrimePoleFamilyPolynomialCalkinCharacter]

/-- Every generator has universal boundary value one. -/
@[simp]
theorem ccmPrimePoleFamilyPolynomialCalkinCharacter_generator
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) (i : ι) :
    ccmPrimePoleFamilyPolynomialCalkinCharacter L hL
      (Ideal.Quotient.mk (ccmPrimePoleFamilyPolynomialCompactIdeal L hL)
        (FreeAlgebra.ι ℂ i)) = 1 := by
  rw [ccmPrimePoleFamilyPolynomialCalkinCharacter_mk]
  simp [ccmPrimePoleFamilyOperatorPolynomialBoundary, operatorPolynomialBoundary]

/-- The universal character is uniquely determined by taking value one on all generators. -/
theorem ccmPrimePoleFamilyPolynomialCalkinCharacter_unique
    (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (χ : CCMPrimePoleFamilyPolynomialCalkinAlgebra L hL →ₐ[ℂ] ℂ)
    (hχ : ∀ i : ι,
      χ (Ideal.Quotient.mk (ccmPrimePoleFamilyPolynomialCompactIdeal L hL)
        (FreeAlgebra.ι ℂ i)) = 1) :
    χ = ccmPrimePoleFamilyPolynomialCalkinCharacter L hL := by
  apply Ideal.Quotient.algHom_ext
  apply FreeAlgebra.hom_ext
  funext i
  change χ (Ideal.Quotient.mk (ccmPrimePoleFamilyPolynomialCompactIdeal L hL)
      (FreeAlgebra.ι ℂ i)) =
    ccmPrimePoleFamilyPolynomialCalkinCharacter L hL
      (Ideal.Quotient.mk (ccmPrimePoleFamilyPolynomialCompactIdeal L hL)
        (FreeAlgebra.ι ℂ i))
  rw [hχ i, ccmPrimePoleFamilyPolynomialCalkinCharacter_generator]

/-- The type of prime places. -/
abbrev CCMPrimeIndex := {p : ℕ // p.Prime}

/-- The CCM scale attached to a prime place. -/
def ccmAllPrimeLogScale (p : CCMPrimeIndex) : ℝ := Real.log (p : ℕ)

theorem ccmAllPrimeLogScale_pos (p : CCMPrimeIndex) : 0 < ccmAllPrimeLogScale p := by
  exact Real.log_pos (by exact_mod_cast p.property.one_lt)

/-- The algebraic all-prime polynomial Calkin quotient. -/
abbrev CCMAllPrimePolePolynomialCalkinAlgebra :=
  CCMPrimePoleFamilyPolynomialCalkinAlgebra ccmAllPrimeLogScale ccmAllPrimeLogScale_pos

/-- **All-prime boundary character.** The complete prime-log family carries one
algebraic polynomial Calkin character with value one at every prime place. -/
def ccmAllPrimePolePolynomialCalkinCharacter :
    CCMAllPrimePolePolynomialCalkinAlgebra →ₐ[ℂ] ℂ :=
  ccmPrimePoleFamilyPolynomialCalkinCharacter ccmAllPrimeLogScale ccmAllPrimeLogScale_pos

@[simp]
theorem ccmAllPrimePolePolynomialCalkinCharacter_generator (p : CCMPrimeIndex) :
    ccmAllPrimePolePolynomialCalkinCharacter
      (Ideal.Quotient.mk
        (ccmPrimePoleFamilyPolynomialCompactIdeal
          ccmAllPrimeLogScale ccmAllPrimeLogScale_pos)
        (FreeAlgebra.ι ℂ p)) = 1 := by
  exact ccmPrimePoleFamilyPolynomialCalkinCharacter_generator
    ccmAllPrimeLogScale ccmAllPrimeLogScale_pos p

end RHTower
