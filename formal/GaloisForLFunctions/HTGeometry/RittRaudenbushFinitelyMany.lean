import GaloisForLFunctions.HTGeometry.DifferentialPolynomialSplitOff
import GaloisForLFunctions.HTGeometry.RittBasisContractionDescent

/-!
# The Ritt–Raudenbush basis theorem in finitely many differential indeterminates

Splitting one indeterminate off the top turns the coefficient-ring form of Ritt's basis theorem into
an induction: over a differential field of characteristic zero every ideal is trivially the radical
differential ideal of a finite set, and each further indeterminate is one application of the
one-variable theorem over the ring already built.

* `radDiffFG_differentialPolynomial_fin` — every radical differential ideal of `C{y₁, …, y_k}` is
  the radical differential ideal of a finite set.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

/-- A differential ring isomorphism has a differential inverse. -/
theorem ringEquiv_symm_deriv {A B : Type*} [CommRing A] [Differential A] [CommRing B]
    [Differential B] (e : A ≃+* B) (he : ∀ x, e (Differential.deriv x) = Differential.deriv (e x))
    (y : B) : e.symm (Differential.deriv y) = Differential.deriv (e.symm y) := by
  have h := he (e.symm y)
  rw [e.apply_symm_apply] at h
  rw [← h, e.symm_apply_apply]

/-- Finite generation of radical differential ideals travels along a differential ring
isomorphism. -/
theorem radDiffFG_of_ringEquiv {A B : Type*} [CommRing A] [Differential A] [CommRing B]
    [Differential B] (e : A ≃+* B)
    (he : ∀ x, e (Differential.deriv x) = Differential.deriv (e x))
    (hB : ∀ J : Ideal B, J.IsRadical → (∀ y ∈ J, Differential.deriv y ∈ J) → IsRadDiffFG J)
    (I : Ideal A) (hrad : I.IsRadical) (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) :
    IsRadDiffFG I := by
  set J : Ideal B := Ideal.comap (e.symm : B →+* A) I with hJ
  have hJrad : J.IsRadical := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    refine hrad ⟨n, ?_⟩
    show e.symm y ^ n ∈ I
    rw [← map_pow]
    exact hn
  have hJδ : ∀ y ∈ J, Differential.deriv y ∈ J := by
    intro y hy
    show e.symm (Differential.deriv y) ∈ I
    rw [ringEquiv_symm_deriv e he y]
    exact hδ _ hy
  have hcomap : Ideal.comap (e : A →+* B) J = I := by
    rw [hJ, Ideal.comap_comap]
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by
      ext x
      exact e.symm_apply_apply x
    rw [this, Ideal.comap_id]
  rw [← hcomap]
  exact isRadDiffFG_comap_of_ringEquiv e he hJrad hJδ (hB J hJrad hJδ)

variable {C : Type*} [Field C] [Algebra ℚ C] [Differential C]

omit [Algebra ℚ C] in
/-- Every ideal of a field is the radical differential ideal of a finite set. -/
theorem isRadDiffFG_of_field (J : Ideal C) : IsRadDiffFG J := by
  rcases Ideal.eq_bot_or_top J with h | h
  · subst h
    refine ⟨∅, (le_antisymm ?_ bot_le).symm⟩
    refine radicalDifferentialIdeal_le (by simp) ?_ ?_
    · intro y hy
      obtain ⟨n, hn⟩ := hy
      rw [Ideal.mem_bot] at hn ⊢
      exact pow_eq_zero_iff'.mp hn |>.1
    · intro x hx
      rw [Ideal.mem_bot] at hx ⊢
      rw [hx, map_zero]
  · subst h
    exact isRadDiffFG_top

omit [Algebra ℚ C] in
/-- Renaming the indeterminates is a differential isomorphism. -/
theorem rename_differentialPolynomialOverDerivation {ι κ : Type*} (e : ι ≃ κ)
    (P : DifferentialPolynomial ι C) :
    MvPolynomial.rename (Prod.map e id) (differentialPolynomialOverDerivation ι C P)
      = differentialPolynomialOverDerivation κ C (MvPolynomial.rename (Prod.map e id) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      have hL : differentialPolynomialOverDerivation ι C (P * MvPolynomial.X j)
          = differentialPolynomialOverDerivation ι C P * MvPolynomial.X j
            + P * differentialPolynomialOverDerivation ι C (MvPolynomial.X j) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      have hR : differentialPolynomialOverDerivation κ C
          (MvPolynomial.rename (Prod.map e id) P * MvPolynomial.rename (Prod.map e id)
            (MvPolynomial.X j))
          = differentialPolynomialOverDerivation κ C
              (MvPolynomial.rename (Prod.map e id) P)
              * MvPolynomial.rename (Prod.map e id) (MvPolynomial.X j)
            + MvPolynomial.rename (Prod.map e id) P * differentialPolynomialOverDerivation κ C
                (MvPolynomial.rename (Prod.map e id) (MvPolynomial.X j)) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      obtain ⟨i, n⟩ := j
      rw [hL, map_add, map_mul, map_mul, hP, map_mul, hR]
      simp [differentialPolynomialOverDerivation_X]

/-- The base-change isomorphism of a renaming, as a differential ring isomorphism. -/
def renameDifferentialEquiv {ι κ : Type*} (e : ι ≃ κ) :
    DifferentialPolynomial ι C ≃+* DifferentialPolynomial κ C :=
  (MvPolynomial.renameEquiv C (e.prodCongr (Equiv.refl ℕ))).toRingEquiv

omit [Algebra ℚ C] in
theorem renameDifferentialEquiv_deriv {ι κ : Type*} (e : ι ≃ κ)
    (P : DifferentialPolynomial ι C) :
    renameDifferentialEquiv e (Differential.deriv P)
      = Differential.deriv (renameDifferentialEquiv (C := C) e P) :=
  rename_differentialPolynomialOverDerivation e P

/-- **One more differential indeterminate.** -/
theorem radDiffFG_option {ι : Type*}
    (hbase : ∀ J : Ideal (DifferentialPolynomial ι C), J.IsRadical →
      (∀ x ∈ J, Differential.deriv x ∈ J) → IsRadDiffFG J)
    (I : Ideal (DifferentialPolynomial (Option ι) C)) (hrad : I.IsRadical)
    (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) : IsRadDiffFG I :=
  radDiffFG_of_ringEquiv (splitOffEquiv C ι) (splitOffEquiv_deriv C ι)
    (fun J hJrad hJδ =>
      radDiffFG_differentialPolynomial_of_base hbase J hJrad hJδ)
    I hrad hδ

/-- **The Ritt–Raudenbush basis theorem.**  Every radical differential ideal of the differential
polynomial ring in finitely many indeterminates over a differential field of characteristic zero is
the radical differential ideal of a finite set. -/
theorem radDiffFG_differentialPolynomial_fin :
    ∀ (k : ℕ) (J : Ideal (DifferentialPolynomial (Fin k) C)), J.IsRadical →
      (∀ x ∈ J, Differential.deriv x ∈ J) → IsRadDiffFG J := by
  intro k
  induction k with
  | zero =>
      intro J hrad hδ
      refine radDiffFG_of_ringEquiv
        (MvPolynomial.isEmptyRingEquiv C (Fin 0 × ℕ)) ?_ (fun L _ _ => isRadDiffFG_of_field L)
        J hrad hδ
      intro P
      induction P using MvPolynomial.induction_on with
      | C c =>
          have hCe : ∀ a : C,
              (MvPolynomial.isEmptyRingEquiv C (Fin 0 × ℕ)) (MvPolynomial.C a) = a := fun a =>
            (RingEquiv.eq_symm_apply (MvPolynomial.isEmptyRingEquiv C (Fin 0 × ℕ))).mp rfl
          show (MvPolynomial.isEmptyRingEquiv C (Fin 0 × ℕ))
              (differentialPolynomialOverDerivation (Fin 0) C (MvPolynomial.C c)) = _
          rw [differentialPolynomialOverDerivation_C, hCe, hCe]
      | add P Q hP hQ => simp only [map_add, hP, hQ]
      | mul_X P j _ => exact (IsEmpty.false j.1).elim
  | succ k ih =>
      intro J hrad hδ
      refine radDiffFG_of_ringEquiv (renameDifferentialEquiv (C := C) (finSuccEquiv k))
        (renameDifferentialEquiv_deriv _) (fun L hLrad hLδ => ?_) J hrad hδ
      exact radDiffFG_option (fun N hNrad hNδ => ih N hNrad hNδ) L hLrad hLδ

end

end GaloisForLFunctions.HTGeometry
