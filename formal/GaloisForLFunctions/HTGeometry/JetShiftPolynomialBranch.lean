import GaloisForLFunctions.HTGeometry.JetNormalizingShiftDescent

/-!
# The polynomial branch of the jet descent

What survives the slicing of a normalizing shift at level `N + 3` when the denominator is constant:
a polynomial `u` over the prefix field with

`Φ̃(u) = R'·u − (A·X + B)`.

Two of its degrees are decided immediately.  In degree zero the equation forces `A = 0`, because the
left side and `R'·u` are both constants.  In degree at least three the two top coefficients see
nothing of the inhomogeneous term, so they satisfy the same affine cocycle as in the homogeneous
case, and their ratio — divided by the degree — is a normalizing shift one level down.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial

noncomputable section

/-! ## The cocycle of a shifted relation -/

variable {K : Type*} [Field K] [CharZero K]

/-- **The affine cocycle of a shifted relation.**  If a polynomial of degree at least three is
carried by a twisted affine substitution to its own scalar multiple up to a term of degree at most
one, the ratio of its two top coefficients solves the cocycle equation. -/
theorem exists_cocycle_of_shift_polynomial (Φ : K →+* K) {ρ L : K} (hρ : ρ ≠ 0)
    {u S : Polynomial K} {a : ℕ} (hdeg : u.natDegree = a + 1) (ha : 2 ≤ a)
    (hSdeg : S.natDegree ≤ 1)
    (hcu : twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u
      = Polynomial.C ρ * u - S) :
    ∃ s : K, Φ s = ρ * s - L := by
  have hSa : S.coeff a = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hSa1 : S.coeff (a + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : (twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u).coeff a
      = ρ * u.coeff a := by
    rw [hcu, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hSa, sub_zero]
  have h2 : (twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u).coeff (a + 1)
      = ρ * u.coeff (a + 1) := by
    rw [hcu, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hSa1, sub_zero]
  have hcoc := twistComp_affine_cocycle_of_coeff Φ hρ hdeg h1 h2
  have hcast : ((a : K) + 1) ≠ 0 := by
    have h : ((a + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  refine ⟨(u.coeff a / u.coeff (a + 1)) / ((a : K) + 1), ?_⟩
  rw [map_div₀, map_add, map_natCast, map_one, hcoc]
  field_simp

omit [CharZero K] in
/-- In degree zero the inhomogeneous term of a shifted relation has no linear part. -/
theorem coeff_one_eq_zero_of_shift_polynomial_deg_zero (Φ : K →+* K) {ρ L : K}
    {u S : Polynomial K} (hdeg : u.natDegree = 0)
    (hcu : twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u
      = Polynomial.C ρ * u - S) :
    S.coeff 1 = 0 := by
  have huC : u = Polynomial.C (u.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hleft : twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u
      = Polynomial.C (Φ (u.coeff 0)) := by
    conv_lhs => rw [huC]
    rw [twistComp_C]
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 1) hcu
  simp only [hleft, Polynomial.coeff_C, Polynomial.coeff_sub, Polynomial.coeff_C_mul] at hcoeff
  rw [huC] at hcoeff
  simp only [Polynomial.coeff_C] at hcoeff
  simpa using hcoeff.symm

/-! ## The branch in the jet field -/

variable {C : Type*} [Field C] [CharZero C]

/-- **The high-degree polynomial branch descends.** -/
theorem hasNormalizingShift_of_polynomial_branch (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (N : ℕ) {u : Polynomial ↥(jetPrefixField C (N + 2))}
    {A B : ↥(jetPrefixField C (N + 2))} (hdeg : 3 ≤ u.natDegree)
    (hcu : twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
        (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
      = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
        - (Polynomial.C A * Polynomial.X + Polynomial.C B)) :
    HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 2 by omega) := by
  classical
  set hM2 : (1 : ℕ) ≤ N + 2 := by omega
  have hρF : substitutionDerivPrefix R hM2 ≠ 0 := substitutionDerivPrefix_ne_zero R hR hM2
  have haffine : substitutionAffine R hM2
      = Polynomial.C (substitutionDerivPrefix R hM2) * Polynomial.X
        + Polynomial.C (substitutionShiftPrefix R hM2) := rfl
  rw [haffine] at hcu
  obtain ⟨a, hadef⟩ : ∃ a : ℕ, u.natDegree = a + 1 := ⟨u.natDegree - 1, by omega⟩
  have hSdeg : (Polynomial.C A * Polynomial.X + Polynomial.C B).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le ?_ ?_
    · exact le_trans (Polynomial.natDegree_mul_le) (by simp)
    · simp
  obtain ⟨s, hs⟩ := exists_cocycle_of_shift_polynomial
    (jetSubstitutionPrefix R hR (N + 2)).toRingHom hρF hadef (by omega) hSdeg hcu
  exact ⟨s, hs⟩

/-- **The degree-zero polynomial branch forces the linear part of the shift to vanish.** -/
theorem top_eq_zero_of_polynomial_branch_deg_zero (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (N : ℕ) {u : Polynomial ↥(jetPrefixField C (N + 2))}
    {A B : ↥(jetPrefixField C (N + 2))} (hdeg : u.natDegree = 0)
    (hcu : twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
        (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
      = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
        - (Polynomial.C A * Polynomial.X + Polynomial.C B)) :
    A = 0 := by
  classical
  set hM2 : (1 : ℕ) ≤ N + 2 := by omega
  have haffine : substitutionAffine R hM2
      = Polynomial.C (substitutionDerivPrefix R hM2) * Polynomial.X
        + Polynomial.C (substitutionShiftPrefix R hM2) := rfl
  rw [haffine] at hcu
  have hcoeff := coeff_one_eq_zero_of_shift_polynomial_deg_zero
    (jetSubstitutionPrefix R hR (N + 2)).toRingHom hdeg hcu
  simpa using hcoeff

end

end GaloisForLFunctions.HTGeometry
