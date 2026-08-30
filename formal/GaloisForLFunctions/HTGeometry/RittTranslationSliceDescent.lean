import GaloisForLFunctions.HTGeometry.RittEigenSliceDescent

/-!
# The inhomogeneous slice over a translated generator

At jet order three and above the top coordinate of the linearizer tower is *unipotent*: the shift
translates it, `σ t = t + γ`, instead of scaling it.  A coprime fraction `P/Q` solving

`σ (P/Q) = P/Q + (α·t + β)`

still forces the denominator to be fixed — coprimality gives `Q ∣ Q^Φ∘(X+γ)`, degrees agree and the
substitution is monic, so `Q^Φ∘(X+γ) = Q` exactly — and the second-highest coefficients then produce
a relation in the coefficient field alone.

Which relation depends on the shape of the fraction, but always with *constant* coefficients: if the
denominator is nonconstant its second-highest coefficient gives `Φ(u) − u = −deg Q · γ`, and if the
denominator is trivial the numerator's second-highest coefficient gives `Φ(u) − u = −deg P · γ`,
corrected by `α / leadingCoeff P` exactly when `deg P = 2`, while the linear and constant cases give
`Φ(u) − u = α` outright.  The uniform statement is

`∃ u κ λ, (κ, λ) ≠ (0,0), Φ κ = κ, Φ λ = λ, Φ(u) − u = κ·α + λ·γ`,

which is what a level induction consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **The translated inhomogeneous coprime descent.** -/
theorem exists_constant_combination_of_translation_cross (Φ : K →+* K) {γ α β : K}
    {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (X + C γ) P * Q
      = twistComp Φ (X + C γ) Q * (P + (C α * X + C β) * Q)) :
    ∃ u κ lam : K, (κ ≠ 0 ∨ lam ≠ 0) ∧ Φ κ = κ ∧ Φ lam = lam ∧
      Φ u - u = κ * α + lam * γ := by
  classical
  have hTdeg : (X + C γ : K[X]).natDegree = 1 := natDegree_X_add_C γ
  have hTmonic : (X + C γ : K[X]).Monic := monic_X_add_C γ
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have htaylor : ∀ p : K[X], twistComp Φ (X + C γ) p = taylor γ (p.map Φ) := by
    intro p
    rw [twistComp, taylor_apply]
  -- the denominator is fixed
  have hcopQ : IsCoprime Q (P + (C α * X + C β) * Q) := by
    have h := hcop.symm.add_mul_left_right (C α * X + C β)
    have heq : P + Q * (C α * X + C β) = P + (C α * X + C β) * Q := by ring
    rwa [heq] at h
  have hdvd : Q ∣ twistComp Φ (X + C γ) Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ (X + C γ) P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hd1 : d = 1 := by
    have hlead := leadingCoeff_twistComp Φ hTdeg Q
    rw [hd, hQ.leadingCoeff, map_one, hTmonic.leadingCoeff, one_pow, mul_one] at hlead
    rw [leadingCoeff_mul, leadingCoeff_C, hQ.leadingCoeff, mul_one] at hlead
    exact hlead
  have hQfix : twistComp Φ (X + C γ) Q = Q := by rw [hd, hd1, map_one, one_mul]
  by_cases he : Q.natDegree = 0
  · -- trivial denominator: the numerator carries the relation
    have hQ1 : Q = 1 := by
      have h1 : Q = C (Q.coeff 0) := eq_C_of_natDegree_eq_zero he
      have h2 : Q.coeff 0 = 1 := by
        have h3 := hQ.coeff_natDegree
        rwa [he] at h3
      rw [h1, h2, map_one]
    subst hQ1
    have hP : twistComp Φ (X + C γ) P = P + (C α * X + C β) := by
      have h := hcross
      rw [hQfix] at h
      simpa using h
    set D : ℕ := P.natDegree with hD
    by_cases hD1 : D ≤ 1
    · -- degree at most one: the top coefficient gives `Φ u − u = α`
      refine ⟨P.coeff 1, 1, 0, Or.inl one_ne_zero, map_one Φ, map_zero Φ, ?_⟩
      have hcoeff := congrArg (fun p : K[X] => p.coeff 1) hP
      simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, mul_one] at hcoeff
      have hlow : (twistComp Φ (X + C γ) P).coeff 1 = Φ (P.coeff 1) := by
        rcases Nat.lt_or_ge D 1 with hlt | hge
        · have hP0 : P.natDegree = 0 := by omega
          obtain ⟨a, ha⟩ : ∃ a : K, P = C a := ⟨P.coeff 0, eq_C_of_natDegree_eq_zero hP0⟩
          rw [ha, twistComp_C]
          simp
        · have hDeq : D = 1 := by omega
          have hnd : (twistComp Φ (X + C γ) P).natDegree = 1 := by
            rw [natDegree_twistComp Φ hTdeg, ← hD, hDeq]
          have := leadingCoeff_twistComp Φ hTdeg P
          rw [hTmonic.leadingCoeff, one_pow, mul_one] at this
          rw [leadingCoeff, hnd] at this
          rw [this, leadingCoeff, ← hD, hDeq]
      rw [hlow] at hcoeff
      simp only [if_neg (by norm_num : ¬ (1 : ℕ) = 0), add_zero] at hcoeff
      linear_combination hcoeff
    · -- degree at least two: the second-highest coefficient gives the combination
      have hDpos : 0 < D := by omega
      set c : K := P.leadingCoeff with hc
      have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr (fun h => by
        rw [h, natDegree_zero] at hD; omega)
      have htop : Φ c = c := by
        have hcoeff := congrArg (fun p : K[X] => p.coeff D) hP
        have hlead : (twistComp Φ (X + C γ) P).coeff D = Φ c := by
          have hnd : (twistComp Φ (X + C γ) P).natDegree = D := by
            rw [natDegree_twistComp Φ hTdeg, ← hD]
          have h2 := leadingCoeff_twistComp Φ hTdeg P
          rw [hTmonic.leadingCoeff, one_pow, mul_one] at h2
          rw [leadingCoeff, hnd] at h2
          rw [h2, ← hc]
        simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C] at hcoeff
        rw [hlead, if_neg (by omega : ¬ (1 : ℕ) = D), if_neg (by omega : ¬ D = 0)] at hcoeff
        simp only [mul_zero, add_zero] at hcoeff
        have hcD : c = P.coeff D := by rw [hc, leadingCoeff, ← hD]
        rw [hcoeff]
        exact hcD.symm
      -- normalise the numerator
      have hP0 : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hD; omega
      set Pm : K[X] := P * C c⁻¹ with hPm
      have hPmm : Pm.Monic := by
        rw [hPm, hc]
        exact monic_mul_leadingCoeff_inv hP0
      have hPmdeg : Pm.natDegree = D := by
        rw [hPm, natDegree_mul hP0 (by simpa using inv_ne_zero hc0), natDegree_C, ← hD, add_zero]
      have hPfac : P = C c * Pm := by
        rw [hPm, ← mul_assoc, mul_comm (C c) P, mul_assoc, ← map_mul,
          mul_inv_cancel₀ hc0, map_one, mul_one]
      have hexp : C (Φ c) * twistComp Φ (X + C γ) Pm = C c * Pm + (C α * X + C β) := by
        rw [← twistComp_C Φ (X + C γ) c, ← twistComp_mul, ← hPfac, hP, hPfac]
      rw [htop] at hexp
      -- read the coefficient one below the top
      have hnext : (twistComp Φ (X + C γ) Pm).nextCoeff = Φ Pm.nextCoeff + (D : K) * γ := by
        rw [htaylor, GaloisForLFunctions.nextCoeff_taylor_of_monic (Pm.map Φ) (hPmm.map Φ)
          (by rw [natDegree_map_twist, hPmdeg]; omega) γ]
        rw [nextCoeff_map Φ.injective, natDegree_map_twist, hPmdeg]
      have hnd : (twistComp Φ (X + C γ) Pm).natDegree = D := by
        rw [natDegree_twistComp Φ hTdeg, hPmdeg]
      have hcoeff := congrArg (fun p : K[X] => p.coeff (D - 1)) hexp
      simp only [coeff_C_mul, coeff_add, coeff_X, coeff_C] at hcoeff
      have hL : (twistComp Φ (X + C γ) Pm).coeff (D - 1) = Φ Pm.nextCoeff + (D : K) * γ := by
        rw [← hnext, nextCoeff_of_natDegree_pos (by rw [hnd]; omega), hnd]
      have hR : Pm.coeff (D - 1) = Pm.nextCoeff := by
        rw [nextCoeff_of_natDegree_pos (by rw [hPmdeg]; omega), hPmdeg]
      rw [hL, hR] at hcoeff
      refine ⟨Pm.nextCoeff, if D = 2 then c⁻¹ else 0, -(D : K), ?_, ?_, ?_, ?_⟩
      · right
        simpa using (by omega : D ≠ 0)
      · by_cases h2 : D = 2
        · rw [if_pos h2, map_inv₀, htop]
        · rw [if_neg h2, map_zero]
      · rw [map_neg, map_natCast]
      · by_cases h2 : D = 2
        · rw [if_pos h2]
          rw [h2] at hcoeff ⊢
          norm_num at hcoeff
          have h : c * (Φ Pm.nextCoeff - Pm.nextCoeff + 2 * γ) = α := by
            linear_combination hcoeff
          field_simp
          linear_combination h
        · rw [if_neg h2]
          rw [if_neg (by omega : ¬ (1 : ℕ) = D - 1), if_neg (by omega : ¬ D - 1 = 0)] at hcoeff
          simp only [mul_zero, add_zero] at hcoeff
          have h : Φ Pm.nextCoeff - Pm.nextCoeff + (D : K) * γ = 0 := by
            refine mul_left_cancel₀ hc0 ?_
            linear_combination hcoeff
          linear_combination h
  · -- nonconstant denominator: its second-highest coefficient carries the relation
    have hepos : 0 < Q.natDegree := Nat.pos_of_ne_zero he
    have hnext : (twistComp Φ (X + C γ) Q).nextCoeff
        = Φ Q.nextCoeff + (Q.natDegree : K) * γ := by
      rw [htaylor, GaloisForLFunctions.nextCoeff_taylor_of_monic (Q.map Φ) (hQ.map Φ)
        (by rw [natDegree_map_twist]; exact hepos) γ]
      rw [nextCoeff_map Φ.injective, natDegree_map_twist]
    rw [hQfix] at hnext
    refine ⟨Q.nextCoeff, 0, -(Q.natDegree : K), ?_, map_zero Φ, ?_, ?_⟩
    · right
      simpa using he
    · rw [map_neg, map_natCast]
    · linear_combination -hnext

end GaloisForLFunctions.HTGeometry
