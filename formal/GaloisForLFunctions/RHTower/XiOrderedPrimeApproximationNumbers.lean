import GaloisForLFunctions.RHTower.XiOrderedPrimeTraceClassRelocation

/-!
# Exact approximation numbers of the ordered Xi reciprocal operator

The signed prime-sector operator has two eigenvalues of equal modulus for every ordered positive
Xi ordinate.  Reindexing its diagonal by `ℕ` therefore identifies every approximation number
exactly, including the even/odd multiplicity duplication.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

/-- Ordered approximation-number sequence for the signed reciprocal-Xi diagonal. -/
def xiOrderedSignedApproxNumber (n : ℕ) : ℝ :=
  (xiOrderedPositiveOrdinate (n / 2))⁻¹

theorem xiOrderedSignedApproxNumber_pos (n : ℕ) :
    0 < xiOrderedSignedApproxNumber n := by
  exact inv_pos.mpr (xiOrderedPositiveOrdinate_pos _)

theorem xiOrderedSignedApproxNumber_antitone :
    Antitone xiOrderedSignedApproxNumber := by
  intro i j hij
  exact (inv_le_inv₀ (xiOrderedPositiveOrdinate_pos _)
    (xiOrderedPositiveOrdinate_pos _)).2
      (xiOrderedPositiveOrdinate_monotone (Nat.div_le_div_right hij))

theorem norm_xiOrderedSignedPrimeMultiplier (i : RouteKSignedPrimeIndex) :
    ‖xiOrderedSignedPrimeMultiplier i‖ =
      xiOrderedSignedApproxNumber (routeKSignedPrimeEquiv.symm i) := by
  cases i with
  | inl p =>
      rw [xiOrderedSignedPrimeMultiplier, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (xiOrderedPrimeReciprocal_pos p)]
      simp [xiOrderedSignedApproxNumber, xiOrderedPrimeReciprocal,
        routeKSignedPrimeEquiv_symm_apply, routeKSignedPrimeNatIndex]
  | inr p =>
      rw [xiOrderedSignedPrimeMultiplier, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (xiOrderedPrimeReciprocal_pos p)]
      simp [xiOrderedSignedApproxNumber, xiOrderedPrimeReciprocal,
        routeKSignedPrimeEquiv_symm_apply, routeKSignedPrimeNatIndex]
      congr 1
      omega

/-- Exact approximation numbers: each positive Xi ordinate contributes both signs. -/
theorem xiOrderedSignedPrimeOperator_approxNumber (n : ℕ) :
    approxNumber xiOrderedSignedPrimeOperator n =
      xiOrderedSignedApproxNumber n := by
  let hbound : ∀ i, ‖xiOrderedSignedPrimeMultiplier i‖ ≤
      xiOrderedSignedApproxNumber 0 :=
    fun i => (norm_xiOrderedSignedPrimeMultiplier i).trans_le
      (xiOrderedSignedApproxNumber_antitone (Nat.zero_le _))
  have hop : xiOrderedSignedPrimeOperator =
      HTGeometry.ellTwoDiagonal xiOrderedSignedPrimeMultiplier hbound := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    funext i
    rw [xiOrderedSignedPrimeOperator, HTGeometry.ellTwoDiagonal_apply,
      HTGeometry.ellTwoDiagonal_apply]
  rw [hop]
  simpa [hbound] using HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq
      routeKSignedPrimeEquiv norm_xiOrderedSignedPrimeMultiplier
      (fun n => (xiOrderedSignedApproxNumber_pos n).le)
      (fun {_ _} h => xiOrderedSignedApproxNumber_antitone h) n

theorem xiOrderedSignedPrimeOperator_approxNumber_even (n : ℕ) :
    approxNumber xiOrderedSignedPrimeOperator (2 * n) =
      (xiOrderedPositiveOrdinate n)⁻¹ := by
  rw [xiOrderedSignedPrimeOperator_approxNumber]
  simp [xiOrderedSignedApproxNumber]

theorem xiOrderedSignedPrimeOperator_approxNumber_odd (n : ℕ) :
    approxNumber xiOrderedSignedPrimeOperator (2 * n + 1) =
      (xiOrderedPositiveOrdinate n)⁻¹ := by
  rw [xiOrderedSignedPrimeOperator_approxNumber]
  simp [xiOrderedSignedApproxNumber]
  congr 1
  omega

end

end RHTower
