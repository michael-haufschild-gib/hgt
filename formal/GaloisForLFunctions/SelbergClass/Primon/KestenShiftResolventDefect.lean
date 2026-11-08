import GaloisForLFunctions.SelbergClass.Primon.KestenGreenBoundaryFactorization

/-!
# The rank-one self-commutator of the prime shift resolvent

Comparing the two Green factorizations gives
`F* F - F F* = q²/(1-q²) |W_p⟩⟨W_p|`. Thus the geometric shift inverse
is hyponormal, with its exact norm imbalance measured by one likelihood
coefficient.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem gap_pos (p : Nat.Primes) : 0 < 1 - primeReciprocal p ^ 2 :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))

/-- The self-commutator of the geometric shift inverse is exactly one positive likelihood direction. -/
theorem kestenShiftResolvent_self_commutator (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    kestenGeometricCovariance p f -
      kestenShiftResolvent p ((kestenShiftResolvent p).adjoint f) =
        (primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) * inner ℝ (kestenPrimeState p) f) •
          kestenPrimeState p := by
  have h₁ := eq_sub_iff_add_eq.mp (kestenGreenOperator_boundary_correction p f)
  have h₂ := eq_sub_iff_add_eq.mp (kestenGreenOperator_causal_correction p f)
  have h : primeReciprocal p • (kestenGeometricCovariance p f -
      kestenShiftResolvent p ((kestenShiftResolvent p).adjoint f)) =
        ((primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) -
          primeReciprocal p ^ 2 / (1 + primeReciprocal p)) *
            inner ℝ (kestenPrimeState p) f) • kestenPrimeState p := by
    rw [smul_sub, ← h₁, ← h₂]
    module
  have hq : primeReciprocal p ≠ 0 := (primeReciprocal_pos p).ne'
  have hq1 : 1 + primeReciprocal p ≠ 0 := by have := primeReciprocal_pos p; positivity
  have hc : (primeReciprocal p)⁻¹ *
      (primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) -
        primeReciprocal p ^ 2 / (1 + primeReciprocal p)) =
          primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) := by
    field_simp [hq, hq1, (gap_pos p).ne']
    ring
  have hh := congrArg (fun g : KestenLikelihoodHilbert => (primeReciprocal p)⁻¹ • g) h
  simpa only [smul_smul, inv_mul_cancel₀ hq, one_smul, ← mul_assoc, hc] using hh

/-- The exact norm imbalance is a nonnegative square of one likelihood readout. -/
theorem norm_sq_kestenShiftResolvent_sub_adjoint (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    ‖kestenShiftResolvent p f‖ ^ 2 - ‖(kestenShiftResolvent p).adjoint f‖ ^ 2 =
      primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) * (inner ℝ (kestenPrimeState p) f) ^ 2 := by
  have h := congrArg (fun g : KestenLikelihoodHilbert => inner ℝ f g)
    (kestenShiftResolvent_self_commutator p f)
  rw [inner_sub_right, inner_kestenGeometricCovariance_self,
    ← ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    _root_.inner_smul_right (𝕜 := ℝ) f (kestenPrimeState p)
      (primeReciprocal p ^ 2 / (1 - primeReciprocal p ^ 2) * inner ℝ (kestenPrimeState p) f),
    real_inner_comm (kestenPrimeState p) f] at h
  simpa only [pow_two, mul_assoc] using h

/-- The geometric shift inverse is hyponormal: its adjoint cannot enlarge any source more than it does. -/
theorem norm_kestenShiftResolvent_adjoint_le (p : Nat.Primes) (f : KestenLikelihoodHilbert) :
    ‖(kestenShiftResolvent p).adjoint f‖ ≤ ‖kestenShiftResolvent p f‖ := by
  have h := norm_sq_kestenShiftResolvent_sub_adjoint p f
  have hp := mul_nonneg (div_nonneg (sq_nonneg (primeReciprocal p)) (gap_pos p).le)
    (sq_nonneg (inner ℝ (kestenPrimeState p) f))
  nlinarith only [h, hp, norm_nonneg ((kestenShiftResolvent p).adjoint f),
    norm_nonneg (kestenShiftResolvent p f)]

end
end GaloisForLFunctions.SelbergClass.Primon
