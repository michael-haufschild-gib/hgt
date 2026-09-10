import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalLogarithm

/-!
# A finite logarithm recovers every actual Fock translation parameter

No convergence or branch choice occurs: the Taylor increment is nilpotent and
formal substitution truncates exactly at the jet dimension.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The logarithm polynomial at the actual finite clock horizon. -/
def gomesFiniteFockLogarithmPolynomial (N : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc N (PowerSeries.log ℂ)

/-- Every exponential increment lies in the based formal-symbol ideal, even at parameter zero. -/
def gomesFiniteFockExponentialIncrement (z : ℂ) : GomesBasedFormalSeries :=
  ⟨PowerSeries.rescale z (PowerSeries.exp ℂ) - 1,
    gomesFiniteFockExponentialIncrement_constantCoeff z⟩

/-- The exact finite logarithm of a Taylor matrix is its parameter times the original clock. -/
theorem gomesFiniteFock_singleTaylor_logarithm (N : ℕ) (z : ℂ) :
    Polynomial.aeval (fockTaylorMatrix N z - 1) (gomesFiniteFockLogarithmPolynomial N) =
      z • fockShiftMatrix N := by
  have h := gomesFiniteFockFormalHom_subst N (PowerSeries.log ℂ)
    (gomesFiniteFockExponentialIncrement z)
  change gomesFiniteFockFormalHom N
      ((PowerSeries.log ℂ).subst (PowerSeries.rescale z (PowerSeries.exp ℂ) - 1)) =
    Polynomial.aeval (gomesFiniteFockFormalHom N
      (PowerSeries.rescale z (PowerSeries.exp ℂ) - 1))
      (PowerSeries.trunc N (PowerSeries.log ℂ)) at h
  rw [← PowerSeries.logOf_eq, gomesFormalSeries_logOf_rescale_exp, map_smul,
    gomesFiniteFockFormalHom_X, map_sub, map_one, gomesFiniteFockFormalHom_exp] at h
  exact h.symm

/-- The explicit terminating logarithm series recovers the actual translation generator in every dimension. -/
theorem gomesFiniteFock_singleTaylor_logarithm_sum (N : ℕ) (z : ℂ) :
    (∑ k ∈ Finset.range N, ((-1 : ℂ) ^ (k + 1) / (k : ℂ)) •
      (fockTaylorMatrix N z - 1) ^ k) = z • fockShiftMatrix N := by
  have h := gomesFiniteFock_singleTaylor_logarithm N z
  rw [gomesFiniteFockLogarithmPolynomial, Polynomial.aeval_def,
    PowerSeries.eval₂_trunc_eq_sum_range] at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro k _
  have hc : PowerSeries.coeff k (PowerSeries.log ℂ) =
      (-1 : ℂ) ^ (k + 1) / (k : ℂ) := by
    rw [PowerSeries.coeff_log]
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  rw [hc, Algebra.smul_def]

/-- The finite logarithm is additive on the actual Taylor family, for every pair of parameters. -/
theorem gomesFiniteFock_singleTaylor_logarithm_add (N : ℕ) (z w : ℂ) :
    Polynomial.aeval (fockTaylorMatrix N (z + w) - 1) (gomesFiniteFockLogarithmPolynomial N) =
      Polynomial.aeval (fockTaylorMatrix N z - 1) (gomesFiniteFockLogarithmPolynomial N) +
      Polynomial.aeval (fockTaylorMatrix N w - 1) (gomesFiniteFockLogarithmPolynomial N) := by
  simp only [gomesFiniteFock_singleTaylor_logarithm, add_smul]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
