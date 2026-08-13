import GaloisForLFunctions.RHTower.Sieve.MaynardAdditiveEnergy
import GaloisForLFunctions.RHTower.Sieve.MaynardRouteTSecondAlternativeBarrier

/-!
# Diagonal-energy transfer from Maynard's third alternative

The sign barrier for Maynard's second alternative is also the exact point where the diagonal
inequality `R^2 ≤ R*` converts the third alternative into the first.  Thus the two count mechanisms
meet without an exponent gap: below the barrier one needs the genuine second/fourth-moment
large-values analysis, while above it every third-alternative estimate is already a first-
alternative estimate.
-/

noncomputable section

namespace RHTower.Sieve

/-- Scalar diagonal-energy transfer.  The scale condition is exactly what is needed to turn
`R* ≤ T x^(3+nu-4 sigma)` into `R ≤ x^(1-sigma)`. -/
theorem maynard_first_alternative_of_rstar
    {R Rstar T x sigma nu : ℝ}
    (hx : 1 ≤ x)
    (hdiag : R ^ 2 ≤ Rstar)
    (hRstar : Rstar ≤ T * x ^ (3 + nu - 4 * sigma))
    (hfit : T ≤ x ^ (2 * sigma - 1 - nu)) :
    R ≤ x ^ (1 - sigma) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hfactor0 : 0 ≤ x ^ (3 + nu - 4 * sigma) := Real.rpow_nonneg hx0 _
  have hscale := mul_le_mul_of_nonneg_right hfit hfactor0
  have hsq : R ^ 2 ≤ (x ^ (1 - sigma)) ^ 2 := by
    calc
      R ^ 2 ≤ Rstar := hdiag
      _ ≤ T * x ^ (3 + nu - 4 * sigma) := hRstar
      _ ≤ x ^ (2 * sigma - 1 - nu) * x ^ (3 + nu - 4 * sigma) := hscale
      _ = x ^ ((2 * sigma - 1 - nu) + (3 + nu - 4 * sigma)) := by
        rw [Real.rpow_add hxpos]
      _ = x ^ (2 - 2 * sigma) := by congr 1; ring
      _ = (x ^ (1 - sigma)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
        norm_num
        ring_nf
  exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hx0 _) hsq

/-- The amplitude inequality defining the count/energy transition is precisely the scale condition
used by `maynard_first_alternative_of_rstar`. -/
theorem maynard_rstar_scale_fit
    {T x mu sigma nu : ℝ}
    (hT : 1 ≤ T) (hmu : 0 < mu) (hx : x = T ^ mu)
    (hsigma : (1 + nu) / 2 + 1 / (2 * mu) ≤ sigma) :
    T ≤ x ^ (2 * sigma - 1 - nu) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hexponent : 1 ≤ mu * (2 * sigma - 1 - nu) := by
    have hmupos : 0 < 2 * mu := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hsigma hmupos.le
    have hinv : (2 * mu) * (1 / (2 * mu)) = 1 := by
      field_simp
    rw [mul_add, hinv] at hscaled
    nlinarith
  calc
    T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
    _ ≤ T ^ (mu * (2 * sigma - 1 - nu)) :=
      Real.rpow_le_rpow_of_exponent_le hT hexponent
    _ = (T ^ mu) ^ (2 * sigma - 1 - nu) := by
      rw [Real.rpow_mul hT0]
    _ = x ^ (2 * sigma - 1 - nu) := by rw [hx]

/-- Finite-set form using the exact diagonal family in Maynard's additive energy. -/
theorem card_le_maynard_first_alternative_of_rstar
    (S : Finset ℤ) {T x mu sigma nu : ℝ}
    (hT : 1 ≤ T) (hmu : 0 < mu) (hx : x = T ^ mu) (hx1 : 1 ≤ x)
    (hsigma : (1 + nu) / 2 + 1 / (2 * mu) ≤ sigma)
    (hRstar : (maynardRStar S : ℝ) ≤
      T * x ^ (3 + nu - 4 * sigma)) :
    (S.card : ℝ) ≤ x ^ (1 - sigma) := by
  have hdiag : ((S.card : ℝ)) ^ 2 ≤ (maynardRStar S : ℝ) := by
    exact_mod_cast card_sq_le_maynardRStar S
  exact maynard_first_alternative_of_rstar hx1 hdiag hRstar
    (maynard_rstar_scale_fit hT hmu hx hsigma)

/-- At the longest Route-T receiver scale, `75/76` is enough for every `nu ≤ 1/2`. -/
theorem card_le_maynard_first_alternative_of_rstar_routeT_barrier
    (S : Finset ℤ) {T x sigma nu : ℝ}
    (hT : 1 ≤ T) (hx : x = T ^ (19 / 9 : ℝ)) (hx1 : 1 ≤ x)
    (hnu : nu ≤ 1 / 2)
    (hsigma : routeTSecondAlternativeBarrier ≤ sigma)
    (hRstar : (maynardRStar S : ℝ) ≤
      T * x ^ (3 + nu - 4 * sigma)) :
    (S.card : ℝ) ≤ x ^ (1 - sigma) := by
  have hthreshold :
      (1 + nu) / 2 + 1 / (2 * (19 / 9 : ℝ)) ≤ sigma := by
    dsimp only [routeTSecondAlternativeBarrier] at hsigma
    norm_num at hnu ⊢
    linarith
  exact card_le_maynard_first_alternative_of_rstar S hT (by norm_num) hx hx1
    hthreshold hRstar

end RHTower.Sieve
