import GaloisForLFunctions.RHTower.PinnedAffinePrimeJetRigidity
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# The actual Adams action on a local divisor jet

For the Euler coordinate `x_p(s) = p^(-s)`, the `n`-th Adams operation is
`x_p(s) ↦ x_p(s)^n = x_{p^n}(s)`.  Around `s = rho + X` this scales the analytic
coordinate by `X ↦ n X`; it does not ramify it by `X ↦ X^n`.  The first theorem
records this exact coefficient law on the prime derivative jets already used by the
pinned-affine boundary.

The dilation has eigenvalues `1,n,...,n^(m-1)` on an order-`m` jet.  Consequently:

* its diagonal determinant is `n^(m(m-1)/2)`, a precise multiplicity character;
* it is reversible for every `m`, so reversibility alone contains no simplicity;
* if these eigenvalues arise in a single pure weight (equivalently, have one common
  norm), then `m = 1` for `n ≥ 2`.

The final theorem closes this pure-local-Adams condition against the independently
supplied first RH ladder rung.  This file proves the local/source algebra and the RH
consumer.  It does not assert the missing source-derived purity comparison.
-/

namespace RHTower

open Polynomial Complex

noncomputable section

/-- Natural powers of a positive Euler exponential are evaluation at the power base. -/
private theorem natCast_cpow_neg_pow_adams (p : ℕ) (hp : 1 ≤ p) (rho : ℂ) (n : ℕ) :
    ((p : ℂ) ^ (-rho)) ^ n = ((p ^ n : ℕ) : ℂ) ^ (-rho) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast (show (0 : ℕ) < p from hp).ne'
  have hpn0 : ((p ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero n (show p ≠ 0 by omega))
  have hlogp : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (p : ℝ)), Complex.ofReal_natCast]
  have hlogpn : Complex.log ((p ^ n : ℕ) : ℂ) = (n : ℂ) * Complex.log (p : ℂ) := by
    have h1 : Complex.log ((p ^ n : ℕ) : ℂ) =
        ((Real.log ((p ^ n : ℕ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_log (by positivity), Complex.ofReal_natCast]
    rw [h1, hlogp, show ((p ^ n : ℕ) : ℝ) = (p : ℝ) ^ n by push_cast; ring,
      Real.log_pow]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hpn0, hlogpn,
    ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Source-correct Adams law.**  Passing from the Euler base `p` to `p^n` multiplies the
`j`-th analytic jet direction by `n^j`, together with the unavoidable base-value amplitude.
Thus the local coordinate action is the dilation `X ↦ nX`, not `X ↦ X^n`. -/
theorem primeDerivativeJet_primePower_coeff
    (k p n : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) (rho : ℂ) (j : Fin k) :
    (primeDerivativeJet k (p ^ n) rho).coeff (j : ℕ) =
      ((p : ℂ) ^ (-rho)) ^ (n - 1) * (n : ℂ) ^ (j : ℕ) *
        (primeDerivativeJet k p rho).coeff (j : ℕ) := by
  rw [primeDerivativeJet_coeff, primeDerivativeJet_coeff]
  rw [← natCast_cpow_neg_pow_adams p hp rho n]
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  have hpow : ((p : ℂ) ^ (-rho)) ^ n =
      ((p : ℂ) ^ (-rho)) ^ (n - 1) * ((p : ℂ) ^ (-rho)) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  ring

/-- The base-amplitude-free logarithmic jet coordinate.  This is the part of a prime
derivative coefficient on which the Euler power map acts by its actual cotangent weight. -/
def normalizedPrimeDerivativeJetCoeff (p j : ℕ) : ℂ :=
  (-(Real.log p : ℂ)) ^ j

/-- **Normalized Adams eigenlaw.**  Pulling a logarithmic jet coordinate back along
`p ↦ p^n` multiplies its `j`-th component by `n^j`.  Unlike
`primeDerivativeJet_primePower_coeff`, no value-amplitude remains. -/
theorem normalizedPrimeDerivativeJetCoeff_primePower
    (p n j : ℕ) :
    normalizedPrimeDerivativeJetCoeff (p ^ n) j =
      (n : ℂ) ^ j * normalizedPrimeDerivativeJetCoeff p j := by
  rw [normalizedPrimeDerivativeJetCoeff, normalizedPrimeDerivativeJetCoeff]
  rw [show ((p ^ n : ℕ) : ℝ) = (p : ℝ) ^ n by push_cast; ring, Real.log_pow]
  push_cast
  rw [← mul_neg, mul_pow]

/-- Every normalized jet coordinate at a genuine Euler base is nonzero. -/
theorem normalizedPrimeDerivativeJetCoeff_ne_zero
    {p j : ℕ} (hp : 2 ≤ p) :
    normalizedPrimeDerivativeJetCoeff p j ≠ 0 := by
  apply pow_ne_zero
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.log_pos (by exact_mod_cast hp))))

/-- **Positive obstruction.**  Every positive logarithmic jet direction grows strictly under
each nontrivial Euler power map.  Thus the raw normalized packet cannot already be a nonzero
eigenpacket in a contractive Hilbert realization. -/
theorem normalizedPrimeDerivativeJetCoeff_primePower_norm_gt
    {p n j : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n) (hj : 0 < j) :
    ‖normalizedPrimeDerivativeJetCoeff p j‖ <
      ‖normalizedPrimeDerivativeJetCoeff (p ^ n) j‖ := by
  rw [normalizedPrimeDerivativeJetCoeff_primePower, norm_mul]
  have hweight : (1 : ℝ) < ‖(n : ℂ) ^ j‖ := by
    simpa using one_lt_pow₀ (show (1 : ℝ) < n by exact_mod_cast hn)
      (Nat.ne_of_gt hj)
  have hpacket : 0 < ‖normalizedPrimeDerivativeJetCoeff p j‖ :=
    norm_pos_iff.mpr (normalizedPrimeDerivativeJetCoeff_ne_zero hp)
  nlinarith

/-- Product of the diagonal Adams-dilation eigenvalues on the order-`m` jet. -/
def adamsDilationDeterminant (m n : ℕ) : ℂ :=
  ∏ j : Fin m, (n : ℂ) ^ (j : ℕ)

/-- The dilation determinant remembers the triangular multiplicity exponent. -/
theorem adamsDilationDeterminant_eq (m n : ℕ) :
    adamsDilationDeterminant m n = (n : ℂ) ^ (m * (m - 1) / 2) := by
  have hsum : (∑ j : Fin m, (j : ℕ)) = m * (m - 1) / 2 := by
    rw [Finset.sum_fin_eq_sum_range]
    convert Finset.sum_range_id m using 1
    apply Finset.sum_congr rfl
    intro x hx
    simp [Finset.mem_range.mp hx]
  rw [adamsDilationDeterminant, Finset.prod_pow_eq_pow_sum]
  rw [hsum]

/-- **Local purity detects reducedness.**  If all Adams-dilation eigenvalues on a positive
order jet have one common norm, a genuine dilation factor `n ≥ 2` leaves room only for the
constant direction, hence the jet has length one. -/
theorem adamsDilation_sameWeight_forces_simple
    {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n)
    (hpure : ∃ r : ℝ, ∀ j : Fin m, ‖((n : ℂ) ^ (j : ℕ))‖ = r) :
    m = 1 := by
  by_contra hne
  have hm2 : 2 ≤ m := by omega
  obtain ⟨r, hr⟩ := hpure
  let j0 : Fin m := ⟨0, hm⟩
  let j1 : Fin m := ⟨1, hm2⟩
  have h0 := hr j0
  have h1 := hr j1
  norm_num [j0] at h0
  simp [j1] at h1
  have hnreal : (n : ℝ) = 1 := by linarith
  have hn1 : n = 1 := by exact_mod_cast hnreal
  omega

/-- **Pure local Adams route to RH.**  The pure-weight condition makes every hypothetical
right-half zero simple.  The first ladder rung makes the same order even, giving the contradiction. -/
theorem riemannHypothesis_of_rhLadder_one_of_rightAdamsDilationPure
    (hladder : RHLadder 1)
    (hpure : ∀ rho ∈ rightHalf, xi rho = 0 →
      ∃ n : ℕ, 2 ≤ n ∧
        ∃ r : ℝ, ∀ j : Fin (analyticOrderAt xi rho).toNat,
          ‖((n : ℂ) ^ (j : ℕ))‖ = r) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨n, hn, hpure_rho⟩ := hpure rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    adamsDilation_sameWeight_forces_simple hmpos hn hpure_rho
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hladder rho hrho hzero
  rw [hmone] at heven
  exact Nat.not_even_one heven

end

end RHTower
