import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Gamma-conductor Schur capacity

The normalized Gamma cyclic characteristic has a source-defined covariance between a prime
Fourier mode and the centered second spectral moment.  If distinct prime modes are resolved as
independent diagonal channels and coupled to one scalar conductor coordinate, positivity of the
resulting quadratic form forces the conductor coordinate to pay a Schur cost for every prime.

The cost is unchanged by nonzero diagonal damping and is bounded below by `9 / (512 * p)`.
Consequently the required scalar conductor capacity is unbounded over finite prime sets.
-/

noncomputable section

namespace RHTower

open Filter Topology

/-- Variance of the prime-log Fourier mode in the normalized Gamma cyclic measure. -/
def gammaConductorPrimeVariance (p : Nat.Primes) : ℝ :=
  1 - semilocalArchimedeanCharacteristic (Real.log (p : ℝ)) ^ 2

/-- Covariance of the prime-log Fourier mode with the centered second spectral moment. -/
def gammaConductorPrimeCross (p : Nat.Primes) : ℝ :=
  semilocalArchimedeanSecondMomentCovarianceKernel (Real.log (p : ℝ))

/-- The scalar Schur-complement cost of one prime channel. -/
def gammaConductorPrimeSchurCost (p : Nat.Primes) : ℝ :=
  gammaConductorPrimeCross p ^ 2 / gammaConductorPrimeVariance p

/-- The square of the Gamma cyclic characteristic is the reciprocal hyperbolic cosine. -/
lemma semilocalArchimedeanCharacteristic_sq (t : ℝ) :
    semilocalArchimedeanCharacteristic t ^ 2 = (Real.cosh t)⁻¹ := by
  rw [semilocalArchimedeanCharacteristic]
  rw [← Real.rpow_mul_natCast (Real.cosh_pos t).le]
  norm_num [Real.rpow_neg_one]

/-- Exact Gamma characteristic at a prime logarithm. -/
lemma semilocalArchimedeanCharacteristic_log_prime_sq (p : Nat.Primes) :
    semilocalArchimedeanCharacteristic (Real.log (p : ℝ)) ^ 2 =
      2 * (p : ℝ) / ((p : ℝ) ^ 2 + 1) := by
  have hp0' : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp0 : (p : ℝ) ≠ 0 := hp0'.ne'
  rw [semilocalArchimedeanCharacteristic_sq, Real.cosh_log hp0']
  field_simp

/-- Exact hyperbolic tangent at a prime logarithm. -/
lemma tanh_log_prime (p : Nat.Primes) :
    Real.tanh (Real.log (p : ℝ)) =
      ((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ 2 + 1) := by
  have hp0' : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp0 : (p : ℝ) ≠ 0 := hp0'.ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_log hp0', Real.cosh_log hp0']
  field_simp

/-- Exact prime-mode variance. -/
lemma gammaConductorPrimeVariance_eq (p : Nat.Primes) :
    gammaConductorPrimeVariance p =
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) ^ 2 + 1) := by
  rw [gammaConductorPrimeVariance, semilocalArchimedeanCharacteristic_log_prime_sq]
  have hden : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The prime-mode variance is strictly positive. -/
lemma gammaConductorPrimeVariance_pos (p : Nat.Primes) :
    0 < gammaConductorPrimeVariance p := by
  rw [gammaConductorPrimeVariance_eq]
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  positivity

/-- Exact square of the prime-to-conductor covariance. -/
lemma gammaConductorPrimeCross_sq_eq (p : Nat.Primes) :
    gammaConductorPrimeCross p ^ 2 =
      (9 / 8 : ℝ) * (p : ℝ) * ((p : ℝ) ^ 2 - 1) ^ 4 /
        ((p : ℝ) ^ 2 + 1) ^ 5 := by
  rw [gammaConductorPrimeCross, semilocalArchimedeanSecondMomentCovarianceKernel]
  rw [mul_pow, mul_pow, semilocalArchimedeanCharacteristic_log_prime_sq,
    tanh_log_prime]
  field_simp
  ring

/-- Exact rational expression for the one-prime Schur cost. -/
lemma gammaConductorPrimeSchurCost_eq (p : Nat.Primes) :
    gammaConductorPrimeSchurCost p =
      (9 / 8 : ℝ) * (p : ℝ) * ((p : ℝ) - 1) ^ 2 * ((p : ℝ) + 1) ^ 4 /
        ((p : ℝ) ^ 2 + 1) ^ 4 := by
  rw [gammaConductorPrimeSchurCost, gammaConductorPrimeCross_sq_eq,
    gammaConductorPrimeVariance_eq]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast p.prop.ne_one)
  have hden : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  rw [show ((p : ℝ) ^ 2 - 1) = ((p : ℝ) - 1) * ((p : ℝ) + 1) by ring]
  field_simp

/-- The real rational profile whose prime samples are the one-prime Gamma Schur costs. -/
def gammaConductorSchurProfile (x : ℝ) : ℝ :=
  (9 / 8 : ℝ) * x * (x - 1) ^ 2 * (x + 1) ^ 4 / (x ^ 2 + 1) ^ 4

/-- The exact Schur cost is the rational profile evaluated at the prime. -/
lemma gammaConductorPrimeSchurCost_eq_profile (p : Nat.Primes) :
    gammaConductorPrimeSchurCost p = gammaConductorSchurProfile (p : ℝ) := by
  rw [gammaConductorPrimeSchurCost_eq]
  rfl

/-- **Sharp Gamma Schur-cost coefficient.**  The rational conductor cost has leading value
`9/(8x)`: multiplying by `x` tends exactly to `9/8`. -/
theorem gammaConductorSchurProfile_leading :
    Tendsto (fun x : ℝ => x * gammaConductorSchurProfile x) atTop (nhds (9 / 8 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hminus : Tendsto (fun x : ℝ => 1 - x⁻¹) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  have hplus : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hinv
  have hden : Tendsto (fun x : ℝ => (1 + x⁻¹ ^ 2) ^ 4) atTop
      (nhds ((1 + 0 ^ 2) ^ 4)) :=
    (tendsto_const_nhds.add (hinv.pow 2)).pow 4
  have hnorm : Tendsto
      (fun x : ℝ => (9 / 8 : ℝ) * (1 - x⁻¹) ^ 2 * (1 + x⁻¹) ^ 4 /
        (1 + x⁻¹ ^ 2) ^ 4) atTop (nhds (9 / 8 : ℝ)) := by
    have h := (((hminus.pow 2).mul (hplus.pow 4)).const_mul (9 / 8 : ℝ)).div hden
      (by norm_num)
    norm_num at h ⊢
    simpa [Pi.div_apply, mul_assoc] using h
  refine hnorm.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  rw [gammaConductorSchurProfile]
  field_simp [hx]

/-- Along the prime values, `p * R_p` tends to the sharp coefficient `9/8`. -/
theorem gammaConductorPrimeSchurCost_leading :
    Tendsto (fun p : Nat.Primes => (p : ℝ) * gammaConductorPrimeSchurCost p)
      cofinite (nhds (9 / 8 : ℝ)) := by
  have h := gammaConductorSchurProfile_leading.comp tendsto_prime_coe_real_cofinite_atTop
  simpa [gammaConductorPrimeSchurCost_eq_profile] using h

/-- Each prime consumes at least `9 / (512 * p)` units of scalar conductor capacity. -/
lemma gammaConductorPrimeSchurCost_lower (p : Nat.Primes) :
    (9 / 512 : ℝ) * (p : ℝ)⁻¹ ≤ gammaConductorPrimeSchurCost p := by
  rw [gammaConductorPrimeSchurCost_eq]
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hp0 : 0 < (p : ℝ) := by positivity
  have h1 : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
  have h2 : (p : ℝ) ≤ (p : ℝ) + 1 := by linarith
  have h3 : (p : ℝ) ^ 2 + 1 ≤ 2 * (p : ℝ) ^ 2 := by nlinarith
  have hdenpos : 0 < ((p : ℝ) ^ 2 + 1) ^ 4 := by positivity
  rw [le_div_iff₀ hdenpos]
  calc
    (9 / 512 : ℝ) * (p : ℝ)⁻¹ * ((p : ℝ) ^ 2 + 1) ^ 4
        ≤ (9 / 512 : ℝ) * (p : ℝ)⁻¹ * (2 * (p : ℝ) ^ 2) ^ 4 := by
          gcongr
    _ = (9 / 32 : ℝ) * (p : ℝ) ^ 7 := by
      field_simp
      ring
    _ ≤ (9 / 8 : ℝ) * (p : ℝ) * ((p : ℝ) - 1) ^ 2 * ((p : ℝ) + 1) ^ 4 := by
      have h1sq : ((p : ℝ) / 2) ^ 2 ≤ ((p : ℝ) - 1) ^ 2 := by gcongr
      have h2four : (p : ℝ) ^ 4 ≤ ((p : ℝ) + 1) ^ 4 := by gcongr
      have hmul : ((p : ℝ) / 2) ^ 2 * (p : ℝ) ^ 4 ≤
          ((p : ℝ) - 1) ^ 2 * ((p : ℝ) + 1) ^ 4 := by
        exact mul_le_mul h1sq h2four (by positivity) (by positivity)
      nlinarith

/-- The scalar Gamma-conductor Schur costs are not summable over the primes. -/
theorem not_summable_gammaConductorPrimeSchurCost :
    ¬ Summable gammaConductorPrimeSchurCost := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes => (9 / 512 : ℝ) * (p : ℝ)⁻¹) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · exact gammaConductorPrimeSchurCost_lower
    · exact hsum
  have hinv : Summable (fun p : Nat.Primes => (p : ℝ)⁻¹) :=
    (summable_mul_left_iff (by norm_num : (9 / 512 : ℝ) ≠ 0)).mp hscaled
  apply Nat.Primes.not_summable_one_div
  simpa [one_div] using hinv

/-- The one-prime Schur cost is nonnegative. -/
lemma gammaConductorPrimeSchurCost_nonneg (p : Nat.Primes) :
    0 ≤ gammaConductorPrimeSchurCost p := by
  exact (by positivity : 0 ≤ (9 / 512 : ℝ) * (p : ℝ)⁻¹) |>.trans
    (gammaConductorPrimeSchurCost_lower p)

/-- Cofinal form of divergence: every proposed finite scalar capacity is exceeded by a finite
prime packet. -/
theorem exists_finset_gammaConductorPrimeSchurCost_gt (B : ℝ) :
    ∃ F : Finset Nat.Primes, B < ∑ p ∈ F, gammaConductorPrimeSchurCost p := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply not_summable_gammaConductorPrimeSchurCost
  exact summable_of_sum_le gammaConductorPrimeSchurCost_nonneg h

/-- Nonzero diagonal damping cancels exactly from the one-prime Schur cost. -/
theorem gammaConductorDampedPrimeSchurCost_eq
    (p : Nat.Primes) {d : ℝ} (hd : d ≠ 0) :
    (d * gammaConductorPrimeCross p) ^ 2 /
        (d ^ 2 * gammaConductorPrimeVariance p) =
      gammaConductorPrimeSchurCost p := by
  rw [gammaConductorPrimeSchurCost]
  have hvar : gammaConductorPrimeVariance p ≠ 0 :=
    (gammaConductorPrimeVariance_pos p).ne'
  field_simp

/-- Abstract scalar Schur-complement capacity theorem, proved directly from nonnegativity of the
quadratic form. -/
theorem scalarConductorCapacity_of_quadratic_nonneg
    {ι : Type*} [Fintype ι] (A c : ι → ℝ) (B : ℝ)
    (hA : ∀ i, 0 < A i)
    (hquad : ∀ (x : ι → ℝ) (y : ℝ),
      0 ≤ ∑ i, A i * (x i) ^ 2 + 2 * y * ∑ i, c i * x i + B * y ^ 2) :
    ∑ i, (c i) ^ 2 / A i ≤ B := by
  have h := hquad (fun i => -(c i) / A i) 1
  have hpoint (i : ι) :
      A i * (-(c i) / A i) ^ 2 + 2 * (c i * (-(c i) / A i)) =
        -((c i) ^ 2 / A i) := by
    have hne : A i ≠ 0 := (hA i).ne'
    field_simp
    ring
  have hsum :
      (∑ i, A i * (-(c i) / A i) ^ 2) +
          2 * ∑ i, c i * (-(c i) / A i) =
        -(∑ i, (c i) ^ 2 / A i) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ i, (A i * (-(c i) / A i) ^ 2 + 2 * (c i * (-(c i) / A i))) =
          ∑ i, -((c i) ^ 2 / A i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hpoint i
      _ = -(∑ i, (c i) ^ 2 / A i) := by simp
  norm_num at h
  rw [hsum] at h
  linarith

/-- A positive independently resolved prime--Gamma block must allocate at least the sum of all
one-prime Schur costs.  The conclusion is independent of the positive diagonal damping. -/
theorem gammaConductorFiniteCapacity_of_quadratic_nonneg
    {ι : Type*} [Fintype ι] (p : ι → Nat.Primes) (d : ι → ℝ) (B : ℝ)
    (hd : ∀ i, 0 < d i)
    (hquad : ∀ (x : ι → ℝ) (y : ℝ),
      0 ≤ ∑ i, (d i) ^ 2 * gammaConductorPrimeVariance (p i) * (x i) ^ 2 +
        2 * y * ∑ i, d i * gammaConductorPrimeCross (p i) * x i + B * y ^ 2) :
    ∑ i, gammaConductorPrimeSchurCost (p i) ≤ B := by
  have hcapacity := scalarConductorCapacity_of_quadratic_nonneg
    (fun i => (d i) ^ 2 * gammaConductorPrimeVariance (p i))
    (fun i => d i * gammaConductorPrimeCross (p i)) B
    (fun i => mul_pos (sq_pos_of_pos (hd i)) (gammaConductorPrimeVariance_pos (p i))) hquad
  convert hcapacity using 1
  apply Finset.sum_congr rfl
  intro i _
  exact (gammaConductorDampedPrimeSchurCost_eq (p i) (hd i).ne').symm

/-- A positive block with fixed scalar conductor capacity forces coherent energy in its normalized
prime covariance.  This is the positive alternative to diagonal scalarization: if
`S = ∑ i, u i ^ 2`, the covariance energy in the direction `u` is at least `S ^ 2 / B`. -/
theorem coherentCovarianceEnergy_lower_of_quadratic_nonneg
    {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (u : ι → ℝ) (B : ℝ)
    (hB : 0 < B)
    (hquad : ∀ (x : ι → ℝ) (y : ℝ),
      0 ≤ (∑ i, ∑ j, K i j * x i * x j) +
        2 * y * (∑ i, u i * x i) + B * y ^ 2) :
    (∑ i, u i ^ 2) ^ 2 / B ≤ ∑ i, ∑ j, K i j * u i * u j := by
  let S : ℝ := ∑ i, u i ^ 2
  have h := hquad u (-S / B)
  have hsum : ∑ i, u i * u i = S := by
    dsimp [S]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at h
  rw [div_le_iff₀ hB]
  field_simp at h
  nlinarith

/-- The prime-to-conductor covariance normalized by the square root of the prime variance. -/
def gammaConductorPrimeNormalizedCross (p : Nat.Primes) : ℝ :=
  gammaConductorPrimeCross p / Real.sqrt (gammaConductorPrimeVariance p)

/-- The square of the normalized cross covariance is exactly the one-prime Schur cost. -/
lemma gammaConductorPrimeNormalizedCross_sq (p : Nat.Primes) :
    gammaConductorPrimeNormalizedCross p ^ 2 = gammaConductorPrimeSchurCost p := by
  rw [gammaConductorPrimeNormalizedCross, gammaConductorPrimeSchurCost]
  have hvar : 0 ≤ gammaConductorPrimeVariance p :=
    (gammaConductorPrimeVariance_pos p).le
  rw [div_pow, Real.sq_sqrt hvar]

/-- Any positive normalized prime-covariance/conductor block must carry coherent covariance energy
at least the square of the accumulated Gamma Schur cost divided by the conductor capacity. -/
theorem gammaConductorCoherentCovarianceEnergy_lower
    {ι : Type*} [Fintype ι] (p : ι → Nat.Primes) (K : ι → ι → ℝ) (B : ℝ)
    (hB : 0 < B)
    (hquad : ∀ (x : ι → ℝ) (y : ℝ),
      0 ≤ (∑ i, ∑ j, K i j * x i * x j) +
        2 * y * (∑ i, gammaConductorPrimeNormalizedCross (p i) * x i) +
          B * y ^ 2) :
    (∑ i, gammaConductorPrimeSchurCost (p i)) ^ 2 / B ≤
      ∑ i, ∑ j, K i j * gammaConductorPrimeNormalizedCross (p i) *
        gammaConductorPrimeNormalizedCross (p j) := by
  have h := coherentCovarianceEnergy_lower_of_quadratic_nonneg K
    (fun i => gammaConductorPrimeNormalizedCross (p i)) B hB hquad
  convert h using 1
  apply congrArg (fun z : ℝ => z ^ 2 / B)
  apply Finset.sum_congr rfl
  intro i _
  exact (gammaConductorPrimeNormalizedCross_sq (p i)).symm

/-- If the normalized prime covariance has diagonal one, its off-diagonal coherent energy is at
least `S ^ 2 / B - S`, where `S` is the accumulated Gamma Schur cost.  Since those costs are
nonsummable, fixed conductor capacity forces unbounded coherent off-diagonal covariance. -/
theorem gammaConductorOffDiagonalCovarianceEnergy_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Nat.Primes) (K : ι → ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hdiag : ∀ i, K i i = 1)
    (hquad : ∀ (x : ι → ℝ) (y : ℝ),
      0 ≤ (∑ i, ∑ j, K i j * x i * x j) +
        2 * y * (∑ i, gammaConductorPrimeNormalizedCross (p i) * x i) +
          B * y ^ 2) :
    (∑ i, gammaConductorPrimeSchurCost (p i)) ^ 2 / B -
        ∑ i, gammaConductorPrimeSchurCost (p i) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        K i j * gammaConductorPrimeNormalizedCross (p i) *
          gammaConductorPrimeNormalizedCross (p j) := by
  have h := gammaConductorCoherentCovarianceEnergy_lower p K B hB hquad
  have hsplit :
      (∑ i, ∑ j, K i j * gammaConductorPrimeNormalizedCross (p i) *
          gammaConductorPrimeNormalizedCross (p j)) =
        (∑ i, gammaConductorPrimeSchurCost (p i)) +
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            K i j * gammaConductorPrimeNormalizedCross (p i) *
              gammaConductorPrimeNormalizedCross (p j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [hdiag i, one_mul, ← pow_two, gammaConductorPrimeNormalizedCross_sq]
  rw [hsplit] at h
  exact sub_le_iff_le_add.mpr (by simpa [add_comm] using h)

end RHTower
