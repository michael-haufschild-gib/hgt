import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeParityRamanujanCoordinates
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSimplePrimeEigenlinesConvergeToRamanujanLines

/-!
# Harmonic coordinates of the prime-parity constraint

Normalize the arithmetic modes and the parity constraint by the same harmonic
mass. Their exact inner products are the mixed incidence counts. The existing
Ramanujan norm and residual limits survive this normalization. Spectral
projection then identifies the squared coordinates on the simple prime
eigenlines, without choosing orientations for their eigenvectors.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.BezoutValuationIncidence

/-- The prime-parity constraint, normalized to unit harmonic mass. -/
def primeParityHorizonVector (p N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => finiteFlip {p} n / Real.sqrt n /
    Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))

/-- Ramanujan modes normalized by the same mass as the arithmetic constraint. -/
def harmonicRamanujanHorizonVector (m N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))⁻¹ • ramanujanHorizonVector m N

theorem primeParityHorizonVector_norm_sq (p : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ‖primeParityHorizonVector p N‖ ^ 2 = 1 := by
  have hH := gaugeHarmonicSum_one_pos hN
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2) = 1
  rw [sum_coe_sort (Icc 1 N) (fun n =>
    (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2)]
  have ht (n : ℕ) :
      (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2 =
        1 / (n : ℝ) / gaugeHarmonicSum (fun _ => 1) N := by
    rw [div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt hH.le,
      sq, singleFlip_mul_self]
  rw [sum_congr rfl (fun n _ => ht n), ← sum_div]
  exact div_self hH.ne'

theorem primeParityHorizonVector_norm (p : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ‖primeParityHorizonVector p N‖ = 1 := by
  nlinarith only [primeParityHorizonVector_norm_sq p hN,
    norm_nonneg (primeParityHorizonVector p N)]

theorem tendsto_harmonicMass_div_log :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (fun _ => 1) N / Real.log N)
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := tendsto_harmonicSum_sub_log.div_atTop hlog
  have he : ∀ᶠ N : ℕ in atTop,
      (harmonicSum N - Real.log N) / Real.log N + 1 =
        gaugeHarmonicSum (fun _ => 1) N / Real.log N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    change (gaugeHarmonicSum (fun _ => 1) N - Real.log N) / Real.log N + 1 = _
    field_simp [hl.ne']
    ring
  simpa only [zero_add] using (hlim.add_const 1).congr' he

private theorem tendsto_div_harmonicMass_of_div_log {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun N : ℕ => a N / Real.log N) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => a N / gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 c) := by
  have he : ∀ᶠ N : ℕ in atTop,
      (a N / Real.log N) / (gaugeHarmonicSum (fun _ => 1) N / Real.log N) =
        a N / gaugeHarmonicSum (fun _ => 1) N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hH := gaugeHarmonicSum_one_pos (show 1 ≤ N by omega)
    field_simp [hl.ne', hH.ne']
  simpa only [div_one] using
    (h.div tendsto_harmonicMass_div_log (by norm_num : (1 : ℝ) ≠ 0)).congr' he

theorem harmonicRamanujanHorizonVector_norm_sq (m N : ℕ) :
    ‖harmonicRamanujanHorizonVector m N‖ ^ 2 =
      ‖ramanujanHorizonVector m N‖ ^ 2 / gaugeHarmonicSum (fun _ => 1) N := by
  have hH : 0 ≤ gaugeHarmonicSum (fun _ => 1) N := sum_nonneg fun _ _ => by positivity
  rw [harmonicRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, inv_pow, Real.sq_sqrt hH]
  ring

theorem tendsto_harmonicRamanujanHorizonVector_norm_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖harmonicRamanujanHorizonVector m N‖ ^ 2)
      atTop (𝓝 1) := by
  simpa only [harmonicRamanujanHorizonVector_norm_sq] using
    tendsto_div_harmonicMass_of_div_log (tendsto_ramanujanHorizonVector_norm_sq hm)

/-- Harmonic normalization preserves the actual prime-matrix quasimode residual. -/
theorem tendsto_harmonicRamanujanHorizonVector_residual_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (harmonicRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • harmonicRamanujanHorizonVector m N‖ ^ 2)
      atTop (𝓝 0) := by
  have he (N : ℕ) :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (harmonicRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • harmonicRamanujanHorizonVector m N‖ ^ 2 =
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 /
          gaugeHarmonicSum (fun _ => 1) N := by
    have hH : 0 ≤ gaugeHarmonicSum (fun _ => 1) N := sum_nonneg fun _ _ => by positivity
    simp only [harmonicRamanujanHorizonVector, map_smul]
    rw [smul_comm (Real.log N - ramanujanAdjunctionEnergy m)
        (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))⁻¹,
      ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hH]
    ring
  simpa only [he] using
    tendsto_div_harmonicMass_of_div_log (tendsto_ramanujanHorizonVector_residual_norm_sq hm)

/-- The arithmetic mixed count is an exact inner product on the actual integer horizon. -/
theorem primeParityHorizonVector_inner {m : ℕ} (hm : 0 < m) (p N : ℕ) :
    ⟪primeParityHorizonVector p N, harmonicRamanujanHorizonVector m N⟫ =
      primeParityRamanujanSum p m N / gaugeHarmonicSum (fun _ => 1) N /
        Real.sqrt (m.totient : ℝ) := by
  have hH : 0 ≤ gaugeHarmonicSum (fun _ => 1) N := sum_nonneg fun _ _ => by positivity
  rw [harmonicRamanujanHorizonVector, real_inner_smul_right,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))⁻¹ *
    (∑ n : PrimeHorizonIndex N, ramanujanPoleProfile m n *
      (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile m n *
    (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)))]
  have ht (n : ℕ) : ramanujanPoleProfile m n *
      (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) =
      (finiteFlip {p} n * ramanujanLagCoefficient m n / n) /
        Real.sqrt (m.totient : ℝ) / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) := by
    rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient hm]
    calc
      _ = (finiteFlip {p} n * ramanujanLagCoefficient m n) /
          (Real.sqrt n * Real.sqrt n) / Real.sqrt (m.totient : ℝ) /
            Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [sum_congr rfl (fun n _ => ht n), ← sum_div, ← sum_div]
  change (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))⁻¹ *
    (primeParityRamanujanSum p m N / Real.sqrt (m.totient : ℝ) /
      Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) = _
  calc
    _ = primeParityRamanujanSum p m N /
        (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) *
          Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) / Real.sqrt (m.totient : ℝ) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hH]

/-- Harmonic Ramanujan coordinates retain the finite Mobius transform of prime parity. -/
theorem tendsto_primeParityHorizonVector_inner {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ⟪primeParityHorizonVector p N, harmonicRamanujanHorizonVector m N⟫)
      atTop (𝓝 ((((p : ℝ) - 1) / ((p : ℝ) + 1) *
        ∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip {p} d) /
          Real.sqrt (m.totient : ℝ))) := by
  simpa only [primeParityHorizonVector_inner hm] using
    (primeParityRamanujanSum_tendsto hp m).div_const (Real.sqrt (m.totient : ℝ))

theorem tendsto_primeParityHorizonVector_inner_zero {p m : ℕ} (hp : p.Prime)
    (hm : 2 ≤ m) (hpm : ¬ p ∣ m) :
    Tendsto (fun N : ℕ =>
      ⟪primeParityHorizonVector p N, harmonicRamanujanHorizonVector m N⟫)
      atTop (𝓝 0) := by
  simpa only [primeParityHorizonVector_inner (show 0 < m by omega), zero_div] using
    (primeParityRamanujanSum_tendsto_zero hp hm hpm).div_const (Real.sqrt (m.totient : ℝ))

private theorem inner_eigenProjection {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (S : Finset I)
    (v u : EuclideanSpace ℝ I) :
    ⟪v, HTGeometry.hermitianEigenProjection hA S u⟫ =
      ∑ i ∈ S, ⟪u, hA.eigenvectorBasis i⟫ * ⟪v, hA.eigenvectorBasis i⟫ := by
  simp only [HTGeometry.hermitianEigenProjection, inner_sum, real_inner_smul_right]

private theorem norm_eigenProjection_sq {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (S : Finset I)
    (u : EuclideanSpace ℝ I) :
    ‖HTGeometry.hermitianEigenProjection hA S u‖ ^ 2 =
      ∑ i ∈ S, ⟪u, hA.eigenvectorBasis i⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eigenProjection]
  refine sum_congr rfl fun i hi => ?_
  rw [HTGeometry.inner_hermitianEigenProjection, if_pos hi, sq]

private theorem eigenProjection_pythagoras {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (S : Finset I)
    (u : EuclideanSpace ℝ I) :
    ‖u - HTGeometry.hermitianEigenProjection hA S u‖ ^ 2 =
      ‖u‖ ^ 2 - ‖HTGeometry.hermitianEigenProjection hA S u‖ ^ 2 := by
  have hi : ⟪u, HTGeometry.hermitianEigenProjection hA S u⟫ =
      ‖HTGeometry.hermitianEigenProjection hA S u‖ ^ 2 := by
    rw [inner_eigenProjection, norm_eigenProjection_sq]
    exact sum_congr rfl fun _ _ => (sq _).symm
  rw [norm_sub_sq_real, hi]
  ring

/-- The harmonically normalized conductor projected onto its actual energy window. -/
def harmonicRamanujanWindowProjection (m N : ℕ) (δ : ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  HTGeometry.hermitianEigenProjection (fullPrimeMatrix_isHermitian N)
    (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ)
    (harmonicRamanujanHorizonVector m N)

theorem tendsto_harmonicRamanujanWindowProjection_error_sq {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖ ^ 2)
      atTop (𝓝 0) := by
  have hbound (N : ℕ) :
      ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (harmonicRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • harmonicRamanujanHorizonVector m N‖ ^ 2 /
          δ ^ 2 := by
    have hgap : ∀ i ∉ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
        δ ≤ |(fullPrimeMatrix_isHermitian N).eigenvalues i -
          (Real.log N - ramanujanAdjunctionEnergy m)| := by
      intro i hi
      rw [← abs_fullPrimeEnergyEigenvalue_sub m N i]
      by_contra hn
      have h := abs_lt.mp (lt_of_not_ge hn)
      apply hi
      apply (mem_fullPrimeEnergyWindow _ _ _ _).mpr
      exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    have h := HTGeometry.gap_sq_mul_eigenProjection_error_le_residual_sq
      (fullPrimeMatrix_isHermitian N)
      (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ)
      (harmonicRamanujanHorizonVector m N) (Real.log N - ramanujanAdjunctionEnergy m)
      δ hδ.le hgap
    rw [le_div_iff₀ (sq_pos_of_pos hδ)]
    simpa only [harmonicRamanujanWindowProjection, mul_comm] using h
  apply squeeze_zero (fun N => sq_nonneg _) hbound
  simpa only [zero_div] using
    (tendsto_harmonicRamanujanHorizonVector_residual_sq hm).div_const (δ ^ 2)

theorem tendsto_harmonicRamanujanWindowProjection_norm_sq {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2)
      atTop (𝓝 1) := by
  have he (N : ℕ) : ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2 =
      ‖harmonicRamanujanHorizonVector m N‖ ^ 2 -
        ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖ ^ 2 := by
    have h := eigenProjection_pythagoras (fullPrimeMatrix_isHermitian N)
      (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ)
      (harmonicRamanujanHorizonVector m N)
    change ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖ ^ 2 =
      ‖harmonicRamanujanHorizonVector m N‖ ^ 2 -
        ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2 at h
    linarith only [h]
  simpa only [he, sub_zero] using (tendsto_harmonicRamanujanHorizonVector_norm_sq hm).sub
    (tendsto_harmonicRamanujanWindowProjection_error_sq hm hδ)

private theorem tendsto_primeParity_inner_projection {p m : ℕ} (hm : 0 < m)
    {δ L : ℝ} (hδ : 0 < δ)
    (hinner : Tendsto (fun N : ℕ =>
      ⟪primeParityHorizonVector p N, harmonicRamanujanHorizonVector m N⟫) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ =>
      ⟪primeParityHorizonVector p N, harmonicRamanujanWindowProjection m N δ⟫)
      atTop (𝓝 L) := by
  have hnorm : Tendsto (fun N : ℕ =>
      ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
      (tendsto_harmonicRamanujanWindowProjection_error_sq hm hδ).sqrt
  have herr : Tendsto (fun N : ℕ =>
      ⟪primeParityHorizonVector p N,
        harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ⟫)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hnorm
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖primeParityHorizonVector p N‖ *
          ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖ :=
        abs_real_inner_le_norm _ _
      _ = _ := by rw [primeParityHorizonVector_norm p hN, one_mul]
  have he (N : ℕ) :
      ⟪primeParityHorizonVector p N, harmonicRamanujanWindowProjection m N δ⟫ =
      ⟪primeParityHorizonVector p N, harmonicRamanujanHorizonVector m N⟫ -
        ⟪primeParityHorizonVector p N,
          harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ⟫ := by
    rw [inner_sub_right]
    ring
  simpa only [he, sub_zero] using hinner.sub herr

/-- The squared gauge coordinate along the projected conductor direction. -/
def primeParityWindowCoordinateSq (p m N : ℕ) (δ : ℝ) : ℝ :=
  ⟪primeParityHorizonVector p N, harmonicRamanujanWindowProjection m N δ⟫ ^ 2 /
    ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2

theorem tendsto_primeParityWindowCoordinateSq {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => primeParityWindowCoordinateSq p m N δ) atTop
      (𝓝 (((((p : ℝ) - 1) / ((p : ℝ) + 1) *
        ∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip {p} d) /
          Real.sqrt (m.totient : ℝ)) ^ 2)) := by
  have h := tendsto_primeParity_inner_projection hm hδ
    (tendsto_primeParityHorizonVector_inner hp hm)
  simpa only [primeParityWindowCoordinateSq, div_one, Pi.div_def] using
    (h.pow 2).div (tendsto_harmonicRamanujanWindowProjection_norm_sq hm hδ)
      (by norm_num : (1 : ℝ) ≠ 0)

theorem primeParityWindowCoordinateSq_eq {p m N : ℕ} {δ : ℝ}
    (i : PrimeHorizonIndex N)
    (hwindow : fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ = {i})
    (hpos : 0 < ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2) :
    primeParityWindowCoordinateSq p m N δ =
      ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 := by
  let e := (fullPrimeMatrix_isHermitian N).eigenvectorBasis i
  have he : ‖e‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [e, ↓reduceIte] using
      (orthonormal_iff_ite.mp (fullPrimeMatrix_isHermitian N).eigenvectorBasis.orthonormal) i i
  have hP : harmonicRamanujanWindowProjection m N δ =
      ⟪harmonicRamanujanHorizonVector m N, e⟫ • e := by
    simp only [harmonicRamanujanWindowProjection, HTGeometry.hermitianEigenProjection,
      hwindow, sum_singleton, e]
  have hnormP : ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2 =
      ⟪harmonicRamanujanHorizonVector m N, e⟫ ^ 2 := by
    rw [hP, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, he, mul_one]
  have hinnerP : ⟪primeParityHorizonVector p N, harmonicRamanujanWindowProjection m N δ⟫ =
      ⟪harmonicRamanujanHorizonVector m N, e⟫ * ⟪primeParityHorizonVector p N, e⟫ := by
    rw [hP, real_inner_smul_right]
  rw [hnormP] at hpos
  have ha : ⟪harmonicRamanujanHorizonVector m N, e⟫ ≠ 0 := by
    intro hz
    rw [hz] at hpos
    norm_num at hpos
  rw [primeParityWindowCoordinateSq, hnormP, hinnerP, mul_pow]
  field_simp [ha]
  rfl

/-- Exact parity counts determine the squared coordinates on actual simple prime
eigenlines, uniformly over the index in each isolating window. -/
theorem exists_primeParity_eigenline_coordinates {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ N : ℕ in atTop,
        (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ).card = 1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
          |fullPrimeEnergyEigenvalue N i - ramanujanAdjunctionEnergy m| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
          |⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 -
            ((((p : ℝ) - 1) / ((p : ℝ) + 1) *
              ∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip {p} d) /
                Real.sqrt (m.totient : ℝ)) ^ 2| < ε) := by
  obtain ⟨δ, hδ, hcard, hnear, _⟩ := exists_simple_fullPrime_eigenline hm
  refine ⟨δ, hδ, hcard, hnear, ?_⟩
  intro ε hε
  have hlim := tendsto_primeParityWindowCoordinateSq hp hm hδ
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N₀, hN₀⟩ := hlim ε hε
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2 :=
    (tendsto_harmonicRamanujanWindowProjection_norm_sq hm hδ).eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcard, hpos, eventually_ge_atTop N₀] with N hc hn hN i hi
  obtain ⟨j, hj⟩ := card_eq_one.mp hc
  have hij : i = j := mem_singleton.mp (hj ▸ hi)
  subst j
  have h := hN₀ N hN
  rw [Real.dist_eq, primeParityWindowCoordinateSq_eq i hj hn] at h
  exact h

end GaloisForLFunctions.ArithmeticCountingPositivity
