import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHaveUnitConductorMass
import GaloisForLFunctions.ArithmeticCountingPositivity.HarmonicParitySpectralCoordinates

/-!
# Finite-prime counts determine actual conductor coordinates

Exact divisibility counts identify the harmonic Ramanujan coefficients.
The common quasimode residual and isolated spectral windows transfer them
to squared coordinates on actual prime eigenlines.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.BezoutValuationIncidence

/-- The mixed harmonic count of a finite-prime sign and a Ramanujan conductor. -/
def finiteFlipRamanujanSum (F : Finset ℕ) (m N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, finiteFlip F n * ramanujanLagCoefficient m n / n

/-- Divisibility incidence preserves the exact decimated signed count. -/
theorem finiteFlipRamanujanSum_eq (F : Finset ℕ) (m N : ℕ) :
    finiteFlipRamanujanSum F m N =
      ∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip F d *
        gaugeHarmonicSum (finiteFlip F) (N / d) := by
  unfold finiteFlipRamanujanSum ramanujanLagCoefficient
  simp_rw [mul_sum, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have he : (∑ n ∈ Icc 1 N, finiteFlip F n *
      (moebiusReal (m / d) * (if d ∣ n then (d : ℝ) else 0)) / n) =
      moebiusReal (m / d) *
        ∑ n ∈ Icc 1 N, finiteFlip F n * (if d ∣ n then (d : ℝ) else 0) / n := by
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [he, gaugeHarmonicSum_divisibility (finiteFlip F)
    (finiteFlip_isSignGauge F) (Nat.pos_of_mem_divisors hd)]
  ring

private theorem finiteFlip_decimation_tendsto (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (finiteFlip F) (N / d) /
      gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 (finiteFlipHarmonicDensity F)) := by
  obtain ⟨K, hK, hbound⟩ := finiteFlip_harmonic_error_bounded F hF
  have hc := (finiteFlipHarmonicDensity_pos hF).le
  let C := K + finiteFlipHarmonicDensity F * (1 + Real.log d)
  have herr (N : ℕ) : |gaugeHarmonicSum (finiteFlip F) (N / d) -
      finiteFlipHarmonicDensity F * gaugeHarmonicSum (fun _ => 1) N| ≤ C := by
    have hb := abs_le.mp (hbound (N / d))
    have hmono : gaugeHarmonicSum (fun _ => 1) (N / d) ≤
        gaugeHarmonicSum (fun _ => 1) N := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
          (mem_Icc.mp hn).2.trans (Nat.div_le_self N d)⟩
      · intro n _ _
        positivity
    have htail := roughHarmonic_sub_div_le 0 N hd
    simp only [roughHarmonic, roughInterval_zero] at htail
    change gaugeHarmonicSum (fun _ => 1) N -
      gaugeHarmonicSum (fun _ => 1) (N / d) ≤ 1 + Real.log d at htail
    have hcost := mul_le_mul_of_nonneg_left htail hc
    have hcost0 : 0 ≤ finiteFlipHarmonicDensity F * (1 + Real.log d) := by positivity
    have hmonoc := mul_le_mul_of_nonneg_left hmono hc
    rw [abs_le]
    dsimp only [C]
    constructor
    · nlinarith only [hb.1, hcost]
    · linarith only [hb.2, hmonoc, hcost0]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop (C / ε))
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hH := gaugeHarmonicSum_one_pos hN1
  have hlarge : C / ε < gaugeHarmonicSum (fun _ => 1) N :=
    (hN₀ N ((le_max_right _ _).trans hN)).trans_le (log_le_gaugeHarmonicSum_one hN1)
  have hsmall : C / gaugeHarmonicSum (fun _ => 1) N < ε := by
    rw [div_lt_iff₀ hε] at hlarge
    rw [div_lt_iff₀ hH]
    nlinarith only [hlarge]
  have he : gaugeHarmonicSum (finiteFlip F) (N / d) /
      gaugeHarmonicSum (fun _ => 1) N - finiteFlipHarmonicDensity F =
      (gaugeHarmonicSum (finiteFlip F) (N / d) -
        finiteFlipHarmonicDensity F * gaugeHarmonicSum (fun _ => 1) N) /
          gaugeHarmonicSum (fun _ => 1) N := by field_simp [hH.ne']
  rw [Real.dist_eq, he, abs_div, abs_of_pos hH]
  exact (div_le_div_of_nonneg_right (herr N) hH.le).trans_lt hsmall

/-- The limiting harmonic count is the product mean times the exact Möbius transform. -/
theorem finiteFlipRamanujanSum_tendsto (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (m : ℕ) :
    Tendsto (fun N : ℕ => finiteFlipRamanujanSum F m N /
      gaugeHarmonicSum (fun _ => 1) N) atTop
      (𝓝 (finiteFlipHarmonicDensity F * finiteFlipMobius F m)) := by
  have hlim := tendsto_finsetSum m.divisors (fun d hd =>
    (finiteFlip_decimation_tendsto F hF (Nat.pos_of_mem_divisors hd)).const_mul
      (moebiusReal (m / d) * finiteFlip F d))
  simpa only [finiteFlipRamanujanSum_eq, sum_div, mul_div_assoc, ← sum_mul,
    mul_comm (finiteFlipHarmonicDensity F), finiteFlipMobius_eq_divisor_sum] using hlim

/-- The finite-prime constraint normalized by harmonic mass. -/
def finiteFlipHorizonVector (F : Finset ℕ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => finiteFlip F n / Real.sqrt n /
    Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))

private theorem finiteFlip_mul_self_all (F : Finset ℕ) (n : ℕ) :
    finiteFlip F n * finiteFlip F n = 1 := by
  rw [finiteFlip, ← prod_mul_distrib]
  refine prod_eq_one fun p _ => ?_
  rw [← mul_pow]
  norm_num

theorem finiteFlipHorizonVector_norm_sq (F : Finset ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ‖finiteFlipHorizonVector F N‖ ^ 2 = 1 := by
  have hH := gaugeHarmonicSum_one_pos hN
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    (finiteFlip F n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2) = 1
  rw [sum_coe_sort (Icc 1 N) (fun n =>
    (finiteFlip F n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2)]
  have ht (n : ℕ) :
      (finiteFlip F n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2 =
        1 / (n : ℝ) / gaugeHarmonicSum (fun _ => 1) N := by
    rw [div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt hH.le,
      sq, finiteFlip_mul_self_all]
  rw [sum_congr rfl (fun n _ => ht n), ← sum_div]
  exact div_self hH.ne'

private theorem finiteFlipHorizonVector_norm (F : Finset ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ‖finiteFlipHorizonVector F N‖ = 1 := by
  nlinarith only [finiteFlipHorizonVector_norm_sq F hN,
    norm_nonneg (finiteFlipHorizonVector F N)]

/-- The arithmetic mixed count is an exact inner product on the actual integer horizon. -/
theorem finiteFlipHorizonVector_inner {m : ℕ} (hm : 0 < m) (F : Finset ℕ) (N : ℕ) :
    ⟪finiteFlipHorizonVector F N, harmonicRamanujanHorizonVector m N⟫ =
      finiteFlipRamanujanSum F m N / gaugeHarmonicSum (fun _ => 1) N /
        Real.sqrt (m.totient : ℝ) := by
  have hH : 0 ≤ gaugeHarmonicSum (fun _ => 1) N := sum_nonneg fun _ _ => by positivity
  rw [harmonicRamanujanHorizonVector, real_inner_smul_right,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))⁻¹ *
    (∑ n : PrimeHorizonIndex N, ramanujanPoleProfile m n *
      (finiteFlip F n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile m n *
    (finiteFlip F n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)))]
  have ht (n : ℕ) : ramanujanPoleProfile m n *
      (finiteFlip F n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) =
      (finiteFlip F n * ramanujanLagCoefficient m n / n) /
        Real.sqrt (m.totient : ℝ) / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) := by
    rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient hm]
    calc
      _ = (finiteFlip F n * ramanujanLagCoefficient m n) /
          (Real.sqrt n * Real.sqrt n) / Real.sqrt (m.totient : ℝ) /
            Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [sum_congr rfl (fun n _ => ht n), ← sum_div, ← sum_div]
  change (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))⁻¹ *
    (finiteFlipRamanujanSum F m N / Real.sqrt (m.totient : ℝ) /
      Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) = _
  calc
    _ = finiteFlipRamanujanSum F m N /
        (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) *
          Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) / Real.sqrt (m.totient : ℝ) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hH]

/-- The counted conductor coefficient is the limit of the normalized inner product. -/
theorem tendsto_finiteFlipHorizonVector_inner (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ⟪finiteFlipHorizonVector F N, harmonicRamanujanHorizonVector m N⟫)
      atTop (𝓝 (finiteFlipConductorCoefficient F m)) := by
  simpa only [finiteFlipHorizonVector_inner hm, finiteFlipConductorCoefficient] using
    (finiteFlipRamanujanSum_tendsto F hF m).div_const (Real.sqrt (m.totient : ℝ))

private theorem tendsto_finiteFlip_inner_projection {F : Finset ℕ} {m : ℕ} (hm : 0 < m)
    {δ L : ℝ} (hδ : 0 < δ)
    (hinner : Tendsto (fun N : ℕ =>
      ⟪finiteFlipHorizonVector F N, harmonicRamanujanHorizonVector m N⟫) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ =>
      ⟪finiteFlipHorizonVector F N, harmonicRamanujanWindowProjection m N δ⟫)
      atTop (𝓝 L) := by
  have hnorm : Tendsto (fun N : ℕ =>
      ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
      (tendsto_harmonicRamanujanWindowProjection_error_sq hm hδ).sqrt
  have herr : Tendsto (fun N : ℕ =>
      ⟪finiteFlipHorizonVector F N,
        harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ⟫)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hnorm
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖finiteFlipHorizonVector F N‖ *
          ‖harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ‖ :=
        abs_real_inner_le_norm _ _
      _ = _ := by rw [finiteFlipHorizonVector_norm F hN, one_mul]
  have he (N : ℕ) :
      ⟪finiteFlipHorizonVector F N, harmonicRamanujanWindowProjection m N δ⟫ =
      ⟪finiteFlipHorizonVector F N, harmonicRamanujanHorizonVector m N⟫ -
        ⟪finiteFlipHorizonVector F N,
          harmonicRamanujanHorizonVector m N - harmonicRamanujanWindowProjection m N δ⟫ := by
    rw [inner_sub_right]
    ring
  simpa only [he, sub_zero] using hinner.sub herr

/-- The squared constraint coordinate in the projected conductor direction. -/
def finiteFlipWindowCoordinateSq (F : Finset ℕ) (m N : ℕ) (δ : ℝ) : ℝ :=
  ⟪finiteFlipHorizonVector F N, harmonicRamanujanWindowProjection m N δ⟫ ^ 2 /
    ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2

/-- Projection onto the actual energy window preserves the counted squared coefficient. -/
theorem tendsto_finiteFlipWindowCoordinateSq (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => finiteFlipWindowCoordinateSq F m N δ) atTop
      (𝓝 (finiteFlipConductorCoefficient F m ^ 2)) := by
  have h := tendsto_finiteFlip_inner_projection hm hδ
    (tendsto_finiteFlipHorizonVector_inner F hF hm)
  simpa only [finiteFlipWindowCoordinateSq, div_one, Pi.div_def] using
    (h.pow 2).div (tendsto_harmonicRamanujanWindowProjection_norm_sq hm hδ)
      (by norm_num : (1 : ℝ) ≠ 0)

private theorem finiteFlipWindowCoordinateSq_eq {F : Finset ℕ} {m N : ℕ} {δ : ℝ}
    (i : PrimeHorizonIndex N)
    (hwindow : fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ = {i})
    (hpos : 0 < ‖harmonicRamanujanWindowProjection m N δ‖ ^ 2) :
    finiteFlipWindowCoordinateSq F m N δ =
      ⟪finiteFlipHorizonVector F N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 := by
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
  have hinnerP : ⟪finiteFlipHorizonVector F N, harmonicRamanujanWindowProjection m N δ⟫ =
      ⟪harmonicRamanujanHorizonVector m N, e⟫ * ⟪finiteFlipHorizonVector F N, e⟫ := by
    rw [hP, real_inner_smul_right]
  rw [hnormP] at hpos
  have ha : ⟪harmonicRamanujanHorizonVector m N, e⟫ ≠ 0 := by
    intro hz
    rw [hz] at hpos
    norm_num at hpos
  rw [finiteFlipWindowCoordinateSq, hnormP, hinnerP, mul_pow]
  field_simp [ha]
  rfl

/-- Every isolated actual conductor eigenline has the counted squared constraint coordinate. -/
theorem exists_finiteFlip_eigenline_coordinates (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {m : ℕ} (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ N : ℕ in atTop,
        (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ).card = 1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
          |fullPrimeEnergyEigenvalue N i - ramanujanAdjunctionEnergy m| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
          |⟪finiteFlipHorizonVector F N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 -
            finiteFlipConductorCoefficient F m ^ 2| < ε) := by
  obtain ⟨δ, hδ, hcard, hnear, _⟩ := exists_simple_fullPrime_eigenline hm
  refine ⟨δ, hδ, hcard, hnear, ?_⟩
  intro ε hε
  have hlim := tendsto_finiteFlipWindowCoordinateSq F hF hm hδ
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
  rw [Real.dist_eq, finiteFlipWindowCoordinateSq_eq i hj hn] at h
  exact h

/-- Actual eigenline sequences realize each positive conductor's energy and arithmetic mass. -/
theorem exists_finiteFlip_conductor_eigenline (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {m : ℕ} (hm : 0 < m) :
    ∃ idx : ∀ N : ℕ, PrimeHorizonIndex (N + 1),
      Tendsto (fun N => fullPrimeEnergyEigenvalue (N + 1) (idx N))
        atTop (𝓝 (ramanujanAdjunctionEnergy m)) ∧
      Tendsto (fun N =>
        ⟪finiteFlipHorizonVector F (N + 1),
          (fullPrimeMatrix_isHermitian (N + 1)).eigenvectorBasis (idx N)⟫ ^ 2)
        atTop (𝓝 (finiteFlipConductorCoefficient F m ^ 2)) := by
  classical
  obtain ⟨δ, hδ, hcard, hnear, hcoord⟩ := exists_finiteFlip_eigenline_coordinates F hF hm
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop n).mono fun N hN => by omega
  have hchoice : ∀ N : ℕ, ∃ i : PrimeHorizonIndex (N + 1),
      (fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ).Nonempty →
        i ∈ fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ := by
    intro N
    by_cases h : (fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ).Nonempty
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩, fun hn => False.elim (h hn)⟩
  choose idx hidx using hchoice
  have hmem : ∀ᶠ N : ℕ in atTop,
      idx N ∈ fullPrimeEnergyWindow (N + 1) (ramanujanAdjunctionEnergy m) δ := by
    filter_upwards [hshift.eventually hcard] with N hc
    apply hidx N
    exact card_pos.mp (by rw [hc]; omega)
  refine ⟨idx, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    apply eventually_atTop.mp
    filter_upwards [hshift.eventually (hnear ε hε), hmem] with N hn hi
    simpa only [Real.dist_eq] using hn (idx N) hi
  · rw [Metric.tendsto_atTop]
    intro ε hε
    apply eventually_atTop.mp
    filter_upwards [hshift.eventually (hcoord ε hε), hmem] with N hn hi
    simpa only [Real.dist_eq] using hn (idx N) hi

end GaloisForLFunctions.ArithmeticCountingPositivity
