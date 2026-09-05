import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalFinitePacketFeshbachAssembly
import GaloisForLFunctions.RHTower.XiMassAdjacentPrimeMask

/-!
# Adjacent-prime cofinal physical Feshbach assembly

P-G84 extracts the positive survivor of P-G83.  The complete graph diverges because it repeats
same-prime minors with infinite incidence.  The ordered adjacent-prime path has bounded incidence,
keeps every local P-G81 packet at its literal physical Cauchy--Binet mass, and remains summable over
all valuation depths.  Bertrand's theorem is used only to compare adjacent prime logarithms.

The resulting numerator, denominator, and both strict Schur gaps are unconditional sums.  Their
global fraction is strictly between `1/2` and `1`, so every cofinal residual weight is positive and
strictly below the symmetrized half residual.  This is an exhaustion-independent infinite physical
assembly; identification with the global Gamma/polar Feshbach operator remains the next gate.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

abbrev gammaSewnCriticalAdjacentPrime_primeTwo : Nat.Primes := ⟨2, by norm_num⟩

abbrev gammaSewnCriticalAdjacentPrime_aperture : ℝ :=
  gammaSewnCriticalFinitePacket_aperture

def gammaSewnCriticalAdjacentPrime_gap : ℝ :=
  Real.log 2 / 2 - gammaSewnCriticalAdjacentPrime_aperture

theorem gammaSewnCriticalAdjacentPrime_gap_pos :
    0 < gammaSewnCriticalAdjacentPrime_gap := by
  have h := gammaSewnCriticalFinitePacket_aperture_admissible 0
    gammaSewnCriticalAdjacentPrime_primeTwo
  dsimp [gammaSewnCriticalAdjacentPrime_gap,
    gammaSewnCriticalAdjacentPrime_aperture] at h ⊢
  norm_num at h ⊢
  linarith

def gammaSewnCriticalAdjacentPrime_depthScale (e : ℕ) : ℝ :=
  (e : ℝ) + 1 / 2

theorem gammaSewnCriticalAdjacentPrime_depthScale_pos (e : ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_depthScale e := by
  unfold gammaSewnCriticalAdjacentPrime_depthScale
  positivity

private theorem criticalAdjacent_twoBoundaryPluckerSq_le
    {lambda mu c L : ℝ}
    (hc : 0 < c) (hL : 0 < L)
    (hlowerLambda : c * L ≤ lambda) (hlowerMu : c * L ≤ mu)
    (hupperLambda : lambda ≤ 6 * c * L) (hupperMu : mu ≤ 6 * c * L)
    (hgapRate : gammaSewnCriticalAdjacentPrime_aperture +
        gammaSewnCriticalAdjacentPrime_gap ≤ c * L) :
    RHTower.twoBoundaryCauchyPairPluckerSq
        gammaSewnCriticalAdjacentPrime_aperture lambda mu ≤
      576 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
        (gammaSewnCriticalAdjacentPrime_gap ^ 4 * c ^ 2 * L ^ 2) := by
  let a := gammaSewnCriticalAdjacentPrime_aperture
  let delta := gammaSewnCriticalAdjacentPrime_gap
  have ha : 0 < a := gammaSewnCriticalPlucker_hostileHarmonicAperture_pos
  have hdelta : 0 < delta := gammaSewnCriticalAdjacentPrime_gap_pos
  have hcL : 0 < c * L := mul_pos hc hL
  have hlambda : 0 < lambda := lt_of_lt_of_le hcL hlowerLambda
  have hmu : 0 < mu := lt_of_lt_of_le hcL hlowerMu
  have hgapLambda : a + delta ≤ lambda := hgapRate.trans hlowerLambda
  have hgapMu : a + delta ≤ mu := hgapRate.trans hlowerMu
  have hdenLambda : delta * lambda ≤ lambda ^ 2 - a ^ 2 := by
    calc
      delta * lambda ≤ (lambda - a) * lambda :=
        mul_le_mul_of_nonneg_right (by linarith) hlambda.le
      _ ≤ (lambda - a) * (lambda + a) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = lambda ^ 2 - a ^ 2 := by ring
  have hdenMu : delta * mu ≤ mu ^ 2 - a ^ 2 := by
    calc
      delta * mu ≤ (mu - a) * mu :=
        mul_le_mul_of_nonneg_right (by linarith) hmu.le
      _ ≤ (mu - a) * (mu + a) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = mu ^ 2 - a ^ 2 := by ring
  have hdenLambdaPos : 0 < lambda ^ 2 - a ^ 2 :=
    lt_of_lt_of_le (mul_pos hdelta hlambda) hdenLambda
  have hdenMuPos : 0 < mu ^ 2 - a ^ 2 :=
    lt_of_lt_of_le (mul_pos hdelta hmu) hdenMu
  have hdenLower :
      (delta ^ 2 * (c * L) ^ 2) ^ 2 ≤
        ((lambda ^ 2 - a ^ 2) * (mu ^ 2 - a ^ 2)) ^ 2 := by
    have hprod : delta ^ 2 * (c * L) ^ 2 ≤
        (lambda ^ 2 - a ^ 2) * (mu ^ 2 - a ^ 2) := by
      calc
        delta ^ 2 * (c * L) ^ 2 = (delta * (c * L)) * (delta * (c * L)) := by ring
        _ ≤ (delta * lambda) * (delta * mu) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hlowerLambda hdelta.le)
            (mul_le_mul_of_nonneg_left hlowerMu hdelta.le)
            (mul_nonneg hdelta.le hcL.le)
            (mul_nonneg hdelta.le hlambda.le)
        _ ≤ (lambda ^ 2 - a ^ 2) * (mu ^ 2 - a ^ 2) :=
          mul_le_mul hdenLambda hdenMu
            (mul_nonneg hdelta.le hmu.le) hdenLambdaPos.le
    exact (sq_le_sq₀ (by positivity)
      (mul_nonneg hdenLambdaPos.le hdenMuPos.le)).2 hprod
  have hdiffAbs : |lambda - mu| ≤ 12 * c * L := by
    calc
      |lambda - mu| ≤ |lambda| + |mu| := abs_sub _ _
      _ = lambda + mu := by rw [abs_of_pos hlambda, abs_of_pos hmu]
      _ ≤ 12 * c * L := by linarith
  have hdiffSq : (lambda - mu) ^ 2 ≤ (12 * c * L) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdiffAbs
  have hnum : (2 * a * (lambda - mu)) ^ 2 ≤
      (24 * a * c * L) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (2 * a))
      (sub_nonneg.mpr hdiffSq)]
  have hdenPos : 0 < ((lambda ^ 2 - a ^ 2) * (mu ^ 2 - a ^ 2)) ^ 2 :=
    sq_pos_of_pos (mul_pos hdenLambdaPos hdenMuPos)
  have hdenLowerPos : 0 < (delta ^ 2 * (c * L) ^ 2) ^ 2 := by positivity
  unfold RHTower.twoBoundaryCauchyPairPluckerSq
    RHTower.twoBoundaryCauchyPairPlucker
  rw [div_pow]
  calc
    (2 * a * (lambda - mu)) ^ 2 /
        ((lambda ^ 2 - a ^ 2) * (mu ^ 2 - a ^ 2)) ^ 2 ≤
      (24 * a * c * L) ^ 2 /
        ((lambda ^ 2 - a ^ 2) * (mu ^ 2 - a ^ 2)) ^ 2 :=
        div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ (24 * a * c * L) ^ 2 /
        (delta ^ 2 * (c * L) ^ 2) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hdenLowerPos hdenLower
    _ = 576 * a ^ 2 / (delta ^ 4 * c ^ 2 * L ^ 2) := by
      field_simp [hdelta.ne', hc.ne', hL.ne']
      ring

def gammaSewnCriticalAdjacentPrime_lower (n : ℕ) : Nat.Primes :=
  RHTower.nthPrimeSubtype n

def gammaSewnCriticalAdjacentPrime_upper (n : ℕ) : Nat.Primes :=
  RHTower.nthPrimeSubtype (n + 1)

theorem gammaSewnCriticalAdjacentPrime_order (n : ℕ) :
    (gammaSewnCriticalAdjacentPrime_lower n : ℕ) <
      (gammaSewnCriticalAdjacentPrime_upper n : ℕ) := by
  exact RHTower.nthPrimeSubtype_strictMono (Nat.lt_succ_self n)

private theorem criticalAdjacent_log_upper_le_two_lower (n : ℕ) :
    Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) ≤
      2 * Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) := by
  simpa [gammaSewnCriticalAdjacentPrime_lower,
    gammaSewnCriticalAdjacentPrime_upper, RHTower.xiMassNthPrimeLogHeight] using
      RHTower.xiMassNthPrimeLogHeight_succ_le_two_mul n

private theorem criticalAdjacent_rate_bounds (e n : ℕ) (i : Fin 4) :
    let c := gammaSewnCriticalAdjacentPrime_depthScale e
    let L := Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ)
    c * L ≤ gammaSewnOrderedPrimeDepthPlucker_rate e
        (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) i ∧
      gammaSewnOrderedPrimeDepthPlucker_rate e
        (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) i ≤ 6 * c * L := by
  let c := gammaSewnCriticalAdjacentPrime_depthScale e
  let L := Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ)
  have hc : 0 < c := gammaSewnCriticalAdjacentPrime_depthScale_pos e
  have hL : 0 < L := Real.log_pos (by
    exact_mod_cast (gammaSewnCriticalAdjacentPrime_lower n).2.one_lt)
  have hlogOrder : L ≤ Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show 0 < (gammaSewnCriticalAdjacentPrime_lower n : ℝ) by
        exact_mod_cast (gammaSewnCriticalAdjacentPrime_lower n).2.pos)
      (show 0 < (gammaSewnCriticalAdjacentPrime_upper n : ℝ) by
        exact_mod_cast (gammaSewnCriticalAdjacentPrime_upper n).2.pos)
      (by exact_mod_cast (gammaSewnCriticalAdjacentPrime_order n).le)
  have hlogUpper := criticalAdjacent_log_upper_le_two_lower n
  have hd : (e : ℝ) + 3 / 2 ≤ 3 * c := by
    have he : (0 : ℝ) ≤ (e : ℝ) := by positivity
    dsimp [c, gammaSewnCriticalAdjacentPrime_depthScale]
    linarith
  have hcd : c ≤ (e : ℝ) + 3 / 2 := by
    dsimp [c, gammaSewnCriticalAdjacentPrime_depthScale]
    linarith
  have hdpos : 0 ≤ (e : ℝ) + 3 / 2 := by positivity
  have hlogUpperNonneg : 0 ≤ Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (gammaSewnCriticalAdjacentPrime_upper n).2.one_le)
  have hlowerD : c * L ≤
      ((e : ℝ) + 3 / 2) * Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) :=
    mul_le_mul hcd hlogOrder hL.le hdpos
  have hupperD : ((e : ℝ) + 3 / 2) *
      Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) ≤ 6 * c * L := by
    calc
      _ ≤ (3 * c) * (2 * L) :=
        mul_le_mul hd hlogUpper hlogUpperNonneg (mul_nonneg (by norm_num) hc.le)
      _ = 6 * c * L := by ring
  have hsuccScale : (e : ℝ) + 1 + 1 / 2 = (e : ℝ) + 3 / 2 := by ring
  have hlowerP : c * L ≤ ((e : ℝ) + 3 / 2) * L :=
    mul_le_mul_of_nonneg_right hcd hL.le
  have hupperP : ((e : ℝ) + 3 / 2) * L ≤ 6 * c * L := by
    calc
      _ ≤ (3 * c) * L := mul_le_mul_of_nonneg_right hd hL.le
      _ ≤ 6 * c * L := by nlinarith [mul_pos hc hL]
  have hlowerQ : c * L ≤ c * Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) :=
    mul_le_mul_of_nonneg_left hlogOrder hc.le
  have hupperQ : c * Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ) ≤
      6 * c * L := by
    calc
      _ ≤ c * (2 * L) := mul_le_mul_of_nonneg_left hlogUpper hc.le
      _ ≤ 6 * c * L := by nlinarith [mul_pos hc hL]
  fin_cases i
  · simpa [gammaSewnOrderedPrimeDepthPlucker_rate,
      gammaSewnOrderedPrimeDepthPlucker_cell,
      RHTower.gammaSewnMobiusApertureCellMidHeight,
      gammaSewnCriticalAdjacentPrime_depthScale, c, L] using
        (And.intro (le_refl (c * L)) (by nlinarith [mul_pos hc hL]))
  · convert And.intro hlowerP hupperP using 1 <;>
      simp [gammaSewnOrderedPrimeDepthPlucker_rate,
        gammaSewnOrderedPrimeDepthPlucker_cell,
        RHTower.gammaSewnMobiusApertureCellMidHeight,
        gammaSewnCriticalAdjacentPrime_depthScale, c, L] <;> ring
  · simpa [gammaSewnOrderedPrimeDepthPlucker_rate,
      gammaSewnOrderedPrimeDepthPlucker_cell,
      RHTower.gammaSewnMobiusApertureCellMidHeight,
      gammaSewnCriticalAdjacentPrime_depthScale, c, L] using And.intro hlowerQ hupperQ
  · convert And.intro hlowerD hupperD using 1 <;>
      simp [gammaSewnOrderedPrimeDepthPlucker_rate,
        gammaSewnOrderedPrimeDepthPlucker_cell,
        RHTower.gammaSewnMobiusApertureCellMidHeight,
        gammaSewnCriticalAdjacentPrime_depthScale, c, L] <;> ring

private theorem criticalAdjacent_amplitude_bounds (e n : ℕ) (i : Fin 4) :
    0 ≤ RHTower.gammaSewnMobiusApertureBoundaryAmplitude
        ((gammaSewnOrderedPrimeDepthPlucker_cell e
          (gammaSewnCriticalAdjacentPrime_lower n)
          (gammaSewnCriticalAdjacentPrime_upper n) i).1) ∧
      RHTower.gammaSewnMobiusApertureBoundaryAmplitude
        ((gammaSewnOrderedPrimeDepthPlucker_cell e
          (gammaSewnCriticalAdjacentPrime_lower n)
          (gammaSewnCriticalAdjacentPrime_upper n) i).1) ≤
        2 * Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) /
          (gammaSewnCriticalAdjacentPrime_lower n : ℝ) := by
  let p := gammaSewnCriticalAdjacentPrime_lower n
  let q := gammaSewnCriticalAdjacentPrime_upper n
  let L := Real.log (p : ℝ)
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hq : 0 < (q : ℝ) := by exact_mod_cast q.2.pos
  have hL : 0 < L := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hpq : (p : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (gammaSewnCriticalAdjacentPrime_order n).le
  have hlogq : Real.log (q : ℝ) ≤ 2 * L :=
    criticalAdjacent_log_upper_le_two_lower n
  have hpden : 0 < (p : ℝ) + 1 := by positivity
  have hqden : 0 < (q : ℝ) + 1 := by positivity
  have hpAmp : 0 ≤ Real.log (p : ℝ) / ((p : ℝ) + 1) ∧
      Real.log (p : ℝ) / ((p : ℝ) + 1) ≤ 2 * L / (p : ℝ) := by
    constructor
    · positivity
    · rw [div_le_div_iff₀ hpden hp]
      dsimp [L]
      nlinarith
  have hqAmp : 0 ≤ Real.log (q : ℝ) / ((q : ℝ) + 1) ∧
      Real.log (q : ℝ) / ((q : ℝ) + 1) ≤ 2 * L / (p : ℝ) := by
    constructor
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast q.2.one_le)) hqden.le
    · rw [div_le_div_iff₀ hqden hp]
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) hL.le]
  fin_cases i <;>
    simp [gammaSewnOrderedPrimeDepthPlucker_cell,
      gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq] <;>
    first | exact hpAmp | exact hqAmp

private theorem criticalAdjacent_rawWeight_le (e n : ℕ) (s : Fin 6) :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight gammaSewnCriticalAdjacentPrime_aperture
        (gammaSewnOrderedPrimeDepthPlucker_rate e
          (gammaSewnCriticalAdjacentPrime_lower n)
          (gammaSewnCriticalAdjacentPrime_upper n))
        (gammaSewnOrderedPrimeDepthPlucker_cell e
          (gammaSewnCriticalAdjacentPrime_lower n)
          (gammaSewnCriticalAdjacentPrime_upper n)) s ≤
      9216 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
          gammaSewnCriticalAdjacentPrime_gap ^ 4 *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 2 /
          (gammaSewnCriticalAdjacentPrime_depthScale e ^ 2 *
            (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 4)) := by
  let p := gammaSewnCriticalAdjacentPrime_lower n
  let q := gammaSewnCriticalAdjacentPrime_upper n
  let c := gammaSewnCriticalAdjacentPrime_depthScale e
  let L := Real.log (p : ℝ)
  let rate := gammaSewnOrderedPrimeDepthPlucker_rate e p q
  let cell := gammaSewnOrderedPrimeDepthPlucker_cell e p q
  let i := RHTower.fourRatePairLeft s
  let j := RHTower.fourRatePairRight s
  have hc : 0 < c := gammaSewnCriticalAdjacentPrime_depthScale_pos e
  have hL : 0 < L := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hi := criticalAdjacent_rate_bounds e n i
  have hj := criticalAdjacent_rate_bounds e n j
  have hgapRate : gammaSewnCriticalAdjacentPrime_aperture +
      gammaSewnCriticalAdjacentPrime_gap ≤ c * L := by
    have hlog2 : Real.log 2 ≤ L :=
      Real.strictMonoOn_log.monotoneOn (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show 0 < (p : ℝ) by exact_mod_cast p.2.pos)
        (by exact_mod_cast p.2.two_le)
    have hcHalf : (1 / 2 : ℝ) ≤ c := by
      have he : (0 : ℝ) ≤ (e : ℝ) := by positivity
      dsimp [c, gammaSewnCriticalAdjacentPrime_depthScale]
      linarith
    dsimp [gammaSewnCriticalAdjacentPrime_gap]
    nlinarith [mul_le_mul hcHalf hlog2 (Real.log_pos (by norm_num)).le (by positivity)]
  have hplucker := criticalAdjacent_twoBoundaryPluckerSq_le hc hL
    hi.1 hj.1 hi.2 hj.2 hgapRate
  have hampi := criticalAdjacent_amplitude_bounds e n i
  have hampj := criticalAdjacent_amplitude_bounds e n j
  have hboundAmp :
      (RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell i).1 *
        RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell j).1) ^ 2 ≤
        16 * L ^ 4 / (p : ℝ) ^ 4 := by
    have hi' : 0 ≤ RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell i).1 ∧
        RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell i).1 ≤ 2 * L / (p : ℝ) := by
      simpa [cell, gammaSewnOrderedPrimeDepthPlucker_cell] using hampi
    have hj' : 0 ≤ RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell j).1 ∧
        RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell j).1 ≤ 2 * L / (p : ℝ) := by
      simpa [cell, gammaSewnOrderedPrimeDepthPlucker_cell] using hampj
    have hprod : RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell i).1 *
        RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell j).1 ≤
        (2 * L / (p : ℝ)) ^ 2 := by
      simpa [pow_two] using mul_le_mul hi'.2 hj'.2 hj'.1 (by positivity)
    have hsquare := (sq_le_sq₀
      (mul_nonneg hi'.1 hj'.1) (sq_nonneg (2 * L / (p : ℝ)))).2 hprod
    calc
      _ ≤ ((2 * L / (p : ℝ)) ^ 2) ^ 2 := hsquare
      _ = 16 * L ^ 4 / (p : ℝ) ^ 4 := by field_simp [hp.ne']; ring
  unfold RHTower.gammaSewnFourRateBoundaryPairRawWeight
  change RHTower.twoBoundaryCauchyPairPluckerSq
      gammaSewnCriticalAdjacentPrime_aperture (rate i) (rate j) *
      (RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell i).1 *
        RHTower.gammaSewnMobiusApertureBoundaryAmplitude (cell j).1) ^ 2 ≤ _
  have hplucker0 : 0 ≤ RHTower.twoBoundaryCauchyPairPluckerSq
      gammaSewnCriticalAdjacentPrime_aperture (rate i) (rate j) := sq_nonneg _
  calc
    _ ≤ (576 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
          (gammaSewnCriticalAdjacentPrime_gap ^ 4 * c ^ 2 * L ^ 2)) *
        (16 * L ^ 4 / (p : ℝ) ^ 4) :=
      mul_le_mul hplucker hboundAmp (sq_nonneg _) (by positivity)
    _ = _ := by
      dsimp [c, L, p]
      field_simp [gammaSewnCriticalAdjacentPrime_gap_pos.ne', hc.ne', hL.ne', hp.ne']
      ring

def gammaSewnCriticalAdjacentPrime_Partition (e n : ℕ) : ℝ :=
  gammaSewnCriticalPrimeDepthPacket_Partition e
    (gammaSewnCriticalAdjacentPrime_lower n)
    (gammaSewnCriticalAdjacentPrime_upper n)

def gammaSewnCriticalAdjacentPrime_Mean (e n : ℕ) : ℝ :=
  gammaSewnCriticalPrimeDepthPacket_Mean e
    (gammaSewnCriticalAdjacentPrime_lower n)
    (gammaSewnCriticalAdjacentPrime_upper n)

def gammaSewnCriticalAdjacentPrime_Total (e n : ℕ) : ℝ :=
  gammaSewnCriticalPrimeDepthPacket_Total e
    (gammaSewnCriticalAdjacentPrime_lower n)
    (gammaSewnCriticalAdjacentPrime_upper n)

theorem gammaSewnCriticalAdjacentPrime_Partition_pos (e n : ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_Partition e n := by
  exact gammaSewnCriticalPrimeDepthPacket_Partition_pos
    (gammaSewnCriticalAdjacentPrime_order n)

theorem gammaSewnCriticalAdjacentPrime_Total_pos (e n : ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_Total e n :=
  gammaSewnCriticalPrimeDepthPacket_Total_pos e _ _

private theorem criticalAdjacent_partition_le (e n : ℕ) :
    gammaSewnCriticalAdjacentPrime_Partition e n ≤
      55296 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
          gammaSewnCriticalAdjacentPrime_gap ^ 4 *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 2 /
          (gammaSewnCriticalAdjacentPrime_depthScale e ^ 2 *
            (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 4)) := by
  let B := 9216 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
      gammaSewnCriticalAdjacentPrime_gap ^ 4 *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 2 /
          (gammaSewnCriticalAdjacentPrime_depthScale e ^ 2 *
            (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 4))
  have hB (s : Fin 6) :
      RHTower.gammaSewnFourRateBoundaryPairRawWeight gammaSewnCriticalAdjacentPrime_aperture
          (gammaSewnOrderedPrimeDepthPlucker_rate e
            (gammaSewnCriticalAdjacentPrime_lower n)
            (gammaSewnCriticalAdjacentPrime_upper n))
          (gammaSewnOrderedPrimeDepthPlucker_cell e
            (gammaSewnCriticalAdjacentPrime_lower n)
            (gammaSewnCriticalAdjacentPrime_upper n)) s ≤ B := by
    simpa [B] using criticalAdjacent_rawWeight_le e n s
  unfold gammaSewnCriticalAdjacentPrime_Partition
    gammaSewnCriticalPrimeDepthPacket_Partition
  simp [Fin.sum_univ_succ]
  have h0 := hB 0
  have h1 := hB 1
  have h2 := hB 2
  have h3 := hB 3
  have h4 := hB 4
  have h5 := hB 5
  calc
    _ ≤ 6 * B := by linarith
    _ = _ := by dsimp [B]; ring

private theorem criticalAdjacent_total_le (e n : ℕ) :
    gammaSewnCriticalAdjacentPrime_Total e n ≤
      (20 / 3 : ℝ) * Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 2 := by
  let L := Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ)
  let U := Real.log (gammaSewnCriticalAdjacentPrime_upper n : ℝ)
  have hL : 0 < L := Real.log_pos (by
    exact_mod_cast (gammaSewnCriticalAdjacentPrime_lower n).2.one_lt)
  have hU : 0 < U := Real.log_pos (by
    exact_mod_cast (gammaSewnCriticalAdjacentPrime_upper n).2.one_lt)
  have hUL : U ≤ 2 * L := criticalAdjacent_log_upper_le_two_lower n
  have hsq : U ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  unfold gammaSewnCriticalAdjacentPrime_Total
    gammaSewnCriticalPrimeDepthPacket_Total
    RHTower.gammaSewnFourRateTotalFisher RHTower.fourRateTotalSum
    RHTower.gammaSewnMobiusApertureBoundaryFisherClock
  simp [gammaSewnOrderedPrimeDepthPlucker_cell]
  dsimp [L, U] at hsq ⊢
  nlinarith

def gammaSewnCriticalAdjacentPrime_DenominatorTerm (z : ℕ × ℕ) : ℝ :=
  gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
    gammaSewnCriticalAdjacentPrime_Total z.1 z.2

def gammaSewnCriticalAdjacentPrime_NumeratorTerm (z : ℕ × ℕ) : ℝ :=
  gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
    gammaSewnCriticalAdjacentPrime_Mean z.1 z.2

theorem gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos (z : ℕ × ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_DenominatorTerm z := by
  exact mul_pos (gammaSewnCriticalAdjacentPrime_Partition_pos z.1 z.2)
    (gammaSewnCriticalAdjacentPrime_Total_pos z.1 z.2)

theorem criticalAdjacent_denominatorTerm_le (z : ℕ × ℕ) :
    gammaSewnCriticalAdjacentPrime_DenominatorTerm z ≤
      (368640 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
          gammaSewnCriticalAdjacentPrime_gap ^ 4) *
        (1 / gammaSewnCriticalAdjacentPrime_depthScale z.1 ^ 2) *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 4 /
          (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 4) := by
  have hP := criticalAdjacent_partition_le z.1 z.2
  have hT := criticalAdjacent_total_le z.1 z.2
  have hP0 := (gammaSewnCriticalAdjacentPrime_Partition_pos z.1 z.2).le
  have hT0 := (gammaSewnCriticalAdjacentPrime_Total_pos z.1 z.2).le
  unfold gammaSewnCriticalAdjacentPrime_DenominatorTerm
  calc
    _ ≤ (55296 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
          gammaSewnCriticalAdjacentPrime_gap ^ 4 *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2 /
          (gammaSewnCriticalAdjacentPrime_depthScale z.1 ^ 2 *
            (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 4))) *
        ((20 / 3 : ℝ) *
          Real.log (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2) :=
      mul_le_mul hP hT hT0 (by positivity)
    _ = _ := by
      have hc := gammaSewnCriticalAdjacentPrime_depthScale_pos z.1
      have hp : 0 < (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) := by
        exact_mod_cast (gammaSewnCriticalAdjacentPrime_lower z.2).2.pos
      field_simp [gammaSewnCriticalAdjacentPrime_gap_pos.ne', hc.ne', hp.ne']
      ring

private theorem summable_criticalAdjacent_depthMajor :
    Summable (fun e : ℕ =>
      1 / gammaSewnCriticalAdjacentPrime_depthScale e ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 / 2) 2).mpr
    (by norm_num : (1 : ℝ) < 2)
  refine h.congr fun e => ?_
  simp [gammaSewnCriticalAdjacentPrime_depthScale]

private theorem summable_criticalAdjacent_primeMajor :
    Summable (fun n : ℕ =>
      Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 4 /
        (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 4) := by
  have hnat := HTGeometry.summable_log_pow_div_nat_rpow 4
    (sigma := (4 : ℝ)) (by norm_num)
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ 4 / (p : ℝ) ^ 4) := by
    refine (hnat.subtype (fun n : ℕ => n.Prime)).congr fun p => ?_
    simp [Function.comp_apply]
  change Summable ((fun p : Nat.Primes =>
    Real.log (p : ℝ) ^ 4 / (p : ℝ) ^ 4) ∘ RHTower.nthPrimeSubtype)
  exact hprime.comp_injective RHTower.nthPrimeSubtype_injective

private theorem summable_criticalAdjacent_productMajor :
    Summable (fun z : ℕ × ℕ =>
      (1 / gammaSewnCriticalAdjacentPrime_depthScale z.1 ^ 2) *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 4 /
          (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 4)) := by
  let f : ℕ → ℝ := fun e =>
    1 / gammaSewnCriticalAdjacentPrime_depthScale e ^ 2
  let g : ℕ → ℝ := fun n =>
    Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 4 /
      (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 4
  have hf : Summable f := summable_criticalAdjacent_depthMajor
  have hg : Summable g := summable_criticalAdjacent_primeMajor
  rw [summable_prod_of_nonneg (fun z => mul_nonneg (by positivity) (by positivity))]
  constructor
  · intro e
    exact hg.mul_left (f e)
  · have houter : Summable (fun e => f e * ∑' n, g n) :=
      hf.mul_right (∑' n, g n)
    refine houter.congr fun e => ?_
    change f e * (∑' n, g n) = ∑' n, f e * g n
    rw [tsum_mul_left]

/-- **P-G84 trace-class survivor.**  The literal adjacent-prime physical denominator is summable
over every edge and every valuation depth. -/
theorem summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm :
    Summable gammaSewnCriticalAdjacentPrime_DenominatorTerm := by
  let C := 368640 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
    gammaSewnCriticalAdjacentPrime_gap ^ 4
  have hmajor := summable_criticalAdjacent_productMajor.mul_left C
  refine Summable.of_nonneg_of_le
    (fun z => (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos z).le)
    (fun z => ?_) hmajor
  simpa [C, mul_assoc] using criticalAdjacent_denominatorTerm_le z

theorem gammaSewnCriticalAdjacentPrime_Mean_gt_half_total (e n : ℕ) :
    (1 / 2 : ℝ) * gammaSewnCriticalAdjacentPrime_Total e n <
      gammaSewnCriticalAdjacentPrime_Mean e n := by
  exact gammaSewnCriticalPrimeDepthPacket_Mean_gt_half_total
    (gammaSewnCriticalAdjacentPrime_order n)

theorem gammaSewnCriticalAdjacentPrime_Mean_lt_total (e n : ℕ) :
    gammaSewnCriticalAdjacentPrime_Mean e n <
      gammaSewnCriticalAdjacentPrime_Total e n := by
  exact gammaSewnCriticalPrimeDepthPacket_Mean_lt_total
    (gammaSewnCriticalAdjacentPrime_order n)

theorem gammaSewnCriticalAdjacentPrime_NumeratorTerm_pos (z : ℕ × ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_NumeratorTerm z := by
  unfold gammaSewnCriticalAdjacentPrime_NumeratorTerm
  have hhalf : 0 < (1 / 2 : ℝ) * gammaSewnCriticalAdjacentPrime_Total z.1 z.2 :=
    mul_pos (by norm_num) (gammaSewnCriticalAdjacentPrime_Total_pos z.1 z.2)
  exact mul_pos (gammaSewnCriticalAdjacentPrime_Partition_pos z.1 z.2)
    (hhalf.trans (gammaSewnCriticalAdjacentPrime_Mean_gt_half_total z.1 z.2))

theorem gammaSewnCriticalAdjacentPrime_NumeratorTerm_lt_denominator (z : ℕ × ℕ) :
    gammaSewnCriticalAdjacentPrime_NumeratorTerm z <
      gammaSewnCriticalAdjacentPrime_DenominatorTerm z := by
  exact mul_lt_mul_of_pos_left
    (gammaSewnCriticalAdjacentPrime_Mean_lt_total z.1 z.2)
    (gammaSewnCriticalAdjacentPrime_Partition_pos z.1 z.2)

theorem summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm :
    Summable gammaSewnCriticalAdjacentPrime_NumeratorTerm := by
  exact Summable.of_nonneg_of_le
    (fun z => (gammaSewnCriticalAdjacentPrime_NumeratorTerm_pos z).le)
    (fun z => (gammaSewnCriticalAdjacentPrime_NumeratorTerm_lt_denominator z).le)
    summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm

def gammaSewnCriticalAdjacentPrime_LowerGapTerm (z : ℕ × ℕ) : ℝ :=
  gammaSewnCriticalAdjacentPrime_NumeratorTerm z -
    (1 / 2 : ℝ) * gammaSewnCriticalAdjacentPrime_DenominatorTerm z

def gammaSewnCriticalAdjacentPrime_UpperGapTerm (z : ℕ × ℕ) : ℝ :=
  gammaSewnCriticalAdjacentPrime_DenominatorTerm z -
    gammaSewnCriticalAdjacentPrime_NumeratorTerm z

theorem gammaSewnCriticalAdjacentPrime_LowerGapTerm_pos (z : ℕ × ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_LowerGapTerm z := by
  unfold gammaSewnCriticalAdjacentPrime_LowerGapTerm
    gammaSewnCriticalAdjacentPrime_NumeratorTerm
    gammaSewnCriticalAdjacentPrime_DenominatorTerm
  rw [show gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
        gammaSewnCriticalAdjacentPrime_Mean z.1 z.2 -
      (1 / 2 : ℝ) *
        (gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
          gammaSewnCriticalAdjacentPrime_Total z.1 z.2) =
      gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
        (gammaSewnCriticalAdjacentPrime_Mean z.1 z.2 -
          (1 / 2 : ℝ) * gammaSewnCriticalAdjacentPrime_Total z.1 z.2) by ring]
  exact mul_pos (gammaSewnCriticalAdjacentPrime_Partition_pos z.1 z.2)
    (sub_pos.mpr (gammaSewnCriticalAdjacentPrime_Mean_gt_half_total z.1 z.2))

theorem gammaSewnCriticalAdjacentPrime_UpperGapTerm_pos (z : ℕ × ℕ) :
    0 < gammaSewnCriticalAdjacentPrime_UpperGapTerm z := by
  unfold gammaSewnCriticalAdjacentPrime_UpperGapTerm
    gammaSewnCriticalAdjacentPrime_NumeratorTerm
    gammaSewnCriticalAdjacentPrime_DenominatorTerm
  rw [show gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
        gammaSewnCriticalAdjacentPrime_Total z.1 z.2 -
      gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
        gammaSewnCriticalAdjacentPrime_Mean z.1 z.2 =
      gammaSewnCriticalAdjacentPrime_Partition z.1 z.2 *
        (gammaSewnCriticalAdjacentPrime_Total z.1 z.2 -
          gammaSewnCriticalAdjacentPrime_Mean z.1 z.2) by ring]
  exact mul_pos (gammaSewnCriticalAdjacentPrime_Partition_pos z.1 z.2)
    (sub_pos.mpr (gammaSewnCriticalAdjacentPrime_Mean_lt_total z.1 z.2))

theorem summable_gammaSewnCriticalAdjacentPrime_LowerGapTerm :
    Summable gammaSewnCriticalAdjacentPrime_LowerGapTerm := by
  exact summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm.sub
    (summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.mul_left (1 / 2 : ℝ))

theorem summable_gammaSewnCriticalAdjacentPrime_UpperGapTerm :
    Summable gammaSewnCriticalAdjacentPrime_UpperGapTerm :=
  summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.sub
    summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm

/-- Cofinal adjacent-prime raw Fisher numerator. -/
def gammaSewnCriticalAdjacentPrime_CofinalNumerator : ℝ :=
  ∑' z : ℕ × ℕ, gammaSewnCriticalAdjacentPrime_NumeratorTerm z

/-- Cofinal adjacent-prime raw total-Fisher denominator. -/
def gammaSewnCriticalAdjacentPrime_CofinalDenominator : ℝ :=
  ∑' z : ℕ × ℕ, gammaSewnCriticalAdjacentPrime_DenominatorTerm z

def gammaSewnCriticalAdjacentPrime_CofinalFraction : ℝ :=
  gammaSewnCriticalAdjacentPrime_CofinalNumerator /
    gammaSewnCriticalAdjacentPrime_CofinalDenominator

theorem hasSum_gammaSewnCriticalAdjacentPrime_CofinalNumerator :
    HasSum gammaSewnCriticalAdjacentPrime_NumeratorTerm
      gammaSewnCriticalAdjacentPrime_CofinalNumerator :=
  summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm.hasSum

theorem hasSum_gammaSewnCriticalAdjacentPrime_CofinalDenominator :
    HasSum gammaSewnCriticalAdjacentPrime_DenominatorTerm
      gammaSewnCriticalAdjacentPrime_CofinalDenominator :=
  summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.hasSum

theorem gammaSewnCriticalAdjacentPrime_CofinalDenominator_pos :
    0 < gammaSewnCriticalAdjacentPrime_CofinalDenominator := by
  unfold gammaSewnCriticalAdjacentPrime_CofinalDenominator
  exact summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.tsum_pos
    (fun z => (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos z).le)
    (0, 0) (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos (0, 0))

private theorem criticalAdjacent_cofinal_lowerGap_eq :
    gammaSewnCriticalAdjacentPrime_CofinalNumerator -
        (1 / 2 : ℝ) * gammaSewnCriticalAdjacentPrime_CofinalDenominator =
      ∑' z : ℕ × ℕ, gammaSewnCriticalAdjacentPrime_LowerGapTerm z := by
  unfold gammaSewnCriticalAdjacentPrime_CofinalNumerator
    gammaSewnCriticalAdjacentPrime_CofinalDenominator
    gammaSewnCriticalAdjacentPrime_LowerGapTerm
  rw [summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm.tsum_sub
    (summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.mul_left (1 / 2 : ℝ)),
    tsum_mul_left]

private theorem criticalAdjacent_cofinal_upperGap_eq :
    gammaSewnCriticalAdjacentPrime_CofinalDenominator -
        gammaSewnCriticalAdjacentPrime_CofinalNumerator =
      ∑' z : ℕ × ℕ, gammaSewnCriticalAdjacentPrime_UpperGapTerm z := by
  unfold gammaSewnCriticalAdjacentPrime_CofinalNumerator
    gammaSewnCriticalAdjacentPrime_CofinalDenominator
    gammaSewnCriticalAdjacentPrime_UpperGapTerm
  rw [summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.tsum_sub
    summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm]

theorem gammaSewnCriticalAdjacentPrime_CofinalNumerator_gt_half_denominator :
    (1 / 2 : ℝ) * gammaSewnCriticalAdjacentPrime_CofinalDenominator <
      gammaSewnCriticalAdjacentPrime_CofinalNumerator := by
  rw [← sub_pos, criticalAdjacent_cofinal_lowerGap_eq]
  exact summable_gammaSewnCriticalAdjacentPrime_LowerGapTerm.tsum_pos
    (fun z => (gammaSewnCriticalAdjacentPrime_LowerGapTerm_pos z).le)
    (0, 0) (gammaSewnCriticalAdjacentPrime_LowerGapTerm_pos (0, 0))

theorem gammaSewnCriticalAdjacentPrime_CofinalNumerator_lt_denominator :
    gammaSewnCriticalAdjacentPrime_CofinalNumerator <
      gammaSewnCriticalAdjacentPrime_CofinalDenominator := by
  rw [← sub_pos, criticalAdjacent_cofinal_upperGap_eq]
  exact summable_gammaSewnCriticalAdjacentPrime_UpperGapTerm.tsum_pos
    (fun z => (gammaSewnCriticalAdjacentPrime_UpperGapTerm_pos z).le)
    (0, 0) (gammaSewnCriticalAdjacentPrime_UpperGapTerm_pos (0, 0))

/-- **Cofinal physical Schur interval.**  The exhaustion-independent adjacent-prime fraction is
strictly between symmetrized half depletion and total depletion. -/
theorem gammaSewnCriticalAdjacentPrime_CofinalFraction_mem :
    gammaSewnCriticalAdjacentPrime_CofinalFraction ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have hden := gammaSewnCriticalAdjacentPrime_CofinalDenominator_pos
  constructor
  · unfold gammaSewnCriticalAdjacentPrime_CofinalFraction
    exact (lt_div_iff₀ hden).2
      gammaSewnCriticalAdjacentPrime_CofinalNumerator_gt_half_denominator
  · unfold gammaSewnCriticalAdjacentPrime_CofinalFraction
    rw [div_lt_iff₀ hden]
    simpa using gammaSewnCriticalAdjacentPrime_CofinalNumerator_lt_denominator

def gammaSewnCriticalAdjacentPrime_CofinalReducedWeight
    (pk : Nat.Primes × ℕ) : ℝ :=
  (1 - gammaSewnCriticalAdjacentPrime_CofinalFraction) *
    gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk

theorem gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem
    (pk : Nat.Primes × ℕ) :
    gammaSewnCriticalAdjacentPrime_CofinalReducedWeight pk ∈
      Set.Ioo 0 ((1 / 2 : ℝ) *
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk) := by
  have hf := gammaSewnCriticalAdjacentPrime_CofinalFraction_mem
  have hw := gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk
  constructor
  · unfold gammaSewnCriticalAdjacentPrime_CofinalReducedWeight
    exact mul_pos (sub_pos.mpr hf.2) hw
  · unfold gammaSewnCriticalAdjacentPrime_CofinalReducedWeight
    nlinarith [mul_pos (sub_pos.mpr hf.1) hw]

end RHTower.HedenmalmThetaSource
