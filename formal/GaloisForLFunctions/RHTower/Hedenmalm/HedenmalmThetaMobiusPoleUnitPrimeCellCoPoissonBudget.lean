import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPoleUnitPrimeCellBoundaryLayer
import GaloisForLFunctions.RHTower.MobiusGammaCoPoissonPrimePowerBoundary
import GaloisForLFunctions.RHTower.EulerActivationSubcriticalOccupancy

/-!
# Gamma/co-Poisson budget of the Route-P prime-cell boundary layer

P-G47 asks for an independently created negative principal symbol on each labelled running Euler
cell.  The existing primitive Gamma/co-Poisson current supplies it exactly: at prime `p` and source
grade `s = 1 + x epsilon`, its grade-one term is `-p^{-s}`, the negative P-G47 running odds.

The cancellation is not yet annihilation.  At finite thermal ratio, the primitive charge splits
into the Julia defect and a strictly positive complement.  The complement is summable over all
primes at every interior source aperture and vanishes at the cold end.  Thus the harmonic
principal obstruction is removed coefficientwise before completion, and the remaining Route-P
gap is localized to a positive midpoint-order Euler--Gamma complement.
-/

open Complex Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- The existing primitive Gamma/co-Poisson grade-one term is exactly the negative running odds
of a literal Route-P source prime. -/
theorem eulerGammaCoPoissonPrimitiveTerm_prime_runningOdds
    (p : Nat.Primes) (x epsilon : ℝ) :
    RHTower.eulerGammaCoPoissonPrimitiveTerm p ((1 + x * epsilon : ℝ) : ℂ) =
      -(thermalBernoulliRunningOdds ((p : ℝ) ^ (-1 : ℝ))
        (x * epsilon * Real.log (p : ℝ)) : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [prime_boundaryLayer_effectiveOdds hp]
  rw [RHTower.eulerGammaCoPoissonPrimitiveTerm_eq p.prop.ne_zero,
    RHTower.dividedVonMangoldtCoefficient,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop,
    LSeries.term_of_ne_zero p.prop.ne_zero]
  simp only [one_div]
  have hlog : (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [div_self hlog, neg_one_mul, neg_inj]
  change (((p : ℝ) : ℂ) ^ ((1 + x * epsilon : ℝ) : ℂ))⁻¹ =
    (((p : ℝ) ^ (-(1 + x * epsilon)) : ℝ) : ℂ)
  rw [Complex.ofReal_cpow hp.le]
  rw [← Complex.cpow_neg]
  congr 2
  push_cast
  rfl

/-- Positive remainder after the primitive co-Poisson charge pays the finite Julia defect. -/
def thermalBernoulliCoPoissonComplement (q k T : ℝ) : ℝ :=
  thermalBernoulliRunningOdds q k -
    thermalBernoulliMidpointDefectOdds q
      (thermalBernoulliBoundaryLayerEccentricity k T) T

/-- Exact rational factorization of the co-Poisson complement. -/
theorem thermalBernoulliCoPoissonComplement_eq
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    thermalBernoulliCoPoissonComplement q k T =
      let a := thermalBernoulliRunningOdds q k
      a * (1 + a) * (2 * T + a - 1) / (T + a) ^ 2 := by
  have ha : 0 < thermalBernoulliRunningOdds q k :=
    thermalBernoulliRunningOdds_pos hq
  have hden : T + thermalBernoulliRunningOdds q k ≠ 0 := by linarith
  rw [thermalBernoulliCoPoissonComplement,
    thermalBernoulliBoundaryLayerDefectOdds_eq_wall hT,
    thermalBernoulliMidpointDefectOdds_one (lt_trans zero_lt_one hT).ne']
  dsimp only
  field_simp [hden]
  ring

/-- The complement is strictly positive at every finite nontrivial cell. -/
theorem thermalBernoulliCoPoissonComplement_pos
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    0 < thermalBernoulliCoPoissonComplement q k T := by
  rw [thermalBernoulliCoPoissonComplement_eq hq hT]
  dsimp only
  have ha : 0 < thermalBernoulliRunningOdds q k :=
    thermalBernoulliRunningOdds_pos hq
  exact div_pos
    (mul_pos (mul_pos ha (by linarith)) (by linarith))
    (sq_pos_of_pos (by linarith))

/-- Finite Julia defect spends strictly less than the primitive running charge. -/
theorem thermalBernoulliBoundaryLayerDefectOdds_lt_runningOdds
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    thermalBernoulliMidpointDefectOdds q
      (thermalBernoulliBoundaryLayerEccentricity k T) T <
        thermalBernoulliRunningOdds q k := by
  have hcomp := thermalBernoulliCoPoissonComplement_pos (k := k) hq hT
  rw [thermalBernoulliCoPoissonComplement] at hcomp
  linarith

/-- In the finite-coordinate cold limit the Julia defect absorbs all running co-Poisson charge. -/
theorem tendsto_thermalBernoulliCoPoissonComplement_atTop (q k : ℝ) :
    Tendsto (thermalBernoulliCoPoissonComplement q k) atTop (nhds 0) := by
  have hdefect := tendsto_thermalBernoulliBoundaryLayerDefectOdds_atTop q k
  have hconst : Tendsto (fun _ : ℝ => thermalBernoulliRunningOdds q k)
      atTop (nhds (thermalBernoulliRunningOdds q k)) := tendsto_const_nhds
  change Tendsto (fun T : ℝ => thermalBernoulliRunningOdds q k -
    thermalBernoulliMidpointDefectOdds q
      (thermalBernoulliBoundaryLayerEccentricity k T) T) atTop (nhds 0)
  simpa using hconst.sub hdefect

/-- Exact signed source budget: primitive Gamma/co-Poisson current plus Julia defect equals the
negative positive complement. -/
theorem eulerGammaCoPoissonPrimitiveTerm_add_boundaryLayerDefect
    (p : Nat.Primes) (x epsilon T : ℝ) :
    RHTower.eulerGammaCoPoissonPrimitiveTerm p ((1 + x * epsilon : ℝ) : ℂ) +
        (thermalBernoulliMidpointDefectOdds ((p : ℝ) ^ (-1 : ℝ))
          (thermalBernoulliBoundaryLayerEccentricity
            (x * epsilon * Real.log (p : ℝ)) T) T : ℝ) =
      -(thermalBernoulliCoPoissonComplement ((p : ℝ) ^ (-1 : ℝ))
        (x * epsilon * Real.log (p : ℝ)) T : ℝ) := by
  rw [eulerGammaCoPoissonPrimitiveTerm_prime_runningOdds]
  rw [thermalBernoulliCoPoissonComplement]
  push_cast
  ring

/-- Uniform elementary bound: below unit running odds, the complement gains one full thermal
factor. -/
theorem thermalBernoulliCoPoissonComplement_le_four_mul_div
    {q k T : ℝ} (hq : 0 < q)
    (ha : thermalBernoulliRunningOdds q k ≤ 1) (hT : 1 < T) :
    thermalBernoulliCoPoissonComplement q k T ≤
      4 * thermalBernoulliRunningOdds q k / T := by
  rw [thermalBernoulliCoPoissonComplement_eq hq hT]
  dsimp only
  let a := thermalBernoulliRunningOdds q k
  have ha0 : 0 < a := thermalBernoulliRunningOdds_pos hq
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hden : 0 < (T + a) ^ 2 := sq_pos_of_pos (by linarith)
  rw [div_le_iff₀ hden]
  rw [show 4 * a / T * (T + a) ^ 2 =
      (4 * a * (T + a) ^ 2) / T by ring]
  rw [le_div_iff₀ hT0]
  have hsum : 1 + a ≤ 2 := by dsimp [a]; linarith
  have hlast : 2 * T + a - 1 ≤ 2 * T := by dsimp [a]; linarith
  have hlast0 : 0 ≤ 2 * T + a - 1 := by dsimp [a]; linarith
  have hnum : a * (1 + a) * (2 * T + a - 1) ≤ 4 * a * T := by
    calc
      a * (1 + a) * (2 * T + a - 1) ≤ a * 2 * (2 * T) := by gcongr
      _ = 4 * a * T := by ring
  have hsq : T ^ 2 ≤ (T + a) ^ 2 := by nlinarith
  calc
    a * (1 + a) * (2 * T + a - 1) * T ≤ (4 * a * T) * T :=
      mul_le_mul_of_nonneg_right hnum hT0.le
    _ = 4 * a * T ^ 2 := by ring
    _ ≤ 4 * a * (T + a) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)

/-- Literal source complement is controlled by midpoint-order prime mass. -/
theorem prime_thermalBernoulliCoPoissonComplement_le
    (p : Nat.Primes) {x delta epsilon : ℝ} (hx : 0 ≤ x)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    thermalBernoulliCoPoissonComplement ((p : ℝ) ^ (-1 : ℝ))
        (x * epsilon * Real.log (p : ℝ)) ((p : ℝ) ^ (delta * epsilon)) ≤
      4 * (p : ℝ) ^ (-(1 + (x + delta) * epsilon)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hq : 0 < (p : ℝ) ^ (-1 : ℝ) := Real.rpow_pos_of_pos hp _
  have hT : 1 < (p : ℝ) ^ (delta * epsilon) :=
    Real.one_lt_rpow hp1 (mul_pos hdelta hepsilon)
  have hrun := prime_boundaryLayer_effectiveOdds
    (x := x) (epsilon := epsilon) hp
  have hrunLe : thermalBernoulliRunningOdds ((p : ℝ) ^ (-1 : ℝ))
      (x * epsilon * Real.log (p : ℝ)) ≤ 1 := by
    rw [hrun]
    exact (Real.rpow_le_one_iff_of_pos hp).2
      (Or.inl ⟨hp1.le, by linarith [mul_nonneg hx hepsilon.le]⟩)
  have hbound := thermalBernoulliCoPoissonComplement_le_four_mul_div
    hq hrunLe hT
  rw [hrun] at hbound
  calc
    thermalBernoulliCoPoissonComplement ((p : ℝ) ^ (-1 : ℝ))
          (x * epsilon * Real.log (p : ℝ)) ((p : ℝ) ^ (delta * epsilon)) ≤
        4 * (p : ℝ) ^ (-(1 + x * epsilon)) /
          (p : ℝ) ^ (delta * epsilon) := hbound
    _ = 4 * (p : ℝ) ^ (-(1 + (x + delta) * epsilon)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hp.le]
      rw [mul_assoc]
      rw [← Real.rpow_add hp]
      congr 2
      ring

/-- After the source-derived principal cancellation, the full prime complement is summable at
every interior aperture. -/
theorem summable_prime_thermalBernoulliCoPoissonComplement
    {x delta epsilon : ℝ} (hx : 0 ≤ x)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    Summable (fun p : Nat.Primes =>
      thermalBernoulliCoPoissonComplement ((p : ℝ) ^ (-1 : ℝ))
        (x * epsilon * Real.log (p : ℝ)) ((p : ℝ) ^ (delta * epsilon))) := by
  have hsigma : 1 < 1 + (x + delta) * epsilon := by
    have : 0 < x + delta := lt_of_lt_of_le hdelta (le_add_of_nonneg_left hx)
    nlinarith
  have hmajor : Summable (fun p : Nat.Primes =>
      4 * (p : ℝ) ^ (-(1 + (x + delta) * epsilon))) :=
    (RHTower.summable_prime_rpow_neg hsigma).mul_left 4
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmajor
  · exact (thermalBernoulliCoPoissonComplement_pos
      (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)
      (Real.one_lt_rpow (by exact_mod_cast p.prop.one_lt)
        (mul_pos hdelta hepsilon))).le
  · exact prime_thermalBernoulliCoPoissonComplement_le p hx hdelta hepsilon

end

end RHTower.HedenmalmThetaSource
