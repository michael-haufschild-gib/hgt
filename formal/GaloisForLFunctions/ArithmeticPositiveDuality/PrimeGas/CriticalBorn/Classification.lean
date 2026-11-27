import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.MovingPhase
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Tilt
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdjacentShellTrace

/-! # Uniqueness of the harmonic exponent for stationary Haar phase sampling -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

theorem cutoff_atTop : Tendsto cutoff atTop atTop := by
  rw [tendsto_atTop]
  intro n
  filter_upwards [eventually_ge_atTop (((n+2 : ℕ) : ℝ))] with x hx
  have h := (Nat.le_floor_iff ((Nat.cast_nonneg (n+2)).trans hx)).mpr hx
  unfold cutoff
  omega

/-- The first circle moment of the elementary Born law is its normalized
coherent phase sum. -/
theorem bornLaw_firstMoment (σ t x : ℝ) :
    circleMeasureMomentZ (bornLaw σ t (cutoff x) : Measure Circle) (-1) =
      firstMoment (1-2*σ) t x := by
  simp only [circleMeasureMomentZ,neg_neg,zpow_one,firstMoment,powerMass,packetSum,
    show 1-2*σ-1 = -(2*σ) by ring]
  change (∫ z : Circle, (z:ℂ) ∂(∑ p ∈ primes (cutoff x),
    (Real.toNNReal (bornWeight σ p / bornMass σ (cutoff x))) • Measure.dirac (phase t p))) =
    (bornMass σ (cutoff x))⁻¹ • ∑ p ∈ primes (cutoff x), bornWeight σ p • (phase t p : ℂ)
  rw [integral_finsetSum_measure (by
    intro p _
    exact (integrable_dirac (by finiteness)).smul_measure_nnreal),smul_sum]
  apply sum_congr rfl
  intro p _
  rw [integral_smul_nnreal_measure,integral_dirac,smul_smul]
  change ((Real.toNNReal _ : ℝ) : ℂ)*(phase t p : ℂ) = _
  have ww : 0≤bornWeight σ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have den : 0≤bornMass σ (cutoff x) := sum_nonneg fun q _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Real.coe_toNNReal _ (div_nonneg ww den)]
  change (((bornWeight σ p / bornMass σ (cutoff x)) : ℝ) : ℂ)*_ =
    (((bornMass σ (cutoff x))⁻¹*bornWeight σ p : ℝ) : ℂ)*_
  rw [div_eq_inv_mul]

/-- Below the isometry line the angular Born ensemble has no weak limit
at a nonzero height, even if arbitrary limiting laws are allowed. -/
theorem subcritical_no_law {σ t : ℝ} (hσ : σ<1/2) (ht : t≠0) (μ : ProbabilityMeasure Circle) :
    ¬Tendsto (bornLaw σ t) atTop (𝓝 μ) := by
  intro h
  have first := ((continuous_circleMeasureMomentZ (-1)).tendsto μ).comp (h.comp cutoff_atTop)
  apply subcritical_no_first_moment (by linarith only [hσ] : 0<1-2*σ) ht
    (circleMeasureMomentZ (μ : Measure Circle) (-1))
  simpa only [Function.comp_def,bornLaw_firstMoment] using first

/-- A single nonzero clock height singles out the critical exponent
among all real exponents by convergence to uniform phase. -/
theorem haar_iff_half (σ : ℝ) {t : ℝ} (ht : t≠0) :
    Tendsto (bornLaw σ t) atTop (𝓝 uniform) ↔ σ=1/2 := by
  constructor
  · intro h
    rcases lt_trichotomy σ (1/2) with lo | eq | hi
    · exact (subcritical_no_law lo ht uniform h).elim
    · exact eq
    · exact (supercritical_not_haar hi t h).elim
  · rintro rfl
    simpa only [show bornLaw (1/2) t = phaseLaw t from funext (bornLaw_half t)] using phase_limit t ht

/-- The sampling power is the squared physical heat amplitude of one prime excitation. -/
theorem bornWeight_eq_heat (s : ℂ) (p : Nat.Primes) :
    bornWeight s.re p.val = ‖heat s (label (Finsupp.single p 1))‖^2 := by
  rw [bornWeight,norm_heat,energy,label_one_quantum,sq,←Real.exp_add,
    Real.rpow_def_of_pos (Nat.cast_pos.mpr p.property.pos)]
  congr 1
  ring

/-- Elementary phase equidistribution at a single nonzero clock height
is equivalent to isometric composition on the entire occupation space. -/
theorem elementary_haar_iff_split (s : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (bornLaw s.re t) atTop (𝓝 uniform) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  (haar_iff_half s.re ht).trans (split_isometric_iff s).symm

/-- RH asks whether weights supplied by every strip zero make the elementary
phases Haar distributed at the single clock height one. -/
theorem rh_iff_unit_clock :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 →
      Tendsto (bornLaw s.val.re 1) atTop (𝓝 uniform) := by
  rw [rh_iff_trace_zero_forces_isometry]
  exact ⟨fun h s hz => (elementary_haar_iff_split s.val one_ne_zero).mpr
    (h s ((adjacentTrace_zero_iff s).mpr hz)),
    fun h s hz => (elementary_haar_iff_split s.val one_ne_zero).mp
      (h s ((adjacentTrace_zero_iff s).mp hz))⟩

#print axioms cutoff_atTop
#print axioms rh_iff_unit_clock
#print axioms bornWeight_eq_heat
#print axioms elementary_haar_iff_split
#print axioms bornLaw_firstMoment
#print axioms subcritical_no_law
#print axioms haar_iff_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
