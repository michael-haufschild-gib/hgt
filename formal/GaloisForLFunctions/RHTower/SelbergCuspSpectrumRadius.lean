/-
# The cusp--spectrum radius law for an extended Selberg-class member

The shift-lattice machinery is stated for an abstract coefficient family with a polynomial bound.
An extended Selberg-class carrier supplies that bound from its own axioms: absolute convergence of
the Dirichlet series to the right of one makes the terms of the series at `s = 2` a null sequence,
hence bounded, hence `‖a(n)‖ ≤ C n²`.  Nothing else about the class is used.

With the bound in hand the whole interior layer transports: the theta function
`Φ_F(s,z) = ∑ a(n) n^{-s} e(z n^{1/d})` converges on the upper half plane for every spectral
parameter, is holomorphic there, has the shift-lattice expansion whose coefficients are the
normalised shifts `F_{z₀}(s - k/d)/k!`, and its growth functional is at most `1/(2π Im z₀)` with
equality exactly when the boundary point below `z₀` is a genuine singularity.  The arithmetic side
transports too: the standard-twist spectrum of `F` is the shift spectrum of its coefficients, and
the cusp gap is `d q^{-1/d}` for the presentation degree and conductor.

Main results:
* `ExtendedSelbergClass.exists_coeff_bound` — the coefficients are polynomially bounded.
* `ExtendedSelbergClass.analyticAt_theta` — `Φ_F(s,·)` is holomorphic on the upper half plane.
* `ExtendedSelbergClass.hasSum_shiftLatticeExpansion` — the shift-lattice expansion.
* `ExtendedSelbergClass.hadamardLimsup_shiftCoeff_le` — the unconditional half of the boxed law.
* `ExtendedSelbergClass.hadamardLimsup_shiftCoeff_eq`, `radius_shiftLattice_eq` — the boxed law at
  an interior base point.
* `ExtendedSelbergClass.infDist_zero_shiftSpectrum`, `cuspConstant_eq` — the cusp gap and constant.
-/
import GaloisForLFunctions.HTGeometry.CuspGapUnconditionalInstances
import GaloisForLFunctions.RHTower.SelbergClass.Basic

open GaloisForLFunctions.HTGeometry Complex

noncomputable section

namespace RHTower

namespace ExtendedSelbergClass

/-- **The coefficients of an extended Selberg-class member are polynomially bounded.**  Absolute
convergence at `s = 2` makes the terms a null sequence, hence bounded. -/
theorem exists_coeff_bound (F : ExtendedSelbergClass) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(F.coeff n : ℂ)‖ ≤ C * (n : ℝ) ^ (2 : ℝ) := by
  have hsum : LSeriesSummable (fun n => F.coeff n) 2 := F.lSeriesSummable 2 (by norm_num)
  have hnorm : Summable fun n => ‖LSeries.term (fun n => F.coeff n) 2 n‖ := hsum.norm
  obtain ⟨C, hC⟩ := hnorm.tendsto_atTop_zero.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : (F.coeff 0 : ℂ) = 0 := ArithmeticFunction.map_zero
    rw [hz, norm_zero, Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
  · have hle : ‖LSeries.term (fun m => F.coeff m) 2 n‖ ≤ C := hC (Set.mem_range_self n)
    rw [LSeries.norm_term_eq, if_neg hn.ne'] at hle
    have hpos : (0 : ℝ) < (n : ℝ) ^ ((2 : ℂ).re) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    rw [div_le_iff₀ hpos] at hle
    simpa using hle

/-- The theta function `Φ_F(s,z) = ∑_{n≥1} a(n) n^{-s} e(z n^{1/d})` of a class member. -/
def theta (F : ExtendedSelbergClass) (s z : ℂ) : ℂ :=
  thetaSeries (fun n => F.coeff n) F.presentationDegree s z

/-- The shift-lattice coefficients `Φ_F(s - k/d, z₀)/k!`. -/
def shiftCoeff (F : ExtendedSelbergClass) (s z₀ : ℂ) (k : ℕ) : ℂ :=
  shiftLatticeCoeff (fun n => F.coeff n) F.presentationDegree s z₀ k

/-- The standard-twist spectrum `{ d (m/q)^{1/d} : a(m) ≠ 0 }`. -/
def shiftSpectrum (F : ExtendedSelbergClass) : Set ℝ :=
  GaloisForLFunctions.HTGeometry.shiftSpectrum (fun n => F.coeff n)
    F.presentationDegree F.presentationConductor

/-- **The theta series converges absolutely on the upper half plane**, for every spectral
parameter. -/
theorem summable_thetaTerm (F : ExtendedSelbergClass) (hd : 0 < F.presentationDegree)
    (s z : ℂ) (hz : 0 < z.im) :
    Summable fun n => thetaTerm (fun n => F.coeff n) F.presentationDegree s z n := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  exact summable_thetaTerm_of_im_pos hC hd s z hz

/-- **`Φ_F(s,·)` is holomorphic on the upper half plane.** -/
theorem analyticAt_theta (F : ExtendedSelbergClass) (hd : 0 < F.presentationDegree)
    (s z₀ : ℂ) (hz : 0 < z₀.im) : AnalyticAt ℂ (fun z => F.theta s z) z₀ := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  exact analyticAt_thetaSeries hC hd s z₀ hz

/-- **The shift-lattice expansion** of the theta function at an interior base point. -/
theorem hasSum_shiftLatticeExpansion (F : ExtendedSelbergClass)
    (hd : 0 < F.presentationDegree) (s z₀ ζ : ℂ) (hζ : ‖ζ‖ < z₀.im) :
    HasSum (fun k => (shiftFactor * ζ) ^ k * F.shiftCoeff s z₀ k) (F.theta s (z₀ + ζ)) := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  exact _root_.GaloisForLFunctions.HTGeometry.hasSum_shiftLatticeExpansion hC hd s z₀ ζ hζ

/-- **The unconditional half of the boxed law**: the growth functional of the shift lattice is at
most the reciprocal of `2π` times the height. -/
theorem hadamardLimsup_shiftCoeff_le (F : ExtendedSelbergClass)
    (hd : 0 < F.presentationDegree) (s z₀ : ℂ) (hz : 0 < z₀.im) :
    hadamardLimsup (F.shiftCoeff s z₀) ≤ ENNReal.ofReal (1 / (2 * Real.pi * z₀.im)) := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  exact hadamardLimsup_shiftLatticeCoeff_le hC hd s z₀ hz

/-- **The boxed law at an interior base point**: with a genuine singularity below, the growth
functional is exactly `1/(2π Im z₀)`. -/
theorem hadamardLimsup_shiftCoeff_eq (F : ExtendedSelbergClass)
    (hd : 0 < F.presentationDegree) (s z₀ : ℂ) (hz : 0 < z₀.im)
    (hsing : ∀ R' : ℝ, z₀.im < R' →
      ¬ ∃ g, AnalyticOnNhd ℂ g (Metric.ball z₀ R') ∧
        ∀ z ∈ Metric.ball z₀ z₀.im, g z = F.theta s z) :
    hadamardLimsup (F.shiftCoeff s z₀) = ENNReal.ofReal (1 / (2 * Real.pi * z₀.im)) := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  exact hadamardLimsup_shiftLatticeCoeff_eq hC hd s z₀ hz hsing

/-- **The radius of the shift-lattice expansion is exactly the height**, given a singularity. -/
theorem radius_shiftLattice_eq (F : ExtendedSelbergClass)
    (hd : 0 < F.presentationDegree) (s z₀ : ℂ) (hz : 0 < z₀.im)
    (hsing : ∀ R' : ℝ, z₀.im < R' →
      ¬ ∃ g, AnalyticOnNhd ℂ g (Metric.ball z₀ R') ∧
        ∀ z ∈ Metric.ball z₀ z₀.im, g z = F.theta s z) :
    (FormalMultilinearSeries.ofScalars ℂ
        fun k => shiftFactor ^ k * F.shiftCoeff s z₀ k).radius = ENNReal.ofReal z₀.im := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  exact _root_.GaloisForLFunctions.HTGeometry.radius_shiftLattice_eq hC hd s z₀ hz hsing

/-- **The cusp gap of a class member is `d q^{-1/d}`**, for the presentation degree and
conductor. -/
theorem infDist_zero_shiftSpectrum (F : ExtendedSelbergClass) (h1 : (F.coeff 1 : ℂ) ≠ 0)
    (hd : 0 < F.presentationDegree) :
    Metric.infDist 0 F.shiftSpectrum
      = F.presentationDegree * F.presentationConductor ^ (-(1 / F.presentationDegree)) :=
  _root_.GaloisForLFunctions.HTGeometry.infDist_zero_shiftSpectrum h1 hd
    F.gammaData.conductor_pos

/-- **The cusp constant of a class member is `q^{1/d}/(2πd)`.** -/
theorem cuspConstant_eq (F : ExtendedSelbergClass) (hd : 0 < F.presentationDegree) :
    1 / (2 * Real.pi *
        (F.presentationDegree * F.presentationConductor ^ (-(1 / F.presentationDegree))))
      = F.presentationConductor ^ (1 / F.presentationDegree)
        / (2 * Real.pi * F.presentationDegree) :=
  cusp_constant_eq hd F.gammaData.conductor_pos

/-- **The cusp case of the boxed law for a class member**: at an interior base point of height the
cusp gap, the growth functional is the cusp constant. -/
theorem hadamardLimsup_shiftCoeff_cusp (F : ExtendedSelbergClass)
    (h1 : (F.coeff 1 : ℂ) ≠ 0) (hd : 0 < F.presentationDegree) (s z₀ : ℂ)
    (hz : z₀.im = Metric.infDist 0 F.shiftSpectrum)
    (hsing : ∀ R' : ℝ, z₀.im < R' →
      ¬ ∃ g, AnalyticOnNhd ℂ g (Metric.ball z₀ R') ∧
        ∀ z ∈ Metric.ball z₀ z₀.im, g z = F.theta s z) :
    hadamardLimsup (F.shiftCoeff s z₀)
      = ENNReal.ofReal (F.presentationConductor ^ (1 / F.presentationDegree)
          / (2 * Real.pi * F.presentationDegree)) := by
  have hgap : Metric.infDist 0 F.shiftSpectrum
      = F.presentationDegree * F.presentationConductor ^ (-(1 / F.presentationDegree)) :=
    F.infDist_zero_shiftSpectrum h1 hd
  have hpos : 0 < z₀.im := by
    rw [hz, hgap]
    exact mul_pos hd (Real.rpow_pos_of_pos F.gammaData.conductor_pos _)
  rw [F.hadamardLimsup_shiftCoeff_eq hd s z₀ hpos hsing, hz, hgap, F.cuspConstant_eq hd]

end ExtendedSelbergClass

end RHTower
