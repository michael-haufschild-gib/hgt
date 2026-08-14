import GaloisForLFunctions.HTGeometry.BohrOrbitClosure
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier

/-!
# The two-frequency phase clock

Two positive frequencies with irrational ratio are rationally independent, so the continuous phase
flow `t ↦ (t a, t b) mod 2π` has dense forward tails in the two-torus.  Steering the pair of phases
to a prescribed target therefore succeeds at arbitrarily late times, and reading the imaginary parts
gives a *clock*: a sequence of times tending to infinity along which the two sines converge to any
prescribed pair of values in the closed unit interval that is realised by a pair of angles.

The two clocks used by a boundary trace are the targets `(1, 0)` and `(0, 1)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **Two frequencies with irrational ratio are integrally independent.** -/
theorem linearIndependent_pair_of_irrational {a b : ℝ} (hb : b ≠ 0)
    (h : Irrational (a / b)) : LinearIndependent ℤ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro m n hmn
  have hmn' : (m : ℝ) * a + (n : ℝ) * b = 0 := by
    simpa [zsmul_eq_mul] using hmn
  by_cases hm : m = 0
  · subst hm
    refine ⟨rfl, ?_⟩
    have : (n : ℝ) * b = 0 := by simpa using hmn'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hb
  · exfalso
    have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hval : a / b = ((-n / m : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith [hmn']
    exact h ⟨(-n / m : ℚ), hval.symm⟩

/-- **The converse: independent frequencies have irrational ratio.** -/
theorem irrational_div_of_linearIndependent_pair {a b : ℝ} (h : LinearIndependent ℤ ![a, b]) :
    Irrational (a / b) := by
  rw [LinearIndependent.pair_iff] at h
  have hb : b ≠ 0 := by
    intro hb0
    have := (h 0 1 (by simp [hb0])).2
    exact absurd this one_ne_zero
  rintro ⟨c, hc⟩
  have ha : a = (c : ℝ) * b := by
    field_simp at hc
    linarith [hc]
  have hden : ((c.den : ℤ) : ℝ) * a + (-(c.num : ℤ) : ℤ) • b = 0 := by
    rw [ha]
    push_cast
    rw [Rat.cast_def]
    field_simp
    push_cast [zsmul_eq_mul]
    ring
  have hzero := (h (c.den : ℤ) (-(c.num : ℤ)) (by
    simpa [zsmul_eq_mul] using hden)).1
  have : (c.den : ℤ) ≠ 0 := by exact_mod_cast c.den_nz
  exact this hzero

/-- The corresponding rational independence of the pair, in the form the torus flow needs. -/
theorem rationallyIndependentSequence_pair {a b : ℝ} (hb : b ≠ 0)
    (h : Irrational (a / b)) : RationallyIndependentSequence ![a, b] :=
  rationallyIndependentSequence_of_linearIndependent_int
    (linearIndependent_pair_of_irrational hb h)

/-- The circle phase flow of a frequency family is the elementary phase. -/
theorem circlePhaseFlow_coe {ι : Type*} (omega : ι → ℝ) (t : ℝ) (i : ι) :
    ((circlePhaseFlow omega t i : Circle) : ℂ) = Complex.exp (((t * omega i : ℝ) : ℂ) * Complex.I) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [circlePhaseFlow, AddCircle.homeomorphCircle_apply, clockPhasePoint,
    AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 2
  field_simp

/-- **The two-frequency clock.**  For frequencies with irrational ratio, every prescribed pair of
phases is realised, to any tolerance, at arbitrarily late times. -/
theorem exists_forwardTime_phase_pair {a b : ℝ} (hb : b ≠ 0) (h : Irrational (a / b))
    (T₀ : ℝ) {ε : ℝ} (hε : 0 < ε) (θ η : ℝ) :
    ∃ t : ℝ, T₀ ≤ t ∧
      ‖Complex.exp (((t * a : ℝ) : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)‖ < ε ∧
      ‖Complex.exp (((t * b : ℝ) : ℂ) * Complex.I) - Complex.exp ((η : ℂ) * Complex.I)‖ < ε := by
  classical
  set omega : Fin 2 → ℝ := ![a, b] with homega
  have hdense := dense_forwardOrbit_circlePhaseFlow (rationallyIndependentSequence_pair hb h) T₀
  set z : Fin 2 → Circle := ![Circle.exp θ, Circle.exp η] with hz
  set U : Set (Fin 2 → Circle) :=
    {y : Fin 2 → Circle | ∀ i : Fin 2, ‖((y i : Circle) : ℂ) - ((z i : Circle) : ℂ)‖ < ε} with hU
  have hcont : ∀ i : Fin 2, Continuous fun y : Fin 2 → Circle => ((y i : Circle) : ℂ) :=
    fun i => continuous_induced_dom.comp (continuous_apply i)
  have hUopen : IsOpen U := by
    have hrw : U = ⋂ i : Fin 2,
        (fun y : Fin 2 → Circle => ((y i : Circle) : ℂ)) ⁻¹'
          (Metric.ball ((z i : Circle) : ℂ) ε) := by
      ext y
      simp [hU, Metric.mem_ball, dist_eq_norm]
    rw [hrw]
    exact isOpen_iInter_of_finite fun i => (hcont i).isOpen_preimage _ Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨z, fun i => by simpa using hε⟩
  obtain ⟨y, hyU, t, htT, hty⟩ := (dense_iff_inter_open.mp hdense) U hUopen hUne
  refine ⟨t, htT, ?_, ?_⟩
  · have := hyU 0
    rw [← hty] at this
    rw [circlePhaseFlow_coe] at this
    simpa [hz, homega] using this
  · have := hyU 1
    rw [← hty] at this
    rw [circlePhaseFlow_coe] at this
    simpa [hz, homega] using this

/-- The sine of a phase is controlled by the phase itself. -/
theorem abs_sin_sub_le_norm_exp_sub (u v : ℝ) :
    |Real.sin u - Real.sin v|
      ≤ ‖Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I)‖ := by
  have him := Complex.abs_im_le_norm
    (Complex.exp ((u : ℂ) * Complex.I) - Complex.exp ((v : ℂ) * Complex.I))
  have h1 : (Complex.exp ((u : ℂ) * Complex.I)).im = Real.sin u := by
    rw [Complex.exp_mul_I]
    simp [Complex.sin_ofReal_re]
  have h2 : (Complex.exp ((v : ℂ) * Complex.I)).im = Real.sin v := by
    rw [Complex.exp_mul_I]
    simp [Complex.sin_ofReal_re]
  rwa [Complex.sub_im, h1, h2] at him

/-- **The clock in sine form.** -/
theorem exists_forwardTime_sin_pair {a b : ℝ} (hb : b ≠ 0) (h : Irrational (a / b))
    (T₀ : ℝ) {ε : ℝ} (hε : 0 < ε) (θ η : ℝ) :
    ∃ t : ℝ, T₀ ≤ t ∧ |Real.sin (t * a) - Real.sin θ| < ε ∧ |Real.sin (t * b) - Real.sin η| < ε := by
  obtain ⟨t, htT, h1, h2⟩ := exists_forwardTime_phase_pair hb h T₀ hε θ η
  exact ⟨t, htT, lt_of_le_of_lt (abs_sin_sub_le_norm_exp_sub _ _) h1,
    lt_of_le_of_lt (abs_sin_sub_le_norm_exp_sub _ _) h2⟩

/-- **A cofinal clock sequence.**  There is a sequence of times tending to infinity along which the
two sines converge to the prescribed pair. -/
theorem exists_clock_seq {a b : ℝ} (hb : b ≠ 0) (h : Irrational (a / b)) (θ η : ℝ) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      Tendsto (fun j => Real.sin (κ j * a)) atTop (𝓝 (Real.sin θ)) ∧
      Tendsto (fun j => Real.sin (κ j * b)) atTop (𝓝 (Real.sin η)) := by
  have hpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := by
    intro j
    positivity
  choose κ hκT hκa hκb using fun j : ℕ =>
    exists_forwardTime_sin_pair hb h (j : ℝ) (hpos j) θ η
  have hsmall : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨κ, tendsto_atTop_mono hκT tendsto_natCast_atTop_atTop, ?_, ?_⟩
  · have hz : Tendsto (fun j : ℕ => Real.sin (κ j * a) - Real.sin θ) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun j => ?_) hsmall
      rw [Real.norm_eq_abs]
      exact (hκa j).le
    simpa using hz.add_const (Real.sin θ)
  · have hz : Tendsto (fun j : ℕ => Real.sin (κ j * b) - Real.sin η) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun j => ?_) hsmall
      rw [Real.norm_eq_abs]
      exact (hκb j).le
    simpa using hz.add_const (Real.sin η)

end GaloisForLFunctions.HTGeometry
