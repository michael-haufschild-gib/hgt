import GaloisForLFunctions.RHTower.SteinhausPrimeHolomorphic
import GaloisForLFunctions.HTGeometry.EulerLogTail

/-!
# Rotating every prime phase by a cube root of unity preserves the Steinhaus measure

The Steinhaus phase space is a countable product of copies of the unit interval with Lebesgue
measure, and the character at a prime reads one coordinate as `e^{2πi ω_p}`.  Multiplying every
phase by the primitive cube root `ω` is therefore the coordinatewise map `t ↦ t + 1/3 (mod 1)`,
which preserves the uniform measure on the interval, hence — by the product structure — the whole
Steinhaus measure.

This is the only group-theoretic input in the seam argument: it is what lets the three rotated
copies of a random phase be treated as three copies of the *same* law, so that the cube-root
cancellation of the Euler logarithm can eliminate the unknown boundary order.
-/

noncomputable section

open MeasureTheory Filter Topology Complex

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel GaloisForLFunctions.HTGeometry

/-- Adding a fraction `c` of a turn, realized on the unit interval. -/
def rotBy (c : ℝ) (t : ℝ) : ℝ := if t ≤ 1 - c then t + c else t - (1 - c)

variable {c : ℝ}

theorem measurable_rotBy (c : ℝ) : Measurable (rotBy c) := by
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · exact measurable_id.add_const _
  · exact measurable_id.sub_const _

/-- **The rotation preserves the uniform measure on the interval.** -/
theorem map_rotBy (hc0 : 0 < c) (hc1 : c < 1) :
    Measure.map (rotBy c) (volume.restrict (Set.Icc (0 : ℝ) 1))
      = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply (measurable_rotBy c) hS,
    Measure.restrict_apply ((measurable_rotBy c) hS), Measure.restrict_apply hS]
  have hsplit : rotBy c ⁻¹' S ∩ Set.Icc (0 : ℝ) 1
      = ((fun t : ℝ => t + c) ⁻¹' (S ∩ Set.Icc (c : ℝ) 1))
        ∪ ((fun t : ℝ => t + (-(1 - c) : ℝ)) ⁻¹' (S ∩ Set.Ioc (0 : ℝ) c)) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_union, Set.mem_Icc, Set.mem_Ioc, rotBy]
    constructor
    · rintro ⟨hSt, h0, h1⟩
      by_cases ht : t ≤ 1 - c
      · rw [if_pos ht] at hSt
        exact Or.inl ⟨hSt, by linarith, by linarith⟩
      · rw [if_neg ht] at hSt
        refine Or.inr ⟨by rw [← sub_eq_add_neg]; exact hSt, by linarith [not_le.mp ht],
          by linarith⟩
    · rintro (⟨hSt, h1, h2⟩ | ⟨hSt, h1, h2⟩)
      · refine ⟨?_, by linarith, by linarith⟩
        rw [if_pos (by linarith : t ≤ 1 - c)]
        exact hSt
      · refine ⟨?_, by linarith, by linarith⟩
        rw [if_neg (by linarith : ¬ t ≤ 1 - c), sub_eq_add_neg]
        exact hSt
  rw [hsplit]
  have hm2 : MeasurableSet ((fun t : ℝ => t + (-(1 - c) : ℝ)) ⁻¹' (S ∩ Set.Ioc (0 : ℝ) c)) :=
    (MeasurableSet.inter hS measurableSet_Ioc).preimage (by fun_prop)
  have hdisj : Disjoint ((fun t : ℝ => t + c) ⁻¹' (S ∩ Set.Icc (c : ℝ) 1))
      ((fun t : ℝ => t + (-(1 - c) : ℝ)) ⁻¹' (S ∩ Set.Ioc (0 : ℝ) c)) := by
    refine Set.disjoint_left.mpr fun t h1 h2 => ?_
    have hle : t + c ≤ 1 := h1.2.2
    have hgt : 0 < t + -(1 - c) := h2.2.1
    linarith
  rw [measure_union hdisj hm2, measure_preimage_add_right, measure_preimage_add_right]
  have hae1 : (S ∩ Set.Icc (c : ℝ) 1 : Set ℝ) =ᵐ[volume] (S ∩ Set.Ioc (c : ℝ) 1 : Set ℝ) :=
    Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ S) (Ioc_ae_eq_Icc).symm
  rw [measure_congr hae1]
  have hdisj2 : Disjoint (S ∩ Set.Ioc (c : ℝ) 1) (S ∩ Set.Ioc (0 : ℝ) c) := by
    refine Set.disjoint_left.mpr fun t h1 h2 => ?_
    have := h1.2.1
    have := h2.2.2
    linarith
  rw [← measure_union hdisj2 (hS.inter measurableSet_Ioc)]
  have hunion : (S ∩ Set.Ioc (c : ℝ) 1) ∪ (S ∩ Set.Ioc (0 : ℝ) c)
      = S ∩ Set.Ioc (0 : ℝ) 1 := by
    rw [← Set.inter_union_distrib_left]
    congr 1
    ext t
    simp only [Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by linarith, h2⟩
      · exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      by_cases h : c < t
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h1, not_lt.mp h⟩
  rw [hunion]
  have hae2 : (S ∩ Set.Ioc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (S ∩ Set.Icc (0 : ℝ) 1 : Set ℝ) :=
    Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ S) Ioc_ae_eq_Icc
  exact measure_congr hae2


/-! ### The rotation on the phase space -/

theorem cexp_two_pi_I_div_three :
    Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((1 / 3 : ℝ) : ℂ)) = cubeRootUnit := by
  have harg : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((1 / 3 : ℝ) : ℂ)
      = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I]
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin, cubeRootUnit]
  push_cast
  ring

/-- The rotation of the whole phase space. -/
def rotOmegaBy (c : ℝ) (ω : Omega) : Omega := fun n => rotBy c (ω n)

theorem measurable_rotOmegaBy (c : ℝ) : Measurable (rotOmegaBy c) :=
  measurable_pi_lambda _ fun n => (measurable_rotBy c).comp (measurable_pi_apply n)

/-- **The rotation preserves the Steinhaus measure.** -/
theorem map_rotOmegaBy (hc0 : 0 < c) (hc1 : c < 1) :
    Measure.map (rotOmegaBy c) steinhausMeasure = steinhausMeasure := by
  have h := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))
    (f := fun _ : ℕ => rotBy c) (fun _ => measurable_rotBy c)
  rw [steinhausMeasure]
  rw [show rotOmegaBy c = fun (x : Omega) (i : ℕ) => rotBy c (x i) from rfl, h]
  congr 1
  funext n
  exact map_rotBy hc0 hc1

theorem measure_preimage_rotOmegaBy (hc0 : 0 < c) (hc1 : c < 1) {A : Set Omega}
    (hA : MeasurableSet A) :
    steinhausMeasure (rotOmegaBy c ⁻¹' A) = steinhausMeasure A := by
  conv_rhs => rw [← map_rotOmegaBy hc0 hc1]
  rw [Measure.map_apply (measurable_rotOmegaBy c) hA]

/-- **The rotation multiplies every prime character by the corresponding root of unity.** -/
theorem X_rotOmegaBy {p : ℕ} (hp : p.Prime) (c : ℝ) (ω : Omega) :
    X p (rotOmegaBy c ω)
      = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((c : ℝ) : ℂ)) * X p ω := by
  rw [X_prime_eq hp, X_prime_eq hp]
  have hcoord : rotOmegaBy c ω p = rotBy c (ω p) := rfl
  rw [hcoord, rotBy]
  by_cases h : ω p ≤ 1 - c
  · rw [if_pos h]
    have hsum : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((ω p + c : ℝ)) : ℂ)
        = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((ω p : ℝ) : ℂ)
          + ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((c : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsum, Complex.exp_add]
    ring
  · rw [if_neg h]
    have hsum : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((ω p - (1 - c) : ℝ)) : ℂ)
        = (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((ω p : ℝ) : ℂ)
          + ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((c : ℝ) : ℂ))
          + (-1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hsum, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add]
    ring

/-! ### The two special rotations -/

/-- **The third-turn rotation multiplies every prime character by the cube root of unity.** -/
theorem X_rotOmega_third {p : ℕ} (hp : p.Prime) (ω : Omega) :
    X p (rotOmegaBy (1 / 3) ω) = cubeRootUnit * X p ω := by
  rw [X_rotOmegaBy hp, cexp_two_pi_I_div_three]

theorem cexp_two_pi_I_div_two :
    Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
  have harg : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ)
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_pi_mul_I]

/-- **The half-turn rotation flips the sign of every prime character.** -/
theorem X_rotOmega_half {p : ℕ} (hp : p.Prime) (ω : Omega) :
    X p (rotOmegaBy (1 / 2) ω) = -X p ω := by
  rw [X_rotOmegaBy hp, cexp_two_pi_I_div_two, neg_one_mul]

end GaloisForLFunctions.RHTower

end
