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

/-- Adding a third of a turn, realized on the unit interval. -/
def rot3 (t : ℝ) : ℝ := if t ≤ 2 / 3 then t + 1 / 3 else t - 2 / 3

theorem measurable_rot3 : Measurable rot3 := by
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · exact measurable_id.add_const _
  · exact measurable_id.sub_const _

/-- **The third-turn rotation preserves the uniform measure on the interval.** -/
theorem map_rot3 :
    Measure.map rot3 (volume.restrict (Set.Icc (0 : ℝ) 1))
      = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply measurable_rot3 hS, Measure.restrict_apply (measurable_rot3 hS),
    Measure.restrict_apply hS]
  have hsplit : rot3 ⁻¹' S ∩ Set.Icc (0 : ℝ) 1
      = ((fun t : ℝ => t + 1 / 3) ⁻¹' (S ∩ Set.Icc (1 / 3 : ℝ) 1))
        ∪ ((fun t : ℝ => t + (-(2 / 3) : ℝ)) ⁻¹' (S ∩ Set.Ioc (0 : ℝ) (1 / 3))) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_union, Set.mem_Icc, Set.mem_Ioc, rot3]
    constructor
    · rintro ⟨hSt, h0, h1⟩
      by_cases ht : t ≤ 2 / 3
      · rw [if_pos ht] at hSt
        exact Or.inl ⟨hSt, by linarith, by linarith⟩
      · rw [if_neg ht] at hSt
        refine Or.inr ⟨by rw [← sub_eq_add_neg]; exact hSt, by linarith [not_le.mp ht],
          by linarith⟩
    · rintro (⟨hSt, h1, h2⟩ | ⟨hSt, h1, h2⟩)
      · refine ⟨?_, by linarith, by linarith⟩
        rw [if_pos (by linarith : t ≤ 2 / 3)]
        exact hSt
      · refine ⟨?_, by linarith, by linarith⟩
        rw [if_neg (by linarith : ¬ t ≤ 2 / 3), sub_eq_add_neg]
        exact hSt
  rw [hsplit]
  have hm2 : MeasurableSet ((fun t : ℝ => t + (-(2 / 3) : ℝ)) ⁻¹' (S ∩ Set.Ioc (0 : ℝ) (1 / 3))) :=
    (MeasurableSet.inter hS measurableSet_Ioc).preimage (by fun_prop)
  have hdisj : Disjoint ((fun t : ℝ => t + 1 / 3) ⁻¹' (S ∩ Set.Icc (1 / 3 : ℝ) 1))
      ((fun t : ℝ => t + (-(2 / 3) : ℝ)) ⁻¹' (S ∩ Set.Ioc (0 : ℝ) (1 / 3))) := by
    refine Set.disjoint_left.mpr fun t h1 h2 => ?_
    have hle : t + 1 / 3 ≤ 1 := h1.2.2
    have hgt : 0 < t + -(2 / 3) := h2.2.1
    linarith
  rw [measure_union hdisj hm2, measure_preimage_add_right, measure_preimage_add_right]
  have hae1 : (S ∩ Set.Icc (1 / 3 : ℝ) 1 : Set ℝ) =ᵐ[volume] (S ∩ Set.Ioc (1 / 3 : ℝ) 1 : Set ℝ) :=
    Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ S) (Ioc_ae_eq_Icc).symm
  rw [measure_congr hae1]
  have hdisj2 : Disjoint (S ∩ Set.Ioc (1 / 3 : ℝ) 1) (S ∩ Set.Ioc (0 : ℝ) (1 / 3)) := by
    refine Set.disjoint_left.mpr fun t h1 h2 => ?_
    have := h1.2.1
    have := h2.2.2
    linarith
  rw [← measure_union hdisj2 (hS.inter measurableSet_Ioc)]
  have hunion : (S ∩ Set.Ioc (1 / 3 : ℝ) 1) ∪ (S ∩ Set.Ioc (0 : ℝ) (1 / 3))
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
      by_cases h : 1 / 3 < t
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

/-- The third-turn rotation of the whole phase space. -/
def rotOmega (ω : Omega) : Omega := fun n => rot3 (ω n)

theorem measurable_rotOmega : Measurable rotOmega :=
  measurable_pi_lambda _ fun n => measurable_rot3.comp (measurable_pi_apply n)

/-- **The rotation preserves the Steinhaus measure.** -/
theorem map_rotOmega : Measure.map rotOmega steinhausMeasure = steinhausMeasure := by
  have h := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))
    (f := fun _ : ℕ => rot3) (fun _ => measurable_rot3)
  rw [steinhausMeasure]
  rw [show rotOmega = fun (x : Omega) (i : ℕ) => rot3 (x i) from rfl, h]
  congr 1
  funext n
  exact map_rot3

theorem measure_preimage_rotOmega {A : Set Omega} (hA : MeasurableSet A) :
    steinhausMeasure (rotOmega ⁻¹' A) = steinhausMeasure A := by
  conv_rhs => rw [← map_rotOmega]
  rw [Measure.map_apply measurable_rotOmega hA]

/-- **The rotation multiplies every prime character by the cube root of unity.** -/
theorem X_rotOmega {p : ℕ} (hp : p.Prime) (ω : Omega) :
    X p (rotOmega ω) = cubeRootUnit * X p ω := by
  rw [X_prime_eq hp, X_prime_eq hp]
  have hcoord : rotOmega ω p = rot3 (ω p) := rfl
  rw [hcoord, rot3]
  by_cases h : ω p ≤ 2 / 3
  · rw [if_pos h]
    have : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((ω p + 1 / 3 : ℝ)) : ℂ)
        = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((ω p : ℝ) : ℂ)
          + ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((1 / 3 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.exp_add, cexp_two_pi_I_div_three]
    ring
  · rw [if_neg h]
    have : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((ω p - 2 / 3 : ℝ)) : ℂ)
        = (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((ω p : ℝ) : ℂ)
          + ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((1 / 3 : ℝ) : ℂ))
          + (-1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
      cexp_two_pi_I_div_three]
    ring

end GaloisForLFunctions.RHTower

end
