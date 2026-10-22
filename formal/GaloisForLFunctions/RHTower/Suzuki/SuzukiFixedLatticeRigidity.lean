import GaloisForLFunctions.RHTower.Suzuki.SuzukiCayleyPhaseLift
import GaloisForLFunctions.HTGeometry.ContinuousPhaseLiftUniqueness

/-!
# Fixed-lattice rigidity, assembled

The rigidity chain of a Suzuki carrier runs

`jets -> Donoghue probability -> m -> Theta -> phi`.

Every link is now formal.  This module assembles them.

The correspondence between a reflection-normalized continuous phase and its boundary Herglotz
function is a bijection: the phase is a continuous lift of the Cayley argument of the Herglotz
function, and both directions of the determination hold.  Consequently rigidity holds for any
carrier class in which the lattice jets determine the boundary Herglotz function — the Clark
property.

That hypothesis is necessary and cannot be weakened to the order structure: on an arbitrary
`ℝ ≃o ℝ`, even one obeying the reflection normalization, the lattice jets do *not* determine the
carrier.  See `SuzukiFixedLatticeRigidityLimit.lean`.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The boundary Herglotz function determines the normalized phase.**  Two reflection-normalized
continuous phases lifting the same boundary Herglotz function are equal. -/
theorem phase_eq_of_boundaryHerglotz_eq {φ₁ φ₂ m₁ m₂ : ℝ → ℝ}
    (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : ∀ x, φ₁ (-x) = 2 * Real.pi - φ₁ x) (hr₂ : ∀ x, φ₂ (-x) = 2 * Real.pi - φ₂ x)
    (hl₁ : ∀ x, Complex.exp ((φ₁ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₁ x : ℝ) : ℂ))
    (hl₂ : ∀ x, Complex.exp ((φ₂ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₂ x : ℝ) : ℂ))
    (hm : m₁ = m₂) : φ₁ = φ₂ := by
  refine eq_of_exp_eq_of_reflection hc₁ hc₂ hr₁ hr₂ ?_
  intro x
  rw [hl₁ x, hl₂ x, hm]

/-- **The normalized phase determines the boundary Herglotz function.**  The Cayley transform is
injective on real boundary values, so the correspondence is a bijection. -/
theorem boundaryHerglotz_eq_of_phase_eq {φ₁ φ₂ m₁ m₂ : ℝ → ℝ}
    (hl₁ : ∀ x, Complex.exp ((φ₁ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₁ x : ℝ) : ℂ))
    (hl₂ : ∀ x, Complex.exp ((φ₂ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₂ x : ℝ) : ℂ))
    (h : φ₁ = φ₂) : m₁ = m₂ := by
  funext x
  refine eq_of_cayleyOfHerglotz_ofReal_eq ?_
  rw [← hl₁ x, ← hl₂ x, h]

/-- The phase and its boundary Herglotz function determine each other. -/
theorem phase_eq_iff_boundaryHerglotz_eq {φ₁ φ₂ m₁ m₂ : ℝ → ℝ}
    (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : ∀ x, φ₁ (-x) = 2 * Real.pi - φ₁ x) (hr₂ : ∀ x, φ₂ (-x) = 2 * Real.pi - φ₂ x)
    (hl₁ : ∀ x, Complex.exp ((φ₁ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₁ x : ℝ) : ℂ))
    (hl₂ : ∀ x, Complex.exp ((φ₂ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₂ x : ℝ) : ℂ)) :
    φ₁ = φ₂ ↔ m₁ = m₂ :=
  ⟨boundaryHerglotz_eq_of_phase_eq hl₁ hl₂,
    phase_eq_of_boundaryHerglotz_eq hc₁ hc₂ hr₁ hr₂ hl₁ hl₂⟩

/-- **`(19)`, fixed-lattice rigidity, for any carrier class with a Clark reconstruction.**

`clark` is the reconstruction sending the lattice jets — the labels and the masses — to the boundary
Herglotz function.  A carrier has the Clark property when its own boundary Herglotz function is the
reconstruction of its own jets.  For such carriers, equal jets force equal phases.

The Clark hypothesis is exactly the analytic content that the order structure cannot supply: by
`not_fixedLatticeJets_determine_reflectionNormalized_carrier` it cannot be dropped, even for
reflection-normalized carriers. -/
theorem suzuki_fixedLattice_rigidity_of_clark
    {φ₁ φ₂ m₁ m₂ : ℝ → ℝ} {u₁ p₁ u₂ p₂ : ℤ → ℝ}
    (clark : (ℤ → ℝ) → (ℤ → ℝ) → (ℝ → ℝ))
    (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hr₁ : ∀ x, φ₁ (-x) = 2 * Real.pi - φ₁ x) (hr₂ : ∀ x, φ₂ (-x) = 2 * Real.pi - φ₂ x)
    (hl₁ : ∀ x, Complex.exp ((φ₁ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₁ x : ℝ) : ℂ))
    (hl₂ : ∀ x, Complex.exp ((φ₂ x : ℂ) * Complex.I) = cayleyOfHerglotz ((m₂ x : ℝ) : ℂ))
    (hClark₁ : m₁ = clark u₁ p₁) (hClark₂ : m₂ = clark u₂ p₂)
    (hu : u₁ = u₂) (hp : p₁ = p₂) : φ₁ = φ₂ := by
  refine phase_eq_of_boundaryHerglotz_eq hc₁ hc₂ hr₁ hr₂ hl₁ hl₂ ?_
  rw [hClark₁, hClark₂, hu, hp]

/-! ## Oddness of the Herglotz function is the reflection normalization

The reflection normalization `phi(-t) = 2 pi - phi(t)` conjugates the inner function, and conjugating
a boundary Cayley value is the same as negating its Herglotz value.  So the normalization is exactly
the statement that the boundary Herglotz function is odd.  This is why a Suzuki spectral
configuration must be symmetric: a single atom at the origin admits no reflection-normalized lift,
while a symmetric pair does. -/

/-- Reflecting the Herglotz value inverts the boundary Cayley value. -/
theorem cayleyOfHerglotz_neg_mul_self (m : ℝ) :
    cayleyOfHerglotz ((-m : ℝ) : ℂ) * cayleyOfHerglotz ((m : ℝ) : ℂ) = 1 := by
  have hd1 : ((-m : ℝ) : ℂ) + Complex.I ≠ 0 := ofReal_add_I_ne_zero (-m)
  have hd2 : ((m : ℝ) : ℂ) + Complex.I ≠ 0 := ofReal_add_I_ne_zero m
  rw [cayleyOfHerglotz, cayleyOfHerglotz, div_mul_div_comm, div_eq_one_iff_eq
    (mul_ne_zero hd1 hd2)]
  push_cast
  ring

/-- **Oddness of the boundary Herglotz function makes the reflection normalization consistent.**
The reflected phase lifts the Cayley value of the reflected Herglotz value. -/
theorem exp_reflection_of_odd {φ m : ℝ → ℝ} (hodd : ∀ t, m (-t) = -m t)
    (hl : ∀ t, Complex.exp ((φ t : ℂ) * Complex.I) = cayleyOfHerglotz ((m t : ℝ) : ℂ)) (t : ℝ) :
    Complex.exp (((2 * Real.pi - φ t : ℝ) : ℂ) * Complex.I)
      = cayleyOfHerglotz ((m (-t) : ℝ) : ℂ) := by
  have hunit : cayleyOfHerglotz ((m t : ℝ) : ℂ) ≠ 0 := by
    rw [← hl t]
    exact Complex.exp_ne_zero _
  have hinv : cayleyOfHerglotz ((-(m t) : ℝ) : ℂ) = (cayleyOfHerglotz ((m t : ℝ) : ℂ))⁻¹ := by
    field_simp
    linear_combination cayleyOfHerglotz_neg_mul_self (m t)
  have hsplit : (((2 * Real.pi - φ t : ℝ) : ℂ)) * Complex.I
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I - ((φ t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hodd t, hinv, hsplit, Complex.exp_sub, ← hl t]
  push_cast
  rw [Complex.exp_two_pi_mul_I, one_div]

/-! ## The origin can never be an atom

At an atom the boundary Herglotz value escapes to infinity, and there the Cayley value tends to `1`.
But the reflection normalization pins the phase at the origin to `pi`, whose Cayley value is `-1`.
So no reflection-normalized carrier can have an atom at the origin — the spectral configuration must
straddle it. -/

theorem cayleyOfHerglotz_sub_one (m : ℝ) :
    cayleyOfHerglotz ((m : ℝ) : ℂ) - 1 = -(2 * Complex.I) / (((m : ℝ) : ℂ) + Complex.I) := by
  have hd := ofReal_add_I_ne_zero m
  rw [cayleyOfHerglotz, div_sub_one hd, div_eq_div_iff hd hd]
  ring

theorem norm_cayleyOfHerglotz_sub_one_le {m : ℝ} (hm : m ≠ 0) :
    ‖cayleyOfHerglotz ((m : ℝ) : ℂ) - 1‖ ≤ 2 / |m| := by
  have hd := ofReal_add_I_ne_zero m
  have hre : |(((m : ℝ) : ℂ) + Complex.I).re| ≤ ‖((m : ℝ) : ℂ) + Complex.I‖ :=
    Complex.abs_re_le_norm _
  have hrev : (((m : ℝ) : ℂ) + Complex.I).re = m := by simp
  rw [hrev] at hre
  have hmpos : 0 < |m| := abs_pos.mpr hm
  have hnpos : 0 < ‖((m : ℝ) : ℂ) + Complex.I‖ := norm_pos_iff.mpr hd
  rw [cayleyOfHerglotz_sub_one, norm_div]
  have hnum : ‖-(2 * Complex.I)‖ = 2 := by simp
  rw [hnum]
  exact div_le_div_of_nonneg_left (by norm_num) hmpos hre

/-- As the boundary Herglotz value escapes to infinity, the Cayley value tends to `1`. -/
theorem tendsto_cayleyOfHerglotz_of_abs_atTop {ι : Type*} {l : Filter ι} {m : ι → ℝ}
    (h : Filter.Tendsto (fun i => |m i|) l Filter.atTop) :
    Filter.Tendsto (fun i => cayleyOfHerglotz ((m i : ℝ) : ℂ)) l (nhds 1) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun i => 2 / |m i|) ?_ ?_
  · filter_upwards [h.eventually_gt_atTop 0] with i hi
    exact norm_cayleyOfHerglotz_sub_one_le (fun hc => by simp [hc] at hi)
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds h

/-- **A reflection-normalized carrier has no atom at the origin.** -/
theorem not_atom_at_zero_of_reflectionNormalized {φ m : ℝ → ℝ}
    (hc : Continuous φ) (hr : ∀ t, φ (-t) = 2 * Real.pi - φ t)
    (hl : ∀ t, t ≠ 0 → Complex.exp ((φ t : ℂ) * Complex.I) = cayleyOfHerglotz ((m t : ℝ) : ℂ))
    (hpole : Filter.Tendsto (fun t => |m t|) (nhdsWithin 0 ({(0 : ℝ)}ᶜ)) Filter.atTop) :
    False := by
  have hphi0 : φ 0 = Real.pi := phase_zero_of_reflection hr
  have hcont : Continuous (fun t : ℝ => Complex.exp ((φ t : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hc).mul continuous_const)
  have hL : Filter.Tendsto (fun t : ℝ => Complex.exp ((φ t : ℂ) * Complex.I))
      (nhdsWithin 0 ({(0 : ℝ)}ᶜ)) (nhds (-1)) := by
    have hbase : Filter.Tendsto (fun t : ℝ => Complex.exp ((φ t : ℂ) * Complex.I))
        (nhdsWithin 0 ({(0 : ℝ)}ᶜ)) (nhds (Complex.exp ((φ 0 : ℂ) * Complex.I))) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hval : Complex.exp ((φ 0 : ℂ) * Complex.I) = -1 := by
      rw [hphi0]
      exact Complex.exp_pi_mul_I
    rwa [hval] at hbase
  have hR : Filter.Tendsto (fun t : ℝ => cayleyOfHerglotz ((m t : ℝ) : ℂ))
      (nhdsWithin 0 ({(0 : ℝ)}ᶜ)) (nhds 1) := tendsto_cayleyOfHerglotz_of_abs_atTop hpole
  have hcongr : Filter.Tendsto (fun t : ℝ => Complex.exp ((φ t : ℂ) * Complex.I))
      (nhdsWithin 0 ({(0 : ℝ)}ᶜ)) (nhds 1) := by
    refine hR.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hl t ht).symm
  have hneq : (-1 : ℂ) = 1 := tendsto_nhds_unique hL hcongr
  norm_num at hneq

/-! ## A non-constant carrier

The rigidity hypotheses are satisfied by a carrier with a genuinely non-constant phase: the one
whose spectral mass sits entirely at the two projective endpoints, so that its boundary Herglotz
function is the identity.  Its phase is the normalized phase lift itself. -/

/-- **A non-constant reflection-normalized Clark carrier exists.**  The endpoint-concentrated
carrier has boundary Herglotz function `m(t) = t` and phase `pi + 2 arctan t`. -/
theorem exists_nonconstant_reflectionNormalized_carrier :
    ∃ φ m : ℝ → ℝ, Continuous φ ∧ (∀ t, φ (-t) = 2 * Real.pi - φ t) ∧
      (∀ t, Complex.exp ((φ t : ℂ) * Complex.I) = cayleyOfHerglotz ((m t : ℝ) : ℂ)) ∧
      (∀ t, m (-t) = -m t) ∧ φ 0 ≠ φ 1 := by
  refine ⟨cayleyPhaseLift, id, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_const.mul Real.continuous_arctan))
  · intro t
    rw [cayleyPhaseLift, cayleyPhaseLift, Real.arctan_neg]
    ring
  · intro t
    exact (cayleyOfHerglotz_ofReal t).symm
  · intro t
    rfl
  · have h0 : cayleyPhaseLift 0 = Real.pi := by
      rw [cayleyPhaseLift, Real.arctan_zero]
      ring
    have h1 : cayleyPhaseLift 1 = Real.pi + 2 * (Real.pi / 4) := by
      rw [cayleyPhaseLift, Real.arctan_one]
    rw [h0, h1]
    have := Real.pi_pos
    intro hc
    linarith

end GaloisForLFunctions.RHTower
