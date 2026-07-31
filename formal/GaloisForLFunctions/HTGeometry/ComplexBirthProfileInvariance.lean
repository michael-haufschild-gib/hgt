import GaloisForLFunctions.HTGeometry.UniversalSpectralSemigroupWallCrossingLaw

/-!
# The birth profile is attained and is an invariant

The wall-crossing regimes are stated for a mode with an exact birth profile `c g^b` on the
positive-coupling ray, and that hypothesis was never produced.  It is attained by the monomial
itself, and it is preserved by eventual equality along the ray.

More is true: the profile is *unique*.  If a mode has a birth profile at two orders, the lower
order forces the higher-order leading coefficient to be zero, which the profile forbids; so the
order and the leading coefficient are both invariants of the mode.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Attainment -/

/-- The monomial `c g^b` has birth profile `(b, c)`. -/
theorem hasComplexBirthProfile_monomial (b : ℕ) {c : ℂ} (hc : c ≠ 0) :
    HasComplexBirthProfile (fun g : ℝ => c * (g : ℂ) ^ b) b c := by
  refine ⟨?_, hc⟩
  have heq : ∀ᶠ g : ℝ in 𝓝[>] 0,
      (fun g : ℝ => c) g = c * (g : ℂ) ^ b / (g : ℂ) ^ b := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    have hg0 : (g : ℂ) ≠ 0 := by
      simpa using ne_of_gt (show (0 : ℝ) < g from hg)
    field_simp
  exact Tendsto.congr' heq tendsto_const_nhds

/-- Eventual equality along the positive ray preserves the birth profile. -/
theorem HasComplexBirthProfile.congr' {mode mode' : ℝ → ℂ} {b : ℕ} {c : ℂ}
    (h : HasComplexBirthProfile mode b c)
    (heq : mode =ᶠ[𝓝[>] 0] mode') :
    HasComplexBirthProfile mode' b c :=
  ⟨h.1.congr' (heq.mono fun g hg => by rw [hg]), h.2⟩

/-! ## Invariance -/

/-- The coordinate tends to zero along the positive ray. -/
theorem tendsto_ofReal_nhdsGT_zero :
    Tendsto (fun g : ℝ => (g : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun g : ℝ => (g : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (((0 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.tendsto 0
  rw [Complex.ofReal_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- A birth profile at a strictly smaller order forces the leading coefficient to vanish. -/
theorem HasComplexBirthProfile.leadingCoeff_eq_zero_of_lt
    {mode : ℝ → ℂ} {b b' : ℕ} {c c' : ℂ}
    (h : HasComplexBirthProfile mode b c) (h' : HasComplexBirthProfile mode b' c')
    (hlt : b < b') : c = 0 := by
  have hpow : Tendsto (fun g : ℝ => (g : ℂ) ^ (b' - b)) (𝓝[>] 0) (𝓝 0) := by
    have h0 := tendsto_ofReal_nhdsGT_zero.pow (b' - b)
    simpa [zero_pow (Nat.sub_ne_zero_of_lt hlt)] using h0
  have hprod := h'.1.mul hpow
  rw [mul_zero] at hprod
  have heq : ∀ᶠ g : ℝ in 𝓝[>] 0,
      mode g / (g : ℂ) ^ b' * (g : ℂ) ^ (b' - b) = mode g / (g : ℂ) ^ b := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    have hg0 : (g : ℂ) ≠ 0 := by
      simpa using ne_of_gt (show (0 : ℝ) < g from hg)
    have hsplit : (g : ℂ) ^ b' = (g : ℂ) ^ b * (g : ℂ) ^ (b' - b) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hsplit]
    field_simp
  exact tendsto_nhds_unique h.1 (hprod.congr' heq)

/-- **The birth order is an invariant of the mode.** -/
theorem HasComplexBirthProfile.order_unique
    {mode : ℝ → ℂ} {b b' : ℕ} {c c' : ℂ}
    (h : HasComplexBirthProfile mode b c) (h' : HasComplexBirthProfile mode b' c') :
    b = b' := by
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · exact absurd (h.leadingCoeff_eq_zero_of_lt h' hlt) h.2
  · exact heq
  · exact absurd (h'.leadingCoeff_eq_zero_of_lt h hgt) h'.2

/-- **The birth profile is an invariant of the mode**: both the order and the leading
coefficient are determined. -/
theorem HasComplexBirthProfile.unique
    {mode : ℝ → ℂ} {b b' : ℕ} {c c' : ℂ}
    (h : HasComplexBirthProfile mode b c) (h' : HasComplexBirthProfile mode b' c') :
    b = b' ∧ c = c' := by
  have hb := h.order_unique h'
  subst hb
  exact ⟨rfl, tendsto_nhds_unique h.1 h'.1⟩

end

end GaloisForLFunctions.HTGeometry
