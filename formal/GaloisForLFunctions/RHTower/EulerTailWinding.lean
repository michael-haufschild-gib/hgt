/-
The Euler-tail winding of the incidence carrier: phase advance forces band-edge events, and
the phase is the difference of the target and anchor phases — the Euler tail.

A nonvanishing carrier along an edge is a modulus times a unimodular phase; when its phase
advances by at least half a turn, the imaginary part is forced through zero (an intermediate
multiple of `π`), and a zero of the imaginary part of the incidence carrier is a vanishing of
the real-ratio pencil member — a transversal band-edge event.  The incidence carrier's phase
is the target phase minus the anchor phase: the anchor subtracts the head of the Euler
constraint, leaving the tail, whose winding the archimedean winding floor drives.  The banked
line winding floor feeds this directly: on a segment long against the local scale the winding
phase already exceeds `π`, and a target phase carrying that floor, net of a bounded anchor
phase, advances past `π` and forces an event.
-/
import GaloisForLFunctions.RHTower.IncidenceCarrier
import GaloisForLFunctions.RHTower.ArgumentVariation

namespace RHTower

open Complex Metric

/-- **Phase advance forces a zero of the imaginary part.**  A carrier presented in polar
form along an edge whose phase advances by at least `π` has an imaginary part vanishing
somewhere on the edge: the phase passes through an integer multiple of `π`, a zero of the
sine. -/
theorem exists_im_zero_of_phase_advance {F : ℝ → ℂ} {r θ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hpolar : ∀ τ ∈ Set.Icc a b, F τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hθc : ContinuousOn θ (Set.Icc a b)) (hadv : θ a + Real.pi ≤ θ b) :
    ∃ τ ∈ Set.Icc a b, (F τ).im = 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, θ a ≤ (k : ℝ) * Real.pi ∧ (k : ℝ) * Real.pi ≤ θ b := by
    refine ⟨⌈θ a / Real.pi⌉, ?_, ?_⟩
    · calc θ a = (θ a / Real.pi) * Real.pi := by field_simp
        _ ≤ (⌈θ a / Real.pi⌉ : ℝ) * Real.pi :=
            mul_le_mul_of_nonneg_right (Int.le_ceil _) hπ.le
    · calc (⌈θ a / Real.pi⌉ : ℝ) * Real.pi ≤ (θ a / Real.pi + 1) * Real.pi :=
            mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one _).le hπ.le
        _ = θ a + Real.pi := by field_simp
        _ ≤ θ b := hadv
  obtain ⟨σ, hσ, hθσ⟩ := intermediate_value_Icc hab hθc (Set.mem_Icc.mpr ⟨hk1, hk2⟩)
  refine ⟨σ, hσ, ?_⟩
  have him : (F σ).im = r σ * Real.sin (θ σ) := by
    rw [hpolar σ hσ, Complex.mul_im]
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [him, hθσ, Real.sin_int_mul_pi, mul_zero]

/-- **A real incidence value is a vanishing real-ratio member.**  Where the anchor does not
vanish and the incidence carrier is real, the pencil member with that real ratio vanishes:
the transversal band-edge event. -/
theorem incidence_real_member_zero_of_im_zero {Λ₁ Λ₂ : ℂ → ℂ} {z : ℂ}
    (h0 : Λ₁ z ≠ 0) (him : (incidence Λ₁ Λ₂ z).im = 0) :
    pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ z).re : ℂ) 1 z = 0 := by
  have hre : incidence Λ₁ Λ₂ z = (((incidence Λ₁ Λ₂ z).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [him])
  have hdiv : -Λ₂ z / Λ₁ z = (((incidence Λ₁ Λ₂ z).re : ℝ) : ℂ) := hre
  rw [div_eq_iff h0] at hdiv
  show (((incidence Λ₁ Λ₂ z).re : ℝ) : ℂ) * Λ₁ z + 1 * Λ₂ z = 0
  linear_combination -hdiv

/-- **Winding forces a band-edge event.**  If the incidence carrier along an edge is a
modulus times a phase whose advance is at least `π`, and the anchor does not vanish there,
then the real-ratio pencil member is forced to vanish somewhere on the edge — a transversal
band-edge event produced by winding rather than by an endpoint sign bracket. -/
theorem exists_bandEvent_of_incidence_phase_advance {Λ₁ Λ₂ : ℂ → ℂ} {γ : ℝ → ℂ}
    {r θ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hΛ₁ : ∀ τ ∈ Set.Icc a b, Λ₁ (γ τ) ≠ 0)
    (hpolar : ∀ τ ∈ Set.Icc a b,
      incidence Λ₁ Λ₂ (γ τ) = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hθc : ContinuousOn θ (Set.Icc a b)) (hadv : θ a + Real.pi ≤ θ b) :
    ∃ τ ∈ Set.Icc a b,
      pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (γ τ)).re : ℂ) 1 (γ τ) = 0 := by
  obtain ⟨τ, hτ, him⟩ :=
    exists_im_zero_of_phase_advance (F := fun τ => incidence Λ₁ Λ₂ (γ τ)) hab hpolar hθc hadv
  exact ⟨τ, hτ, incidence_real_member_zero_of_im_zero (hΛ₁ τ hτ) him⟩

/-- **The incidence phase is the Euler tail.**  The incidence carrier's phase is the target
phase minus the anchor phase: subtracting the anchor removes the head of the constraint and
leaves the tail, `θ_target − θ_anchor`, whose modulus is `−R₂/R₁`. -/
theorem incidence_phase_of_factor_phases {Λ₁ Λ₂ : ℂ → ℂ} {z : ℂ} {R₁ R₂ θ₁ θ₂ : ℝ}
    (h1 : R₁ ≠ 0)
    (hP1 : Λ₁ z = (R₁ : ℂ) * Complex.exp ((θ₁ : ℝ) * I))
    (hP2 : Λ₂ z = (R₂ : ℂ) * Complex.exp ((θ₂ : ℝ) * I)) :
    incidence Λ₁ Λ₂ z = ((-R₂ / R₁ : ℝ) : ℂ) * Complex.exp (((θ₂ - θ₁ : ℝ)) * I) := by
  unfold incidence
  rw [hP1, hP2]
  have he : Complex.exp ((θ₁ : ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hR1 : (R₁ : ℂ) ≠ 0 := by exact_mod_cast h1
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.ofReal_div, Complex.ofReal_neg]
  field_simp

/-- **The Euler-tail winding lemma.**  If along an edge the anchor and target are nonvanishing
polar factors with continuous phases, and the Euler-tail phase `θ_target − θ_anchor` advances
by at least `π`, then a transversal band-edge event is forced: the winding of the tail across
the edge produces a vanishing real-ratio member.  The advance hypothesis is exactly what the
winding-floor instruments supply — a target-phase floor net of a bounded anchor phase. -/
theorem exists_bandEvent_of_euler_tail {Λ₁ Λ₂ : ℂ → ℂ} {γ : ℝ → ℂ}
    {R₁ R₂ θ₁ θ₂ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hR1 : ∀ τ ∈ Set.Icc a b, R₁ τ ≠ 0)
    (hP1 : ∀ τ ∈ Set.Icc a b, Λ₁ (γ τ) = (R₁ τ : ℂ) * Complex.exp ((θ₁ τ : ℝ) * I))
    (hP2 : ∀ τ ∈ Set.Icc a b, Λ₂ (γ τ) = (R₂ τ : ℂ) * Complex.exp ((θ₂ τ : ℝ) * I))
    (hθ1c : ContinuousOn θ₁ (Set.Icc a b)) (hθ2c : ContinuousOn θ₂ (Set.Icc a b))
    (hadv : (θ₂ a - θ₁ a) + Real.pi ≤ (θ₂ b - θ₁ b)) :
    ∃ τ ∈ Set.Icc a b,
      pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (γ τ)).re : ℂ) 1 (γ τ) = 0 := by
  refine exists_bandEvent_of_incidence_phase_advance (θ := fun τ => θ₂ τ - θ₁ τ)
    (r := fun τ => -R₂ τ / R₁ τ) hab ?_ ?_ (hθ2c.sub hθ1c) hadv
  · intro τ hτ
    rw [hP1 τ hτ]
    exact mul_ne_zero (by exact_mod_cast hR1 τ hτ) (Complex.exp_ne_zero _)
  · intro τ hτ
    exact incidence_phase_of_factor_phases (hR1 τ hτ) (hP1 τ hτ) (hP2 τ hτ)

/-- The banked line winding floor, converted to a half-turn advance: on a segment long against
the local scale, the archimedean winding phase already exceeds `π`.  This is the winding-floor
instrument in the form the Euler-tail lemma consumes for its target-phase advance. -/
theorem windingPhase_ge_pi_of_long {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlong : Real.pi ≤
      (b - a) * ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)) :
    Real.pi ≤ windingPhase a b :=
  le_trans hlong (windingPhase_ge_of_floor ha hab)

/-- **The Euler-tail advance from a floor net of a ceiling.**  If the target phase carries an
advance floor `μ_target` and the anchor phase advance is bounded above by `C_anchor`, and the
edge is long enough that `floor − ceiling ≥ π`, then the Euler-tail phase advances by at least
`π`.  This is the arithmetic that turns the banked winding floor into the advance hypothesis of
the Euler-tail lemma. -/
theorem euler_tail_advance_of_floor_ceiling {θ₁ θ₂ : ℝ → ℝ} {a b μ C : ℝ}
    (hfloor : μ ≤ θ₂ b - θ₂ a) (hceil : θ₁ b - θ₁ a ≤ C) (hgap : Real.pi ≤ μ - C) :
    (θ₂ a - θ₁ a) + Real.pi ≤ (θ₂ b - θ₁ b) := by
  linarith

end RHTower

namespace RHTower

open Complex Metric

/-- **The winding floor forces a band-edge event, end to end.**  If along an edge the anchor
and target are nonvanishing polar factors, the target phase carries an advance floor `μ`, the
anchor phase advance is bounded by `C`, and the floor exceeds the ceiling by at least `π`, then
a transversal band-edge event is forced.  This is the winding-floor instrument threaded to the
incidence carrier: the archimedean floor of `windingPhase_ge_of_floor` supplies `μ`, a
Dirichlet-polynomial phase bound supplies `C`, and their gap past `π` produces the event. -/
theorem exists_bandEvent_of_target_winding_floor {Λ₁ Λ₂ : ℂ → ℂ} {γ : ℝ → ℂ}
    {R₁ R₂ θ₁ θ₂ : ℝ → ℝ} {a b μ C : ℝ} (hab : a ≤ b)
    (hR1 : ∀ τ ∈ Set.Icc a b, R₁ τ ≠ 0)
    (hP1 : ∀ τ ∈ Set.Icc a b, Λ₁ (γ τ) = (R₁ τ : ℂ) * Complex.exp ((θ₁ τ : ℝ) * I))
    (hP2 : ∀ τ ∈ Set.Icc a b, Λ₂ (γ τ) = (R₂ τ : ℂ) * Complex.exp ((θ₂ τ : ℝ) * I))
    (hθ1c : ContinuousOn θ₁ (Set.Icc a b)) (hθ2c : ContinuousOn θ₂ (Set.Icc a b))
    (hfloor : μ ≤ θ₂ b - θ₂ a) (hceil : θ₁ b - θ₁ a ≤ C) (hgap : Real.pi ≤ μ - C) :
    ∃ τ ∈ Set.Icc a b,
      pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (γ τ)).re : ℂ) 1 (γ τ) = 0 :=
  exists_bandEvent_of_euler_tail hab hR1 hP1 hP2 hθ1c hθ2c
    (euler_tail_advance_of_floor_ceiling hfloor hceil hgap)

end RHTower
