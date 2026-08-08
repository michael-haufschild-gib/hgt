import Mathlib

/-!
# Coordinate cutoffs and the valuation-shift commutator

A weighted valuation shift and a coordinatewise multiplier commute on derivative profiles exactly
when the multiplier does not depend on the coordinate.  If the multiplier is required to switch on
after a coordinate-dependent terminal time and those times are unbounded, no such coordinate-free
multiplier exists; and when the coordinate dependence is genuine the commutator has no zero-order
`L²` bound, because twisting the test profile by `exp(iNL)` multiplies the derivative by `N` while
leaving the profile's mass fixed.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {G : Type*} [AddCommGroup G]

/-- A weighted valuation shift: `(S_s Z)_ν = α_{s,ν} Z_{ν+s}`. -/
def valuationShift (α : G → G → ℂ) (s : G) (Z : G → ℝ → ℂ) : G → ℝ → ℂ :=
  fun ν L => α s ν * Z (ν + s) L

/-- A coordinatewise multiplier: `(M_χ Z)_ν = χ_ν Z_ν`. -/
def coordinateMultiplier (χ : G → ℝ → ℂ) (Z : G → ℝ → ℂ) : G → ℝ → ℂ :=
  fun ν L => χ ν L * Z ν L

/-- The commutator `[M_χ, S_s]`. -/
def valuationCutoffCommutator (χ : G → ℝ → ℂ) (α : G → G → ℂ) (s : G) (Z : G → ℝ → ℂ) : G → ℝ → ℂ :=
  fun ν L => coordinateMultiplier χ (valuationShift α s Z) ν L
    - valuationShift α s (coordinateMultiplier χ Z) ν L

/-- **The commutator identity `(3)`.**  The commutator is the shift weight times the coordinate
increment of the cutoff, applied to the shifted profile. -/
theorem valuationCutoffCommutator_apply (χ : G → ℝ → ℂ) (α : G → G → ℂ) (s : G) (Z : G → ℝ → ℂ)
    (ν : G) (L : ℝ) :
    valuationCutoffCommutator χ α s Z ν L = α s ν * (χ ν L - χ (ν + s) L) * Z (ν + s) L := by
  simp only [valuationCutoffCommutator, coordinateMultiplier, valuationShift]
  ring

section Vanishing

open Classical

variable {χ : G → ℝ → ℂ} {α : G → G → ℂ} {s ν : G}

/-- The linear test profile concentrated at one coordinate. -/
noncomputable def linearTestProfile (μ₀ : G) : G → ℝ → ℂ :=
  fun μ L => if μ = μ₀ then (L : ℂ) else 0

omit [AddCommGroup G] in
theorem linearTestProfile_self (μ₀ : G) : linearTestProfile μ₀ μ₀ = fun L : ℝ => (L : ℂ) := by
  funext L; simp [linearTestProfile]

omit [AddCommGroup G] in
theorem linearTestProfile_eq_zero {μ₀ μ : G} (h : μ ≠ μ₀) : linearTestProfile μ₀ μ = 0 := by
  funext L
  simp [linearTestProfile, h]

omit [AddCommGroup G] in
theorem differentiable_linearTestProfile (μ₀ μ : G) :
    Differentiable ℝ (linearTestProfile μ₀ μ) := by
  by_cases h : μ = μ₀
  · subst h
    rw [linearTestProfile_self]
    fun_prop
  · rw [linearTestProfile_eq_zero h]
    simp

omit [AddCommGroup G] in
theorem deriv_linearTestProfile_self (μ₀ : G) (L : ℝ) :
    deriv (linearTestProfile μ₀ μ₀) L = 1 := by
  rw [linearTestProfile_self]
  have hd : HasDerivAt (fun L : ℝ => (L : ℂ)) 1 L := by
    simpa using (hasDerivAt_id L).ofReal_comp
  exact hd.deriv

/-- **`(4)`, first implication.**  If the commutator annihilates every derivative profile then the
cutoff is constant along the edge, provided the shift weight does not vanish. -/
theorem cutoff_eq_of_commutator_vanishing (hα : α s ν ≠ 0)
    (h : ∀ F : G → ℝ → ℂ, (∀ μ, Differentiable ℝ (F μ)) →
      (∀ μ, μ ≠ ν + s → F μ = 0) →
      ∀ μ M, valuationCutoffCommutator χ α s (fun μ' L => deriv (F μ') L) μ M = 0) :
    ∀ L, χ ν L = χ (ν + s) L := by
  intro L
  have hz := h (linearTestProfile (ν + s)) (differentiable_linearTestProfile (ν + s))
    (fun μ hμ => linearTestProfile_eq_zero hμ) ν L
  rw [valuationCutoffCommutator_apply, deriv_linearTestProfile_self, mul_one] at hz
  rcases mul_eq_zero.mp hz with h1 | h1
  · exact absurd h1 hα
  · linear_combination h1

/-- **`(4)`, converse.**  A cutoff constant along the edge annihilates the commutator. -/
theorem commutator_eq_zero_of_cutoff_eq (h : ∀ L, χ ν L = χ (ν + s) L) (Z : G → ℝ → ℂ) (L : ℝ) :
    valuationCutoffCommutator χ α s Z ν L = 0 := by
  rw [valuationCutoffCommutator_apply, h L, sub_self, mul_zero, zero_mul]

end Vanishing

section Generating

variable {χ : G → ℝ → ℂ}

/-- **`(4)`, third equivalence.**  A cutoff invariant under a generating set of shifts is a single
scalar cutoff. -/
theorem cutoff_eq_zero_of_generating {S : Set G} (hgen : AddSubgroup.closure S = ⊤)
    (h : ∀ ν : G, ∀ s ∈ S, χ ν = χ (ν + s)) (ν : G) : χ ν = χ 0 := by
  set H : AddSubgroup G :=
    { carrier := {g | ∀ μ : G, χ (μ + g) = χ μ}
      zero_mem' := by intro μ; simp
      add_mem' := by
        intro g₁ g₂ hg₁ hg₂ μ
        have h1 : χ (μ + g₁ + g₂) = χ (μ + g₁) := hg₂ (μ + g₁)
        have h2 : χ (μ + g₁) = χ μ := hg₁ μ
        rw [show μ + (g₁ + g₂) = μ + g₁ + g₂ by abel, h1, h2]
      neg_mem' := by
        intro g hg μ
        have := hg (μ - g)
        rw [show μ - g + g = μ by abel] at this
        rw [show μ + -g = μ - g by abel, this] } with hHdef
  have hsub : S ⊆ (H : Set G) := by
    intro s hs μ
    exact (h μ s hs).symm
  have hle : AddSubgroup.closure S ≤ H := (AddSubgroup.closure_le H).mpr hsub
  rw [hgen] at hle
  have hmem : ν ∈ H := hle (AddSubgroup.mem_top ν)
  have := hmem 0
  rwa [zero_add] at this

end Generating

section Adapted

/-- **`(5)` is incompatible with unbounded terminal times.**  A single scalar cutoff cannot be
adapted to a family of validity times that is unbounded above. -/
theorem no_adapted_scalar_cutoff {χ₀ : ℝ → ℂ} {τ : G → ℝ}
    (hoff : ∀ ν : G, ∀ L : ℝ, L ≤ τ ν → χ₀ L = 0)
    (hon : ∀ ν : G, ∀ L : ℝ, τ ν + 1 ≤ L → χ₀ L = 1)
    (hunb : ∀ C : ℝ, ∃ ν : G, C < τ ν) : False := by
  obtain ⟨ν₁, hν₁⟩ := hunb (τ (0 : G) + 1)
  have h1 : χ₀ (τ (0 : G) + 1) = 1 := hon 0 _ le_rfl
  have h0 : χ₀ (τ (0 : G) + 1) = 0 := hoff ν₁ _ hν₁.le
  rw [h1] at h0
  exact one_ne_zero h0

end Adapted

section FirstOrder

open Complex

variable {χ : G → ℝ → ℂ} {α : G → G → ℂ} {s ν : G}

/-- The profile `φ(L) exp(iNL)` twisting a real bump by a frequency. -/
noncomputable def twistedBump (φ : ℝ → ℝ) (N : ℝ) : ℝ → ℂ :=
  fun L => (φ L : ℂ) * Complex.exp (N * L * Complex.I)

/-- Its derivative. -/
noncomputable def twistedBumpDeriv (φ φ' : ℝ → ℝ) (N : ℝ) : ℝ → ℂ :=
  fun L => ((φ' L : ℂ) + Complex.I * N * (φ L : ℂ)) * Complex.exp (N * L * Complex.I)

theorem hasDerivAt_twistedBump {φ φ' : ℝ → ℝ} (h : ∀ L, HasDerivAt φ (φ' L) L) (N L : ℝ) :
    HasDerivAt (twistedBump φ N) (twistedBumpDeriv φ φ' N L) L := by
  have h1 : HasDerivAt (fun L : ℝ => (φ L : ℂ)) ((φ' L : ℂ)) L :=
    (h L).ofReal_comp
  have h2 : HasDerivAt (fun L : ℝ => Complex.exp (N * L * Complex.I))
      (Complex.exp (N * L * Complex.I) * (N * Complex.I)) L := by
    have hb : HasDerivAt (fun L : ℝ => (N * L * Complex.I : ℂ)) (N * Complex.I) L := by
      have hid : HasDerivAt (fun L : ℝ => (L : ℂ)) 1 L := by
        simpa using (hasDerivAt_id L).ofReal_comp
      simpa using (hid.const_mul (N : ℂ)).mul_const Complex.I
    simpa using hb.cexp
  rw [show twistedBumpDeriv φ φ' N L = (φ' L : ℂ) * Complex.exp (N * L * Complex.I)
      + (φ L : ℂ) * (Complex.exp (N * L * Complex.I) * (N * Complex.I)) by
    rw [twistedBumpDeriv]; ring]
  exact h1.mul h2

/-- The modulus square of the twisted derivative separates the two real components. -/
theorem normSq_twistedBumpDeriv (φ φ' : ℝ → ℝ) (N L : ℝ) :
    ‖twistedBumpDeriv φ φ' N L‖ ^ 2 = φ' L ^ 2 + N ^ 2 * φ L ^ 2 := by
  rw [twistedBumpDeriv, norm_mul, mul_pow]
  have hexp : ‖Complex.exp (N * L * Complex.I)‖ = 1 := by
    rw [show ((N : ℂ) * L * Complex.I) = ((N * L : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, one_pow, mul_one]
  have hre : ((φ' L : ℂ) + Complex.I * N * (φ L : ℂ)).re = φ' L := by simp
  have him : ((φ' L : ℂ) + Complex.I * N * (φ L : ℂ)).im = N * φ L := by simp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  ring

theorem norm_twistedBump (φ : ℝ → ℝ) (N L : ℝ) : ‖twistedBump φ N L‖ ^ 2 = φ L ^ 2 := by
  rw [twistedBump, norm_mul, mul_pow]
  have hexp : ‖Complex.exp (N * L * Complex.I)‖ = 1 := by
    rw [show ((N : ℂ) * L * Complex.I) = ((N * L : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The commutator is genuinely first order `(6)`.**  Pointwise, twisting the test profile by a
frequency `N` multiplies the commutator's mass by at least `δ² N²` while leaving the profile's mass
unchanged. -/
theorem sq_norm_valuationCutoffCommutator_twisted_ge {φ φ' : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ L, φ L ≠ 0 → δ ≤ ‖α s ν * (χ ν L - χ (ν + s) L)‖) (N L : ℝ) :
    δ ^ 2 * (N ^ 2 * φ L ^ 2)
      ≤ ‖valuationCutoffCommutator χ α s (fun _ => twistedBumpDeriv φ φ' N) ν L‖ ^ 2 := by
  rw [valuationCutoffCommutator_apply, norm_mul, mul_pow, normSq_twistedBumpDeriv]
  by_cases hz : φ L = 0
  · rw [hz]
    simp
    positivity
  · have hb := hbound L hz
    have h1 : δ ^ 2 ≤ ‖α s ν * (χ ν L - χ (ν + s) L)‖ ^ 2 := by
      exact pow_le_pow_left₀ hδ hb 2
    have h2 : N ^ 2 * φ L ^ 2 ≤ φ' L ^ 2 + N ^ 2 * φ L ^ 2 := by nlinarith [sq_nonneg (φ' L)]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **No zero-order bound.**  For every constant `C` there is a frequency whose twisted profile
violates `‖[M_χ, S_s] ∂_L F‖₂ ≤ C ‖F‖₂`. -/
theorem no_zero_order_bound {φ φ' : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ L, φ L ≠ 0 → δ ≤ ‖α s ν * (χ ν L - χ (ν + s) L)‖)
    (hint : Integrable (fun L => φ L ^ 2))
    (hpos : 0 < ∫ L, φ L ^ 2)
    (hintc : ∀ N : ℝ,
      Integrable (fun L => ‖valuationCutoffCommutator χ α s (fun _ => twistedBumpDeriv φ φ' N) ν L‖ ^ 2))
    (C : ℝ) :
    ∃ N : ℝ, C * (∫ L, ‖twistedBump φ N L‖ ^ 2)
      < ∫ L, ‖valuationCutoffCommutator χ α s (fun _ => twistedBumpDeriv φ φ' N) ν L‖ ^ 2 := by
  obtain ⟨N, hN⟩ : ∃ N : ℝ, C < δ ^ 2 * N ^ 2 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (C / δ ^ 2)
    refine ⟨Real.sqrt n, ?_⟩
    have hδ2 : 0 < δ ^ 2 := by positivity
    have hns : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    rw [hns]
    rw [div_lt_iff₀ hδ2] at hn
    linarith
  refine ⟨N, ?_⟩
  have hmass : (∫ L, ‖twistedBump φ N L‖ ^ 2) = ∫ L, φ L ^ 2 := by
    simp only [norm_twistedBump]
  have hlow : (∫ L, δ ^ 2 * (N ^ 2 * φ L ^ 2))
      ≤ ∫ L, ‖valuationCutoffCommutator χ α s (fun _ => twistedBumpDeriv φ φ' N) ν L‖ ^ 2 :=
    integral_mono ((hint.const_mul (N ^ 2)).const_mul (δ ^ 2)) (hintc N)
      (fun L => sq_norm_valuationCutoffCommutator_twisted_ge hδ.le hbound N L)
  have hcalc : (∫ L, δ ^ 2 * (N ^ 2 * φ L ^ 2)) = δ ^ 2 * N ^ 2 * ∫ L, φ L ^ 2 := by
    rw [integral_const_mul, integral_const_mul, mul_assoc]
  rw [hmass]
  have : C * (∫ L, φ L ^ 2) < δ ^ 2 * N ^ 2 * ∫ L, φ L ^ 2 :=
    mul_lt_mul_of_pos_right hN hpos
  linarith [hcalc ▸ hlow]

end FirstOrder

end GaloisForLFunctions.HTGeometry
