import GaloisForLFunctions.HTGeometry.KleinGordonPropagatorDerivative

/-!
# The free Klein–Gordon equation has a strong `L²` solution

Differentiating the propagator once costs one power of `⟨D⟩⁻¹` in the datum; differentiating it twice
costs two. So on the range of `⟨D⟩⁻²` the free evolution is twice differentiable as a curve in `L²`,
and its second derivative is again a bounded expression in the datum. That is a **strong** solution of
the Klein–Gordon equation: no distributions, no unbounded operators, every step an identity between
elements of `L²`.

The equation itself is stated in the only form available without naming the unbounded `⟨D⟩²`, namely

`⟨D⟩⁻²(∂ₜ²u) = -u`,

which for a doubly regular field is equivalent to `∂ₜ²u + ⟨D⟩²u = 0` — and `⟨ξ⟩² = 1 + ‖ξ‖²` is the
symbol of `1 - (2π)⁻²Δ`, so this is the physical field equation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The propagators commute with the inverse frequency -/

theorem kgFreqInvOp_comp_kgCosOp (t : ℝ) :
    (kgFreqInvOp (E := E)).comp (kgCosOp t)
      = fourierMulCLM (measurable_kgCosOverFreq (E := E) t) zero_le_one
        (norm_kgCosOverFreq_le t) := by
  rw [kgFreqInvOp_eq, kgCosOp_eq]
  refine fourierMulCLM_comp _ _ (measurable_kgCosOverFreq (E := E) t) _ _ _ _ _
    (norm_kgCosOverFreq_le t) (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.cos (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
    = (((kgFreq ξ)⁻¹ : ℝ) : ℂ) * ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, div_eq_inv_mul]

theorem kgFreqInvOp_comp_kgSinOp (t : ℝ) :
    (kgFreqInvOp (E := E)).comp (kgSinOp t)
      = fourierMulCLM (measurable_kgSinOverFreq (E := E) t) zero_le_one
        (norm_kgSinOverFreq_le t) := by
  rw [kgFreqInvOp_eq, kgSinOp_eq]
  refine fourierMulCLM_comp _ _ (measurable_kgSinOverFreq (E := E) t) _ _ _ _ _
    (norm_kgSinOverFreq_le t) (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
    = (((kgFreq ξ)⁻¹ : ℝ) : ℂ) * ((Real.sin (t * kgFreq ξ) : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, div_eq_inv_mul]

/-- **The cosine propagator commutes with `⟨D⟩⁻¹`.** -/
theorem kgFreqInvOp_kgCosOp (t : ℝ) (x : Lp (α := E) ℂ 2) :
    kgFreqInvOp (kgCosOp t x) = kgCosOp t (kgFreqInvOp x) := by
  have h1 := kgFreqInvOp_comp_kgCosOp (E := E) t
  have h2 := kgCosOp_comp_kgFreqInvOp (E := E) t
  have h := h1.trans h2.symm
  exact congrArg (fun T : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 => T x) h

/-- **The sine propagator commutes with `⟨D⟩⁻¹`.** -/
theorem kgFreqInvOp_kgSinOp (t : ℝ) (x : Lp (α := E) ℂ 2) :
    kgFreqInvOp (kgSinOp t x) = kgSinOp t (kgFreqInvOp x) := by
  have h1 := kgFreqInvOp_comp_kgSinOp (E := E) t
  have h2 := kgSinOp_comp_kgFreqInvOp (E := E) t
  have h := h1.trans h2.symm
  exact congrArg (fun T : Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 => T x) h

/-! ## The free field of a doubly regular datum -/

/-- The free Klein–Gordon field with position datum `⟨D⟩⁻²f` and velocity datum `⟨D⟩⁻¹h`. -/
def kgFreeField (f h : Lp (α := E) ℂ 2) (t : ℝ) : Lp (α := E) ℂ 2 :=
  kgCosOp t (kgFreqInvOp (kgFreqInvOp f)) + kgSinOp t (kgFreqInvOp (kgFreqInvOp h))

/-- The velocity of the free field. -/
def kgFreeVelocity (f h : Lp (α := E) ℂ 2) (t : ℝ) : Lp (α := E) ℂ 2 :=
  -(kgSinOp t (kgFreqInvOp f)) + kgCosOp t (kgFreqInvOp h)

/-- **The free field is differentiable, with the stated velocity.** -/
theorem hasDerivAt_kgFreeField (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    HasDerivAt (kgFreeField f h) (kgFreeVelocity f h t) t :=
  (hasDerivAt_kgCosOp_freqInv t (kgFreqInvOp f)).add
    (hasDerivAt_kgSinOp_freqInv t (kgFreqInvOp h))

/-- **The velocity is differentiable**, and its derivative is the datum propagated with no
regularisation left. -/
theorem hasDerivAt_kgFreeVelocity (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    HasDerivAt (kgFreeVelocity f h) (-(kgCosOp t f) + -(kgSinOp t h)) t :=
  ((hasDerivAt_kgSinOp_freqInv t f).neg).add (hasDerivAt_kgCosOp_freqInv t h)

theorem deriv_kgFreeField (f h : Lp (α := E) ℂ 2) :
    deriv (kgFreeField f h) = kgFreeVelocity f h :=
  funext fun t => (hasDerivAt_kgFreeField f h t).deriv

theorem deriv_deriv_kgFreeField (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    deriv (deriv (kgFreeField f h)) t = -(kgCosOp t f) + -(kgSinOp t h) := by
  rw [deriv_kgFreeField]
  exact (hasDerivAt_kgFreeVelocity f h t).deriv

/-! ## The field equation -/

/-- The field is the doubly regularised propagation of the datum. -/
theorem kgFreeField_eq (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    kgFreeField f h t
      = kgFreqInvOp (kgFreqInvOp (kgCosOp t f + kgSinOp t h)) := by
  rw [map_add, map_add, kgFreqInvOp_kgCosOp, kgFreqInvOp_kgCosOp, kgFreqInvOp_kgSinOp,
    kgFreqInvOp_kgSinOp]
  rfl

/-- **The free field solves the Klein–Gordon equation strongly.** Every step is an identity in `L²`:
the field is twice differentiable as a curve, and `⟨D⟩⁻²∂ₜ²u = -u`, which for a doubly regular field
is the equation `∂ₜ²u + ⟨D⟩²u = 0`. -/
theorem kgFreeField_kleinGordon (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    kgFreqInvOp (kgFreqInvOp (deriv (deriv (kgFreeField f h)) t)) = -(kgFreeField f h t) := by
  rw [deriv_deriv_kgFreeField, kgFreeField_eq]
  have hsum : -(kgCosOp (E := E) t f) + -(kgSinOp t h) = -(kgCosOp t f + kgSinOp t h) := by
    rw [neg_add]
  rw [hsum, map_neg, map_neg]

/-! ## The Cauchy data -/

theorem kgFreeField_zero (f h : Lp (α := E) ℂ 2) :
    kgFreeField f h 0 = kgFreqInvOp (kgFreqInvOp f) := by
  rw [kgFreeField, kgCosOp_zero, kgSinOp_zero]
  simp

theorem kgFreeVelocity_zero (f h : Lp (α := E) ℂ 2) :
    kgFreeVelocity f h 0 = kgFreqInvOp h := by
  rw [kgFreeVelocity, kgCosOp_zero, kgSinOp_zero]
  simp

/-- **Existence for the Cauchy problem of the free Klein–Gordon equation**, in the strong `L²` sense,
for every datum in the range of `⟨D⟩⁻²` with velocity in the range of `⟨D⟩⁻¹`. -/
theorem exists_kgFreeField (f h : Lp (α := E) ℂ 2) :
    ∃ u : ℝ → Lp (α := E) ℂ 2,
      (∀ t : ℝ, HasDerivAt u (deriv u t) t) ∧
      (∀ t : ℝ, HasDerivAt (deriv u) (deriv (deriv u) t) t) ∧
      (∀ t : ℝ, kgFreqInvOp (kgFreqInvOp (deriv (deriv u) t)) = -(u t)) ∧
      u 0 = kgFreqInvOp (kgFreqInvOp f) ∧ deriv u 0 = kgFreqInvOp h := by
  refine ⟨kgFreeField f h, fun t => ?_, fun t => ?_, kgFreeField_kleinGordon f h,
    kgFreeField_zero f h, ?_⟩
  · have h1 := hasDerivAt_kgFreeField f h t
    rwa [h1.deriv]
  · have h2 := hasDerivAt_kgFreeVelocity f h t
    rw [deriv_kgFreeField]
    rwa [h2.deriv]
  · rw [deriv_kgFreeField]
    exact kgFreeVelocity_zero f h

/-! ## The energy of the strong solution -/

/-- The gradient part `⟨D⟩u` of the free field: applying `⟨D⟩⁻¹` to it returns the field. -/
def kgFreeGradient (f h : Lp (α := E) ℂ 2) (t : ℝ) : Lp (α := E) ℂ 2 :=
  kgFreqInvOp (kgCosOp t f + kgSinOp t h)

theorem kgFreqInvOp_kgFreeGradient (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    kgFreqInvOp (kgFreeGradient f h t) = kgFreeField f h t := (kgFreeField_eq f h t).symm

theorem kgFreeGradient_eq (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    kgFreeGradient f h t = kgCosOp t (kgFreqInvOp f) + kgSinOp t (kgFreqInvOp h) := by
  rw [kgFreeGradient, map_add, kgFreqInvOp_kgCosOp, kgFreqInvOp_kgSinOp]

set_option maxHeartbeats 1000000 in
/-- **The energy state of the strong solution is the propagator applied to the energy state of the
data.** -/
theorem kgPropagator_kgFreeState (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    kgPropagator t (kgPair E (kgFreqInvOp f, kgFreqInvOp h))
      = kgPair E (kgFreeGradient f h t, kgFreeVelocity f h t) := by
  simp only [kgPropagator_apply, kgPair_fst, kgPair_snd, kgFreeGradient_eq, kgFreeVelocity]

set_option maxHeartbeats 1000000 in
/-- **Energy conservation for the strong solution of the free Klein–Gordon equation.** The sum of the
squared `L²` norms of `⟨D⟩u` and `∂ₜu` is independent of the time. -/
theorem kgFreeField_energy_const (f h : Lp (α := E) ℂ 2) (t : ℝ) :
    ‖kgFreeGradient f h t‖ ^ 2 + ‖kgFreeVelocity f h t‖ ^ 2
      = ‖kgFreqInvOp (E := E) f‖ ^ 2 + ‖kgFreqInvOp (E := E) h‖ ^ 2 := by
  have h0 := kgEnergy_kgPropagator (E := E) t (kgPair E (kgFreqInvOp f, kgFreqInvOp h))
  have h1 : kgEnergy (kgPropagator (E := E) t (kgPair E (kgFreqInvOp f, kgFreqInvOp h)))
      = ‖kgFreeGradient f h t‖ ^ 2 + ‖kgFreeVelocity f h t‖ ^ 2 := by
    rw [kgPropagator_kgFreeState]
    simp only [kgEnergy, kgPair_fst, kgPair_snd]
  have h2 : kgEnergy (kgPair E (kgFreqInvOp (E := E) f, kgFreqInvOp (E := E) h))
      = ‖kgFreqInvOp (E := E) f‖ ^ 2 + ‖kgFreqInvOp (E := E) h‖ ^ 2 := by
    simp only [kgEnergy, kgPair_fst, kgPair_snd]
  rw [← h1, ← h2, h0]

end GaloisForLFunctions.HTGeometry
