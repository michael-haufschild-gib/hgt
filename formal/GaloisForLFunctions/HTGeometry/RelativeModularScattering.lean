import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The scattering operator as a relative modular invariant

Transporting the free wedge modular conjugation by the incoming Møller operator gives the
incoming conjugation `J_in = V_in J₀ V_in⁻¹`; the interacting conjugation is
`J = V_in J₀ V_out⁻¹` and the physical scattering operator is `S = V_in V_out⁻¹`.  From the single
fact that `J₀` is an involution one gets

```text
S = J_in ∘ J,        J = J_in ∘ S,
```

so the whole scattering law is the relative position of two conjugations.  Complex conjugate
linearity of `J₀` makes both conjugations antiunitary and their composite complex linear: the
relative modular operator is a genuine unitary.  When the interacting conjugation is itself an
involution, the relative unitary satisfies the reality law `J_in M J_in = M⁻¹`.

The factorizing `n`-particle multiplier is the product of the two-particle function over all
rapidity pairs.  It depends only on rapidity differences — so it is invariant under the common
boost — and on a two-particle chamber it is literally the input two-particle function.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ComplexConjugate BigOperators

noncomputable section

section Linearity

variable {A B C : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

/-- Complex linearity of a real-linear map: the unitary half of the modular dictionary. -/
def IsComplexLinearMap (f : A → B) : Prop := ∀ (c : ℂ) (x : A), f (c • x) = c • f x

/-- Complex conjugate linearity: the antiunitary half. -/
def IsConjugateLinearMap (f : A → B) : Prop :=
  ∀ (c : ℂ) (x : A), f (c • x) = conj c • f x

/-- **Two antiunitaries compose to a unitary.** -/
theorem IsConjugateLinearMap.comp {g : B → C} {f : A → B}
    (hg : IsConjugateLinearMap g) (hf : IsConjugateLinearMap f) :
    IsComplexLinearMap (g ∘ f) := by
  intro c x
  show g (f (c • x)) = c • g (f x)
  rw [hf, hg]
  simp

theorem IsComplexLinearMap.comp_conjugate {g : B → C} {f : A → B}
    (hg : IsComplexLinearMap g) (hf : IsConjugateLinearMap f) :
    IsConjugateLinearMap (g ∘ f) := by
  intro c x
  show g (f (c • x)) = conj c • g (f x)
  rw [hf, hg]

theorem IsConjugateLinearMap.comp_complex {g : B → C} {f : A → B}
    (hg : IsConjugateLinearMap g) (hf : IsComplexLinearMap f) :
    IsConjugateLinearMap (g ∘ f) := by
  intro c x
  show g (f (c • x)) = conj c • g (f x)
  rw [hf, hg]

/-- The inverse of a complex-linear isometric equivalence is complex linear. -/
theorem isComplexLinearMap_symm (V : A ≃ₗᵢ[ℝ] B) (hV : IsComplexLinearMap V) :
    IsComplexLinearMap V.symm := by
  intro c y
  apply V.injective
  rw [V.apply_symm_apply, hV, V.apply_symm_apply]

end Linearity

section Modular

variable {Fock Phys : Type*}
  [NormedAddCommGroup Fock] [NormedSpace ℂ Fock]
  [NormedAddCommGroup Phys] [NormedSpace ℂ Phys]

variable (J₀ : Fock ≃ₗᵢ[ℝ] Fock) (Vin Vout : Fock ≃ₗᵢ[ℝ] Phys)

/-- `J_in = V_in J₀ V_in⁻¹`: the free wedge conjugation transported by the incoming Møller
operator. -/
def incomingConjugation : Phys ≃ₗᵢ[ℝ] Phys := (Vin.symm.trans J₀).trans Vin

/-- `J = V_in J₀ V_out⁻¹`: the interacting wedge conjugation. -/
def interactingConjugation : Phys ≃ₗᵢ[ℝ] Phys := (Vout.symm.trans J₀).trans Vin

/-- `S = V_in V_out⁻¹`: the scattering operator on the physical Hilbert space. -/
def physicalScattering : Phys ≃ₗᵢ[ℝ] Phys := Vout.symm.trans Vin

@[simp]
theorem incomingConjugation_apply (x : Phys) :
    incomingConjugation J₀ Vin x = Vin (J₀ (Vin.symm x)) := rfl

@[simp]
theorem interactingConjugation_apply (x : Phys) :
    interactingConjugation J₀ Vin Vout x = Vin (J₀ (Vout.symm x)) := rfl

@[simp]
theorem physicalScattering_apply (x : Phys) :
    physicalScattering Vin Vout x = Vin (Vout.symm x) := rfl

/-- **The scattering operator is the relative modular operator.**  `S = J_in ∘ J`. -/
theorem physicalScattering_eq_incoming_comp_interacting
    (hJ₀ : ∀ y, J₀ (J₀ y) = y) (x : Phys) :
    incomingConjugation J₀ Vin (interactingConjugation J₀ Vin Vout x) =
      physicalScattering Vin Vout x := by
  simp [hJ₀]

/-- **The interacting conjugation factorises through the scattering operator.**  `J = J_in ∘ S`. -/
theorem interactingConjugation_eq_incoming_comp_scattering (x : Phys) :
    incomingConjugation J₀ Vin (physicalScattering Vin Vout x) =
      interactingConjugation J₀ Vin Vout x := by
  simp

/-- The incoming conjugation is an involution. -/
theorem incomingConjugation_involutive (hJ₀ : ∀ y, J₀ (J₀ y) = y) (x : Phys) :
    incomingConjugation J₀ Vin (incomingConjugation J₀ Vin x) = x := by
  simp [hJ₀]

/-- Both wedge conjugations are antiunitary. -/
theorem incomingConjugation_conjugateLinear
    (hJ₀ : IsConjugateLinearMap J₀) (hVin : IsComplexLinearMap Vin) :
    IsConjugateLinearMap (incomingConjugation J₀ Vin) := by
  intro c x
  simp only [incomingConjugation_apply]
  rw [isComplexLinearMap_symm Vin hVin, hJ₀, hVin]

theorem interactingConjugation_conjugateLinear
    (hJ₀ : IsConjugateLinearMap J₀) (hVin : IsComplexLinearMap Vin)
    (hVout : IsComplexLinearMap Vout) :
    IsConjugateLinearMap (interactingConjugation J₀ Vin Vout) := by
  intro c x
  simp only [interactingConjugation_apply]
  rw [isComplexLinearMap_symm Vout hVout, hJ₀, hVin]

/-- **The relative modular operator is unitary.**  A product of two antiunitaries is complex
linear, and it is an isometric equivalence by construction. -/
theorem physicalScattering_complexLinear
    (hVin : IsComplexLinearMap Vin) (hVout : IsComplexLinearMap Vout) :
    IsComplexLinearMap (physicalScattering Vin Vout) := by
  intro c x
  simp only [physicalScattering_apply]
  rw [isComplexLinearMap_symm Vout hVout, hVin]

/-- **The incoming Fock form of the scattering operator.**  `V_in⁻¹ S V_in = V_out⁻¹ V_in`. -/
theorem incoming_form_physicalScattering (x : Fock) :
    Vin.symm (physicalScattering Vin Vout (Vin x)) = Vout.symm (Vin x) := by
  simp

/-- **Reality law for the relative modular unitary.**  If the interacting conjugation is an
involution, then `J_in M J_in = M⁻¹` for `M = J_in ∘ J`, which by unitarity is `M*`. -/
theorem incomingConjugation_conj_physicalScattering
    (hJ₀ : ∀ y, J₀ (J₀ y) = y)
    (hJ : ∀ y, interactingConjugation J₀ Vin Vout
      (interactingConjugation J₀ Vin Vout y) = y) (x : Phys) :
    incomingConjugation J₀ Vin
        (physicalScattering Vin Vout (incomingConjugation J₀ Vin x)) =
      (physicalScattering Vin Vout).symm x := by
  have hSJ : ∀ y, physicalScattering Vin Vout y =
      incomingConjugation J₀ Vin (interactingConjugation J₀ Vin Vout y) := fun y =>
    (physicalScattering_eq_incoming_comp_interacting J₀ Vin Vout hJ₀ y).symm
  have hLHS : incomingConjugation J₀ Vin
      (physicalScattering Vin Vout (incomingConjugation J₀ Vin x)) =
      interactingConjugation J₀ Vin Vout (incomingConjugation J₀ Vin x) := by
    rw [hSJ, incomingConjugation_involutive J₀ Vin hJ₀]
  have hRHS : (physicalScattering Vin Vout).symm x =
      interactingConjugation J₀ Vin Vout (incomingConjugation J₀ Vin x) := by
    apply (physicalScattering Vin Vout).injective
    rw [(physicalScattering Vin Vout).apply_symm_apply, hSJ, hJ,
      incomingConjugation_involutive J₀ Vin hJ₀]
  rw [hLHS, hRHS]

/-- The free case realises every hypothesis: with `V_out = V_in` the interacting conjugation is
the incoming one, hence an involution, and the scattering operator is the identity. -/
theorem interactingConjugation_free (x : Phys) :
    interactingConjugation J₀ Vin Vin x = incomingConjugation J₀ Vin x := rfl

theorem physicalScattering_free (x : Phys) : physicalScattering Vin Vin x = x := by
  simp

end Modular

section Realisation

/-- Complex conjugation is an antiunitary involution, so the modular hypotheses are non-vacuous. -/
theorem conjLIE_conjugateLinear : IsConjugateLinearMap (Complex.conjLIE : ℂ → ℂ) := by
  intro c x
  simp [Complex.conjLIE]

theorem conjLIE_involutive (z : ℂ) : Complex.conjLIE (Complex.conjLIE z) = z := by
  simp [Complex.conjLIE]

end Realisation

section Multiplier

/-- The factorizing `n`-particle multiplier of a two-particle scattering function: the product
over all ordered rapidity pairs. -/
def factorizingMultiplier (S₂ : ℝ → ℂ) (n : ℕ) (θ : Fin n → ℝ) : ℂ :=
  ∏ p ∈ Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2, S₂ |θ p.1 - θ p.2|

/-- **Boost invariance.**  The multiplier depends only on rapidity differences, so the common
boost adds no interacting information. -/
theorem factorizingMultiplier_translate (S₂ : ℝ → ℂ) (n : ℕ) (θ : Fin n → ℝ) (a : ℝ) :
    factorizingMultiplier S₂ n (fun i => θ i + a) = factorizingMultiplier S₂ n θ := by
  unfold factorizingMultiplier
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 2
  ring

@[simp]
theorem factorizingMultiplier_zero (S₂ : ℝ → ℂ) (θ : Fin 0 → ℝ) :
    factorizingMultiplier S₂ 0 θ = 1 := by
  simp [factorizingMultiplier]

@[simp]
theorem factorizingMultiplier_one (S₂ : ℝ → ℂ) (θ : Fin 1 → ℝ) :
    factorizingMultiplier S₂ 1 θ = 1 := by
  unfold factorizingMultiplier
  rw [show (Finset.univ.filter fun p : Fin 1 × Fin 1 => p.1 < p.2) = ∅ by decide]
  simp

theorem factorizingMultiplier_two (S₂ : ℝ → ℂ) (θ : Fin 2 → ℝ) :
    factorizingMultiplier S₂ 2 θ = S₂ |θ 0 - θ 1| := by
  unfold factorizingMultiplier
  rw [show (Finset.univ.filter fun p : Fin 2 × Fin 2 => p.1 < p.2) = {(0, 1)} by decide]
  simp

/-- **On a two-particle chamber the relative modular multiplier is the input scattering
function.**  Hence the two descriptions generate the same differential field. -/
theorem factorizingMultiplier_two_chamber (S₂ : ℝ → ℂ) (θ : Fin 2 → ℝ) (h : θ 1 ≤ θ 0) :
    factorizingMultiplier S₂ 2 θ = S₂ (θ 0 - θ 1) := by
  rw [factorizingMultiplier_two, abs_of_nonneg (by linarith)]

theorem factorizingMultiplier_two_diagonal (S₂ : ℝ → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    factorizingMultiplier S₂ 2 ![t, 0] = S₂ t := by
  rw [factorizingMultiplier_two_chamber S₂ _ (by simpa using ht)]
  simp

end Multiplier

end

end GaloisForLFunctions.HTGeometry
