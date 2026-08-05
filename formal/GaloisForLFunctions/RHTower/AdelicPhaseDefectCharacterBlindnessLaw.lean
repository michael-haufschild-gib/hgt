import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Phase defects, reciprocity, and character blindness

A *local phase* is an arbitrary map `γ : G → N` from a commutative group of scalings to a
commutative group of values.  Its **coboundary defect**

```text
μ(a,b) = γ a * γ b * (γ 1 * γ (a * b))⁻¹
```

is the failure of `γ` to be multiplicative after normalisation at the unit.  This is the shape in
which reciprocity laws present themselves: for the Kashiwara–Maslov phase of a triple of
Lagrangians the defect of the one-dimensional Weil index is the local Hilbert symbol, and Hilbert
reciprocity is the statement that the product of the local defects over all places is trivial.

Two facts organise the whole layer.

* **Classification.** Two normalised phases have the same defect exactly when they differ by a
  group character.  So the defect layer is precisely the quotient of the phase layer by the
  character group.
* **Reciprocity.** For a finite family of places, the product of the local defects is itself the
  coboundary defect of the global normalised phase.  Total-defect triviality is therefore
  equivalent to multiplicativity of the global phase, and nothing more.

The classification has an immediate negative consequence.  A criterion formulated purely at the
defect level cannot detect a character twist, because the twist does not change the defect.  In
the Riemann setting the two endpoint residues of the rational adelic source are the characters

```text
α_ρ(ℓ) = (1/2 - Re ρ) · ℓ,   β_ρ(ℓ) = (Re ρ - 1/2) · ℓ
```

on the logarithmic scaling group, and the critical line is exactly the statement `α_ρ = 1`.  Their
product is trivial for every spectral parameter — this is the adelic product formula — so the
product carries no information about `Re ρ`.  The last theorem here upgrades that observation:
*no* predicate on defect data whatsoever is equivalent to `Re ρ = 1/2`.
-/

namespace GaloisForLFunctions.RHTower

variable {G N : Type*} [CommGroup G] [CommGroup N]

/-! ## Normalised phases and their defects -/

/-- The local phase renormalised to send the unit to the unit. -/
def normalizedPhase (γ : G → N) (a : G) : N := γ a * (γ 1)⁻¹

/-- The coboundary defect of a local phase: its failure to be multiplicative after
normalisation at the unit. -/
def phaseDefect (γ : G → N) (a b : G) : N := γ a * γ b * (γ 1 * γ (a * b))⁻¹

@[simp]
theorem normalizedPhase_one (γ : G → N) : normalizedPhase γ 1 = 1 := by
  simp [normalizedPhase]

/-- The defect only depends on the normalised phase, and is its coboundary. -/
theorem phaseDefect_eq_normalizedPhase (γ : G → N) (a b : G) :
    phaseDefect γ a b =
      normalizedPhase γ a * normalizedPhase γ b * (normalizedPhase γ (a * b))⁻¹ := by
  simp [phaseDefect, normalizedPhase, mul_comm, mul_left_comm, mul_assoc, mul_inv_rev]

@[simp]
theorem phaseDefect_one_left (γ : G → N) (b : G) : phaseDefect γ 1 b = 1 := by
  simp [phaseDefect, mul_comm, mul_left_comm, mul_assoc, mul_inv_rev]

@[simp]
theorem phaseDefect_one_right (γ : G → N) (a : G) : phaseDefect γ a 1 = 1 := by
  simp [phaseDefect, mul_comm, mul_left_comm, mul_assoc, mul_inv_rev]

/-- The defect is symmetric. -/
theorem phaseDefect_comm (γ : G → N) (a b : G) : phaseDefect γ a b = phaseDefect γ b a := by
  simp [phaseDefect, mul_comm, mul_assoc, mul_inv_rev]

/-- The defect is a two-cocycle. -/
theorem phaseDefect_cocycle (γ : G → N) (a b c : G) :
    phaseDefect γ a b * phaseDefect γ (a * b) c =
      phaseDefect γ b c * phaseDefect γ a (b * c) := by
  simp only [phaseDefect]
  rw [show a * b * c = a * (b * c) from mul_assoc a b c]
  simp [mul_comm, mul_left_comm, mul_assoc, mul_inv_rev]

/-- The defect vanishes exactly when the normalised phase is a homomorphism. -/
theorem phaseDefect_eq_one_iff (γ : G → N) (a b : G) :
    phaseDefect γ a b = 1 ↔
      normalizedPhase γ (a * b) = normalizedPhase γ a * normalizedPhase γ b := by
  rw [phaseDefect_eq_normalizedPhase, mul_inv_eq_one]
  exact eq_comm

/-! ## Character blindness and the classification of defects -/

/-- **Character blindness.** Twisting a local phase by a character does not change its defect. -/
theorem phaseDefect_character_smul (χ : G →* N) (γ : G → N) :
    phaseDefect (fun a => χ a * γ a) = phaseDefect γ := by
  funext a b
  simp [phaseDefect, map_mul, map_one, mul_comm, mul_left_comm, mul_assoc, mul_inv_rev]

/-- **Phase-defect classification.**  Two phases normalised at the unit have the same defect
exactly when they differ by a character.  The defect layer is therefore the quotient of the phase
layer by the character group, and carries no more information than that quotient. -/
theorem phaseDefect_eq_iff_exists_character {γ δ : G → N} (hγ : γ 1 = 1) (hδ : δ 1 = 1) :
    phaseDefect γ = phaseDefect δ ↔ ∃ χ : G →* N, ∀ a, δ a = χ a * γ a := by
  constructor
  · intro h
    have key : ∀ a b : G, δ a * (γ a)⁻¹ * (δ b * (γ b)⁻¹) = δ (a * b) * (γ (a * b))⁻¹ := by
      intro a b
      have hab := congrFun (congrFun h a) b
      simp only [phaseDefect, hγ, hδ, one_mul] at hab
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at hab
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_mul_div_comm,
        div_eq_div_iff_mul_eq_mul, mul_comm (δ (a * b)) (γ a * γ b)]
      exact hab.symm
    refine ⟨{ toFun := fun a => δ a * (γ a)⁻¹
              map_one' := by simp [hγ, hδ]
              map_mul' := fun a b => (key a b).symm }, fun a => ?_⟩
    simp
  · rintro ⟨χ, hχ⟩
    have hδγ : δ = fun a => χ a * γ a := funext hχ
    rw [hδγ, phaseDefect_character_smul]

/-! ## Reciprocity over a finite family of places -/

variable {V : Type*} [Fintype V]

/-- The global normalised phase attached to a finite family of local phases. -/
def globalPhase (γ : V → G → N) (a : G) : N := ∏ v, normalizedPhase (γ v) a

@[simp]
theorem globalPhase_one (γ : V → G → N) : globalPhase γ 1 = 1 := by
  simp [globalPhase]

/-- **Abstract reciprocity.**  The product of the local defects over all places is the coboundary
defect of the global normalised phase.  Nothing beyond the global phase enters. -/
theorem prod_phaseDefect (γ : V → G → N) (a b : G) :
    ∏ v, phaseDefect (γ v) a b =
      globalPhase γ a * globalPhase γ b * (globalPhase γ (a * b))⁻¹ := by
  simp only [phaseDefect_eq_normalizedPhase, globalPhase]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

/-- Total-defect triviality is exactly multiplicativity of the global phase.  This is the abstract
form of Hilbert reciprocity: the local symbols multiply to one over all places precisely because
the normalised global Bruhat word is multiplicative. -/
theorem prod_phaseDefect_eq_one_iff (γ : V → G → N) :
    (∀ a b : G, ∏ v, phaseDefect (γ v) a b = 1) ↔
      ∀ a b : G, globalPhase γ (a * b) = globalPhase γ a * globalPhase γ b := by
  constructor
  · intro h a b
    have hab := h a b
    rw [prod_phaseDefect, mul_inv_eq_one] at hab
    exact hab.symm
  · intro h a b
    rw [prod_phaseDefect, mul_inv_eq_one]
    exact (h a b).symm

/-- Twisting every local phase by a single character leaves the total defect unchanged. -/
theorem prod_phaseDefect_character_smul (χ : G →* N) (γ : V → G → N) (a b : G) :
    ∏ v, phaseDefect (fun x => χ x * γ v x) a b = ∏ v, phaseDefect (γ v) a b :=
  Finset.prod_congr rfl fun v _ =>
    congrFun (congrFun (phaseDefect_character_smul χ (γ v)) a) b

/-! ## No defect-level criterion detects a character -/

/-- **Defect-level blindness.**  If a predicate on defect data is equivalent to triviality of the
twisting character, then every character is trivial.  Contrapositively, as soon as one nontrivial
character exists, no such predicate does. -/
theorem eq_one_of_phaseDefect_criterion {P : (G → G → N) → Prop} {γ : G → N}
    (hP : ∀ χ : G →* N, P (phaseDefect fun a => χ a * γ a) ↔ χ = 1) (χ : G →* N) : χ = 1 := by
  have hrw : ∀ ψ : G →* N, phaseDefect (fun a => ψ a * γ a) = phaseDefect γ :=
    fun ψ => phaseDefect_character_smul ψ γ
  have hbase : P (phaseDefect γ) := by
    have h1 : P (phaseDefect fun a => (1 : G →* N) a * γ a) := (hP 1).mpr rfl
    rwa [hrw] at h1
  exact (hP χ).mp (by rw [hrw]; exact hbase)

/-- No defect-level criterion can detect a character twist once a nontrivial character exists. -/
theorem not_exists_phaseDefect_criterion {γ : G → N} (χ₀ : G →* N) (hχ₀ : χ₀ ≠ 1) :
    ¬ ∃ P : (G → G → N) → Prop,
      ∀ χ : G →* N, P (phaseDefect fun a => χ a * γ a) ↔ χ = 1 := by
  rintro ⟨P, hP⟩
  exact hχ₀ (eq_one_of_phaseDefect_criterion hP χ₀)

/-! ## The Riemann endpoint characters -/

/-- The logarithmic scaling group: the additive reals `ℓ(q) = log |q|` written multiplicatively. -/
abbrev LogScaling : Type := Multiplicative ℝ

/-- The power character `ℓ ↦ s · ℓ` of the logarithmic scaling group. -/
noncomputable def logScalingCharacter (s : ℝ) : LogScaling →* LogScaling where
  toFun a := Multiplicative.ofAdd (s * Multiplicative.toAdd a)
  map_one' := by simp
  map_mul' a b := by
    show Multiplicative.ofAdd (s * (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [mul_add, ofAdd_add]

@[simp]
theorem logScalingCharacter_apply (s : ℝ) (a : LogScaling) :
    logScalingCharacter s a = Multiplicative.ofAdd (s * Multiplicative.toAdd a) := rfl

theorem logScalingCharacter_eq_one_iff (s : ℝ) : logScalingCharacter s = 1 ↔ s = 0 := by
  constructor
  · intro h
    have h1 := congrArg
      (fun f : LogScaling →* LogScaling =>
        Multiplicative.toAdd (f (Multiplicative.ofAdd (1 : ℝ)))) h
    simpa [logScalingCharacter] using h1
  · rintro rfl
    ext a
    simp [logScalingCharacter]

@[simp]
theorem logScalingCharacter_zero : logScalingCharacter 0 = 1 :=
  (logScalingCharacter_eq_one_iff 0).mpr rfl

theorem logScalingCharacter_add (s t : ℝ) :
    logScalingCharacter (s + t) = logScalingCharacter s * logScalingCharacter t := by
  ext a
  simp [logScalingCharacter, add_mul, ofAdd_add]

/-- Source-inverse endpoint residue `α_ρ(ℓ) = (1/2 - Re ρ) · ℓ`. -/
noncomputable def xiSourceInverseCharacter (ρ : ℂ) : LogScaling →* LogScaling :=
  logScalingCharacter (1 / 2 - ρ.re)

/-- Analytic-adjoint endpoint residue `β_ρ(ℓ) = (Re ρ - 1/2) · ℓ`. -/
noncomputable def xiAnalyticAdjointCharacter (ρ : ℂ) : LogScaling →* LogScaling :=
  logScalingCharacter (ρ.re - 1 / 2)

/-- Triviality of the source-inverse endpoint residue is exactly the critical line. -/
theorem xiSourceInverseCharacter_eq_one_iff (ρ : ℂ) :
    xiSourceInverseCharacter ρ = 1 ↔ ρ.re = 1 / 2 := by
  rw [xiSourceInverseCharacter, logScalingCharacter_eq_one_iff, sub_eq_zero]
  exact eq_comm

/-- **Adelic product formula shadow.**  The two endpoint residues are inverse to one another for
*every* spectral parameter, so their product is the trivial character throughout the critical
strip and separates nothing. -/
theorem xiSourceInverse_mul_xiAnalyticAdjoint (ρ : ℂ) :
    xiSourceInverseCharacter ρ * xiAnalyticAdjointCharacter ρ = 1 := by
  rw [xiSourceInverseCharacter, xiAnalyticAdjointCharacter, ← logScalingCharacter_add]
  simp

/-- **Critical-line blindness of the defect layer.**  No predicate on coboundary-defect data is
equivalent to the critical-line condition on the source-inverse endpoint residue.  Any argument
that reaches only reciprocity — the product of the two endpoint residues, or any invariant
factoring through the defect of the twisted phase — is therefore incapable of forcing
`Re ρ = 1/2`. -/
theorem no_phaseDefect_criterion_detects_criticalLine (γ : LogScaling → LogScaling)
    (P : (LogScaling → LogScaling → LogScaling) → Prop)
    (hP : ∀ ρ : ℂ, P (phaseDefect fun a => xiSourceInverseCharacter ρ a * γ a) ↔ ρ.re = 1 / 2) :
    False := by
  have hrw : ∀ ρ : ℂ,
      phaseDefect (fun a => xiSourceInverseCharacter ρ a * γ a) = phaseDefect γ :=
    fun ρ => phaseDefect_character_smul _ γ
  have hhalf : P (phaseDefect γ) := by
    have h := (hP (((1 : ℝ) / 2 : ℝ) : ℂ)).mpr (by simp)
    rwa [hrw] at h
  have hone : ((1 : ℂ)).re = 1 / 2 := by
    refine (hP 1).mp ?_
    rw [hrw]
    exact hhalf
  rw [Complex.one_re] at hone
  linarith

end GaloisForLFunctions.RHTower
