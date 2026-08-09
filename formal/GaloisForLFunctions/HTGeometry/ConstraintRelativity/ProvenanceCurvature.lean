import Mathlib

/-!
# Framed provenance curvature and the universal scalar no-go

Every comparable pair in every partial order is realized as a completion compositor of finite
chains, so a universal scalar on completion defects would be a universal scalar on intervals.

Two independent countertheorems kill the scalar formulation.  The completed nucleus alone forgets
whether raw transport was flat: the same nucleus and the same induced completed leg occur once with
a strict compositor and once with a flat one.  And no finite faithful chain-additive divergence can
also be data-processing for all bottom-preserving join maps — the two-element and three-element
chains already contradict each other.

The positive survivor is the free provenance group: every chain-additive divergence is the pullback
of the universal oriented class `J(x,y) = e_y − e_x` along an observer-chosen potential.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## Completion compositors realize every interval -/

/-- The three-element chain with the closure that collapses the middle point upward. -/
def midClosure : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 2

theorem midClosure_monotone : Monotone midClosure := by decide

theorem midClosure_extensive : ∀ z, z ≤ midClosure z := by decide

theorem midClosure_idempotent : ∀ z, midClosure (midClosure z) = midClosure z := by decide

/-- The raw transport `C₂ → C₃` hitting the non-closed middle point. -/
def rawTransport : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 1

theorem rawTransport_monotone : Monotone rawTransport := by decide

/-- **Lemma 2.1.**  Every comparable pair is exactly a completion compositor of finite chains. -/
theorem interval_is_completion_defect {K : Type*} [PartialOrder K] [OrderBot K] {a b : K}
    (hab : a ≤ b) :
    ∃ V : Fin 3 → K, Monotone V ∧ V 0 = ⊥ ∧
      V (rawTransport 1) = a ∧ V (midClosure (rawTransport 1)) = b := by
  classical
  refine ⟨fun z => if z = 0 then ⊥ else if z = 1 then a else b, ?_, by simp, ?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  · show (if rawTransport 1 = 0 then (⊥ : K) else if rawTransport 1 = 1 then a else b) = a
    rfl
  · show (if midClosure (rawTransport 1) = 0 then (⊥ : K)
      else if midClosure (rawTransport 1) = 1 then a else b) = b
    rfl

/-! ## The nucleus forgets flatness -/

/-- The transport that lands directly in the nucleus. -/
def nucleusTransport : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 2

theorem nucleusTransport_monotone : Monotone nucleusTransport := by decide

/-- The reporter that separates the middle point from the top. -/
def collapseReporter : Fin 3 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1

theorem collapseReporter_monotone : Monotone collapseReporter := by decide

/-- **Theorem 3.1.**  The completed nucleus and the induced completed leg do not determine
flatness: `rawTransport` and `nucleusTransport` have the same completion, `nucleusTransport` lands
in the nucleus, yet the first compositor is strict and the second is flat. -/
theorem nucleus_forgets_flatness :
    (∀ z, midClosure (rawTransport z) = midClosure (nucleusTransport z)) ∧
      (∀ z, midClosure (nucleusTransport z) = nucleusTransport z) ∧
      collapseReporter (rawTransport 1) < collapseReporter (midClosure (rawTransport 1)) ∧
      collapseReporter (nucleusTransport 1)
        = collapseReporter (midClosure (nucleusTransport 1)) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Additive scalars are potentials -/

section Potential

variable {L : Type*} [PartialOrder L] [OrderBot L] (D : L → L → ℝ)

/-- **Theorem 4.1.**  Every chain-additive divergence is a potential difference. -/
theorem additive_eq_potential_sub
    (hadd : ∀ x y z : L, x ≤ y → y ≤ z → D x z = D x y + D y z)
    {x y : L} (hxy : x ≤ y) : D x y = D ⊥ y - D ⊥ x := by
  have h := hadd ⊥ x y bot_le hxy
  linarith

theorem additive_bot_self (hadd : ∀ x y z : L, x ≤ y → y ≤ z → D x z = D x y + D y z) :
    D ⊥ (⊥ : L) = 0 := by
  have h := hadd ⊥ ⊥ (⊥ : L) le_rfl le_rfl
  linarith

/-- **Theorem 4.1, faithfulness.**  A chain-additive nonnegative divergence is faithful exactly
when its potential is strictly increasing. -/
theorem faithful_iff_strict_potential
    (hadd : ∀ x y z : L, x ≤ y → y ≤ z → D x z = D x y + D y z)
    (hnonneg : ∀ x y : L, 0 ≤ D x y) :
    (∀ x y : L, x ≤ y → (D x y = 0 ↔ x = y))
      ↔ (∀ x y : L, x < y → D ⊥ x < D ⊥ y) := by
  constructor
  · intro hfaith x y hlt
    have hne : D x y ≠ 0 := fun h => absurd ((hfaith x y hlt.le).1 h) hlt.ne
    have hpos : 0 < D x y := lt_of_le_of_ne (hnonneg x y) (Ne.symm hne)
    have := additive_eq_potential_sub D hadd hlt.le
    linarith
  · intro hstrict x y hxy
    constructor
    · intro hz
      by_contra hne
      have hlt : x < y := lt_of_le_of_ne hxy hne
      have hs := hstrict x y hlt
      have := additive_eq_potential_sub D hadd hxy
      linarith
    · rintro rfl
      have := additive_eq_potential_sub D hadd (le_refl x)
      linarith

end Potential

/-! ## The sharp scalar no-go -/

/-- The embedding of the two-chain as the extreme interval of the three-chain. -/
def embedExtreme : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 2

/-- The retraction collapsing the middle point downward. -/
def retractDown : Fin 3 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1

/-- The embedding of the two-chain as the lower interval of the three-chain. -/
def embedLower : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 1

/-- The retraction collapsing the middle point upward. -/
def retractUp : Fin 3 → Fin 2
  | 0 => 0
  | 1 => 1
  | 2 => 1

/-- **Theorem 5.1.**  No divergence family on the two- and three-element chains is simultaneously
chain-additive, faithful, and data-processing for the four bottom-preserving join maps between
them. -/
theorem scalar_nogo (D₂ : Fin 2 → Fin 2 → ℝ) (D₃ : Fin 3 → Fin 3 → ℝ)
    (hadd₃ : ∀ x y z : Fin 3, x ≤ y → y ≤ z → D₃ x z = D₃ x y + D₃ y z)
    (hfaith₃ : ∀ x y : Fin 3, x ≤ y → (D₃ x y = 0 ↔ x = y))
    (hdp₁ : ∀ x y : Fin 2, D₃ (embedExtreme x) (embedExtreme y) ≤ D₂ x y)
    (hdp₂ : ∀ x y : Fin 3, D₂ (retractDown x) (retractDown y) ≤ D₃ x y)
    (hdp₃ : ∀ x y : Fin 2, D₃ (embedLower x) (embedLower y) ≤ D₂ x y)
    (hdp₄ : ∀ x y : Fin 3, D₂ (retractUp x) (retractUp y) ≤ D₃ x y) :
    False := by
  have hext : D₃ 0 2 = D₂ 0 1 := by
    have h1 : D₃ 0 2 ≤ D₂ 0 1 := hdp₁ 0 1
    have h2 : D₂ 0 1 ≤ D₃ 0 2 := hdp₂ 0 2
    linarith
  have hlow : D₃ 0 1 = D₂ 0 1 := by
    have h1 : D₃ 0 1 ≤ D₂ 0 1 := hdp₃ 0 1
    have h2 : D₂ 0 1 ≤ D₃ 0 1 := hdp₄ 0 1
    linarith
  have hchain : D₃ 0 2 = D₃ 0 1 + D₃ 1 2 := hadd₃ 0 1 2 (by decide) (by decide)
  have hzero : D₃ 1 2 = 0 := by
    rw [hext, hlow] at hchain
    linarith
  have := (hfaith₃ 1 2 (by decide)).1 hzero
  exact absurd this (by decide)

/-! ## The universal oriented provenance class -/

section Provenance

variable {L : Type*} [PartialOrder L] [OrderBot L] [DecidableEq L]

/-- The free provenance group generator of a point, with the bottom element sent to zero. -/
noncomputable def provenance (x : L) : L →₀ ℤ := if x = ⊥ then 0 else Finsupp.single x 1

/-- **Card `(6.2)`.**  The universal oriented provenance class of a comparable pair. -/
noncomputable def provenanceClass (x y : L) : L →₀ ℤ := provenance y - provenance x

/-- The universal class is chain-additive. -/
theorem provenanceClass_add (x y z : L) :
    provenanceClass x z = provenanceClass x y + provenanceClass y z := by
  simp only [provenanceClass]
  abel

/-- **The universal survivor.**  Every chain-additive divergence is the pullback of the universal
provenance class along an observer-chosen potential. -/
theorem additive_factors_through_provenance (D : L → L → ℝ)
    (hadd : ∀ x y z : L, x ≤ y → y ≤ z → D x z = D x y + D y z) :
    ∃ φ : (L →₀ ℤ) →+ ℝ, ∀ x y : L, x ≤ y → D x y = φ (provenanceClass x y) := by
  classical
  refine ⟨Finsupp.liftAddHom (fun a : L => (zmultiplesHom ℝ (D ⊥ a))), fun x y hxy => ?_⟩
  have hprov : ∀ z : L, (Finsupp.liftAddHom (fun a : L => (zmultiplesHom ℝ (D ⊥ a))))
      (provenance z) = D ⊥ z := by
    intro z
    by_cases hz : z = ⊥
    · subst hz
      simp [provenance, additive_bot_self D hadd]
    · simp [provenance, hz]
  rw [provenanceClass, map_sub, hprov, hprov]
  exact additive_eq_potential_sub D hadd hxy

end Provenance

end HTGeometry.ConstraintRelativity
