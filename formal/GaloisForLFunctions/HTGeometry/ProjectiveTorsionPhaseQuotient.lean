import GaloisForLFunctions.HTGeometry.PhaseTargetProximity
import GaloisForLFunctions.HTGeometry.PrimeTorsionHardPolygon
import GaloisForLFunctions.HTGeometry.GappedEigenlineTimeUniformFloor

/-!
# The projective torsion phase group and the rays it acts on

The projective `k`-torsion phases of a `D`-level uniform superposition form the quotient of the
group of `k`-torsion phase vectors by its diagonal.  Anchoring at the first coordinate exhibits that
quotient as the free module on the `D-1` relative phases, so it is a group of exponent `k` and order
`k^{D-1}`.

The quotient is exactly what the uniform phase ray sees: translating a phase vector by a diagonal
phase multiplies its ray by a unimodular scalar, and the pure-state trace distance is blind to
that.  Hence every fidelity question about the rays of a phase vector is a question about its
anchored representative.
-/

open RHTower

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section TorsionQuotient

/-- The diagonal phase subgroup `μ_k^{diag}`, in additive coordinates. -/
def diagPhaseHom (D k : ℕ) : ZMod k →+ (Fin D → ZMod k) where
  toFun c := fun _ => c
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem diagPhaseHom_apply (D k : ℕ) (c : ZMod k) (a : Fin D) :
    diagPhaseHom D k c a = c := rfl

/-- Anchoring at the first coordinate: the `D-1` relative phases. -/
def anchorPhaseHom (d k : ℕ) : (Fin (d + 1) → ZMod k) →+ (Fin d → ZMod k) where
  toFun m := fun j => m j.succ - m 0
  map_zero' := by funext j; simp
  map_add' m n := by
    funext j
    show (m + n) j.succ - (m + n) 0 = (m j.succ - m 0) + (n j.succ - n 0)
    simp only [Pi.add_apply]
    ring

@[simp] theorem anchorPhaseHom_apply (d k : ℕ) (m : Fin (d + 1) → ZMod k) (j : Fin d) :
    anchorPhaseHom d k m j = m j.succ - m 0 := rfl

theorem anchorPhaseHom_surjective (d k : ℕ) : Function.Surjective (anchorPhaseHom d k) := by
  intro n
  refine ⟨Fin.cons 0 n, ?_⟩
  funext j
  rw [anchorPhaseHom_apply, Fin.cons_succ, Fin.cons_zero, sub_zero]

/-- The anchoring kernel is precisely the diagonal. -/
theorem ker_anchorPhaseHom (d k : ℕ) :
    (anchorPhaseHom d k).ker = (diagPhaseHom (d + 1) k).range := by
  ext m
  constructor
  · intro hm
    have hm' : ∀ j : Fin d, m j.succ - m 0 = 0 := by
      intro j
      have := AddMonoidHom.mem_ker.mp hm
      exact congrFun this j
    refine ⟨m 0, ?_⟩
    funext a
    refine Fin.cases ?_ ?_ a
    · rfl
    · intro j
      have := hm' j
      show m 0 = m j.succ
      linear_combination -this
  · rintro ⟨c, rfl⟩
    rw [AddMonoidHom.mem_ker]
    funext j
    rw [anchorPhaseHom_apply, diagPhaseHom_apply, diagPhaseHom_apply, sub_self]
    rfl

/-- **`(2)`.**  The projective `k`-torsion phase group `Q_{D,k} = μ_k^D / μ_k^{diag}`. -/
abbrev projPhaseTorsion (d k : ℕ) : Type :=
  (Fin (d + 1) → ZMod k) ⧸ (diagPhaseHom (d + 1) k).range

/-- **The identification of `Q_{D,k}` with the anchored model.** -/
def projPhaseTorsionEquiv (d k : ℕ) : projPhaseTorsion d k ≃+ (Fin d → ZMod k) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_anchorPhaseHom d k).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (anchorPhaseHom_surjective d k))

/-- **`(3)`.**  The projective torsion group has order `k^{D-1}`. -/
theorem card_projPhaseTorsion (d k : ℕ) [NeZero k] :
    Nat.card (projPhaseTorsion d k) = k ^ d := by
  classical
  rw [Nat.card_congr (projPhaseTorsionEquiv d k).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

end TorsionQuotient

section TorsionRays

variable {D d k : ℕ}

/-- The unimodular phase vector of a `k`-torsion phase class representative. -/
def torsionPhaseVec (k : ℕ) [NeZero k] {D : ℕ} (m : Fin D → ZMod k) : Fin D → ℂ :=
  fun a => (ZMod.toCircle (m a) : ℂ)

@[simp] theorem norm_torsionPhaseVec [NeZero k] (m : Fin D → ZMod k) (a : Fin D) :
    ‖torsionPhaseVec k m a‖ = 1 := Circle.norm_coe _

/-- **`(1)` at a torsion phase.**  The uniform phase ray of a `k`-torsion phase vector. -/
def torsionRay (k : ℕ) [NeZero k] {D : ℕ} (m : Fin D → ZMod k) : EuclideanSpace ℂ (Fin D) :=
  phaseRay (torsionPhaseVec k m)

theorem norm_torsionRay [NeZero k] (m : Fin D → ZMod k) (hD : 0 < D) : ‖torsionRay k m‖ = 1 :=
  norm_phaseRay (fun a => norm_torsionPhaseVec m a) hD

/-- Scaling a phase vector by a constant scales its ray. -/
theorem phaseRay_const_mul (c : ℂ) (q : Fin D → ℂ) :
    phaseRay (fun a => c * q a) = c • phaseRay q := by
  refine PiLp.ext fun a => ?_
  show ((Real.sqrt (D : ℝ))⁻¹ : ℂ) * (c * q a) = c * (((Real.sqrt (D : ℝ))⁻¹ : ℂ) * q a)
  ring

/-- The ray map is additive. -/
theorem phaseRay_sub (q r : Fin D → ℂ) :
    phaseRay q - phaseRay r = phaseRay (fun a => q a - r a) := by
  refine PiLp.ext fun a => ?_
  show ((Real.sqrt (D : ℝ))⁻¹ : ℂ) * q a - ((Real.sqrt (D : ℝ))⁻¹ : ℂ) * r a
      = ((Real.sqrt (D : ℝ))⁻¹ : ℂ) * (q a - r a)
  ring

/-- Translating by a diagonal phase multiplies the ray by a unimodular scalar. -/
theorem torsionRay_add_diag [NeZero k] (m : Fin D → ZMod k) (c : ZMod k) :
    torsionRay k (m + fun _ => c) = ((ZMod.toCircle c : ℂ)) • torsionRay k m := by
  have hvec : torsionPhaseVec k (m + fun _ => c)
      = fun a => (ZMod.toCircle c : ℂ) * torsionPhaseVec k m a := by
    funext a
    show (ZMod.toCircle (m a + c) : ℂ) = (ZMod.toCircle c : ℂ) * (ZMod.toCircle (m a) : ℂ)
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm]
  rw [torsionRay, torsionRay, hvec, phaseRay_const_mul]

/-- The pure-state trace distance only sees the projective class of a phase vector. -/
theorem pureStateTraceDistance_torsionRay_add_diag [NeZero k] (m : Fin D → ZMod k) (c : ZMod k)
    (y : EuclideanSpace ℂ (Fin D)) :
    pureStateTraceDistance (torsionRay k (m + fun _ => c)) y
      = pureStateTraceDistance (torsionRay k m) y := by
  rw [torsionRay_add_diag]
  exact _root_.HTGeometry.pureStateTraceDistance_smul_left _ (Circle.norm_coe _) _ _

/-- The anchored representative of a projective torsion class, as a ray. -/
def anchoredRay (k : ℕ) [NeZero k] {d : ℕ} (n : Fin d → ZMod k) : EuclideanSpace ℂ (Fin (d + 1)) :=
  torsionRay k (Fin.cons 0 n)

theorem norm_anchoredRay [NeZero k] (n : Fin d → ZMod k) : ‖anchoredRay k n‖ = 1 :=
  norm_torsionRay _ (Nat.succ_pos d)

/-- **The rays of `(1)` are a function of the projective class.**  Every phase vector has the same
trace distances as the anchored representative of its class. -/
theorem pureStateTraceDistance_torsionRay_eq_anchored [NeZero k] (m : Fin (d + 1) → ZMod k)
    (y : EuclideanSpace ℂ (Fin (d + 1))) :
    pureStateTraceDistance (torsionRay k m) y
      = pureStateTraceDistance (anchoredRay k (anchorPhaseHom d k m)) y := by
  have hm : m = (Fin.cons 0 (anchorPhaseHom d k m) : Fin (d + 1) → ZMod k) + fun _ => m 0 := by
    funext a
    refine Fin.cases ?_ ?_ a
    · simp only [Pi.add_apply, Fin.cons_zero, zero_add]
    · intro j
      simp only [Pi.add_apply, Fin.cons_succ, anchorPhaseHom_apply, sub_add_cancel]
  conv_lhs => rw [hm]
  rw [pureStateTraceDistance_torsionRay_add_diag]
  rfl

/-- **`(6)`.**  The easy projective classes: those whose anchored ray is within `delta` of some
target of the dictionary. -/
def easyAnchored (k : ℕ) [NeZero k] {d : ℕ} (Y : Finset (EuclideanSpace ℂ (Fin (d + 1))))
    (δ : ℝ) : Finset (Fin d → ZMod k) :=
  letI := Classical.decPred fun n : Fin d → ZMod k =>
    ∃ y ∈ Y, pureStateTraceDistance (anchoredRay k n) y ≤ δ
  Finset.univ.filter fun n => ∃ y ∈ Y, pureStateTraceDistance (anchoredRay k n) y ≤ δ

theorem mem_easyAnchored [NeZero k] {Y : Finset (EuclideanSpace ℂ (Fin (d + 1)))} {δ : ℝ}
    {n : Fin d → ZMod k} :
    n ∈ easyAnchored k Y δ ↔ ∃ y ∈ Y, pureStateTraceDistance (anchoredRay k n) y ≤ δ := by
  simp only [easyAnchored, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A class outside the easy set is strictly harder than `delta` against every target. -/
theorem lt_pureStateTraceDistance_of_not_mem_easyAnchored [NeZero k]
    {Y : Finset (EuclideanSpace ℂ (Fin (d + 1)))} {δ : ℝ} {n : Fin d → ZMod k}
    (hn : n ∉ easyAnchored k Y δ) {y : EuclideanSpace ℂ (Fin (d + 1))} (hy : y ∈ Y) :
    δ < pureStateTraceDistance (anchoredRay k n) y := by
  by_contra h
  exact hn (mem_easyAnchored.mpr ⟨y, hy, not_lt.mp h⟩)

end TorsionRays

end

end GaloisForLFunctions.HTGeometry
