import GaloisForLFunctions.HTGeometry.FiniteQuantumTorusRepresentation

/-!
# Cyclic clock lift

An internal endomorphism can be lifted coordinatewise through a finite root-of-unity clock.  The
construction is independent of the coordinate index carried alongside the clock, so detector
representations share one lift and one exact power law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {d : ℕ} [NeZero d] [Fact (1 < d)]

/-- Coordinate amplitudes equipped with a cyclic phase clock. -/
abbrev CyclicClockState (M : Type v) (ι : Type w) (d : ℕ) :=
  ι → ZMod d → M

/-- Lift an internal operator coordinatewise through the root-of-unity clock. -/
def cyclicClockLift {ι : Type w}
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) :
    Module.End K (CyclicClockState M ι d) where
  toFun f x k := finiteQuantumCharacter d q hq k • A (f x k)
  map_add' f g := by
    funext x k
    simp [smul_add]
  map_smul' c f := by
    funext x k
    simp [smul_smul, mul_comm]

/-- Cyclic clock lifting is linear in the internal operator. -/
def cyclicClockLiftLinear {ι : Type w}
    (q : K) (hq : q ^ d = 1) :
    Module.End K M →ₗ[K] Module.End K (CyclicClockState M ι d) where
  toFun := cyclicClockLift q hq
  map_add' A B := by
    apply LinearMap.ext
    intro f
    funext x k
    simp [cyclicClockLift, smul_add]
  map_smul' c A := by
    apply LinearMap.ext
    intro f
    funext x k
    simp [cyclicClockLift, smul_smul, mul_comm]

omit [CharZero K] [Fact (1 < d)] in
/-- Exact power formula for the coordinate-parametric cyclic clock lift. -/
theorem cyclicClockLift_pow_apply {ι : Type w}
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) :
    ∀ r : ℕ, ∀ f : CyclicClockState M ι d, ∀ x : ι, ∀ k : ZMod d,
      ((cyclicClockLift q hq A) ^ r) f x k =
        (finiteQuantumCharacter d q hq k) ^ r • (A ^ r) (f x k)
  | 0, f, x, k => by simp
  | r + 1, f, x, k => by
      rw [pow_succ, Module.End.mul_apply,
        cyclicClockLift_pow_apply (ι := ι) q hq A r]
      simp only [cyclicClockLift, LinearMap.coe_mk, AddHom.coe_mk,
        map_smul, smul_smul, pow_succ]
      rfl

omit [CharZero K] [Fact (1 < d)] in
/-- The cyclic clock lift preserves every scalar `d`th-power identity. -/
theorem cyclicClockLift_pow_degree {ι : Type w}
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (F : K)
    (hA : A ^ d = F • LinearMap.id) :
    (cyclicClockLift (ι := ι) q hq A) ^ d = F • LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext x k
  rw [cyclicClockLift_pow_apply, finiteQuantumCharacter_pow_degree, hA]
  simp

end

end GaloisForLFunctions.HTGeometry
