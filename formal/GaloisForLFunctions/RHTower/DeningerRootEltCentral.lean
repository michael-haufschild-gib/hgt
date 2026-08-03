import GaloisForLFunctions.RHTower.DeningerRootUniqueRoots
import GaloisForLFunctions.RHTower.DeningerRootElement

/-!
# The adjoined root is self-centralizing

The adjoined root generates the infinite cyclic factor of a root adjunction and does not lie in the
base group, and that factor is abelian, so it does not conjugate into the base group either.  The
centralizer criterion for factor elements therefore places every element commuting with it inside
that factor, which is the cyclic group it generates.

* `deningerRootGen_not_mem` : the generator is not in the base group.
* `deningerRootElt_centralizer` : the centralizer of the adjoined root.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

variable (A : Type u) [Group A] (a : A) (m : ℤ)

/-- **The generator of the cyclic factor is not in the base group** when the exponent is at least two
in absolute value. -/
theorem deningerRootGen_not_mem (hm2 : 2 ≤ m.natAbs) :
    deningerRootGen.{u} ∉ (deningerRootMap A a m (ULift.up false)).range := by
  rintro ⟨w, hw⟩
  have h1 : (MulEquiv.ulift w) ^ m = Multiplicative.ofAdd (1 : ℤ) :=
    MulEquiv.ulift.symm.injective hw
  have h3 : m * Multiplicative.toAdd (MulEquiv.ulift w) = 1 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [mul_comm] using this
  have hdvd : m ∣ 1 := ⟨Multiplicative.toAdd (MulEquiv.ulift w), h3.symm⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hdvd) with h | h <;> omega

/-- **The centralizer of the adjoined root** is the cyclic group it generates. -/
theorem deningerRootElt_centralizer (hm : m ≠ 0) (hm2 : 2 ≤ m.natAbs)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (w : PushoutI (deningerRootMap A a m))
    (hcomm : w * deningerRootElt A a m = deningerRootElt A a m * w) :
    w ∈ Subgroup.zpowers (deningerRootElt A a m) := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  have hgen := deningerRootGen_not_mem A a m hm2
  obtain ⟨x, hx⟩ | ⟨x', k, hk⟩ :=
    deningerCentralizer_factor (d := d) (ULift.up false) deningerRootGen.{u} hgen w hcomm
  · obtain ⟨c, hc⟩ : ∃ c : ℤ, deningerRootGen.{u} ^ c = x := by
      refine ⟨Multiplicative.toAdd (MulEquiv.ulift x), ?_⟩
      apply MulEquiv.ulift.injective
      apply Multiplicative.toAdd.injective
      simp [deningerRootGen]
    refine ⟨c, ?_⟩
    show (deningerRootElt A a m) ^ c = w
    rw [deningerRootElt, ← map_zpow, hx]
    exact congrArg (PushoutI.of (φ := deningerRootMap A a m) (ULift.up false)) hc
  · refine absurd ⟨k, ?_⟩ hgen
    exact (deningerRootFactorFalse_conj A x'⁻¹ deningerRootGen.{u} _
      (by rw [inv_inv]; exact hk)).symm

end RootAdjunction

end RHTower
