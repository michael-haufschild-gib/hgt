import GaloisForLFunctions.HTGeometry.UniformizerPowerBasis
import GaloisForLFunctions.HTGeometry.EigenvolumeRamificationSystem

/-!
# When the ramification index exceeds one

For a totally ramified extension the ramification index is the degree, so it exceeds one exactly
when the extension is nontrivial.  This is the local content of the expansion step: what has to be
supplied globally is that the map is not an isomorphism along the horizon, and the local
consequence is then immediate.

Pointwise expansion also discharges the cycle hypothesis of the horizon theorem directly, since a
fixed point of an iterate already carries ramification at the zeroth step.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

section Local

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]

/-- **The ramification index of a totally ramified extension exceeds one exactly when the
extension is nontrivial.** -/
theorem one_lt_ramificationIndex {πA : A} (hπA : Irreducible πA) (e : ℕ)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) {x : B} (hx : addVal B x = 1)
    (hres : ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0)
    (hdvd : algebraMap A B πA ∣ x ^ e) (hdeg : 1 < Module.finrank A B) :
    1 < e := by
  rwa [finrank_eq_ramificationIndex hπA e hram hx hres hdvd] at hdeg

end Local

section System

variable {α : Type*} {F : α → α} {c : α → ℤ} {e : α → ℕ}

/-- **Pointwise expansion discharges the cycle hypothesis.**  If every place of the divisorial
support is ramified, then every recurrent cycle carries ramification, at its zeroth step. -/
theorem ramified_cycle_of_forall_one_lt (h : ∀ y, c y ≠ 0 → 1 < e y) :
    ∀ y : α, c y ≠ 0 → ∀ n : ℕ, 0 < n → F^[n] y = y → ∃ k < n, 1 < e (F^[k] y) :=
  fun y hy n hn _ => ⟨0, hn, by simpa using h y hy⟩

/-- **The horizon is reduced under pointwise expansion.** -/
theorem eigenvolumeOrder_eq_neg_one_of_forall_one_lt
    (hF : Function.Surjective F) (hone : ∀ y, 1 ≤ e y)
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    (hfin : {y : α | c y ≠ 0}.Finite)
    (hexp : ∀ y, c y ≠ 0 → 1 < e y)
    {x : α} (hx : c x ≠ 0) :
    c x = -1 :=
  eigenvolumeOrder_eq_neg_one_of_someRamified hF hone hlaw hfin
    (ramified_cycle_of_forall_one_lt hexp) hx

end System

end GaloisForLFunctions.HTGeometry
