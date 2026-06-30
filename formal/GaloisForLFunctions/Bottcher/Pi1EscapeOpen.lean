/-
# `π₁(escapeOpen) ≅ ℤ`

The far field `escapeOpen c = { ‖z‖ > R }` (`R = max 2 ‖c‖`) is the exterior of a disk. Its universal
cover is `exp` restricted to the half-plane `{ Re z > log R }` (convex, hence simply connected): `exp`
maps it onto `escapeOpen` (`‖exp z‖ = e^{Re z} > R`), and it is the full `exp`-preimage. So the abstract
`IsCoveringMap.pi1FiberEquiv` (universal cover ⟹ `π₁ ≃` fiber) gives `π₁(escapeOpen) ≅ ℤ` exactly as for
`ℂ*`.
-/
import GaloisForLFunctions.Bottcher.CoveringPi1
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Topology

namespace Bottcher

/-- `exp z ∈ escapeOpen c ↔ log R < Re z` where `R = max 2 ‖c‖`. -/
theorem exp_mem_escapeOpen_iff (c : ℂ) (z : ℂ) :
    Complex.exp z ∈ escapeOpen c ↔ Real.log (max 2 ‖c‖) < z.re := by
  have hR : (0 : ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  simp only [escapeOpen, Set.mem_setOf_eq, Complex.norm_exp]
  exact (Real.log_lt_iff_lt_exp hR).symm

/-- The `exp`-preimage of `escapeOpen c` is the open half-plane `{ Re z > log R }`. -/
theorem preimage_exp_escapeOpen (c : ℂ) :
    Complex.exp ⁻¹' (escapeOpen c) = {z : ℂ | Real.log (max 2 ‖c‖) < z.re} := by
  ext z; simp only [Set.mem_preimage, Set.mem_setOf_eq, exp_mem_escapeOpen_iff]

/-- That half-plane is convex. -/
theorem convex_preimage_exp_escapeOpen (c : ℂ) :
    Convex ℝ (Complex.exp ⁻¹' (escapeOpen c)) := by
  rw [preimage_exp_escapeOpen]
  exact convex_halfSpace_gt ⟨fun x y => Complex.add_re x y, fun a x => by simp⟩ _

/-- Hence the half-plane subtype is simply connected. -/
noncomputable instance simplyConnected_preimage_exp_escapeOpen (c : ℂ) :
    SimplyConnectedSpace (Complex.exp ⁻¹' (escapeOpen c)) := by
  have hne : (Complex.exp ⁻¹' (escapeOpen c)).Nonempty := by
    refine ⟨Real.log (max 2 ‖c‖) + 1, ?_⟩
    rw [preimage_exp_escapeOpen]; simp
  haveI : ContractibleSpace (Complex.exp ⁻¹' (escapeOpen c)) :=
    (convex_preimage_exp_escapeOpen c).contractibleSpace hne
  infer_instance

/-- `exp` restricted to its preimage is a covering map onto `escapeOpen c`. -/
theorem isCoveringMap_exp_escapeOpen (c : ℂ) :
    IsCoveringMap ((escapeOpen c).restrictPreimage Complex.exp) := by
  have h0 : escapeOpen c ⊆ {0}ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp only [escapeOpen, Set.mem_setOf_eq, norm_zero] at hz
    have : (0 : ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    linarith
  exact (Complex.isCoveringMapOn_exp.mono h0).isCoveringMap_restrictPreimage

/-- **`π₁(escapeOpen c, w₀) ≃ fiber`** of the `exp` universal cover, for any basepoint. -/
noncomputable def pi1EscapeOpenEquivFiber (c : ℂ) (w₀ : escapeOpen c)
    (e₀ : ((escapeOpen c).restrictPreimage Complex.exp) ⁻¹' {w₀}) :
    Path.Homotopic.Quotient w₀ w₀ ≃ ((escapeOpen c).restrictPreimage Complex.exp) ⁻¹' {w₀} :=
  (isCoveringMap_exp_escapeOpen c).pi1FiberEquiv w₀ e₀

end Bottcher
