import GaloisForLFunctions.RHTower.SuzukiResidualOvercrowding
import GaloisForLFunctions.RHTower.SuzukiCompactifiedPhaseProfile

/-!
# The Suzuki compactified labels are a reflection-paired monotone family

The residual-overcrowding theorems are order combinatorics of an abstract label family.  This
module discharges that abstraction: Suzuki's own compactified inverse-phase labels

`u k = arctan (φ⁻¹ (π + (2k - 1) π))`

are strictly increasing in the index and obey the reflection pairing `u (1 - k) = -u k`, because
the even phase lattice is strictly increasing and odd under `k ↦ 1 - k`, and the compactified
inverse phase is strictly increasing and odd under the source reflection normalization.

Consequently every conclusion of the abstract theorems applies to the concrete Suzuki family: the
window label count bounds the label index, the interior escaped-label tail vanishes identically,
and eventual Rouché count stability closes the interior residual.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-- The Suzuki compactified inverse-phase label family. -/
noncomputable def suzukiCompactifiedLabel (φ : ℝ ≃o ℝ) (k : ℤ) : ℝ :=
  suzukiCompactifiedInversePhase φ (suzukiEvenPhaseLattice k)

theorem suzukiEvenPhaseLattice_strictMono : StrictMono suzukiEvenPhaseLattice := by
  intro j k hjk
  rw [suzukiEvenPhaseLattice, suzukiEvenPhaseLattice]
  have hj : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith

theorem suzukiEvenPhaseLattice_one_sub (k : ℤ) :
    suzukiEvenPhaseLattice (1 - k) = -suzukiEvenPhaseLattice k := by
  rw [suzukiEvenPhaseLattice, suzukiEvenPhaseLattice]
  push_cast
  ring

/-- **The labels are strictly increasing in the index.** -/
theorem suzukiCompactifiedLabel_strictMono (φ : ℝ ≃o ℝ) :
    StrictMono (suzukiCompactifiedLabel φ) :=
  (suzukiCompactifiedInversePhase_strictMono φ).comp suzukiEvenPhaseLattice_strictMono

/-- **The labels obey the reflection pairing.** -/
theorem suzukiCompactifiedLabel_reflect {φ : ℝ ≃o ℝ}
    (hreflection : ∀ x, φ (-x) = 2 * Real.pi - φ x) (k : ℤ) :
    suzukiCompactifiedLabel φ (1 - k) = -suzukiCompactifiedLabel φ k := by
  rw [suzukiCompactifiedLabel, suzukiCompactifiedLabel, suzukiEvenPhaseLattice_one_sub,
    suzukiCompactifiedInversePhase_neg hreflection]

/-- **Uniform label-head bound for the concrete Suzuki family.** -/
theorem suzuki_abs_le_card_labelWindow {φ : ℝ ≃o ℝ}
    (hreflection : ∀ x, φ (-x) = 2 * Real.pi - φ x)
    {r : ℝ} (hfin : (labelWindow (suzukiCompactifiedLabel φ) r).Finite)
    {k : ℤ} (hle : |suzukiCompactifiedLabel φ k| ≤ r) :
    |k| ≤ (hfin.toFinset.card : ℤ) :=
  abs_le_card_labelWindow (suzukiCompactifiedLabel_strictMono φ)
    (suzukiCompactifiedLabel_reflect hreflection) hfin hle

/-- **The interior escaped-label tail of the concrete Suzuki family vanishes.** -/
theorem suzuki_escapedTail_eq_zero {φ : ℝ ≃o ℝ}
    (hreflection : ∀ x, φ (-x) = 2 * Real.pi - φ x)
    {r : ℝ} (hfin : (labelWindow (suzukiCompactifiedLabel φ) r).Finite) {f : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0) {k : ℤ} (hk : (hfin.toFinset.card : ℤ) < |k|) :
    f (suzukiCompactifiedLabel φ k) = 0 :=
  escapedTail_eq_zero (suzukiCompactifiedLabel_strictMono φ)
    (suzukiCompactifiedLabel_reflect hreflection) hfin hsupp hk

/-- **Theorem C on the concrete family.**  Eventual Rouché count stability in one interior window
closes the interior residual of the Suzuki compactified label family. -/
theorem suzuki_residual_eq_zero_of_eventually_count
    {Φ : ℕ → ℝ ≃o ℝ} {P : ℕ → ℤ → ℝ} {p u : ℤ → ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {S : ℕ → ℝ} {Sinf L : ℝ}
    (hreflection : ∀ i, ∀ x, (Φ i) (-x) = 2 * Real.pi - (Φ i) x)
    {r : ℝ} (hfin : ∀ i, (labelWindow (suzukiCompactifiedLabel (Φ i)) r).Finite) {M : ℕ}
    (hcount : ∀ᶠ i in atTop, (hfin i).toFinset.card ≤ M)
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0)
    (hSsum : ∀ i, HasSum (fun k => P i k * f (suzukiCompactifiedLabel (Φ i) k)) (S i))
    (hS : Tendsto S atTop (𝓝 Sinf))
    (hP : ∀ k, Tendsto (fun i => P i k) atTop (𝓝 (p k)))
    (hU : ∀ k, Tendsto (fun i => suzukiCompactifiedLabel (Φ i) k) atTop (𝓝 (u k)))
    (hL : Tendsto (fun K : ℕ => labelHead p (fun k => f (u k)) K) atTop (𝓝 L)) :
    Sinf = L :=
  residual_eq_zero_of_eventually_count hf
    (fun i => suzukiCompactifiedLabel_strictMono (Φ i))
    (fun i => suzukiCompactifiedLabel_reflect (hreflection i)) hfin hcount hsupp hSsum hS hP hU hL

/-! ## Fixed-lattice rigidity: the phase lift is injective -/

/-- **The compactified inverse phase determines the phase.**  Cayley compactification and the fixed
centering are both injective, so two carriers with the same compactified inverse phase have the same
underlying order isomorphism.  This is the last link of the fixed-lattice rigidity chain: once the
Donoghue data agree, the carriers agree. -/
theorem suzukiCompactifiedInversePhase_injective :
    Function.Injective (suzukiCompactifiedInversePhase : (ℝ ≃o ℝ) → ℝ → ℝ) := by
  intro φ ψ h
  have hsymm : (φ.symm : ℝ → ℝ) = (ψ.symm : ℝ → ℝ) := by
    funext x
    have hx := congrFun h (x - Real.pi)
    rw [suzukiCompactifiedInversePhase, suzukiCompactifiedInversePhase,
      suzukiCenteredInversePhase, suzukiCenteredInversePhase] at hx
    have harg : Real.pi + (x - Real.pi) = x := by ring
    rw [harg] at hx
    exact Real.arctan_injective hx
  have : φ.symm = ψ.symm := by
    ext x
    exact congrFun hsymm x
  have hfun : (φ : ℝ → ℝ) = (ψ : ℝ → ℝ) := by
    funext y
    have := congrArg (fun e : ℝ ≃o ℝ => e y) (congrArg OrderIso.symm this)
    simpa using this
  ext y
  exact congrFun hfun y

/-- **Fixed-lattice rigidity, transport form.**  Equal compactified inverse phases give equal
labels at every lattice index. -/
theorem suzukiCompactifiedLabel_eq_of_phase_eq {φ ψ : ℝ ≃o ℝ}
    (h : suzukiCompactifiedInversePhase φ = suzukiCompactifiedInversePhase ψ) (k : ℤ) :
    suzukiCompactifiedLabel φ k = suzukiCompactifiedLabel ψ k := by
  rw [suzukiCompactifiedLabel, suzukiCompactifiedLabel, suzukiCompactifiedInversePhase_injective h]

end GaloisForLFunctions.RHTower
