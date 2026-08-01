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

/-! ## Exact projective-window threshold -/

/-- **Every strictly interior projective window contains finitely many Suzuki labels.**

The compactification itself is not enough: strict monotonicity can coexist with a bounded range.
Here the phase order isomorphism supplies the missing properness.  Applying `tan` inside the
projective interval converts a label bound into upper and lower affine bounds on the integer lattice
index. -/
theorem finite_labelWindow_suzukiCompactifiedLabel_of_lt_pi_div_two
    (φ : ℝ ≃o ℝ) {r : ℝ} (hr : r < Real.pi / 2) :
    (labelWindow (suzukiCompactifiedLabel φ) r).Finite := by
  by_cases hr0 : r < 0
  · refine Set.finite_empty.subset ?_
    intro k hk
    exact (not_le_of_gt hr0) (le_trans (abs_nonneg _) hk)
  · have hr0 : 0 ≤ r := le_of_not_gt hr0
    have hpi : 0 < 2 * Real.pi := by positivity
    obtain ⟨a : ℤ, ha⟩ := exists_int_lt (φ (Real.tan (-r)) / (2 * Real.pi))
    obtain ⟨b : ℤ, hb⟩ := exists_int_gt (φ (Real.tan r) / (2 * Real.pi))
    refine (Set.finite_Icc a b).subset ?_
    intro k hk
    have hklo : -r ≤ Real.arctan
        (suzukiCenteredInversePhase φ (suzukiEvenPhaseLattice k)) := by
      simpa [labelWindow, suzukiCompactifiedLabel, suzukiCompactifiedInversePhase]
        using neg_le_of_abs_le hk
    have hkhi : Real.arctan
        (suzukiCenteredInversePhase φ (suzukiEvenPhaseLattice k)) ≤ r := by
      simpa [labelWindow, suzukiCompactifiedLabel, suzukiCompactifiedInversePhase]
        using le_of_abs_le hk
    have hneglo : -(Real.pi / 2) < -r := by linarith
    have hneghi : -r < Real.pi / 2 := by linarith [Real.pi_pos]
    have hcenterlo : Real.tan (-r) ≤
        suzukiCenteredInversePhase φ (suzukiEvenPhaseLattice k) := by
      rw [← Real.arctan_le_arctan_iff, Real.arctan_tan hneglo hneghi]
      exact hklo
    have hcenterhi : suzukiCenteredInversePhase φ (suzukiEvenPhaseLattice k) ≤
        Real.tan r := by
      rw [← Real.arctan_le_arctan_iff, Real.arctan_tan]
      · exact hkhi
      · linarith [Real.pi_pos]
      · exact hr
    have hphaselo : φ (Real.tan (-r)) ≤ 2 * (k : ℝ) * Real.pi := by
      have := φ.monotone hcenterlo
      simpa [suzukiCenteredInversePhase, pi_add_suzukiEvenPhaseLattice] using this
    have hphasehi : 2 * (k : ℝ) * Real.pi ≤ φ (Real.tan r) := by
      have := φ.monotone hcenterhi
      simpa [suzukiCenteredInversePhase, pi_add_suzukiEvenPhaseLattice] using this
    have halinear : (a : ℝ) * (2 * Real.pi) < φ (Real.tan (-r)) :=
      (lt_div_iff₀ hpi).mp ha
    have hblinear : φ (Real.tan r) < (b : ℝ) * (2 * Real.pi) :=
      (div_lt_iff₀ hpi).mp hb
    constructor
    · have hab : (a : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
      exact le_of_lt (by exact_mod_cast hab)
    · have hkb : (k : ℝ) < (b : ℝ) := by nlinarith [Real.pi_pos]
      exact le_of_lt (by exact_mod_cast hkb)

/-- **At and beyond the projective boundary the label window is all of `ℤ`.** -/
theorem labelWindow_suzukiCompactifiedLabel_eq_univ_of_pi_div_two_le
    (φ : ℝ ≃o ℝ) {r : ℝ} (hr : Real.pi / 2 ≤ r) :
    labelWindow (suzukiCompactifiedLabel φ) r = Set.univ := by
  ext k
  simp only [labelWindow, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have hmem := suzukiCompactifiedInversePhase_mem_Ioo φ (suzukiEvenPhaseLattice k)
  have habs : |suzukiCompactifiedLabel φ k| < Real.pi / 2 := by
    simpa [suzukiCompactifiedLabel] using (abs_lt.mpr hmem)
  exact habs.le.trans hr

/-- **Sharp finiteness classification.**  A Suzuki compactified-label window is finite exactly
when its radius lies strictly below the projective boundary `π / 2`. -/
theorem finite_labelWindow_suzukiCompactifiedLabel_iff (φ : ℝ ≃o ℝ) (r : ℝ) :
    (labelWindow (suzukiCompactifiedLabel φ) r).Finite ↔ r < Real.pi / 2 := by
  constructor
  · intro hfin
    by_contra hnot
    have huniv := labelWindow_suzukiCompactifiedLabel_eq_univ_of_pi_div_two_le φ
      (le_of_not_gt hnot)
    rw [huniv] at hfin
    exact Set.infinite_univ hfin
  · exact finite_labelWindow_suzukiCompactifiedLabel_of_lt_pi_div_two φ

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

/-! ## Premise-free interior-window forms -/

/-- The exact window threshold removes the abstract finiteness premise from the concrete Suzuki
label-head bound.  `Set.ncard` makes the bound independent of the chosen finiteness proof. -/
theorem suzuki_abs_le_ncard_labelWindow_of_lt_pi_div_two {φ : ℝ ≃o ℝ}
    (hreflection : ∀ x, φ (-x) = 2 * Real.pi - φ x)
    {r : ℝ} (hr : r < Real.pi / 2) {k : ℤ}
    (hle : |suzukiCompactifiedLabel φ k| ≤ r) :
    |k| ≤ (Set.ncard (labelWindow (suzukiCompactifiedLabel φ) r) : ℤ) := by
  let hfin := finite_labelWindow_suzukiCompactifiedLabel_of_lt_pi_div_two φ hr
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact suzuki_abs_le_card_labelWindow hreflection hfin hle

/-- The concrete Suzuki escaped-label tail needs no separate window-finiteness premise inside the
projective interval. -/
theorem suzuki_escapedTail_eq_zero_of_lt_pi_div_two {φ : ℝ ≃o ℝ}
    (hreflection : ∀ x, φ (-x) = 2 * Real.pi - φ x)
    {r : ℝ} (hr : r < Real.pi / 2) {f : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0) {k : ℤ}
    (hk : (Set.ncard (labelWindow (suzukiCompactifiedLabel φ) r) : ℤ) < |k|) :
    f (suzukiCompactifiedLabel φ k) = 0 := by
  let hfin := finite_labelWindow_suzukiCompactifiedLabel_of_lt_pi_div_two φ hr
  apply suzuki_escapedTail_eq_zero hreflection hfin hsupp
  rwa [← Set.ncard_eq_toFinset_card _ hfin]

/-- Eventual Rouché count stability now closes the Suzuki interior residual without a separate
family of finiteness hypotheses: strict interior support produces those hypotheses uniformly in
the family index. -/
theorem suzuki_residual_eq_zero_of_eventually_count_of_lt_pi_div_two
    {Φ : ℕ → ℝ ≃o ℝ} {P : ℕ → ℤ → ℝ} {p u : ℤ → ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {S : ℕ → ℝ} {Sinf L : ℝ}
    (hreflection : ∀ i, ∀ x, (Φ i) (-x) = 2 * Real.pi - (Φ i) x)
    {r : ℝ} (hr : r < Real.pi / 2) {M : ℕ}
    (hcount : ∀ᶠ i in atTop,
      Set.ncard (labelWindow (suzukiCompactifiedLabel (Φ i)) r) ≤ M)
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0)
    (hSsum : ∀ i, HasSum (fun k => P i k * f (suzukiCompactifiedLabel (Φ i) k)) (S i))
    (hS : Tendsto S atTop (𝓝 Sinf))
    (hP : ∀ k, Tendsto (fun i => P i k) atTop (𝓝 (p k)))
    (hU : ∀ k, Tendsto (fun i => suzukiCompactifiedLabel (Φ i) k) atTop (𝓝 (u k)))
    (hL : Tendsto (fun K : ℕ => labelHead p (fun k => f (u k)) K) atTop (𝓝 L)) :
    Sinf = L := by
  let hfin : ∀ i, (labelWindow (suzukiCompactifiedLabel (Φ i)) r).Finite :=
    fun i => finite_labelWindow_suzukiCompactifiedLabel_of_lt_pi_div_two (Φ i) hr
  refine suzuki_residual_eq_zero_of_eventually_count (M := M) hf hreflection hfin ?_
    hsupp hSsum hS hP hU hL
  filter_upwards [hcount] with i hi
  rwa [← Set.ncard_eq_toFinset_card _ (hfin i)]

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
