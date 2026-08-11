import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Separation.Hausdorff

/-!
# Conservative inverse completion

This module certifies the abstract selection consequence of Witt formation mechanics.  If finite
formation and exterior responses are exact inverse pairs and both converge in one Hausdorff
topological monoid with continuous multiplication, their limits remain inverse.  Every
multiplicative receiver therefore sees a nonzero completed formation.

The arithmetic construction of such a joint completion for the Euler shell is deliberately not
assumed or encoded here.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Conservative inverse completion.** Exact right inverses survive joint convergence in a
Hausdorff topological monoid with continuous multiplication. -/
theorem wittConservativeInverse_limit
    {A : Type*} [TopologicalSpace A] [T2Space A] [Monoid A] [ContinuousMul A]
    (formation exterior : ℕ → A) (completedFormation completedExterior : A)
    (hinverse : ∀ n, formation n * exterior n = 1)
    (hformation : Tendsto formation atTop (𝓝 completedFormation))
    (hexterior : Tendsto exterior atTop (𝓝 completedExterior)) :
    completedFormation * completedExterior = 1 := by
  apply tendsto_nhds_unique (hformation.mul hexterior)
  simpa only [hinverse] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : A)) atTop (𝓝 1))

/-- A jointly completed formation cannot become zero when its exterior companion also converges. -/
theorem wittConservativeInverse_limit_ne_zero
    {A : Type*} [TopologicalSpace A] [T2Space A] [MonoidWithZero A] [Nontrivial A]
    [ContinuousMul A]
    (formation exterior : ℕ → A) (completedFormation completedExterior : A)
    (hinverse : ∀ n, formation n * exterior n = 1)
    (hformation : Tendsto formation atTop (𝓝 completedFormation))
    (hexterior : Tendsto exterior atTop (𝓝 completedExterior)) :
    completedFormation ≠ 0 := by
  intro hzero
  have hconserve := wittConservativeInverse_limit formation exterior
    completedFormation completedExterior hinverse hformation hexterior
  rw [hzero, zero_mul] at hconserve
  exact zero_ne_one hconserve

/-- Every unital multiplicative receiver preserves completed inverse conservation and hence sees a
nonzero formation value. -/
theorem wittConservativeInverse_receiver_ne_zero
    {A B : Type*} [TopologicalSpace A] [T2Space A] [Monoid A] [ContinuousMul A]
    [MonoidWithZero B] [Nontrivial B]
    (formation exterior : ℕ → A) (completedFormation completedExterior : A)
    (hinverse : ∀ n, formation n * exterior n = 1)
    (hformation : Tendsto formation atTop (𝓝 completedFormation))
    (hexterior : Tendsto exterior atTop (𝓝 completedExterior))
    (receiver : A →* B) :
    receiver completedFormation ≠ 0 := by
  intro hzero
  have hconserve := congrArg receiver
    (wittConservativeInverse_limit formation exterior completedFormation completedExterior
      hinverse hformation hexterior)
  simp only [map_mul, map_one, hzero, zero_mul] at hconserve
  exact zero_ne_one hconserve

/-- Pointwise form: one jointly convergent inverse family excludes zeros at every receiver index. -/
theorem wittConservativeInverse_pointwise_ne_zero
    {X A : Type*} [TopologicalSpace A] [T2Space A] [MonoidWithZero A] [Nontrivial A]
    [ContinuousMul A]
    (formation exterior : ℕ → X → A) (completedFormation completedExterior : X → A)
    (hinverse : ∀ n x, formation n x * exterior n x = 1)
    (hformation : ∀ x, Tendsto (fun n => formation n x) atTop (𝓝 (completedFormation x)))
    (hexterior : ∀ x, Tendsto (fun n => exterior n x) atTop (𝓝 (completedExterior x)))
    (x : X) :
    completedFormation x ≠ 0 := by
  exact wittConservativeInverse_limit_ne_zero
    (fun n => formation n x) (fun n => exterior n x)
    (completedFormation x) (completedExterior x)
    (fun n => hinverse n x) (hformation x) (hexterior x)

/-- Closed statement of the complex-valued conservative inverse-completion law. -/
def WittConservativeInverseCompletionLaw : Prop :=
  ∀ (formation exterior : ℕ → ℂ) (completedFormation completedExterior : ℂ),
    (∀ n, formation n * exterior n = 1) →
    Tendsto formation atTop (𝓝 completedFormation) →
    Tendsto exterior atTop (𝓝 completedExterior) →
    completedFormation * completedExterior = 1 ∧ completedFormation ≠ 0

/-- The conservative inverse-completion law holds unconditionally over the complex numbers. -/
theorem wittConservativeInverseCompletion_closed :
    WittConservativeInverseCompletionLaw := by
  intro formation exterior completedFormation completedExterior hinverse hformation hexterior
  exact ⟨wittConservativeInverse_limit formation exterior completedFormation completedExterior
      hinverse hformation hexterior,
    wittConservativeInverse_limit_ne_zero formation exterior completedFormation completedExterior
      hinverse hformation hexterior⟩

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-! ## The sharp completion obstruction -/

/-- **The unit group need not be closed (CIC, section 4).**  In `ℝ` the units `N⁻¹` are
conservative — each has an exterior companion `N` with `N⁻¹ · N = 1` — yet they converge to the
nonunit `0` while their companions escape every bounded set.  Losing the exterior companion is
exactly how a completion creates a divisor, so the inverse coordinate cannot be dropped. -/
theorem wittConservativeInverse_unitGroup_not_closed :
    (∀ N : ℕ, 0 < N → ((N : ℝ))⁻¹ * (N : ℝ) = 1) ∧
      Filter.Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) Filter.atTop (nhds 0) ∧
      ¬ ∃ e : ℝ, Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop (nhds e) := by
  refine ⟨fun N hN => inv_mul_cancel₀ (by exact_mod_cast hN.ne'), tendsto_inv_atTop_zero.comp
    tendsto_natCast_atTop_atTop, ?_⟩
  rintro ⟨e, he⟩
  have hbdd := he.isBoundedUnder_le
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 0 + 1)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ≤ C := hC
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  have hle := hM (max M N) (le_max_left _ _)
  have hlt : (max C 0 + 1 : ℝ) < ((max M N : ℕ) : ℝ) := by
    refine lt_of_lt_of_le hN ?_
    exact_mod_cast Nat.cast_le.mpr (le_max_right M N)
  have : C < (max C 0 + 1 : ℝ) := by
    have := le_max_left C 0
    linarith
  linarith

end GaloisForLFunctions.HTGeometry
