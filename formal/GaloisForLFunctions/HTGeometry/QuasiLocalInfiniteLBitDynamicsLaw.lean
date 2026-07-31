import GaloisForLFunctions.HTGeometry.QuasiLocalInfiniteLBitLaw

/-!
# Infinite-volume diagonal dynamics for the quasi-local l-bit field

The summable coefficient field is upgraded here from a compatible family of finite Hamiltonians to
one genuine energy observable on the full Boolean configuration space `ℕ → Bool`.

Every finite support defines a Walsh sign character.  Absolute summability of the coefficients
then gives absolute convergence for every configuration, a uniform energy bound, and uniform
convergence of the physical finite-window energies obtained by retaining every interaction
contained in the first `n` sites.  The resulting infinite energy is continuous in the product
topology.
-/

open Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real Walsh character carried by one finite support on an infinite Boolean
configuration. -/
def infiniteLBitCharacter
    (S : Finset ℕ) (σ : ℕ → Bool) : ℝ :=
  ∏ i ∈ S, if σ i then -1 else 1

@[simp]
theorem abs_infiniteLBitCharacter
    (S : Finset ℕ) (σ : ℕ → Bool) :
    |infiniteLBitCharacter S σ| = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [infiniteLBitCharacter]
  | @insert i S hi hS =>
      rw [show
        infiniteLBitCharacter (insert i S) σ =
          (if σ i then (-1 : ℝ) else 1) *
            infiniteLBitCharacter S σ by
          simp [infiniteLBitCharacter, hi]]
      by_cases hσ : σ i = true
      · simp [hσ, hS]
      · simp [hσ, hS]

/-- Every finite-support character is continuous for the product topology on Boolean
configurations. -/
theorem continuous_infiniteLBitCharacter
    (S : Finset ℕ) :
    Continuous (infiniteLBitCharacter S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      change Continuous
        (fun _ : ℕ → Bool => (1 : ℝ))
      exact continuous_const
  | @insert i S hi hS =>
      have hbool :
          Continuous
            (fun b : Bool =>
              if b then (-1 : ℝ) else 1) :=
        continuous_of_discreteTopology
      have hcoordinate :
          Continuous
            (fun σ : ℕ → Bool =>
              if σ i then (-1 : ℝ) else 1) :=
        hbool.comp
          (continuous_apply i)
      rw [show
        infiniteLBitCharacter (insert i S) =
          fun σ =>
            (if σ i then (-1 : ℝ) else 1) *
              infiniteLBitCharacter S σ by
          funext σ
          simp [infiniteLBitCharacter, hi]]
      exact hcoordinate.mul hS

/-- One summand of the infinite diagonal energy. -/
def quasiLocalInfiniteLBitEnergyTerm
    (S : Finset ℕ) (σ : ℕ → Bool) : ℝ :=
  quasiLocalInfiniteLBitCoefficient S *
    infiniteLBitCharacter S σ

@[simp]
theorem abs_quasiLocalInfiniteLBitEnergyTerm
    (S : Finset ℕ) (σ : ℕ → Bool) :
    |quasiLocalInfiniteLBitEnergyTerm S σ| =
      |quasiLocalInfiniteLBitCoefficient S| := by
  simp [quasiLocalInfiniteLBitEnergyTerm, abs_mul]

/-- The energy series is absolutely summable for every infinite configuration. -/
theorem summable_norm_quasiLocalInfiniteLBitEnergyTerm
    (σ : ℕ → Bool) :
    Summable
      (fun S : Finset ℕ =>
        ‖quasiLocalInfiniteLBitEnergyTerm S σ‖) := by
  simpa [Real.norm_eq_abs] using
    summable_abs_quasiLocalInfiniteLBitCoefficient

/-- The energy series itself is summable for every infinite configuration. -/
theorem summable_quasiLocalInfiniteLBitEnergyTerm
    (σ : ℕ → Bool) :
    Summable
      (fun S : Finset ℕ =>
        quasiLocalInfiniteLBitEnergyTerm S σ) :=
  (summable_norm_quasiLocalInfiniteLBitEnergyTerm σ).of_norm

/-- The genuine infinite-configuration diagonal energy. -/
def quasiLocalInfiniteLBitEnergy
    (σ : ℕ → Bool) : ℝ :=
  ∑' S : Finset ℕ,
    quasiLocalInfiniteLBitEnergyTerm S σ

/-- Total absolute coefficient mass controlling every infinite energy. -/
def quasiLocalInfiniteLBitMass : ℝ :=
  ∑' S : Finset ℕ,
    |quasiLocalInfiniteLBitCoefficient S|

/-- Uniform infinite-volume energy bound by total absolute interaction mass. -/
theorem abs_quasiLocalInfiniteLBitEnergy_le_mass
    (σ : ℕ → Bool) :
    |quasiLocalInfiniteLBitEnergy σ| ≤
      quasiLocalInfiniteLBitMass := by
  simpa only
      [quasiLocalInfiniteLBitEnergy,
        quasiLocalInfiniteLBitMass,
        Real.norm_eq_abs,
        abs_quasiLocalInfiniteLBitEnergyTerm] using
    norm_tsum_le_tsum_norm
      (summable_norm_quasiLocalInfiniteLBitEnergyTerm σ)

/-- All interaction supports wholly contained in the first `n` lattice sites. -/
def quasiLocalInfiniteLBitWindowSupports
    (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset

/-- Physical finite-window energy retaining every interaction contained in the first `n`
sites. -/
def quasiLocalInfiniteLBitWindowEnergy
    (n : ℕ) (σ : ℕ → Bool) : ℝ :=
  ∑ S ∈ quasiLocalInfiniteLBitWindowSupports n,
    quasiLocalInfiniteLBitEnergyTerm S σ

/-- First-site windows are cofinal among all finite families of finite supports. -/
theorem tendsto_quasiLocalInfiniteLBitWindowSupports_atTop :
    Tendsto quasiLocalInfiniteLBitWindowSupports
      atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro F
  let U : Finset ℕ := F.sup id
  refine ⟨(U.sup id).succ, ?_⟩
  intro n hn S hSF
  apply Finset.mem_powerset.mpr
  have hSU : S ⊆ U := by
    change S ⊆ F.sup id
    exact Finset.le_sup (f := id) hSF
  have hUrange :
      U ⊆ Finset.range (U.sup id).succ :=
    Finset.subset_range_sup_succ U
  exact hSU.trans
    (hUrange.trans (Finset.range_mono hn))

/-- Exact configuration-independent tail bound after every finite window. -/
theorem abs_quasiLocalInfiniteLBitEnergy_sub_window_le_tail
    (n : ℕ) (σ : ℕ → Bool) :
    |quasiLocalInfiniteLBitEnergy σ -
        quasiLocalInfiniteLBitWindowEnergy n σ| ≤
      ∑' S :
        {S : Finset ℕ //
          S ∉ quasiLocalInfiniteLBitWindowSupports n},
        |quasiLocalInfiniteLBitCoefficient S.1| := by
  let W := quasiLocalInfiniteLBitWindowSupports n
  have hsum :=
    Summable.sum_add_tsum_subtype_compl
      (summable_quasiLocalInfiniteLBitEnergyTerm σ) W
  have htail :
      quasiLocalInfiniteLBitEnergy σ -
          quasiLocalInfiniteLBitWindowEnergy n σ =
        ∑' S : {S : Finset ℕ // S ∉ W},
          quasiLocalInfiniteLBitEnergyTerm S.1 σ := by
    dsimp only
      [quasiLocalInfiniteLBitEnergy,
        quasiLocalInfiniteLBitWindowEnergy]
    linarith
  rw [htail, ← Real.norm_eq_abs]
  calc
    ‖∑' S : {S : Finset ℕ // S ∉ W},
        quasiLocalInfiniteLBitEnergyTerm S.1 σ‖
        ≤ ∑' S : {S : Finset ℕ // S ∉ W},
            ‖quasiLocalInfiniteLBitEnergyTerm S.1 σ‖ := by
          exact norm_tsum_le_tsum_norm
            (Summable.subtype
              (summable_norm_quasiLocalInfiniteLBitEnergyTerm σ)
              (fun S : Finset ℕ => S ∉ W))
    _ = ∑' S : {S : Finset ℕ // S ∉ W},
          |quasiLocalInfiniteLBitCoefficient S.1| := by
            apply tsum_congr
            intro S
            simp [Real.norm_eq_abs]

/-- Absolute coefficient mass outside the first `n` sites tends to zero. -/
theorem tendsto_quasiLocalInfiniteLBitWindowTail_zero :
    Tendsto
      (fun n =>
        ∑' S :
          {S : Finset ℕ //
            S ∉ quasiLocalInfiniteLBitWindowSupports n},
          |quasiLocalInfiniteLBitCoefficient S.1|)
      atTop (𝓝 0) := by
  exact
    (tendsto_tsum_compl_atTop_zero
      (fun S : Finset ℕ =>
        |quasiLocalInfiniteLBitCoefficient S|)).comp
      tendsto_quasiLocalInfiniteLBitWindowSupports_atTop

/-- **Thermodynamic finite-window law.**  The physical first-`n`-site energies converge uniformly
over every infinite Boolean configuration to the genuine infinite energy. -/
theorem tendstoUniformly_quasiLocalInfiniteLBitWindowEnergy :
    TendstoUniformly
      quasiLocalInfiniteLBitWindowEnergy
      quasiLocalInfiniteLBitEnergy atTop := by
  have hgeneral :
      TendstoUniformly
        (fun F : Finset (Finset ℕ) =>
          fun σ : ℕ → Bool =>
            ∑ S ∈ F,
              quasiLocalInfiniteLBitEnergyTerm S σ)
        quasiLocalInfiniteLBitEnergy atTop := by
    change TendstoUniformly
      (fun F : Finset (Finset ℕ) =>
        fun σ : ℕ → Bool =>
          ∑ S ∈ F,
            quasiLocalInfiniteLBitEnergyTerm S σ)
      (fun σ =>
        ∑' S : Finset ℕ,
          quasiLocalInfiniteLBitEnergyTerm S σ) atTop
    apply tendstoUniformly_tsum
      summable_abs_quasiLocalInfiniteLBitCoefficient
    intro S σ
    simp [Real.norm_eq_abs]
  rw [Metric.tendstoUniformly_iff] at hgeneral ⊢
  intro ε hε
  have heventually :=
    tendsto_quasiLocalInfiniteLBitWindowSupports_atTop.eventually
      (hgeneral ε hε)
  simpa
    [quasiLocalInfiniteLBitWindowEnergy] using
      heventually

/-- Explicit epsilon form: one finite site window approximates the infinite energy uniformly, and
every larger window retains the same error target. -/
theorem exists_quasiLocalInfiniteLBitWindow_uniformError
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∀ m, n ≤ m → ∀ σ : ℕ → Bool,
      |quasiLocalInfiniteLBitEnergy σ -
          quasiLocalInfiniteLBitWindowEnergy m σ| < ε := by
  have heventually :=
    (Metric.tendstoUniformly_iff.mp
      tendstoUniformly_quasiLocalInfiniteLBitWindowEnergy)
      ε hε
  rw [eventually_atTop] at heventually
  obtain ⟨n, hn⟩ := heventually
  refine ⟨n, fun m hm σ => ?_⟩
  simpa [Real.dist_eq] using hn m hm σ

/-- The infinite energy observable is continuous in the product topology on Boolean
configurations. -/
theorem continuous_quasiLocalInfiniteLBitEnergy :
    Continuous quasiLocalInfiniteLBitEnergy := by
  apply continuous_tsum
    (fun S =>
      continuous_const.mul
        (continuous_infiniteLBitCharacter S))
    summable_abs_quasiLocalInfiniteLBitCoefficient
  intro S σ
  simp

end

end GaloisForLFunctions.HTGeometry
