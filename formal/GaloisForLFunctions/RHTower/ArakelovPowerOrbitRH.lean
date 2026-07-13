import GaloisForLFunctions.ArakelovW
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Arakelov power-orbit stability forces RH

In the Arakelov coordinate `w(rho) = 1 - rho⁻¹`, the critical line is the unit circle and the
right half-plane is the open unit disk.  Lift the power map `w -> w^n` back to the spectral
coordinate by

`P_n(rho) = (1 - w(rho)^n)⁻¹`.

If the Xi zero set were forward invariant under one such map with `n >= 2`, then every
hypothetical right-half zero would generate a zero orbit converging to `rho = 1`.  Continuity
would force `xi(1) = 0`, contradicting `xi(1) = 1/2`.  Thus one source-derived Arakelov power
operation preserving the Xi divisor proves RH.

This is a consumer theorem.  It does not assert that the prime Adams operation, the Böttcher
power map, or modular-lambda transport preserves the Xi divisor.
-/

open Complex Filter Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The lift of `w -> w^n` through the Arakelov coordinate. -/
def arakelovPowerLift (n : ℕ) (rho : ℂ) : ℂ :=
  (1 - arakelovW rho ^ n)⁻¹

/-- The explicit `k`-fold power orbit. -/
def arakelovPowerOrbit (n : ℕ) (rho : ℂ) (k : ℕ) : ℂ :=
  (1 - arakelovW rho ^ (n ^ k))⁻¹

@[simp] theorem arakelovW_arakelovPowerLift (n : ℕ) (rho : ℂ) :
    arakelovW (arakelovPowerLift n rho) = arakelovW rho ^ n := by
  simp [arakelovW, arakelovPowerLift]

@[simp] theorem arakelovW_arakelovPowerOrbit (n : ℕ) (rho : ℂ) (k : ℕ) :
    arakelovW (arakelovPowerOrbit n rho k) = arakelovW rho ^ (n ^ k) := by
  simp [arakelovW, arakelovPowerOrbit]

@[simp] theorem arakelovPowerOrbit_zero (n : ℕ) (rho : ℂ) :
    arakelovPowerOrbit n rho 0 = rho := by
  simp [arakelovPowerOrbit, arakelovW]

/-- The explicit orbit agrees with iteration of the one-step power lift. -/
theorem arakelovPowerOrbit_succ (n : ℕ) (rho : ℂ) (k : ℕ) :
    arakelovPowerOrbit n rho (k + 1) =
      arakelovPowerLift n (arakelovPowerOrbit n rho k) := by
  rw [arakelovPowerLift, arakelovW_arakelovPowerOrbit]
  simp [arakelovPowerOrbit, pow_succ, pow_mul]

/-- Every contracting Arakelov power orbit converges to the nonzero Xi anchor `rho = 1`. -/
theorem arakelovPowerOrbit_tendsto_one {n : ℕ} (hn : 2 ≤ n) {rho : ℂ}
    (hcontract : ‖arakelovW rho‖ < 1) :
    Tendsto (arakelovPowerOrbit n rho) atTop (𝓝 1) := by
  have hindex : Tendsto (fun k : ℕ => n ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have hpow : Tendsto (fun m : ℕ => arakelovW rho ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hcontract
  have hsub : Tendsto (fun k : ℕ => 1 - arakelovW rho ^ (n ^ k)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hpow.comp hindex)
  simpa [arakelovPowerOrbit] using hsub.inv₀ (by norm_num : (1 : ℂ) ≠ 0)

/-- Forward invariance of the actual Xi zero set under one Arakelov power lift. -/
def XiArakelovPowerStable (n : ℕ) : Prop :=
  ∀ rho : ℂ, xi rho = 0 → xi (arakelovPowerLift n rho) = 0

/-- Every Xi zero carries a finite orbit under exponentiation of its Arakelov coordinate.  Unlike
`XiArakelovPowerStable`, this does not require the intermediate power-orbit points to be Xi zeros. -/
def XiArakelovPowerPreperiodic (n : ℕ) : Prop :=
  ∀ rho : ℂ, rho ∈ rightHalf → xi rho = 0 →
    ∃ a b : ℕ, a < b ∧ arakelovW rho ^ (n ^ a) = arakelovW rho ^ (n ^ b)

/-- The weaker stability premise needed by the accumulation argument: only hypothetical
right-half Xi zeros, and their successive images, must remain zeros. -/
def XiRightArakelovPowerStable (n : ℕ) : Prop :=
  ∀ rho : ℂ, rho ∈ rightHalf → xi rho = 0 → xi (arakelovPowerLift n rho) = 0

/-- A nontrivial Arakelov power lift preserves the open right half-plane. -/
theorem arakelovPowerLift_mem_rightHalf {n : ℕ} (hn : 2 ≤ n) {rho : ℂ}
    (hrho : rho ∈ rightHalf) : arakelovPowerLift n rho ∈ rightHalf := by
  have hrho0 : rho ≠ 0 := by
    intro h
    subst rho
    have hpos := Set.mem_setOf.mp hrho
    norm_num at hpos
  have hcontract : ‖arakelovW rho‖ < 1 :=
    (arakelovW_norm_lt_one_iff rho hrho0).mpr (Set.mem_setOf.mp hrho)
  have hpowcontract : ‖arakelovW rho ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hcontract (by omega)
  have hpowne : arakelovW rho ^ n ≠ 1 := by
    intro h
    have hnorm := congrArg norm h
    rw [norm_one] at hnorm
    exact (ne_of_lt hpowcontract) hnorm
  have hlift0 : arakelovPowerLift n rho ≠ 0 := by
    apply inv_ne_zero
    exact sub_ne_zero.mpr (Ne.symm hpowne)
  apply Set.mem_setOf.mpr
  apply (arakelovW_norm_lt_one_iff (arakelovPowerLift n rho) hlift0).mp
  rw [arakelovW_arakelovPowerLift]
  exact hpowcontract

/-- Right-half one-step stability propagates both zerohood and right-half membership along the
complete explicit orbit. -/
theorem xi_arakelovPowerOrbit_eq_zero_of_rightStable {n : ℕ} (hn : 2 ≤ n)
    (hstable : XiRightArakelovPowerStable n) {rho : ℂ}
    (hrho : rho ∈ rightHalf) (hzero : xi rho = 0) :
    ∀ k : ℕ, arakelovPowerOrbit n rho k ∈ rightHalf ∧
      xi (arakelovPowerOrbit n rho k) = 0 := by
  intro k
  induction k with
  | zero => simpa using And.intro hrho hzero
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by omega, ← Nat.add_one]
      rw [arakelovPowerOrbit_succ]
      exact ⟨arakelovPowerLift_mem_rightHalf hn ih.1, hstable _ ih.1 ih.2⟩

/-- One-step zero stability propagates to the entire explicit power orbit. -/
theorem xi_arakelovPowerOrbit_eq_zero {n : ℕ}
    (hstable : XiArakelovPowerStable n) {rho : ℂ} (hzero : xi rho = 0) :
    ∀ k : ℕ, xi (arakelovPowerOrbit n rho k) = 0 := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by omega, ← Nat.add_one]
      rw [arakelovPowerOrbit_succ]
      exact hstable _ ih

/-- **Arakelov power-orbit criterion for RH.**  Forward stability of the Xi divisor under one
nontrivial power map forces every Xi zero onto the critical line. -/
theorem riemannHypothesis_of_xiArakelovPowerStable {n : ℕ} (hn : 2 ≤ n)
    (hstable : XiArakelovPowerStable n) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hright hzero
  have hrho0 : rho ≠ 0 := by
    intro h
    subst rho
    have hpos := Set.mem_setOf.mp hright
    norm_num at hpos
  have hcontract : ‖arakelovW rho‖ < 1 :=
    (arakelovW_norm_lt_one_iff rho hrho0).mpr (Set.mem_setOf.mp hright)
  have horbit := arakelovPowerOrbit_tendsto_one hn hcontract
  have hxi : Tendsto (fun k => xi (arakelovPowerOrbit n rho k)) atTop (𝓝 (xi 1)) :=
    ((xi_analyticOnNhd_univ 1 (Set.mem_univ 1)).continuousAt.tendsto).comp horbit
  have hzeros := xi_arakelovPowerOrbit_eq_zero hstable hzero
  have hzeroLimit : Tendsto (fun k => xi (arakelovPowerOrbit n rho k)) atTop (𝓝 0) := by
    have heq : (fun k => xi (arakelovPowerOrbit n rho k)) = fun _ : ℕ => (0 : ℂ) :=
      funext hzeros
    rw [heq]
    exact tendsto_const_nhds
  have hanchor : xi 1 = 0 := tendsto_nhds_unique hxi hzeroLimit
  rw [xi_one] at hanchor
  norm_num at hanchor

/-- **Finite-monodromy variant.**  It is enough that every Xi zero have a preperiodic Arakelov
coordinate under one nontrivial power map.  No power-orbit point has to remain in the Xi divisor. -/
theorem riemannHypothesis_of_xiArakelovPowerPreperiodic {n : ℕ} (hn : 2 ≤ n)
    (hpre : XiArakelovPowerPreperiodic n) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hright hzero
  have hrho0 : rho ≠ 0 := by
    intro h
    subst rho
    have hpos := Set.mem_setOf.mp hright
    norm_num at hpos
  have hcontract : ‖arakelovW rho‖ < 1 :=
    (arakelovW_norm_lt_one_iff rho hrho0).mpr (Set.mem_setOf.mp hright)
  have hw0 : arakelovW rho ≠ 0 := by
    intro hw
    have hrho1 : rho = 1 := arakelovW_injective (hw.trans (by simp [arakelovW]))
    subst rho
    rw [xi_one] at hzero
    norm_num at hzero
  obtain ⟨a, b, hab, hpowers⟩ := hpre rho hright hzero
  have hnorm : ‖arakelovW rho‖ ^ (n ^ a) = ‖arakelovW rho‖ ^ (n ^ b) := by
    simpa only [norm_pow] using congrArg norm hpowers
  have hexponents : n ^ a = n ^ b :=
    pow_right_injective₀ (norm_pos_iff.mpr hw0) (ne_of_lt hcontract) hnorm
  have hlt : n ^ a < n ^ b :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < n)).mpr hab
  exact (ne_of_lt hlt) hexponents

/-- **Circularity audit for finite monodromy.**  The bare right-half preperiodicity
certificate is equivalent to RH: the reverse implication is vacuous because RH removes
its indexing set.  A genuine route must construct the finite orbit from a separately
defined source object. -/
theorem xiArakelovPowerPreperiodic_iff_riemannHypothesis {n : ℕ} (hn : 2 ≤ n) :
    XiArakelovPowerPreperiodic n ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiArakelovPowerPreperiodic hn
  · intro hRH rho hright hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH rho hright hzero).elim

/-- **Right-half power-orbit criterion.**  The full-divisor stability hypothesis can be weakened
to forward stability only on the hypothetical right-half divisor. -/
theorem riemannHypothesis_of_xiRightArakelovPowerStable {n : ℕ} (hn : 2 ≤ n)
    (hstable : XiRightArakelovPowerStable n) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hright hzero
  have hrho0 : rho ≠ 0 := by
    intro h
    subst rho
    have hpos := Set.mem_setOf.mp hright
    norm_num at hpos
  have hcontract : ‖arakelovW rho‖ < 1 :=
    (arakelovW_norm_lt_one_iff rho hrho0).mpr (Set.mem_setOf.mp hright)
  have horbit := arakelovPowerOrbit_tendsto_one hn hcontract
  have hxi : Tendsto (fun k => xi (arakelovPowerOrbit n rho k)) atTop (𝓝 (xi 1)) :=
    ((xi_analyticOnNhd_univ 1 (Set.mem_univ 1)).continuousAt.tendsto).comp horbit
  have hzeros := xi_arakelovPowerOrbit_eq_zero_of_rightStable hn hstable hright hzero
  have hzeroLimit : Tendsto (fun k => xi (arakelovPowerOrbit n rho k)) atTop (𝓝 0) := by
    have heq : (fun k => xi (arakelovPowerOrbit n rho k)) = fun _ : ℕ => (0 : ℂ) :=
      funext fun k => (hzeros k).2
    rw [heq]
    exact tendsto_const_nhds
  have hanchor : xi 1 = 0 := tendsto_nhds_unique hxi hzeroLimit
  rw [xi_one] at hanchor
  norm_num at hanchor

/-- The right-half stability certificate has the same vacuity boundary as finite
preperiodicity.  Only a source-defined endomorphism can make this equivalence useful. -/
theorem xiRightArakelovPowerStable_iff_riemannHypothesis {n : ℕ} (hn : 2 ≤ n) :
    XiRightArakelovPowerStable n ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiRightArakelovPowerStable hn
  · intro hRH rho hright hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH rho hright hzero).elim

end

end RHTower
