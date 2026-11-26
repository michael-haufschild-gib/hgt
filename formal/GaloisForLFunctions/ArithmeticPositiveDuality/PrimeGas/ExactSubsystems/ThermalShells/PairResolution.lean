import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.PrimeSelection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.CloseModes

/-! # Actual prime pairs at the boundary of thermal distinguishability -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

open Filter Topology Set _root_.RHTower
open BinaryOrientation.LargestPrime.Bands
open BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

/-- Distinct positive temperatures never attain the sharp positive-width bound on a finite
selection of prime configurations. -/
theorem strict_at_positive_temperatures {S : Finset Nat.Primes} {k : ℕ} {U : Finset (BreadthSubset k ↥S)}
    (hU : U.Nonempty) {β γ D : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hne : β ≠ γ) (hwidth : 0 < D)
    (hD : ∀ x ∈ U, ∀ y ∈ U, |energyOf x-energyOf y| ≤ D) :
    variation (born β) (born γ) U < Real.tanh (|β-γ| * D/4) := by
  apply lt_of_le_of_ne ((born_variation β γ U).le.trans (thermal_variation energyOf hU β γ D hD))
  have hη := mul_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) hwidth
  exact fun he => (add_pos hβ hγ).ne' ((prime_sharp_iff hU β γ D hD hη).mp he).1

/-- The count-one configuration with only prime p occupied. -/
def oneMode {S : Finset Nat.Primes} (p : ↥S) : BreadthSubset 1 ↥S := ⟨{p},Finset.card_singleton p⟩

theorem oneMode_energy {S : Finset Nat.Primes} (p : ↥S) :
    energyOf (oneMode p) = squarefreePrimeEnergy p.val := by simp [energyOf,oneMode]

def twoModes {S : Finset Nat.Primes} (p q : ↥S) : Finset (BreadthSubset 1 ↥S) := {oneMode p,oneMode q}

private theorem pair_span {Ω : Type*} [DecidableEq Ω] (E : Ω → ℝ) (x y : Ω) :
    ∀ a ∈ ({x,y} : Finset Ω), ∀ b ∈ ({x,y} : Finset Ω), |E a-E b| ≤ |E x-E y| := by
  intro a ha b hb
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [abs_sub_comm]

private theorem twoModes_span {S : Finset Nat.Primes} {p q : ↥S} (h : 0 < squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val) :
    ∀ x ∈ twoModes p q, ∀ y ∈ twoModes p q, |energyOf x-energyOf y| ≤ squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val := by
  have H := pair_span energyOf (oneMode p) (oneMode q)
  rwa [oneMode_energy,oneMode_energy,abs_sub_comm (squarefreePrimeEnergy p.val) (squarefreePrimeEnergy q.val),abs_of_pos h] at H

/-- Two actual prime configurations attain the sharp bound at opposite temperatures. -/
theorem two_prime_sharp {S : Finset Nat.Primes} (p q : ↥S) {b : ℝ} (hb : 0 < b)
    (hg : 0 < squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val) :
    variation (born (-b)) (born b) (twoModes p q) =
      Real.tanh (b*(squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val)/2) := by
  let g := squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val
  have hU : (twoModes p q).Nonempty := ⟨oneMode p,Finset.mem_insert_self _ _⟩
  have hneg : -b-b < 0 := by linarith only [hb]
  have ht : 0 < |-b-b| * g := mul_pos (abs_pos.mpr hneg.ne) hg
  have hxy : oneMode p ≠ oneMode q := fun he => (sub_pos.mp hg).ne (by simpa only [oneMode_energy] using congrArg energyOf he)
  have H := (prime_sharp_iff hU (-b) b g (twoModes_span hg) ht).mpr
    ⟨neg_add_cancel b,oneMode p,oneMode q,hxy,rfl,by rw [oneMode_energy,oneMode_energy,abs_sub_comm,abs_of_pos hg]⟩
  rw [H,abs_of_neg hneg]
  congr 1
  dsimp [g]
  ring

/-- An inverse-temperature contrast proportional to the reciprocal energy gap retains fixed signal. -/
theorem resolution_scale {S : Finset Nat.Primes} (p q : ↥S) {t : ℝ} (ht : 0 < t)
    (hg : 0 < squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val) :
    let b := t/(squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val)
    variation (born (-b)) (born b) (twoModes p q) = Real.tanh (t/2) := by
  dsimp only
  rw [two_prime_sharp p q (div_pos ht hg) hg,div_mul_cancel₀ _ hg.ne']

/-- Arbitrarily thin genuine prime pairs retaining any fixed scaled thermal signal exist
throughout every sufficiently far moving band. -/
theorem sharp_in_every_band {c d ε : ℝ} (hc : 0 < c) (hcd : c < d) (hε : 0 < ε) :
    ∀ᶠ h in criticalApproach, ∃ p q : ↥(added c d h),
      let g := squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val
      0 < g ∧ g < ε ∧ ∀ t > (0:ℝ), variation (born (-(t/g))) (born (t/g)) (twoModes p q) = Real.tanh (t/2) := by
  filter_upwards [eventually_close_modes hc hcd hε] with h hh
  obtain ⟨p,q,hg,hgε⟩ := hh
  exact ⟨p,q,hg,hgε,fun _ ht => resolution_scale p q ht hg⟩

/-- In every fixed moving band there are genuine prime pairs with nonzero but arbitrarily small
total variation at two distinct fixed temperatures. -/
theorem eventually_weak_contrast {c d ε : ℝ} (hc : 0 < c) (hcd : c < d) (hε : 0 < ε) {β γ : ℝ} (hb : β ≠ γ) :
    ∀ᶠ h in criticalApproach, ∃ p q : ↥(added c d h), squarefreePrimeEnergy p.val < squarefreePrimeEnergy q.val ∧
      0 < variation (born β) (born γ) (twoModes p q) ∧ variation (born β) (born γ) (twoModes p q) < ε := by
  have h0 : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have H := h0.const_mul |β-γ|
  rw [mul_zero] at H
  have good : ∀ᶠ z : ℝ in 𝓝[>] 0, 0 < z ∧ Real.tanh (|β-γ| * z/4) < ε := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ)),(small_contrast H).eventually_lt_const hε] with z hz ht
    exact ⟨hz,ht⟩
  obtain ⟨D,hD,ht⟩ := Filter.Eventually.exists good
  filter_upwards [eventually_close_modes hc hcd hD] with h he
  obtain ⟨p,q,hpq,hgap⟩ := he
  let U := twoModes p q
  have hp : oneMode p ∈ U := Finset.mem_insert_self _ _
  have hq : oneMode q ∈ U := Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hU : U.Nonempty := ⟨_,hp⟩
  have hn : variation (weight β energyOf) (weight γ energyOf) U ≠ 0 := by
    intro hz
    rcases (variation_zero_iff energyOf hU β γ).mp hz with h | h
    · exact hb h
    · exact (sub_pos.mp hpq).ne (by simpa only [oneMode_energy] using h _ hp _ hq)
  refine ⟨p,q,sub_pos.mp hpq,?_,?_⟩
  · rw [born_variation]
    exact lt_of_le_of_ne (variation_nonneg _ _ _) hn.symm
  · rw [born_variation]
    exact (thermal_variation energyOf hU β γ D (fun x hx y hy => (twoModes_span hpq x hx y hy).trans hgap.le)).trans_lt ht

#print axioms strict_at_positive_temperatures
#print axioms two_prime_sharp
#print axioms resolution_scale
#print axioms sharp_in_every_band
#print axioms eventually_weak_contrast

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
