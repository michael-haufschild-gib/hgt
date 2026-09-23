import GaloisForLFunctions.RHTower.HedenmalmSoninSingularGreenWeylSewingWeld
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge

/-!
# Weyl-defect quantization wall

The raw Calderón--Witt/Sonin Weyl reciprocity defect is continuous in horizontal displacement.
Consequently, for every positive integer packet charge and every tolerance, a strictly off-wall
packet has defect arbitrarily close to one. No packet-independent raw-defect threshold can bound
the discrete Xi reflection-incidence charge.

Normalizing its negative logarithm by horizontal displacement recovers the exact integer packet
charge. This tropical detector is necessarily discontinuous at the wall. On actual Xi strip
windows, weighting its unit value by squared analytic order gives exactly the canonical reflection
self-intersection charge. Thus continuous source geometry and discrete divisor incidence meet only
through a singular wall operation; a horizontal gap or an independent residue/order mechanism is
required to turn raw Weyl estimates into RH's strict two-unit endpoint.
-/

open Complex Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Product defect of `M` identical reflected Weyl incidences. -/
def deningerCalderonWittGammaWeylPacketDefect
    (M : ℕ) (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  (deningerCalderonWittGammaWeylLowerSewingCost (-a) p q n *
    deningerCalderonWittGammaWeylLowerSewingCost a p q n) ^ M

/-- Packet defect is exponential in charge times absolute horizontal displacement. -/
theorem deningerCalderonWittGammaWeylPacketDefect_eq
    (M : ℕ) (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylPacketDefect M a p q n =
      Real.exp (-4 * (M : ℝ) * |a| *
        (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) := by
  rw [deningerCalderonWittGammaWeylPacketDefect,
    deningerCalderonWittGammaWeylReciprocityDefect_eq,
    ← Real.exp_nat_mul]
  congr 1
  ring

/-- At every fixed integer charge, raw packet defect tends to one at the wall. -/
theorem deningerCalderonWittGammaWeylPacketDefect_tendsto_one
    (M : ℕ) (p q : Nat.Primes) (n : ℕ) :
    Tendsto (fun a : ℝ =>
      deningerCalderonWittGammaWeylPacketDefect M a p q n)
      (𝓝 0) (𝓝 1) := by
  have hcont : ContinuousAt (fun a : ℝ =>
      Real.exp (-4 * (M : ℝ) * |a| *
        (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1))) 0 := by
    fun_prop
  rw [show (1 : ℝ) = Real.exp (-4 * (M : ℝ) * |(0 : ℝ)| *
      (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1)) by norm_num]
  simpa only [deningerCalderonWittGammaWeylPacketDefect_eq] using hcont.tendsto

theorem eventually_one_sub_lt_deningerCalderonWittGammaWeylPacketDefect
    (M : ℕ) (p q : Nat.Primes) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in 𝓝[≠] 0,
      1 - ε < deningerCalderonWittGammaWeylPacketDefect M a p q n := by
  have hnear := (deningerCalderonWittGammaWeylPacketDefect_tendsto_one M p q n).eventually
    (eventually_gt_nhds (sub_lt_self 1 hε))
  exact hnear.filter_mono nhdsWithin_le_nhds

/-- Every nonempty strictly off-wall packet has defect strictly below one. -/
theorem deningerCalderonWittGammaWeylPacketDefect_lt_one
    {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : a ≠ 0)
    (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylPacketDefect M a p q n < 1 := by
  rw [deningerCalderonWittGammaWeylPacketDefect_eq, Real.exp_lt_one_iff]
  have hL : 0 < Real.log (p : ℝ) + Real.log (q : ℝ) := by
    exact add_pos
      (Real.log_pos (by exact_mod_cast p.property.one_lt))
      (Real.log_pos (by exact_mod_cast q.property.one_lt))
  have ha' : 0 < |a| := abs_pos.mpr ha
  have hM' : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hprod : 0 <
      4 * (M : ℝ) * |a| *
        (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1) := by
    positivity
  nlinarith

/-- Every positive packet charge can be strictly off-wall yet arbitrarily close to unit defect. -/
theorem eventually_deningerCalderonWittGammaWeylPacketDefect_between
    {M : ℕ} (hM : 0 < M) (p q : Nat.Primes) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in 𝓝[≠] 0,
      a ≠ 0 ∧
        1 - ε < deningerCalderonWittGammaWeylPacketDefect M a p q n ∧
        deningerCalderonWittGammaWeylPacketDefect M a p q n < 1 := by
  filter_upwards
    [eventually_one_sub_lt_deningerCalderonWittGammaWeylPacketDefect
      M p q n hε,
      self_mem_nhdsWithin] with a hlower ha
  exact ⟨ha, hlower,
    deningerCalderonWittGammaWeylPacketDefect_lt_one hM ha p q n⟩

/-- Explicit existence form of the arbitrary-charge near-unit obstruction. -/
theorem exists_deningerCalderonWittGammaWeylPacketDefect_between
    {M : ℕ} (hM : 0 < M) (p q : Nat.Primes) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, a ≠ 0 ∧
      1 - ε < deningerCalderonWittGammaWeylPacketDefect M a p q n ∧
      deningerCalderonWittGammaWeylPacketDefect M a p q n < 1 := by
  exact (eventually_deningerCalderonWittGammaWeylPacketDefect_between
    hM p q n hε).exists

/-- Singular logarithmic valuation of a Weyl-defect packet, completed by zero at the wall. -/
def deningerCalderonWittGammaWeylTropicalPacketCharge
    (M : ℕ) (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  if a = 0 then 0 else
    -Real.log (deningerCalderonWittGammaWeylPacketDefect M a p q n) /
      (4 * |a| * (Real.log (p : ℝ) + Real.log (q : ℝ)) * ((n : ℝ) + 1))

/-- Away from the wall, tropical valuation recovers exact integer packet charge. -/
theorem deningerCalderonWittGammaWeylTropicalPacketCharge_eq
    (M : ℕ) {a : ℝ} (ha : a ≠ 0) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylTropicalPacketCharge M a p q n = M := by
  have hL : Real.log (p : ℝ) + Real.log (q : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos
      (Real.log_pos (by exact_mod_cast p.property.one_lt))
      (Real.log_pos (by exact_mod_cast q.property.one_lt)))
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [deningerCalderonWittGammaWeylTropicalPacketCharge, if_neg ha,
    deningerCalderonWittGammaWeylPacketDefect_eq, Real.log_exp]
  field_simp [abs_ne_zero.mpr ha, hL, hn]

@[simp] theorem deningerCalderonWittGammaWeylTropicalPacketCharge_zero
    (M : ℕ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaWeylTropicalPacketCharge M 0 p q n = 0 := by
  simp [deningerCalderonWittGammaWeylTropicalPacketCharge]

/-- Exact integer recovery forces a jump from charge `M` off-wall to zero on the wall. -/
theorem not_continuousAt_deningerCalderonWittGammaWeylTropicalPacketCharge
    {M : ℕ} (hM : 0 < M) (p q : Nat.Primes) (n : ℕ) :
    ¬ ContinuousAt
      (fun a : ℝ => deningerCalderonWittGammaWeylTropicalPacketCharge M a p q n) 0 := by
  intro hcont
  let a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ha0 : ∀ k, a k ≠ 0 := by
    intro k
    dsimp [a]
    positivity
  have hatend : Tendsto a atTop (𝓝 0) := by
    simpa [a] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htoZero : Tendsto
      (fun k => deningerCalderonWittGammaWeylTropicalPacketCharge M (a k) p q n)
      atTop (𝓝 0) := by
    have hcomp := hcont.tendsto.comp hatend
    rw [deningerCalderonWittGammaWeylTropicalPacketCharge_zero] at hcomp
    change Tendsto
      ((fun x : ℝ =>
        deningerCalderonWittGammaWeylTropicalPacketCharge M x p q n) ∘ a)
      atTop (𝓝 0)
    exact hcomp
  have htoM : Tendsto
      (fun k => deningerCalderonWittGammaWeylTropicalPacketCharge M (a k) p q n)
      atTop (𝓝 (M : ℝ)) := by
    have heq : (fun k =>
        deningerCalderonWittGammaWeylTropicalPacketCharge M (a k) p q n) =
        fun _ : ℕ => (M : ℝ) := by
      funext k
      exact deningerCalderonWittGammaWeylTropicalPacketCharge_eq M (ha0 k) p q n
    rw [heq]
    exact tendsto_const_nhds
  have hzero : (0 : ℝ) = M := tendsto_nhds_unique htoZero htoM
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)) hzero.symm

/-- Xi window charge obtained by tropicalizing one Weyl defect at each support point and weighting
by squared analytic multiplicity. -/
def xiWeylTropicalReflectionCharge
    (T : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    (((analyticOrderAt xi rho).toNat : ℝ) ^ (2 : ℕ)) *
      deningerCalderonWittGammaWeylTropicalPacketCharge 1
        (xiNearbyPoleDualityAdjunctionFracture rho).re p q n

/-- **Quantization wall.** Tropical Weyl charge is exactly the canonical Xi reflection
self-intersection charge, independently of retained prime pair and valuation depth. -/
theorem xiWeylTropicalReflectionCharge_eq
    (T : ℝ) (p q : Nat.Primes) (n : ℕ) :
    xiWeylTropicalReflectionCharge T p q n =
      (xiReflectionSelfIntersectionCharge T : ℝ) := by
  classical
  rw [xiWeylTropicalReflectionCharge,
    xiReflectionSelfIntersectionCharge_eq_offLineSquareOrder,
    xiStripWindowOffLineSquareOrder]
  rw [Nat.cast_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hline : rho.re = 1 / 2
  · have hfracture : (xiNearbyPoleDualityAdjunctionFracture rho).re = 0 := by
      rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
      simp [hline]
    rw [hfracture]
    simp only [deningerCalderonWittGammaWeylTropicalPacketCharge_zero,
      mul_zero]
    rw [if_neg]
    exact not_ne_iff.mpr hline
  · have hfracture : (xiNearbyPoleDualityAdjunctionFracture rho).re ≠ 0 := by
      rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
      simp
      intro h
      apply hline
      norm_num at h ⊢
      exact sub_eq_zero.mp h
    rw [deningerCalderonWittGammaWeylTropicalPacketCharge_eq 1 hfracture]
    simp only [Nat.cast_one, mul_one]
    rw [if_pos hline]
    norm_cast

end RHTower
