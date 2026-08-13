import GaloisForLFunctions.RHTower.SuzukiRootPortObservationGram
import GaloisForLFunctions.RHTower.SuzukiExteriorSymbolBounds
import GaloisForLFunctions.RHTower.SuzukiWienerNeumannMajorant

/-!
# Suzuki's finite prime alphabet as a Wiener-algebra element

The prime block of Suzuki's exterior symbol is the evaluation of one finitely supported element of
the valuation Wiener algebra,

`t_a = -∑_{p^j ≤ e^{2a}} (log p) p^{-j/2} (δ_{j e_p} + δ_{-j e_p})`,

whose two oriented atoms per visible prime power are distinct because the seam coordinate of a
visible step is strictly positive.  Hence the `ℓ¹` mass of `t_a` is exactly twice the sum of the
prime weights, and its unit-phase evaluation is exactly Suzuki's cosine sum.  Together with the
bounded normalized remainder this gives the exact normalization `p_a = L + q_a + Ev(t_a)`, i.e.
`κ = 1`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The two oriented atoms carried by one visible prime-power step. -/
def suzukiOrientedStep (s : Nat.Primes × ℕ) (b : Bool) : SuzukiSeamValuation :=
  if b then suzukiPrimePowerStep s else -suzukiPrimePowerStep s

/-- **Distinct oriented visible steps carry distinct valuation atoms.** -/
theorem suzukiOrientedStep_injOn {S : Finset (Nat.Primes × ℕ)} (hj : ∀ pj ∈ S, 1 ≤ pj.2) :
    Set.InjOn (fun x : (Nat.Primes × ℕ) × Bool => suzukiOrientedStep x.1 x.2)
      (S ×ˢ (Finset.univ : Finset Bool)) := by
  intro x hx y hy hxy
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hx hy
  have hx1 : x.1 ∈ S := hx.1
  have hy1 : y.1 ∈ S := hy.1
  have hposx : 0 < primeSeamCoordinate (suzukiPrimePowerStep x.1) :=
    primePowerStep_coordinate_pos (hj x.1 hx1)
  have hposy : 0 < primeSeamCoordinate (suzukiPrimePowerStep y.1) :=
    primePowerStep_coordinate_pos (hj y.1 hy1)
  have hstep : x.2 = y.2 := by
    by_contra hne
    rcases Bool.eq_false_or_eq_true x.2 with hx2 | hx2 <;>
      rcases Bool.eq_false_or_eq_true y.2 with hy2 | hy2
    · exact hne (by rw [hx2, hy2])
    · rw [hx2, hy2] at hxy
      simp only [suzukiOrientedStep, if_true, if_false] at hxy
      have := congrArg primeSeamCoordinate hxy
      rw [map_neg] at this
      linarith
    · rw [hx2, hy2] at hxy
      simp only [suzukiOrientedStep, if_true, if_false] at hxy
      have := congrArg primeSeamCoordinate hxy
      rw [map_neg] at this
      linarith
    · exact hne (by rw [hx2, hy2])
  have hbase : suzukiPrimePowerStep x.1 = suzukiPrimePowerStep y.1 := by
    rcases Bool.eq_false_or_eq_true x.2 with hx2 | hx2
    · rw [hx2] at hxy
      rw [← hstep, hx2] at hxy
      simp only [suzukiOrientedStep, if_false] at hxy
      exact neg_injective hxy
    · rw [hx2] at hxy
      rw [← hstep, hx2] at hxy
      simpa [suzukiOrientedStep] using hxy
  exact Prod.ext (primePowerStep_injOn hj hx1 hy1 hbase) hstep

/-- Suzuki's `(13)`: the finite prime coefficient family `t_a` of the valuation Wiener algebra. -/
def suzukiWienerAtoms (S : Finset (Nat.Primes × ℕ)) : SuzukiSeamValuation → ℂ := fun ν =>
  -∑ x ∈ S ×ˢ (Finset.univ : Finset Bool),
      (suzukiPrimePowerWeight x.1 : ℂ) * (if ν = suzukiOrientedStep x.1 x.2 then 1 else 0)

/-- Off the oriented atoms the coefficient family vanishes. -/
theorem suzukiWienerAtoms_eq_zero {S : Finset (Nat.Primes × ℕ)} {ν : SuzukiSeamValuation}
    (hν : ∀ x ∈ S ×ˢ (Finset.univ : Finset Bool), ν ≠ suzukiOrientedStep x.1 x.2) :
    suzukiWienerAtoms S ν = 0 := by
  rw [suzukiWienerAtoms, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro x hx
  rw [if_neg (hν x hx), mul_zero]

/-- At an oriented atom the coefficient is exactly minus the prime weight. -/
theorem suzukiWienerAtoms_apply {S : Finset (Nat.Primes × ℕ)} (hj : ∀ pj ∈ S, 1 ≤ pj.2)
    {x : (Nat.Primes × ℕ) × Bool} (hx : x ∈ S ×ˢ (Finset.univ : Finset Bool)) :
    suzukiWienerAtoms S (suzukiOrientedStep x.1 x.2) = -(suzukiPrimePowerWeight x.1 : ℂ) := by
  rw [suzukiWienerAtoms]
  congr 1
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl, mul_one]
  · intro y hy hne
    have : suzukiOrientedStep x.1 x.2 ≠ suzukiOrientedStep y.1 y.2 := by
      intro heq
      exact hne (suzukiOrientedStep_injOn hj hy hx heq.symm).symm
    rw [if_neg (fun h => this h), mul_zero]
  · intro hxnot
    exact absurd hx hxnot

/-- The finite support of the coefficient family. -/
def suzukiAtomSupport (S : Finset (Nat.Primes × ℕ)) : Finset SuzukiSeamValuation :=
  (S ×ˢ (Finset.univ : Finset Bool)).image fun x => suzukiOrientedStep x.1 x.2

/-- **`(18)`: the exact Wiener mass of the visible prime alphabet.**  Each visible prime power
contributes its weight twice, once per orientation. -/
theorem discreteMass_enorm_suzukiWienerAtoms {S : Finset (Nat.Primes × ℕ)}
    (hj : ∀ pj ∈ S, 1 ≤ pj.2) :
    discreteMass (fun ν => ‖suzukiWienerAtoms S ν‖ₑ)
      = ENNReal.ofReal (2 * ∑ s ∈ S, suzukiPrimePowerWeight s) := by
  have hzero : ∀ ν ∉ suzukiAtomSupport S, ‖suzukiWienerAtoms S ν‖ₑ = 0 := by
    intro ν hν
    have : suzukiWienerAtoms S ν = 0 := by
      apply suzukiWienerAtoms_eq_zero
      intro x hx heq
      exact hν (by rw [suzukiAtomSupport, Finset.mem_image]; exact ⟨x, hx, heq.symm⟩)
    rw [this]
    simp
  rw [discreteMass, tsum_eq_sum hzero, suzukiAtomSupport,
    Finset.sum_image (fun x hx y hy h => suzukiOrientedStep_injOn hj hx hy h)]
  have hterm : ∀ x ∈ S ×ˢ (Finset.univ : Finset Bool),
      ‖suzukiWienerAtoms S (suzukiOrientedStep x.1 x.2)‖ₑ
        = ENNReal.ofReal (suzukiPrimePowerWeight x.1) := by
    intro x hx
    rw [suzukiWienerAtoms_apply hj hx, enorm_neg]
    rw [← Complex.enorm_real, ofReal_norm_eq_enorm]
    congr 1
    rw [Real.norm_eq_abs, abs_of_nonneg (suzukiPrimePowerWeight_nonneg x.1)]
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∑ x ∈ S ×ˢ (Finset.univ : Finset Bool),
      ENNReal.ofReal (suzukiPrimePowerWeight x.1)
      = ∑ s ∈ S, ∑ _b ∈ (Finset.univ : Finset Bool), ENNReal.ofReal (suzukiPrimePowerWeight s) :=
    Finset.sum_product
  rw [hsplit]
  have hcard : ∀ s ∈ S, (∑ _b ∈ (Finset.univ : Finset Bool),
      ENNReal.ofReal (suzukiPrimePowerWeight s))
      = ENNReal.ofReal (2 * suzukiPrimePowerWeight s) := by
    intro s _
    rw [Finset.sum_const, Finset.card_univ]
    have : Fintype.card Bool = 2 := rfl
    rw [this, two_nsmul, ← ENNReal.ofReal_add (suzukiPrimePowerWeight_nonneg s)
      (suzukiPrimePowerWeight_nonneg s)]
    congr 1
    ring
  rw [Finset.sum_congr rfl hcard, ← ENNReal.ofReal_sum_of_nonneg, Finset.mul_sum]
  intro s _
  have := suzukiPrimePowerWeight_nonneg s
  linarith

/-- Unit-phase evaluation of a valuation coefficient family at frequency `ξ`. -/
def suzukiWienerEval (ξ : ℝ) (t : SuzukiSeamValuation → ℂ) : ℂ :=
  ∑' ν, t ν * Complex.exp (Complex.I * (ξ * primeSeamCoordinate ν : ℝ))

/-- **`(15)`, prime block: unit-phase evaluation of `t_a` is Suzuki's finite cosine sum.** -/
theorem suzukiWienerEval_atoms {S : Finset (Nat.Primes × ℕ)} (hj : ∀ pj ∈ S, 1 ≤ pj.2) (ξ : ℝ) :
    suzukiWienerEval ξ (suzukiWienerAtoms S)
      = -2 * ∑ s ∈ S, (suzukiPrimePowerWeight s : ℂ)
          * Complex.cos ((ξ * ((s.2 : ℝ) * Real.log ((s.1 : ℕ) : ℝ)) : ℝ)) := by
  have hzero : ∀ ν ∉ suzukiAtomSupport S,
      suzukiWienerAtoms S ν * Complex.exp (Complex.I * (ξ * primeSeamCoordinate ν : ℝ)) = 0 := by
    intro ν hν
    have : suzukiWienerAtoms S ν = 0 := by
      apply suzukiWienerAtoms_eq_zero
      intro x hx heq
      exact hν (by rw [suzukiAtomSupport, Finset.mem_image]; exact ⟨x, hx, heq.symm⟩)
    rw [this, zero_mul]
  rw [suzukiWienerEval, tsum_eq_sum hzero, suzukiAtomSupport,
    Finset.sum_image (fun x hx y hy h => suzukiOrientedStep_injOn hj hx hy h)]
  have hterm : ∀ x ∈ S ×ˢ (Finset.univ : Finset Bool),
      suzukiWienerAtoms S (suzukiOrientedStep x.1 x.2)
          * Complex.exp (Complex.I * (ξ * primeSeamCoordinate (suzukiOrientedStep x.1 x.2) : ℝ))
        = -(suzukiPrimePowerWeight x.1 : ℂ)
            * Complex.exp (Complex.I *
                ((if x.2 then 1 else -1) * (ξ * ((x.1.2 : ℝ) * Real.log ((x.1.1 : ℕ) : ℝ))) : ℝ)) := by
    intro x hx
    rw [suzukiWienerAtoms_apply hj hx]
    congr 2
    rcases Bool.eq_false_or_eq_true x.2 with h | h
    · rw [h]
      simp only [suzukiOrientedStep, if_false, if_false, map_neg,
        primeSeamCoordinate_primePowerStep]
      push_cast
      ring
    · rw [h]
      simp only [suzukiOrientedStep, if_true, if_true, primeSeamCoordinate_primePowerStep]
      push_cast
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_product]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [Finset.sum_bool]
  have hcos : Complex.cos ((ξ * ((s.2 : ℝ) * Real.log ((s.1 : ℕ) : ℝ)) : ℝ))
      = (Complex.exp (Complex.I * ((ξ * ((s.2 : ℝ) * Real.log ((s.1 : ℕ) : ℝ))) : ℝ))
          + Complex.exp (-(Complex.I * ((ξ * ((s.2 : ℝ) * Real.log ((s.1 : ℕ) : ℝ))) : ℝ)))) / 2 := by
    rw [Complex.cos]
    congr 1 <;> ring_nf
  rw [hcos]
  have hneg : ((-1 : ℝ) * (ξ * ((s.2 : ℝ) * Real.log ((s.1 : ℕ) : ℝ))) : ℝ)
      = -((ξ * ((s.2 : ℝ) * Real.log ((s.1 : ℕ) : ℝ))) : ℝ) := by ring
  simp only [if_true, if_false, one_mul, hneg]
  push_cast
  ring

end

end GaloisForLFunctions.RHTower
