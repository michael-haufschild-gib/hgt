import GaloisForLFunctions.RHTower.FermiNymanRawMobiusTailFloor
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Möbius interpolation by factorials of integer degree

A Möbius-weighted sum of factorial degrees ⌊m/d⌋ gives the indicator of
the prefix through m at every positive integer sample. Its first difference
therefore gives the unit mass at m. Both statements hold over any
commutative ring, including integral contact orders and real spline data.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction

/-- The floor row of a factorial presentation at the positive degree k. -/
def factorialFloorReading (R : Type*) [CommRing R] (k : ℕ) :=
  Finsupp.linearCombination R (fun j : ℕ => ((j/k:ℕ):R))

/-- Möbius inversion of a single cutoff. The factorial degrees are integers. -/
def prefixFactorialCoeffs (R : Type*) [CommRing R] (m : ℕ) : ℕ →₀ R :=
  ∑ d ∈ Icc 1 m, Finsupp.single (m/d) ((moebius d:ℤ):R)

private theorem mobius_floor_nat (m : ℕ) {k : ℕ} (hk : 0 < k) :
    (∑ d ∈ Icc 1 m, moebius d * ((m/d/k:ℕ):ℤ))=if k ≤ m then 1 else 0 := by
  let M := m/k
  have hM : M ≤ m := Nat.div_le_self _ _
  have h := _root_.RHTower.sum_moebius_floor_truncated m (x := (M:ℝ))
    (Nat.cast_nonneg M) (by simpa only [Nat.floor_natCast] using hM)
  have hle : (1:ℝ) ≤ M ↔ k ≤ m := by
    have hc : (1:ℝ) ≤ M ↔ 1 ≤ M := by norm_cast
    exact hc.trans ((Nat.le_div_iff_mul_le hk).trans (by rw [one_mul]))
  have hdiv (d : ℕ) : (⌊(M:ℝ)/d⌋:ℤ)=((m/d/k:ℕ):ℤ) := by
    rw [Int.floor_div_natCast,Int.floor_natCast,← Int.natCast_ediv]
    dsimp only [M]
    rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.mul_comm k d]
  simp only [hdiv,hle] at h
  by_cases hm : k ≤ m <;> simp only [hm,ite_true,ite_false] at h ⊢ <;> exact_mod_cast h

theorem factorialFloorReading_prefix (R : Type*) [CommRing R] (m : ℕ) {k : ℕ} (hk : 0 < k) :
    factorialFloorReading R k (prefixFactorialCoeffs R m)=if k ≤ m then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z:R)) (mobius_floor_nat m hk)
  simp only [factorialFloorReading,prefixFactorialCoeffs,map_sum,Finsupp.linearCombination_single,
    smul_eq_mul]
  push_cast at h
  exact h

/-- The unique positive-degree presentation of the prescribed finite samples. -/
def sampleFactorialCoeffs {R : Type*} [CommRing R] (L : ℕ) (f : ℕ → R) : ℕ →₀ R :=
  ∑ m ∈ Icc 1 L, f m • (prefixFactorialCoeffs R m-prefixFactorialCoeffs R (m-1))

/-- Exact at all positive integer degrees, including every prime power. -/
theorem factorialFloorReading_sample {R : Type*} [CommRing R] (L : ℕ) (f : ℕ → R)
    {k : ℕ} (hk : 0 < k) :
    factorialFloorReading R k (sampleFactorialCoeffs L f)=if k ≤ L then f k else 0 := by
  simp only [sampleFactorialCoeffs,map_sum,map_smul,map_sub,factorialFloorReading_prefix R _ hk,smul_eq_mul]
  have step (m : ℕ) :
      f m*((if k ≤ m then 1 else 0)-(if k ≤ m-1 then 1 else 0))=if m=k then f m else 0 := by
    rcases lt_trichotomy m k with h|h|h
    · simp [show ¬ k ≤ m by omega,show ¬ k ≤ m-1 by omega,h.ne]
    · simp [h,show ¬ k ≤ k-1 by omega]
    · simp [h.le,show k ≤ m-1 by omega,h.ne']
  rw [sum_congr rfl fun m _ => step m]
  simp [mem_Icc,hk]

/-- The balance of the factorial presentation reads the sample at one. -/
theorem sampleFactorialCoeffs_balance {R : Type*} [CommRing R] (L : ℕ) (f : ℕ → R) :
    Finsupp.linearCombination R (fun j : ℕ => (j:R)) (sampleFactorialCoeffs L f)=
      if 1 ≤ L then f 1 else 0 := by
  simpa only [factorialFloorReading,Nat.div_one] using
    (factorialFloorReading_sample L f (k := 1) Nat.one_pos)

private theorem reading_max_support {R : Type*} [CommRing R] (c : ℕ →₀ R) {k : ℕ}
    (hk : k ∈ c.support) (hpos : 0 < k) (hmax : ∀ j ∈ c.support, j ≤ k) :
    factorialFloorReading R k c=c k := by
  change (∑ j ∈ c.support, c j*((j/k:ℕ):R))=c k
  rw [sum_eq_single_of_mem k hk]
  · simp [Nat.div_self hpos]
  · intro j hj hne
    simp [Nat.div_eq_of_lt (lt_of_le_of_ne (hmax j hj) hne)]

/-- Equality at all positive degrees forces equality of presentations
whose zero-degree coefficients vanish. -/
theorem factorialFloorReading_injective {R : Type*} [CommRing R] {a b : ℕ →₀ R}
    (hz : a 0=b 0) (h : ∀ k : ℕ, 0 < k → factorialFloorReading R k a=factorialFloorReading R k b) :
    a=b := by
  let c := a-b
  by_contra hne
  have hc : c≠0 := sub_ne_zero.mpr hne
  have hnon := Finsupp.support_nonempty_iff.mpr hc
  let k := c.support.max' hnon
  have hk : k ∈ c.support := max'_mem _ _
  have hk0 : k≠0 := by
    intro he
    apply Finsupp.mem_support_iff.mp hk
    rw [he]
    exact sub_eq_zero.mpr hz
  have hv := reading_max_support c hk (Nat.pos_of_ne_zero hk0) (fun j hj => le_max' _ _ hj)
  rw [show c=a-b from rfl,map_sub,h k (Nat.pos_of_ne_zero hk0),sub_self] at hv
  exact Finsupp.mem_support_iff.mp hk hv.symm

end GaloisForLFunctions.CountingHolography.Sections
