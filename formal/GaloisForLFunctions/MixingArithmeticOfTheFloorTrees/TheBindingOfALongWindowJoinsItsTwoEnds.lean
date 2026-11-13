import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsCarriedByItsFloorTrees
import Mathlib.NumberTheory.Chebyshev

/-!
# The binding of a long window joins its two ends

Take the window `(R, 2MR]`, `M = 10m`, at block size `R`, and its two dyadic ends `A = (R, 2R]`
and `B = (MR, 2MR]`. Each end alone holds the depth of a dyadic window, `−N(1, 1)` per unit of
mass. The ends are joined by the floor maps of the integers `k` of the size of the ratio: a
block `b ∈ B` is a child of a block of `A` under `k` iff `kR ≤ b < 2kR`. For `6m ≤ k ≤ 15m` at
least `2mR` blocks of `B` are such children (`twoEnds_count_ge`), so the contacts between the ends
are at least `(2R/15) (ψ(15m) − ψ(6m))` (`sum_twoEnds_floorContact_ge`).

On the packet `1_A + 1_B/√M`, whose mass is `2R`, the neutral part is at most
`2R N(1, 1) − (4R/(15√M)) (ψ(15m) − ψ(6m))` (`sum_twoEnds_neutralBlock_le`). So the ground
eigenvalue of the window satisfies (`eigenvalue_le_twoEnds`)

  `λ ≤ N(1, 1) − (2/(15√(10m))) (ψ(15m) − ψ(6m))`,

and with Chebyshev's bounds `ψ(15m) − ψ(6m) ≥ 3m log 2 − log(15m + 1) − 2√(6m) log(6m)`
(`psi_sub_psi_ge`) the binding energy of a window of ratio `20m` is at least a fixed multiple of
`√m`. With the upper bound by the Chebyshev sum `2 Σ_{k ≤ Q} Λ(k)/√k`, the binding energy of a
window of ratio `ρ` has the exact order `√ρ`, and it is carried by the floor maps of the
integers of the size of `ρ`, which join the two ends of the window.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### Sums over an interval of positions -/

/-- The indicator of the positions `s, …, s + n − 1`. -/
def blockRange (s n : ℕ) (j : ℕ) : ℝ := if s ≤ j ∧ j < s + n then 1 else 0

/-- A sum weighted by the indicator of an interval of positions is the sum over the interval. -/
theorem sum_blockRange_mul {s n J : ℕ} (h : s + n ≤ J) (F : ℕ → ℝ) :
    ∑ j ∈ range J, blockRange s n j * F j = ∑ i ∈ range n, F (s + i) := by
  have hfilt : (range J).filter (fun j => s ≤ j ∧ j < s + n) = Ico s (s + n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  simp only [blockRange, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, hfilt, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- The form of a symmetric kernel on `x + τ y`. -/
theorem sum_comb_form {J : ℕ} (K : ℕ → ℕ → ℝ) (hK : ∀ a b, K a b = K b a) (x y : ℕ → ℝ)
    (τ : ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, (x j + τ * y j) * (x l + τ * y l) * K j l =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * K j l +
        2 * τ * ∑ j ∈ range J, ∑ l ∈ range J, x j * y l * K j l +
          τ ^ 2 * ∑ j ∈ range J, ∑ l ∈ range J, y j * y l * K j l := by
  have hsw : ∑ j ∈ range J, ∑ l ∈ range J, y j * x l * K j l =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * y l * K j l := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [hK]; ring
  have hexp : ∑ j ∈ range J, ∑ l ∈ range J, (x j + τ * y j) * (x l + τ * y l) * K j l =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * K j l +
        τ * ∑ j ∈ range J, ∑ l ∈ range J, x j * y l * K j l +
        τ * ∑ j ∈ range J, ∑ l ∈ range J, y j * x l * K j l +
        τ ^ 2 * ∑ j ∈ range J, ∑ l ∈ range J, y j * y l * K j l := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, hsw]
  ring

/-! ### The count of the children between the ends -/

/-- The block `q ∈ [R, 2R)` is reached by exactly one position of the first end. -/
theorem sum_range_ite_eq_one {R q : ℕ} (h1 : R ≤ q) (h2 : q < 2 * R) :
    ∑ j ∈ range R, (if q = R + j then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single (q - R)]
  · rw [if_pos (by omega)]
  · intro j _ hj
    rw [if_neg (by omega)]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- A set of positions of the upper end that are all children of the lower end. -/
theorem twoEnds_count_of_subset {m R k : ℕ} (hk0 : 0 < k) {S : Finset ℕ}
    (hS : S ⊆ range (10 * m * R))
    (hchild : ∀ i ∈ S, R * k ≤ 10 * m * R + i ∧ 10 * m * R + i < 2 * R * k) :
    (S.card : ℝ) ≤ ∑ i ∈ range (10 * m * R), ∑ j ∈ range R,
      (if (10 * m * R + i) / k = R + j then (1 : ℝ) else 0) := by
  have hone : ∀ i ∈ S,
      ∑ j ∈ range R, (if (10 * m * R + i) / k = R + j then (1 : ℝ) else 0) = 1 := fun i hi =>
    sum_range_ite_eq_one ((Nat.le_div_iff_mul_le hk0).mpr (hchild i hi).1)
      ((Nat.div_lt_iff_lt_mul hk0).mpr (hchild i hi).2)
  calc (S.card : ℝ) = ∑ i ∈ S, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ∑ i ∈ S, ∑ j ∈ range R, (if (10 * m * R + i) / k = R + j then (1 : ℝ) else 0) :=
        (Finset.sum_congr rfl hone).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS fun i _ _ =>
        Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

/-- **At least `2mR` blocks of the upper end are children of the lower end under the floor map
of `k`**, for `6m ≤ k ≤ 15m`. -/
theorem twoEnds_count_ge {m R k : ℕ} (hk₁ : 6 * m ≤ k) (hk₂ : k ≤ 15 * m) (hk0 : 0 < k) :
    (2 * m * R : ℝ) ≤ ∑ i ∈ range (10 * m * R), ∑ j ∈ range R,
      (if (10 * m * R + i) / k = R + j then (1 : ℝ) else 0) := by
  have h6 : 6 * m * R ≤ k * R := Nat.mul_le_mul_right R hk₁
  rcases le_total k (10 * m) with hk | hk
  · -- the children are the first `2mR` blocks of the upper end
    have hk' : k * R ≤ 10 * m * R := Nat.mul_le_mul_right R hk
    have hS : range (2 * m * R) ⊆ range (10 * m * R) :=
      Finset.range_subset_range.mpr (Nat.mul_le_mul_right R (by omega))
    have h := twoEnds_count_of_subset (m := m) (R := R) hk0 hS fun i hi => by
      have hi := Finset.mem_range.mp hi
      constructor
      · rw [mul_comm R k]; omega
      · have : 12 * m * R ≤ 2 * R * k := by nlinarith
        nlinarith
    simpa using h
  · -- the children start at `(k − 10m)R`
    obtain ⟨d, rfl⟩ : ∃ d, k = 10 * m + d := ⟨k - 10 * m, by omega⟩
    have hd : d ≤ 5 * m := by omega
    have hdR : d * R ≤ 5 * m * R := Nat.mul_le_mul_right R hd
    have hS : Ico (d * R) (d * R + 2 * m * R) ⊆ range (10 * m * R) := fun i hi => by
      have hi := Finset.mem_Ico.mp hi
      exact Finset.mem_range.mpr (by nlinarith)
    have h := twoEnds_count_of_subset (m := m) (R := R) hk0 hS fun i hi => by
      have hi := Finset.mem_Ico.mp hi
      constructor
      · nlinarith
      · nlinarith
    simpa [Nat.card_Ico] using h

/-- The von Mangoldt sum over `(a, b]` is the difference of Chebyshev's function. -/
theorem psi_sub_psi_le_sum_Icc (a b : ℕ) (hab : a ≤ b) :
    ψ (b : ℝ) - ψ (a : ℝ) ≤ ∑ k ∈ Icc a b, (Λ k : ℝ) := by
  rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, Nat.floor_natCast,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab, add_sub_cancel_left]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
    have := Finset.mem_Ioc.mp hk
    exact Finset.mem_Icc.mpr ⟨this.1.le, this.2⟩) fun k _ _ =>
    ArithmeticFunction.vonMangoldt_nonneg

/-- **The contacts between the two ends.** -/
theorem sum_twoEnds_floorContact_ge {m R Q : ℕ} (hm : 1 ≤ m) (hR : 1 ≤ R) (hQ : 15 * m ≤ Q) :
    2 * R / 15 * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ)) ≤
      ∑ j ∈ range R, ∑ i ∈ range (10 * m * R), floorContact Q (R + j) (10 * m * R + i) := by
  have hexp : ∑ j ∈ range R, ∑ i ∈ range (10 * m * R), floorContact Q (R + j) (10 * m * R + i) =
      ∑ k ∈ Icc 2 Q, (Λ k : ℝ) / k * ∑ i ∈ range (10 * m * R), ∑ j ∈ range R,
        (if (10 * m * R + i) / k = R + j then (1 : ℝ) else 0) := by
    simp only [floorContact, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
  rw [hexp]
  have hsub : Icc (6 * m) (15 * m) ⊆ Icc 2 Q := Finset.Icc_subset_Icc (by omega) hQ
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => by
    have hk2 := (Finset.mem_Icc.mp hk).1
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num))
  have hterm : ∀ k ∈ Icc (6 * m) (15 * m), (Λ k : ℝ) * (2 * R / 15) ≤
      (Λ k : ℝ) / k * ∑ i ∈ range (10 * m * R), ∑ j ∈ range R,
        (if (10 * m * R + i) / k = R + j then (1 : ℝ) else 0) := by
    intro k hk
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hcount := twoEnds_count_ge (R := R) hk₁ hk₂ (by omega)
    have hΛ : (0 : ℝ) ≤ Λ k := ArithmeticFunction.vonMangoldt_nonneg
    have hkm : (k : ℝ) ≤ 15 * m := by exact_mod_cast hk₂
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    calc (Λ k : ℝ) * (2 * R / 15) = (Λ k : ℝ) / k * (k * (2 * R / 15)) := by
          field_simp
      _ ≤ (Λ k : ℝ) / k * (2 * m * R) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hΛ hk0.le)
          have hR' : (0 : ℝ) ≤ R := Nat.cast_nonneg R
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount (div_nonneg hΛ hk0.le)
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [← Finset.sum_mul, mul_comm]
  have hpsi := psi_sub_psi_le_sum_Icc (6 * m) (15 * m) (by omega)
  have hR' : (0 : ℝ) ≤ 2 * R / 15 := by positivity
  exact mul_le_mul_of_nonneg_left hpsi hR'

/-! ### The packet on the two ends -/

/-- **The neutral part on the packet `1_A + 1_B/√M`** of the window `(R, 20mR]`. -/
theorem sum_twoEnds_neutralBlock_le {m R Q : ℕ} (hm : 1 ≤ m) (hR : 1 ≤ R) (hQ : 15 * m ≤ Q) :
    ∑ j ∈ range ((20 * m - 1) * R), ∑ l ∈ range ((20 * m - 1) * R),
        (firstBlocks R j + 1 / Real.sqrt (10 * m) * blockRange ((10 * m - 1) * R) (10 * m * R) j) *
          (firstBlocks R l + 1 / Real.sqrt (10 * m) *
            blockRange ((10 * m - 1) * R) (10 * m * R) l) * neutralBlock Q (R + j) (R + l) ≤
      2 * R * neutralBlock Q 1 1 -
        4 * R / (15 * Real.sqrt (10 * m)) * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ)) := by
  have hRJ : R ≤ (20 * m - 1) * R := by
    have : 1 ≤ 20 * m - 1 := by omega
    nlinarith
  have hsJ : (10 * m - 1) * R + 10 * m * R ≤ (20 * m - 1) * R := by
    have e1 : (10 * m - 1) * R + 10 * m * R = (20 * m - 1) * R := by
      rw [← Nat.add_mul]
      congr 1
      omega
    omega
  have hsR : (10 * m - 1) * R + R = 10 * m * R := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  rw [sum_comb_form (fun j l => neutralBlock Q (R + j) (R + l))
    (fun a b => neutralBlock_comm Q _ _)]
  -- the first end
  have hAA : ∑ j ∈ range ((20 * m - 1) * R), ∑ l ∈ range ((20 * m - 1) * R), firstBlocks R j * firstBlocks R l *
      neutralBlock Q (R + j) (R + l) = R * neutralBlock Q 1 1 := by
    rw [← sum_neutralBlock_dyadic Q hR]
    have h1 : ∀ j, ∑ l ∈ range ((20 * m - 1) * R), firstBlocks R j * firstBlocks R l *
        neutralBlock Q (R + j) (R + l) =
        firstBlocks R j * ∑ l ∈ range R, neutralBlock Q (R + j) (R + l) := fun j => by
      rw [← sum_range_firstBlocks_mul hRJ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [h1]
    exact sum_range_firstBlocks_mul hRJ _
  -- the second end
  have hBB : ∑ j ∈ range ((20 * m - 1) * R), ∑ l ∈ range ((20 * m - 1) * R),
      blockRange ((10 * m - 1) * R) (10 * m * R) j *
        blockRange ((10 * m - 1) * R) (10 * m * R) l * neutralBlock Q (R + j) (R + l) =
      (10 * m * R : ℕ) * neutralBlock Q 1 1 := by
    rw [← sum_neutralBlock_dyadic Q (show 1 ≤ 10 * m * R by nlinarith)]
    have h1 : ∀ j, ∑ l ∈ range ((20 * m - 1) * R), blockRange ((10 * m - 1) * R) (10 * m * R) j *
        blockRange ((10 * m - 1) * R) (10 * m * R) l * neutralBlock Q (R + j) (R + l) =
        blockRange ((10 * m - 1) * R) (10 * m * R) j *
          ∑ i ∈ range (10 * m * R), neutralBlock Q (R + j) (10 * m * R + i) := fun j => by
      have := sum_blockRange_mul hsJ (fun l => blockRange ((10 * m - 1) * R) (10 * m * R) j *
        neutralBlock Q (R + j) (R + l))
      rw [Finset.mul_sum]
      refine (Finset.sum_congr rfl fun l _ => by ring).trans (this.trans ?_)
      exact Finset.sum_congr rfl fun i _ => by
        rw [show R + ((10 * m - 1) * R + i) = 10 * m * R + i by omega]
    simp only [h1]
    rw [sum_blockRange_mul hsJ]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
      rw [show R + ((10 * m - 1) * R + i) = 10 * m * R + i by omega]
  -- the coupling of the ends
  have hAB : ∑ j ∈ range ((20 * m - 1) * R), ∑ l ∈ range ((20 * m - 1) * R), firstBlocks R j *
      blockRange ((10 * m - 1) * R) (10 * m * R) l * neutralBlock Q (R + j) (R + l) =
      ∑ j ∈ range R, ∑ i ∈ range (10 * m * R), neutralBlock Q (R + j) (10 * m * R + i) := by
    have h1 : ∀ j, ∑ l ∈ range ((20 * m - 1) * R), firstBlocks R j *
        blockRange ((10 * m - 1) * R) (10 * m * R) l * neutralBlock Q (R + j) (R + l) =
        firstBlocks R j * ∑ i ∈ range (10 * m * R), neutralBlock Q (R + j) (10 * m * R + i) :=
      fun j => by
        have := sum_blockRange_mul hsJ (fun l => firstBlocks R j * neutralBlock Q (R + j) (R + l))
        rw [Finset.mul_sum]
        refine (Finset.sum_congr rfl fun l _ => by ring).trans (this.trans ?_)
        exact Finset.sum_congr rfl fun i _ => by
          rw [show R + ((10 * m - 1) * R + i) = 10 * m * R + i by omega]
    simp only [h1]
    exact sum_range_firstBlocks_mul hRJ _
  have hcross : ∑ j ∈ range R, ∑ i ∈ range (10 * m * R), neutralBlock Q (R + j) (10 * m * R + i) ≤
      -(2 * R / 15 * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ))) := by
    have hc := sum_twoEnds_floorContact_ge hm hR hQ
    have hle : ∑ j ∈ range R, ∑ i ∈ range (10 * m * R), neutralBlock Q (R + j) (10 * m * R + i) ≤
        -∑ j ∈ range R, ∑ i ∈ range (10 * m * R), floorContact Q (R + j) (10 * m * R + i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hj := Finset.mem_range.mp hj
      have hab : R + j < 10 * m * R + i := by nlinarith
      have h1 := neutralBlock_eq_one_sub Q (R + j) (10 * m * R + i)
      rw [min_eq_left hab.le, max_eq_right hab.le] at h1
      have h2 := neutralBlock_neg hab.ne 1
      linarith
    linarith
  rw [hAA, hBB, hAB]
  have hτ2 : (1 / Real.sqrt (10 * m)) ^ 2 * ((10 * m * R : ℕ) : ℝ) = R := by
    have hm' : (0 : ℝ) < 10 * m := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      linarith
    simp only [div_pow, one_pow, Real.sq_sqrt hm'.le]
    push_cast
    field_simp
  have hτ0 : 0 ≤ (1 / Real.sqrt (10 * m)) := by positivity
  have hτform : 2 * (1 / Real.sqrt (10 * m)) * (2 * R / 15 * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ))) =
      4 * R / (15 * Real.sqrt (10 * m)) * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ)) := by
    field_simp
    ring
  have hcross' := mul_le_mul_of_nonneg_left hcross (by positivity : (0 : ℝ) ≤ 2 * (1 / Real.sqrt (10 * m)))
  have e : (1 / Real.sqrt (10 * m)) ^ 2 * (((10 * m * R : ℕ) : ℝ) * neutralBlock Q 1 1) = R * neutralBlock Q 1 1 := by
    rw [← mul_assoc, hτ2]
  rw [e]
  nlinarith [hcross', hτform]

/-- The mass of the packet on the two ends is `2R`. -/
theorem sum_twoEnds_sq {m R : ℕ} (hm : 1 ≤ m) (hR : 1 ≤ R) :
    ∑ j ∈ range ((20 * m - 1) * R),
        (firstBlocks R j + 1 / Real.sqrt (10 * m) * blockRange ((10 * m - 1) * R) (10 * m * R) j) ^ 2 =
      2 * R := by
  have hdisj : ∀ j, firstBlocks R j * blockRange ((10 * m - 1) * R) (10 * m * R) j = 0 := by
    intro j
    simp only [firstBlocks, blockRange]
    split_ifs with h1 h2 <;> try norm_num
    exfalso
    have : R ≤ (10 * m - 1) * R := by
      have : 1 ≤ 10 * m - 1 := by omega
      nlinarith
    omega
  have hJ : R ≤ (20 * m - 1) * R := by
    have : 1 ≤ 20 * m - 1 := by omega
    nlinarith
  have hsJ : (10 * m - 1) * R + 10 * m * R ≤ (20 * m - 1) * R := by
    have e1 : (10 * m - 1) * R + 10 * m * R = (20 * m - 1) * R := by
      rw [← Nat.add_mul]
      congr 1
      omega
    omega
  have hexp : ∀ j, (firstBlocks R j + 1 / Real.sqrt (10 * m) *
      blockRange ((10 * m - 1) * R) (10 * m * R) j) ^ 2 =
      firstBlocks R j * 1 + (1 / Real.sqrt (10 * m)) ^ 2 *
        (blockRange ((10 * m - 1) * R) (10 * m * R) j * 1) := by
    intro j
    have hsq1 : firstBlocks R j ^ 2 = firstBlocks R j := by
      simp only [firstBlocks]; split_ifs <;> norm_num
    have hsq2 : blockRange ((10 * m - 1) * R) (10 * m * R) j ^ 2 =
        blockRange ((10 * m - 1) * R) (10 * m * R) j := by
      simp only [blockRange]; split_ifs <;> norm_num
    have h := hdisj j
    calc _ = firstBlocks R j ^ 2 + 2 * (1 / Real.sqrt (10 * m)) *
            (firstBlocks R j * blockRange ((10 * m - 1) * R) (10 * m * R) j) +
          (1 / Real.sqrt (10 * m)) ^ 2 * blockRange ((10 * m - 1) * R) (10 * m * R) j ^ 2 := by
          ring
      _ = _ := by rw [hsq1, hsq2, h]; ring
  simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_range_firstBlocks_mul hJ, sum_blockRange_mul hsJ]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hm' : (0 : ℝ) < 10 * m := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  rw [div_pow, one_pow, Real.sq_sqrt hm'.le]
  push_cast
  field_simp
  ring

/-- **The binding energy of a window of ratio `20m` is at least the depth of a dyadic window plus
`(2/(15√(10m))) (ψ(15m) − ψ(6m))`**, at every block size. -/
theorem eigenvalue_le_twoEnds {m R Q : ℕ} (hm : 1 ≤ m) (hR : 1 ≤ R) (hQ : 15 * m ≤ Q)
    {φ : Fin ((20 * m - 1) * R) → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q R ((20 * m - 1) * R) *ᵥ φ = lam • φ) :
    lam ≤ neutralBlock Q 1 1 -
      2 / (15 * Real.sqrt (10 * m)) * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ)) := by
  set σ : ℕ → ℝ := fun j =>
    firstBlocks R j + 1 / Real.sqrt (10 * m) * blockRange ((10 * m - 1) * R) (10 * m * R) j
  have hray : lam * ∑ i : Fin ((20 * m - 1) * R), σ i ^ 2 ≤
      bilin (neutralWindow Q R ((20 * m - 1) * R)) (fun i => σ i) (fun i => σ i) :=
    lam_mul_sum_sq_le_bilin (neutralWindow_symm Q R _)
      (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) hφ heig (fun i => σ i)
  have hb : bilin (neutralWindow Q R ((20 * m - 1) * R)) (fun i => σ i) (fun i => σ i) =
      ∑ j ∈ range ((20 * m - 1) * R), ∑ l ∈ range ((20 * m - 1) * R),
        σ j * σ l * neutralBlock Q (R + j) (R + l) :=
    sum_fin_windowMatrix_coe (neutralBlock Q) R _ σ
  have hmass : ∑ i : Fin ((20 * m - 1) * R), σ i ^ 2 = 2 * R :=
    (Fin.sum_univ_eq_sum_range (fun i => σ i ^ 2) _).trans (sum_twoEnds_sq hm hR)
  have hform := sum_twoEnds_neutralBlock_le hm hR hQ
  rw [hb, hmass] at hray
  have hR' : (0 : ℝ) < 2 * R := by
    have : (0 : ℝ) < R := by exact_mod_cast hR
    linarith
  have hfinal : lam * (2 * R) ≤ (neutralBlock Q 1 1 -
      2 / (15 * Real.sqrt (10 * m)) * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ))) * (2 * R) := by
    have e : (neutralBlock Q 1 1 -
        2 / (15 * Real.sqrt (10 * m)) * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ))) * (2 * R) =
        2 * R * neutralBlock Q 1 1 -
          4 * R / (15 * Real.sqrt (10 * m)) * (ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ)) := by
      ring
    rw [e]
    exact hray.trans hform
  exact le_of_mul_le_mul_right hfinal hR'

/-- **Chebyshev's bounds on the primes of `(6m, 15m]`**. -/
theorem psi_sub_psi_ge {m : ℕ} (hm : 1 ≤ m) :
    3 * m * Real.log 2 - Real.log (15 * m + 1) - 2 * Real.sqrt (6 * m) * Real.log (6 * m) ≤
      ψ ((15 * m : ℕ) : ℝ) - ψ ((6 * m : ℕ) : ℝ) := by
  have h1 := Chebyshev.psi_ge (15 * m)
  have h2 := Chebyshev.psi_le (x := ((6 * m : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ 6 * m by omega))
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  push_cast at h1 h2 ⊢
  rw [hlog4] at h2
  nlinarith

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
