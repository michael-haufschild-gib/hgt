import GaloisForLFunctions.BezoutValuationIncidence.RamanujanRadicalDilationReduction


/-!
# Physical clock sectors and their finite-cutoff boundary

The existing divisor reindexing and exact radical coefficient law transport
physical Diophantine sectors, keeping the original cutoff. For
`s = primeRadical r`, `v = lagVisibilityClock r`, and `T = H / v`, the law is

`S_r(v*h,H) = v*S_s(h,T) + v*(1/(T+1)-v/(H+1))*M_s(h,T)`.

Here `M` is the signed coefficient mass on the same finite fiber. At the
aligned horizon `H = v*(T+1)-1`, the correction vanishes exactly. The radical's
successor sector therefore survives at physical lag `v` in the original mode.
All sums retain one physical horizon. Data-only capstones cover every
nontrivial mode and positive integer scales; allowed signed sums can cancel.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

private theorem sector_clock_pos {r : ℕ} (hr : r ≠ 0) :
    0 < lagVisibilityClock r :=
  Nat.pos_of_ne_zero fun hz => hr ((lagVisibilityClock_eq_zero_iff r).mp hz)

private theorem mul_mem_Icc_of_mem_div {v H k : ℕ} (hv : 0 < v)
    (hk : k ∈ Icc 1 (H / v)) : v * k ∈ Icc 1 H := by
  obtain ⟨hk1, hkH⟩ := mem_Icc.mp hk
  apply mem_Icc.mpr
  constructor
  · have := Nat.mul_pos hv (show 0 < k by omega)
    omega
  · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hv).mp hkH

/-- Every finite weighted coefficient sum retains the exact clock reindexing. -/
theorem ramanujan_weighted_sum_clock_reindex (r N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, (d4BMRamanujanNaturalCoefficient n r).re * F n) =
      (lagVisibilityClock r : ℝ) *
        ∑ n ∈ Icc 1 (N / lagVisibilityClock r),
          (d4BMRamanujanNaturalCoefficient n (primeRadical r)).re * F (lagVisibilityClock r * n) := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [d4BMRamanujanNaturalCoefficient, lagVisibilityClock]
  · have hv := sector_clock_pos hr.ne'
    calc
      _ = ∑ n ∈ (Icc 1 N).filter (fun n => lagVisibilityClock r ∣ n),
          (d4BMRamanujanNaturalCoefficient n r).re * F n := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n _
        by_cases hn : lagVisibilityClock r ∣ n
        · simp only [if_pos hn]
        · have hz : (d4BMRamanujanNaturalCoefficient n r).re = 0 := by
            by_contra h
            exact hn ((ramanujanNaturalCoefficient_re_ne_zero_iff_clock r n).mp h).2
          simp only [if_neg hn, hz, zero_mul]
      _ = _ := by
        rw [sum_Icc_filter_dvd_reindex (lagVisibilityClock r) N hv]
        simp only [ramanujanNaturalCoefficient_re_clock_mul, mul_sum, mul_assoc]

private theorem clock_gap (v p q a b : ℕ) :
    dilationJumpGap p q (v * a, v * b) = (v : ℤ) * dilationJumpGap p q (a, b) := by
  simp only [dilationJumpGap, Nat.cast_mul]
  ring

/-- Exact finite sector transport before rescaling the reciprocal kernel. -/
theorem ramanujanDilationLagSector_clock_reindex {r : ℕ} (hr : r ≠ 0)
    (p q H : ℕ) (h : ℤ) :
    ramanujanDilationLagSector r p q H ((lagVisibilityClock r : ℤ) * h) =
      (lagVisibilityClock r : ℝ) ^ 2 *
        ∑ ab ∈ (dilationJumpPairs (H / lagVisibilityClock r) p q).filter
          (fun ab => dilationJumpGap p q ab = h),
          (d4BMRamanujanNaturalCoefficient ab.1 (primeRadical r)).re *
            (d4BMRamanujanNaturalCoefficient ab.2 (primeRadical r)).re *
            reciprocalJumpKernel H (p * (lagVisibilityClock r * ab.1))
              (q * (lagVisibilityClock r * ab.2)) := by
  classical
  let v := lagVisibilityClock r
  let W (a b : ℕ) : ℝ := if dilationJumpGap p q (a, b) = (v : ℤ) * h then
    reciprocalJumpKernel H (p * a) (q * b) else 0
  have hvZ : (v : ℤ) ≠ 0 := by exact_mod_cast (sector_clock_pos hr).ne'
  have heq (a b : ℕ) :
      (dilationJumpGap p q (v * a, v * b) = (v : ℤ) * h) ↔
        dilationJumpGap p q (a, b) = h := by
    rw [clock_gap]
    constructor
    · exact mul_left_cancel₀ hvZ
    · intro he
      rw [he]
  have hdiv (k : ℕ) : H / k / v = H / v / k := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k v]
  have hshape : ramanujanDilationLagSector r p q H ((v : ℤ) * h) =
      ∑ a ∈ Icc 1 (H / p), (d4BMRamanujanNaturalCoefficient a r).re *
        ∑ b ∈ Icc 1 (H / q), (d4BMRamanujanNaturalCoefficient b r).re * W a b := by
    simp only [ramanujanDilationLagSector, dilationJumpPairs, sum_filter,
      sum_product, ramanujanJumpPairTerm, mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    simp only [W]
    split_ifs <;> ring
  rw [hshape]
  simp_rw [ramanujan_weighted_sum_clock_reindex r]
  change (v : ℝ) * (∑ a ∈ Icc 1 (H / p / v),
    (d4BMRamanujanNaturalCoefficient a (primeRadical r)).re *
      ((v : ℝ) * ∑ b ∈ Icc 1 (H / q / v),
        (d4BMRamanujanNaturalCoefficient b (primeRadical r)).re * W (v * a) (v * b))) = _
  rw [hdiv p, hdiv q]
  simp only [dilationJumpPairs, sum_filter, sum_product, mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp only [W, heq]
  split_ifs <;> ring

/-- The finite Green kernel carries an explicit defect under integer clock rescaling. -/
theorem reciprocalJumpKernel_clock_rescaling {v H i j : ℕ} (hv : 0 < v)
    (hi : i ∈ Icc 1 (H / v)) (hj : j ∈ Icc 1 (H / v)) :
    (v : ℝ) ^ 2 * reciprocalJumpKernel H (v * i) (v * j) =
      (v : ℝ) * reciprocalJumpKernel (H / v) i j +
        (v : ℝ) * (1 / (((H / v : ℕ) : ℝ) + 1) - (v : ℝ) / ((H : ℝ) + 1)) := by
  have hmax : max (v * i) (v * j) = v * max i j := by
    rcases le_total i j with hij | hji
    · rw [max_eq_right hij, max_eq_right (Nat.mul_le_mul_left v hij)]
    · rw [max_eq_left hji, max_eq_left (Nat.mul_le_mul_left v hji)]
  rw [reciprocalJumpKernel_eq (mul_mem_Icc_of_mem_div hv hi) (mul_mem_Icc_of_mem_div hv hj),
    reciprocalJumpKernel_eq hi hj, hmax]
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hm0 : ((max i j : ℕ) : ℝ) ≠ 0 := by
    have hi1 := (mem_Icc.mp hi).1
    have : 0 < max i j := by omega
    exact_mod_cast this.ne'
  push_cast
  field_simp
  ring

/-- Signed coefficient mass on the same finite Diophantine fiber as the sector. -/
def ramanujanDilationLagMass (r p q H : ℕ) (h : ℤ) : ℝ :=
  ∑ ab ∈ (dilationJumpPairs H p q).filter (fun ab => dilationJumpGap p q ab = h),
    (d4BMRamanujanNaturalCoefficient ab.1 r).re *
      (d4BMRamanujanNaturalCoefficient ab.2 r).re

/-- Physical sector reduction includes its signed finite-cutoff boundary correction. -/
theorem ramanujanDilationLagSector_eq_clock_mul_radical_add_boundary {r p q : ℕ}
    (hr : r ≠ 0) (hp : 0 < p) (hq : 0 < q) (H : ℕ) (h : ℤ) :
    ramanujanDilationLagSector r p q H ((lagVisibilityClock r : ℤ) * h) =
      (lagVisibilityClock r : ℝ) *
        ramanujanDilationLagSector (primeRadical r) p q (H / lagVisibilityClock r) h +
      (lagVisibilityClock r : ℝ) *
        (1 / (((H / lagVisibilityClock r : ℕ) : ℝ) + 1) -
          (lagVisibilityClock r : ℝ) / ((H : ℝ) + 1)) *
        ramanujanDilationLagMass (primeRadical r) p q (H / lagVisibilityClock r) h := by
  classical
  rw [ramanujanDilationLagSector_clock_reindex hr]
  unfold ramanujanDilationLagSector ramanujanDilationLagMass
  simp only [mul_sum]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro ab hab
  have hab' := (mem_filter.mp hab).1
  obtain ⟨ha, hb⟩ := mem_product.mp hab'
  have hk := reciprocalJumpKernel_clock_rescaling (sector_clock_pos hr)
    (mul_mem_Icc_of_mem_div hp ha) (mul_mem_Icc_of_mem_div hq hb)
  have hpa : p * (lagVisibilityClock r * ab.1) = lagVisibilityClock r * (p * ab.1) := by ring
  have hqb : q * (lagVisibilityClock r * ab.2) = lagVisibilityClock r * (q * ab.2) := by ring
  unfold ramanujanJumpPairTerm
  rw [hpa, hqb]
  calc
    _ = ((d4BMRamanujanNaturalCoefficient ab.1 (primeRadical r)).re *
      (d4BMRamanujanNaturalCoefficient ab.2 (primeRadical r)).re) *
        ((lagVisibilityClock r : ℝ) ^ 2 * reciprocalJumpKernel H
          (lagVisibilityClock r * (p * ab.1)) (lagVisibilityClock r * (q * ab.2))) := by ring
    _ = _ := by rw [hk]; ring

/-- Data-only finite-cutoff law on every nontrivial mode and positive integer scales. -/
theorem dilation_clock_sector_boundary (r p q H : ℕ) (h : ℤ) :
    let R := r + 2
    let v := lagVisibilityClock R
    let s := primeRadical R
    ramanujanDilationLagSector R (p + 1) (q + 1) H ((v : ℤ) * h) =
      (v : ℝ) * ramanujanDilationLagSector s (p + 1) (q + 1) (H / v) h +
        (v : ℝ) * (1 / (((H / v : ℕ) : ℝ) + 1) - (v : ℝ) / ((H : ℝ) + 1)) *
          ramanujanDilationLagMass s (p + 1) (q + 1) (H / v) h :=
  ramanujanDilationLagSector_eq_clock_mul_radical_add_boundary (by omega) (by omega) (by omega) H h

/-- An aligned physical cutoff removes exactly the clock boundary defect. -/
theorem ramanujanDilationLagSector_clock_aligned {r p q : ℕ}
    (hr : r ≠ 0) (hp : 0 < p) (hq : 0 < q) (T : ℕ) (h : ℤ) :
    ramanujanDilationLagSector r p q (lagVisibilityClock r * (T + 1) - 1)
        ((lagVisibilityClock r : ℤ) * h) =
      (lagVisibilityClock r : ℝ) * ramanujanDilationLagSector (primeRadical r) p q T h := by
  let v := lagVisibilityClock r
  have hv : 0 < v := sector_clock_pos hr
  have hform : v * (T + 1) - 1 = (v - 1) + v * T := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hdiv : (v * (T + 1) - 1) / v = T := by
    rw [hform, Nat.add_mul_div_left _ _ hv, Nat.div_eq_of_lt (by omega), zero_add]
  have hplus : (((v * (T + 1) - 1 : ℕ) : ℝ) + 1) = (v : ℝ) * ((T : ℝ) + 1) := by
    have hpos : 1 ≤ v * (T + 1) := by
      have := Nat.mul_pos hv (show 0 < T + 1 by omega)
      omega
    exact_mod_cast Nat.sub_add_cancel hpos
  have hzero : 1 / ((T : ℝ) + 1) -
      (v : ℝ) / ((((v * (T + 1) - 1 : ℕ) : ℝ) + 1)) = 0 := by
    have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
    rw [hplus]
    field_simp
    ring
  have he := ramanujanDilationLagSector_eq_clock_mul_radical_add_boundary hr hp hq
    (v * (T + 1) - 1) h
  rw [hdiv, hzero, mul_zero, zero_mul, add_zero] at he
  exact he

/-- The squarefree successor survives at the original physical visibility clock. -/
theorem dilation_clock_successor_transport (r p q T : ℕ) :
    let R := r + 2
    let v := lagVisibilityClock R
    ramanujanDilationLagSector R (p + 1) (q + 1) (v * (T + 1) - 1) (v : ℤ) =
      (v : ℝ) * ramanujanDilationLagSector (primeRadical R) (p + 1) (q + 1) T 1 := by
  simpa only [mul_one] using ramanujanDilationLagSector_clock_aligned
    (r := r + 2) (p := p + 1) (q := q + 1) (by omega) (by omega) (by omega) T 1

end
end GaloisForLFunctions.BezoutValuationIncidence
