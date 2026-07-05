/-
# The widest-gap march on the harmonic pole class, uniformly in the carrier length

Poles sit at the partial sums of `2/j` (`harmT`), so consecutive gaps have widths `2/j` and
the first gap is the widest. For the charge in that gap at offset `s ∈ [3/5, 1)` before its
ahead pole, the rank-paired adiabatic ledger of the step into the second gap is positive for
EVERY number of ahead poles. The single behind pair contributes a gain of at least `2`
(`coth v ≥ 1/v` at the shrunken behind distance against `coth v < 1 + 1/v` at the old one),
while the total ahead loss stays below `4` uniformly: each loss term is at most
`2/(e^a − 1)` at the marched ahead distance `a`, the harmonic slice `harmT (3+k) − harmT 2`
dominates `2·log((k+4)/3)` term by term, and `e^s ≥ 1 + s ≥ 8/5` turns the `k`-th loss bound
into the rational envelope `90/(8(k+4)² − 45)`, whose partial sums a telescoping comparison
keeps below `3.89`. With the far cushion above `2`, the ledger clears at the sparse edge of
the class for all carrier lengths.
-/
import GaloisForLFunctions.RHTower.LegAdiabatic
import GaloisForLFunctions.RHTower.LegBulkCarrier

namespace RHTower

open Finset


/-! ### Harmonic slices dominate logarithms -/

/-- `harmT` is monotone: it is a sum of positive terms over an initial segment. -/
theorem harmT_mono {n m : ℕ} (h : n ≤ m) : harmT n ≤ harmT m :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun j _ _ => by positivity)

/-- One step of the harmonic carrier: `harmT (m+1) = harmT m + 2/(m+1)`. -/
theorem harmT_succ (m : ℕ) : harmT (m + 1) = harmT m + 2 / (m + 1) := by
  rw [harmT, harmT, Finset.sum_range_succ]

/-- The first two gaps have total width `3`. -/
theorem harmT_two : harmT 2 = 3 := by
  simp [harmT, Finset.sum_range_succ]
  norm_num

/-- **The harmonic slice dominates the logarithm**: `2·log((k+4)/3) ≤ harmT (3+k) − harmT 2`.
Each harmonic step `2/(m+1)` dominates the logarithmic step `2·log((m+2)/(m+1))` by the
tangent-line bound `log x ≤ x − 1`. -/
theorem harmT_slice_ge_log (k : ℕ) :
    2 * Real.log (((k : ℝ) + 4) / 3) ≤ harmT (3 + k) - harmT 2 := by
  induction k with
  | zero =>
      have hlog : Real.log ((4 : ℝ) / 3) ≤ 1 / 3 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
        linarith
      have h3 : harmT 3 - harmT 2 = 2 / 3 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, harmT_succ]
        norm_num
      simp only [Nat.cast_zero, zero_add, Nat.add_zero]
      rw [h3]
      linarith
  | succ k ih =>
      have hpos1 : (0 : ℝ) < ((k : ℝ) + 4) / 3 := by positivity
      have hpos2 : (0 : ℝ) < ((k : ℝ) + 5) / ((k : ℝ) + 4) := by positivity
      have hstep : 2 * Real.log (((k : ℝ) + 5) / ((k : ℝ) + 4)) ≤ 2 / ((k : ℝ) + 4) := by
        have := Real.log_le_sub_one_of_pos hpos2
        have harith : ((k : ℝ) + 5) / ((k : ℝ) + 4) - 1 = 1 / ((k : ℝ) + 4) := by
          field_simp
          ring
        have h2 : 2 / ((k : ℝ) + 4) = 2 * (1 / ((k : ℝ) + 4)) := by ring
        rw [h2]
        linarith
      have hsplit : Real.log ((((k : ℝ) + 1) + 4) / 3)
          = Real.log (((k : ℝ) + 4) / 3) + Real.log (((k : ℝ) + 5) / ((k : ℝ) + 4)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
      have hcarrier : harmT (3 + (k + 1)) = harmT (3 + k) + 2 / ((k : ℝ) + 4) := by
        rw [show 3 + (k + 1) = (3 + k) + 1 from rfl, harmT_succ]
        push_cast
        ring_nf
      push_cast
      rw [hsplit, hcarrier]
      linarith

/-! ### The sparse-edge configuration: rank distances of the widest-gap step -/

/-- Ahead rank distances before the step: pole `2 + k` of the harmonic carrier seen from the
charge in the widest gap, at offset `s` before its ahead pole. -/
noncomputable def edgeOldA (s : ℝ) : ℕ → ℝ := fun k => harmT (2 + k) - 2 + s

/-- Ahead rank distances after the step into the second gap, at the same offset `s`. -/
noncomputable def edgeNewA (s : ℝ) : ℕ → ℝ := fun k => harmT (3 + k) - 3 + s

/-- The single behind distance before the step: the widest gap has width `2`. -/
def edgeOldB (s : ℝ) : ℕ → ℝ := fun _ => 2 - s

/-- The single behind distance after the step: the second gap has width `1`. -/
def edgeNewB (s : ℝ) : ℕ → ℝ := fun _ => 1 - s

/-- **The exponential of a marched ahead distance dominates a rational square**: from the
harmonic-log bound and `e^s ≥ 1 + s ≥ 8/5`. -/
theorem exp_edgeNewA_ge (k : ℕ) {s : ℝ} (hs : 3 / 5 ≤ s) :
    8 / 5 * ((((k : ℝ) + 4) / 3) ^ 2) ≤ Real.exp (edgeNewA s k) := by
  have hx : (0 : ℝ) < ((k : ℝ) + 4) / 3 := by positivity
  have hslice := harmT_slice_ge_log k
  have hsq : ((((k : ℝ) + 4) / 3) ^ 2) ≤ Real.exp (harmT (3 + k) - 3) := by
    calc ((((k : ℝ) + 4) / 3) ^ 2)
        = Real.exp (2 * Real.log (((k : ℝ) + 4) / 3)) := by
          rw [show (2 : ℝ) * Real.log (((k : ℝ) + 4) / 3)
              = Real.log (((k : ℝ) + 4) / 3) + Real.log (((k : ℝ) + 4) / 3) by ring,
            Real.exp_add, Real.exp_log hx]
          ring
      _ ≤ Real.exp (harmT (3 + k) - 3) := by
          apply Real.exp_le_exp.mpr
          have := harmT_two
          linarith
  have hexp_s : (8 : ℝ) / 5 ≤ Real.exp s := by
    have := Real.add_one_le_exp s
    linarith
  have hmul : 8 / 5 * ((((k : ℝ) + 4) / 3) ^ 2)
      ≤ Real.exp (harmT (3 + k) - 3) * Real.exp s := by
    calc 8 / 5 * ((((k : ℝ) + 4) / 3) ^ 2)
        = ((((k : ℝ) + 4) / 3) ^ 2) * (8 / 5) := by ring
      _ ≤ Real.exp (harmT (3 + k) - 3) * Real.exp s :=
          mul_le_mul hsq hexp_s (by norm_num) (Real.exp_pos _).le
  calc 8 / 5 * ((((k : ℝ) + 4) / 3) ^ 2)
      ≤ Real.exp (harmT (3 + k) - 3) * Real.exp s := hmul
    _ = Real.exp (edgeNewA s k) := by rw [← Real.exp_add, edgeNewA]

/-- **Rational envelope for one ahead loss**: the `k`-th loss of the widest-gap step is at most
`90/(8(k+4)² − 45)`, uniformly over offsets `s ≥ 3/5`. The loss is below the excess
`2/(e^a − 1)` of the marched `coth` over `1`, and the exponential bound turns that excess
rational. -/
theorem edge_loss_le (k : ℕ) {s : ℝ} (hs : 3 / 5 ≤ s) :
    rcoth (edgeNewA s k / 2) - rcoth (edgeOldA s k / 2)
      ≤ 90 / (8 * ((k : ℝ) + 4) ^ 2 - 45) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hnewA : (0 : ℝ) < edgeNewA s k := by
    have h1 : harmT 3 ≤ harmT (3 + k) := harmT_mono (by omega)
    have h3 : harmT 3 = harmT 2 + 2 / 3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, harmT_succ]; norm_num
    rw [edgeNewA]
    have := harmT_two
    linarith
  have holdA : (0 : ℝ) < edgeOldA s k := by
    have h1 : harmT 2 ≤ harmT (2 + k) := harmT_mono (by omega)
    rw [edgeOldA]
    have := harmT_two
    linarith
  have hone : 1 < rcoth (edgeOldA s k / 2) := one_lt_rcoth_of_pos (by positivity)
  have hden : (0 : ℝ) < 8 * ((k : ℝ) + 4) ^ 2 - 45 := by
    have hk : (16 : ℝ) ≤ ((k : ℝ) + 4) ^ 2 := by nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
    linarith
  have hexp := exp_edgeNewA_ge k hs
  have hE1 : (0 : ℝ) < Real.exp (edgeNewA s k) - 1 := by
    have hk : (16 : ℝ) ≤ ((k : ℝ) + 4) ^ 2 := by nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
    nlinarith
  have hsub : rcoth (edgeNewA s k / 2) - 1 = 2 / (Real.exp (edgeNewA s k) - 1) := by
    have := rcoth_sub_one (show (0 : ℝ) < edgeNewA s k / 2 by positivity)
    rw [show 2 * (edgeNewA s k / 2) = edgeNewA s k by ring] at this
    exact this
  have henv : 2 / (Real.exp (edgeNewA s k) - 1) ≤ 90 / (8 * ((k : ℝ) + 4) ^ 2 - 45) := by
    rw [div_le_div_iff₀ hE1 hden]
    nlinarith [hexp]
  linarith

/-- **Telescoping tail for the rational envelope**: from rank `K ≥ 2` on, each envelope term is
below `(45/4)(1/(k+3) − 1/(k+4))`, so every partial tail sum is below `45/(4(K+3))`. -/
theorem edge_env_tail {K R : ℕ} (hK : 2 ≤ K) (hKR : K ≤ R) :
    (∑ k ∈ Finset.Ico K R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45))
      ≤ 45 / (4 * ((K : ℝ) + 3)) := by
  have hterm : ∀ k ∈ Finset.Ico K R,
      (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45)
        ≤ 45 / 4 * (1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 4)) := by
    intro k hk
    have hk2 : 2 ≤ k := le_trans hK (Finset.mem_Ico.mp hk).1
    have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hden : (0 : ℝ) < 8 * ((k : ℝ) + 4) ^ 2 - 45 := by nlinarith
    have hgap : 45 / 4 * (1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 4))
        = 45 / 4 * (1 / (((k : ℝ) + 3) * ((k : ℝ) + 4))) := by
      congr 1
      field_simp
      ring
    rw [hgap, div_le_iff₀ hden]
    have hprod : (0 : ℝ) < ((k : ℝ) + 3) * ((k : ℝ) + 4) := by positivity
    rw [show (45 : ℝ) / 4 * (1 / (((k : ℝ) + 3) * ((k : ℝ) + 4))) * (8 * ((k : ℝ) + 4) ^ 2 - 45)
        = 45 / 4 * (8 * ((k : ℝ) + 4) ^ 2 - 45) / (((k : ℝ) + 3) * ((k : ℝ) + 4)) by ring]
    rw [le_div_iff₀ hprod]
    nlinarith
  calc (∑ k ∈ Finset.Ico K R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45))
      ≤ ∑ k ∈ Finset.Ico K R, (45 : ℝ) / 4 * (1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 4)) :=
        Finset.sum_le_sum hterm
    _ = 45 / 4 * ∑ k ∈ Finset.Ico K R, (1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 4)) := by
        rw [Finset.mul_sum]
    _ ≤ 45 / (4 * ((K : ℝ) + 3)) := by
        have htel : (∑ k ∈ Finset.Ico K R, (1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 4)))
            = 1 / ((K : ℝ) + 3) - 1 / ((R : ℝ) + 3) := by
          rw [Finset.sum_Ico_eq_sum_range]
          have hshift : ∀ i, 1 / (((K + i : ℕ) : ℝ) + 3) - 1 / (((K + i : ℕ) : ℝ) + 4)
              = (fun j => 1 / (((K + j : ℕ) : ℝ) + 3)) i
                - (fun j => 1 / (((K + j : ℕ) : ℝ) + 3)) (i + 1) := by
            intro i
            simp only []
            push_cast
            ring_nf
          calc (∑ i ∈ Finset.range (R - K), (1 / (((K + i : ℕ) : ℝ) + 3) - 1 / (((K + i : ℕ) : ℝ) + 4)))
              = ∑ i ∈ Finset.range (R - K), ((fun j => 1 / (((K + j : ℕ) : ℝ) + 3)) i
                  - (fun j => 1 / (((K + j : ℕ) : ℝ) + 3)) (i + 1)) :=
                Finset.sum_congr rfl (fun i _ => hshift i)
            _ = 1 / (((K + 0 : ℕ) : ℝ) + 3) - 1 / (((K + (R - K) : ℕ) : ℝ) + 3) :=
                Finset.sum_range_sub' _ _
            _ = 1 / ((K : ℝ) + 3) - 1 / ((R : ℝ) + 3) := by
                rw [Nat.add_zero, Nat.add_sub_cancel' hKR]
        rw [htel]
        have hR3 : (0 : ℝ) < (R : ℝ) + 3 := by positivity
        have h1 : (0 : ℝ) ≤ 1 / ((R : ℝ) + 3) := by positivity
        have heq : (45 : ℝ) / 4 * (1 / ((K : ℝ) + 3)) = 45 / (4 * ((K : ℝ) + 3)) := by
          field_simp
        nlinarith [h1]

/-- **The total ahead loss of the widest-gap step is below `4`, for every carrier length**:
six explicit envelope terms plus the telescoping tail give `3.89 < 4`, uniformly in the
number of ahead poles and over all offsets `s ≥ 3/5`. -/
theorem edge_loss_sum_lt_four (R : ℕ) {s : ℝ} (hs : 3 / 5 ≤ s) :
    (∑ k ∈ range R, (rcoth (edgeNewA s k / 2) - rcoth (edgeOldA s k / 2))) < 4 := by
  have henv_nonneg : ∀ k : ℕ, (0 : ℝ) ≤ 90 / (8 * ((k : ℝ) + 4) ^ 2 - 45) := by
    intro k
    have hden : (0 : ℝ) < 8 * ((k : ℝ) + 4) ^ 2 - 45 := by
      nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
    positivity
  have hbound : (∑ k ∈ range R, (rcoth (edgeNewA s k / 2) - rcoth (edgeOldA s k / 2)))
      ≤ ∑ k ∈ range R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45) :=
    Finset.sum_le_sum (fun k _ => edge_loss_le k hs)
  have hsix : (∑ k ∈ range 6, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45)) + 45 / 36 < 4 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rcases le_total R 6 with hR | hR
  · have hsub : (∑ k ∈ range R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45))
        ≤ ∑ k ∈ range 6, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hR)
        (fun k _ _ => henv_nonneg k)
    have htail : (0 : ℝ) ≤ 45 / 36 := by norm_num
    linarith
  · have hsplit : (∑ k ∈ range R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45))
        = (∑ k ∈ range 6, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45))
          + ∑ k ∈ Finset.Ico 6 R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le 6) hR]
    have htail := edge_env_tail (K := 6) (R := R) (by norm_num) hR
    have h36 : (45 : ℝ) / (4 * ((6 : ℕ) : ℝ) + 12) = 45 / 36 := by norm_num
    have htail' : (∑ k ∈ Finset.Ico 6 R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45))
        ≤ 45 / 36 := by
      calc (∑ k ∈ Finset.Ico 6 R, (90 : ℝ) / (8 * ((k : ℝ) + 4) ^ 2 - 45))
          ≤ 45 / (4 * (((6 : ℕ) : ℝ) + 3)) := htail
        _ = 45 / 36 := by norm_num
    linarith

/-- **The single behind pair of the widest-gap step gains at least `2`** for offsets
`s ∈ [3/5, 1)`: the shrunken behind distance `1 − s` pushes `coth ≥ 2/(1−s) ≥ 5` while the
old behind distance `2 − s > 1` keeps the departing `coth` below `1 + 2/(2−s) < 3`. -/
theorem edge_gain_ge_two {s : ℝ} (hs : 3 / 5 ≤ s) (hs1 : s < 1) :
    2 ≤ rcoth ((1 - s) / 2) - rcoth ((2 - s) / 2) := by
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have h2s : (0 : ℝ) < 2 - s := by linarith
  have hlo : 1 / ((1 - s) / 2) ≤ rcoth ((1 - s) / 2) := inv_le_rcoth (by positivity)
  have hhi : rcoth ((2 - s) / 2) < 1 + 1 / ((2 - s) / 2) := rcoth_lt_one_add_inv (by positivity)
  have e1 : 1 / ((1 - s) / 2) = 2 / (1 - s) := one_div_div _ _
  have e2 : 1 / ((2 - s) / 2) = 2 / (2 - s) := one_div_div _ _
  have h3 : (5 : ℝ) ≤ 2 / (1 - s) := by
    rw [le_div_iff₀ h1s]
    linarith
  have h4 : 2 / (2 - s) ≤ 2 := by
    rw [div_le_iff₀ h2s]
    linarith
  rw [e1] at hlo
  rw [e2] at hhi
  linarith

/-- **The widest-gap march of the harmonic class clears for EVERY carrier length**: with the
charge at offset `s ∈ [3/5, 1)` in the widest gap, the rank ledger of the step into the second
gap is positive for every number `R` of paired ahead poles — behind gain at least `2`, total
ahead loss below `4 = 2 + 2`, and the unconditional far cushion above `2`. The far distances
are the newly entered behind pole at `3 − s` and the departing ahead pole at
`harmT (R+2) − 2 + s`. -/
theorem harmonic_edge_march (R : ℕ) {s : ℝ} (hs : 3 / 5 ≤ s) (hs1 : s < 1) :
    0 < legRankNew 1 R (edgeNewB s) (edgeNewA s) s (3 - s)
        - legRankOld 1 R (edgeOldB s) (edgeOldA s) s (harmT (R + 2) - 2 + s) := by
  have hfA : (0 : ℝ) < harmT (R + 2) - 2 + s := by
    have h1 : harmT 2 ≤ harmT (R + 2) := harmT_mono (by omega)
    have := harmT_two
    linarith
  have hfB : (0 : ℝ) < 3 - s := by linarith
  refine rank_march_pos_of_gain_loss (γ := 2) hfA hfB ?_ ?_
  · rw [Finset.sum_range_one]
    exact edge_gain_ge_two hs hs1
  · have h4 := edge_loss_sum_lt_four R hs
    linarith

end RHTower
