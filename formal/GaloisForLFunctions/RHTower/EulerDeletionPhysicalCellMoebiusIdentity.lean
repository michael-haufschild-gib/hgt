import GaloisForLFunctions.RHTower.EulerDeletionCoefficientPrefixEnergy
import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingale
import GaloisForLFunctions.RHTower.MoebiusApproximantResidual
import GaloisForLFunctions.RHTower.TruncatedMoebiusResidual

/-!
# Initial physical cells of the Euler-deletion source

On the unmodified initial physical cells, the literal finite Möbius residue source has one
exact scalar coefficient: the reciprocal Möbius tail.  The resulting physical-energy lower
bound retains the original positive cell mass and every source divisor level.  It records a
necessary quantitative condition for an EDQ covariance ceiling; it supplies no tail estimate.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower

private theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ d ∈ Icc 1 N, f d := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

open DeletionCoefficientTransfer

/-- On each physical cell in the literal initial cutoff, floor inversion leaves exactly the
reciprocal Möbius tail. -/
theorem physical_moebius_cell_eq_reciprocal_tail {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    cell (fun d => ((μ d : ℤ) : ℝ)) N n =
      (n : ℝ) * (∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)) - 1 := by
  rw [cell]
  have h := sum_moebius_modSeq hn hnN
  calc
    (∑ i ∈ range N, ((μ (i + 1) : ℤ) : ℝ) *
        ((n % (i + 1) : ℕ) : ℝ) / ((i : ℝ) + 1)) =
      ∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) * (((n % d : ℕ) : ℝ) / (d : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using
          (sum_range_succ_eq_sum_Icc
            (fun d => ((μ d : ℤ) : ℝ) * (((n % d : ℕ) : ℝ) / (d : ℝ))) N)
    _ = _ := h

/-- On every physical cell, including the complete tail, the source is the reciprocal Möbius
tail minus the exact truncated divisor accumulation. -/
theorem physical_moebius_cell_eq_truncated_divisor_tail (N k : ℕ) :
    cell (fun d => ((μ d : ℤ) : ℝ)) N k =
      (k : ℝ) * (∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)) -
        ∑ j ∈ Icc 1 k, truncMoebiusDivisorSum N j := by
  have hcell : cell (fun d => ((μ d : ℤ) : ℝ)) N k =
      ∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) * (((k % d : ℕ) : ℝ) / (d : ℝ)) := by
    rw [cell]
    simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using
      (sum_range_succ_eq_sum_Icc
        (fun d => ((μ d : ℤ) : ℝ) * (((k % d : ℕ) : ℝ) / (d : ℝ))) N)
  have hneg :
      ∑ d ∈ Icc 1 N, (-((μ d : ℤ) : ℝ)) * (((k % d : ℕ) : ℝ) / (d : ℝ)) =
        -∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) * (((k % d : ℕ) : ℝ) / (d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have h := moebius_residual_eq_general k N
  rw [hneg] at h
  rw [hcell]
  linarith

/-- The complete original physical energy is exactly the weighted square of the truncated
Möbius-divisor discrepancy.  This leaves the fixed start of the physical tail in place. -/
theorem hasSum_physical_moebius_truncated_divisor_energy (N : ℕ) :
    HasSum
      (fun i : ℕ =>
        ((((i + 1 : ℕ) : ℝ) *
          (∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)) -
          ∑ j ∈ Icc 1 (i + 1), truncMoebiusDivisorSum N j) ^ 2) /
          (((i : ℝ) + 1) * ((i : ℝ) + 2)))
      (‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ ^ 2) := by
  convert hasSum_source_energy (fun d => ((μ d : ℤ) : ℝ)) N using 1
  funext i
  rw [physical_moebius_cell_eq_truncated_divisor_tail]

/-- The full truncated-divisor discrepancy evolves by the literal newly inserted divisor.
The formula retains its Möbius sign and the fixed physical cell cutoff. -/
theorem truncated_divisor_accumulation_succ (N k : ℕ) :
    (∑ j ∈ Icc 1 k, truncMoebiusDivisorSum (N + 1) j) =
      (∑ j ∈ Icc 1 k, truncMoebiusDivisorSum N j) +
        ((μ (N + 1) : ℤ) : ℝ) * ((k / (N + 1) : ℕ) : ℝ) := by
  calc
    ∑ j ∈ Icc 1 k, truncMoebiusDivisorSum (N + 1) j =
      ∑ d ∈ Icc 1 (N + 1), ((μ d : ℤ) : ℝ) * ((k / d : ℕ) : ℝ) :=
        (sum_moebius_floor_eq_sum_trunc k (N + 1)).symm
    _ = (∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) * ((k / d : ℕ) : ℝ)) +
        ((μ (N + 1) : ℤ) : ℝ) * ((k / (N + 1) : ℕ) : ℝ) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    _ = _ := by rw [sum_moebius_floor_eq_sum_trunc]

/-- Exact chronological energy increment of the literal physical source.  The middle term is
the signed cross-time covariance that a multi-prime EDQ estimate must control. -/
theorem physical_moebius_source_energy_succ (N : ℕ) :
    ‖source (fun d => ((μ d : ℤ) : ℝ)) (N + 1)‖ ^ 2 =
      ‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ ^ 2 +
        2 * Complex.re (inner ℂ
          (source (fun d => ((μ d : ℤ) : ℝ)) N)
          ((((μ (N + 1) : ℤ) : ℝ) : ℂ) • bdGen (1 / ((N + 1 : ℕ) : ℝ)))) +
        ‖(((μ (N + 1) : ℤ) : ℝ) : ℂ) • bdGen (1 / ((N + 1 : ℕ) : ℝ))‖ ^ 2 := by
  have hsource : source (fun d => ((μ d : ℤ) : ℝ)) (N + 1) =
      source (fun d => ((μ d : ℤ) : ℝ)) N +
        ((((μ (N + 1) : ℤ) : ℝ) : ℂ) • bdGen (1 / ((N + 1 : ℕ) : ℝ))) := by
    unfold source
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hsource]
  simpa using
    (norm_add_sq (𝕜 := ℂ) (source (fun d => ((μ d : ℤ) : ℝ)) N)
      ((((μ (N + 1) : ℤ) : ℝ) : ℂ) • bdGen (1 / ((N + 1 : ℕ) : ℝ))))

/-- The chronological cross-time covariance is the literal signed finite Gram column at the
new modulus.  Thus a block estimate must retain this full Möbius column. -/
theorem physical_moebius_source_cross_eq_signed_gram_column (N : ℕ) :
    Complex.re (inner ℂ
      (source (fun d => ((μ d : ℤ) : ℝ)) N)
      ((((μ (N + 1) : ℤ) : ℝ) : ℂ) • bdGen (1 / ((N + 1 : ℕ) : ℝ)))) =
      ((μ (N + 1) : ℤ) : ℝ) *
        ∑ i ∈ range N, ((μ (i + 1) : ℤ) : ℝ) *
          bdGram (1 / ((i + 1 : ℕ) : ℝ)) (1 / ((N + 1 : ℕ) : ℝ)) := by
  unfold source
  rw [sum_inner, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left, inner_smul_right, inner_bdGen_eq_bdGram,
    Complex.conj_ofReal]
  push_cast
  simp
  ring

/-- A whole chronological cutoff block changes each physical cell by its literal signed residue
sum.  The identity keeps every insertion in the block and does not replace the fixed physical
carrier by an average. -/
theorem physical_moebius_cell_block (N L k : ℕ) :
    cell (fun d => ((μ d : ℤ) : ℝ)) (N + L) k =
      cell (fun d => ((μ d : ℤ) : ℝ)) N k +
        ∑ i ∈ range L, ((μ (N + i + 1) : ℤ) : ℝ) *
          (((k % (N + i + 1) : ℕ) : ℝ) / ((N + i + 1 : ℕ) : ℝ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    calc
      cell (fun d => ((μ d : ℤ) : ℝ)) (N + (L + 1)) k =
          cell (fun d => ((μ d : ℤ) : ℝ)) (N + L) k +
            ((μ (N + L + 1) : ℤ) : ℝ) *
              (((k % (N + L + 1) : ℕ) : ℝ) / ((N + L + 1 : ℕ) : ℝ)) := by
        rw [show N + (L + 1) = (N + L) + 1 by omega]
        simp only [cell, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ = _ := by
        rw [ih, Finset.sum_range_succ]
        abel

/-- The literal source over a cutoff block is the signed sum of all its inserted residue
vectors.  This is the multi-prime object whose covariance must be estimated. -/
theorem physical_moebius_source_block (N L : ℕ) :
    source (fun d => ((μ d : ℤ) : ℝ)) (N + L) =
      source (fun d => ((μ d : ℤ) : ℝ)) N +
        ∑ i ∈ range L, ((((μ (N + i + 1) : ℤ) : ℝ) : ℂ) •
          bdGen (1 / ((N + i + 1 : ℕ) : ℝ))) := by
  induction L with
  | zero => simp
  | succ L ih =>
    calc
      source (fun d => ((μ d : ℤ) : ℝ)) (N + (L + 1)) =
          source (fun d => ((μ d : ℤ) : ℝ)) (N + L) +
            ((((μ (N + L + 1) : ℤ) : ℝ) : ℂ) •
              bdGen (1 / ((N + L + 1 : ℕ) : ℝ))) := by
        rw [show N + (L + 1) = (N + L) + 1 by omega]
        unfold source
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
      _ = _ := by
        rw [ih, Finset.sum_range_succ]
        abel

/-- Exact energy evolution over a complete cutoff block.  The first added term retains every
old--new signed covariance; the final norm retains every new--new signed covariance. -/
theorem physical_moebius_source_energy_block (N L : ℕ) :
    ‖source (fun d => ((μ d : ℤ) : ℝ)) (N + L)‖ ^ 2 =
      ‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ ^ 2 +
        2 * Complex.re (inner ℂ
          (source (fun d => ((μ d : ℤ) : ℝ)) N)
          (∑ i ∈ range L, ((((μ (N + i + 1) : ℤ) : ℝ) : ℂ) •
            bdGen (1 / ((N + i + 1 : ℕ) : ℝ))))) +
        ‖∑ i ∈ range L, ((((μ (N + i + 1) : ℤ) : ℝ) : ℂ) •
          bdGen (1 / ((N + i + 1 : ℕ) : ℝ)))‖ ^ 2 := by
  rw [physical_moebius_source_block]
  simpa using (norm_add_sq (𝕜 := ℂ) _ _)

/-- The old--new term of the complete block energy is the finite signed Gram rectangle.
This is the exact multi-prime cancellation target; no one-prime majorant has been taken. -/
theorem physical_moebius_source_cross_block_eq_signed_gram (N L : ℕ) :
    Complex.re (inner ℂ
      (source (fun d => ((μ d : ℤ) : ℝ)) N)
      (∑ i ∈ range L, ((((μ (N + i + 1) : ℤ) : ℝ) : ℂ) •
        bdGen (1 / ((N + i + 1 : ℕ) : ℝ))))) =
      ∑ j ∈ range L, ((μ (N + j + 1) : ℤ) : ℝ) *
        ∑ i ∈ range N, ((μ (i + 1) : ℤ) : ℝ) *
          bdGram (1 / ((i + 1 : ℕ) : ℝ))
            (1 / ((N + j + 1 : ℕ) : ℝ)) := by
  unfold source
  rw [inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_inner, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left, inner_smul_right, inner_bdGen_eq_bdGram,
    Complex.conj_ofReal]
  push_cast
  simp
  ring

private theorem sum_initial_cell_weight (N : ℕ) :
    (∑ i ∈ range N, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    field_simp
    ring

private theorem initial_cell_energy_le_source_energy (N : ℕ) :
    (∑ i ∈ range N,
      cell (fun d => ((μ d : ℤ) : ℝ)) N (i + 1) ^ 2 /
        (((i : ℝ) + 1) * ((i : ℝ) + 2))) ≤
      ‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ ^ 2 := by
  apply ge_of_tendsto
    (hasSum_source_energy (fun d => ((μ d : ℤ) : ℝ)) N).tendsto_sum_nat
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun K hNK => hNK⟩] with K hNK
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK)
  intro i hi _
  positivity

/-- The literal physical source energy controls the reciprocal Möbius tail on its unmodified
initial cells.  Thus every EDQ covariance ceiling must suppress this tail at the physical scale. -/
theorem reciprocal_moebius_tail_sq_mul_le_physical_energy (N : ℕ) :
    (N : ℝ) * (∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)) ^ 2 ≤
      4 * ‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ ^ 2 + 4 := by
  let M : ℝ := ∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)
  let f : ℕ → ℝ := fun i =>
    cell (fun d => ((μ d : ℤ) : ℝ)) N (i + 1) ^ 2 /
      (((i : ℝ) + 1) * ((i : ℝ) + 2))
  have hfinite : (∑ i ∈ range N, f i) ≤
      ‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ ^ 2 := by
    exact initial_cell_energy_le_source_energy N
  have hterm (i : ℕ) (hi : i ∈ range N) :
      M ^ 2 * (((i : ℝ) + 1) / ((i : ℝ) + 2)) ≤
        2 * f i + 2 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
    have hiN : i < N := mem_range.mp hi
    have hcell := physical_moebius_cell_eq_reciprocal_tail
      (n := i + 1) (N := N) (by omega) (by omega)
    have hcell' : cell (fun d => ((μ d : ℤ) : ℝ)) N (i + 1) =
        ((i : ℝ) + 1) * M - 1 := by
      simpa only [M, Nat.cast_add, Nat.cast_one] using hcell
    have hsq : (((i : ℝ) + 1) * M) ^ 2 ≤
        2 * ((((i : ℝ) + 1) * M - 1) ^ 2) + 2 := by
      nlinarith [sq_nonneg (((i : ℝ) + 1) * M - 2)]
    have hden : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    dsimp [f]
    rw [hcell']
    calc
      M ^ 2 * (((i : ℝ) + 1) / ((i : ℝ) + 2)) =
        (((i : ℝ) + 1) * M) ^ 2 /
          (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
          field_simp
      _ ≤ (2 * ((((i : ℝ) + 1) * M - 1) ^ 2) + 2) /
          (((i : ℝ) + 1) * ((i : ℝ) + 2)) :=
        div_le_div_of_nonneg_right hsq hden.le
      _ = _ := by ring
  have hratio (i : ℕ) : (1 : ℝ) / 2 ≤ ((i : ℝ) + 1) / ((i : ℝ) + 2) := by
    have h : ((1 : ℝ) / 2) * ((i : ℝ) + 2) ≤ (i : ℝ) + 1 := by
      nlinarith [show (0 : ℝ) ≤ (i : ℝ) by positivity]
    exact (le_div_iff₀ (by positivity : 0 < (i : ℝ) + 2)).mpr h
  have hratio_sum : (N : ℝ) / 2 ≤
      ∑ i ∈ range N, ((i : ℝ) + 1) / ((i : ℝ) + 2) := by
    calc
      (N : ℝ) / 2 = ∑ _i ∈ range N, (1 : ℝ) / 2 := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hratio i)
  have htail : (∑ i ∈ range N,
      1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) : ℝ) ≤ 1 := by
    rw [sum_initial_cell_weight]
    linarith [show 0 ≤ 1 / ((N : ℝ) + 1) by positivity]
  have hsum : M ^ 2 * ∑ i ∈ range N, ((i : ℝ) + 1) / ((i : ℝ) + 2) ≤
      2 * (∑ i ∈ range N, f i) +
        2 * ∑ i ∈ range N, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
    calc
      _ ≤ ∑ i ∈ range N, (2 * f i + 2 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i hi => hterm i hi)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hleft : M ^ 2 * ((N : ℝ) / 2) ≤
      M ^ 2 * ∑ i ∈ range N, ((i : ℝ) + 1) / ((i : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hratio_sum (sq_nonneg M)
  change (N : ℝ) * M ^ 2 ≤ _
  calc
    (N : ℝ) * M ^ 2 = 2 * (M ^ 2 * ((N : ℝ) / 2)) := by ring
    _ ≤ 2 * (M ^ 2 * ∑ i ∈ range N, ((i : ℝ) + 1) / ((i : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hleft (by positivity)
    _ ≤ 2 * (2 * (∑ i ∈ range N, f i) +
        2 * ∑ i ∈ range N, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by nlinarith

/-- The EDQ predictable drift must control the reciprocal Möbius tail at the physical scale.
This is an exact necessary demand on the remaining signed covariance theorem. -/
theorem reciprocal_moebius_tail_sq_mul_le_predictable_drift (N : ℕ) :
    (N : ℝ) * (∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)) ^ 2 ≤
      8 * ‖DeletionResidueMartingale.predictableDrift N‖ ^ 2 + 20 := by
  have hphysical := reciprocal_moebius_tail_sq_mul_le_physical_energy N
  have hgap := DeletionResidueMartingale.source_drift_norm_gap N
  rw [sq_abs] at hgap
  have hsource : ‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ ^ 2 ≤
      2 * ‖DeletionResidueMartingale.predictableDrift N‖ ^ 2 + 4 := by
    nlinarith [sq_nonneg
      (‖source (fun d => ((μ d : ℤ) : ℝ)) N‖ -
        2 * ‖DeletionResidueMartingale.predictableDrift N‖)]
  nlinarith

end RHTower
