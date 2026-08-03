import GaloisForLFunctions.RHTower.MobiusThetaInternalJetPrimeNormalComplexGraph

/-!
# Adaptive prime-normal spectral codiagonal

The divisor-independent schedule `m(p,N) = 8pN` turns every exact strict residual column of the
Möbius–theta prime-normal source into a uniform quarter-contraction once
`1 / 2 ≤ N * re(centeredParameter w)`.  The resulting all-prime `ℓ¹` codiagonal is the isometric
Möbius prime head plus this contraction, hence is bounded below by `3 / 4`, injective, and has
closed range.  The basis-column theorem records that this operator uses the exact source column;
it is not an abstract triangular recoding.

This is a spectral coefficient-space conservativity theorem.  It does not identify that space
with the Gamma/co-Poisson Green completion and therefore does not by itself imply RH.
-/

open Complex MeasureTheory ArithmeticFunction Set Filter Topology
open scoped BigOperators ENNReal NNReal Topology Moebius

namespace RHTower

noncomputable section

theorem adaptivePrimeNormal_ratio_pow_le
    {p : ℕ} (hp : 0 < p) (j : ℕ) :
    ((p : ℝ) / (p + j + 1 : ℕ)) ^ (4 * p) ≤
      1 / ((j + 2 : ℕ) : ℝ) ^ 4 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hx : (0 : ℝ) ≤ (j + 1 : ℕ) / p := by positivity
  have hbern := one_add_mul_le_pow (a := ((j + 1 : ℕ) : ℝ) / p)
    (le_trans (by norm_num : (-2 : ℝ) ≤ 0) hx) p
  have hbase : ((j + 2 : ℕ) : ℝ) ≤
      (1 + ((j + 1 : ℕ) : ℝ) / p) ^ p := by
    calc
      ((j + 2 : ℕ) : ℝ) = 1 + ((j + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      _ = 1 + (p : ℝ) * (((j + 1 : ℕ) : ℝ) / p) := by
        rw [mul_div_cancel₀ _ hpR.ne']
      _ ≤ _ := hbern
  have hbasepos : (0 : ℝ) <
      (1 + ((j + 1 : ℕ) : ℝ) / p) ^ p := by positivity
  have hjpos : (0 : ℝ) < (j + 2 : ℕ) := by positivity
  have hinv :
      ((1 + ((j + 1 : ℕ) : ℝ) / p) ^ p)⁻¹ ≤
        (((j + 2 : ℕ) : ℝ))⁻¹ := by
    exact (inv_le_inv₀ hbasepos hjpos).mpr hbase
  have hratio :
      ((p : ℝ) / (p + j + 1 : ℕ)) ^ p =
        ((1 + ((j + 1 : ℕ) : ℝ) / p) ^ p)⁻¹ := by
    rw [← inv_pow]
    congr 1
    field_simp
    push_cast
    ring
  rw [show 4 * p = p * 4 by omega, pow_mul, hratio]
  simpa only [one_div, inv_pow] using pow_le_pow_left₀ (by positivity) hinv 4

theorem adaptivePrimeNormal_quartic_le_telescoping (j : ℕ) :
    1 / ((j + 2 : ℕ) : ℝ) ^ 4 ≤
      (1 / 4 : ℝ) *
        (1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ)) := by
  have hj1 : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hj2 : (0 : ℝ) < (j + 2 : ℕ) := by positivity
  have htel :
      1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ) =
        1 / (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
    field_simp
    push_cast
    ring
  rw [htel]
  have hmul :
      (1 / 4 : ℝ) *
          (1 / (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))) =
        1 / ((4 : ℝ) * ((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
    field_simp
  rw [hmul]
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith [sq_nonneg ((j : ℝ) + 1),
    mul_nonneg (by positivity : (0 : ℝ) ≤ j)
      (by positivity : (0 : ℝ) ≤ j)]

theorem hasSum_adaptivePrimeNormal_telescoping :
    HasSum (fun j : ℕ =>
      (1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ))) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    norm_num) 1).2
  have hpartial : (fun n : ℕ => ∑ j ∈ Finset.range n,
      (1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ))) =
      fun n : ℕ => 1 - 1 / ((n + 1 : ℕ) : ℝ) := by
    funext n
    convert (Finset.sum_range_sub'
      (fun j : ℕ => (((j + 1 : ℕ) : ℝ))⁻¹) n) using 1 <;>
      simp only [one_div, Nat.cast_add, Nat.cast_one] <;> ring
  rw [hpartial]
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htop
  simpa [one_div, Nat.cast_add, Nat.cast_one] using tendsto_const_nhds.sub hinv

theorem summable_adaptivePrimeNormal_quartic :
    Summable (fun j : ℕ => 1 / ((j + 2 : ℕ) : ℝ) ^ 4) := by
  simpa [one_div, Nat.cast_add, Nat.cast_ofNat] using
    (_root_.summable_nat_add_iff 2).2
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 4))

theorem tsum_adaptivePrimeNormal_quartic_le_quarter :
    (∑' j : ℕ, 1 / ((j + 2 : ℕ) : ℝ) ^ 4) ≤ 1 / 4 := by
  calc
    (∑' j : ℕ, 1 / ((j + 2 : ℕ) : ℝ) ^ 4) ≤
        ∑' j : ℕ, (1 / 4 : ℝ) *
          (1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ)) :=
      Summable.tsum_le_tsum adaptivePrimeNormal_quartic_le_telescoping
        summable_adaptivePrimeNormal_quartic
        (hasSum_adaptivePrimeNormal_telescoping.mul_left (1 / 4 : ℝ)).summable
    _ = 1 / 4 :=
      by simpa using
        (hasSum_adaptivePrimeNormal_telescoping.mul_left (1 / 4 : ℝ)).tsum_eq

/-- Global divisor-independent exponent schedule. -/
def adaptivePrimeNormalExponent (p N : ℕ) : ℕ := 8 * p * N

theorem adaptivePrimeNormal_exponent_ge
    {p N : ℕ} {sigma : ℝ}
    (hNsigma : (1 / 2 : ℝ) ≤ (N : ℝ) * sigma) :
    (4 * p : ℕ) ≤ (adaptivePrimeNormalExponent p N : ℝ) * sigma := by
  rw [adaptivePrimeNormalExponent]
  push_cast
  nlinarith [show (0 : ℝ) ≤ p by positivity]

theorem norm_adaptivePrimeNormal_tail_le_quartic
    {p : ℕ} (hp : 0 < p) {N : ℕ} {w : ℂ}
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) (j : ℕ) :
    ‖mobiusThetaPrimeNormalSpectralTailCoefficient p
        (adaptivePrimeNormalExponent p N) w j‖ ≤
      1 / ((j + 2 : ℕ) : ℝ) ^ 4 := by
  rw [norm_mobiusThetaPrimeNormalSpectralTailCoefficient hp]
  have hmu : |(μ (p + j + 1) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p + j + 1)
  have hratioPos : 0 < (p : ℝ) / (p + j + 1 : ℕ) := by positivity
  have hratioLe : (p : ℝ) / (p + j + 1 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (by omega : p ≤ p + j + 1)
  calc
    |(μ (p + j + 1) : ℝ)| *
          ((p : ℝ) / (p + j + 1 : ℕ)) ^
            ((adaptivePrimeNormalExponent p N : ℝ) *
              (mobiusThetaCenteredParameter w).re) ≤
        ((p : ℝ) / (p + j + 1 : ℕ)) ^
            ((adaptivePrimeNormalExponent p N : ℝ) *
              (mobiusThetaCenteredParameter w).re) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu
        (Real.rpow_nonneg hratioPos.le _)
    _ ≤ ((p : ℝ) / (p + j + 1 : ℕ)) ^ ((4 * p : ℕ) : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_ge hratioPos hratioLe
        (by exact_mod_cast adaptivePrimeNormal_exponent_ge hNw)
    _ = ((p : ℝ) / (p + j + 1 : ℕ)) ^ (4 * p) := by
      rw [Real.rpow_natCast]
    _ ≤ 1 / ((j + 2 : ℕ) : ℝ) ^ 4 :=
      adaptivePrimeNormal_ratio_pow_le hp j

theorem summable_norm_adaptivePrimeNormal_tail
    {p : ℕ} (hp : 0 < p) {N : ℕ} {w : ℂ}
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    Summable (fun j : ℕ =>
      ‖mobiusThetaPrimeNormalSpectralTailCoefficient p
        (adaptivePrimeNormalExponent p N) w j‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_adaptivePrimeNormal_tail_le_quartic hp hNw)
    summable_adaptivePrimeNormal_quartic

theorem tsum_norm_adaptivePrimeNormal_tail_le_quarter
    {p : ℕ} (hp : 0 < p) {N : ℕ} {w : ℂ}
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    (∑' j : ℕ,
      ‖mobiusThetaPrimeNormalSpectralTailCoefficient p
        (adaptivePrimeNormalExponent p N) w j‖) ≤ 1 / 4 := by
  exact le_trans
    (Summable.tsum_le_tsum
      (norm_adaptivePrimeNormal_tail_le_quartic hp hNw)
      (summable_norm_adaptivePrimeNormal_tail hp hNw)
      summable_adaptivePrimeNormal_quartic)
    tsum_adaptivePrimeNormal_quartic_le_quarter

/-! Generic `l1` column synthesis infrastructure. -/

section LpOneSynthesis

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

private theorem lpOne_hasSum_norm (x : lp (fun _ : ι => ℂ) 1) :
    HasSum (fun i : ι => ‖x i‖) ‖x‖ := by
  simpa using lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) x

theorem summable_lpOne_smul_columns
    (v : ι → F) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C)
    (x : lp (fun _ : ι => ℂ) 1) :
    Summable (fun i => x i • v i) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg (x _ • v _))
    (fun i => by
      rw [norm_smul]
      calc
        ‖x i‖ * ‖v i‖ ≤ ‖x i‖ * C :=
          mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
        _ = C * ‖x i‖ := mul_comm _ _)
    ((lpOne_hasSum_norm x).summable.mul_left C)

omit [CompleteSpace F] in
theorem summable_norm_lpOne_smul_columns
    (v : ι → F) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C)
    (x : lp (fun _ : ι => ℂ) 1) :
    Summable (fun i => ‖x i • v i‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => by
      rw [norm_smul]
      calc
        ‖x i‖ * ‖v i‖ ≤ ‖x i‖ * C :=
          mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
        _ = C * ‖x i‖ := mul_comm _ _)
    ((lpOne_hasSum_norm x).summable.mul_left C)

def lpOneColumnSynthesis
    (v : ι → F) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    lp (fun _ : ι => ℂ) 1 →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, x i • v i
      map_add' := by
        intro x y
        rw [← (summable_lpOne_smul_columns v C hv x).tsum_add
          (summable_lpOne_smul_columns v C hv y)]
        apply tsum_congr
        intro i
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
      map_smul' := by
        intro c x
        calc
          (∑' i, (c • x) i • v i) = ∑' i, c • (x i • v i) := by
            apply tsum_congr
            intro i
            simp only [lp.coeFn_smul, Pi.smul_apply, smul_smul, smul_eq_mul]
          _ = c • ∑' i, x i • v i :=
            (summable_lpOne_smul_columns v C hv x).tsum_const_smul c }
    C (fun x => by
      calc
        ‖∑' i, x i • v i‖ ≤ ∑' i, ‖x i • v i‖ :=
          norm_tsum_le_tsum_norm
            (summable_norm_lpOne_smul_columns v C hv x)
        _ ≤ ∑' i, C * ‖x i‖ :=
          Summable.tsum_le_tsum (fun i => by
            rw [norm_smul]
            calc
              ‖x i‖ * ‖v i‖ ≤ ‖x i‖ * C :=
                mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
              _ = C * ‖x i‖ := mul_comm _ _)
            (summable_norm_lpOne_smul_columns v C hv x)
            ((lpOne_hasSum_norm x).summable.mul_left C)
        _ = C * ‖x‖ := (lpOne_hasSum_norm x).mul_left C |>.tsum_eq)

theorem norm_lpOneColumnSynthesis_le
    (v : ι → F) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C)
    (x : lp (fun _ : ι => ℂ) 1) :
    ‖lpOneColumnSynthesis v C hv x‖ ≤ C * ‖x‖ := by
  change ‖∑' i, x i • v i‖ ≤ C * ‖x‖
  calc
    ‖∑' i, x i • v i‖ ≤ ∑' i, ‖x i • v i‖ :=
      norm_tsum_le_tsum_norm
        (summable_norm_lpOne_smul_columns v C hv x)
    _ ≤ ∑' i, C * ‖x i‖ :=
      Summable.tsum_le_tsum (fun i => by
        rw [norm_smul]
        calc
          ‖x i‖ * ‖v i‖ ≤ ‖x i‖ * C :=
            mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
          _ = C * ‖x i‖ := mul_comm _ _)
        (summable_norm_lpOne_smul_columns v C hv x)
        ((lpOne_hasSum_norm x).summable.mul_left C)
    _ = C * ‖x‖ := (lpOne_hasSum_norm x).mul_left C |>.tsum_eq

theorem lpOneColumnSynthesis_single
    [DecidableEq ι]
    (v : ι → F) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C)
    (i : ι) (c : ℂ) :
    lpOneColumnSynthesis v C hv
        (lp.single (E := fun _ : ι => ℂ) 1 i c) = c • v i := by
  change (∑' j : ι,
    (lp.single (E := fun _ : ι => ℂ) 1 i c) j • v j) = c • v i
  rw [tsum_eq_single i]
  · simp
  · intro j hji
    simp [lp.single_apply, hji]

end LpOneSynthesis

/-! Source-specific prime and arithmetic `l1` spaces. -/

abbrev AdaptivePrimeL1 := lp (fun _ : Nat.Primes => ℂ) 1
abbrev AdaptiveArithmeticL1 := lp (fun _ : ℕ => ℂ) 1

def adaptivePrimeNormalDiagonalFunction
    (x : AdaptivePrimeL1) (n : ℕ) : ℂ :=
  if hn : n.Prime then -x ⟨n, hn⟩ else 0

theorem summable_norm_adaptivePrimeNormalDiagonalFunction
    (x : AdaptivePrimeL1) :
    Summable (fun n : ℕ => ‖adaptivePrimeNormalDiagonalFunction x n‖) := by
  let s : Set ℕ := {n | n.Prime}
  let g : ℕ → ℝ := fun n => if hn : n.Prime then ‖x ⟨n, hn⟩‖ else 0
  have hx : Summable (fun p : Nat.Primes => ‖x p‖) :=
    (lpOne_hasSum_norm x).summable
  have hcomp : Summable (g ∘ Subtype.val : Nat.Primes → ℝ) := by
    have hfun : (g ∘ Subtype.val : Nat.Primes → ℝ) =
        fun p => ‖x p‖ := by
      funext p
      simp [g, p.2]
    rw [hfun]
    exact hx
  have hind : Summable (s.indicator g) :=
    (summable_subtype_iff_indicator.mp hcomp)
  have hfun : s.indicator g =
      fun n => ‖adaptivePrimeNormalDiagonalFunction x n‖ := by
    funext n
    by_cases hn : n.Prime <;>
      simp [s, g, adaptivePrimeNormalDiagonalFunction, Set.indicator, hn]
  rw [hfun] at hind
  exact hind

def adaptivePrimeNormalDiagonalEmbedding :
    AdaptivePrimeL1 →ₗᵢ[ℂ] AdaptiveArithmeticL1 where
  toFun x := ⟨adaptivePrimeNormalDiagonalFunction x,
    memℓp_gen (by
      simpa using summable_norm_adaptivePrimeNormalDiagonalFunction x)⟩
  map_add' x y := by
    ext n
    simp only [adaptivePrimeNormalDiagonalFunction, lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' c x := by
    ext n
    simp only [adaptivePrimeNormalDiagonalFunction, lp.coeFn_smul, Pi.smul_apply]
    split_ifs <;> simp [smul_eq_mul]
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
    let s : Set ℕ := {n | n.Prime}
    have htsum := tsum_subtype s
      (fun n => ‖adaptivePrimeNormalDiagonalFunction x n‖)
    calc
      (∑' n : ℕ, ‖adaptivePrimeNormalDiagonalFunction x n‖) =
          ∑' n : ℕ,
            s.indicator (fun k => ‖adaptivePrimeNormalDiagonalFunction x k‖) n := by
        apply tsum_congr
        intro n
        by_cases hn : n.Prime <;>
          simp [s, adaptivePrimeNormalDiagonalFunction, Set.indicator, hn]
      _ = ∑' p : s, ‖adaptivePrimeNormalDiagonalFunction x p.1‖ := htsum.symm
      _ = ∑' p : Nat.Primes, ‖x p‖ := by
        apply tsum_congr
        intro p
        have hp : p.1.Prime := p.2
        simp [adaptivePrimeNormalDiagonalFunction, hp]

def adaptivePrimeNormalTailColumn
    (p : Nat.Primes) (N : ℕ) (w : ℂ) : AdaptiveArithmeticL1 :=
  ∑' j : ℕ,
    (lp.single (E := fun _ : ℕ => ℂ) 1 (p.1 + j + 1)
        (mobiusThetaPrimeNormalSpectralTailCoefficient p.1
          (adaptivePrimeNormalExponent p.1 N) w j) : AdaptiveArithmeticL1)

theorem summable_adaptivePrimeNormalTailColumn_terms
    (p : Nat.Primes) {N : ℕ} {w : ℂ}
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    Summable (fun j : ℕ =>
      (lp.single (E := fun _ : ℕ => ℂ) 1 (p.1 + j + 1)
        (mobiusThetaPrimeNormalSpectralTailCoefficient p.1
          (adaptivePrimeNormalExponent p.1 N) w j) :
        AdaptiveArithmeticL1)) := by
  apply Summable.of_norm
  simpa [lp.norm_single (by norm_num : (0 : ENNReal) < 1)] using
    summable_norm_adaptivePrimeNormal_tail p.2.pos hNw

theorem norm_adaptivePrimeNormalTailColumn_le_quarter
    (p : Nat.Primes) {N : ℕ} {w : ℂ}
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    ‖adaptivePrimeNormalTailColumn p N w‖ ≤ 1 / 4 := by
  calc
    ‖adaptivePrimeNormalTailColumn p N w‖ ≤
        ∑' j : ℕ,
          ‖(lp.single (E := fun _ : ℕ => ℂ) 1 (p.1 + j + 1)
            (mobiusThetaPrimeNormalSpectralTailCoefficient p.1
              (adaptivePrimeNormalExponent p.1 N) w j) :
            AdaptiveArithmeticL1)‖ := by
      apply norm_tsum_le_tsum_norm
      simpa [lp.norm_single (by norm_num : (0 : ENNReal) < 1)] using
        summable_norm_adaptivePrimeNormal_tail p.2.pos hNw
    _ = ∑' j : ℕ,
        ‖mobiusThetaPrimeNormalSpectralTailCoefficient p.1
          (adaptivePrimeNormalExponent p.1 N) w j‖ := by
      apply tsum_congr
      intro j
      rw [lp.norm_single (by norm_num : (0 : ENNReal) < 1)]
    _ ≤ 1 / 4 :=
      tsum_norm_adaptivePrimeNormal_tail_le_quarter p.2.pos hNw

def adaptivePrimeNormalTailOperator
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    AdaptivePrimeL1 →L[ℂ] AdaptiveArithmeticL1 :=
  lpOneColumnSynthesis
    (fun p => adaptivePrimeNormalTailColumn p N w)
    (1 / 4)
    (fun p => norm_adaptivePrimeNormalTailColumn_le_quarter p hNw)

theorem norm_adaptivePrimeNormalTailOperator_le_quarter
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re)
    (x : AdaptivePrimeL1) :
    ‖adaptivePrimeNormalTailOperator N w hNw x‖ ≤ (1 / 4 : ℝ) * ‖x‖ := by
  exact norm_lpOneColumnSynthesis_le _ _ _ x

theorem adaptivePrimeNormalTailOperator_single
    (p : Nat.Primes) (c : ℂ) (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    adaptivePrimeNormalTailOperator N w hNw
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p c) =
      c • adaptivePrimeNormalTailColumn p N w := by
  exact lpOneColumnSynthesis_single _ _ _ p c

def adaptivePrimeNormalCodiagonal
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    AdaptivePrimeL1 →L[ℂ] AdaptiveArithmeticL1 :=
  adaptivePrimeNormalDiagonalEmbedding.toContinuousLinearMap +
    adaptivePrimeNormalTailOperator N w hNw

theorem adaptivePrimeNormalCodiagonal_source_column
    (p : Nat.Primes) (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    adaptivePrimeNormalCodiagonal N w hNw
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) =
      adaptivePrimeNormalDiagonalEmbedding
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) +
        adaptivePrimeNormalTailColumn p N w := by
  rw [adaptivePrimeNormalCodiagonal, _root_.add_apply,
    adaptivePrimeNormalTailOperator_single, one_smul,
    LinearIsometry.coe_toContinuousLinearMap]

theorem adaptivePrimeNormalDiagonalFunction_source_head
    (p : Nat.Primes) :
    adaptivePrimeNormalDiagonalFunction
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) p.1 = -1 := by
  simp [adaptivePrimeNormalDiagonalFunction, p.2, lp.single_apply]

theorem adaptivePrimeNormalCodiagonal_lower_bound
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re)
    (x : AdaptivePrimeL1) :
    (3 / 4 : ℝ) * ‖x‖ ≤ ‖adaptivePrimeNormalCodiagonal N w hNw x‖ := by
  have hdecomp : adaptivePrimeNormalDiagonalEmbedding x =
      adaptivePrimeNormalCodiagonal N w hNw x -
        adaptivePrimeNormalTailOperator N w hNw x := by
    simp [adaptivePrimeNormalCodiagonal]
  have htri : ‖adaptivePrimeNormalDiagonalEmbedding x‖ ≤
      ‖adaptivePrimeNormalCodiagonal N w hNw x‖ +
        ‖adaptivePrimeNormalTailOperator N w hNw x‖ := by
    rw [hdecomp]
    exact norm_sub_le _ _
  have htail := norm_adaptivePrimeNormalTailOperator_le_quarter N w hNw x
  rw [adaptivePrimeNormalDiagonalEmbedding.norm_map] at htri
  linarith

theorem adaptivePrimeNormalCodiagonal_injective
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    Function.Injective (adaptivePrimeNormalCodiagonal N w hNw) := by
  intro x y hxy
  have hzero : adaptivePrimeNormalCodiagonal N w hNw (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hlower := adaptivePrimeNormalCodiagonal_lower_bound N w hNw (x - y)
  rw [hzero, norm_zero] at hlower
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem adaptivePrimeNormalCodiagonal_isClosed_range
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    IsClosed (Set.range (adaptivePrimeNormalCodiagonal N w hNw)) := by
  have hanti : AntilipschitzWith (4 / 3 : ℝ≥0)
      (adaptivePrimeNormalCodiagonal N w hNw) := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    have hlower :=
      adaptivePrimeNormalCodiagonal_lower_bound N w hNw (x - y)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    change ‖x - y‖ ≤ (4 / 3 : ℝ) *
      ‖adaptivePrimeNormalCodiagonal N w hNw (x - y)‖
    nlinarith [norm_nonneg (x - y),
      norm_nonneg (adaptivePrimeNormalCodiagonal N w hNw (x - y))]
  exact hanti.isClosed_range (adaptivePrimeNormalCodiagonal N w hNw).uniformContinuous

end
end RHTower
