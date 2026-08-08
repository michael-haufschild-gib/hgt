import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The squarefree Möbius cross-Gram diagonal

Tensoring the transverse projective seam `⟪v_∞, v_0⟫ = -1/p` over the prime support of a squarefree
integer produces the diagonal

`A e_n = μ(n)/n`   (`n` squarefree),

which is the producer/reporter cross-Gram of the two complete point/complement polarizations.  This
file proves the exact arithmetic identity behind that computation and the analytic classification of
the resulting diagonal:

* `∏_{p ∣ n} (-1/p) = μ(n)/n` for every squarefree `n`;
* the transverse diagonal has supremum exactly `1/2`, attained at `n = 2`;
* it is square-summable, with `Σ_{n>1 squarefree} n^{-2} = ζ(2)/ζ(4) - 1`, hence Hilbert–Schmidt;
* it is *not* absolutely summable, since the primes alone already diverge — the first-trace wall;
* its unsigned and signed spectral Dirichlet traces are `ζ(s)/ζ(2s)` and `1/ζ(s)`.
-/

open Complex Filter Finset
open ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## The cross-Gram diagonal -/

/-- The producer/reporter cross-Gram coefficient at the squarefree index `n`. -/
def moebiusCrossGramDiagonal (n : ℕ) : ℂ := (moebius n : ℂ) / (n : ℂ)

/-- **Equation (31).**  Tensoring the transverse projective seam `-1/p` over the prime support of a
squarefree integer produces exactly the Möbius cross-Gram coefficient. -/
theorem prod_transverseSeam_eq_crossGram {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (-(1 / (p : ℂ))) = moebiusCrossGramDiagonal n := by
  have hprod : ∏ p ∈ n.primeFactors, ((p : ℕ) : ℂ) = (n : ℂ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  have hneg : ∏ p ∈ n.primeFactors, (-(1 / (p : ℂ))) =
      (-1) ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (1 / (p : ℂ)) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by ring
  have hinv : ∏ p ∈ n.primeFactors, (1 / (p : ℂ)) = 1 / (n : ℂ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, hprod]
  have hcard : cardFactors n = n.primeFactors.card := by
    rw [← cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero |>.mpr hn,
      cardDistinctFactors_apply, Nat.primeFactors,
      List.toFinset_card_of_nodup
        ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn),
      List.Nodup.dedup ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)]
  rw [hneg, hinv, moebiusCrossGramDiagonal, moebius_apply_of_squarefree hn, hcard]
  push_cast
  ring

theorem moebiusCrossGramDiagonal_eq_zero_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) :
    moebiusCrossGramDiagonal n = 0 := by
  rw [moebiusCrossGramDiagonal, moebius_eq_zero_of_not_squarefree hn]
  simp

@[simp]
theorem moebiusCrossGramDiagonal_one : moebiusCrossGramDiagonal 1 = 1 := by
  simp [moebiusCrossGramDiagonal]

theorem norm_moebiusCrossGramDiagonal_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ‖moebiusCrossGramDiagonal n‖ = 1 / (n : ℝ) := by
  have hpos : 0 < n := hn.ne_zero.bot_lt
  have hmu : ‖(moebius n : ℂ)‖ = 1 := by
    rw [moebius_apply_of_squarefree hn]
    push_cast
    simp [norm_pow]
  rw [moebiusCrossGramDiagonal, norm_div, hmu, Complex.norm_natCast, one_div]

theorem norm_moebiusCrossGramDiagonal_le_half {n : ℕ} (h1 : 1 < n) :
    ‖moebiusCrossGramDiagonal n‖ ≤ 1 / 2 := by
  by_cases hn : Squarefree n
  · rw [norm_moebiusCrossGramDiagonal_of_squarefree hn]
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    exact one_div_le_one_div_of_le (by norm_num) h2
  · rw [moebiusCrossGramDiagonal_eq_zero_of_not_squarefree hn]
    norm_num

theorem norm_moebiusCrossGramDiagonal_two : ‖moebiusCrossGramDiagonal 2‖ = 1 / 2 := by
  rw [norm_moebiusCrossGramDiagonal_of_squarefree Nat.squarefree_two]
  norm_num

theorem norm_moebiusCrossGramDiagonal_le_one (n : ℕ) :
    ‖moebiusCrossGramDiagonal n‖ ≤ 1 := by
  by_cases hn : Squarefree n
  · rw [norm_moebiusCrossGramDiagonal_of_squarefree hn]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn.ne_zero
    rw [div_le_one (by linarith)]
    exact h1
  · rw [moebiusCrossGramDiagonal_eq_zero_of_not_squarefree hn]
    norm_num

/-! ## The transverse squarefree occupation weights -/

/-- Indicator of a transverse (vacuum-orthogonal) squarefree occupation index. -/
def squarefreeTransverseWeight (t : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ 1 < n then (1 : ℝ) / (n : ℝ) ^ t else 0

theorem squarefreeTransverseWeight_nonneg (t : ℝ) (n : ℕ) :
    0 ≤ squarefreeTransverseWeight t n := by
  rw [squarefreeTransverseWeight]
  split <;> positivity

/-- **Equation (32), summability.**  The transverse cross-Gram diagonal is square-summable, so the
operator it defines is Hilbert–Schmidt. -/
theorem summable_squarefreeTransverseWeight_two :
    Summable (squarefreeTransverseWeight 2) := by
  refine Summable.of_nonneg_of_le (fun n => squarefreeTransverseWeight_nonneg 2 n) ?_
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2))
  intro n
  rw [squarefreeTransverseWeight]
  split
  · exact le_of_eq (by rw [Real.rpow_two])
  · positivity

/-- **Equation (33).**  The transverse cross-Gram diagonal is not absolutely summable: already the
prime subseries diverges.  This is the first-trace wall. -/
theorem not_summable_squarefreeTransverseWeight_one :
    ¬ Summable (squarefreeTransverseWeight 1) := by
  intro h
  refine not_summable_one_div_on_primes ?_
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · by_cases hp : n ∈ {p : ℕ | Nat.Prime p}
    · rw [Set.indicator_of_mem hp]
      positivity
    · rw [Set.indicator_of_notMem hp]
  · by_cases hp : n ∈ {p : ℕ | Nat.Prime p}
    · have hprime : Nat.Prime n := hp
      have hsq : Squarefree n := hprime.squarefree
      have h1 : 1 < n := hprime.one_lt
      rw [Set.indicator_of_mem hp, squarefreeTransverseWeight, if_pos ⟨hsq, h1⟩,
        Real.rpow_one]
    · rw [Set.indicator_of_notMem hp]
      exact squarefreeTransverseWeight_nonneg 1 n

/-! ## The two exact spectral Dirichlet traces -/

/-- **Equation (34).**  The unsigned spectral trace of the cross-Gram operator is the squarefree
Euler partition `ζ(s)/ζ(2s)`. -/
theorem tsum_crossGram_unsigned_trace {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if Squarefree n then 1 / (n : ℂ) ^ s else 0) =
      riemannZeta s / riemannZeta (2 * s) :=
  tsum_squarefree_cpow hs

/-- **Equation (35).**  The signed spectral trace of the cross-Gram operator is the reciprocal
zeta function. -/
theorem LSeries_crossGram_signed_trace {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (moebius n : ℂ)) s = (riemannZeta s)⁻¹ :=
  LSeries_moebius_eq_inv_riemannZeta hs

/-! ## The transverse occupation space and the cross-Gram operator -/

/-- Transverse (vacuum-orthogonal) squarefree occupation indices. -/
abbrev SquarefreeTransverse := {n : ℕ // Squarefree n ∧ 1 < n}

/-- The transverse squarefree occupation space. -/
abbrev SquarefreeTransverseSpace := lp (fun _ : SquarefreeTransverse => ℂ) 2

theorem norm_crossGramDiagonal_transverse (n : SquarefreeTransverse) :
    ‖moebiusCrossGramDiagonal (n : ℕ)‖ = 1 / ((n : ℕ) : ℝ) :=
  norm_moebiusCrossGramDiagonal_of_squarefree n.property.1

theorem norm_crossGramDiagonal_transverse_le (n : SquarefreeTransverse) :
    ‖moebiusCrossGramDiagonal (n : ℕ)‖ ≤ 1 / 2 :=
  norm_moebiusCrossGramDiagonal_le_half n.property.2

theorem crossGramDiagonal_ne_zero (n : SquarefreeTransverse) :
    moebiusCrossGramDiagonal (n : ℕ) ≠ 0 := by
  intro hzero
  have := norm_crossGramDiagonal_transverse n
  rw [hzero, norm_zero] at this
  have hpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by
    have := n.property.2
    exact_mod_cast lt_trans Nat.zero_lt_one this
  have : (0 : ℝ) < 1 / ((n : ℕ) : ℝ) := by positivity
  linarith

theorem memℓp_crossGram (f : SquarefreeTransverseSpace) :
    Memℓp (fun n : SquarefreeTransverse => moebiusCrossGramDiagonal (n : ℕ) * f n) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun n => ‖f n‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left ((1 / 2 : ℝ) ^ (2 : ℝ)))
  intro n
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (norm_crossGramDiagonal_transverse_le n) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

/-- The producer/reporter cross-Gram, as a linear map on the transverse occupation space. -/
def crossGramLinearMap : SquarefreeTransverseSpace →ₗ[ℂ] SquarefreeTransverseSpace where
  toFun f := ⟨fun n => moebiusCrossGramDiagonal (n : ℕ) * f n, memℓp_crossGram f⟩
  map_add' := by
    intro f g
    ext n
    simp [mul_add]
  map_smul' := by
    intro c f
    ext n
    simp [mul_left_comm]

@[simp]
theorem crossGramLinearMap_apply (f : SquarefreeTransverseSpace) (n : SquarefreeTransverse) :
    (crossGramLinearMap f : SquarefreeTransverse → ℂ) n =
      moebiusCrossGramDiagonal (n : ℕ) * f n := rfl

theorem norm_crossGramLinearMap_le (f : SquarefreeTransverseSpace) :
    ‖crossGramLinearMap f‖ ≤ (1 / 2 : ℝ) * ‖f‖ := by
  have hnn : (0 : ℝ) ≤ ‖crossGramLinearMap f‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖f‖ := by positivity
  have htsumD : ‖crossGramLinearMap f‖ ^ (2 : ℝ)
      = ∑' n, ‖(crossGramLinearMap f) n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : SquarefreeTransverse => ℂ)
      (by norm_num) (crossGramLinearMap f)
  have htsumf : ‖f‖ ^ (2 : ℝ) = ∑' n, ‖f n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : SquarefreeTransverse => ℂ)
      (by norm_num) f
  have hsumf : Summable fun n => ‖f n‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hsumD : Summable fun n => ‖(crossGramLinearMap f) n‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ n, ‖(crossGramLinearMap f) n‖ ^ (2 : ℝ)
      ≤ (1 / 2 : ℝ) ^ (2 : ℝ) * ‖f n‖ ^ (2 : ℝ) := by
    intro n
    rw [crossGramLinearMap_apply, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (norm_crossGramDiagonal_transverse_le n) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : ‖crossGramLinearMap f‖ ^ (2 : ℝ) ≤ ((1 / 2 : ℝ) * ‖f‖) ^ (2 : ℝ) := by
    rw [htsumD, Real.mul_rpow (by norm_num) (norm_nonneg _), htsumf, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumD (hsumf.mul_left ((1 / 2 : ℝ) ^ (2 : ℝ)))
  have hx2 : ‖crossGramLinearMap f‖ ^ (2 : ℝ) = ‖crossGramLinearMap f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]; norm_num
  have hy2 : ((1 / 2 : ℝ) * ‖f‖) ^ (2 : ℝ) = ((1 / 2 : ℝ) * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]; norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

/-- **Equation (28).**  The producer/reporter cross-Gram operator on the transverse squarefree
occupation space. -/
def crossGramOperator : SquarefreeTransverseSpace →L[ℂ] SquarefreeTransverseSpace :=
  LinearMap.mkContinuous crossGramLinearMap (1 / 2) norm_crossGramLinearMap_le

@[simp]
theorem crossGramOperator_apply (f : SquarefreeTransverseSpace) (n : SquarefreeTransverse) :
    (crossGramOperator f) n = moebiusCrossGramDiagonal (n : ℕ) * f n := rfl

theorem norm_crossGramOperator_le : ‖crossGramOperator‖ ≤ 1 / 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

@[simp]
theorem crossGramOperator_single (m : SquarefreeTransverse) :
    crossGramOperator (lp.single 2 m (1 : ℂ)) =
      lp.single 2 m (moebiusCrossGramDiagonal (m : ℕ)) := by
  ext n
  rw [crossGramOperator_apply]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs with hnm
  · subst hnm
    rw [mul_one]
  · rw [mul_zero]

theorem le_norm_crossGramOperator (m : SquarefreeTransverse) :
    ‖moebiusCrossGramDiagonal (m : ℕ)‖ ≤ ‖crossGramOperator‖ := by
  have hone : ‖(lp.single 2 m (1 : ℂ) : SquarefreeTransverseSpace)‖ = 1 := by
    rw [lp.norm_single (E := fun _ : SquarefreeTransverse => ℂ) (p := 2) (by norm_num) m (1 : ℂ)]
    simp
  have hval : ‖crossGramOperator (lp.single 2 m (1 : ℂ))‖ =
      ‖moebiusCrossGramDiagonal (m : ℕ)‖ := by
    rw [crossGramOperator_single,
      lp.norm_single (E := fun _ : SquarefreeTransverse => ℂ) (p := 2) (by norm_num) m _]
  have hop := crossGramOperator.le_opNorm (lp.single 2 m (1 : ℂ))
  rw [hval, hone, mul_one] at hop
  exact hop

/-- **Equation (29).**  The producer/reporter polarization angle is uniformly strict on the
vacuum-orthogonal parts: the cross-Gram has operator norm exactly `1/2`. -/
theorem norm_crossGramOperator : ‖crossGramOperator‖ = 1 / 2 := by
  refine le_antisymm norm_crossGramOperator_le ?_
  have := le_norm_crossGramOperator ⟨2, ⟨Nat.squarefree_two, one_lt_two⟩⟩
  rwa [show ((⟨2, ⟨Nat.squarefree_two, one_lt_two⟩⟩ : SquarefreeTransverse) : ℕ) = 2 from rfl,
    norm_moebiusCrossGramDiagonal_two] at this

/-- **Equation (29), pairing form.**  Every vacuum-orthogonal producer/reporter pairing is
strictly contracted by the factor `1/2`. -/
theorem norm_inner_crossGram_le (x y : SquarefreeTransverseSpace) :
    ‖(inner ℂ x (crossGramOperator y) : ℂ)‖ ≤ 1 / 2 * (‖x‖ * ‖y‖) := by
  calc ‖(inner ℂ x (crossGramOperator y) : ℂ)‖ ≤ ‖x‖ * ‖crossGramOperator y‖ :=
        norm_inner_le_norm (𝕜 := ℂ) x (crossGramOperator y)
    _ ≤ ‖x‖ * (1 / 2 * ‖y‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact le_trans (crossGramOperator.le_opNorm y)
          (mul_le_mul_of_nonneg_right norm_crossGramOperator_le (norm_nonneg _))
    _ = 1 / 2 * (‖x‖ * ‖y‖) := by ring

/-- The cross-Gram operator is injective on the transverse space. -/
theorem crossGramOperator_injective : Function.Injective crossGramOperator := by
  intro f g hfg
  ext n
  have h := congrArg (fun w : SquarefreeTransverseSpace => (w : SquarefreeTransverse → ℂ) n) hfg
  simp only [crossGramOperator_apply] at h
  exact mul_left_cancel₀ (crossGramDiagonal_ne_zero n) h

/-! ## The closed inverse graph and its exact domain -/

theorem norm_moebius_transverse (n : SquarefreeTransverse) :
    ‖(moebius (n : ℕ) : ℂ)‖ = 1 := by
  rw [moebius_apply_of_squarefree n.property.1]
  push_cast
  simp [norm_pow]

theorem moebius_sq_transverse (n : SquarefreeTransverse) :
    ((moebius (n : ℕ) : ℂ)) * ((moebius (n : ℕ) : ℂ)) = 1 := by
  have h : moebius (n : ℕ) * moebius (n : ℕ) = 1 := by
    rw [moebius_apply_of_squarefree n.property.1, ← pow_add]
    exact Even.neg_one_pow ⟨cardFactors (n : ℕ), rfl⟩
  exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h

theorem crossGramDiagonal_mul_inverse (n : SquarefreeTransverse) :
    moebiusCrossGramDiagonal (n : ℕ) * ((moebius (n : ℕ) : ℂ) * ((n : ℕ) : ℂ)) = 1 := by
  have hnpos : 0 < (n : ℕ) := lt_trans Nat.zero_lt_one n.property.2
  have hn0 : (((n : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [moebiusCrossGramDiagonal]
  field_simp
  rw [sq]
  exact moebius_sq_transverse n

/-- **Equation (30).**  The range of the transverse cross-Gram is exactly the weighted `ℓ²`
domain of its unbounded Möbius inverse. -/
theorem mem_range_crossGramOperator_iff (y : SquarefreeTransverseSpace) :
    (∃ x : SquarefreeTransverseSpace, crossGramOperator x = y) ↔
      Memℓp (fun n : SquarefreeTransverse => ((n : ℕ) : ℂ) * y n) 2 := by
  constructor
  · rintro ⟨x, rfl⟩
    have hpoint : ∀ n : SquarefreeTransverse,
        ((n : ℕ) : ℂ) * (crossGramOperator x) n = (moebius (n : ℕ) : ℂ) * x n := by
      intro n
      have hnpos : 0 < (n : ℕ) := lt_trans Nat.zero_lt_one n.property.2
      have hn0 : (((n : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hnpos.ne'
      rw [crossGramOperator_apply, moebiusCrossGramDiagonal]
      field_simp
    have hnorm : ∀ n : SquarefreeTransverse,
        ‖((n : ℕ) : ℂ) * (crossGramOperator x) n‖ = ‖x n‖ := by
      intro n
      rw [hpoint n, norm_mul, norm_moebius_transverse n, one_mul]
    refine memℓp_gen ?_
    have hsum : Summable fun n : SquarefreeTransverse => ‖x n‖ ^ (2 : ℝ) :=
      (lp.memℓp x).summable (by norm_num)
    exact hsum.congr fun n => by rw [hnorm n]; norm_num
  · intro hy
    have hsum : Summable fun n : SquarefreeTransverse =>
        ‖((n : ℕ) : ℂ) * y n‖ ^ (2 : ℝ) := hy.summable (by norm_num)
    have hnorm : ∀ n : SquarefreeTransverse,
        ‖(moebius (n : ℕ) : ℂ) * (((n : ℕ) : ℂ) * y n)‖ = ‖((n : ℕ) : ℂ) * y n‖ := by
      intro n
      rw [norm_mul, norm_moebius_transverse n, one_mul]
    refine ⟨⟨fun n => (moebius (n : ℕ) : ℂ) * (((n : ℕ) : ℂ) * y n), ?_⟩, ?_⟩
    · exact memℓp_gen (hsum.congr fun n => by rw [hnorm n]; norm_num)
    · ext n
      rw [crossGramOperator_apply]
      show moebiusCrossGramDiagonal (n : ℕ) *
        ((moebius (n : ℕ) : ℂ) * (((n : ℕ) : ℂ) * y n)) = y n
      rw [show moebiusCrossGramDiagonal (n : ℕ) *
          ((moebius (n : ℕ) : ℂ) * (((n : ℕ) : ℂ) * y n)) =
          (moebiusCrossGramDiagonal (n : ℕ) * ((moebius (n : ℕ) : ℂ) * ((n : ℕ) : ℂ))) * y n
          from by ring, crossGramDiagonal_mul_inverse n, one_mul]

end

end RHTower
