import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheGoldenDatumHasNoFixedBudget
import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The relative square sees only the original counts

The first milestone of the amplification question: construct the two-factor **relative**
operation — the coefficientwise (Euler-factor-wise) product over the one base — and compute its
trace, support, pole and boundary, then test it on the golden datum.

**Over `ℤ`.** For sources `a, b` the relative product is `(a ⊗ b)(n) = a(n) b(n)` (`relProd`).

* **Gauge.** `χ_x a ⊗ χ_y b = χ_{x+y}(a ⊗ b)` (`relProd_twisted`): the relative product adds gauge
  points. The relative square of a source with its conjugate is gauge invariant and equals `|a|²`
  (`relProd_twisted_conj`); its trace is the coefficient energy (`sum_relProd_conj`). It is
  multiplicative information.
* **Support and boundary.** `supp(a ⊗ b) ⊆ supp a ∩ supp b` (`relProd_eq_zero_of_left`): the length
  does not grow and a finite presentation loses no cell. The external square of the flat critical
  source, truncated at horizon `N`, loses the pairs with `ab > N`; that escaped mass is at least
  `(r/2)²` whenever `4^r ≤ N` (`ofNat_div_four_sq_le_externalEscape`), so it is unbounded
  (`tendsto_externalEscape`). Relative operations have no boundary and no new content; external
  ones carry the near-incidences and pay an unbounded boundary.
* **Pole.** The relative square of the flat source is the flat source: `ζ ⊗ ζ = ζ`, one simple
  pole, while the external square is `ζ²`.

**Over `𝔽_q`.** The relative square of a curve datum has eigenvalues `β_iβ_j` and power sums
`(Σ β_i^j)²` (`relSquarePowerSum_eq`). These are nonnegative for **every** datum, pure or not
(`relSquarePowerSum_nonneg`), and the relative square has a fixed budget iff the datum has one
(`bounded_relSquare_iff`). The golden datum's relative square grows like `φ^{2j}`
(`goldenDatum_relSquare_ge`).

So the relative square's useful estimate is determined by the original counts: it is an external
product in disguise for the purposes of the loss law, and its positivity is that of a square. A
two-factor operation with new content must be a correspondence — a gauge-charged pair form whose
diagonal is fixed and whose near-incidences carry the information, as `C × C` does for Weil.
-/

open Finset Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry ArithmeticCastelnuovoSeveri

/-! ### The relative product over `ℤ` -/

/-- The relative (coefficientwise, Euler-factor-wise) product of two sources. -/
def relProd (a b : ℕ → ℂ) : ℕ → ℂ := fun n => a n * b n

/-- **The relative product adds gauge points.** -/
theorem relProd_twisted (x y : GaugeTorus) (a b : ℕ → ℂ) :
    relProd (twisted x a) (twisted y b) = twisted (x + y) (relProd a b) := by
  funext n
  simp only [relProd, twisted, twist_add]
  ring

/-- **The relative square with the conjugate is gauge invariant**, equal to `|a|²`. -/
theorem relProd_twisted_conj (x : GaugeTorus) (a : ℕ → ℂ) :
    relProd (twisted x a) (fun n => conj (twisted x a n)) = fun n => ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
  funext n
  simp only [relProd, twisted, map_mul]
  have h := twist_mul_conj_self x n
  calc twist x n * a n * (conj (twist x n) * conj (a n))
      = (twist x n * conj (twist x n)) * (a n * conj (a n)) := by ring
    _ = ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
        rw [h, one_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The trace of the relative square is the coefficient energy. -/
theorem sum_relProd_conj (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ n ∈ s, relProd a (fun n => conj (a n)) n = ∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [relProd, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The relative product keeps the support.** -/
theorem relProd_eq_zero_of_left {a : ℕ → ℂ} (b : ℕ → ℂ) {n : ℕ} (h : a n = 0) :
    relProd a b n = 0 := by
  rw [relProd, h, zero_mul]

/-- The relative square of the flat source is the flat source: `ζ ⊗ ζ = ζ`. -/
theorem relProd_one_one : relProd (fun _ => 1) (fun _ => 1) = fun _ => 1 := by
  funext n; simp [relProd]

/-! ### The boundary of the external square -/

/-- The escaped mass of the external square of the flat critical source at horizon `N`:
`Σ_{a, b ≤ N, ab > N} 1/(ab)`. -/
def externalEscape (N : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if N < a * b then 1 / ((a : ℝ) * b) else 0

/-- Every dyadic block has harmonic mass at least `1/2`. -/
theorem half_le_sum_dyadic_inv {K : ℕ} (hK : 1 ≤ K) :
    (1 / 2 : ℝ) ≤ ∑ j ∈ Ioc K (2 * K), 1 / (j : ℝ) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hterm : ∀ j ∈ Ioc K (2 * K), 1 / (2 * (K : ℝ)) ≤ 1 / (j : ℝ) := by
    intro j hj
    have hj := Finset.mem_Ioc.mp hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    exact one_div_le_one_div_of_le hjpos (by exact_mod_cast hj.2)
  calc (1 / 2 : ℝ) = ((Ioc K (2 * K)).card : ℝ) * (1 / (2 * (K : ℝ))) := by
        rw [Nat.card_Ioc, show 2 * K - K = K by omega]; field_simp
    _ = ∑ j ∈ Ioc K (2 * K), 1 / (2 * (K : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- `r` dyadic blocks above `K` carry harmonic mass at least `r/2`. -/
theorem half_mul_le_sum_inv {K : ℕ} (hK : 1 ≤ K) (r : ℕ) :
    (r / 2 : ℝ) ≤ ∑ j ∈ Ioc K (2 ^ r * K), 1 / (j : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hK' : 1 ≤ 2 ^ r * K := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hle : K ≤ 2 ^ r * K := Nat.le_mul_of_pos_left K (by positivity)
    have hsplit : Ioc K (2 ^ (r + 1) * K) = Ioc K (2 ^ r * K) ∪ Ioc (2 ^ r * K) (2 * (2 ^ r * K)) := by
      rw [show 2 ^ (r + 1) * K = 2 * (2 ^ r * K) by ring]
      exact (Finset.Ioc_union_Ioc_eq_Ioc hle (by omega)).symm
    have hdisj : Disjoint (Ioc K (2 ^ r * K)) (Ioc (2 ^ r * K) (2 * (2 ^ r * K))) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Ioc] at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have := half_le_sum_dyadic_inv hK'
    push_cast
    linarith

/-- **The external square loses an unbounded mass to the boundary.** If `4^r ≤ N`, the escaped mass
is at least `(r/2)²`: with `K = ⌊√N⌋`, every pair `a, b ∈ (K, 2^r K]` has `ab > N`, and these
`r` dyadic blocks carry harmonic mass at least `r/2`. -/
theorem ofNat_div_four_sq_le_externalEscape {N r : ℕ} (hN : 4 ^ r ≤ N) :
    ((r : ℝ) / 2) ^ 2 ≤ externalEscape N := by
  set K := Nat.sqrt N with hK
  have h44 : 2 ^ r * 2 ^ r = 4 ^ r := by rw [← mul_pow]; norm_num
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (by norm_num)) hN
  have hK1 : 1 ≤ K := Nat.le_sqrt.mpr (by simpa using hN1)
  have h2r : 2 ^ r ≤ K := Nat.le_sqrt.mpr (h44 ▸ hN)
  have hKN : 2 ^ r * K ≤ N := le_trans (Nat.mul_le_mul_right K h2r) (Nat.sqrt_le N)
  have hblock := half_mul_le_sum_inv hK1 r
  have hsub : Ioc K (2 ^ r * K) ⊆ Icc 1 N := by
    intro j hj
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hj ⊢
    exact ⟨by omega, hj.2.trans hKN⟩
  have hprod : (∑ a ∈ Ioc K (2 ^ r * K), 1 / (a : ℝ)) * (∑ b ∈ Ioc K (2 ^ r * K), 1 / (b : ℝ)) ≤
      externalEscape N := by
    rw [Finset.sum_mul_sum, externalEscape]
    calc ∑ a ∈ Ioc K (2 ^ r * K), ∑ b ∈ Ioc K (2 ^ r * K), 1 / (a : ℝ) * (1 / (b : ℝ))
        = ∑ a ∈ Ioc K (2 ^ r * K), ∑ b ∈ Ioc K (2 ^ r * K),
            (if N < a * b then 1 / ((a : ℝ) * b) else 0) := by
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
          have ha := (Finset.mem_Ioc.mp ha).1
          have hb := (Finset.mem_Ioc.mp hb).1
          have hab : N < a * b :=
            lt_of_lt_of_le (Nat.lt_succ_sqrt N) (Nat.mul_le_mul ha hb)
          rw [if_pos hab, one_div_mul_one_div]
      _ ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Ioc K (2 ^ r * K),
            (if N < a * b then 1 / ((a : ℝ) * b) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ =>
            Finset.sum_nonneg fun b _ => by split_ifs <;> positivity
      _ ≤ _ := Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => by split_ifs <;> positivity
  have hr0 : (0 : ℝ) ≤ r / 2 := by positivity
  calc ((r : ℝ) / 2) ^ 2 = (r / 2) * (r / 2) := sq _
    _ ≤ (∑ a ∈ Ioc K (2 ^ r * K), 1 / (a : ℝ)) * (∑ b ∈ Ioc K (2 ^ r * K), 1 / (b : ℝ)) :=
        mul_le_mul hblock hblock hr0 (hr0.trans hblock)
    _ ≤ _ := hprod

/-- **The boundary of the external square is unbounded.** -/
theorem tendsto_externalEscape : Tendsto externalEscape atTop atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨r, hr⟩ := exists_nat_ge (2 * Real.sqrt (max B 0))
  filter_upwards [eventually_ge_atTop (4 ^ r)] with N hN
  have h := ofNat_div_four_sq_le_externalEscape hN
  have hs : Real.sqrt (max B 0) ≤ r / 2 := by linarith
  have hsq : max B 0 ≤ ((r : ℝ) / 2) ^ 2 := by
    have := Real.sq_sqrt (le_max_right B 0)
    nlinarith [Real.sqrt_nonneg (max B 0)]
  linarith [le_max_left B 0]

/-! ### The relative square over `𝔽_q` -/

/-- The power sums of the relative square of a curve datum: `Σ_{i,i'} (β_i β_{i'})^j`. -/
def relSquarePowerSum {ι : Type*} [Fintype ι] (D : CurveDatum ι) (j : ℕ) : ℂ :=
  ∑ i, ∑ i', (D.β i * D.β i') ^ j

/-- **The relative square's power sums are the squares of the original ones.** -/
theorem relSquarePowerSum_eq {ι : Type*} [Fintype ι] (D : CurveDatum ι) (j : ℕ) :
    relSquarePowerSum D j = D.powerSum j ^ 2 := by
  rw [relSquarePowerSum, CurveDatum.powerSum, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => mul_pow _ _ _

/-- **Positivity of the relative square is automatic**: its traces are squares of real numbers, for
every datum, pure or not. -/
theorem relSquarePowerSum_nonneg {ι : Type*} [Fintype ι] (D : CurveDatum ι) (j : ℕ) :
    relSquarePowerSum D j = ((D.trace j ^ 2 : ℝ) : ℂ) ∧ 0 ≤ D.trace j ^ 2 := by
  refine ⟨?_, sq_nonneg _⟩
  rw [relSquarePowerSum_eq, D.powerSum_eq_trace]
  push_cast
  ring

/-- **The relative square has a fixed budget iff the datum has one.** -/
theorem bounded_relSquare_iff {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    (∃ C, ∀ j, ‖relSquarePowerSum D j‖ ≤ C) ↔ ∃ C, ∀ j, ‖D.powerSum j‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨Real.sqrt C, fun j => ?_⟩
    have h := hC j
    rw [relSquarePowerSum_eq, norm_pow] at h
    exact Real.le_sqrt_of_sq_le h
  · rintro ⟨C, hC⟩
    refine ⟨C ^ 2, fun j => ?_⟩
    rw [relSquarePowerSum_eq, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC j) 2

open Real in
/-- **The golden relative square grows like `φ^{2j}`.** -/
theorem goldenDatum_relSquare_ge (j : ℕ) :
    goldenRatio ^ (2 * j) ≤ ‖relSquarePowerSum goldenDatum j‖ := by
  rw [(relSquarePowerSum_nonneg goldenDatum j).1, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), pow_mul']
  exact pow_le_pow_left₀ (pow_nonneg goldenRatio_pos.le j) (goldenRatio_pow_le_goldenDatum_trace j) 2

end GaloisForLFunctions.ArithmeticCorrelationGeometry
