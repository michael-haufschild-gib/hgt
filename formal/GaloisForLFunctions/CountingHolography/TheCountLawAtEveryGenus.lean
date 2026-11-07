import GaloisForLFunctions.ArithmeticScatteringHolography.TheCountLawOfTheProbes
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw

/-!
# The count law at every genus

A count law `K : ℤ² → ℕ` (the parallelogram law on the probes `y - x π`) is determined by three
channel numbers, `K(0,1)`, `K(1,0)` and `K(1,1)` (`countLaw_eq_form`). For a curve of genus `g` over
`𝔽_q` the natural numbers at level `n` (probes `y - x πⁿ`) are

  `K(0,1) = g`,  `K(1,0) = g qⁿ`,  `K(1,1) = N_n + (g - 1)(qⁿ + 1)`,

with `N_n = #C(𝔽_{qⁿ})`. The count law then is the **genus form**
`K = g y² - a_n x y + g qⁿ x²`, `a_n = qⁿ + 1 - N_n` (`countLaw_eq_genusForm`), which is half the
Castelnuovo–Severi defect of `yΔ - xΓ_{Fⁿ}` (`toeplitz_twoTerm`). Such a count exists exactly when
`a_n² ≤ 4 g² qⁿ` (`exists_genusCountLaw_iff`).

**The tower.** A curve datum has every mode on the universal circle exactly when its channel numbers
extend to a count law at every level of the base-change tower (`towerCountLaw_iff_unitary`). The input
is only `g`, `q` and the point counts: the count law at all levels is Hasse–Weil, by power-sum
elimination and the functional equation. At genus one the first level suffices; at genus two it does
not (`TheGenusTwoRung`).

The golden fake has positive channel counts at every level and no count law at the first one
(`golden_counts_without_law`): it fails through the count.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri

/-! ### Three numbers determine a count law -/

/-- A function with the parallelogram law that vanishes at `(0,1)`, `(1,0)`, `(1,1)` vanishes. -/
theorem eq_zero_of_parallelogram {F : ℤ → ℤ → ℤ}
    (hlaw : ∀ x y u v, F (x + u) (y + v) + F (x - u) (y - v) = 2 * F x y + 2 * F u v)
    (h01 : F 0 1 = 0) (h10 : F 1 0 = 0) (h11 : F 1 1 = 0) (x y : ℤ) : F x y = 0 := by
  have h00 : F 0 0 = 0 := by
    have := hlaw 0 0 0 0
    simp only [add_zero, sub_zero] at this
    linarith
  have hzero (y : ℤ) : F 0 y = 0 := by
    refine eq_zero_of_second_diff (g := fun y => F 0 y) (fun n => ?_) h00 h01 y
    have := hlaw 0 n 0 1
    simp only [add_zero, sub_zero, h01] at this
    linarith
  have hone (y : ℤ) : F 1 y = 0 := by
    refine eq_zero_of_second_diff (g := fun y => F 1 y) (fun n => ?_) h10 h11 y
    have := hlaw 1 n 0 1
    simp only [add_zero, sub_zero, h01] at this
    linarith
  refine eq_zero_of_second_diff (g := fun x => F x y) (fun n => ?_) (hzero y) (hone y) x
  have := hlaw n y 1 0
  simp only [add_zero, sub_zero, h10] at this
  linarith

/-- **A count law is the binary form of its three channel numbers.** -/
theorem countLaw_eq_form {K : ℤ → ℤ → ℕ} (hK : CountLaw K) (x y : ℤ) :
    (K x y : ℤ) = K 0 1 * y ^ 2 + ((K 1 1 : ℤ) - K 0 1 - K 1 0) * x * y + K 1 0 * x ^ 2 := by
  set A : ℤ := (K 0 1 : ℤ)
  set B : ℤ := (K 1 0 : ℤ)
  set C : ℤ := (K 1 1 : ℤ)
  have key := eq_zero_of_parallelogram
    (F := fun x y => (K x y : ℤ) - (A * y ^ 2 + (C - A - B) * x * y + B * x ^ 2))
    (fun x y u v => by
      have := hK x y u v
      linear_combination this)
    (by simp [A]) (by simp [B]) (by simp only [C, A, B]; ring) x y
  linarith

/-! ### The genus form -/

/-- The genus-`g` count of the probe `y - x π` at size `Q` and trace `a`: `g y² - a x y + g Q x²`. -/
def genusForm (g Q a x y : ℤ) : ℤ := g * y ^ 2 - a * x * y + g * Q * x ^ 2

/-- **The channel numbers of a curve force the genus form.** -/
theorem countLaw_eq_genusForm {K : ℤ → ℤ → ℕ} (hK : CountLaw K) {g Q a : ℤ} (h01 : (K 0 1 : ℤ) = g)
    (h10 : (K 1 0 : ℤ) = g * Q) (h11 : (K 1 1 : ℤ) = g * (Q + 1) - a) (x y : ℤ) :
    (K x y : ℤ) = genusForm g Q a x y := by
  rw [countLaw_eq_form hK, h01, h10, h11]
  unfold genusForm
  ring

theorem genusForm_cast {g : ℤ} (hg : (g : ℝ) ≠ 0) (Q a x y : ℤ) :
    ((genusForm g Q a x y : ℤ) : ℝ) = g * kreinSquare (Q : ℝ) ((a : ℝ) / g) (x : ℝ) (y : ℝ) := by
  unfold genusForm kreinSquare
  push_cast
  field_simp

/-- The genus form is nonnegative on the probes exactly under the Weil bound `a² ≤ 4 g² Q`. -/
theorem genusForm_nonneg_iff {g Q a : ℤ} (hg : 0 < g) :
    (∀ x y, 0 ≤ genusForm g Q a x y) ↔ a ^ 2 ≤ 4 * g ^ 2 * Q := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have e : (∀ x y, 0 ≤ genusForm g Q a x y) ↔
      ∀ m n : ℤ, 0 ≤ kreinSquare (Q : ℝ) ((a : ℝ) / g) (n : ℝ) (m : ℝ) := by
    constructor
    · intro h m n
      have := h n m
      have hc : (0 : ℝ) ≤ ((genusForm g Q a n m : ℤ) : ℝ) := by exact_mod_cast this
      rw [genusForm_cast hg'.ne'] at hc
      exact nonneg_of_mul_nonneg_right (by linarith) hg'
    · intro h x y
      have hc : (0 : ℝ) ≤ ((genusForm g Q a x y : ℤ) : ℝ) := by
        rw [genusForm_cast hg'.ne']
        exact mul_nonneg hg'.le (h y x)
      exact_mod_cast hc
  rw [e, integer_kreinSquare_nonneg_iff, div_pow, div_le_iff₀ (by positivity)]
  constructor
  · intro h
    have : ((a ^ 2 : ℤ) : ℝ) ≤ ((4 * g ^ 2 * Q : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((a ^ 2 : ℤ) : ℝ) ≤ ((4 * g ^ 2 * Q : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

/-- **A genus-`g` count law exists exactly under the Weil bound.** -/
theorem exists_genusCountLaw_iff {g Q a : ℤ} (hg : 0 < g) :
    (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = g ∧ (K 1 0 : ℤ) = g * Q ∧
      (K 1 1 : ℤ) = g * (Q + 1) - a) ↔ a ^ 2 ≤ 4 * g ^ 2 * Q := by
  rw [← genusForm_nonneg_iff hg]
  constructor
  · rintro ⟨K, hK, h01, h10, h11⟩ x y
    rw [← countLaw_eq_genusForm hK h01 h10 h11]
    positivity
  · intro hn
    have hc (x y : ℤ) : ((genusForm g Q a x y).toNat : ℤ) = genusForm g Q a x y :=
      Int.toNat_of_nonneg (hn x y)
    refine ⟨fun x y => (genusForm g Q a x y).toNat, fun x y u v => ?_, ?_, ?_, ?_⟩
    · simp only [hc]
      unfold genusForm
      ring
    · simp only [hc]
      unfold genusForm
      ring
    · simp only [hc]
      unfold genusForm
      ring
    · simp only [hc]
      unfold genusForm
      ring

/-! ### The genus form is half the Castelnuovo–Severi defect -/

section CurveData

variable {ι : Type*} [Fintype ι]

/-- **The two-term Toeplitz form.** On the probe with coefficient `y` at lag `0` and `-x qⁿᐟ²` at lag `n`,
the Castelnuovo–Severi defect is `#ι (y² + qⁿ x²) - 2 x y qⁿᐟ² Re Σ βⁿ`: twice the genus form. -/
theorem toeplitz_twoTerm (D : CurveDatum ι) {n : ℕ} (hn : n ≠ 0) (x y : ℝ) :
    D.toeplitz {0, n} (fun k => if k = 0 then y else -x * D.sqrtq ^ n) =
      Fintype.card ι * (y ^ 2 + D.q ^ n * x ^ 2) - 2 * (D.sqrtq ^ n * D.trace n) * x * y := by
  rw [CurveDatum.toeplitz, Finset.sum_pair (Ne.symm hn), Finset.sum_pair (Ne.symm hn),
    Finset.sum_pair (Ne.symm hn)]
  simp only [hn, if_true, if_false, Nat.dist_self, Nat.dist_zero_left, Nat.dist_zero_right,
    CurveDatum.trace_zero]
  have hq : D.sqrtq ^ n * D.sqrtq ^ n = D.q ^ n := by rw [← mul_pow, ← sq, D.sqrtq_sq]
  linear_combination (Fintype.card ι : ℝ) * x ^ 2 * hq

/-- On the circle the power sums are bounded by the number of modes. -/
theorem abs_trace_le_of_unitary (D : CurveDatum ι) (hU : ∀ i, ‖D.β i‖ = 1) (n : ℕ) :
    |D.trace n| ≤ Fintype.card ι := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← D.powerSum_eq_trace]
  calc ‖D.powerSum n‖ ≤ ∑ i, ‖D.β i ^ n‖ := norm_sum_le _ _
    _ = Fintype.card ι := by simp [hU]

/-- **Power-sum elimination.** Traces bounded by the number of modes at every level put every mode on
the circle. -/
theorem unitary_of_abs_trace_le (D : CurveDatum ι) (h : ∀ n, 1 ≤ n → |D.trace n| ≤ Fintype.card ι) :
    ∀ i, ‖D.β i‖ = 1 := by
  have hle : ∀ i, ‖D.β i‖ ≤ 1 := by
    intro i
    refine RHTower.WeilKloosterman.norm_le_of_power_sums_bound Finset.univ D.β
      (C := Fintype.card ι) (m0 := 1) zero_le_one (fun m hm => ?_) i (Finset.mem_univ i)
    rw [one_pow, mul_one]
    have e : ∑ i ∈ Finset.univ, D.β i ^ m = D.powerSum m := rfl
    rw [e, D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
    exact h m hm
  intro i
  have hfe := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at hfe
  nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i)), hle i, hle (D.fePerm i)]

/-- The count law at level `n` is the Weil bound at level `n`. -/
theorem exists_levelCountLaw_iff (D : CurveDatum ι) {g Q : ℕ} (hg : Fintype.card ι = 2 * g) (hg0 : 0 < g)
    (hQ : D.q = Q) {N : ℕ} {n : ℕ} (hN : (N : ℝ) = D.pointCount n) :
    (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = g ∧ K 1 0 = g * Q ^ n ∧
      K 1 1 = N + (g - 1) * (Q ^ n + 1)) ↔ |D.trace n| ≤ Fintype.card ι := by
  set a : ℤ := (Q : ℤ) ^ n + 1 - N with ha
  have hacast : (a : ℝ) = D.sqrtq ^ n * D.trace n := by
    rw [ha]
    push_cast
    rw [hN, CurveDatum.pointCount, hQ]
    ring
  have hlaw : (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = g ∧ K 1 0 = g * Q ^ n ∧
      K 1 1 = N + (g - 1) * (Q ^ n + 1)) ↔
      (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = g ∧ (K 1 0 : ℤ) = g * (Q ^ n : ℤ) ∧
        (K 1 1 : ℤ) = g * ((Q ^ n : ℤ) + 1) - a) := by
    have e11 : ((N + (g - 1) * (Q ^ n + 1) : ℕ) : ℤ) = g * ((Q ^ n : ℤ) + 1) - a := by
      rw [ha, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      ring
    refine exists_congr fun K => and_congr Iff.rfl ?_
    refine and_congr (by exact_mod_cast Iff.rfl) (and_congr (by exact_mod_cast Iff.rfl) ?_)
    rw [← e11]
    exact_mod_cast Iff.rfl
  rw [hlaw, exists_genusCountLaw_iff (by exact_mod_cast hg0)]
  have hs : 0 < D.sqrtq ^ n := pow_pos D.sqrtq_pos n
  have hqn : ((Q : ℤ) ^ n : ℤ) = ((Q ^ n : ℕ) : ℤ) := by push_cast; ring
  have hsq : (D.sqrtq ^ n) ^ 2 = (Q : ℝ) ^ n := by rw [← pow_mul, mul_comm, pow_mul, D.sqrtq_sq, hQ]
  have hcard : (Fintype.card ι : ℝ) = 2 * g := by exact_mod_cast hg
  constructor
  · intro h
    have hr : ((a ^ 2 : ℤ) : ℝ) ≤ ((4 * (g : ℤ) ^ 2 * (Q : ℤ) ^ n : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at hr
    rw [hacast, mul_pow, hsq] at hr
    rw [hcard, abs_le]
    have hQn : (0 : ℝ) < (Q : ℝ) ^ n := by rw [← hsq]; positivity
    have ht2 : D.trace n ^ 2 ≤ 4 * (g : ℝ) ^ 2 :=
      le_of_mul_le_mul_left (by linarith : (Q : ℝ) ^ n * D.trace n ^ 2 ≤ (Q : ℝ) ^ n * (4 * g ^ 2)) hQn
    have hg' : (0 : ℝ) ≤ g := by positivity
    constructor <;> nlinarith
  · intro h
    rw [hcard] at h
    have hsq' : D.trace n ^ 2 ≤ (2 * g : ℝ) ^ 2 := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    have hr : ((a ^ 2 : ℤ) : ℝ) ≤ ((4 * (g : ℤ) ^ 2 * (Q : ℤ) ^ n : ℤ) : ℝ) := by
      push_cast
      rw [hacast, mul_pow, hsq]
      have hQn : (0 : ℝ) ≤ (Q : ℝ) ^ n := by rw [← hsq]; positivity
      nlinarith
    exact_mod_cast hr

/-- **The count law at every genus.** A curve datum of genus `g` with `q = Q` and natural point counts
`N_n` has every mode on the universal circle exactly when, at every level `n ≥ 1`, its channel numbers
`g`, `g Qⁿ`, `N_n + (g - 1)(Qⁿ + 1)` extend to a count of all probes `y - x πⁿ`. -/
theorem towerCountLaw_iff_unitary (D : CurveDatum ι) {g Q : ℕ} (hg : Fintype.card ι = 2 * g) (hg0 : 0 < g)
    (hQ : D.q = Q) {N : ℕ → ℕ} (hN : ∀ n, (N n : ℝ) = D.pointCount n) :
    (∀ n, 1 ≤ n → ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = g ∧ K 1 0 = g * Q ^ n ∧
      K 1 1 = N n + (g - 1) * (Q ^ n + 1)) ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h
    exact unitary_of_abs_trace_le D fun n hn =>
      (exists_levelCountLaw_iff D hg hg0 hQ (hN n)).mp (h n hn)
  · intro hU n _
    exact (exists_levelCountLaw_iff D hg hg0 hQ (hN n)).mpr (abs_trace_le_of_unitary D hU n)

end CurveData

/-! ### The golden fake: counts without a law -/

/-- The point counts of the golden fake, `5ⁿ + 1 - L_n`, as natural numbers. -/
def goldenCount (n : ℕ) : ℕ := ((5 : ℤ) ^ n + 1 - goldenLucas n).toNat

theorem goldenCount_cast (n : ℕ) : (goldenCount n : ℝ) = goldenDatum.pointCount n := by
  have hnn : (0 : ℤ) ≤ (5 : ℤ) ^ n + 1 - goldenLucas n := by
    have h : 0 ≤ goldenDatum.pointCount n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [CurveDatum.pointCount_zero]; simp
      · linarith [one_le_goldenDatum_pointCount hn]
    rw [goldenDatum_pointCount_eq] at h
    exact_mod_cast h
  rw [goldenDatum_pointCount_eq, goldenCount]
  have : (((5 : ℤ) ^ n + 1 - goldenLucas n).toNat : ℤ) = (5 : ℤ) ^ n + 1 - goldenLucas n :=
    Int.toNat_of_nonneg hnn
  exact_mod_cast this

/-- **The golden fake fails through the count.** Every level has at least one channel, and the channel
numbers of the first level extend to no count law. -/
theorem golden_counts_without_law :
    (∀ n, 1 ≤ n → 1 ≤ goldenCount n) ∧
      ¬ ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = 1 ∧ K 1 0 = 1 * 5 ^ 1 ∧
        K 1 1 = goldenCount 1 + (1 - 1) * (5 ^ 1 + 1) := by
  have hq : goldenDatum.q = ((5 : ℕ) : ℝ) := by norm_num [goldenDatum]
  refine ⟨fun n hn => ?_, fun h => ?_⟩
  · have h1 := one_le_goldenDatum_pointCount hn
    rw [← goldenCount_cast] at h1
    exact_mod_cast h1
  · have hlev := (exists_levelCountLaw_iff goldenDatum (g := 1) (by simp) one_pos hq
      (goldenCount_cast 1)).mp h
    rw [goldenDatum_trace, Fintype.card_fin, pow_one, pow_one] at hlev
    have hφ := Real.one_lt_goldenRatio
    have hinv : Real.goldenRatio * Real.goldenRatio⁻¹ = 1 := mul_inv_cancel₀ Real.goldenRatio_pos.ne'
    have h2 := (abs_le.mp hlev).2
    push_cast at h2
    nlinarith [sq_nonneg (Real.goldenRatio - 1)]

end GaloisForLFunctions.CountingHolography

end
