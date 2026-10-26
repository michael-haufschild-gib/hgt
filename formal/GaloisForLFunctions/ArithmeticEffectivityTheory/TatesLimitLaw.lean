import GaloisForLFunctions.ArithmeticOrientationGeometry.ScalingDataAndWeilPlanes
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDefectOfAGraphIsTwiceItsDegree

/-!
# Tate's limit law: positivity of a quadratic form from a naive height

Over a number field the Néron–Tate height is a positive semidefinite quadratic form, and the proof
uses two inputs only: the theorem of the square up to a bounded error, and the nonnegativity of
naive heights (the product formula). This is the arithmetic form of Weil's polarization. The
module isolates it on an arbitrary abelian group and applies it to the integral correspondence
ring of a scaling datum.

* **Tate's limit** (`tendsto_tateSeq`, `abs_tateLimit_sub_le`, `tateLimit_two_nsmul`). If
  `|h(2x) − 4h(x)| ≤ C`, then `q(x) = lim 4^{−n} h(2^n x)` exists, `q(2x) = 4q(x)` and
  `|q − h| ≤ C/3`; it is the only such function at bounded distance from `h`
  (`eq_of_two_nsmul_of_bounded`).
* **The theorem of the square** (`tateLimit_parallelogram`). An approximate parallelogram law for
  `h` makes `q` satisfy the exact one; then `q(m x) = m² q(x)` (`parallelogram_nsmul`).
* **Positivity** (`tateLimit_nonneg`, `nonneg_of_naiveHeight`). If `h` is bounded below, `q ≥ 0`.
  More generally a function `q` homogeneous of degree two is nonnegative iff some function bounded
  below lies at bounded distance from it (`exists_naiveHeight_iff_nonneg`).
* **Northcott** (`isOfFinAddOrder_of_tateLimit_eq_zero`). If the sublevel sets of `h` are finite,
  `q(x) = 0` only at torsion points.
* **The integral correspondence ring** (`orbitHodgeIndex_iff_int`,
  `orbitHodgeIndex_iff_exists_naiveHeight`). On a scaling datum, Rosati positivity at a cycle `x`
  holds on real correspondences iff it holds on integral ones `ξ ∈ ℤ[G]`, iff the integral Rosati
  form `ξ ↦ τ_x(ξ ξ′)` has a naive height. For `ℤ`: RH iff every cycle's integral Rosati form has a
  naive height (`riemannHypothesis_iff_forall_exists_naiveHeight`).
* **Calibration** (`genusOne_exists_naiveHeight_iff`, `goldenDatum_no_naiveHeight`). In
  genus one the degree `deg(m − nF)` on `ℤ²` has a naive height iff the Hasse bound holds — over a
  finite field it is the order of a kernel, hence its own naive height; the golden datum has
  `deg(2 − F) = −1` and none.

The quadratic part over `ℤ` is free (the theorem of the square for normalized graphs). What a proof
needs is the other input: a function on `ℤ[G]`, nonnegative for an arithmetic reason, at bounded
distance from the Rosati form.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

section Tate

variable {M : Type*} [AddCommGroup M]

/-- Tate's sequence `4^{−n} h(2^n x)`. -/
def tateSeq (h : M → ℝ) (n : ℕ) (x : M) : ℝ := h ((2 ^ n : ℕ) • x) / 4 ^ n

theorem tateSeq_zero (h : M → ℝ) (x : M) : tateSeq h 0 x = h x := by simp [tateSeq]

theorem tateSeq_succ_sub (h : M → ℝ) (n : ℕ) (x : M) :
    tateSeq h (n + 1) x - tateSeq h n x =
      (h (2 • ((2 ^ n : ℕ) • x)) - 4 * h ((2 ^ n : ℕ) • x)) / 4 ^ (n + 1) := by
  have h2 : (2 ^ (n + 1) : ℕ) • x = 2 • ((2 ^ n : ℕ) • x) := by
    rw [smul_smul, pow_succ, mul_comm]
  rw [tateSeq, tateSeq, h2, pow_succ]
  field_simp

/-- The increments of Tate's sequence are bounded by `C / 4^{n+1}`. -/
theorem abs_tateSeq_succ_sub_le {h : M → ℝ} {C : ℝ} (hC : ∀ x, |h (2 • x) - 4 * h x| ≤ C)
    (n : ℕ) (x : M) : |tateSeq h (n + 1) x - tateSeq h n x| ≤ C / 4 * (1 / 4) ^ n := by
  rw [tateSeq_succ_sub, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (n + 1))]
  rw [div_le_iff₀ (by positivity)]
  calc |h (2 • ((2 ^ n : ℕ) • x)) - 4 * h ((2 ^ n : ℕ) • x)| ≤ C := hC _
    _ = C / 4 * (1 / 4) ^ n * 4 ^ (n + 1) := by
        rw [one_div, inv_pow, pow_succ]
        field_simp

theorem summable_tateSeq_increments {h : M → ℝ} {C : ℝ} (hC : ∀ x, |h (2 • x) - 4 * h x| ≤ C)
    (x : M) : Summable fun n => tateSeq h (n + 1) x - tateSeq h n x :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (C / 4)) fun n => by
      simpa only [Real.norm_eq_abs] using abs_tateSeq_succ_sub_le hC n x

/-- **Tate's limit** `q(x) = h(x) + Σ_n (a_{n+1}(x) − a_n(x))`. -/
def tateLimit (h : M → ℝ) (x : M) : ℝ := h x + ∑' n, (tateSeq h (n + 1) x - tateSeq h n x)

theorem tendsto_tateSeq {h : M → ℝ} {C : ℝ} (hC : ∀ x, |h (2 • x) - 4 * h x| ≤ C) (x : M) :
    Tendsto (fun n => tateSeq h n x) atTop (𝓝 (tateLimit h x)) := by
  have hs := (summable_tateSeq_increments hC x).hasSum.tendsto_sum_nat
  have htel : ∀ n, tateSeq h n x = h x + ∑ k ∈ range n, (tateSeq h (k + 1) x - tateSeq h k x) := by
    intro n
    rw [sum_range_sub (fun k => tateSeq h k x), tateSeq_zero]
    ring
  exact (tendsto_const_nhds.add hs).congr fun n => (htel n).symm

/-- `|q − h| ≤ C/3`. -/
theorem abs_tateLimit_sub_le {h : M → ℝ} {C : ℝ} (hC : ∀ x, |h (2 • x) - 4 * h x| ≤ C) (x : M) :
    |tateLimit h x - h x| ≤ C / 3 := by
  have hsum := summable_tateSeq_increments hC x
  have hg : HasSum (fun n : ℕ => C / 4 * (1 / 4 : ℝ) ^ n) (C / 3) := by
    have := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (C / 4)
    rwa [show (1 - 1 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num,
      show C / 4 * (4 / 3 : ℝ) = C / 3 by ring] at this
  rw [tateLimit, add_sub_cancel_left, ← hg.tsum_eq]
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [← tsum_neg]
    exact hg.summable.neg.tsum_le_tsum
      (fun n => neg_le_of_abs_le (abs_tateSeq_succ_sub_le hC n x)) hsum
  · exact hsum.tsum_le_tsum (fun n => le_of_abs_le (abs_tateSeq_succ_sub_le hC n x)) hg.summable

/-- **Homogeneity**: `q(2x) = 4 q(x)`. -/
theorem tateLimit_two_nsmul {h : M → ℝ} {C : ℝ} (hC : ∀ x, |h (2 • x) - 4 * h x| ≤ C) (x : M) :
    tateLimit h (2 • x) = 4 * tateLimit h x := by
  have h1 := tendsto_tateSeq hC (2 • x)
  have h2 : Tendsto (fun n => tateSeq h n (2 • x)) atTop (𝓝 (4 * tateLimit h x)) := by
    have := ((tendsto_add_atTop_iff_nat 1).mpr (tendsto_tateSeq hC x)).const_mul 4
    refine this.congr fun n => ?_
    simp only [tateSeq, smul_smul, pow_succ]
    field_simp
  exact tendsto_nhds_unique h1 h2

/-- A function with `d(2x) = 4d(x)` that is bounded vanishes. -/
theorem eq_zero_of_two_nsmul_of_bounded {d : M → ℝ} (hd : ∀ x, d (2 • x) = 4 * d x) {B : ℝ}
    (hB : ∀ x, |d x| ≤ B) (x : M) : d x = 0 := by
  have hpow : ∀ n : ℕ, d ((2 ^ n : ℕ) • x) = 4 ^ n * d x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_comm, ← smul_smul, hd, ih, pow_succ]
      ring
  have hle : ∀ n : ℕ, |d x| ≤ B * (1 / 4) ^ n := by
    intro n
    have := hB ((2 ^ n : ℕ) • x)
    rw [hpow, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n)] at this
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have hlim : Tendsto (fun n : ℕ => B * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul B
  exact abs_nonpos_iff.mp (ge_of_tendsto' hlim hle)

/-- **Uniqueness of the quadratic part**: two functions with `q(2x) = 4 q(x)` at bounded distance
from `h` coincide. -/
theorem eq_of_two_nsmul_of_bounded {h q₁ q₂ : M → ℝ} (h₁ : ∀ x, q₁ (2 • x) = 4 * q₁ x)
    (h₂ : ∀ x, q₂ (2 • x) = 4 * q₂ x) {B₁ B₂ : ℝ} (hB₁ : ∀ x, |q₁ x - h x| ≤ B₁)
    (hB₂ : ∀ x, |q₂ x - h x| ≤ B₂) : q₁ = q₂ := by
  funext x
  have := eq_zero_of_two_nsmul_of_bounded (d := fun y => q₁ y - q₂ y)
    (fun y => by simp only [h₁, h₂]; ring) (B := B₁ + B₂) (fun y => by
      calc |q₁ y - q₂ y| = |(q₁ y - h y) - (q₂ y - h y)| := by ring_nf
        _ ≤ |q₁ y - h y| + |q₂ y - h y| := abs_sub _ _
        _ ≤ B₁ + B₂ := add_le_add (hB₁ y) (hB₂ y)) x
  linarith

/-- An approximate parallelogram law gives approximate doubling, with constant `B + |h 0|`. -/
theorem abs_two_nsmul_sub_le_of_parallelogram {h : M → ℝ} {B : ℝ}
    (hP : ∀ x y, |h (x + y) + h (x - y) - 2 * h x - 2 * h y| ≤ B) (x : M) :
    |h (2 • x) - 4 * h x| ≤ B + |h 0| := by
  have := hP x x
  rw [← two_nsmul, sub_self] at this
  calc |h (2 • x) - 4 * h x| = |(h (2 • x) + h 0 - 2 * h x - 2 * h x) - h 0| := by ring_nf
    _ ≤ |h (2 • x) + h 0 - 2 * h x - 2 * h x| + |h 0| := abs_sub _ _
    _ ≤ B + |h 0| := by linarith

/-- **The theorem of the square in the limit.** An approximate parallelogram law for `h` gives the
exact parallelogram law for its Tate limit. -/
theorem tateLimit_parallelogram {h : M → ℝ} {B : ℝ}
    (hP : ∀ x y, |h (x + y) + h (x - y) - 2 * h x - 2 * h y| ≤ B) (x y : M) :
    tateLimit h (x + y) + tateLimit h (x - y) = 2 * tateLimit h x + 2 * tateLimit h y := by
  have hC := abs_two_nsmul_sub_le_of_parallelogram hP
  have hlim := (((tendsto_tateSeq hC (x + y)).add (tendsto_tateSeq hC (x - y))).sub
    ((tendsto_tateSeq hC x).const_mul 2)).sub ((tendsto_tateSeq hC y).const_mul 2)
  have hzero : Tendsto (fun n => tateSeq h n (x + y) + tateSeq h n (x - y) -
      2 * tateSeq h n x - 2 * tateSeq h n y) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => B * (1 / 4 : ℝ) ^ n) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs]
      have := hP ((2 ^ n : ℕ) • x) ((2 ^ n : ℕ) • y)
      rw [← nsmul_add, ← nsmul_sub] at this
      simp only [tateSeq]
      rw [show h ((2 ^ n : ℕ) • (x + y)) / 4 ^ n + h ((2 ^ n : ℕ) • (x - y)) / 4 ^ n -
          2 * (h ((2 ^ n : ℕ) • x) / 4 ^ n) - 2 * (h ((2 ^ n : ℕ) • y) / 4 ^ n) =
          (h ((2 ^ n : ℕ) • (x + y)) + h ((2 ^ n : ℕ) • (x - y)) - 2 * h ((2 ^ n : ℕ) • x) -
            2 * h ((2 ^ n : ℕ) • y)) / 4 ^ n by ring,
        abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n), one_div, inv_pow,
        ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right this (by positivity)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul B
  have := tendsto_nhds_unique hlim hzero
  linarith

/-- The exact parallelogram law makes `q` homogeneous of degree two on `ℕ`-multiples. -/
theorem parallelogram_nsmul {q : M → ℝ} (hq : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x : M) (m : ℕ) : q (m • x) = (m : ℝ) ^ 2 * q x := by
  have h0 : q 0 = 0 := by have := hq 0 0; simp only [add_zero, sub_zero] at this; linarith
  have key : ∀ m : ℕ, q (m • x) = (m : ℝ) ^ 2 * q x ∧ q ((m + 1) • x) = ((m : ℝ) + 1) ^ 2 * q x := by
    intro m
    induction m with
    | zero => simp [h0]
    | succ m ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have := hq ((m + 1) • x) x
      rw [← succ_nsmul, show (m + 1) • x - x = m • x by rw [succ_nsmul, add_sub_cancel_right],
        ih.1, ih.2] at this
      push_cast
      linarith
  exact (key m).1

/-- **Positivity from a naive height**: if `q(m x) = m² q(x)` and some `h ≥ −K` lies within `B`
of `q`, then `q ≥ 0`. -/
theorem nonneg_of_naiveHeight {q h : M → ℝ} (hq : ∀ (m : ℕ) x, q (m • x) = (m : ℝ) ^ 2 * q x)
    {K B : ℝ} (hK : ∀ x, -K ≤ h x) (hB : ∀ x, |h x - q x| ≤ B) (x : M) : 0 ≤ q x := by
  by_contra hneg
  have hneg := not_le.mp hneg
  obtain ⟨m, hm⟩ := exists_nat_gt ((K + B) / -q x)
  have h1 := hK (m • x)
  have h2 := (abs_le.mp (hB (m • x))).2
  rw [hq] at h2
  have hm' : K + B < (m : ℝ) * -q x := by rwa [div_lt_iff₀ (neg_pos.mpr hneg)] at hm
  have hm1 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  nlinarith

/-- **Naive heights detect positivity**: a function homogeneous of degree two is nonnegative iff
some function bounded below lies at bounded distance from it. -/
theorem exists_naiveHeight_iff_nonneg {q : M → ℝ} (hq : ∀ (m : ℕ) x, q (m • x) = (m : ℝ) ^ 2 * q x) :
    (∃ h : M → ℝ, ∃ K B : ℝ, (∀ x, -K ≤ h x) ∧ ∀ x, |h x - q x| ≤ B) ↔ ∀ x, 0 ≤ q x :=
  ⟨fun ⟨_, _, _, hK, hB⟩ => nonneg_of_naiveHeight hq hK hB,
    fun hq0 => ⟨q, 0, 0, fun x => by simpa using hq0 x, fun x => by simp⟩⟩

/-- **Tate's limit of a function bounded below is nonnegative.** -/
theorem tateLimit_nonneg {h : M → ℝ} {C K : ℝ} (hC : ∀ x, |h (2 • x) - 4 * h x| ≤ C)
    (hK : ∀ x, -K ≤ h x) (x : M) : 0 ≤ tateLimit h x := by
  have hlow : Tendsto (fun n : ℕ => -K * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul (-K)
  refine le_of_tendsto_of_tendsto' hlow (tendsto_tateSeq hC x) fun n => ?_
  rw [tateSeq, one_div, inv_pow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hK _) (by positivity)

/-- **Northcott.** If `h` has finite sublevel sets and satisfies an approximate parallelogram law,
its Tate limit vanishes only at torsion points. -/
theorem isOfFinAddOrder_of_tateLimit_eq_zero {h : M → ℝ} {B : ℝ}
    (hP : ∀ x y, |h (x + y) + h (x - y) - 2 * h x - 2 * h y| ≤ B)
    (hN : ∀ T, {x | h x ≤ T}.Finite) {x : M} (hx : tateLimit h x = 0) : IsOfFinAddOrder x := by
  have hC := abs_two_nsmul_sub_le_of_parallelogram hP
  have hsq := parallelogram_nsmul (tateLimit_parallelogram hP) x
  have hmem : ∀ m : ℕ, m • x ∈ {y | h y ≤ (B + |h 0|) / 3} := by
    intro m
    have := (abs_le.mp (abs_tateLimit_sub_le hC (m • x))).1
    rw [hsq, hx, mul_zero] at this
    simp only [Set.mem_setOf_eq]
    linarith
  obtain ⟨m, n, hmn, he⟩ := (hN _).exists_lt_map_eq_of_forall_mem hmem
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  simp [sub_nsmul x hmn.le, he]

end Tate

/-! ### The integral correspondence ring of a scaling datum -/

section IntegralRing

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ArithmeticOrientationGeometry.ScalingDatum G E)

/-- The **integral Rosati form** at a cycle `x` on `ℤ[G]`: `τ_x(ξ ξ′) = Σ_{g,h} ξ_g ξ_h c_x(g − h)`. -/
def intRosatiForm (x : E) (ξ : G →₀ ℤ) : ℝ :=
  ∑ g ∈ ξ.support, ∑ h ∈ ξ.support, (ξ g : ℝ) * ξ h * D.orbitCorr x (g - h)

/-- The integral Rosati form may be summed over any superset of the support. -/
theorem intRosatiForm_eq_sum_of_subset (x : E) (ξ : G →₀ ℤ) {S : Finset G} (hS : ξ.support ⊆ S) :
    intRosatiForm D x ξ = ∑ g ∈ S, ∑ h ∈ S, (ξ g : ℝ) * ξ h * D.orbitCorr x (g - h) := by
  classical
  have hz : ∀ g, g ∉ ξ.support → (ξ g : ℝ) = 0 := fun g hg => by
    simp [Finsupp.notMem_support_iff.mp hg]
  rw [intRosatiForm, sum_subset hS fun g _ hg => by simp only [hz g hg, zero_mul, sum_const_zero]]
  exact sum_congr rfl fun g _ => sum_subset hS fun h _ hh => by simp [hz h hh]

theorem intRosatiForm_nsmul (x : E) (m : ℕ) (ξ : G →₀ ℤ) :
    intRosatiForm D x (m • ξ) = (m : ℝ) ^ 2 * intRosatiForm D x ξ := by
  rw [intRosatiForm_eq_sum_of_subset D x (m • ξ) Finsupp.support_smul, intRosatiForm, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun h _ => ?_
  simp only [Finsupp.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  ring

/-- **Integral orbit Hodge index**: the Rosati form is nonnegative on `ℤ[G]`. -/
def IntOrbitHodgeIndex (x : E) : Prop := ∀ ξ : G →₀ ℤ, 0 ≤ intRosatiForm D x ξ

/-- Integer coefficients on a finite set of scales, as an element of `ℤ[G]`. -/
def intCorr [DecidableEq G] (S : Finset G) (m : G → ℤ) : G →₀ ℤ :=
  Finsupp.onFinset S (fun g => if g ∈ S then m g else 0) fun g hg => by
    by_contra h; exact hg (if_neg h)

theorem intRosatiForm_intCorr [DecidableEq G] (x : E) (S : Finset G) (m : G → ℤ) :
    intRosatiForm D x (intCorr S m) =
      ∑ g ∈ S, ∑ h ∈ S, (m g : ℝ) * m h * D.orbitCorr x (g - h) := by
  rw [intRosatiForm_eq_sum_of_subset D x (intCorr S m) (S := S) Finsupp.support_onFinset_subset]
  refine sum_congr rfl fun g hg => sum_congr rfl fun h hh => ?_
  simp [intCorr, Finsupp.onFinset_apply, hg, hh]

/-- **Rosati positivity is decided on integral correspondences.** Rounding `⌊n c⌋ / n → c`
transports positivity from `ℤ[G]` to real coefficients. -/
theorem orbitHodgeIndex_iff_int (x : E) : D.OrbitHodgeIndex x ↔ IntOrbitHodgeIndex D x := by
  classical
  constructor
  · intro hH ξ
    simpa [intRosatiForm] using hH ξ.support (fun g => (ξ g : ℝ))
  · intro hI S c
    set Q : (G → ℝ) → ℝ := fun a => ∑ g ∈ S, ∑ h ∈ S, a g * a h * D.orbitCorr x (g - h)
    have hround : ∀ g, Tendsto (fun n : ℕ => (⌊(n : ℝ) * c g⌋ : ℝ) / n) atTop (𝓝 (c g)) := by
      intro g
      have hlow : Tendsto (fun n : ℕ => c g - 1 / (n : ℝ)) atTop (𝓝 (c g)) := by
        have := (tendsto_const_nhds (x := c g)).sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa only [sub_zero] using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [le_div_iff₀ hn', sub_mul, one_div, inv_mul_cancel₀ hn'.ne']
        have := Int.sub_one_lt_floor ((n : ℝ) * c g)
        linarith
      · filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [div_le_iff₀ hn']
        have := Int.floor_le ((n : ℝ) * c g)
        linarith
    have hQ : Tendsto (fun n : ℕ => Q fun g => (⌊(n : ℝ) * c g⌋ : ℝ) / n) atTop (𝓝 (Q c)) :=
      tendsto_finsetSum _ fun g _ => tendsto_finsetSum _ fun h _ =>
        ((hround g).mul (hround h)).mul_const _
    refine ge_of_tendsto hQ ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hint := hI (intCorr S fun g => ⌊(n : ℝ) * c g⌋)
    rw [intRosatiForm_intCorr] at hint
    have hscale : ∑ g ∈ S, ∑ h ∈ S, ((⌊(n : ℝ) * c g⌋ : ℤ) : ℝ) * ((⌊(n : ℝ) * c h⌋ : ℤ) : ℝ) *
        D.orbitCorr x (g - h) = (n : ℝ) ^ 2 * Q fun g => (⌊(n : ℝ) * c g⌋ : ℝ) / n := by
      simp only [Q, mul_sum]
      refine sum_congr rfl fun g _ => sum_congr rfl fun h _ => ?_
      field_simp
    rw [hscale] at hint
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)

/-- **Rosati positivity is the existence of a naive height** on the integral correspondence ring:
a function bounded below at bounded distance from the integral Rosati form. -/
theorem orbitHodgeIndex_iff_exists_naiveHeight (x : E) :
    D.OrbitHodgeIndex x ↔ ∃ h : (G →₀ ℤ) → ℝ, ∃ K B : ℝ,
      (∀ ξ, -K ≤ h ξ) ∧ ∀ ξ, |h ξ - intRosatiForm D x ξ| ≤ B := by
  rw [orbitHodgeIndex_iff_int, IntOrbitHodgeIndex,
    exists_naiveHeight_iff_nonneg (intRosatiForm_nsmul D x)]

end IntegralRing

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri in
/-- **RH as naive heights.** RH holds iff for every cycle of the scaling surface the integral Rosati
form on `ℤ[ℝ]` has a naive height. -/
theorem riemannHypothesis_iff_forall_exists_naiveHeight :
    RiemannHypothesis ↔ ∀ x : ScalingCycle, ∃ h : (ℝ →₀ ℤ) → ℝ, ∃ K B : ℝ,
      (∀ ξ, -K ≤ h ξ) ∧ ∀ ξ, |h ξ - intRosatiForm zetaScalingDatum x ξ| ≤ B := by
  exact (zetaScalingDatum_hodgeIndex_iff.symm.trans
    ((ArithmeticOrientationGeometry.ScalingDatum.hodgeIndex_tfae zetaScalingDatum).out 0 1)).trans
    (forall_congr' fun x => orbitHodgeIndex_iff_exists_naiveHeight _ x)

/-! ### Calibration in genus one -/

open ArithmeticCastelnuovoSeveri

/-- The degree form `deg(m − nF)` on `ℤ²`. -/
def intEndDeg {ι : Type*} [Fintype ι] (D : CurveDatum ι) (v : ℤ × ℤ) : ℝ := D.endDeg v.1 v.2

theorem intEndDeg_nsmul {ι : Type*} [Fintype ι] (D : CurveDatum ι) (m : ℕ) (v : ℤ × ℤ) :
    intEndDeg D (m • v) = (m : ℝ) ^ 2 * intEndDeg D v := by
  obtain ⟨a, b⟩ := v
  rw [Prod.smul_mk]
  simp only [intEndDeg, CurveDatum.endDeg, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  ring

/-- **Hasse from a naive height.** For a genus-one datum the degree form on `ℤ²` has a naive height
iff the datum is unitary. Over a finite field `deg(m − nF)` is the order of a kernel and is its own
naive height. -/
theorem genusOne_exists_naiveHeight_iff (D : CurveDatum (Fin 2)) :
    (∃ h : ℤ × ℤ → ℝ, ∃ K B : ℝ, (∀ v, -K ≤ h v) ∧ ∀ v, |h v - intEndDeg D v| ≤ B) ↔
      ∀ i, ‖D.β i‖ = 1 := by
  exact (exists_naiveHeight_iff_nonneg (intEndDeg_nsmul D)).trans
    ((⟨fun h m n => h (m, n), fun h v => h v.1 v.2⟩ : (∀ v, 0 ≤ intEndDeg D v) ↔
      ∀ m n : ℤ, 0 ≤ D.endDeg m n).trans (D.genusOne_hasse_tfae.out 0 1).symm)

/-- **The golden datum has no naive height**: `deg(2 − F) = −1`. -/
theorem goldenDatum_no_naiveHeight :
    ¬ ∃ h : ℤ × ℤ → ℝ, ∃ K B : ℝ, (∀ v, -K ≤ h v) ∧ ∀ v, |h v - intEndDeg goldenDatum v| ≤ B :=
  fun hex => goldenDatum_not_unitary ((genusOne_exists_naiveHeight_iff goldenDatum).mp hex)

end GaloisForLFunctions.ArithmeticEffectivityTheory
