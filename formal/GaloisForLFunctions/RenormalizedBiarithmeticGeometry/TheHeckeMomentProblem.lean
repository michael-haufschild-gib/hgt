import GaloisForLFunctions.ConjugateDiagonalGeometry.ZetaDepthDistribution
import Mathlib.Algebra.Polynomial.Roots

/-!
# The Hecke moment problem

For a compact `C²` test `f` and a scale `L`, the collided weights `w_ρ = m_ρ |f̂(ρ)|²` and the depth
kernel `k_ρ = 2cosh(2δ_ρ L) − 2 ≥ 0` define the moment sequence

`m_j(L) = Σ_ρ w_ρ k_ρ^j`,  `m_0 = D(f)`, `m_1 = E(L)`, `m_2 = E(2L) − 4E(L)`

(`depthMoment_zero`, `depthMoment_one`, `depthMoment_two`). It is the moment sequence of a positive
measure on `[0, ∞)`, so it solves a Stieltjes moment problem.

* **Hankel positivity** (`hankelForm_eq_tsum`, `hankelForm_nonneg`). For every shift `s` and
  coefficients `c`, `Σ_{i,j} c_i c_j m_{i+j+s} = Σ_ρ w_ρ k_ρ^s (Σ_i c_i k_ρ^i)² ≥ 0`.
* **Null vectors are annihilating polynomials** (`hankelForm_eq_zero_iff`). The Hankel form vanishes
  at `c` iff the polynomial `Σ c_i X^i` vanishes at every depth level seen by `f`.
* **Shell rigidity** (`seenLevels_finite_of_hankel_null`, `ncard_seenLevels_lt_of_hankel_null`). A
  nonzero null vector of size `n` forces at most `n − 1` seen depth levels; for `L ≠ 0` these are
  absolute depths. The case `n = 2` is the unit-shell rigidity of CDG.
* **Log-convexity** (`depthMoment_sq_le`): `m_j² ≤ m_{j−1} m_{j+1}`, which at `j = 1` is two-scale
  rigidity `E(L)² ≤ D(E(2L) − 4E(L))`.

The Hecke defects at scales `L, 2L, 3L, …` are linear combinations of the moments, so every Hankel
inequality is an inequality between computable Hecke defects; finite integer theta prefixes compute
all moments (CDG `finiteThetaSource_uniform_moving_moments`).
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open Zeta23 GaloisForLFunctions.ConjugateDiagonalGeometry GaloisForLFunctions.ArithmeticPolarization

/-- The depth level `k_ρ = 2cosh(2δ_ρ L) − 2` of a zero at scale `L`. -/
abbrev level (L : ℝ) (ρ : zetaZeroConfig.carrier) : ℝ := depthKernel L (zetaDepth ρ)

/-- The depth moments `m_j(L) = Σ_ρ w_ρ k_ρ^j`. -/
def depthMoment (f : CompactTest) (L : ℝ) (j : ℕ) : ℝ :=
  ∑' ρ, zetaWeight f ρ * level L ρ ^ j

theorem depthMoment_zero (f : CompactTest) (L : ℝ) :
    depthMoment f L 0 = collidedForm zetaZeroConfig f.1 := by
  simp only [depthMoment, pow_zero, mul_one]
  rfl

theorem depthMoment_one (f : CompactTest) (L : ℝ) : depthMoment f L 1 = heckeDefect f L := by
  simp only [depthMoment, pow_one, heckeDefect]

theorem depthMoment_two (f : CompactTest) (L : ℝ) :
    depthMoment f L 2 = heckeDefect f (2 * L) - 4 * heckeDefect f L := by
  rw [heckeDefect_double, depthMoment]
  ring

/-! ### Hankel forms -/

/-- The shifted Hankel form `Σ_{i,j} c_i c_j m_{i+j+s}`. -/
def hankelForm (f : CompactTest) (L : ℝ) (s : ℕ) {n : ℕ} (c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * depthMoment f L (i + j + s)

/-- The value of the polynomial with coefficients `c` at `t`. -/
def coeffEval {n : ℕ} (c : Fin n → ℝ) (t : ℝ) : ℝ := ∑ i, c i * t ^ (i : ℕ)

theorem hasSum_hankelForm (f : CompactTest) (L : ℝ) (s : ℕ) {n : ℕ} (c : Fin n → ℝ) :
    HasSum (fun ρ => zetaWeight f ρ * level L ρ ^ s * coeffEval c (level L ρ) ^ 2)
      (hankelForm f L s c) := by
  have h := hasSum_sum fun (i : Fin n) (_ : i ∈ univ) =>
    hasSum_sum fun (j : Fin n) (_ : j ∈ univ) =>
      ((summable_zeta_kernel_pow f L ((i : ℕ) + j + s)).hasSum).mul_left (c i * c j)
  refine h.congr_fun fun ρ => ?_
  simp only [coeffEval]
  rw [sq, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_add]
  ring

/-- **The Hankel forms are traces over the zeros**: `Σ_ρ w_ρ k_ρ^s (Σ_i c_i k_ρ^i)²`. -/
theorem hankelForm_eq_tsum (f : CompactTest) (L : ℝ) (s : ℕ) {n : ℕ} (c : Fin n → ℝ) :
    hankelForm f L s c =
      ∑' ρ, zetaWeight f ρ * level L ρ ^ s * coeffEval c (level L ρ) ^ 2 :=
  (hasSum_hankelForm f L s c).tsum_eq.symm

theorem hankel_term_nonneg (f : CompactTest) (L : ℝ) (s : ℕ) {n : ℕ} (c : Fin n → ℝ)
    (ρ : zetaZeroConfig.carrier) :
    0 ≤ zetaWeight f ρ * level L ρ ^ s * coeffEval c (level L ρ) ^ 2 :=
  mul_nonneg (mul_nonneg (zetaWeight_nonneg f ρ) (pow_nonneg (depthKernel_nonneg _ _) s))
    (sq_nonneg _)

/-- **Hankel positivity** of the depth moments at every shift. -/
theorem hankelForm_nonneg (f : CompactTest) (L : ℝ) (s : ℕ) {n : ℕ} (c : Fin n → ℝ) :
    0 ≤ hankelForm f L s c :=
  (hasSum_hankelForm f L s c).nonneg (hankel_term_nonneg f L s c)

/-- **Null vectors are annihilating polynomials of the seen levels.** -/
theorem hankelForm_eq_zero_iff (f : CompactTest) (L : ℝ) {n : ℕ} (c : Fin n → ℝ) :
    hankelForm f L 0 c = 0 ↔
      ∀ ρ, zetaWeight f ρ ≠ 0 → coeffEval c (level L ρ) = 0 := by
  constructor
  · intro h ρ hρ
    have hs := hasSum_hankelForm f L 0 c
    rw [h] at hs
    have hz := congrFun ((hasSum_zero_iff_of_nonneg (hankel_term_nonneg f L 0 c)).mp hs) ρ
    simp only [pow_zero, mul_one, Pi.zero_apply] at hz
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp hz).resolve_left hρ)
  · intro h
    rw [hankelForm_eq_tsum]
    refine (tsum_congr fun ρ => ?_).trans tsum_zero
    by_cases hρ : zetaWeight f ρ = 0
    · simp [hρ]
    · simp [h ρ hρ]

/-! ### Shell rigidity -/

/-- The depth levels seen by `f` at scale `L`. -/
def seenLevels (f : CompactTest) (L : ℝ) : Set ℝ :=
  {t | ∃ ρ, zetaWeight f ρ ≠ 0 ∧ level L ρ = t}

/-- The polynomial with coefficients `c`. -/
def coeffPoly {n : ℕ} (c : Fin n → ℝ) : Polynomial ℝ :=
  ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

theorem eval_coeffPoly {n : ℕ} (c : Fin n → ℝ) (t : ℝ) :
    (coeffPoly c).eval t = coeffEval c t := by
  simp [coeffPoly, coeffEval, Polynomial.eval_finsetSum]

theorem coeffPoly_ne_zero {n : ℕ} {c : Fin n → ℝ} (hc : c ≠ 0) : coeffPoly c ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  intro h
  have := congrArg (fun p => Polynomial.coeff p i) h
  simp only [coeffPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (Fin.ext h).symm)])
    (fun h => absurd (mem_univ i) h), if_pos rfl] at this
  exact hi this

theorem seenLevels_subset_roots (f : CompactTest) (L : ℝ) {n : ℕ} {c : Fin n → ℝ}
    (hnull : hankelForm f L 0 c = 0) :
    seenLevels f L ⊆ {t | (coeffPoly c).eval t = 0} := by
  rintro t ⟨ρ, hρ, rfl⟩
  simp only [Set.mem_setOf_eq, eval_coeffPoly]
  exact (hankelForm_eq_zero_iff f L c).mp hnull ρ hρ

/-- **Shell rigidity, finiteness.** A nonzero Hankel null vector forces finitely many seen levels. -/
theorem seenLevels_finite_of_hankel_null (f : CompactTest) (L : ℝ) {n : ℕ} {c : Fin n → ℝ}
    (hc : c ≠ 0) (hnull : hankelForm f L 0 c = 0) : (seenLevels f L).Finite := by
  refine Set.Finite.subset (coeffPoly c).roots.toFinset.finite_toSet fun t ht => ?_
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_roots (coeffPoly_ne_zero hc)).mpr (seenLevels_subset_roots f L hnull ht)

/-- **Shell rigidity, count.** A nonzero Hankel null vector of size `n` forces fewer than `n` seen
depth levels. -/
theorem ncard_seenLevels_lt_of_hankel_null (f : CompactTest) (L : ℝ) {n : ℕ} {c : Fin n → ℝ}
    (hc : c ≠ 0) (hnull : hankelForm f L 0 c = 0) : (seenLevels f L).ncard < n := by
  have hp := coeffPoly_ne_zero hc
  have hsub : seenLevels f L ⊆ ((coeffPoly c).roots.toFinset : Set ℝ) := fun t ht => by
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hp).mpr (seenLevels_subset_roots f L hnull ht)
  have hdeg : (coeffPoly c).natDegree < n := by
    have h := Polynomial.degree_sum_fin_lt c
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (funext fun i => i.elim0) hc
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr h
  calc (seenLevels f L).ncard ≤ ((coeffPoly c).roots.toFinset : Set ℝ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (coeffPoly c).roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card (coeffPoly c).roots := Multiset.toFinset_card_le _
    _ ≤ (coeffPoly c).natDegree := Polynomial.card_roots' _
    _ < n := hdeg

/-! ### Log-convexity -/

/-- **Log-convexity of the moments**: `m_j² ≤ m_{j−1} m_{j+1}`. -/
theorem depthMoment_sq_le (f : CompactTest) (L : ℝ) (j : ℕ) :
    depthMoment f L (j + 1) ^ 2 ≤ depthMoment f L j * depthMoment f L (j + 2) := by
  -- The shifted Hankel form at `c = (m_{j+1}, −m_j)`.
  set a := depthMoment f L (j + 1)
  set b := depthMoment f L j
  set d := depthMoment f L (j + 2)
  have h := hankelForm_nonneg f L j (n := 2) ![a, -b]
  have hval : hankelForm f L j (n := 2) ![a, -b] = b * (b * d - a ^ 2) := by
    simp only [hankelForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, zero_add]
    simp only [show (1 + 1 + j : ℕ) = j + 2 by ring, show (1 + j : ℕ) = j + 1 by ring]
    ring
  rw [hval] at h
  rcases (show 0 ≤ b from tsum_nonneg fun ρ =>
      mul_nonneg (zetaWeight_nonneg f ρ) (pow_nonneg (depthKernel_nonneg _ _) _)).lt_or_eq
    with hb | hb
  · nlinarith
  · -- If `m_j = 0` every weighted level vanishes, so `m_{j+1} = 0`.
    have hterms : ∀ ρ, zetaWeight f ρ * level L ρ ^ j = 0 := by
      have hs : HasSum (fun ρ => zetaWeight f ρ * level L ρ ^ j) b :=
        (summable_zeta_kernel_pow f L j).hasSum
      rw [← hb] at hs
      exact fun ρ => congrFun ((hasSum_zero_iff_of_nonneg fun ρ => mul_nonneg
        (zetaWeight_nonneg f ρ) (pow_nonneg (depthKernel_nonneg _ _) _)).mp hs) ρ
    have ha : a = 0 := by
      simp only [a, depthMoment]
      refine (tsum_congr fun ρ => ?_).trans tsum_zero
      rw [pow_succ, ← mul_assoc, hterms ρ, zero_mul]
    rw [ha, ← hb]
    simp

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
