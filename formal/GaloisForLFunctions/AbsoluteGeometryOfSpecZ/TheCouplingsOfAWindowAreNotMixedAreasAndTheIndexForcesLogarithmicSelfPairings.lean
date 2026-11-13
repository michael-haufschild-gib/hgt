import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfABlockAndAFarWindowIsMinusTheProductOfTheirCharges

/-!
# The couplings of a window are not mixed areas, and the index forces logarithmic self-pairings

A realization of a window `(R, R + J]` is a configuration with one member for each block whose
pairings are the couplings `w(a, b) = −N(a, b) > 0`, `a ≠ b`, of the neutral part `N`, and whose
pairing matrix has at most one positive square (the Hodge index inequality for curves on a
surface, Minkowski's inequality for mixed areas of planar convex bodies). The couplings are
given, so the self-pairings are the only freedom: a *completion* is the matrix `G_d` with
`N(a, b)` off the diagonal and `d(a)` on it (`neutralWithDiagonal`), and a realization with the
self-pairings `−d(a)` exists in a space of signature `(1, ·)` iff `G_d` has at most one negative
square.

* **The law of two runs** (`sum_selfPairing_ge_of_hermNegIndex_le_one`). Let `J ≤ R`. If `G_d`
  has at most one negative square, then of any two runs of `m` blocks of the window that are at
  least `m` blocks apart, one has `Σ d(a) ≥ m log m − 2m`.
* **Constant self-pairing** (`log_sub_two_le_of_hermNegIndex_le_one`). `d ≡ c` forces
  `c ≥ log m − 2` when `3m ≤ J`: the second largest eigenvalue of the matrix of the couplings
  grows like the logarithm of the number of blocks.
* **No nonnegative self-pairings** (`two_le_hermNegIndex_of_selfPairing_nonpos`,
  `two_le_hermNegIndex_neg_of_couplings`). For `R, J ≥ 24` a symmetric matrix with the couplings
  off the diagonal and a nonnegative diagonal has two positive squares. So the couplings are not
  the mixed areas of planar convex bodies, nor the pairings of classes of nonnegative
  self-pairing on a surface, whatever the areas: Minkowski's inequality fails for the sums of the
  bodies of two far runs.
* **The rate is attained** (`sum_neutralBlock_self_le`,
  `hermNegIndex_neutralWithDiagonal_self_le_one`). The neutral part of the dyadic window
  `(3m, 6m]` is a completion with at most one negative square, and its self-pairings sum to at
  most `m log m + m/2` on every run of `m` blocks.

Proof of the law. Inside a run the couplings are at least half the jets to the differences,
`½ D(|j − l|)`, and these sum to `m log m` exactly (`sum_sum_xLogXDiff_max_sub_min`); so on the
flat packet `x` of a run `G_d(x, x) ≤ Σ d − m log m`. Two blocks more than `m` apart and without
contact are coupled by at most `2/m`, so the flat packets `x, y` of the two runs have
`|G_d(x, y)| ≤ 2m`. If both sums of `d` are below `m log m − 2m`, then
`G_d(x, y)² ≤ 4m² < G_d(x, x) G_d(y, y)` and `G_d(x, x) < 0`: two negative squares.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Completions and runs -/

/-- A completion of the couplings: the neutral part off the diagonal, the self-pairing `d` on
it. -/
def neutralWithDiagonal (Q : ℕ) (d : ℕ → ℝ) (a b : ℕ) : ℝ :=
  if a = b then d a else neutralBlock Q a b

theorem neutralWithDiagonal_comm (Q : ℕ) (d : ℕ → ℝ) (a b : ℕ) :
    neutralWithDiagonal Q d a b = neutralWithDiagonal Q d b a := by
  unfold neutralWithDiagonal
  by_cases h : a = b
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h), neutralBlock_comm]

/-- The neutral part is its completion by its own diagonal. -/
theorem neutralWithDiagonal_self (Q a b : ℕ) :
    neutralWithDiagonal Q (fun c => neutralBlock Q c c) a b = neutralBlock Q a b := by
  unfold neutralWithDiagonal
  by_cases h : a = b
  · rw [if_pos h, h]
  · rw [if_neg h]

/-- The flat packet of the run of the `m` blocks from the offset `p`. -/
def blockRun (p m j : ℕ) : ℝ := if p ≤ j ∧ j < p + m then 1 else 0

/-- A sum against the flat packet of a run is the sum over the run. -/
theorem sum_blockRun_mul {p m J : ℕ} (hJ : p + m ≤ J) (f : ℕ → ℝ) :
    ∑ j ∈ range J, blockRun p m j * f j = ∑ i ∈ range m, f (p + i) := by
  obtain ⟨K, rfl⟩ : ∃ K, J = p + m + K := ⟨J - (p + m), by omega⟩
  have h1 : ∑ j ∈ range p, blockRun p m j * f j = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hj' := Finset.mem_range.mp hj
      rw [blockRun, if_neg (by omega), zero_mul]
  have h3 : ∑ j ∈ range K, blockRun p m (p + m + j) * f (p + m + j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [blockRun, if_neg (by omega), zero_mul]
  rw [Finset.sum_range_add, Finset.sum_range_add, h1, h3, zero_add, add_zero]
  exact Finset.sum_congr rfl fun i hi => by
    have hi' := Finset.mem_range.mp hi
    rw [blockRun, if_pos (by omega), one_mul]

/-- The form of the matrix of a window on two step functions, as a sum over the blocks. -/
theorem bilin_windowMatrix_coe (K : ℕ → ℕ → ℝ) (R J : ℕ) (x y : ℕ → ℝ) :
    bilin (windowMatrix K R J) (fun i : Fin J => x i) (fun i : Fin J => y i) =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * y l * K (R + j) (R + l) := by
  unfold bilin
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ l ∈ range J, x j * y l * K (R + j) (R + l)) J]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => x i * y l * K (R + i) (R + l)) J]
  rfl

/-- The form of the matrix of a window on the flat packets of two runs. -/
theorem bilin_windowMatrix_blockRun (K : ℕ → ℕ → ℝ) (R : ℕ) {J p q m : ℕ} (hp : p + m ≤ J)
    (hq : q + m ≤ J) :
    bilin (windowMatrix K R J) (fun i : Fin J => blockRun p m i)
        (fun i : Fin J => blockRun q m i) =
      ∑ j ∈ range m, ∑ l ∈ range m, K (R + p + j) (R + q + l) := by
  rw [bilin_windowMatrix_coe K R J (blockRun p m) (blockRun q m)]
  have h1 : ∀ j ∈ range J,
      ∑ l ∈ range J, blockRun p m j * blockRun q m l * K (R + j) (R + l) =
        blockRun p m j * ∑ l ∈ range m, K (R + j) (R + (q + l)) := by
    intro j _
    rw [← sum_blockRun_mul hq (fun l => K (R + j) (R + l)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl h1,
    sum_blockRun_mul hp (fun j => ∑ l ∈ range m, K (R + j) (R + (q + l)))]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by
    rw [Nat.add_assoc R p j, Nat.add_assoc R q l]

/-! ### The couplings inside a run and between two runs -/

/-- Off the diagonal the neutral part is at most minus half the jet to the difference. -/
theorem neutralBlock_le_neg_xLogXDiff (Q : ℕ) {a b : ℕ} (hab : a ≠ b) :
    neutralBlock Q a b ≤ -(xLogXDiff (max a b - min a b) / 2) := by
  have key : ∀ {a b : ℕ}, a < b → neutralBlock Q a b ≤ -(xLogXDiff (b - a) / 2) := by
    intro a b h
    have h1 := xLogXDiff_pos (n := a + b + 1) (by omega)
    have hC : 0 ≤ floorContact Q a b := Finset.sum_nonneg fun k _ => by
      split_ifs
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
      · exact le_rfl
    rw [neutralBlock_of_lt h]
    unfold blockJet
    linarith
  rcases lt_or_gt_of_ne hab with h | h
  · rw [max_eq_right h.le, min_eq_left h.le]
    exact key h
  · rw [max_eq_left h.le, min_eq_right h.le, neutralBlock_comm]
    exact key h

/-- The jets to the differences from one block of a run telescope to two steps of `n log n`. -/
theorem sum_range_xLogXDiff_max_sub_min {J j : ℕ} (hj : j < J) :
    ∑ l ∈ range J, xLogXDiff (max j l - min j l) = xLogXStep j + xLogXStep (J - 1 - j) := by
  obtain ⟨K, rfl⟩ : ∃ K, J = j + 1 + K := ⟨J - 1 - j, by omega⟩
  have ha : ∑ l ∈ range (j + 1), xLogXDiff (max j l - min j l) = xLogXStep j := by
    rw [← sum_range_succ_xLogXDiff j, ← Finset.sum_range_reflect (fun d => xLogXDiff d) (j + 1)]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    show xLogXDiff (max j l - min j l) = xLogXDiff (j + 1 - 1 - l)
    congr 1
    omega
  have hb : ∑ i ∈ range K, xLogXDiff (max j (j + 1 + i) - min j (j + 1 + i)) =
      xLogXStep K := by
    rw [← sum_range_succ_xLogXDiff K, Finset.sum_range_succ', xLogXDiff_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    omega
  rw [Finset.sum_range_add, ha, hb]
  congr 2
  omega

/-- **The jets to the differences inside a run of `m` blocks sum to `2 m log m`.** -/
theorem sum_sum_xLogXDiff_max_sub_min (m : ℕ) :
    ∑ j ∈ range m, ∑ l ∈ range m, xLogXDiff (max j l - min j l) = 2 * xLogX m := by
  have h0 : xLogX 0 = 0 := by simp [xLogX]
  have hstep : ∑ j ∈ range m, xLogXStep j = xLogX m := by
    have h := sum_range_xLogXStep 0 m
    simp only [zero_add] at h
    rw [h, h0, sub_zero]
  have hin : ∀ j ∈ range m, ∑ l ∈ range m, xLogXDiff (max j l - min j l) =
      xLogXStep j + xLogXStep (m - 1 - j) :=
    fun j hj => sum_range_xLogXDiff_max_sub_min (Finset.mem_range.mp hj)
  rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib,
    Finset.sum_range_reflect (fun j => xLogXStep j) m, hstep]
  ring

/-- **Inside a run of `m` blocks the couplings sum to at least `m log m`**: on the flat packet of
the run a completion is at most the sum of the self-pairings minus `m log m`. -/
theorem sum_neutralWithDiagonal_run_le (Q : ℕ) (d : ℕ → ℝ) (A m : ℕ) :
    ∑ j ∈ range m, ∑ l ∈ range m, neutralWithDiagonal Q d (A + j) (A + l) ≤
      ∑ j ∈ range m, d (A + j) - m * Real.log m := by
  have hterm : ∀ j l : ℕ, neutralWithDiagonal Q d (A + j) (A + l) ≤
      (if j = l then d (A + j) else 0) - xLogXDiff (max j l - min j l) / 2 := by
    intro j l
    unfold neutralWithDiagonal
    by_cases h : j = l
    · subst h
      exact le_of_eq (by
        rw [if_pos rfl, if_pos rfl, max_self, min_self, Nat.sub_self, xLogXDiff_zero, zero_div,
          sub_zero])
    · rw [if_neg (by omega), if_neg h]
      have h1 := neutralBlock_le_neg_xLogXDiff Q (a := A + j) (b := A + l) (by omega)
      have e : max (A + j) (A + l) - min (A + j) (A + l) = max j l - min j l := by omega
      rw [e] at h1
      linarith
  have hd : ∀ j ∈ range m, ∑ l ∈ range m, (if j = l then d (A + j) else 0) = d (A + j) :=
    fun j hj => by rw [Finset.sum_ite_eq, if_pos hj]
  have hD : ∑ j ∈ range m, ∑ l ∈ range m, xLogXDiff (max j l - min j l) / 2 =
      m * Real.log m := by
    have h2 : ∀ j ∈ range m, ∑ l ∈ range m, xLogXDiff (max j l - min j l) / 2 =
        (∑ l ∈ range m, xLogXDiff (max j l - min j l)) / 2 :=
      fun j _ => (Finset.sum_div _ _ _).symm
    rw [Finset.sum_congr rfl h2, ← Finset.sum_div, sum_sum_xLogXDiff_max_sub_min, xLogX]
    ring
  calc ∑ j ∈ range m, ∑ l ∈ range m, neutralWithDiagonal Q d (A + j) (A + l)
      ≤ ∑ j ∈ range m, ∑ l ∈ range m,
          ((if j = l then d (A + j) else 0) - xLogXDiff (max j l - min j l) / 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l
    _ = ∑ j ∈ range m, d (A + j) - m * Real.log m := by
        simp only [Finset.sum_sub_distrib]
        rw [Finset.sum_congr rfl hd, hD]

/-- **Two blocks without contact that are at least `m` apart are coupled by at most `2/m`.** -/
theorem neg_two_div_le_neutralBlock {Q a b m : ℕ} (hm : 1 ≤ m) (hab : a + m ≤ b)
    (hb : b < 2 * a) : -(2 / (m : ℝ)) ≤ neutralBlock Q a b := by
  have hlt : a < b := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := blockJet_le hlt
  have h2 : (m : ℝ) ≤ (b : ℝ) - a := by
    have h : ((a + m : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    push_cast at h
    linarith
  have h3 : 2 / ((b : ℝ) - a) ≤ 2 / (m : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hm0 h2
  rw [neutralBlock_of_lt hlt, floorContact_eq_zero_of_lt_two_mul hb]
  linarith

/-- **Two runs of `m` blocks, at least `m` blocks apart and without contact, are coupled by at
most `2m`.** -/
theorem abs_sum_neutralWithDiagonal_runs_le {Q A B m : ℕ} (d : ℕ → ℝ) (hm : 1 ≤ m)
    (hAB : A + 2 * m ≤ B) (hB : B + m ≤ 2 * A) :
    |∑ j ∈ range m, ∑ l ∈ range m, neutralWithDiagonal Q d (A + j) (B + l)| ≤ 2 * (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo : ∀ j ∈ range m, ∀ l ∈ range m,
      -(2 / (m : ℝ)) ≤ neutralWithDiagonal Q d (A + j) (B + l) := by
    intro j hj l hl
    have hj' := Finset.mem_range.mp hj
    have hl' := Finset.mem_range.mp hl
    rw [neutralWithDiagonal, if_neg (by omega)]
    exact neg_two_div_le_neutralBlock hm (by omega) (by omega)
  have hhi : ∀ j ∈ range m, ∀ l ∈ range m, neutralWithDiagonal Q d (A + j) (B + l) ≤ 0 := by
    intro j hj l _
    have hj' := Finset.mem_range.mp hj
    rw [neutralWithDiagonal, if_neg (by omega)]
    exact (neutralBlock_neg (by omega) Q).le
  have e : (m : ℝ) * (2 / (m : ℝ)) = 2 := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hm0.ne', mul_one]
  have hconst : ∑ _j ∈ range m, ∑ _l ∈ range m, -(2 / (m : ℝ)) = -(2 * (m : ℝ)) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul,
      mul_neg, e]
    ring
  rw [abs_le]
  constructor
  · rw [← hconst]
    exact Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl => hlo j hj l hl
  · exact (Finset.sum_nonpos fun j hj => Finset.sum_nonpos fun l hl => hhi j hj l hl).trans
      (by positivity)

/-! ### The law of two runs -/

/-- Two numbers below `−c < 0` have a product above every square that is at most `c²`. -/
theorem sq_lt_mul_of_lt_neg {c x y z : ℝ} (hc : 0 < c) (hx : x < -c) (hy : y < -c)
    (hz : z ^ 2 ≤ c ^ 2) : z ^ 2 < x * y := by
  nlinarith [mul_pos (show 0 < -c - x by linarith) (show 0 < -c - y by linarith),
    mul_pos hc (show 0 < -c - x by linarith), mul_pos hc (show 0 < -c - y by linarith)]

/-- **The law of two runs.** Let `(R, R + J]` be a window with `J ≤ R` and `G_d` a completion of
its couplings with at most one negative square. Of two runs of `m` blocks of the window that are
at least `m` blocks apart, one has self-pairings with the sum at least `m log m − 2m`. -/
theorem sum_selfPairing_ge_of_hermNegIndex_le_one {Q R J p q m : ℕ} (d : ℕ → ℝ) (hm : 1 ≤ m)
    (hpq : p + 2 * m ≤ q) (hq : q + m ≤ J) (hJ : J ≤ R)
    (h : hermNegIndex ((windowMatrix (neutralWithDiagonal Q d) R J).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1) :
    m * Real.log m - 2 * m ≤ ∑ j ∈ range m, d (R + p + j) ∨
      m * Real.log m - 2 * m ≤ ∑ j ∈ range m, d (R + q + j) := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨hp', hq'⟩ := hcon
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpJ : p + m ≤ J := by omega
  -- the two runs are negative below `−2m`
  have hxx : bilin (windowMatrix (neutralWithDiagonal Q d) R J)
      (fun i : Fin J => blockRun p m i) (fun i : Fin J => blockRun p m i) <
        -(2 * (m : ℝ)) := by
    rw [bilin_windowMatrix_blockRun _ R hpJ hpJ]
    have h1 := sum_neutralWithDiagonal_run_le Q d (R + p) m
    linarith
  have hyy : bilin (windowMatrix (neutralWithDiagonal Q d) R J)
      (fun i : Fin J => blockRun q m i) (fun i : Fin J => blockRun q m i) <
        -(2 * (m : ℝ)) := by
    rw [bilin_windowMatrix_blockRun _ R hq hq]
    have h1 := sum_neutralWithDiagonal_run_le Q d (R + q) m
    linarith
  -- and coupled by at most `2m`
  have hxy : |bilin (windowMatrix (neutralWithDiagonal Q d) R J)
      (fun i : Fin J => blockRun p m i) (fun i : Fin J => blockRun q m i)| ≤ 2 * (m : ℝ) := by
    rw [bilin_windowMatrix_blockRun _ R hpJ hq]
    exact abs_sum_neutralWithDiagonal_runs_le d hm (by omega) (by omega)
  have h2 := two_le_hermNegIndex_of_unbound_pair
    (G := windowMatrix (neutralWithDiagonal Q d) R J)
    (fun i j => neutralWithDiagonal_comm Q d _ _)
    (hxx.trans (by linarith))
    (sq_lt_mul_of_lt_neg (c := 2 * (m : ℝ)) (by positivity) hxx hyy
      (sq_le_sq' (abs_le.mp hxy).1 (abs_le.mp hxy).2))
  exact absurd (h2.trans h) (by norm_num)

/-- **A constant self-pairing is at least `log m − 2`.** If the completion of the couplings of a
window `(R, R + J]`, `3m ≤ J ≤ R`, by the constant self-pairing `c` has at most one negative
square, then `c ≥ log m − 2`. -/
theorem log_sub_two_le_of_hermNegIndex_le_one {Q R J m : ℕ} (c : ℝ) (hm : 1 ≤ m)
    (hmJ : 3 * m ≤ J) (hJ : J ≤ R)
    (h : hermNegIndex ((windowMatrix (neutralWithDiagonal Q fun _ => c) R J).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1) :
    Real.log m - 2 ≤ c := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := sum_selfPairing_ge_of_hermNegIndex_le_one (p := 0) (q := 2 * m) (fun _ => c) hm
    (by omega) (by omega) hJ h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, or_self] at h1
  by_contra hc
  rw [not_le] at hc
  nlinarith [mul_pos hm0 (sub_pos.mpr hc)]

/-- **No completion with self-pairings `≤ 0` has at most one negative square**, on a window
`(R, R + J]` with `R, J ≥ 24`. -/
theorem two_le_hermNegIndex_of_selfPairing_nonpos {Q R J : ℕ} (d : ℕ → ℝ) (hd : ∀ a, d a ≤ 0)
    (hR : 24 ≤ R) (hJ : 24 ≤ J) :
    2 ≤ hermNegIndex ((windowMatrix (neutralWithDiagonal Q d) R J).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) := by
  -- the first `24` blocks form a principal submatrix
  have hmono : hermNegIndex ((windowMatrix (neutralWithDiagonal Q d) R 24).map (↑) :
      Matrix (Fin 24) (Fin 24) ℂ) ≤
      hermNegIndex ((windowMatrix (neutralWithDiagonal Q d) R J).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) :=
    HeckeKreinToeplitz.hermNegIndex_submatrix_le
      ((windowMatrix (neutralWithDiagonal Q d) R J).map (↑) : Matrix (Fin J) (Fin J) ℂ)
      (Fin.castLE hJ)
  refine le_trans ?_ hmono
  by_contra hcon
  have h24 : hermNegIndex ((windowMatrix (neutralWithDiagonal Q d) R 24).map (↑) :
      Matrix (Fin 24) (Fin 24) ℂ) ≤ 1 := by omega
  -- two runs of eight blocks, eight blocks apart
  have h1 := sum_selfPairing_ge_of_hermNegIndex_le_one (p := 0) (q := 16) (m := 8) d
    (by norm_num) (by norm_num) (by norm_num) hR h24
  have hlog : (2 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    push_cast
    linarith
  have h8 : (0 : ℝ) < (8 : ℕ) * Real.log (8 : ℕ) - 2 * (8 : ℕ) := by
    push_cast
    linarith
  have hs : ∀ A : ℕ, ∑ j ∈ range 8, d (A + j) ≤ 0 := fun A =>
    Finset.sum_nonpos fun j _ => hd (A + j)
  rcases h1 with h1 | h1
  · exact absurd (h8.trans_le h1) (not_lt.mpr (hs _))
  · exact absurd (h8.trans_le h1) (not_lt.mpr (hs _))

/-- **The couplings of a window are not mixed areas.** A symmetric matrix `M` with the couplings
`−N(a, b)` of the blocks of a window `(R, R + J]`, `R, J ≥ 24`, off the diagonal and nonnegative
self-pairings has two positive squares. So `M` is not a matrix of mixed areas of planar convex
bodies (Minkowski's inequality), nor of pairings of classes of nonnegative self-pairing on a
surface (the Hodge index theorem), whatever the self-pairings. -/
theorem two_le_hermNegIndex_neg_of_couplings {Q R J : ℕ} (hR : 24 ≤ R) (hJ : 24 ≤ J)
    (M : Matrix (Fin J) (Fin J) ℝ)
    (hoff : ∀ i j : Fin J, i ≠ j → M i j = blockWeight Q (R + i) (R + j))
    (hdiag : ∀ i, 0 ≤ M i i) :
    2 ≤ hermNegIndex ((-M).map (↑) : Matrix (Fin J) (Fin J) ℂ) := by
  let d : ℕ → ℝ := fun a => if h : a - R < J then -M ⟨a - R, h⟩ ⟨a - R, h⟩ else 0
  have hd : ∀ a, d a ≤ 0 := by
    intro a
    show (if h : a - R < J then -M ⟨a - R, h⟩ ⟨a - R, h⟩ else 0) ≤ 0
    split_ifs with h
    · exact neg_nonpos.mpr (hdiag _)
    · exact le_rfl
  have hM : -M = windowMatrix (neutralWithDiagonal Q d) R J := by
    ext i j
    show -M i j = neutralWithDiagonal Q d (R + i) (R + j)
    unfold neutralWithDiagonal
    by_cases hij : i = j
    · subst hij
      have h : R + (i : ℕ) - R < J := by
        have := i.2
        omega
      have e : (⟨R + (i : ℕ) - R, h⟩ : Fin J) = i :=
        Fin.ext (Nat.add_sub_cancel_left R (i : ℕ))
      rw [if_pos rfl]
      show -M i i =
        if h : R + (i : ℕ) - R < J then -M ⟨R + (i : ℕ) - R, h⟩ ⟨R + (i : ℕ) - R, h⟩ else 0
      rw [dif_pos h, e]
    · rw [if_neg (fun h => hij (Fin.ext (Nat.add_left_cancel h))), hoff i j hij, blockWeight,
        neg_neg]
  rw [hM]
  exact two_le_hermNegIndex_of_selfPairing_nonpos d hd hR hJ

/-! ### The rate is attained by the windows -/

/-- The self-pairing of a block is at most its density. -/
theorem neutralBlock_self_le (Q : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    neutralBlock Q a a ≤
      xLogXStep a - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := by
  have h1 := xLogXDiff_pos (n := a + a + 1) (by omega)
  have hJ : 0 ≤ blockJet a a := by
    unfold blockJet
    rw [Nat.sub_self, xLogXDiff_zero]
    linarith
  rw [neutralBlock, blockMatrix_self ha, blockDensity, xLogXStep]
  linarith

/-- **The self-pairings of a run of `m` blocks below `6m` sum to at most `m log m + m/2`.** -/
theorem sum_neutralBlock_self_le (Q : ℕ) {A m : ℕ} (hA : 1 ≤ A) (hm : 1 ≤ m)
    (hAm : A + m ≤ 6 * m) :
    ∑ j ∈ range m, neutralBlock Q (A + j) (A + j) ≤ m * Real.log m + m / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h4 : Real.log 6 ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have h5 := Real.one_half_lt_eulerMascheroniConstant
  have hterm : ∀ j ∈ range m, neutralBlock Q (A + j) (A + j) ≤ Real.log m + 1 / 2 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have h1 := neutralBlock_self_le Q (a := A + j) (by omega)
    have h2 := xLogXStep_le (A + j)
    have h3 : Real.log (((A + j : ℕ) : ℝ) + 1) ≤ Real.log 6 + Real.log m := by
      rw [← Real.log_mul (by norm_num) hm0.ne']
      refine Real.log_le_log (by positivity) ?_
      have h : ((A + j + 1 : ℕ) : ℝ) ≤ ((6 * m : ℕ) : ℝ) := by
        exact_mod_cast (by omega : A + j + 1 ≤ 6 * m)
      push_cast at h ⊢
      linarith
    linarith
  calc ∑ j ∈ range m, neutralBlock Q (A + j) (A + j)
      ≤ ∑ _j ∈ range m, (Real.log m + 1 / 2) := Finset.sum_le_sum hterm
    _ = m * Real.log m + m / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- **The windows attain the logarithmic rate.** The neutral part of the dyadic window
`(3m, 6m]` is the completion of its couplings by its own self-pairings, and it has at most one
negative square. -/
theorem hermNegIndex_neutralWithDiagonal_self_le_one {Q m : ℕ} (hm : 1 ≤ m) (hQ : 2 ≤ Q) :
    hermNegIndex ((windowMatrix (neutralWithDiagonal Q fun a => neutralBlock Q a a) (3 * m)
      (3 * m)).map (↑) : Matrix (Fin (3 * m)) (Fin (3 * m)) ℂ) ≤ 1 := by
  have e : windowMatrix (neutralWithDiagonal Q fun a => neutralBlock Q a a) (3 * m) (3 * m) =
      neutralWindow Q (3 * m) (3 * m) := by
    ext i j
    exact neutralWithDiagonal_self Q _ _
  rw [e]
  exact hermNegIndex_neutralWindow_le_one (by omega) (by omega) hQ

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
