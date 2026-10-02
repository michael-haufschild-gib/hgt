import GaloisForLFunctions.HTGeometry.HermiteRealRoots
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Topology.Algebra.Polynomial

/-!
# The forward heat polynomials change sign at `k` separated points

The forward heat evolution of `σ^k` is
`Q_k(σ) = Σ_{2m ≤ k} (−1)^m k!/(m!(k−2m)!) σ^{k−2m} = √2^k Heₖ(σ/√2)` (`eval_heatPoly_eq`), by the
explicit coefficients of the Hermite polynomials (`realHermite_eq_sum`) and
`(2m)! = 2^m m! (2m−1)‼`.  Since `Heₖ` has `k` simple real roots, `Q_k` has `k` real roots at which it
changes sign, and the sign changes can be taken on pairwise disjoint intervals
(`exists_heatPoly_sign_changes`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficient `(−1)^m (2m−1)‼ C(k, 2m)` of `X^{k−2m}` in `Heₖ`. -/
def hermiteCoeff (k m : ℕ) : ℝ := (-1) ^ m * ((2 * m - 1).doubleFactorial : ℝ) * (k.choose (2 * m) : ℝ)

theorem realHermite_eq_sum (k : ℕ) :
    realHermite k = ∑ m ∈ range (k / 2 + 1), C (hermiteCoeff k m) * X ^ (k - 2 * m) := by
  ext i
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [realHermite, coeff_map, coeff_hermite]
  by_cases hi : Even (k + i) ∧ i ≤ k
  · obtain ⟨hev, hik⟩ := hi
    obtain ⟨m, hm⟩ : ∃ m, k - i = 2 * m := by
      have h2 := hev
      rw [Nat.even_add, ← Nat.even_sub hik] at h2
      obtain ⟨m, hm⟩ := h2
      exact ⟨m, by omega⟩
    rw [if_pos hev, Finset.sum_eq_single m]
    · rw [if_pos (show i = k - 2 * m by omega)]
      simp only [hermiteCoeff, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast]
      rw [show (k - i) / 2 = m by omega, show k - i - 1 = 2 * m - 1 by omega,
        show k.choose i = k.choose (2 * m) by rw [← hm, Nat.choose_symm hik]]
    · intro b hb hbm
      simp only [mem_range] at hb
      rw [if_neg (by omega)]
    · intro hm'
      simp only [mem_range, not_lt] at hm'
      omega
  · rw [Finset.sum_eq_zero]
    · by_cases hev : Even (k + i)
      · have hik : k < i := by
          by_contra h
          exact hi ⟨hev, by omega⟩
        rw [if_pos hev, Nat.choose_eq_zero_of_lt hik]
        simp
      · rw [if_neg hev]; simp
    · intro m hm
      simp only [mem_range] at hm
      rw [if_neg]
      intro hik
      apply hi
      refine ⟨?_, by omega⟩
      rw [hik, show k + (k - 2 * m) = 2 * (k - m) by omega]
      exact even_two_mul _

/-- The forward heat polynomial `Q_k(x) = Σ_{2m ≤ k} (−1)^m k!/(m!(k−2m)!) x^{k−2m}`. -/
def heatPoly (k : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ range (k / 2 + 1),
    ((-1) ^ m * (k.factorial : ℝ) / ((m.factorial : ℝ) * ((k - 2 * m).factorial : ℝ))) *
      x ^ (k - 2 * m)

theorem hermiteCoeff_mul_two_pow {k m : ℕ} (hm : 2 * m ≤ k) :
    hermiteCoeff k m * 2 ^ m =
      (-1) ^ m * (k.factorial : ℝ) / ((m.factorial : ℝ) * ((k - 2 * m).factorial : ℝ)) := by
  have hch : (k.choose (2 * m) : ℝ) * ((2 * m).factorial : ℝ) * ((k - 2 * m).factorial : ℝ) =
      k.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have hdf : ((2 * m).factorial : ℝ) = 2 ^ m * (m.factorial : ℝ) * ((2 * m - 1).doubleFactorial : ℝ) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * m - 1)
      rw [show 2 * m - 1 + 1 = 2 * m by omega, Nat.doubleFactorial_two_mul] at h1
      rw [h1]; push_cast; ring
  have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hkf : ((k - 2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [hermiteCoeff, eq_div_iff (mul_ne_zero hmf hkf), ← hch, hdf]
  ring

/-- `Q_k(x) = √2^k Heₖ(x/√2)`. -/
theorem eval_heatPoly_eq (k : ℕ) (x : ℝ) :
    heatPoly k x = Real.sqrt 2 ^ k * (realHermite k).eval (x / Real.sqrt 2) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [realHermite_eq_sum, eval_finsetSum, Finset.mul_sum, heatPoly]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mem_range] at hm
  have hm2 : 2 * m ≤ k := by omega
  rw [eval_mul, eval_C, eval_pow, eval_X, ← hermiteCoeff_mul_two_pow hm2]
  have hk : Real.sqrt 2 ^ k = Real.sqrt 2 ^ (k - 2 * m) * 2 ^ m := by
    rw [show (2 : ℝ) ^ m = Real.sqrt 2 ^ (2 * m) by rw [pow_mul, hs2], ← pow_add,
      show k - 2 * m + 2 * m = k by omega]
  rw [hk, div_pow]
  field_simp

/-- A real polynomial changes sign across a root where its derivative does not vanish, on every
small symmetric interval. -/
theorem exists_sign_change_of_derivative_ne_zero {p : ℝ[X]} {ρ : ℝ} (hρ : p.IsRoot ρ)
    (hd : (derivative p).eval ρ ≠ 0) :
    ∃ η, 0 < η ∧ ∀ ε, 0 < ε → ε < η → p.eval (ρ - ε) * p.eval (ρ + ε) < 0 := by
  obtain ⟨r, hr⟩ : X - C ρ ∣ p := dvd_iff_isRoot.mpr hρ
  have hrρ : r.eval ρ = (derivative p).eval ρ := by
    rw [hr, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
    simp
  have hcont : ContinuousAt (fun x => r.eval x) ρ := r.continuous.continuousAt
  have hne : r.eval ρ ≠ 0 := hrρ ▸ hd
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.mp hcont (|r.eval ρ| / 2) (by positivity)
  have hsign : ∀ y, |y - ρ| < η → 0 < r.eval y * r.eval ρ := by
    intro y hy
    have h := hball (by rw [Real.dist_eq]; exact hy)
    rw [Real.dist_eq] at h
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · rw [abs_of_neg hneg] at h
      have : r.eval y < 0 := by
        have := (abs_lt.mp h).2; linarith
      nlinarith
    · rw [abs_of_pos hpos] at h
      have : 0 < r.eval y := by
        have := (abs_lt.mp h).1; linarith
      nlinarith
  refine ⟨η, hη, fun ε hε hεη => ?_⟩
  have h1 := hsign (ρ - ε) (by rw [show ρ - ε - ρ = -ε by ring, abs_neg, abs_of_pos hε]; exact hεη)
  have h2 := hsign (ρ + ε) (by rw [show ρ + ε - ρ = ε by ring, abs_of_pos hε]; exact hεη)
  have hρ2 : 0 < r.eval ρ ^ 2 := by positivity
  have hprod : 0 < r.eval (ρ - ε) * r.eval (ρ + ε) := by
    have e : r.eval (ρ - ε) * r.eval (ρ + ε) * r.eval ρ ^ 2 =
        (r.eval (ρ - ε) * r.eval ρ) * (r.eval (ρ + ε) * r.eval ρ) := by ring
    have h := mul_pos h1 h2
    rw [← e] at h
    nlinarith
  rw [hr, eval_mul, eval_mul]
  simp only [eval_sub, eval_X, eval_C]
  have e2 : (ρ - ε - ρ) * r.eval (ρ - ε) * ((ρ + ε - ρ) * r.eval (ρ + ε)) =
      -(ε ^ 2) * (r.eval (ρ - ε) * r.eval (ρ + ε)) := by ring
  rw [e2]
  have : 0 < ε ^ 2 := by positivity
  nlinarith

/-- At a root of a polynomial with no repeated roots the derivative does not vanish. -/
theorem derivative_eval_ne_zero_of_roots_nodup {p : ℝ[X]} (hp : p ≠ 0) (hnd : p.roots.Nodup)
    {ρ : ℝ} (hρ : p.IsRoot ρ) : (derivative p).eval ρ ≠ 0 := by
  classical
  intro h0
  have hmem : ρ ∈ p.roots := (mem_roots hp).mpr hρ
  have hcount : p.rootMultiplicity ρ = 1 := by
    rw [← count_roots]; exact Multiset.count_eq_one_of_mem hnd hmem
  have hder := derivative_rootMultiplicity_of_root hρ
  rw [hcount] at hder
  by_cases hd0 : derivative p = 0
  · rw [eq_C_of_derivative_eq_zero hd0] at hρ hp
    simp only [IsRoot, eval_C] at hρ
    exact hp (by rw [hρ, C_0])
  · have := (rootMultiplicity_pos hd0).mpr h0
    omega

/-- **Sign changes of the forward heat polynomial.** `Q_k` has `k` real points at which it changes
sign on a common interval half-width `ε`, and these points are more than `2ε` apart. -/
theorem exists_heatPoly_sign_changes (k : ℕ) :
    ∃ Z : Finset ℝ, Z.card = k ∧ ∃ ε > 0,
      (∀ ρ ∈ Z, heatPoly k (ρ - ε) * heatPoly k (ρ + ε) < 0) ∧
      (∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → 2 * ε < |ρ - ρ'|) := by
  classical
  obtain ⟨hnd, hcard⟩ := realHermite_roots_nodup_card k
  set R := (realHermite k).roots.toFinset with hR
  have hRcard : R.card = k := by rw [hR, Multiset.toFinset_card_of_nodup hnd, hcard]
  have hs : 0 < Real.sqrt 2 := by positivity
  set Z := R.image (fun y => Real.sqrt 2 * y) with hZ
  have hinj : Function.Injective (fun y : ℝ => Real.sqrt 2 * y) :=
    fun a b h => mul_left_cancel₀ hs.ne' h
  have hZcard : Z.card = k := by rw [hZ, Finset.card_image_of_injective _ hinj, hRcard]
  refine ⟨Z, hZcard, ?_⟩
  -- the sign-change radius at every root of `Heₖ`
  have hη : ∀ y ∈ R, ∃ η, 0 < η ∧ ∀ ε, 0 < ε → ε < η →
      (realHermite k).eval (y - ε) * (realHermite k).eval (y + ε) < 0 := by
    intro y hy
    have hroot : (realHermite k).IsRoot y := (mem_roots (realHermite_ne_zero k)).mp
      (Multiset.mem_toFinset.mp hy)
    exact exists_sign_change_of_derivative_ne_zero hroot
      (derivative_eval_ne_zero_of_roots_nodup (realHermite_ne_zero k) hnd hroot)
  choose! η hηpos hηsign using hη
  rcases R.eq_empty_or_nonempty with hRe | hRne
  · refine ⟨1, one_pos, fun ρ hρ => ?_, fun ρ hρ => ?_⟩ <;> simp [hZ, hRe] at hρ
  set η₀ := R.inf' hRne η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff hRne).mpr fun y hy => hηpos y hy
  -- a positive lower bound for the separation of `Z`
  obtain ⟨d, hd, hdsep⟩ : ∃ d, 0 < d ∧ ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → d ≤ |ρ - ρ'| := by
    rcases (Z.offDiag).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun ρ hρ ρ' hρ' hne => ?_⟩
      have : (ρ, ρ') ∈ Z.offDiag := Finset.mem_offDiag.mpr ⟨hρ, hρ', hne⟩
      rw [he] at this; simp at this
    · refine ⟨Z.offDiag.inf' hne (fun pr => |pr.1 - pr.2|), ?_, fun ρ hρ ρ' hρ' hne' => ?_⟩
      · refine (Finset.lt_inf'_iff hne).mpr fun pr hpr => ?_
        obtain ⟨-, -, hpr⟩ := Finset.mem_offDiag.mp hpr
        exact abs_pos.mpr (sub_ne_zero.mpr hpr)
      · have hmem : (ρ, ρ') ∈ Z.offDiag := Finset.mem_offDiag.mpr ⟨hρ, hρ', hne'⟩
        exact Finset.inf'_le (fun pr : ℝ × ℝ => |pr.1 - pr.2|) hmem
  set ε := min (Real.sqrt 2 * η₀ / 2) (d / 4)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε, hε, fun ρ hρ => ?_, fun ρ hρ ρ' hρ' hne => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hρ
    have hεy : ε / Real.sqrt 2 < η y := by
      rw [div_lt_iff₀ hs]
      have h1 : ε ≤ Real.sqrt 2 * η₀ / 2 := min_le_left _ _
      have h2 : η₀ ≤ η y := Finset.inf'_le _ hy
      nlinarith
    have h := hηsign y hy (ε / Real.sqrt 2) (by positivity) hεy
    rw [eval_heatPoly_eq, eval_heatPoly_eq]
    have e1 : (Real.sqrt 2 * y - ε) / Real.sqrt 2 = y - ε / Real.sqrt 2 := by field_simp
    have e2 : (Real.sqrt 2 * y + ε) / Real.sqrt 2 = y + ε / Real.sqrt 2 := by field_simp
    rw [e1, e2]
    have hpos : 0 < Real.sqrt 2 ^ k * Real.sqrt 2 ^ k := by positivity
    have e3 : Real.sqrt 2 ^ k * (realHermite k).eval (y - ε / Real.sqrt 2) *
        (Real.sqrt 2 ^ k * (realHermite k).eval (y + ε / Real.sqrt 2)) =
        (Real.sqrt 2 ^ k * Real.sqrt 2 ^ k) * ((realHermite k).eval (y - ε / Real.sqrt 2) *
          (realHermite k).eval (y + ε / Real.sqrt 2)) := by ring
    rw [e3]
    exact mul_neg_of_pos_of_neg hpos h
  · have h1 := hdsep ρ hρ ρ' hρ' hne
    have h2 : ε ≤ d / 4 := min_le_right _ _
    linarith

end

end GaloisForLFunctions.HTGeometry
