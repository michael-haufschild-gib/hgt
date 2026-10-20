import GaloisForLFunctions.BezoutValuationIncidence.SelbergSupportExactRecurrenceComplexity
import GaloisForLFunctions.BezoutValuationIncidence.QuadraticWindowHorizonSharpnessAtCommonReturns
import GaloisForLFunctions.RHTower.Sieve.LargeSieveSeparated
import GaloisForLFunctions.RHTower.Sieve.GeometricSumBound

/-!
# The window sandwich at quadratic order

Every level-`N` response is the exponential sum `s(k) = Σ_{ζ ∈ T_N} Y(ord ζ) ζ^k` over the roots of
unity of order at most `N`, and these frequencies are `1/N²`-separated on the circle, since a
nontrivial `m`-th root of unity sits at distance at least `1/m` from `1`. Smoothing a window by a
trapezoid — the average of `L` box windows of length `K'` — turns the off-diagonal kernel into the
product of two geometric sums, of size `≤ 4 / |z - 1|²`. Squared reciprocal distances of a
`δ`-separated family sum to `≤ 4/δ²` with no logarithm, so

`|Σ_{i<L} Σ_{j<K'} |u(T₀+i+j)|² - L K' Σ |a|²| ≤ N⁴ Σ |a|²`

for every exponential sum `u(k) = Σ_{ζ ∈ T_N} a(ζ) ζ^k`; a response has `Σ |a|² = Q_Sel`. A box window is squeezed between trapezoids with ramps of length `L = N²`, which gives the
two-sided window sandwich

`|Σ_{A<k≤A+K} (s(k) - κ)² - K ((H - κ)² + V)| ≤ (2N² - 1)((H - κ)² + V)`

at every phase, length and offset. The constant of order `N² log N` from the period-cell argument
loses only a logarithm, and the common-return spike shows that no constant below
`N² / (1 + log N)³` up to lower order works: the optimal window sandwich constant has order
`N^{2+o(1)}`.
-/

open Finset GaloisForLFunctions.BiScaleUncertainty RHTower.Sieve
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Separation of the response frequencies -/

/-- A nontrivial `m`-th root of unity lies at circle distance at least `1/m` from `1`. -/
theorem one_div_le_toIntDist_of_circleFreq_pow {x : ℝ} {m : ℕ} (hm : 0 < m)
    (hpow : circleFreq x ^ m = 1) (hne : circleFreq x ≠ 1) : 1 / (m : ℝ) ≤ toIntDist x := by
  rw [circleFreq, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hpow
  obtain ⟨n, hn⟩ := hpow
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmx : (m : ℝ) * x = n := by
    have h := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at h
    have hpi := Real.pi_pos
    have h2 : ((m : ℝ) * x - n) * (2 * Real.pi) = 0 := by linarith
    have := (mul_eq_zero.mp h2).resolve_right (by positivity)
    linarith
  by_contra hlt
  push Not at hlt
  have habs : |((n - m * round x : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [← hmx, ← mul_sub, abs_mul, abs_of_pos hm0]
    have h1 : |x - (round x : ℝ)| < 1 / m := hlt
    calc (m : ℝ) * |x - (round x : ℝ)| < m * (1 / m) := mul_lt_mul_of_pos_left h1 hm0
      _ = 1 := by field_simp
  have hint : n - m * round x = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  have hxr : x = round x := by
    have h1 : (m : ℝ) * x = m * (round x : ℝ) := by
      rw [hmx]
      exact_mod_cast sub_eq_zero.mp hint
    exact mul_left_cancel₀ hm0.ne' h1
  apply hne
  rw [circleFreq, hxr]
  convert Complex.exp_int_mul_two_pi_mul_I (round x) using 2
  push_cast
  ring

/-- The angle of a point of the circle, in full turns. -/
def rootAngle (ζ : ℂ) : ℝ := Complex.arg ζ / (2 * Real.pi)

theorem circleFreq_rootAngle {ζ : ℂ} (hζ : ‖ζ‖ = 1) : circleFreq (rootAngle ζ) = ζ := by
  have h := Complex.norm_mul_exp_arg_mul_I ζ
  rw [hζ, Complex.ofReal_one, one_mul] at h
  have harg : 2 * Real.pi * rootAngle ζ = Complex.arg ζ := by
    unfold rootAngle
    field_simp
  rw [circleFreq, harg]
  exact h

theorem norm_eq_one_of_mem_responseRoots {N : ℕ} {ζ : ℂ} (hζ : ζ ∈ responseRoots N) :
    ‖ζ‖ = 1 := by
  obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp hζ
  have hd0 := (mem_Icc.mp hd).1
  exact Complex.norm_eq_one_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hd0 1).mp hζd) (by omega)

theorem conj_mul_self_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) : conj ζ * ζ = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]
  norm_num

/-- **Farey separation of the response frequencies.** Distinct roots of unity of order at most
`N` are `1/N²` apart on the circle. -/
theorem responseRoots_separated {N : ℕ} {ζ ξ : ℂ} (hζ : ζ ∈ responseRoots N)
    (hξ : ξ ∈ responseRoots N) (hne : ζ ≠ ξ) :
    1 / (N : ℝ) ^ 2 ≤ toIntDist (rootAngle ξ - rootAngle ζ) := by
  obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp hζ
  obtain ⟨d', hd', hξd⟩ := mem_biUnion.mp hξ
  have hd0 := (mem_Icc.mp hd).1
  have hd0' := (mem_Icc.mp hd').1
  have hpζ := (Polynomial.mem_nthRootsFinset hd0 1).mp hζd
  have hpξ := (Polynomial.mem_nthRootsFinset hd0' 1).mp hξd
  have hnζ := norm_eq_one_of_mem_responseRoots hζ
  have hcf : circleFreq (rootAngle ξ - rootAngle ζ) = conj ζ * ξ := by
    rw [← conj_circleFreq_mul, circleFreq_rootAngle hnζ,
      circleFreq_rootAngle (norm_eq_one_of_mem_responseRoots hξ)]
  have hpow : circleFreq (rootAngle ξ - rootAngle ζ) ^ (d * d') = 1 := by
    rw [hcf, mul_pow, ← map_pow, pow_mul, hpζ, one_pow, map_one, one_mul, mul_comm d d', pow_mul,
      hpξ, one_pow]
  have hne1 : circleFreq (rootAngle ξ - rootAngle ζ) ≠ 1 := by
    rw [hcf]
    intro h
    apply hne
    calc ζ = ζ * (conj ζ * ξ) := by rw [h, mul_one]
      _ = (conj ζ * ζ) * ξ := by ring
      _ = ξ := by rw [conj_mul_self_of_norm_eq_one hnζ, one_mul]
  refine le_trans ?_ (one_div_le_toIntDist_of_circleFreq_pow (Nat.mul_pos hd0 hd0') hpow hne1)
  have hdN : (d : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hd).2
  have hdN' : (d' : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hd').2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hd1' : (1 : ℝ) ≤ d' := by exact_mod_cast hd0'
  have hprod : ((d * d' : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    push_cast
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) hprod

/-! ## §2. Squared reciprocal distances of a separated family -/

theorem sum_Icc_one_div_sq_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Icc 1 M, 1 / (k : ℝ) ^ 2 ≤ 2 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have key : 1 / ((M + 1 : ℕ) : ℝ) ^ 2 + 1 / ((M + 1 : ℕ) : ℝ) ≤ 1 / (M : ℝ) := by
      push_cast
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- Squared reciprocal circle distances to a `δ`-separated family sum to at most `4/δ²`. -/
theorem sum_erase_one_div_toIntDist_sq_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a)) {r : ι} (hr : r ∈ s) :
    ∑ t ∈ s.erase r, 1 / toIntDist (lam t - lam r) ^ 2 ≤ 4 / δ ^ 2 := by
  classical
  set M : ℕ := ⌈1 / (2 * δ)⌉₊
  have hM : 1 / (2 * δ) ≤ (M : ℝ) := Nat.le_ceil _
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℝ) ≤ 1 / (2 * δ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact_mod_cast h1.trans hM
  set F : ι → ℕ × Bool :=
    fun t => (levelOf δ (lam t - lam r), decide (0 ≤ reduce (lam t - lam r))) with hF
  have hsep' : ∀ t ∈ s.erase r, δ ≤ toIntDist (lam t - lam r) := fun t ht =>
    hsep r hr t (mem_of_mem_erase ht) (Ne.symm (ne_of_mem_erase ht))
  -- termwise: the squared reciprocal distance is at most `δ⁻²` times the squared reciprocal level
  have hterm : ∀ t ∈ s.erase r,
      1 / toIntDist (lam t - lam r) ^ 2 ≤ (1 / δ ^ 2) * (1 / ((F t).1 : ℝ) ^ 2) := by
    intro t ht
    have hlev1 : 1 ≤ levelOf δ (lam t - lam r) := one_le_levelOf hδ0 (hsep' t ht)
    have hlevR : (1 : ℝ) ≤ (levelOf δ (lam t - lam r) : ℝ) := by exact_mod_cast hlev1
    have hle := levelOf_mul_le (δ := δ) (x := lam t - lam r) hδ0
    have hpos : (0 : ℝ) < (levelOf δ (lam t - lam r) : ℝ) * δ := by positivity
    have hsq : ((levelOf δ (lam t - lam r) : ℝ) * δ) ^ 2 ≤ toIntDist (lam t - lam r) ^ 2 :=
      pow_le_pow_left₀ hpos.le hle 2
    have hmain := one_div_le_one_div_of_le (by positivity) hsq
    calc 1 / toIntDist (lam t - lam r) ^ 2
        ≤ 1 / ((levelOf δ (lam t - lam r) : ℝ) * δ) ^ 2 := hmain
      _ = (1 / δ ^ 2) * (1 / ((F t).1 : ℝ) ^ 2) := by
        simp only [hF]
        field_simp
  -- the level–side pair separates the family
  have hinj : ∀ a ∈ s.erase r, ∀ b ∈ s.erase r, F a = F b → a = b := by
    intro a ha b hb hab
    by_contra hne
    simp only [hF, Prod.mk.injEq, decide_eq_decide] at hab
    obtain ⟨hlev, hside⟩ := hab
    have hla := levelOf_mul_le (δ := δ) (x := lam a - lam r) hδ0
    have hlb := levelOf_mul_le (δ := δ) (x := lam b - lam r) hδ0
    have hua := lt_levelOf_succ_mul (δ := δ) (x := lam a - lam r) hδ0
    have hub := lt_levelOf_succ_mul (δ := δ) (x := lam b - lam r) hδ0
    rw [hlev] at hla hua
    have hgap : |reduce (lam a - lam r) - reduce (lam b - lam r)| < δ := by
      have hda : |reduce (lam a - lam r)| = toIntDist (lam a - lam r) := rfl
      have hdb : |reduce (lam b - lam r)| = toIntDist (lam b - lam r) := rfl
      rcases le_or_gt 0 (reduce (lam a - lam r)) with hpa | hna
      · have hpb : 0 ≤ reduce (lam b - lam r) := hside.mp hpa
        rw [abs_of_nonneg hpa] at hda
        rw [abs_of_nonneg hpb] at hdb
        rw [abs_lt]
        constructor <;> linarith
      · have hnb : reduce (lam b - lam r) < 0 := by
          by_contra hcon
          exact absurd (hside.mpr (not_lt.mp hcon)) (not_le.mpr hna)
        rw [abs_of_neg hna] at hda
        rw [abs_of_neg hnb] at hdb
        rw [abs_lt]
        constructor <;> linarith
    have hclose := toIntDist_sub_lt (u := lam a - lam r) (v := lam b - lam r) (δ := δ) hδ hgap
    have heq : (lam a - lam r) - (lam b - lam r) = lam a - lam b := by ring
    rw [heq] at hclose
    have hfar : δ ≤ toIntDist (lam a - lam b) :=
      hsep b (mem_of_mem_erase hb) a (mem_of_mem_erase ha) (Ne.symm hne)
    linarith
  have himg : (s.erase r).image F ⊆ Icc 1 M ×ˢ (univ : Finset Bool) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨one_le_levelOf hδ0 (hsep' t ht), levelOf_le hδ0 hM⟩,
      mem_univ _⟩
  have hrect : ∑ p ∈ Icc 1 M ×ˢ (univ : Finset Bool), 1 / ((p.1 : ℕ) : ℝ) ^ 2 =
      2 * ∑ k ∈ Icc 1 M, 1 / (k : ℝ) ^ 2 := by
    rw [sum_product, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
    ring
  have hH := sum_Icc_one_div_sq_le hM1
  have hMpos : (0 : ℝ) < 1 / (M : ℝ) := by
    have : (0 : ℝ) < M := by exact_mod_cast hM1
    positivity
  calc ∑ t ∈ s.erase r, 1 / toIntDist (lam t - lam r) ^ 2
      ≤ ∑ t ∈ s.erase r, (1 / δ ^ 2) * (1 / ((F t).1 : ℝ) ^ 2) := sum_le_sum hterm
    _ = (1 / δ ^ 2) * ∑ p ∈ (s.erase r).image F, 1 / ((p.1 : ℕ) : ℝ) ^ 2 := by
        rw [← mul_sum, sum_image hinj]
    _ ≤ (1 / δ ^ 2) * ∑ p ∈ Icc 1 M ×ˢ (univ : Finset Bool), 1 / ((p.1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity) (by positivity)
    _ ≤ 4 / δ ^ 2 := by
        rw [hrect]
        have : (1 / δ ^ 2) * (2 * ∑ k ∈ Icc 1 M, 1 / (k : ℝ) ^ 2) ≤ (1 / δ ^ 2) * 4 :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith [show (1 / δ ^ 2) * 4 = 4 / δ ^ 2 by ring]

theorem toIntDist_neg (x : ℝ) : toIntDist (-x) = toIntDist x := by
  unfold toIntDist
  apply le_antisymm
  · calc |-x - (round (-x) : ℝ)| ≤ |-x - ((-round x : ℤ) : ℝ)| := round_le (-x) (-round x)
      _ = |x - (round x : ℝ)| := by
        rw [← abs_neg]
        push_cast
        ring_nf
  · calc |x - (round x : ℝ)| ≤ |x - ((-round (-x) : ℤ) : ℝ)| := round_le x (-round (-x))
      _ = |-x - (round (-x) : ℝ)| := by
        rw [← abs_neg]
        push_cast
        ring_nf

/-! ## §3. Trapezoid smoothing of an exponential sum -/

/-- The trapezoid kernel is the product of two geometric sums. -/
theorem sum_range_sum_range_pow (z : ℂ) (T₀ L K : ℕ) :
    ∑ i ∈ range L, ∑ j ∈ range K, z ^ (T₀ + i + j) =
      z ^ T₀ * ((∑ i ∈ range L, z ^ i) * ∑ j ∈ range K, z ^ j) := by
  rw [sum_mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_add]
  ring

/-- `‖Σ a(ζ) ζ^k‖²` as a double sum over pairs of frequencies. -/
theorem norm_sq_sum_mul_pow (T : Finset ℂ) (a : ℂ → ℂ) (k : ℕ) :
    ((‖∑ ζ ∈ T, a ζ * ζ ^ k‖ ^ 2 : ℝ) : ℂ) =
      ∑ ζ ∈ T, ∑ ξ ∈ T, a ζ * conj (a ξ) * (ζ * conj ξ) ^ k := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, sum_mul_sum]
  refine sum_congr rfl fun ζ _ => sum_congr rfl fun ξ _ => ?_
  rw [map_mul, map_pow, mul_pow]
  ring

/-- **Trapezoid-smoothed dual large sieve with exact main term.** For unit frequencies whose
angles are `δ`-separated, the average of `L` box windows of length `K` of `|Σ a(ζ) ζ^k|²` is
`L K Σ |a|²` up to `Σ |a|² / δ²`, uniformly in the phase. -/
theorem abs_trapezoid_sum_sub_le {T : Finset ℂ} (a : ℂ → ℂ) (θ : ℂ → ℝ)
    (hθ : ∀ ζ ∈ T, circleFreq (θ ζ) = ζ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ ζ ∈ T, ∀ ξ ∈ T, ζ ≠ ξ → δ ≤ toIntDist (θ ξ - θ ζ)) (T₀ L K : ℕ) :
    |∑ i ∈ range L, ∑ j ∈ range K, ‖∑ ζ ∈ T, a ζ * ζ ^ (T₀ + i + j)‖ ^ 2 -
        L * K * ∑ ζ ∈ T, ‖a ζ‖ ^ 2| ≤ (∑ ζ ∈ T, ‖a ζ‖ ^ 2) / δ ^ 2 := by
  classical
  have hnorm : ∀ ζ ∈ T, ‖ζ‖ = 1 := fun ζ hζ => by rw [← hθ ζ hζ]; exact norm_circleFreq _
  set G : ℂ → ℂ := fun z => z ^ T₀ * ((∑ i ∈ range L, z ^ i) * ∑ j ∈ range K, z ^ j) with hG
  set Off : ℂ := ∑ ζ ∈ T, ∑ ξ ∈ T.erase ζ, a ζ * conj (a ξ) * G (ζ * conj ξ) with hOff
  -- the smoothed sum is the diagonal plus the off-diagonal kernel
  have hexp : ((∑ i ∈ range L, ∑ j ∈ range K,
      ‖∑ ζ ∈ T, a ζ * ζ ^ (T₀ + i + j)‖ ^ 2 : ℝ) : ℂ) =
      ((L * K * ∑ ζ ∈ T, ‖a ζ‖ ^ 2 : ℝ) : ℂ) + Off := by
    simp_rw [Complex.ofReal_sum, norm_sq_sum_mul_pow]
    have hswap : ∑ i ∈ range L, ∑ j ∈ range K, ∑ ζ ∈ T, ∑ ξ ∈ T,
        a ζ * conj (a ξ) * (ζ * conj ξ) ^ (T₀ + i + j) =
        ∑ ζ ∈ T, ∑ ξ ∈ T, a ζ * conj (a ξ) * G (ζ * conj ξ) := by
      calc _ = ∑ i ∈ range L, ∑ ζ ∈ T, ∑ ξ ∈ T, ∑ j ∈ range K,
            a ζ * conj (a ξ) * (ζ * conj ξ) ^ (T₀ + i + j) := by
            refine sum_congr rfl fun i _ => ?_
            rw [sum_comm]
            exact sum_congr rfl fun ζ _ => sum_comm
        _ = ∑ ζ ∈ T, ∑ ξ ∈ T, ∑ i ∈ range L, ∑ j ∈ range K,
            a ζ * conj (a ξ) * (ζ * conj ξ) ^ (T₀ + i + j) := by
            rw [sum_comm]
            exact sum_congr rfl fun ζ _ => sum_comm
        _ = _ := by
            refine sum_congr rfl fun ζ _ => sum_congr rfl fun ξ _ => ?_
            rw [hG]
            dsimp only
            rw [← sum_range_sum_range_pow, mul_sum]
            exact sum_congr rfl fun i _ => by rw [mul_sum]
    have hdiag : ((L * K * ∑ ζ ∈ T, ‖a ζ‖ ^ 2 : ℝ) : ℂ) =
        ∑ ζ ∈ T, a ζ * conj (a ζ) * G (ζ * conj ζ) := by
      push_cast
      rw [mul_sum]
      refine sum_congr rfl fun ζ hζ => ?_
      have h1 : ζ * conj ζ = 1 := by
        rw [mul_comm]
        exact conj_mul_self_of_norm_eq_one (hnorm ζ hζ)
      simp only [hG, h1, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, one_mul]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hswap, hOff, hdiag, ← sum_add_distrib]
    exact sum_congr rfl fun ζ hζ => (add_sum_erase T _ hζ).symm
  -- each off-diagonal kernel is at most `1 / (4 dist²)`
  have hker : ∀ ζ ∈ T, ∀ ξ ∈ T.erase ζ,
      ‖a ζ * conj (a ξ) * G (ζ * conj ξ)‖ ≤
        ‖a ζ‖ * ‖a ξ‖ * (1 / (4 * toIntDist (θ ξ - θ ζ) ^ 2)) := by
    intro ζ hζ ξ hξ
    have hξT := mem_of_mem_erase hξ
    have hne : ζ ≠ ξ := Ne.symm (ne_of_mem_erase hξ)
    have hd := hsep ζ hζ ξ hξT hne
    have hz1 : ‖ζ * conj ξ‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, hnorm ζ hζ, hnorm ξ hξT, one_mul]
    have hchord : 4 * toIntDist (θ ξ - θ ζ) ≤ ‖ζ * conj ξ - 1‖ := by
      have h := four_mul_toIntDist_le_norm_sub (θ ζ) (θ ξ)
      rw [hθ ζ hζ, hθ ξ hξT] at h
      have hc : ζ * conj ξ - 1 = conj (conj ζ * ξ - 1) := by
        rw [map_sub, map_mul, Complex.conj_conj, map_one, mul_comm]
      rwa [hc, Complex.norm_conj]
    have hdpos : 0 < toIntDist (θ ξ - θ ζ) := lt_of_lt_of_le hδ0 hd
    have hzne : ζ * conj ξ ≠ 1 := by
      intro h
      rw [h, sub_self, norm_zero] at hchord
      linarith
    have hpos : 0 < ‖ζ * conj ξ - 1‖ := by linarith
    have hgeo := fun M => norm_geom_sum_le hz1.le hzne M
    have hG' : ‖G (ζ * conj ξ)‖ ≤ 4 / ‖ζ * conj ξ - 1‖ ^ 2 := by
      simp only [hG, norm_mul, norm_pow, hz1, one_pow, one_mul]
      calc ‖∑ i ∈ range L, (ζ * conj ξ) ^ i‖ * ‖∑ j ∈ range K, (ζ * conj ξ) ^ j‖
          ≤ (2 / ‖ζ * conj ξ - 1‖) * (2 / ‖ζ * conj ξ - 1‖) :=
            mul_le_mul (hgeo L) (hgeo K) (norm_nonneg _) (by positivity)
        _ = 4 / ‖ζ * conj ξ - 1‖ ^ 2 := by ring
    have hsq : (4 * toIntDist (θ ξ - θ ζ)) ^ 2 ≤ ‖ζ * conj ξ - 1‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hchord 2
    have hG'' : ‖G (ζ * conj ξ)‖ ≤ 1 / (4 * toIntDist (θ ξ - θ ζ) ^ 2) := by
      refine hG'.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left hG'' (by positivity)
  -- squared reciprocal distances from every frequency are at most `4/δ²`
  have hrow : ∀ ζ ∈ T, ∑ ξ ∈ T.erase ζ, 1 / toIntDist (θ ξ - θ ζ) ^ 2 ≤ 4 / δ ^ 2 :=
    fun ζ hζ => sum_erase_one_div_toIntDist_sq_le T θ hδ0 hδ
      (fun a ha b hb hab => hsep a ha b hb hab) hζ
  have hrow' : ∀ ξ ∈ T, ∑ ζ ∈ T.erase ξ, 1 / toIntDist (θ ξ - θ ζ) ^ 2 ≤ 4 / δ ^ 2 := by
    intro ξ hξ
    have h := hrow ξ hξ
    refine le_of_eq_of_le (sum_congr rfl fun ζ _ => ?_) h
    rw [← toIntDist_neg, neg_sub]
  -- AM–GM and the symmetry of the pair sum
  have hswap : ∑ ζ ∈ T, ∑ ξ ∈ T.erase ζ, ‖a ξ‖ ^ 2 * (1 / toIntDist (θ ξ - θ ζ) ^ 2) =
      ∑ ξ ∈ T, ∑ ζ ∈ T.erase ξ, ‖a ξ‖ ^ 2 * (1 / toIntDist (θ ξ - θ ζ) ^ 2) :=
    sum_comm' fun ζ ξ => by
      simp only [mem_erase]
      constructor
      · rintro ⟨hζ, hne, hξ⟩
        exact ⟨⟨Ne.symm hne, hζ⟩, hξ⟩
      · rintro ⟨⟨hne, hζ⟩, hξ⟩
        exact ⟨hζ, Ne.symm hne, hξ⟩
  have hB : 0 ≤ ∑ ζ ∈ T, ‖a ζ‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hoff : ‖Off‖ ≤ (∑ ζ ∈ T, ‖a ζ‖ ^ 2) / δ ^ 2 := by
    calc ‖Off‖ ≤ ∑ ζ ∈ T, ∑ ξ ∈ T.erase ζ, ‖a ζ * conj (a ξ) * G (ζ * conj ξ)‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun ζ _ => norm_sum_le _ _)
      _ ≤ ∑ ζ ∈ T, ∑ ξ ∈ T.erase ζ, ‖a ζ‖ * ‖a ξ‖ * (1 / (4 * toIntDist (θ ξ - θ ζ) ^ 2)) :=
          sum_le_sum fun ζ hζ => sum_le_sum fun ξ hξ => hker ζ hζ ξ hξ
      _ ≤ ∑ ζ ∈ T, ∑ ξ ∈ T.erase ζ, (‖a ζ‖ ^ 2 * (1 / toIntDist (θ ξ - θ ζ) ^ 2) +
            ‖a ξ‖ ^ 2 * (1 / toIntDist (θ ξ - θ ζ) ^ 2)) / 8 := by
          refine sum_le_sum fun ζ _ => sum_le_sum fun ξ _ => ?_
          have hab : ‖a ζ‖ * ‖a ξ‖ ≤ (‖a ζ‖ ^ 2 + ‖a ξ‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖a ζ‖ - ‖a ξ‖)]
          have hw : 0 ≤ 1 / toIntDist (θ ξ - θ ζ) ^ 2 := by positivity
          calc ‖a ζ‖ * ‖a ξ‖ * (1 / (4 * toIntDist (θ ξ - θ ζ) ^ 2))
              = (‖a ζ‖ * ‖a ξ‖) * (1 / toIntDist (θ ξ - θ ζ) ^ 2) / 4 := by
                field_simp
            _ ≤ ((‖a ζ‖ ^ 2 + ‖a ξ‖ ^ 2) / 2) * (1 / toIntDist (θ ξ - θ ζ) ^ 2) / 4 := by
                gcongr
            _ = _ := by ring
      _ = (∑ ζ ∈ T, ∑ ξ ∈ T.erase ζ, ‖a ζ‖ ^ 2 * (1 / toIntDist (θ ξ - θ ζ) ^ 2) +
            ∑ ζ ∈ T, ∑ ξ ∈ T.erase ζ, ‖a ξ‖ ^ 2 * (1 / toIntDist (θ ξ - θ ζ) ^ 2)) / 8 := by
          simp only [add_div, sum_div, sum_add_distrib]
      _ = (∑ ζ ∈ T, ‖a ζ‖ ^ 2 * ∑ ξ ∈ T.erase ζ, 1 / toIntDist (θ ξ - θ ζ) ^ 2 +
            ∑ ξ ∈ T, ‖a ξ‖ ^ 2 * ∑ ζ ∈ T.erase ξ, 1 / toIntDist (θ ξ - θ ζ) ^ 2) / 8 := by
          rw [hswap]
          simp only [mul_sum]
      _ ≤ (∑ ζ ∈ T, ‖a ζ‖ ^ 2 * (4 / δ ^ 2) + ∑ ξ ∈ T, ‖a ξ‖ ^ 2 * (4 / δ ^ 2)) / 8 := by
          gcongr with ζ hζ ξ hξ
          · exact hrow ζ hζ
          · exact hrow' ξ hξ
      _ = (∑ ζ ∈ T, ‖a ζ‖ ^ 2) / δ ^ 2 := by
          rw [← sum_mul]
          field_simp
          ring
  have hreal : |∑ i ∈ range L, ∑ j ∈ range K, ‖∑ ζ ∈ T, a ζ * ζ ^ (T₀ + i + j)‖ ^ 2 -
      L * K * ∑ ζ ∈ T, ‖a ζ‖ ^ 2| = ‖Off‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, hexp, add_sub_cancel_left]
  rw [hreal]
  exact hoff

/-! ## §4. The window sandwich for responses -/

/-- Summing a function of the order over the roots of order at most `N` weighs each order `q` by
the `φ(q)` primitive roots. -/
theorem sum_responseRoots_orderOf (N : ℕ) (f : ℕ → ℝ) :
    ∑ ζ ∈ responseRoots N, f (orderOf ζ) = ∑ q ∈ Icc 1 N, (q.totient : ℝ) * f q := by
  classical
  have hset : responseRoots N = (Icc 1 N).biUnion fun q => primitiveRoots q ℂ := by
    ext ζ
    rw [mem_biUnion]
    constructor
    · intro hζ
      have hq := orderOf_mem_Icc_of_mem_responseRoots hζ
      exact ⟨orderOf ζ, hq,
        (mem_primitiveRoots (mem_Icc.mp hq).1).mpr (IsPrimitiveRoot.orderOf ζ)⟩
    · rintro ⟨q, hq, hζ⟩
      exact primitiveRoot_mem_responseRoots hq ((mem_primitiveRoots (mem_Icc.mp hq).1).mp hζ)
  rw [hset, sum_biUnion fun q _ q' _ hne => IsPrimitiveRoot.disjoint hne]
  refine sum_congr rfl fun q hq => ?_
  have hq0 := (mem_Icc.mp hq).1
  rw [sum_congr rfl (g := fun _ => f q) fun ζ hζ => by
      rw [← ((mem_primitiveRoots hq0).mp hζ).eq_orderOf],
    sum_const, (Complex.isPrimitiveRoot_exp q (by omega)).card_primitiveRoots, nsmul_eq_mul]

theorem sum_responseRoots_selberg_sq (N : ℕ) (c : ℕ → ℝ) :
    ∑ ζ ∈ responseRoots N, selbergMultiplesCoord N c (orderOf ζ) ^ 2 =
      selbergTotientDiagonalForm N c :=
  sum_responseRoots_orderOf N fun q => selbergMultiplesCoord N c q ^ 2

theorem sieveSeq_sq_eq_norm_sq (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N c k ^ 2 =
      ‖∑ ζ ∈ responseRoots N, (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ζ ^ k‖ ^ 2 := by
  rw [← sieveSeq_eq_sum_responseRoots, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem pow_factorial_eq_one_of_mem_responseRoots {N : ℕ} {ζ : ℂ} (hζ : ζ ∈ responseRoots N) :
    ζ ^ N.factorial = 1 := by
  obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp hζ
  obtain ⟨t, ht⟩ := Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2
  rw [ht, pow_mul, (Polynomial.mem_nthRootsFinset (mem_Icc.mp hd).1 1).mp hζd, one_pow]

/-- **Trapezoid sandwich over the response frequencies.** The average of `L` box windows of
length `K` of `|Σ_{ζ ∈ T} a(ζ) ζ^k|²` is `L K Σ |a|²` up to `N⁴ Σ |a|²`, at every phase. -/
theorem abs_trapezoid_responseRoots_sub_le {N : ℕ} (hN : 2 ≤ N) {T : Finset ℂ}
    (hT : T ⊆ responseRoots N) (a : ℂ → ℂ) (T₀ L K : ℕ) :
    |∑ i ∈ range L, ∑ j ∈ range K, ‖∑ ζ ∈ T, a ζ * ζ ^ (T₀ + i + j)‖ ^ 2 -
        L * K * ∑ ζ ∈ T, ‖a ζ‖ ^ 2| ≤ (N : ℝ) ^ 4 * ∑ ζ ∈ T, ‖a ζ‖ ^ 2 := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hδ0 : (0 : ℝ) < 1 / (N : ℝ) ^ 2 := by positivity
  have hδ : 1 / (N : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine (abs_trapezoid_sum_sub_le a rootAngle
    (fun ζ hζ => circleFreq_rootAngle (norm_eq_one_of_mem_responseRoots (hT hζ))) hδ0 hδ
    (fun ζ hζ ξ hξ hne => responseRoots_separated (hT hζ) (hT hξ) hne) T₀ L K).trans_eq ?_
  field_simp

/-- **Box-window sandwich over the response frequencies.** At every phase `A` and length `K`,
`Σ_{A<k≤A+K} |Σ_{ζ ∈ T} a(ζ) ζ^k|²` is `K Σ |a|²` up to `(2N² - 1) Σ |a|²`. -/
theorem abs_window_sum_norm_sq_sub_le {N : ℕ} (hN : 2 ≤ N) {T : Finset ℂ}
    (hT : T ⊆ responseRoots N) (a : ℂ → ℂ) (A K : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K), ‖∑ ζ ∈ T, a ζ * ζ ^ k‖ ^ 2 - K * ∑ ζ ∈ T, ‖a ζ‖ ^ 2| ≤
      (2 * (N : ℝ) ^ 2 - 1) * ∑ ζ ∈ T, ‖a ζ‖ ^ 2 := by
  set f : ℕ → ℝ := fun k => ‖∑ ζ ∈ T, a ζ * ζ ^ k‖ ^ 2 with hf
  set Q := ∑ ζ ∈ T, ‖a ζ‖ ^ 2 with hQdef
  have hQ : 0 ≤ Q := sum_nonneg fun _ _ => sq_nonneg _
  have hper : ∀ k j : ℕ, f (k + j * N.factorial) = f k := by
    intro k j
    simp only [hf]
    congr 2
    refine sum_congr rfl fun ζ hζ => ?_
    rw [pow_add, mul_comm j, pow_mul, pow_factorial_eq_one_of_mem_responseRoots (hT hζ), one_pow,
      mul_one]
  set L := N ^ 2 with hL
  have hL1 : 1 ≤ L := Nat.one_le_pow _ _ (by omega)
  have hLR : (L : ℝ) = (N : ℝ) ^ 2 := by rw [hL]; push_cast; ring
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  set S := ∑ k ∈ Icc (A + 1) (A + K), f k with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hbox : ∀ t K' : ℕ, ∑ j ∈ range K', f (t + j) =
      ∑ k ∈ Ico t (t + K'), f k := fun t K' => by
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hN4 : (N : ℝ) ^ 4 = (L : ℝ) * (N : ℝ) ^ 2 := by rw [hLR]; ring
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- lower trapezoid inside the window
    rcases Nat.lt_or_ge (K + 1) L with hKL | hKL
    · have hK : (K : ℝ) + 1 ≤ L := by exact_mod_cast hKL.le
      nlinarith
    · set K' := K + 1 - L with hK'
      have hin : ∀ i ∈ range L, ∑ j ∈ range K', f (A + 1 + i + j) ≤ S := by
        intro i hi
        have hi' := mem_range.mp hi
        rw [hbox]
        refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => sq_nonneg _
        obtain ⟨h1, h2⟩ := mem_Ico.mp hk
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      have hsum : ∑ i ∈ range L, ∑ j ∈ range K', f (A + 1 + i + j) ≤ L * S := by
        calc _ ≤ ∑ _i ∈ range L, S := sum_le_sum hin
          _ = L * S := by rw [sum_const, card_range, nsmul_eq_mul]
      have htr := (abs_le.mp (abs_trapezoid_responseRoots_sub_le hN hT a (A + 1) L K')).1
      have hK'R : (K' : ℝ) = K + 1 - L := by
        rw [hK', Nat.cast_sub hKL]
        push_cast
        ring
      rw [hK'R, hN4] at htr
      have : (L : ℝ) * ((K : ℝ) - (2 * (N : ℝ) ^ 2 - 1)) * Q ≤ L * S := by
        rw [← hLR] at htr ⊢
        nlinarith
      have h2 := le_of_mul_le_mul_left (by linarith : (L : ℝ) * (((K : ℝ) -
        (2 * (N : ℝ) ^ 2 - 1)) * Q) ≤ L * S) hLpos
      linarith
  · -- upper trapezoid around the window, moved by a multiple of the period
    set P := L * N.factorial with hP
    have hLP : L ≤ P := Nat.le_mul_of_pos_right L (Nat.factorial_pos N)
    set T₀ := A + 1 + P - (L - 1) with hT₀
    set K' := K + L - 1 with hK'
    have hshift : S = ∑ k ∈ Icc (A + 1 + P) (A + K + P), f k := by
      rw [hS, ← Finset.map_add_right_Icc, sum_map]
      refine sum_congr rfl fun k _ => ?_
      simp only [addRightEmbedding_apply, hP]
      rw [hper]
    have hout : ∀ i ∈ range L, S ≤ ∑ j ∈ range K', f (T₀ + i + j) := by
      intro i hi
      have hi' := mem_range.mp hi
      rw [hbox, hshift]
      refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => sq_nonneg _
      obtain ⟨h1, h2⟩ := mem_Icc.mp hk
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    have hsum : L * S ≤ ∑ i ∈ range L, ∑ j ∈ range K', f (T₀ + i + j) := by
      calc L * S = ∑ _i ∈ range L, S := by rw [sum_const, card_range, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum hout
    have htr := (abs_le.mp (abs_trapezoid_responseRoots_sub_le hN hT a T₀ L K')).2
    have hK'R : (K' : ℝ) = K + L - 1 := by
      rw [hK', Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hK'R, hN4] at htr
    have h1 : (L : ℝ) * S ≤ L * (((K : ℝ) + (2 * (N : ℝ) ^ 2 - 1)) * Q) := by
      rw [← hLR] at htr ⊢
      nlinarith
    have h2 := le_of_mul_le_mul_left h1 hLpos
    linarith


/-- **The window sandwich at quadratic order.** At every phase `A` and length `K`, the window sum
of the squared response is `K Q_Sel` up to `(2N² - 1) Q_Sel`. -/
theorem abs_window_sum_sq_sub_le_two_mul_sq {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (A K : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K), sieveSeq N c k ^ 2 - K * selbergTotientDiagonalForm N c| ≤
      (2 * (N : ℝ) ^ 2 - 1) * selbergTotientDiagonalForm N c := by
  have h := abs_window_sum_norm_sq_sub_le hN (subset_refl _)
    (fun ζ => (selbergMultiplesCoord N c (orderOf ζ) : ℂ)) A K
  simp only [← sieveSeq_sq_eq_norm_sq] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sum_responseRoots_selberg_sq] using h

/-- The predicate form, with an arbitrary offset of the response. -/
theorem isWindowSandwichConstant_two_mul_sq {N : ℕ} (hN : 2 ≤ N) :
    IsWindowSandwichConstant N (2 * (N : ℝ) ^ 2 - 1) := by
  intro A K c κ
  have h := abs_window_sum_sq_sub_le_two_mul_sq hN (sieveRowShift c κ) A K
  rw [selbergTotientDiagonalForm_sieveRowShift (by omega)] at h
  simpa only [sieveSeq_sieveRowShift (by omega : 1 ≤ N)] using h

/-- **The optimal window sandwich constant has order `N^{2+o(1)}`.** `2N² - 1` is admissible, and
every admissible constant `S` satisfies `(N - 1 - log N)² ≤ (1 + S)(1 + log N)³`. -/
theorem windowSandwichConstant_quadratic_order {N : ℕ} (hN : 2 ≤ N) :
    IsWindowSandwichConstant N (2 * (N : ℝ) ^ 2 - 1) ∧
      ∀ S : ℝ, IsWindowSandwichConstant N S →
        ((N : ℝ) - 1 - Real.log N) ^ 2 ≤ (1 + S) * (1 + Real.log N) ^ 3 :=
  ⟨isWindowSandwichConstant_two_mul_sq hN,
    fun _ hS => isWindowSandwichConstant_lower_bound (by omega) hS⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
