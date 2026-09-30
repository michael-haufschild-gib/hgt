import GaloisForLFunctions.RHTower.PrimeSupportedConvolutionMoments
import GaloisForLFunctions.RHTower.SelbergVonMangoldtPolyTypical

/-!
# High moments of the prime part of Selberg's von Mangoldt polynomial

For an arithmetic function `a` supported on `[1, N]`, the `m`-th power of the Dirichlet polynomial
`E_a(z) = Σ_{n ≤ N} a(n) n^{−z}` is the Dirichlet polynomial of the convolution power:
`E_a^m = E_{a^{⋆m}}` on `[1, N^m]` (`edPoly_pow_eq`). When `a` is supported on primes, the mean value
theorem and `‖a^{⋆m}‖²_w ≤ m! ‖a‖²_w^m` give on `Re z = 1/2 − d`

`∫_{T₁}^{T₂} |E_a|^{2m} ≤ (T₂ − T₁ + 8N^m(1 + log N^m)) · m! · (Σ_{n ≤ N} |a(n)|² n^{2d−1})^m`
(`integral_norm_edPoly_pow_displaced_le`).

Split `D_x = P_x + H_x`, where `P_x` carries the primes and `H_x` the proper prime powers. On
`Re z ≥ 1/2 + δ`, `0 < δ ≤ 1`, the proper prime powers are pointwise small,
`|H_x(z)| ≤ 36/δ` (`norm_selbergPrimePowerPoly_le`): the powers `p^k`, `k ≥ 2`, contribute a
geometric series `≤ 4 p^{−1−2δ} log p`, summed by Chebyshev's bound. The prime part has large values
`|P_x| > M` near the box `1/2 + 3R/4 ≤ Re ≤ 1/2 + 6R`, `|Im − t| ≤ 6R`, only on a set of heights of
measure `≤ 1380 · m! (20/R²)^m (T + 17R + 8N^m(1 + log N^m))/(π M^{2m})`
(`volume_largeNearBox_selbergPrimePoly_le`).
-/

noncomputable section

open Complex Set MeasureTheory ArithmeticFunction

namespace RHTower

/-! ## Powers of Dirichlet polynomials -/

/-- The powers of a function supported on `[1, N]` are supported on `[1, N^m]`. -/
theorem support_pow_le {a : ArithmeticFunction ℂ} {N : ℕ} (haN : ∀ k, a k ≠ 0 → 1 ≤ k ∧ k ≤ N) :
    ∀ m k, (a ^ m) k ≠ 0 → 1 ≤ k ∧ k ≤ N ^ m := by
  intro m
  induction m with
  | zero =>
    intro k hk
    rw [pow_zero, one_apply] at hk
    split_ifs at hk with h
    · subst h; exact ⟨le_rfl, by simp⟩
    · exact absurd rfl hk
  | succ m ih =>
    intro k hk
    rw [pow_succ, mul_apply] at hk
    obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    obtain ⟨h1, hN1⟩ := ih x.1 (left_ne_zero_of_mul hx0)
    obtain ⟨h2, hN2⟩ := haN x.2 (right_ne_zero_of_mul hx0)
    obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rw [← hmul]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    rw [pow_succ]; exact Nat.mul_le_mul hN1 hN2

theorem ofReal_natCast_mul_cpow_neg (d e : ℕ) (z : ℂ) :
    (((d * e : ℕ) : ℝ) : ℂ) ^ (-z) = ((d : ℝ) : ℂ) ^ (-z) * ((e : ℝ) : ℂ) ^ (-z) := by
  push_cast
  exact Complex.natCast_mul_natCast_cpow d e (-z)

/-- **The power of a Dirichlet polynomial is the polynomial of the convolution power.** -/
theorem edPoly_pow_eq {a : ArithmeticFunction ℂ} {N : ℕ} (haN : ∀ k, a k ≠ 0 → 1 ≤ k ∧ k ≤ N)
    (z : ℂ) : ∀ m : ℕ, edPoly (⇑a) (Finset.Icc 1 N) z ^ m = edPoly (⇑(a ^ m)) (Finset.Icc 1 (N ^ m)) z := by
  have hsupp := support_pow_le haN
  intro m
  induction m with
  | zero =>
    simp only [pow_zero]
    unfold edPoly
    rw [show Finset.Icc 1 1 = {1} from rfl, Finset.sum_singleton, one_apply, if_pos rfl]
    simp
  | succ m ih =>
    rw [pow_succ, ih]
    unfold edPoly
    rw [Finset.sum_mul_sum]
    have e : ∀ n ∈ Finset.Icc 1 (N ^ (m + 1)), (a ^ (m + 1)) n * ((n : ℝ) : ℂ) ^ (-z) =
        ∑ x ∈ n.divisorsAntidiagonal,
          (a ^ m) x.1 * ((x.1 : ℝ) : ℂ) ^ (-z) * (a x.2 * ((x.2 : ℝ) : ℂ) ^ (-z)) := by
      intro n _
      rw [pow_succ, mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      rw [← hmul, ofReal_natCast_mul_cpow_neg]
      ring
    rw [Finset.sum_congr rfl e]
    symm
    refine sum_Icc_sum_divisorsAntidiagonal (fun x hx => ?_) (le_of_eq (pow_succ N m).symm)
    have h1 : (a ^ m) x.1 ≠ 0 := by
      intro h; apply hx; rw [h]; simp
    have h2 : a x.2 ≠ 0 := by
      intro h; apply hx; rw [h]; simp
    exact ⟨hsupp m x.1 h1, haN x.2 h2⟩

/-- **High moments of a prime Dirichlet polynomial on a displaced line.** -/
theorem integral_norm_edPoly_pow_displaced_le {a : ArithmeticFunction ℂ} {N : ℕ}
    (ha : ∀ k, a k ≠ 0 → k.Prime) (haN : ∀ k, a k ≠ 0 → k ≤ N) (d : ℝ) (m : ℕ) (T₁ T₂ : ℝ)
    (hT : T₁ ≤ T₂) :
    (∫ τ in T₁..T₂, ‖edPoly (⇑a) (Finset.Icc 1 N) (displacedLinePt d τ) ^ m‖ ^ 2) ≤
      (T₂ - T₁ + 8 * (N ^ m : ℕ) * (1 + Real.log (N ^ m : ℕ))) *
        (m.factorial * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1)) ^ m) := by
  have haN' : ∀ k, a k ≠ 0 → 1 ≤ k ∧ k ≤ N := fun k hk => ⟨(ha k hk).one_lt.le, haN k hk⟩
  simp_rw [edPoly_pow_eq haN']
  refine (integral_normSq_edPoly_displaced_le d _ (N ^ m) T₁ T₂).trans ?_
  have hfac : 0 ≤ T₂ - T₁ + 8 * ((N ^ m : ℕ) : ℝ) * (1 + Real.log (N ^ m : ℕ)) := by
    rcases Nat.eq_zero_or_pos (N ^ m) with h0 | hpos
    · rw [h0]; simp; linarith
    · have := Real.log_nonneg (show (1 : ℝ) ≤ (N ^ m : ℕ) by exact_mod_cast hpos)
      positivity
  refine mul_le_mul_of_nonneg_left ?_ hfac
  have hw0 : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (2 * d - 1) := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hwmul : ∀ d' e : ℕ, ((d' * e : ℕ) : ℝ) ^ (2 * d - 1) =
      (d' : ℝ) ^ (2 * d - 1) * (e : ℝ) ^ (2 * d - 1) := fun d' e => by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact wMass_pow_le (w := fun n : ℕ => (n : ℝ) ^ (2 * d - 1)) hw0 hwmul ha haN m

/-! ## The prime part and the prime-power part of `D_x` -/

/-- The prime coefficients `Λ(p) W_x(p)`. -/
def selbergPrimeCoeff (x : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime then selbergPolyCoeff x n else 0, by simp [Nat.not_prime_zero]⟩

theorem selbergPrimeCoeff_apply (x : ℝ) (n : ℕ) :
    selbergPrimeCoeff x n = if n.Prime then selbergPolyCoeff x n else 0 := rfl

/-- The prime part `P_x(z) = Σ_{p ≤ N_x} Λ(p) W_x(p) p^{−z}`. -/
def selbergPrimePoly (x : ℝ) (z : ℂ) : ℂ :=
  edPoly (⇑(selbergPrimeCoeff x)) (Finset.Icc 1 (selbergPolyLength x)) z

/-- The proper prime-power part `H_x(z) = Σ_{n ≤ N_x, n not prime} Λ(n) W_x(n) n^{−z}`. -/
def selbergPrimePowerPoly (x : ℝ) (z : ℂ) : ℂ :=
  edPoly (fun n => if n.Prime then 0 else selbergPolyCoeff x n)
    (Finset.Icc 1 (selbergPolyLength x)) z

theorem selbergVonMangoldtPoly_eq_prime_add {x : ℝ} (hx : 1 < x) (z : ℂ) :
    selbergVonMangoldtPoly x z = selbergPrimePoly x z + selbergPrimePowerPoly x z := by
  rw [selbergVonMangoldtPoly_eq_edPoly hx]
  unfold selbergPrimePoly selbergPrimePowerPoly edPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : n.Prime <;> simp [selbergPrimeCoeff_apply, hp]

theorem selbergPrimeCoeff_support {x : ℝ} (hx : 1 < x) (k : ℕ) (hk : selbergPrimeCoeff x k ≠ 0) :
    k.Prime ∧ k ≤ selbergPolyLength x := by
  rw [selbergPrimeCoeff_apply] at hk
  split_ifs at hk with hp
  · refine ⟨hp, ?_⟩
    by_contra hlt
    push Not at hlt
    apply hk
    have hx2 : x ^ 2 ≤ k := by
      have h1 := Nat.le_ceil (x ^ 2)
      have h2 : (selbergPolyLength x : ℝ) < k := by exact_mod_cast hlt
      unfold selbergPolyLength at h2
      linarith
    unfold selbergPolyCoeff
    rw [selbergWeight_eq_zero hx hx2]
    simp
  · exact absurd rfl hk

theorem differentiable_selbergPrimePoly (x : ℝ) : Differentiable ℂ (selbergPrimePoly x) :=
  differentiable_edPoly _ fun _ hn => (Finset.mem_Icc.mp hn).1

/-- The prime energy on `Re z = 1/2 + δ`. -/
theorem sum_selbergPrimeCoeff_sq_le {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖selbergPrimeCoeff x n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤ 5 / δ ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_vonMangoldt_sq_rpow_le hδ hδ1 N)
  have hn : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have e : (2 * -δ - 1) = -1 - 2 * δ := by ring
  rw [e]
  have hp : 0 ≤ (n : ℝ) ^ (-1 - 2 * δ) := Real.rpow_nonneg hn.le _
  refine mul_le_mul_of_nonneg_right ?_ hp
  rw [selbergPrimeCoeff_apply]
  split_ifs
  · unfold selbergPolyCoeff
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    have hW0 := selbergWeight_nonneg hx n
    have hW1 := selbergWeight_le_one hx n
    have : selbergWeight x n ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (vonMangoldt n)]
  · simp

/-! ## The proper prime powers are pointwise small -/

/-- The proper prime powers up to `N` inject into the pairs `(p, k)`, `p ≤ N` prime, `2 ≤ k ≤ N`. -/
theorem sum_nonprime_vonMangoldt_le_pairs (N : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime), vonMangoldt n * f n ≤
      ∑ q ∈ ((Finset.Icc 1 N).filter Nat.Prime) ×ˢ Finset.Icc 2 N,
        Real.log q.1 * f (q.1 ^ q.2) := by
  classical
  set S := (Finset.Icc 1 N).filter (fun n => ¬ n.Prime) with hS
  set P := ((Finset.Icc 1 N).filter Nat.Prime) ×ˢ Finset.Icc 2 N with hP
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.1 ^ q.2) P := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    obtain ⟨hq1', hq2'⟩ := Finset.mem_product.mp hq'
    have hp := (Finset.mem_filter.mp hq1).2
    have hp' := (Finset.mem_filter.mp hq1').2
    have hk := (Finset.mem_Icc.mp hq2).1
    have hk' := (Finset.mem_Icc.mp hq2').1
    simp only at h
    have h' : q.1 ^ (q.2 - 1 + 1) = q'.1 ^ (q'.2 - 1 + 1) := by
      rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact h
    obtain ⟨e1, e2⟩ := Nat.Prime.pow_inj hp hp' h'
    exact Prod.ext e1 (by omega)
  have hsub : S.filter (fun n => vonMangoldt n ≠ 0) ⊆ P.image (fun q => q.1 ^ q.2) := by
    intro n hn
    obtain ⟨hnS, hΛ⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hnp⟩ := Finset.mem_filter.mp hnS
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
    have hpp : IsPrimePow n := by
      by_contra h; exact hΛ (vonMangoldt_eq_zero_iff.mpr h)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hnp (by simpa using hp)
    refine Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, ?_⟩, hp⟩
      exact le_trans (Nat.le_self_pow (by omega) p) hnN
    · refine Finset.mem_Icc.mpr ⟨hk2, le_trans (Nat.lt_pow_self hp.one_lt).le hnN⟩
  calc ∑ n ∈ S, vonMangoldt n * f n
      = ∑ n ∈ S.filter (fun n => vonMangoldt n ≠ 0), vonMangoldt n * f n := by
        refine (Finset.sum_filter_of_ne fun n _ h => ?_).symm
        intro h0; apply h; rw [h0, zero_mul]
    _ ≤ ∑ n ∈ P.image (fun q => q.1 ^ q.2), vonMangoldt n * f n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          mul_nonneg vonMangoldt_nonneg (hf n)
    _ = ∑ q ∈ P, vonMangoldt (q.1 ^ q.2) * f (q.1 ^ q.2) := Finset.sum_image hinj
    _ = ∑ q ∈ P, Real.log q.1 * f (q.1 ^ q.2) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
        have hp := (Finset.mem_filter.mp hq1).2
        have hk := (Finset.mem_Icc.mp hq2).1
        rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]

/-- The geometric series over `k ≥ 2` at one prime. -/
theorem sum_Icc_prime_pow_rpow_le {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 + δ)) ≤ 4 * (p : ℝ) ^ (-1 - 2 * δ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set r : ℝ := (p : ℝ) ^ (-(1 / 2 + δ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hr34 : r ≤ 3 / 4 := by
    have h1 : r ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, inv_le_comm₀ (by positivity)
        (by norm_num), Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    linarith
  have e : ∀ k : ℕ, ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 + δ)) = r ^ k := by
    intro k
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, mul_comm,
      Real.rpow_mul hp0.le, Real.rpow_natCast]
  simp_rw [e]
  have hIco : Finset.Icc 2 N ⊆ Finset.Ico 2 (N + 1) := by
    intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_Ico]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hIco fun k _ _ => pow_nonneg hr0 k).trans ?_
  refine (geom_sum_Ico_le_of_lt_one hr0 (by linarith)).trans ?_
  have hr2 : r ^ 2 = (p : ℝ) ^ (-1 - 2 * δ) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1; push_cast; ring
  rw [hr2, div_le_iff₀ (by linarith)]
  have := Real.rpow_nonneg hp0.le (-1 - 2 * δ)
  nlinarith

/-- **The proper prime powers on `Re z = 1/2 + δ`:** `Σ_{n ≤ N, n not prime} Λ(n) n^{−1/2−δ} ≤ 36/δ`
for `0 < δ ≤ 1`. -/
theorem sum_nonprime_vonMangoldt_rpow_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime),
      vonMangoldt n * (n : ℝ) ^ (-(1 / 2 + δ)) ≤ 36 / δ := by
  have h1 := sum_nonprime_vonMangoldt_le_pairs N (fun n => (n : ℝ) ^ (-(1 / 2 + δ)))
    fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine h1.trans ?_
  rw [Finset.sum_product]
  have hs : (1 : ℝ) < 1 + 2 * δ := by linarith
  have hsum : Summable fun n : ℕ => vonMangoldt n / (n : ℝ) ^ (1 + 2 * δ) :=
    summable_vonMangoldt_div_rpow_mertensVonMangoldtEulerConstant hs
  calc ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑ k ∈ Finset.Icc 2 N,
        Real.log p * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 + δ))
      ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, 4 * (vonMangoldt p / (p : ℝ) ^ (1 + 2 * δ)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpp := (Finset.mem_filter.mp hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        rw [← Finset.mul_sum, vonMangoldt_apply_prime hpp]
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
        have hg := sum_Icc_prime_pow_rpow_le hpp hδ N
        have e : (p : ℝ) ^ (-1 - 2 * δ) = 1 / (p : ℝ) ^ (1 + 2 * δ) := by
          rw [one_div, ← Real.rpow_neg hp0.le]; congr 1; ring
        rw [e] at hg
        calc Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 + δ))
            ≤ Real.log p * (4 * (1 / (p : ℝ) ^ (1 + 2 * δ))) :=
              mul_le_mul_of_nonneg_left hg hlog
          _ = 4 * (Real.log p / (p : ℝ) ^ (1 + 2 * δ)) := by ring
    _ = 4 * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, vonMangoldt p / (p : ℝ) ^ (1 + 2 * δ) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ (1 + 2 * δ) := by
        refine mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun n _ => ?_) (by norm_num)
        exact div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ 4 * (6 * (1 + 2 * δ) / (1 + 2 * δ - 1)) :=
        mul_le_mul_of_nonneg_left (tsum_vonMangoldt_div_rpow_le_six hs) (by norm_num)
    _ ≤ 36 / δ := by
        have h2 : (1 + 2 * δ - 1) = 2 * δ := by ring
        have e : 4 * (6 * (1 + 2 * δ) / (1 + 2 * δ - 1)) = (12 + 24 * δ) / δ := by
          rw [h2]; field_simp; ring
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) hδ.le

/-- **The prime-power part is pointwise small:** `|H_x(z)| ≤ 36/δ` on `Re z ≥ 1/2 + δ`. -/
theorem norm_selbergPrimePowerPoly_le {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z : ℂ}
    (hz : 1 / 2 + δ ≤ z.re) : ‖selbergPrimePowerPoly x z‖ ≤ 36 / δ := by
  refine le_trans ?_ (sum_nonprime_vonMangoldt_rpow_le hδ hδ1 (selbergPolyLength x))
  unfold selbergPrimePowerPoly edPoly
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  by_cases hp : n.Prime
  · simp [hp]
  · simp only [hp, if_false, not_false_eq_true, if_true]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
    unfold selbergPolyCoeff
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg vonMangoldt_nonneg (selbergWeight_nonneg hx n))]
    have hW1 := selbergWeight_le_one hx n
    have hW0 := selbergWeight_nonneg hx n
    have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
    have hpow : (n : ℝ) ^ (-z.re) ≤ (n : ℝ) ^ (-(1 / 2 + δ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hp0 : 0 ≤ (n : ℝ) ^ (-z.re) := Real.rpow_nonneg hn0.le _
    calc vonMangoldt n * selbergWeight x n * (n : ℝ) ^ (-z.re)
        ≤ vonMangoldt n * 1 * (n : ℝ) ^ (-z.re) := by gcongr
      _ ≤ vonMangoldt n * (n : ℝ) ^ (-(1 / 2 + δ)) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hpow hΛ

/-! ## Large values of the prime part near the box -/

/-- The column mean square of `P_x^m` on `Re z = 1/2 + δ`. -/
theorem integral_norm_selbergPrimePoly_pow_le {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (m : ℕ) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    ∫ τ in T₁..T₂, ‖selbergPrimePoly x (((1 / 2 + δ : ℝ) : ℂ) + (τ : ℂ) * I) ^ m‖ ^ 2 ≤
      (T₂ - T₁ + 8 * (selbergPolyLength x ^ m : ℕ) * (1 + Real.log (selbergPolyLength x ^ m : ℕ))) *
        (m.factorial * (5 / δ ^ 2) ^ m) := by
  set N := selbergPolyLength x with hNdef
  have hpt : ∀ τ : ℝ, selbergPrimePoly x (((1 / 2 + δ : ℝ) : ℂ) + (τ : ℂ) * I) =
      edPoly (⇑(selbergPrimeCoeff x)) (Finset.Icc 1 N) (displacedLinePt (-δ) τ) := by
    intro τ
    unfold selbergPrimePoly displacedLinePt
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  refine (integral_norm_edPoly_pow_displaced_le (fun k hk => (selbergPrimeCoeff_support hx k hk).1)
    (fun k hk => (selbergPrimeCoeff_support hx k hk).2) (-δ) m T₁ T₂ hT).trans ?_
  have hfac : 0 ≤ T₂ - T₁ + 8 * ((N ^ m : ℕ) : ℝ) * (1 + Real.log (N ^ m : ℕ)) := by
    rcases Nat.eq_zero_or_pos (N ^ m) with h0 | hpos
    · rw [h0]; simp; linarith
    · have := Real.log_nonneg (show (1 : ℝ) ≤ (N ^ m : ℕ) by exact_mod_cast hpos)
      positivity
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hfac
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (sum_selbergPrimeCoeff_sq_le hx hδ hδ1 N) m

/-- **Large values of the prime part near the box**, through the `m`-th moment. -/
theorem volume_largeNearBox_selbergPrimePoly_le {T x R M : ℝ} (hT : 0 < T) (hx : 1 < x)
    (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hM : 0 < M) {m : ℕ} (hm : 1 ≤ m) :
    volume (largeNearBox (selbergPrimePoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R M) ≤
      ENNReal.ofReal (1380 * (m.factorial * (20 / R ^ 2) ^ m *
        (T + 17 * R + 8 * (selbergPolyLength x ^ m : ℕ) *
          (1 + Real.log (selbergPolyLength x ^ m : ℕ)))) / (Real.pi * (M ^ m) ^ 2)) := by
  set N := selbergPolyLength x with hN
  set Q : ℝ := m.factorial * (20 / R ^ 2) ^ m *
    (T + 17 * R + 8 * (N ^ m : ℕ) * (1 + Real.log (N ^ m : ℕ))) with hQ
  have hlogN : 0 ≤ 8 * ((N ^ m : ℕ) : ℝ) * (1 + Real.log (N ^ m : ℕ)) := by
    rcases Nat.eq_zero_or_pos (N ^ m) with h0 | hpos
    · rw [h0]; simp
    · have := Real.log_nonneg (show (1 : ℝ) ≤ (N ^ m : ℕ) by exact_mod_cast hpos)
      positivity
  have hsub : largeNearBox (selbergPrimePoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R M ⊆
      largeNearBox (fun z => selbergPrimePoly x z ^ m) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R
        (M ^ m) := by
    rintro t ⟨ht, z, h1, h2, h3, hz⟩
    refine ⟨ht, z, h1, h2, h3, ?_⟩
    rw [norm_pow]
    exact pow_lt_pow_left₀ hz hM.le (by omega)
  have hcol : ∀ c ∈ Icc (1 / 2 + 3 * R / 4 - R / 4) (1 / 2 + 6 * R + R / 4),
      ∫ y in (T - (7 : ℕ) * R)..(T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R),
        ‖(fun z => selbergPrimePoly x z ^ m) ((c : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ Q := by
    intro c hc
    set δ := c - 1 / 2 with hδ
    have hδ0 : R / 2 ≤ δ := by rw [hδ]; linarith [hc.1]
    have hδ1 : δ ≤ 1 := by rw [hδ]; linarith [hc.2]
    have hδpos : 0 < δ := by linarith
    have hceq : c = 1 / 2 + δ := by rw [hδ]; ring
    have hceil : (⌈T / R⌉₊ : ℝ) ≤ T / R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlen : T - (7 : ℕ) * R ≤ T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R := by
      push_cast
      have : (0 : ℝ) ≤ ⌈T / R⌉₊ := Nat.cast_nonneg _
      nlinarith
    have h := integral_norm_selbergPrimePoly_pow_le hx hδpos hδ1 m hlen
    simp only
    rw [hceq]
    refine h.trans ?_
    have hlen2 : T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) ≤ T + 17 * R := by
      push_cast
      have : (⌈T / R⌉₊ : ℝ) * R ≤ (T / R + 1) * R := mul_le_mul_of_nonneg_right hceil hR.le
      have e : (T / R + 1) * R = T + R := by field_simp
      nlinarith
    have hδ2 : 5 / δ ^ 2 ≤ 20 / R ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hA : 0 ≤ T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) +
        8 * ((N ^ m : ℕ) : ℝ) * (1 + Real.log (N ^ m : ℕ)) := by linarith
    have hpow : (m.factorial : ℝ) * (5 / δ ^ 2) ^ m ≤ m.factorial * (20 / R ^ 2) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hδ2 m) (by positivity)
    calc (T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) +
          8 * ((N ^ m : ℕ) : ℝ) * (1 + Real.log (N ^ m : ℕ))) * (m.factorial * (5 / δ ^ 2) ^ m)
        ≤ (T + 17 * R + 8 * ((N ^ m : ℕ) : ℝ) * (1 + Real.log (N ^ m : ℕ))) *
            (m.factorial * (20 / R ^ 2) ^ m) :=
          mul_le_mul (by linarith) hpow (by positivity) (by linarith)
      _ = Q := by rw [hQ]; ring
  have hbox := volume_largeNearBox_le ((differentiable_selbergPrimePoly x).pow m)
    (T := T) (a := 1 / 2 + 3 * R / 4) (b := 1 / 2 + 6 * R) (R := R) (r := R / 4) (M := M ^ m)
    (Q := Q) (by positivity) (by linarith) (by positivity) (by linarith) hcol
  refine (measure_mono hsub).trans (hbox.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  field_simp
  ring_nf

end RHTower
