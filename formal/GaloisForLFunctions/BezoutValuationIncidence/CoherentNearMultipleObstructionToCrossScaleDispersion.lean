import GaloisForLFunctions.BezoutValuationIncidence.SecondOrderCrossScaleLawAndTheBernoulliKernel

/-!
# The coherent near-multiple obstruction to cross-scale dispersion

The Bernoulli kernel `𝔅(d, n) = Σ_{j ≥ 1} Φ_d(jn)/j²` is large and positive when `n` lies just
above a multiple of `d`: the first term is `Φ_d(n) ≥ (d² - 1)/12 - (n mod d) d/2`, and every other
term is at least `-(d² + 2)/24`, so with `π < 3.15`

`32 (n mod d) ≤ d  ⟹  𝔅(d, n) ≥ d²/25 - 1/4`.

Such configurations exist for a positive proportion of any set of small moduli. For a set `S` of
moduli in `[64H, D]` and any `Q`, double counting the residues `n₀ mod d ∈ [0, d/64]` over
`n₀ ∈ [Q, Q + 2D)` gives a shift `n₀` with `128 |{d ∈ S : 64 (n₀ mod d) ≤ d}| ≥ |S|`, and on the
window `[n₀, n₀ + H)` every such `d` stays in the positive region. The second-order law then
gives, for all nonnegative rows `c` on the coherent moduli and `c'` on the window, when
`n₀ ≥ 75 D`,

`B(c, c') + m(c) R(c') + β(c) H(c') ≥ (1/100) (Σ_d c(d) d)(Σ_n c'(n)/n²)`.

The right side is `1/100` of the rank-two remainder bound `2 K_c Σ|c'(n)|/n²` of the exact rank-two
law. The trivial remainder bound is attained, up to the factor `100`, by coherent configurations,
for every set of small moduli (primes included) and every placement of the large scale.

Against the large-sieve dispersion `½ √(Σ c(p)² p²) √(L + 2Q₀² - 1) √(Σ c'(n)²/n⁴)` with
`c = 1_{S'}`, `c' = 1_{[n₀, n₀+H)}`, `S ⊆ (D/2, D]`, `H ≍ D`, the two bounds differ by
`≍ √(|S|/D)`. The large-sieve threshold `Q ≥ P^{5/3}` for diagonal quality of Type-II cross-scale
forms is sharp up to `√(log P)` for prime packets. Below it no Type-II input escapes the
rank-two law with a diagonal-size remainder. The replacement hypothesis is equidistribution of the
large-scale coefficients across the near-multiple windows `{n : n mod p ≤ p/32}`, i.e.
cancellation of `Σ_{n ∈ I} c'(n)` on intervals `I` of length `≍ P` placed against coherent residues.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Positivity of the Bernoulli kernel near multiples -/

theorem residuePotential_ge {d : ℕ} (M : ℕ) :
    -(((d : ℝ) ^ 2 + 2) / 24) ≤ residuePotential d M := by
  unfold residuePotential
  nlinarith [sq_nonneg ((d : ℝ) - 2 * ((M % d : ℕ) : ℝ))]

theorem residuePotential_ge_sub (d M : ℕ) :
    ((d : ℝ) ^ 2 - 1) / 12 - ((M % d : ℕ) : ℝ) * d / 2 ≤ residuePotential d M := by
  unfold residuePotential
  have : (0 : ℝ) ≤ ((M % d : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this this]

/-- **Bernoulli positivity.** If `32 (n mod d) ≤ d` then `𝔅(d, n) ≥ d²/25 - 1/4`. -/
theorem bernoulliKernel_ge {d n : ℕ} (hd : 0 < d) (hn : 32 * (n % d) ≤ d) :
    (d : ℝ) ^ 2 / 25 - 1 / 4 ≤ bernoulliKernel d n := by
  have hS := summable_residuePotential_div_sq hd n
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, one_pow,
      div_one, Nat.cast_add, Nat.cast_ofNat] at h
    exact h
  set K : ℝ := ((d : ℝ) ^ 2 + 2) / 24
  have htail : -K * (Real.pi ^ 2 / 6 - 1) ≤
      ∑' j : ℕ, residuePotential d ((j + 1 + 1) * n) / (((j + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    rw [← (hz.mul_left (-K)).tsum_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) (hz.mul_left _).summable
      ((summable_nat_add_iff 1).mpr hS)
    have h : -K ≤ residuePotential d ((j + 1 + 1) * n) := residuePotential_ge _
    have hpos : (0 : ℝ) < ((j : ℝ) + 2) ^ 2 := by positivity
    push_cast
    rw [show (j : ℝ) + 1 + 1 = j + 2 by ring, mul_one_div, neg_div,
      ← sub_nonneg, sub_neg_eq_add, ← add_div]
    exact div_nonneg (by linarith) hpos.le
  have hhead : ((d : ℝ) ^ 2 - 1) / 12 - (d : ℝ) ^ 2 / 64 ≤
      residuePotential d ((0 + 1) * n) / (((0 : ℕ) : ℝ) + 1) ^ 2 := by
    simp only [zero_add, one_mul, Nat.cast_zero, one_pow, div_one]
    refine le_trans ?_ (residuePotential_ge_sub d n)
    have h32 : 32 * ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast hn
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith
  have hpi : Real.pi ^ 2 < 9.9225 := by
    have := Real.pi_lt_d2
    have := Real.pi_pos
    nlinarith
  rw [bernoulliKernel, hS.tsum_eq_zero_add]
  have hK : 0 ≤ K := by positivity
  have hprod := mul_le_mul_of_nonneg_left hpi.le hK
  simp only [K] at hprod htail
  nlinarith

/-! ## §2. Coherent windows and the coherent shift -/

/-- If `64 (n₀ mod d) ≤ d` and `64 H ≤ d`, every `n₀ + t`, `t < H`, satisfies `32 ((n₀+t) mod d) ≤ d`. -/
theorem mod_add_coherent {d n₀ t H : ℕ} (h₀ : 64 * (n₀ % d) ≤ d) (ht : t < H) (hH : 64 * H ≤ d) :
    32 * ((n₀ + t) % d) ≤ d := by
  have hd : 0 < d := by omega
  have hlt := Nat.mod_lt n₀ hd
  have hmod : (n₀ + t) % d = n₀ % d + t := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : t < d), Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  omega

theorem card_filter_Ico_mul_eq {d : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hp : Function.Periodic p d) (Q k : ℕ) :
    ((Ico Q (Q + k * d)).filter p).card = k * Nat.count p d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [card_filter, show Q + (k + 1) * d = Q + k * d + d by ring,
      ← sum_Ico_consecutive _ (by omega : Q ≤ Q + k * d) (by omega : Q + k * d ≤ Q + k * d + d),
      ← card_filter, ← card_filter, ih, Nat.filter_Ico_card_eq_of_periodic _ _ p hp]
    ring

/-- In any `T` consecutive integers at least `(T - d)/64` lie in `[0, d/64]` modulo `d`. -/
theorem card_filter_Ico_mod_small_ge {d : ℕ} (hd : 0 < d) (Q T : ℕ) :
    T ≤ d + 64 * ((Ico Q (Q + T)).filter fun n => 64 * (n % d) ≤ d).card := by
  set p : ℕ → Prop := fun n => 64 * (n % d) ≤ d
  have hper : Function.Periodic p d := fun n => by simp only [p, Nat.add_mod_right]
  have hcount : d ≤ 64 * Nat.count p d := by
    rw [Nat.count_eq_card_filter_range]
    have hsub : range (d / 64 + 1) ⊆ {x ∈ range d | p x} := by
      intro x hx
      have hx' := mem_range.mp hx
      have hxd : x < d := by omega
      simp only [mem_filter, mem_range, p, Nat.mod_eq_of_lt hxd]
      exact ⟨hxd, by omega⟩
    have := card_le_card hsub
    rw [card_range] at this
    omega
  have hblock := card_filter_Ico_mul_eq p hper Q (T / d)
  have hmono : ((Ico Q (Q + T / d * d)).filter p).card ≤ ((Ico Q (Q + T)).filter p).card :=
    card_le_card (filter_subset_filter _ (Ico_subset_Ico_right (by
      have := Nat.div_mul_le_self T d; omega)))
  have hT : T ≤ d + T / d * d := by
    have := Nat.div_add_mod T d
    have := Nat.mod_lt T hd
    nlinarith
  calc T ≤ d + T / d * d := hT
    _ ≤ d + T / d * (64 * Nat.count p d) := by gcongr
    _ = d + 64 * ((Ico Q (Q + T / d * d)).filter p).card := by rw [hblock]; ring
    _ ≤ d + 64 * ((Ico Q (Q + T)).filter p).card := by gcongr

/-- **The coherent shift.** For moduli `S ⊆ [1, D]` and any `Q` there is `n₀ ∈ [Q, Q + 2D)` with
`|S| ≤ 128 |{d ∈ S : 64 (n₀ mod d) ≤ d}|`. -/
theorem exists_coherent_shift {S : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hS : ∀ d ∈ S, 0 < d ∧ d ≤ D) (Q : ℕ) :
    ∃ n₀ ∈ Ico Q (Q + 2 * D), S.card ≤ 128 * (S.filter fun d => 64 * (n₀ % d) ≤ d).card := by
  classical
  have hne : (Ico Q (Q + 2 * D)).Nonempty := nonempty_Ico.mpr (by omega)
  refine exists_le_of_sum_le hne ?_
  have hswap : ∑ n₀ ∈ Ico Q (Q + 2 * D), (S.filter fun d => 64 * (n₀ % d) ≤ d).card =
      ∑ d ∈ S, ((Ico Q (Q + 2 * D)).filter fun n₀ => 64 * (n₀ % d) ≤ d).card := by
    simp only [card_filter]
    exact sum_comm
  have hd : ∀ d ∈ S, D ≤ 64 * ((Ico Q (Q + 2 * D)).filter fun n₀ => 64 * (n₀ % d) ≤ d).card :=
    fun d hdS => by
      have := card_filter_Ico_mod_small_ge (hS d hdS).1 Q (2 * D)
      have := (hS d hdS).2
      omega
  rw [← mul_sum, hswap, sum_const, Nat.card_Ico, smul_eq_mul, show Q + 2 * D - Q = 2 * D by omega]
  calc 2 * D * S.card = 2 * ∑ _d ∈ S, D := by rw [sum_const, smul_eq_mul]; ring
    _ ≤ 2 * ∑ d ∈ S, 64 * ((Ico Q (Q + 2 * D)).filter fun n₀ => 64 * (n₀ % d) ≤ d).card :=
        Nat.mul_le_mul_left _ (sum_le_sum hd)
    _ = 128 * ∑ d ∈ S, ((Ico Q (Q + 2 * D)).filter fun n₀ => 64 * (n₀ % d) ≤ d).card := by
        rw [← mul_sum]; ring

/-! ## §3. The coherent lower bound -/

/-- **The coherent lower bound.** Let every modulus `d ∈ S` satisfy `64 H ≤ d ≤ D` and
`64 (n₀ mod d) ≤ d`, with `0 < D`, `75 D ≤ n₀` and `1 ≤ H`. For nonnegative rows `c` on `S` and `c'` on
`[n₀, n₀ + H)`,
`B(c, c') + m(c) R(c') + β(c) H(c') ≥ (1/100)(Σ_d c(d) d)(Σ_n c'(n)/n²)`. -/
theorem coherent_lower_bound {N D H n₀ : ℕ} {S : Finset ℕ} {c c' : ℕ → ℝ} (hH : 1 ≤ H)
    (hS : ∀ d ∈ S, 64 * H ≤ d ∧ d ≤ D ∧ 64 * (n₀ % d) ≤ d) (hD0 : 0 < D) (hD : 75 * D ≤ n₀)
    (hc : ∀ d, c d ≠ 0 → d ∈ S) (hc0 : ∀ d, 0 ≤ c d)
    (hc' : ∀ n, c' n ≠ 0 → n ∈ Ico n₀ (n₀ + H)) (hc'0 : ∀ n, 0 ≤ c' n) :
    1 / 100 * (∑ d ∈ Icc 1 N, c d * d) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 ≤
      rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set E := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c'
  set A := ∑ d ∈ Icc 1 N, c d * d
  set B := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  have hA : 0 ≤ A := sum_nonneg fun d _ => mul_nonneg (hc0 d) (Nat.cast_nonneg _)
  have hB : 0 ≤ B := sum_nonneg fun n _ => div_nonneg (hc'0 n) (by positivity)
  -- the kernel term is at least `A B / 50`
  have hmain : 1 / 50 * (A * B) ≤
      ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2) := by
    rw [show A * B = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * c d * d / (n : ℝ) ^ 2 by
      rw [mul_comm, sum_mul_sum]
      exact sum_congr rfl fun n _ => sum_congr rfl fun d _ => by ring, mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [mul_sum]
    refine sum_le_sum fun d hd => ?_
    by_cases hcn : c' n = 0
    · simp [hcn]
    by_cases hcd : c d = 0
    · simp [hcd]
    obtain ⟨hHd, -, hcoh⟩ := hS d (hc d hcd)
    have hwin := mem_Ico.mp (hc' n hcn)
    have h32 : 32 * (n % d) ≤ d := by
      have := mod_add_coherent (t := n - n₀) hcoh (by omega) hHd
      rwa [show n₀ + (n - n₀) = n by omega] at this
    have hd0 : 0 < d := by omega
    have hdR : (64 : ℝ) ≤ d := by exact_mod_cast (by omega : 64 ≤ d)
    have hK := bernoulliKernel_ge hd0 h32
    have hK' : (d : ℝ) ^ 2 / 50 ≤ bernoulliKernel d n := by nlinarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hdpos : (0 : ℝ) < d := by linarith
    have hfac : 0 ≤ c' n * (c d / d) / (n : ℝ) ^ 2 :=
      div_nonneg (mul_nonneg (hc'0 n) (div_nonneg (hc0 d) hdpos.le)) (by positivity)
    calc 1 / 50 * (c' n * c d * d / (n : ℝ) ^ 2)
        = c' n * (c d / d) / (n : ℝ) ^ 2 * ((d : ℝ) ^ 2 / 50) := by field_simp
      _ ≤ c' n * (c d / d) / (n : ℝ) ^ 2 * bernoulliKernel d n :=
          mul_le_mul_of_nonneg_left hK' hfac
      _ = _ := by ring
  -- the error is at most `A B / 100`
  have herr : 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 ≤
      1 / 100 * (A * B) := by
    have h1 : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 ≤ D * A := by
      rw [mul_sum]
      refine sum_le_sum fun d _ => ?_
      rw [abs_of_nonneg (hc0 d)]
      by_cases hcd : c d = 0
      · simp [hcd]
      have hdD : (d : ℝ) ≤ D := by exact_mod_cast (hS d (hc d hcd)).2.1
      have hmul := mul_le_mul_of_nonneg_left hdD (mul_nonneg (hc0 d) (Nat.cast_nonneg d))
      calc c d * (d : ℝ) ^ 2 = c d * d * d := by ring
        _ ≤ c d * d * D := hmul
        _ = D * (c d * d) := by ring
    have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast (by omega : 0 < n₀)
    have h2 : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 ≤ B / n₀ := by
      rw [div_eq_mul_inv B, sum_mul]
      refine sum_le_sum fun n hn => ?_
      rw [abs_of_nonneg (hc'0 n)]
      by_cases hcn : c' n = 0
      · simp [hcn]
      have hn₀ : (n₀ : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp (hc' n hcn)).1
      have hnR : (0 : ℝ) < n := lt_of_lt_of_le hn₀pos hn₀
      rw [show c' n / (n : ℝ) ^ 3 = c' n / (n : ℝ) ^ 2 * (n : ℝ)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hn₀pos hn₀) (div_nonneg (hc'0 n) (by positivity))
    have hDn : (75 : ℝ) * D ≤ n₀ := by exact_mod_cast hD
    have hDpos : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hsum1 : 0 ≤ ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := sum_nonneg fun d _ => by positivity
    calc 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (D * A) * (B / n₀) := by gcongr
      _ = 3 / 4 * (D / n₀) * (A * B) := by ring
      _ ≤ 1 / 100 * (A * B) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hA hB)
          have : (D : ℝ) / n₀ ≤ 1 / 75 := by
            rw [div_le_iff₀ hn₀pos]; linarith
          linarith
  have hlow := (abs_le.mp hlaw).1
  nlinarith [hmain, herr]

/-- The trivial remainder bound `2 K_c Σ|c'(n)|/n²` of the rank-two law is attained up to the
factor `100` on coherent configurations. -/
theorem coherent_lower_bound_rowFluctBound {N D H n₀ : ℕ} {S : Finset ℕ} {c c' : ℕ → ℝ}
    (hH : 1 ≤ H) (hS : ∀ d ∈ S, 64 * H ≤ d ∧ d ≤ D ∧ 64 * (n₀ % d) ≤ d) (hD0 : 0 < D)
    (hD : 75 * D ≤ n₀) (hc : ∀ d, c d ≠ 0 → d ∈ S) (hc0 : ∀ d, 0 ≤ c d)
    (hc' : ∀ n, c' n ≠ 0 → n ∈ Ico n₀ (n₀ + H)) (hc'0 : ∀ n, 0 ≤ c' n) :
    1 / 100 * (2 * rowFluctBound N c * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) ≤
      rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' := by
  have h := coherent_lower_bound hH hS hD0 hD hc hc0 hc' hc'0 (N := N)
  have hK : 2 * rowFluctBound N c = ∑ d ∈ Icc 1 N, c d * d := by
    rw [rowFluctBound, mul_sum]
    exact sum_congr rfl fun d _ => by rw [abs_of_nonneg (hc0 d)]; ring
  have hB : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 = ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 :=
    sum_congr rfl fun n _ => by rw [abs_of_nonneg (hc'0 n)]
  rw [hK, hB, ← mul_assoc]
  exact h

/-- **Every set of small moduli has a coherent configuration.** For moduli `S ⊆ [64H, D]`,
`1 ≤ H`, `0 < D` and `Q ≥ 75 D`, there are `n₀ ∈ [Q, Q + 2D)` and `S' ⊆ S` with `|S| ≤ 128 |S'|`
such that every pair of nonnegative rows `c` on `S'` and `c'` on `[n₀, n₀ + H)` has
`B(c, c') + m(c) R(c') + β(c) H(c') ≥ (1/100)(Σ_d c(d) d)(Σ_n c'(n)/n²)`. -/
theorem exists_coherent_configuration {S : Finset ℕ} {D H Q : ℕ} (hH : 1 ≤ H) (hD0 : 0 < D)
    (hS : ∀ d ∈ S, 64 * H ≤ d ∧ d ≤ D) (hQ : 75 * D ≤ Q) :
    ∃ n₀ ∈ Ico Q (Q + 2 * D), ∃ S' ⊆ S, S.card ≤ 128 * S'.card ∧
      ∀ (N : ℕ) (c c' : ℕ → ℝ), (∀ d, c d ≠ 0 → d ∈ S') → (∀ d, 0 ≤ c d) →
        (∀ n, c' n ≠ 0 → n ∈ Ico n₀ (n₀ + H)) → (∀ n, 0 ≤ c' n) →
        1 / 100 * (∑ d ∈ Icc 1 N, c d * d) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 ≤
          rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
            rowBeta N c * finiteHarmonicSum N c' := by
  obtain ⟨n₀, hn₀, hcard⟩ := exists_coherent_shift hD0
    (fun d hd => ⟨by have := (hS d hd).1; omega, (hS d hd).2⟩) Q
  refine ⟨n₀, hn₀, S.filter fun d => 64 * (n₀ % d) ≤ d, filter_subset _ _, hcard, ?_⟩
  intro N c c' hc hc0 hc' hc'0
  refine coherent_lower_bound hH (fun d hd => ?_) hD0 (by have := (mem_Ico.mp hn₀).1; omega)
    hc hc0 hc' hc'0
  obtain ⟨hdS, hcoh⟩ := mem_filter.mp hd
  exact ⟨(hS d hdS).1, (hS d hdS).2, hcoh⟩

/-! ## §4. Against the diagonal -/

/-- **The coherent configuration exceeds the diagonal.** Let `S' ⊆ (D/2, D]` be coherent for `n₀`
(`64 (n₀ mod d) ≤ d`, `64 H ≤ d`), `0 < D`, `75 D ≤ n₀`, `1 ≤ H`, `n₀ + H ≤ N + 1`. For the
indicator rows `c = 1_{S'}`, `c' = 1_{[n₀, n₀+H)}`, i.e. `a_d = 1/d`, `b_n = 1/n` in
`Σ a_d b_n 𝒢(d, n) = B(c, c')`, with diagonal `D(a) D(b) = (Σ_{S'} 1/d)(Σ_W 1/n)`:
`E ≥ D |S'| H / (200 (n₀ + H)²)` and
`E² ≥ (1/80000) · D³ |S'| H n₀/(n₀ + H)⁴ · D(a) D(b)`,
where `E = B + m R' + β H'`. For primes `S' ≍ D/log D`, `H ≍ D`, `n₀ ≍ Q`, the remainder of the
rank-two law exceeds the diagonal by `≍ D^{5/2}/(Q^{3/2} √(log D))`. -/
theorem coherent_configuration_exceeds_diagonal {N D H n₀ : ℕ} {S' : Finset ℕ} (hH : 1 ≤ H)
    (hS : ∀ d ∈ S', 64 * H ≤ d ∧ d ≤ D ∧ D < 2 * d ∧ 64 * (n₀ % d) ≤ d) (hD0 : 0 < D)
    (hD : 75 * D ≤ n₀) (hN : n₀ + H ≤ N + 1) :
    (D : ℝ) * S'.card * H / (200 * ((n₀ : ℝ) + H) ^ 2) ≤
        rowBilinear N (fun d => if d ∈ S' then 1 else 0) (fun n => if n ∈ Ico n₀ (n₀ + H) then 1 else 0) +
          rowMean N (fun d => if d ∈ S' then 1 else 0) *
            vonMangoldtReadout N (fun n => if n ∈ Ico n₀ (n₀ + H) then 1 else 0) +
          rowBeta N (fun d => if d ∈ S' then 1 else 0) *
            finiteHarmonicSum N (fun n => if n ∈ Ico n₀ (n₀ + H) then 1 else 0) ∧
      1 / 80000 * ((D : ℝ) ^ 3 * S'.card * H * n₀ / ((n₀ : ℝ) + H) ^ 4) *
          ((∑ d ∈ S', 1 / (d : ℝ)) * ∑ n ∈ Ico n₀ (n₀ + H), 1 / (n : ℝ)) ≤
        (rowBilinear N (fun d => if d ∈ S' then 1 else 0)
            (fun n => if n ∈ Ico n₀ (n₀ + H) then 1 else 0) +
          rowMean N (fun d => if d ∈ S' then 1 else 0) *
            vonMangoldtReadout N (fun n => if n ∈ Ico n₀ (n₀ + H) then 1 else 0) +
          rowBeta N (fun d => if d ∈ S' then 1 else 0) *
            finiteHarmonicSum N (fun n => if n ∈ Ico n₀ (n₀ + H) then 1 else 0)) ^ 2 := by
  classical
  set W := Ico n₀ (n₀ + H)
  set c : ℕ → ℝ := fun d => if d ∈ S' then 1 else 0
  set c' : ℕ → ℝ := fun n => if n ∈ W then 1 else 0
  set E := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c'
  have hn₀ : (0 : ℝ) < n₀ := by exact_mod_cast (by omega : 0 < n₀)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlow := coherent_lower_bound (N := N) (S := S') (c := c) (c' := c') hH
    (fun d hd => ⟨(hS d hd).1, (hS d hd).2.1, (hS d hd).2.2.2⟩) hD0 hD
    (fun d hd => by by_contra h; exact hd (if_neg h)) (fun d => by simp only [c]; split_ifs <;> norm_num)
    (fun n hn => by by_contra h; exact hn (if_neg h)) (fun n => by simp only [c']; split_ifs <;> norm_num)
  have hS'N : S' ⊆ Icc 1 N := fun d hd => by
    have := hS d hd
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hWN : W ⊆ Icc 1 N := fun n hn => by
    have := mem_Ico.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hA : (D : ℝ) / 2 * S'.card ≤ ∑ d ∈ Icc 1 N, c d * d := by
    rw [← sum_subset hS'N fun d _ hd => by simp [c, hd]]
    rw [show (D : ℝ) / 2 * S'.card = ∑ _d ∈ S', (D : ℝ) / 2 by rw [sum_const, nsmul_eq_mul]; ring]
    refine sum_le_sum fun d hd => ?_
    simp only [c, if_pos hd, one_mul]
    have : (D : ℝ) < 2 * d := by exact_mod_cast (hS d hd).2.2.1
    linarith
  have hB : (H : ℝ) / ((n₀ : ℝ) + H) ^ 2 ≤ ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 := by
    rw [← sum_subset hWN fun n _ hn => by simp [c', hn]]
    rw [show (H : ℝ) / ((n₀ : ℝ) + H) ^ 2 = ∑ _n ∈ W, 1 / ((n₀ : ℝ) + H) ^ 2 by
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul, show n₀ + H - n₀ = H by omega]; ring]
    refine sum_le_sum fun n hn => ?_
    simp only [c', if_pos hn]
    have hn' := mem_Ico.mp hn
    have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn'.1
    have h2 : (n : ℝ) ≤ n₀ + H := by exact_mod_cast hn'.2.le
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hn₀ h1
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (pow_le_pow_left₀ hnpos.le h2 2)
  have hE1 : (D : ℝ) * S'.card * H / (200 * ((n₀ : ℝ) + H) ^ 2) ≤ E := by
    refine le_trans ?_ hlow
    have hcard : (0 : ℝ) ≤ S'.card := Nat.cast_nonneg _
    calc (D : ℝ) * S'.card * H / (200 * ((n₀ : ℝ) + H) ^ 2)
        = 1 / 100 * ((D : ℝ) / 2 * S'.card) * ((H : ℝ) / ((n₀ : ℝ) + H) ^ 2) := by
          field_simp; ring
      _ ≤ _ := by gcongr
  refine ⟨hE1, ?_⟩
  have hdiag1 : ∑ d ∈ S', 1 / (d : ℝ) ≤ 2 * S'.card / D := by
    rw [show 2 * (S'.card : ℝ) / D = ∑ _d ∈ S', 2 / (D : ℝ) by
      rw [sum_const, nsmul_eq_mul]; ring]
    refine sum_le_sum fun d hd => ?_
    have : (D : ℝ) < 2 * d := by exact_mod_cast (hS d hd).2.2.1
    rw [div_le_div_iff₀ (by linarith) hDR]
    linarith
  have hdiag2 : ∑ n ∈ W, 1 / (n : ℝ) ≤ H / n₀ := by
    rw [show (H : ℝ) / n₀ = ∑ _n ∈ W, 1 / (n₀ : ℝ) by
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul, show n₀ + H - n₀ = H by omega]; ring]
    refine sum_le_sum fun n hn => ?_
    exact one_div_le_one_div_of_le hn₀ (by exact_mod_cast (mem_Ico.mp hn).1)
  have hE0 : 0 ≤ (D : ℝ) * S'.card * H / (200 * ((n₀ : ℝ) + H) ^ 2) := by positivity
  have hsq := pow_le_pow_left₀ hE0 hE1 2
  refine le_trans ?_ hsq
  have hd1 : 0 ≤ ∑ d ∈ S', 1 / (d : ℝ) := sum_nonneg fun d _ => by positivity
  have hd2 : 0 ≤ ∑ n ∈ W, 1 / (n : ℝ) := sum_nonneg fun n _ => by positivity
  have hprod : (∑ d ∈ S', 1 / (d : ℝ)) * ∑ n ∈ W, 1 / (n : ℝ) ≤
      2 * S'.card / D * (H / n₀) := mul_le_mul hdiag1 hdiag2 hd2 (by positivity)
  have hpref : 0 ≤ 1 / 80000 * ((D : ℝ) ^ 3 * S'.card * H * n₀ / ((n₀ : ℝ) + H) ^ 4) := by
    positivity
  calc 1 / 80000 * ((D : ℝ) ^ 3 * S'.card * H * n₀ / ((n₀ : ℝ) + H) ^ 4) *
        ((∑ d ∈ S', 1 / (d : ℝ)) * ∑ n ∈ W, 1 / (n : ℝ))
      ≤ 1 / 80000 * ((D : ℝ) ^ 3 * S'.card * H * n₀ / ((n₀ : ℝ) + H) ^ 4) *
          (2 * S'.card / D * (H / n₀)) := mul_le_mul_of_nonneg_left hprod hpref
    _ = ((D : ℝ) * S'.card * H / (200 * ((n₀ : ℝ) + H) ^ 2)) ^ 2 := by
        field_simp
        ring

end

end GaloisForLFunctions.BezoutValuationIncidence
