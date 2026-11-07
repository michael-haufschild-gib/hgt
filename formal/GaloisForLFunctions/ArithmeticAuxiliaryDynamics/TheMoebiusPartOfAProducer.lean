import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheForcedJumpsOfAProducer
import GaloisForLFunctions.ArithmeticKreinLangerTheory.MultivariateParityAuxiliariesReachTheMainTerm

/-!
# The Möbius part of a producer

By rigidity, a constant window forces `c = m μ` on the window. So the core of every producer is the
sawtooth `F_T(r) = −Σ_{b ≤ T} (μ(b)/b) (r mod b)`. Its size is computable.

* For `1 ≤ r ≤ T`: `F_T(r) = 1 − r m(T)`, where `m(T) = Σ_{b ≤ T} μ(b)/b`.
* For `r > T`: `F_T(r) = 1 − r m(T) − E_T(r)`, with `E_T(r) = Σ_{T < b ≤ r} μ(b) ⌊r/b⌋`. By the
  hyperbola method, if `|M(y)| ≤ η y` for `y ≥ T`, then `|E_T(r)| ≤ 2 η r (1 + log r)`.
* Always `|F_T(r)| ≤ T`.

So the near behaviour of the Möbius part is controlled exactly by the Mertens function. This module
also turns a finite family of rational sawtooth weights into an integer producer.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- **Rational sawtooth weights give an integer producer.** Weights `q k` on letters `k ≥ 2`, with
nonnegative sum `f(r) = Σ q_k (r mod k)` and `f ≥ 1` on `[1, B)`, clear to an integer producer whose
slope is `m Σ q_k log k`. -/
theorem exists_producer_of_weights_coeff {J : Finset ℕ} (q : ℕ → ℚ) {B K : ℕ}
    (hJ2 : ∀ k ∈ J, 2 ≤ k) (hJK : ∀ k ∈ J, k ≤ K) (hK : 1 ≤ K) (hB : 2 ≤ B)
    (hnn : ∀ r, 0 ≤ ∑ k ∈ J, (q k : ℝ) * ((r % k : ℕ) : ℝ))
    (hwin : ∀ r ∈ Ico 1 B, 1 ≤ ∑ k ∈ J, (q k : ℝ) * ((r % k : ℕ) : ℝ)) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
      stencilSlope c = (m : ℝ) * ∑ k ∈ J, (q k : ℝ) * Real.log k ∧
      c.support ⊆ insert 1 J ∧ ∀ k ∈ J, (c k : ℝ) = -(m : ℝ) * k * (q k : ℝ) := by
  classical
  set D : ℕ := ∏ k ∈ J, (q k).den with hD
  have hD_pos : 0 < D := prod_pos fun k _ => (q k).pos
  have hD_real_pos : (0 : ℝ) < D := by exact_mod_cast hD_pos
  let z : ℕ → ℤ := fun k => (q k).num * ((D / (q k).den : ℕ) : ℤ)
  have hz_real : ∀ k ∈ J, (z k : ℝ) = (D : ℝ) * (q k : ℝ) := by
    intro k hk
    have hdvd : (q k).den ∣ D := dvd_prod_of_mem (fun j => (q j).den) hk
    have hden_ne : ((q k).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q k).pos.ne'
    simp only [z, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hden_ne, Rat.cast_def]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  let c : ℕ →₀ ℤ := Finsupp.single 1 (∑ k ∈ J, z k) + ∑ k ∈ J, Finsupp.single k (-(k : ℤ) * z k)
  have h1_notMem : 1 ∉ J := fun h => by have := hJ2 1 h; omega
  have hc0 : c 0 = 0 := by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega : (0 : ℕ) ≠ 1),
      Finsupp.finsetSum_apply, zero_add, sum_eq_zero]
    intro k hk
    have hk_ge2 := hJ2 k hk
    exact Finsupp.single_eq_of_ne (by omega : (0 : ℕ) ≠ k)
  have hc1 : c 1 = ∑ k ∈ J, z k := by
    have hsum0 : (∑ k ∈ J, Finsupp.single k (-(k : ℤ) * z k)) 1 = 0 := by
      rw [Finsupp.finsetSum_apply, sum_eq_zero]
      intro k hk
      exact Finsupp.single_eq_of_ne (fun h => h1_notMem (h ▸ hk))
    rw [Finsupp.add_apply, Finsupp.single_eq_same, hsum0, add_zero]
  have hc_mem : ∀ k ∈ J, c k = -(k : ℤ) * z k := by
    intro k hk
    have hk1 : k ≠ 1 := fun h => h1_notMem (h ▸ hk)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hk1, zero_add,
      Finsupp.finsetSum_apply, sum_eq_single k]
    · exact Finsupp.single_eq_same
    · intro j _ hjk
      exact Finsupp.single_eq_of_ne hjk.symm
    · intro h; exact absurd hk h
  have hc_out : ∀ k : ℕ, k ∉ insert 1 J → c k = 0 := by
    intro k hk
    have hk1 : k ≠ 1 := fun h => hk (mem_insert.mpr (Or.inl h))
    have hkJ : k ∉ J := fun h => hk (mem_insert.mpr (Or.inr h))
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hk1, zero_add,
      Finsupp.finsetSum_apply, sum_eq_zero]
    intro j hj
    exact Finsupp.single_eq_of_ne (fun h => hkJ (h ▸ hj))
  have hc_supp : c.support ⊆ insert 1 J := by
    intro k hk
    by_contra hnot
    exact Finsupp.mem_support_iff.mp hk (hc_out k hnot)
  have hbal : IsBalanced c := by
    rw [IsBalanced, sum_subset hc_supp (fun k _ hk => by
      rw [Finsupp.notMem_support_iff.mp hk, Int.cast_zero, zero_div]),
      sum_insert h1_notMem, hc1, Nat.cast_one, div_one, Int.cast_sum]
    have hsumJ : ∑ k ∈ J, (c k : ℝ) / k = -∑ k ∈ J, (z k : ℝ) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hJ2 k hk; omega)
      rw [hc_mem k hk]
      push_cast
      rw [div_eq_iff hk_ne]
      ring
    rw [hsumJ]
    ring
  have hstep_formula : ∀ r : ℕ, (stepWeight c r : ℝ) =
      (D : ℝ) * ∑ k ∈ J, (q k : ℝ) * ((r % k : ℕ) : ℝ) := by
    intro r
    rw [stepWeight_eq_sum_mod hc0 hbal r,
      sum_subset hc_supp (fun k _ hk => by
        rw [Finsupp.notMem_support_iff.mp hk, Int.cast_zero, neg_zero, zero_div, zero_mul]),
      sum_insert h1_notMem, Nat.mod_one, Nat.cast_zero, mul_zero, zero_add, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hJ2 k hk; omega)
    rw [hc_mem k hk]
    push_cast
    have hdiv : -(-(k : ℝ) * (z k : ℝ)) / k = (z k : ℝ) := by
      rw [div_eq_iff hk_ne]
      ring
    rw [hdiv, hz_real k hk]
    ring
  have hP : IsProducer c D B := by
    refine ⟨hc0, hbal, fun r => ?_, hD_pos, hB, fun r hr => ?_⟩
    · have hR : (0 : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep_formula r]
        exact mul_nonneg hD_real_pos.le (hnn r)
      exact_mod_cast hR
    · have hR : ((D : ℤ) : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep_formula r]
        push_cast
        calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (hwin r hr) hD_real_pos.le
      exact_mod_cast hR
  refine ⟨c, D, hP, fun k hk => ?_, ?_, hc_supp, fun k hk => ?_⟩
  · have := hc_supp hk
    rcases mem_insert.mp this with h | h
    · omega
    · exact hJK k h
  · rw [stencilSlope,
      sum_subset hc_supp (fun k _ hk => by
        rw [Finsupp.notMem_support_iff.mp hk, Int.cast_zero, neg_zero, zero_mul, zero_div]),
      sum_insert h1_notMem, Nat.cast_one, Real.log_one, mul_zero, zero_div, zero_add, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hJ2 k hk; omega)
    rw [hc_mem k hk]
    push_cast
    have hdiv : -(-(k : ℝ) * (z k : ℝ)) * Real.log k / k = (z k : ℝ) * Real.log k := by
      rw [div_eq_iff hk_ne]
      ring
    rw [hdiv, hz_real k hk]
    ring
  · rw [hc_mem k hk]
    push_cast
    rw [hz_real k hk]
    ring

/-- **Exact clearing of rational sawtooth weights.** Nonnegative rational sawtooth sums with value at
least `1` on a window clear to an integer producer, with no rounding error in the slope. -/
theorem exists_producer_of_weights {J : Finset ℕ} (q : ℕ → ℚ) {B K : ℕ}
    (hJ2 : ∀ k ∈ J, 2 ≤ k) (hJK : ∀ k ∈ J, k ≤ K) (hK : 1 ≤ K) (hB : 2 ≤ B)
    (hnn : ∀ r, 0 ≤ ∑ k ∈ J, (q k : ℝ) * ((r % k : ℕ) : ℝ))
    (hwin : ∀ r ∈ Ico 1 B, 1 ≤ ∑ k ∈ J, (q k : ℝ) * ((r % k : ℕ) : ℝ)) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
      stencilSlope c = (m : ℝ) * ∑ k ∈ J, (q k : ℝ) * Real.log k := by
  obtain ⟨c, m, h1, h2, h3, _⟩ := exists_producer_of_weights_coeff q hJ2 hJK hK hB hnn hwin
  exact ⟨c, m, h1, h2, h3⟩

/-- The Möbius sawtooth `F_T(r) = −Σ_{b ≤ T} (μ(b)/b) (r mod b)`. -/
def mobiusPart (T r : ℕ) : ℝ :=
  ∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ)

/-- The Mertens function. -/
def mertens (y : ℕ) : ℝ := ∑ b ∈ Ioc 0 y, (ArithmeticFunction.moebius b : ℝ)

/-- The harmonic Möbius sum `m(T) = Σ_{b ≤ T} μ(b)/b`. -/
def mobiusHarmonic (T : ℕ) : ℝ := ∑ b ∈ Icc 1 T, (ArithmeticFunction.moebius b : ℝ) / b

/-- The Möbius tail of the floor sum. -/
def mobiusTail (T s : ℕ) : ℝ :=
  ∑ b ∈ Ioc T s, (ArithmeticFunction.moebius b : ℝ) * ((s / b : ℕ) : ℝ)

private lemma abs_moebius_le (b : ℕ) : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **The sup bound.** `|F_T(r)| ≤ T`. -/
theorem abs_mobiusPart_le (T r : ℕ) : |mobiusPart T r| ≤ T := by
  rw [mobiusPart]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ b ∈ Icc 1 T, |(-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ)| ≤ 1 := by
    intro b hb
    have hb1 := (mem_Icc.mp hb).1
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb1
    have hmod : ((r % b : ℕ) : ℝ) ≤ b := by exact_mod_cast (Nat.mod_lt r hb1).le
    have h1 : |((r % b : ℕ) : ℝ)| = ((r % b : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hbR, h1]
    calc |(ArithmeticFunction.moebius b : ℝ)| / b * ((r % b : ℕ) : ℝ)
        ≤ 1 / b * b := by
          gcongr
          exact abs_moebius_le b
      _ = 1 := by field_simp
  refine (sum_le_sum hterm).trans ?_
  simp

/-- The sawtooth in floors: `F_T(r) = −r m(T) + Σ_{b ≤ T} μ(b) ⌊r/b⌋`. -/
theorem mobiusPart_eq (T r : ℕ) :
    mobiusPart T r = -((r : ℝ) * mobiusHarmonic T) +
      ∑ b ∈ Icc 1 T, (ArithmeticFunction.moebius b : ℝ) * ((r / b : ℕ) : ℝ) := by
  rw [mobiusPart, mobiusHarmonic, mul_sum, ← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun b hb => ?_
  have hb1 := (mem_Icc.mp hb).1
  have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiv : (b : ℝ) * ((r / b : ℕ) : ℝ) + ((r % b : ℕ) : ℝ) = r := by
    exact_mod_cast Nat.div_add_mod r b
  have hmod : ((r % b : ℕ) : ℝ) = (r : ℝ) - (b : ℝ) * ((r / b : ℕ) : ℝ) := by linarith
  rw [hmod]
  field_simp
  ring

/-- **The exact window.** For `1 ≤ s ≤ T`, `Σ_{b ≤ T} μ(b) ⌊s/b⌋ = 1`. -/
theorem sum_moebius_floor_of_le {T s : ℕ} (hs : 1 ≤ s) (hsT : s ≤ T) :
    ∑ b ∈ Icc 1 T, (ArithmeticFunction.moebius b : ℝ) * ((s / b : ℕ) : ℝ) = 1 := by
  rw [← sum_Icc_moebius_mul_div_eq_one hs]
  symm
  refine sum_subset (Icc_subset_Icc_right hsT) fun b hb hb' => ?_
  have hb1 := (mem_Icc.mp hb).1
  have hlt : s < b := by
    by_contra h
    exact hb' (mem_Icc.mpr ⟨hb1, by omega⟩)
  rw [Nat.div_eq_of_lt hlt]
  simp

/-- **Beyond the window.** For `s > T`, `Σ_{b ≤ T} μ(b) ⌊s/b⌋ = 1 − E_T(s)`. -/
theorem sum_moebius_floor_of_gt {T s : ℕ} (hsT : T < s) :
    ∑ b ∈ Icc 1 T, (ArithmeticFunction.moebius b : ℝ) * ((s / b : ℕ) : ℝ) = 1 - mobiusTail T s := by
  have hs : 1 ≤ s := by omega
  have hfull := sum_Icc_moebius_mul_div_eq_one hs
  have hsplit : Icc 1 s = Icc 1 T ∪ Ioc T s := by
    ext b
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 T) (Ioc T s) := by
    rw [Finset.disjoint_left]
    intro b h1 h2
    simp only [mem_Icc, mem_Ioc] at h1 h2
    omega
  rw [hsplit, sum_union hdisj] at hfull
  rw [mobiusTail]
  linarith

/-- The hyperbola method for the Möbius tail. -/
private lemma mobiusTail_eq (T s : ℕ) :
    mobiusTail T s = ∑ j ∈ Icc 1 s, ∑ b ∈ Ioc T (s / j), (ArithmeticFunction.moebius b : ℝ) := by
  classical
  have hcount : ∀ b ∈ Ioc T s, (ArithmeticFunction.moebius b : ℝ) * ((s / b : ℕ) : ℝ) =
      ∑ j ∈ Icc 1 s, if b ≤ s / j then (ArithmeticFunction.moebius b : ℝ) else 0 := by
    intro b hb
    obtain ⟨_, hbs⟩ := mem_Ioc.mp hb
    have hb0 : 0 < b := by
      have := (mem_Ioc.mp hb).1
      omega
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have hset : (Icc 1 s).filter (fun j => b ≤ s / j) = Icc 1 (s / b) := by
      ext j
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hj1, _⟩, hj⟩
        refine ⟨hj1, ?_⟩
        rw [Nat.le_div_iff_mul_le hb0]
        have := (Nat.le_div_iff_mul_le (by omega : 0 < j)).mp hj
        rwa [mul_comm]
      · rintro ⟨hj1, hj⟩
        have hjb : j * b ≤ s := (Nat.le_div_iff_mul_le hb0).mp hj
        refine ⟨⟨hj1, (Nat.le_mul_of_pos_right j hb0).trans hjb⟩, ?_⟩
        rw [Nat.le_div_iff_mul_le (by omega : 0 < j)]
        rwa [mul_comm]
    rw [hset, Nat.card_Icc]
    simp
  rw [mobiusTail, sum_congr rfl hcount, sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext b
  have hj1 := (mem_Icc.mp hj).1
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, h3.trans (Nat.div_le_self s j)⟩, h3⟩

/-- **The Möbius tail is bounded by the Mertens function.** If `|M(y)| ≤ η y` for `y ≥ T`, then
`|E_T(s)| ≤ 2 η s (1 + log s)`. -/
theorem abs_mobiusTail_le {T s : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y) :
    |mobiusTail T s| ≤ 2 * η * s * (1 + Real.log s) := by
  rw [mobiusTail_eq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hterm : ∀ j ∈ Icc 1 s, |∑ b ∈ Ioc T (s / j), (ArithmeticFunction.moebius b : ℝ)| ≤
      2 * η * s * (1 / (j : ℝ)) := by
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
    by_cases hTy : T < s / j
    · have hsplit : ∑ b ∈ Ioc T (s / j), (ArithmeticFunction.moebius b : ℝ) =
          mertens (s / j) - mertens T := by
        rw [mertens, mertens, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le T) hTy.le]
        ring
      rw [hsplit]
      have hy : ((s / j : ℕ) : ℝ) ≤ (s : ℝ) / j := Nat.cast_div_le
      have hTR : (T : ℝ) ≤ ((s / j : ℕ) : ℝ) := by exact_mod_cast hTy.le
      calc |mertens (s / j) - mertens T| ≤ |mertens (s / j)| + |mertens T| := abs_sub _ _
        _ ≤ η * ((s / j : ℕ) : ℝ) + η * T := add_le_add (hM _ hTy.le) (hM _ le_rfl)
        _ ≤ η * ((s : ℝ) / j) + η * ((s : ℝ) / j) := by gcongr; exact hTR.trans hy
        _ = _ := by ring
    · rw [Ioc_eq_empty_of_le (not_lt.mp hTy), sum_empty, abs_zero]
      positivity
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hH := harmonic_le_one_add_log s
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  have hsum : ∑ j ∈ Icc 1 s, (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log s := by
    refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) hH
    rw [one_div]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **The near law of the Möbius part.** For `s ≥ 1`, if `|M(y)| ≤ η y` on `y ≥ T`, then
`|F_T(s) − 1| ≤ s (|m(T)| + 2 η (1 + log s))`. -/
theorem abs_mobiusPart_sub_one_le {T s : ℕ} (hs : 1 ≤ s) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y) :
    |mobiusPart T s - 1| ≤ (s : ℝ) * (|mobiusHarmonic T| + 2 * η * (1 + Real.log s)) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : 0 ≤ Real.log (s : ℝ) := Real.log_natCast_nonneg s
  have hsm : |(s : ℝ) * mobiusHarmonic T| = (s : ℝ) * |mobiusHarmonic T| := by
    rw [abs_mul, abs_of_pos hs0]
  rw [mobiusPart_eq]
  by_cases hsT : s ≤ T
  · rw [sum_moebius_floor_of_le hs hsT]
    have hrew : -((s : ℝ) * mobiusHarmonic T) + 1 - 1 = -((s : ℝ) * mobiusHarmonic T) := by ring
    rw [hrew, abs_neg, hsm]
    have : 0 ≤ (s : ℝ) * (2 * η * (1 + Real.log s)) := by positivity
    nlinarith
  · push Not at hsT
    rw [sum_moebius_floor_of_gt hsT]
    have hrew : -((s : ℝ) * mobiusHarmonic T) + (1 - mobiusTail T s) - 1 =
        -((s : ℝ) * mobiusHarmonic T) - mobiusTail T s := by ring
    rw [hrew]
    have h1 := abs_mobiusTail_le (s := s) hη hM
    calc |-((s : ℝ) * mobiusHarmonic T) - mobiusTail T s|
        ≤ |-((s : ℝ) * mobiusHarmonic T)| + |mobiusTail T s| := abs_sub _ _
      _ ≤ (s : ℝ) * |mobiusHarmonic T| + 2 * η * s * (1 + Real.log s) := by
          rw [abs_neg, hsm]
          linarith
      _ = _ := by ring

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
