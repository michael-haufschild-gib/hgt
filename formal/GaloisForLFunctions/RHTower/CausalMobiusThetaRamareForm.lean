import GaloisForLFunctions.RHTower.CausalMobiusThetaStability

/-!
# The Ramaré prime–cofactor form of the causal tail and its diagonal energy

For `t ≥ 1`, reindexing every squarefree `n > t` by its prime divisors gives the absolutely
convergent double series

`B(t) = −Σ_p Σ_{m ≥ 1, p ∤ m, pm > t} μ(m)/(ω(m)+1) · k(log(pm/t))/√(pm)`  (9)

and its diagonal energy is `Σ_{n>t sqfree} a_t(n)²/ω(n) ≤ Σ_{n>t} k(log(n/t))²/n = O(1)`  (10).
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- `a_t(n) = n^{−1/2} k(log(n/t))`. -/
def causalAmplitude (t : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log (n / t))

/-- The Ramaré cofactor term on `(p, m)`: `−μ(m)/(ω(m)+1) a_t(pm)` for prime `p ∤ m`, `pm > t`. -/
def ramareCofactorTerm (t : ℝ) (pm : ℕ × ℕ) : ℝ :=
  if pm.1.Prime ∧ ¬ pm.1 ∣ pm.2 ∧ t < ((pm.1 * pm.2 : ℕ) : ℝ) then
    -((ArithmeticFunction.moebius pm.2 : ℤ) : ℝ) / ((pm.2.primeFactors.card : ℝ) + 1) *
      causalAmplitude t (pm.1 * pm.2)
  else 0

theorem exists_causalAmplitude_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (n : ℕ), 0 < t → t < n →
      0 ≤ causalAmplitude t n ∧ causalAmplitude t n ≤ C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le 2
  refine ⟨C, hC0, fun t n ht htn => ?_⟩
  have hn : (0 : ℝ) < n := ht.trans htn
  have hlog : 0 ≤ Real.log (n / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hk := hC (Real.log (n / t))
  rw [abs_of_nonneg hlog, abs_of_pos (HedenmalmThetaSource.thetaCuspFullSource_pos _)] at hk
  have hexp : Real.exp (-(2 * Real.log (n / t))) = (t / n) ^ 2 := by
    rw [show -(2 * Real.log (n / t)) = (2 : ℕ) * Real.log (t / n) by
      rw [Real.log_div hn.ne' ht.ne', Real.log_div ht.ne' hn.ne']; push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (div_pos ht hn)]
  rw [hexp] at hk
  refine ⟨mul_nonneg (Real.rpow_nonneg hn.le _) (HedenmalmThetaSource.thetaCuspFullSource_pos _).le, ?_⟩
  have hsplit : (n : ℝ) ^ (-(5 / 2 : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hn.le, ← Real.rpow_add hn]; norm_num
  rw [causalAmplitude, hsplit]
  calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log (n / t))
      ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (C * (t / n) ^ 2) :=
        mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hn.le _)
    _ = C * t ^ 2 * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) ^ 2)⁻¹) := by field_simp

theorem natCast_mul_rpow_neg_five_halves (p m : ℕ) :
    ((p * m : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) = (p : ℝ) ^ (-(5 / 2 : ℝ)) * (m : ℝ) ^ (-(5 / 2 : ℝ)) := by
  push_cast; exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem abs_ramareCofactorTerm_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (t : ℝ) (n : ℕ), 0 < t → t < n →
      0 ≤ causalAmplitude t n ∧ causalAmplitude t n ≤ C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)))
    {t : ℝ} (ht : 0 < t) (pm : ℕ × ℕ) :
    |ramareCofactorTerm t pm| ≤ C * t ^ 2 * ((pm.1 : ℝ) ^ (-(5 / 2 : ℝ)) * (pm.2 : ℝ) ^ (-(5 / 2 : ℝ))) := by
  rw [ramareCofactorTerm]
  split_ifs with h
  · obtain ⟨-, -, htn⟩ := h
    obtain ⟨h0, h1⟩ := hC t _ ht htn
    have hμ : |((ArithmeticFunction.moebius pm.2 : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hden : (1 : ℝ) ≤ (pm.2.primeFactors.card : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) pm.2.primeFactors.card]
    rw [abs_mul, abs_div, abs_neg, abs_of_nonneg h0,
      abs_of_pos (show (0 : ℝ) < (pm.2.primeFactors.card : ℝ) + 1 by positivity),
      ← natCast_mul_rpow_neg_five_halves]
    calc |((ArithmeticFunction.moebius pm.2 : ℤ) : ℝ)| / ((pm.2.primeFactors.card : ℝ) + 1) *
          causalAmplitude t (pm.1 * pm.2)
        ≤ 1 * (C * t ^ 2 * ((pm.1 * pm.2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) := by
          refine mul_le_mul ?_ h1 h0 zero_le_one
          rw [div_le_one (by linarith)]; linarith
      _ = _ := one_mul _
  · rw [abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem summable_ramareCofactorTerm {t : ℝ} (ht : 0 < t) : Summable (ramareCofactorTerm t) := by
  obtain ⟨C, hC0, hC⟩ := exists_causalAmplitude_le
  have hnorm : Summable fun p : ℕ => ‖(p : ℝ) ^ (-(5 / 2 : ℝ))‖ := by
    refine summable_natCast_rpow_neg_five_halves.congr fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hs : Summable fun pm : ℕ × ℕ => (pm.1 : ℝ) ^ (-(5 / 2 : ℝ)) * (pm.2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
    summable_mul_of_summable_norm (f := fun p : ℕ => (p : ℝ) ^ (-(5 / 2 : ℝ)))
      (g := fun m : ℕ => (m : ℝ) ^ (-(5 / 2 : ℝ))) hnorm hnorm
  exact Summable.of_norm_bounded (hs.mul_left (C * t ^ 2)) fun pm => by
    rw [Real.norm_eq_abs]; exact abs_ramareCofactorTerm_le hC0 hC ht pm

theorem primeFactors_card_prime_mul {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    (p * m).primeFactors.card = m.primeFactors.card + 1 := by
  rw [Nat.primeFactors_mul hp.ne_zero hm, hp.primeFactors, Finset.singleton_union,
    Finset.card_insert_of_notMem (fun h => hpm (Nat.dvd_of_mem_primeFactors h))]

/-- The fiber of `(p, m) ↦ pm` over `n`, read through the prime factors of `n`. -/
theorem tsum_fiber_eq_sum_primeFactors (f : ℕ × ℕ → ℝ) (hf : ∀ pm : ℕ × ℕ, ¬ pm.1.Prime → f pm = 0)
    {n : ℕ} (hn : n ≠ 0) :
    ∑' b : (fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {n}, f b = ∑ p ∈ n.primeFactors, f (p, n / p) := by
  rw [tsum_subtype ((fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {n}) f]
  have hinj : Set.InjOn (fun p : ℕ => (p, n / p)) n.primeFactors := fun a _ b _ h => by
    simpa using congrArg Prod.fst h
  rw [tsum_eq_sum (s := n.primeFactors.image fun p => (p, n / p)), Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpn := Nat.dvd_of_mem_primeFactors hp
    rw [Set.indicator_of_mem (show (p, n / p) ∈ (fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {n} from
      by simp [Nat.mul_div_cancel' hpn])]
  · intro b hb
    by_cases hmem : b ∈ (fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {n}
    · rw [Set.indicator_of_mem hmem]
      have hbn : b.1 * b.2 = n := hmem
      by_cases hp : b.1.Prime
      · exfalso; apply hb
        rw [Finset.mem_image]
        refine ⟨b.1, Nat.mem_primeFactors.2 ⟨hp, ⟨b.2, hbn.symm⟩, hn⟩, ?_⟩
        ext
        · rfl
        · simp only; rw [← hbn, Nat.mul_div_cancel_left _ hp.pos]
      · exact hf b hp
    · exact Set.indicator_of_notMem hmem _

/-- The Ramaré fiber identity: over `n`, the cofactor terms recombine to `μ(n) a_t(n)`. -/
theorem sum_primeFactors_ramareCofactorTerm {t : ℝ} (ht : 1 ≤ t) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.primeFactors, ramareCofactorTerm t (p, n / p) = causalMobiusThetaTerm t n := by
  by_cases htn : t < n
  · have hn1 : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith)
    have hterm : causalMobiusThetaTerm t n = ((ArithmeticFunction.moebius n : ℤ) : ℝ) * causalAmplitude t n := by
      rw [causalMobiusThetaTerm, Set.indicator_of_mem (show t ∈ Ioo 0 (n : ℝ) from ⟨by linarith, htn⟩),
        causalAmplitude]; ring
    rw [hterm]
    by_cases hsq : Squarefree n
    · have hω : (n.primeFactors.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.2 (Nat.nonempty_primeFactors.2 hn1)).ne'
      have heach : ∀ p ∈ n.primeFactors, ramareCofactorTerm t (p, n / p) =
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) * causalAmplitude t n / n.primeFactors.card := by
        intro p hp
        have hpP := Nat.prime_of_mem_primeFactors hp
        have hpn := Nat.dvd_of_mem_primeFactors hp
        have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
        have hpm : ¬ p ∣ n / p := by
          intro h
          have := hsq p (by rw [← hmul]; exact Nat.mul_dvd_mul_left p h)
          exact hpP.one_lt.ne' (Nat.isUnit_iff.1 this)
        have hm0 : n / p ≠ 0 := by
          intro h; rw [h, mul_zero] at hmul; exact hn hmul.symm
        rw [ramareCofactorTerm, if_pos ⟨hpP, hpm, by simp only; rw [hmul]; exact htn⟩]
        simp only
        rw [hmul]
        have hμ : ArithmeticFunction.moebius n = -ArithmeticFunction.moebius (n / p) := by
          conv_lhs => rw [← hmul]
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
            ((Nat.Prime.coprime_iff_not_dvd hpP).2 hpm), ArithmeticFunction.moebius_apply_prime hpP]
          ring
        have hcard : (n.primeFactors.card : ℝ) = ((n / p).primeFactors.card : ℝ) + 1 := by
          conv_lhs => rw [← hmul]
          rw [primeFactors_card_prime_mul hpP hpm hm0]; push_cast; ring
        rw [hcard, hμ]
        push_cast
        ring
      rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul]
      field_simp
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero, zero_mul]
      refine Finset.sum_eq_zero fun p hp => ?_
      have hpP := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
      rw [ramareCofactorTerm]
      split_ifs with h
      · have hsqm : ¬ Squarefree (n / p) := by
          intro hsqm
          apply hsq
          rw [← hmul]
          exact (Nat.squarefree_mul ((Nat.Prime.coprime_iff_not_dvd hpP).2 h.2.1)).2
            ⟨hpP.squarefree, hsqm⟩
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqm]
        simp
      · rfl
  · rw [causalMobiusThetaTerm, Set.indicator_of_notMem fun h => htn h.2]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
    rw [ramareCofactorTerm, if_neg]
    rintro ⟨-, -, h⟩
    simp only at h
    rw [hmul] at h
    exact htn h

/-- **(9) The Ramaré prime–cofactor form**, as an absolutely convergent double series. -/
theorem hasSum_ramareCofactorTerm {t : ℝ} (ht : 1 ≤ t) :
    HasSum (ramareCofactorTerm t) (causalMobiusThetaTail t) := by
  have hs := summable_ramareCofactorTerm (by linarith : (0 : ℝ) < t)
  have hfib := hs.hasSum.tsum_fiberwise (fun pm : ℕ × ℕ => pm.1 * pm.2)
  have hf0 : ∀ pm : ℕ × ℕ, ¬ pm.1.Prime → ramareCofactorTerm t pm = 0 := fun pm hp => by
    rw [ramareCofactorTerm, if_neg fun h => hp h.1]
  have hcongr : (fun n : ℕ => ∑' b : (fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {n}, ramareCofactorTerm t b) =
      causalMobiusThetaTerm t := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [causalMobiusThetaTerm, Set.indicator_of_notMem (fun h => by have := h.2; simp at this; linarith)]
      rw [tsum_subtype]
      refine (tsum_congr fun b => ?_).trans tsum_zero
      by_cases hmem : b ∈ (fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {0}
      · rw [Set.indicator_of_mem hmem, ramareCofactorTerm]
        have hb : b.1 * b.2 = 0 := hmem
        rw [if_neg]
        rintro ⟨-, -, h⟩
        rw [hb] at h
        simp at h; linarith
      · exact Set.indicator_of_notMem hmem _
    · rw [tsum_fiber_eq_sum_primeFactors _ hf0 hn.ne', sum_primeFactors_ramareCofactorTerm ht hn.ne']
  rw [hcongr] at hfib
  have heq := (summable_causalMobiusThetaTerm t).hasSum.unique hfib
  rw [causalMobiusThetaTail, heq]
  exact hs.hasSum

/-- **(9), iterated form.**  `B(t) = −Σ_p Σ_{m, p∤m, pm>t} μ(m)/(ω(m)+1) k(log(pm/t))/√(pm)`. -/
theorem causalMobiusThetaTail_eq_ramare {t : ℝ} (ht : 1 ≤ t) :
    causalMobiusThetaTail t = -∑' p : ℕ, ∑' m : ℕ,
      (if p.Prime ∧ ¬ p ∣ m ∧ t < ((p * m : ℕ) : ℝ) then
        ((ArithmeticFunction.moebius m : ℤ) : ℝ) / ((m.primeFactors.card : ℝ) + 1) *
          (thetaCuspFullSource (Real.log ((p * m : ℕ) / t)) / Real.sqrt ((p * m : ℕ) : ℝ))
      else 0) := by
  have hs := summable_ramareCofactorTerm (by linarith : (0 : ℝ) < t)
  have h := (hasSum_ramareCofactorTerm ht).tsum_eq
  rw [hs.tsum_prod' fun p => hs.prod_factor p] at h
  rw [← h, ← tsum_neg]
  refine tsum_congr fun p => ?_
  rw [← tsum_neg]
  refine tsum_congr fun m => ?_
  rw [ramareCofactorTerm]
  dsimp only
  split_ifs
  · rw [causalAmplitude, natCast_rpow_neg_half_eq_inv_sqrt]; ring
  · rw [neg_zero]

/-! ## (10) The diagonal energy of the Ramaré blocks -/

theorem summable_ramareCofactorTerm_sq {t : ℝ} (ht : 0 < t) :
    Summable fun pm : ℕ × ℕ => ramareCofactorTerm t pm ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_causalAmplitude_le
  have hs := summable_ramareCofactorTerm ht
  refine Summable.of_norm_bounded (hs.abs.mul_left (C * t ^ 2)) fun pm => ?_
  have hb := abs_ramareCofactorTerm_le hC0 hC ht pm
  have h1 : (pm.1 : ℝ) ^ (-(5 / 2 : ℝ)) * (pm.2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 := by
    have e : ∀ q : ℕ, (q : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 := fun q => by
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; norm_num
      · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq) (by norm_num)
    exact mul_le_one₀ (e _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) (e _)
  rw [Real.norm_eq_abs, abs_pow, sq]
  calc |ramareCofactorTerm t pm| * |ramareCofactorTerm t pm|
      ≤ C * t ^ 2 * |ramareCofactorTerm t pm| := by
        refine mul_le_mul_of_nonneg_right (hb.trans ?_) (abs_nonneg _)
        calc C * t ^ 2 * ((pm.1 : ℝ) ^ (-(5 / 2 : ℝ)) * (pm.2 : ℝ) ^ (-(5 / 2 : ℝ)))
            ≤ C * t ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = C * t ^ 2 := mul_one _
    _ = C * t ^ 2 * |ramareCofactorTerm t pm| := rfl

/-- The fiber of the squared blocks over `n`: `a_t(n)²/ω(n)` on squarefree `n > t`. -/
theorem sum_primeFactors_ramareCofactorTerm_sq {t : ℝ} (ht : 1 ≤ t) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.primeFactors, ramareCofactorTerm t (p, n / p) ^ 2 =
      if t < n ∧ Squarefree n then (moebiusInvSqrtWeight n * thetaCuspFullSource (Real.log (n / t))) ^ 2 /
        (n.primeFactors.card : ℝ) else 0 := by
  by_cases h : t < n ∧ Squarefree n
  · rw [if_pos h]
    obtain ⟨htn, hsq⟩ := h
    have hn1 : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith)
    have hω : (n.primeFactors.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.2 (Nat.nonempty_primeFactors.2 hn1)).ne'
    have hμ2 : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 = 1 := by
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h
      · exact absurd h (ArithmeticFunction.moebius_ne_zero_iff_squarefree.2 hsq)
      · rw [h]; norm_num
      · rw [h]; norm_num
    have heach : ∀ p ∈ n.primeFactors, ramareCofactorTerm t (p, n / p) ^ 2 =
        causalAmplitude t n ^ 2 / (n.primeFactors.card : ℝ) ^ 2 := by
      intro p hp
      have hpP := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
      have hpm : ¬ p ∣ n / p := by
        intro h
        have := hsq p (by rw [← hmul]; exact Nat.mul_dvd_mul_left p h)
        exact hpP.one_lt.ne' (Nat.isUnit_iff.1 this)
      have hm0 : n / p ≠ 0 := by
        intro h; rw [h, mul_zero] at hmul; exact hn hmul.symm
      rw [ramareCofactorTerm, if_pos ⟨hpP, hpm, by simp only; rw [hmul]; exact htn⟩]
      simp only
      rw [hmul]
      have hμ : ArithmeticFunction.moebius n = -ArithmeticFunction.moebius (n / p) := by
        conv_lhs => rw [← hmul]
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
          ((Nat.Prime.coprime_iff_not_dvd hpP).2 hpm), ArithmeticFunction.moebius_apply_prime hpP]
        ring
      have hcard : (n.primeFactors.card : ℝ) = ((n / p).primeFactors.card : ℝ) + 1 := by
        conv_lhs => rw [← hmul]
        rw [primeFactors_card_prime_mul hpP hpm hm0]; push_cast; ring
      have hμ2' : ((ArithmeticFunction.moebius (n / p) : ℤ) : ℝ) ^ 2 = 1 := by
        rw [← hμ2, hμ]; push_cast; ring
      rw [← hcard, mul_pow, div_pow, neg_sq, hμ2']
      ring
    rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul, moebiusInvSqrtWeight, mul_pow, mul_pow,
      hμ2, causalAmplitude, mul_pow]
    field_simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
    rw [ramareCofactorTerm]
    split_ifs with h'
    · obtain ⟨-, hpm, htn⟩ := h'
      simp only at htn
      rw [hmul] at htn
      have hsq : ¬ Squarefree n := fun hsq => h ⟨htn, hsq⟩
      have hsqm : ¬ Squarefree (n / p) := by
        intro hsqm
        apply hsq
        rw [← hmul]
        exact (Nat.squarefree_mul ((Nat.Prime.coprime_iff_not_dvd hpP).2 hpm)).2 ⟨hpP.squarefree, hsqm⟩
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqm]
      simp
    · simp

/-- **(10) Diagonal energy of the Ramaré blocks.**  Counting the `ω(n)` representations,
`Σ_{p,m} |μ(m) a_t(pm)/(ω(m)+1)|² = Σ_{n>t sqfree} a_t(n)²/ω(n)`, and this is uniformly bounded
on `t ≥ 1`. -/
theorem hasSum_ramareCofactorTerm_sq {t : ℝ} (ht : 1 ≤ t) :
    HasSum (fun pm : ℕ × ℕ => ramareCofactorTerm t pm ^ 2)
      (∑' n : ℕ, if t < n ∧ Squarefree n then
        (moebiusInvSqrtWeight n * thetaCuspFullSource (Real.log (n / t))) ^ 2 /
          (n.primeFactors.card : ℝ) else 0) := by
  have hs := summable_ramareCofactorTerm_sq (by linarith : (0 : ℝ) < t)
  have hfib := hs.hasSum.tsum_fiberwise (fun pm : ℕ × ℕ => pm.1 * pm.2)
  have hf0 : ∀ pm : ℕ × ℕ, ¬ pm.1.Prime → ramareCofactorTerm t pm ^ 2 = 0 := fun pm hp => by
    rw [ramareCofactorTerm, if_neg fun h => hp h.1]; ring
  have hcongr : (fun n : ℕ => ∑' b : (fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {n},
      ramareCofactorTerm t b ^ 2) = fun n : ℕ => if t < n ∧ Squarefree n then
        (moebiusInvSqrtWeight n * thetaCuspFullSource (Real.log (n / t))) ^ 2 /
          (n.primeFactors.card : ℝ) else 0 := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_neg (fun h => by have := h.1; simp at this; linarith),
        tsum_subtype ((fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {0}) (fun pm => ramareCofactorTerm t pm ^ 2)]
      refine (tsum_congr fun b => ?_).trans tsum_zero
      by_cases hmem : b ∈ (fun pm : ℕ × ℕ => pm.1 * pm.2) ⁻¹' {0}
      · rw [Set.indicator_of_mem hmem, ramareCofactorTerm]
        have hb : b.1 * b.2 = 0 := hmem
        rw [if_neg]
        · ring
        rintro ⟨-, -, h⟩
        rw [hb] at h
        simp at h; linarith
      · exact Set.indicator_of_notMem hmem _
    · rw [tsum_fiber_eq_sum_primeFactors (fun pm => ramareCofactorTerm t pm ^ 2) hf0 hn.ne',
        sum_primeFactors_ramareCofactorTerm_sq ht hn.ne']
  rw [hcongr] at hfib
  rw [hfib.tsum_eq]
  exact hs.hasSum

theorem exists_ramare_diagonal_energy_le :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∑' pm : ℕ × ℕ, ramareCofactorTerm t pm ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := exists_tsum_causal_diagonal_energy_le
  refine ⟨C, fun t ht => ?_⟩
  obtain ⟨hsum, hle⟩ := hC t ht
  rw [(hasSum_ramareCofactorTerm_sq ht).tsum_eq]
  have hnonneg : ∀ n : ℕ, 0 ≤ (if t < n ∧ Squarefree n then
      (moebiusInvSqrtWeight n * thetaCuspFullSource (Real.log (n / t))) ^ 2 /
        (n.primeFactors.card : ℝ) else 0) := fun n => by
    split_ifs <;> positivity
  refine le_trans ?_ hle
  exact Summable.tsum_le_tsum (fun n => causal_squarefree_diagonal_le ht n)
    (Summable.of_nonneg_of_le hnonneg (fun n => causal_squarefree_diagonal_le ht n) hsum) hsum

end

end RHTower
