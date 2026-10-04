import GaloisForLFunctions.RHTower.ThetaChronologicalCausalJumps

/-!
# The causal Möbius–theta tail: prime-deletion stability, layer cake and diagonal energy

`B(t) = Σ_{n>t} μ(n) n^{−1/2} k(log(n/t))`.

* **(7)** For a finite set `S` of primes and a prime `p ∉ S`, the `S`-coprime tails satisfy
  `B^S(t) = B^{S∪p}(t) − p^{−1/2} B^{S∪p}(t/p)` and `B^{S∪p}(t) = Σ_j p^{−j/2} B^S(t/p^j)`; hence
  the subpower bound (2) holds for `B` iff it holds for `B^S`, and `RH ⟺` subpower `B^S`.
* **(8)** Layer cake: `B(t) = ∫_0^∞ (−k'(y)) W(t,y) dy`, `W(t,y) = Σ_{t<n≤te^y} μ(n)/√n`.
* **(10)** Uniform diagonal energy `Σ_{n>t} k(log(n/t))²/n = O(1)` on `t ≥ 1`.
* Unit-interval interpolation `|B(t) − B(N)| ≤ C N^{−1/2}` for `N ≤ t < N+1`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## `S`-coprime tails -/

/-- `B^S(t) = Σ_{n>t, (n, ∏S)=1} μ(n) n^{−1/2} k(log(n/t))`. -/
def causalTailCoprime (S : Finset ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0

theorem causalTailCoprime_empty (t : ℝ) : causalTailCoprime ∅ t = causalMobiusThetaTail t := by
  simp [causalTailCoprime, causalMobiusThetaTail]

theorem abs_causalTailCoprime_term_le {C : ℝ}
    (hC : ∀ (t : ℝ) (n : ℕ), 0 < t → |causalMobiusThetaTerm t n| ≤ C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)))
    (S : Finset ℕ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    |if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0| ≤
      C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  split_ifs
  · exact hC t n ht
  · rw [abs_zero]; exact le_trans (abs_nonneg _) (hC t n ht)

theorem summable_causalTailCoprime_term (S : Finset ℕ) (t : ℝ) :
    Summable fun n : ℕ => if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0 := by
  rcases le_or_gt t 0 with ht | ht
  · have h0 : ∀ n, (if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0) = 0 := fun n => by
      split_ifs <;> simp [causalMobiusThetaTerm_of_nonpos ht]
    simp_rw [h0]; exact summable_zero
  obtain ⟨C, _, hC⟩ := exists_abs_causalMobiusThetaTerm_le
  exact Summable.of_norm_bounded (summable_natCast_rpow_neg_five_halves.mul_left (C * t ^ 2))
    fun n => by rw [Real.norm_eq_abs]; exact abs_causalTailCoprime_term_le hC S ht n

/-- `|B^S(t)| ≤ C t²` for `t > 0`. -/
theorem exists_abs_causalTailCoprime_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℕ) (t : ℝ), 0 < t → |causalTailCoprime S t| ≤ C * t ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_causalMobiusThetaTerm_le
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(5 / 2 : ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨C * Z, by positivity, fun S t ht => ?_⟩
  have hs := summable_causalTailCoprime_term S t
  calc |causalTailCoprime S t| ≤ ∑' n : ℕ, |if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hs.abs)).trans_eq
          (tsum_congr fun n => Real.norm_eq_abs _)
    _ ≤ ∑' n : ℕ, C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)) :=
        hs.abs.tsum_le_tsum (fun n => abs_causalTailCoprime_term_le hC S ht n)
          (summable_natCast_rpow_neg_five_halves.mul_left _)
    _ = C * Z * t ^ 2 := by rw [tsum_mul_left]; ring

theorem causalTailCoprime_of_nonpos (S : Finset ℕ) {t : ℝ} (ht : t ≤ 0) : causalTailCoprime S t = 0 := by
  rw [causalTailCoprime]
  have h0 : ∀ n, (if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0) = 0 := fun n => by
    split_ifs <;> simp [causalMobiusThetaTerm_of_nonpos ht]
  simp_rw [h0, tsum_zero]

/-- One term at a multiple `pm` of a prime: `−p^{−1/2}` times the term at `m`, scale `t/p`. -/
theorem causalMobiusThetaTerm_prime_mul {p : ℕ} (hp : p.Prime) (m : ℕ) (t : ℝ) :
    causalMobiusThetaTerm t (p * m) =
      if p ∣ m then 0 else -((p : ℝ) ^ (-(1 / 2 : ℝ))) * causalMobiusThetaTerm (t / p) m := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hμ : ArithmeticFunction.moebius (p * m) = if p ∣ m then 0 else -ArithmeticFunction.moebius m := by
    by_cases hpm : p ∣ m
    · rw [if_pos hpm, ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
      intro hsq
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p (Nat.mul_dvd_mul_left p hpm)))
    · rw [if_neg hpm, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm), ArithmeticFunction.moebius_apply_prime hp]
      ring
  by_cases hpm : p ∣ m
  · rw [if_pos hpm, causalMobiusThetaTerm, hμ, if_pos hpm]
    simp
  rw [if_neg hpm, causalMobiusThetaTerm, causalMobiusThetaTerm, hμ, if_neg hpm]
  by_cases ht : t ∈ Ioo 0 ((p * m : ℕ) : ℝ)
  · have ht' : t / p ∈ Ioo 0 (m : ℝ) := by
      constructor
      · exact div_pos ht.1 hpR
      · rw [div_lt_iff₀ hpR]; have := ht.2; push_cast at this; linarith
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    have hm : (0 : ℝ) < m := lt_trans ht'.1 ht'.2
    have hlog : Real.log ((p * m : ℕ) / t) = Real.log (m / (t / p)) := by
      congr 1; push_cast; field_simp
    rw [hlog, show ((p * m : ℕ) : ℝ) = (p : ℝ) * m by push_cast; ring,
      Real.mul_rpow hpR.le hm.le]
    push_cast
    ring
  · have ht' : t / p ∉ Ioo 0 (m : ℝ) := by
      intro h
      apply ht
      refine ⟨by have := h.1; rwa [div_pos_iff_of_pos_right hpR] at this, ?_⟩
      have := h.2
      rw [div_lt_iff₀ hpR] at this
      push_cast; linarith
    rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht', mul_zero]

/-- **(7) Prime-deletion stability.**  `B^S(t) = B^{S∪p}(t) − p^{−1/2} B^{S∪p}(t/p)` for a prime
`p ∉ S` when `S` consists of primes. -/
theorem causalTailCoprime_eq_insert {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (t : ℝ) :
    causalTailCoprime S t = causalTailCoprime (insert p S) t -
      (p : ℝ) ^ (-(1 / 2 : ℝ)) * causalTailCoprime (insert p S) (t / p) := by
  set f : ℕ → ℝ := fun n => if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0
  have hf := summable_causalTailCoprime_term S t
  have hsplit : ∀ n, f n = (if (∀ q ∈ insert p S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0) +
      (if p ∣ n then f n else 0) := by
    intro n
    simp only [f, Finset.mem_insert, forall_eq_or_imp]
    by_cases hpn : p ∣ n <;> simp [hpn]
  have hs1 := summable_causalTailCoprime_term (insert p S) t
  have hs2 : Summable fun n => if p ∣ n then f n else 0 :=
    Summable.of_norm_bounded hf.norm fun n => by
      by_cases h : p ∣ n
      · rw [if_pos h]
      · rw [if_neg h, norm_zero]; exact norm_nonneg _
  have hmul : (∑' n, if p ∣ n then f n else 0) =
      ∑' m, f (p * m) := by
    have hinj : Function.Injective (fun m : ℕ => p * m) := fun a b h => by
      simpa [hp.pos.ne'] using h
    rw [← hinj.tsum_eq (f := fun n => if p ∣ n then f n else 0)]
    · exact tsum_congr fun m => by simp
    · intro n hn
      by_contra h
      apply hn
      have : ¬ p ∣ n := fun hd => h ⟨n / p, (Nat.mul_div_cancel' hd)⟩
      simp [this]
  have hcop : ∀ m, f (p * m) = -((p : ℝ) ^ (-(1 / 2 : ℝ))) *
      (if (∀ q ∈ insert p S, ¬ q ∣ m) then causalMobiusThetaTerm (t / p) m else 0) := by
    intro m
    simp only [f]
    have hiff : (∀ q ∈ S, ¬ q ∣ p * m) ↔ (∀ q ∈ S, ¬ q ∣ m) := by
      constructor
      · intro h q hq hqm; exact h q hq (dvd_mul_of_dvd_right hqm p)
      · intro h q hq hqm
        rcases (Nat.Prime.dvd_mul (hS q hq)).1 hqm with h1 | h1
        · have := (Nat.prime_dvd_prime_iff_eq (hS q hq) hp).1 h1
          exact hpS (this ▸ hq)
        · exact h q hq h1
    rw [causalMobiusThetaTerm_prime_mul hp]
    by_cases hpm : p ∣ m
    · simp [hpm]
    · rw [if_neg hpm]
      have hins : (∀ q ∈ insert p S, ¬ q ∣ m) ↔ (∀ q ∈ S, ¬ q ∣ m) := by
        simp only [Finset.mem_insert, forall_eq_or_imp, hpm, not_false_eq_true, true_and]
      by_cases hS' : ∀ q ∈ S, ¬ q ∣ m
      · rw [if_pos (hiff.2 hS'), if_pos (hins.2 hS')]
      · rw [if_neg (fun h => hS' (hiff.1 h)), if_neg (fun h => hS' (hins.1 h)), mul_zero]
  rw [causalTailCoprime, show (fun n => if (∀ q ∈ S, ¬ q ∣ n) then causalMobiusThetaTerm t n else 0) = f
    from rfl, tsum_congr hsplit, hs1.tsum_add hs2, hmul, tsum_congr hcop, tsum_mul_left,
    causalTailCoprime, causalTailCoprime]
  ring

/-- **(7) The inverse series** `B^{S∪p}(t) = Σ_j p^{−j/2} B^S(t/p^j)`. -/
theorem hasSum_causalTailCoprime_insert {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (t : ℝ) :
    HasSum (fun j : ℕ => ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ j * causalTailCoprime S (t / (p : ℝ) ^ j))
      (causalTailCoprime (insert p S) t) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_causalTailCoprime_le_sq
  have hbound : ∀ (T : Finset ℕ) (u : ℝ), |causalTailCoprime T u| ≤ C * u ^ 2 := fun T u => by
    rcases le_or_gt u 0 with hu | hu
    · rw [causalTailCoprime_of_nonpos T hu, abs_zero]; positivity
    · exact hC T u hu
  set ρ : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by linarith) _
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hpR.le (by norm_num)
  have hrel : ∀ j : ℕ, causalTailCoprime S (t / (p : ℝ) ^ j) =
      causalTailCoprime (insert p S) (t / (p : ℝ) ^ j) -
        ρ * causalTailCoprime (insert p S) (t / (p : ℝ) ^ (j + 1)) := fun j => by
    rw [causalTailCoprime_eq_insert hS hp hpS, pow_succ, div_div]
  have hpartial : ∀ J : ℕ, ∑ j ∈ Finset.range J, ρ ^ j * causalTailCoprime S (t / (p : ℝ) ^ j) =
      causalTailCoprime (insert p S) t - ρ ^ J * causalTailCoprime (insert p S) (t / (p : ℝ) ^ J) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ih, hrel J, pow_succ]
      ring
  have hgeom : Summable fun j : ℕ => C * t ^ 2 * ((1 / (p : ℝ) ^ 2) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) (by
      rw [div_lt_one (by positivity)]; nlinarith)).mul_left _
  have hterm : ∀ j : ℕ, ‖ρ ^ j * causalTailCoprime S (t / (p : ℝ) ^ j)‖ ≤
      C * t ^ 2 * ((1 / (p : ℝ) ^ 2) ^ j) := fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 j)]
    have hpj : (0 : ℝ) < (p : ℝ) ^ j := by positivity
    calc ρ ^ j * |causalTailCoprime S (t / (p : ℝ) ^ j)| ≤ 1 * (C * (t / (p : ℝ) ^ j) ^ 2) :=
          mul_le_mul (pow_le_one₀ hρ0 hρ1) (hbound S _) (abs_nonneg _) zero_le_one
      _ = C * t ^ 2 * ((1 / (p : ℝ) ^ 2) ^ j) := by
          rw [div_pow, ← pow_mul, one_div, inv_pow, ← pow_mul]; field_simp; ring_nf
  have hsum : Summable fun j : ℕ => ρ ^ j * causalTailCoprime S (t / (p : ℝ) ^ j) :=
    Summable.of_norm_bounded hgeom hterm
  have hlim : Tendsto (fun J : ℕ => ρ ^ J * causalTailCoprime (insert p S) (t / (p : ℝ) ^ J)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun J : ℕ => C * t ^ 2 * ((1 / (p : ℝ) ^ 2) ^ J)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / (p : ℝ) ^ 2) (by positivity)
        (by rw [div_lt_one (by positivity)]; nlinarith)).const_mul (C * t ^ 2)
      simpa using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun J => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 J)]
    calc ρ ^ J * |causalTailCoprime (insert p S) (t / (p : ℝ) ^ J)| ≤ 1 * (C * (t / (p : ℝ) ^ J) ^ 2) :=
          mul_le_mul (pow_le_one₀ hρ0 hρ1) (hbound _ _) (abs_nonneg _) zero_le_one
      _ = C * t ^ 2 * ((1 / (p : ℝ) ^ 2) ^ J) := by
          rw [div_pow, ← pow_mul, one_div, inv_pow, ← pow_mul]; field_simp; ring_nf
  have h2 : Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J, ρ ^ j * causalTailCoprime S (t / (p : ℝ) ^ j))
      atTop (𝓝 (causalTailCoprime (insert p S) t)) := by
    simp_rw [hpartial]
    simpa using (tendsto_const_nhds (x := causalTailCoprime (insert p S) t)).sub hlim
  have heq : ∑' j, ρ ^ j * causalTailCoprime S (t / (p : ℝ) ^ j) = causalTailCoprime (insert p S) t :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat h2
  exact heq ▸ hsum.hasSum

/-- The subpower bound (2) on `t ≥ 1`. -/
def SubpowerBound (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → |f t| ≤ C * t ^ ε

/-- **(7) Stability of the criterion under deletion of one prime.** -/
theorem subpowerBound_causalTailCoprime_insert_iff {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) :
    SubpowerBound (causalTailCoprime S) ↔ SubpowerBound (causalTailCoprime (insert p S)) := by
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_causalTailCoprime_le_sq
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set ρ : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by linarith) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpR (by norm_num)
  -- one value at any positive argument `u ≤ t`, `t ≥ 1`
  have hval : ∀ (T : Finset ℕ) {ε C : ℝ}, 0 < ε → (∀ t : ℝ, 1 ≤ t → |causalTailCoprime T t| ≤ C * t ^ ε) →
      ∀ {t u : ℝ}, 1 ≤ t → 0 < u → u ≤ t → |causalTailCoprime T u| ≤ (|C| + C0) * t ^ ε := by
    intro T ε C hε hT t u ht hu hut
    have htε : 1 ≤ t ^ ε := Real.one_le_rpow ht hε.le
    rcases le_or_gt 1 u with hu1 | hu1
    · calc |causalTailCoprime T u| ≤ C * u ^ ε := hT u hu1
        _ ≤ |C| * t ^ ε := mul_le_mul (le_abs_self C) (Real.rpow_le_rpow hu.le hut hε.le)
            (Real.rpow_nonneg hu.le _) (abs_nonneg C)
        _ ≤ (|C| + C0) * t ^ ε := by nlinarith [Real.rpow_nonneg (zero_le_one.trans ht) ε]
    · calc |causalTailCoprime T u| ≤ C0 * u ^ 2 := hC0 T u hu
        _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left (by nlinarith) hC00
        _ ≤ (|C| + C0) * t ^ ε := by nlinarith [abs_nonneg C]
  constructor
  · intro hSb ε hε
    obtain ⟨C, hC⟩ := hSb ε hε
    refine ⟨(|C| + C0) / (1 - ρ), fun t ht => ?_⟩
    have hs := hasSum_causalTailCoprime_insert hS hp hpS t
    have hbd : ∀ j : ℕ, ‖ρ ^ j * causalTailCoprime S (t / (p : ℝ) ^ j)‖ ≤ ρ ^ j * ((|C| + C0) * t ^ ε) := by
      intro j
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 j)]
      refine mul_le_mul_of_nonneg_left (hval S hε hC ht (by positivity) ?_) (pow_nonneg hρ0 j)
      exact div_le_self (by linarith) (one_le_pow₀ hpR.le)
    have hgeom : HasSum (fun j : ℕ => ρ ^ j * ((|C| + C0) * t ^ ε)) ((|C| + C0) * t ^ ε / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right ((|C| + C0) * t ^ ε)
      rwa [show (1 - ρ)⁻¹ * ((|C| + C0) * t ^ ε) = (|C| + C0) * t ^ ε / (1 - ρ) by
        rw [div_eq_mul_inv]; ring] at this
    calc |causalTailCoprime (insert p S) t| = ‖∑' j, ρ ^ j * causalTailCoprime S (t / (p : ℝ) ^ j)‖ := by
          rw [hs.tsum_eq, Real.norm_eq_abs]
      _ ≤ ∑' j, ρ ^ j * ((|C| + C0) * t ^ ε) :=
          tsum_of_norm_bounded hgeom hbd |>.trans (le_of_eq hgeom.tsum_eq.symm) |>.trans_eq rfl
      _ = (|C| + C0) / (1 - ρ) * t ^ ε := by rw [hgeom.tsum_eq]; ring
  · intro hSb ε hε
    obtain ⟨C, hC⟩ := hSb ε hε
    refine ⟨(|C| + C0) * (1 + ρ), fun t ht => ?_⟩
    rw [causalTailCoprime_eq_insert hS hp hpS]
    have h1 := hval (insert p S) hε hC ht (by linarith) le_rfl
    have h2 := hval (insert p S) hε hC ht (by positivity : (0 : ℝ) < t / p)
      (div_le_self (by linarith) hpR.le)
    calc |causalTailCoprime (insert p S) t - ρ * causalTailCoprime (insert p S) (t / p)|
        ≤ |causalTailCoprime (insert p S) t| + ρ * |causalTailCoprime (insert p S) (t / p)| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hρ0]
      _ ≤ (|C| + C0) * t ^ ε + ρ * ((|C| + C0) * t ^ ε) := by gcongr
      _ = (|C| + C0) * (1 + ρ) * t ^ ε := by ring

/-- **The criterion is stable under deletion of any finite set of primes.** -/
theorem subpowerBound_causalTail_iff_coprime {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) :
    SubpowerBound causalMobiusThetaTail ↔ SubpowerBound (causalTailCoprime S) := by
  induction S using Finset.induction_on with
  | empty => simp only [SubpowerBound, causalTailCoprime_empty]
  | insert p S hpS ih =>
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [ih hS']
    exact subpowerBound_causalTailCoprime_insert_iff hS' (hS p (Finset.mem_insert_self p S)) hpS

/-- **RH ⟺ subpower bound for the tail with any finite prime set deleted.** -/
theorem riemannHypothesis_iff_subpower_causalTailCoprime {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) :
    RiemannHypothesis ↔ SubpowerBound (causalTailCoprime S) := by
  rw [← subpowerBound_causalTail_iff_coprime hS]
  exact riemannHypothesis_iff_causalMobiusThetaTail_subpower

/-! ## (8) Layer cake -/

/-- `W(t,y) = Σ_{t<n≤te^y} μ(n)/√n`. -/
def causalWindowSum (t y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊t⌋₊ ⌊t * Real.exp y⌋₊, moebiusInvSqrtWeight n

theorem thetaCuspFullSource_eq_integral_Ioi_neg_deriv (v : ℝ) :
    thetaCuspFullSource v = ∫ y in Ioi v, -deriv thetaCuspFullSource y := by
  have hint : IntegrableOn (deriv thetaCuspFullSource) (Ioi v) := by
    obtain ⟨C, _, hC⟩ := exists_abs_deriv_thetaCuspFullSource_le 1
    refine Integrable.mono' ((integrable_exp_neg_mul_abs (by norm_num : (0:ℝ) < 1)).const_mul C).integrableOn
      continuous_deriv_thetaCuspFullSource.aestronglyMeasurable.restrict (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; simpa [one_mul] using hC x
  rw [integral_neg, integral_Ioi_of_hasDerivAt_of_tendsto (m := 0)
    continuous_thetaCuspFullSource.continuousWithinAt
    (fun x _ => (differentiable_thetaCuspFullSource x).hasDerivAt) hint
    tendsto_thetaCuspFullSource_atTop_zero]
  ring

theorem neg_deriv_thetaCuspFullSource_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ -deriv thetaCuspFullSource y := by
  linarith [deriv_thetaCuspFullSource_nonpos hy]

/-- **(8) The layer-cake form.**  `B(t) = ∫_0^∞ (−k'(y)) W(t,y) dy` for `t > 0`. -/
theorem causalMobiusThetaTail_eq_layerCake {t : ℝ} (ht : 0 < t) :
    causalMobiusThetaTail t = ∫ y in Ioi (0 : ℝ), -deriv thetaCuspFullSource y * causalWindowSum t y := by
  set F : ℕ → ℝ → ℝ := fun n y => (Ici (Real.log (n / t))).indicator
    (fun y => -deriv thetaCuspFullSource y * (if t < n then moebiusInvSqrtWeight n else 0)) y
  have hk' : IntegrableOn (fun y => -deriv thetaCuspFullSource y) (Ioi 0) :=
    integrableOn_Ioi_deriv_thetaCuspFullSource.neg
  -- each term
  have hterm : ∀ n : ℕ, causalMobiusThetaTerm t n = ∫ y in Ioi (0 : ℝ), F n y := by
    intro n
    by_cases htn : t < n
    · have hn : (0 : ℝ) < n := ht.trans htn
      have hlog : 0 < Real.log (n / t) := Real.log_pos (by rw [one_lt_div ht]; exact htn)
      have hset : Ioi (0 : ℝ) ∩ Ici (Real.log (n / t)) = Ici (Real.log (n / t)) :=
        inter_eq_right.2 fun y hy => lt_of_lt_of_le hlog hy
      simp only [F, if_pos htn]
      rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        inter_comm, hset, integral_Ici_eq_integral_Ioi, integral_mul_const,
        ← thetaCuspFullSource_eq_integral_Ioi_neg_deriv, causalMobiusThetaTerm,
        Set.indicator_of_mem (show t ∈ Ioo 0 (n : ℝ) from ⟨ht, htn⟩), moebiusInvSqrtWeight]
      ring
    · have h0 : ∀ y, F n y = 0 := fun y => by simp [F, htn]
      simp_rw [h0, integral_zero]
      rw [causalMobiusThetaTerm, Set.indicator_of_notMem fun h => htn h.2]
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => by
    simp only [F]
    exact (hk'.mul_const _).indicator measurableSet_Ici
  have hFnorm : ∀ n, (∫ y in Ioi (0 : ℝ), ‖F n y‖) = |causalMobiusThetaTerm t n| := by
    intro n
    by_cases htn : t < n
    · have hn : (0 : ℝ) < n := ht.trans htn
      have hlog : 0 < Real.log (n / t) := Real.log_pos (by rw [one_lt_div ht]; exact htn)
      have hset : Ioi (0 : ℝ) ∩ Ici (Real.log (n / t)) = Ici (Real.log (n / t)) :=
        inter_eq_right.2 fun y hy => lt_of_lt_of_le hlog hy
      have h1 : (fun y => ‖F n y‖) = (Ici (Real.log (n / t))).indicator
          (fun y => -deriv thetaCuspFullSource y * |moebiusInvSqrtWeight n|) := by
        funext y
        simp only [F, if_pos htn, Real.norm_eq_abs]
        by_cases hy : y ∈ Ici (Real.log (n / t))
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, abs_mul,
            abs_of_nonneg (neg_deriv_thetaCuspFullSource_nonneg (lt_of_lt_of_le hlog hy))]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, abs_zero]
      rw [h1, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        inter_comm, hset, integral_Ici_eq_integral_Ioi, integral_mul_const,
        ← thetaCuspFullSource_eq_integral_Ioi_neg_deriv, causalMobiusThetaTerm,
        Set.indicator_of_mem (show t ∈ Ioo 0 (n : ℝ) from ⟨ht, htn⟩), abs_mul, abs_mul,
        abs_of_pos (HedenmalmThetaSource.thetaCuspFullSource_pos _), moebiusInvSqrtWeight, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      ring
    · have h0 : ∀ y, F n y = 0 := fun y => by simp [F, htn]
      simp_rw [h0, norm_zero, integral_zero]
      rw [causalMobiusThetaTerm, Set.indicator_of_notMem fun h => htn h.2, abs_zero]
  have hsum : Summable fun n => ∫ y in Ioi (0 : ℝ), ‖F n y‖ := by
    simp_rw [hFnorm]; exact (summable_causalMobiusThetaTerm t).abs
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ∑' n, F n y = -deriv thetaCuspFullSource y * causalWindowSum t y := by
    intro y hy
    rw [causalWindowSum, Finset.mul_sum]
    rw [tsum_eq_sum (s := Finset.Ioc ⌊t⌋₊ ⌊t * Real.exp y⌋₊)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      have htn : t < n := by
        have := Nat.lt_of_floor_lt hn.1; exact_mod_cast this
      have hn' : (n : ℝ) ≤ t * Real.exp y := by
        have := Nat.le_floor_iff (by positivity) |>.1 hn.2; exact_mod_cast this
      have hmem : y ∈ Ici (Real.log (n / t)) := by
        rw [Set.mem_Ici, Real.log_le_iff_le_exp (div_pos (ht.trans htn) ht), div_le_iff₀ ht]
        linarith
      simp only [F, Set.indicator_of_mem hmem, if_pos htn]
    · intro n hn
      simp only [F]
      by_cases htn : t < n
      · have hmem : y ∉ Ici (Real.log (n / t)) := by
          intro hmem
          apply hn
          rw [Finset.mem_Ioc]
          refine ⟨Nat.floor_lt (ht.le) |>.2 htn, ?_⟩
          rw [Nat.le_floor_iff (by positivity)]
          rw [Set.mem_Ici, Real.log_le_iff_le_exp (div_pos (ht.trans htn) ht), div_le_iff₀ ht] at hmem
          linarith
        exact Set.indicator_of_notMem hmem _
      · simp [if_neg htn]
  rw [causalMobiusThetaTail, tsum_congr hterm,
    integral_tsum_of_summable_integral_norm hFint hsum]
  exact setIntegral_congr_fun measurableSet_Ioi hpt

/-! ## (10) Uniform diagonal energy and interpolation -/

/-- `Σ_{j<M} (N+1+j)^{−3} ≤ N^{−2} − (N+M)^{−2}`. -/
theorem sum_range_inv_pow_three_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ j ∈ Finset.range M, (((N + 1 + j : ℕ) : ℝ) ^ 3)⁻¹ ≤
      ((N : ℝ) ^ 2)⁻¹ - (((N + M : ℕ) : ℝ) ^ 2)⁻¹ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hm : (1 : ℝ) ≤ ((N + M : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + M)
    have hstep : (((N + 1 + M : ℕ) : ℝ) ^ 3)⁻¹ ≤
        (((N + M : ℕ) : ℝ) ^ 2)⁻¹ - (((N + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
      have e1 : ((N + 1 + M : ℕ) : ℝ) = ((N + M : ℕ) : ℝ) + 1 := by push_cast; ring
      have e2 : ((N + (M + 1) : ℕ) : ℝ) = ((N + M : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e1, e2]
      set x : ℝ := ((N + M : ℕ) : ℝ)
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      have hx : 0 < x := by linarith
      field_simp
      nlinarith [hx, sq_nonneg x]
    linarith

theorem summable_shift_inv_pow_three (N : ℕ) : Summable fun j : ℕ => (((N + 1 + j : ℕ) : ℝ) ^ 3)⁻¹ := by
  have h := (Real.summable_nat_pow_inv (p := 3)).2 (by norm_num)
  exact h.comp_injective (i := fun j => N + 1 + j) fun a b hab => by simpa using hab

theorem tsum_shift_inv_pow_three_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' j : ℕ, (((N + 1 + j : ℕ) : ℝ) ^ 3)⁻¹ ≤ ((N : ℝ) ^ 2)⁻¹ :=
  Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun M =>
    (sum_range_inv_pow_three_le hN M).trans (sub_le_self _ (by positivity))

/-- **(10) Uniform diagonal energy.**  `Σ_{n>t} k(log(n/t))²/n ≤ C` for every `t ≥ 1`. -/
theorem exists_tsum_causal_diagonal_energy_le :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      Summable (fun n : ℕ => if t < n then thetaCuspFullSource (Real.log (n / t)) ^ 2 / n else 0) ∧
      ∑' n : ℕ, (if t < n then thetaCuspFullSource (Real.log (n / t)) ^ 2 / n else 0) ≤ C := by
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_thetaCuspFullSource_le 1
  refine ⟨4 * C1 ^ 2, fun t ht => ?_⟩
  set N := ⌊t⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast ht)
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htN : t < N + 1 := Nat.lt_floor_add_one t
  set f : ℕ → ℝ := fun n => if t < n then thetaCuspFullSource (Real.log (n / t)) ^ 2 / n else 0
  have hfb : ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ if N < n then C1 ^ 2 * t ^ 2 * ((n : ℝ) ^ 3)⁻¹ else 0 := by
    intro n
    simp only [f]
    by_cases htn : t < n
    · have hn : (0 : ℝ) < n := by linarith
      have hNn : N < n := by exact_mod_cast (show (N : ℝ) < n by linarith)
      rw [if_pos htn, if_pos hNn]
      have hlog : 0 ≤ Real.log (n / t) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
      have hk := hC1 (Real.log (n / t))
      rw [abs_of_nonneg hlog, one_mul, abs_of_pos (HedenmalmThetaSource.thetaCuspFullSource_pos _),
        Real.exp_neg, Real.exp_log (div_pos hn (by linarith)), inv_div] at hk
      have hk0 := (HedenmalmThetaSource.thetaCuspFullSource_pos (Real.log (n / t))).le
      refine ⟨by positivity, ?_⟩
      calc thetaCuspFullSource (Real.log (n / t)) ^ 2 / n ≤ (C1 * (t / n)) ^ 2 / n := by gcongr
        _ = C1 ^ 2 * t ^ 2 * ((n : ℝ) ^ 3)⁻¹ := by field_simp
    · have hNn : ¬ N < n := fun h => htn (by
        have : (N + 1 : ℝ) ≤ n := by exact_mod_cast h
        linarith)
      simp [htn, hNn]
  have hg0 : ∀ n : ℕ, 0 ≤ (if N < n then C1 ^ 2 * t ^ 2 * ((n : ℝ) ^ 3)⁻¹ else 0) := fun n => by
    by_cases h : N < n
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  have hg1 : ∀ n : ℕ, (if N < n then C1 ^ 2 * t ^ 2 * ((n : ℝ) ^ 3)⁻¹ else 0) ≤
      C1 ^ 2 * t ^ 2 * ((n : ℝ) ^ 3)⁻¹ := fun n => by
    by_cases h : N < n
    · rw [if_pos h]
    · rw [if_neg h]; positivity
  have hg : Summable fun n : ℕ => if N < n then C1 ^ 2 * t ^ 2 * ((n : ℝ) ^ 3)⁻¹ else 0 :=
    Summable.of_nonneg_of_le hg0 hg1
      (((Real.summable_nat_pow_inv (p := 3)).2 (by norm_num)).mul_left (C1 ^ 2 * t ^ 2))
  have hfs : Summable f := Summable.of_nonneg_of_le (fun n => (hfb n).1) (fun n => (hfb n).2) hg
  refine ⟨hfs, ?_⟩
  calc ∑' n, f n ≤ ∑' n : ℕ, (if N < n then C1 ^ 2 * t ^ 2 * ((n : ℝ) ^ 3)⁻¹ else 0) :=
        hfs.tsum_le_tsum (fun n => (hfb n).2) hg
    _ = C1 ^ 2 * t ^ 2 * ∑' j : ℕ, (((N + 1 + j : ℕ) : ℝ) ^ 3)⁻¹ := by
        rw [← hg.sum_add_tsum_nat_add (N + 1)]
        rw [Finset.sum_eq_zero fun n hn => by
          rw [if_neg (by have := Finset.mem_range.1 hn; omega)]]
        rw [zero_add, ← tsum_mul_left]
        refine tsum_congr fun j => ?_
        rw [if_pos (by omega), show j + (N + 1) = N + 1 + j by ring]
    _ ≤ C1 ^ 2 * t ^ 2 * ((N : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (tsum_shift_inv_pow_three_le hN) (by positivity)
    _ ≤ 4 * C1 ^ 2 := by
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have ht2 : t ≤ 2 * N := by linarith
        rw [mul_assoc, ← div_eq_mul_inv]
        have : t ^ 2 / (N : ℝ) ^ 2 ≤ 4 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        nlinarith [sq_nonneg C1]

/-- The squarefree diagonal `Σ_{n>t sqfree} a_t(n)²/ω(n)` is bounded by the diagonal energy. -/
theorem causal_squarefree_diagonal_le {t : ℝ} (ht : 1 ≤ t) (n : ℕ) :
    (if t < n ∧ Squarefree n then (moebiusInvSqrtWeight n * thetaCuspFullSource (Real.log (n / t))) ^ 2 /
      (n.primeFactors.card : ℝ) else 0) ≤
      if t < n then thetaCuspFullSource (Real.log (n / t)) ^ 2 / n else 0 := by
  by_cases h : t < n ∧ Squarefree n
  · rw [if_pos h, if_pos h.1]
    have hn : (1 : ℕ) < n := by exact_mod_cast (show (1 : ℝ) < n by linarith [h.1])
    have hω : (1 : ℝ) ≤ n.primeFactors.card := by
      exact_mod_cast Finset.card_pos.2 (Nat.nonempty_primeFactors.2 hn)
    have hnR : (0 : ℝ) < n := by linarith [h.1]
    have hw : moebiusInvSqrtWeight n ^ 2 ≤ (n : ℝ)⁻¹ := by
      have := abs_moebiusInvSqrtWeight_le n
      rw [natCast_rpow_neg_half_eq_inv_sqrt] at this
      calc moebiusInvSqrtWeight n ^ 2 = |moebiusInvSqrtWeight n| ^ 2 := (sq_abs _).symm
        _ ≤ ((Real.sqrt n)⁻¹) ^ 2 := by gcongr
        _ = (n : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hnR.le]
    have hk := sq_nonneg (thetaCuspFullSource (Real.log (n / t)))
    rw [mul_pow, div_le_iff₀ (by linarith)]
    calc moebiusInvSqrtWeight n ^ 2 * thetaCuspFullSource (Real.log (n / t)) ^ 2
        ≤ (n : ℝ)⁻¹ * thetaCuspFullSource (Real.log (n / t)) ^ 2 := by gcongr
      _ = thetaCuspFullSource (Real.log (n / t)) ^ 2 / n * 1 := by ring
      _ ≤ thetaCuspFullSource (Real.log (n / t)) ^ 2 / n * (n.primeFactors.card : ℝ) := by gcongr
  · rw [if_neg h]
    split_ifs <;> positivity

/-! ## Interpolation between integer times -/

theorem rpow_neg_three_halves_eq_inv_mul_sqrt {x : ℝ} (hx : 0 < x) : x ^ (-(3 / 2 : ℝ)) = (x * Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx.le (by norm_num)]
  norm_num

/-- `Σ_{j<M} (N+1+j)^{−3/2} ≤ 2(N^{−1/2} − (N+M)^{−1/2})`. -/
theorem sum_range_rpow_neg_three_halves_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ j ∈ Finset.range M, ((N + 1 + j : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      2 * ((Real.sqrt N)⁻¹ - (Real.sqrt ((N + M : ℕ) : ℝ))⁻¹) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    set m : ℝ := ((N + M : ℕ) : ℝ)
    have hm : 1 ≤ m := by simp only [m]; exact_mod_cast (by omega : 1 ≤ N + M)
    have e1 : ((N + 1 + M : ℕ) : ℝ) = m + 1 := by simp only [m]; push_cast; ring
    have e2 : ((N + (M + 1) : ℕ) : ℝ) = m + 1 := by simp only [m]; push_cast; ring
    rw [e1, e2]
    have hstep : (m + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 * ((Real.sqrt m)⁻¹ - (Real.sqrt (m + 1))⁻¹) := by
      rw [rpow_neg_three_halves_eq_inv_mul_sqrt (by linarith)]
      set a := Real.sqrt m
      set b := Real.sqrt (m + 1)
      have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
      have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
      have ha2 : a ^ 2 = m := Real.sq_sqrt (by linarith)
      have hb2 : b ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
      have hab : a < b := Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have hden : (m + 1) * b = b ^ 3 := by rw [← hb2]; ring
      have hba : b - a = 1 / (a + b) := by
        field_simp
        nlinarith
      rw [hden, show 2 * (a⁻¹ - b⁻¹) = 2 / (a * b * (a + b)) by
        rw [show a⁻¹ - b⁻¹ = (b - a) / (a * b) by field_simp, hba]; field_simp]
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha hb]
    linarith

theorem tsum_shift_rpow_neg_three_halves_le {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun j : ℕ => ((N + 1 + j : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ∧
    ∑' j : ℕ, ((N + 1 + j : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 * (Real.sqrt N)⁻¹ := by
  have hb : ∀ M, ∑ j ∈ Finset.range M, ((N + 1 + j : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 * (Real.sqrt N)⁻¹ :=
    fun M => (sum_range_rpow_neg_three_halves_le hN M).trans (by
      have : 0 ≤ (Real.sqrt ((N + M : ℕ) : ℝ))⁻¹ := by positivity
      linarith)
  have h0 : ∀ j, 0 ≤ ((N + 1 + j : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact ⟨summable_of_sum_range_le h0 hb, Real.tsum_le_of_sum_range_le h0 hb⟩

/-- **Unit-interval interpolation.**  `|B(t) − B(N)| ≤ C N^{−1/2}` for `N ≤ t < N + 1`. -/
theorem exists_abs_causalTail_sub_le :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, (N : ℝ) ≤ t → t < N + 1 →
      |causalMobiusThetaTail t - causalMobiusThetaTail N| ≤ C * (Real.sqrt N)⁻¹ := by
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_deriv_thetaCuspFullSource_le 1
  refine ⟨4 * C1, fun N hN t hNt htN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 < t := by linarith
  set f : ℕ → ℝ := fun n => causalMobiusThetaTerm t n - causalMobiusThetaTerm N n
  have hzero : ∀ n : ℕ, n ≤ N → f n = 0 := by
    intro n hn
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
    simp only [f, causalMobiusThetaTerm]
    rw [Set.indicator_of_notMem (fun h => by have := h.2; linarith),
      Set.indicator_of_notMem (fun h => by have := h.2; linarith), sub_zero]
  have hbound : ∀ n : ℕ, N < n → |f n| ≤ 2 * C1 * ((n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro n hn
    have hnR : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hmemt : t ∈ Ioo 0 (n : ℝ) := ⟨ht0, by linarith⟩
    have hmemN : (N : ℝ) ∈ Ioo 0 (n : ℝ) := ⟨by linarith, by linarith⟩
    simp only [f, causalMobiusThetaTerm, Set.indicator_of_mem hmemt, Set.indicator_of_mem hmemN]
    set a := Real.log (n / t)
    set b := Real.log (n / N)
    have ha0 : 0 ≤ a := Real.log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
    have hab : a ≤ b := Real.log_le_log (div_pos hn0 ht0) (div_le_div_of_nonneg_left hn0.le (by linarith) hNt)
    have hba : b - a ≤ 1 / N := by
      simp only [a, b]
      rw [← Real.log_div (div_pos hn0 (by linarith)).ne' (div_pos hn0 ht0).ne',
        show (n : ℝ) / N / (n / t) = t / N by field_simp]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [div_sub_one (by linarith), div_le_div_iff_of_pos_right (by linarith)]
      linarith
    have hea : Real.exp (-a) ≤ 2 * N / n := by
      simp only [a]
      rw [Real.exp_neg, Real.exp_log (div_pos hn0 ht0), inv_div, div_le_div_iff_of_pos_right hn0]
      linarith
    have hmvt : |thetaCuspFullSource b - thetaCuspFullSource a| ≤ C1 * (2 * N / n) * (b - a) := by
      rcases eq_or_lt_of_le hab with heq | hlt
      · rw [heq, sub_self, abs_zero, sub_self, mul_zero]
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope thetaCuspFullSource
        (deriv thetaCuspFullSource) hlt (continuous_thetaCuspFullSource.continuousOn)
        (fun x _ => (differentiable_thetaCuspFullSource x).hasDerivAt)
      rw [eq_div_iff (by linarith)] at hceq
      rw [← hceq, abs_mul, abs_of_pos (by linarith : 0 < b - a)]
      refine mul_le_mul_of_nonneg_right ((hC1 c).trans ?_) (by linarith)
      rw [abs_of_nonneg (by linarith [hc.1] : 0 ≤ c), one_mul]
      exact mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 (by linarith [hc.1])).trans hea) hC10
    have hw := abs_moebiusInvSqrtWeight_le n
    rw [moebiusInvSqrtWeight] at hw
    rw [show ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource a -
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource b =
        -(((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) *
          (thetaCuspFullSource b - thetaCuspFullSource a) by ring, abs_mul, abs_neg]
    have hsplit : (n : ℝ) ^ (-(3 / 2 : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]; norm_num
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))| *
          |thetaCuspFullSource b - thetaCuspFullSource a|
        ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (C1 * (2 * N / n) * (1 / N)) :=
          mul_le_mul hw (hmvt.trans (mul_le_mul_of_nonneg_left hba (by positivity))) (abs_nonneg _)
            (Real.rpow_nonneg hn0.le _)
      _ = 2 * C1 * ((n : ℝ) ^ (-(3 / 2 : ℝ))) := by rw [hsplit]; field_simp
  have hs1 := summable_causalMobiusThetaTerm t
  have hs2 := summable_causalMobiusThetaTerm (N : ℝ)
  have hfs : Summable f := hs1.sub hs2
  obtain ⟨hsh, hsh2⟩ := tsum_shift_rpow_neg_three_halves_le hN
  rw [causalMobiusThetaTail, causalMobiusThetaTail, ← hs1.tsum_sub hs2,
    ← hfs.sum_add_tsum_nat_add (N + 1), Finset.sum_eq_zero fun n hn =>
      hzero n (by have := Finset.mem_range.1 hn; omega), zero_add]
  calc |∑' j, f (j + (N + 1))| ≤ ∑' j, 2 * C1 * (((N + 1 + j : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [← Real.norm_eq_abs]
        refine tsum_of_norm_bounded (hsh.mul_left (2 * C1)).hasSum fun j => ?_
        rw [Real.norm_eq_abs, show j + (N + 1) = N + 1 + j by ring]
        exact hbound _ (by omega)
    _ ≤ 2 * C1 * (2 * (Real.sqrt N)⁻¹) := by
        rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hsh2 (by positivity)
    _ = 4 * C1 * (Real.sqrt N)⁻¹ := by ring

end

end RHTower
