import GaloisForLFunctions.RHTower.KloostermanComposite
import GaloisForLFunctions.RHTower.EstermannKloostermanSaving
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.SmoothNumbers

open RHTower.Sieve

/-!
# Absolute convergence of the Kloosterman zeta function

`kmax(c) = max_{a unit} |S(am, an; c)|` is submultiplicative on coprime moduli (twisted multiplicativity,
`kmax_mul`). Weil's bound at good primes, the prime-power bound `2p^{⌈k/2⌉}`, and the trivial bound at `2` and at
primes dividing `n`, together with a general summability criterion for submultiplicative functions
(`summable_of_submult`, via smooth-number Euler products), give
`Σ_{c ≥ 1} |S(m, n; c)| c^{-2σ} < ∞` for `n ≠ 0` and `σ > 3/4` (`kloosterman_zeta_summable`). This is the
arithmetic input of Selberg's `λ₁ ≥ 3/16`.
-/

namespace GaloisForLFunctions.RHTower.KloostermanZeta

open GaloisForLFunctions.RHTower.KloostermanComposite

noncomputable section

/-- The largest Kloosterman sum `|S(am, an; c)|` over units `a` modulo `c` (zero for `c = 0`). -/
def kmax (m n : ℤ) (c : ℕ) : ℝ :=
  if h : c = 0 then 0 else
    haveI : NeZero c := ⟨h⟩
    ⨆ a : (ZMod c)ˣ, ‖kloostermanSum c ((a : ZMod c) * m) ((a : ZMod c) * n)‖

theorem kmax_eq (m n : ℤ) (c : ℕ) [hc : NeZero c] :
    kmax m n c = ⨆ a : (ZMod c)ˣ, ‖kloostermanSum c ((a : ZMod c) * m) ((a : ZMod c) * n)‖ := by
  rw [kmax, dif_neg hc.ne]

theorem le_kmax (m n : ℤ) (c : ℕ) [NeZero c] {x : ZMod c} (hx : IsUnit x) :
    ‖kloostermanSum c (x * m) (x * n)‖ ≤ kmax m n c := by
  rw [kmax_eq]
  obtain ⟨u, rfl⟩ := hx
  exact le_ciSup (f := fun a : (ZMod c)ˣ => ‖kloostermanSum c ((a : ZMod c) * m) ((a : ZMod c) * n)‖)
    (Set.finite_range _).bddAbove u

theorem kmax_le (m n : ℤ) (c : ℕ) [NeZero c] {B : ℝ}
    (h : ∀ x : ZMod c, IsUnit x → ‖kloostermanSum c (x * m) (x * n)‖ ≤ B) : kmax m n c ≤ B := by
  rw [kmax_eq]
  exact ciSup_le (fun a => h a a.isUnit)

theorem kmax_nonneg (m n : ℤ) (c : ℕ) : 0 ≤ kmax m n c := by
  by_cases hc : c = 0
  · simp [kmax, hc]
  · haveI : NeZero c := ⟨hc⟩
    exact (norm_nonneg _).trans (le_kmax m n c (x := 1) isUnit_one)

theorem kmax_one (m n : ℤ) : kmax m n 1 ≤ 1 := by
  apply kmax_le
  intro x _
  refine (norm_kloostermanSum_le_totient 1 _ _).trans ?_
  simp

/-- **Submultiplicativity** from twisted multiplicativity. -/
theorem kmax_mul (m n : ℤ) {q r : ℕ} (h : q.Coprime r) : kmax m n (q * r) ≤ kmax m n q * kmax m n r := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp [kmax]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [kmax]
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  haveI : NeZero (q * r) := ⟨(Nat.mul_pos hq hr).ne'⟩
  apply kmax_le
  intro x hx
  rw [kloostermanSum_mul h, norm_mul]
  set e := ZMod.chineseRemainder h
  have hrq : IsUnit ((r : ZMod q))⁻¹ := by
    rw [← ZMod.coe_unitOfCoprime r h.symm, ZMod.inv_coe_unit]; exact Units.isUnit _
  have hqr : IsUnit ((q : ZMod r))⁻¹ := by
    rw [← ZMod.coe_unitOfCoprime q h, ZMod.inv_coe_unit]; exact Units.isUnit _
  have hx1 : IsUnit (e x).1 := (hx.map e.toRingHom).map (RingHom.fst _ _)
  have hx2 : IsUnit (e x).2 := (hx.map e.toRingHom).map (RingHom.snd _ _)
  have em : ∀ z : ℤ, e (z : ZMod (q * r)) = ((z : ZMod q), (z : ZMod r)) := fun z => by
    rw [map_intCast]; rfl
  simp only [map_mul, em, Prod.fst_mul, Prod.snd_mul]
  apply mul_le_mul _ _ (norm_nonneg _) (kmax_nonneg m n q)
  · have := le_kmax m n q (hx1.mul hrq)
    refine le_of_eq_of_le ?_ this
    congr 2 <;> ring
  · have := le_kmax m n r (hx2.mul hqr)
    refine le_of_eq_of_le ?_ this
    congr 2 <;> ring


theorem kmax_le_self (m n : ℤ) (c : ℕ) : kmax m n c ≤ c := by
  by_cases hc : c = 0
  · simp [kmax, hc]
  haveI : NeZero c := ⟨hc⟩
  apply kmax_le
  intro x _
  refine (norm_kloostermanSum_le_totient c _ _).trans ?_
  exact_mod_cast Nat.totient_le c

theorem isUnit_intCast_of_not_dvd {p k : ℕ} [hp : Fact p.Prime] {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    IsUnit ((n : ZMod (p ^ k))) := by
  have : (n : ZMod (p ^ k)) = ((n.natAbs : ℕ) : ZMod (p ^ k)) * (n.sign : ZMod (p ^ k)) := by
    rcases Int.natAbs_eq n with h | h
    · conv_lhs => rw [h]
      rcases lt_trichotomy n 0 with h0 | h0 | h0
      · omega
      · subst h0; simp at hn
      · simp [Int.sign_eq_one_of_pos h0]
    · conv_lhs => rw [h]
      rcases lt_trichotomy n 0 with h0 | h0 | h0
      · simp [Int.sign_eq_neg_one_of_neg h0]
      · subst h0; simp at hn
      · omega
  rw [this]
  refine IsUnit.mul ?_ ?_
  · rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hd; apply hn
    exact Int.natCast_dvd.mpr hd
  · rcases Int.sign_trichotomy n with h | h | h
    · simp [h]
    · exact absurd (by rw [Int.sign_eq_zero_iff_zero.mp h]; exact dvd_zero _) hn
    · simp [h]

/-- Weil at a good prime. -/
theorem kmax_prime_le (m n : ℤ) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : ¬ (p : ℤ) ∣ n) :
    kmax m n p ≤ 2 * Real.sqrt p := by
  apply kmax_le
  intro x hx
  apply _root_.RHTower.norm_kloostermanSum_le_weil p hp2
  have hn' : (n : ZMod p) ≠ 0 := fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp h)
  exact mul_ne_zero hx.ne_zero hn'

/-- Prime powers at a good prime. -/
theorem kmax_prime_pow_le (m n : ℤ) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : ¬ (p : ℤ) ∣ n)
    {k : ℕ} (hk : 2 ≤ k) : kmax m n (p ^ k) ≤ 2 * (p : ℝ) ^ ((k + 1) / 2) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  apply kmax_le
  intro x hx
  exact norm_kloostermanSum_prime_pow_le p k ((k + 1) / 2) hp2 (by omega) (by omega) _
    (hx.mul (isUnit_intCast_of_not_dvd hn))

end

section submult
open Finset
variable {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg1 : g 1 ≤ 1)
  (hmul : ∀ a b, a.Coprime b → g (a * b) ≤ g a * g b)
  (hs : ∀ p, p.Prime → Summable (fun k => g (p ^ (k + 1))))

/-- Local factor `1 + Σ_{k ≥ 1} g(p^k)`. -/
noncomputable def localFactor (g : ℕ → ℝ) (p : ℕ) : ℝ := 1 + ∑' k, g (p ^ (k + 1))

include hg0 hg1 hs in
theorem sum_pow_le {p : ℕ} (hp : p.Prime) (S : Finset ℕ) : ∑ e ∈ S, g (p ^ e) ≤ localFactor g p := by
  classical
  unfold localFactor
  have hS : S ⊆ insert 0 ((S.filter (· ≠ 0)).image id) := by
    intro e he; by_cases h : e = 0
    · simp [h]
    · exact mem_insert_of_mem (by simp [he, h])
  calc ∑ e ∈ S, g (p ^ e) ≤ g (p ^ 0) + ∑ e ∈ S.filter (· ≠ 0), g (p ^ e) := by
        rw [← sum_filter_add_sum_filter_not S (· ≠ 0), add_comm]
        gcongr
        calc ∑ e ∈ S.filter (fun e => ¬ e ≠ 0), g (p ^ e) ≤ ∑ e ∈ ({0} : Finset ℕ), g (p ^ e) :=
              sum_le_sum_of_subset_of_nonneg (fun e he => by simp at he; simp [he.2])
                (fun _ _ _ => hg0 _)
          _ = g (p ^ 0) := by simp
    _ ≤ 1 + ∑' k, g (p ^ (k + 1)) := by
        rw [pow_zero]
        gcongr
        calc ∑ e ∈ S.filter (· ≠ 0), g (p ^ e) = ∑ k ∈ (S.filter (· ≠ 0)).image (· - 1), g (p ^ (k + 1)) := by
              rw [sum_image]
              · apply sum_congr rfl; intro e he
                have : e ≠ 0 := (mem_filter.mp he).2
                congr 2; omega
              · intro a ha b hb h
                have := (mem_filter.mp ha).2; have := (mem_filter.mp hb).2
                simp at h; omega
          _ ≤ _ := (hs p hp).sum_le_tsum _ (fun k _ => hg0 _)

include hg0 hg1 hmul hs in
/-- Finite sums over `N`-smooth numbers are bounded by the product of local factors below `N`. -/
theorem sum_smooth_le (N : ℕ) : ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ N.smoothNumbers →
    ∑ n ∈ F, g n ≤ ∏ p ∈ N.primesBelow, localFactor g p := by
  classical
  induction N with
  | zero =>
    intro F hF
    have : F ⊆ {1} := by
      intro n hn; have := hF hn; rw [Nat.smoothNumbers_zero] at this; simpa using this
    calc ∑ n ∈ F, g n ≤ ∑ n ∈ ({1} : Finset ℕ), g n :=
          sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => hg0 _)
      _ ≤ _ := by simp [hg1]
  | succ N ih =>
    intro F hF
    by_cases hN : N.Prime
    · -- `F ⊆ (N+1)`-smooth numbers `= p^e m`
      set e := Nat.equivProdNatSmoothNumbers hN
      set F' : Finset (ℕ × N.smoothNumbers) :=
        (F.attach.image (fun n => e.symm ⟨n.1, hF n.2⟩))
      have hF' : ∑ n ∈ F, g n = ∑ x ∈ F', g (N ^ x.1 * x.2) := by
        rw [sum_image (fun a _ b _ h => by
          have := congrArg e h; simp at this; exact this)]
        rw [← sum_attach F]
        apply sum_congr rfl; intro n _
        have := Nat.equivProdNatSmoothNumbers_apply' hN (e.symm ⟨n.1, hF n.2⟩)
        rw [Equiv.apply_symm_apply] at this
        simp only at this ⊢
        rw [← this]
      rw [hF']
      set E := F'.image Prod.fst
      set M := F'.image Prod.snd
      have hlocal : 0 ≤ localFactor g N := by
        have := sum_pow_le hg0 hg1 hs hN ∅; simpa using this
      calc ∑ x ∈ F', g (N ^ x.1 * x.2) ≤ ∑ x ∈ E ×ˢ M, g (N ^ x.1) * g x.2 := by
            apply (sum_le_sum (fun x _ => hmul _ _ ((Nat.Coprime.pow_left _
              (hN.smoothNumbers_coprime x.2.2))))).trans
            apply sum_le_sum_of_subset_of_nonneg
            · intro x hx; exact mem_product.mpr ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hx⟩
            · intro _ _ _; exact mul_nonneg (hg0 _) (hg0 _)
        _ = (∑ a ∈ E, g (N ^ a)) * ∑ m ∈ M, g m := by rw [sum_product, sum_mul_sum]
        _ ≤ localFactor g N * ∏ p ∈ N.primesBelow, localFactor g p := by
            apply mul_le_mul (sum_pow_le hg0 hg1 hs hN E) _ (sum_nonneg (fun _ _ => hg0 _)) hlocal
            have := ih (M.image Subtype.val) (by
              intro n hn; simp only [coe_image, Set.mem_image] at hn
              obtain ⟨m, _, rfl⟩ := hn; exact m.2)
            rwa [sum_image (fun a _ b _ h => Subtype.ext h)] at this
        _ = ∏ p ∈ (N + 1).primesBelow, localFactor g p := by
            rw [Nat.primesBelow_succ, if_pos hN, prod_insert (by simp [Nat.mem_primesBelow])]
    · have h := Nat.smoothNumbers_succ hN
      rw [h] at hF
      rw [Nat.primesBelow_succ, if_neg hN]
      exact ih F hF

include hg0 hg1 hmul hs in
/-- **Summability of submultiplicative functions.** A nonnegative `g` with `g 1 ≤ 1`, `g(ab) ≤ g(a)g(b)` for
coprime `a, b`, and summable prime-power series `E(p) = Σ_{k ≥ 1} g(p^k)` with `Σ_p E(p) < ∞` is summable. -/
theorem summable_of_submult (hE : Summable (fun p : Nat.Primes => ∑' k, g ((p : ℕ) ^ (k + 1)))) :
    Summable g := by
  classical
  set T := ∑' p : Nat.Primes, ∑' k, g ((p : ℕ) ^ (k + 1))
  have hEnn : ∀ p, 0 ≤ ∑' k, g (p ^ (k + 1)) := fun p => tsum_nonneg (fun _ => hg0 _)
  refine summable_of_sum_range_le hg0 (c := g 0 + Real.exp T) (fun N => ?_)
  have hsplit : ∑ n ∈ range N, g n ≤ g 0 + ∑ n ∈ (range N).erase 0, g n := by
    by_cases h0 : 0 ∈ range N
    · rw [← add_sum_erase _ _ h0]
    · rw [erase_eq_of_notMem h0]; linarith [hg0 0]
  refine hsplit.trans (add_le_add_right ?_ _)
  have hsm := sum_smooth_le hg0 hg1 hmul hs N ((range N).erase 0) (by
    intro n hn
    simp only [coe_erase, coe_range, Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff] at hn
    exact Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn.2) hn.1)
  refine hsm.trans ?_
  calc ∏ p ∈ N.primesBelow, localFactor g p ≤ ∏ p ∈ N.primesBelow, Real.exp (∑' k, g (p ^ (k + 1))) := by
        apply prod_le_prod
        · intro p _; unfold localFactor; linarith [hEnn p]
        · intro p _; unfold localFactor; linarith [Real.add_one_le_exp (∑' k, g (p ^ (k + 1)))]
    _ = Real.exp (∑ p ∈ N.primesBelow, ∑' k, g (p ^ (k + 1))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp T := by
        apply Real.exp_le_exp.mpr
        have hsub : ∑ p ∈ N.primesBelow, ∑' k, g (p ^ (k + 1)) =
            ∑ p ∈ N.primesBelow.subtype Nat.Prime, ∑' k, g ((p : ℕ) ^ (k + 1)) := by
          exact (sum_subtype_of_mem (fun p => ∑' k, g (p ^ (k + 1)))
            (fun p hp => Nat.prime_of_mem_primesBelow hp)).symm
        rw [hsub]
        have hE' : Summable (fun p : {p : ℕ // p.Prime} => ∑' k, g ((p : ℕ) ^ (k + 1))) := hE
        exact le_of_le_of_eq (hE'.sum_le_tsum _ (fun p _ => hEnn (p : ℕ))) rfl

end submult

section zeta

/-- The weighted Kloosterman coefficient `kmax(c) c^{-2σ}`. -/
noncomputable def kw (m n : ℤ) (σ : ℝ) (c : ℕ) : ℝ := kmax m n c * (c : ℝ) ^ (-2 * σ)

variable {m n : ℤ} {σ : ℝ}

theorem kw_nonneg (c : ℕ) : 0 ≤ kw m n σ c :=
  mul_nonneg (kmax_nonneg m n c) (Real.rpow_nonneg (Nat.cast_nonneg c) _)

theorem kw_one : kw m n σ 1 ≤ 1 := by
  simp only [kw, Nat.cast_one, Real.one_rpow, mul_one]; exact kmax_one m n

theorem kw_mul {a b : ℕ} (h : a.Coprime b) : kw m n σ (a * b) ≤ kw m n σ a * kw m n σ b := by
  simp only [kw, Nat.cast_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  have ha := Real.rpow_nonneg (Nat.cast_nonneg a) (-2 * σ)
  have hb := Real.rpow_nonneg (Nat.cast_nonneg b) (-2 * σ)
  have hk := kmax_mul m n h
  calc kmax m n (a * b) * ((a : ℝ) ^ (-2 * σ) * (b : ℝ) ^ (-2 * σ))
      ≤ kmax m n a * kmax m n b * ((a : ℝ) ^ (-2 * σ) * (b : ℝ) ^ (-2 * σ)) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg ha hb)
    _ = _ := by ring

theorem kw_pow_le_geom {p : ℕ} (hp : p.Prime) (k : ℕ) :
    kw m n σ (p ^ k) ≤ ((p : ℝ) ^ (1 - 2 * σ)) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [kw]
  calc kmax m n (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-2 * σ)
      ≤ ((p ^ k : ℕ) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right (kmax_le_self m n _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ((p : ℝ) ^ (1 - 2 * σ)) ^ k := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le,
          ← Real.rpow_add hp0]
        congr 1; ring



theorem kw_prime_le {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : ¬ (p : ℤ) ∣ n) :
    kw m n σ p ≤ 2 * (p : ℝ) ^ (1 / 2 - 2 * σ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  simp only [kw]
  calc kmax m n p * (p : ℝ) ^ (-2 * σ) ≤ 2 * Real.sqrt p * (p : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right (kmax_prime_le m n hp2 hn) (Real.rpow_nonneg hp0.le _)
    _ = 2 * (p : ℝ) ^ (1 / 2 - 2 * σ) := by
        rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hp0]; ring_nf

theorem kw_prime_pow_le (hσ : 3 / 4 ≤ σ) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hn : ¬ (p : ℤ) ∣ n) {k : ℕ} (hk : 2 ≤ k) :
    kw m n σ (p ^ k) ≤ 2 * Real.sqrt p * ((p : ℝ)⁻¹) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  simp only [kw]
  have h1 : ((p : ℝ) ^ ((k + 1) / 2 : ℕ)) ≤ (p : ℝ) ^ (((k : ℝ) + 1) / 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have : (((k + 1) / 2 : ℕ) : ℝ) * 2 ≤ (k : ℝ) + 1 := by
      have := Nat.div_mul_le_self (k + 1) 2
      exact_mod_cast this
    linarith
  have h2 : ((p ^ k : ℕ) : ℝ) ^ (-2 * σ) ≤ (p : ℝ) ^ (-(3 / 2) * (k : ℝ)) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  calc kmax m n (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-2 * σ)
      ≤ (2 * (p : ℝ) ^ (((k : ℝ) + 1) / 2)) * (p : ℝ) ^ (-(3 / 2) * (k : ℝ)) := by
        apply mul_le_mul _ h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact (kmax_prime_pow_le m n hp2 hn hk).trans (by linarith)
    _ = 2 * Real.sqrt p * ((p : ℝ)⁻¹) ^ k := by
        rw [Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hp0.le, mul_assoc, mul_assoc,
          ← Real.rpow_add hp0, ← Real.rpow_add hp0]
        congr 2; ring



theorem kw_hs (hσ : 1 / 2 < σ) {p : ℕ} (hp : p.Prime) : Summable (fun k => kw m n σ (p ^ (k + 1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set r := (p : ℝ) ^ (1 - 2 * σ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by linarith) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  refine Summable.of_nonneg_of_le (fun k => kw_nonneg _) (fun k => kw_pow_le_geom hp (k + 1)) ?_
  simp_rw [pow_succ]
  exact (summable_geometric_of_lt_one hr0 hr1).mul_right r

/-- The local sum at a good prime is `≤ 2 p^{1/2 - 2σ} + 4 p^{-3/2}`. -/
theorem kw_local_le (hσ : 3 / 4 < σ) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : ¬ (p : ℤ) ∣ n) :
    ∑' k, kw m n σ (p ^ (k + 1)) ≤ 2 * (p : ℝ) ^ (1 / 2 - 2 * σ) + 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hs := kw_hs (m := m) (n := n) (by linarith : 1 / 2 < σ) hp.out
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add, pow_one]
  apply add_le_add (kw_prime_le hp2 hn)
  set q := (p : ℝ)⁻¹
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by simp only [q]; rw [inv_lt_one₀ hp0]; linarith
  have hb : ∀ k, kw m n σ (p ^ (k + 1 + 1)) ≤ 2 * Real.sqrt p * q ^ 2 * q ^ k := by
    intro k
    have := kw_prime_pow_le (m := m) (n := n) hσ.le hp2 hn (k := k + 2) (by omega)
    rw [show k + 1 + 1 = k + 2 by ring]
    refine this.trans (le_of_eq ?_)
    ring
  have hsum : Summable (fun k : ℕ => 2 * Real.sqrt p * q ^ 2 * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∑' k, kw m n σ (p ^ (k + 1 + 1)) ≤ ∑' k : ℕ, 2 * Real.sqrt p * q ^ 2 * q ^ k :=
        (hs.comp_injective (add_left_injective 1)).tsum_le_tsum hb hsum
    _ = 2 * Real.sqrt p * q ^ 2 * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    _ ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        have h1q : (1 - q)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          simp only [q]
          rw [le_sub_comm, inv_le_comm₀ hp0 (by norm_num)]; linarith
        have heq : Real.sqrt p * q ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
          simp only [q]
          rw [Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0]
          norm_num
        have hpos : 0 ≤ Real.sqrt p * q ^ 2 := by positivity
        calc 2 * Real.sqrt p * q ^ 2 * (1 - q)⁻¹ = 2 * (Real.sqrt p * q ^ 2) * (1 - q)⁻¹ := by ring
          _ ≤ 2 * (Real.sqrt p * q ^ 2) * 2 := by gcongr
          _ = 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [heq]; ring

/-- **Absolute convergence of the Kloosterman zeta function.** For `n ≠ 0` and `σ > 3/4`,
`Σ_c max_a |S(am, an; c)| c^{-2σ}` converges. -/
theorem kw_summable (hn : n ≠ 0) (hσ : 3 / 4 < σ) : Summable (kw m n σ) := by
  classical
  apply summable_of_submult (fun c => kw_nonneg c) kw_one (fun a b h => kw_mul h)
    (fun p hp => kw_hs (by linarith) hp)
  set E : Nat.Primes → ℝ := fun p => ∑' k, kw m n σ ((p : ℕ) ^ (k + 1))
  set M : ℕ := max 2 n.natAbs
  set bad : Finset Nat.Primes := (Finset.range (M + 1)).subtype Nat.Prime
  set B : Nat.Primes → ℝ := fun p => 2 * ((p : ℕ) : ℝ) ^ (1 / 2 - 2 * σ) + 4 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
  have hB : Summable B := by
    apply Summable.add
    · exact (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 2
    · exact (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left 4
  have hF : Summable (fun p => if p ∈ bad then E p else 0) :=
    summable_of_ne_finset_zero (s := bad) (fun p hp => if_neg hp)
  have hEnn : ∀ p, 0 ≤ E p := fun p => tsum_nonneg (fun _ => kw_nonneg _)
  refine Summable.of_nonneg_of_le hEnn (fun p => ?_) (hB.add hF)
  by_cases hp : p ∈ bad
  · simp only [if_pos hp]
    have : 0 ≤ B p := by simp only [B]; positivity
    linarith
  · simp only [if_neg hp, add_zero]
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hpM : M < (p : ℕ) := by
      by_contra h; push Not at h
      exact hp (Finset.mem_subtype.mpr (Finset.mem_range.mpr (by omega)))
    have hp2 : (p : ℕ) ≠ 2 := by omega
    have hnd : ¬ ((p : ℕ) : ℤ) ∣ n := by
      intro hd
      have := Int.natAbs_dvd_natAbs.mpr hd
      simp only [Int.natAbs_natCast] at this
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) this
      omega
    exact kw_local_le hσ hp2 hnd



/-- **The Kloosterman zeta function converges absolutely for `Re s > 3/4`:**
`Σ_{c ≥ 1} |S(m, n; c)| c^{-2σ} < ∞` for `n ≠ 0`, `σ > 3/4`. -/
theorem kloosterman_zeta_summable (hn : n ≠ 0) (hσ : 3 / 4 < σ) :
    Summable (fun c : ℕ => ‖kloostermanSum (c + 1) (m : ZMod (c + 1)) (n : ZMod (c + 1))‖ *
      ((c + 1 : ℕ) : ℝ) ^ (-2 * σ)) := by
  have h := (summable_nat_add_iff 1).mpr (kw_summable (m := m) hn hσ)
  refine Summable.of_nonneg_of_le (fun c => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (fun c => ?_) h
  simp only [kw]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have := le_kmax m n (c + 1) (x := 1) isUnit_one
  simpa using this

end zeta

end GaloisForLFunctions.RHTower.KloostermanZeta
