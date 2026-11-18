import GaloisForLFunctions.RHTower.LogVonMangoldtGaussianSums
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence

/-!
# Coincident products of ordinary prime weights

For two finite cofactors dividing the same product, divide the product by
their least common multiple. The remaining variable occurs as the common
factor in two von Mangoldt weights. Beyond its first term their correlation
is supported on powers of a single prime and can be summed exactly.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- On the positive integers greater than one, simultaneous nonzero
dilates of the von Mangoldt weight force both dilations and their argument
to be powers of the least prime divisor of the first dilation. -/
theorem prime_powers_of_dilated_mangoldt_product {a b n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n)
    (h : vonMangoldt (a*n) * vonMangoldt (b*n) ≠ 0) :
    (∃ i : ℕ, a = a.minFac ^ i) ∧ (∃ j : ℕ, b = a.minFac ^ j) ∧
      ∃ k : ℕ, 0 < k ∧ n = a.minFac ^ k := by
  let p := a.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hL := vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)
  have hR := vonMangoldt_ne_zero_iff.mp (right_ne_zero_of_mul h)
  obtain ⟨e, _, he⟩ := RHTower.GaussZeroSum.eq_minFac_pow_of_dvd ha (dvd_mul_right a n) hL
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp
    (show a ∣ p ^ e by rw [← he]; exact dvd_mul_right a n)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp
    (show n ∣ p ^ e by rw [← he]; exact dvd_mul_left n a)
  have hkpos : 0 < k := by
    by_contra! hk0
    simp [Nat.eq_zero_of_le_zero hk0] at hk
    omega
  have hpn : p ∣ n := hk ▸ dvd_pow_self _ hkpos.ne'
  obtain ⟨f, _, hf⟩ := RHTower.GaussZeroSum.eq_minFac_pow_of_dvd hp.two_le
    (dvd_mul_of_dvd_right hpn b) hR
  rw [hp.minFac_eq] at hf
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp
    (show b ∣ p ^ f by rw [← hf]; exact dvd_mul_right b n)
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hkpos, hk⟩⟩

private theorem mangoldt_weights_on_prime_powers {p a b n : ℕ} (hp : p.Prime)
    (ha : ∃ i : ℕ, a = p ^ i) (hb : ∃ j : ℕ, b = p ^ j)
    (hn : ∃ k : ℕ, 0 < k ∧ n = p ^ k) :
    vonMangoldt (a*n) * vonMangoldt (b*n) = Real.log p * vonMangoldt n := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hn
  rw [← pow_add, ← pow_add, vonMangoldt_apply_pow (by omega : i+k ≠ 0),
    vonMangoldt_apply_pow (by omega : j+k ≠ 0), vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hp]

open Classical in
/-- Closed form for the off-diagonal prime-weight correlation with a common
integer factor. The term at one is excluded and equals `Λ(a)Λ(b)` separately. -/
theorem sum_dilated_mangoldt_product {a : ℕ} (ha : 2 ≤ a) (b : ℕ) {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 2 X, vonMangoldt (a*n) * vonMangoldt (b*n) =
      if (∃ i : ℕ, a = a.minFac ^ i) ∧ (∃ j : ℕ, b = a.minFac ^ j) then
        Real.log a.minFac * Real.log ((a.minFac ^ Nat.log a.minFac X : ℕ) : ℝ)
      else 0 := by
  classical
  let p := a.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  let Q := p ^ Nat.log p X
  have hQ : Q ≤ X := Nat.pow_log_le_self _ (by omega)
  have hQpos : 0 < Q := pow_pos hp.pos _
  by_cases hd : (∃ i : ℕ, a = p ^ i) ∧ (∃ j : ℕ, b = p ^ j)
  · rw [if_pos hd]
    have hterm (n : ℕ) (hn : n ∈ Icc 2 X) :
        vonMangoldt (a*n) * vonMangoldt (b*n) = if n ∣ Q then Real.log p * vonMangoldt n else 0 := by
      obtain ⟨hn2, hnX⟩ := mem_Icc.mp hn
      split_ifs with hdiv
      · obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdiv
        have hkpos : 0 < k := by
          by_contra! h
          simp [Nat.eq_zero_of_le_zero h] at hk
          omega
        exact mangoldt_weights_on_prime_powers hp hd.1 hd.2 ⟨k, hkpos, hk⟩
      · by_contra h
        obtain ⟨k, _, hk⟩ := (prime_powers_of_dilated_mangoldt_product ha hn2 h).2.2
        have hkle := (Nat.le_log_iff_pow_le hp.one_lt (by omega : X ≠ 0)).mpr
          (show p ^ k ≤ X by rw [← hk]; exact hnX)
        exact hdiv (hk ▸ pow_dvd_pow p hkle)
    have hsupport : (Icc 2 X).filter (· ∣ Q) = Q.divisors.erase 1 := by
      ext n
      simp only [mem_filter, mem_Icc, mem_erase, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hn, _⟩, hdvd⟩
        exact ⟨by omega, hdvd, hQpos.ne'⟩
      · rintro ⟨hne, hdvd, _⟩
        have hn0 := Nat.pos_of_dvd_of_pos hdvd hQpos
        exact ⟨⟨by omega, (Nat.le_of_dvd hQpos hdvd).trans hQ⟩, hdvd⟩
    rw [sum_congr rfl hterm, ← sum_filter, hsupport, ← mul_sum]
    have hhead : (∑ n ∈ Q.divisors.erase 1, vonMangoldt n) = ∑ n ∈ Q.divisors, vonMangoldt n := by
      apply sum_subset (erase_subset _ _)
      intro n hn hnot
      by_cases h : n = 1
      · simpa only [h] using vonMangoldt_apply_one
      · exact False.elim (hnot (mem_erase.mpr ⟨h, hn⟩))
    rw [hhead, vonMangoldt_sum]
  · rw [if_neg hd]
    apply sum_eq_zero
    intro n hn
    by_contra h
    obtain ⟨h₁, h₂, _⟩ := prime_powers_of_dilated_mangoldt_product ha (mem_Icc.mp hn).1 h
    exact hd ⟨h₁, h₂⟩

/-- Uniform logarithmic upper bound for the common-factor tail,
independent of the second dilation. -/
theorem sum_dilated_mangoldt_product_le {a : ℕ} (ha : 2 ≤ a) (b : ℕ) {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 2 X, vonMangoldt (a*n) * vonMangoldt (b*n) ≤ Real.log a * Real.log X := by
  classical
  rw [sum_dilated_mangoldt_product ha b hX]
  split_ifs
  · have hp : a.minFac.Prime := Nat.minFac_prime (by omega)
    apply mul_le_mul
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast Nat.minFac_le (by omega : 0 < a))
    · have hpos : 0 < a.minFac ^ Nat.log a.minFac X := pow_pos hp.pos _
      exact Real.log_le_log (by exact_mod_cast hpos)
        (by exact_mod_cast Nat.pow_log_le_self a.minFac (by omega : X ≠ 0))
    · exact Real.log_natCast_nonneg _
    · exact Real.log_natCast_nonneg _
  · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

/-- The logarithmic bound survives an arbitrary restriction on both prime
heads and an arbitrary complex weight bounded by one on the retained rows. -/
theorem norm_sum_weighted_dilated_mangoldt_le {a X : ℕ} (ha : 2 ≤ a) (b : ℕ) (hX : 1 ≤ X)
    (S : Finset ℕ) (hS : S ⊆ Icc 2 X) (w : ℕ → ℂ) (hw : ∀ n ∈ S, ‖w n‖ ≤ 1) :
    ‖∑ n ∈ S, w n * ((vonMangoldt (a*n) * vonMangoldt (b*n) : ℝ) : ℂ)‖ ≤
      Real.log a * Real.log X := by
  have hpos (n : ℕ) : 0 ≤ vonMangoldt (a*n) * vonMangoldt (b*n) :=
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  calc
    _ ≤ ∑ n ∈ S, ‖w n * ((vonMangoldt (a*n) * vonMangoldt (b*n) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, vonMangoldt (a*n) * vonMangoldt (b*n) := by
      refine sum_le_sum fun n hn => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos n)]
      exact mul_le_of_le_one_left (hpos n) (hw n hn)
    _ ≤ ∑ n ∈ Icc 2 X, vonMangoldt (a*n) * vonMangoldt (b*n) :=
      sum_le_sum_of_subset_of_nonneg hS fun n _ _ => hpos n
    _ ≤ _ := sum_dilated_mangoldt_product_le ha b hX

/-- Two distinct cofactor divisibility conditions have a logarithmic total
prime-weight overlap beyond the single product at their least common multiple.
The weights here are evaluated at the actual complementary factors. -/
theorem sum_coincident_prime_weights_le {d e N : ℕ} (hd : 0 < d) (he : 0 < e) (hne : d ≠ e)
    (hN : Nat.lcm d e ≤ N) :
    let L := Nat.lcm d e
    (∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n), vonMangoldt (n/d) * vonMangoldt (n/e)) ≤
      vonMangoldt (L/d) * vonMangoldt (L/e) + Real.log L * Real.log (N/L : ℕ) := by
  intro L
  let a := L / d
  let b := L / e
  let J := N / L
  have hL : 0 < L := Nat.lcm_pos hd he
  have hdL : d ∣ L := Nat.dvd_lcm_left d e
  have heL : e ∣ L := Nat.dvd_lcm_right d e
  have hJ : 1 ≤ J := (Nat.one_le_div_iff hL).mpr hN
  have hsplit {z : ℕ} (hz : z ∣ L) (k : ℕ) : L*k/z = (L/z)*k := by
    rw [Nat.mul_comm L k, Nat.mul_div_assoc k hz, Nat.mul_comm]
  have hmask : (Icc 1 N).filter (fun n => d ∣ n ∧ e ∣ n) = (Icc 1 N).filter (L ∣ ·) := by
    ext n
    simp only [mem_filter, L, Nat.lcm_dvd_iff]
  rw [hmask, RHTower.sum_Icc_filter_dvd_reindex L N hL]
  simp_rw [hsplit hdL, hsplit heL]
  change (∑ k ∈ Icc 1 J, vonMangoldt (a*k) * vonMangoldt (b*k)) ≤ _
  have htail : (Icc 1 J).erase 1 = Icc 2 J := by
    ext k
    simp only [mem_erase, mem_Icc]
    omega
  rw [← sum_erase_add _ _ (mem_Icc.mpr ⟨le_rfl, hJ⟩), htail, mul_one, mul_one, add_comm]
  refine add_le_add le_rfl ?_
  have hbound {u v : ℕ} (hu : 2 ≤ u) (huL : u ≤ L) :
      ∑ k ∈ Icc 2 J, vonMangoldt (u*k) * vonMangoldt (v*k) ≤ Real.log L * Real.log J :=
    (sum_dilated_mangoldt_product_le hu v hJ).trans (mul_le_mul_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < u)) (by exact_mod_cast huL))
      (Real.log_natCast_nonneg J))
  by_cases ha : 2 ≤ a
  · exact hbound ha (Nat.div_le_self L d)
  have hb : 2 ≤ b := by
    by_contra! hb
    have ha1 : a = 1 := le_antisymm (by omega)
      ((Nat.one_le_div_iff hd).mpr (Nat.le_of_dvd hL hdL))
    have hb1 : b = 1 := le_antisymm (by omega)
      ((Nat.one_le_div_iff he).mpr (Nat.le_of_dvd hL heL))
    have h₁ : a * d = L := Nat.div_mul_cancel hdL
    have h₂ : b * e = L := Nat.div_mul_cancel heL
    rw [ha1, one_mul] at h₁
    rw [hb1, one_mul] at h₂
    exact hne (h₁.trans h₂.symm)
  calc
    _ = ∑ k ∈ Icc 2 J, vonMangoldt (b*k) * vonMangoldt (a*k) :=
      sum_congr rfl fun k _ => mul_comm _ _
    _ ≤ _ := hbound hb (Nat.div_le_self L e)

#print axioms sum_dilated_mangoldt_product
#print axioms norm_sum_weighted_dilated_mangoldt_le
#print axioms sum_coincident_prime_weights_le

end GaloisForLFunctions.ExceptionalLayerTheory
