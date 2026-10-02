import GaloisForLFunctions.RHTower.PrimeWindowHarmonicMultiplicity
import GaloisForLFunctions.RHTower.Sieve.TwistedDiagonalAdapted
import GaloisForLFunctions.RHTower.SteinhausComplexConvolution

/-!
# Prime-masked resonator convolution energy

Exact GCD reindexing preserves both collision endpoints. Every free prime descends
to the reduced collision ray, whose complete spatial cutoff supplies the reciprocal
maximum reduced index. The full complex convolution square is therefore bounded
by GCD/max resonator energy times the harmonic free-prime density. No support
cardinality or independence assumption is used.
-/

open Finset
open scoped BigOperators
noncomputable section
namespace RHTower

/-- A dilation retains the complete prime-product cutoff and gains its full reciprocal scale. -/
theorem card_primeWindowSupported_dilate_mul_log_le_harmonic
    {S : Finset ℕ} {N H R : ℕ} (hH : 1 ≤ H) (hN : H ^ 2 ≤ N) (hR : 0 < R)
    (hS : ∀ n ∈ S, 0 < n ∧ R * n ≤ N) :
    ((primeWindowSupported S N H).card : ℝ) * Real.log N ≤
      (2 * (N : ℝ) * Real.log 4 / R) * ∑ k ∈ Icc 1 H, 1 / (k : ℝ) := by
  classical
  let P : ℕ → Finset ℕ := fun k => {p ∈ Nat.primesLE (N / (R * k)) | N / H < p}
  have hsub : primeWindowSupported S N H ⊆
      (Icc 1 H).biUnion (fun k => (P k).image (fun p => p * k)) := by
    intro n hn
    obtain ⟨hnS, p, hp, k, hnk⟩ := mem_filter.mp hn
    have hnkpos : 0 < p * k := by simpa [hnk] using (hS n hnS).1
    have hk0 : 0 < k := by nlinarith
    have hRpk : R * (p * k) ≤ N := by simpa [hnk] using (hS n hnS).2
    have hpk : p * k ≤ N := (Nat.le_mul_of_pos_left _ hR).trans hRpk
    have hNHp : N < p * H := (Nat.div_lt_iff_lt_mul (by omega)).mp (mem_largePrimes.mp hp).2
    have hkH : k ≤ H := by nlinarith
    have hpSlice : p ∈ P k := by
      apply mem_filter.mpr
      refine ⟨Nat.mem_primesLE.mpr ⟨?_, (mem_largePrimes.mp hp).1.2⟩, (mem_largePrimes.mp hp).2⟩
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hR hk0)).mpr
      nlinarith only [hRpk]
    exact mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨hk0, hkH⟩,
      mem_image.mpr ⟨p, hpSlice, hnk.symm⟩⟩
  have hcard : (primeWindowSupported S N H).card ≤ ∑ k ∈ Icc 1 H, (P k).card := by
    calc
      _ ≤ ((Icc 1 H).biUnion (fun k => (P k).image (fun p => p * k))).card := card_le_card hsub
      _ ≤ ∑ k ∈ Icc 1 H, ((P k).image (fun p => p * k)).card := card_biUnion_le
      _ ≤ _ := sum_le_sum (fun _ _ => card_image_le)
  have hcR : ((primeWindowSupported S N H).card : ℝ) ≤ ∑ k ∈ Icc 1 H, ((P k).card : ℝ) := by
    exact_mod_cast hcard
  have hN1 : 1 ≤ N := (by nlinarith : 1 ≤ H ^ 2).trans hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  calc
    _ ≤ (∑ k ∈ Icc 1 H, ((P k).card : ℝ)) * Real.log N :=
      mul_le_mul_of_nonneg_right hcR hlog
    _ = ∑ k ∈ Icc 1 H, ((P k).card : ℝ) * Real.log N := sum_mul _ _ _
    _ ≤ ∑ k ∈ Icc 1 H, 2 * (N : ℝ) * Real.log 4 * (1 / ((R * k : ℕ) : ℝ)) :=
      sum_le_sum (fun _ _ => card_prime_window_slice_mul_log_le hH hN)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      push_cast
      ring

/-- A free prime of a masked dilated integer descends to its cofactor when the dilation
lies below the free-prime window. -/
theorem primeWindowSupported_dilate_descent {S : Finset ℕ} {N H v d : ℕ}
    (hv : 0 < v) (hvN : v ≤ N / H) (hd : v * d ∈ primeWindowSupported S N H) :
    ∃ p ∈ largePrimes N (N / H), p ∣ d := by
  obtain ⟨_, p, hp, hpd⟩ := mem_filter.mp hd
  refine ⟨p, hp, ?_⟩
  rcases (mem_largePrimes.mp hp).1.2.dvd_mul.mp hpd with h1 | h2
  · exact (Nat.not_dvd_of_pos_of_lt hv (hvN.trans_lt (mem_largePrimes.mp hp).2) h1).elim
  · exact h2

/-- Exact resonator collisions inside the free-prime mask have GCD/max density.
Both masked endpoints and their original spatial cutoff are retained. -/
theorem card_primeWindow_collision_mul_log_le
    {S : Finset ℕ} {N H a b : ℕ} (hH : 1 ≤ H) (hN : H ^ 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hbN : b ≤ N / H)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ m ∈ primeWindowSupported S N H,
      (({n ∈ primeWindowSupported S N H | n * b = m * a}).card : ℝ)) * Real.log N ≤
      (2 * (N : ℝ) * Real.log 4 * ∑ k ∈ Icc 1 H, 1 / (k : ℝ)) *
        ((Nat.gcd a b : ℝ) / (max a b : ℕ)) := by
  classical
  let F := primeWindowSupported S N H
  let u := a / Nat.gcd a b
  let v := b / Nat.gcd a b
  let R := max u v
  let D := (Icc 1 N).filter (fun d => v * d ∈ F ∧ u * d ∈ F)
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left b ha) hg
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right a hb) hg
  have hR : 0 < R := hu.trans_le (le_max_left _ _)
  have hF (n : ℕ) (hn : n ∈ F) : 0 < n ∧ n ≤ N :=
    hS n (mem_filter.mp hn).1
  have hD (d : ℕ) : d ∈ D ↔ v * d ∈ F ∧ u * d ∈ F := by
    constructor
    · exact fun hd => (mem_filter.mp hd).2
    · intro hd
      have hd0 : 0 < d := by have := (hF _ hd.1).1; nlinarith
      have hdN : d ≤ N := (Nat.le_mul_of_pos_left _ hv).trans (hF _ hd.1).2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0, hdN⟩, hd⟩
  have hDS (d : ℕ) (hd : d ∈ D) : 0 < d ∧ R * d ≤ N := by
    have hm := mem_Icc.mp (mem_filter.mp hd).1
    have hpair := (hD d).mp hd
    refine ⟨hm.1, ?_⟩
    change max u v * d ≤ N
    rw [max_mul]
    exact max_le (hF _ hpair.2).2 (hF _ hpair.1).2
  have hmask : primeWindowSupported D N H = D := by
    apply filter_eq_self.mpr
    intro d hd
    exact primeWindowSupported_dilate_descent hv ((Nat.div_le_self b _).trans hbN)
      ((hD d).mp hd).1
  have heq : (∑ m ∈ F, (({n ∈ F | n * b = m * a}).card : ℝ)) = (D.card : ℝ) := by
    have he := Sieve.twisted_diagonal_reindex_gcd (fun _ _ => (1 : ℝ)) F hb D hD
    simpa using he
  have hcount := card_primeWindowSupported_dilate_mul_log_le_harmonic hH hN hR hDS
  rw [hmask] at hcount
  have hgR : Nat.gcd a b * R = max a b := by
    dsimp [R, u, v]
    rw [mul_max, Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
  have hgRreal : (Nat.gcd a b : ℝ) * (R : ℝ) = (max a b : ℕ) := by exact_mod_cast hgR
  have hg0 : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [heq]
  calc
    _ ≤ _ := hcount
    _ = _ := by rw [← hgRreal]; field_simp


private theorem sum_normSq_conv_le_collisions (A S : Finset ℕ) (c v : ℕ → ℂ) :
    (∑ k ∈ prodSupport A S, ‖dpolyComplexConv c v A S k‖ ^ 2) ≤
      ∑ a ∈ A, ∑ b ∈ A, (‖c a‖ * ‖c b‖) *
        ∑ m ∈ S, ∑ n ∈ S.filter (fun n => n * b = m * a), ‖v m‖ * ‖v n‖ := by
  classical
  let E := A ×ˢ S
  let f : ℕ × ℕ → ℝ := fun q => ‖c q.1 * v q.2‖
  have hmap : ∀ q ∈ E, q.1 * q.2 ∈ prodSupport A S := fun q hq =>
    mem_image.mpr ⟨q, hq, rfl⟩
  have hsplit : (∑ k ∈ prodSupport A S,
      (∑ q ∈ E.filter (fun q => q.1 * q.2 = k), f q) ^ 2) =
      ∑ q ∈ E, f q * ∑ z ∈ E.filter (fun z => z.1 * z.2 = q.1 * q.2), f z := by
    rw [← sum_fiberwise_of_maps_to hmap
      (fun q => f q * ∑ z ∈ E.filter (fun z => z.1 * z.2 = q.1 * q.2), f z)]
    apply sum_congr rfl
    intro k _
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro q hq
    rw [(mem_filter.mp hq).2]
  calc
    _ ≤ ∑ k ∈ prodSupport A S,
        (∑ q ∈ E.filter (fun q => q.1 * q.2 = k), f q) ^ 2 := by
      apply sum_le_sum
      intro k _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = _ := hsplit
    _ = _ := by
      dsimp [E, f]
      simp_rw [sum_filter, sum_product, norm_mul, mul_sum]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      by_cases he : n * b = m * a
      · have he' : b * n = a * m := by simpa [mul_comm] using he
        simp only [he, he', if_true]
        ring
      · have he' : ¬ b * n = a * m := by simpa [mul_comm] using he
        simp only [he, he', if_false, mul_zero]

/-- Complete complex convolution energy of a literal prime mask under every
short resonator, controlled by GCD/max energy without support-cardinality loss. -/
theorem sum_normSq_primeWindow_conv_mul_log_le
    {S A : Finset ℕ} {N H : ℕ} (hH : 1 ≤ H) (hN : H ^ 2 ≤ N)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N)
    (hA : ∀ a ∈ A, 0 < a ∧ a ≤ N / H)
    (c v : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ n ∈ primeWindowSupported S N H, ‖v n‖ ≤ B) :
    (∑ k ∈ prodSupport A (primeWindowSupported S N H),
      ‖dpolyComplexConv c v A (primeWindowSupported S N H) k‖ ^ 2) * Real.log N ≤
      (2 * B ^ 2 * (N : ℝ) * Real.log 4 * (1 + Real.log H)) *
        ∑ a ∈ A, ∑ b ∈ A, ‖c a‖ * ‖c b‖ *
          ((Nat.gcd a b : ℝ) / (max a b : ℕ)) := by
  classical
  let F := primeWindowSupported S N H
  have hN1 : 1 ≤ N := (by nlinarith : 1 ≤ H ^ 2).trans hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hpair (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
      (∑ m ∈ F, ∑ n ∈ F.filter (fun n => n * b = m * a), ‖v m‖ * ‖v n‖) * Real.log N ≤
      B ^ 2 * (2 * (N : ℝ) * Real.log 4 * (1 + Real.log H)) *
        ((Nat.gcd a b : ℝ) / (max a b : ℕ)) := by
    have hbnd : (∑ m ∈ F, ∑ n ∈ F.filter (fun n => n * b = m * a), ‖v m‖ * ‖v n‖) ≤
        B ^ 2 * ∑ m ∈ F, ((F.filter (fun n => n * b = m * a)).card : ℝ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      calc
        _ ≤ ∑ _n ∈ F.filter (fun n => n * b = m * a), B ^ 2 := by
          apply sum_le_sum
          intro n hn
          simpa only [pow_two] using mul_le_mul (hv m hm) (hv n (mem_filter.mp hn).1)
            (norm_nonneg _) hB
        _ = _ := by simp [mul_comm]
    calc
      _ ≤ (B ^ 2 * ∑ m ∈ F, ((F.filter (fun n => n * b = m * a)).card : ℝ)) * Real.log N :=
        mul_le_mul_of_nonneg_right hbnd hlog
      _ = B ^ 2 * ((∑ m ∈ F, ((F.filter (fun n => n * b = m * a)).card : ℝ)) * Real.log N) := by ring
      _ ≤ B ^ 2 * ((2 * (N : ℝ) * Real.log 4 * ∑ k ∈ Icc 1 H, 1 / (k : ℝ)) *
          ((Nat.gcd a b : ℝ) / (max a b : ℕ))) :=
        mul_le_mul_of_nonneg_left (card_primeWindow_collision_mul_log_le hH hN
          (hA a ha).1 (hA b hb).1 (hA b hb).2 hS) (sq_nonneg B)
      _ ≤ _ := by
        have hc := Sieve.sum_Icc_one_div_le_one_add_log H
        have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hc (by positivity)) (sq_nonneg B)
  calc
    _ ≤ (∑ a ∈ A, ∑ b ∈ A, (‖c a‖ * ‖c b‖) *
        ∑ m ∈ F, ∑ n ∈ F.filter (fun n => n * b = m * a), ‖v m‖ * ‖v n‖) * Real.log N :=
      mul_le_mul_of_nonneg_right (sum_normSq_conv_le_collisions A F c v) hlog
    _ = ∑ a ∈ A, ∑ b ∈ A, (‖c a‖ * ‖c b‖) *
        ((∑ m ∈ F, ∑ n ∈ F.filter (fun n => n * b = m * a), ‖v m‖ * ‖v n‖) * Real.log N) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      rw [sum_mul]
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ ∑ a ∈ A, ∑ b ∈ A, (‖c a‖ * ‖c b‖) *
        (B ^ 2 * (2 * (N : ℝ) * Real.log 4 * (1 + Real.log H)) *
          ((Nat.gcd a b : ℝ) / (max a b : ℕ))) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpair a b ha hb) (by positivity)
    _ = _ := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring

end RHTower
