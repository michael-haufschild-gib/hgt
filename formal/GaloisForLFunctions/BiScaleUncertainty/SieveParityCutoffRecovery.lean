import GaloisForLFunctions.BiScaleUncertainty.SievePhysicalTranslationStability
import GaloisForLFunctions.BiScaleUncertainty.SieveParityAnchorEstimate

/-! Arithmetic cutoff recovery from rounded fifth and sixth products. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

/-- A positive parity anchor controls all magnitudes even when their support changes. -/
theorem parity_magnitude_bound (N : ℕ) (hN : 2 ≤ N) (c e : ℕ → ℝ)
    (δ : ℝ) (d : ℕ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hd : 2 ≤ d)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hb : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N e q| ≤ 3)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^d)
    (q : ℕ) (hq : q ∈ Icc 1 N) :
    abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have hp : δ^d ≤ δ^2 := pow_le_pow_of_le_one hδ hδ1 hd
  have h6' : ∀ v : Fin 6 → ℕ,
      |translatedMoment N c v-translatedMoment N e v| ≤ δ^2 := fun v => (h6 v).trans hp
  exact anchored_magnitude _ _ _ _ δ hc he (hb q hq) hδ
    (coordinate_sixth_error N c e (δ^2) h6' 2 h2)
    (anchored_square_error N c e (δ^2) h6' hq h2)

/-- Every odd or parity-depth mode has its sign fixed by the nonzero parity mode. -/
theorem rounded_low (N : ℕ) (hN : 2 ≤ N) (c e : ℕ → ℝ) (δ : ℝ) (d : ℕ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*δ < 1) (hd : 3 ≤ d)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hmag : ∀ q ∈ Icc 1 N,
      abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^d)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^d)
    (q : ℕ) (hq : q ∈ Icc 1 N) (hdepth : q.factorization 2 ≤ 1) :
    Threshold.source (4*δ) (selbergMultiplesCoord N c q) =
      Threshold.target (4*δ) (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q) := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have h2depth : (2 : ℕ).factorization 2 = 1 := by norm_num
  have he0 : 0 ≤ selbergMultiplesCoord N e 2 := by linarith
  by_cases hq0 : q.factorization 2 = 0
  · apply rounded_anchor_cube δ _ _ _ _ 2 d hδ hδ1 hsmall hd hc he0
      (hmag q hq) (hmag 2 h2)
    exact TopAnchor.lower_product_error N c e (δ^d) h5 hq h2 (by omega)
  · have hsame : q.factorization 2 = (2 : ℕ).factorization 2 := by omega
    apply rounded_anchor_cube δ _ _ _ _ 3 d hδ hδ1 hsmall hd hc he0
      (hmag q hq) (hmag 2 h2)
    simpa only [mul_pow] using same_depth_product_error N c e (δ^d) h6 hq h2 hsame

/-- Any retained higher mode orients every lower mode at perturbation degree five. -/
theorem rounded_lower (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ) (d : ℕ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*δ < 1) (hd : 5 ≤ d)
    (hmag : ∀ q ∈ Icc 1 N,
      abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^d)
    {q u : ℕ} (hq : q ∈ Icc 1 N) (hu : u ∈ Icc 1 N)
    (hdepth : q.factorization 2 < u.factorization 2)
    (hret : 4*δ < |selbergMultiplesCoord N c u|) :
    Threshold.source (4*δ) (selbergMultiplesCoord N c q) =
      Threshold.target (4*δ) (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q) := by
  apply rounded_orient δ _ _ _ _ 1 1 3 0 d hδ hδ1 hsmall ⟨1, rfl⟩ hd hret
      (by norm_num) (by norm_num) (hmag q hq) (hmag u hu) (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hδ)
  simpa only [pow_zero, mul_one] using TopAnchor.lower_product_error N c e (δ^d) h5 hq hu hdepth

theorem rounded_four_eight (N : ℕ) (hN : 8 ≤ N) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*δ < 1)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hmag : ∀ q ∈ Icc 1 N,
      abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^3)
    (hret : 4*δ < |selbergMultiplesCoord N c 8|) :
    Threshold.source (4*δ) (selbergMultiplesCoord N c 4) =
      Threshold.target (4*δ) (selbergMultiplesCoord N c 4) (selbergMultiplesCoord N e 4) := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have h4 : 4 ∈ Icc 1 N := by simp; omega
  have h8 : 8 ∈ Icc 1 N := by simp; omega
  apply rounded_orient δ _ _ _ _ _ _ 1 2 3 hδ hδ1 hsmall ⟨0, rfl⟩
    (by decide) hret hc (by linarith) (hmag 4 h4) (hmag 8 h8) (hmag 2 h2)
  simpa only [pow_one] using four_eight_error N hN c e (δ^3) h5

theorem rounded_four_twelve (N : ℕ) (hN : 12 ≤ N) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*δ < 1)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hmag : ∀ q ∈ Icc 1 N,
      abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^5) :
    Threshold.source (4*δ) (selbergMultiplesCoord N c 12)*
        Threshold.source (4*δ) (selbergMultiplesCoord N c 4) =
      Threshold.target (4*δ) (selbergMultiplesCoord N c 12) (selbergMultiplesCoord N e 12)*
        Threshold.target (4*δ) (selbergMultiplesCoord N c 4) (selbergMultiplesCoord N e 4) := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have h4 : 4 ∈ Icc 1 N := by simp; omega
  have h12 : 12 ∈ Icc 1 N := by simp; omega
  exact rounded_pair δ _ _ _ _ _ _ 5 hδ hδ1 hsmall (by decide) hc (by linarith)
    (hmag 12 h12) (hmag 4 h4) (hmag 2 h2) (four_twelve_error N hN c e (δ^5) h6)

/-- Below twenty, every mode above the parity depth is a multiple of four from this list. -/
theorem high_orders_below_twenty {q : ℕ} (hq : 0 < q) (h20 : q < 20)
    (hdepth : 1 < q.factorization 2) : q = 4 ∨ q = 8 ∨ q = 12 ∨ q = 16 := by
  obtain ⟨p, hp⟩ := ValuationPhase.order_odd_decomposition hq
  have hpow : 2^(q.factorization 2) = 4*2^(q.factorization 2-2) := by
    calc
      2^(q.factorization 2) = 2^(2+(q.factorization 2-2)) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num
  have he : q = 4*(2^(q.factorization 2-2)*(2*p+1)) := by
    calc
      q = 2^(q.factorization 2)*(2*p+1) := hp
      _ = _ := by rw [hpow]; ring
  omega

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
open ValuationPhase
set_option autoImplicit false

/-- Existing common-sign recovery and the canonical companion realize the selected phase relations. -/
theorem coordinate_recovery_of_phase_relations (N : ℕ) (c e : ℕ → ℝ)
    (hV : 0 < activeDepth N c)
    (habs : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N e q| = |selbergMultiplesCoord N c q|)
    (hlower : ∀ q ∈ Icc 1 N, q.factorization 2 < activeDepth N c →
      selbergMultiplesCoord N e q = selbergMultiplesCoord N c q)
    (htop : ∀ q ∈ Icc 1 N, q.factorization 2 = activeDepth N c →
      ∀ u ∈ Icc 1 N, u.factorization 2 = activeDepth N c →
        selbergMultiplesCoord N c q*selbergMultiplesCoord N c u =
          selbergMultiplesCoord N e q*selbergMultiplesCoord N e u) :
    (∀ q ∈ Icc 1 N, selbergMultiplesCoord N e q = selbergMultiplesCoord N c q) ∨
      (∀ q ∈ Icc 1 N, selbergMultiplesCoord N e q = selbergMultiplesCoord N (companion N c) q) := by
  have hzero (q : ℕ) (hq : q ∈ Icc 1 N) (hgt : activeDepth N c < q.factorization 2) :
      selbergMultiplesCoord N c q = 0 ∧ selbergMultiplesCoord N e q = 0 := by
    have hc : selbergMultiplesCoord N c q = 0 := by
      by_contra hc
      have hh := depth_le_activeDepth N q c hq hc
      omega
    refine ⟨hc, abs_eq_zero.mp ?_⟩
    rw [habs q hq, hc, abs_zero]
  have hp := (pair_products_eq_iff_common_sign
    {q : ℕ | q ∈ Icc 1 N ∧ q.factorization 2 = activeDepth N c}
    (selbergMultiplesCoord N c) (selbergMultiplesCoord N e)).mp
      (fun q hq u hu => htop q hq.1 hq.2 u hu.1 hu.2)
  rcases hp with hp | hp
  · left
    intro q hq
    by_cases hlt : q.factorization 2 < activeDepth N c
    · exact hlower q hq hlt
    · by_cases heq : q.factorization 2 = activeDepth N c
      · exact (hp q ⟨hq, heq⟩).symm
      · obtain ⟨hc, he⟩ := hzero q hq (by omega)
        rw [hc, he]
  · right
    intro q hq
    rw [coordinate_companion N c q hq]
    by_cases heq : q.factorization 2 = activeDepth N c
    · rw [if_pos ⟨hV, heq⟩]
      have hh := hp q ⟨hq, heq⟩
      linarith
    · rw [if_neg (by tauto)]
      by_cases hlt : q.factorization 2 < activeDepth N c
      · exact hlower q hq hlt
      · obtain ⟨hc, he⟩ := hzero q hq (by omega)
        rw [hc, he]

/-- Coordinate rounding errors transfer to one actual natural translation. -/
theorem physical_error_of_coordinate_recovery (N : ℕ) (c e C E : ℕ → ℝ) (τ : ℝ)
    (hc : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N c q-selbergMultiplesCoord N C q| ≤ τ)
    (he : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N e q-selbergMultiplesCoord N E q| ≤ 2*τ)
    (hr : (∀ q ∈ Icc 1 N, selbergMultiplesCoord N E q = selbergMultiplesCoord N C q) ∨
      (∀ q ∈ Icc 1 N, selbergMultiplesCoord N E q = selbergMultiplesCoord N (companion N C) q)) :
    ∃ h : ℕ, ∀ n : ℕ, |sieveSeq N e n-sieveSeq N c (n+h)| ≤
      3*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*τ := by
  have hseq (A B : ℕ → ℝ)
      (hab : ∀ q ∈ Icc 1 N, selbergMultiplesCoord N A q = selbergMultiplesCoord N B q)
      (n : ℕ) : sieveSeq N A n = sieveSeq N B n := by
    have hh := sieveSeq_error_le_totient_sum N A B 0
      (fun q hq => by rw [hab q hq]; simp) n
    have hz : |sieveSeq N A n-sieveSeq N B n| = 0 :=
      le_antisymm (by simpa using hh) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  have hclose (h : ℕ) (hs : ∀ n, sieveSeq N E n = sieveSeq N C (n+h)) (n : ℕ) :
      |sieveSeq N e n-sieveSeq N c (n+h)| ≤
        3*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*τ := by
    have ht := sieveSeq_error_le_totient_sum N e E (2*τ) he n
    have hc' := sieveSeq_error_le_totient_sum N c C τ hc (n+h)
    have htri := abs_sub_le (sieveSeq N e n) (sieveSeq N E n) (sieveSeq N c (n+h))
    rw [hs n, abs_sub_comm (sieveSeq N C (n+h))] at htri
    rw [hs n] at ht
    nlinarith
  rcases hr with hr | hr
  · refine ⟨0, hclose 0 ?_⟩
    intro n
    simpa using hseq E C hr n
  · refine ⟨canonicalShift N C, hclose (canonicalShift N C) ?_⟩
    intro n
    rw [hseq E (companion N C) hr n, sieveSeq_companion]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
open ValuationPhase
set_option autoImplicit false

private theorem depth_four : (4 : ℕ).factorization 2 = 2 := by
  change (2^2).factorization 2 = 2
  exact Nat.factorization_pow_self Nat.prime_two

private theorem depth_eight : (8 : ℕ).factorization 2 = 3 := by
  change (2^3).factorization 2 = 3
  exact Nat.factorization_pow_self Nat.prime_two

private theorem depth_sixteen : (16 : ℕ).factorization 2 = 4 := by
  change (2^4).factorization 2 = 4
  exact Nat.factorization_pow_self Nat.prime_two

private theorem depth_twelve : (12 : ℕ).factorization 2 = 2 := by
  change (4*3).factorization 2 = 2
  rw [Nat.factorization_mul (by decide : (4 : ℕ) ≠ 0) (by decide : (3 : ℕ) ≠ 0)]
  simp only [Finsupp.add_apply, depth_four,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 3), Nat.add_zero]

/-- Below twenty the pair 4,12 is the only repeated block above the parity depth. -/
theorem equal_depth_products_below_twenty (N : ℕ) (hN : N < 20) (a b : ℕ → ℝ)
    (hsq : ∀ q ∈ Icc 1 N, (a q)^2 = (b q)^2)
    (hlow : ∀ q ∈ Icc 1 N, q.factorization 2 ≤ 1 → a q = b q)
    (h412 : 12 ≤ N → a 12*a 4 = b 12*b 4)
    {q u : ℕ} (hq : q ∈ Icc 1 N) (hu : u ∈ Icc 1 N)
    (hdu : q.factorization 2 = u.factorization 2) : a q*a u = b q*b u := by
  by_cases heq : q = u
  · subst u
    simpa only [pow_two] using hsq q hq
  · by_cases hlowq : q.factorization 2 ≤ 1
    · rw [hlow q hq hlowq, hlow u hu (by omega)]
    · have hq0 : 0 < q := (mem_Icc.mp hq).1
      have hu0 : 0 < u := (mem_Icc.mp hu).1
      have hqN : q ≤ N := (mem_Icc.mp hq).2
      have huN : u ≤ N := (mem_Icc.mp hu).2
      have hqcases := high_orders_below_twenty hq0 (by omega) (by omega : 1 < q.factorization 2)
      have hucases := high_orders_below_twenty hu0 (by omega) (by omega : 1 < u.factorization 2)
      rcases hqcases with rfl | rfl | rfl | rfl <;>
        rcases hucases with rfl | rfl | rfl | rfl <;>
          norm_num [depth_four, depth_eight, depth_twelve, depth_sixteen] at hdu
      all_goals try exact False.elim (heq rfl)
      all_goals simpa only [mul_comm] using h412 (by omega)

/-- The sole higher-depth orientation needed below twelve is the 4-to-8 relation. -/
theorem phase_recovery_below_twelve (N : ℕ) (hN : N < 12) (c e : ℕ → ℝ)
    (hV : 0 < activeDepth N c)
    (habs : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N e q| = |selbergMultiplesCoord N c q|)
    (hlow : ∀ q ∈ Icc 1 N, q.factorization 2 ≤ 1 →
      selbergMultiplesCoord N c q = selbergMultiplesCoord N e q)
    (h48 : 8 ≤ N → selbergMultiplesCoord N c 8 ≠ 0 →
      selbergMultiplesCoord N c 4 = selbergMultiplesCoord N e 4) :
    (∀ q ∈ Icc 1 N, selbergMultiplesCoord N e q = selbergMultiplesCoord N c q) ∨
      (∀ q ∈ Icc 1 N, selbergMultiplesCoord N e q = selbergMultiplesCoord N (companion N c) q) := by
  have hsq (q : ℕ) (hq : q ∈ Icc 1 N) :
      (selbergMultiplesCoord N c q)^2 = (selbergMultiplesCoord N e q)^2 := by
    have hh := congrArg (fun x : ℝ => x^2) (habs q hq)
    simpa only [sq_abs] using hh.symm
  apply coordinate_recovery_of_phase_relations N c e hV habs
  · intro q hq hlt
    by_cases hlowq : q.factorization 2 ≤ 1
    · exact (hlow q hq hlowq).symm
    · obtain ⟨u, hu, hun, huV⟩ := exists_at_activeDepth N c hV
      have hq0 : 0 < q := (mem_Icc.mp hq).1
      have hu0 : 0 < u := (mem_Icc.mp hu).1
      have hqN : q ≤ N := (mem_Icc.mp hq).2
      have huN : u ≤ N := (mem_Icc.mp hu).2
      have hqcases := high_orders_below_twenty hq0 (by omega) (by omega : 1 < q.factorization 2)
      have hucases := high_orders_below_twenty hu0 (by omega) (by omega : 1 < u.factorization 2)
      have hdepth : q.factorization 2 < u.factorization 2 := by omega
      rcases hqcases with rfl | rfl | rfl | rfl <;>
        rcases hucases with rfl | rfl | rfl | rfl <;>
          norm_num [depth_four, depth_eight, depth_twelve, depth_sixteen] at hdepth
      all_goals first | omega | exact (h48 (by omega) hun).symm
  · intro q hq hqV u hu huV
    exact equal_depth_products_below_twenty N (by omega) _ _ hsq hlow
      (fun hh => by omega) hq hu (by omega)

/-- A retained parity mode gives positive active depth after thresholding. -/
theorem threshold_depth_pos (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hsmall : 4*δ < 1) (hc : 1 ≤ selbergMultiplesCoord N c 2) :
    0 < activeDepth N (thresholdSourceWeights N c (4*δ)) := by
  have hτ : 0 ≤ 4*δ := by linarith
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have hne : selbergMultiplesCoord N (thresholdSourceWeights N c (4*δ)) 2 ≠ 0 := by
    rw [coordinate_thresholdSource N c (4*δ) hτ]
    have hc0 : 0 ≤ selbergMultiplesCoord N c 2 := by linarith
    rw [Threshold.source, if_pos (by rw [abs_of_nonneg hc0]; linarith)]
    linarith
  have hh := depth_le_activeDepth N 2 (thresholdSourceWeights N c (4*δ)) h2 hne
  norm_num at hh
  omega

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
open ValuationPhase
set_option autoImplicit false

theorem rounded_recovery_three (N : ℕ) (hN : 2 ≤ N) (hN12 : N < 12)
    (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : 4*δ < 1)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hmag : ∀ q ∈ Icc 1 N,
      abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^3)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^3) :
    (∀ q ∈ Icc 1 N, selbergMultiplesCoord N (thresholdTargetWeights N c e (4*δ)) q =
      selbergMultiplesCoord N (thresholdSourceWeights N c (4*δ)) q) ∨
    (∀ q ∈ Icc 1 N, selbergMultiplesCoord N (thresholdTargetWeights N c e (4*δ)) q =
      selbergMultiplesCoord N (companion N (thresholdSourceWeights N c (4*δ))) q) := by
  have hτ : 0 ≤ 4*δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  apply phase_recovery_below_twelve N hN12 _ _ (threshold_depth_pos N hN c δ hδ hsmall hc)
  · intro q _
    rw [coordinate_thresholdTarget N c e (4*δ) hτ, coordinate_thresholdSource N c (4*δ) hτ]
    exact rounded_abs _ _ _
  · intro q hq hdepth
    rw [coordinate_thresholdTarget N c e (4*δ) hτ, coordinate_thresholdSource N c (4*δ) hτ]
    exact rounded_low N hN c e δ 3 hδ hδ1 hsmall (by decide) hc he hmag h5 h6 q hq hdepth
  · intro hN8 hne
    rw [coordinate_thresholdSource N c (4*δ) hτ] at hne
    have hret : 4*δ < |selbergMultiplesCoord N c 8| := by
      by_contra hn
      exact hne (by simp [Threshold.source, hn])
    rw [coordinate_thresholdTarget N c e (4*δ) hτ, coordinate_thresholdSource N c (4*δ) hτ]
    exact rounded_four_eight N hN8 c e δ hδ hδ1 hsmall hc he hmag h5 hret

theorem rounded_recovery_five (N : ℕ) (hN : 2 ≤ N) (hN20 : N < 20)
    (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : 4*δ < 1)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hmag : ∀ q ∈ Icc 1 N,
      abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^5)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^5) :
    (∀ q ∈ Icc 1 N, selbergMultiplesCoord N (thresholdTargetWeights N c e (4*δ)) q =
      selbergMultiplesCoord N (thresholdSourceWeights N c (4*δ)) q) ∨
    (∀ q ∈ Icc 1 N, selbergMultiplesCoord N (thresholdTargetWeights N c e (4*δ)) q =
      selbergMultiplesCoord N (companion N (thresholdSourceWeights N c (4*δ))) q) := by
  let C := thresholdSourceWeights N c (4*δ)
  let E := thresholdTargetWeights N c e (4*δ)
  have hτ : 0 ≤ 4*δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hC (q : ℕ) : selbergMultiplesCoord N C q =
      Threshold.source (4*δ) (selbergMultiplesCoord N c q) :=
    coordinate_thresholdSource N c (4*δ) hτ q
  have hE (q : ℕ) : selbergMultiplesCoord N E q =
      Threshold.target (4*δ) (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q) :=
    coordinate_thresholdTarget N c e (4*δ) hτ q
  have hV : 0 < activeDepth N C := threshold_depth_pos N hN c δ hδ hsmall hc
  have habs (q : ℕ) : |selbergMultiplesCoord N E q| = |selbergMultiplesCoord N C q| := by
    rw [hC, hE]
    exact rounded_abs _ _ _
  have hsq (q : ℕ) (_hq : q ∈ Icc 1 N) :
      (selbergMultiplesCoord N C q)^2 = (selbergMultiplesCoord N E q)^2 := by
    have hh := congrArg (fun x : ℝ => x^2) (habs q)
    simpa only [sq_abs] using hh.symm
  have hlow (q : ℕ) (hq : q ∈ Icc 1 N) (hdepth : q.factorization 2 ≤ 1) :
      selbergMultiplesCoord N C q = selbergMultiplesCoord N E q := by
    rw [hC, hE]
    exact rounded_low N hN c e δ 5 hδ hδ1 hsmall (by decide) hc he hmag h5 h6 q hq hdepth
  apply coordinate_recovery_of_phase_relations N C E hV (fun q _ => habs q)
  · intro q hq hdepth
    obtain ⟨u, hu, hun, huV⟩ := exists_at_activeDepth N C hV
    have hret : 4*δ < |selbergMultiplesCoord N c u| := by
      rw [hC] at hun
      by_contra hn
      exact hun (by simp [Threshold.source, hn])
    rw [hC, hE]
    exact (rounded_lower N c e δ 5 hδ hδ1 hsmall (by decide) hmag h5 hq hu (by omega) hret).symm
  · intro q hq hqV u hu huV
    apply equal_depth_products_below_twenty N hN20 _ _ hsq hlow ?_ hq hu (by omega)
    intro hN12
    rw [hC, hC, hE, hE]
    exact rounded_four_twelve N hN12 c e δ hδ hδ1 hsmall hc he hmag h6

/-- The chosen rounding threshold gives a uniform physical error of twelve times the totient budget. -/
theorem physical_error_of_rounding (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmag : ∀ q ∈ Icc 1 N,
      abs (|selbergMultiplesCoord N c q|-|selbergMultiplesCoord N e q|) ≤ 4*δ)
    (hr : (∀ q ∈ Icc 1 N, selbergMultiplesCoord N (thresholdTargetWeights N c e (4*δ)) q =
      selbergMultiplesCoord N (thresholdSourceWeights N c (4*δ)) q) ∨
    (∀ q ∈ Icc 1 N, selbergMultiplesCoord N (thresholdTargetWeights N c e (4*δ)) q =
      selbergMultiplesCoord N (companion N (thresholdSourceWeights N c (4*δ))) q)) :
    ∃ h : ℕ, ∀ n : ℕ, |sieveSeq N e n-sieveSeq N c (n+h)| ≤
      12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*δ := by
  have hτ : 0 ≤ 4*δ := by linarith
  have hc (q : ℕ) (_hq : q ∈ Icc 1 N) :
      |selbergMultiplesCoord N c q-selbergMultiplesCoord N (thresholdSourceWeights N c (4*δ)) q| ≤ 4*δ := by
    rw [coordinate_thresholdSource N c (4*δ) hτ]
    exact Threshold.source_error _ _ hτ
  have he (q : ℕ) (hq : q ∈ Icc 1 N) :
      |selbergMultiplesCoord N e q-selbergMultiplesCoord N (thresholdTargetWeights N c e (4*δ)) q| ≤ 2*(4*δ) := by
    rw [coordinate_thresholdTarget N c e (4*δ) hτ]
    exact Threshold.target_error _ _ _ hτ (hmag q hq)
  obtain ⟨h, hh⟩ := physical_error_of_coordinate_recovery N c e _ _ (4*δ) hc he hr
  refine ⟨h, fun n => ?_⟩
  calc
    _ ≤ 3*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*(4*δ) := hh n
    _ = _ := by ring

theorem exists_translate_error_small_three (N : ℕ) (hN : 2 ≤ N) (hN12 : N < 12)
    (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : 4*δ < 1)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hb : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N e q| ≤ 3)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^3)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^3) :
    ∃ h : ℕ, ∀ n : ℕ, |sieveSeq N e n-sieveSeq N c (n+h)| ≤
      12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*δ := by
  have hmag := parity_magnitude_bound N hN c e δ 3 hδ (by linarith) (by decide) hc he hb h6
  exact physical_error_of_rounding N c e δ hδ hmag
    (rounded_recovery_three N hN hN12 c e δ hδ hsmall hc he hmag h5 h6)

theorem exists_translate_error_small_five (N : ℕ) (hN : 2 ≤ N) (hN20 : N < 20)
    (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : 4*δ < 1)
    (hc : 1 ≤ selbergMultiplesCoord N c 2) (he : 1 ≤ selbergMultiplesCoord N e 2)
    (hb : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N e q| ≤ 3)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^5)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^5) :
    ∃ h : ℕ, ∀ n : ℕ, |sieveSeq N e n-sieveSeq N c (n+h)| ≤
      12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*δ := by
  have hmag := parity_magnitude_bound N hN c e δ 5 hδ (by linarith) (by decide) hc he hb h6
  exact physical_error_of_rounding N c e δ hδ hmag
    (rounded_recovery_five N hN hN20 c e δ hδ hsmall hc he hmag h5 h6)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
