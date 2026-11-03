import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# Empty annuli with a lower bound for the distance product

Repeatedly retaining the smaller of two disjoint balls charges each contraction only to
the surviving points. This bounds the product of killing distances without replacing
all distances by the smallest one.
-/

open scoped BigOperators
noncomputable section
namespace SquareRootThreshold

/-- A root inside the selected cluster contributes one; other distances are clipped at one. -/
def clusterDistanceFactor (c : ℂ) (t : ℝ) (q : ℂ) : ℝ :=
  if t / 2 ≤ ‖q - c‖ then min 1 ‖q - c‖ else 1

theorem clusterDistanceFactor_nonneg (c q : ℂ) (t : ℝ) :
    0 ≤ clusterDistanceFactor c t q := by
  unfold clusterDistanceFactor
  split_ifs <;> positivity

theorem clusterDistanceFactor_le_one (c q : ℂ) (t : ℝ) :
    clusterDistanceFactor c t q ≤ 1 := by
  unfold clusterDistanceFactor
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

private theorem power_le_product {P : Finset ℂ} {n : ℕ} {a : ℝ} {f : ℂ → ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hn : P.card ≤ n) (hf : ∀ q ∈ P, a ≤ f q) :
    a ^ n ≤ ∏ q ∈ P, f q := by
  calc a ^ n ≤ a ^ P.card := pow_le_pow_of_le_one ha ha1 hn
    _ = ∏ _q ∈ P, a := by simp
    _ ≤ ∏ q ∈ P, f q := Finset.prod_le_prod (fun _ _ => ha) hf

/-- A finite cluster has an empty annulus whose exterior distance product loses only
an exponential in the number of points, with base `r/(16λ)²`. -/
theorem exists_empty_annulus_with_product {lam : ℝ} (hlam : 1 ≤ lam) :
    ∀ (n : ℕ) (P : Finset ℂ) (p : ℂ) (r : ℝ), P.card ≤ n → p ∈ P → 0 < r → r ≤ 1 →
      ∃ c ∈ P, ∃ t : ℝ, 0 < t ∧ t ≤ r ∧ ‖c - p‖ ≤ r / 2 ∧
        (∀ q ∈ P, ‖q - c‖ < t / 2 → ‖q - c‖ < t / (2 * lam)) ∧
        (r * (1 / (16 * lam)) ^ 2) ^ (2 * n) ≤ ∏ q ∈ P, clusterDistanceFactor c t q := by
  classical
  have hlam0 : 0 < lam := by linarith
  set b := 1 / (16 * lam) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb16 : b ≤ 1 / 16 := by
    rw [hb, div_le_iff₀ (by positivity)]
    linarith
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P p r hcard hp hr hr1
    have hn0 : 0 < n := (Finset.card_pos.mpr ⟨p, hp⟩).trans_le hcard
    have hbase0 : 0 ≤ r * b ^ 2 := by positivity
    have hbase1 : r * b ^ 2 ≤ 1 := by nlinarith
    by_cases hA : ∀ q ∈ P, ‖q - p‖ < r / 4 → ‖q - p‖ < r / (4 * lam)
    · refine ⟨p, hp, r / 2, by positivity, by linarith, by simp; positivity, ?_, ?_⟩
      · intro q hq hqt
        have h := hA q hq (by linarith)
        convert h using 1
        ring_nf
      · have hprod : (r / 4) ^ n ≤ ∏ q ∈ P, clusterDistanceFactor p (r / 2) q := by
          apply power_le_product (by positivity) (by linarith) hcard
          intro q _
          unfold clusterDistanceFactor
          split_ifs with hq
          · exact le_min (by linarith) (by linarith)
          · linarith
        calc (r * b ^ 2) ^ (2 * n) ≤ (r * b ^ 2) ^ n :=
              pow_le_pow_of_le_one hbase0 hbase1 (by omega)
          _ ≤ (r / 4) ^ n := pow_le_pow_left₀ hbase0 (by nlinarith) n
          _ ≤ _ := hprod
    push Not at hA
    obtain ⟨q, hq, hq1, hq2⟩ := hA
    set d := ‖q - p‖ with hd
    have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hq2
    set Fp := P.filter fun x => ‖x - p‖ < d / 2 with hFp
    set Fq := P.filter fun x => ‖x - q‖ < d / 2 with hFq
    have hdisj : Disjoint Fp Fq := by
      rw [Finset.disjoint_left]
      intro x hxp hxq
      have h1 := (Finset.mem_filter.mp hxp).2
      have h2 := (Finset.mem_filter.mp hxq).2
      have htri : d ≤ ‖x - p‖ + ‖x - q‖ := by
        calc d = ‖(x - p) - (x - q)‖ := by rw [hd]; congr 1; ring
          _ ≤ ‖x - p‖ + ‖x - q‖ := norm_sub_le _ _
      linarith
    have hsum : Fp.card + Fq.card ≤ n := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans hcard
    have hrb : r * b ≤ d / 4 := by
      have he : r * b = (r / (4 * lam)) / 4 := by rw [hb]; field_simp; ring
      rw [he]; linarith
    have key : ∀ c₀ ∈ P, ‖c₀ - p‖ ≤ d →
        2 * (P.filter fun x => ‖x - c₀‖ < d / 2).card ≤ n →
        ∃ c ∈ P, ∃ t : ℝ, 0 < t ∧ t ≤ r ∧ ‖c - p‖ ≤ r / 2 ∧
          (∀ x ∈ P, ‖x - c‖ < t / 2 → ‖x - c‖ < t / (2 * lam)) ∧
          (r * b ^ 2) ^ (2 * n) ≤ ∏ x ∈ P, clusterDistanceFactor c t x := by
      intro c₀ hc₀ hc₀p hhalf
      set Q := P.filter fun x => ‖x - c₀‖ < d / 2 with hQ
      have hQP : Q ⊆ P := Finset.filter_subset _ _
      have hm : Q.card < n := by omega
      have hc₀Q : c₀ ∈ Q := Finset.mem_filter.mpr ⟨hc₀, by simp; positivity⟩
      obtain ⟨c, hcQ, t, ht0, htd, hcc, hgap, hprodQ⟩ :=
        ih Q.card hm Q c₀ (d / 4) le_rfl hc₀Q (by positivity) (by linarith)
      have hout : ∀ x ∈ P \ Q, d / 4 ≤ ‖x - c‖ := by
        intro x hx
        have hxQ := (Finset.mem_sdiff.mp hx).2
        have hxP := (Finset.mem_sdiff.mp hx).1
        have hx : d / 2 ≤ ‖x - c₀‖ := by
          by_contra! hlt
          exact hxQ (Finset.mem_filter.mpr ⟨hxP, hlt⟩)
        have htri := norm_sub_le_norm_sub_add_norm_sub x c c₀
        linarith
      refine ⟨c, hQP hcQ, t, ht0, by linarith, ?_, ?_, ?_⟩
      · have htri := norm_sub_le_norm_sub_add_norm_sub c c₀ p
        linarith
      · intro x hx hxt
        apply hgap x
        · by_contra hxQ
          have := hout x (Finset.mem_sdiff.mpr ⟨hx, hxQ⟩)
          linarith
        · exact hxt
      · have hd41 : d / 4 ≤ 1 := by linarith
        have hsmall0 : 0 ≤ d / 4 * b ^ 2 := by positivity
        have hsmall1 : d / 4 * b ^ 2 ≤ 1 := by nlinarith
        have hin : (d / 4 * b ^ 2) ^ n ≤ ∏ x ∈ Q, clusterDistanceFactor c t x :=
          (pow_le_pow_of_le_one hsmall0 hsmall1 hhalf).trans hprodQ
        have houtprod : (d / 4) ^ n ≤ ∏ x ∈ P \ Q, clusterDistanceFactor c t x := by
          apply power_le_product (by positivity) hd41
            ((Finset.card_le_card Finset.sdiff_subset).trans hcard)
          intro x hx
          have hxlow := hout x hx
          unfold clusterDistanceFactor
          split_ifs
          · exact le_min hd41 hxlow
          · exact hd41
        calc (r * b ^ 2) ^ (2 * n) ≤ (d / 4 * b) ^ (2 * n) :=
              pow_le_pow_left₀ hbase0 (by nlinarith) _
          _ = (d / 4) ^ n * (d / 4 * b ^ 2) ^ n := by ring
          _ ≤ (∏ x ∈ P \ Q, clusterDistanceFactor c t x) *
              ∏ x ∈ Q, clusterDistanceFactor c t x :=
            mul_le_mul houtprod hin (by positivity)
              (Finset.prod_nonneg fun x _ => clusterDistanceFactor_nonneg c x t)
          _ = ∏ x ∈ P, clusterDistanceFactor c t x := Finset.prod_sdiff hQP
    rcases le_or_gt (2 * Fp.card) n with h | h
    · exact key p hp (by simp; positivity) h
    · apply key q hq le_rfl
      change 2 * Fq.card ≤ n
      omega

end SquareRootThreshold
