import GaloisForLFunctions.RHTower.WeilLogShiftGramCanonicalDictionary

/-! # Consistent canonical Gram coordinates and their addition geometry -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

structure FiniteWeilGramCoordinates (s : Finset ℕ) where
  tests : Finset FiniteWeilGramTest
  certificate : FiniteWeilGramNormCertificate s tests
  cardinality : tests.card = (if s = ∅ then 0 else s.card + 1)
  balance : tests → ℝ
  balance_pos : ∀ w, 0 < balance w
  balance_zero : ∀ c : s → ℝ, ∑ w, balance w * finiteWeilGramForm s w.1 c = 0
  weights : ((s → ℝ) →ₗ[ℝ] ℝ) → tests → ℝ
  weights_nonneg : ∀ L w, 0 ≤ weights L w
  weights_support_card : ∀ L, (Finset.univ.filter fun w => weights L w ≠ 0).card ≤ s.card
  represents : ∀ (L : (s → ℝ) →ₗ[ℝ] ℝ) (c : s → ℝ),
    L c = ∑ w, weights L w * finiteWeilGramForm s w.1 c
  ray : ∀ (L : (s → ℝ) →ₗ[ℝ] ℝ) (b : tests → ℝ),
    ((∀ w, 0 ≤ b w) ∧ ∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) ↔
      ∃ t : ℝ, 0 ≤ t ∧ ∀ w, b w = weights L w + t * balance w

theorem nonempty_finiteWeilGramCoordinates (s : Finset ℕ) :
    Nonempty (FiniteWeilGramCoordinates s) := by
  obtain ⟨tests, hcert, hcard, a, ha, hbal, hdata⟩ := exists_finiteWeilGram_ray_dictionary s
  choose Q hQ hcardQ hrep hray using hdata
  exact ⟨{ tests := tests
           certificate := hcert
           cardinality := hcard
           balance := a
           balance_pos := ha
           balance_zero := hbal
           weights := Q
           weights_nonneg := hQ
           weights_support_card := hcardQ
           represents := hrep
           ray := hray }⟩

noncomputable def finiteWeilGramCoordinates (s : Finset ℕ) : FiniteWeilGramCoordinates s :=
  Classical.choice (nonempty_finiteWeilGramCoordinates s)

namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

theorem weights_le (L : (s → ℝ) →ₗ[ℝ] ℝ) (b : D.tests → ℝ)
    (hb : ∀ w, 0 ≤ b w)
    (hrep : ∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) :
    D.weights L ≤ b := by
  obtain ⟨t, ht, he⟩ := (D.ray L b).mp ⟨hb, hrep⟩
  intro w
  rw [he w]
  exact le_add_of_nonneg_right (mul_nonneg ht (D.balance_pos w).le)

theorem weights_zero : D.weights 0 = 0 := by
  have hle : D.weights 0 ≤ 0 := D.weights_le 0 0 (fun _ => le_rfl) (by
    intro c
    simp only [LinearMap.zero_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero])
  exact le_antisymm hle (fun w => D.weights_nonneg 0 w)

theorem weights_boundary (L : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.tests = ∅ ∨ ∃ w, D.weights L w = 0 := by
  by_cases hs : s = ∅
  · exact Or.inl (Finset.card_eq_zero.mp (by simpa only [if_pos hs] using D.cardinality))
  · right
    have hcard : D.tests.card = s.card + 1 := by
      simpa only [if_neg hs] using D.cardinality
    by_contra hn
    push Not at hn
    have h := D.weights_support_card L
    have hf : (Finset.univ.filter fun w => D.weights L w ≠ 0) = Finset.univ :=
      Finset.filter_eq_self.mpr (fun w _ => hn w)
    rw [hf, Finset.card_univ, Fintype.card_coe] at h
    omega

theorem weights_eq_of_boundary (L : (s → ℝ) →ₗ[ℝ] ℝ) (b : D.tests → ℝ)
    (hb : ∀ w, 0 ≤ b w)
    (hrep : ∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c)
    (hzero : ∃ w, b w = 0) : b = D.weights L := by
  obtain ⟨t, ht, he⟩ := (D.ray L b).mp ⟨hb, hrep⟩
  obtain ⟨w, hw⟩ := hzero
  have hp : 0 ≤ t * D.balance w := mul_nonneg ht (D.balance_pos w).le
  have hprod : t * D.balance w = 0 := by
    have h := he w
    rw [hw] at h
    linarith [D.weights_nonneg L w]
  have ht0 : t = 0 := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (D.balance_pos w))
  funext v
  simpa only [ht0, zero_mul, add_zero] using he v

theorem weights_nnreal_smul (r : NNReal) (L : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.weights ((r : ℝ) • L) = (r : ℝ) • D.weights L := by
  let b : D.tests → ℝ := fun w => (r : ℝ) * D.weights L w
  have hb (w : D.tests) : 0 ≤ b w := mul_nonneg r.property (D.weights_nonneg L w)
  have hrep : ∀ c : s → ℝ,
      ((r : ℝ) • L) c = ∑ w, b w * finiteWeilGramForm s w.1 c := by
    intro c
    rw [LinearMap.smul_apply, smul_eq_mul, D.represents L c, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    dsimp [b]
    ring
  rcases D.weights_boundary L with ht | ⟨w, hw⟩
  · funext v
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp
      (show D.tests.Nonempty from ⟨v.1, v.2⟩)) ht)
  · have he := D.weights_eq_of_boundary ((r : ℝ) • L) b hb hrep
      ⟨w, by dsimp [b]; rw [hw, mul_zero]⟩
    funext v
    simpa only [b, Pi.smul_apply, smul_eq_mul] using congrFun he.symm v

theorem weights_add_represents (L M : (s → ℝ) →ₗ[ℝ] ℝ) :
    (∀ w, 0 ≤ (D.weights L + D.weights M) w) ∧
      ∀ c : s → ℝ, (L + M) c =
        ∑ w, (D.weights L + D.weights M) w * finiteWeilGramForm s w.1 c := by
  refine ⟨fun w => add_nonneg (D.weights_nonneg L w) (D.weights_nonneg M w), ?_⟩
  intro c
  simp only [LinearMap.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    ← D.represents L c, ← D.represents M c]

theorem weights_add_le (L M : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.weights (L + M) ≤ D.weights L + D.weights M := by
  have h := D.weights_add_represents L M
  exact D.weights_le (L + M) (D.weights L + D.weights M) h.1 h.2

theorem exists_weights_add_defect (L M : (s → ℝ) →ₗ[ℝ] ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ w,
      D.weights L w + D.weights M w = D.weights (L + M) w + t * D.balance w := by
  simpa only [Pi.add_apply] using
    (D.ray (L + M) (D.weights L + D.weights M)).mp (D.weights_add_represents L M)

theorem weights_add_eq_iff (L M : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.weights (L + M) = D.weights L + D.weights M ↔
      D.tests = ∅ ∨ ∃ w, D.weights L w = 0 ∧ D.weights M w = 0 := by
  constructor
  · intro he
    rcases D.weights_boundary (L + M) with ht | ⟨w, hw⟩
    · exact Or.inl ht
    · have hv := congrFun he w
      change D.weights (L + M) w = D.weights L w + D.weights M w at hv
      rw [hw] at hv
      exact Or.inr ⟨w, by linarith [D.weights_nonneg L w, D.weights_nonneg M w],
        by linarith [D.weights_nonneg L w, D.weights_nonneg M w]⟩
  · rintro (ht | ⟨w, hL, hM⟩)
    · funext v
      exact False.elim ((Finset.nonempty_iff_ne_empty.mp
        (show D.tests.Nonempty from ⟨v.1, v.2⟩)) ht)
    · have h := D.weights_add_represents L M
      exact (D.weights_eq_of_boundary (L + M) (D.weights L + D.weights M) h.1 h.2
        ⟨w, by change D.weights L w + D.weights M w = 0; rw [hL, hM, add_zero]⟩).symm

end FiniteWeilGramCoordinates

end RHTower
