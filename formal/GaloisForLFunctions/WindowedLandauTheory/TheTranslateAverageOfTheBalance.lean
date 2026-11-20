import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.ThickTranslates
import GaloisForLFunctions.WindowedLandauTheory.ClassCesaroIncrements

/-!
# The translate average of the balance

For weights `w` on the split classes and a translate `u₀`, let `w̃` agree with `w` except that it
equals `b` on the classes thick at `u₀`. Averaged over all translates, the character side of the
balance identity with weights `w̃` splits into

* the *thick part* `(|T₂|/2|H|) · b · S(A/b)` with the sign signal
  `S(y) = Σ_{ψ sign} conj ψ((1,0),0) · G_ψ(y)` (`average_balanceTotal_thickened`), and
* a *thin part* of size at most `2|Φ|(x+1)bθ` once `‖G_ψ(y)‖ ≤ θy` on the thin scales
  (`norm_thinPart_le`).

Replacing `w` by `w̃` costs at most `2|Φ| · 7(x+1)(η+1)` when `b ≤ w ≤ b + η + 1` on the thick
classes (`abs_re_balanceTotal_sub_le`), and the sign signal stays within
`3 x^{1/2+ε} + signCost` of `G_ζ(x)` near `x` when the nonzero sign characters have square-root values
at `x` (`re_signSignal_ge`).
-/

open Finset

namespace WindowedLandauTheory

noncomputable section

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem card_splitSet_eq : ((splitSet H).card : ℂ) = 2 * (Fintype.card H : ℂ) := by
  have h := card_eq_two_mul_card_splitSet (H := H)
  have h4 : (Fintype.card (SignPair × H) : ℂ) = 4 * (Fintype.card H : ℂ) := by
    rw [Fintype.card_prod]
    push_cast
    rfl
  rw [h4] at h
  linear_combination -h / 2

omit [DecidableEq H] in
theorem card_addChar_eq : (Fintype.card (AddChar (SignPair × H) ℂ) : ℝ) =
    2 * ((splitSet H).card : ℝ) := by
  rw [AddChar.card_eq]
  have h := card_eq_two_mul_card_splitSet (H := H)
  exact_mod_cast h

open Classical in
/-- The sign signal `S(y) = Σ_{ψ sign} conj ψ((1,0),0) · G_ψ(y)`. -/
def signSignal (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ) (y : ℝ) : ℂ :=
  ∑ ψ ∈ (univ : Finset (AddChar (SignPair × H) ℂ)).filter IsSignCharacter,
    starRingEnd ℂ (ψ ramifiedClass) * classCesaro D ℓ ψ y

/-- The cost of moving the sign signal from `x` to a point within distance one. -/
def signCost (x CL : ℝ) : ℝ :=
  3 * (Real.log (x + 1) + (Real.log 4 + 4) + CL * Real.log x) + (Real.log 4 + 7)

omit [DecidableEq H] in
open Classical in
theorem card_nonzero_signCharacters_le :
    (((univ : Finset (AddChar (SignPair × H) ℂ)).filter IsSignCharacter).erase 0).card ≤ 3 := by
  have h := card_signCharacters_le (H := H)
  rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, isSignCharacter_zero (H := H)⟩)]
  omega

omit [DecidableEq H] in
open Classical in
/-- **The sign signal near `x`.** -/
theorem re_signSignal_ge (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    {x ε CL y : ℝ} (hx : 3 ≤ x) (hCL : 0 ≤ CL) (hy : |y - x| ≤ 1)
    (hVal : ∀ ψ : AddChar (SignPair × H) ℂ, IsSignCharacter ψ → ψ ≠ 0 →
      ‖classCesaro D ℓ ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ℓ ψ‖ ≤ CL * Real.log x) :
    zetaCesaroFunctional x - 3 * x ^ ((1 : ℝ) / 2 + ε) - signCost x CL ≤
      (signSignal D ℓ y).re := by
  have hx1 : 1 ≤ x := by linarith
  have hy1 : 1 ≤ y := by
    have := (abs_le.1 hy).1
    linarith
  set S := (univ : Finset (AddChar (SignPair × H) ℂ)).filter IsSignCharacter with hS
  have h0S : (0 : AddChar (SignPair × H) ℂ) ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, isSignCharacter_zero⟩
  have hsplit : signSignal D ℓ y = (zetaCesaroFunctional y : ℂ) +
      ∑ ψ ∈ S.erase 0, starRingEnd ℂ (ψ ramifiedClass) * classCesaro D ℓ ψ y := by
    rw [signSignal, ← Finset.add_sum_erase S _ h0S]
    congr 1
    rw [AddChar.zero_apply, map_one, one_mul, classCesaro, if_pos rfl]
  set B := x ^ ((1 : ℝ) / 2 + ε) + Real.log (x + 1) + (Real.log 4 + 4) + CL * Real.log x with hB
  have hB0 : 0 ≤ B := by
    have h1 : 0 < x ^ ((1 : ℝ) / 2 + ε) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    have h3 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ CL * Real.log x := mul_nonneg hCL (Real.log_nonneg hx1)
    linarith
  have hterm : ∀ ψ ∈ S.erase 0,
      ‖starRingEnd ℂ (ψ ramifiedClass) * classCesaro D ℓ ψ y‖ ≤ B := by
    intro ψ hψ
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hψ
    have hsg : IsSignCharacter ψ := (Finset.mem_filter.1 hmem).2
    obtain ⟨hv, hl⟩ := hVal ψ hsg hne
    rw [norm_mul, Complex.norm_conj, AddChar.norm_apply, one_mul]
    have hinc := norm_classCesaro_sub_le D ℓ hne hx1 hy1 hy
    calc ‖classCesaro D ℓ ψ y‖ ≤ ‖classCesaro D ℓ ψ x‖ +
          ‖classCesaro D ℓ ψ y - classCesaro D ℓ ψ x‖ := by
          simpa using norm_add_le (classCesaro D ℓ ψ x)
            (classCesaro D ℓ ψ y - classCesaro D ℓ ψ x)
      _ ≤ x ^ ((1 : ℝ) / 2 + ε) + (Real.log (x + 1) + (Real.log 4 + 4) + ‖ℓ ψ‖) :=
          add_le_add hv hinc
      _ ≤ B := by
          rw [hB]
          linarith
  have hsum : ‖∑ ψ ∈ S.erase 0, starRingEnd ℂ (ψ ramifiedClass) * classCesaro D ℓ ψ y‖ ≤
      3 * B := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ B hterm).trans ?_)
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_nonzero_signCharacters_le) hB0
  have hre := (abs_le.1 ((Complex.abs_re_le_norm _).trans hsum)).1
  have hz := (abs_le.1 (abs_zetaCesaroFunctional_sub_le hx1 hy1 hy)).1
  rw [hsplit, Complex.add_re, Complex.ofReal_re]
  unfold signCost
  linarith

/-- The weights set to `b` on the classes thick at `u₀`. -/
def thickened (T₂ : Finset H) (b : ℝ) (u₀ : H) (w : SignPair × H → ℝ) (ρ : SignPair × H) : ℝ :=
  if IsThick T₂ u₀ ρ then b else w ρ

omit [DecidableEq H] in
/-- An average of character sums over non-split classes is at most `2|Φ|K` in norm. -/
theorem norm_classSum_le (S' : Finset (SignPair × H)) (hS' : S' ⊆ nonsplitSet H)
    (F : SignPair × H → AddChar (SignPair × H) ℂ → ℂ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ g ∈ S', ∀ ψ, ‖F g ψ‖ ≤ K) :
    ‖(1 / ((splitSet H).card : ℂ)) * ∑ g ∈ S', ∑ ψ : AddChar (SignPair × H) ℂ,
        starRingEnd ℂ (ψ g) * F g ψ‖ ≤ 2 * ((splitSet H).card : ℝ) * K := by
  have hΦ : (0 : ℝ) < (splitSet H).card := by
    have := splitSet_card_ne_zero (H := H)
    have h' : (splitSet H).card ≠ 0 := by exact_mod_cast this
    exact_mod_cast Nat.pos_of_ne_zero h'
  have hcard : (S'.card : ℝ) ≤ (splitSet H).card := by
    have := Finset.card_le_card hS'
    rw [card_nonsplitSet] at this
    exact_mod_cast this
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hinner : ∀ g ∈ S', ‖∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * F g ψ‖ ≤
      2 * ((splitSet H).card : ℝ) * K := by
    intro g hg
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ ψ ∈ (univ : Finset (AddChar (SignPair × H) ℂ)),
        ‖starRingEnd ℂ (ψ g) * F g ψ‖ ≤ K := by
      intro ψ _
      rw [norm_mul, Complex.norm_conj, AddChar.norm_apply, one_mul]
      exact hK g hg ψ
    refine (Finset.sum_le_card_nsmul _ _ K h1).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, Finset.card_univ, card_addChar_eq]
  have hout : ‖∑ g ∈ S', ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * F g ψ‖ ≤
      ((splitSet H).card : ℝ) * (2 * ((splitSet H).card : ℝ) * K) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hinner).trans ?_)
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  calc 1 / ((splitSet H).card : ℝ) *
        ‖∑ g ∈ S', ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * F g ψ‖
      ≤ 1 / ((splitSet H).card : ℝ) * (((splitSet H).card : ℝ) * (2 * ((splitSet H).card : ℝ) * K)) :=
        mul_le_mul_of_nonneg_left hout (by positivity)
    _ = 2 * ((splitSet H).card : ℝ) * K := by field_simp

/-- **Thickening costs little.** -/
theorem abs_re_balanceTotal_sub_le (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    (T₂ : Finset H) {A b η x : ℝ} (t u₀ : H) {w : SignPair × H → ℝ} (hA : 0 < A)
    (hAx : A ≤ (x + 1) * b) (hb : 0 < b) (hη : 0 ≤ η) (hx : 0 ≤ x)
    (hthick : ∀ ρ, IsThick T₂ u₀ ρ → b ≤ w ρ ∧ w ρ ≤ b + η + 1) :
    |(balanceTotal D ℓ A t w).re - (balanceTotal D ℓ A t (thickened T₂ b u₀ w)).re| ≤
      2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1)) := by
  have e : (balanceTotal D ℓ A t w).re - (balanceTotal D ℓ A t (thickened T₂ b u₀ w)).re =
      ((1 / ((splitSet H).card : ℂ)) * ∑ g ∈ nonsplitSet H, ∑ ψ : AddChar (SignPair × H) ℂ,
        starRingEnd ℂ (ψ g) * ((w (partnerClass t g) : ℂ) *
          classCesaro D ℓ ψ (A / w (partnerClass t g)) -
          (thickened T₂ b u₀ w (partnerClass t g) : ℂ) *
          classCesaro D ℓ ψ (A / thickened T₂ b u₀ w (partnerClass t g)))).re := by
    rw [← Complex.sub_re, balanceTotal, balanceTotal, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 2
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ψ _ => by ring
  rw [e]
  refine (Complex.abs_re_le_norm _).trans
    (norm_classSum_le _ (subset_refl _) _ (by positivity) fun g hg ψ => ?_)
  have hg' : ¬IsSplit g := by simpa [nonsplitSet] using hg
  have hρ := isSplit_partnerClass t hg'
  by_cases hth : IsThick T₂ u₀ (partnerClass t g)
  · rw [thickened, if_pos hth]
    obtain ⟨h1, h2⟩ := hthick _ hth
    have hl := norm_mul_classCesaro_sub_le D ℓ ψ hA hb h1
    rw [norm_sub_rev] at hl
    refine hl.trans ?_
    have e1 : 7 * A / b ≤ 7 * (x + 1) := by
      rw [div_le_iff₀ hb]
      nlinarith
    have e0 : 0 ≤ 7 * A / b := by positivity
    exact mul_le_mul e1 (by linarith) (by linarith) (by positivity)
  · rw [thickened, if_neg hth, sub_self, norm_zero]
    positivity

/-- **The thin part.** On classes not thick at `u₀` the thickened weights are the thin weights,
and thin scales make each term at most `(x+1)bθ`. -/
theorem norm_thinPart_le (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    (T₂ : Finset H) {A b b' X' θ x : ℝ} (t u₀ : H) {w : SignPair × H → ℝ} (hx : 3 ≤ x)
    (hb : 0 < b) (hX' : 0 < X') (hbX : b' * X' ≤ x * b) (hθ : 0 ≤ θ)
    (hAx : (x - 1) * b ≤ A ∧ A ≤ (x + 1) * b)
    (hwpos : ∀ ρ, IsSplit ρ → 0 < w ρ)
    (hthin : ∀ ρ, IsSplit ρ → ¬IsThick T₂ u₀ ρ → w ρ ≤ 2 * b')
    (hThin : ∀ (ψ : AddChar (SignPair × H) ℂ) (y : ℝ), X' / 3 ≤ y →
      ‖classCesaro D ℓ ψ y‖ ≤ y * θ) :
    ‖(1 / ((splitSet H).card : ℂ)) * ∑ g ∈ (nonsplitSet H).filter
        (fun g => ¬IsThick T₂ u₀ (partnerClass t g)), ∑ ψ : AddChar (SignPair × H) ℂ,
        starRingEnd ℂ (ψ g) * ((thickened T₂ b u₀ w (partnerClass t g) : ℂ) *
          classCesaro D ℓ ψ (A / thickened T₂ b u₀ w (partnerClass t g)))‖ ≤
      2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) := by
  refine norm_classSum_le _ (Finset.filter_subset _ _) _ (by positivity) fun g hg ψ => ?_
  obtain ⟨hg1, hg2⟩ := Finset.mem_filter.1 hg
  have hg' : ¬IsSplit g := by simpa [nonsplitSet] using hg1
  have hρ := isSplit_partnerClass t hg'
  rw [thickened, if_neg hg2]
  have hw0 := hwpos _ hρ
  have hw2 := hthin _ hρ hg2
  have hA0 : 0 < A := lt_of_lt_of_le (by nlinarith) hAx.1
  have hy : X' / 3 ≤ A / w (partnerClass t g) := by
    rw [le_div_iff₀ hw0]
    have h1 : X' / 3 * w (partnerClass t g) ≤ X' / 3 * (2 * b') := by
      exact mul_le_mul_of_nonneg_left hw2 (by positivity)
    nlinarith [hAx.1]
  have ht := hThin ψ _ hy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
  calc w (partnerClass t g) * ‖classCesaro D ℓ ψ (A / w (partnerClass t g))‖
      ≤ w (partnerClass t g) * (A / w (partnerClass t g) * θ) :=
        mul_le_mul_of_nonneg_left ht hw0.le
    _ = A * θ := by field_simp
    _ ≤ (x + 1) * b * θ := mul_le_mul_of_nonneg_right hAx.2 hθ

open Classical in
/-- **The translate average of the thickened balance**: thick part `(|T₂|/2|H|) b S(A/b)` plus the
average of the thin parts. -/
theorem average_balanceTotal_thickened (D : FrobeniusData H)
    (ℓ : AddChar (SignPair × H) ℂ → ℂ) (T₂ : Finset H) (A b : ℝ) (t : H)
    (w : H → SignPair × H → ℝ) :
    (1 / (Fintype.card H : ℂ)) * ∑ u₀ : H, balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀)) =
      (T₂.card : ℂ) / (2 * (Fintype.card H : ℂ)) * (b : ℂ) * signSignal D ℓ (A / b) +
      (1 / (Fintype.card H : ℂ)) * ∑ u₀ : H, (1 / ((splitSet H).card : ℂ)) *
        ∑ g ∈ (nonsplitSet H).filter (fun g => ¬IsThick T₂ u₀ (partnerClass t g)),
          ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) *
            ((thickened T₂ b u₀ (w u₀) (partnerClass t g) : ℂ) *
              classCesaro D ℓ ψ (A / thickened T₂ b u₀ (w u₀) (partnerClass t g))) := by
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hΦ := splitSet_card_ne_zero (H := H)
  set F : SignPair × H → ℂ := fun g => ∑ ψ : AddChar (SignPair × H) ℂ,
    starRingEnd ℂ (ψ g) * ((b : ℂ) * classCesaro D ℓ ψ (A / b)) with hF
  -- split every balance at the thick classes
  have hsplit : ∀ u₀ : H, balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀)) =
      (1 / ((splitSet H).card : ℂ)) * ∑ g ∈ (nonsplitSet H).filter
        (fun g => IsThick T₂ u₀ (partnerClass t g)), F g +
      (1 / ((splitSet H).card : ℂ)) * ∑ g ∈ (nonsplitSet H).filter
        (fun g => ¬IsThick T₂ u₀ (partnerClass t g)),
          ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) *
            ((thickened T₂ b u₀ (w u₀) (partnerClass t g) : ℂ) *
              classCesaro D ℓ ψ (A / thickened T₂ b u₀ (w u₀) (partnerClass t g))) := by
    intro u₀
    rw [balanceTotal, ← mul_add, ← Finset.sum_filter_add_sum_filter_not (nonsplitSet H)
      (fun g => IsThick T₂ u₀ (partnerClass t g))]
    congr 2
    · refine Finset.sum_congr rfl fun g hg => ?_
      have hth : IsThick T₂ u₀ (partnerClass t g) := (Finset.mem_filter.1 hg).2
      rw [hF]
      exact Finset.sum_congr rfl fun ψ _ => by rw [thickened, if_pos hth]; ring
    · exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun ψ _ => by ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, mul_add]
  congr 1
  -- the thick part averages to the signal
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (Fintype.card H : ℂ)), mul_assoc,
    average_sum_thick T₂ t F]
  have hcoset : ∑ h : H, F (((1, 0), h)) = (Fintype.card H : ℂ) * (b : ℂ) * signSignal D ℓ (A / b) := by
    rw [hF]
    simp only []
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_coset_conj]
    rw [signSignal, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    split_ifs <;> ring
  rw [hcoset, card_splitSet_eq]
  field_simp

end

end

end WindowedLandauTheory
