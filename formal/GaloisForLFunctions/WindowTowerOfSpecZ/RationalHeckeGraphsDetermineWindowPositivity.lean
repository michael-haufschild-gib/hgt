import GaloisForLFunctions.WindowTowerOfSpecZ.TheRationalLatticeOfAWindow
import GaloisForLFunctions.MultiplicativePositivityGeometry.AbelianZeroMass

/-!
# Finite rational Hecke graphs determine window positivity

An arithmetic correlation form is nonnegative on every compact window test iff
it is nonnegative on every finite rational graph of smaller logarithmic spread.
The converse averages translated graph forms over finite Følner sets of rational
logarithms. Their edge counts approach their vertex counts uniformly over the
finitely many active shifts, recovering the full window form after integration.
-/

noncomputable section

open Finset MeasureTheory Set

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ MultiplicativePositivityGeometry

/-- The quadratic form of the finite rational graph with edges `r ↦ nr`. -/
def rationalHeckeForm (N : ℕ) (c : ℕ → ℝ) (S : Finset ℚ) (y : ℚ → ℝ) : ℝ :=
  (∑ r ∈ S, y r ^ 2) + ∑ n ∈ Finset.Icc 2 N, c n *
    ∑ r ∈ S, ∑ s ∈ S, if (s : ℝ) = n * r then y r * y s else 0

/-- Positivity on every finite rational graph that fits strictly inside the window. -/
def RationalHeckePositive (A : ℝ) (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ S : Finset ℚ, (∀ r ∈ S, 0 < r) →
    (∀ r ∈ S, ∀ s ∈ S, Real.log s - Real.log r < A) →
      ∀ y : ℚ → ℝ, 0 ≤ rationalHeckeForm N c S y

private theorem rationalHeckeForm_filter (N : ℕ) (c : ℕ → ℝ)
    (S : Finset ℚ) (y : ℚ → ℝ) :
    rationalHeckeForm N c (S.filter fun r => y r ≠ 0) y =
      rationalHeckeForm N c S y := by
  classical
  unfold rationalHeckeForm
  congr 1
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : y r = 0
    · simp only [hr, ne_eq, not_true_eq_false, if_false, zero_pow two_ne_zero]
    · rw [if_pos hr]
  · apply Finset.sum_congr rfl
    intro n _
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : y r = 0
    · simp only [hr, ne_eq, not_true_eq_false, zero_mul, ite_self,
        Finset.sum_const_zero]
    · rw [if_pos hr, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : y s = 0
      · simp only [hs, ne_eq, not_true_eq_false, mul_zero, ite_self]
      · rw [if_pos hs]

private theorem RationalHeckePositive.of_amplitude_spread
    {A : ℝ} {N : ℕ} {c : ℕ → ℝ} (h : RationalHeckePositive A N c)
    (S : Finset ℚ) (hpos : ∀ r ∈ S, 0 < r) (y : ℚ → ℝ)
    (hspread : ∀ r ∈ S, y r ≠ 0 → ∀ s ∈ S, y s ≠ 0 →
      Real.log s - Real.log r < A) : 0 ≤ rationalHeckeForm N c S y := by
  classical
  rw [← rationalHeckeForm_filter N c S y]
  refine h _ (fun r hr => hpos r (Finset.mem_filter.mp hr).1) ?_ y
  intro r hr s hs
  exact hspread r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2
    s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2

private theorem window_nonzero_mem_interior {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) {u : ℝ} (hu : H u ≠ 0) : u ∈ Ioo (-A) 0 := by
  have hs : Function.support H ⊆ Icc (-A) 0 := by
    intro x hx
    by_contra h
    exact hx (hH.vanish x h)
  have hi := interior_maximal hs hH.continuous.isOpen_support hu
  simpa only [interior_Icc] using hi

private def IsRationalLog (v : ℝ) : Prop := ∃ q : ℚ, 0 < q ∧ Real.log q = v

private theorem rationalLog_zero : IsRationalLog 0 := ⟨1, one_pos, by simp⟩

private theorem IsRationalLog.add {v w : ℝ} (hv : IsRationalLog v)
    (hw : IsRationalLog w) : IsRationalLog (v + w) := by
  obtain ⟨q, hq, rfl⟩ := hv
  obtain ⟨r, hr, rfl⟩ := hw
  refine ⟨q * r, mul_pos hq hr, ?_⟩
  rw [Rat.cast_mul, Real.log_mul (by exact_mod_cast hq.ne')
    (by exact_mod_cast hr.ne')]

private theorem IsRationalLog.nsmul {v : ℝ} (hv : IsRationalLog v) (n : ℕ) :
    IsRationalLog (n • v) := by
  obtain ⟨q, hq, rfl⟩ := hv
  refine ⟨q ^ n, pow_pos hq n, ?_⟩
  rw [Rat.cast_pow, Real.log_pow, nsmul_eq_mul]

private theorem rationalLog_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ S, IsRationalLog (f i)) : IsRationalLog (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using rationalLog_zero
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem rationalLog_abFolnerSet (N M : ℕ) {v : ℝ}
    (hv : v ∈ abFolnerSet ((Finset.Icc 2 N).image fun n : ℕ => Real.log n) M) :
    IsRationalLog v := by
  classical
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hv
  apply rationalLog_sum
  intro s _
  apply IsRationalLog.nsmul
  obtain ⟨n, hn, hnlog⟩ := Finset.mem_image.mp s.property
  refine ⟨n, ?_, ?_⟩
  · exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (Finset.mem_Icc.mp hn).1)
  · simpa only [Rat.cast_natCast] using hnlog

private def finiteLogForm (N : ℕ) (c : ℕ → ℝ) (F : Finset ℝ)
    (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ v ∈ F, H (x + v) ^ 2) + ∑ n ∈ Finset.Icc 2 N, c n *
    ∑ v ∈ F.filter (fun v => v + Real.log n ∈ F),
      H (x + v) * H (x + (v + Real.log n))

private theorem finiteLogForm_nonneg {A : ℝ} {N : ℕ} {c : ℕ → ℝ}
    (h : RationalHeckePositive A N c) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (F : Finset ℝ) (hF : ∀ v ∈ F, IsRationalLog v) (x : ℝ) :
    0 ≤ finiteLogForm N c F H x := by
  classical
  have hrepr : ∀ v : ℝ, ∃ q : ℚ, 0 < q ∧ (v ∈ F → Real.log q = v) := by
    intro v
    by_cases hv : v ∈ F
    · obtain ⟨q, hq, heq⟩ := hF v hv
      exact ⟨q, hq, fun _ => heq⟩
    · exact ⟨1, one_pos, fun h => (hv h).elim⟩
  choose q hqpos hqlog using hrepr
  have hqinj : Set.InjOn q F := by
    intro v hv w hw heq
    rw [← hqlog v hv, ← hqlog w hw, heq]
  have hpos : ∀ r ∈ F.image q, 0 < r := by
    intro r hr
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hr
    exact hqpos v
  have hs := h.of_amplitude_spread (F.image q) hpos (fun r => H (x + Real.log r))
    (fun r _ hr s _ hs => by
      have hu := window_nonzero_mem_interior hH hr
      have hv := window_nonzero_mem_interior hH hs
      linarith only [hu.1, hv.2])
  have heq : rationalHeckeForm N c (F.image q) (fun r => H (x + Real.log r)) =
      finiteLogForm N c F H x := by
    unfold rationalHeckeForm finiteLogForm
    congr 1
    · rw [Finset.sum_image hqinj]
      exact Finset.sum_congr rfl fun v hv => by
        dsimp only
        rw [hqlog v hv]
    · apply Finset.sum_congr rfl
      intro n hn
      congr 1
      rw [Finset.sum_image hqinj, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_image hqinj]
      have hrel : ∀ w ∈ F, ((q w : ℝ) = n * q v) ↔ w = v + Real.log n := by
        intro w hw
        have hnpos : (0 : ℝ) < n := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (Finset.mem_Icc.mp hn).1)
        have hqv : (0 : ℝ) < q v := by exact_mod_cast hqpos v
        have hqw : (0 : ℝ) < q w := by exact_mod_cast hqpos w
        constructor
        · intro he
          have hl := congrArg Real.log he
          rw [Real.log_mul hnpos.ne' hqv.ne', hqlog v hv, hqlog w hw] at hl
          linarith only [hl]
        · intro he
          apply Real.log_injOn_pos hqw (mul_pos hnpos hqv)
          rw [Real.log_mul hnpos.ne' hqv.ne', hqlog v hv, hqlog w hw, he, add_comm]
      calc
        (∑ w ∈ F, if (q w : ℝ) = n * q v then
            H (x + Real.log (q v)) * H (x + Real.log (q w)) else 0) =
            ∑ w ∈ F, if w = v + Real.log n then H (x + v) * H (x + w) else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          simp only [hrel w hw, hqlog v hv, hqlog w hw]
        _ = if v + Real.log n ∈ F then
            H (x + v) * H (x + (v + Real.log n)) else 0 := by
          rw [Finset.sum_ite_eq']
  rwa [heq] at hs

private theorem integral_finiteLogForm {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (N : ℕ) (c : ℕ → ℝ) (F : Finset ℝ) :
    (∫ x, finiteLogForm N c F H x) =
      (F.card : ℝ) * (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 N,
        c n * ((F.filter fun v => v + Real.log n ∈ F).card : ℝ) *
          ∫ u, H u * H (u + Real.log n) := by
  classical
  have hsq : ∀ v : ℝ, Integrable fun x => H (x + v) ^ 2 := fun v =>
    _root_.RHTower.WeilMarkovPole.integrable_sq
      (hH.continuous.comp (continuous_add_const v))
      (hH.hasCompactSupport.comp_homeomorph (Homeomorph.addRight v))
  have hprod : ∀ v w : ℝ, Integrable fun x => H (x + v) * H (x + w) := fun v w =>
    ((hH.continuous.comp (continuous_add_const v)).mul
      (hH.continuous.comp (continuous_add_const w))).integrable_of_hasCompactSupport
      (hH.hasCompactSupport.comp_homeomorph (Homeomorph.addRight v)).mul_right
  unfold finiteLogForm
  rw [integral_add (integrable_finsetSum _ fun v _ => hsq v)
    (integrable_finsetSum (Finset.Icc 2 N) fun (n : ℕ) _ =>
      (integrable_finsetSum _ fun v _ => hprod v (v + Real.log (n : ℝ))).const_mul (c n)),
    integral_finsetSum _ fun v _ => hsq v,
    integral_finsetSum (Finset.Icc 2 N) fun (n : ℕ) _ =>
      (integrable_finsetSum _ fun v _ => hprod v (v + Real.log (n : ℝ))).const_mul (c n)]
  congr 1
  · simp only [integral_add_right_eq_self (fun u => H u ^ 2), Finset.sum_const,
      nsmul_eq_mul]
  · apply Finset.sum_congr rfl
    intro n _
    rw [integral_const_mul, integral_finsetSum _ fun v _ => hprod v (v + Real.log n)]
    have heq : ∀ v : ℝ, (∫ x, H (x + v) * H (x + (v + Real.log n))) =
        ∫ x, H x * H (x + Real.log n) := fun v => by
      simpa only [add_assoc] using
        (integral_add_right_eq_self (fun x => H x * H (x + Real.log n)) v)
    simp only [heq, Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Every finite arithmetic correlation form is positive on a window exactly when
all finite rational Hecke graphs of smaller logarithmic spread are positive. -/
theorem windowForm_nonneg_iff_rationalHeckePositive (A : ℝ) (N : ℕ) (c : ℕ → ℝ) :
    (∀ H : ℝ → ℝ, IsWindowTest A H →
      0 ≤ (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 N,
        c n * ∫ u, H u * H (u + Real.log n)) ↔ RationalHeckePositive A N c := by
  classical
  constructor
  · intro h S hpos hspread y
    obtain ⟨H, hH, I, hI, heq⟩ := exists_windowTest_eq_heckeForm S hpos hspread N c y
    have hform := h H hH
    rw [heq] at hform
    exact (mul_nonneg_iff_of_pos_left hI).mp hform
  · intro h H hH
    let D := ∫ u, H u ^ 2
    let C := fun n : ℕ => ∫ u, H u * H (u + Real.log n)
    let Q := D + ∑ n ∈ Finset.Icc 2 N, c n * C n
    let B := ∑ n ∈ Finset.Icc 2 N, |c n * C n|
    change 0 ≤ Q
    by_contra hQ
    have hQneg : Q < 0 := not_le.mp hQ
    have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
    let ε := -Q / (2 * (B + 1))
    have hε : 0 < ε := div_pos (neg_pos.mpr hQneg) (by linarith only [hB])
    let S := (Finset.Icc 2 N).image fun n : ℕ => Real.log n
    obtain ⟨M, hM, hstep⟩ := exists_abFolner_step S hε
    let F := abFolnerSet S M
    have hFpos : (0 : ℝ) < F.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_abFolnerSet S hM⟩
    have hpoint : ∀ x : ℝ, 0 ≤ finiteLogForm N c F H x :=
      finiteLogForm_nonneg h hH F (fun _ hv => rationalLog_abFolnerSet N M hv)
    have hweight := MeasureTheory.integral_nonneg (μ := volume)
      (f := fun x : ℝ => finiteLogForm N c F H x) hpoint
    rw [integral_finiteLogForm hH N c F] at hweight
    change 0 ≤ (F.card : ℝ) * D + ∑ n ∈ Finset.Icc 2 N,
      c n * ((F.filter fun v => v + Real.log n ∈ F).card : ℝ) * C n at hweight
    have hterm : ∀ n ∈ Finset.Icc 2 N,
        c n * ((F.filter fun v => v + Real.log n ∈ F).card : ℝ) * C n ≤
          (F.card : ℝ) * (c n * C n) + ε * (F.card : ℝ) * |c n * C n| := by
      intro n hn
      let K : ℝ := (F.filter fun v => v + Real.log n ∈ F).card
      have hKle : K ≤ (F.card : ℝ) := by
        dsimp only [K]
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset (fun v => v + Real.log (n : ℝ) ∈ F) F)
      have hKge : (1 - ε) * (F.card : ℝ) ≤ K := by
        have hc := card_abShift_mem_ge (S := S) (N := M) (p := Real.log n)
          (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
        change 2 * (F.card : ℝ) - (abFolnerSet S (M + 1)).card ≤ K at hc
        linarith only [hc, hstep]
      have hd0 : 0 ≤ (F.card : ℝ) - K := sub_nonneg.mpr hKle
      have hdε : (F.card : ℝ) - K ≤ ε * (F.card : ℝ) := by linarith only [hKge]
      have h1 := mul_le_mul_of_nonneg_right (neg_le_abs (c n * C n)) hd0
      have h2 := mul_le_mul_of_nonneg_left hdε (abs_nonneg (c n * C n))
      change c n * K * C n ≤ _
      nlinarith only [h1, h2]
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hmul : 0 ≤ (F.card : ℝ) * (Q + ε * B) := by
      dsimp only [Q, B]
      nlinarith only [hweight, hsum]
    have hQB := (mul_nonneg_iff_of_pos_left hFpos).mp hmul
    have heq : ε * (2 * (B + 1)) = -Q := by
      exact div_mul_cancel₀ _ (by linarith only [hB] : 2 * (B + 1) ≠ 0)
    have hεB : 0 ≤ ε * B := mul_nonneg hε.le hB
    nlinarith only [hQB, heq, hε, hεB]

#print axioms windowForm_nonneg_iff_rationalHeckePositive

end GaloisForLFunctions.WindowTowerOfSpecZ
