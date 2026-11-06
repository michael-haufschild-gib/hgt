import GaloisForLFunctions.RHTower.SteinhausPrimeDivergence
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation
import GaloisForLFunctions.HTGeometry.TrigonometricSumWindowMean

/-!
# Below the window, moments of prime sums are Steinhaus moments

Let `P` be a finite set of primes at most `Y` and `w ≥ 0` a weight. The *prime field* at height `t` is `Σ_{p ∈ P} w(p) cos(t log p)`, and its *model* replaces `p^{−it}` by the
Steinhaus character `X_p`. Their `j`-th moments agree up to the off-diagonal:

  `|T⁻¹ ∫_T^{2T} field^j dt − E model^j| ≤ 2 (A Y)^j / T`,   `A = Σ_p w(p)`  (`abs_mean_primeField_pow_sub_model_le`).

**Mechanism.** Both fields are `Re Σ_p w(p) χ(p)` for a completely multiplicative character `χ`. So the `j`-th power expands over the same index set into monomials `χ(n) conj χ(m)`,
with `n, m` products of at most `j` primes (`ofReal_charField_pow_eq`). On the model the mean of a monomial is `δ_{nm}` (`integral_X_mul_conj`). On the line it is `δ_{nm}` up to
`2 max(n, m)/T`, by the separation `|log n − log m| ≥ 1/max(n, m)`. The bound is the sum of these errors over all monomials.

This is the only place where heights enter the multiscale analysis below the window: at length `Y` with `(A Y)^j = o(T)`, the first `j` moments of a prime field are those of
independent phases.
-/

noncomputable section

open Complex MeasureTheory Filter Set
open RHTower.SteinhausModel

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The character `n ↦ n^{−it}`. -/
def lineChar (t : ℝ) (n : ℕ) : ℂ := cexp (((-(t * Real.log n) : ℝ) : ℂ) * I)

theorem lineChar_one (t : ℝ) : lineChar t 1 = 1 := by simp [lineChar]

theorem lineChar_mul (t : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    lineChar t (m * n) = lineChar t m * lineChar t n := by
  unfold lineChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  rw [Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
  push_cast
  ring

theorem lineChar_re (t : ℝ) (n : ℕ) : (lineChar t n).re = Real.cos (t * Real.log n) := by
  rw [lineChar, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The field `Σ_{p ∈ P} w(p) Re χ(p)` of a character. -/
def charField (w : ℕ → ℝ) (P : Finset ℕ) (χ : ℕ → ℂ) : ℝ := ∑ p ∈ P, w p * (χ p).re

/-- The prime field at height `t`. -/
def primeField (w : ℕ → ℝ) (P : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, w p * Real.cos (t * Real.log p)

/-- The Steinhaus model of the prime field. -/
def modelField (w : ℕ → ℝ) (P : Finset ℕ) (ω : Omega) : ℝ := ∑ p ∈ P, w p * (X p ω).re

theorem primeField_eq_charField (w : ℕ → ℝ) (P : Finset ℕ) (t : ℝ) :
    primeField w P t = charField w P (lineChar t) := by
  unfold primeField charField
  exact Finset.sum_congr rfl fun p _ => by rw [lineChar_re]

theorem modelField_eq_charField (w : ℕ → ℝ) (P : Finset ℕ) (ω : Omega) :
    modelField w P ω = charField w P (fun n => X n ω) := rfl

/-- One of `χ(p)`, `conj χ(p)`, according to a bit. -/
def bitChar (χ : ℕ → ℂ) (x : ℕ × Bool) : ℂ :=
  if x.2 then χ x.1 else (starRingEnd ℂ) (χ x.1)

/-- The index set of one factor. -/
def bitSet (P : Finset ℕ) : Finset (ℕ × Bool) := P ×ˢ Finset.univ

theorem ofReal_charField_eq (w : ℕ → ℝ) (P : Finset ℕ) (χ : ℕ → ℂ) :
    ((charField w P χ : ℝ) : ℂ) = ∑ x ∈ bitSet P, ((w x.1 / 2 : ℝ) : ℂ) * bitChar χ x := by
  unfold charField bitSet
  rw [Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, bitChar, if_true, Bool.false_eq_true, if_false]
  have h := Complex.add_conj (χ p)
  have hre : (((χ p).re : ℝ) : ℂ) = (χ p + (starRingEnd ℂ) (χ p)) / 2 := by
    rw [h]
    push_cast
    ring
  rw [hre]
  ring

/-- The numerator of a monomial: the product of the primes with bit `true`. -/
def monoNum {j : ℕ} (g : Fin j → ℕ × Bool) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i => (g i).2 = true), (g i).1

/-- The denominator of a monomial: the product of the primes with bit `false`. -/
def monoDen {j : ℕ} (g : Fin j → ℕ × Bool) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i => ¬ (g i).2 = true), (g i).1

/-- The weight of a monomial. -/
def monoWeight (w : ℕ → ℝ) {j : ℕ} (g : Fin j → ℕ × Bool) : ℝ := ∏ i, (w (g i).1 / 2)

/-- A completely multiplicative function on the positive integers. -/
structure IsCompletelyMultiplicative (χ : ℕ → ℂ) : Prop where
  one : χ 1 = 1
  mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → χ (m * n) = χ m * χ n

theorem IsCompletelyMultiplicative.prod {χ : ℕ → ℂ} (hχ : IsCompletelyMultiplicative χ) {ι : Type*}
    (s : Finset ι) {f : ι → ℕ} (hf : ∀ i ∈ s, f i ≠ 0) :
    ∏ i ∈ s, χ (f i) = χ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hχ.one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi),
      hχ.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem isCompletelyMultiplicative_lineChar (t : ℝ) : IsCompletelyMultiplicative (lineChar t) :=
  ⟨lineChar_one t, fun hm hn => lineChar_mul t hm hn⟩

theorem isCompletelyMultiplicative_X (ω : Omega) :
    IsCompletelyMultiplicative (fun n => X n ω) :=
  ⟨X_one ω, fun hm hn => X_mul hm hn ω⟩

/-- **The power of a character field as a sum of monomials.** The index set and the weights do not depend on the character. -/
theorem ofReal_charField_pow_eq (w : ℕ → ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, p ≠ 0) {χ : ℕ → ℂ}
    (hχ : IsCompletelyMultiplicative χ) (j : ℕ) :
    ((charField w P χ : ℝ) : ℂ) ^ j =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin j => bitSet P),
        ((monoWeight w g : ℝ) : ℂ) * (χ (monoNum g) * (starRingEnd ℂ) (χ (monoDen g))) := by
  rw [ofReal_charField_eq]
  have hprod : (∑ x ∈ bitSet P, ((w x.1 / 2 : ℝ) : ℂ) * bitChar χ x) ^ j =
      ∏ _i : Fin j, ∑ x ∈ bitSet P, ((w x.1 / 2 : ℝ) : ℂ) * bitChar χ x := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hmem : ∀ i, (g i).1 ∈ P := fun i =>
    (Finset.mem_product.mp (Fintype.mem_piFinset.mp hg i)).1
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp only [monoWeight]
    push_cast
    rfl
  · simp only [bitChar]
    rw [Finset.prod_ite]
    congr 1
    · rw [monoNum]
      exact hχ.prod _ fun i _ => hP _ (hmem i)
    · rw [monoDen, ← hχ.prod _ fun i _ => hP _ (hmem i), map_prod]

theorem monoNum_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p ≠ 0) {j : ℕ} {g : Fin j → ℕ × Bool}
    (hg : g ∈ Fintype.piFinset (fun _ : Fin j => bitSet P)) : monoNum g ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ =>
    hP _ (Finset.mem_product.mp (Fintype.mem_piFinset.mp hg i)).1

theorem monoDen_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p ≠ 0) {j : ℕ} {g : Fin j → ℕ × Bool}
    (hg : g ∈ Fintype.piFinset (fun _ : Fin j => bitSet P)) : monoDen g ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ =>
    hP _ (Finset.mem_product.mp (Fintype.mem_piFinset.mp hg i)).1

theorem monoNum_le {P : Finset ℕ} {Y : ℕ} (hY1 : 1 ≤ Y) (hY : ∀ p ∈ P, p ≤ Y) {j : ℕ}
    {g : Fin j → ℕ × Bool} (hg : g ∈ Fintype.piFinset (fun _ : Fin j => bitSet P)) :
    monoNum g ≤ Y ^ j := by
  refine (Finset.prod_le_pow_card _ _ Y fun i _ =>
    hY _ (Finset.mem_product.mp (Fintype.mem_piFinset.mp hg i)).1).trans ?_
  refine Nat.pow_le_pow_right hY1 ?_
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin j)) _

theorem monoDen_le {P : Finset ℕ} {Y : ℕ} (hY1 : 1 ≤ Y) (hY : ∀ p ∈ P, p ≤ Y) {j : ℕ}
    {g : Fin j → ℕ × Bool} (hg : g ∈ Fintype.piFinset (fun _ : Fin j => bitSet P)) :
    monoDen g ≤ Y ^ j := by
  refine (Finset.prod_le_pow_card _ _ Y fun i _ =>
    hY _ (Finset.mem_product.mp (Fintype.mem_piFinset.mp hg i)).1).trans ?_
  refine Nat.pow_le_pow_right hY1 ?_
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin j)) _

/-- The total weight of all monomials: `A^j`. -/
theorem sum_monoWeight_eq (w : ℕ → ℝ) (P : Finset ℕ) (j : ℕ) :
    ∑ g ∈ Fintype.piFinset (fun _ : Fin j => bitSet P), monoWeight w g = (∑ p ∈ P, w p) ^ j := by
  have hone : ∑ x ∈ bitSet P, w x.1 / 2 = ∑ p ∈ P, w p := by
    unfold bitSet
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton]
    ring
  rw [← hone]
  have hprod : (∑ x ∈ bitSet P, w x.1 / 2) ^ j = ∏ _i : Fin j, ∑ x ∈ bitSet P, w x.1 / 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod, Finset.prod_univ_sum]
  rfl

theorem monoWeight_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {j : ℕ} (g : Fin j → ℕ × Bool) :
    0 ≤ monoWeight w g :=
  Finset.prod_nonneg fun i _ => div_nonneg (hw _) (by norm_num)

/-- The window mean over `[T, 2T]`. -/
def windowMean (T : ℝ) (F : ℝ → ℂ) : ℂ := (T : ℂ)⁻¹ * ∫ t in T..(T + T), F t

theorem continuous_lineChar (n : ℕ) : Continuous fun t : ℝ => lineChar t n := by
  unfold lineChar
  fun_prop

/-- **The line mean of a monomial.** It is `δ_{nm}` up to `2 max(n, m)/T`. -/
theorem norm_windowMean_lineChar_sub_le {T : ℝ} (hT : 0 < T) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ‖windowMean T (fun t => lineChar t n * (starRingEnd ℂ) (lineChar t m)) -
        (if n = m then 1 else 0)‖ ≤ 2 * ((max n m : ℕ) : ℝ) / T := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  by_cases hnm : n = m
  · subst hnm
    have hone : ∀ t : ℝ, lineChar t n * (starRingEnd ℂ) (lineChar t n) = 1 := by
      intro t
      have hn1 : ‖lineChar t n‖ = 1 := by
        rw [lineChar, Complex.norm_exp_ofReal_mul_I]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn1]
      norm_num
    simp only [hone, if_true, windowMean, intervalIntegral.integral_const]
    have : (T : ℂ)⁻¹ * ((T + T - T : ℝ) • (1 : ℂ)) = 1 := by
      rw [add_sub_cancel_right, Complex.real_smul, mul_one, inv_mul_cancel₀ hT0]
    rw [this, sub_self, norm_zero]
    positivity
  · have hne : Real.log m - Real.log n ≠ 0 := by
      intro h
      have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr hm0) (Set.mem_Ioi.mpr hn0) (sub_eq_zero.mp h)
      exact hnm (by exact_mod_cast this.symm)
    have hpt : ∀ t : ℝ, lineChar t n * (starRingEnd ℂ) (lineChar t m) =
        cexp (I * (((Real.log m - Real.log n : ℝ) : ℂ) * t)) := by
      intro t
      unfold lineChar
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    simp only [hpt, if_neg hnm, sub_zero, windowMean]
    have hb := TrigSum.norm_integral_exp_I_mul_le (Real.log m - Real.log n) hne T T
    have hsep := HTGeometry.inv_max_le_abs_log_sub_log (Nat.pos_of_ne_zero hn)
      (Nat.pos_of_ne_zero hm) hnm
    rw [abs_sub_comm] at hsep
    have hmax : (0 : ℝ) < ((max n m : ℕ) : ℝ) := by
      exact_mod_cast lt_max_of_lt_left (Nat.pos_of_ne_zero hn)
    have habs : 0 < |Real.log m - Real.log n| := abs_pos.mpr hne
    have hinv : 2 / |Real.log m - Real.log n| ≤ 2 * ((max n m : ℕ) : ℝ) := by
      rw [div_le_iff₀ habs]
      have := (inv_le_iff_one_le_mul₀ hmax).mp hsep
      nlinarith
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le, inv_mul_le_iff₀ hT]
    refine hb.trans (hinv.trans (le_of_eq ?_))
    field_simp

/-- **The model mean of a monomial.** -/
theorem integral_X_monomial {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ ω, X n ω * (starRingEnd ℂ) (X m ω) ∂steinhausMeasure = if n = m then 1 else 0 :=
  integral_X_mul_conj hn hm

/-- **Below the window, moments of a prime field are Steinhaus moments.** For primes `p ∈ P` with `p ≤ Y` and `w ≥ 0`,
`|T⁻¹ ∫_T^{2T} field^j dt − E model^j| ≤ 2 (A Y)^j / T`, `A = Σ_p w(p)`. -/
theorem abs_mean_primeField_pow_sub_model_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p ≠ 0) {Y : ℕ} (hY1 : 1 ≤ Y) (hY : ∀ p ∈ P, p ≤ Y) {T : ℝ} (hT : 0 < T)
    (j : ℕ) :
    |T⁻¹ * (∫ t in T..(T + T), primeField w P t ^ j) -
        ∫ ω, modelField w P ω ^ j ∂steinhausMeasure| ≤
      2 * ((∑ p ∈ P, w p) * Y) ^ j / T := by
  classical
  set G := Fintype.piFinset (fun _ : Fin j => bitSet P) with hG
  -- the line side as a sum of monomial means
  have hline : ((T⁻¹ * (∫ t in T..(T + T), primeField w P t ^ j) : ℝ) : ℂ) =
      ∑ g ∈ G, ((monoWeight w g : ℝ) : ℂ) *
        windowMean T (fun t => lineChar t (monoNum g) *
          (starRingEnd ℂ) (lineChar t (monoDen g))) := by
    have hpt : ∀ t : ℝ, ((primeField w P t ^ j : ℝ) : ℂ) =
        ∑ g ∈ G, ((monoWeight w g : ℝ) : ℂ) *
          (lineChar t (monoNum g) * (starRingEnd ℂ) (lineChar t (monoDen g))) := by
      intro t
      rw [primeField_eq_charField, Complex.ofReal_pow]
      exact ofReal_charField_pow_eq w hP (isCompletelyMultiplicative_lineChar t) j
    have hcont : ∀ g ∈ G, IntervalIntegrable (fun t : ℝ => ((monoWeight w g : ℝ) : ℂ) *
        (lineChar t (monoNum g) * (starRingEnd ℂ) (lineChar t (monoDen g)))) volume T (T + T) :=
      fun g _ => (continuous_const.mul ((continuous_lineChar _).mul
        (continuous_star.comp (continuous_lineChar _)))).intervalIntegrable _ _
    rw [Complex.ofReal_mul, Complex.ofReal_inv, ← intervalIntegral.integral_ofReal]
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum hcont, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [intervalIntegral.integral_const_mul]
    simp only [windowMean]
    ring
  -- the model side as a sum of monomial means
  have hmodel : ((∫ ω, modelField w P ω ^ j ∂steinhausMeasure : ℝ) : ℂ) =
      ∑ g ∈ G, ((monoWeight w g : ℝ) : ℂ) *
        ∫ ω, X (monoNum g) ω * (starRingEnd ℂ) (X (monoDen g) ω) ∂steinhausMeasure := by
    have hpt : ∀ ω : Omega, ((modelField w P ω ^ j : ℝ) : ℂ) =
        ∑ g ∈ G, ((monoWeight w g : ℝ) : ℂ) *
          (X (monoNum g) ω * (starRingEnd ℂ) (X (monoDen g) ω)) := by
      intro ω
      rw [modelField_eq_charField, Complex.ofReal_pow]
      exact ofReal_charField_pow_eq w hP (isCompletelyMultiplicative_X ω) j
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun g _ => (integrable_X_mul_conj _ _).const_mul _]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_const_mul]
  have hdiff : (((T⁻¹ * (∫ t in T..(T + T), primeField w P t ^ j)) -
      ∫ ω, modelField w P ω ^ j ∂steinhausMeasure : ℝ) : ℂ) =
      ∑ g ∈ G, ((monoWeight w g : ℝ) : ℂ) *
        (windowMean T (fun t => lineChar t (monoNum g) *
            (starRingEnd ℂ) (lineChar t (monoDen g))) -
          if monoNum g = monoDen g then 1 else 0) := by
    rw [Complex.ofReal_sub, hline, hmodel, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [integral_X_monomial (monoNum_pos hP hg) (monoDen_pos hP hg)]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff]
  have hY0 : (0 : ℝ) < (Y : ℝ) ^ j := by
    have : (0 : ℝ) < Y := by exact_mod_cast hY1
    positivity
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ g ∈ G, ‖((monoWeight w g : ℝ) : ℂ) *
      (windowMean T (fun t => lineChar t (monoNum g) *
          (starRingEnd ℂ) (lineChar t (monoDen g))) -
        if monoNum g = monoDen g then 1 else 0)‖ ≤
      monoWeight w g * (2 * (Y : ℝ) ^ j / T) := by
    intro g hg
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (monoWeight_nonneg hw g)]
    refine mul_le_mul_of_nonneg_left ?_ (monoWeight_nonneg hw g)
    refine (norm_windowMean_lineChar_sub_le hT (monoNum_pos hP hg) (monoDen_pos hP hg)).trans ?_
    have hmax : max (monoNum g) (monoDen g) ≤ Y ^ j :=
      max_le (monoNum_le hY1 hY hg) (monoDen_le hY1 hY hg)
    have hmaxR : ((max (monoNum g) (monoDen g) : ℕ) : ℝ) ≤ (Y : ℝ) ^ j := by
      exact_mod_cast hmax
    exact div_le_div_of_nonneg_right (by linarith) hT.le
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, hG, sum_monoWeight_eq, mul_pow]
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
