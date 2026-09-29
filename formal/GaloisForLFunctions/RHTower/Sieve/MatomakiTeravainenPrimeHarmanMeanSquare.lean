import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanSourceMeanValue

/-!
# Matomäki–Teräväinen (5.2): the mean square of the prime-weighted Harman polynomial

For the prime polynomial `P₁(s) = ∑_{P < p ≤ 2P} p^{-s}`, `P ≍ (log X)^a`, `a ∈ [1.0999, 1.1]`, and
the Harman polynomial `P(s)` at `Y ≍ X/P`,
`∫_{T₀}^{T} |P₁(1+it)P(1+it)|² dt ≤ 2(log X)^{-2-ε/10} + 2(log X)^{-1-ε/10} PT/X`
for every `T ≥ 1`, `T₀ = exp(c (log X)^{1/2})`.  The height range splits three ways:

* where `|P₁(1+it)| ≥ P^{-ε/10}` and `t ≤ X`: the Proposition-2.2 family bound of
  `MatomakiTeravainenLargeAmplifierSetMeanSquare` (given the Deshouillers–Iwaniec and Watt
  twisted fourth moments), times `|P₁|² ≤ 4`;
* where `|P₁(1+it)| < P^{-ε/10}` and `t ≤ X`: `P^{-ε/5}` times the sifted mean value of `P`;
* heights above `X`: the product mean value of `P₁P`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The prime polynomial of `(P, 2P]` on the one-line: `|P₁(1+it)| ≤ 2`. -/
theorem norm_primeSetPoly_le_two {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P : ℝ} (hP : 1 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) (t : ℝ) :
    ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤ 2 := by
  have hP0 : 0 < P := by linarith
  have hterm : ∀ p ∈ B, ‖(p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤ 1 / P := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hBp p hp).pos
    rw [Complex.norm_natCast_cpow_of_pos (hBp p hp).pos]
    have hre : (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)).re = -1 := by simp
    rw [hre, Real.rpow_neg_one, ← one_div]
    exact one_div_le_one_div_of_le hP0 (hB p hp).1.le
  have hcard := card_le_of_subset_Ioc_real hP0.le hB
  calc ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖
      ≤ ∑ p ∈ B, ‖(p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ B, 1 / P := Finset.sum_le_sum hterm
    _ = (B.card : ℝ) / P := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (P + 1) / P := by gcongr
    _ ≤ 2 := by rw [div_le_iff₀ hP0]; linarith

theorem continuous_primeSetPoly (B : Finset ℕ) (hB0 : 0 ∉ B) :
    Continuous fun t : ℝ => ∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) := by
  refine continuous_finsetSum _ fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := fun h => hB0 (h ▸ hp)
    exact_mod_cast this
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg.const_cpow
    (Or.inl hp0)

/-- **The three-part split of (5.2).**  On `[T₀, T]`, the large-amplifier part (`|P₁| ≥ P^{-ε/10}`,
heights `≤ X`) costs `4·B_U`, the small-amplifier part costs `P^{-ε/5}` times the mean value of the
second factor, and heights above `X` cost the product mean value. -/
theorem setIntegral_primeSet_mul_split_le {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P : ℝ}
    (hP : 1 ≤ P) (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {G : ℝ → ℂ} (hG : Continuous G)
    {X T₀ T εU BU BN BH : ℝ} (hT₀ : 0 < T₀) (hT₀X : T₀ ≤ X) (hT : 1 ≤ T)
    (hU : ∀ U : Set ℝ, MeasurableSet U → U ⊆ Set.Icc T₀ X →
      (∀ t ∈ U, P ^ (-εU / 10) ≤
        ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
      ∫ t in U, ‖G t‖ ^ 2 ≤ BU)
    (hN : ∫ t in Set.Icc (-min T X) (min T X), ‖G t‖ ^ 2 ≤ BN)
    (hH : X < T → ∫ t in Set.Icc (-T) T,
      ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * G t‖ ^ 2 ≤ BH)
    (hBH : 0 ≤ BH) :
    ∫ t in Set.Icc T₀ T,
        ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * G t‖ ^ 2 ≤
      4 * BU + P ^ (-εU / 5) * BN + BH := by
  classical
  have hB0 : (0 : ℕ) ∉ B := fun h => (hBp 0 h).ne_zero rfl
  set P₁ : ℝ → ℂ := fun t => ∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) with hP₁
  have hP₁c : Continuous P₁ := continuous_primeSetPoly B hB0
  have hP₁2 : ∀ t, ‖P₁ t‖ ≤ 2 := norm_primeSetPoly_le_two hBp hP hB
  have hP0 : 0 < P := by linarith
  set c : ℝ := P ^ (-εU / 10) with hc
  have hc0 : 0 < c := by positivity
  set F : ℝ → ℝ := fun t => ‖P₁ t * G t‖ ^ 2 with hF
  have hFc : Continuous F := ((hP₁c.mul hG).norm).pow 2
  have hGc : Continuous fun t => ‖G t‖ ^ 2 := hG.norm.pow 2
  set T' := min T X with hT'
  set Ulg : Set ℝ := Set.Icc T₀ T' ∩ {t | c ≤ ‖P₁ t‖} with hUlg
  set Nsm : Set ℝ := Set.Icc T₀ T' ∩ {t | ‖P₁ t‖ < c} with hNsm
  set Hi : Set ℝ := Set.Ioc X T with hHi
  have hUm : MeasurableSet Ulg :=
    measurableSet_Icc.inter (isClosed_le continuous_const hP₁c.norm).measurableSet
  have hNm : MeasurableSet Nsm :=
    measurableSet_Icc.inter (isOpen_lt hP₁c.norm continuous_const).measurableSet
  have hT'X : T' ≤ X := min_le_right _ _
  have hT'T : T' ≤ T := min_le_left _ _
  -- the cover
  have hcov : Set.Icc T₀ T ⊆ ⋃ i : Fin 3, ![Ulg, Nsm, Hi] i := by
    intro t ht
    simp only [Set.mem_iUnion]
    rcases le_or_gt t X with htX | htX
    · have htT' : t ∈ Set.Icc T₀ T' := ⟨ht.1, le_min ht.2 htX⟩
      rcases le_or_gt c ‖P₁ t‖ with hct | hct
      · exact ⟨0, htT', hct⟩
      · exact ⟨1, htT', hct⟩
    · exact ⟨2, htX, ht.2⟩
  have hsub : ∀ i : Fin 3, ![Ulg, Nsm, Hi] i ⊆ Set.Icc 0 T := by
    intro i
    fin_cases i
    · exact fun t ht => ⟨by linarith [ht.1.1], ht.1.2.trans hT'T⟩
    · exact fun t ht => ⟨by linarith [ht.1.1], ht.1.2.trans hT'T⟩
    · exact fun t ht => ⟨by linarith [ht.1, hT₀X], ht.2⟩
  have hmain := setIntegral_le_sum_setIntegral_of_subset_iUnion (f := F) hFc hsub
    (hcov.trans (le_refl _)) (fun t => by positivity)
  rw [Fin.sum_univ_three] at hmain
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hmain
  refine hmain.trans ?_
  have hint : ∀ {S : Set ℝ}, S ⊆ Set.Icc (-T) T → IntegrableOn F S := fun h =>
    hFc.integrableOn_Icc.mono_set h
  have hintG : ∀ {S : Set ℝ}, S ⊆ Set.Icc (-T) T → IntegrableOn (fun t => ‖G t‖ ^ 2) S := fun h =>
    hGc.integrableOn_Icc.mono_set h
  have hUT : Ulg ⊆ Set.Icc (-T) T := fun t ht => ⟨by linarith [ht.1.1], ht.1.2.trans hT'T⟩
  have hNT : Nsm ⊆ Set.Icc (-T) T := fun t ht => ⟨by linarith [ht.1.1], ht.1.2.trans hT'T⟩
  -- the large-amplifier part
  have h1 : ∫ t in Ulg, F t ≤ 4 * BU := by
    have hpt : ∀ t ∈ Ulg, F t ≤ 4 * ‖G t‖ ^ 2 := by
      intro t _
      rw [hF]; dsimp only
      rw [norm_mul, mul_pow]
      have := pow_le_pow_left₀ (norm_nonneg _) (hP₁2 t) 2
      nlinarith [sq_nonneg ‖G t‖]
    calc ∫ t in Ulg, F t ≤ ∫ t in Ulg, 4 * ‖G t‖ ^ 2 :=
          setIntegral_mono_on (hint hUT) ((hintG hUT).const_mul 4) hUm hpt
      _ = 4 * ∫ t in Ulg, ‖G t‖ ^ 2 := integral_const_mul _ _
      _ ≤ 4 * BU := by
          gcongr
          exact hU Ulg hUm (fun t ht => ⟨ht.1.1, ht.1.2.trans hT'X⟩) (fun t ht => ht.2)
  -- the small-amplifier part
  have h2 : ∫ t in Nsm, F t ≤ P ^ (-εU / 5) * BN := by
    have hc2 : c ^ 2 = P ^ (-εU / 5) := by
      rw [hc, ← Real.rpow_mul_natCast hP0.le]; ring_nf
    have hpt : ∀ t ∈ Nsm, F t ≤ P ^ (-εU / 5) * ‖G t‖ ^ 2 := by
      intro t ht
      rw [hF]; dsimp only
      rw [norm_mul, mul_pow, ← hc2]
      have := pow_le_pow_left₀ (norm_nonneg _) (le_of_lt ht.2) 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hNsub : Nsm ⊆ Set.Icc (-T') T' := fun t ht => ⟨by linarith [ht.1.1, ht.1.2], ht.1.2⟩
    calc ∫ t in Nsm, F t ≤ ∫ t in Nsm, P ^ (-εU / 5) * ‖G t‖ ^ 2 :=
          setIntegral_mono_on (hint hNT) ((hintG hNT).const_mul _) hNm hpt
      _ = P ^ (-εU / 5) * ∫ t in Nsm, ‖G t‖ ^ 2 := integral_const_mul _ _
      _ ≤ P ^ (-εU / 5) * ∫ t in Set.Icc (-T') T', ‖G t‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (setIntegral_mono_set hGc.integrableOn_Icc
            (Filter.Eventually.of_forall fun t => by positivity)
            (Filter.Eventually.of_forall hNsub)) (by positivity)
      _ ≤ P ^ (-εU / 5) * BN := by gcongr
  -- the high part
  have h3 : ∫ t in Hi, F t ≤ BH := by
    rcases le_or_gt T X with hTX | hTX
    · have : Hi = ∅ := by
        rw [hHi]; exact Set.Ioc_eq_empty (by linarith)
      rw [this, setIntegral_empty]; exact hBH
    · refine le_trans ?_ (hH hTX)
      exact setIntegral_mono_set hFc.integrableOn_Icc
        (Filter.Eventually.of_forall fun t => by positivity)
        (Filter.Eventually.of_forall fun t ht => ⟨by linarith [ht.1, hT₀X], ht.2⟩)
  linarith

/-- The family budget in the logarithmic variable `L = log X`. -/
theorem eventually_family_budget_log {K : ℝ} (hK : 0 ≤ K) {A : ℕ} (hA : 5 ≤ A) {ε : ℝ}
    (hε1 : ε ≤ 1) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ N : ℝ, 0 ≤ N → N ≤ Real.exp ((Real.log L) ^ 5) →
      8 * N ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) +
          8 * (K * (20 * Real.pi * Real.exp 1 + 240 * Real.pi * L ^ (11 / 10 : ℝ)) *
            L ^ (-((A : ℕ) : ℝ))) ≤
        L ^ (-(2 + ε / 10)) := by
  have h5 := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) (by norm_num : (0 : ℝ) < 1 / 40)).bound
    (by norm_num : (0 : ℝ) < 1 / 8)
  have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  have hbig := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40)).eventually_ge_atTop
    (8 * Real.log 16)
  have hK' := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 18 / 10)).eventually_ge_atTop
    (16 * K * (20 * Real.pi * Real.exp 1 + 240 * Real.pi))
  filter_upwards [h5, h1, hbig, hK', Filter.eventually_ge_atTop (2 : ℝ)] with L h5 h1 hbig hK' hL2 N hN0 hN
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hr : 0 < L ^ (1 / 40 : ℝ) := Real.rpow_pos_of_pos hL0 _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogL _), Real.norm_of_nonneg hr.le] at h5
  rw [Real.norm_of_nonneg hlogL, Real.norm_of_nonneg hr.le] at h1
  have h5' : (Real.log L) ^ 5 ≤ L ^ (1 / 40 : ℝ) / 8 := by
    rw [show (Real.log L) ^ 5 = (Real.log L) ^ (5 : ℝ) by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    linarith
  -- the family term
  have hT1 : 8 * N ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) ≤ L ^ (-(2 + ε / 10)) / 2 := by
    have hN2 : N ^ 2 ≤ Real.exp (2 * (Real.log L) ^ 5) := by
      calc N ^ 2 ≤ (Real.exp ((Real.log L) ^ 5)) ^ 2 := pow_le_pow_left₀ hN0 hN 2
        _ = Real.exp (2 * (Real.log L) ^ 5) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hexp : 8 * Real.exp (2 * (Real.log L) ^ 5) * Real.exp (-L ^ (1 / 40 : ℝ)) ≤
        L ^ (-(2 + ε / 10)) / 2 := by
      have hrw : L ^ (-(2 + ε / 10)) / 2 = Real.exp (-(2 + ε / 10) * Real.log L - Real.log 2) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num), Real.rpow_def_of_pos hL0]; ring_nf
      have h8 : (8 : ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
      rw [hrw, h8, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hl8 : Real.log 8 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hl16 : Real.log 2 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
      have hεlog : ε / 10 * Real.log L ≤ Real.log L / 10 := by
        have := mul_le_mul_of_nonneg_right hε1 hlogL
        linarith
      have hexpand : -(2 + ε / 10) * Real.log L = -(2 * Real.log L) - ε / 10 * Real.log L := by ring
      rw [hexpand]
      have ha : 2 * Real.log L ^ 5 ≤ L ^ (1 / 40 : ℝ) / 4 := by linarith only [h5']
      have hb : 2 * Real.log L ≤ L ^ (1 / 40 : ℝ) / 8 := by linarith only [h1]
      have hc : ε / 10 * Real.log L ≤ L ^ (1 / 40 : ℝ) / 160 := by linarith only [h1, hεlog]
      have hd : Real.log 8 + Real.log 2 ≤ L ^ (1 / 40 : ℝ) / 4 := by
        linarith only [hbig, hl8, hl16]
      linarith only [ha, hb, hc, hd, hr]
    calc 8 * N ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) ≤
          8 * Real.exp (2 * (Real.log L) ^ 5) * Real.exp (-L ^ (1 / 40 : ℝ)) := by gcongr
      _ ≤ _ := hexp
  -- the error term
  have hT2 : 8 * (K * (20 * Real.pi * Real.exp 1 + 240 * Real.pi * L ^ (11 / 10 : ℝ)) *
      L ^ (-((A : ℕ) : ℝ))) ≤ L ^ (-(2 + ε / 10)) / 2 := by
    have hL11 : 1 ≤ L ^ (11 / 10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hbr : 20 * Real.pi * Real.exp 1 + 240 * Real.pi * L ^ (11 / 10 : ℝ) ≤
        (20 * Real.pi * Real.exp 1 + 240 * Real.pi) * L ^ (11 / 10 : ℝ) := by
      have : 0 ≤ 20 * Real.pi * Real.exp 1 := by positivity
      nlinarith
    have hA5 : L ^ (-((A : ℕ) : ℝ)) ≤ L ^ (-5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by
        have : (5 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
        linarith)
    have hsplit : L ^ (11 / 10 : ℝ) * L ^ (-5 : ℝ) * L ^ (18 / 10 : ℝ) = L ^ (-(2 + 1 / 10) : ℝ) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
    have hε' : L ^ (-(2 + 1 / 10) : ℝ) ≤ L ^ (-(2 + ε / 10)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    set C := 20 * Real.pi * Real.exp 1 + 240 * Real.pi with hC
    have hC0 : 0 ≤ C := by positivity
    have hpow0 : 0 < L ^ (-5 : ℝ) := by positivity
    have h18 : 0 < L ^ (18 / 10 : ℝ) := by positivity
    calc 8 * (K * (20 * Real.pi * Real.exp 1 + 240 * Real.pi * L ^ (11 / 10 : ℝ)) *
          L ^ (-((A : ℕ) : ℝ)))
        ≤ 8 * (K * (C * L ^ (11 / 10 : ℝ)) * L ^ (-5 : ℝ)) := by gcongr
      _ = (16 * K * C) * (L ^ (11 / 10 : ℝ) * L ^ (-5 : ℝ)) / 2 := by ring
      _ ≤ L ^ (18 / 10 : ℝ) * (L ^ (11 / 10 : ℝ) * L ^ (-5 : ℝ)) / 2 := by gcongr
      _ = L ^ (-(2 + 1 / 10) : ℝ) / 2 := by rw [← hsplit]; ring
      _ ≤ L ^ (-(2 + ε / 10)) / 2 := by gcongr
  linarith

/-- The small-amplifier and high-height budgets of (5.2). -/
theorem harmanProduct_small_high_budget {L P X T T' Y ε C_N C_H : ℝ} (hL1 : 1 ≤ L) (hLP : L ≤ P)
    (hX0 : 0 < X) (hY0 : 0 < Y) (hT'T : T' ≤ T) (hT'0 : 0 ≤ T') (hXPY : X ≤ 2 * P * Y) (hε : 0 < ε)
    (hCN : 0 ≤ C_N) (hCNL : C_N * L ^ (-(ε / 5)) ≤ L ^ (-(ε / 10)) / 2)
    (hCH : C_H * L ^ (1 + ε / 10) ≤ P) :
    P ^ (-(ε / 5)) * (C_N * (T' / (Y * L) + 1 / L ^ 2)) ≤
        L ^ (-(2 + ε / 10)) / 2 + L ^ (-(1 + ε / 10)) * P * T / X ∧
      C_H * T / X ≤ L ^ (-(1 + ε / 10)) * P * T / X := by
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < P := by linarith
  have hPL : P ^ (-(ε / 5)) ≤ L ^ (-(ε / 5)) :=
    Real.rpow_le_rpow_of_nonpos hL0 hLP (by linarith)
  have hYinv : 1 / Y ≤ 2 * P / X := by
    rw [div_le_div_iff₀ hY0 hX0]; linarith
  have hsum : T' / (Y * L) + 1 / L ^ 2 ≤ 2 * P * T / (X * L) + 1 / L ^ 2 := by
    have : T' / (Y * L) ≤ 2 * P * T / (X * L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : T' * X ≤ T * (2 * P * Y) := by nlinarith
      nlinarith
    linarith
  have hsum0 : 0 ≤ T' / (Y * L) + 1 / L ^ 2 := by positivity
  have hLm : L ^ (-(ε / 10)) * (1 / L) = L ^ (-(1 + ε / 10)) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hL0]; ring_nf
  have hLm2 : L ^ (-(ε / 10)) * (1 / L ^ 2) = L ^ (-(2 + ε / 10)) := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]; push_cast; ring_nf
  constructor
  · calc P ^ (-(ε / 5)) * (C_N * (T' / (Y * L) + 1 / L ^ 2))
        ≤ L ^ (-(ε / 5)) * (C_N * (2 * P * T / (X * L) + 1 / L ^ 2)) := by gcongr
      _ = (C_N * L ^ (-(ε / 5))) * (2 * P * T / (X * L) + 1 / L ^ 2) := by ring
      _ ≤ (L ^ (-(ε / 10)) / 2) * (2 * P * T / (X * L) + 1 / L ^ 2) := by
          have : 0 ≤ 2 * P * T / (X * L) + 1 / L ^ 2 := by
            have hT0 : 0 ≤ T := le_trans hT'0 hT'T
            positivity
          gcongr
      _ = (L ^ (-(ε / 10)) * (1 / L)) * P * T / X + (L ^ (-(ε / 10)) * (1 / L ^ 2)) / 2 := by
          field_simp
      _ = L ^ (-(2 + ε / 10)) / 2 + L ^ (-(1 + ε / 10)) * P * T / X := by
          rw [hLm, hLm2]; ring
  · have hT0 : 0 ≤ T := le_trans hT'0 hT'T
    have hCH' : C_H ≤ L ^ (-(1 + ε / 10)) * P := by
      have hpos : 0 < L ^ (1 + ε / 10) := by positivity
      have hinv : L ^ (-(1 + ε / 10)) * L ^ (1 + ε / 10) = 1 := by
        rw [← Real.rpow_add hL0]; simp
      calc C_H = C_H * L ^ (1 + ε / 10) * L ^ (-(1 + ε / 10)) := by
            rw [mul_assoc, mul_comm (L ^ (1 + ε / 10)), hinv, mul_one]
        _ ≤ P * L ^ (-(1 + ε / 10)) := by gcongr
        _ = L ^ (-(1 + ε / 10)) * P := by ring
    calc C_H * T / X ≤ L ^ (-(1 + ε / 10)) * P * T / X := by gcongr

/-- The large-amplifier budget at the Proposition-2.2 family, with `X/Y ≤ 2P ≤ 6L^{1.1}`. -/
theorem largeAmplifier_budget_of_family {L X Y P K ε : ℝ} {A : ℕ}
    (hbud : ∀ N : ℝ, 0 ≤ N → N ≤ Real.exp ((Real.log L) ^ 5) →
      8 * N ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) +
          8 * (K * (20 * Real.pi * Real.exp 1 + 240 * Real.pi * L ^ (11 / 10 : ℝ)) *
            L ^ (-((A : ℕ) : ℝ))) ≤ L ^ (-(2 + ε / 10)))
    {n : ℕ} (hn : (n : ℝ) ≤ Real.exp ((Real.log L) ^ 5)) (hY0 : 0 < Y) (hXPY : X ≤ 2 * P * Y)
    (hP : 2 * P ≤ 6 * L ^ (11 / 10 : ℝ)) (hL0 : 0 < L) (hK : 0 ≤ K) :
    4 * (2 * (n : ℝ) ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) +
      2 * (K * (20 * Real.pi * Real.exp 1 + 40 * Real.pi * X / Y) * L ^ (-((A : ℕ) : ℝ)))) ≤
      L ^ (-(2 + ε / 10)) := by
  have hb := hbud (n : ℝ) (Nat.cast_nonneg _) hn
  have hXY : X / Y ≤ 6 * L ^ (11 / 10 : ℝ) := by
    rw [div_le_iff₀ hY0]
    have : 2 * P * Y ≤ 6 * L ^ (11 / 10 : ℝ) * Y := mul_le_mul_of_nonneg_right hP hY0.le
    linarith
  have hmono : 40 * Real.pi * X / Y ≤ 240 * Real.pi * L ^ (11 / 10 : ℝ) := by
    have e : 40 * Real.pi * X / Y = 40 * Real.pi * (X / Y) := by ring
    rw [e]
    have hpi : 0 ≤ 40 * Real.pi := by positivity
    calc 40 * Real.pi * (X / Y) ≤ 40 * Real.pi * (6 * L ^ (11 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left hXY hpi
      _ = 240 * Real.pi * L ^ (11 / 10 : ℝ) := by ring
  have hLA : 0 ≤ L ^ (-((A : ℕ) : ℝ)) := Real.rpow_nonneg hL0.le _
  calc 4 * (2 * (n : ℝ) ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) +
        2 * (K * (20 * Real.pi * Real.exp 1 + 40 * Real.pi * X / Y) * L ^ (-((A : ℕ) : ℝ))))
      = 8 * (n : ℝ) ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) +
        8 * (K * (20 * Real.pi * Real.exp 1 + 40 * Real.pi * X / Y) * L ^ (-((A : ℕ) : ℝ))) := by
        ring
    _ ≤ 8 * (n : ℝ) ^ 2 * Real.exp (-L ^ (1 / 40 : ℝ)) +
        8 * (K * (20 * Real.pi * Real.exp 1 + 240 * Real.pi * L ^ (11 / 10 : ℝ)) *
          L ^ (-((A : ℕ) : ℝ))) := by gcongr
    _ ≤ L ^ (-(2 + ε / 10)) := hb

/-- **The (5.2) core.**  The three mean values combined through the three-part split. -/
theorem harmanProduct_meanSquare_core {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P : ℝ}
    (hP1 : 1 ≤ P) (hBr : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {G : ℝ → ℂ} (hGc : Continuous G)
    {X T₀ T ε L Y BU C_N C_H : ℝ} (hX0 : 0 < X) (hX1 : 1 ≤ X) (hT₀ : 0 < T₀) (hT₀X : T₀ ≤ X)
    (hT : 1 ≤ T) (hL1 : 1 ≤ L) (hLP : L ≤ P) (hY0 : 0 < Y) (hXPY : X ≤ 2 * P * Y) (hε : 0 < ε)
    (hCN : 0 ≤ C_N) (hCNL : C_N * L ^ (-(ε / 5)) ≤ L ^ (-(ε / 10)) / 2)
    (hCHP : C_H * L ^ (1 + ε / 10) ≤ P)
    (hC_H : C_H = 156 ^ 2 * 8 * (10 * Real.pi * Real.exp 1 + 20 * Real.pi))
    (hUb : ∀ U : Set ℝ, MeasurableSet U → U ⊆ Set.Icc T₀ X →
      (∀ t ∈ U, P ^ (-ε / 10) ≤
        ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
      ∫ t in U, ‖G t‖ ^ 2 ≤ BU)
    (hBU4 : 4 * BU ≤ L ^ (-(2 + ε / 10)))
    (hNb : ∫ t in Set.Icc (-min T X) (min T X), ‖G t‖ ^ 2 ≤ C_N * (min T X / (Y * L) + 1 / L ^ 2))
    (hHb : X < T → ∫ t in Set.Icc (-T) T,
      ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * G t‖ ^ 2 ≤
        156 ^ 2 * 8 * (10 * Real.pi * Real.exp 1 + 10 * Real.pi * T / (P * Y))) :
    ∫ t in Set.Icc T₀ T,
        ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * G t‖ ^ 2 ≤
      2 * L ^ (-(2 + ε / 10)) + 2 * L ^ (-(1 + ε / 10)) * P * T / X := by
  set BH : ℝ := if X < T then 156 ^ 2 * 8 * (10 * Real.pi * Real.exp 1 + 10 * Real.pi * T / (P * Y))
    else 0 with hBH
  have hsplit := setIntegral_primeSet_mul_split_le hBp hP1 hBr hGc (X := X) (T₀ := T₀) (T := T)
    (εU := ε) (BU := BU) (BN := C_N * (min T X / (Y * L) + 1 / L ^ 2)) (BH := BH) hT₀ hT₀X hT hUb hNb
    (fun h => by rw [hBH, if_pos h]; exact hHb h) (by rw [hBH]; split_ifs <;> positivity)
  refine hsplit.trans ?_
  have hL0 : 0 < L := by linarith
  obtain ⟨hBNb, hBHb⟩ := harmanProduct_small_high_budget (T' := min T X) (C_N := C_N) (C_H := C_H)
    hL1 hLP hX0 hY0 (min_le_left _ _) (le_trans zero_le_one (le_min hT hX1)) hXPY hε hCN hCNL hCHP
  have hPε : P ^ (-ε / 5) = P ^ (-(ε / 5)) := by rw [neg_div]
  have hBHt : BH ≤ L ^ (-(1 + ε / 10)) * P * T / X := by
    rw [hBH]
    split_ifs with h
    · refine le_trans ?_ hBHb
      have hT0 : 0 < T := by linarith
      have hP0 : 0 < P := by linarith
      have h1 : 10 * Real.pi * Real.exp 1 ≤ 10 * Real.pi * Real.exp 1 * (T / X) := by
        have : 1 ≤ T / X := by rw [le_div_iff₀ hX0]; linarith
        have hpe : 0 ≤ 10 * Real.pi * Real.exp 1 := by positivity
        nlinarith
      have h2 : 10 * Real.pi * T / (P * Y) ≤ 20 * Real.pi * (T / X) := by
        rw [div_le_iff₀ (by positivity)]
        have hm : T * X ≤ T * (2 * P * Y) := mul_le_mul_of_nonneg_left hXPY hT0.le
        have e : 20 * Real.pi * (T / X) * (P * Y) = 10 * Real.pi * (T * (2 * P * Y)) / X := by
          field_simp; ring
        rw [e, le_div_iff₀ hX0]
        have hpi : 0 ≤ 10 * Real.pi := by positivity
        nlinarith
      calc 156 ^ 2 * 8 * (10 * Real.pi * Real.exp 1 + 10 * Real.pi * T / (P * Y))
          ≤ 156 ^ 2 * 8 * (10 * Real.pi * Real.exp 1 * (T / X) + 20 * Real.pi * (T / X)) := by
            gcongr
        _ = C_H * T / X := by rw [hC_H]; ring
    · have hT0 : 0 ≤ T := by linarith
      have hP0 : 0 ≤ P := by linarith
      positivity
  rw [hPε]
  have hLpos : 0 ≤ L ^ (-(2 + ε / 10)) := Real.rpow_nonneg hL0.le _
  refine (add_le_add (add_le_add hBU4 hBNb) hBHt).trans ?_
  have e : 2 * L ^ (-(1 + ε / 10)) * P * T / X = 2 * (L ^ (-(1 + ε / 10)) * P * T / X) := by ring
  rw [e]
  linarith only [hLpos]

/-- The `z`-facts for the product mean value: `z = ⌈X^{2/11}⌉ ≥ 2`, every prime of `(P, 2P]` lies
below `z` when `2P ≤ 6(log X)^{1.1} < X^{2/11}`, and `4Y < z⁶` for `Y ≤ X`. -/
theorem mtProposition22ZNat_facts {X P L Y : ℝ} {B : Finset ℕ} (hX1 : 1 < X)
    (h11 : 5 ≤ X ^ (1 / 11 : ℝ)) (hP : 2 * P ≤ 6 * L) (h6L : 7 * L ≤ X ^ (2 / 11 : ℝ))
    (hBr : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) (hYX : Y ≤ X) :
    2 ≤ mtProposition22ZNat X ∧ (∀ p ∈ B, p < mtProposition22ZNat X) ∧
      4 * Y < ((mtProposition22ZNat X : ℕ) : ℝ) ^ 6 := by
  have hX0 : 0 < X := by linarith
  have hzR : X ^ (2 / 11 : ℝ) ≤ (mtProposition22ZNat X : ℝ) := Nat.le_ceil _
  have h25 : (25 : ℝ) ≤ X ^ (2 / 11 : ℝ) := by
    have : X ^ (2 / 11 : ℝ) = X ^ (1 / 11 : ℝ) * X ^ (1 / 11 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    rw [this]; nlinarith
  refine ⟨?_, fun p hp => ?_, ?_⟩
  · have : (2 : ℝ) ≤ (mtProposition22ZNat X : ℝ) := by linarith
    exact_mod_cast this
  · have h1 := (hBr p hp).2
    have : (p : ℝ) < (mtProposition22ZNat X : ℝ) := by linarith
    exact_mod_cast this
  · have h12 : X ^ (12 / 11 : ℝ) ≤ (mtProposition22ZNat X : ℝ) ^ 6 := by
      calc X ^ (12 / 11 : ℝ) = (X ^ (2 / 11 : ℝ)) ^ 6 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
        _ ≤ (mtProposition22ZNat X : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) hzR 6
    have h4X : 4 * X < X ^ (12 / 11 : ℝ) := by
      have hs : X ^ (12 / 11 : ℝ) = X ^ (1 / 11 : ℝ) * X := by
        rw [← Real.rpow_add_one hX0.ne']; norm_num
      rw [hs]; nlinarith
    linarith

/-- **Matomäki–Teräväinen (5.2), given Deshouillers–Iwaniec and Watt.**  For the prime polynomial
`P₁` of `(P, 2P]`, `P ∈ [(log X)^a, 3(log X)^{1.1}]`, and the Harman polynomial `P` at `Y ≍ X/P`:
`∫_{T₀}^{T} |P₁(1+it)P(1+it)|² dt ≤ 2(log X)^{-2-ε/10} + 2(log X)^{-1-ε/10} PT/X` for every
`T ≥ 1`, `T₀ = exp(c (log X)^{1/2})`. -/
theorem eventually_harmanProduct_meanSquare_le (hDI : MTDeshouillersIwaniecBound)
    (hW : MTWattBound) {a₀ ε c : ℝ} {A : ℕ} (hA : 5 ≤ A) (ha₀ : 10999 / 10000 ≤ a₀)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ (a P : ℝ) (B : Finset ℕ), a₀ ≤ a → a ≤ 11 / 10 →
      Real.log X ^ a ≤ P → P ≤ 3 * Real.log X ^ (11 / 10 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Y : ℕ, X ^ (1 - ε / 100) < Y → (Y : ℝ) ≤ X / 2 → X ≤ 2 * P * Y →
      ∀ T : ℝ, 1 ≤ T →
        ∫ t in Set.Icc (Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))) T,
            ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
              LSeries (fun n => mtHarmanProposition22SourceAF (mtProposition22ZNat X)
                (mtProposition22QNat X) (mtProposition22DNat X ε) (mtProposition22ENat X ε) Y n)
                (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          2 * Real.log X ^ (-(2 + ε / 10)) + 2 * Real.log X ^ (-(1 + ε / 10)) * P * T / X := by
  obtain ⟨C_N, hC_N, hNev⟩ := eventually_integral_normSq_LSeries_harmanSource_le
  set C_E : ℝ := (92224 : ℝ) * (5 : ℝ) ^ 35 + 7232 with hC_E
  set C_H : ℝ := 156 ^ 2 * 8 * (10 * Real.pi * Real.exp 1 + 20 * Real.pi) with hC_H
  have hCH0 : 0 < C_H := by positivity
  -- logarithmic-scale facts
  have hLfacts : ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧ C_N * L ^ (-(ε / 5)) ≤ L ^ (-(ε / 10)) / 2 ∧
      C_H * L ^ (1 + ε / 10) ≤ L ^ a₀ ∧ 3 * L ^ (11 / 10 : ℝ) ≤ L ^ (6 / 5 : ℝ) ∧
      6 * L ^ (11 / 10 : ℝ) ≤ L ^ (2 : ℝ) ∧ c * L ^ ((1 : ℝ) / 2) ≤ L := by
    have h1 := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε / 10)).eventually_ge_atTop (2 * C_N)
    have h2 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < a₀ - 1 - ε / 10)).eventually_ge_atTop C_H
    have h3 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop 6
    have h4 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop c
    filter_upwards [h1, h2, h3, h4, Filter.eventually_ge_atTop (1 : ℝ)] with L h1 h2 h3 h4 hL1
    have hL0 : 0 < L := by linarith
    refine ⟨hL1, ?_, ?_, ?_, ?_, ?_⟩
    · have hs : L ^ (-(ε / 5)) * L ^ (ε / 10) = L ^ (-(ε / 10)) := by
        rw [← Real.rpow_add hL0]; ring_nf
      have hp : 0 < L ^ (-(ε / 5)) := by positivity
      calc C_N * L ^ (-(ε / 5)) = (2 * C_N) * L ^ (-(ε / 5)) / 2 := by ring
        _ ≤ L ^ (ε / 10) * L ^ (-(ε / 5)) / 2 := by gcongr
        _ = L ^ (-(ε / 10)) / 2 := by rw [mul_comm, hs]
    · have hs : L ^ (a₀ - 1 - ε / 10) * L ^ (1 + ε / 10) = L ^ a₀ := by
        rw [← Real.rpow_add hL0]; ring_nf
      calc C_H * L ^ (1 + ε / 10) ≤ L ^ (a₀ - 1 - ε / 10) * L ^ (1 + ε / 10) := by gcongr
        _ = L ^ a₀ := hs
    · have hs : L ^ (1 / 10 : ℝ) * L ^ (11 / 10 : ℝ) = L ^ (6 / 5 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      calc 3 * L ^ (11 / 10 : ℝ) ≤ L ^ (1 / 10 : ℝ) * L ^ (11 / 10 : ℝ) := by
            have : (3 : ℝ) ≤ L ^ (1 / 10 : ℝ) := by linarith
            gcongr
        _ = L ^ (6 / 5 : ℝ) := hs
    · have hs : L ^ (9 / 10 : ℝ) * L ^ (11 / 10 : ℝ) = L ^ (2 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      have h9 : L ^ (1 / 10 : ℝ) ≤ L ^ (9 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      calc 6 * L ^ (11 / 10 : ℝ) ≤ L ^ (9 / 10 : ℝ) * L ^ (11 / 10 : ℝ) := by
            have : (6 : ℝ) ≤ L ^ (9 / 10 : ℝ) := by linarith
            gcongr
        _ = L ^ (2 : ℝ) := hs
    · have hsq : L = L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hL0]; norm_num
      have hr0 : 0 ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
      calc c * L ^ ((1 : ℝ) / 2) ≤ L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h4 hr0
        _ = L := hsq.symm
  filter_upwards [eventually_proposition22Source_setIntegral_le hDI hW (by omega : 1 ≤ A) ha₀ hε hε1 hc,
    eventually_nonempty_mtProposition22Decomposition A hA hε (by linarith),
    hNev, Real.tendsto_log_atTop.eventually (eventually_family_budget_log (K := C_E) (ε := ε) (by positivity)
      hA (by linarith)),
    Real.tendsto_log_atTop.eventually hLfacts,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).eventually_ge_atTop 5,
    eventually_polylog_le_rpow 2 (C := 7) (κ := 2 / 11) (by norm_num) (by norm_num),
    Filter.eventually_gt_atTop (1 : ℝ)] with X hU hdec hN hbud hLX h11 hpoly hX1
  intro a P B ha₀a ha11 hPa hP3 hBiff Y hYlo hYhi hXPY T hT
  obtain ⟨hL1, hCNL, hCHL, h65, h2L, hcL⟩ := hLX
  obtain ⟨dec⟩ := hdec Y hYlo hYhi
  have hX0 : 0 < X := by linarith
  set L := Real.log X with hLdef
  have hL0 : 0 < L := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hLP : L ≤ P := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ a := Real.rpow_le_rpow_of_exponent_le hL1 ha1
      _ ≤ P := hPa
  have hP1 : 1 ≤ P := le_trans hL1 hLP
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => ((hBiff p).1 hp).1
  have hBr : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P := fun p hp => ((hBiff p).1 hp).2
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hYlo.le
  have hY1 : 1 ≤ Y := by exact_mod_cast (show (1 : ℝ) ≤ Y by
    have := Real.one_le_rpow hX1.le (by linarith : (0 : ℝ) ≤ 1 - ε / 100); linarith)
  have hYX : (Y : ℝ) ≤ X := by linarith
  have hY99 : X ^ (99 / 100 : ℝ) ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)) hYlo.le
  -- the Harman polynomial
  set G : ℝ → ℂ := fun t => LSeries (fun n => mtHarmanProposition22SourceAF (mtProposition22ZNat X)
    (mtProposition22QNat X) (mtProposition22DNat X ε) (mtProposition22ENat X ε) Y n)
    (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) with hG
  have hsuppG : ∀ n, mtHarmanProposition22SourceAF (mtProposition22ZNat X) (mtProposition22QNat X)
      (mtProposition22DNat X ε) (mtProposition22ENat X ε) Y n ≠ 0 → n ∈ Finset.Icc 1 (4 * Y) := by
    intro n hn
    obtain ⟨hn0, -, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hn
    exact Finset.mem_Icc.2 ⟨hn0, by exact_mod_cast (show (n : ℝ) ≤ ((4 * Y : ℕ) : ℝ) by
      push_cast; exact hhi)⟩
  have hGc : Continuous G := continuous_LSeries_one_line_of_support hsuppG
  -- `z`-facts for the product mean value
  have hL24 : L ≤ 1 + Real.log (24 * X) := by
    rw [hLdef, Real.log_mul (by norm_num) hX0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have h6L : 7 * L ^ (11 / 10 : ℝ) ≤ X ^ (2 / 11 : ℝ) := by
    have h2 : L ^ (2 : ℝ) ≤ (1 + Real.log (24 * X)) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ hL0.le hL24 2
    have h11' : L ^ (11 / 10 : ℝ) ≤ L ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have : 7 * (1 + Real.log (24 * X)) ^ 2 ≤ X ^ (2 / 11 : ℝ) := hpoly
    linarith only [h2, h11', this]
  obtain ⟨hz2, hBz, hz6⟩ := mtProposition22ZNat_facts (L := L ^ (11 / 10 : ℝ)) hX1 h11
    (by linarith only [hP3]) h6L hBr hYX
  have hz6' : 4 * Y < mtProposition22ZNat X ^ 6 := by exact_mod_cast hz6
  have hT₀X : Real.exp (c * L ^ ((1 : ℝ) / 2)) ≤ X := by
    calc Real.exp (c * L ^ ((1 : ℝ) / 2)) ≤ Real.exp L := Real.exp_le_exp.2 hcL
      _ = X := Real.exp_log hX0
  have hXY : X / L ^ 2 ≤ Y := by
    have hL2 : (L : ℝ) ^ 2 = L ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [div_le_iff₀ (by positivity), hL2]
    have h2P : 2 * P ≤ L ^ (2 : ℝ) := by linarith only [hP3, h2L]
    nlinarith
  have hPL65 : P ≤ L ^ (6 / 5 : ℝ) := by linarith only [hP3, h65]
  have hBU4 := largeAmplifier_budget_of_family hbud dec.family_card hY0 hXPY (by linarith only [hP3])
    hL0 (by positivity)
  exact harmanProduct_meanSquare_core hBp hP1 hBr hGc hX0 hX1.le (Real.exp_pos _) hT₀X hT hL1 hLP
    hY0 hXPY hε hC_N.le hCNL (hCHL.trans (Real.rpow_le_rpow_of_exponent_le hL1 ha₀a |>.trans hPa))
    hC_H (fun U hUm hUsub hS => hU a P B ha₀a ha11 hPa hPL65 hBiff Y hXY hYX dec U hUm hUsub hS)
    hBU4 (hN _ _ _ Y hY99 hYX (min T X) (le_min hT hX1.le) (min_le_right _ _))
    (fun _ => integral_normSq_primeSet_mul_harmanSource_le hBp hP1 hBr hz2 hBz hY1 hz6' hT)

end

end RHTower.Sieve
