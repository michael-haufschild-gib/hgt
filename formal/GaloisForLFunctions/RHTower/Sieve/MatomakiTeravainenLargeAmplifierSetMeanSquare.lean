import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeI_IIMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22PaperAssembly

/-!
# The large-amplifier part of Matomäki–Teräväinen (5.2)

On the set `U` where the prime polynomial is `≥ P^{-ε/10}`, the Proposition-2.2 source
`ρ⁻(n) 1_{(Y/2, 4Y]}` splits into `|F| ≤ exp((log log X)^5)` pieces and an error.  Every piece is of
Type I, I/II or II and has one-line mean square `≤ exp(-(log X)^{1/40})` over `U` (§5.1–§5.3,
given the Deshouillers–Iwaniec and Watt twisted fourth moments); the error has mean square
`≪ (1 + X/Y)(log X)^{-A}` by the mean value theorem.  Hence
`∫_U |P(1+it)|² ≤ 2|F|² exp(-(log X)^{1/40}) + 2 C_E (20πe + 40πX/Y)(log X)^{-A}`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter

noncomputable section

/-- A product of two finitely supported arithmetic functions is finitely supported. -/
theorem mul_support_Icc {F G : ArithmeticFunction ℂ} {MF MG : ℕ}
    (hF : ∀ n, F n ≠ 0 → n ∈ Finset.Icc 1 MF) (hG : ∀ n, G n ≠ 0 → n ∈ Finset.Icc 1 MG) :
    ∀ n, (F * G) n ≠ 0 → n ∈ Finset.Icc 1 (MF * MG) := by
  intro n hn
  have h : LSeries.convolution (fun n => F n) (fun n => G n) n ≠ 0 := by
    rw [← arithmeticFunction_mul_eq_lseriesConvolution]; exact hn
  exact convolution_mem_Icc_of_support_mul hF hG h

/-- The Type-I piece on the one-line is the product of its two factors. -/
theorem MTTypeIPieceData.LSeries_eq {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε) (t : ℝ) :
    LSeries (fun n => data.pieceAF n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      mtTypeIShortFactor data t * mtTypeILongFactor data t := by
  have hsupp : ∀ n, data.pieceAF n ≠ 0 →
      n ∈ Finset.Icc 1 (⌈2 * data.M₁⌉₊ * ⌈(1 + δ) * data.M₂⌉₊) :=
    mul_support_Icc (mtRealIntervalAF_support_nat data.α data.M₁ (2 * data.M₁))
      (mtRealIntervalAF_support_nat (fun _ => (1 : ℂ)) data.M₂ ((1 + δ) * data.M₂))
  rw [← perronPoly_eq_LSeries_of_support hsupp]
  exact MTTypeIPieceData.perronPoly_factorization data 1 t

/-- The Type-I/II piece on the one-line is the product of its three factors. -/
theorem MTTypeI_II_PieceData.LSeries_eq {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε)
    (t : ℝ) :
    LSeries (fun n => data.pieceAF n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      mtTypeI_IIShortFactor data t * mtTypeI_IITwistFactor data t * mtTypeI_IILongFactor data t := by
  have hsupp : ∀ n, data.pieceAF n ≠ 0 →
      n ∈ Finset.Icc 1 (⌈2 * data.M₁⌉₊ * ⌈2 * data.M₂⌉₊ * ⌈(1 + δ) * data.M₃⌉₊) :=
    mul_support_Icc (mul_support_Icc
      (mtRealIntervalAF_support_nat data.α data.M₁ (2 * data.M₁))
      (mtRealIntervalAF_support_nat data.β data.M₂ (2 * data.M₂)))
      (mtRealIntervalAF_support_nat (fun _ => (1 : ℂ)) data.M₃ ((1 + δ) * data.M₃))
  rw [← perronPoly_eq_LSeries_of_support hsupp]
  exact MTTypeI_II_PieceData.perronPoly_factorization data 1 t

/-- The Type-II piece on the one-line is the product of its two factors. -/
theorem MTTypeIIPieceData.LSeries_eq {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (t : ℝ) :
    LSeries (fun n => data.pieceAF n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t := by
  have hsupp : ∀ n, data.pieceAF n ≠ 0 →
      n ∈ Finset.Icc 1 (⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ * ⌈2 * data.M₂⌉₊) :=
    mul_support_Icc
      (mtRealIntervalAF_support_nat (mtTypeIIPrimeCoefficient data.indices data.block) data.M₁
        ((1 + δ) ^ data.indices.card * data.M₁))
      (mtRealIntervalAF_support_nat data.β data.M₂ (2 * data.M₂))
  rw [← perronPoly_eq_LSeries_of_support hsupp]
  exact MTTypeIIPieceData.perronPoly_factorization data 1 t

/-- Every Proposition-2.2 piece is finitely supported. -/
theorem MTUniformProposition22Piece.exists_support {K : ℕ} {X Y z₀ z δ ε : ℝ}
    {f : ArithmeticFunction ℂ} (hf : MTUniformProposition22Piece K X Y z₀ z δ ε f) :
    ∃ L : ℕ, ∀ n, f n ≠ 0 → n ∈ Finset.Icc 1 L := by
  cases hf with
  | typeI data _ =>
      exact ⟨_, mul_support_Icc (mtRealIntervalAF_support_nat data.α data.M₁ (2 * data.M₁))
        (mtRealIntervalAF_support_nat (fun _ => (1 : ℂ)) data.M₂ ((1 + δ) * data.M₂))⟩
  | typeI_II data _ _ =>
      exact ⟨_, mul_support_Icc (mul_support_Icc
        (mtRealIntervalAF_support_nat data.α data.M₁ (2 * data.M₁))
        (mtRealIntervalAF_support_nat data.β data.M₂ (2 * data.M₂)))
        (mtRealIntervalAF_support_nat (fun _ => (1 : ℂ)) data.M₃ ((1 + δ) * data.M₃))⟩
  | typeII data _ _ =>
      exact ⟨_, mul_support_Icc
        (mtRealIntervalAF_support_nat (mtTypeIIPrimeCoefficient data.indices data.block) data.M₁
          ((1 + δ) ^ data.indices.card * data.M₁))
        (mtRealIntervalAF_support_nat data.β data.M₂ (2 * data.M₂))⟩

/-- The one-line value of a finitely supported coefficient is continuous in the height. -/
theorem continuous_LSeries_one_line_of_support {f : ℕ → ℂ} {L : ℕ}
    (hf : ∀ n, f n ≠ 0 → n ∈ Finset.Icc 1 L) :
    Continuous fun t : ℝ => LSeries f (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) := by
  have h : (fun t : ℝ => LSeries f (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) =
      fun t => perronPoly f L 1 t := funext fun t => (perronPoly_eq_LSeries_of_support hf 1 t).symm
  rw [h]; exact continuous_perronPoly _ _ 1

/-- **Every Proposition-2.2 piece satisfies (5.3)**, given Deshouillers–Iwaniec and Watt. -/
theorem eventually_proposition22Piece_setIntegral_le (hDI : MTDeshouillersIwaniecBound)
    (hW : MTWattBound) {a₀ ε c : ℝ} {A : ℕ} (hA : 1 ≤ A) (ha₀ : 10999 / 10000 ≤ a₀)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ (a P : ℝ) (B : Finset ℕ), a₀ ≤ a → a ≤ 11 / 10 →
      Real.log X ^ a ≤ P → P ≤ Real.log X ^ (6 / 5 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ {Y : ℝ} (f : ArithmeticFunction ℂ),
      MTUniformProposition22Piece 5 X Y (mtLowerCutoff X) (mtProposition22ZReal X)
        (mtPaperWidth A X) ε f →
      X / Real.log X ^ 2 ≤ Y → Y ≤ X →
      ∀ U : Set ℝ, MeasurableSet U →
        U ⊆ Set.Icc (Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))) X →
        (∀ t ∈ U, P ^ (-ε / 10) ≤
          ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
        ∫ t in U, ‖LSeries (fun n => f n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  filter_upwards [eventually_typeI_setIntegral_le hDI hA ha₀ hε1 hε le_rfl hc,
    eventually_typeI_II_setIntegral_le hW hA ha₀ hε hε1 le_rfl hc,
    eventually_typeII_setIntegral_le hA ha₀ hε hε1 hε le_rfl hc] with X hI hI_II hII
  intro a P B ha₀a ha11 hPa hP65 hBiff Y f hf hYlo hYhi U hU hUsub hS
  cases hf with
  | typeI data hα =>
      simp_rw [MTTypeIPieceData.LSeries_eq]
      exact hI a P B ha₀a hPa hP65 hBiff data hα hYlo U hU hUsub hS
  | typeI_II data hα hβ =>
      simp_rw [MTTypeI_II_PieceData.LSeries_eq]
      exact hI_II a P B ha₀a hPa hP65 hBiff data hα hβ hYlo U hU hUsub hS
  | typeII data hprime hβ =>
      simp_rw [MTTypeIIPieceData.LSeries_eq]
      exact hII a P B ha₀a ha11 hPa hP65 hBiff data hprime hβ hYlo hYhi U hU hUsub hS

/-- `‖∑ x_i + e‖² ≤ 2|S| ∑ ‖x_i‖² + 2‖e‖²`. -/
theorem norm_sum_add_sq_le {ι : Type*} (S : Finset ι) (x : ι → ℂ) (e : ℂ) :
    ‖∑ i ∈ S, x i + e‖ ^ 2 ≤ 2 * S.card * ∑ i ∈ S, ‖x i‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
  have h1 : ‖∑ i ∈ S, x i‖ ≤ ∑ i ∈ S, ‖x i‖ := norm_sum_le _ _
  have h2 : (∑ i ∈ S, ‖x i‖) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖x i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have h3 : ‖∑ i ∈ S, x i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖x i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have h4 : ‖∑ i ∈ S, x i + e‖ ≤ ‖∑ i ∈ S, x i‖ + ‖e‖ := norm_add_le _ _
  have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  nlinarith [sq_nonneg (‖∑ i ∈ S, x i‖ - ‖e‖)]

/-- The Proposition-2.2 error has one-line mean square `≤ C_E (20πe + 40πT/Y)(log X)^{-A}` on
`[-T, T]`. -/
theorem integral_LSeries_proposition22_error_le {A : ℕ} {X ε T : ℝ} {Y : ℕ}
    (dec : MTProposition22Decomposition A X ε Y) (hY : 0 < Y) (hT : 1 ≤ T) :
    ∫ t in Set.Icc (-T) T,
        ‖LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
      ((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) * (20 * Real.pi * Real.exp 1 + 40 * Real.pi * T / Y) *
        (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hsupp : ∀ n, dec.error n ≠ 0 → n ∈ Finset.Icc 1 (8 * Y) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := dec.error_support hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hlo
    refine Finset.mem_Icc.2 ⟨by exact_mod_cast hn0, ?_⟩
    exact_mod_cast (show (n : ℝ) ≤ ((8 * Y : ℕ) : ℝ) by push_cast; exact hhi)
  have hval : ∀ t : ℝ, LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      perronPoly (fun n => dec.error n) (8 * Y) 1 t := fun t =>
    (perronPoly_eq_LSeries_of_support hsupp 1 t).symm
  simp_rw [hval]
  have hMVT := integral_normSq_perronPoly_le_of_lower_support (fun n => dec.error n) (8 * Y)
    (N₀ := (Y : ℝ) / 4) (by positivity) hT (fun n hn => (dec.error_support hn).1)
  refine hMVT.trans ?_
  have hE := dec.error_mean_square
  have hpre : 0 ≤ 5 * Real.pi * Real.exp 1 / ((Y : ℝ) / 4) + 5 * Real.pi / 2 * T / ((Y : ℝ) / 4) ^ 2 := by
    have : 0 ≤ T := by linarith
    positivity
  calc (5 * Real.pi * Real.exp 1 / ((Y : ℝ) / 4) + 5 * Real.pi / 2 * T / ((Y : ℝ) / 4) ^ 2) *
        ∑ n ∈ Finset.Icc 1 (8 * Y), ‖dec.error n‖ ^ 2
      ≤ (5 * Real.pi * Real.exp 1 / ((Y : ℝ) / 4) + 5 * Real.pi / 2 * T / ((Y : ℝ) / 4) ^ 2) *
          (((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) * (Y : ℝ) * (Real.log X) ^ (-((A : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hE hpre
    _ = _ := by field_simp; ring

/-- **The `U`-part of (5.2).**  For the Proposition-2.2 source at `Y`, the one-line mean square over
`U` is at most `2|F|² exp(-(log X)^{1/40}) + 2 C_E (20πe + 40πX/Y)(log X)^{-A}`, given
Deshouillers–Iwaniec and Watt. -/
theorem eventually_proposition22Source_setIntegral_le (hDI : MTDeshouillersIwaniecBound)
    (hW : MTWattBound) {a₀ ε c : ℝ} {A : ℕ} (hA : 1 ≤ A) (ha₀ : 10999 / 10000 ≤ a₀)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ (a P : ℝ) (B : Finset ℕ), a₀ ≤ a → a ≤ 11 / 10 →
      Real.log X ^ a ≤ P → P ≤ Real.log X ^ (6 / 5 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ (Y : ℕ), X / Real.log X ^ 2 ≤ Y → (Y : ℝ) ≤ X →
      ∀ (dec : MTProposition22Decomposition A X ε Y) (U : Set ℝ), MeasurableSet U →
        U ⊆ Set.Icc (Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))) X →
        (∀ t ∈ U, P ^ (-ε / 10) ≤
          ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
        ∫ t in U, ‖LSeries (fun n => mtHarmanProposition22SourceAF (mtProposition22ZNat X)
            (mtProposition22QNat X) (mtProposition22DNat X ε) (mtProposition22ENat X ε) Y n)
            (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          2 * (dec.indexSet.card : ℝ) ^ 2 * Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) +
            2 * (((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) *
              (20 * Real.pi * Real.exp 1 + 40 * Real.pi * X / Y) *
              (Real.log X) ^ (-((A : ℕ) : ℝ))) := by
  filter_upwards [eventually_proposition22Piece_setIntegral_le hDI hW hA ha₀ hε hε1 hc,
    eventually_ge_atTop (3 : ℝ)] with X hpiece hX3
  intro a P B ha₀a ha11 hPa hP65 hBiff Y hYlo hYhi dec U hU hUsub hS
  classical
  have hX1 : 1 ≤ X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hY : 0 < Y := by
    have h1 : (0 : ℝ) < X / Real.log X ^ 2 := by positivity
    exact_mod_cast h1.trans_le hYlo
  -- supports
  have hsupp : ∀ i ∈ dec.indexSet, ∃ L : ℕ, ∀ n, dec.piece i n ≠ 0 → n ∈ Finset.Icc 1 L :=
    fun i hi => (dec.piece_shape i hi).exists_support
  choose L hL using hsupp
  have herr : ∀ n, dec.error n ≠ 0 → n ∈ Finset.Icc 1 (8 * Y) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := dec.error_support hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hlo
    refine Finset.mem_Icc.2 ⟨by exact_mod_cast hn0, ?_⟩
    exact_mod_cast (show (n : ℝ) ≤ ((8 * Y : ℕ) : ℝ) by push_cast; exact hhi)
  -- the source splits on the one-line
  have hsplit : ∀ t : ℝ, LSeries (fun n => mtHarmanProposition22SourceAF (mtProposition22ZNat X)
      (mtProposition22QNat X) (mtProposition22DNat X ε) (mtProposition22ENat X ε) Y n)
      (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      ∑ i ∈ dec.indexSet, LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) +
        LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) := by
    intro t
    rw [dec.identity]
    have hfun : (fun n => (∑ i ∈ dec.indexSet, dec.piece i + dec.error) n) =
        (∑ i ∈ dec.indexSet, fun n => dec.piece i n) + fun n => dec.error n := by
      funext n
      rw [ArithmeticFunction.add_apply, arithmeticFunction_finset_sum_apply, Pi.add_apply,
        Finset.sum_apply]
    rw [hfun, LSeries_add, LSeries_sum]
    · exact fun i hi => LSeriesSummable_of_support (hL i hi) _
    · exact LSeriesSummable.sum fun i hi => LSeriesSummable_of_support (hL i hi) _
    · exact LSeriesSummable_of_support herr _
  simp_rw [hsplit]
  -- integrability
  have hUI : U ⊆ Set.Icc (-X) X := fun t ht =>
    ⟨by linarith [(hUsub ht).1, Real.exp_pos (c * Real.log X ^ ((1 : ℝ) / 2))], (hUsub ht).2⟩
  have hcont : ∀ i ∈ dec.indexSet, Continuous fun t : ℝ =>
      ‖LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 :=
    fun i hi => (continuous_LSeries_one_line_of_support (hL i hi)).norm.pow 2
  have hconte : Continuous fun t : ℝ =>
      ‖LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 :=
    (continuous_LSeries_one_line_of_support herr).norm.pow 2
  have hintI : ∀ i ∈ dec.indexSet, IntegrableOn (fun t : ℝ =>
      ‖LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) U :=
    fun i hi => ((hcont i hi).integrableOn_Icc).mono_set hUI
  have hinte : IntegrableOn (fun t : ℝ =>
      ‖LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) U :=
    hconte.integrableOn_Icc.mono_set hUI
  have hsumint : IntegrableOn (fun t : ℝ => ∑ i ∈ dec.indexSet,
      ‖LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) U :=
    integrable_finsetSum _ hintI
  have hbound : ∫ t in U, ‖∑ i ∈ dec.indexSet,
        LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) +
        LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
      ∫ t in U, (2 * dec.indexSet.card * ∑ i ∈ dec.indexSet,
        ‖LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 +
        2 * ‖LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity)
      ((hsumint.const_mul _).add (hinte.const_mul _))
      (Filter.Eventually.of_forall fun t => norm_sum_add_sq_le _ _ _)
  refine hbound.trans ?_
  rw [integral_add (hsumint.const_mul _) (hinte.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ hintI]
  have hpieces : ∑ i ∈ dec.indexSet, ∫ t in U,
      ‖LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
      dec.indexSet.card * Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
    have h := Finset.sum_le_sum fun i hi => hpiece a P B ha₀a ha11 hPa hP65 hBiff (dec.piece i)
      (dec.piece_shape i hi) hYlo hYhi U hU hUsub hS
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  have herrU : ∫ t in U, ‖LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
      ((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) * (20 * Real.pi * Real.exp 1 + 40 * Real.pi * X / Y) *
        (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
    refine le_trans ?_ (integral_LSeries_proposition22_error_le dec hY hX1)
    exact setIntegral_mono_set hconte.integrableOn_Icc
      (Filter.Eventually.of_forall fun t => by positivity) (Filter.Eventually.of_forall hUI)
  have hcard0 : (0 : ℝ) ≤ dec.indexSet.card := Nat.cast_nonneg _
  calc 2 * (dec.indexSet.card : ℝ) * (∑ i ∈ dec.indexSet, ∫ t in U,
        ‖LSeries (fun n => dec.piece i n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) +
      2 * (∫ t in U, ‖LSeries (fun n => dec.error n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
      ≤ 2 * (dec.indexSet.card : ℝ) * (dec.indexSet.card * Real.exp (-(Real.log X) ^ (1 / 40 : ℝ))) +
          2 * (((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) *
            (20 * Real.pi * Real.exp 1 + 40 * Real.pi * X / Y) *
            (Real.log X) ^ (-((A : ℕ) : ℝ))) := by gcongr
    _ = _ := by ring

end

end RHTower.Sieve
