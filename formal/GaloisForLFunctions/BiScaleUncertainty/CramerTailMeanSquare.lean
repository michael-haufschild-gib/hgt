import GaloisForLFunctions.RHTower.CramerChebyshevMeanSquare
import GaloisForLFunctions.RHTower.WeilDeletionZeroSide

/-!
# Tail mean-square bounds for the Cramér zero sum and the dyadic Chebyshev decomposition

To upgrade Cramér's dyadic mean-square bound `∫_X^{2X} (ψ(x) − x)² dx ≪ X²` to the exact asymptotic
limit `(1/M) ∫_0^M Ẽ(t)² dt → Σ_ρ m_ρ²/|ρ|²` under the Riemann hypothesis, the zero sum in the
genus-kernel window formula must be split at a height `2^{K₀}` into a finite low-ordinate sum and a
high-ordinate tail.

This module establishes three inputs for that split:

* **Equivalence of zero configurations** (`xiDivisorSupportEquivCarrier`): the support of the global
  `ξ`-divisor is in canonical bijection with Zeta23's nontrivial zero carrier, preserving
  multiplicity and the zero energy `Σ_ρ m_ρ²/|ρ|²`.
* **Geometric decay of the dyadic tail mean square** (`cramer_tail_summable_zero_energy`): on every
  dyadic block `[X, 2X]`, any absolutely convergent zero sum supported on ordinates `|γ_q| > 2^{K₀}`
  with coefficients `‖c_q‖ ≤ D/|γ_q|` satisfies
  `∫_X^{2X} ‖Σ_q c_q x^q‖² x⁻³ dx ≤ C_tail · (5/6)^{K₀} · D² / X`.
* **Dyadic Chebyshev decomposition at `r = 1`** (`dyadic_chebyshev_sq_div_le`): passing to the
  short-window limit `r → 1⁺` after isolating the low-ordinate sum `Z_low(1, x) = −Σ_{|γ_q|≤2^{K₀}} x^q/q`
  yields, for every `X ≥ 2`, `η > 0`, and `K₀ ∈ ℕ`,
  `∫_X^{2X} (ψ(x) − x)²/x² dx ≤ (1+η) ∫_X^{2X} ‖Z_low(1, x)‖²/x² dx + 3(1+1/η)(8 C_tail (5/6)^{K₀} + B₀²/X)`.
-/

open Complex Finset MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open _root_.RHTower

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Equivalence of `XiDivisorSupport` and `Zeta23.zetaZeroConfig.carrier` -/

/-- Every copy in `XiZeroCopy` lies in Zeta23's nontrivial zero carrier. -/
theorem xiZeroCopy_mem_zetaZeroCarrier (q : XiZeroCopy) : (q.1 : ℂ) ∈ 𝒵 := by
  have hre0 := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  have h0 := xiZeroCopy_ne_zero q
  have h1 := xiZeroCopy_ne_one q
  have hxi := xi_xiZeroCopy_eq_zero q
  rw [xi_eq_xiUnit_mul_zeta h0 h1 hre0] at hxi
  have hζ : riemannZeta (q.1 : ℂ) = 0 :=
    (mul_eq_zero.mp hxi).resolve_left (xiUnit_ne_zero h0 h1 hre0)
  exact ⟨hζ, hre0, hre1⟩

/-- The first copy above a support point of the `ξ`-divisor. -/
def firstCopy (ρ : XiDivisorSupport) : XiZeroCopy :=
  ⟨ρ, ⟨0, xiSupportMultiplicity_pos ρ⟩⟩

@[simp]
theorem firstCopy_fst (ρ : XiDivisorSupport) : (firstCopy ρ).1 = ρ := rfl

/-- Canonical equivalence between the support of the `ξ`-divisor and Zeta23's nontrivial zeros. -/
def xiDivisorSupportEquivCarrier : XiDivisorSupport ≃ 𝒵 where
  toFun ρ := ⟨(ρ : ℂ), xiZeroCopy_mem_zetaZeroCarrier (firstCopy ρ)⟩
  invFun ρ := RHTower.WeilDeletion.toSupport ρ
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem xiDivisorSupportEquivCarrier_coe (ρ : XiDivisorSupport) :
    ((xiDivisorSupportEquivCarrier ρ : 𝒵) : ℂ) = (ρ : ℂ) := rfl

@[simp]
theorem xiDivisorSupportEquivCarrier_symm_coe (ρ : 𝒵) :
    ((xiDivisorSupportEquivCarrier.symm ρ : XiDivisorSupport) : ℂ) = (ρ : ℂ) := rfl

theorem xiSupportMultiplicity_eq_zetaZeroMult (ρ : XiDivisorSupport) :
    xiSupportMultiplicity ρ = Zeta23.zetaZeroConfig.mult (ρ : ℂ) := by
  have h := RHTower.WeilDeletion.zeroMult_eq_xiSupportMultiplicity (xiDivisorSupportEquivCarrier ρ)
  exact h.symm

/-- Equality of the zero energy summed over `XiDivisorSupport` and over `Zeta23.zetaZeroConfig.carrier`. -/
theorem tsum_xiDivisorSupport_zeroEnergy_eq :
    (∑' ρ : XiDivisorSupport, (xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) =
      ∑' ρ : 𝒵, (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2 := by
  rw [← xiDivisorSupportEquivCarrier.tsum_eq]
  refine tsum_congr fun ρ => ?_
  rw [xiDivisorSupportEquivCarrier_coe, xiSupportMultiplicity_eq_zetaZeroMult]

/-! ## Geometric tail bound for the dyadic zero-sum mean square -/

private def tailCountConstant : ℝ := |xiLineTwoLogDerivConstant| + 20

private theorem tailCountConstant_pos : 0 < tailCountConstant := by
  dsimp [tailCountConstant]
  positivity

private theorem tail_log_bound (k : ℕ) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ 8 * (2 : ℝ) ^ (k + 1)) :
    |xiLineTwoLogDerivConstant| + 1 + Real.log s ≤
      tailCountConstant * ((k : ℝ) + 1) := by
  have hlog := Real.log_le_log hs hs'
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have h2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have h8 : Real.log 8 ≤ 8 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA := abs_nonneg xiLineTwoLogDerivConstant
  dsimp [tailCountConstant]
  push_cast at hlog
  nlinarith [mul_nonneg hk hA]

private def heightIndex (q : XiZeroCopy) : ℕ :=
  Classical.choose (exists_nat_pow_near
    (show (1 : ℝ) ≤ |zeroOrdinate q| by linarith [four_lt_abs_zeroOrdinate q])
    (by norm_num : (1 : ℝ) < 2))

private theorem heightIndex_spec (q : XiZeroCopy) :
    (2 : ℝ) ^ heightIndex q ≤ |zeroOrdinate q| ∧
      |zeroOrdinate q| < (2 : ℝ) ^ (heightIndex q + 1) :=
  Classical.choose_spec (exists_nat_pow_near
    (show (1 : ℝ) ≤ |zeroOrdinate q| by linarith [four_lt_abs_zeroOrdinate q])
    (by norm_num : (1 : ℝ) < 2))

private theorem le_heightIndex_of_not_mem_xiCopiesBelow {K₀ : ℕ} {q : XiZeroCopy}
    (hq : q ∉ xiCopiesBelow ((2 : ℝ) ^ K₀)) : K₀ ≤ heightIndex q := by
  rw [mem_xiCopiesBelow, not_le] at hq
  have hlt : (2 : ℝ) ^ K₀ < (2 : ℝ) ^ (heightIndex q + 1) :=
    hq.trans (heightIndex_spec q).2
  have hpow : K₀ < heightIndex q + 1 :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlt
  omega

private theorem tail_shell_card (F : Finset XiZeroCopy) (k : ℕ)
    (hF : ∀ q ∈ F, |zeroOrdinate q| < (2 : ℝ) ^ (k + 1)) :
    (F.card : ℝ) ≤ 80 * tailCountConstant * ((k : ℝ) + 1) * (2 : ℝ) ^ k := by
  have hsub : F ⊆ xiCopiesBelow ((2 : ℝ) ^ (k + 1)) :=
    fun q hq => mem_xiCopiesBelow.mpr (hF q hq).le
  have hc : (F.card : ℝ) ≤ (xiCopiesBelow ((2 : ℝ) ^ (k + 1))).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hcount := card_xiCopiesBelow_le_log (S := (2 : ℝ) ^ (k + 1)) (by positivity)
  have hR : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hlog := tail_log_bound k (s := (2 : ℝ) ^ (k + 1) + 6) (by positivity) (by linarith)
  have hA := le_abs_self xiLineTwoLogDerivConstant
  have hB := tailCountConstant_pos
  have hc0 : 0 ≤ xiLineTwoLogDerivConstant + Real.log ((2 : ℝ) ^ (k + 1) + 6) :=
    add_nonneg xiLineTwoLogDerivConstant_nonneg (Real.log_nonneg (by linarith))
  calc
    _ ≤ 20 * (2 ^ (k + 1) + 1) *
        (xiLineTwoLogDerivConstant + Real.log (2 ^ (k + 1) + 6)) := hc.trans hcount
    _ ≤ 20 * (2 * 2 ^ (k + 1)) * (tailCountConstant * ((k : ℝ) + 1)) := by
      gcongr <;> first | positivity | linarith
    _ = _ := by rw [pow_succ]; ring

private theorem tail_shell_row (F : Finset XiZeroCopy) (k : ℕ)
    (hF : ∀ q ∈ F, |zeroOrdinate q| < (2 : ℝ) ^ (k + 1))
    {q : XiZeroCopy} (hq : q ∈ F) :
    ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|) ≤
      32 * tailCountConstant ^ 2 * ((k : ℝ) + 1) ^ 2 := by
  have hR : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hqR := hF q hq
  have hb : ∀ q' ∈ F,
      |(q'.1 : ℂ).im - (q.1 : ℂ).im| ≤ 2 * (2 : ℝ) ^ (k + 1) := by
    intro q' hq'
    have h := abs_sub (zeroOrdinate q') (zeroOrdinate q)
    have hq'R := hF q' hq'
    change |zeroOrdinate q' - zeroOrdinate q| ≤ _
    linarith
  have h := sum_inv_one_add_abs_im_sub_le F (by positivity) hb
  have hlog₁ := tail_log_bound k (s := |zeroOrdinate q| + 2 * (2 : ℝ) ^ (k + 1) + 4)
    (by positivity) (by linarith)
  have hlog₂ := tail_log_bound k (s := 2 * (2 : ℝ) ^ (k + 1) + 1)
    (by positivity) (by linarith)
  have hA := abs_nonneg xiLineTwoLogDerivConstant
  have hB := tailCountConstant_pos
  have hL : 0 ≤ Real.log (2 * (2 : ℝ) ^ (k + 1) + 1) := Real.log_nonneg (by linarith)
  simp_rw [abs_sub_comm (q.1 : ℂ).im] at ⊢
  calc
    _ ≤ 32 * (|xiLineTwoLogDerivConstant| +
        Real.log (|zeroOrdinate q| + 2 * 2 ^ (k + 1) + 4)) *
        (1 + Real.log (2 * 2 ^ (k + 1) + 1)) := h
    _ ≤ 32 * (tailCountConstant * ((k : ℝ) + 1)) *
        (tailCountConstant * ((k : ℝ) + 1)) := by
      gcongr <;> first | positivity | linarith
    _ = _ := by ring

private theorem tail_shell_energy (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 0 < X) (hD : 0 ≤ D) (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ) (k : ℕ)
    (hF : ∀ q ∈ F, heightIndex q = k)
    (hc : ∀ q ∈ F, ‖c q‖ ≤ D / |zeroOrdinate q|) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      10240 * tailCountConstant ^ 3 * D ^ 2 / X *
        (((k : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ k) := by
  have hlo : ∀ q ∈ F, (2 : ℝ) ^ k ≤ |zeroOrdinate q| := by
    intro q hq
    simpa only [hF q hq] using (heightIndex_spec q).1
  have hhi : ∀ q ∈ F, |zeroOrdinate q| < (2 : ℝ) ^ (k + 1) := by
    intro q hq
    simpa only [hF q hq] using (heightIndex_spec q).2
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hcb : ∀ q ∈ F, ‖c q‖ ^ 2 ≤ D ^ 2 / ((2 : ℝ) ^ k) ^ 2 := by
    intro q hq
    have h := (hc q hq).trans (div_le_div_of_nonneg_left hD hpow (hlo q hq))
    simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hmean := integral_norm_sq_zeroSum_div_cube_le hX F c
    (fun q hq => tail_shell_row F k hhi hq)
  have he : ∀ q : XiZeroCopy, X ^ (2 * (q.1 : ℂ).re - 2) = X⁻¹ := by
    intro q
    rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
    norm_num [Real.rpow_neg_one]
  simp_rw [he] at hmean
  have hsum : ∑ q ∈ F, ‖c q‖ ^ 2 * X⁻¹ ≤
      (80 * tailCountConstant * ((k : ℝ) + 1) * (2 : ℝ) ^ k) *
        (D ^ 2 / ((2 : ℝ) ^ k) ^ 2 * X⁻¹) := by
    calc
      _ ≤ ∑ q ∈ F, D ^ 2 / ((2 : ℝ) ^ k) ^ 2 * X⁻¹ := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_right (hcb q hq) (inv_nonneg.mpr hX.le)
      _ = (F.card : ℝ) * (D ^ 2 / ((2 : ℝ) ^ k) ^ 2 * X⁻¹) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (tail_shell_card F k hhi) (by positivity)
  refine hmean.trans ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_)
  rw [div_pow, one_pow]
  field_simp
  ring

private theorem summable_tail_shell_budget :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 3 * (4 / 5 : ℝ) ^ k) := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 (r := 4 / 5) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 4 / 5) (by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 4 / 5) (by norm_num)
  have h3 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 (r := 4 / 5) (by norm_num)
  apply (h3.add ((h2.mul_left 3).add ((h1.mul_left 3).add h0))).congr
  intro k
  ring

private theorem tail_sum_continuous {X : ℝ} (hX : 0 < X)
    (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ) :
    ContinuousOn (fun x : ℝ =>
      ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) (uIcc X (2 * X)) := by
  have hx : ∀ x ∈ uIcc X (2 * X), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact hX.trans_le hx.1
  apply ContinuousOn.div _ (continuousOn_id.pow 3) (fun x h => pow_ne_zero _ (hx x h).ne')
  apply ContinuousOn.pow _ 2
  apply ContinuousOn.norm
  apply continuousOn_finsetSum
  intro q _
  apply continuousOn_const.mul
  apply continuousOn_of_forall_continuousAt
  intro x h
  exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hx x h).ne')

/-- Universal constant governing the dyadic tail mean square of critical-line zero sums. -/
def cramerTailEnergyConstant : ℝ :=
  40960 * tailCountConstant ^ 3 *
    ∑' k : ℕ, ((k : ℝ) + 1) ^ 3 * (4 / 5 : ℝ) ^ k

theorem cramerTailEnergyConstant_nonneg : 0 ≤ cramerTailEnergyConstant := by
  unfold cramerTailEnergyConstant
  have := tailCountConstant_pos
  positivity

/-- Finite high-ordinate zero sums over `q ∉ xiCopiesBelow (2^{K₀})` decay like `(5/6)^{K₀}`. -/
theorem cramer_tail_finite_zero_energy (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 0 < X) (hD : 0 ≤ D) (K₀ : ℕ) (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ)
    (hK₀ : ∀ q ∈ F, q ∉ xiCopiesBelow ((2 : ℝ) ^ K₀))
    (hc : ∀ q ∈ F, ‖c q‖ ≤ D / |zeroOrdinate q|) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * D ^ 2 / X := by
  classical
  let S := F.image heightIndex
  let Fk (k : ℕ) := F.filter (fun q => heightIndex q = k)
  let H (k : ℕ) (x : ℝ) := ∑ q ∈ Fk k, c q * (x : ℂ) ^ (q.1 : ℂ)
  have hsplit (x : ℝ) : (∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)) = ∑ k ∈ S, H k x :=
    (Finset.sum_fiberwise_of_maps_to
      (fun q hq => Finset.mem_image_of_mem _ hq)
      (fun q => c q * (x : ℂ) ^ (q.1 : ℂ))).symm
  have hweights : ∑ k ∈ S, (3 / 4 : ℝ) ^ k ≤ 4 := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    calc
      _ ≤ ∑' k : ℕ, (3 / 4 : ℝ) ^ k := hs.sum_le_tsum S (by intros; positivity)
      _ = 4 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hpt (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
        4 * ∑ k ∈ S, (‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k := by
    have hx0 := hX.trans_le hx.1
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (f := fun k => (3 / 4 : ℝ) ^ k)
      (g := fun k => ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k)
      (r := fun k => ‖H k x‖)
      (by intros; positivity) (by intros; positivity)
      (fun k _ => by rw [mul_div_cancel₀ _ (by positivity)])
    have hs0 : 0 ≤ ∑ k ∈ S, ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k := by positivity
    have hn : ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 ≤
        4 * ∑ k ∈ S, ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k := by
      rw [hsplit]
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S (fun k => H k x)) 2).trans
        (hcs.trans (mul_le_mul_of_nonneg_right hweights hs0))
    calc
      _ ≤ (4 * ∑ k ∈ S, ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k) / x ^ 3 :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ = _ := by
        simp only [mul_div_assoc, Finset.sum_div]
        congr 1; apply Finset.sum_congr rfl; intros; ring
  have hi (k : ℕ) : IntervalIntegrable
      (fun x : ℝ => (‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k) volume X (2 * X) :=
    ((tail_sum_continuous hX (Fk k) c).div_const _).intervalIntegrable
  have hE (k : ℕ) (hk : k ∈ S) :
      (∫ x in X..2 * X, ‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k ≤
        10240 * tailCountConstant ^ 3 * D ^ 2 / X * (5 / 6 : ℝ) ^ K₀ *
          (((k : ℝ) + 1) ^ 3 * (4 / 5 : ℝ) ^ k) := by
    obtain ⟨q, hqF, rfl⟩ := Finset.mem_image.mp hk
    have hKle : K₀ ≤ heightIndex q := le_heightIndex_of_not_mem_xiCopiesBelow (hK₀ q hqF)
    have hpow56 : (5 / 6 : ℝ) ^ heightIndex q ≤ (5 / 6 : ℝ) ^ K₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hKle
    have hfac : (2 / 3 : ℝ) ^ heightIndex q ≤
        (5 / 6 : ℝ) ^ K₀ * (4 / 5 : ℝ) ^ heightIndex q := by
      calc (2 / 3 : ℝ) ^ heightIndex q
          = (5 / 6 : ℝ) ^ heightIndex q * (4 / 5 : ℝ) ^ heightIndex q := by
            rw [← mul_pow]; norm_num
        _ ≤ (5 / 6 : ℝ) ^ K₀ * (4 / 5 : ℝ) ^ heightIndex q :=
            mul_le_mul_of_nonneg_right hpow56 (by positivity)
    have h := tail_shell_energy hRH hX hD (Fk (heightIndex q)) c (heightIndex q)
      (fun q' hq' => (Finset.mem_filter.mp hq').2)
      (fun q' hq' => hc q' (Finset.mem_filter.mp hq').1)
    have h1 : (∫ x in X..2 * X, ‖H (heightIndex q) x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ heightIndex q ≤
        10240 * tailCountConstant ^ 3 * D ^ 2 / X *
          (((heightIndex q : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ heightIndex q) := by
      calc
        _ ≤ (10240 * tailCountConstant ^ 3 * D ^ 2 / X *
            (((heightIndex q : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ heightIndex q)) /
              (3 / 4 : ℝ) ^ heightIndex q :=
          div_le_div_of_nonneg_right h (by positivity)
        _ = _ := by simp only [mul_div_assoc, ← div_pow]; norm_num
    refine h1.trans ?_
    have hC0 : 0 ≤ 10240 * tailCountConstant ^ 3 * D ^ 2 / X * ((heightIndex q : ℝ) + 1) ^ 3 := by
      have := tailCountConstant_pos; positivity
    calc 10240 * tailCountConstant ^ 3 * D ^ 2 / X *
          (((heightIndex q : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ heightIndex q)
        = (10240 * tailCountConstant ^ 3 * D ^ 2 / X * ((heightIndex q : ℝ) + 1) ^ 3) *
            (2 / 3 : ℝ) ^ heightIndex q := by ring
      _ ≤ (10240 * tailCountConstant ^ 3 * D ^ 2 / X * ((heightIndex q : ℝ) + 1) ^ 3) *
            ((5 / 6 : ℝ) ^ K₀ * (4 / 5 : ℝ) ^ heightIndex q) :=
          mul_le_mul_of_nonneg_left hfac hC0
      _ = _ := by ring
  calc
    _ ≤ ∫ x in X..2 * X, 4 * ∑ k ∈ S,
        (‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k :=
      intervalIntegral.integral_mono_on (by linarith)
        (tail_sum_continuous hX F c).intervalIntegrable
        (by simpa only [Finset.sum_apply] using
          ((IntervalIntegrable.sum S (fun k _ => hi k)).const_mul 4)) hpt
    _ = 4 * ∑ k ∈ S, (∫ x in X..2 * X, ‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun k _ => hi k)]
      simp only [intervalIntegral.integral_div]
    _ ≤ 4 * ∑ k ∈ S, 10240 * tailCountConstant ^ 3 * D ^ 2 / X * (5 / 6 : ℝ) ^ K₀ *
        (((k : ℝ) + 1) ^ 3 * (4 / 5 : ℝ) ^ k) := by
      gcongr with k hk
      exact hE k hk
    _ = (40960 * tailCountConstant ^ 3 * (5 / 6 : ℝ) ^ K₀ * D ^ 2 / X) *
        ∑ k ∈ S, ((k : ℝ) + 1) ^ 3 * (4 / 5 : ℝ) ^ k := by rw [← Finset.mul_sum]; ring
    _ ≤ (40960 * tailCountConstant ^ 3 * (5 / 6 : ℝ) ^ K₀ * D ^ 2 / X) *
        ∑' k : ℕ, ((k : ℝ) + 1) ^ 3 * (4 / 5 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_left
        (summable_tail_shell_budget.sum_le_tsum S (by intros; positivity))
      have := tailCountConstant_pos
      positivity
    _ = _ := by unfold cramerTailEnergyConstant; ring

/-- **Dyadic tail mean-square bound** for an absolutely convergent zero sum vanishing on
`xiCopiesBelow (2^{K₀})`. -/
theorem cramer_tail_summable_zero_energy (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 1 ≤ X) (hD : 0 ≤ D) (K₀ : ℕ) (c : XiZeroCopy → ℂ)
    (hK₀ : ∀ q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀), c q = 0)
    (hc : ∀ q, ‖c q‖ ≤ D / |zeroOrdinate q|) (hcs : Summable (fun q => ‖c q‖)) :
    ∫ x in X..2 * X, ‖∑' q : XiZeroCopy, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * D ^ 2 / X := by
  classical
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  let B := (2 * X) * ∑' q : XiZeroCopy, ‖c q‖
  have hterm (x : ℝ) (hx : x ∈ uIcc X (2 * X)) (q : XiZeroCopy) :
      ‖c q * (x : ℂ) ^ (q.1 : ℂ)‖ ≤ (2 * X) * ‖c q‖ := by
    rw [uIcc_of_le hXX] at hx
    have hx1 : 1 ≤ x := hX.trans hx.1
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hp : x ^ (q.1 : ℂ).re ≤ 2 * X := by
      calc
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (xiZeroCopy_re_lt_one q).le
        _ = x := Real.rpow_one x
        _ ≤ _ := hx.2
    nlinarith [norm_nonneg (c q)]
  have hs (x : ℝ) (hx : x ∈ uIcc X (2 * X)) :
      Summable (fun q : XiZeroCopy => c q * (x : ℂ) ^ (q.1 : ℂ)) :=
    Summable.of_norm_bounded (hcs.mul_left (2 * X)) (hterm x hx)
  have hnorm (F : Finset XiZeroCopy) (x : ℝ) (hx : x ∈ uIcc X (2 * X)) :
      ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ≤ B := by
    calc
      _ ≤ ∑ q ∈ F, ‖c q * (x : ℂ) ^ (q.1 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ F, (2 * X) * ‖c q‖ := Finset.sum_le_sum (fun q _ => hterm x hx q)
      _ = (2 * X) * ∑ q ∈ F, ‖c q‖ := (Finset.mul_sum ..).symm
      _ ≤ B := mul_le_mul_of_nonneg_left
        (hcs.sum_le_tsum F (fun q _ => norm_nonneg _)) (by positivity)
  have ht : Tendsto (fun F : Finset XiZeroCopy =>
      ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3)
      atTop (𝓝 (∫ x in X..2 * X, ‖∑' q : XiZeroCopy,
        c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => B ^ 2 / X ^ 3)
    · exact Eventually.of_forall (fun F =>
        ((tail_sum_continuous hX0 F c).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    · apply Eventually.of_forall
      intro F
      apply ae_of_all
      intro x hx
      have hx' := uIoc_subset_uIcc hx
      have hxX : X ≤ x :=
        (show x ∈ Set.Icc X (2 * X) from by simpa only [Set.uIcc_of_le hXX] using hx').1
      have hx0 : 0 < x := hX0.trans_le hxX
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply div_le_div₀ (by positivity)
        (pow_le_pow_left₀ (norm_nonneg _) (hnorm F x hx') 2)
        (by positivity) (pow_le_pow_left₀ hX0.le hxX 3)
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro x hx
      exact ((hs x (uIoc_subset_uIcc hx)).hasSum.norm.pow 2).div_const (x ^ 3)
  refine le_of_tendsto ht (Eventually.of_forall fun F => ?_)
  have hsdiff : ∀ x : ℝ, (∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)) =
      ∑ q ∈ F \ xiCopiesBelow ((2 : ℝ) ^ K₀), c q * (x : ℂ) ^ (q.1 : ℂ) := fun x => by
    symm
    refine Finset.sum_subset sdiff_subset fun q hqF hq => ?_
    rw [Finset.mem_sdiff, not_and, not_not] at hq
    rw [hK₀ q (hq hqF), zero_mul]
  simp_rw [hsdiff]
  exact cramer_tail_finite_zero_energy hRH hX0 hD K₀ (F \ xiCopiesBelow ((2 : ℝ) ^ K₀)) c
    (fun q hq => (Finset.mem_sdiff.mp hq).2) (fun q _ => hc q)

/-! ## Short-window coefficients and the dyadic Chebyshev decomposition -/

/-- The unit-scale short-window coefficient `T(ρ; 1, r)` of a zero copy. -/
def windowCoeff (r : ℝ) (q : XiZeroCopy) : ℂ :=
  lagWindowZeroTerm (q.1 : ℂ) 1 r

/-- Uniform `2/|γ_q|` bound for `windowCoeff r q` on `1 < r ≤ 2`. -/
theorem norm_windowCoeff_le {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) (q : XiZeroCopy) :
    ‖windowCoeff r q‖ ≤ 2 / |zeroOrdinate q| := by
  have hr0 : 0 < r := by linarith
  have hw : 0 < 1 - 1 / r := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hr
  have hρ1 : (q.1 : ℂ) - 1 ≠ 0 := by
    intro h
    exact xiZeroCopy_one_sub_ne_zero q (by linear_combination -h)
  have h0 : (0 : ℝ) ∉ uIcc 1 r := by
    rw [uIcc_of_le hr.le]
    norm_num
  have hI := integral_cpow (a := 1) (b := r) (r := (q.1 : ℂ) - 2)
    (Or.inr ⟨by intro h; exact hρ1 (by linear_combination h), h0⟩)
  rw [show (q.1 : ℂ) - 2 + 1 = (q.1 : ℂ) - 1 by ring] at hI
  have hrep : (q.1 : ℂ) * windowCoeff r q =
      -(∫ t in (1 : ℝ)..r, (t : ℂ) ^ ((q.1 : ℂ) - 2)) / ((1 - 1 / r : ℝ) : ℂ) := by
    rw [hI, windowCoeff, lagWindowZeroTerm]
    norm_num
    have hρ0 := xiZeroCopy_ne_zero q
    have hρ1' := xiZeroCopy_one_sub_ne_zero q
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => 2 * t ^ (-2 : ℤ)) volume 1 r :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul 2
  have hnorm : ‖∫ t in (1 : ℝ)..r, (t : ℂ) ^ ((q.1 : ℂ) - 2)‖ ≤ 2 * (1 - 1 / r) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hr.le
      (f := fun t : ℝ => (t : ℂ) ^ ((q.1 : ℂ) - 2))
      (ae_of_all _ (fun t ht => ?_)) hint
    · simpa only [intervalIntegral.integral_const_mul,
        integral_zpow_neg_two (by norm_num : (0 : ℝ) < 1) hr.le, one_div_one] using h
    · have ht0 : 0 < t := by linarith [ht.1]
      have ht1 : 1 ≤ t := ht.1.le
      have hpow : t ^ (q.1 : ℂ).re ≤ 2 := by
        calc
          _ ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (xiZeroCopy_re_lt_one q).le
          _ = t := Real.rpow_one t
          _ ≤ 2 := ht.2.trans hr2
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re]
      change t ^ ((q.1 : ℂ).re - 2) ≤ 2 * t ^ (-2 : ℤ)
      rw [show (q.1 : ℂ).re - 2 = (q.1 : ℂ).re + (-2 : ℤ) by norm_num; ring,
        Real.rpow_add ht0, Real.rpow_intCast]
      exact mul_le_mul_of_nonneg_right hpow (zpow_nonneg ht0.le _)
  have hprod : ‖(q.1 : ℂ)‖ * ‖windowCoeff r q‖ ≤ 2 := by
    rw [← norm_mul, hrep, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr hnorm
  have hγ : 0 < |zeroOrdinate q| := by linarith [four_lt_abs_zeroOrdinate q]
  rw [le_div_iff₀ hγ]
  have him := Complex.abs_im_le_norm (q.1 : ℂ)
  change |zeroOrdinate q| ≤ ‖(q.1 : ℂ)‖ at him
  nlinarith [mul_le_mul_of_nonneg_right him (norm_nonneg (windowCoeff r q))]

/-- Uniform linear convergence `‖windowCoeff r q − (−1/q)‖ ≤ r − 1` as `r → 1⁺`. -/
theorem norm_windowCoeff_add_inv_le {r : ℝ} (hr : 1 < r) (q : XiZeroCopy) :
    ‖windowCoeff r q - (-1 / (q.1 : ℂ))‖ ≤ r - 1 := by
  have hq0 : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_ne_zero q)
  have h := norm_mul_lagWindowZeroTerm_add_cpow_le one_pos le_rfl hr
    (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
  rw [Complex.ofReal_one, Complex.one_cpow, Real.one_rpow, mul_one] at h
  have hmul : (q.1 : ℂ) * (windowCoeff r q - (-1 / (q.1 : ℂ))) =
      (q.1 : ℂ) * lagWindowZeroTerm (q.1 : ℂ) 1 r + 1 := by
    unfold windowCoeff
    have hne := xiZeroCopy_ne_zero q
    field_simp
    ring
  have hmain : ‖(q.1 : ℂ)‖ * ‖windowCoeff r q - (-1 / (q.1 : ℂ))‖ ≤ ‖(q.1 : ℂ)‖ * (r - 1) := by
    rw [← norm_mul, hmul]
    exact h
  exact le_of_mul_le_mul_left hmain hq0

theorem windowCoeff_scale {r x : ℝ} (hr : 1 < r) (hx : 0 < x) (q : XiZeroCopy) :
    lagWindowZeroTerm (q.1 : ℂ) x (r * x) = windowCoeff r q * (x : ℂ) ^ (q.1 : ℂ) := by
  have hr0 : 0 < r := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [windowCoeff, lagWindowZeroTerm, lagWindowZeroTerm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr0.le hx.le,
    Complex.cpow_sub _ _ hxC, Complex.cpow_one]
  norm_num
  field_simp

/-- The finite low-ordinate zero sum `−Σ_{q ∈ xiCopiesBelow (2^{K₀})} x^q / q` at `r = 1`. -/
def lowZeroSum (K₀ : ℕ) (x : ℝ) : ℂ :=
  ∑ q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀), (-1 / (q.1 : ℂ)) * (x : ℂ) ^ (q.1 : ℂ)

/-- The high-ordinate tail coefficient sequence vanishing on `xiCopiesBelow (2^{K₀})`. -/
def highWindowCoeff (K₀ : ℕ) (r : ℝ) (q : XiZeroCopy) : ℂ :=
  by classical exact if q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀) then 0 else windowCoeff r q

theorem summable_norm_highWindowCoeff (K₀ : ℕ) {r : ℝ} (hr : 1 < r) :
    Summable (fun q : XiZeroCopy => ‖highWindowCoeff K₀ r q‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    (summable_norm_lagWindowZeroTerm (by norm_num : (1 : ℝ) ≤ 1) hr)
  unfold highWindowCoeff windowCoeff
  split_ifs
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_rfl

theorem norm_highWindowCoeff_le (K₀ : ℕ) {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) (q : XiZeroCopy) :
    ‖highWindowCoeff K₀ r q‖ ≤ 2 / |zeroOrdinate q| := by
  unfold highWindowCoeff
  split_ifs
  · rw [norm_zero]
    have : 0 < |zeroOrdinate q| := by linarith [four_lt_abs_zeroOrdinate q]
    positivity
  · exact norm_windowCoeff_le hr hr2 q

theorem highWindowCoeff_eq_zero_of_mem {K₀ : ℕ} {r : ℝ} {q : XiZeroCopy}
    (hq : q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀)) : highWindowCoeff K₀ r q = 0 := by
  unfold highWindowCoeff
  exact if_pos hq

/-- Splitting the full window zero sum into `lowZeroSum`, the `r → 1` finite drift, and the high tail. -/
theorem tsum_windowCoeff_eq_split (K₀ : ℕ) {r x : ℝ} (hr : 1 < r) (hx : 1 ≤ x) :
    (∑' q : XiZeroCopy, windowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)) =
      lowZeroSum K₀ x +
        (∑ q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀),
          (windowCoeff r q - (-1 / (q.1 : ℂ))) * (x : ℂ) ^ (q.1 : ℂ)) +
        ∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ) := by
  classical
  set F := xiCopiesBelow ((2 : ℝ) ^ K₀)
  have hx0 : 0 < x := by linarith
  have hterm (c : XiZeroCopy → ℂ) (q : XiZeroCopy) :
      ‖c q * (x : ℂ) ^ (q.1 : ℂ)‖ ≤ x * ‖c q‖ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hp : x ^ (q.1 : ℂ).re ≤ x := by
      calc x ^ (q.1 : ℂ).re ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (xiZeroCopy_re_lt_one q).le
        _ = x := Real.rpow_one x
    nlinarith [norm_nonneg (c q)]
  have hs_full : Summable (fun q : XiZeroCopy => windowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)) :=
    Summable.of_norm_bounded
      ((summable_norm_lagWindowZeroTerm (by norm_num : (1 : ℝ) ≤ 1) hr).mul_left x)
      (hterm (windowCoeff r))
  have hs_high : Summable (fun q : XiZeroCopy => highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)) :=
    Summable.of_norm_bounded ((summable_norm_highWindowCoeff K₀ hr).mul_left x)
      (hterm (highWindowCoeff K₀ r))
  let lowInd : XiZeroCopy → ℂ := fun q => if q ∈ F then windowCoeff r q * (x : ℂ) ^ (q.1 : ℂ) else 0
  have hs_low : Summable lowInd :=
    summable_of_ne_finset_zero (s := F) fun q hq => if_neg hq
  have hpt : ∀ q : XiZeroCopy, windowCoeff r q * (x : ℂ) ^ (q.1 : ℂ) =
      lowInd q + highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ) := fun q => by
    dsimp [lowInd, highWindowCoeff, F]
    split_ifs <;> ring
  rw [tsum_congr hpt, hs_low.tsum_add hs_high]
  have hlow_eq : (∑' q : XiZeroCopy, lowInd q) =
      ∑ q ∈ F, windowCoeff r q * (x : ℂ) ^ (q.1 : ℂ) := by
    rw [tsum_eq_sum (s := F) fun q hq => if_neg hq]
    exact Finset.sum_congr rfl fun q hq => if_pos hq
  rw [hlow_eq, add_left_inj, lowZeroSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Pointwise bound on the `r → 1` drift of the finite low-ordinate zero sum. -/
theorem norm_lowZeroSum_drift_le (K₀ : ℕ) {r x : ℝ} (hr : 1 < r) (hx : 1 ≤ x) :
    ‖∑ q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀),
        (windowCoeff r q - (-1 / (q.1 : ℂ))) * (x : ℂ) ^ (q.1 : ℂ)‖ ≤
      (r - 1) * ((xiCopiesBelow ((2 : ℝ) ^ K₀)).card : ℝ) * x := by
  have hx0 : 0 < x := by linarith
  calc ‖∑ q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀),
        (windowCoeff r q - (-1 / (q.1 : ℂ))) * (x : ℂ) ^ (q.1 : ℂ)‖
      ≤ ∑ q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀),
          ‖(windowCoeff r q - (-1 / (q.1 : ℂ))) * (x : ℂ) ^ (q.1 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀), (r - 1) * x := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hp : x ^ (q.1 : ℂ).re ≤ x := by
          calc x ^ (q.1 : ℂ).re ≤ x ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hx (xiZeroCopy_re_lt_one q).le
            _ = x := Real.rpow_one x
        exact mul_le_mul (norm_windowCoeff_add_inv_le hr q) hp (by positivity) (by linarith)
    _ = (r - 1) * ((xiCopiesBelow ((2 : ℝ) ^ K₀)).card : ℝ) * x := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Trivial-zero window bound on `a ≥ 2`. -/
private theorem trivial_window_bound {a b : ℝ} (ha : 2 ≤ a) (hab : a < b) :
    0 ≤ (trivialZeroSeriesReal a / a - trivialZeroSeriesReal b / b) / (1 / a - 1 / b) ∧
    (trivialZeroSeriesReal a / a - trivialZeroSeriesReal b / b) / (1 / a - 1 / b) ≤ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  let u := 1 / a
  let v := 1 / b
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hvu : v < u := one_div_lt_one_div_of_lt ha0 hab
  have hu2 : u ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) ha
  have hw : 0 < u - v := sub_pos.mpr hvu
  have hsa : HasSum (fun k : ℕ => u ^ (2 * (k + 1) + 1) /
      (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) (trivialZeroSeriesReal a / a) := by
    refine ((summable_trivialZeroSeriesReal_term (by linarith : 1 ≤ a)).hasSum.div_const a).congr
      fun F => Finset.sum_congr rfl fun k _ => ?_
    dsimp only [u]; rw [pow_succ, one_div_pow, one_div]; ring
  have hsb : HasSum (fun k : ℕ => v ^ (2 * (k + 1) + 1) /
      (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) (trivialZeroSeriesReal b / b) := by
    refine ((summable_trivialZeroSeriesReal_term (by linarith : 1 ≤ b)).hasSum.div_const b).congr
      fun F => Finset.sum_congr rfl fun k _ => ?_
    dsimp only [v]; rw [pow_succ, one_div_pow, one_div]; ring
  have hterm (k : ℕ) :
      u ^ (2 * (k + 1) + 1) / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) -
        v ^ (2 * (k + 1) + 1) / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) ≤
          (u - v) * (1 / 4 : ℝ) ^ k := by
    have hd : 0 < 2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
    have hp := abs_pow_sub_pow_le (a := u) (b := v) (n := 2 * (k + 1) + 1)
    rw [abs_of_pos hu, abs_of_pos hv, max_eq_left hvu.le, abs_of_pos hw, Nat.add_sub_cancel] at hp
    have hpow : u ^ (2 * (k + 1)) ≤ (1 / 4 : ℝ) ^ k := by
      rw [pow_mul]
      calc (u ^ 2) ^ (k + 1) ≤ (1 / 4 : ℝ) ^ (k + 1) :=
            pow_le_pow_left₀ (sq_nonneg u) (by nlinarith) _
        _ ≤ (1 / 4 : ℝ) ^ k := by
            rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm : ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤
        2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by push_cast; nlinarith
    calc
      _ = (u ^ (2 * (k + 1) + 1) - v ^ (2 * (k + 1) + 1)) /
          (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) := by ring
      _ ≤ |u ^ (2 * (k + 1) + 1) - v ^ (2 * (k + 1) + 1)| /
          (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) :=
        div_le_div_of_nonneg_right (le_abs_self _) hd.le
      _ ≤ ((u - v) * ((2 * (k + 1) + 1 : ℕ) : ℝ) * u ^ (2 * (k + 1))) /
          (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) :=
        div_le_div_of_nonneg_right hp hd.le
      _ ≤ (u - v) * u ^ (2 * (k + 1)) := by
        rw [div_le_iff₀ hd]
        calc _ = ((u - v) * u ^ (2 * (k + 1))) * ((2 * (k + 1) + 1 : ℕ) : ℝ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hw.le
  have hgeom := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (u - v)
  have hbound : trivialZeroSeriesReal a / a - trivialZeroSeriesReal b / b ≤ 2 * (u - v) := by
    rw [← (hsa.sub hsb).tsum_eq]
    calc _ ≤ ∑' k : ℕ, (u - v) * (1 / 4 : ℝ) ^ k :=
          (hsa.sub hsb).summable.tsum_le_tsum hterm hgeom
      _ = (u - v) * (1 - (1 / 4 : ℝ))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ ≤ _ := by norm_num; linarith
  exact ⟨div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti (by linarith) hab.le)) hw.le,
    (div_le_iff₀ hw).mpr hbound⟩

private def primeWindowError (r x : ℝ) : ℝ :=
  chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) -
    Real.log ((r * x) / x) / (1 / x - 1 / (r * x))

private theorem primeWindowError_measurable (r : ℝ) : Measurable (primeWindowError r) := by
  have hL : Measurable lagPsiSum := by
    change Measurable ((fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)) ∘ (Nat.floor : ℝ → ℕ))
    exact measurable_from_nat.comp Nat.measurable_floor
  have hψ : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  unfold primeWindowError chebyshevLagWindow
  fun_prop

private theorem primeWindow_bounds {r x : ℝ} (hr : 1 < r) (hx : 0 < x) :
    Chebyshev.psi x ≤ chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) ∧
    chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) ≤ Chebyshev.psi (r * x) ∧
    x ≤ Real.log ((r * x) / x) / (1 / x - 1 / (r * x)) ∧
    Real.log ((r * x) / x) / (1 / x - 1 / (r * x)) ≤ r * x := by
  have hxr : x < r * x := by nlinarith
  have hw : 0 < 1 / x - 1 / (r * x) := sub_pos.mpr (one_div_lt_one_div_of_lt hx hxr)
  obtain ⟨h₁, h₂⟩ := chebyshevLagWindow_bounds hx hxr.le
  obtain ⟨h₃, h₄⟩ := log_div_le_mul_inv_sub hx hxr.le
  exact ⟨(le_div_iff₀ hw).mpr h₁, (div_le_iff₀ hw).mpr h₂,
    (le_div_iff₀ hw).mpr h₃, (div_le_iff₀ hw).mpr h₄⟩

private theorem primeWindowError_bound {r X x : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (hX : 0 < X) (hx : x ∈ Set.Icc X (2 * X)) :
    |primeWindowError r x| ≤ Chebyshev.psi (4 * X) + 4 * X := by
  have hx0 := hX.trans_le hx.1
  obtain ⟨h₁, _, h₃, _⟩ := primeWindow_bounds hr hx0
  have hrx : r * x ≤ 4 * X := by nlinarith [mul_le_mul_of_nonneg_right hr2 hx0.le, hx.2]
  have hψ := Chebyshev.psi_mono hrx
  have hJ0 : 0 ≤ chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) :=
    (Chebyshev.psi_nonneg x).trans h₁
  have hL0 : 0 ≤ Real.log ((r * x) / x) / (1 / x - 1 / (r * x)) := hx0.le.trans h₃
  unfold primeWindowError
  calc _ ≤ |chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x))| +
          |Real.log ((r * x) / x) / (1 / x - 1 / (r * x))| := abs_sub _ _
    _ ≤ _ := by
      obtain ⟨_, h₂, _, h₄⟩ := primeWindow_bounds hr hx0
      rw [abs_of_nonneg hJ0, abs_of_nonneg hL0]; linarith

private theorem psi_right_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun r : ℝ => Chebyshev.psi (r * x)) (𝓝[>] 1) (𝓝 (Chebyshev.psi x)) := by
  have ht : Tendsto (fun r : ℝ => r * x) (𝓝[>] 1) (𝓝 x) := by
    simpa using ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1)).mul_const x).mono_left
      nhdsWithin_le_nhds
  have hf : ∀ᶠ r : ℝ in 𝓝[>] 1, ⌊r * x⌋₊ = ⌊x⌋₊ := by
    filter_upwards [ht.eventually (gt_mem_nhds (Nat.lt_floor_add_one x)), self_mem_nhdsWithin]
      with r hr hrlow
    have hrx : x ≤ r * x := by
      simpa using mul_le_mul_of_nonneg_right (show 1 ≤ r from hrlow.le) hx.le
    apply (Nat.floor_eq_iff (hx.le.trans hrx)).mpr
    exact ⟨(Nat.floor_le hx.le).trans hrx, hr⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [hf] with r hr
  rw [Chebyshev.psi_eq_psi_coe_floor (r * x), hr, ← Chebyshev.psi_eq_psi_coe_floor x]

private theorem primeWindowError_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun r => primeWindowError r x) (𝓝[>] 1) (𝓝 (Chebyshev.psi x - x)) := by
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] 1, 1 < r := self_mem_nhdsWithin
  have hJ : Tendsto (fun r => chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)))
      (𝓝[>] 1) (𝓝 (Chebyshev.psi x)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (psi_right_limit hx)
      (hbounds.mono fun r hr => (primeWindow_bounds hr hx).1)
      (hbounds.mono fun r hr => (primeWindow_bounds hr hx).2.1)
  have ht : Tendsto (fun r : ℝ => r * x) (𝓝[>] 1) (𝓝 x) := by
    simpa using ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1)).mul_const x).mono_left
      nhdsWithin_le_nhds
  have hL : Tendsto (fun r => Real.log ((r * x) / x) / (1 / x - 1 / (r * x)))
      (𝓝[>] 1) (𝓝 x) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (hbounds.mono fun r hr => (primeWindow_bounds hr hx).2.2.1)
      (hbounds.mono fun r hr => (primeWindow_bounds hr hx).2.2.2)
  exact hJ.sub hL

/-- Weighted four-term square inequality `(a + b₁ + b₂ + b₃)² ≤ (1+η)a² + 3(1+1/η)(b₁² + b₂² + b₃²)`. -/
private theorem add_four_sq_le {η : ℝ} (hη : 0 < η) (a b₁ b₂ b₃ : ℝ) :
    (a + b₁ + b₂ + b₃) ^ 2 ≤
      (1 + η) * a ^ 2 + 3 * (1 + 1 / η) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) := by
  set b := b₁ + b₂ + b₃
  have h1 : (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := by
    have h0 : 0 ≤ (η * a - b) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
    have e : (a + b) ^ 2 = (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 - (η * a - b) ^ 2 / η := by
      field_simp; ring
    linarith
  have h2 : b ^ 2 ≤ 3 * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) := by
    dsimp [b]
    nlinarith [sq_nonneg (b₁ - b₂), sq_nonneg (b₁ - b₃), sq_nonneg (b₂ - b₃)]
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  calc (a + b₁ + b₂ + b₃) ^ 2 = (a + b) ^ 2 := by dsimp [b]; ring
    _ ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := h1
    _ ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * (3 * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 hη1)
    _ = _ := by ring

/-- Pointwise bound on `primeWindowError r x ^ 2 / x ^ 2` splitting off `lowZeroSum K₀ x`. -/
private theorem primeWindowError_sq_div_le (K₀ : ℕ) {r x η : ℝ} (hr : 1 < r) (hx : 2 ≤ x)
    (hη : 0 < η) :
    primeWindowError r x ^ 2 / x ^ 2 ≤
      (1 + η) * (‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
        3 * (1 + 1 / η) *
          (((r - 1) * ((xiCopiesBelow ((2 : ℝ) ^ K₀)).card : ℝ)) ^ 2 +
            ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2 +
            (|Real.log (2 * Real.pi)| + 2) ^ 2 / x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxr : x < r * x := by nlinarith
  let Zlow := lowZeroSum K₀ x
  let Zdrift := ∑ q ∈ xiCopiesBelow ((2 : ℝ) ^ K₀),
    (windowCoeff r q - (-1 / (q.1 : ℂ))) * (x : ℂ) ^ (q.1 : ℂ)
  let Zhigh := ∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)
  let T := (trivialZeroSeriesReal x / x - trivialZeroSeriesReal (r * x) / (r * x)) /
    (1 / x - 1 / (r * x))
  have hT := trivial_window_bound hx hxr
  have hform := chebyshevLagWindow_div_eq (by linarith : 1 < x) hxr
  have hsum : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (r * x)) =
      Zlow + Zdrift + Zhigh := by
    rw [tsum_congr (fun q => windowCoeff_scale hr hx0 q)]
    exact tsum_windowCoeff_eq_split K₀ hr hx1
  rw [hsum] at hform
  have hE : primeWindowError r x =
      Zlow.re + Zdrift.re + Zhigh.re + (T - Real.log (2 * Real.pi)) := by
    unfold primeWindowError
    rw [hform]
    simp only [Complex.add_re]
    dsimp [T]
    ring
  have hfour := add_four_sq_le hη Zlow.re Zdrift.re Zhigh.re (T - Real.log (2 * Real.pi))
  rw [← hE] at hfour
  have h1 : Zlow.re ^ 2 ≤ ‖Zlow‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm Zlow) 2
  have h2 : Zdrift.re ^ 2 ≤ ((r - 1) * ((xiCopiesBelow ((2 : ℝ) ^ K₀)).card : ℝ) * x) ^ 2 := by
    have hdr := (Complex.abs_re_le_norm Zdrift).trans (norm_lowZeroSum_drift_le K₀ hr hx1)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdr 2
  have h3 : Zhigh.re ^ 2 ≤ ‖Zhigh‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm Zhigh) 2
  have h4 : (T - Real.log (2 * Real.pi)) ^ 2 ≤ (|Real.log (2 * Real.pi)| + 2) ^ 2 := by
    have hb : |T - Real.log (2 * Real.pi)| ≤ |Real.log (2 * Real.pi)| + 2 := by
      have h := abs_sub T (Real.log (2 * Real.pi))
      rw [abs_of_nonneg hT.1] at h
      linarith [hT.2]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hη1 : 0 ≤ 3 * (1 + 1 / η) := by positivity
  have hnum : primeWindowError r x ^ 2 ≤
      (1 + η) * ‖Zlow‖ ^ 2 +
        3 * (1 + 1 / η) *
          (((r - 1) * ((xiCopiesBelow ((2 : ℝ) ^ K₀)).card : ℝ) * x) ^ 2 +
            ‖Zhigh‖ ^ 2 + (|Real.log (2 * Real.pi)| + 2) ^ 2) := by
    calc primeWindowError r x ^ 2
        ≤ (1 + η) * Zlow.re ^ 2 +
            3 * (1 + 1 / η) * (Zdrift.re ^ 2 + Zhigh.re ^ 2 + (T - Real.log (2 * Real.pi)) ^ 2) := hfour
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left (add_le_add (add_le_add h2 h3) h4) hη1)
  refine (div_le_div_of_nonneg_right hnum (sq_nonneg x)).trans_eq ?_
  have hxne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0.ne'
  field_simp
  ring

theorem continuousOn_lowZeroSum_sq_div (K₀ : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) (Icc a b) := by
  have hx : ∀ x ∈ Icc a b, 0 < x := fun x hx => ha.trans_le hx.1
  refine ContinuousOn.div ?_ (continuousOn_id.pow 2) (fun x h => pow_ne_zero 2 (hx x h).ne')
  refine (ContinuousOn.norm ?_).pow 2
  unfold lowZeroSum
  refine continuousOn_finsetSum _ fun q _ => continuousOn_const.mul ?_
  exact continuousOn_of_forall_continuousAt fun x h =>
    Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hx x h).ne')

/-- **Dyadic Chebyshev decomposition at `r = 1`.** Under RH, for every `X ≥ 2`, `η > 0`, and
height index `K₀ ∈ ℕ`, the dyadic mean square of `(ψ(x) − x)/x` is bounded by `(1+η)` times the
dyadic mean square of `lowZeroSum K₀` plus a geometric tail `(5/6)^{K₀}` and an `O(1/X)` remainder. -/
theorem dyadic_chebyshev_sq_div_le (hRH : RiemannHypothesis) (K₀ : ℕ) {X η : ℝ}
    (hX : 2 ≤ X) (hη : 0 < η) :
    ∫ x in X..2 * X, (Chebyshev.psi x - x) ^ 2 / x ^ 2 ≤
      (1 + η) * (∫ x in X..2 * X, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
        3 * (1 + 1 / η) *
          (8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ +
            (|Real.log (2 * Real.pi)| + 2) ^ 2 / X) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  set N₀ : ℝ := ((xiCopiesBelow ((2 : ℝ) ^ K₀)).card : ℝ)
  set B₀ : ℝ := |Real.log (2 * Real.pi)| + 2
  -- bound at `1 < r ≤ 2`
  have hwindow : ∀ {r : ℝ}, 1 < r → r ≤ 2 →
      ∫ x in X..2 * X, primeWindowError r x ^ 2 / x ^ 2 ≤
        (1 + η) * (∫ x in X..2 * X, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
          3 * (1 + 1 / η) *
            (((r - 1) * N₀) ^ 2 * X +
              8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ +
              B₀ ^ 2 / X) := by
    intro r hr hr2
    have hWI : IntervalIntegrable (fun x => primeWindowError r x ^ 2 / x ^ 2) volume X (2 * X) := by
      refine (intervalIntegrable_const (c := (Chebyshev.psi (4 * X) + 4 * X) ^ 2 / X ^ 2)).mono_fun'
        (((primeWindowError_measurable r).pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      rw [Set.uIoc_of_le hXX] at hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hnum : primeWindowError r x ^ 2 ≤ (Chebyshev.psi (4 * X) + 4 * X) ^ 2 := by
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg _) (primeWindowError_bound hr hr2 hX0 ⟨hx.1.le, hx.2⟩) 2
      exact div_le_div₀ (by positivity) hnum (by positivity) (pow_le_pow_left₀ hX0.le hx.1.le 2)
    have hlowI : IntervalIntegrable (fun x => ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) volume X (2 * X) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hXX]
      exact continuousOn_lowZeroSum_sq_div K₀ hX0
    have hs_high := summable_norm_highWindowCoeff K₀ hr
    have hhigh_cont : ContinuousOn (fun x : ℝ =>
        ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2)
        (uIcc X (2 * X)) := by
      refine (ContinuousOn.norm ?_).pow 2
      refine continuousOn_tsum (u := fun q => (2 * X) * ‖highWindowCoeff K₀ r q‖)
        (fun q => continuousOn_const.mul (continuousOn_of_forall_continuousAt fun x hx => by
          rw [uIcc_of_le hXX] at hx
          exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hX0.trans_le hx.1).ne')))
        (hs_high.mul_left _) (fun q x hx => ?_)
      rw [uIcc_of_le hXX] at hx
      have hx1 : 1 ≤ x := hX1.trans hx.1
      have hx0 : 0 < x := hX0.trans_le hx.1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hp : x ^ (q.1 : ℂ).re ≤ 2 * X := by
        calc x ^ (q.1 : ℂ).re ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (xiZeroCopy_re_lt_one q).le
          _ = x := Real.rpow_one x
          _ ≤ 2 * X := hx.2
      nlinarith [norm_nonneg (highWindowCoeff K₀ r q)]
    have hhigh2I : IntervalIntegrable (fun x =>
        ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2)
        volume X (2 * X) :=
      (hhigh_cont.div (continuousOn_id.pow 2) fun x hx => by
        rw [uIcc_of_le hXX] at hx; exact pow_ne_zero 2 (hX0.trans_le hx.1).ne').intervalIntegrable
    have hhigh3I : IntervalIntegrable (fun x =>
        ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3)
        volume X (2 * X) :=
      (hhigh_cont.div (continuousOn_id.pow 3) fun x hx => by
        rw [uIcc_of_le hXX] at hx; exact pow_ne_zero 3 (hX0.trans_le hx.1).ne').intervalIntegrable
    -- bound the high-ordinate integral using `cramer_tail_summable_zero_energy`
    have hhigh_int : ∫ x in X..2 * X,
        ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2 ≤
          8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ := by
      have htail := cramer_tail_summable_zero_energy hRH hX1 (by norm_num : (0 : ℝ) ≤ 2) K₀
        (highWindowCoeff K₀ r) (fun q hq => highWindowCoeff_eq_zero_of_mem hq)
        (norm_highWindowCoeff_le K₀ hr hr2) hs_high
      calc ∫ x in X..2 * X,
            ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2
          ≤ ∫ x in X..2 * X, (2 * X) *
              (‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) := by
            refine intervalIntegral.integral_mono_on hXX hhigh2I (hhigh3I.const_mul _) fun x hx => ?_
            have hx0 : 0 < x := hX0.trans_le hx.1
            have hnn : 0 ≤ ‖∑' q : XiZeroCopy,
                highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 := by positivity
            calc ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2
                = x * (‖∑' q : XiZeroCopy,
                    highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) := by field_simp
              _ ≤ (2 * X) * (‖∑' q : XiZeroCopy,
                    highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) :=
                  mul_le_mul_of_nonneg_right hx.2 hnn
        _ = (2 * X) * ∫ x in X..2 * X,
              ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (2 * X) * (cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * 2 ^ 2 / X) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ = 8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ := by field_simp; ring
    -- pointwise comparison on `[X, 2X]` with `B₀²/x² ≤ B₀²/X²`
    have hpt : ∀ x ∈ Icc X (2 * X), primeWindowError r x ^ 2 / x ^ 2 ≤
        (1 + η) * (‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
          3 * (1 + 1 / η) *
            (((r - 1) * N₀) ^ 2 +
              ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2 +
              B₀ ^ 2 / X ^ 2) := fun x hx => by
      refine (primeWindowError_sq_div_le K₀ hr (hX.trans hx.1) hη).trans ?_
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity))
      exact div_le_div_of_nonneg_left (sq_nonneg B₀) (by positivity) (pow_le_pow_left₀ hX0.le hx.1 2)
    have hR_I : IntervalIntegrable (fun x =>
        (1 + η) * (‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
          3 * (1 + 1 / η) *
            (((r - 1) * N₀) ^ 2 +
              ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2 +
              B₀ ^ 2 / X ^ 2)) volume X (2 * X) :=
      (hlowI.const_mul _).add
        (((intervalIntegrable_const.add hhigh2I).add intervalIntegrable_const).const_mul _)
    calc ∫ x in X..2 * X, primeWindowError r x ^ 2 / x ^ 2
        ≤ ∫ x in X..2 * X, ((1 + η) * (‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
            3 * (1 + 1 / η) *
              (((r - 1) * N₀) ^ 2 +
                ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2 +
                B₀ ^ 2 / X ^ 2)) :=
          intervalIntegral.integral_mono_on hXX hWI hR_I hpt
      _ = (1 + η) * (∫ x in X..2 * X, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
            3 * (1 + 1 / η) *
              (((r - 1) * N₀) ^ 2 * X +
                (∫ x in X..2 * X,
                  ‖∑' q : XiZeroCopy, highWindowCoeff K₀ r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 2) +
                B₀ ^ 2 / X) := by
          rw [intervalIntegral.integral_add (hlowI.const_mul _)
            (((intervalIntegrable_const.add hhigh2I).add intervalIntegrable_const).const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add (intervalIntegrable_const.add hhigh2I) intervalIntegrable_const,
            intervalIntegral.integral_add intervalIntegrable_const hhigh2I,
            intervalIntegral.integral_const, intervalIntegral.integral_const,
            smul_eq_mul, smul_eq_mul]
          field_simp; ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add le_rfl hhigh_int) le_rfl) (by positivity))
  -- pass to the limit `r → 1⁺`
  have hrange : ∀ᶠ r : ℝ in 𝓝[>] 1, r ∈ Set.Ioo 1 2 := Ioo_mem_nhdsGT (by norm_num)
  have htL : Tendsto (fun r => ∫ x in X..2 * X, primeWindowError r x ^ 2 / x ^ 2) (𝓝[>] 1)
      (𝓝 (∫ x in X..2 * X, (Chebyshev.psi x - x) ^ 2 / x ^ 2)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => (Chebyshev.psi (4 * X) + 4 * X) ^ 2 / X ^ 2)
    · exact Eventually.of_forall fun r =>
        (((primeWindowError_measurable r).pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable
    · filter_upwards [hrange] with r hr
      apply ae_of_all
      intro x hx
      rw [Set.uIoc_of_le hXX] at hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hnum : primeWindowError r x ^ 2 ≤ (Chebyshev.psi (4 * X) + 4 * X) ^ 2 := by
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg _) (primeWindowError_bound hr.1 hr.2.le hX0 ⟨hx.1.le, hx.2⟩) 2
      exact div_le_div₀ (by positivity) hnum (by positivity) (pow_le_pow_left₀ hX0.le hx.1.le 2)
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro x hx
      rw [Set.uIoc_of_le hXX] at hx
      exact ((primeWindowError_tendsto (hX0.trans hx.1)).pow 2).div_const (x ^ 2)
  have htR : Tendsto (fun r : ℝ =>
      (1 + η) * (∫ x in X..2 * X, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
        3 * (1 + 1 / η) *
          (((r - 1) * N₀) ^ 2 * X +
            8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ +
            B₀ ^ 2 / X)) (𝓝[>] 1)
      (𝓝 ((1 + η) * (∫ x in X..2 * X, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
        3 * (1 + 1 / η) *
          (0 + 8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ + B₀ ^ 2 / X))) := by
    have h0 : Tendsto (fun r : ℝ => ((r - 1) * N₀) ^ 2 * X) (𝓝[>] 1) (𝓝 0) := by
      have hc : Continuous (fun r : ℝ => ((r - 1) * N₀) ^ 2 * X) := by fun_prop
      have hsub := hc.tendsto 1
      simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsub
      exact hsub.mono_left nhdsWithin_le_nhds
    exact tendsto_const_nhds.add
      (tendsto_const_nhds.mul ((h0.add tendsto_const_nhds).add tendsto_const_nhds))
  rw [zero_add] at htR
  exact le_of_tendsto_of_tendsto htL htR (hrange.mono fun r hr => hwindow hr.1 hr.2.le)

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
