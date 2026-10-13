import GaloisForLFunctions.RHTower.JointAncestryTypicalCapApprox

/-!
# Typical JAS positivity fails below a finitely attained zero-free abscissa

**Theorem** (`exists_card_jasPhaseAggregate_re_neg_gt_of_finite_top`).  Suppose the real parts
of the zeros have a maximum `β₀`, attained by finitely many zero copies.  Then for every level
`σ ∈ (½, β₀)` there are `N ≥ 3` and `ε > 0` such that for every `X` some finite set `P` of
primes `p > X` has more than `ε N^{|P|}` phase vectors `k : P → ℤ/N` with
`Re jasPhaseAggregate σ 1 N P k < 0`.

So typical positivity at a level `σ` forces every zero into `Re ρ ≤ σ` in such configurations.
With the half-plane producer (typical positivity at every `σ > ½ + Θ`), the typical abscissa
equals the zero-free abscissa `½ + Θ`.

Proof.  On a short prime window `(X, CX]` with `log C` small, every low zero's heavy phase sum
is `X^{ρ−½}` times one variable `Z(k)`, and the copies with `|Re ρ − ½| < Θ` freeze to their
weights.  The shifted aggregate is then the rotating model
`L + Re Σ_top b_ρ exp(g_ρ ω^{−j} X^Θ Z(k))` (`abs_shifted_sub_model_le`).  We choose `X` with the
top frequencies `g_ρ = e^{iγ log X}` separated (`exists_ge_forall_cos_le`).  The rotation lemma
plus Paley–Zygmund plus orbit counting (`card_neg_ge_of_rotation_model`) then give a fixed
proportion of negative phase vectors.
-/

open Complex Finset Filter
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The top of the zero set -/

theorem re_reflect (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
  change (1 - (q.1 : ℂ)).re = _; simp

theorem one_sub_le_re_of_max {β₀ : ℝ} (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀)
    (q : XiZeroCopy) : 1 - β₀ ≤ (q.1 : ℂ).re := by
  have := hmax (xiZeroCopyReflectEquiv q); rw [re_reflect] at this; linarith

theorem abs_re_sub_half_le_of_max {β₀ : ℝ} (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ β₀ - 1 / 2 := by
  rw [abs_le]; constructor <;> linarith [hmax q, one_sub_le_re_of_max hmax q]

theorem finite_top_of_max {β₀ : ℝ} (hfin : {q : XiZeroCopy | (q.1 : ℂ).re = β₀}.Finite) :
    {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = β₀ - 1 / 2}.Finite := by
  have hrefl : {q : XiZeroCopy | (q.1 : ℂ).re = 1 - β₀}.Finite := by
    have := hfin.preimage (f := xiZeroCopyReflectEquiv) xiZeroCopyReflectEquiv.injective.injOn
    refine this.subset fun q hq => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq, re_reflect] at hq ⊢
    linarith
  refine (hfin.union hrefl).subset fun q hq => ?_
  simp only [Set.mem_setOf_eq] at hq
  rcases abs_eq (by
    have := abs_nonneg ((q.1 : ℂ).re - 1 / 2); linarith : (0 : ℝ) ≤ β₀ - 1 / 2) |>.mp hq with h | h
  · left; simp only [Set.mem_setOf_eq]; linarith
  · right; simp only [Set.mem_setOf_eq]; linarith

/-! ## The dominant class and the separation -/

theorem capFreq_eq_of_im_eq {X : ℝ} {s q : XiZeroCopy} (h : (s.1 : ℂ).im = (q.1 : ℂ).im) :
    capFreq X s = capFreq X q := by unfold capFreq; rw [h]

theorem re_capFreq_mul_conj (X : ℝ) (s q : XiZeroCopy) :
    (capFreq X s * conj (capFreq X q)).re =
      Real.cos (((s.1 : ℂ).im - (q.1 : ℂ).im) * Real.log X) := by
  unfold capFreq
  rw [← Complex.exp_conj, ← Complex.exp_add]
  generalize Real.log X = L
  have : (((s.1 : ℂ).im * L : ℝ) : ℂ) * Complex.I + conj ((((q.1 : ℂ).im * L : ℝ) : ℂ) * Complex.I) =
      ((((s.1 : ℂ).im - (q.1 : ℂ).im) * L : ℝ) : ℂ) * Complex.I := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem capCoeffTop_of_im_eq {Θ : ℝ} {s q₁ : XiZeroCopy} (hq₁ : (q₁.1 : ℂ).re = 1 / 2 + Θ)
    (hs : |(s.1 : ℂ).re - 1 / 2| = Θ) (him : (s.1 : ℂ).im = (q₁.1 : ℂ).im) :
    capCoeffTop Θ s = lagWeight q₁ := by
  unfold capCoeffTop
  split_ifs with htop
  · have : (s.1 : ℂ) = (q₁.1 : ℂ) := Complex.ext (by rw [htop, hq₁]) him
    unfold lagWeight; rw [this]
  · have hbot : (s.1 : ℂ).re = 1 / 2 - Θ := by
      rcases abs_eq (by have := abs_nonneg ((s.1 : ℂ).re - 1 / 2); linarith : (0 : ℝ) ≤ Θ)
        |>.mp hs with h | h
      · exact absurd (by linarith) htop
      · linarith
    have : (s.1 : ℂ) = 1 - conj (q₁.1 : ℂ) := Complex.ext (by simp [hbot, hq₁]; ring)
      (by simp [him])
    unfold lagWeight; rw [this]
    simp only [map_div₀, map_one, map_mul, map_sub, Complex.conj_conj]
    ring

/-! ## Good phase vectors -/

theorem capHigh_nonneg (σ : ℝ) (N : ℕ) (P : Finset Nat.Primes) (Low : Finset XiZeroCopy)
    (k : ↥P → Fin N) : 0 ≤ capHigh σ N P Low k :=
  tsum_nonneg fun q => by positivity

/-- **Most phase vectors are good.** -/
theorem card_good_ge {σ Θ X C δ : ℝ} {N : ℕ} (hN : 3 ≤ N) {P : Finset Nat.Primes} (hX : 1 ≤ X)
    (hΘ : 0 ≤ Θ) (hΘσ : Θ ≤ σ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    (Low : Finset XiZeroCopy) (hLow : ∀ q ∈ Low, |(q.1 : ℂ).re - 1 / 2| ≤ Θ ∧
      ‖(q.1 : ℂ) - 1 / 2‖ * Real.log C ≤ 1)
    (hδ : 0 < δ)
    (hdet : Real.exp (-(2 * Θ) * Real.log X) * capVar Θ σ X P +
        2 / 3 * Real.exp ((Θ - σ) * Real.log X) *
          (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P)) ≤ δ / 2)
    (hcoh : ∀ q ∈ Low, 2 * (64 / δ ^ 2) *
        (4 * capVar Θ σ X P * (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) ^ 2) ≤
          1 / (256 * (Low.card + 1)))
    (hsec : 2 * (16 / δ ^ 2) * (1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
        (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P))) ≤ 1 / (256 * (Low.card + 1)))
    (hhigh : ∑ k : ↥P → Fin N, capHigh σ N P Low k ≤ (N : ℝ) ^ Fintype.card ↥P / 192) :
    (31 / 32 : ℝ) * (N : ℝ) ^ Fintype.card ↥P ≤
      ((Finset.univ.filter fun k : ↥P → Fin N => capHigh σ N P Low k ≤ 1 / 3 ∧
        ∀ q ∈ Low, capDelta σ X P q k ≤ δ).card : ℝ) := by
  set n : ℝ := (N : ℝ) ^ Fintype.card ↥P with hn
  set G := Finset.univ.filter fun k : ↥P → Fin N => capHigh σ N P Low k ≤ 1 / 3 ∧
    ∀ q ∈ Low, capDelta σ X P q k ≤ δ
  set B1 := Finset.univ.filter fun k : ↥P → Fin N => 1 / 3 < capHigh σ N P Low k
  set B2 := Low.biUnion fun q => Finset.univ.filter fun k : ↥P → Fin N => δ < capDelta σ X P q k
  have hcompl : Finset.univ.filter (fun k : ↥P → Fin N => ¬ (capHigh σ N P Low k ≤ 1 / 3 ∧
      ∀ q ∈ Low, capDelta σ X P q k ≤ δ)) ⊆ B1 ∪ B2 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_le, not_forall,
      exists_prop] at hk
    rcases hk with h | ⟨q, hq, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
  have hB1 : (B1.card : ℝ) ≤ n / 64 := by
    have := card_lt_le_sum_div (fun k : ↥P → Fin N => capHigh σ N P Low k)
      (fun k => capHigh_nonneg σ N P Low k) (by norm_num : (0 : ℝ) < 1 / 3)
    refine this.trans ?_
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hB2 : (B2.card : ℝ) ≤ n / 128 := by
    have h1 : (B2.card : ℝ) ≤ ∑ q ∈ Low,
        ((Finset.univ.filter fun k : ↥P → Fin N => δ < capDelta σ X P q k).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∀ q ∈ Low, ((Finset.univ.filter fun k : ↥P → Fin N =>
        δ < capDelta σ X P q k).card : ℝ) ≤ n * (2 / (256 * (Low.card + 1))) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := hLow q hq
      refine (card_capDelta_gt_le hN hX hΘ hΘσ hP hq1 hq2 hδ hdet).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := hcoh q hq
      have e : (2 : ℝ) / (256 * (Low.card + 1)) =
          1 / (256 * (Low.card + 1)) + 1 / (256 * (Low.card + 1)) := by ring
      linarith
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have hL : (Low.card : ℝ) * (n * (2 / (256 * (Low.card + 1)))) ≤ n / 128 := by
      have hc : (0 : ℝ) ≤ Low.card := Nat.cast_nonneg _
      rw [show (Low.card : ℝ) * (n * (2 / (256 * (Low.card + 1)))) =
        n / 128 * (Low.card / (Low.card + 1)) by field_simp; ring]
      have : (Low.card : ℝ) / (Low.card + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hn0 : 0 ≤ n / 128 := by positivity
      nlinarith
    linarith
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (↥P → Fin N)))
    (fun k : ↥P → Fin N => capHigh σ N P Low k ≤ 1 / 3 ∧ ∀ q ∈ Low, capDelta σ X P q k ≤ δ)
  have huniv : ((Finset.univ : Finset (↥P → Fin N)).card : ℝ) = n := by
    simp [hn]
  have hc := Finset.card_le_card hcompl
  have hu := Finset.card_union_le B1 B2
  have : (G.card : ℝ) + (Finset.univ.filter (fun k : ↥P → Fin N => ¬ (capHigh σ N P Low k ≤ 1 / 3 ∧
      ∀ q ∈ Low, capDelta σ X P q k ≤ δ))).card = n := by
    rw [← huniv]; exact_mod_cast hsplit
  have hcR : ((Finset.univ.filter (fun k : ↥P → Fin N => ¬ (capHigh σ N P Low k ≤ 1 / 3 ∧
      ∀ q ∈ Low, capDelta σ X P q k ≤ δ))).card : ℝ) ≤ B1.card + B2.card := by
    exact_mod_cast hc.trans hu
  linarith

/-- `X^{2Θ}` and `p^{−2σ}` as exponentials: the two variance normalisations agree. -/
theorem capVar_eq_capVariance {Θ σ X : ℝ} (hX : 0 < X) {W : Finset ℕ} (hW : ∀ n ∈ W, n.Prime)
    {P : Finset Nat.Primes} (hPW : ∀ p : Nat.Primes, p ∈ P ↔ (p : ℕ) ∈ W) :
    capVar Θ σ X P = capVariance Θ σ X W := by
  unfold capVar capVariance
  rw [Real.rpow_def_of_pos hX, show Real.log X * (2 * Θ) = 2 * Θ * Real.log X by ring]
  congr 1
  rw [Finset.sum_coe_sort P (fun p : Nat.Primes => Real.exp (-(2 * σ) * Real.log ((p : ℕ) : ℝ)))]
  refine Finset.sum_bij' (fun p _ => (p : ℕ)) (fun n hn => ⟨n, hW n hn⟩)
    (fun p hp => (hPW p).mp hp) (fun n hn => (hPW ⟨n, hW n hn⟩).mpr hn)
    (fun p _ => rfl) (fun n _ => rfl) (fun p hp => ?_)
  have hn0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [Real.rpow_def_of_pos hn0]; ring_nf

/-- `exp(c log X) → 0` for `c < 0`. -/
theorem tendsto_exp_mul_log_atTop {c : ℝ} (hc : c < 0) :
    Tendsto (fun X : ℝ => Real.exp (c * Real.log X)) atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp (Real.tendsto_log_atTop.const_mul_atTop_of_neg hc)

theorem eventually_exp_mul_log_le {c ε : ℝ} (hc : c < 0) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, Real.exp (c * Real.log X) ≤ ε :=
  (tendsto_exp_mul_log_atTop hc).eventually (ge_mem_nhds hε)

/-! ## The count on one window -/

theorem sc_sq_mul_sum_capCoef_sq (Θ σ X : ℝ) (P : Finset Nat.Primes) :
    Real.exp (Θ * Real.log X) ^ 2 * ∑ p : ↥P, capCoef σ p ^ 2 = capVar Θ σ X P := by
  unfold capVar capCoef
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_pow, sq (Real.exp (-σ * _)), ← Real.exp_add, sq (Real.exp (Θ * Real.log X)),
    ← Real.exp_add]
  ring_nf

theorem re_jasPhaseAggregate_one_neg_iff (σ : ℝ) (N : ℕ) (P : Finset Nat.Primes)
    (k : ↥P → Fin N) : (jasPhaseAggregate σ 1 N P k).re < 0 ↔
      (∑' q : XiZeroCopy, lagWeight q *
        ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (k p)).re < 0 := by
  have h2 : (2 : ℂ) ^ P.card = (((2 : ℝ) ^ P.card : ℝ) : ℂ) := by norm_cast
  rw [jasPhaseAggregate_one_eq, h2, Complex.re_ofReal_mul]
  constructor
  · intro h; by_contra h'; push Not at h'; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) P.card]
  · intro h; exact mul_neg_of_pos_of_neg (by positivity) h

/-- **The count on one window.** -/
theorem count_of_window {σ Θ X R₁ δ ΘF κ : ℝ} {N : ℕ} (hN3 : 3 ≤ N) {P : Finset Nat.Primes}
    (hX : 1 ≤ X) (hΘσ : Θ ≤ σ) (habs : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hAB : ∀ q : XiZeroCopy, ∀ p : ↥P, 1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖) ≤ 1 / 2)
    {T F : Finset XiZeroCopy} (hTF : Disjoint T F) (hT : ∀ s ∈ T, |(s.1 : ℂ).re - 1 / 2| = Θ)
    {q₁ : XiZeroCopy} (hq₁T : q₁ ∈ T) (hq₁ : (q₁.1 : ℂ).re = 1 / 2 + Θ)
    (hΘF : ΘF ≤ Θ) (hF : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| ≤ ΘF)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hsepX : ∀ s ∈ T, (s.1 : ℂ).im ≠ (q₁.1 : ℂ).im →
      Real.cos (((s.1 : ℂ).im - (q₁.1 : ℂ).im) * Real.log X) ≤ 1 - κ)
    (hVR : 2 * rotRadius ‖lagWeight q₁‖ κ (∑ s : ↥T, ‖capCoeffTop Θ s‖) lagWeightTotal ^ 2 ≤
      capVar Θ σ X P)
    (hR₁ : 32 * capVar Θ σ X P ≤ R₁ ^ 2) (hR₁0 : 0 ≤ R₁) (hN : 6 * R₁ + 2 ≤ N)
    (hgood : (31 / 32 : ℝ) * (N : ℝ) ^ Fintype.card ↥P ≤
      ((Finset.univ.filter fun k : ↥P → Fin N => capHigh σ N P (T ∪ F) k ≤ 1 / 3 ∧
        ∀ q ∈ T ∪ F, capDelta σ X P q k ≤ δ).card : ℝ))
    (hδ1 : δ ≤ 1) (hs1 : Real.exp (-(2 * Θ) * Real.log X) * R₁ ≤ 1)
    (hs2 : 2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁) ≤ 1)
    (hbudget : (∑ s ∈ T, ‖lagWeight s‖) * (2 * Real.exp (2 * R₁) * δ +
          2 * Real.exp R₁ * (Real.exp (-(2 * Θ) * Real.log X) * R₁)) +
        (∑ q ∈ F, ‖lagWeight q‖) * (2 * Real.exp (2 * R₁) * δ +
          2 * (2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁))) ≤ 2 / 3) :
    rotFrac κ / 16 * (N : ℝ) ^ P.card ≤
      ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate σ 1 N P k).re < 0).card : ℝ) := by
  have hN0 : 0 < N := by omega
  have hβ : 0 < ‖lagWeight q₁‖ := norm_pos_iff.mpr fun h => by
    have := lagWeight_re_pos q₁; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
  have hsep : ∀ s : ↥T, capFreq X s ≠ capFreq X q₁ →
      (capFreq X s * conj (capFreq X q₁)).re ≤ 1 - κ := by
    intro s hs
    have him : ((s : XiZeroCopy).1 : ℂ).im ≠ (q₁.1 : ℂ).im := fun h => hs (capFreq_eq_of_im_eq h)
    rw [re_capFreq_mul_conj]; exact hsepX s s.2 him
  have hclass : ∀ s : ↥T, capFreq X s = capFreq X q₁ → capCoeffTop Θ s = lagWeight q₁ := by
    intro s hs
    have him : ((s : XiZeroCopy).1 : ℂ).im = (q₁.1 : ℂ).im := by
      by_contra h
      have h1 := hsepX s s.2 h
      have h2 := re_capFreq_mul_conj X s q₁
      rw [hs, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_capFreq] at h2
      simp at h2
      linarith
    exact capCoeffTop_of_im_eq hq₁ (hT s s.2) him
  have hB : ‖lagWeight q₁‖ ≤ ‖∑ s ∈ Finset.univ.filter (fun s : ↥T => capFreq X s = capFreq X q₁),
      capCoeffTop Θ s‖ := by
    rw [Finset.sum_congr rfl fun s hs => hclass s (Finset.mem_filter.mp hs).2, Finset.sum_const,
      nsmul_eq_mul, norm_mul, Complex.norm_natCast]
    have hmem : (⟨q₁, hq₁T⟩ : ↥T) ∈ Finset.univ.filter (fun s : ↥T => capFreq X s = capFreq X q₁) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hcard : (1 : ℝ) ≤ (Finset.univ.filter (fun s : ↥T => capFreq X s = capFreq X q₁)).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨_, hmem⟩
    nlinarith [norm_nonneg (lagWeight q₁)]
  have hL : |(∑ q ∈ F, lagWeight q).re| ≤ lagWeightTotal := by
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    exact summable_norm_lagWeight.sum_le_tsum F (fun q _ => norm_nonneg _)
  have hcv := sc_sq_mul_sum_capCoef_sq Θ σ X P
  have hcount := card_neg_ge_of_rotation_model (ι := ↥P) (S := ↥T) hN3
    (fun k => (∑' q : XiZeroCopy, lagWeight q *
      ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (k p)).re)
    (capCoef σ) (Real.exp_pos (Θ * Real.log X))
    (fun s => capFreq X s) (fun s => capCoeffTop Θ s) (capFreq X q₁)
    (fun s => norm_capFreq X s) (norm_capFreq X q₁) hβ hκ hκ1 lagWeightTotal_nonneg hB hsep le_rfl
    hL (by rw [hcv]; exact hVR) (by rw [hcv]; exact hR₁) hR₁0 hN
    (Finset.univ.filter fun k : ↥P → Fin N => capHigh σ N P (T ∪ F) k ≤ 1 / 3 ∧
      ∀ q ∈ T ∪ F, capDelta σ X P q k ≤ δ) hgood (by
    intro k hk hζ j
    obtain ⟨hhigh, hδ⟩ := (Finset.mem_filter.mp hk).2
    have hζ' : Real.exp (Θ * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖ ≤ R₁ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hζ
      exact hζ
    have happ := abs_shifted_sub_model_le hN0 hX hΘσ habs hAB hTF hT hΘF hF k j hζ' hδ hδ1 hs1 hs2
    rw [Finset.sum_coe_sort T (fun s => capCoeffTop Θ s * Complex.exp (capFreq X s *
      (conj (unitRoot N ^ (j : ℕ)) * ((Real.exp (Θ * Real.log X) : ℂ) *
        linearPhaseSum (capCoef σ) k))))]
    linarith)
  have hcongr : (Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate σ 1 N P k).re < 0) =
      Finset.univ.filter fun k : ↥P → Fin N => (∑' q : XiZeroCopy, lagWeight q *
        ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (k p)).re < 0 :=
    Finset.filter_congr fun k _ => re_jasPhaseAggregate_one_neg_iff σ N P k
  rw [hcongr, ← Fintype.card_coe P]
  exact hcount

/-! ## The theorem -/

/-- Finite sets of copies have a strict gap below a top they avoid. -/
theorem exists_gap_of_finset {Θ : ℝ} (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < Θ) (hΘ : 0 < Θ) :
    ∃ ΘF : ℝ, ΘF < Θ ∧ ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| ≤ ΘF := by
  by_cases hne : F.Nonempty
  · obtain ⟨q₀, hq₀, hmax⟩ := Finset.exists_max_image F (fun q => |(q.1 : ℂ).re - 1 / 2|) hne
    exact ⟨_, hF q₀ hq₀, hmax⟩
  · exact ⟨0, hΘ, fun q hq => absurd ⟨q, hq⟩ hne⟩

/-! ## Parameter arithmetic -/

theorem fs_det {a b e c V δ : ℝ} (hV : 0 < V) (hc0 : 0 ≤ c) (hc : c ≤ V + 1) (he0 : 0 ≤ e)
    (he : e ≤ Real.exp 1) (ha : a ≤ δ / (4 * (V + 1)))
    (hb : b ≤ δ / (16 * Real.exp 1 * (V + 1))) (hδ : 0 < δ) :
    a * c + 2 / 3 * b * (e * (4 * c)) ≤ δ / 2 := by
  have hE := Real.exp_pos 1
  have h1 : a * c ≤ δ / 4 := by
    calc a * c ≤ δ / (4 * (V + 1)) * (V + 1) := mul_le_mul ha hc hc0 (by positivity)
      _ = δ / 4 := by field_simp
  have h2 : 2 / 3 * b * (e * (4 * c)) ≤ δ / 4 := by
    calc 2 / 3 * b * (e * (4 * c)) ≤ 2 / 3 * (δ / (16 * Real.exp 1 * (V + 1))) *
          (Real.exp 1 * (4 * (V + 1))) := by gcongr
      _ = δ / 6 := by field_simp; ring
      _ ≤ δ / 4 := by linarith
  linarith

theorem fs_coh {V L δ y c : ℝ} (hV : 0 < V) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hc : c ≤ V + 1) (hy0 : 0 ≤ y) (hy : y ≤ δ / (512 * (V + 2) * (L + 1))) :
    2 * (64 / δ ^ 2) * (4 * c * y ^ 2) ≤ 1 / (256 * (L + 1)) := by
  have hy2 : y ^ 2 ≤ (δ / (512 * (V + 2) * (L + 1))) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  calc 2 * (64 / δ ^ 2) * (4 * c * y ^ 2)
      ≤ 2 * (64 / δ ^ 2) * (4 * (V + 1) * (δ / (512 * (V + 2) * (L + 1))) ^ 2) := by gcongr
    _ = (V + 1) / (512 * (V + 2) ^ 2 * (L + 1) ^ 2) := by field_simp; ring
    _ ≤ (V + 2) ^ 2 / (512 * (V + 2) ^ 2 * (L + 1)) := by
        have hL1 : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
        apply div_le_div₀ (by positivity) (by nlinarith) (by positivity)
        exact mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = 1 / (512 * (L + 1)) := by field_simp
    _ ≤ 1 / (256 * (L + 1)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith

theorem fs_sec {V L δ x e c : ℝ} (hV : 0 < V) (hL : 0 ≤ L) (hδ : 0 < δ) (hc0 : 0 ≤ c)
    (hc : c ≤ V + 1) (he0 : 0 ≤ e) (he : e ≤ Real.exp 1)
    (hx : x ≤ δ ^ 2 / (2048 * (L + 1) * Real.exp 1 * (V + 1))) :
    2 * (16 / δ ^ 2) * (1 / 16 * x * (e * (4 * c))) ≤ 1 / (256 * (L + 1)) := by
  have hE := Real.exp_pos 1
  calc 2 * (16 / δ ^ 2) * (1 / 16 * x * (e * (4 * c))) ≤
      2 * (16 / δ ^ 2) * (1 / 16 * (δ ^ 2 / (2048 * (L + 1) * Real.exp 1 * (V + 1))) *
        (Real.exp 1 * (4 * (V + 1)))) := by gcongr
    _ = 1 / (256 * (L + 1)) := by field_simp; ring

theorem fs_high {t τ N n V e c : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ τ) (hN : 0 < N) (hn : 0 ≤ n)
    (hτ : τ = 1 / (192 * N * Real.exp (Real.exp 1 * (V + 1))))
    (hec : e * c ≤ Real.exp 1 * (V + 1)) :
    t * (N * (n * Real.exp (e * c))) ≤ n / 192 := by
  have hE := Real.exp_le_exp.mpr hec
  have hE0 := Real.exp_pos (e * c)
  have hτ0 : 0 ≤ τ := le_trans ht0 ht
  calc t * (N * (n * Real.exp (e * c))) ≤ τ * (N * (n * Real.exp (Real.exp 1 * (V + 1)))) := by
        gcongr
    _ = n / 192 := by rw [hτ]; field_simp

theorem fs_s1 {x R W : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hx : x ≤ 1 / (12 * Real.exp R * (R + 1) * (W + 1))) : x * R ≤ 1 := by
  calc x * R ≤ 1 / (12 * Real.exp R * (R + 1) * (W + 1)) * R := mul_le_mul_of_nonneg_right hx hR
    _ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        have h1 := Real.one_le_exp hR
        have h2 : R + 1 ≤ (R + 1) * (W + 1) := by nlinarith
        have h3 : (R + 1) * (W + 1) ≤ 12 * Real.exp R * ((R + 1) * (W + 1)) := by nlinarith
        nlinarith

theorem fs_s2 {x R W : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hx : x ≤ 1 / (24 * (R + 1) * (W + 1))) : 2 * (x * R) ≤ 1 := by
  calc 2 * (x * R) ≤ 2 * (1 / (24 * (R + 1) * (W + 1)) * R) := by gcongr
    _ = R / (12 * (R + 1) * (W + 1)) := by field_simp; ring
    _ ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith

theorem fs_budget {WT WF R δ x y : ℝ} (hWT : 0 ≤ WT) (hWF : 0 ≤ WF) (hR : 0 ≤ R) (hδbud : 2 * Real.exp (2 * R) * δ * (WT + WF) ≤ 1 / 6)
    (hx : x ≤ 1 / (12 * Real.exp R * (R + 1) * (WT + 1)))
    (hy : y ≤ 1 / (24 * (R + 1) * (WF + 1))) :
    WT * (2 * Real.exp (2 * R) * δ + 2 * Real.exp R * (x * R)) +
      WF * (2 * Real.exp (2 * R) * δ + 2 * (2 * (y * R))) ≤ 2 / 3 := by
  have hE1 := Real.exp_pos R
  have h5 : WT * (2 * Real.exp R * (x * R)) ≤ 1 / 6 := by
    calc WT * (2 * Real.exp R * (x * R)) ≤
        WT * (2 * Real.exp R * (1 / (12 * Real.exp R * (R + 1) * (WT + 1)) * R)) := by gcongr
      _ = WT * R / (6 * (R + 1) * (WT + 1)) := by field_simp; ring
      _ ≤ 1 / 6 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h8 : WF * (2 * (2 * (y * R))) ≤ 1 / 6 := by
    calc WF * (2 * (2 * (y * R))) ≤ WF * (2 * (2 * (1 / (24 * (R + 1) * (WF + 1)) * R))) := by
          gcongr
      _ = WF * R / (6 * (R + 1) * (WF + 1)) := by field_simp; ring
      _ ≤ 1 / 6 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

/-- **One window.**  The conclusion at a separated scale `X` carrying a prime window. -/
theorem final_step {σ Θ ΘF κ R₁ V δ η₀ τ WT WF X C : ℝ} {N : ℕ} {T F : Finset XiZeroCopy}
    {q₁ : XiZeroCopy} {Xg : ℕ} {W : Finset ℕ}
    (hN3 : 3 ≤ N) (hN : 6 * R₁ + 2 ≤ N) (hR₁0 : 0 ≤ R₁) (hR₁sq : R₁ ^ 2 = 32 * (V + 1))
    (hV0 : 0 < V)
    (hVR : 2 * rotRadius ‖lagWeight q₁‖ κ (∑ s : ↥T, ‖capCoeffTop Θ s‖) lagWeightTotal ^ 2 ≤ V)
    (hΘ0 : 0 < Θ) (hΘhalf : Θ ≤ 1 / 2) (hΘσ : Θ < σ)
    (habs : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hT : ∀ s ∈ T, |(s.1 : ℂ).re - 1 / 2| = Θ) (hq₁T : q₁ ∈ T)
    (hq₁ : (q₁.1 : ℂ).re = 1 / 2 + Θ) (hTF : Disjoint T F) (hΘFlt : ΘF < Θ)
    (hF : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| ≤ ΘF) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hsepX : ∀ s ∈ T, (s.1 : ℂ).im ≠ (q₁.1 : ℂ).im →
      Real.cos (((s.1 : ℂ).im - (q₁.1 : ℂ).im) * Real.log X) ≤ 1 - κ)
    (hτ : τ = 1 / (192 * N * Real.exp (Real.exp 1 * (V + 1))))
    (htail : ∑' q : {q : XiZeroCopy // q ∉ T ∪ F}, ‖lagWeight (q : XiZeroCopy)‖ < τ)
    (hWT : WT = ∑ s ∈ T, ‖lagWeight s‖) (hWF : WF = ∑ q ∈ F, ‖lagWeight q‖)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδbud : 2 * Real.exp (2 * R₁) * δ * (WT + WF) ≤ 1 / 6)
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1)
    (hzη : ∀ q ∈ T ∪ F, ‖(q.1 : ℂ) - 1 / 2‖ * η₀ ≤ δ / (512 * (V + 2) * ((T ∪ F).card + 1)))
    (hC : C = Real.exp η₀)
    (hWsub : W ⊆ multiplicativePrimeWindow X C) (hV1 : V ≤ capVariance Θ σ X W)
    (hV2 : capVariance Θ σ X W ≤ V + 1) (hXg : (Xg : ℝ) + 1 ≤ X) (hX1 : 1 ≤ X)
    (hc5a : Real.exp (-(2 * Θ) * Real.log X) ≤ δ / (4 * (V + 1)))
    (hc5b : Real.exp (-(2 * Θ) * Real.log X) ≤ 1 / (12 * Real.exp R₁ * (R₁ + 1) * (WT + 1)))
    (hc6a : Real.exp ((Θ - σ) * Real.log X) ≤ 1 / 2)
    (hc6b : Real.exp ((Θ - σ) * Real.log X) ≤ δ / (16 * Real.exp 1 * (V + 1)))
    (hc7 : Real.exp (2 * (Θ - σ) * Real.log X) ≤
      δ ^ 2 / (2048 * ((T ∪ F).card + 1) * Real.exp 1 * (V + 1)))
    (hc8 : Real.exp ((ΘF - Θ) * Real.log X) ≤ 1 / (24 * (R₁ + 1) * (WF + 1))) :
    ∃ P : Finset Nat.Primes, (∀ p ∈ P, Xg < (p : ℕ)) ∧ rotFrac κ / 32 * (N : ℝ) ^ P.card <
      ((Finset.univ.filter fun k : ↥P → Fin N =>
        (jasPhaseAggregate σ 1 N P k).re < 0).card : ℝ) := by
  have hlogC : Real.log C = η₀ := by rw [hC, Real.log_exp]
  have hWprime : ∀ n ∈ W, n.Prime := fun n hn =>
    (mem_multiplicativePrimeWindow_bounds (hWsub hn)).2.2
  obtain ⟨P, hPW⟩ : ∃ P : Finset Nat.Primes, ∀ p : Nat.Primes, p ∈ P ↔ (p : ℕ) ∈ W :=
    ⟨W.subtype Nat.Prime, fun p => Finset.mem_subtype⟩
  have hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧
      (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X := fun p hp => by
    obtain ⟨h1, h2, -⟩ := mem_multiplicativePrimeWindow_bounds (hWsub ((hPW p).mp hp))
    exact ⟨h1, h2⟩
  have hX0 : 0 < X := by linarith
  have hcv : capVar Θ σ X P = capVariance Θ σ X W := capVar_eq_capVariance hX0 hWprime hPW
  have hV1' : V ≤ capVar Θ σ X P := hcv ▸ hV1
  have hV2' : capVar Θ σ X P ≤ V + 1 := hcv ▸ hV2
  have hcv0 : 0 ≤ capVar Θ σ X P := le_trans hV0.le hV1'
  refine ⟨P, fun p hp => ?_, ?_⟩
  · have := (hP p hp).1
    have : ((Xg : ℕ) : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hEΘ : Real.exp (2 * Θ * Real.log C) ≤ Real.exp 1 := by
    rw [hlogC]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hE0 := (Real.exp_pos (2 * Θ * Real.log C)).le
  have hLc : (0 : ℝ) ≤ (T ∪ F).card := Nat.cast_nonneg _
  have hLowz : ∀ q ∈ T ∪ F, |(q.1 : ℂ).re - 1 / 2| ≤ Θ ∧ ‖(q.1 : ℂ) - 1 / 2‖ * Real.log C ≤ 1 := by
    intro q hq
    refine ⟨habs q, ?_⟩
    rw [hlogC]
    refine (hzη q hq).trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have hAB : ∀ q : XiZeroCopy, ∀ p : ↥P, 1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖) ≤ 1 / 2 := by
    intro q p
    have hle := exp_le_of_window hX1 (c := Θ - σ) (by linarith) hP p
    have hA := (norm_capA_le (σ := σ) (habs q) p).trans hle
    have hB := (norm_capB_le (σ := σ) (habs q) p).trans hle
    linarith
  have hdet := fs_det hV0 hcv0 hV2' hE0 hEΘ hc5a hc6b hδ0
  have hcoh : ∀ q ∈ T ∪ F, 2 * (64 / δ ^ 2) *
      (4 * capVar Θ σ X P * (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) ^ 2) ≤
        1 / (256 * ((T ∪ F).card + 1)) := fun q hq => by
    rw [hlogC]; exact fs_coh hV0 hLc hδ0 hV2' (by positivity) (hzη q hq)
  have hsec := fs_sec hV0 hLc hδ0 hcv0 hV2' hE0 hEΘ hc7
  have hhigh : ∑ k : ↥P → Fin N, capHigh σ N P (T ∪ F) k ≤ (N : ℝ) ^ Fintype.card ↥P / 192 :=
    (sum_capHigh_le (C := C) hN3 hX1 hΘ0.le hΘσ.le hP habs (T ∪ F)).trans
      (fs_high (tsum_nonneg fun _ => norm_nonneg _) htail.le
        (by exact_mod_cast (by omega : 0 < N)) (by positivity) hτ
        (mul_le_mul hEΘ hV2' hcv0 (Real.exp_pos 1).le))
  have hgood := card_good_ge (C := C) hN3 hX1 hΘ0.le hΘσ.le hP (T ∪ F) hLowz hδ0 hdet hcoh hsec
    hhigh
  have hWT0 : 0 ≤ WT := by rw [hWT]; positivity
  have hWF0 : 0 ≤ WF := by rw [hWF]; positivity
  have hs1 := fs_s1 hR₁0 hWT0 hc5b
  have hs2 := fs_s2 hR₁0 hWF0 hc8
  have hbudget := fs_budget hWT0 hWF0 hR₁0 hδbud hc5b hc8
  rw [hWT, hWF] at hbudget
  have hcount := count_of_window hN3 hX1 hΘσ.le habs hAB hTF hT hq₁T hq₁ hΘFlt.le hF hκ0 hκ1
    hsepX (hVR.trans hV1') (by rw [hR₁sq]; linarith) hR₁0 hN hgood hδ1 hs1 hs2 hbudget
  have hfrac := rotFrac_pos hκ0 hκ1
  have hn0 : (0 : ℝ) < (N : ℝ) ^ P.card := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    positivity
  have hprod := mul_pos hfrac hn0
  calc rotFrac κ / 32 * (N : ℝ) ^ P.card < rotFrac κ / 16 * (N : ℝ) ^ P.card := by linarith
    _ ≤ _ := hcount

theorem eta_facts {δ z V L : ℝ} (hδ : 0 < δ) (hz : 1 ≤ z) (hV : 0 < V) (hL : 0 ≤ L) :
    0 < δ / (512 * z * (V + 2) * (L + 1)) ∧
      z * (δ / (512 * z * (V + 2) * (L + 1))) = δ / (512 * (V + 2) * (L + 1)) ∧
      δ / (512 * (V + 2) * (L + 1)) ≤ δ ∧
      0 < δ ^ 2 / (2048 * (L + 1) * Real.exp 1 * (V + 1)) := by
  have hz0 : 0 < z := by linarith
  refine ⟨by positivity, by field_simp, ?_, by positivity⟩
  apply div_le_self hδ.le
  nlinarith

/-- **Typical JAS positivity fails below a finitely attained zero-free abscissa.** -/
theorem exists_card_jasPhaseAggregate_re_neg_gt_of_finite_top {β₀ σ : ℝ}
    (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀)
    (hfin : {q : XiZeroCopy | (q.1 : ℂ).re = β₀}.Finite)
    (hne : ∃ q : XiZeroCopy, (q.1 : ℂ).re = β₀) (hσ : 1 / 2 < σ) (hσβ : σ < β₀) :
    ∃ N : ℕ, 3 ≤ N ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ X : ℕ, ∃ P : Finset Nat.Primes,
      (∀ p ∈ P, X < (p : ℕ)) ∧ ε * (N : ℝ) ^ P.card <
        ((Finset.univ.filter fun k : ↥P → Fin N =>
          (jasPhaseAggregate σ 1 N P k).re < 0).card : ℝ) := by
  classical
  obtain ⟨q₁, hq₁⟩ := hne
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : ℝ, Θ = β₀ - 1 / 2 := ⟨_, rfl⟩
  have hΘ0 : 0 < Θ := by rw [hΘdef]; linarith
  have hβ₀1 : β₀ < 1 := hq₁ ▸ xiZeroCopy_re_lt_one q₁
  have hΘhalf : Θ ≤ 1 / 2 := by rw [hΘdef]; linarith
  have hΘσ : Θ < σ := by rw [hΘdef]; linarith
  have habs : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ Θ := fun q => by
    rw [hΘdef]; exact abs_re_sub_half_le_of_max hmax q
  obtain ⟨T, hTmem⟩ : ∃ T : Finset XiZeroCopy, ∀ q, q ∈ T ↔ |(q.1 : ℂ).re - 1 / 2| = Θ := by
    refine ⟨(finite_top_of_max hfin).toFinset, fun q => ?_⟩
    rw [Set.Finite.mem_toFinset, hΘdef]; rfl
  have hT : ∀ s ∈ T, |(s.1 : ℂ).re - 1 / 2| = Θ := fun s hs => (hTmem s).mp hs
  have hq₁' : (q₁.1 : ℂ).re = 1 / 2 + Θ := by rw [hq₁, hΘdef]; ring
  have hq₁T : q₁ ∈ T := (hTmem q₁).mpr (by rw [hq₁']; ring_nf; exact abs_of_pos hΘ0)
  -- separation constants
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = Real.pi /
      (4 * (Fintype.card {s : ↥T // ((s : XiZeroCopy).1 : ℂ).im ≠ (q₁.1 : ℂ).im} + 1)) :=
    ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; have := Real.pi_pos; positivity
  have haπ : a ≤ Real.pi / 2 := by
    rw [hadef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := Real.pi_pos
    have : (0 : ℝ) ≤ Fintype.card {s : ↥T // ((s : XiZeroCopy).1 : ℂ).im ≠ (q₁.1 : ℂ).im} :=
      Nat.cast_nonneg _
    nlinarith
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 - Real.cos a := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκdef]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [Real.pi_pos]) ha0
    rw [Real.cos_zero] at this; linarith
  have hκ1 : κ ≤ 1 := by
    rw [hκdef]
    have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], haπ⟩
    linarith
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = 2 * rotRadius ‖lagWeight q₁‖ κ
      (∑ s : ↥T, ‖capCoeffTop Θ s‖) lagWeightTotal ^ 2 + 1 := ⟨_, rfl⟩
  have hV0 : 0 < V := by rw [hVdef]; positivity
  have hVR : 2 * rotRadius ‖lagWeight q₁‖ κ (∑ s : ↥T, ‖capCoeffTop Θ s‖) lagWeightTotal ^ 2 ≤
      V := by rw [hVdef]; linarith
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = Real.sqrt (32 * (V + 1)) := ⟨_, rfl⟩
  have hR₁0 : 0 ≤ R₁ := by rw [hR₁def]; exact Real.sqrt_nonneg _
  have hR₁sq : R₁ ^ 2 = 32 * (V + 1) := by rw [hR₁def, Real.sq_sqrt (by positivity)]
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈6 * R₁ + 2⌉₊ + 3 := ⟨_, rfl⟩
  have hN3 : 3 ≤ N := by omega
  have hN : 6 * R₁ + 2 ≤ N := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil (6 * R₁ + 2)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hfrac := rotFrac_pos hκ0 hκ1
  refine ⟨N, hN3, rotFrac κ / 32, by positivity, fun Xg => ?_⟩
  -- the tail and the low copies
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = 1 / (192 * N * Real.exp (Real.exp 1 * (V + 1))) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτdef]; positivity
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_tsum_compl_atTop_zero (fun q : XiZeroCopy => ‖lagWeight q‖)).eventually
      (gt_mem_nhds hτ0))
  obtain ⟨F, hFdef⟩ : ∃ F : Finset XiZeroCopy, F = (T ∪ s₀) \ T := ⟨_, rfl⟩
  have hTF : Disjoint T F := by rw [hFdef]; exact Finset.disjoint_sdiff
  have hTFLow : T ∪ F = T ∪ s₀ := by
    rw [hFdef]
    exact Finset.union_sdiff_of_subset Finset.subset_union_left
  have htail : ∑' q : {q : XiZeroCopy // q ∉ T ∪ F}, ‖lagWeight (q : XiZeroCopy)‖ < τ := by
    rw [hTFLow]; exact hs₀ (T ∪ s₀) Finset.subset_union_right
  have hFlt : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < Θ := by
    intro q hq
    rw [hFdef] at hq
    have hqT : q ∉ T := (Finset.mem_sdiff.mp hq).2
    exact lt_of_le_of_ne (habs q) fun h => hqT ((hTmem q).mpr h)
  obtain ⟨ΘF, hΘFlt, hF⟩ := exists_gap_of_finset F hFlt hΘ0
  -- the error budget
  obtain ⟨WT, hWT⟩ : ∃ w : ℝ, w = ∑ s ∈ T, ‖lagWeight s‖ := ⟨_, rfl⟩
  obtain ⟨WF, hWF⟩ : ∃ w : ℝ, w = ∑ q ∈ F, ‖lagWeight q‖ := ⟨_, rfl⟩
  have hWT0 : 0 ≤ WT := by rw [hWT]; positivity
  have hWF0 : 0 ≤ WF := by rw [hWF]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (12 * Real.exp (2 * R₁) * (WT + WF + 1)) := ⟨_, rfl⟩
  have hE2 := Real.exp_pos (2 * R₁)
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * R₁)
    nlinarith
  have hδbud : 2 * Real.exp (2 * R₁) * δ * (WT + WF) ≤ 1 / 6 := by
    rw [hδdef, show 2 * Real.exp (2 * R₁) * (1 / (12 * Real.exp (2 * R₁) * (WT + WF + 1))) *
      (WT + WF) = (WT + WF) / (6 * (WT + WF + 1)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]; linarith
  obtain ⟨zmax, hzdef⟩ : ∃ z : ℝ, z = ∑ q ∈ T ∪ F, ‖(q.1 : ℂ) - 1 / 2‖ + 1 := ⟨_, rfl⟩
  have hz1 : 1 ≤ zmax := by
    rw [hzdef]
    have : 0 ≤ ∑ q ∈ T ∪ F, ‖(q.1 : ℂ) - 1 / 2‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hzq : ∀ q ∈ T ∪ F, ‖(q.1 : ℂ) - 1 / 2‖ ≤ zmax := fun q hq => by
    rw [hzdef]
    have := Finset.single_le_sum (f := fun q : XiZeroCopy => ‖(q.1 : ℂ) - 1 / 2‖)
      (fun _ _ => norm_nonneg _) hq
    linarith
  obtain ⟨η₀, hηdef⟩ : ∃ η : ℝ, η = δ / (512 * zmax * (V + 2) * ((T ∪ F).card + 1)) := ⟨_, rfl⟩
  have hLc : (0 : ℝ) ≤ (T ∪ F).card := Nat.cast_nonneg _
  obtain ⟨hη0', hzη0', hδle, hpos7⟩ := eta_facts hδ0 hz1 hV0 hLc
  have hη0 : 0 < η₀ := by rw [hηdef]; exact hη0'
  have hzη0 : zmax * η₀ = δ / (512 * (V + 2) * ((T ∪ F).card + 1)) := by rw [hηdef]; exact hzη0'
  have hzη : ∀ q ∈ T ∪ F, ‖(q.1 : ℂ) - 1 / 2‖ * η₀ ≤
      δ / (512 * (V + 2) * ((T ∪ F).card + 1)) := fun q hq => by
    rw [← hzη0]; exact mul_le_mul_of_nonneg_right (hzq q hq) hη0.le
  have hη1 : η₀ ≤ 1 := by
    have h1 : η₀ ≤ zmax * η₀ := le_mul_of_one_le_left hη0.le hz1
    linarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Real.exp η₀ := ⟨_, rfl⟩
  have hC1 : 1 < C := by rw [hCdef]; exact Real.one_lt_exp_iff.mpr hη0
  -- eventual conditions
  have hev := (eventually_exists_capWindow hΘ0.le (by linarith : 0 < 2 * σ - 2 * Θ)
    (by rw [hΘdef]; linarith : 2 * σ - 2 * Θ < 1) hC1 hV0).and
    ((eventually_ge_atTop ((Xg : ℝ) + 1)).and ((eventually_ge_atTop (1 : ℝ)).and
    ((eventually_exp_mul_log_le (by linarith : -(2 * Θ) < 0)
      (by positivity : 0 < δ / (4 * (V + 1)))).and
    ((eventually_exp_mul_log_le (by linarith : -(2 * Θ) < 0)
      (by positivity : 0 < 1 / (12 * Real.exp R₁ * (R₁ + 1) * (WT + 1)))).and
    ((eventually_exp_mul_log_le (by linarith : Θ - σ < 0) (by norm_num : (0 : ℝ) < 1 / 2)).and
    ((eventually_exp_mul_log_le (by linarith : Θ - σ < 0)
      (by positivity : 0 < δ / (16 * Real.exp 1 * (V + 1)))).and
    ((eventually_exp_mul_log_le (by linarith : 2 * (Θ - σ) < 0) hpos7).and
    (eventually_exp_mul_log_le (by linarith : ΘF - Θ < 0)
      (by positivity : 0 < 1 / (24 * (R₁ + 1) * (WF + 1)))))))))))
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hev
  -- separation of the top frequencies
  obtain ⟨u, hu, hcos⟩ := exists_ge_forall_cos_le
    (fun s : {s : ↥T // ((s : XiZeroCopy).1 : ℂ).im ≠ (q₁.1 : ℂ).im} =>
      ((s.1 : XiZeroCopy).1 : ℂ).im - (q₁.1 : ℂ).im)
    (fun s => sub_ne_zero.mpr s.2) (Real.log (max X₀ 1))
  have hlogX : Real.log (Real.exp u) = u := Real.log_exp u
  have hXX₀ : X₀ ≤ Real.exp u := by
    have h1 : max X₀ 1 ≤ Real.exp u := by
      rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right X₀ 1))]
      exact Real.exp_le_exp.mpr hu
    exact (le_max_left _ _).trans h1
  obtain ⟨⟨W, hWsub, hV1, hV2⟩, hXg, hX1, hc5a, hc5b, hc6a, hc6b, hc7, hc8⟩ :=
    hX₀ (Real.exp u) hXX₀
  have hsepX : ∀ s ∈ T, (s.1 : ℂ).im ≠ (q₁.1 : ℂ).im →
      Real.cos (((s.1 : ℂ).im - (q₁.1 : ℂ).im) * Real.log (Real.exp u)) ≤ 1 - κ := by
    intro s hs hne'
    have := hcos ⟨⟨s, hs⟩, hne'⟩
    rw [← hadef] at this
    rw [hlogX, hκdef, show (1 : ℝ) - (1 - Real.cos a) = Real.cos a by ring]
    exact this
  exact final_step hN3 hN hR₁0 hR₁sq hV0 hVR hΘ0 hΘhalf hΘσ habs hT hq₁T hq₁' hTF hΘFlt hF hκ0
    hκ1 hsepX hτdef htail hWT hWF hδ0 hδ1 hδbud hη0 hη1 hzη hCdef hWsub hV1 hV2 hXg hX1 hc5a hc5b
    hc6a hc6b hc7 hc8

end

end RHTower
