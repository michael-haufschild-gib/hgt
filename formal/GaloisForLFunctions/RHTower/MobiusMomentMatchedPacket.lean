import GaloisForLFunctions.RHTower.MobiusMomentSimplexSelector
import GaloisForLFunctions.RHTower.MobiusTwoJetPrimeSemiprimePacket

/-!
# Moment-matched literal blocks of cubic Gamma atoms

Fix `d ≥ 1` and the nodes `t_i = (i+1)/(d+2)`, `0 ≤ i ≤ d`.  Candidates of one sign are grouped by
a cofactor `q` and a window `i`, with normalized positions in `[t_i, t_i + ε]`.  For each group of
`m_q` candidates the barycentric radius gives window weights in `[0,1]`, summing to one, whose
weighted power sums are exactly `m_q` times the nominal barycenter; so both signs carry the same
fractional moments `(Σ_q m_q) v_0`.  Pooled floor rounding then selects exactly `M = Σ_q m_q`
candidates of each sign with power sums of orders `1, …, d` within `2` of each other.

For a block `[X, X+L]`, `L ≤ X`, the Taylor law of order `d+1` bounds the selected packet by
`Σ_{j=1}^{d} 2 L^j/j! ‖∂^j f_X‖ + (#selected) L^{d+1}/(d+1)! K_{d+1} 4X² X^{-(5+δ)/2}/X^{d+1}`,
since its zeroth moment vanishes.
-/

open Finset

noncomputable section

namespace RHTower.CubicGamma

open RHTower.MomentSelector

/-! ### Selection and the Taylor bound for one block -/

/-- Two sides with equal integer mass and equal fractional power sums of orders `1, …, d` admit
exactly `M` selected labels on each side with power sums within `2`. -/
theorem exists_matched_selection {ι : Type*} (sP sN : Finset ι) (uP uN wP wN : ι → ℝ) (d M : ℕ)
    (huP : ∀ i ∈ sP, 0 ≤ uP i ∧ uP i ≤ 1) (huN : ∀ i ∈ sN, 0 ≤ uN i ∧ uN i ≤ 1)
    (hwP : ∀ i ∈ sP, 0 ≤ wP i ∧ wP i ≤ 1) (hwN : ∀ i ∈ sN, 0 ≤ wN i ∧ wN i ≤ 1)
    (hmP : ∑ i ∈ sP, wP i = M) (hmN : ∑ i ∈ sN, wN i = M)
    (hmom : ∀ j < d, ∑ i ∈ sP, wP i * uP i ^ (j + 1) = ∑ i ∈ sN, wN i * uN i ^ (j + 1)) :
    ∃ TP ⊆ sP, ∃ TN ⊆ sN, TP.card = M ∧ TN.card = M ∧
      ∀ j < d, |∑ i ∈ TP, uP i ^ (j + 1) - ∑ i ∈ TN, uN i ^ (j + 1)| ≤ 2 := by
  obtain ⟨TP, hTP, hcP, hmomP⟩ := exists_pooled_selection sP uP wP huP hwP hmP
  obtain ⟨TN, hTN, hcN, hmomN⟩ := exists_pooled_selection sN uN wN huN hwN hmN
  refine ⟨TP, hTP, TN, hTN, hcP, hcN, fun j hj => ?_⟩
  have h1 := abs_le.mp (hmomP (j + 1))
  have h2 := abs_le.mp (hmomN (j + 1))
  have h3 := hmom j hj
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Taylor bound for a matched block** of order `d+1`. -/
theorem gammaNorm_matched_block_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {ι : Type*}
    (TP TN : Finset ι) (xP xN : ι → ℝ) {X L : ℝ} (hX : 0 < X) (hLX : L ≤ X) (d : ℕ)
    (hxP : ∀ i ∈ TP, X ≤ xP i ∧ xP i ≤ X + L) (hxN : ∀ i ∈ TN, X ≤ xN i ∧ xN i ≤ X + L)
    (hcard : TP.card = TN.card)
    (hmom : ∀ j < d, |∑ i ∈ TP, (xP i - X) ^ (j + 1) - ∑ i ∈ TN, (xN i - X) ^ (j + 1)| ≤
      2 * L ^ (j + 1)) :
    gammaNorm δ (fun t => ∑ i ∈ TP, atom (xP i) t - ∑ i ∈ TN, atom (xN i) t) ≤
      ∑ j ∈ range d, 2 * L ^ (j + 1) / ((j + 1).factorial : ℝ) *
          (jetConst (j + 1) * X ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (j + 1)) +
        ((TP.card + TN.card : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
          (jetConst (d + 1) * (4 * X ^ 2) * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1))) := by
  classical
  set c : ι ⊕ ι → ℝ := fun x => Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1) x with hc
  set p : ι ⊕ ι → ℝ := fun x => Sum.elim xP xN x with hp
  have hmem : ∀ x ∈ TP.disjSum TN, X ≤ p x ∧ p x ≤ X + L := by
    intro x hx
    rcases mem_disjSum.mp hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hxP i hi
    · exact hxN i hi
  have h := gammaNorm_atomPacket_le hδ0 hδ1 (TP.disjSum TN) c p (d + 1) hX
    (fun x hx => (hmem x hx).1)
  have hfun : (fun t => ∑ x ∈ TP.disjSum TN, c x * atom (p x) t) =
      fun t => ∑ i ∈ TP, atom (xP i) t - ∑ i ∈ TN, atom (xN i) t := by
    funext t
    rw [sum_disjSum]
    simp [hc, hp, sub_eq_add_neg, sum_neg_distrib]
  rw [hfun] at h
  refine h.trans ?_
  have hXe : 0 < X ^ ((5 + δ) / 2) := Real.rpow_pos_of_pos hX _
  have hinv : 0 ≤ (X ^ ((5 + δ) / 2))⁻¹ := (inv_pos.mpr hXe).le
  have hmom' : ∀ j : ℕ, ∑ x ∈ TP.disjSum TN, c x * (p x - X) ^ j =
      ∑ i ∈ TP, (xP i - X) ^ j - ∑ i ∈ TN, (xN i - X) ^ j := by
    intro j
    rw [sum_disjSum]
    simp [hc, hp, sub_eq_add_neg, sum_neg_distrib]
  -- the moment terms
  have hjets : ∑ j ∈ range (d + 1), |∑ x ∈ TP.disjSum TN, c x * (p x - X) ^ j| /
      (j.factorial : ℝ) * (jetConst j * X ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ j) ≤
      ∑ j ∈ range d, 2 * L ^ (j + 1) / ((j + 1).factorial : ℝ) *
          (jetConst (j + 1) * X ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (j + 1)) := by
    rw [sum_range_succ']
    have h0 : |∑ x ∈ TP.disjSum TN, c x * (p x - X) ^ 0| = 0 := by
      rw [hmom' 0]
      simp [hcard]
    rw [h0, zero_div, zero_mul, add_zero]
    apply sum_le_sum
    intro j hj
    have hjd := mem_range.mp hj
    rw [hmom' (j + 1)]
    have hjc := jetConst_nonneg (j + 1)
    have hf : (0 : ℝ) < ((j + 1).factorial : ℝ) := by positivity
    have hB : 0 ≤ jetConst (j + 1) * X ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (j + 1) := by positivity
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hmom j hjd) hf.le) hB
  -- the remainder
  have hrem : ∑ x ∈ TP.disjSum TN, |c x| * ((p x - X) ^ (d + 1) / ((d + 1).factorial : ℝ) *
      (jetConst (d + 1) * p x ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1))) ≤
      ((TP.card + TN.card : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
        (jetConst (d + 1) * (4 * X ^ 2) * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1))) := by
    have hterm : ∀ x ∈ TP.disjSum TN, |c x| * ((p x - X) ^ (d + 1) / ((d + 1).factorial : ℝ) *
        (jetConst (d + 1) * p x ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1))) ≤
        L ^ (d + 1) / ((d + 1).factorial : ℝ) *
          (jetConst (d + 1) * (4 * X ^ 2) * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1)) := by
      intro x hx
      obtain ⟨h1, h2⟩ := hmem x hx
      have hc1 : |c x| = 1 := by
        rcases x with i | i <;> simp [hc]
      have hpX : (p x - X) ^ (d + 1) ≤ L ^ (d + 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      have hp2 : p x ^ 2 ≤ 4 * X ^ 2 := by nlinarith
      have hjc := jetConst_nonneg (d + 1)
      have hL0 : 0 ≤ L := by linarith
      have hA : (p x - X) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤
          L ^ (d + 1) / ((d + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right hpX (by positivity)
      have hB : jetConst (d + 1) * p x ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1) ≤
          jetConst (d + 1) * (4 * X ^ 2) * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1) := by
        gcongr
      have hB0 : 0 ≤ jetConst (d + 1) * p x ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1) := by
        positivity
      rw [hc1, one_mul]
      exact mul_le_mul hA hB hB0 (by positivity)
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [sum_const, card_disjSum, nsmul_eq_mul]
  exact add_le_add hjets hrem

/-! ### Window weights -/

/-- The nodes `t_i = (i+1)/(d+2)`. -/
def layerNodes (d : ℕ) : Fin (d + 1) → ℝ := fun i => ((i : ℝ) + 1) / ((d : ℝ) + 2)

theorem layerNodes_injective (d : ℕ) : Function.Injective (layerNodes d) := by
  intro i j h
  simp only [layerNodes] at h
  have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  rw [div_left_inj' hd.ne'] at h
  exact Fin.ext (by exact_mod_cast (by linarith : (i : ℝ) = j))

theorem layerNodes_bounds (d : ℕ) (i : Fin (d + 1)) :
    0 ≤ layerNodes d i ∧ layerNodes d i + 1 / ((d : ℝ) + 2) ≤ 1 := by
  have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hi : (i : ℝ) ≤ d := by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
  refine ⟨by unfold layerNodes; positivity, ?_⟩
  unfold layerNodes
  rw [← add_div, div_le_one hd]
  linarith

/-- The window width for order `d`: the barycentric radius at `κ = 1/(2(d+1))`, scaled so that the
windows `[t_i, t_i + ε]` are disjoint and inside `[0, 1]`. -/
theorem exists_window_width (d : ℕ) (hd : 1 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / (2 * ((d : ℝ) + 2)) ∧
      ∀ Q : Fin (d + 1) → Fin d → ℝ,
        (∀ i k, |Q i k - layerNodes d i ^ (k.val + 1)| ≤ d * ε) →
        ∃ w : Fin (d + 1) → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ ∑ i, w i = 1 ∧
          ∀ k : Fin d, ∑ i, w i * Q i k = nominalBarycenter (layerNodes d) k := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨ε₁, hε₁, h⟩ := exists_barycentric_radius (layerNodes d) (layerNodes_injective d)
    (κ := 1 / (2 * ((d : ℝ) + 1))) (by positivity)
  refine ⟨min (ε₁ / d) (1 / (2 * ((d : ℝ) + 2))), by positivity, min_le_right _ _,
    fun Q hQ => ?_⟩
  have hQ' : ∀ i k, |Q i k - layerNodes d i ^ (k.val + 1)| ≤ ε₁ := by
    intro i k
    refine (hQ i k).trans ?_
    calc (d : ℝ) * min (ε₁ / d) (1 / (2 * ((d : ℝ) + 2))) ≤ d * (ε₁ / d) := by
          gcongr; exact min_le_left _ _
      _ = ε₁ := by field_simp
  obtain ⟨w, hw1, hwm, hwκ⟩ := h Q hQ'
  refine ⟨w, fun i => ?_, hw1, hwm⟩
  have hab := abs_le.mp (hwκ i)
  have h1 : 1 / ((d : ℝ) + 1) - 1 / (2 * ((d : ℝ) + 1)) = 1 / (2 * ((d : ℝ) + 1)) := by
    field_simp; ring
  have h2 : 1 / ((d : ℝ) + 1) + 1 / (2 * ((d : ℝ) + 1)) ≤ 1 := by
    rw [show 1 / ((d : ℝ) + 1) + 1 / (2 * ((d : ℝ) + 1)) = 3 / (2 * ((d : ℝ) + 1)) by
      field_simp; ring, div_le_one (by positivity)]
    linarith
  have h3 : 0 < 1 / (2 * ((d : ℝ) + 1)) := by positivity
  constructor
  · linarith [hab.1]
  · linarith [hab.2]

/-- The label set of a cofactor family: cofactor `q ∈ F`, window `i`, index `ℓ < m_q`. -/
def familyLabels {d : ℕ} (F : Finset ℕ) (m : ℕ → ℕ) : Finset (Σ _ : ℕ, Fin (d + 1) × ℕ) :=
  F.sigma fun q => (univ : Finset (Fin (d + 1))) ×ˢ range (m q)

theorem sum_familyLabels {d : ℕ} (F : Finset ℕ) (m : ℕ → ℕ) (f : (Σ _ : ℕ, Fin (d + 1) × ℕ) → ℝ) :
    ∑ x ∈ familyLabels (d := d) F m, f x =
      ∑ q ∈ F, ∑ i : Fin (d + 1), ∑ ℓ ∈ range (m q), f ⟨q, (i, ℓ)⟩ := by
  unfold familyLabels
  rw [sum_sigma]
  apply sum_congr rfl
  intro q _
  rw [sum_product]

/-- **Window weights.**  Labels in the windows `[t_i, t_i + ε]` carry weights in `[0,1]` with total
`Σ_q m_q` and weighted power sums `(Σ_q m_q)` times the nominal barycenter. -/
theorem exists_window_weights {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ∀ Q : Fin (d + 1) → Fin d → ℝ,
        (∀ i k, |Q i k - layerNodes d i ^ (k.val + 1)| ≤ d * ε) →
        ∃ w : Fin (d + 1) → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ ∑ i, w i = 1 ∧
          ∀ k : Fin d, ∑ i, w i * Q i k = nominalBarycenter (layerNodes d) k)
    (hε0 : 0 ≤ ε) (hεw : ε ≤ 1 / ((d : ℝ) + 2))
    (F : Finset ℕ) (m : ℕ → ℕ) (u : (Σ _ : ℕ, Fin (d + 1) × ℕ) → ℝ)
    (hu : ∀ q ∈ F, ∀ i : Fin (d + 1), ∀ ℓ < m q,
      layerNodes d i ≤ u ⟨q, (i, ℓ)⟩ ∧ u ⟨q, (i, ℓ)⟩ ≤ layerNodes d i + ε) :
    ∃ w : (Σ _ : ℕ, Fin (d + 1) × ℕ) → ℝ,
      (∀ x ∈ familyLabels F m, 0 ≤ w x ∧ w x ≤ 1) ∧
      ∑ x ∈ familyLabels F m, w x = ((∑ q ∈ F, m q : ℕ) : ℝ) ∧
      ∀ k : Fin d, ∑ x ∈ familyLabels F m, w x * u x ^ (k.val + 1) =
        ((∑ q ∈ F, m q : ℕ) : ℝ) * nominalBarycenter (layerNodes d) k := by
  classical
  -- weights for each cofactor
  have hq : ∀ q : ℕ, ∃ lw : Fin (d + 1) → ℝ, (q ∈ F →
      (∀ i, 0 ≤ lw i ∧ lw i ≤ 1) ∧ ∑ i, lw i = 1 ∧
      ∀ k : Fin d, ∑ i, lw i * ∑ ℓ ∈ range (m q), u ⟨q, (i, ℓ)⟩ ^ (k.val + 1) =
        (m q : ℝ) * nominalBarycenter (layerNodes d) k) := by
    intro q
    by_cases hqF : q ∈ F
    · rcases Nat.eq_zero_or_pos (m q) with h0 | hpos
      · -- no candidates: the nominal weights
        obtain ⟨w, hw01, hw1, -⟩ := hε (fun i k => layerNodes d i ^ (k.val + 1))
          (fun i k => by simp; positivity)
        refine ⟨w, fun _ => ⟨hw01, hw1, fun k => ?_⟩⟩
        simp [h0]
      · have hm0 : (0 : ℝ) < m q := by exact_mod_cast hpos
        set Q : Fin (d + 1) → Fin d → ℝ :=
          fun i k => (∑ ℓ ∈ range (m q), u ⟨q, (i, ℓ)⟩ ^ (k.val + 1)) / m q with hQ
        have hclose : ∀ i k, |Q i k - layerNodes d i ^ (k.val + 1)| ≤ d * ε := by
          intro i k
          have hk : ((k.val + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast k.isLt
          have hterm : ∀ ℓ ∈ range (m q), |u ⟨q, (i, ℓ)⟩ ^ (k.val + 1) -
              layerNodes d i ^ (k.val + 1)| ≤ d * ε := by
            intro ℓ hℓ
            obtain ⟨h1, h2⟩ := hu q hqF i ℓ (mem_range.mp hℓ)
            obtain ⟨h3, h4⟩ := layerNodes_bounds d i
            have h := abs_pow_sub_pow_le_window h3 h1 h2 (by linarith) (k.val + 1)
            have hε0 : 0 ≤ ε := by linarith
            exact h.trans (mul_le_mul_of_nonneg_right hk hε0)
          have e : Q i k - layerNodes d i ^ (k.val + 1) =
              (∑ ℓ ∈ range (m q), (u ⟨q, (i, ℓ)⟩ ^ (k.val + 1) - layerNodes d i ^ (k.val + 1))) /
                m q := by
            rw [hQ, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
            field_simp
          rw [e, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
          calc |∑ ℓ ∈ range (m q), (u ⟨q, (i, ℓ)⟩ ^ (k.val + 1) - layerNodes d i ^ (k.val + 1))|
              ≤ ∑ ℓ ∈ range (m q), |u ⟨q, (i, ℓ)⟩ ^ (k.val + 1) - layerNodes d i ^ (k.val + 1)| :=
                abs_sum_le_sum_abs _ _
            _ ≤ ∑ _ℓ ∈ range (m q), (d : ℝ) * ε := sum_le_sum hterm
            _ = d * ε * m q := by rw [sum_const, card_range, nsmul_eq_mul]; ring
        obtain ⟨w, hw01, hw1, hwm⟩ := hε Q hclose
        refine ⟨w, fun _ => ⟨hw01, hw1, fun k => ?_⟩⟩
        rw [← hwm k, mul_sum]
        apply sum_congr rfl
        intro i _
        rw [hQ]
        field_simp
    · exact ⟨fun _ => 0, fun h => absurd h hqF⟩
  choose lw hlw using hq
  refine ⟨fun x => lw x.1 x.2.1, fun x hx => ?_, ?_, fun k => ?_⟩
  · have hx' : x.1 ∈ F := by
      unfold familyLabels at hx
      exact (mem_sigma.mp hx).1
    exact (hlw x.1 hx').1 x.2.1
  · rw [sum_familyLabels]
    push_cast
    apply sum_congr rfl
    intro q hqF
    simp only [sum_const, card_range, nsmul_eq_mul]
    rw [← mul_sum, (hlw q hqF).2.1, mul_one]
  · rw [sum_familyLabels]
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro q hqF
    rw [← (hlw q hqF).2.2 k]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]

end RHTower.CubicGamma
