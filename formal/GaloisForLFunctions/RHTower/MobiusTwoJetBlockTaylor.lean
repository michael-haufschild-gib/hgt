import GaloisForLFunctions.RHTower.MobiusCubicGammaAtomJets
import GaloisForLFunctions.RHTower.MobiusBalancedTwoJetSelection

/-!
# Balanced two-jet blocks of cubic Gamma atoms

A block `[X, X+L]` with `L ≤ X` carries two families of opposite displacement pairs: `m` pairs
`(a⁻_i, b⁺_i)` with `a⁻_i` in the left quarter and `b⁺_i` in the right quarter, and `m` pairs
`(a⁺_i, b⁻_i)` placed the other way round.  Taking one family completely and a prefix of the other
balances the first moment to within `L`, with unit coefficients.  The second-order Taylor law for
atom packets then gives, uniformly in `0 ≤ δ ≤ 1`,

`‖Σ_{i<s⁻} (f_{a⁻_i} - f_{b⁺_i}) + Σ_{i<s⁺} (f_{a⁺_i} - f_{b⁻_i})‖_δ
   ≤ K₁ L X^{-(3+δ)/2} + 8 m L² K₂ X^{-(5+δ)/2}`,

because the zeroth moment of a pair packet vanishes, its first moment is the net displacement, and
its second-order remainder costs `L²` per atom.
-/

open Finset

noncomputable section

namespace RHTower.CubicGamma

/-- The sum of a mapped `List.range` is the `Finset.range` sum. -/
theorem list_sum_map_range (u : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map u).sum = ∑ i ∈ range n, u i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- **Balanced prefixes.**  Two families of displacements in `[0, L]` admit prefixes, one of them
complete, whose totals differ by at most `L`. -/
theorem exists_balanced_prefixes {L : ℝ} (hL : 0 ≤ L) (m : ℕ) (u v : ℕ → ℝ)
    (hu : ∀ i < m, 0 ≤ u i ∧ u i ≤ L) (hv : ∀ i < m, 0 ≤ v i ∧ v i ≤ L) :
    ∃ su sv : ℕ, su ≤ m ∧ sv ≤ m ∧ (su = m ∨ sv = m) ∧
      |∑ i ∈ range su, u i - ∑ i ∈ range sv, v i| ≤ L := by
  have hu' : ∀ x ∈ (List.range m).map u, 0 ≤ x ∧ x ≤ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hu i (List.mem_range.mp hi)
  have hv' : ∀ x ∈ (List.range m).map v, 0 ≤ x ∧ x ≤ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hv i (List.mem_range.mp hi)
  obtain ⟨us, vs, ut, vt, hsu, hsv, hend, hbal⟩ :=
    RHTower.exists_balanced_two_orientations L hL _ _ hu' hv'
  -- a prefix of a mapped range is a mapped shorter range
  have hprefix : ∀ (w : ℕ → ℝ) (xs ys : List ℝ), (List.range m).map w = xs ++ ys →
      xs.length ≤ m ∧ xs.sum = ∑ i ∈ range xs.length, w i ∧ (ys = [] → xs.length = m) := by
    intro w xs ys h
    have hlen : xs.length + ys.length = m := by
      have := congrArg List.length h
      simp only [List.length_map, List.length_range, List.length_append] at this
      omega
    refine ⟨by omega, ?_, fun hy => by rw [hy] at hlen; simpa using hlen⟩
    have hx : xs = ((List.range m).map w).take xs.length := by rw [h, List.take_left]
    rw [hx, ← List.map_take, List.take_range, min_eq_left (by omega), list_sum_map_range]
    congr 1
    simp
  obtain ⟨hlu, hsumu, hendu⟩ := hprefix u us ut hsu
  obtain ⟨hlv, hsumv, hendv⟩ := hprefix v vs vt hsv
  refine ⟨us.length, vs.length, hlu, hlv, ?_, ?_⟩
  · rcases hend with h | h
    · exact Or.inl (hendu h)
    · exact Or.inr (hendv h)
  · rw [← hsumu, ← hsumv]
    exact hbal

/-- **Pair packet Taylor bound.**  For pairs `a_i, b_i ∈ [X, X+L]` with `L ≤ X`,
`‖Σ_i (f_{a_i} - f_{b_i})‖_δ ≤ K₁ |Σ_i (a_i - b_i)| X X^{-(5+δ)/2} + 4 |s| L² K₂ X^{-(5+δ)/2}`. -/
theorem gammaNorm_pairPacket_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {X L : ℝ} (hX : 0 < X) (hLX : L ≤ X)
    (ha : ∀ i ∈ s, X ≤ a i ∧ a i ≤ X + L) (hb : ∀ i ∈ s, X ≤ b i ∧ b i ≤ X + L) :
    gammaNorm δ (fun t => ∑ i ∈ s, (atom (a i) t - atom (b i) t)) ≤
      jetConst 1 * |∑ i ∈ s, (a i - b i)| * X * (X ^ ((5 + δ) / 2))⁻¹ +
        4 * s.card * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ := by
  classical
  set c : ι × Bool → ℝ := fun x => if x.2 then 1 else -1 with hc
  set p : ι × Bool → ℝ := fun x => if x.2 then a x.1 else b x.1 with hp
  have hmem : ∀ x ∈ s ×ˢ (univ : Finset Bool), X ≤ p x ∧ p x ≤ X + L := by
    intro x hx
    have hx1 : x.1 ∈ s := (mem_product.mp hx).1
    simp only [hp]
    split_ifs
    · exact ha _ hx1
    · exact hb _ hx1
  have h := gammaNorm_atomPacket_le hδ0 hδ1 (s ×ˢ (univ : Finset Bool)) c p 2 hX
    (fun x hx => (hmem x hx).1)
  have hfun : (fun t => ∑ x ∈ s ×ˢ (univ : Finset Bool), c x * atom (p x) t) =
      fun t => ∑ i ∈ s, (atom (a i) t - atom (b i) t) := by
    funext t
    rw [Finset.sum_product]
    apply sum_congr rfl
    intro i _
    simp [hc, hp]
    ring
  rw [hfun] at h
  refine h.trans ?_
  have hmoment : ∀ j : ℕ, ∑ x ∈ s ×ˢ (univ : Finset Bool), c x * (p x - X) ^ j =
      ∑ i ∈ s, ((a i - X) ^ j - (b i - X) ^ j) := by
    intro j
    rw [Finset.sum_product]
    apply sum_congr rfl
    intro i _
    simp [hc, hp]
    ring
  have hXe : 0 < X ^ ((5 + δ) / 2) := Real.rpow_pos_of_pos hX _
  -- the two moment terms
  have hjets : ∑ j ∈ range 2, |∑ x ∈ s ×ˢ (univ : Finset Bool), c x * (p x - X) ^ j| /
      (j.factorial : ℝ) * (jetConst j * X ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ j) =
        jetConst 1 * |∑ i ∈ s, (a i - b i)| * X * (X ^ ((5 + δ) / 2))⁻¹ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hmoment, hmoment]
    have h0 : ∑ i ∈ s, ((a i - X) ^ 0 - (b i - X) ^ 0) = 0 := by simp
    have h1 : ∑ i ∈ s, ((a i - X) ^ 1 - (b i - X) ^ 1) = ∑ i ∈ s, (a i - b i) := by
      apply sum_congr rfl; intro i _; ring
    rw [h0, h1]
    simp only [abs_zero, zero_div, zero_mul, zero_add, Nat.factorial_one, Nat.cast_one, div_one,
      pow_one]
    field_simp
  -- the remainder
  have hrem : ∑ x ∈ s ×ˢ (univ : Finset Bool), |c x| * ((p x - X) ^ 2 / (Nat.factorial 2 : ℝ) *
      (jetConst 2 * p x ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ 2)) ≤
        4 * s.card * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ := by
    have hterm : ∀ x ∈ s ×ˢ (univ : Finset Bool), |c x| * ((p x - X) ^ 2 /
        (Nat.factorial 2 : ℝ) * (jetConst 2 * p x ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ 2)) ≤
          2 * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ := by
      intro x hx
      obtain ⟨h1, h2⟩ := hmem x hx
      have hc1 : |c x| = 1 := by simp only [hc]; split_ifs <;> simp
      have hpX : (p x - X) ^ 2 ≤ L ^ 2 := by
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      have hp2 : p x ^ 2 ≤ 4 * X ^ 2 := by nlinarith
      have hjc := jetConst_nonneg 2
      have hinv : 0 ≤ (X ^ ((5 + δ) / 2))⁻¹ := (inv_pos.mpr hXe).le
      rw [hc1, one_mul]
      calc (p x - X) ^ 2 / (Nat.factorial 2 : ℝ) *
            (jetConst 2 * p x ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ 2)
          ≤ L ^ 2 / (Nat.factorial 2 : ℝ) *
            (jetConst 2 * (4 * X ^ 2) * (X ^ ((5 + δ) / 2))⁻¹ / X ^ 2) := by gcongr
        _ = 2 * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ := by
            simp only [Nat.factorial, Nat.succ_eq_add_one]
            field_simp
            norm_num
            ring
    calc _ ≤ ∑ x ∈ s ×ˢ (univ : Finset Bool), 2 * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ :=
          sum_le_sum hterm
      _ = _ := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_bool,
            nsmul_eq_mul]
          push_cast
          ring
  rw [hjets]
  linarith

/-- **Balanced block.**  Four families in the quarters of `[X, X+L]` yield a unit-coefficient
packet, one orientation complete, with the two-jet bound uniform in `0 ≤ δ ≤ 1`. -/
theorem exists_block_two_jet {X L : ℝ} (hX : 0 < X) (hL : 0 ≤ L) (hLX : L ≤ X) (m : ℕ)
    (aN bP aP bN : ℕ → ℝ)
    (haN : ∀ i < m, X ≤ aN i ∧ aN i ≤ X + L / 4)
    (hbP : ∀ i < m, X + 3 * L / 4 ≤ bP i ∧ bP i ≤ X + L)
    (haP : ∀ i < m, X + 3 * L / 4 ≤ aP i ∧ aP i ≤ X + L)
    (hbN : ∀ i < m, X ≤ bN i ∧ bN i ≤ X + L / 4) :
    ∃ su sv : ℕ, su ≤ m ∧ sv ≤ m ∧ (su = m ∨ sv = m) ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      gammaNorm δ (fun t => ∑ i ∈ range su, (atom (aN i) t - atom (bP i) t) +
        ∑ i ∈ range sv, (atom (aP i) t - atom (bN i) t)) ≤
        jetConst 1 * L * X * (X ^ ((5 + δ) / 2))⁻¹ +
          8 * m * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ := by
  obtain ⟨su, sv, hsu, hsv, hend, hbal⟩ := exists_balanced_prefixes hL m
    (fun i => bP i - aN i) (fun i => aP i - bN i)
    (fun i hi => ⟨by linarith [(haN i hi).2, (hbP i hi).1], by linarith [(haN i hi).1, (hbP i hi).2]⟩)
    (fun i hi => ⟨by linarith [(hbN i hi).2, (haP i hi).1], by linarith [(hbN i hi).1, (haP i hi).2]⟩)
  refine ⟨su, sv, hsu, hsv, hend, fun δ hδ0 hδ1 => ?_⟩
  set A : ℕ ⊕ ℕ → ℝ := fun x => Sum.elim aN aP x with hA
  set B : ℕ ⊕ ℕ → ℝ := fun x => Sum.elim bP bN x with hB
  have hmemA : ∀ x ∈ (range su).disjSum (range sv), X ≤ A x ∧ A x ≤ X + L := by
    intro x hx
    rcases mem_disjSum.mp hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have := haN i (by have := mem_range.mp hi; omega)
      exact ⟨this.1, by simp only [hA, Sum.elim_inl]; linarith [this.2]⟩
    · have := haP i (by have := mem_range.mp hi; omega)
      exact ⟨by simp only [hA, Sum.elim_inr]; linarith [this.1], this.2⟩
  have hmemB : ∀ x ∈ (range su).disjSum (range sv), X ≤ B x ∧ B x ≤ X + L := by
    intro x hx
    rcases mem_disjSum.mp hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have := hbP i (by have := mem_range.mp hi; omega)
      exact ⟨by simp only [hB, Sum.elim_inl]; linarith [this.1], this.2⟩
    · have := hbN i (by have := mem_range.mp hi; omega)
      exact ⟨this.1, by simp only [hB, Sum.elim_inr]; linarith [this.2]⟩
  have h := gammaNorm_pairPacket_le hδ0 hδ1 ((range su).disjSum (range sv)) A B hX hLX hmemA hmemB
  have hfun : (fun t => ∑ x ∈ (range su).disjSum (range sv), (atom (A x) t - atom (B x) t)) =
      fun t => ∑ i ∈ range su, (atom (aN i) t - atom (bP i) t) +
        ∑ i ∈ range sv, (atom (aP i) t - atom (bN i) t) := by
    funext t
    rw [Finset.sum_disjSum]
    rfl
  rw [hfun, Finset.sum_disjSum, Finset.card_disjSum, Finset.card_range, Finset.card_range] at h
  refine h.trans ?_
  have hfirst : |∑ x ∈ range su, (A (Sum.inl x) - B (Sum.inl x)) +
      ∑ x ∈ range sv, (A (Sum.inr x) - B (Sum.inr x))| ≤ L := by
    simp only [hA, hB, Sum.elim_inl, Sum.elim_inr]
    have e : ∑ x ∈ range su, (aN x - bP x) + ∑ x ∈ range sv, (aP x - bN x) =
        -(∑ i ∈ range su, (bP i - aN i) - ∑ i ∈ range sv, (aP i - bN i)) := by
      simp only [Finset.sum_sub_distrib]
      ring
    rw [e, abs_neg]
    exact hbal
  have hXe : 0 < X ^ ((5 + δ) / 2) := Real.rpow_pos_of_pos hX _
  have hinv : 0 ≤ (X ^ ((5 + δ) / 2))⁻¹ := (inv_pos.mpr hXe).le
  have hj1 := jetConst_nonneg 1
  have hj2 := jetConst_nonneg 2
  have hcard : ((su + sv : ℕ) : ℝ) ≤ 2 * m := by
    push_cast
    have : (su : ℝ) ≤ m := by exact_mod_cast hsu
    have : (sv : ℝ) ≤ m := by exact_mod_cast hsv
    linarith
  have h1 : jetConst 1 * |∑ x ∈ range su, (A (Sum.inl x) - B (Sum.inl x)) +
      ∑ x ∈ range sv, (A (Sum.inr x) - B (Sum.inr x))| * X * (X ^ ((5 + δ) / 2))⁻¹ ≤
        jetConst 1 * L * X * (X ^ ((5 + δ) / 2))⁻¹ := by gcongr
  have h2 : 4 * ((su + sv : ℕ) : ℝ) * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ ≤
      8 * m * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ := by
    have := mul_le_mul_of_nonneg_left hcard (show (0 : ℝ) ≤ 4 by norm_num)
    calc 4 * ((su + sv : ℕ) : ℝ) * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹
        ≤ 4 * (2 * m) * L ^ 2 * jetConst 2 * (X ^ ((5 + δ) / 2))⁻¹ := by gcongr
      _ = _ := by ring
  push_cast at h2 ⊢
  linarith

end RHTower.CubicGamma
