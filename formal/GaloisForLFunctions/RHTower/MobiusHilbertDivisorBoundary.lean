import GaloisForLFunctions.RHTower.MobiusDivisorMonotoneSignLaw
import GaloisForLFunctions.RHTower.MobiusHilbertFormCriterion

/-!
# Integrality at the boundary exponent: the divisor section cancels twice the diagonal

At Gamma exponents `r > 1` the divisor-comparable Möbius section is absolutely summable, so its sign
law carries no information about zeros.  At the boundary exponent `r = 1` (the Hilbert matrix) it
does not converge absolutely, and the drift of the divisor sign law becomes logarithmic:

`Σ_{m ∣ n, m < n ≤ N} μ(m)μ(n)/(m+n) ≤ 3/2 - (1/2) Σ_{n ≤ N} μ(n)²/n`.

In the symmetric Hilbert form the divisor section therefore cancels at least twice the diagonal
`D_N = Σ_{n ≤ N} μ(n)²/(2n)`, up to the constant `3`.  Writing the Hilbert energy as
`E_N = D_N + 2·(divisor section) + (non-comparable section)`, this gives
`E_N ≤ (non-comparable section - D_N) + 3`.  Positivity of `E_N` gives the reverse bound: the
excess `non-comparable - D_N` is at least `-3`.  So the Riemann hypothesis follows as soon as the
non-comparable section exceeds the diagonal by only `O(N^ε)`.

*Proof of the drift bound.*  Layer-cake summation against `w(k) = 1/k` and the discrete sign law
`C_N(K) ≤ -#{squarefree n ∈ (N'/2, N']}`, `N' = min N (K-1)`, reduce the section to
`-Σ_n I(n)` over squarefree `2 ≤ n ≤ N`.  For `2n ≤ N` the layers `K ∈ [n+1, 2n]` telescope to
`1/(n+1) - 1/(2n+1)`; for `2n > N` all layers from `n+1` on give `1/(n+1)`.  Both are at least
`1/(2n) - 1/n²`, and `Σ 1/n² ≤ 1`.
-/

open Finset ArithmeticFunction

namespace RHTower

noncomputable section

/-- The one-sided divisor-comparable Hilbert section `Σ_{m ∣ n, m < n ≤ N} μ(m)μ(n)/(m+n)`. -/
def mobiusHilbertDivisorSection (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
    mobiusRealCoefficient m * mobiusRealCoefficient n * (1 / ((m + n : ℕ) : ℝ))

/-- The Hilbert layer weight `1/max(k,1)`. -/
def hilbertLayerWeight (k : ℕ) : ℝ := 1 / ((max k 1 : ℕ) : ℝ)

theorem hilbertLayerWeight_pos (k : ℕ) : 0 < hilbertLayerWeight k := by
  unfold hilbertLayerWeight
  have : (0 : ℝ) < ((max k 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < max k 1 by omega)
  positivity

theorem hilbertLayerWeight_antitone : Antitone hilbertLayerWeight := by
  intro a b hab
  unfold hilbertLayerWeight
  have ha : (0 : ℝ) < ((max a 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < max a 1 by omega)
  exact one_div_le_one_div_of_le ha (by exact_mod_cast max_le_max hab le_rfl)

theorem hilbertLayerWeight_of_one_le {k : ℕ} (hk : 1 ≤ k) : hilbertLayerWeight k = 1 / (k : ℝ) := by
  unfold hilbertLayerWeight
  rw [max_eq_left hk]

/-- The drift count `#{squarefree n ∈ (N'/2, N']}` with `N' = min N (K-1)`. -/
def squarefreeDriftCount (N K : ℕ) : ℝ :=
  (((Finset.Icc 2 (min N (K - 1))).filter Squarefree).card : ℝ) -
    (((Finset.Icc 2 (min N (K - 1) / 2)).filter Squarefree).card : ℝ)

/-- The drift count as a sum of indicators over squarefree `2 ≤ n ≤ N`. -/
theorem squarefreeDriftCount_eq (N K : ℕ) :
    squarefreeDriftCount N K =
      ∑ n ∈ (Finset.Icc 2 N).filter Squarefree,
        if min N (K - 1) / 2 < n ∧ n ≤ min N (K - 1) then (1 : ℝ) else 0 := by
  classical
  set N' := min N (K - 1) with hN'
  set A := (Finset.Icc 2 N').filter Squarefree with hA
  set B := (Finset.Icc 2 (N' / 2)).filter Squarefree with hB
  have hBA : B ⊆ A := by
    intro n hn
    simp only [hA, hB, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.div_le_self _ _)⟩, hn.2⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hBA
  have hsd : A \ B = ((Finset.Icc 2 N).filter Squarefree).filter
      (fun n => N' / 2 < n ∧ n ≤ N') := by
    ext n
    simp only [hA, hB, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    have hN'N : N' ≤ N := min_le_left _ _
    constructor
    · rintro ⟨⟨⟨h2, hn⟩, hsq⟩, hnot⟩
      refine ⟨⟨⟨h2, le_trans hn hN'N⟩, hsq⟩, ?_, hn⟩
      by_contra hle
      push Not at hle
      exact hnot ⟨⟨h2, hle⟩, hsq⟩
    · rintro ⟨⟨⟨h2, _⟩, hsq⟩, hlt, hn⟩
      exact ⟨⟨⟨h2, hn⟩, hsq⟩, fun h => by omega⟩
  unfold squarefreeDriftCount
  rw [← hN', ← hA, ← hB, ← hcard, Nat.cast_add, hsd, Finset.sum_boole]
  ring

private theorem mobiusRealCoefficient_sq_eq_one {n : ℕ} (hn : Squarefree n) :
    mobiusRealCoefficient n ^ 2 = 1 := by
  have hne : moebius n ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hn
  rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
    simp [mobiusRealCoefficient, hm]

private theorem mobiusRealCoefficient_eq_zero {n : ℕ} (hn : ¬Squarefree n) :
    mobiusRealCoefficient n = 0 := by
  simp [mobiusRealCoefficient, moebius_eq_zero_of_not_squarefree hn]

/-- Telescoping of the layer weights on an interval. -/
theorem sum_Ico_hilbertLayerWeight_sub (a b : ℕ) (hab : a ≤ b) :
    ∑ K ∈ Finset.Ico a b, (hilbertLayerWeight K - hilbertLayerWeight (K + 1)) =
      hilbertLayerWeight a - hilbertLayerWeight b := by
  rw [Finset.sum_Ico_eq_sum_range]
  have := Finset.sum_range_sub' (fun i => hilbertLayerWeight (a + i)) (b - a)
  simp only [add_zero, Nat.add_sub_cancel' hab] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_assoc]

/-- **Layer cake with drift.** -/
theorem mobiusHilbertDivisorSection_le_neg_drift (N : ℕ) :
    mobiusHilbertDivisorSection N ≤
      -(hilbertLayerWeight (2 * N) * squarefreeDriftCount N (2 * N) +
        ∑ K ∈ Finset.range (2 * N),
          (hilbertLayerWeight K - hilbertLayerWeight (K + 1)) * squarefreeDriftCount N K) := by
  set w := hilbertLayerWeight with hw
  set L : ℕ := 2 * N with hL
  have hpairLe : ∀ n ∈ Finset.Icc 1 N, ∀ m ∈ n.properDivisors, m + n ≤ L := by
    intro n hn m hm
    have := Nat.mem_properDivisors.mp hm
    have := (Finset.mem_Icc.mp hn).2
    omega
  have hrewrite : mobiusHilbertDivisorSection N =
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
        mobiusRealCoefficient m * mobiusRealCoefficient n * w (m + n) := by
    unfold mobiusHilbertDivisorSection
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    have hm1 := Nat.pos_of_mem_properDivisors hm
    rw [hw, hilbertLayerWeight_of_one_le (by omega)]
  have hfull : (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
      mobiusRealCoefficient m * mobiusRealCoefficient n) = divisorPairCountBelow N L := by
    unfold divisorPairCountBelow divisorPairRowBelow
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.filter_true_of_mem (hpairLe n hn)]
  have hlayer : (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
      mobiusRealCoefficient m * mobiusRealCoefficient n * w (m + n)) =
      w L * divisorPairCountBelow N L +
        ∑ K ∈ Finset.range L, (w K - w (K + 1)) * divisorPairCountBelow N K := by
    calc (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ n.properDivisors,
          mobiusRealCoefficient m * mobiusRealCoefficient n * w (m + n)) =
        ∑ n ∈ Finset.Icc 1 N,
          (w L * ∑ m ∈ n.properDivisors, mobiusRealCoefficient m * mobiusRealCoefficient n +
            ∑ K ∈ Finset.range L, (w K - w (K + 1)) * divisorPairRowBelow K n) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          exact sum_mul_weight_eq_layerCake _ _ (fun m => m + n) w L (hpairLe n hn)
      _ = w L * divisorPairCountBelow N L +
          ∑ K ∈ Finset.range L, (w K - w (K + 1)) * divisorPairCountBelow N K := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfull, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun K _ => ?_
          rw [divisorPairCountBelow, Finset.mul_sum]
  have hS : ∀ K, divisorPairCountBelow N K ≤ -squarefreeDriftCount N K := fun K => by
    unfold squarefreeDriftCount
    exact divisorPairCountBelow_le N K
  have hwL : 0 ≤ w L := (hilbertLayerWeight_pos L).le
  have h1 : w L * divisorPairCountBelow N L ≤ w L * -squarefreeDriftCount N L :=
    mul_le_mul_of_nonneg_left (hS L) hwL
  have h2 : ∑ K ∈ Finset.range L, (w K - w (K + 1)) * divisorPairCountBelow N K ≤
      ∑ K ∈ Finset.range L, (w K - w (K + 1)) * -squarefreeDriftCount N K :=
    Finset.sum_le_sum fun K _ => mul_le_mul_of_nonneg_left (hS K)
      (sub_nonneg.mpr (hilbertLayerWeight_antitone (Nat.le_succ K)))
  rw [hrewrite, hlayer]
  simp only [mul_neg, Finset.sum_neg_distrib] at h1 h2 ⊢
  linarith

/-- The layer indicator of `n` at level `K`. -/
def hilbertDriftIndicator (N K n : ℕ) : ℝ :=
  if min N (K - 1) / 2 < n ∧ n ≤ min N (K - 1) then 1 else 0

/-- The layer mass `I(n)` collected by one squarefree `n`. -/
def hilbertDriftMass (N n : ℕ) : ℝ :=
  hilbertLayerWeight (2 * N) * hilbertDriftIndicator N (2 * N) n +
    ∑ K ∈ Finset.range (2 * N),
      (hilbertLayerWeight K - hilbertLayerWeight (K + 1)) * hilbertDriftIndicator N K n

theorem weightedDrift_eq_sum_hilbertDriftMass (N : ℕ) :
    hilbertLayerWeight (2 * N) * squarefreeDriftCount N (2 * N) +
        ∑ K ∈ Finset.range (2 * N),
          (hilbertLayerWeight K - hilbertLayerWeight (K + 1)) * squarefreeDriftCount N K =
      ∑ n ∈ (Finset.Icc 2 N).filter Squarefree, hilbertDriftMass N n := by
  simp only [squarefreeDriftCount_eq, hilbertDriftMass, hilbertDriftIndicator, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range (2 * N)), ← Finset.sum_add_distrib]

theorem hilbertDriftIndicator_nonneg (N K n : ℕ) : 0 ≤ hilbertDriftIndicator N K n := by
  unfold hilbertDriftIndicator
  split_ifs <;> norm_num

/-- **Per-integer layer mass.**  Every `2 ≤ n ≤ N` collects at least `1/(2n) - 1/n²`. -/
theorem hilbertDriftMass_ge {N n : ℕ} (hn2 : 2 ≤ n) (hnN : n ≤ N) :
    1 / (2 * (n : ℝ)) - 1 / (n : ℝ) ^ 2 ≤ hilbertDriftMass N n := by
  set w := hilbertLayerWeight with hw
  have hc : ∀ K, 0 ≤ w K - w (K + 1) := fun K =>
    sub_nonneg.mpr (hilbertLayerWeight_antitone (Nat.le_succ K))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hwn1 : w (n + 1) = 1 / ((n : ℝ) + 1) := by
    rw [hw, hilbertLayerWeight_of_one_le (by omega)]
    push_cast
    ring
  have hsub : ∀ a b : ℕ, a ≤ b → b ≤ 2 * N →
      (∀ K ∈ Finset.Ico a b, hilbertDriftIndicator N K n = 1) →
      w a - w b ≤ ∑ K ∈ Finset.range (2 * N), (w K - w (K + 1)) * hilbertDriftIndicator N K n := by
    intro a b hab hb hind
    rw [← sum_Ico_hilbertLayerWeight_sub a b hab]
    calc ∑ K ∈ Finset.Ico a b, (w K - w (K + 1))
        = ∑ K ∈ Finset.Ico a b, (w K - w (K + 1)) * hilbertDriftIndicator N K n := by
          refine Finset.sum_congr rfl fun K hK => ?_
          rw [hind K hK, mul_one]
      _ ≤ ∑ K ∈ Finset.range (2 * N), (w K - w (K + 1)) * hilbertDriftIndicator N K n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun K _ _ =>
            mul_nonneg (hc K) (hilbertDriftIndicator_nonneg N K n)
          intro K hK
          rw [Finset.mem_Ico] at hK
          exact Finset.mem_range.mpr (by omega)
  have hwL : 0 ≤ w (2 * N) * hilbertDriftIndicator N (2 * N) n :=
    mul_nonneg (hilbertLayerWeight_pos _).le (hilbertDriftIndicator_nonneg N _ n)
  unfold hilbertDriftMass
  rcases le_or_gt (2 * n) N with hsmall | hlarge
  · -- small `n`: the layers `n+1 ≤ K ≤ 2n` telescope
    have hlow := hsub (n + 1) (2 * n + 1) (by omega) (by omega) (by
      intro K hK
      rw [Finset.mem_Ico] at hK
      unfold hilbertDriftIndicator
      rw [if_pos]
      have hmin : min N (K - 1) = K - 1 := min_eq_right (by omega)
      rw [hmin]
      constructor <;> omega)
    have hw2 : w (2 * n + 1) = 1 / (2 * (n : ℝ) + 1) := by
      rw [hw, hilbertLayerWeight_of_one_le (by omega)]
      push_cast
      ring
    rw [hwn1, hw2] at hlow
    have hkey : 1 / (2 * (n : ℝ)) - 1 / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / (2 * (n : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (n : ℝ), mul_pos (by linarith : (0 : ℝ) < n) (by linarith : (0 : ℝ) < n)]
    linarith
  · -- large `n`: every layer from `n+1` on collects `n`
    have hind : ∀ K ∈ Finset.Ico (n + 1) (2 * N), hilbertDriftIndicator N K n = 1 := by
      intro K hK
      rw [Finset.mem_Ico] at hK
      unfold hilbertDriftIndicator
      rw [if_pos]
      rcases le_total N (K - 1) with h1 | h1
      · rw [min_eq_left h1]
        constructor <;> omega
      · rw [min_eq_right h1]
        constructor <;> omega
    have hlow := hsub (n + 1) (2 * N) (by omega) le_rfl hind
    have hLind : hilbertDriftIndicator N (2 * N) n = 1 := by
      unfold hilbertDriftIndicator
      rw [if_pos]
      rw [min_eq_left (by omega)]
      constructor <;> omega
    rw [hLind, mul_one] at hwL ⊢
    rw [hwn1] at hlow
    have hkey : 1 / (2 * (n : ℝ)) - 1 / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
      have h1 : 1 / (2 * (n : ℝ)) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
      linarith
    linarith

theorem sum_Icc_mobiusRealCoefficient_sq_div {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, mobiusRealCoefficient n ^ 2 / (n : ℝ) =
      1 + ∑ n ∈ (Finset.Icc 2 N).filter Squarefree, 1 / (n : ℝ) := by
  classical
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp), Finset.sum_filter]
  have h1 : mobiusRealCoefficient 1 ^ 2 / ((1 : ℕ) : ℝ) = 1 := by
    simp [mobiusRealCoefficient]
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with hsq
  · rw [mobiusRealCoefficient_sq_eq_one hsq]
  · rw [mobiusRealCoefficient_eq_zero hsq]
    simp

theorem sum_squarefree_inv_sq_le (N : ℕ) :
    ∑ n ∈ (Finset.Icc 2 N).filter Squarefree, 1 / (n : ℝ) ^ 2 ≤ 1 := by
  have hsub : (Finset.Icc 2 N).filter Squarefree ⊆ Finset.Ioo 1 (N + 1) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioo] at hn ⊢
    omega
  calc ∑ n ∈ (Finset.Icc 2 N).filter Squarefree, 1 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Ioo 1 (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioo 1 (N + 1))
          (fun n => n ∈ (Finset.Icc 2 N).filter Squarefree)]
        have hfe : (Finset.Ioo 1 (N + 1)).filter (fun n => n ∈ (Finset.Icc 2 N).filter Squarefree) =
            (Finset.Icc 2 N).filter Squarefree := by
          ext n
          simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨hsub (Finset.mem_filter.mpr h), h⟩
        rw [hfe]
        have : 0 ≤ ∑ n ∈ (Finset.Ioo 1 (N + 1)).filter
            (fun n => n ∉ (Finset.Icc 2 N).filter Squarefree), ((n : ℝ) ^ 2)⁻¹ :=
          Finset.sum_nonneg fun n _ => by positivity
        have heq : ∑ n ∈ (Finset.Icc 2 N).filter Squarefree, 1 / (n : ℝ) ^ 2 =
            ∑ n ∈ (Finset.Icc 2 N).filter Squarefree, ((n : ℝ) ^ 2)⁻¹ :=
          Finset.sum_congr rfl fun n _ => one_div _
        linarith
    _ ≤ 2 / ((1 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 1 (N + 1)
    _ = 1 := by norm_num

/-- **Boundary integrality law.**  The divisor-comparable Hilbert section cancels half the harmonic
squarefree mass: `Σ_{m ∣ n, m < n ≤ N} μ(m)μ(n)/(m+n) ≤ 3/2 - (1/2) Σ_{n ≤ N} μ(n)²/n`. -/
theorem mobiusHilbertDivisorSection_le (N : ℕ) :
    mobiusHilbertDivisorSection N ≤
      3 / 2 - (1 / 2) * ∑ n ∈ Finset.Icc 1 N, mobiusRealCoefficient n ^ 2 / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    norm_num [mobiusHilbertDivisorSection]
  have hdrift := mobiusHilbertDivisorSection_le_neg_drift N
  rw [weightedDrift_eq_sum_hilbertDriftMass] at hdrift
  set T := (Finset.Icc 2 N).filter Squarefree with hT
  have hmass : ∑ n ∈ T, (1 / (2 * (n : ℝ)) - 1 / (n : ℝ) ^ 2) ≤ ∑ n ∈ T, hilbertDriftMass N n := by
    refine Finset.sum_le_sum fun n hn => ?_
    simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hilbertDriftMass_ge hn.1.1 hn.1.2
  rw [Finset.sum_sub_distrib] at hmass
  have hhalf : ∑ n ∈ T, 1 / (2 * (n : ℝ)) = (1 / 2) * ∑ n ∈ T, 1 / (n : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [one_div_mul_one_div]
  have hsq := sum_squarefree_inv_sq_le N
  have hharm := sum_Icc_mobiusRealCoefficient_sq_div hN
  rw [← hT] at hsq hharm
  linarith

/-- The Hilbert diagonal in natural indexing: `D_N = (1/2) Σ_{n ≤ N} μ(n)²/n`. -/
theorem finiteMobiusGammaHankelDiagonalEnergy_one_eq (N : ℕ) :
    finiteMobiusGammaHankelDiagonalEnergy N 1 =
      (1 / 2) * ∑ n ∈ Finset.Icc 1 N, mobiusRealCoefficient n ^ 2 / (n : ℝ) := by
  unfold finiteMobiusGammaHankelDiagonalEnergy
  rw [Real.Gamma_one, one_mul, Finset.mul_sum, ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.sum_Ico_add' (fun n : ℕ => 1 / 2 * (mobiusRealCoefficient n ^ 2 / (n : ℝ))) 0 N 1,
    ← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Real.rpow_one]
  have hco : shiftedMobiusRealCoefficient n = mobiusRealCoefficient (n + 1) := rfl
  rw [hco]
  push_cast
  field_simp

/-- The non-comparable part of the Hilbert form: the energy minus its diagonal minus twice the
divisor-comparable section. -/
def mobiusHilbertNonComparableSection (N : ℕ) : ℝ :=
  finiteMobiusGammaHankelEnergy N 1 - finiteMobiusGammaHankelDiagonalEnergy N 1 -
    2 * mobiusHilbertDivisorSection N

/-- **Integrality ceiling.**  The Hilbert energy is at most the excess of the non-comparable
section over the diagonal, plus `3`. -/
theorem finiteMobiusGammaHankelEnergy_one_le_nonComparableExcess (N : ℕ) :
    finiteMobiusGammaHankelEnergy N 1 ≤
      (mobiusHilbertNonComparableSection N - finiteMobiusGammaHankelDiagonalEnergy N 1) + 3 := by
  have h := mobiusHilbertDivisorSection_le N
  have hD := finiteMobiusGammaHankelDiagonalEnergy_one_eq N
  unfold mobiusHilbertNonComparableSection
  linarith

/-- **Positivity floor.**  The non-comparable section never falls more than `3` below the
diagonal. -/
theorem neg_three_le_nonComparableExcess (N : ℕ) :
    -3 ≤ mobiusHilbertNonComparableSection N - finiteMobiusGammaHankelDiagonalEnergy N 1 := by
  have h := finiteMobiusGammaHankelEnergy_one_le_nonComparableExcess N
  have hE := finiteMobiusGammaHankelEnergy_nonneg N (by norm_num : (0 : ℝ) < 1)
  linarith

/-- **RH from the non-comparable excess.**  If the non-comparable Möbius Hilbert section exceeds
the diagonal by only `O_ε((N+1)^ε)`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_nonComparableExcess_subpower
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      mobiusHilbertNonComparableSection N - finiteMobiusGammaHankelDiagonalEnergy N 1 ≤
        C * ((N : ℝ) + 1) ^ ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mobiusHilbertFormSubpower
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C + 3, fun N => ?_⟩
  have h1 := finiteMobiusGammaHankelEnergy_one_le_nonComparableExcess N
  have hpow : 1 ≤ ((N : ℝ) + 1) ^ ε :=
    Real.one_le_rpow (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) hε.le
  nlinarith [hC N]

end

end RHTower
