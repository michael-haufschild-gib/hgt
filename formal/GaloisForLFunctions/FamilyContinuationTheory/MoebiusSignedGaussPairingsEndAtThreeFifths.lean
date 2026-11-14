import GaloisForLFunctions.FamilyContinuationTheory.TheMoebiusParityOfAGaussMonomial
import GaloisForLFunctions.FamilyContinuationTheory.TheBudgetInTheTwistExponent

/-!
# Möbius-signed Gauss pairings end at three-fifths

A Gauss-monomial identity for the Möbius sign at primes splits `r = a + d` nontrivial finite-field
multiplicative characters `χ₁, …, χ_r` into `a` completed `m_i`-th order Gauss-sum factors (`i ∈ A`)
and `d` Poisson row twists (`j ∈ D`), evaluated at a period `k` (`k = lcm(m₁, …, m_r)` when `d = 0`,
and any positive multiple of `lcm(m₁, …, m_r)` when `d ≥ 1`). By Kubota's completion normalizing
factor `ζ_K(m w − (m − 2)/2)` (`w ↔ 1 − w`, periodicity exponent `(m − 2)/2`) and row-Poisson root
normalization `1/√Q`, the resulting local correction resonance is `R = Q^{c − k s}` with

`c = ∑_{i ∈ A} (1/2 − 1/m_i) k + d (k/2 − 1)`.

Its uncoupled Euler-product boundary is `(c + 1)/k`, its single-step Grossencharacter GRH boundary
is `(c + 1/2)/k`, and its coupled infinite-tower fixed point (`b = (c + b)/k`) is `c/(k − 1)`.

1. **Universal `2/3`, `3/5`, and `7/12` barriers (`two_thirds_le_uncoupledBoundary`,
   `three_fifths_le_coupledBarrier`, `seven_twelfths_le_grhStepBoundary`):**
   Every Möbius-signed Gauss pairing over any group with at most one involution — in particular
   `MulChar F R` over every finite field `F` and integral domain `R` — satisfies
   `(c + 1)/k ≥ 2/3`, `c/(k − 1) ≥ 3/5`, and `(c + 1/2)/k ≥ 7/12`.
2. **Nonexistence below `3/5` and on the critical line (`not_exists_moebiusGaussPairing_lt_three_fifths`,
   `not_exists_moebiusGaussPairing_reaching_critical_line`, `sInf_coupledBarrier_eq_three_fifths`):**
   No Möbius-signed Gauss pairing satisfies `c/(k − 1) < 3/5`, none satisfies `c ≤ (k − 1)/2`, and
   the greatest lower bound of `c/(k − 1)` across all finite-field Gauss pairings is `3/5`
   (attained on `ZMod 7`).
3. **Equality rigidity of `(3, 6)` and uniqueness of the cubic-sextic probe
   (`coupledBarrier_eq_three_fifths_iff`, `reduced_row_probe_eq_three_fifths_iff`):**
   `c/(k − 1) = 3/5` holds if and only if `(c, k) = (3, 6)`. Among reduced row probes (`m_i ≥ 3`,
   `d ≥ 1`), equality holds if and only if `a = 1`, `d = 1`, `m_comp = 3`, `n_row = 6`, `k = 6`.
4. **`GL₁` Liouville obstruction and universal `m ≥ 4` positive-form budget barriers
   (`hasSum_liouville_local_series`, `corner_unslotted_ge_closedForm`,
   `higher_order_quadratic_pair_budget_obstruction`):**
   Nonvanishing prime-square coefficients force `∑_{t ≥ 0} (−X)^t = (1 − X)/(1 − X²)`, introducing
   `(1 − X²)⁻¹` (`L(2s, η²)`). On the positive-form side, every quadratic-product Gauss-sum probe of
   coefficient order `m ≥ 4` and Kazhdan–Patterson conductor exponent `κ ≥ m − 1` has unslotted
   corner `≥ 25/28 > 7/8` and effective twist exponent `θ ≥ 22/21 > 1` for all row lengths `M ∈ ℝ`.
5. **General `(c, k)` coupled-tower contraction and stationary floor
   (`abscissa_le_max_fixedPoint_of_tower`, `stationary_sequence_achieves_fixedPoint`,
   `moebiusGaussPairing_tower_floor_ge_three_fifths`):**
   The affine zero-transfer recurrence `Θ_r ≤ max(σ₀, (c + Θ_{r+1})/k)` (`Θ_r ≤ 1`) contracts to
   `Θ₀ ≤ max(σ₀, c/(k − 1))` and admits the stationary solution `Θ_r ≡ c/(k − 1)` whenever
   `σ₀ ≤ c/(k − 1)`, locking every coupled Gauss-sum continuation tower at `≥ 3/5 > 1/2`.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.FamilyContinuationTheory

/-! ### 1. Formal structure of Möbius-signed Gauss pairings -/

section PairingDefinition

/-- Least common multiple of element orders across a list `L : List G`. -/
noncomputable def tupleOrderLcm {G : Type*} [Group G] (L : List G) : ℕ :=
  L.foldr (fun x acc => Nat.lcm (orderOf x) acc) 1

theorem orderOf_dvd_tupleOrderLcm {G : Type*} [Group G] {x : G} {L : List G} (hx : x ∈ L) :
    orderOf x ∣ tupleOrderLcm L := by
  induction L with
  | nil => nomatch hx
  | cons y tl ih =>
    simp only [tupleOrderLcm, List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Nat.dvd_lcm_left _ _
    · exact (ih hmem).trans (Nat.dvd_lcm_right _ _)

theorem tupleOrderLcm_pos {G : Type*} [Group G] {L : List G} (hL : ∀ x ∈ L, 2 ≤ orderOf x) :
    0 < tupleOrderLcm L := by
  induction L with
  | nil => simp [tupleOrderLcm]
  | cons y tl ih =>
    simp only [tupleOrderLcm, List.foldr_cons]
    have hy : 0 < orderOf y := by
      have := hL y List.mem_cons_self
      omega
    exact Nat.lcm_pos hy (ih fun z hz => hL z (List.mem_cons_of_mem _ hz))

theorem tupleOrderLcm_dvd_of_forall_dvd {G : Type*} [Group G] {L : List G} {m : ℕ}
    (h : ∀ x ∈ L, orderOf x ∣ m) : tupleOrderLcm L ∣ m := by
  induction L with
  | nil => exact one_dvd m
  | cons y tl ih =>
    simp only [tupleOrderLcm, List.foldr_cons]
    exact Nat.lcm_dvd (h y List.mem_cons_self) (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem tupleOrderLcm_eq_or_lcm_two {G : Type*} [Group G] {L : List G}
    (hL : ∀ x ∈ L, 2 ≤ orderOf x) :
    tupleOrderLcm L = tupleOrderLcm (nonQuadraticPart L) ∨
      tupleOrderLcm L = Nat.lcm 2 (tupleOrderLcm (nonQuadraticPart L)) := by
  by_cases hall3 : ∀ x ∈ L, 3 ≤ orderOf x
  · left
    have hfilt : nonQuadraticPart L = L := by
      simp only [nonQuadraticPart, List.filter_eq_self, decide_eq_true_eq]
      exact hall3
    rw [hfilt]
  · right
    simp only [not_forall, not_le] at hall3
    obtain ⟨q, hqL, hqlt⟩ := hall3
    have hq2 : orderOf q = 2 := by have := hL q hqL; omega
    apply Nat.dvd_antisymm
    · refine tupleOrderLcm_dvd_of_forall_dvd fun x hx => ?_
      by_cases hx3 : 3 ≤ orderOf x
      · have hxS : x ∈ nonQuadraticPart L := by
          simp [nonQuadraticPart, hx, hx3]
        exact (orderOf_dvd_tupleOrderLcm hxS).trans (Nat.dvd_lcm_right _ _)
      · have hx2 : orderOf x = 2 := by have := hL x hx; omega
        rw [hx2]
        exact Nat.dvd_lcm_left 2 _
    · refine Nat.lcm_dvd ?_ ?_
      · rw [← hq2]
        exact orderOf_dvd_tupleOrderLcm hqL
      · refine tupleOrderLcm_dvd_of_forall_dvd fun x hx => ?_
        simp only [nonQuadraticPart, List.mem_filter] at hx
        exact orderOf_dvd_tupleOrderLcm hx.1

/-- A Möbius-signed Gauss-monomial pairing `(c, k)` over a commutative group `G` (in particular
`MulChar F R`), splitting a Möbius-signed character tuple into `compChars` (completed Gauss-sum
factors) and `rowChars` (Poisson row twists) at an admissible period `period`. -/
structure MoebiusGaussPairing (G : Type*) [CommGroup G] where
  compChars : List G
  rowChars : List G
  moebius : IsMoebiusSignedTuple (compChars ++ rowChars)
  period : ℕ
  period_pos : 0 < period
  lcm_dvd_period : tupleOrderLcm (compChars ++ rowChars) ∣ period
  period_eq_of_no_rows : rowChars = [] → period = tupleOrderLcm (compChars ++ rowChars)

namespace MoebiusGaussPairing

variable {G : Type*} [CommGroup G]

/-- Local resonance exponent `c = ∑_{i ∈ A} (1/2 − 1/m_i) k + d (k/2 − 1)` (`R = Q^{c − k s}`). -/
noncomputable def pairingC (P : MoebiusGaussPairing G) : ℝ :=
  (P.compChars.map fun x => (1 / 2 - 1 / (orderOf x : ℝ)) * (P.period : ℝ)).sum +
    (P.rowChars.length : ℝ) * ((P.period : ℝ) / 2 - 1)

/-- Uncoupled Euler-product convergence boundary `(c + 1)/k`. -/
noncomputable def uncoupledBoundary (P : MoebiusGaussPairing G) : ℝ :=
  (P.pairingC + 1) / (P.period : ℝ)

/-- Coupled Grossencharacter tower fixed-point barrier `c/(k − 1)`. -/
noncomputable def coupledBarrier (P : MoebiusGaussPairing G) : ℝ :=
  P.pairingC / ((P.period : ℝ) - 1)

/-- Single-step conditional boundary `(c + 1/2)/k` under Grossencharacter GRH (`Θ_corr = 1/2`). -/
noncomputable def grhStepBoundary (P : MoebiusGaussPairing G) : ℝ :=
  (P.pairingC + 1 / 2) / (P.period : ℝ)

theorem orderOf_dvd_period (P : MoebiusGaussPairing G) {x : G}
    (hx : x ∈ P.compChars ++ P.rowChars) : orderOf x ∣ P.period :=
  (orderOf_dvd_tupleOrderLcm hx).trans P.lcm_dvd_period

/-- Every Möbius-signed Gauss pairing has period `k ≥ 3`. -/
theorem three_le_period (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    3 ≤ P.period := by
  have hlen := two_le_length_nonQuadraticPart hG P.moebius
  match hS : nonQuadraticPart (P.compChars ++ P.rowChars) with
  | [] => rw [hS] at hlen; simp at hlen
  | x :: _ =>
    have hxS : x ∈ nonQuadraticPart (P.compChars ++ P.rowChars) := by
      rw [hS]; exact List.mem_cons_self
    have hx3 : 3 ≤ orderOf x := three_le_orderOf_mem_nonQuadraticPart hxS
    have hxL : x ∈ P.compChars ++ P.rowChars := by
      simp only [nonQuadraticPart, List.mem_filter] at hxS
      exact hxS.1
    exact le_trans hx3 (Nat.le_of_dvd P.period_pos (P.orderOf_dvd_period hxL))

/-! ### 2. Universal `2/3`, `3/5`, and `7/12` barriers and `(3, 6)` rigidity -/

private noncomputable def alphaWeight (x : G) : ℝ :=
  1 / 2 - 1 / (orderOf x : ℝ)

private theorem alphaWeight_nonneg {x : G} (hx : 2 ≤ orderOf x) : 0 ≤ alphaWeight x := by
  unfold alphaWeight
  have hx' : (2 : ℝ) ≤ orderOf x := by exact_mod_cast hx
  have hdiv : 1 / (orderOf x : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hx'
  linarith

private theorem alphaWeight_ge_one_sixth {x : G} (hx : 3 ≤ orderOf x) :
    1 / 6 ≤ alphaWeight x := by
  unfold alphaWeight
  have hx' : (3 : ℝ) ≤ orderOf x := by exact_mod_cast hx
  have hdiv : 1 / (orderOf x : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) hx'
  linarith

private theorem alphaWeight_ge_one_fourth {x : G} (hx : 4 ≤ orderOf x) :
    1 / 4 ≤ alphaWeight x := by
  unfold alphaWeight
  have hx' : (4 : ℝ) ≤ orderOf x := by exact_mod_cast hx
  have hdiv : 1 / (orderOf x : ℝ) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) hx'
  linarith

private theorem comp_sum_eq_nonQuadraticPart_mul {L : List G} (k : ℝ)
    (hL : ∀ x ∈ L, 2 ≤ orderOf x) :
    (L.map fun x => (1 / 2 - 1 / (orderOf x : ℝ)) * k).sum =
      ((nonQuadraticPart L).map alphaWeight).sum * k := by
  induction L with
  | nil => simp [nonQuadraticPart]
  | cons x tl ih =>
    have hx2 : 2 ≤ orderOf x := hL x List.mem_cons_self
    have htl : ∀ y ∈ tl, 2 ≤ orderOf y := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    by_cases hx3 : 3 ≤ orderOf x
    · have hfilt : nonQuadraticPart (x :: tl) = x :: nonQuadraticPart tl := by
        simp [nonQuadraticPart, hx3]
      rw [List.map_cons, List.sum_cons, ih htl, hfilt, List.map_cons, List.sum_cons]
      unfold alphaWeight
      ring
    · have hx_eq2 : orderOf x = 2 := by omega
      have hfilt : nonQuadraticPart (x :: tl) = nonQuadraticPart tl := by
        simp [nonQuadraticPart, hx3]
      rw [List.map_cons, List.sum_cons, ih htl, hfilt, hx_eq2]
      norm_num

private theorem list_alpha_sum_ge_mul_length {S : List G} {c : ℝ}
    (hS : ∀ x ∈ S, c ≤ alphaWeight x) :
    (S.length : ℝ) * c ≤ (S.map alphaWeight).sum := by
  induction S with
  | nil => simp
  | cons x tl ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
    have hx := hS x List.mem_cons_self
    have htl := ih fun y hy => hS y (List.mem_cons_of_mem _ hy)
    linarith

private theorem row_sum_ge_nonQuadratic_alpha {D : List G} {k : ℕ} (hk3 : 3 ≤ k)
    (hD_dvd : ∀ y ∈ D, orderOf y ∣ k) :
    ((nonQuadraticPart D).map alphaWeight).sum * (k : ℝ) ≤
      (D.length : ℝ) * ((k : ℝ) / 2 - 1) := by
  have hk_pos : 0 < k := by omega
  have hk_real : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hlist : ∀ S : List G, (∀ y ∈ S, orderOf y ∣ k) →
      (S.map alphaWeight).sum * (k : ℝ) ≤ (S.length : ℝ) * ((k : ℝ) / 2 - 1) := by
    intro S hS
    induction S with
    | nil => simp
    | cons y tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hy_dvd : orderOf y ∣ k := hS y List.mem_cons_self
      have hy_le : orderOf y ≤ k := Nat.le_of_dvd hk_pos hy_dvd
      have hy_pos : 0 < orderOf y := Nat.pos_of_dvd_of_pos hy_dvd hk_pos
      have hy_real : (orderOf y : ℝ) ≤ k := by exact_mod_cast hy_le
      have hy_rpos : (0 : ℝ) < orderOf y := by exact_mod_cast hy_pos
      have hdiv_ge : 1 ≤ (k : ℝ) / (orderOf y : ℝ) := (one_le_div hy_rpos).mpr hy_real
      have hy_bound : alphaWeight y * (k : ℝ) ≤ (k : ℝ) / 2 - 1 := by
        unfold alphaWeight
        have heq : (1 / 2 - 1 / (orderOf y : ℝ)) * (k : ℝ) =
            (k : ℝ) / 2 - (k : ℝ) / (orderOf y : ℝ) := by ring
        linarith
      have htl_bound := ih fun z hz => hS z (List.mem_cons_of_mem _ hz)
      linarith
  have hterm_le := hlist (nonQuadraticPart D) fun y hy => by
    simp only [nonQuadraticPart, List.mem_filter] at hy
    exact hD_dvd y hy.1
  have hlen_le : ((nonQuadraticPart D).length : ℝ) ≤ D.length := by
    exact_mod_cast List.length_filter_le _ D
  have hpos_twist : 0 ≤ (k : ℝ) / 2 - 1 := by linarith
  exact hterm_le.trans (mul_le_mul_of_nonneg_right hlen_le hpos_twist)

/-- Pointwise dominance: `P.pairingC` is always at least `∑_{x ∈ S} (1/2 − 1/orderOf x) · k`,
where `S = nonQuadraticPart (P.compChars ++ P.rowChars)`. -/
theorem alpha_sum_mul_period_le_pairingC (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    ((nonQuadraticPart (P.compChars ++ P.rowChars)).map alphaWeight).sum * (P.period : ℝ) ≤
      P.pairingC := by
  have hk3 := P.three_le_period hG
  have hA : ∀ x ∈ P.compChars, 2 ≤ orderOf x := fun x hx =>
    P.moebius.two_le_order x (List.mem_append_left _ hx)
  have hD : ∀ y ∈ P.rowChars, orderOf y ∣ P.period := fun y hy =>
    P.orderOf_dvd_period (List.mem_append_right _ hy)
  have hsplit : nonQuadraticPart (P.compChars ++ P.rowChars) =
      nonQuadraticPart P.compChars ++ nonQuadraticPart P.rowChars := by
    simp [nonQuadraticPart, List.filter_append]
  unfold pairingC
  rw [comp_sum_eq_nonQuadraticPart_mul (P.period : ℝ) hA, hsplit, List.map_append,
    List.sum_append, add_mul]
  linarith [row_sum_ge_nonQuadratic_alpha hk3 hD]

private theorem pairingC_ge_of_period_three (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G)
    (hk : P.period = 3) : (3 / 2 : ℝ) ≤ P.pairingC := by
  set S := nonQuadraticPart (P.compChars ++ P.rowChars)
  have hlen2 : 2 ≤ S.length := two_le_length_nonQuadraticPart hG P.moebius
  have hlen3 : 3 ≤ S.length := by
    by_contra hlt
    have heq2 : S.length = 2 := by omega
    obtain ⟨x₁, x₂, hS_eq⟩ : ∃ x₁ x₂, S = [x₁, x₂] := by
      match S, heq2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨hSsq, hSpar⟩ := nonQuadraticPart_moebius_parity hG P.moebius
    rw [show nonQuadraticPart (P.compChars ++ P.rowChars) = S from rfl, hS_eq] at hSsq hSpar
    have hprod_ne : x₁ * x₂ ≠ 1 := by
      rcases hSpar with ⟨_, hodd⟩ | ⟨hp, _⟩
      · exfalso; obtain ⟨u, hu⟩ := hodd; simp at hu
      · simpa using hp
    have hprod_sq : (x₁ * x₂) ^ 2 = 1 := by simpa using hSsq
    have hq2 : orderOf (x₁ * x₂) = 2 := orderOf_eq_prime hprod_sq hprod_ne
    have hx₁3 : 3 ≤ orderOf x₁ :=
      three_le_orderOf_mem_nonQuadraticPart (hS_eq ▸ List.mem_cons_self)
    obtain ⟨_, _, h4le⟩ := even_and_four_le_lcm_of_quadratic_product hG hx₁3 hq2
    have hx₁_dvd : orderOf x₁ ∣ 3 := by
      rw [← hk]
      have hx₁S : x₁ ∈ S := hS_eq ▸ List.mem_cons_self
      simp only [S, nonQuadraticPart, List.mem_filter] at hx₁S
      exact P.orderOf_dvd_period hx₁S.1
    have hx₂_dvd : orderOf x₂ ∣ 3 := by
      rw [← hk]
      have hx₂S : x₂ ∈ S := hS_eq ▸ List.mem_cons_of_mem _ List.mem_cons_self
      simp only [S, nonQuadraticPart, List.mem_filter] at hx₂S
      exact P.orderOf_dvd_period hx₂S.1
    have hlcm_le : Nat.lcm (orderOf x₁) (orderOf x₂) ≤ 3 :=
      Nat.le_of_dvd (by decide) (Nat.lcm_dvd hx₁_dvd hx₂_dvd)
    omega
  have hsum : (S.length : ℝ) * (1 / 6) ≤ (S.map alphaWeight).sum :=
    list_alpha_sum_ge_mul_length fun x hx =>
      alphaWeight_ge_one_sixth (three_le_orderOf_mem_nonQuadraticPart hx)
  have hlen_real : (3 : ℝ) ≤ S.length := by exact_mod_cast hlen3
  have halpha : (1 / 2 : ℝ) ≤ (S.map alphaWeight).sum := by linarith
  have hbase := P.alpha_sum_mul_period_le_pairingC hG
  rw [hk] at hbase
  push_cast at hbase
  linarith

private theorem pairingC_ge_of_period_four (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G)
    (hk : P.period = 4) : (2 : ℝ) ≤ P.pairingC := by
  set S := nonQuadraticPart (P.compChars ++ P.rowChars)
  have hlen2 := two_le_length_nonQuadraticPart hG P.moebius
  have hall4 : ∀ x ∈ S, 4 ≤ orderOf x := by
    intro x hx
    have hx3 : 3 ≤ orderOf x := three_le_orderOf_mem_nonQuadraticPart hx
    have hx_dvd : orderOf x ∣ 4 := by
      rw [← hk]
      simp only [S, nonQuadraticPart, List.mem_filter] at hx
      exact P.orderOf_dvd_period hx.1
    have hx_le : orderOf x ≤ 4 := Nat.le_of_dvd (by decide) hx_dvd
    by_cases h3 : orderOf x = 3
    · rw [h3] at hx_dvd; norm_num at hx_dvd
    · omega
  have hsum : (S.length : ℝ) * (1 / 4) ≤ (S.map alphaWeight).sum :=
    list_alpha_sum_ge_mul_length fun x hx => alphaWeight_ge_one_fourth (hall4 x hx)
  have hlen_real : (2 : ℝ) ≤ S.length := by exact_mod_cast hlen2
  have halpha : (1 / 2 : ℝ) ≤ (S.map alphaWeight).sum := by linarith
  have hbase := P.alpha_sum_mul_period_le_pairingC hG
  rw [hk] at hbase
  push_cast at hbase
  linarith

private theorem pairingC_ge_of_period_five (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G)
    (hk : P.period = 5) : (3 : ℝ) ≤ P.pairingC := by
  set S := nonQuadraticPart (P.compChars ++ P.rowChars)
  have hlen2 := two_le_length_nonQuadraticPart hG P.moebius
  have hall5 : ∀ x ∈ S, (3 / 10 : ℝ) ≤ alphaWeight x := by
    intro x hx
    have hx3 : 3 ≤ orderOf x := three_le_orderOf_mem_nonQuadraticPart hx
    have hx_dvd : orderOf x ∣ 5 := by
      rw [← hk]
      simp only [S, nonQuadraticPart, List.mem_filter] at hx
      exact P.orderOf_dvd_period hx.1
    have hx_le : orderOf x ≤ 5 := Nat.le_of_dvd (by decide) hx_dvd
    have hx5 : orderOf x = 5 := by
      by_cases h3 : orderOf x = 3
      · rw [h3] at hx_dvd; norm_num at hx_dvd
      · by_cases h4 : orderOf x = 4
        · rw [h4] at hx_dvd; norm_num at hx_dvd
        · omega
    unfold alphaWeight
    rw [hx5]
    norm_num
  have hsum : (S.length : ℝ) * (3 / 10) ≤ (S.map alphaWeight).sum :=
    list_alpha_sum_ge_mul_length hall5
  have hlen_real : (2 : ℝ) ≤ S.length := by exact_mod_cast hlen2
  have halpha : (3 / 5 : ℝ) ≤ (S.map alphaWeight).sum := by linarith
  have hbase := P.alpha_sum_mul_period_le_pairingC hG
  rw [hk] at hbase
  push_cast at hbase
  linarith

/-- Core linear lower bound `c ≥ (2/3) k − 1` across all Möbius-signed Gauss pairings. -/
theorem two_thirds_mul_period_sub_one_le_pairingC (hG : HasUniqueOrderTwo G)
    (P : MoebiusGaussPairing G) :
    (2 / 3 : ℝ) * (P.period : ℝ) - 1 ≤ P.pairingC := by
  have hk3 := P.three_le_period hG
  by_cases hk_lt6 : P.period < 6
  · interval_cases hk_val : P.period
    · have hc := pairingC_ge_of_period_three hG P hk_val
      norm_num; linarith
    · have hc := pairingC_ge_of_period_four hG P hk_val
      norm_num; linarith
    · have hc := pairingC_ge_of_period_five hG P hk_val
      norm_num; linarith
  · have hk6 : 6 ≤ P.period := by omega
    have hk6_real : (6 : ℝ) ≤ P.period := by exact_mod_cast hk6
    by_cases hrows : P.rowChars = []
    · -- `d = 0`: `period = tupleOrderLcm compChars`
      have hk_lcm : P.period = tupleOrderLcm P.compChars := by
        simpa [hrows] using P.period_eq_of_no_rows hrows
      have hA2 : ∀ x ∈ P.compChars, 2 ≤ orderOf x := fun x hx =>
        P.moebius.two_le_order x (List.mem_append_left _ hx)
      have hc_eq : P.pairingC = ((nonQuadraticPart P.compChars).map alphaWeight).sum * P.period := by
        unfold pairingC
        rw [hrows, List.length_nil, Nat.cast_zero, zero_mul, add_zero]
        exact comp_sum_eq_nonQuadraticPart_mul (P.period : ℝ) hA2
      set S := nonQuadraticPart P.compChars
      have hS_full : nonQuadraticPart (P.compChars ++ P.rowChars) = S := by simp [S, hrows]
      have hlen2 : 2 ≤ S.length := hS_full ▸ two_le_length_nonQuadraticPart hG P.moebius
      obtain ⟨hSsq, hSpar⟩ := nonQuadraticPart_moebius_parity hG P.moebius
      rw [hS_full] at hSsq hSpar
      by_cases hlen4 : 4 ≤ S.length
      · have hsum : (S.length : ℝ) * (1 / 6) ≤ (S.map alphaWeight).sum :=
          list_alpha_sum_ge_mul_length fun x hx =>
            alphaWeight_ge_one_sixth (three_le_orderOf_mem_nonQuadraticPart hx)
        have hlen_real : (4 : ℝ) ≤ S.length := by exact_mod_cast hlen4
        have halpha : (2 / 3 : ℝ) ≤ (S.map alphaWeight).sum := by linarith
        have hprod : (2 / 3 : ℝ) * P.period ≤ (S.map alphaWeight).sum * P.period :=
          mul_le_mul_of_nonneg_right halpha (by positivity)
        linarith
      · by_cases hlen3 : S.length = 3
        · obtain ⟨x₁, x₂, x₃, hS_eq⟩ : ∃ x₁ x₂ x₃, S = [x₁, x₂, x₃] := by
            match S, hlen3 with
            | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
          have hx₁3 : 3 ≤ orderOf x₁ :=
            three_le_orderOf_mem_nonQuadraticPart (hS_eq ▸ List.mem_cons_self)
          have hx₂3 : 3 ≤ orderOf x₂ :=
            three_le_orderOf_mem_nonQuadraticPart
              (hS_eq ▸ List.mem_cons_of_mem _ List.mem_cons_self)
          have hx₃3 : 3 ≤ orderOf x₃ :=
            three_le_orderOf_mem_nonQuadraticPart
              (hS_eq ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          have hprod1 : x₁ * x₂ * x₃ = 1 := by
            rcases hSpar with ⟨hp, _⟩ | ⟨_, hev⟩
            · rw [hS_eq] at hp; simpa [mul_assoc] using hp
            · exfalso; rw [hlen3] at hev; obtain ⟨u, hu⟩ := hev; omega
          rcases three_orders_of_prod_eq_one hx₁3 hx₂3 hx₃3 hprod1 with
            ⟨e₁, e₂, e₃⟩ | ⟨g₁, g₂⟩ | ⟨g₁, g₃⟩ | ⟨g₂, g₃⟩
          · -- `(3, 3, 3)` with `k ≥ 6` forces `k = 6` and `c = 3`
            have hlcmS : tupleOrderLcm S = 3 := by
              simp [hS_eq, tupleOrderLcm, e₁, e₂, e₃]
            have hk_eq6 : P.period = 6 := by
              rcases tupleOrderLcm_eq_or_lcm_two hA2 with heq | heq2
              · rw [hk_lcm, heq, hlcmS] at hk6; omega
              · rw [hk_lcm, heq2, hlcmS]; decide
            have halpha_eq : (S.map alphaWeight).sum = 1 / 2 := by
              simp [hS_eq, alphaWeight, e₁, e₂, e₃]
              norm_num
            rw [hc_eq, halpha_eq, hk_eq6]
            norm_num
          · have ha₁ := alphaWeight_ge_one_fourth g₁
            have ha₂ := alphaWeight_ge_one_fourth g₂
            have ha₃ := alphaWeight_ge_one_sixth hx₃3
            have halpha : (2 / 3 : ℝ) ≤ (S.map alphaWeight).sum := by
              simp only [hS_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
              linarith
            have hprod : (2 / 3 : ℝ) * P.period ≤ (S.map alphaWeight).sum * P.period :=
              mul_le_mul_of_nonneg_right halpha (by positivity)
            linarith
          · have ha₁ := alphaWeight_ge_one_fourth g₁
            have ha₂ := alphaWeight_ge_one_sixth hx₂3
            have ha₃ := alphaWeight_ge_one_fourth g₃
            have halpha : (2 / 3 : ℝ) ≤ (S.map alphaWeight).sum := by
              simp only [hS_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
              linarith
            have hprod : (2 / 3 : ℝ) * P.period ≤ (S.map alphaWeight).sum * P.period :=
              mul_le_mul_of_nonneg_right halpha (by positivity)
            linarith
          · have ha₁ := alphaWeight_ge_one_sixth hx₁3
            have ha₂ := alphaWeight_ge_one_fourth g₂
            have ha₃ := alphaWeight_ge_one_fourth g₃
            have halpha : (2 / 3 : ℝ) ≤ (S.map alphaWeight).sum := by
              simp only [hS_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
              linarith
            have hprod : (2 / 3 : ℝ) * P.period ≤ (S.map alphaWeight).sum * P.period :=
              mul_le_mul_of_nonneg_right halpha (by positivity)
            linarith
        · -- `S.length = 2`
          have hlen_eq2 : S.length = 2 := by omega
          obtain ⟨x₁, x₂, hS_eq⟩ : ∃ x₁ x₂, S = [x₁, x₂] := by
            match S, hlen_eq2 with
            | [a, b], _ => exact ⟨a, b, rfl⟩
          have hx₁3 : 3 ≤ orderOf x₁ :=
            three_le_orderOf_mem_nonQuadraticPart (hS_eq ▸ List.mem_cons_self)
          have hprod_ne : x₁ * x₂ ≠ 1 := by
            rcases hSpar with ⟨_, hodd⟩ | ⟨hp, _⟩
            · exfalso; rw [hlen_eq2] at hodd; obtain ⟨u, hu⟩ := hodd; omega
            · rw [hS_eq] at hp; simpa using hp
          have hprod_sq : (x₁ * x₂) ^ 2 = 1 := by rw [hS_eq] at hSsq; simpa using hSsq
          have hq2 : orderOf (x₁ * x₂) = 2 := orderOf_eq_prime hprod_sq hprod_ne
          have hlcmS_eq : tupleOrderLcm S = Nat.lcm (orderOf x₁) (orderOf x₂) := by
            simp [hS_eq, tupleOrderLcm]
          obtain ⟨_, hev_lcm, _⟩ := even_and_four_le_lcm_of_quadratic_product hG hx₁3 hq2
          have hk_eq_lcm : P.period = Nat.lcm (orderOf x₁) (orderOf x₂) := by
            rcases tupleOrderLcm_eq_or_lcm_two hA2 with heq | heq2
            · rw [hk_lcm, heq, hlcmS_eq]
            · rw [hk_lcm, heq2, hlcmS_eq]
              obtain ⟨w, hw⟩ := hev_lcm
              exact Nat.lcm_eq_right ⟨w, by omega⟩
          rcases quadratic_product_order_trichotomy hG hx₁3 hq2 with
            ⟨_, hm₂, hlcm⟩ | ⟨m₀, _, hm₀3, hm₁, hm₂, hlcm⟩ | ⟨_, hm₂, hlcm⟩
          · -- `(m₁, 2 m₁)`: `k = 2 m₁`, `c = k - 3 ≥ (2/3) k - 1`
            have hk_val : P.period = 2 * orderOf x₁ := hk_eq_lcm.trans hlcm
            have hm₁_pos : (0 : ℝ) < orderOf x₁ := by exact_mod_cast (by omega : 0 < orderOf x₁)
            have hc_val : P.pairingC = (P.period : ℝ) - 3 := by
              rw [hc_eq, hS_eq]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
                alphaWeight, hm₂, hk_val, Nat.cast_mul, Nat.cast_ofNat]
              field_simp [hm₁_pos.ne']
              ring
            linarith
          · -- `(2 m₀, m₀)`: `k = 2 m₀`, `c = k - 3 ≥ (2/3) k - 1`
            have hk_val : P.period = 2 * m₀ := hk_eq_lcm.trans hlcm
            have hm₀_pos : (0 : ℝ) < m₀ := by exact_mod_cast (by omega : 0 < m₀)
            have hc_val : P.pairingC = (P.period : ℝ) - 3 := by
              rw [hc_eq, hS_eq]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
                alphaWeight, hm₁, hm₂, hk_val, Nat.cast_mul, Nat.cast_ofNat]
              field_simp [hm₀_pos.ne']
              ring
            linarith
          · -- `(4u, 4u)`: `k = m₁ ≥ 6`, `c = k - 2 > (2/3) k - 1`
            have hk_val : P.period = orderOf x₁ := hk_eq_lcm.trans hlcm
            have hm₁_pos : (0 : ℝ) < orderOf x₁ := by exact_mod_cast (by omega : 0 < orderOf x₁)
            have hc_val : P.pairingC = (P.period : ℝ) - 2 := by
              rw [hc_eq, hS_eq]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
                alphaWeight, hm₂, hk_val]
              field_simp [hm₁_pos.ne']
              ring
            linarith
    · -- `d ≥ 1`: at least one row twist
      have hd1 : 1 ≤ P.rowChars.length := List.length_pos_iff.mpr hrows
      have hA2 : ∀ x ∈ P.compChars, 2 ≤ orderOf x := fun x hx =>
        P.moebius.two_le_order x (List.mem_append_left _ hx)
      have hcomp_eq := comp_sum_eq_nonQuadraticPart_mul (P.period : ℝ) hA2
      by_cases hSA : nonQuadraticPart P.compChars = []
      · -- All `S` elements lie in `rowChars`, so `d ≥ S.length ≥ 2`
        have hsplit : nonQuadraticPart (P.compChars ++ P.rowChars) =
            nonQuadraticPart P.compChars ++ nonQuadraticPart P.rowChars := by
          simp [nonQuadraticPart, List.filter_append]
        rw [hSA, List.nil_append] at hsplit
        have hd2 : 2 ≤ P.rowChars.length := by
          have hlenS := two_le_length_nonQuadraticPart hG P.moebius
          rw [hsplit] at hlenS
          exact le_trans hlenS (List.length_filter_le _ P.rowChars)
        have hd2_real : (2 : ℝ) ≤ P.rowChars.length := by exact_mod_cast hd2
        have hcomp_nn : 0 ≤ ((nonQuadraticPart P.compChars).map alphaWeight).sum * P.period := by
          rw [hSA]; simp
        unfold pairingC
        rw [hcomp_eq]
        nlinarith
      · -- At least one element of `S` lies in `compChars` (`≥ k/6`) plus `d ≥ 1` (`≥ k/2 − 1`)
        obtain ⟨x, hxSA⟩ := List.exists_mem_of_ne_nil (nonQuadraticPart P.compChars) hSA
        have hx3 : 3 ≤ orderOf x := three_le_orderOf_mem_nonQuadraticPart hxSA
        have hcomp_ge : (1 / 6 : ℝ) ≤ ((nonQuadraticPart P.compChars).map alphaWeight).sum := by
          have hnonneg : ∀ y ∈ nonQuadraticPart P.compChars, 0 ≤ alphaWeight y := fun y hy =>
            alphaWeight_nonneg (le_trans (by decide) (three_le_orderOf_mem_nonQuadraticPart hy))
          have hsingle : ∀ L : List G, x ∈ L → (∀ y ∈ L, 0 ≤ alphaWeight y) →
              alphaWeight x ≤ (L.map alphaWeight).sum := by
            intro L hxL hnn
            induction L with
            | nil => nomatch hxL
            | cons z tl ih =>
              simp only [List.map_cons, List.sum_cons]
              rcases List.mem_cons.mp hxL with rfl | hmem
              · have htl_nn : 0 ≤ (tl.map alphaWeight).sum := by
                  simpa using list_alpha_sum_ge_mul_length
                    (c := 0) (fun y hy => hnn y (List.mem_cons_of_mem _ hy))
                linarith
              · have hz_nn := hnn z List.mem_cons_self
                have htl_ge := ih hmem (fun y hy => hnn y (List.mem_cons_of_mem _ hy))
                linarith
          exact le_trans (alphaWeight_ge_one_sixth hx3)
            (hsingle (nonQuadraticPart P.compChars) hxSA hnonneg)
        have hd1_real : (1 : ℝ) ≤ P.rowChars.length := by exact_mod_cast hd1
        have hprod : (1 / 6 : ℝ) * P.period ≤
            ((nonQuadraticPart P.compChars).map alphaWeight).sum * P.period :=
          mul_le_mul_of_nonneg_right hcomp_ge (by positivity)
        unfold pairingC
        rw [hcomp_eq]
        nlinarith

/-- **Universal uncoupled `2/3` barrier.** Every Möbius-signed Gauss pairing satisfies
`(c + 1)/k ≥ 2/3`. -/
theorem two_thirds_le_uncoupledBoundary (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    2 / 3 ≤ P.uncoupledBoundary := by
  have hk_pos : (0 : ℝ) < P.period := by exact_mod_cast P.period_pos
  unfold uncoupledBoundary
  rw [le_div_iff₀ hk_pos]
  linarith [P.two_thirds_mul_period_sub_one_le_pairingC hG]

/-- **Universal coupled `3/5` barrier.** Every Möbius-signed Gauss pairing satisfies
`c/(k − 1) ≥ 3/5`. -/
theorem three_fifths_le_coupledBarrier (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    3 / 5 ≤ P.coupledBarrier := by
  have hk3 := P.three_le_period hG
  have hk1_pos : (0 : ℝ) < (P.period : ℝ) - 1 := by
    have : (3 : ℝ) ≤ P.period := by exact_mod_cast hk3
    linarith
  unfold coupledBarrier
  rw [le_div_iff₀ hk1_pos]
  by_cases hk_lt6 : P.period < 6
  · interval_cases hk_val : P.period
    · have hc := pairingC_ge_of_period_three hG P hk_val
      norm_num; linarith
    · have hc := pairingC_ge_of_period_four hG P hk_val
      norm_num; linarith
    · have hc := pairingC_ge_of_period_five hG P hk_val
      norm_num; linarith
  · have hk6_real : (6 : ℝ) ≤ P.period := by exact_mod_cast (by omega : 6 ≤ P.period)
    have hc := P.two_thirds_mul_period_sub_one_le_pairingC hG
    linarith

/-- **Universal single-step GRH `7/12` barrier.** Every Möbius-signed Gauss pairing satisfies
`(c + 1/2)/k ≥ 7/12`. -/
theorem seven_twelfths_le_grhStepBoundary (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    7 / 12 ≤ P.grhStepBoundary := by
  have hk3 := P.three_le_period hG
  have hk_pos : (0 : ℝ) < P.period := by exact_mod_cast P.period_pos
  unfold grhStepBoundary
  rw [le_div_iff₀ hk_pos]
  by_cases hk_lt6 : P.period < 6
  · interval_cases hk_val : P.period
    · have hc := pairingC_ge_of_period_three hG P hk_val
      norm_num; linarith
    · have hc := pairingC_ge_of_period_four hG P hk_val
      norm_num; linarith
    · have hc := pairingC_ge_of_period_five hG P hk_val
      norm_num; linarith
  · have hk6_real : (6 : ℝ) ≤ P.period := by exact_mod_cast (by omega : 6 ≤ P.period)
    have hc := P.two_thirds_mul_period_sub_one_le_pairingC hG
    linarith

/-- **Equality rigidity of `(3, 6)`.** Across all Möbius-signed Gauss pairings,
`c/(k − 1) = 3/5` holds if and only if `c = 3` and `k = 6`. -/
theorem coupledBarrier_eq_three_fifths_iff (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    P.coupledBarrier = 3 / 5 ↔ P.pairingC = 3 ∧ P.period = 6 := by
  constructor
  · intro heq
    have hk3 := P.three_le_period hG
    have hk1_pos : (0 : ℝ) < (P.period : ℝ) - 1 := by
      have : (3 : ℝ) ≤ P.period := by exact_mod_cast hk3
      linarith
    unfold coupledBarrier at heq
    have hmul : P.pairingC = 3 / 5 * ((P.period : ℝ) - 1) := (div_eq_iff hk1_pos.ne').mp heq
    by_cases hk_lt6 : P.period < 6
    · exfalso
      interval_cases hk_val : P.period
      · have hc := pairingC_ge_of_period_three hG P hk_val
        norm_num at hmul; linarith
      · have hc := pairingC_ge_of_period_four hG P hk_val
        norm_num at hmul; linarith
      · have hc := pairingC_ge_of_period_five hG P hk_val
        norm_num at hmul; linarith
    · have hk6 : 6 ≤ P.period := by omega
      have hk6_real : (6 : ℝ) ≤ P.period := by exact_mod_cast hk6
      have hc_lo := P.two_thirds_mul_period_sub_one_le_pairingC hG
      have hk_le6_real : (P.period : ℝ) ≤ 6 := by linarith
      have hk_le6 : P.period ≤ 6 := by exact_mod_cast hk_le6_real
      have hk_eq6 : P.period = 6 := by omega
      refine ⟨?_, hk_eq6⟩
      rw [hk_eq6] at hmul
      norm_num at hmul
      exact hmul
  · rintro ⟨hc, hk⟩
    unfold coupledBarrier
    rw [hc, hk]
    norm_num

/-- **Uniqueness of the canonical cubic-sextic row probe.** Among reduced row probes (all character
orders `≥ 3` and at least one Poisson row twist `rowChars ≠ []`), `c/(k − 1) = 3/5` holds if and
only if `compChars = [χ]` (`orderOf χ = 3`), `rowChars = [φ]` (`orderOf φ = 6`), and `period = 6`. -/
theorem reduced_row_probe_eq_three_fifths_iff (hG : HasUniqueOrderTwo G)
    (P : MoebiusGaussPairing G)
    (hred : ∀ x ∈ P.compChars ++ P.rowChars, 3 ≤ orderOf x)
    (hrows : P.rowChars ≠ []) :
    P.coupledBarrier = 3 / 5 ↔
      ∃ χ φ : G, P.compChars = [χ] ∧ P.rowChars = [φ] ∧
        orderOf χ = 3 ∧ orderOf φ = 6 ∧ P.period = 6 := by
  rw [P.coupledBarrier_eq_three_fifths_iff hG]
  constructor
  · rintro ⟨hc, hk⟩
    have hA3 : ∀ x ∈ P.compChars, 3 ≤ orderOf x := fun x hx =>
      hred x (List.mem_append_left _ hx)
    have hA2 : ∀ x ∈ P.compChars, 2 ≤ orderOf x := fun x hx => le_trans (by decide) (hA3 x hx)
    have hSA_eq : nonQuadraticPart P.compChars = P.compChars := by
      simp only [nonQuadraticPart, List.filter_eq_self, decide_eq_true_eq]
      exact hA3
    have hc_decomp : P.pairingC =
        (P.compChars.map alphaWeight).sum * 6 + (P.rowChars.length : ℝ) * 2 := by
      unfold pairingC
      rw [comp_sum_eq_nonQuadraticPart_mul (P.period : ℝ) hA2, hSA_eq, hk]
      norm_num
    have hcomp_ge : (P.compChars.length : ℝ) * (1 / 6) ≤ (P.compChars.map alphaWeight).sum :=
      list_alpha_sum_ge_mul_length fun x hx => alphaWeight_ge_one_sixth (hA3 x hx)
    have hd1 : 1 ≤ P.rowChars.length := List.length_pos_iff.mpr hrows
    have hd_le1 : P.rowChars.length ≤ 1 := by
      have hcomp_nn : 0 ≤ (P.compChars.map alphaWeight).sum :=
        le_trans (by positivity) hcomp_ge
      have hdr : (P.rowChars.length : ℝ) ≤ 3 / 2 := by linarith
      have : P.rowChars.length < 2 := by
        by_contra hge2
        have hr2 : (2 : ℝ) ≤ P.rowChars.length := by exact_mod_cast (by omega : 2 ≤ P.rowChars.length)
        linarith
      omega
    have hd_eq1 : P.rowChars.length = 1 := by omega
    obtain ⟨φ, hφ_eq⟩ : ∃ φ, P.rowChars = [φ] := by
      match P.rowChars, hd_eq1 with
      | [b], _ => exact ⟨b, rfl⟩
    have hsum_eq : (P.compChars.map alphaWeight).sum = 1 / 6 := by
      rw [hd_eq1, Nat.cast_one] at hc_decomp
      linarith
    have hS_full : nonQuadraticPart (P.compChars ++ P.rowChars) = P.compChars ++ P.rowChars := by
      simp only [nonQuadraticPart, List.filter_eq_self, decide_eq_true_eq]
      exact hred
    have hlen_tot : 2 ≤ (P.compChars ++ P.rowChars).length :=
      hS_full ▸ two_le_length_nonQuadraticPart hG P.moebius
    have ha1 : 1 ≤ P.compChars.length := by
      rw [List.length_append, hd_eq1] at hlen_tot
      omega
    have ha_le1 : P.compChars.length ≤ 1 := by
      have har : (P.compChars.length : ℝ) ≤ 1 := by linarith
      exact_mod_cast har
    have ha_eq1 : P.compChars.length = 1 := by omega
    obtain ⟨χ, hχ_eq⟩ : ∃ χ, P.compChars = [χ] := by
      match P.compChars, ha_eq1 with
      | [a], _ => exact ⟨a, rfl⟩
    have hχ_ord_real : (orderOf χ : ℝ) = 3 := by
      rw [hχ_eq] at hsum_eq
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        alphaWeight] at hsum_eq
      have hinv : 1 / (orderOf χ : ℝ) = 1 / 3 := by linarith
      rw [one_div, one_div] at hinv
      exact inv_inj.mp hinv
    have hχ_ord : orderOf χ = 3 := by exact_mod_cast hχ_ord_real
    have hprod_sq : (χ * φ) ^ 2 = 1 := by
      have hsq := P.moebius.prod_sq_eq_one
      rw [hχ_eq, hφ_eq] at hsq
      simpa using hsq
    have hprod_ne : χ * φ ≠ 1 := by
      rcases P.moebius.parity with ⟨_, hodd⟩ | ⟨hp, _⟩
      · exfalso
        rw [hχ_eq, hφ_eq] at hodd
        obtain ⟨u, hu⟩ := hodd; simp at hu
      · rw [hχ_eq, hφ_eq] at hp
        simpa using hp
    have hq2 : orderOf (χ * φ) = 2 := orderOf_eq_prime hprod_sq hprod_ne
    have hφ_ord : orderOf φ = 6 := by
      rcases quadratic_product_order_trichotomy hG (by omega : 3 ≤ orderOf χ) hq2 with
        ⟨_, hm₂, _⟩ | ⟨m₀, _, _, hm₁, _, _⟩ | ⟨h4, _, _⟩
      · omega
      · omega
      · rw [hχ_ord] at h4; norm_num at h4
    exact ⟨χ, φ, hχ_eq, hφ_eq, hχ_ord, hφ_ord, hk⟩
  · rintro ⟨χ, φ, hχ_eq, hφ_eq, hχ_ord, _, hk⟩
    refine ⟨?_, hk⟩
    unfold pairingC
    rw [hχ_eq, hφ_eq, hk]
    simp [hχ_ord]
    norm_num

end MoebiusGaussPairing

/-! ### Direct specialization to finite-field multiplicative characters `MulChar F R` -/

/-- **Definitive negative answer to `c/(k − 1) < 3/5` for finite-field Gauss pairings.** There is
no finite field `F`, integral domain `R`, and Möbius-signed Gauss pairing `P` on `MulChar F R` with
`P.coupledBarrier < 3/5`. -/
theorem not_exists_moebiusGaussPairing_lt_three_fifths :
    ¬ ∃ (F : Type*) (_ : Field F) (_ : Fintype F)
        (R : Type*) (_ : CommRing R) (_ : IsDomain R)
        (P : MoebiusGaussPairing (MulChar F R)),
        P.coupledBarrier < 3 / 5 := by
  rintro ⟨F, _, _, R, _, _, P, hlt⟩
  have hge := P.three_fifths_le_coupledBarrier (mulChar_hasUniqueOrderTwo F R)
  linarith

/-- **Definitive negative answer to `c ≤ (k − 1)/2` (critical-line reach) for finite-field Gauss
pairings.** No Möbius-signed Gauss pairing on `MulChar F R` satisfies `c ≤ (k − 1)/2`. -/
theorem not_exists_moebiusGaussPairing_reaching_critical_line :
    ¬ ∃ (F : Type*) (_ : Field F) (_ : Fintype F)
        (R : Type*) (_ : CommRing R) (_ : IsDomain R)
        (P : MoebiusGaussPairing (MulChar F R)),
        P.pairingC ≤ ((P.period : ℝ) - 1) / 2 := by
  rintro ⟨F, _, _, R, _, _, P, hle⟩
  have hG := mulChar_hasUniqueOrderTwo F R
  have hk3 := P.three_le_period hG
  have hk1_pos : (0 : ℝ) < (P.period : ℝ) - 1 := by
    have : (3 : ℝ) ≤ P.period := by exact_mod_cast hk3
    linarith
  have hbar := P.three_fifths_le_coupledBarrier hG
  unfold MoebiusGaussPairing.coupledBarrier at hbar
  have hle_half : P.pairingC / ((P.period : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ hk1_pos]
    linarith
  linarith

/-- Unconditional witness on `F = ZMod 7` realizing the canonical cubic-sextic pairing `(c, k) = (3, 6)`
with coupled barrier `3/5`, uncoupled boundary `2/3`, and GRH single-step boundary `7/12`. -/
theorem exists_zmod_seven_canonical_pairing :
    ∃ P : MoebiusGaussPairing (MulChar (ZMod 7) ℂ),
      P.pairingC = 3 ∧ P.period = 6 ∧
      P.uncoupledBoundary = 2 / 3 ∧ P.coupledBarrier = 3 / 5 ∧ P.grhStepBoundary = 7 / 12 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hexp_ne : Monoid.exponent (ZMod 7)ˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod 7)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp (Monoid.exponent (ZMod 7)ˣ) hexp_ne⟩,
      rootsOfUnity.isCyclic _ _⟩
  obtain ⟨e⟩ := MulChar.mulEquiv_units (ZMod 7) ℂ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod 7)ˣ)
  have hcard_u : Fintype.card (ZMod 7)ˣ = 6 := by
    rw [Fintype.card_units, ZMod.card 7]
  have hord_g : orderOf g = 6 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_u]
  let φ : MulChar (ZMod 7) ℂ := e.symm g
  have hord_φ : orderOf φ = 6 := by rw [MulEquiv.orderOf_eq, hord_g]
  let χ : MulChar (ZMod 7) ℂ := φ ^ 2
  have hord_χ : orderOf χ = 3 := by
    rw [orderOf_pow' φ two_ne_zero, hord_φ]
    decide
  have hprod_eq : χ * φ = φ ^ 3 := by change φ ^ 2 * φ = φ ^ 3; rw [← pow_succ]
  have hord_prod : orderOf (χ * φ) = 2 := by
    rw [hprod_eq, orderOf_pow' φ (by decide), hord_φ]
    decide
  have hmoeb : IsMoebiusSignedTuple [χ, φ] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega
    · simp only [List.prod_cons, List.prod_nil, mul_one]
      exact hord_prod ▸ pow_orderOf_eq_one (χ * φ)
    · right
      refine ⟨?_, ⟨1, rfl⟩⟩
      simp only [List.prod_cons, List.prod_nil, mul_one]
      intro h1
      rw [h1, orderOf_one] at hord_prod
      omega
  have hlcm_eq : tupleOrderLcm [χ, φ] = 6 := by
    simp [tupleOrderLcm, hord_χ, hord_φ]
    decide
  let P : MoebiusGaussPairing (MulChar (ZMod 7) ℂ) :=
    { compChars := [χ]
      rowChars := [φ]
      moebius := hmoeb
      period := 6
      period_pos := by decide
      lcm_dvd_period := by simp [hlcm_eq]
      period_eq_of_no_rows := fun h => by nomatch h }
  have hc : P.pairingC = 3 := by
    simp [P, MoebiusGaussPairing.pairingC, hord_χ]
    norm_num
  refine ⟨P, hc, rfl, ?_, ?_, ?_⟩
  · simp [MoebiusGaussPairing.uncoupledBoundary, hc, P]; norm_num
  · simp [MoebiusGaussPairing.coupledBarrier, hc, P]; norm_num
  · simp [MoebiusGaussPairing.grhStepBoundary, hc, P]; norm_num

/-- **Exact infimum `3/5` across all finite-field Gauss pairings.** -/
theorem sInf_coupledBarrier_eq_three_fifths :
    sInf {r : ℝ | ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (P : MoebiusGaussPairing (MulChar F ℂ)), r = P.coupledBarrier} = 3 / 5 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨P₀, _, _, _, hbar₀, _⟩ := exists_zmod_seven_canonical_pairing
  apply le_antisymm
  · refine csInf_le ⟨3 / 5, ?_⟩ ⟨ZMod 7, inferInstance, inferInstance, P₀, hbar₀.symm⟩
    rintro r ⟨F, hF₁, hF₂, P, rfl⟩
    exact P.three_fifths_le_coupledBarrier (@mulChar_hasUniqueOrderTwo F hF₁ hF₂ ℂ _ _)
  · refine le_csInf ⟨P₀.coupledBarrier, ZMod 7, inferInstance, inferInstance, P₀, rfl⟩ ?_
    rintro r ⟨F, hF₁, hF₂, P, rfl⟩
    exact P.three_fifths_le_coupledBarrier (@mulChar_hasUniqueOrderTwo F hF₁ hF₂ ℂ _ _)

end PairingDefinition

/-! ### 3. `GL₁` Liouville obstruction and universal `m ≥ 4` exponent-budget barriers -/

section AnalyticAndBudgetObstructions

/-- **`GL₁` Liouville local-factor obstruction.** On the open unit disc `‖X‖ < 1`, a completely
multiplicative local series with `−1` prime sign sums to `(1 − X)/(1 − X²)`, introducing the
denominator `(1 − X²)` (`L(2s, η²)`), whereas a `GL₁` Hecke local factor `∑_t (ψ X)^t = (1 − ψ X)⁻¹`
places `1 − ψ X` in the denominator rather than the numerator. -/
theorem hasSum_liouville_local_series {X : ℂ} (hX : ‖X‖ < 1) :
    HasSum (fun t : ℕ => (-X) ^ t) ((1 - X) / (1 - X ^ 2)) ∧
      1 - X ≠ 0 ∧ 1 - X ^ 2 ≠ 0 := by
  have hneg : ‖-X‖ < 1 := by simpa using hX
  have hgeom := hasSum_geometric_of_norm_lt_one hneg
  have h1sub : 1 - X ≠ 0 := by
    intro h0
    have hX1 : X = 1 := by linear_combination -h0
    rw [hX1, norm_one] at hX
    linarith
  have h1add : 1 + X ≠ 0 := by
    intro h0
    have hXm1 : X = -1 := by linear_combination h0
    rw [hXm1, norm_neg, norm_one] at hX
    linarith
  have h1sq : 1 - X ^ 2 ≠ 0 := by
    rw [show 1 - X ^ 2 = (1 - X) * (1 + X) by ring]
    exact mul_ne_zero h1sub h1add
  have heq : (1 - (-X))⁻¹ = (1 - X) / (1 - X ^ 2) := by
    have h1 : 1 - (-X) = 1 + X := by ring
    rw [h1]
    field_simp [h1add, h1sq]
    ring
  exact ⟨heq ▸ hgeom, h1sub, h1sq⟩

/-- **Closed-form unslotted balanced corner for general conductor exponent `κ ≥ 5/2`.** For every
`κ ≥ 5/2`, twist order `n ≥ 1`, and row length `M : ℝ`,
`max (lowUnslotted κ n M) (floorUnslotted n M) ≥ (3/2 − 1/n) (2κ − 1)/(2κ + 1)`,
with equality attained at `M = 4/(2κ + 1)`. -/
theorem corner_unslotted_ge_closedForm {κ n : ℝ} (hκ : 5 / 2 ≤ κ) (hn : 1 ≤ n) (M : ℝ) :
    (3 / 2 - 1 / n) * ((2 * κ - 1) / (2 * κ + 1)) ≤
      max (Budget.lowUnslotted κ n M) (Budget.floorUnslotted n M) := by
  have h2κ : 0 < 2 * κ + 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hcoef : 0 ≤ 3 / 2 - 1 / n := by
    have hinv : 1 / n ≤ 1 := div_le_one_of_le₀ hn hn0.le
    linarith
  rcases le_total M (4 / (2 * κ + 1)) with hle | hge
  · refine le_max_of_le_right ?_
    unfold Budget.floorUnslotted
    have hM_mul : M * (2 * κ + 1) ≤ 4 := (le_div_iff₀ h2κ).mp hle
    have hsub : (2 * κ - 1) / (2 * κ + 1) ≤ 1 - M / 2 := by
      rw [div_le_iff₀ h2κ]
      linarith
    exact mul_le_mul_of_nonneg_left hsub hcoef
  · refine le_max_of_le_left ?_
    unfold Budget.lowUnslotted
    have hm : (κ - 1) * M - 1 ≤ max 0 ((κ - 1) * M - 1) := le_max_right _ _
    have hbase : 1 - (1 - (4 / (2 * κ + 1)) / 2) / n +
        ((κ - 1) * (4 / (2 * κ + 1)) - 1) / 2 =
        (3 / 2 - 1 / n) * ((2 * κ - 1) / (2 * κ + 1)) := by
      field_simp [h2κ.ne', hn0.ne']
      ring
    have hslope_coef : 0 ≤ 1 / (2 * n) + (κ - 1) / 2 := by
      have h1 : 0 ≤ 1 / (2 * n) := by positivity
      linarith
    have hslope : 0 ≤ (1 / (2 * n) + (κ - 1) / 2) * (M - 4 / (2 * κ + 1)) :=
      mul_nonneg hslope_coef (sub_nonneg.mpr hge)
    have hdiff : 1 - (1 - M / 2) / n + ((κ - 1) * M - 1) / 2 =
        (1 - (1 - (4 / (2 * κ + 1)) / 2) / n +
          ((κ - 1) * (4 / (2 * κ + 1)) - 1) / 2) +
        (1 / (2 * n) + (κ - 1) / 2) * (M - 4 / (2 * κ + 1)) := by
      field_simp [hn0.ne']
      ring
    linarith only [hm, hbase, hslope, hdiff]

theorem corner_unslotted_attained {κ n : ℝ} (hκ : 5 / 2 ≤ κ) (hn : 0 < n) :
    max (Budget.lowUnslotted κ n (4 / (2 * κ + 1))) (Budget.floorUnslotted n (4 / (2 * κ + 1))) =
      (3 / 2 - 1 / n) * ((2 * κ - 1) / (2 * κ + 1)) := by
  have h2κ : 0 < 2 * κ + 1 := by linarith
  have hnonneg : 0 ≤ (κ - 1) * (4 / (2 * κ + 1)) - 1 := by
    have hrew : (κ - 1) * (4 / (2 * κ + 1)) = (4 * κ - 4) / (2 * κ + 1) := by ring
    rw [hrew, sub_nonneg, one_le_div h2κ]
    linarith
  have h1 : Budget.lowUnslotted κ n (4 / (2 * κ + 1)) =
      (3 / 2 - 1 / n) * ((2 * κ - 1) / (2 * κ + 1)) := by
    unfold Budget.lowUnslotted
    rw [max_eq_right hnonneg]
    field_simp [h2κ.ne', hn.ne']
    ring
  have h2 : Budget.floorUnslotted n (4 / (2 * κ + 1)) =
      (3 / 2 - 1 / n) * ((2 * κ - 1) / (2 * κ + 1)) := by
    unfold Budget.floorUnslotted
    field_simp [h2κ.ne', hn.ne']
    ring
  rw [h1, h2, max_self]

/-- **Universal positive-form budget obstruction for higher-order Gauss-sum pairings (`m ≥ 4`).**
For every quadratic-product character pair `(χ, φ)` (`orderOf (χ * φ) = 2`) of coefficient order
`m = orderOf χ ≥ 4` and conductor exponent `κ ≥ m − 1` (the Kazhdan–Patterson distinguished theta
rank), every row length `M ∈ ℝ` satisfies
`max (lowUnslotted κ (orderOf φ) M) (floorUnslotted (orderOf φ) M) ≥ 25/28 > 7/8`
and effective twist exponent
`positiveFormTheta (orderOf φ) (...) ≥ 22/21 > 1`. -/
theorem higher_order_quadratic_pair_budget_obstruction {G : Type*} [CommGroup G]
    (hG : HasUniqueOrderTwo G) {χ φ : G} (hm4 : 4 ≤ orderOf χ) (hq : orderOf (χ * φ) = 2)
    {κ : ℝ} (hκ : (orderOf χ : ℝ) - 1 ≤ κ) (M : ℝ) :
    25 / 28 ≤ max (Budget.lowUnslotted κ (orderOf φ) M) (Budget.floorUnslotted (orderOf φ) M) ∧
      22 / 21 ≤ Budget.positiveFormTheta (orderOf φ)
        (max (Budget.lowUnslotted κ (orderOf φ) M) (Budget.floorUnslotted (orderOf φ) M)) := by
  obtain ⟨hn3, _, _⟩ := even_and_four_le_lcm_of_quadratic_product hG (by omega) hq
  have hn_real : (3 : ℝ) ≤ orderOf φ := by exact_mod_cast hn3
  have hn1 : (1 : ℝ) < orderOf φ := by linarith
  by_cases hm_eq4 : orderOf χ = 4
  · -- `m = 4`: trichotomy forces `orderOf φ = 4` and `κ ≥ 3`
    have hn_eq4 : orderOf φ = 4 := by
      rcases quadratic_product_order_trichotomy hG (by omega : 3 ≤ orderOf χ) hq with
        ⟨⟨u, hu⟩, _, _⟩ | ⟨m₀, ⟨u, hu⟩, _, hm₁, _, _⟩ | ⟨_, hm₂, _⟩
      · omega
      · omega
      · exact hm₂.trans hm_eq4
    have hκ3 : (3 : ℝ) ≤ κ := by rw [hm_eq4] at hκ; norm_num at hκ; exact hκ
    have h2κ : 0 < 2 * κ + 1 := by linarith
    have hcorner := corner_unslotted_ge_closedForm (κ := κ) (n := 4) (by linarith) (by norm_num) M
    have hfrac : (5 / 7 : ℝ) ≤ (2 * κ - 1) / (2 * κ + 1) := by
      rw [le_div_iff₀ h2κ]; linarith
    have hmul_lo : (25 / 28 : ℝ) ≤ (3 / 2 - 1 / (4 : ℝ)) * ((2 * κ - 1) / (2 * κ + 1)) := by
      have h54 : (3 / 2 - 1 / (4 : ℝ)) = 5 / 4 := by norm_num
      rw [h54]
      linarith only [hfrac]
    have hσ : (25 / 28 : ℝ) ≤ max (Budget.lowUnslotted κ 4 M) (Budget.floorUnslotted 4 M) :=
      hmul_lo.trans hcorner
    rw [hn_eq4]
    push_cast
    refine ⟨hσ, ?_⟩
    have hθ := (Budget.positiveFormTheta_strictMono (by norm_num : (1 : ℝ) < 4)).monotone hσ
    have hval : Budget.positiveFormTheta 4 (25 / 28) = 22 / 21 := by
      norm_num [Budget.positiveFormTheta]
    linarith only [hθ, hval]
  · -- `m ≥ 5`: `κ ≥ 4` and `orderOf φ ≥ 3` give corner `≥ 49/54 > 25/28` and `θ ≥ 11/9 > 22/21`
    have hm5 : 5 ≤ orderOf χ := by omega
    have hκ4 : (4 : ℝ) ≤ κ := by
      have hm5_real : (5 : ℝ) ≤ orderOf χ := by exact_mod_cast hm5
      linarith
    have h2κ : 0 < 2 * κ + 1 := by linarith
    have hcorner := corner_unslotted_ge_closedForm (κ := κ) (n := (orderOf φ : ℝ))
      (by linarith) (by linarith) M
    have hfrac : (7 / 9 : ℝ) ≤ (2 * κ - 1) / (2 * κ + 1) := by
      rw [le_div_iff₀ h2κ]; linarith
    have hinv : (orderOf φ : ℝ)⁻¹ ≤ 1 / 3 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hn_real
    have hcoef_lo : (7 / 6 : ℝ) ≤ 3 / 2 - 1 / (orderOf φ : ℝ) := by
      rw [one_div]
      linarith only [hinv]
    have hprod_lo : (3 / 2 - 1 / (orderOf φ : ℝ)) * (7 / 9) ≤
        (3 / 2 - 1 / (orderOf φ : ℝ)) * ((2 * κ - 1) / (2 * κ + 1)) :=
      mul_le_mul_of_nonneg_left hfrac (le_trans (by norm_num) hcoef_lo)
    have hσ_lo : (3 / 2 - 1 / (orderOf φ : ℝ)) * (7 / 9) ≤
        max (Budget.lowUnslotted κ (orderOf φ) M) (Budget.floorUnslotted (orderOf φ) M) :=
      hprod_lo.trans hcorner
    have hσ_49 : (49 / 54 : ℝ) ≤ (3 / 2 - 1 / (orderOf φ : ℝ)) * (7 / 9) := by
      have hmul := mul_le_mul_of_nonneg_right hcoef_lo (by norm_num : (0 : ℝ) ≤ 7 / 9)
      linarith only [hmul]
    refine ⟨le_trans (by norm_num) (hσ_49.trans hσ_lo), ?_⟩
    have hθ_mono := (Budget.positiveFormTheta_strictMono hn1).monotone hσ_lo
    have hθ_closed : Budget.positiveFormTheta (orderOf φ)
        ((3 / 2 - 1 / (orderOf φ : ℝ)) * (7 / 9)) =
        4 / 3 - 2 / (9 * ((orderOf φ : ℝ) - 1)) := by
      unfold Budget.positiveFormTheta
      have hn0 : (orderOf φ : ℝ) ≠ 0 := by linarith
      have hnsub : (orderOf φ : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hn0, hnsub]
      ring
    have hsub_le : 2 / (9 * ((orderOf φ : ℝ) - 1)) ≤ 1 / 9 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hθ_11 : (11 / 9 : ℝ) ≤ 4 / 3 - 2 / (9 * ((orderOf φ : ℝ) - 1)) :=
      le_sub_iff_add_le.mpr ((add_le_add_right hsub_le (11 / 9)).trans_eq (by ring))
    exact le_trans (by norm_num) (hθ_11.trans (hθ_closed ▸ hθ_mono))

/-- **Multi-row positive-form budget obstruction (`d ≥ 2`).** Any Gauss pairing with `d ≥ 2` row
twists and a row twist `φ ∈ P.rowChars` of order `n ≥ 3` has balanced positive-form design boundary
`lowBoundaryDesign d n ≥ 1` and effective twist exponent `thetaDesign d n ≥ n/(n − 1) > 1`. -/
theorem multi_row_probe_budget_obstruction {G : Type*} [CommGroup G]
    (P : MoebiusGaussPairing G) (hd : 2 ≤ P.rowChars.length)
    {φ : G} (_ : φ ∈ P.rowChars) (hn3 : 3 ≤ orderOf φ) :
    1 ≤ Budget.lowBoundaryDesign P.rowChars.length (orderOf φ) ∧
      (orderOf φ : ℝ) / ((orderOf φ : ℝ) - 1) ≤
        Budget.thetaDesign P.rowChars.length (orderOf φ) := by
  have hd_real : (2 : ℝ) ≤ P.rowChars.length := by exact_mod_cast hd
  have hn_real : (3 : ℝ) ≤ orderOf φ := by exact_mod_cast hn3
  exact ⟨Budget.one_le_lowBoundaryDesign hd_real hn_real,
    Budget.thetaDesign_ge_trivial hd_real hn_real⟩

end AnalyticAndBudgetObstructions

/-! ### 4. General `(c, k)` coupled-tower contraction and universal `3/5` tower floor -/

section CoupledTowerContraction

/-- Affine zero-transfer map `b ↦ (c + b)/k` of a `(c, k)` continuation frame. -/
noncomputable def pairingStep (c k b : ℝ) : ℝ := (c + b) / k

private theorem pairingStep_mono {c k a b : ℝ} (hk : 0 < k) (hab : a ≤ b) :
    pairingStep c k a ≤ pairingStep c k b := by
  unfold pairingStep
  exact div_le_div_of_nonneg_right (by linarith) hk.le

theorem pairingStep_fixedPoint_iff {c k : ℝ} (hk : 1 < k) (b : ℝ) :
    pairingStep c k b = b ↔ b = c / (k - 1) := by
  have hk0 : k ≠ 0 := by linarith
  have hk1 : k - 1 ≠ 0 := by linarith
  unfold pairingStep
  rw [div_eq_iff hk0]
  constructor
  · intro h; rw [eq_div_iff hk1]; linarith
  · intro h; have h' := (eq_div_iff hk1).mp h; linarith

/-- Explicit `R`-step iterate of `b ↦ (c + b)/k` around its fixed point `c/(k − 1)`. -/
theorem iterate_pairingStep_eq {c k : ℝ} (hk : 1 < k) (b₀ : ℝ) (R : ℕ) :
    (pairingStep c k)^[R] b₀ = c / (k - 1) + (b₀ - c / (k - 1)) / k ^ R := by
  have hk0 : k ≠ 0 := by linarith
  have hk1 : k - 1 ≠ 0 := by linarith
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold pairingStep
    have hkR : k ^ R ≠ 0 := pow_ne_zero R hk0
    rw [pow_succ]
    field_simp [hk0, hk1, hkR]
    ring

theorem tendsto_iterate_pairingStep {c k : ℝ} (hk : 1 < k) (b₀ : ℝ) :
    Tendsto (fun R : ℕ => (pairingStep c k)^[R] b₀) atTop (𝓝 (c / (k - 1))) := by
  have habs : |(1 / k : ℝ)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_lt_one (by linarith)).mpr hk
  have h0 : Tendsto (fun R : ℕ => (b₀ - c / (k - 1)) * (1 / k) ^ R) atTop
      (𝓝 ((b₀ - c / (k - 1)) * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs).const_mul (b₀ - c / (k - 1))
  have h1 : Tendsto (fun R : ℕ => c / (k - 1) + (b₀ - c / (k - 1)) * (1 / k) ^ R) atTop
      (𝓝 (c / (k - 1) + (b₀ - c / (k - 1)) * 0)) :=
    tendsto_const_nhds.add h0
  simp only [mul_zero, add_zero] at h1
  refine h1.congr fun R => ?_
  rw [iterate_pairingStep_eq hk b₀ R, one_div, inv_pow]
  ring

private theorem pairingStep_max_le {c k σ₀ x : ℝ} (hk : 1 < k) (hx : c / (k - 1) ≤ x) :
    pairingStep c k (max σ₀ x) ≤ max σ₀ (pairingStep c k x) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  rcases le_or_gt σ₀ x with hle | hgt
  · rw [max_eq_right hle]
    exact le_max_right _ _
  · rw [max_eq_left hgt.le]
    have hlt_fp : c / (k - 1) < σ₀ := hx.trans_lt hgt
    have hc_lt : c < σ₀ * (k - 1) := (div_lt_iff₀ hk1).mp hlt_fp
    have hstep_lt : pairingStep c k σ₀ < σ₀ := by
      unfold pairingStep
      rw [div_lt_iff₀ hk0]
      linarith
    exact hstep_lt.le.trans (le_max_left _ _)

/-- **General `(c, k)` coupled-tower contraction theorem.** Any sequence of tower abscissas
`Θ : ℕ → ℝ` bounded above by `1` and satisfying the zero-transfer step
`Θ r ≤ max σ₀ ((c + Θ (r + 1))/k)` (`k > 1`, `c ≤ k − 1`) satisfies `Θ 0 ≤ max σ₀ (c/(k − 1))`. -/
theorem abscissa_le_max_fixedPoint_of_tower {c k σ₀ : ℝ} (hk : 1 < k) (hc : c ≤ k - 1)
    {Θ : ℕ → ℝ} (hΘ_le : ∀ r : ℕ, Θ r ≤ 1)
    (hstep : ∀ r : ℕ, Θ r ≤ max σ₀ (pairingStep c k (Θ (r + 1)))) :
    Θ 0 ≤ max σ₀ (c / (k - 1)) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hfp_le_one : c / (k - 1) ≤ 1 := (div_le_one hk1).mpr hc
  have hfp_le_iter : ∀ d : ℕ, c / (k - 1) ≤ (pairingStep c k)^[d] 1 := by
    intro d
    rw [iterate_pairingStep_eq hk 1 d]
    have hnn : 0 ≤ (1 - c / (k - 1)) / k ^ d :=
      div_nonneg (sub_nonneg.mpr hfp_le_one) (pow_nonneg hk0.le d)
    linarith
  have hd_bound : ∀ d r : ℕ, Θ r ≤ max σ₀ ((pairingStep c k)^[d] 1) := by
    intro d
    induction d with
    | zero =>
      intro r
      exact (hΘ_le r).trans (le_max_right _ _)
    | succ d ih =>
      intro r
      have hmon : pairingStep c k (Θ (r + 1)) ≤
          pairingStep c k (max σ₀ ((pairingStep c k)^[d] 1)) :=
        pairingStep_mono hk0 (ih (r + 1))
      calc Θ r ≤ max σ₀ (pairingStep c k (Θ (r + 1))) := hstep r
        _ ≤ max σ₀ (pairingStep c k (max σ₀ ((pairingStep c k)^[d] 1))) :=
            max_le_max_left σ₀ hmon
        _ ≤ max σ₀ (max σ₀ (pairingStep c k ((pairingStep c k)^[d] 1))) :=
            max_le_max_left σ₀ (pairingStep_max_le hk (hfp_le_iter d))
        _ = max σ₀ ((pairingStep c k)^[d + 1] 1) := by
            rw [← max_assoc, max_self, Function.iterate_succ_apply']
  have htend : Tendsto (fun d : ℕ => max σ₀ ((pairingStep c k)^[d] 1)) atTop
      (𝓝 (max σ₀ (c / (k - 1)))) :=
    tendsto_const_nhds.max (tendsto_iterate_pairingStep hk 1)
  exact ge_of_tendsto htend (Eventually.of_forall fun d => hd_bound d 0)

/-- **Stationary optimality of `c/(k − 1)`.** Whenever `σ₀ ≤ c/(k − 1)`, the constant sequence
`Θ r = c/(k − 1)` satisfies `Θ r = max σ₀ ((c + Θ (r + 1))/k)` identically, proving no bound below
`c/(k − 1)` follows from the coupled zero-transfer recurrence alone. -/
theorem stationary_sequence_achieves_fixedPoint {c k σ₀ : ℝ} (hk : 1 < k)
    (hσ₀ : σ₀ ≤ c / (k - 1)) (r : ℕ) :
    (fun _ : ℕ => c / (k - 1)) r =
      max σ₀ (pairingStep c k ((fun _ : ℕ => c / (k - 1)) (r + 1))) := by
  dsimp only
  rw [(pairingStep_fixedPoint_iff hk _).mpr rfl, max_eq_right hσ₀]

/-- **Universal `3/5` coupled-tower floor across all Möbius-signed Gauss pairings.** Every
Möbius-signed Gauss pairing `P` has `1 < P.period`, stationary fixed point `P.coupledBarrier ≥ 3/5`
(strictly above `1/2`), and at `σ₀ = 1/2` admits the stationary critical-strip barrier
`Θ r = P.coupledBarrier ≥ 3/5`. -/
theorem moebiusGaussPairing_tower_floor_ge_three_fifths {G : Type*} [CommGroup G]
    (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    (1 : ℝ) < P.period ∧
      3 / 5 ≤ P.coupledBarrier ∧
      (∀ r : ℕ, (fun _ : ℕ => P.coupledBarrier) r =
        max (1 / 2 : ℝ)
          (pairingStep P.pairingC P.period ((fun _ : ℕ => P.coupledBarrier) (r + 1)))) := by
  have hk3 := P.three_le_period hG
  have hk1 : (1 : ℝ) < P.period := by
    have : (3 : ℝ) ≤ P.period := by exact_mod_cast hk3
    linarith
  have hbar := P.three_fifths_le_coupledBarrier hG
  have hhalf : (1 / 2 : ℝ) ≤ P.pairingC / ((P.period : ℝ) - 1) := by
    change (1 / 2 : ℝ) ≤ P.coupledBarrier
    linarith
  exact ⟨hk1, hbar, stationary_sequence_achieves_fixedPoint hk1 hhalf⟩

end CoupledTowerContraction

/-! ### 5. Master classification and barrier theorem -/

/-- **Complete solution for Möbius-signed Gauss pairings.**
1. *No pairing below `3/5`:* `¬ ∃ (F, R, P), P.coupledBarrier < 3/5`.
2. *No pairing reaching `1/2`:* `¬ ∃ (F, R, P), P.pairingC ≤ (P.period − 1)/2`.
3. *Sharp infimum `3/5`:* `sInf {P.coupledBarrier} = 3/5`, attained at `(c, k) = (3, 6)` on `ZMod 7`.
4. *Universal bounds and `(3, 6)` rigidity:* Every pairing on `MulChar F R` satisfies
   `(c + 1)/k ≥ 2/3`, `c/(k − 1) ≥ 3/5`, `(c + 1/2)/k ≥ 7/12`, with `c/(k − 1) = 3/5 ↔ (c, k) = (3, 6)`,
   and among reduced row probes iff `compChars = [χ]` (`orderOf χ = 3`), `rowChars = [φ]`
   (`orderOf φ = 6`), `period = 6`.
5. *Higher-order positive-form budget obstruction:* Every quadratic-product character pair on
   `MulChar F R` of coefficient order `m ≥ 4` and conductor exponent `κ ≥ m − 1` satisfies
   `max (lowUnslotted κ (orderOf φ) M) (floorUnslotted (orderOf φ) M) ≥ 25/28` and
   `positiveFormTheta (orderOf φ) (...) ≥ 22/21 > 1` for all `M : ℝ`. -/
theorem moebius_signed_gauss_pairings_complete_solution :
    (¬ ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (R : Type) (_ : CommRing R) (_ : IsDomain R)
        (P : MoebiusGaussPairing (MulChar F R)),
        P.coupledBarrier < 3 / 5) ∧
    (¬ ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (R : Type) (_ : CommRing R) (_ : IsDomain R)
        (P : MoebiusGaussPairing (MulChar F R)),
        P.pairingC ≤ ((P.period : ℝ) - 1) / 2) ∧
    (sInf {r : ℝ | ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (P : MoebiusGaussPairing (MulChar F ℂ)), r = P.coupledBarrier} = 3 / 5) ∧
    (∀ (F : Type*) [Field F] [Fintype F] (R : Type*) [CommRing R] [IsDomain R]
        (P : MoebiusGaussPairing (MulChar F R)),
      2 / 3 ≤ P.uncoupledBoundary ∧
      3 / 5 ≤ P.coupledBarrier ∧
      7 / 12 ≤ P.grhStepBoundary ∧
      (P.coupledBarrier = 3 / 5 ↔ P.pairingC = 3 ∧ P.period = 6)) ∧
    (∀ (F : Type*) [Field F] [Fintype F] (R : Type*) [CommRing R] [IsDomain R]
        {χ φ : MulChar F R},
      4 ≤ orderOf χ → orderOf (χ * φ) = 2 →
      ∀ {κ : ℝ}, (orderOf χ : ℝ) - 1 ≤ κ → ∀ M : ℝ,
        25 / 28 ≤ max (Budget.lowUnslotted κ (orderOf φ) M) (Budget.floorUnslotted (orderOf φ) M) ∧
        22 / 21 ≤ Budget.positiveFormTheta (orderOf φ)
          (max (Budget.lowUnslotted κ (orderOf φ) M) (Budget.floorUnslotted (orderOf φ) M))) :=
  ⟨not_exists_moebiusGaussPairing_lt_three_fifths,
    not_exists_moebiusGaussPairing_reaching_critical_line,
    sInf_coupledBarrier_eq_three_fifths,
    fun F _ _ R _ _ P =>
      let hG := mulChar_hasUniqueOrderTwo F R
      ⟨P.two_thirds_le_uncoupledBoundary hG,
        P.three_fifths_le_coupledBarrier hG,
        P.seven_twelfths_le_grhStepBoundary hG,
        P.coupledBarrier_eq_three_fifths_iff hG⟩,
    fun F _ _ R _ _ {_ _} hm4 hq {_} hκ M =>
      higher_order_quadratic_pair_budget_obstruction (mulChar_hasUniqueOrderTwo F R) hm4 hq hκ M⟩

end GaloisForLFunctions.FamilyContinuationTheory
