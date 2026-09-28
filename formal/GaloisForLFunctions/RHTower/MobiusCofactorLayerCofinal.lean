import GaloisForLFunctions.RHTower.MobiusCofactorLayerExtraction

/-!
# Summability of the layered extraction and the choice of the order

* The atom jets obey `‖∂_x^r f_x‖_δ ≤ K_r R^{-r-1/2-δ/2}` for `x ≥ R`.
* For a single cofactor `q ≤ R^{2/5}` the order-three packet obeys
  `‖P_{R,q}‖_δ ≤ C [R^{-(1+δ)/2} + R^{α-3/2-δ/2} q^{1-α} + R^{3α-5/2-δ/2} q^{2-3α}/log R]`.   (5)
* Under `(d+1)(1-α)(1-η) > 1/2` the layered packets at `R = 2^j` have norms with a summable majorant
  uniform in `0 ≤ δ ≤ 1`, so removing them from `S_{2^{J+2}}` is a bounded perturbation.
* Odd squarefree `q ≤ R^β`, `β < 1/2`, are admissible cofactors.
* For every `η < 1` some order `d` satisfies the condition; for `d = 3` it is exactly `η < 33/58`.
-/

open Finset Filter Topology

noncomputable section

namespace RHTower.CubicGamma

open RHTower.MomentSelector
open scoped ArithmeticFunction.Moebius

/-- `‖∂_x^r f_x‖_δ ≤ K_r R^{-r-1/2-δ/2}` for `x ≥ R > 0`, `0 ≤ δ ≤ 1`. -/
theorem gammaNorm_atomJet_le_of_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (r : ℕ) {R x : ℝ}
    (hR : 0 < R) (hRx : R ≤ x) :
    gammaNorm δ (atomJet r x) ≤ jetConst r * R ^ (-(r : ℝ) - 1 / 2 - δ / 2) := by
  have hx : 0 < x := hR.trans_le hRx
  refine (gammaNorm_atomJet_le hδ0 hδ1 r hx).trans ?_
  have e : ∀ y : ℝ, 0 < y → y ^ 2 * (y ^ ((5 + δ) / 2))⁻¹ / y ^ r = y ^ (-(r : ℝ) - 1 / 2 - δ / 2) := by
    intro y hy
    rw [← Real.rpow_natCast y r, ← Real.rpow_neg hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le,
      ← Real.rpow_two, ← Real.rpow_add hy, ← Real.rpow_add hy]
    congr 1; ring
  have hjc := jetConst_nonneg r
  calc jetConst r * x ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ / x ^ r
      = jetConst r * (x ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ / x ^ r) := by ring
    _ = jetConst r * x ^ (-(r : ℝ) - 1 / 2 - δ / 2) := by rw [e x hx]
    _ ≤ jetConst r * R ^ (-(r : ℝ) - 1 / 2 - δ / 2) := by
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hR hRx (show -(r : ℝ) - 1 / 2 - δ / 2 ≤ 0 by linarith)) hjc

/-- **The per-cofactor bound (5).**  For all large `R` and odd squarefree `q ≤ R^{2/5}` the
order-three single-cofactor packet satisfies
`‖P_{R,q}‖_δ ≤ C [R^{-(1+δ)/2} + R^{α-3/2-δ/2} q^{1-α} + R^{3α-5/2-δ/2} q^{2-3α}/log R]`. -/
theorem exists_threeWindow_cofactor_bound :
    ∃ C R₀ : ℝ, 0 < C ∧ 5 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ q : ℕ, 1 ≤ q → Odd q → Squarefree q →
      (q : ℝ) ≤ R ^ ((2 : ℝ) / 5) →
      ∃ UP UN : Finset ℕ, Disjoint UP UN ∧ (∀ n ∈ UP, μ n = 1) ∧ (∀ n ∈ UN, μ n = -1) ∧
        (∀ n ∈ UP ∪ UN, 2 * R < n ∧ (n : ℝ) < 4 * R ∧ AtomShape R q n) ∧
        UP.card = UN.card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ UP ∪ UN, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (R ^ (-(1 + δ) / 2) +
              R ^ (supplyExp - 3 / 2 - δ / 2) * (q : ℝ) ^ (1 - supplyExp) +
              R ^ (3 * supplyExp - 5 / 2 - δ / 2) * (q : ℝ) ^ (2 - 3 * supplyExp) / Real.log R) := by
  obtain ⟨ε, hε0, z₀, hz₀, hfam⟩ := exists_family_packet (d := 2) (by norm_num)
  obtain ⟨R₀, hR₀, hthr⟩ := exists_threeWindow_threshold z₀ ε
  have hj1 := jetConst_nonneg 1
  have hj2 := jetConst_nonneg 2
  have hj3 := jetConst_nonneg 3
  refine ⟨4 * jetConst 1 + 8 * jetConst 2 / ε + jetConst 3 / (768 * ε ^ 2) + 1, R₀,
    by positivity, hR₀, fun R hR q hq1 hqodd hqsq hqY => ?_⟩
  obtain ⟨hz, hLR, -, -⟩ := hthr R hR
  have hR5 : 5 ≤ R := hR₀.trans hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  obtain ⟨hL0, hLq⟩ := threeWindow_length hR1 hε0 hq1 hqY hLR
  obtain ⟨hRq, -, -⟩ := threeWindow_scale hR1 hq1 hqY
  set L : ℝ := (q : ℝ) * (4 * R / q) ^ supplyExp / ε with hLdef
  have hR35 : R ^ ((2 : ℝ) / 5) < R ^ ((3 : ℝ) / 5) := by
    rcases eq_or_lt_of_le hR1 with h | h
    · rw [← h] at hR5; norm_num at hR5
    · exact Real.rpow_lt_rpow_of_exponent_lt h (by norm_num)
  have hadm : AdmissibleCofactor R q := by
    refine ⟨hq1, hqodd, hqsq, fun ℓ hℓ hℓq => ?_⟩
    have : (ℓ : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hℓq
    linarith
  have hFq : ∀ q' ∈ ({q} : Finset ℕ), AdmissibleCofactor R q' ∧ 2 ≤ R / q' ∧ z₀ ≤ R / q' ∧
      (q' : ℝ) * (4 * R / q') ^ supplyExp ≤ ε * L := by
    intro q' hq'
    rw [mem_singleton] at hq'
    subst hq'
    refine ⟨hadm, (le_max_right _ _).trans (hz.trans hRq), (le_max_left _ _).trans
      (hz.trans hRq), ?_⟩
    rw [hLdef, mul_div_cancel₀ _ hε0.ne']
  obtain ⟨UP, UN, hd, hμP, hμN, hpos, hcP, hcN, hnorm⟩ := hfam R L {q} hR5 hL0 hLq hFq
  refine ⟨UP, UN, hd, hμP, hμN, fun n hn => ?_, by rw [hcP, hcN], fun δ hδ0 hδ1 => ?_⟩
  · obtain ⟨h1, h2, q', hq', hsh⟩ := hpos n hn
    rw [mem_singleton] at hq'
    subst hq'
    exact ⟨h1, h2, hsh⟩
  have hJL : ((⌊2 * R / L⌋₊ : ℕ) : ℝ) * L ≤ 2 * R := by
    have h := Nat.floor_le (show 0 ≤ 2 * R / L by positivity)
    calc ((⌊2 * R / L⌋₊ : ℕ) : ℝ) * L ≤ 2 * R / L * L := by gcongr
      _ = 2 * R := by field_simp
  refine (hnorm δ hδ0 hδ1).trans ?_
  rw [sum_singleton]
  refine (threeWindow_block_arith hR1 hL0.le hJL).trans ?_
  set E := (R ^ ((5 + δ) / 2))⁻¹ with hE
  have hE0 : 0 < E := inv_pos.mpr (Real.rpow_pos_of_pos hR0 _)
  -- the three terms
  have t1 : R * R * E = R ^ (-(1 + δ) / 2) := by
    rw [hE, ← Real.rpow_neg hR0.le, show R * R = R ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
      ← Real.rpow_add hR0]
    congr 1; ring
  have hLeq : L = 4 ^ supplyExp / ε * ((q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp) := by
    rw [hLdef, cofactor_H_eq hq1 hR0.le, Real.div_rpow hR0.le hq0.le, Real.rpow_sub hq0,
      Real.rpow_one]
    field_simp
  have h4 := four_rpow_supplyExp_le
  have h40 : 0 ≤ (4 : ℝ) ^ supplyExp := Real.rpow_nonneg (by norm_num) _
  have hqα := Real.rpow_nonneg hq0.le (1 - supplyExp)
  have hRα := Real.rpow_nonneg hR0.le supplyExp
  have t2 : R * L * E ≤ 4 / ε * (R ^ (supplyExp - 3 / 2 - δ / 2) * (q : ℝ) ^ (1 - supplyExp)) := by
    have e : R * R ^ supplyExp * E = R ^ (supplyExp - 3 / 2 - δ / 2) := by
      rw [hE, ← Real.rpow_neg hR0.le, show R * R ^ supplyExp = R ^ (1 : ℝ) * R ^ supplyExp by
        rw [Real.rpow_one], ← Real.rpow_add hR0, ← Real.rpow_add hR0]
      congr 1; ring
    calc R * L * E = 4 ^ supplyExp / ε * ((q : ℝ) ^ (1 - supplyExp) * (R * R ^ supplyExp * E)) := by
          rw [hLeq]; ring
      _ ≤ 4 / ε * ((q : ℝ) ^ (1 - supplyExp) * (R * R ^ supplyExp * E)) := by gcongr
      _ = _ := by rw [e]; ring
  have t3 : (cofactorSupply R q : ℝ) * L ^ 2 * E ≤
      1 / (2048 * ε ^ 2) * (R ^ (3 * supplyExp - 5 / 2 - δ / 2) * (q : ℝ) ^ (2 - 3 * supplyExp) /
        Real.log R) := by
    have hm : (cofactorSupply R q : ℝ) ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) :=
      Nat.floor_le (by
        have := Real.rpow_nonneg (div_nonneg hR0.le hq0.le) supplyExp
        have : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
        positivity)
    have hmL := supply_mul_length_sq_le hR5 hε0 hq1 hm
    have e : R ^ (3 * supplyExp) * E = R ^ (3 * supplyExp - 5 / 2 - δ / 2) := by
      rw [hE, ← Real.rpow_neg hR0.le, ← Real.rpow_add hR0]
      congr 1; ring
    have eq : (q : ℝ) ^ (-(3 * supplyExp - 2)) = (q : ℝ) ^ (2 - 3 * supplyExp) := by
      congr 1; ring
    calc (cofactorSupply R q : ℝ) * L ^ 2 * E
        ≤ R ^ (3 * supplyExp) * (q : ℝ) ^ (-(3 * supplyExp - 2)) /
            (2048 * ε ^ 2 * Real.log R) * E := by
          gcongr
      _ = _ := by rw [eq, ← e]; field_simp
  have hA := Real.rpow_nonneg hR0.le (-(1 + δ) / 2)
  have hB : 0 ≤ R ^ (supplyExp - 3 / 2 - δ / 2) * (q : ℝ) ^ (1 - supplyExp) := by positivity
  have hD : 0 ≤ R ^ (3 * supplyExp - 5 / 2 - δ / 2) * (q : ℝ) ^ (2 - 3 * supplyExp) /
      Real.log R := by positivity
  set A := R ^ (-(1 + δ) / 2)
  set B := R ^ (supplyExp - 3 / 2 - δ / 2) * (q : ℝ) ^ (1 - supplyExp)
  set D := R ^ (3 * supplyExp - 5 / 2 - δ / 2) * (q : ℝ) ^ (2 - 3 * supplyExp) / Real.log R
  have k1 : 4 * jetConst 1 * (R * R * E) ≤ 4 * jetConst 1 * A := by rw [t1]
  have k2 : 2 * jetConst 2 * (R * L * E) ≤ 8 * jetConst 2 / ε * B := by
    calc 2 * jetConst 2 * (R * L * E) ≤ 2 * jetConst 2 * (4 / ε * B) := by gcongr
      _ = 8 * jetConst 2 / ε * B := by ring
  have k3 : 8 / 3 * jetConst 3 * ((cofactorSupply R q : ℝ) * L ^ 2 * E) ≤
      jetConst 3 / (768 * ε ^ 2) * D := by
    calc 8 / 3 * jetConst 3 * ((cofactorSupply R q : ℝ) * L ^ 2 * E)
        ≤ 8 / 3 * jetConst 3 * (1 / (2048 * ε ^ 2) * D) := by gcongr
      _ = jetConst 3 / (768 * ε ^ 2) * D := by field_simp; ring
  have c1 : 4 * jetConst 1 * A ≤ (4 * jetConst 1 + 8 * jetConst 2 / ε +
      jetConst 3 / (768 * ε ^ 2) + 1) * A := by
    gcongr; have : 0 ≤ 8 * jetConst 2 / ε + jetConst 3 / (768 * ε ^ 2) := by positivity
    linarith
  have c2 : 8 * jetConst 2 / ε * B ≤ (4 * jetConst 1 + 8 * jetConst 2 / ε +
      jetConst 3 / (768 * ε ^ 2) + 1) * B := by
    gcongr; have : 0 ≤ jetConst 3 / (768 * ε ^ 2) := by positivity
    linarith
  have c3 : jetConst 3 / (768 * ε ^ 2) * D ≤ (4 * jetConst 1 + 8 * jetConst 2 / ε +
      jetConst 3 / (768 * ε ^ 2) + 1) * D := by
    gcongr; have : 0 ≤ 8 * jetConst 2 / ε := by positivity
    linarith
  linarith

/-- Odd squarefree `q ≤ R^β` with `β < 1/2` are admissible: each prime factor is at most
`q ≤ R^β < R^{1-β} ≤ R/q`. -/
theorem admissibleCofactor_of_le_rpow {R β : ℝ} (hR : 1 < R) (hβ : β < 1 / 2) {q : ℕ}
    (hq : 1 ≤ q) (hodd : Odd q) (hsq : Squarefree q) (hqR : (q : ℝ) ≤ R ^ β) :
    AdmissibleCofactor R q := by
  refine ⟨hq, hodd, hsq, fun ℓ _ hℓq => ?_⟩
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hℓ : (ℓ : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hℓq
  have h1 : R ^ β < R ^ (1 - β) := Real.rpow_lt_rpow_of_exponent_lt hR (by linarith)
  have h2 : R ^ (1 - β) ≤ R / q := by
    rw [Real.rpow_sub hR0, Real.rpow_one]
    exact div_le_div_of_nonneg_left hR0.le hq0 hqR
  linarith

/-- For `d = 3` the layer condition `(d+1)(1-α)(1-η) > 1/2` is exactly `η < 33/58`. -/
theorem layer_condition_three_iff (η : ℝ) :
    1 / 2 < ((3 : ℕ) + 1 : ℝ) * (1 - supplyExp) * (1 - η) ↔ η < 33 / 58 := by
  unfold supplyExp
  constructor <;> intro h <;> push_cast at * <;> linarith

/-- For every `η < 1` some order `d ≥ 1` satisfies `(d+1)(1-α)(1-η) > 1/2`. -/
theorem exists_layer_order {η : ℝ} (hη1 : η < 1) :
    ∃ d : ℕ, 1 ≤ d ∧ 1 / 2 < ((d : ℝ) + 1) * (1 - supplyExp) * (1 - η) := by
  have hα : 0 < 1 - supplyExp := by unfold supplyExp; norm_num
  have hp : 0 < (1 - supplyExp) * (1 - η) := mul_pos hα (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * ((1 - supplyExp) * (1 - η))))
  refine ⟨max n 1, le_max_right _ _, ?_⟩
  have h1 : (n : ℝ) + 1 ≤ ((max n 1 : ℕ) : ℝ) + 1 := by
    have : (n : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left n 1
    linarith
  have h2 : 1 / 2 < (n : ℝ) * ((1 - supplyExp) * (1 - η)) := by
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  have h3 : (n : ℝ) * ((1 - supplyExp) * (1 - η)) ≤
      (((max n 1 : ℕ) : ℝ) + 1) * ((1 - supplyExp) * (1 - η)) := by
    gcongr; linarith
  linarith

/-- **Dyadic layered packets and the cofinal reduction.**  Let `d ≥ 1`, `0 < η < 1` with
`(d+1)(1-α)(1-η) > 1/2`.  The layered packets of (7) at `R = 2^j` occupy disjoint dyadic shells,
use admissible cofactors `q ≤ 2^{jη}` in unique-largest-prime shapes, have literal Möbius signs
balanced with at least `c 2^j` atoms of each sign, and have norms with a summable majorant uniform
in `0 ≤ δ ≤ 1`; removing them from `S_{2^{J+2}}` is a bounded perturbation. -/
theorem layer_cofinal_reduction {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hθ : 1 / 2 < ((d : ℝ) + 1) * (1 - supplyExp) * (1 - η)) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : ℕ → Finset ℕ,
      (∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2)) ∧
      (∀ j, ∀ n ∈ U j, ∃ q : ℕ, (q : ℝ) ≤ ((2 : ℝ) ^ j) ^ η ∧ AdmissibleCofactor (2 ^ j) q ∧
        AtomShape (2 ^ j) q n) ∧
      (∀ j, ∀ n ∈ U j, μ n = 1 ∨ μ n = -1) ∧
      (∀ j, ((U j).filter fun n => μ n = 1).card = ((U j).filter fun n => μ n = -1).card) ∧
      (∀ᶠ j in atTop, c * 2 ^ j ≤ ((U j).filter fun n => μ n = 1).card) ∧
      (∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        ((∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (mobiusCubicSource (2 ^ (J + 2))) ≤ B) ↔
          ∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
            ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ B) := by
  classical
  obtain ⟨c, C, R₀, hc, hC, hR₀, hpk⟩ := exists_layer_extraction hd hη0 hη1
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, R₀ ≤ (2 : ℝ) ^ j₀ :=
    pow_unbounded_of_one_lt R₀ (by norm_num) |>.imp fun _ h => h.le
  set θ : ℝ := ((d : ℝ) + 1) * (1 - supplyExp) * (1 - η) with hθdef
  have hex : ∀ j : ℕ, ∃ U : Finset ℕ,
      (j₀ ≤ j → (∀ n ∈ U, 2 * (2 : ℝ) ^ j < n ∧ (n : ℝ) < 4 * 2 ^ j ∧
          ∃ q : ℕ, (q : ℝ) ≤ ((2 : ℝ) ^ j) ^ η ∧ AdmissibleCofactor (2 ^ j) q ∧
            AtomShape (2 ^ j) q n) ∧
        (∀ n ∈ U, μ n = 1 ∨ μ n = -1) ∧
        (U.filter fun n => μ n = 1).card = (U.filter fun n => μ n = -1).card ∧
        c * 2 ^ j ≤ (U.filter fun n => μ n = 1).card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (((2 : ℝ) ^ j) ^ (-(1 / 2 : ℝ) - δ / 2) * Real.log (2 ^ j) +
              ((2 : ℝ) ^ j) ^ (1 / 2 - θ - δ / 2))) ∧
      (j < j₀ → U = ∅) := by
    intro j
    by_cases hj : j₀ ≤ j
    · have hR : R₀ ≤ (2 : ℝ) ^ j := hj₀.trans (pow_le_pow_right₀ (by norm_num) hj)
      obtain ⟨A, B, hAB, hA, hB, hsh, hcard, hcount, hnorm⟩ := hpk _ hR
      have hfA : (A ∪ B).filter (fun n => μ n = 1) = A := by
        rw [filter_union, filter_true_of_mem hA,
          filter_false_of_mem (fun n hn h => by rw [hB n hn] at h; norm_num at h), union_empty]
      have hfB : (A ∪ B).filter (fun n => μ n = -1) = B := by
        rw [filter_union, filter_false_of_mem (fun n hn h => by rw [hA n hn] at h; norm_num at h),
          filter_true_of_mem hB, empty_union]
      refine ⟨A ∪ B, fun _ => ⟨hsh, fun n hn => ?_, by rw [hfA, hfB, hcard],
        by rw [hfA]; exact hcount, hnorm⟩, fun h => absurd hj (by omega)⟩
      rcases mem_union.mp hn with hn | hn
      · exact Or.inl (hA n hn)
      · exact Or.inr (hB n hn)
    · exact ⟨∅, fun h => absurd h hj, fun _ => rfl⟩
  choose U hU hU0 using hex
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set r₁ : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hr₁
  set r₂ : ℝ := (2 : ℝ) ^ (-(θ - 1 / 2)) with hr₂
  have hr₁0 : 0 ≤ r₁ := Real.rpow_nonneg (by norm_num) _
  have hr₂0 : 0 ≤ r₂ := Real.rpow_nonneg (by norm_num) _
  have hr₁1 : r₁ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr₂1 : r₂ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set b : ℕ → ℝ := fun j => C * (Real.log 2 * ((j : ℝ) ^ 1 * r₁ ^ j) + r₂ ^ j) with hbdef
  have hb : Summable b := by
    have h1 : Summable (fun j : ℕ => (j : ℝ) ^ 1 * r₁ ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg hr₁0]; exact hr₁1)
    exact ((h1.mul_left (Real.log 2)).add (summable_geometric_of_lt_one hr₂0 hr₂1)).mul_left C
  have hsupp : ∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2) := by
    intro j n hn
    by_cases hj : j₀ ≤ j
    · obtain ⟨h1, h2, -⟩ := (hU j hj).1 n hn
      have e1 : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
      have e2 : ((2 ^ (j + 2) : ℕ) : ℝ) = 4 * (2 : ℝ) ^ j := by push_cast; ring
      constructor
      · have : ((2 ^ (j + 1) : ℕ) : ℝ) < (n : ℝ) := by rw [e1]; exact h1
        exact_mod_cast this
      · have : (n : ℝ) < ((2 ^ (j + 2) : ℕ) : ℝ) := by rw [e2]; exact h2
        exact_mod_cast this
    · simp [hU0 j (by omega)] at hn
  have hnorm : ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j := by
    intro j δ hδ0 hδ1
    by_cases hj : j₀ ≤ j
    · refine ((hU j hj).2.2.2.2 δ hδ0 hδ1).trans ?_
      have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hlogj : Real.log (2 ^ j) = (j : ℝ) ^ 1 * Real.log 2 := by
        rw [Real.log_pow, pow_one]
      have hp1 : ((2 : ℝ) ^ j) ^ (-(1 / 2 : ℝ) - δ / 2) ≤ r₁ ^ j := by
        rw [hr₁, ← two_pow_rpow_neg]
        exact Real.rpow_le_rpow_of_exponent_le h2j (by linarith)
      have hp2 : ((2 : ℝ) ^ j) ^ (1 / 2 - θ - δ / 2) ≤ r₂ ^ j := by
        rw [hr₂, ← two_pow_rpow_neg]
        exact Real.rpow_le_rpow_of_exponent_le h2j (by linarith)
      have hl0 : 0 ≤ Real.log (2 ^ j) := Real.log_nonneg h2j
      have hp3 : ((2 : ℝ) ^ j) ^ (-(1 / 2 : ℝ) - δ / 2) * Real.log (2 ^ j) ≤
          Real.log 2 * ((j : ℝ) ^ 1 * r₁ ^ j) :=
        calc ((2 : ℝ) ^ j) ^ (-(1 / 2 : ℝ) - δ / 2) * Real.log (2 ^ j)
            ≤ r₁ ^ j * Real.log (2 ^ j) := by gcongr
          _ = Real.log 2 * ((j : ℝ) ^ 1 * r₁ ^ j) := by rw [hlogj]; ring
      simp only [hbdef]
      gcongr
    · simp only [hU0 j (by omega), Finset.sum_empty]
      have : gammaNorm δ (fun _ : ℝ => (0 : ℝ)) = 0 := by
        simp [gammaNorm, gammaEnergy, gammaInner]
      rw [this]
      simp only [hbdef]
      positivity
  refine ⟨c, hc, U, hsupp, fun j n hn => ?_, fun j n hn => ?_, fun j => ?_, ?_,
    ⟨b, hb, hnorm⟩, fun δ hδ0 hδ1 => ?_⟩
  · by_cases hj : j₀ ≤ j
    · exact ((hU j hj).1 n hn).2.2
    · simp [hU0 j (by omega)] at hn
  · by_cases hj : j₀ ≤ j
    · exact (hU j hj).2.1 n hn
    · simp [hU0 j (by omega)] at hn
  · by_cases hj : j₀ ≤ j
    · exact (hU j hj).2.2.1
    · simp [hU0 j (by omega)]
  · filter_upwards [eventually_ge_atTop j₀] with j hj
    exact (hU j hj).2.2.2.1
  · exact (cofinal_packet_reduction U b hb hsupp hδ0 fun j => hnorm j δ hδ0 hδ1).2

/-- **Layered extraction for every `η < 1`.**  For every `0 < η < 1` there is a dyadic family of
literal Möbius packets with admissible cofactors `q ≤ 2^{jη}`, balanced signs of linear density,
and a summable norm majorant uniform in `0 ≤ δ ≤ 1`, whose removal from `S_{2^{J+2}}` is a bounded
perturbation.  The order `d` is chosen with `(d+1)(1-α)(1-η) > 1/2`. -/
theorem layer_cofinal_reduction_of_lt_one {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : ℕ → Finset ℕ,
      (∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2)) ∧
      (∀ j, ∀ n ∈ U j, ∃ q : ℕ, (q : ℝ) ≤ ((2 : ℝ) ^ j) ^ η ∧ AdmissibleCofactor (2 ^ j) q ∧
        AtomShape (2 ^ j) q n) ∧
      (∀ j, ∀ n ∈ U j, μ n = 1 ∨ μ n = -1) ∧
      (∀ j, ((U j).filter fun n => μ n = 1).card = ((U j).filter fun n => μ n = -1).card) ∧
      (∀ᶠ j in atTop, c * 2 ^ j ≤ ((U j).filter fun n => μ n = 1).card) ∧
      (∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        ((∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (mobiusCubicSource (2 ^ (J + 2))) ≤ B) ↔
          ∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
            ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ B) := by
  obtain ⟨d, hd, hθ⟩ := exists_layer_order hη1
  exact layer_cofinal_reduction hd hη0 hη1 hθ

end RHTower.CubicGamma
