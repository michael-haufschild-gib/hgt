/-
# LegLatticeStep — one step of the equilibrium march increases the energy

Setting as in `LegEquilibrium`: charges on two arithmetic progressions with step `h = δ/2`,
`m` (or `m+1`) ahead points `a_k = (ϑ + k)h` and `N` (or `N+1`) behind points
`b_k = (1 − ϑ + k)h`. The energy of a configuration is
`W = ¼·[Σ csch²(b_k) + Σ csch²(a_k)]`, and an equilibrium is a root of the constraint
`g(ϑ) = Σ coth(b_k) − Σ coth(a_k) = −(total charge)`.

One step of the march converts the nearest ahead charge into the farthest behind charge:
the split `(N, m+1)` at equilibrium offset `θ` becomes `(N+1, m)` at equilibrium offset `θ'`.
Main result: **the energy strictly increases along the step**,
`W_{N,m+1}(θ) < W_{N+1,m}(θ')`, whenever `θ ≤ 1/8`, `δ ≤ 1`, and `δm² ≥ 4`.

Mechanism — a competition between an exact loss and a drift-driven gain:
* The re-split at fixed `θ` loses `¼[csch²(a_m) − csch²(b_N)] ≤ 1/(4δ)` (`δm² ≥ 4` tames the
  removed near-ahead term).
* The constraint forces the new equilibrium inward: `g_{N+1,m}(θ) − g_{N+1,m}(θ') =
  coth(b_N) + coth(a_m) ∈ (2, 2 + 4/(mδ)]`, and the derivative bracket
  `7/(4θ²δ) ≤ g' ≤ 39/(16δθ'²)` (csch² between `e^{−2s}/s²` and `1/s²`, plus telescoping
  inverse-square sums) pins the drift: `(32/39)δθ'² ≤ θ − θ' ≤ (3/7)θ`.
* Along the drift the energy climbs at rate `−W' = (δ/4)[Σφ(a) − Σφ(b)] ≥
  (δ/4)(2/ϑ³ − 34)/δ³` (`dW_margin_small_delta`, the quantitative ahead-sum dominance), so
  the gain is at least `1/δ`, four times the loss.

`rcsch_sq_ge_exp` is the lower csch² bound; `lattice_energy_hasDerivAt` is the energy
derivative; `lattice_step_energy_increase` is the theorem.
-/
import GaloisForLFunctions.RHTower.LegEquilibrium

noncomputable section

namespace RHTower

open Finset

/-- Lower csch² bound at every scale: `e^{−2s}/s² ≤ csch²(s)` for `s > 0`, from
`sinh s ≤ s·cosh s ≤ s·e^s`. -/
theorem rcsch_sq_ge_exp {s : ℝ} (hs : 0 < s) :
    Real.exp (-(2 * s)) / s ^ 2 ≤ (rcsch s) ^ 2 := by
  have hsinh : 0 < Real.sinh s := sinh_pos_of_pos hs
  have h1 : Real.sinh s ≤ s * Real.exp s := by
    have h2 := sinh_le_mul_cosh hs.le
    have h3 := cosh_le_exp hs.le
    nlinarith [hs, Real.cosh_pos s]
  have h2 : (Real.sinh s) ^ 2 ≤ (s * Real.exp s) ^ 2 := pow_le_pow_left₀ hsinh.le h1 2
  have h3 : (rcsch s) ^ 2 = 1 / (Real.sinh s) ^ 2 := by
    rw [rcsch, div_pow, one_pow]
  have h4 : 1 / (s * Real.exp s) ^ 2 ≤ 1 / (Real.sinh s) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) h2
  have h5 : Real.exp (-(2 * s)) / s ^ 2 = 1 / (s * Real.exp s) ^ 2 := by
    rw [Real.exp_neg, show (2 : ℝ) * s = s + s from by ring, Real.exp_add, mul_pow]
    have := Real.exp_ne_zero s
    field_simp
  rw [h3, h5]
  exact h4

set_option maxHeartbeats 1000000 in
/-- **Quantitative ahead-sum dominance**: on `θ ∈ (0, 1/8]`, `δ ∈ (0, 1]`, `M ≥ 1`, `N ≥ M`,
the ahead φ-sum beats the behind φ-sum by an explicit cubic margin,
`Σ_{k<M} φ(a_k) − Σ_{k<N} φ(b_k) ≥ (2/θ³ − 34)/δ³`. The `k = 0` pair alone contributes
`≥ 2/(θ³δ³) − 24/δ³` (cubic bracket of `φ`), the remaining pairs are nonnegative, and the
unpaired behind tail is at most `10/δ³` (telescoped inverse-square/cube sums). -/
theorem dW_margin_small_delta {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M)
    (hθ0 : 0 < θ) (hθ8 : θ ≤ 1 / 8) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 / θ ^ 3 - 34) / δ ^ 3
      ≤ (∑ k ∈ range M, rphi ((θ + k) * (δ / 2)))
        - ∑ k ∈ range N, rphi ((1 - θ + k) * (δ / 2)) := by
  have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hδ3 : (0 : ℝ) < δ ^ 3 := by positivity
  set fa : ℕ → ℝ := fun k => rphi ((θ + k) * (δ / 2)) with hfa
  set fb : ℕ → ℝ := fun k => rphi ((1 - θ + k) * (δ / 2)) with hfb
  have hxpos : 0 < θ * δ / 2 := by positivity
  have hx1 : θ * δ / 2 ≤ 1 := by nlinarith
  have hypos : 0 < (1 - θ) * δ / 2 := by nlinarith
  have hy1 : (1 - θ) * δ / 2 ≤ 1 := by nlinarith
  -- k = 0 head pair, exact cubic bracket
  have hhead0 : 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3
      ≤ fa 0 - fb 0 := by
    simp only [hfa, hfb, Nat.cast_zero, add_zero]
    rw [show θ * (δ / 2) = θ * δ / 2 from by ring,
      show (1 - θ) * (δ / 2) = (1 - θ) * δ / 2 from by ring]
    exact headGain_lower hxpos hx1 hypos hy1
  have hnonneg : ∀ k ∈ range M, 0 ≤ fa k - fb k := by
    intro k _
    simp only [hfa, hfb]
    have h1 : (0 : ℝ) < (θ + k) * (δ / 2) := by positivity
    have h2 : (θ + k) * (δ / 2) ≤ (1 - θ + k) * (δ / 2) := by
      have hδ2 : (0 : ℝ) < δ / 2 := by positivity
      nlinarith [hθ8, hδ2]
    have hanti := rphi_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr h1)
      (Set.mem_Ioi.mpr (lt_of_lt_of_le h1 h2)) h2
    linarith
  have hheadsum : fa 0 - fb 0 ≤ ∑ k ∈ range M, (fa k - fb k) :=
    Finset.single_le_sum hnonneg (Finset.mem_range.mpr (by omega))
  -- unpaired tail
  have htail : (∑ k ∈ Ico M N, fb k)
      ≤ (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)))
        + (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) := by
    simp only [hfb]
    exact phi_tail_small_delta hMN hδ0 (by linarith) (by linarith)
  have hd23 : (1 : ℝ) / δ ^ 2 ≤ 1 / δ ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) hδ3]
    nlinarith [hδ1, hδ0, pow_pos hδ0 2]
  have hTup : (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)))
      + (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) ≤ 10 / δ ^ 3 := by
    have hMθ : (7 / 8 : ℝ) ≤ (M : ℝ) - θ := by linarith
    have h1θM : (15 / 8 : ℝ) ≤ 1 - θ + (M : ℝ) := by linarith
    have ha1 : 1 / (1 - θ + (M : ℝ)) ≤ 8 / 15 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have ha2 : 1 / ((M : ℝ) - θ) ≤ 8 / 7 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hbr : (1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)) ≤ 64 / 105 := by
      calc (1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)) ≤ (8 / 15) * (8 / 7) :=
            mul_le_mul ha1 ha2 (by positivity) (by norm_num)
        _ = 64 / 105 := by norm_num
    have ht1 : (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ))) ≤ 5 / δ ^ 3 := by
      calc (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)))
          ≤ (8 / δ ^ 3) * (64 / 105) := by
            apply mul_le_mul_of_nonneg_left hbr (by positivity)
        _ ≤ 5 / δ ^ 3 := by rw [div_mul_eq_mul_div, div_le_div_iff₀ hδ3 hδ3]; nlinarith [hδ3]
    have ht2 : (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) ≤ 5 / δ ^ 3 := by
      have hstep : (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) ≤ (4 / δ ^ 2) * (8 / 7) :=
        mul_le_mul_of_nonneg_left ha2 (by positivity)
      have hstep2 : (4 / δ ^ 2) * (8 / 7) = (32 / 7) * (1 / δ ^ 2) := by ring
      have hstep3 : (32 / 7 : ℝ) * (1 / δ ^ 2) ≤ (32 / 7) * (1 / δ ^ 3) :=
        mul_le_mul_of_nonneg_left hd23 (by norm_num)
      have hstep4 : (32 / 7 : ℝ) * (1 / δ ^ 3) ≤ 5 / δ ^ 3 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hδ3]; nlinarith [hδ3]
      linarith [hstep, hstep2, hstep3, hstep4]
    have h10 : (10 : ℝ) / δ ^ 3 = 5 / δ ^ 3 + 5 / δ ^ 3 := by ring
    linarith [ht1, ht2, h10]
  -- exact value of the head bracket
  have e1 : 1 / (4 * (θ * δ / 2) ^ 3) = 2 / (θ ^ 3 * δ ^ 3) := by
    rw [show (4 : ℝ) * (θ * δ / 2) ^ 3 = θ ^ 3 * δ ^ 3 / 2 from by ring]; rw [one_div_div]
  have e2 : Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 = 8 * Real.cosh 1 / ((1 - θ) ^ 3 * δ ^ 3) := by
    rw [show ((1 - θ) * δ / 2) ^ 3 = (1 - θ) ^ 3 * δ ^ 3 / 8 from by ring, div_div_eq_mul_div,
      mul_comm (Real.cosh 1) (8 : ℝ)]
  have hb2 : 8 * Real.cosh 1 / ((1 - θ) ^ 3 * δ ^ 3) ≤ 24 / δ ^ 3 := by
    have h1θ3 : (7 / 8 : ℝ) ^ 3 ≤ (1 - θ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 3
    rw [div_le_div_iff₀ (by nlinarith [h1θ3, hδ3] : (0 : ℝ) < (1 - θ) ^ 3 * δ ^ 3) hδ3]
    nlinarith [cosh_one_lt_two, hδ3, Real.cosh_pos (1 : ℝ), h1θ3]
  have hheadval : 2 / (θ ^ 3 * δ ^ 3) - 24 / δ ^ 3 ≤ fa 0 - fb 0 := by
    rw [e1, e2] at hhead0
    linarith [hb2]
  have hred := l1_reduction hMN fa fb
  have hbridge : (2 / θ ^ 3 - 34) / δ ^ 3 = 2 / (θ ^ 3 * δ ^ 3) - 24 / δ ^ 3 - 10 / δ ^ 3 := by
    have hθne : θ ≠ 0 := hθ0.ne'
    have hδne : δ ≠ 0 := hδ0.ne'
    field_simp
    ring
  have htailfull : (∑ k ∈ Ico M N, fb k) ≤ 10 / δ ^ 3 := le_trans htail hTup
  linarith [hred, hheadsum, hheadval, htailfull, hbridge.le, hbridge.ge]

set_option maxHeartbeats 800000 in
/-- Derivative of the lattice energy in the offset variable:
`W(ϑ) = ¼[Σ_{k<N} csch²((1−ϑ+k)δ/2) + Σ_{k<M} csch²((ϑ+k)δ/2)]` has
`W′(ϑ) = (δ/4)·[Σ_{k<N} φ(b_k) − Σ_{k<M} φ(a_k)]`: moving toward the behind train relaxes
it and compresses the ahead train. -/
theorem lattice_energy_hasDerivAt {δ : ℝ} (hδ0 : 0 < δ) (M N : ℕ) {ϑ : ℝ}
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) :
    HasDerivAt (fun y => (1 / 4) * ((∑ k ∈ range N, (rcsch ((1 - y + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range M, (rcsch ((y + k) * (δ / 2))) ^ 2))
      ((δ / 4) * ((∑ k ∈ range N, rphi ((1 - ϑ + k) * (δ / 2)))
        - ∑ k ∈ range M, rphi ((ϑ + k) * (δ / 2)))) ϑ := by
  have hb : ∀ k ∈ range N, HasDerivAt (fun y => (rcsch ((1 - y + (k : ℝ)) * (δ / 2))) ^ 2)
      (δ * rphi ((1 - ϑ + (k : ℝ)) * (δ / 2))) ϑ := by
    intro k _
    have harg : 0 < (1 - ϑ + (k : ℝ)) * (δ / 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith
    have hin : HasDerivAt (fun y : ℝ => (1 - y + (k : ℝ)) * (δ / 2)) ((0 - 1) * (δ / 2)) ϑ :=
      (((hasDerivAt_const ϑ (1 : ℝ)).sub (hasDerivAt_id ϑ)).add_const (k : ℝ)).mul_const (δ / 2)
    have hcomp := (rcsch_sq_hasDerivAt harg.ne').comp ϑ hin
    convert hcomp using 1
    ring
  have ha : ∀ k ∈ range M, HasDerivAt (fun y => (rcsch ((y + (k : ℝ)) * (δ / 2))) ^ 2)
      (-(δ * rphi ((ϑ + (k : ℝ)) * (δ / 2)))) ϑ := by
    intro k _
    have harg : 0 < (ϑ + (k : ℝ)) * (δ / 2) := by positivity
    have hin : HasDerivAt (fun y : ℝ => (y + (k : ℝ)) * (δ / 2)) (1 * (δ / 2)) ϑ :=
      ((hasDerivAt_id ϑ).add_const (k : ℝ)).mul_const (δ / 2)
    have hcomp := (rcsch_sq_hasDerivAt harg.ne').comp ϑ hin
    convert hcomp using 1
    ring
  have hbsum := HasDerivAt.fun_sum (fun k hk => hb k hk)
  have hasum := HasDerivAt.fun_sum (fun k hk => ha k hk)
  have h := (hbsum.add hasum).const_mul (1 / 4 : ℝ)
  convert h using 1
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

set_option maxHeartbeats 6400000 in
/-- **One step of the equilibrium march strictly increases the energy** (the constant-step
lattice form of energy monotonicity). Let `θ` be an equilibrium of the split
(`N` behind, `m+1` ahead) and `θ'` an equilibrium of the shifted split (`N+1` behind, `m`
ahead) with the same total charge `N + m + 1`. If `θ ≤ 1/8`, `δ ≤ 1` and `δm² ≥ 4`, then
`W_{N,m+1}(θ) < W_{N+1,m}(θ')`. The constraint pins the drift `θ − θ'` inside
`[(32/39)δθ'², (3/7)θ]`; the energy climbs along it by at least `1/δ`
(`dW_margin_small_delta`), beating the re-split loss `≤ 1/(4δ)`. -/
theorem lattice_step_energy_increase {θ θ' δ : ℝ} {m N : ℕ} (hm1 : 1 ≤ m) (hmN : m + 1 ≤ N)
    (hθ0 : 0 < θ) (hθ8 : θ ≤ 1 / 8) (hθ'0 : 0 < θ') (hθ'1 : θ' < 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hband : 4 ≤ δ * (m : ℝ) ^ 2)
    (hEq1 : (∑ k ∈ range N, rcoth ((1 - θ + k) * (δ / 2)))
        - (∑ k ∈ range (m + 1), rcoth ((θ + k) * (δ / 2))) = -((N : ℝ) + m + 1))
    (hEq2 : (∑ k ∈ range (N + 1), rcoth ((1 - θ' + k) * (δ / 2)))
        - (∑ k ∈ range m, rcoth ((θ' + k) * (δ / 2))) = -((N : ℝ) + m + 1)) :
    (1 / 4) * ((∑ k ∈ range N, (rcsch ((1 - θ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range (m + 1), (rcsch ((θ + k) * (δ / 2))) ^ 2)
      < (1 / 4) * ((∑ k ∈ range (N + 1), (rcsch ((1 - θ' + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range m, (rcsch ((θ' + k) * (δ / 2))) ^ 2) := by
  have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmR : (0 : ℝ) < (m : ℝ) := by linarith
  set G : ℝ → ℝ := fun y => (∑ k ∈ range (N + 1), rcoth ((1 - y + k) * (δ / 2)))
      - ∑ k ∈ range m, rcoth ((y + k) * (δ / 2)) with hG
  set Wnew : ℝ → ℝ := fun y => (1 / 4) * ((∑ k ∈ range (N + 1),
      (rcsch ((1 - y + k) * (δ / 2))) ^ 2) + ∑ k ∈ range m, (rcsch ((y + k) * (δ / 2))) ^ 2)
    with hWnew
  have hGθ' : G θ' = -((N : ℝ) + m + 1) := hEq2
  -- G at the OLD equilibrium exceeds the level by the two coth extras (the swap value)
  have hGθ : G θ = -((N : ℝ) + m + 1)
      + (rcoth ((1 - θ + (N : ℝ)) * (δ / 2)) + rcoth ((θ + (m : ℝ)) * (δ / 2))) := by
    simp only [hG]
    rw [Finset.sum_range_succ (fun k => rcoth ((1 - θ + (k : ℝ)) * (δ / 2))) N,
      show (∑ k ∈ range m, rcoth ((θ + (k : ℝ)) * (δ / 2)))
        = (∑ k ∈ range (m + 1), rcoth ((θ + (k : ℝ)) * (δ / 2)))
          - rcoth ((θ + (m : ℝ)) * (δ / 2)) from by
        rw [Finset.sum_range_succ (fun k => rcoth ((θ + (k : ℝ)) * (δ / 2))) m]; ring]
    linarith [hEq1]
  have hbNpos : (0 : ℝ) < (1 - θ + (N : ℝ)) * (δ / 2) := by
    have : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith
  have hampos : (0 : ℝ) < (θ + (m : ℝ)) * (δ / 2) := by positivity
  have hswpos : 2 < rcoth ((1 - θ + (N : ℝ)) * (δ / 2)) + rcoth ((θ + (m : ℝ)) * (δ / 2)) := by
    have h1 := one_lt_rcoth_of_pos hbNpos
    have h2 := one_lt_rcoth_of_pos hampos
    linarith
  -- the new equilibrium sits strictly inward
  have hθ'θ : θ' < θ := by
    rcases lt_trichotomy θ' θ with h | h | h
    · exact h
    · exfalso
      rw [h] at hGθ'
      linarith [hGθ, hGθ', hswpos]
    · exfalso
      have hmono : StrictMonoOn G (Set.Icc θ θ') := by
        apply strictMonoOn_of_deriv_pos (convex_Icc θ θ')
        · intro y hy
          exact (lattice_constraint_hasDerivAt hδ0 m (N + 1)
            (lt_of_lt_of_le hθ0 hy.1)
            (lt_of_le_of_lt hy.2 hθ'1)).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          have hd : HasDerivAt G ((δ / 2) * ((∑ k ∈ range (N + 1),
              (rcsch ((1 - y + k) * (δ / 2))) ^ 2)
              + ∑ k ∈ range m, (rcsch ((y + k) * (δ / 2))) ^ 2)) y :=
            lattice_constraint_hasDerivAt hδ0 m (N + 1) (lt_trans hθ0 hy.1)
              (lt_trans hy.2 hθ'1)
          rw [hd.deriv]
          have hy0 : 0 < y := lt_trans hθ0 hy.1
          have hpos0 : 0 < ∑ k ∈ range m, (rcsch ((y + (k : ℝ)) * (δ / 2))) ^ 2 := by
            apply Finset.sum_pos
            · intro k _
              have harg : 0 < (y + (k : ℝ)) * (δ / 2) := by positivity
              have := rcsch_pos_of_pos harg
              positivity
            · exact Finset.nonempty_range_iff.mpr (by omega)
          have hpos1 : 0 ≤ ∑ k ∈ range (N + 1), (rcsch ((1 - y + (k : ℝ)) * (δ / 2))) ^ 2 :=
            Finset.sum_nonneg (fun k _ => by positivity)
          exact mul_pos (by positivity) (add_pos_of_nonneg_of_pos hpos1 hpos0)
      have hlt := hmono (Set.left_mem_Icc.mpr h.le) (Set.right_mem_Icc.mpr h.le) h
      linarith [hGθ, hGθ', hswpos, hlt]
  have hgap : (0 : ℝ) < θ - θ' := by linarith
  have hθ'8 : θ' ≤ 1 / 8 := by linarith
  -- MVT for the constraint on [θ', θ]
  have hcontG : ContinuousOn G (Set.Icc θ' θ) := by
    intro y hy
    exact (lattice_constraint_hasDerivAt hδ0 m (N + 1)
      (lt_of_lt_of_le hθ'0 hy.1)
      (by linarith [hy.2] : y < 1)).continuousAt.continuousWithinAt
  have hderivG : ∀ y ∈ Set.Ioo θ' θ,
      HasDerivAt G ((fun y => (δ / 2) * ((∑ k ∈ range (N + 1),
        (rcsch ((1 - y + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range m, (rcsch ((y + k) * (δ / 2))) ^ 2)) y) y := by
    intro y hy
    exact lattice_constraint_hasDerivAt hδ0 m (N + 1) (lt_trans hθ'0 hy.1)
      (by linarith [hy.2] : y < 1)
  obtain ⟨ζ, hζ, hslopeG⟩ := exists_hasDerivAt_eq_slope G
    (fun y => (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - y + k) * (δ / 2))) ^ 2)
      + ∑ k ∈ range m, (rcsch ((y + k) * (δ / 2))) ^ 2)) hθ'θ hcontG hderivG
  rw [eq_div_iff hgap.ne'] at hslopeG
  have hζ0 : 0 < ζ := lt_trans hθ'0 hζ.1
  have hζθ : ζ < θ := hζ.2
  -- the drift equation: g'(ζ)·(θ − θ') = swap value
  have hswval : (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
      + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2) * (θ - θ')
      = rcoth ((1 - θ + (N : ℝ)) * (δ / 2)) + rcoth ((θ + (m : ℝ)) * (δ / 2)) := by
    linarith [hslopeG, hGθ, hGθ']
  -- derivative upper bound 39/(16δθ'²) at ζ
  have hbup : ∑ k ∈ range (N + 1), (rcsch ((1 - ζ + (k : ℝ)) * (δ / 2))) ^ 2 ≤ 24 / δ ^ 2 := by
    have hterm : ∀ k ∈ range (N + 1), (rcsch ((1 - ζ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ (4 / δ ^ 2) * (1 / (1 / 2 + (k : ℝ)) ^ 2) := by
      intro k _
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hpos2 : 0 < (1 / 2 + (k : ℝ)) * (δ / 2) := by positivity
      have hle : (1 / 2 + (k : ℝ)) * (δ / 2) ≤ (1 - ζ + (k : ℝ)) * (δ / 2) := by
        nlinarith [hζθ, hθ8, hδ0]
      have hmono : (rcsch ((1 - ζ + (k : ℝ)) * (δ / 2))) ^ 2
          ≤ (rcsch ((1 / 2 + (k : ℝ)) * (δ / 2))) ^ 2 := by
        rcases eq_or_lt_of_le hle with h | h
        · rw [← h]
        · have h1 : rcsch ((1 - ζ + (k : ℝ)) * (δ / 2))
              ≤ rcsch ((1 / 2 + (k : ℝ)) * (δ / 2)) :=
            (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hpos2)
              (Set.mem_Ioi.mpr (lt_of_lt_of_le hpos2 hle)) h).le
          exact pow_le_pow_left₀ (rcsch_pos_of_pos (lt_of_lt_of_le hpos2 hle)).le h1 2
      have hinv := rcsch_sq_le_inv_sq hpos2
      have heq : 1 / ((1 / 2 + (k : ℝ)) * (δ / 2)) ^ 2
          = (4 / δ ^ 2) * (1 / (1 / 2 + (k : ℝ)) ^ 2) := by
        rw [mul_pow]
        field_simp
        ring
      linarith [hmono, hinv, heq.ge]
    have hsum6 : ∑ k ∈ range (N + 1), 1 / ((1 : ℝ) / 2 + (k : ℝ)) ^ 2 ≤ 6 := by
      have h1N : 1 ≤ N + 1 := by omega
      have hsplit := Finset.sum_range_add_sum_Ico
        (fun k => 1 / ((1 : ℝ) / 2 + (k : ℝ)) ^ 2) h1N
      have htel := inv_sq_telescope (a := 1 / 2) (M := 1) (N := N + 1) h1N
        (by norm_num : (0 : ℝ) < 1 / 2 + (1 : ℕ) - 1)
      have h0 : ∑ k ∈ range 1, 1 / ((1 : ℝ) / 2 + (k : ℝ)) ^ 2 = 4 := by
        rw [Finset.sum_range_one]
        norm_num
      have htelval : (1 : ℝ) / (1 / 2 + (1 : ℕ) - 1) = 2 := by norm_num
      rw [htelval] at htel
      linarith [hsplit, htel, h0]
    calc ∑ k ∈ range (N + 1), (rcsch ((1 - ζ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ ∑ k ∈ range (N + 1), (4 / δ ^ 2) * (1 / (1 / 2 + (k : ℝ)) ^ 2) :=
          Finset.sum_le_sum hterm
      _ = (4 / δ ^ 2) * ∑ k ∈ range (N + 1), 1 / (1 / 2 + (k : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (4 / δ ^ 2) * 6 := by
          apply mul_le_mul_of_nonneg_left hsum6 (by positivity)
      _ = 24 / δ ^ 2 := by ring
  have haup : ∑ k ∈ range m, (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2
      ≤ (4 / δ ^ 2) * (1 / ζ ^ 2 + 1 / ζ) := by
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2) hm1
    have h0 : ∑ k ∈ range 1, (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ (4 / δ ^ 2) * (1 / ζ ^ 2) := by
      rw [Finset.sum_range_one]
      have harg : (0 : ℝ) < (ζ + ((0 : ℕ) : ℝ)) * (δ / 2) := by
        simp only [Nat.cast_zero, add_zero]
        positivity
      have hinv := rcsch_sq_le_inv_sq harg
      have heq : 1 / ((ζ + ((0 : ℕ) : ℝ)) * (δ / 2)) ^ 2 = (4 / δ ^ 2) * (1 / ζ ^ 2) := by
        simp only [Nat.cast_zero, add_zero]
        rw [mul_pow]
        field_simp
        ring
      linarith [hinv, heq.ge]
    have hIco : ∑ k ∈ Ico 1 m, (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ (4 / δ ^ 2) * (1 / ζ) := by
      have hterm : ∀ k ∈ Ico 1 m, (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2
          ≤ (4 / δ ^ 2) * (1 / (ζ + (k : ℝ)) ^ 2) := by
        intro k _
        have harg : (0 : ℝ) < (ζ + (k : ℝ)) * (δ / 2) := by positivity
        have hinv := rcsch_sq_le_inv_sq harg
        have heq : 1 / ((ζ + (k : ℝ)) * (δ / 2)) ^ 2
            = (4 / δ ^ 2) * (1 / (ζ + (k : ℝ)) ^ 2) := by
          rw [mul_pow]
          field_simp
          ring
        linarith [hinv, heq.ge]
      have htel := inv_sq_telescope (a := ζ) (M := 1) (N := m) hm1
        (by push_cast; linarith : (0 : ℝ) < ζ + (1 : ℕ) - 1)
      have htelval : (1 : ℝ) / (ζ + (1 : ℕ) - 1) = 1 / ζ := by
        push_cast
        ring_nf
      rw [htelval] at htel
      calc ∑ k ∈ Ico 1 m, (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2
          ≤ ∑ k ∈ Ico 1 m, (4 / δ ^ 2) * (1 / (ζ + (k : ℝ)) ^ 2) := Finset.sum_le_sum hterm
        _ = (4 / δ ^ 2) * ∑ k ∈ Ico 1 m, 1 / (ζ + (k : ℝ)) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ (4 / δ ^ 2) * (1 / ζ) := mul_le_mul_of_nonneg_left htel (by positivity)
    have hmulout : (4 / δ ^ 2) * (1 / ζ ^ 2) + (4 / δ ^ 2) * (1 / ζ)
        = (4 / δ ^ 2) * (1 / ζ ^ 2 + 1 / ζ) := by ring
    linarith [hsplit, h0, hIco, hmulout.le, hmulout.ge]
  have hgup : (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
      + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2) ≤ 39 / (16 * δ * θ' ^ 2) := by
    have hz1 : 1 / ζ ≤ 1 / θ' := one_div_le_one_div_of_le hθ'0 hζ.1.le
    have hz2 : 1 / ζ ^ 2 ≤ 1 / θ' ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hθ'0.le hζ.1.le 2)
    have hbase : 6 + 1 / θ' ^ 2 + 1 / θ' ≤ 39 / (32 * θ' ^ 2) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 32 * θ' ^ 2)]
      have hexp : (6 + 1 / θ' ^ 2 + 1 / θ') * (32 * θ' ^ 2)
          = 192 * θ' ^ 2 + 32 + 32 * θ' := by
        field_simp
        ring
      rw [hexp]
      nlinarith [pow_le_pow_left₀ hθ'0.le hθ'8 2, hθ'8, hθ'0]
    have hstep : (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2)
        ≤ (δ / 2) * (24 / δ ^ 2 + (4 / δ ^ 2) * (1 / θ' ^ 2 + 1 / θ')) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : (4 / δ ^ 2) * (1 / ζ ^ 2 + 1 / ζ) ≤ (4 / δ ^ 2) * (1 / θ' ^ 2 + 1 / θ') := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hz1, hz2]
      linarith [hbup, haup, h1]
    have hval1 : (δ / 2) * (24 / δ ^ 2 + (4 / δ ^ 2) * (1 / θ' ^ 2 + 1 / θ'))
        = (2 / δ) * (6 + 1 / θ' ^ 2 + 1 / θ') := by
      field_simp
      ring
    have hval2 : (2 / δ) * (39 / (32 * θ' ^ 2)) = 39 / (16 * δ * θ' ^ 2) := by
      field_simp
      ring
    calc (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2)
        ≤ (δ / 2) * (24 / δ ^ 2 + (4 / δ ^ 2) * (1 / θ' ^ 2 + 1 / θ')) := hstep
      _ = (2 / δ) * (6 + 1 / θ' ^ 2 + 1 / θ') := hval1
      _ ≤ (2 / δ) * (39 / (32 * θ' ^ 2)) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = 39 / (16 * δ * θ' ^ 2) := hval2
  -- derivative lower bound 7/(4θ²δ) at ζ
  have hglo : 7 / (4 * θ ^ 2 * δ) ≤ (δ / 2)
      * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2) := by
    have hnn : ∀ k ∈ range m, (0 : ℝ) ≤ (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2 :=
      fun k _ => sq_nonneg _
    have h00 : (rcsch ((ζ + ((0 : ℕ) : ℝ)) * (δ / 2))) ^ 2
        ≤ ∑ k ∈ range m, (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2 :=
      Finset.single_le_sum hnn (Finset.mem_range.mpr (show 0 < m by omega))
    simp only [Nat.cast_zero, add_zero] at h00
    have hargζ : (0 : ℝ) < ζ * (δ / 2) := by positivity
    have hargθ : (0 : ℝ) < θ * (δ / 2) := by positivity
    have hanti : (rcsch (θ * (δ / 2))) ^ 2 ≤ (rcsch (ζ * (δ / 2))) ^ 2 := by
      have hlt : ζ * (δ / 2) < θ * (δ / 2) := by nlinarith [hζθ, hδ0]
      have h1 : rcsch (θ * (δ / 2)) ≤ rcsch (ζ * (δ / 2)) :=
        (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hargζ) (Set.mem_Ioi.mpr hargθ) hlt).le
      exact pow_le_pow_left₀ (rcsch_pos_of_pos hargθ).le h1 2
    have hexp := rcsch_sq_ge_exp hargθ
    have he78 : (7 : ℝ) / 8 ≤ Real.exp (-(2 * (θ * (δ / 2)))) := by
      have h1 := Real.add_one_le_exp (-(2 * (θ * (δ / 2))))
      have h2 : θ * δ ≤ 1 / 8 := by
        nlinarith [mul_le_mul hθ8 hδ1 hδ0.le (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      nlinarith [h1, h2]
    have h1 : (7 / 8 : ℝ) / (θ * (δ / 2)) ^ 2
        ≤ Real.exp (-(2 * (θ * (δ / 2)))) / (θ * (δ / 2)) ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right he78 (by positivity)
    have hval : (7 / 8 : ℝ) / (θ * (δ / 2)) ^ 2 = 7 / (2 * θ ^ 2 * δ ^ 2) := by
      field_simp
      ring
    have hlow : 7 / (2 * θ ^ 2 * δ ^ 2) ≤ (rcsch (ζ * (δ / 2))) ^ 2 := by
      linarith [hval.ge, h1, hexp, hanti]
    have hBnn : 0 ≤ ∑ k ∈ range (N + 1), (rcsch ((1 - ζ + (k : ℝ)) * (δ / 2))) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hA : 7 / (2 * θ ^ 2 * δ ^ 2) ≤ ∑ k ∈ range m, (rcsch ((ζ + (k : ℝ)) * (δ / 2))) ^ 2 :=
      le_trans hlow h00
    have hval2 : (δ / 2) * (7 / (2 * θ ^ 2 * δ ^ 2)) = 7 / (4 * θ ^ 2 * δ) := by
      field_simp
      ring
    calc 7 / (4 * θ ^ 2 * δ) = (δ / 2) * (7 / (2 * θ ^ 2 * δ ^ 2)) := hval2.symm
      _ ≤ (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
          + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hA, hBnn]
  -- the swap value bracket
  have hswub : rcoth ((1 - θ + (N : ℝ)) * (δ / 2)) + rcoth ((θ + (m : ℝ)) * (δ / 2))
      ≤ 2 + 4 / ((m : ℝ) * δ) := by
    have h1 := rcoth_lt_inv_add_one hbNpos
    have h2 := rcoth_lt_inv_add_one hampos
    have hmN0 : m ≤ N := by omega
    have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN0
    have h3 : 1 / ((1 - θ + (N : ℝ)) * (δ / 2)) ≤ 2 / ((m : ℝ) * δ) := by
      rw [div_le_div_iff₀ hbNpos (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ + (N : ℝ) - (m : ℝ)) hδ0.le]
    have h4 : 1 / ((θ + (m : ℝ)) * (δ / 2)) ≤ 2 / ((m : ℝ) * δ) := by
      rw [div_le_div_iff₀ hampos (by positivity)]
      nlinarith [mul_nonneg hθ0.le hδ0.le]
    have hb : (4 : ℝ) / ((m : ℝ) * δ) = 2 / ((m : ℝ) * δ) + 2 / ((m : ℝ) * δ) := by ring
    linarith [h1, h2, h3, h4, hb]
  -- drift bracket
  have hdlo : (32 / 39) * δ * θ' ^ 2 ≤ θ - θ' := by
    have h2 : (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2) * (θ - θ')
        ≤ 39 / (16 * δ * θ' ^ 2) * (θ - θ') :=
      mul_le_mul_of_nonneg_right hgup hgap.le
    have h3 : 2 < 39 / (16 * δ * θ' ^ 2) * (θ - θ') := by
      linarith [hswval, hswpos, h2]
    have h4 : (0 : ℝ) < 16 * δ * θ' ^ 2 := by positivity
    have h5 : 39 / (16 * δ * θ' ^ 2) * (θ - θ') * (16 * δ * θ' ^ 2)
        = 39 * (θ - θ') := by
      field_simp
    have h6 := mul_lt_mul_of_pos_right h3 h4
    rw [h5] at h6
    nlinarith [h6]
  have hdhi : θ - θ' ≤ (3 / 7) * θ := by
    have h2 : 7 / (4 * θ ^ 2 * δ) * (θ - θ')
        ≤ (δ / 2) * ((∑ k ∈ range (N + 1), (rcsch ((1 - ζ + k) * (δ / 2))) ^ 2)
          + ∑ k ∈ range m, (rcsch ((ζ + k) * (δ / 2))) ^ 2) * (θ - θ') :=
      mul_le_mul_of_nonneg_right hglo hgap.le
    have h1 : 7 / (4 * θ ^ 2 * δ) * (θ - θ') ≤ 2 + 4 / ((m : ℝ) * δ) := by
      linarith [hswval, hswub, h2]
    have h5 := mul_le_mul_of_nonneg_right h1
      (by positivity : (0 : ℝ) ≤ 4 * θ ^ 2 * δ / 7)
    have h6 : 7 / (4 * θ ^ 2 * δ) * (θ - θ') * (4 * θ ^ 2 * δ / 7) = θ - θ' := by
      field_simp
    rw [h6] at h5
    have h7 : (2 + 4 / ((m : ℝ) * δ)) * (4 * θ ^ 2 * δ / 7)
        = 8 * θ ^ 2 * δ / 7 + 16 * θ ^ 2 / (7 * (m : ℝ)) := by
      field_simp
      ring
    have hθδ : θ * δ ≤ 1 / 8 := by nlinarith
    have h8 : 8 * θ ^ 2 * δ / 7 ≤ θ / 7 := by
      nlinarith [mul_le_mul_of_nonneg_left hθδ (by linarith : (0 : ℝ) ≤ 8 * θ)]
    have h9 : 16 * θ ^ 2 / (7 * (m : ℝ)) ≤ 2 * θ / 7 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 14 * θ)
        (by linarith : (0 : ℝ) ≤ (m : ℝ) - 8 * θ)]
    linarith [h5, h7.le, h7.ge, h8, h9]
  have hθ'ge : (4 / 7) * θ ≤ θ' := by linarith
  -- MVT for the energy on [θ', θ]
  have hcontW : ContinuousOn Wnew (Set.Icc θ' θ) := by
    intro y hy
    exact (lattice_energy_hasDerivAt hδ0 m (N + 1)
      (lt_of_lt_of_le hθ'0 hy.1)
      (by linarith [hy.2] : y < 1)).continuousAt.continuousWithinAt
  have hderivW : ∀ y ∈ Set.Ioo θ' θ,
      HasDerivAt Wnew ((fun y => (δ / 4) * ((∑ k ∈ range (N + 1),
        rphi ((1 - y + k) * (δ / 2))) - ∑ k ∈ range m, rphi ((y + k) * (δ / 2)))) y) y := by
    intro y hy
    exact lattice_energy_hasDerivAt hδ0 m (N + 1) (lt_trans hθ'0 hy.1)
      (by linarith [hy.2] : y < 1)
  obtain ⟨η, hη, hslopeW⟩ := exists_hasDerivAt_eq_slope Wnew
    (fun y => (δ / 4) * ((∑ k ∈ range (N + 1), rphi ((1 - y + k) * (δ / 2)))
      - ∑ k ∈ range m, rphi ((y + k) * (δ / 2)))) hθ'θ hcontW hderivW
  rw [eq_div_iff hgap.ne'] at hslopeW
  have hη0 : 0 < η := lt_trans hθ'0 hη.1
  have hη8 : η ≤ 1 / 8 := by linarith [hη.2]
  have hmarg := dW_margin_small_delta (show m ≤ N + 1 by omega) hm1 hη0 hη8 hδ0 hδ1
  have hθ3pos : (0 : ℝ) < θ ^ 3 := by positivity
  -- transfer the margin from η to θ
  have hη3 : (2 / θ ^ 3 - 34) / δ ^ 3 ≤ (2 / η ^ 3 - 34) / δ ^ 3 := by
    have h1 : η ^ 3 ≤ θ ^ 3 := pow_le_pow_left₀ hη0.le hη.2.le 3
    have h3 := one_div_le_one_div_of_le (pow_pos hη0 3) h1
    have hb1 : (2 / θ ^ 3 - 34) / δ ^ 3 = (2 * (1 / θ ^ 3) - 34) * (1 / δ ^ 3) := by ring
    have hb2 : (2 / η ^ 3 - 34) / δ ^ 3 = (2 * (1 / η ^ 3) - 34) * (1 / δ ^ 3) := by ring
    rw [hb1, hb2]
    apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ 1 / δ ^ 3)
    linarith [h3]
  have hmargθpos : (0 : ℝ) < (2 / θ ^ 3 - 34) / δ ^ 3 := by
    have h1 : θ ^ 3 ≤ 1 / 512 := by nlinarith [pow_le_pow_left₀ hθ0.le hθ8 3]
    have h2 : (1024 : ℝ) ≤ 2 / θ ^ 3 := by
      rw [le_div_iff₀ hθ3pos]
      nlinarith [h1, hθ3pos]
    exact div_pos (by linarith) (by positivity)
  -- the gain along the drift
  have hgain : 1 / δ ≤ Wnew θ' - Wnew θ := by
    have hWdiff : Wnew θ' - Wnew θ
        = (θ - θ') * ((δ / 4) * ((∑ k ∈ range m, rphi ((η + k) * (δ / 2)))
          - ∑ k ∈ range (N + 1), rphi ((1 - η + k) * (δ / 2)))) := by
      linear_combination hslopeW
    rw [hWdiff]
    have hSlb : (2 / θ ^ 3 - 34) / δ ^ 3
        ≤ (∑ k ∈ range m, rphi ((η + k) * (δ / 2)))
          - ∑ k ∈ range (N + 1), rphi ((1 - η + k) * (δ / 2)) := le_trans hη3 hmarg
    have hfac : (0 : ℝ) ≤ (δ / 4) * ((2 / θ ^ 3 - 34) / δ ^ 3) :=
      le_of_lt (mul_pos (by positivity) hmargθpos)
    have hp1 : (32 / 39) * δ * θ' ^ 2 * ((δ / 4) * ((2 / θ ^ 3 - 34) / δ ^ 3))
        ≤ (θ - θ') * ((δ / 4) * ((∑ k ∈ range m, rphi ((η + k) * (δ / 2)))
          - ∑ k ∈ range (N + 1), rphi ((1 - η + k) * (δ / 2)))) :=
      mul_le_mul hdlo (mul_le_mul_of_nonneg_left hSlb (by positivity)) hfac hgap.le
    have hcore : 39 * θ ^ 3 ≤ 8 * θ' ^ 2 * (2 - 34 * θ ^ 3) := by
      have c1 : θ ^ 3 ≤ 1 / 512 := by nlinarith [pow_le_pow_left₀ hθ0.le hθ8 3]
      have c2 : (495 : ℝ) / 256 ≤ 2 - 34 * θ ^ 3 := by linarith
      have c3 : (16 / 49) * θ ^ 2 ≤ θ' ^ 2 := by
        nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 / 7 * θ) hθ'ge 2]
      have c4 : (16 / 49) * θ ^ 2 * ((495 : ℝ) / 256) ≤ θ' ^ 2 * (2 - 34 * θ ^ 3) :=
        mul_le_mul c3 c2 (by norm_num) (sq_nonneg θ')
      have c5 : θ ^ 3 ≤ θ ^ 2 * (1 / 8) := by
        nlinarith [mul_le_mul_of_nonneg_left hθ8 (sq_nonneg θ)]
      linarith [c4, c5]
    have hp2 : 1 / δ ≤ (32 / 39) * δ * θ' ^ 2 * ((δ / 4) * ((2 / θ ^ 3 - 34) / δ ^ 3)) := by
      have hθne : θ ≠ 0 := hθ0.ne'
      have hδne : δ ≠ 0 := hδ0.ne'
      have hA : (32 / 39) * δ * θ' ^ 2 * ((δ / 4) * ((2 / θ ^ 3 - 34) / δ ^ 3))
          = (8 * θ' ^ 2 * (2 - 34 * θ ^ 3)) / (39 * θ ^ 3) * (1 / δ) := by
        field_simp
        ring
      rw [hA]
      have hB : (1 : ℝ) ≤ (8 * θ' ^ 2 * (2 - 34 * θ ^ 3)) / (39 * θ ^ 3) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 39 * θ ^ 3)]
        linarith [hcore]
      have hstep := mul_le_mul hB (le_refl (1 / δ)) (by positivity) (by linarith [hB])
      calc 1 / δ = 1 * (1 / δ) := by ring
        _ ≤ (8 * θ' ^ 2 * (2 - 34 * θ ^ 3)) / (39 * θ ^ 3) * (1 / δ) := hstep
    linarith [hp1, hp2]
  -- the re-split loss
  have hlossY : (rcsch ((θ + (m : ℝ)) * (δ / 2))) ^ 2 ≤ 1 / δ := by
    have h1 := rcsch_sq_le_inv_sq hampos
    have h2 : 1 / ((θ + (m : ℝ)) * (δ / 2)) ^ 2 ≤ 1 / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ0]
      have hint1 : 4 * δ ≤ δ * (m : ℝ) ^ 2 * δ := by nlinarith [hband, hδ0]
      nlinarith [hint1, mul_nonneg (mul_nonneg hθ0.le hmR.le) (sq_nonneg δ),
        mul_nonneg (sq_nonneg θ) (sq_nonneg δ)]
    linarith
  have hlossid : Wnew θ - ((1 / 4) * ((∑ k ∈ range N, (rcsch ((1 - θ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range (m + 1), (rcsch ((θ + k) * (δ / 2))) ^ 2))
      = (1 / 4) * ((rcsch ((1 - θ + (N : ℝ)) * (δ / 2))) ^ 2
        - (rcsch ((θ + (m : ℝ)) * (δ / 2))) ^ 2) := by
    simp only [hWnew]
    rw [Finset.sum_range_succ (fun k => (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2) N,
      Finset.sum_range_succ (fun k => (rcsch ((θ + (k : ℝ)) * (δ / 2))) ^ 2) m]
    ring
  have hXnn : (0 : ℝ) ≤ (rcsch ((1 - θ + (N : ℝ)) * (δ / 2))) ^ 2 := sq_nonneg _
  have hδinvpos : (0 : ℝ) < 1 / δ := by positivity
  show (1 / 4) * ((∑ k ∈ range N, (rcsch ((1 - θ + k) * (δ / 2))) ^ 2)
      + ∑ k ∈ range (m + 1), (rcsch ((θ + k) * (δ / 2))) ^ 2) < Wnew θ'
  linarith [hgain, hlossid, hlossY, hXnn, hδinvpos]

end RHTower
