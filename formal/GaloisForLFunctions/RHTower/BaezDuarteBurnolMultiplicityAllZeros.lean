import GaloisForLFunctions.RHTower.BaezDuarteBurnolMultiplicity
import GaloisForLFunctions.RHTower.BaezDuarteBurnolAllCriticalZeros

/-!
# Burnol's multiplicity-weighted lower bound over all critical zeros

Let `m_ρ` be the order of the zero `ρ` of `ζ`.  For every real `c` below the extended sum
`Σ_ρ 2m_ρ²/|ρ|² ∈ [0, ∞]` over the distinct zeros on the critical line in the upper half-plane,

  `c ≤ d_N² log N`   for all large `N`

(`eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order`), that is,
`liminf d_N² log N ≥ Σ_ρ 2m_ρ²/|ρ|²`.  Conversely, `liminf d_N² log N ≤ Σ_ρ 2/|ρ|²` (the value at
simple zeros) forces RH and the simplicity of every critical zero
(`riemannHypothesis_and_simple_of_frequently_le_tsum`).

**Proof.**  A real number below an extended sum of nonnegative terms lies below a finite partial
sum, and Burnol's bound for finitely many multiple zeros applies
(`eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZeros`).  The derivatives of `ζ` below the
order vanish (`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`), and the order is finite
and positive at a zero `≠ 1`.
-/

open Complex Filter Topology

namespace RHTower

/-- At a zero `ρ ≠ 1` of `ζ`, the order `m = analyticOrderNatAt ζ ρ` is at least one and
`ζ^{(i)}(ρ) = 0` for `i < m`. -/
theorem one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hζ : riemannZeta ρ = 0) :
    1 ≤ analyticOrderNatAt riemannZeta ρ ∧
      ∀ i < analyticOrderNatAt riemannZeta ρ, iteratedDeriv i riemannZeta ρ = 0 := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (x := 2) (by simp) (by simpa using hρ1)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)))]
    exact ENat.zero_ne_top
  have hcast := Nat.cast_analyticOrderNatAt htop
  refine ⟨?_, (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp hcast.le⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [h0, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at hcast
  rcases hcast with h | h
  · exact h han
  · exact h hζ

/-- **Burnol's multiplicity-weighted bound over all critical zeros.**  If
`c < Σ_ρ 2m_ρ²/|ρ|²` in `[0, ∞]`, the sum over the distinct zeros `ρ` of `ζ` with `Re ρ = ½`,
`Im ρ > 0` and `m_ρ` their orders, then `c ≤ d_N² log N` for all large `N`. -/
theorem eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order {c : ℝ}
    (hc : ENNReal.ofReal c < ∑' ρ : criticalUpperZeros,
      ENNReal.ofReal (2 * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2)) :
    ∀ᶠ N : ℕ in atTop, c ≤ bdDistDiscrete N ^ 2 * Real.log N := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hc
  obtain ⟨s, hs⟩ := hc
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
    ENNReal.ofReal_lt_ofReal_iff'] at hs
  set Z : Finset ℂ := s.map (Function.Embedding.subtype _) with hZ
  have hZmem : ∀ ρ ∈ Z, ρ ∈ criticalUpperZeros := by
    intro ρ hρ
    rw [hZ, Finset.mem_map] at hρ
    obtain ⟨σ, -, rfl⟩ := hρ
    exact σ.2
  have hρ1 : ∀ ρ ∈ Z, ρ ≠ 1 := fun ρ hρ h => by
    have := (hZmem ρ hρ).2.1; rw [h] at this; norm_num at this
  have hZsum : ∑ ρ ∈ Z, 2 * (analyticOrderNatAt riemannZeta ρ : ℝ) ^ 2 / ‖ρ‖ ^ 2 =
      ∑ ρ ∈ s, 2 * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2 := by
    rw [hZ, Finset.sum_map]
    rfl
  refine eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZeros (Z := Z)
    (fun ρ hρ => (hZmem ρ hρ).2) (fun ρ => analyticOrderNatAt riemannZeta ρ)
    (fun ρ hρ => (one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta (hρ1 ρ hρ)
      (hZmem ρ hρ).1).1)
    (fun ρ hρ => (one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta (hρ1 ρ hρ)
      (hZmem ρ hρ).1).2) ?_
  rw [hZsum]
  exact hs.1

/-! ## The sharp rate as a receiver for RH and simplicity -/

/-- **A logarithmic rate along a subsequence gives RH.**  If `d_N² log N ≤ B` for infinitely many
`N`, then `d_N → 0` (the distances are antitone), hence RH. -/
theorem riemannHypothesis_of_frequently_bdDistDiscrete_sq_mul_log_le {B : ℝ}
    (h : ∃ᶠ N : ℕ in atTop, bdDistDiscrete N ^ 2 * Real.log N ≤ B) : RiemannHypothesis := by
  refine riemannHypothesis_of_tendsto_bdDistDiscrete ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  set B' : ℝ := max B 1 with hB'
  have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- a large index with a small distance
  obtain ⟨N₀, hN₀big, hN₀⟩ := Filter.frequently_atTop.mp h
    (⌈Real.exp (B' / ε ^ 2)⌉₊ + 2)
  have hN₀2 : (2 : ℝ) ≤ N₀ := by exact_mod_cast (by omega : 2 ≤ N₀)
  have hlogpos : 0 < Real.log N₀ := Real.log_pos (by linarith)
  have hlogbig : B' / ε ^ 2 < Real.log N₀ := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have h1 := Nat.le_ceil (Real.exp (B' / ε ^ 2))
    have h2 : ((⌈Real.exp (B' / ε ^ 2)⌉₊ + 2 : ℕ) : ℝ) ≤ N₀ := by exact_mod_cast hN₀big
    push_cast at h2
    linarith
  have hd0 : 0 ≤ bdDistDiscrete N₀ := (bdDistDiscrete_pos N₀).le
  have hdN₀ : bdDistDiscrete N₀ < ε := by
    have hsq : bdDistDiscrete N₀ ^ 2 < ε ^ 2 := by
      have h1 : bdDistDiscrete N₀ ^ 2 * Real.log N₀ ≤ B' := hN₀.trans (le_max_left _ _)
      have h2 : B' < ε ^ 2 * Real.log N₀ := by
        rw [div_lt_iff₀ (by positivity)] at hlogbig; linarith
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hlogpos.le
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq
  refine ⟨N₀, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (bdDistDiscrete_pos N).le]
  exact (bdDistDiscrete_antitone hN).trans_lt hdN₀

/-- **Burnol's rate at the distinct-zero value forces RH and simple critical zeros.**  Let
`S = Σ_ρ 2/|ρ|²` over the distinct zeros on the critical line in the upper half-plane.  If
`liminf_{N→∞} d_N² log N ≤ S`, then RH holds and every zero of `ζ` on the critical line is simple.
A multiple zero `ρ₀` of order `m₀ ≥ 2` would raise the floor to at least `S + 2(m₀² − 1)/|ρ₀|²`
(`eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order`). -/
theorem riemannHypothesis_and_simple_of_frequently_le_tsum
    (h : ∀ ε > 0, ∃ᶠ N : ℕ in atTop, bdDistDiscrete N ^ 2 * Real.log N ≤
      (∑' ρ : criticalUpperZeros, 2 / ‖(ρ : ℂ)‖ ^ 2) + ε) :
    RiemannHypothesis ∧ ∀ ρ ∈ criticalUpperZeros, analyticOrderNatAt riemannZeta ρ = 1 := by
  classical
  refine ⟨riemannHypothesis_of_frequently_bdDistDiscrete_sq_mul_log_le (h 1 one_pos), ?_⟩
  intro ρ₀ hρ₀
  have hρ₀1 : ρ₀ ≠ 1 := fun e => by have := hρ₀.2.1; rw [e] at this; norm_num at this
  have hm₀ := (one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta hρ₀1 hρ₀.1).1
  by_contra hne
  have hm₀2 : 2 ≤ analyticOrderNatAt riemannZeta ρ₀ := by omega
  set S : ℝ := ∑' ρ : criticalUpperZeros, 2 / ‖(ρ : ℂ)‖ ^ 2 with hS
  have hnorm : ∀ ρ ∈ criticalUpperZeros, 0 < ‖ρ‖ := fun ρ hρ =>
    norm_pos_iff.mpr fun e => by have := hρ.2.1; rw [e] at this; norm_num at this
  have hn₀ := hnorm ρ₀ hρ₀
  set δ : ℝ := 2 * ((analyticOrderNatAt riemannZeta ρ₀ : ℝ) ^ 2 - 1) / ‖ρ₀‖ ^ 2 with hδ
  have hm₀R : (2 : ℝ) ≤ analyticOrderNatAt riemannZeta ρ₀ := by exact_mod_cast hm₀2
  have hδ0 : 0 < δ := by
    have : (0 : ℝ) < (analyticOrderNatAt riemannZeta ρ₀ : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hS0 : 0 ≤ S := tsum_nonneg fun ρ => by positivity
  -- the extended multiplicity sum exceeds `S + δ/2`
  have hlt : ENNReal.ofReal (S + δ / 2) < ∑' ρ : criticalUpperZeros,
      ENNReal.ofReal (2 * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) := by
    set ρ₀' : criticalUpperZeros := ⟨ρ₀, hρ₀⟩
    have hpt : ∀ ρ : criticalUpperZeros, ENNReal.ofReal (2 / ‖(ρ : ℂ)‖ ^ 2) +
        (if ρ = ρ₀' then ENNReal.ofReal δ else 0) ≤
        ENNReal.ofReal (2 * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) := by
      intro ρ
      have hρ1 : (ρ : ℂ) ≠ 1 := fun e => by have := ρ.2.2.1; rw [e] at this; norm_num at this
      have hmρ := (one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta hρ1 ρ.2.1).1
      have hmρR : (1 : ℝ) ≤ analyticOrderNatAt riemannZeta (ρ : ℂ) := by exact_mod_cast hmρ
      have hnρ := hnorm ρ ρ.2
      split_ifs with he
      · rw [← ENNReal.ofReal_add (by positivity) hδ0.le]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        have hv : (ρ : ℂ) = ρ₀ := by rw [he]
        rw [hv, hδ]
        field_simp
        ring
      · rw [add_zero]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_div_iff_of_pos_right (by positivity)]
        nlinarith
    have hsum := ENNReal.tsum_le_tsum hpt
    rw [ENNReal.tsum_add, tsum_ite_eq, ← ENNReal.ofReal_tsum_of_nonneg (fun ρ => by positivity)
      summable_criticalUpperZeros_inv_sq, ← ENNReal.ofReal_add hS0 hδ0.le] at hsum
    refine lt_of_lt_of_le ?_ hsum
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  have hev := eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order hlt
  obtain ⟨N, hN1, hN2⟩ := ((h (δ / 4) (by positivity)).and_eventually hev).exists
  linarith

end RHTower
