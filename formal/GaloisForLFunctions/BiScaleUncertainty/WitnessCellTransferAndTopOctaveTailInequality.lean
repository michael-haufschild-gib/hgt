import GaloisForLFunctions.BiScaleUncertainty.VasyuninReciprocityAndExactTailGramProducer
import GaloisForLFunctions.BiScaleUncertainty.SawtoothCharacterExpansionAndCriticalStripPoleBridge

/-!
# Witness Single-Cell Transfer Laws, Top-Octave Origin-Mass Inequality & Route PM Master Synthesis

This module builds **Missing Tool 3** of the `BiScaleUncertainty` framework and completes the
end-to-end synthesis of all three missing tools across Routes `FZZ-P`, `PM`, and `PW-B`:

1. **Unconditional Witness Orthogonality to Cellular Möbius & Dyadic Resolvent Combinators (§1):**
   Every bundled square-integrable Fermi–Nyman witness `w : L2FermiWitness` is orthogonal on
   $(0, 1]$ to:
   - `dilatedMobiusFermiCombinator k N` (`B_{k, N}`),
   - `dyadicResolventCellThreshold k N` ($\widetilde{B}_{k, N}$), and
   - `singleCellFermiCombinator k N` ($\Delta_{k, N} = \widetilde{B}_{k, N} - \widetilde{B}_{k+1, N}$)
   for every cell index $k \ge 1$ and cutoff $N \ge 0$.

2. **Exact Single-Cell & Top-Octave Witness Transfer into the Small-$t$ Origin Tail (§2):**
   Because $\Delta_{k, N}(t) = \delta_{n, k}$ across all bulk cells $I_n = (1/(n+1), 1/n]$
   ($1 \le n \le N$), integrating $\Delta_{k, N}(t)\,\overline{w(t)}$ over the bulk head
   $(1/(N+1), 1]$ isolates the single cell integral $\int_{1/(k+1)}^{1/k} \overline{w(t)}\,dt$.
   Combining this with global witness orthogonality $\int_0^1 \Delta_{k, N}(t)\,\overline{w(t)}\,dt = 0$
   transfers every bulk cell integral **identically into the small-$t$ origin tail** $(0, 1/(N+1)]$:
   $$\int_{1/(k+1)}^{1/k} \overline{w(t)}\,dt
     = -\int_0^{1/(N+1)} \operatorname{singleCellFermiCombinator}(k, N, t)\,\overline{w(t)}\,dt.$$
   In particular, for $k = 1$ at cutoff $N + 1$, the top-octave integral on $(1/2, 1]$ is
   transferred purely to $(0, 1/(N+2)]$, with all intermediate cells $I_2, \dots, I_{N+1}$
   identically cancelled:
   $$\int_{1/2}^1 \overline{w(t)}\,dt
     = -\int_0^{1/(N+2)} \operatorname{singleCellFermiCombinator}(1, N + 1, t)\,\overline{w(t)}\,dt.$$

3. **Cauchy–Schwarz Origin-Mass & Global-Minus-Cell Energy Bounds on Witness Cell Integrals (§3):**
   Applying Cauchy–Schwarz on $(0, 1/(N+1)]$ and substituting the exact global-minus-cell tail
   energy identity from `VasyuninReciprocityAndExactTailGramProducer` yields the unconditional
   inequalities:
   $$\left\|\int_{1/(k+1)}^{1/k} \overline{w(t)}\,dt\right\|^2
     \le \operatorname{witnessMass}\!\left(w, \frac{1}{N+1}\right)
         \left(\int_0^1 \bigl\|\operatorname{singleCellFermiCombinator}(k, N, t)\bigr\|^2\,dt
           - \frac{1}{k(k+1)}\right),$$
   $$\left\|\int_{1/2}^1 \overline{w(t)}\,dt\right\|^2
     \le \operatorname{witnessMass}\!\left(w, \frac{1}{N+2}\right)
         \left(\int_0^1 \bigl\|\operatorname{singleCellFermiCombinator}(1, N + 1, t)\bigr\|^2\,dt
           - \frac{1}{2}\right).$$

4. **Master Synthesis of Tools 1, 2, and 3 (`biscaleUncertainty_three_tools_and_rh_master_synthesis`, §4):**
   Packages all three newly constructed tools and their direct bridges to `RiemannHypothesis`
   into a single unconditional master theorem.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry RHTower
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Witness Orthogonality to Cellular Möbius & Dyadic Resolvent Combinators -/

/-- Every `w : L2FermiWitness` is orthogonal on `(0, 1]` to `fermiNymanGen (d : ℝ)` for `d > 0`. -/
theorem L2FermiWitness.integral_fermiNymanGen_pos_mul_conj_eq_zero
    (w : L2FermiWitness) {d : ℕ} (hd : 0 < d) :
    ∫ t in Ioc (0 : ℝ) 1,
      fermiNymanGen (d : ℝ) t * (starRingEnd ℂ) (w t) = 0 :=
  w.isWitness.orth (d : ℝ) (by exact_mod_cast hd)

/-- **Witness Orthogonality to `dilatedMobiusFermiCombinator`:**
For every `w : L2FermiWitness`, `k > 0`, and `N : ℕ`, `dilatedMobiusFermiCombinator k N` is
orthogonal to `w` on `(0, 1]`. -/
theorem L2FermiWitness.integral_dilatedMobiusFermiCombinator_mul_conj_eq_zero
    (w : L2FermiWitness) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1,
      dilatedMobiusFermiCombinator k N t * (starRingEnd ℂ) (w t) = 0 := by
  have hcomb : (fun t => dilatedMobiusFermiCombinator k N t * (starRingEnd ℂ) (w t)) =
      fun t => ∑ m ∈ Finset.Icc 1 (N / k),
        (-((ArithmeticFunction.moebius m : ℤ) : ℂ)) *
          (fermiNymanGen ((k * m : ℕ) : ℝ) t * (starRingEnd ℂ) (w t)) := by
    funext t
    unfold dilatedMobiusFermiCombinator
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hcomb, integral_finsetSum _ fun m _ =>
    (integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) w.measurable_toFun
      (integrableOn_normSq_fermiNymanGen _) w.integrableOn_normSq).const_mul _]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
  have hkm_pos : 0 < k * m := Nat.mul_pos hk hm_pos
  rw [integral_const_mul,
    w.integral_fermiNymanGen_pos_mul_conj_eq_zero hkm_pos, mul_zero]

/-- **Witness Orthogonality to `dyadicResolventCellThreshold`:**
For every `w : L2FermiWitness`, `k > 0`, and `N : ℕ`, `dyadicResolventCellThreshold k N` is
orthogonal to `w` on `(0, 1]`. -/
theorem L2FermiWitness.integral_dyadicResolventCellThreshold_mul_conj_eq_zero
    (w : L2FermiWitness) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1,
      dyadicResolventCellThreshold k N t * (starRingEnd ℂ) (w t) = 0 := by
  have hcomb : (fun t => dyadicResolventCellThreshold k N t * (starRingEnd ℂ) (w t)) =
      fun t => ∑ j ∈ Finset.range (N + 1),
        ((2 : ℂ) ^ j) *
          (dilatedMobiusFermiCombinator (2 ^ j * k) N t * (starRingEnd ℂ) (w t)) := by
    funext t
    unfold dyadicResolventCellThreshold
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hcomb, integral_finsetSum _ fun j _ =>
    (integrableOn_mul_conj_of_sq (measurable_dilatedMobiusFermiCombinator _ N) w.measurable_toFun
      (integrableOn_normSq_dilatedMobiusFermiCombinator _ N) w.integrableOn_normSq).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h2jk : 0 < 2 ^ j * k := Nat.mul_pos (pow_pos (by decide) j) hk
  rw [integral_const_mul,
    w.integral_dilatedMobiusFermiCombinator_mul_conj_eq_zero h2jk N, mul_zero]

/-- **Witness Orthogonality to `singleCellFermiCombinator`:**
For every `w : L2FermiWitness`, `k > 0`, and `N : ℕ`, `singleCellFermiCombinator k N` is
orthogonal to `w` on `(0, 1]`. -/
theorem L2FermiWitness.integral_singleCellFermiCombinator_mul_conj_eq_zero
    (w : L2FermiWitness) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1,
      singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t) = 0 := by
  have h1 : IntegrableOn
      (fun t => dyadicResolventCellThreshold k N t * (starRingEnd ℂ) (w t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_dyadicResolventCellThreshold k N) w.measurable_toFun
      (integrableOn_normSq_dyadicResolventCellThreshold k N) w.integrableOn_normSq
  have h2 : IntegrableOn
      (fun t => dyadicResolventCellThreshold (k + 1) N t * (starRingEnd ℂ) (w t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_dyadicResolventCellThreshold (k + 1) N) w.measurable_toFun
      (integrableOn_normSq_dyadicResolventCellThreshold (k + 1) N) w.integrableOn_normSq
  have hsplit : (fun t => singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t)) =
      fun t => dyadicResolventCellThreshold k N t * (starRingEnd ℂ) (w t) -
        dyadicResolventCellThreshold (k + 1) N t * (starRingEnd ℂ) (w t) := by
    funext t
    unfold singleCellFermiCombinator
    ring
  have hk1 : 0 < k + 1 := Nat.succ_pos k
  rw [hsplit, integral_sub h1 h2,
    w.integral_dyadicResolventCellThreshold_mul_conj_eq_zero hk N,
    w.integral_dyadicResolventCellThreshold_mul_conj_eq_zero hk1 N, sub_self]

/-! ## §2. Exact Single-Cell & Top-Octave Witness Transfer Laws into the Origin Tail -/

/-- **Bulk Head Evaluation of `singleCellFermiCombinator` Against a Witness:**
For every `w : L2FermiWitness`, `k > 0`, and `N : ℕ`, the bulk-head pairing of
`singleCellFermiCombinator k N` with `w` on `(1 / (N + 1), 1]` equals the single-cell integral
`∫_{1/(k+1)}^{1/k} conj(w(t)) dt` if `k ≤ N`, and `0` otherwise. -/
theorem L2FermiWitness.setIntegral_head_singleCellFermiCombinator_mul_conj_eq
    (w : L2FermiWitness) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
      singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t)) =
    if k ≤ N then
      ∫ t in Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)), (starRingEnd ℂ) (w t)
    else 0 := by
  have hint : IntegrableOn
      (fun t => singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_singleCellFermiCombinator k N) w.measurable_toFun
      (integrableOn_normSq_singleCellFermiCombinator k N) w.integrableOn_normSq
  rw [setIntegral_Ioc_inv_succ_one_eq_sum_cells N hint]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (∫ t in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
        singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t)) =
      if n = k then
        ∫ t in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (starRingEnd ℂ) (w t)
      else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    by_cases hnk : n = k
    · rw [if_pos hnk]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [singleCellFermiCombinator_eq_kronecker_on_cell hk hn1 hnN ht, if_pos hnk, one_mul]
    · rw [if_neg hnk]
      have h0 : EqOn
          (fun t => singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t))
          (fun _ => (0 : ℂ))
          (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
        intro t ht
        dsimp only
        rw [singleCellFermiCombinator_eq_kronecker_on_cell hk hn1 hnN ht, if_neg hnk, zero_mul]
      rw [setIntegral_congr_fun measurableSet_Ioc h0, integral_zero]
  have hk1 : 1 ≤ k := hk
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc, hk1, true_and]

/-- **Exact Single-Cell Witness Transfer Law:**
For every `w : L2FermiWitness`, `k > 0`, and `N ≥ k`, the integral of `conj(w(t))` over the
reciprocal cell `I_k = (1 / (k + 1), 1 / k]` equals the negative small-`t` origin-tail pairing
of `singleCellFermiCombinator k N` with `w` on `(0, 1 / (N + 1)]`. -/
theorem L2FermiWitness.setIntegral_cell_conj_eq_neg_tail_singleCellFermiCombinator
    (w : L2FermiWitness) {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    (∫ t in Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)), (starRingEnd ℂ) (w t)) =
      -∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t) := by
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hint : IntegrableOn
      (fun t => singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_singleCellFermiCombinator k N) w.measurable_toFun
      (integrableOn_normSq_singleCellFermiCombinator k N) w.integrableOn_normSq
  have hsplit :
      (∫ t in Ioc (0 : ℝ) 1,
        singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t)) =
      (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t)) +
      (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
        singleCellFermiCombinator k N t * (starRingEnd ℂ) (w t)) := by
    rw [← Ioc_union_Ioc_eq_Ioc hc0 hc1,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hint.mono_set (Set.Ioc_subset_Ioc le_rfl hc1))
        (hint.mono_set (Set.Ioc_subset_Ioc hc0 le_rfl))]
  rw [w.integral_singleCellFermiCombinator_mul_conj_eq_zero hk N,
    w.setIntegral_head_singleCellFermiCombinator_mul_conj_eq hk N,
    if_pos hkN] at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit.symm

/-- **Unconditional Top-Octave Witness Transfer Law (`k = 1`):**
For every `w : L2FermiWitness` and every cutoff `N : ℕ`, the top-octave integral
`∫_{1/2}^1 conj(w(t)) dt` equals the negative small-`t` origin-tail pairing on
`(0, 1 / (N + 2)]`, with all intermediate cells `I_2, ..., I_{N+1}` identically cancelled! -/
theorem L2FermiWitness.setIntegral_top_octave_conj_eq_neg_tail
    (w : L2FermiWitness) (N : ℕ) :
    (∫ t in Ioc (1 / 2 : ℝ) 1, (starRingEnd ℂ) (w t)) =
      -∫ t in Ioc (0 : ℝ) (1 / (((N + 1 : ℕ) : ℝ) + 1)),
        singleCellFermiCombinator 1 (N + 1) t * (starRingEnd ℂ) (w t) := by
  have h := w.setIntegral_cell_conj_eq_neg_tail_singleCellFermiCombinator
    (k := 1) (N := N + 1) zero_lt_one (Nat.le_add_left 1 N)
  have hcell : Ioc (1 / ((1 : ℝ) + 1)) (1 / (1 : ℝ)) = Ioc (1 / 2 : ℝ) 1 := by
    norm_num
  rw [Nat.cast_one, hcell] at h
  exact h

/-! ## §3. Cauchy–Schwarz Origin-Mass & Global-Minus-Cell Energy Bounds on Witness Cell Integrals -/

/-- **Single-Cell Witness Integral Bound via Origin Mass & Small-`t` Tail Energy:**
For every `w : L2FermiWitness`, `k > 0`, and `N ≥ k`,
$$\left\|\int_{1/(k+1)}^{1/k} \overline{w(t)}\,dt\right\|^2
  \le \operatorname{witnessMass}\!\left(w, \frac{1}{N+1}\right)
      \int_0^{1/(N+1)} \bigl\|\operatorname{singleCellFermiCombinator}(k, N, t)\bigr\|^2\,dt.$$ -/
theorem L2FermiWitness.norm_sq_setIntegral_cell_le_witnessMass_mul_tail
    (w : L2FermiWitness) {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    ‖∫ t in Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)), (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      witnessMass w (1 / ((N : ℝ) + 1)) *
        ∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
          ‖singleCellFermiCombinator k N t‖ ^ 2 := by
  rw [w.setIntegral_cell_conj_eq_neg_tail_singleCellFermiCombinator hk hkN, norm_neg]
  set S : Set ℝ := Ioc (0 : ℝ) (1 / ((N : ℝ) + 1))
  set g : ℝ → ℂ := singleCellFermiCombinator k N
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hg_meas : Measurable g := measurable_singleCellFermiCombinator k N
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) S :=
    (integrableOn_normSq_singleCellFermiCombinator k N).mono_set (Set.Ioc_subset_Ioc le_rfl hc1)
  have hw2 : IntegrableOn (fun t => ‖w t‖ ^ 2) S :=
    w.integrableOn_normSq.mono_set (Set.Ioc_subset_Ioc le_rfl hc1)
  have h1 : ‖∫ t in S, g t * (starRingEnd ℂ) (w t)‖ ≤ ∫ t in S, ‖g t‖ * ‖w t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_mul, Complex.norm_conj]
  have h2 := sq_integral_mul_le (μ := volume.restrict S) (f := fun t => ‖g t‖)
    (g := fun t => ‖w t‖) hg_meas.aestronglyMeasurable.norm
    w.measurable_toFun.aestronglyMeasurable.norm hg2 hw2
  calc
    ‖∫ t in S, g t * (starRingEnd ℂ) (w t)‖ ^ 2
      ≤ (∫ t in S, ‖g t‖ * ‖w t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∫ t in S, ‖g t‖ ^ 2) * ∫ t in S, ‖w t‖ ^ 2 := h2
    _ = witnessMass w (1 / ((N : ℝ) + 1)) * ∫ t in S, ‖g t‖ ^ 2 := by
        unfold witnessMass S
        ring

/-- **Unconditional Top-Octave Witness Integral Bound via Global-Minus-Half Energy:**
For every `w : L2FermiWitness` and `N : ℕ`,
$$\left\|\int_{1/2}^1 \overline{w(t)}\,dt\right\|^2
  \le \operatorname{witnessMass}\!\left(w, \frac{1}{N+2}\right)
      \left(\int_0^1 \bigl\|\operatorname{singleCellFermiCombinator}(1, N + 1, t)\bigr\|^2\,dt - \frac{1}{2}\right).$$ -/
theorem L2FermiWitness.norm_sq_setIntegral_top_octave_le_witnessMass_mul_global_sub_half
    (w : L2FermiWitness) (N : ℕ) :
    ‖∫ t in Ioc (1 / 2 : ℝ) 1, (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      witnessMass w (1 / (((N + 1 : ℕ) : ℝ) + 1)) *
        ((∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator 1 (N + 1) t‖ ^ 2) - 1 / 2) := by
  have h := w.norm_sq_setIntegral_cell_le_witnessMass_mul_tail
    (k := 1) (N := N + 1) zero_lt_one (Nat.le_add_left 1 N)
  have hcell : Ioc (1 / ((1 : ℝ) + 1)) (1 / (1 : ℝ)) = Ioc (1 / 2 : ℝ) 1 := by
    norm_num
  rw [Nat.cast_one, hcell,
    integral_normSq_topOctaveSingleCell_tail_eq_global_sub_half N] at h
  exact h

/-- For every `w : L2FermiWitness` and `N : ℕ`, the origin mass at `1 / (N + 2)` is bounded above
by the lower-half witness energy `witnessMass w (1 / 2) = ∫_0^{1/2} ‖w t‖^2 dt`. -/
theorem L2FermiWitness.witnessMass_inv_succ_succ_le_lower_half
    (w : L2FermiWitness) (N : ℕ) :
    witnessMass w (1 / (((N + 1 : ℕ) : ℝ) + 1)) ≤
      ∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2 := by
  unfold witnessMass
  have hle : 1 / (((N + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    push_cast
    linarith
  exact setIntegral_mono_set
    (w.integrableOn_normSq.mono_set (Set.Ioc_subset_Ioc le_rfl (by norm_num)))
    (Eventually.of_forall fun t => sq_nonneg _)
    (Eventually.of_forall fun t ht => Set.Ioc_subset_Ioc_right hle ht)

/-- **Unconditional Top-Octave-to-Lower-Half Energy Transfer Inequality:**
For every `w : L2FermiWitness` and `N : ℕ`, the squared modulus of the top-octave integral
`∫_{1/2}^1 conj(w(t)) dt` is bounded above by the lower-half witness energy `∫_0^{1/2} ‖w t‖^2 dt`
times the global-minus-half energy of `singleCellFermiCombinator 1 (N + 1)`. -/
theorem L2FermiWitness.norm_sq_setIntegral_top_octave_le_lower_half_mul_global_sub_half
    (w : L2FermiWitness) (N : ℕ) :
    ‖∫ t in Ioc (1 / 2 : ℝ) 1, (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) *
        ((∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator 1 (N + 1) t‖ ^ 2) - 1 / 2) := by
  have h1 := w.norm_sq_setIntegral_top_octave_le_witnessMass_mul_global_sub_half N
  have h2 := w.witnessMass_inv_succ_succ_le_lower_half N
  have htail_nonneg :
      0 ≤ (∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator 1 (N + 1) t‖ ^ 2) - 1 / 2 := by
    rw [← integral_normSq_topOctaveSingleCell_tail_eq_global_sub_half N]
    exact setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right h2 htail_nonneg)

/-! ## §4. Master Synthesis of All Three New Tools & Route PM / PW-B / FZZ-P Bridges -/

/-- **Master Synthesis of Tools 1, 2, and 3 in `BiScaleUncertainty`:**
Unifies the three newly formalized structural tools and their direct bridges to `RiemannHypothesis`:
1. **Tool 1 (Exact Global-Minus-Head Tail Gram & Single-Cell Tail Energy):**
   `fermiTailGram N d₁ d₂` equals `fermiGlobalGram d₁ d₂` minus the exact finite cellular head
   sum over `1 ≤ n ≤ N` (`fermiTailGram_eq_global_sub_sum_cellMatrix`), with zero truncation
   remainder.
2. **Tool 2 (Sawtooth Period Second Moment, Complementary Cancellation & Cofinal RH Bridge):**
   - For every `d > 0`, `∑_{r=0}^{d-1} centeredDiscreteSawtooth d r ^ 2 = (d² - 1) / (12 d)`.
   - Cofinal critical-strip boundedness of the reciprocal-weighted second moment of
     `pmPowerDampedRamanujanCenteredSawtoothPrefix` implies `RiemannHypothesis`.
3. **Tool 3 (Single-Cell Witness Transfer & Top-Octave-to-Lower-Half Energy Inequality):**
   - For every `w : L2FermiWitness` and `N : ℕ`,
     `∫_{1/2}^1 conj(w t) dt = -∫_0^{1/(N+2)} singleCellFermiCombinator 1 (N + 1) t * conj(w t) dt`
     and `‖∫_{1/2}^1 conj(w t) dt‖² ≤ (∫_0^{1/2} ‖w t‖² dt) * (∫_0^1 ‖singleCellFermiCombinator 1 (N + 1) t‖² dt - 1/2)`.
   - `RiemannHypothesis` is equivalent to top-octave energy domination
     `∫_{1/2}^1 ‖w t‖² dt ≤ ∫_0^{1/2} ‖w t‖² dt` for all `IsFermiNymanWitness w`. -/
theorem biscaleUncertainty_three_tools_and_rh_master_synthesis :
    (∀ N d₁ d₂ : ℕ,
      fermiTailGram N d₁ d₂ =
        fermiGlobalGram d₁ d₂ -
          ((∑ n ∈ Finset.Icc 1 N,
            (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
              ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ)) ∧
    (∀ {d : ℕ}, 0 < d →
      (∑ r ∈ Finset.range d, centeredDiscreteSawtooth d r ^ 2) =
        ((d : ℝ) ^ 2 - 1) / (12 * (d : ℝ))) ∧
    ((∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ B : ℝ, ∀ Q : ℕ,
      (∑' N : ℕ, (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1))) ≤ B) → RiemannHypothesis) ∧
    (∀ (w : L2FermiWitness) (N : ℕ),
      (∫ t in Ioc (1 / 2 : ℝ) 1, (starRingEnd ℂ) (w t)) =
        -∫ t in Ioc (0 : ℝ) (1 / (((N + 1 : ℕ) : ℝ) + 1)),
          singleCellFermiCombinator 1 (N + 1) t * (starRingEnd ℂ) (w t) ∧
      ‖∫ t in Ioc (1 / 2 : ℝ) 1, (starRingEnd ℂ) (w t)‖ ^ 2 ≤
        (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) *
          ((∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator 1 (N + 1) t‖ ^ 2) - 1 / 2)) ∧
    (RiemannHypothesis ↔
      ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
        (∫ t in Ioc (1 / 2 : ℝ) 1, ‖w t‖ ^ 2) ≤ (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2)) :=
  ⟨fermiTailGram_eq_global_sub_sum_cellMatrix,
    fun hd => sum_sq_centeredDiscreteSawtooth_range hd,
    riemannHypothesis_of_cofinal_centeredSawtooth_budget,
    fun w N => ⟨w.setIntegral_top_octave_conj_eq_neg_tail N,
      w.norm_sq_setIntegral_top_octave_le_lower_half_mul_global_sub_half N⟩,
    riemannHypothesis_iff_witness_top_octave_energy_le_lower_half⟩

end GaloisForLFunctions.BiScaleUncertainty

end
