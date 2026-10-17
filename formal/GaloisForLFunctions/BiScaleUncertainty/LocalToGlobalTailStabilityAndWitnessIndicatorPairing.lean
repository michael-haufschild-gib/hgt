import GaloisForLFunctions.BiScaleUncertainty.WitnessGermOriginMassAndJointTailHeadSynthesis

/-!
# Pillar XXXIV: Quantitative Local-to-Global Tail Stability & Step-Brick Witness Pairing

This module develops **Component 3** of the FZZ-P / `BiScaleUncertainty` synthesis, bridging the
local bulk completeness of `FermiNymanWitnessGermRigidity` on $(\delta, 1]$ with quantitative
$L^2(0, \delta]$ origin-tail amplification bounds and non-multiplicative step-brick representations
of the Fermi–Nyman generators:

1. **Explicit Step-Brick Representation of $\varphi_{a+1}$ on the Bulk $(1/(2(a+1)), \infty)$:**
   Because the linear terms $\frac{1}{(a+1)t} - 2\frac{1}{2(a+1)t} = 0$ cancel identically in
   $\varphi_{a+1}(t) = \{1/((a+1)t)\} - 2\{1/(2(a+1)t)\} = 2\lfloor 1/(2(a+1)t)\rfloor - \lfloor 1/((a+1)t)\rfloor$,
   every Fermi generator is a pure step function. On the bulk region $t > \frac{1}{2(a+1)}$,
   - $\varphi_{a+1}(t) = 0$ for all $t > \frac{1}{a+1}$ (`fermiNymanGen_nat_eq_zero_of_gt_inv`),
   - $\varphi_{a+1}(t) = -1$ on the top dyadic octave $\bigl(\frac{1}{2(a+1)}, \frac{1}{a+1}\bigr]$
     (`fermiNymanGen_nat_eq_neg_one_on_top_octave`), and
   - consequently, on the entire half-line $\bigl(\frac{1}{2(a+1)}, \infty\bigr)$, $\varphi_{a+1}(t)$
     coincides identically with the negative step-brick indicator
     $-\mathbf{1}_{(1/(2(a+1)),\, 1/(a+1)]}(t)$ (`fermiNymanGen_nat_eq_neg_indicator_on_bulk`).

2. **Quantitative $L^2$ Origin-Tail Amplification Bounds on $(0, 1/(N+1)]$:**
   Using the global pointwise bound $\|\varphi_{a+1}(t)\| \le 3$, any finite generator combination
   $\Phi_{c,a}(t) = \sum_{j} c_j \varphi_{a_j+1}(t)$ satisfies $\|\Phi_{c,a}(t)\| \le 3 \sum_j \|c_j\|$,
   yielding the unconditional linear-in-cutoff origin-tail bounds:
   $$\int_0^{1/(N+1)} \|\Phi_{c,a}(t)\|^2\,dt \le \frac{9}{N + 1}\Bigl(\sum_j \|c_j\|\Bigr)^2,$$
   $$\int_0^{1/(N+1)} \|h(t) - \Phi_{c,a}(t)\|^2\,dt \le \frac{2}{N + 1}\left(1 + 9\Bigl(\sum_j \|c_j\|\Bigr)^2\right).$$

3. **Quantitative Local-to-Global Witness Pairing Bound:**
   Pairing any bundled $L^2$ witness $w \in W$ (`L2FermiWitness`) against $h - \Phi_{c,a}$ splits
   across $t = 1/(N+1)$ and bounds $\bigl\|\int_0^1 h(t)\overline{w(t)}\,dt\bigr\|^2$ by the bulk
   head approximation error on $(1/(N+1), 1]$ plus the origin-damped $\ell^1$ tail penalty
   $$\frac{4}{N + 1}\,\operatorname{witnessMass}\!\left(w, \frac{1}{N+1}\right)
     \left(1 + 9\Bigl(\sum_j \|c_j\|\Bigr)^2\right).$$
-/

open Complex MeasureTheory Set Filter Topology Finset
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry
open RHTower

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Explicit Step-Brick Representation of `fermiNymanGen` on the Bulk `(1/(2a), 1]` -/

/-- Above `1 / (a + 1)`, the Fermi generator `φ_{a+1}(t)` vanishes identically because both
`1 / ((a + 1) t)` and `1 / (2 (a + 1) t)` lie in `(0, 1)`. -/
theorem fermiNymanGen_nat_eq_zero_of_gt_inv (a : ℕ) (t : ℝ) :
    (Ioi (1 / ((a + 1 : ℕ) : ℝ))).indicator (fermiNymanGen ((a + 1 : ℕ) : ℝ)) t = 0 := by
  by_cases ht : t ∈ Ioi (1 / ((a + 1 : ℕ) : ℝ))
  · rw [indicator_of_mem ht]
    have ha : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
    have ht_gt : 1 / ((a + 1 : ℕ) : ℝ) < t := ht
    have ht0 : 0 < t := lt_trans (one_div_pos.mpr ha) ht_gt
    have h1 : 1 / (((a + 1 : ℕ) : ℝ) * t) < 1 := by
      rw [div_lt_one (mul_pos ha ht0)]
      have := (div_lt_iff₀ ha).mp ht_gt
      linarith
    have h2 : 1 / (2 * ((a + 1 : ℕ) : ℝ) * t) < 1 := by
      rw [div_lt_one (by positivity)]
      have := (div_lt_iff₀ ha).mp ht_gt
      linarith
    have h_alg : (1 : ℝ) / (((a + 1 : ℕ) : ℝ) * t) =
        2 * (1 / (2 * ((a + 1 : ℕ) : ℝ) * t)) := by
      rw [mul_assoc, ← one_div_mul_one_div]
      ring
    unfold fermiNymanGen nymanGen
    rw [Int.fract_eq_self.mpr ⟨by positivity, h1⟩,
      Int.fract_eq_self.mpr ⟨by positivity, h2⟩, h_alg,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  · exact indicator_of_notMem ht _

/-- On the top dyadic octave `(1 / (2(a + 1)), 1 / (a + 1)]` of scale `a + 1`, the Fermi generator
`φ_{a+1}(t)` is identically `-1`, because `1 ≤ 1 / ((a+1)t) < 2` while `1 / (2(a+1)t) < 1`. -/
theorem fermiNymanGen_nat_eq_neg_one_on_top_octave (a : ℕ) (t : ℝ) :
    (Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ))).indicator
      (fermiNymanGen ((a + 1 : ℕ) : ℝ)) t =
    (Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ))).indicator
      (fun _ => (-1 : ℂ)) t := by
  by_cases ht : t ∈ Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ))
  · rw [indicator_of_mem ht, indicator_of_mem ht]
    have ha : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
    have ht0 : 0 < t := lt_trans (by positivity) ht.1
    have h1_ge : 1 ≤ 1 / (((a + 1 : ℕ) : ℝ) * t) := by
      rw [le_div_iff₀ (mul_pos ha ht0)]
      have := (le_div_iff₀ ha).mp ht.2
      linarith
    have h1_lt : 1 / (((a + 1 : ℕ) : ℝ) * t) < 2 := by
      rw [div_lt_iff₀ (mul_pos ha ht0)]
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ((a + 1 : ℕ) : ℝ))).mp ht.1
      linarith
    have h2_lt : 1 / (2 * ((a + 1 : ℕ) : ℝ) * t) < 1 := by
      rw [div_lt_one (by positivity)]
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ((a + 1 : ℕ) : ℝ))).mp ht.1
      linarith
    have hfl1 : ⌊1 / (((a + 1 : ℕ) : ℝ) * t)⌋ = 1 := by
      rw [Int.floor_eq_iff, Int.cast_one]
      exact ⟨h1_ge, by linarith⟩
    have h_alg : (1 : ℝ) / (((a + 1 : ℕ) : ℝ) * t) =
        2 * (1 / (2 * ((a + 1 : ℕ) : ℝ) * t)) := by
      rw [mul_assoc, ← one_div_mul_one_div]
      ring
    unfold fermiNymanGen nymanGen
    rw [Int.fract, hfl1, Int.fract_eq_self.mpr ⟨by positivity, h2_lt⟩, h_alg,
      Int.cast_one, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]

/-- **Unconditional Bulk Step-Brick Identity (`fermiNymanGen_nat_eq_neg_indicator_on_bulk`):**
For every `a : ℕ` and `t : ℝ`, on the bulk interval `(1 / (2(a + 1)), ∞)`, the Fermi generator
`φ_{a+1}(t)` is identically `-1_{(1/(2(a+1)), 1/(a+1)]}(t)`! -/
theorem fermiNymanGen_nat_eq_neg_indicator_on_bulk (a : ℕ) (t : ℝ) :
    (Ioi (1 / (2 * ((a + 1 : ℕ) : ℝ)))).indicator (fermiNymanGen ((a + 1 : ℕ) : ℝ)) t =
      -(Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ))).indicator
        (fun _ => (1 : ℂ)) t := by
  by_cases ht : t ∈ Ioi (1 / (2 * ((a + 1 : ℕ) : ℝ)))
  · rw [indicator_of_mem ht]
    by_cases hle : t ≤ 1 / ((a + 1 : ℕ) : ℝ)
    · have hmem : t ∈ Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ)) := ⟨ht, hle⟩
      have h := fermiNymanGen_nat_eq_neg_one_on_top_octave a t
      rw [indicator_of_mem hmem, indicator_of_mem hmem] at h
      rw [h, indicator_of_mem hmem]
    · have hgt : t ∈ Ioi (1 / ((a + 1 : ℕ) : ℝ)) := lt_of_not_ge hle
      have hnot : t ∉ Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ)) :=
        fun h => hle h.2
      have h := fermiNymanGen_nat_eq_zero_of_gt_inv a t
      rw [indicator_of_mem hgt] at h
      rw [h, indicator_of_notMem hnot, neg_zero]
  · have hnot : t ∉ Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ)) :=
      fun h => ht h.1
    rw [indicator_of_notMem ht, indicator_of_notMem hnot, neg_zero]

/-! ## §2. Quantitative `L²` Origin-Tail Amplification Bound for Finite Generator Combinations -/

/-- Pointwise `ℓ¹` norm bound on `natScaleFermiComb c a t`: since `‖φ_{a+1}(t)‖ ≤ 3` everywhere,
`‖Φ_{c,a}(t)‖ ≤ 3 * ∑ j, ‖c j‖` for all `t : ℝ`. -/
theorem norm_natScaleFermiComb_le_three_mul_sum {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) (t : ℝ) :
    ‖natScaleFermiComb c a t‖ ≤ 3 * ∑ j : Fin m, ‖c j‖ := by
  unfold natScaleFermiComb fermiNymanCombination
  calc
    ‖∑ j : Fin m, c j * fermiNymanGen ((a j + 1 : ℕ) : ℝ) t‖
      ≤ ∑ j : Fin m, ‖c j * fermiNymanGen ((a j + 1 : ℕ) : ℝ) t‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin m, ‖c j‖ * 3 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le _ t) (norm_nonneg _)
    _ = 3 * ∑ j : Fin m, ‖c j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring

/-- **Unconditional Quantitative Origin-Tail Energy Bound (`integral_normSq_natScaleFermiComb_tail_le`):**
For every cutoff `N : ℕ` and finite generator combination `natScaleFermiComb c a`, the small-`t`
tail energy on `(0, 1 / (N + 1)]` is bounded unconditionally from above by
`9 / (N + 1) * (∑ j, ‖c j‖)²`. -/
theorem integral_normSq_natScaleFermiComb_tail_le (N : ℕ) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)), ‖natScaleFermiComb c a t‖ ^ 2) ≤
      (9 / ((N : ℝ) + 1)) * (∑ j : Fin m, ‖c j‖) ^ 2 := by
  set S := Ioc (0 : ℝ) (1 / ((N : ℝ) + 1))
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hint : IntegrableOn (fun t => ‖natScaleFermiComb c a t‖ ^ 2) S :=
    (integrableOn_normSq_natScaleFermiComb c a).mono_set (Ioc_subset_Ioc le_rfl hc1)
  have hconst : IntegrableOn (fun _ : ℝ => (3 * ∑ j : Fin m, ‖c j‖) ^ 2) S :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hle := setIntegral_mono_on hint hconst measurableSet_Ioc fun t _ => by
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_natScaleFermiComb_le_three_mul_sum c a t) 2
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), sub_zero, smul_eq_mul] at hle
  calc
    (∫ t in S, ‖natScaleFermiComb c a t‖ ^ 2)
      ≤ 1 / ((N : ℝ) + 1) * (3 * ∑ j : Fin m, ‖c j‖) ^ 2 := hle
    _ = (9 / ((N : ℝ) + 1)) * (∑ j : Fin m, ‖c j‖) ^ 2 := by ring

/-- **Unconditional Quantitative Haar Origin-Tail Energy Bound (`integral_normSq_dyadicHaar_sub_natScaleFermiComb_tail_le`):**
For every cutoff `N : ℕ` and finite generator combination `natScaleFermiComb c a`, the small-`t`
Haar tail energy on `(0, 1 / (N + 1)]` is bounded unconditionally from above by
`2 / (N + 1) * (1 + 9 * (∑ j, ‖c j‖)²)`. -/
theorem integral_normSq_dyadicHaar_sub_natScaleFermiComb_tail_le
    (N : ℕ) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
      ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2) ≤
      (2 / ((N : ℝ) + 1)) * (1 + 9 * (∑ j : Fin m, ‖c j‖) ^ 2) := by
  set S := Ioc (0 : ℝ) (1 / ((N : ℝ) + 1))
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hdiff : IntegrableOn (fun t => ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2) S :=
    (integrableOn_normSq_sub measurable_dyadicHaar (measurable_natScaleFermiComb c a)
      integrableOn_normSq_dyadicHaar (integrableOn_normSq_natScaleFermiComb c a)).mono_set
      (Ioc_subset_Ioc le_rfl hc1)
  have hconst : IntegrableOn (fun _ : ℝ => 2 + 2 * (3 * ∑ j : Fin m, ‖c j‖) ^ 2) S :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hle := setIntegral_mono_on hdiff hconst measurableSet_Ioc fun t _ => by
    have h1 : ‖dyadicHaar t - natScaleFermiComb c a t‖ ≤
        ‖dyadicHaar t‖ + ‖natScaleFermiComb c a t‖ := norm_sub_le _ _
    have h2 : ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2 ≤
        2 * ‖dyadicHaar t‖ ^ 2 + 2 * ‖natScaleFermiComb c a t‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖dyadicHaar t‖ - ‖natScaleFermiComb c a t‖)]
    rw [norm_dyadicHaar] at h2
    have h3 : ‖natScaleFermiComb c a t‖ ^ 2 ≤ (3 * ∑ j : Fin m, ‖c j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_natScaleFermiComb_le_three_mul_sum c a t) 2
    linarith
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), sub_zero, smul_eq_mul] at hle
  calc
    (∫ t in S, ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2)
      ≤ 1 / ((N : ℝ) + 1) * (2 + 2 * (3 * ∑ j : Fin m, ‖c j‖) ^ 2) := hle
    _ = (2 / ((N : ℝ) + 1)) * (1 + 9 * (∑ j : Fin m, ‖c j‖) ^ 2) := by ring

/-- **Unconditional Quantitative Local-to-Global Witness Pairing Bound
(`L2FermiWitness.norm_sq_dyadicHaar_pairing_le_l1_tail_add_bulk_head`):**
Combining `norm_sq_dyadicHaar_pairing_le_tail_add_head` with
`integral_normSq_dyadicHaar_sub_natScaleFermiComb_tail_le` bounds the global witness pairing
`‖∫_0^1 h(t) conj(w(t)) dt‖²` purely in terms of the bulk head error on `(1/(N+1), 1]` and the
quadratic origin-damped `ℓ¹` coefficient factor `witnessMass w (1/(N+1)) / (N+1) * (1 + 9 (∑ ‖c_j‖)²)`. -/
theorem L2FermiWitness.norm_sq_dyadicHaar_pairing_le_l1_tail_add_bulk_head
    (w : L2FermiWitness) (N : ℕ) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    ‖∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      (4 / ((N : ℝ) + 1)) * witnessMass w (1 / ((N : ℝ) + 1)) *
        (1 + 9 * (∑ j : Fin m, ‖c j‖) ^ 2) +
      2 * ((∫ t in Ioc (1 / ((N : ℝ) + 1)) 1, ‖w t‖ ^ 2) *
        ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
          ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2) := by
  have h1 := w.norm_sq_dyadicHaar_pairing_le_tail_add_head N c a
  have h2 := integral_normSq_dyadicHaar_sub_natScaleFermiComb_tail_le N c a
  have hwm : 0 ≤ witnessMass w (1 / ((N : ℝ) + 1)) :=
    witnessMass_nonneg w (1 / ((N : ℝ) + 1))
  have hmul := mul_le_mul_of_nonneg_left h2 hwm
  have hring :
      2 * (witnessMass w (1 / ((N : ℝ) + 1)) *
        ((2 / ((N : ℝ) + 1)) * (1 + 9 * (∑ j : Fin m, ‖c j‖) ^ 2))) =
      (4 / ((N : ℝ) + 1)) * witnessMass w (1 / ((N : ℝ) + 1)) *
        (1 + 9 * (∑ j : Fin m, ‖c j‖) ^ 2) := by ring
  linarith

end GaloisForLFunctions.BiScaleUncertainty
