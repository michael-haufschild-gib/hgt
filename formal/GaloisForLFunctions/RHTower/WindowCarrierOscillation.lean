import GaloisForLFunctions.RHTower.ChiCarrierJets
import GaloisForLFunctions.HTGeometry.FourierIteratedDerivDecay

/-!
# Height oscillation of the windowed dual carrier

For the compactly supported smooth block window `w = blockWindow p q η` and the dual carrier
`G(t;v) = χ(s₁+w)χ(s₂+w)` on the Levinson lines, the windowed carrier `h_v = w·G(·;v)` is smooth
with support in `[p − η, q + η]`.  When `p − η ≥ 4` and `2|v| ≤ p − η`, the jet laws of the window
(`‖w^{(j)}‖ ≤ C_j/η^j`) and of the carrier (`‖G^{(i)}‖ ≤ i!‖G‖(33(1+|v|)/t)^i`) give

`‖h_v^{(K)}(t)‖ ≤ windowCarrierJetConst K η (p−η) v · ‖G(t;v)‖`,

and `K`-fold integration by parts against `e^{-iξt}` yields the height-oscillation bound

`‖∫ w(t) G(t;v) e^{-iξt} dt‖ ≤ (q − p + 2η) · windowCarrierJetConst K η (p−η) v · e⁸(1+q+η+|v|)⁴ / |ξ|^K`.

This is the frequency-by-frequency input for the dual off-diagonal of the block twisted moment:
one power of `1/|ξ|` per derivative, at the price of one factor `1/η + 33(1+|v|)/(p−η)` each.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The windowed dual carrier `h_v(t) = w(t)·G(t;v)`. -/
def windowCarrier (d v p q η : ℝ) (t : ℝ) : ℂ :=
  blockWindowC p q η t * chiCarrier d v t

theorem contDiff_windowCarrier {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v p q η : ℝ) (n : ℕ) :
    ContDiff ℝ n (windowCarrier d v p q η) :=
  ((contDiff_blockWindowC p q η).of_le (WithTop.coe_le_coe.mpr le_top)).mul
    (contDiff_chiCarrier hd hdq v n)

theorem tsupport_windowCarrier_subset {d v p q η : ℝ} (hη : 0 < η) :
    tsupport (windowCarrier d v p q η) ⊆ Set.Icc (p - η) (q + η) :=
  (tsupport_mul_subset_left (f := blockWindowC p q η) (g := chiCarrier d v)).trans
    (tsupport_blockWindowC_subset hη)

theorem hasCompactSupport_windowCarrier {d v p q η : ℝ} (hη : 0 < η) :
    HasCompactSupport (windowCarrier d v p q η) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (subset_tsupport _ |>.trans (tsupport_windowCarrier_subset hη))

theorem iteratedDeriv_windowCarrier_eq_zero (n : ℕ) {d v p q η : ℝ} (hη : 0 < η) {t : ℝ}
    (ht : t ∉ Set.Icc (p - η) (q + η)) : iteratedDeriv n (windowCarrier d v p q η) t = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hnot : t ∉ Function.support (iteratedFDeriv ℝ n (windowCarrier d v p q η)) := fun h =>
    ht (tsupport_windowCarrier_subset hη (support_iteratedFDeriv_subset n h))
  simp [Function.notMem_support.mp hnot]

/-- The jet constant of the windowed carrier: the Leibniz sum of the window and carrier
constants at scale `η` and base height `L`. -/
def windowCarrierJetConst (K : ℕ) (η L v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), (K.choose j : ℝ) * (blockWindowConst j / η ^ j)
    * ((K - j).factorial * (33 * (1 + |v|) / L) ^ (K - j))

theorem windowCarrierJetConst_nonneg (K : ℕ) {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (v : ℝ) :
    0 ≤ windowCarrierJetConst K η L v :=
  Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by positivity)
    (div_nonneg (blockWindowConst_nonneg j) (by positivity))) (by positivity)

/-- **Jets of the windowed carrier on the support.** -/
theorem norm_iteratedDeriv_windowCarrier_le (K : ℕ) {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4)
    {v p q η : ℝ} (hη : 0 < η) (hL : 4 ≤ p - η) (hv : 2 * |v| ≤ p - η) {t : ℝ}
    (ht : p - η ≤ t) :
    ‖iteratedDeriv K (windowCarrier d v p q η) t‖
      ≤ windowCarrierJetConst K η (p - η) v * ‖chiCarrier d v t‖ := by
  have hL0 : (0 : ℝ) < p - η := by linarith
  have ht4 : (4 : ℝ) ≤ t := by linarith
  have hvt : 2 * |v| ≤ t := by linarith
  have hleib := norm_iteratedFDeriv_mul_le
    ((contDiff_blockWindowC p q η).of_le (WithTop.coe_le_coe.mpr le_top) :
      ContDiff ℝ ((K : ℕ∞) : WithTop ℕ∞) (blockWindowC p q η))
    (contDiff_chiCarrier hd hdq v K) t (le_refl ((K : ℕ∞) : WithTop ℕ∞))
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
  refine hleib.trans ?_
  rw [windowCarrierJetConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have h1 := norm_iteratedDeriv_blockWindowC_le j p q hη t
  have h2 := norm_iteratedDeriv_chiCarrier_le hd hdq ht4 hvt (K - j)
  have hbase : 33 * (1 + |v|) / t ≤ 33 * (1 + |v|) / (p - η) :=
    div_le_div_of_nonneg_left (by positivity) hL0 ht
  have h2' : ‖iteratedDeriv (K - j) (chiCarrier d v) t‖
      ≤ (K - j).factorial * ‖chiCarrier d v t‖ * (33 * (1 + |v|) / (p - η)) ^ (K - j) :=
    h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _)
      (by positivity))
  calc (K.choose j : ℝ) * ‖iteratedDeriv j (blockWindowC p q η) t‖
        * ‖iteratedDeriv (K - j) (chiCarrier d v) t‖
      ≤ (K.choose j : ℝ) * (blockWindowConst j / η ^ j)
          * ((K - j).factorial * ‖chiCarrier d v t‖ * (33 * (1 + |v|) / (p - η)) ^ (K - j)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2' (norm_nonneg _)
          (mul_nonneg (by positivity) (div_nonneg (blockWindowConst_nonneg j) (by positivity)))
    _ = (K.choose j : ℝ) * (blockWindowConst j / η ^ j)
          * ((K - j).factorial * (33 * (1 + |v|) / (p - η)) ^ (K - j)) * ‖chiCarrier d v t‖ := by
        ring

/-- The polynomial envelope of the carrier on the window support. -/
theorem norm_chiCarrier_le_of_mem {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {v p q η : ℝ}
    (hL : 4 ≤ p - η) (hv : 2 * |v| ≤ p - η) {t : ℝ} (ht : t ∈ Set.Icc (p - η) (q + η)) :
    ‖chiCarrier d v t‖ ≤ Real.exp 8 * (1 + (q + η) + |v|) ^ (4 : ℕ) := by
  have ht4 : (4 : ℝ) ≤ t := by linarith [ht.1]
  have hvt : 2 * |v| ≤ t := by linarith [ht.1]
  refine (norm_chiCarrier_le hd hdq ht4 hvt).trans ?_
  have hpos : (0 : ℝ) ≤ 1 + (q + η) + |v| := by
    have := abs_nonneg v
    linarith [ht.2]
  have hb1 : 1 + |t - v| ≤ 1 + (q + η) + |v| := by
    have := abs_sub t v
    have := abs_of_pos (by linarith : (0 : ℝ) < t)
    linarith [ht.2]
  have hb2 : 1 + |t + v| ≤ 1 + (q + η) + |v| := by
    have := abs_add_le t v
    have := abs_of_pos (by linarith : (0 : ℝ) < t)
    linarith [ht.2]
  have h1 : (1 + |t - v|) ^ (2 : ℕ) ≤ (1 + (q + η) + |v|) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hb1 2
  have h2 : (1 + |t + v|) ^ (2 : ℕ) ≤ (1 + (q + η) + |v|) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hb2 2
  calc Real.exp 8 * ((1 + |t - v|) ^ (2 : ℕ) * (1 + |t + v|) ^ (2 : ℕ))
      ≤ Real.exp 8 * ((1 + (q + η) + |v|) ^ (2 : ℕ) * (1 + (q + η) + |v|) ^ (2 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp 8 * (1 + (q + η) + |v|) ^ (4 : ℕ) := by ring

theorem integrable_iteratedDeriv_windowCarrier {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4)
    {v p q η : ℝ} (hη : 0 < η) (n : ℕ) :
    Integrable (iteratedDeriv n (windowCarrier d v p q η)) :=
  integrable_iteratedDeriv_of_hasCompactSupport (contDiff_windowCarrier hd hdq v p q η n)
    (hasCompactSupport_windowCarrier hη) le_rfl

/-- The `L¹` norm of the `K`-th derivative of the windowed carrier. -/
theorem integral_norm_iteratedDeriv_windowCarrier_le (K : ℕ) {d : ℝ} (hd : 0 < d)
    (hdq : d ≤ 1 / 4) {v p q η : ℝ} (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q)
    (hv : 2 * |v| ≤ p - η) :
    ∫ t, ‖iteratedDeriv K (windowCarrier d v p q η) t‖
      ≤ (q - p + 2 * η) * (windowCarrierJetConst K η (p - η) v
          * (Real.exp 8 * (1 + (q + η) + |v|) ^ (4 : ℕ))) := by
  have h := integral_norm_le_of_forall_mem_Icc (g := iteratedDeriv K (windowCarrier d v p q η))
    (a := p - η) (b := q + η)
    (M := windowCarrierJetConst K η (p - η) v * (Real.exp 8 * (1 + (q + η) + |v|) ^ (4 : ℕ)))
    (by linarith) (integrable_iteratedDeriv_windowCarrier hd hdq hη K)
    (fun t ht => iteratedDeriv_windowCarrier_eq_zero K hη ht)
    (fun t ht => by
      refine (norm_iteratedDeriv_windowCarrier_le K hd hdq hη hL hv ht.1).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_chiCarrier_le_of_mem hd hdq hL hv ht)
        (windowCarrierJetConst_nonneg K hη (by linarith) v))
  refine h.trans (le_of_eq ?_)
  ring

/-- **Height-oscillation bound for the windowed dual carrier.** -/
theorem norm_integral_windowCarrier_mul_cexp_le (K : ℕ) {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4)
    {v p q η : ℝ} (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) (hv : 2 * |v| ≤ p - η) {ξ : ℝ}
    (hξ : ξ ≠ 0) :
    ‖∫ t, windowCarrier d v p q η t * Complex.exp (-(ξ * t) * I)‖
      ≤ (q - p + 2 * η) * (windowCarrierJetConst K η (p - η) v
          * (Real.exp 8 * (1 + (q + η) + |v|) ^ (4 : ℕ))) / |ξ| ^ K := by
  refine (norm_integral_mul_cexp_le_of_iteratedDeriv K (contDiff_windowCarrier hd hdq v p q η K)
    (fun n _ => integrable_iteratedDeriv_windowCarrier hd hdq hη n) hξ).trans ?_
  exact div_le_div_of_nonneg_right
    (integral_norm_iteratedDeriv_windowCarrier_le K hd hdq hη hL hpq hv) (by positivity)

end RHTower

end
