import GaloisForLFunctions.RHTower.XiSliceLogLogOrderPositivity

/-!
# Slice positivity at orders `≥ C log log t`: the density statement

For every `δ > 0` there is `C` such that for all large `T`, the heights `t ∈ [T, 2T]` at which
`c_{2k}(t)` is not positive for some `k ≥ C log log t` have measure at most `δT`
(`eventually_volume_xiSliceCoeff_nonpos_loglog_le`).

Dyadic scales `R_j = 2^j k₀/log T`, `k₀ ≍ log log T`: scale data (`ZetaScaleData`) hold at
`R_j` off a set of measure summable in `j` (zero shadows once, large values `V 2^j`, small values
`W₀ 2^j`), and an order `k ∈ [2k₀, (log t)/24)` falls into one scale with `R_j log t ≤ k ≤
2R_j log t` (`exists_xiSliceCoeff_pos_of_scaleData`). Orders `≥ (log t)/24` are covered by
`eventually_volume_xiSliceCoeff_nonpos_le`.
-/

open Complex Real MeasureTheory Set Filter
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Every `x ≥ 1` lies in a dyadic interval `[2^j, 2^{j+1})`. -/
theorem exists_pow_two_le_lt {x : ℝ} (hx : 1 ≤ x) : ∃ j : ℕ, (2 : ℝ) ^ j ≤ x ∧ x < 2 ^ (j + 1) := by
  classical
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  have hex : ∃ n : ℕ, x < (2 : ℝ) ^ n := ⟨n, hn⟩
  set m := Nat.find hex with hm
  have hmx : x < (2 : ℝ) ^ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, pow_zero] at hmx; linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨j, ?_, by rw [hj] at hmx; exact hmx⟩
  have := Nat.find_min hex (show j < m by omega)
  exact not_lt.mp this

/-- **Dyadic selection of the scale.** With `L ≤ u ≤ L + 1`, an order `k ≥ 2k₀` has a scale
`R = 2^j k₀/L` with `R u ≤ k ≤ 2R u`, `2^j k₀ ≤ k`. -/
theorem exists_scale_of_order {k₀ L u k : ℝ} (hk₀ : 0 < k₀) (hL : 1 ≤ L) (hu1 : L ≤ u)
    (hu2 : u ≤ L + 1) (hk : 2 * k₀ ≤ k) :
    ∃ j : ℕ, (2 : ℝ) ^ j * k₀ / L * u ≤ k ∧ k ≤ 2 * ((2 : ℝ) ^ j * k₀ / L) * u
      ∧ (2 : ℝ) ^ j * k₀ ≤ k := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have hx : 1 ≤ k * L / (k₀ * u) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨j, hj1, hj2⟩ := exists_pow_two_le_lt hx
  have hj1' : (2 : ℝ) ^ j * k₀ / L * u ≤ k := by
    rw [le_div_iff₀ (by positivity)] at hj1
    rw [div_mul_eq_mul_div, div_le_iff₀ hL0]
    nlinarith
  refine ⟨j, hj1', ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)] at hj2
    rw [pow_succ] at hj2
    have : k * L ≤ 2 * ((2 : ℝ) ^ j * k₀ / L) * u * L := by
      field_simp
      nlinarith
    exact le_of_mul_le_mul_right this hL0
  · have : (2 : ℝ) ^ j * k₀ ≤ (2 : ℝ) ^ j * k₀ / L * u := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
      exact mul_le_mul_of_nonneg_left hu1 (by positivity)
    linarith

/-- **Positivity at a good height.** If scale data hold at every dyadic scale `2^j k₀/L ≤ 1/16`
with `10¹¹ (log M_j + W_j + 1) ≤ 2^j k₀`, then `c_{2k}(t) > 0` for `2k₀ ≤ k ≤ (log t)/16`. -/
theorem xiSliceCoeff_pos_of_good {k₁ k₀ L t : ℝ} {M W : ℕ → ℝ}
    (hpos : ∀ t R M W : ℝ, ∀ k : ℕ, ZetaScaleData t R M W → 0 < R → R ≤ 1 / 16 →
      48 ≤ t → 10000 ≤ Real.log t → R * Real.log t ≤ k → (k : ℝ) ≤ 2 * R * Real.log t →
      10 ^ 11 * (Real.log M + W + 1) ≤ k → k₁ ≤ k → 0 < xiSliceCoeff t (2 * k))
    (hk₀ : 0 < k₀) (hk₁ : k₁ ≤ k₀) (hL : 1 ≤ L) (hu1 : L ≤ Real.log t) (hu2 : Real.log t ≤ L + 1)
    (ht : 48 ≤ t) (hu : 10000 ≤ Real.log t)
    (hdata : ∀ j : ℕ, (2 : ℝ) ^ j * k₀ / L ≤ 1 / 16 → ZetaScaleData t ((2 : ℝ) ^ j * k₀ / L) (M j) (W j))
    (hB : ∀ j : ℕ, 10 ^ 11 * (Real.log (M j) + W j + 1) ≤ (2 : ℝ) ^ j * k₀)
    {k : ℕ} (hk : 2 * k₀ ≤ k) (hk' : (k : ℝ) ≤ Real.log t / 16) :
    0 < xiSliceCoeff t (2 * k) := by
  obtain ⟨j, hj1, hj2, hj3⟩ := exists_scale_of_order hk₀ hL hu1 hu2 hk
  have hu0 : 0 < Real.log t := by linarith
  have hR0 : 0 < (2 : ℝ) ^ j * k₀ / L := by positivity
  have hR16 : (2 : ℝ) ^ j * k₀ / L ≤ 1 / 16 := by
    have : (2 : ℝ) ^ j * k₀ / L * Real.log t ≤ Real.log t / 16 := hj1.trans hk'
    nlinarith
  exact hpos t _ _ _ k (hdata j hR16) hR0 hR16 ht hu hj1 hj2 ((hB j).trans hj3)
    (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j, one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)])

/-- The bad heights of the scale-`R` large values. -/
def loglogLargeSet (T k₀ c V : ℝ) (j : ℕ) : Set ℝ :=
  zetaLargeNearScale T (3 / 2 * ((2 : ℝ) ^ j * k₀ / Real.log T))
    (V * 2 ^ j * (4 * T) ^ (c * (3 / 2 * ((2 : ℝ) ^ j * k₀ / Real.log T)))
      * (1 + Real.log (4 * T)) ^ 2)

/-- The bad heights of the scale-`R` small values. -/
def loglogSmallSet (T k₀ W₀ : ℝ) (j : ℕ) : Set ℝ :=
  {t | t ∈ Icc T (2 * T) ∧ Real.log ‖riemannZeta
    (((1 / 2 + 3 * ((2 : ℝ) ^ j * k₀ / Real.log T) : ℝ) : ℂ) + (t : ℂ) * I)‖ < -(W₀ * 2 ^ j)}

/-- **The bad heights are covered.** Outside the edges, the zero shadow, the large and small
values at the dyadic scales and the high-order exceptional set, every order `k ≥` the threshold
has `c_{2k}(t) > 0`. -/
theorem loglog_bad_subset {k₁ k₀ T c V W₀ η : ℝ} {thr : ℝ → ℝ}
    (hpos : ∀ t R M W : ℝ, ∀ k : ℕ, ZetaScaleData t R M W → 0 < R → R ≤ 1 / 16 →
      48 ≤ t → 10000 ≤ Real.log t → R * Real.log t ≤ k → (k : ℝ) ≤ 2 * R * Real.log t →
      10 ^ 11 * (Real.log M + W + 1) ≤ k → k₁ ≤ k → 0 < xiSliceCoeff t (2 * k))
    (hk₀ : 1 ≤ k₀) (hk₁ : k₁ ≤ k₀) (hT : 48 ≤ T) (hL : 10000 ≤ Real.log T) (hη : η ≤ 1 / 16)
    (hB : ∀ j : ℕ, 10 ^ 11 * (Real.log (V * 2 ^ j * (4 * T) ^ (c * (3 / 2 * ((2 : ℝ) ^ j * k₀
      / Real.log T))) * (1 + Real.log (4 * T)) ^ 2) + W₀ * 2 ^ j + 1) ≤ (2 : ℝ) ^ j * k₀)
    (hthr : ∀ t ∈ Icc T (2 * T), 2 * k₀ ≤ thr t) :
    {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, thr t ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ⊆
      (Icc T (T + 31) ∪ Icc (2 * T - 31) (2 * T))
      ∪ (zetaZeroShadowScaled (k₀ / Real.log T / 10) 30 ∩ Icc (T + 31) (2 * T - 31))
      ∪ (⋃ j ∈ (Finset.range (⌈Real.log T⌉₊ + 1)).filter
          (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
          (loglogLargeSet T k₀ c V j ∪ loglogSmallSet T k₀ W₀ j))
      ∪ {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, η * Real.log t ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} := by
  classical
  rintro t ⟨ht, k, hk, hneg⟩
  by_contra hout
  simp only [mem_union, mem_iUnion, not_or, mem_inter_iff, not_and, mem_setOf_eq,
    Finset.mem_filter, Finset.mem_range, exists_prop, not_exists] at hout
  obtain ⟨⟨⟨⟨hE1, hE2⟩, hshadow⟩, hscales⟩, hhigh⟩ := hout
  have hTt : T ≤ t := ht.1
  have ht0 : 0 < t := by linarith
  set L := Real.log T with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hu1 : L ≤ Real.log t := Real.log_le_log (by linarith) hTt
  have hu2 : Real.log t ≤ L + 1 := by
    have h2 := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    have := Real.log_two_lt_d9
    linarith
  have hin : t ∈ Icc (T + 31) (2 * T - 31) := by
    by_contra hn
    rw [mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · exact hE1 ⟨ht.1, hn.le⟩
    · exact hE2 ⟨hn.le, ht.2⟩
  -- orders below `η log t` are handled by the scales
  have hkη : (k : ℝ) < η * Real.log t := by
    by_contra hk'
    exact hhigh ht k (not_lt.mp hk') hneg
  apply hneg
  refine xiSliceCoeff_pos_of_good (M := fun j => V * 2 ^ j * (4 * T) ^ (c * (3 / 2 * ((2 : ℝ) ^ j
    * k₀ / L))) * (1 + Real.log (4 * T)) ^ 2) (W := fun j => W₀ * 2 ^ j) hpos (by linarith) hk₁ hL1 hu1
    hu2 (by linarith) (by linarith) ?_ hB ((hthr t ht).trans hk) (by nlinarith)
  intro j hj
  have hjN : j < ⌈L⌉₊ + 1 := by
    have h1 : (2 : ℝ) ^ j ≤ L := by
      have : (2 : ℝ) ^ j * k₀ ≤ L / 16 := by
        rw [div_le_iff₀ (by linarith)] at hj; linarith
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
    have h2 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : (j : ℝ) < ⌈L⌉₊ + 1 := by linarith [Nat.le_ceil L]
    exact_mod_cast h3
  obtain ⟨hlarge, hsmall⟩ := hscales j ⟨hjN, hj⟩
  set R := (2 : ℝ) ^ j * k₀ / L with hR
  have hR0 : 0 < R := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- zero-freeness from the shadow
    intro w hw0 hwre
    by_contra hclose
    rw [not_lt] at hclose
    refine hshadow ⟨w, hw0, ?_, ?_⟩ hin
    · have : k₀ / L / 10 ≤ R / 10 := by
        rw [hR]
        have : k₀ / L ≤ (2 : ℝ) ^ j * k₀ / L := by
          rw [mul_div_assoc]
          exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
        linarith
      linarith
    · linarith
  · intro z hz1 hz2 hz3
    by_contra hbig
    rw [not_le] at hbig
    exact hlarge ⟨ht, z, hz1, by linarith, by linarith, hbig⟩
  · by_contra hlow
    rw [not_le] at hlow
    exact hsmall ⟨ht, by simpa [scaleCentre, hR] using hlow⟩

/-- The large values summed over the scales. -/
theorem volume_loglogLarge_le {C₁ c V T k₀ : ℝ} (N : ℕ)
    (hlarge : ∀ c R T V : ℝ, 0 < c → c ≤ 1 → 0 < R → R ≤ 1 / 8 → 8 ≤ T → 0 < V →
      volume (zetaLargeNearScale T R (V * (4 * T) ^ (c * R) * (1 + Real.log (4 * T)) ^ 2))
        ≤ ENNReal.ofReal (C₁ * T / (c ^ 2 * V ^ 2)))
    (hC₁ : 0 < C₁) (hc : 0 < c) (hc1 : c ≤ 1) (hV : 1 ≤ V) (hT : 8 ≤ T) (hk₀ : 0 < k₀)
    (hL : 0 < Real.log T) :
    volume (⋃ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
      loglogLargeSet T k₀ c V j) ≤ ENNReal.ofReal (2 * (C₁ * T / (c ^ 2 * V ^ 2))) := by
  classical
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
      volume (loglogLargeSet T k₀ c V j) ≤ ENNReal.ofReal (C₁ * T / (c ^ 2 * V ^ 2) * (1 / 2) ^ j) := by
    intro j hj
    have hRj := (Finset.mem_filter.mp hj).2
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    have h := hlarge c (3 / 2 * ((2 : ℝ) ^ j * k₀ / Real.log T)) T (V * 2 ^ j) hc hc1
      (by positivity) (by linarith) hT (by positivity)
    unfold loglogLargeSet
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have h4 : (V * 2 ^ j) ^ 2 = V ^ 2 * (2 ^ j) ^ 2 := by ring
    rw [h4, one_div_pow, ← div_eq_mul_one_div, div_div]
    have hC0 : 0 ≤ C₁ * T := by positivity
    apply div_le_div_of_nonneg_left hC0 (by positivity)
    have : (2 : ℝ) ^ j ≤ (2 ^ j) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left hpow.le (one_le_pow₀ (by norm_num))
    have hcv : 0 < c ^ 2 * V ^ 2 := by positivity
    nlinarith
  calc ∑ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
        volume (loglogLargeSet T k₀ c V j)
      ≤ ∑ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
          ENNReal.ofReal (C₁ * T / (c ^ 2 * V ^ 2) * (1 / 2) ^ j) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ j ∈ (Finset.range N).filter
          (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
          C₁ * T / (c ^ 2 * V ^ 2) * (1 / 2) ^ j) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity).symm
    _ ≤ ENNReal.ofReal (2 * (C₁ * T / (c ^ 2 * V ^ 2))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        have h1 : ∑ j ∈ (Finset.range N).filter
            (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16), ((1 : ℝ) / 2) ^ j ≤ 2 :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => by positivity).trans (sum_geometric_two_le N)
        have : 0 ≤ C₁ * T / (c ^ 2 * V ^ 2) := by positivity
        nlinarith

/-- The small values summed over the scales. -/
theorem volume_loglogSmall_le {C₂ W₀ T k₀ : ℝ} (N : ℕ)
    (hsmall : ∀ T : ℝ, 40 ≤ T → ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 1 → ∀ W : ℝ, 0 < W →
      volume {t | t ∈ Icc T (2 * T) ∧ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ < -W}
        ≤ ENNReal.ofReal (C₂ * T * Real.log (2 + Real.log T) / W))
    (hC₂ : 0 < C₂) (hW₀ : 0 < W₀) (hT : 40 ≤ T) (hk₀ : 0 < k₀) (hL : 0 < Real.log T) :
    volume (⋃ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
      loglogSmallSet T k₀ W₀ j)
      ≤ ENNReal.ofReal (2 * (C₂ * T * Real.log (2 + Real.log T) / W₀)) := by
  classical
  have hLL : 0 ≤ Real.log (2 + Real.log T) := Real.log_nonneg (by linarith)
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
      volume (loglogSmallSet T k₀ W₀ j)
        ≤ ENNReal.ofReal (C₂ * T * Real.log (2 + Real.log T) / W₀ * (1 / 2) ^ j) := by
    intro j hj
    have hRj := (Finset.mem_filter.mp hj).2
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    have h := hsmall T hT (1 / 2 + 3 * ((2 : ℝ) ^ j * k₀ / Real.log T)) (by
      have : 0 < (2 : ℝ) ^ j * k₀ / Real.log T := by positivity
      linarith) (by linarith) (W₀ * 2 ^ j) (by positivity)
    unfold loglogSmallSet
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [one_div_pow]; field_simp
  calc ∑ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
        volume (loglogSmallSet T k₀ W₀ j)
      ≤ ∑ j ∈ (Finset.range N).filter (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
          ENNReal.ofReal (C₂ * T * Real.log (2 + Real.log T) / W₀ * (1 / 2) ^ j) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ j ∈ (Finset.range N).filter
          (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16),
          C₂ * T * Real.log (2 + Real.log T) / W₀ * (1 / 2) ^ j) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity).symm
    _ ≤ ENNReal.ofReal (2 * (C₂ * T * Real.log (2 + Real.log T) / W₀)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        have h1 : ∑ j ∈ (Finset.range N).filter
            (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16), ((1 : ℝ) / 2) ^ j ≤ 2 :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => by positivity).trans (sum_geometric_two_le N)
        have : 0 ≤ C₂ * T * Real.log (2 + Real.log T) / W₀ := by positivity
        nlinarith

/-- `1 + log 4T ≤ (3/2)(2 + log T)` for `T ≥ 1`. -/
theorem one_add_log_four_mul_le {T : ℝ} (hT : 1 ≤ T) :
    1 + Real.log (4 * T) ≤ 3 / 2 * (2 + Real.log T) := by
  rw [Real.log_mul (by norm_num) (by linarith)]
  have : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  linarith [Real.log_nonneg hT]

/-- **The budget `10¹¹ B_j ≤ 2^j k₀`** for `k₀ = K₀ (1 + log(2 + log T))`,
`W₀ = 8 C₂ log(2 + log T)/δ`, `c = 10⁻¹³`. -/
theorem loglog_budget {V C₂ δ K₀ T : ℝ} (hV : 1 ≤ V) (hC₂ : 0 < C₂) (hδ : 0 < δ) (hT : 40 ≤ T)
    (hK₀ : 10 ^ 12 * (Real.log V + 4 + 8 * C₂ / δ) ≤ K₀) (j : ℕ) :
    10 ^ 11 * (Real.log (V * 2 ^ j * (4 * T) ^ (1 / 10 ^ 13 * (3 / 2 * ((2 : ℝ) ^ j
      * (K₀ * (1 + Real.log (2 + Real.log T))) / Real.log T))) * (1 + Real.log (4 * T)) ^ 2)
      + 8 * C₂ * Real.log (2 + Real.log T) / δ * 2 ^ j + 1)
      ≤ (2 : ℝ) ^ j * (K₀ * (1 + Real.log (2 + Real.log T))) := by
  set ℓ := Real.log (2 + Real.log T) with hℓ
  set L := Real.log T with hL
  have hL1 : 2 ≤ L := by
    rw [hL]
    have h := Real.log_le_log (by positivity) (show Real.exp 2 ≤ T by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1])
    rw [Real.log_exp] at h; exact h
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hpow1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hj : (j : ℝ) * Real.log 2 ≤ 2 ^ j := by
    have h1 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : (0 : ℝ) ≤ j := j.cast_nonneg
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hK₀0 : 0 < K₀ := lt_of_lt_of_le (by positivity) hK₀
  set k₀ := K₀ * (1 + ℓ) with hk₀
  have hk₀0 : 0 < k₀ := by positivity
  have h4T : Real.log (4 * T) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) (by linarith), hL]
    have : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    linarith
  have h1l : 1 ≤ 1 + Real.log (4 * T) := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
  have hl1 : Real.log (1 + Real.log (4 * T)) ≤ 1 + ℓ := by
    have := one_add_log_four_mul_le (by linarith : (1 : ℝ) ≤ T)
    calc Real.log (1 + Real.log (4 * T)) ≤ Real.log (3 / 2 * (2 + Real.log T)) :=
          Real.log_le_log (by linarith) this
      _ = Real.log (3 / 2) + ℓ := by
          rw [Real.log_mul (by norm_num) (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)])]
      _ ≤ 1 + ℓ := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2); linarith
  have hx : 1 / 10 ^ 13 * (3 / 2 * ((2 : ℝ) ^ j * k₀ / L)) * Real.log (4 * T)
      ≤ 3 / 10 ^ 13 * ((2 : ℝ) ^ j * k₀) := by
    have hR0 : 0 ≤ (2 : ℝ) ^ j * k₀ / L := by positivity
    calc 1 / 10 ^ 13 * (3 / 2 * ((2 : ℝ) ^ j * k₀ / L)) * Real.log (4 * T)
        ≤ 1 / 10 ^ 13 * (3 / 2 * ((2 : ℝ) ^ j * k₀ / L)) * (2 * L) := by gcongr
      _ = 3 / 10 ^ 13 * ((2 : ℝ) ^ j * k₀) := by field_simp
  have hlog : Real.log (V * 2 ^ j * (4 * T) ^ (1 / 10 ^ 13 * (3 / 2 * ((2 : ℝ) ^ j * k₀ / L)))
      * (1 + Real.log (4 * T)) ^ 2)
      = Real.log V + j * Real.log 2 + 1 / 10 ^ 13 * (3 / 2 * ((2 : ℝ) ^ j * k₀ / L))
        * Real.log (4 * T) + 2 * Real.log (1 + Real.log (4 * T)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_rpow (by linarith)]
    push_cast; ring
  rw [hlog]
  have hW : 8 * C₂ * ℓ / δ * 2 ^ j = 2 ^ j * (8 * C₂ / δ * ℓ) := by ring
  rw [hW]
  have hk₀big : 10 ^ 11 * (Real.log V + 4 + 2 * ℓ + 8 * C₂ / δ * ℓ) ≤ 97 / 100 * k₀ := by
    rw [hk₀]
    have hA : 0 ≤ 8 * C₂ / δ := by positivity
    have h1 : 10 ^ 12 * (Real.log V + 4 + 8 * C₂ / δ) * (1 + ℓ) ≤ K₀ * (1 + ℓ) :=
      mul_le_mul_of_nonneg_right hK₀ (by linarith)
    nlinarith
  have hsum : 10 ^ 11 * (Real.log V + j * Real.log 2 + 2 * Real.log (1 + Real.log (4 * T))
      + 2 ^ j * (8 * C₂ / δ * ℓ) + 1)
      ≤ 2 ^ j * (10 ^ 11 * (Real.log V + 4 + 2 * ℓ + 8 * C₂ / δ * ℓ)) := by
    have hA : 0 ≤ 8 * C₂ / δ * ℓ := by positivity
    nlinarith
  have hfin : 2 ^ j * (10 ^ 11 * (Real.log V + 4 + 2 * ℓ + 8 * C₂ / δ * ℓ))
      ≤ 2 ^ j * (97 / 100 * k₀) := mul_le_mul_of_nonneg_left hk₀big hpow.le
  have hxx : 10 ^ 11 * (1 / 10 ^ 13 * (3 / 2 * ((2 : ℝ) ^ j * k₀ / L)) * Real.log (4 * T))
      ≤ 3 / 100 * ((2 : ℝ) ^ j * k₀) := by nlinarith
  nlinarith

/-- The threshold `6K₀ log log t` dominates `2K₀ (1 + log(2 + log T))` on `[T, 2T]`. -/
theorem loglog_threshold {K₀ T t : ℝ} (hK₀ : 0 ≤ K₀) (hT : Real.exp 10000 ≤ T) (hTt : T ≤ t) :
    2 * (K₀ * (1 + Real.log (2 + Real.log T))) ≤ 6 * K₀ * Real.log (Real.log t) := by
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hL : 10000 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hT; rwa [Real.log_exp] at this
  have hLt : Real.log T ≤ Real.log t := Real.log_le_log hT0 hTt
  have hll : Real.log (Real.log T) ≤ Real.log (Real.log t) := Real.log_le_log (by linarith) hLt
  have hll1 : 1 ≤ Real.log (Real.log T) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.log T by
      have := Real.exp_one_lt_d9; linarith)
    rwa [Real.log_exp] at h
  have h2 : Real.log (2 + Real.log T) ≤ Real.log 2 + Real.log (Real.log T) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  nlinarith

theorem loglog_numeric_shadow {δ D k₀ T : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D) (hk₀ : 4800 * D / δ ≤ k₀)
    (hk₀1 : 1 ≤ k₀) (hT : 40 ≤ T) :
    60 * (D / (k₀ / Real.log T / 10 * Real.log (4 * T)) * (4 * T / 4)) ≤ δ * T / 8 := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hL4 : Real.log T ≤ Real.log (4 * T) := Real.log_le_log hT0 (by linarith)
  have hL40 : 0 < Real.log (4 * T) := by linarith
  have hk0 : 0 < k₀ := by linarith
  have h1 : 4800 * D ≤ k₀ * δ := (div_le_iff₀ hδ).mp hk₀
  have e : D / (k₀ / Real.log T / 10 * Real.log (4 * T)) * (4 * T / 4)
      = 10 * D * T * Real.log T / (k₀ * Real.log (4 * T)) := by
    field_simp
  rw [e, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  have h2 : Real.log T * (60 * (10 * D * T)) ≤ Real.log (4 * T) * (60 * (10 * D * T)) :=
    mul_le_mul_of_nonneg_right hL4 (by positivity)
  have h3 : 600 * D * T * 8 ≤ δ * T * k₀ := by nlinarith
  nlinarith

theorem loglog_numeric_log {δ K T B₀ : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hT : 40 ≤ T)
    (hB₀ : B₀ = 8 * (60 * 32 * K + 62) / δ + 1) (hTB : B₀ ≤ T ^ (1 / 2 : ℝ)) :
    62 + 60 * (K * Real.log (4 * T) ^ 2) ≤ δ * T / 8 := by
  have hT0 : 0 < T := by linarith
  have hlog : Real.log (4 * T) ≤ 4 * (4 * T) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 4 * T) (by norm_num : (0 : ℝ) < 1 / 4)
    linarith [show (4 * T) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (4 * T) ^ (1 / 4 : ℝ) by ring]
  have hlog0 : 0 ≤ Real.log (4 * T) := Real.log_nonneg (by linarith)
  have hq : ((4 * T) ^ (1 / 4 : ℝ)) ^ 2 = 2 * T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.mul_rpow (by norm_num) hT0.le]
    norm_num
  have hsq : Real.log (4 * T) ^ 2 ≤ 32 * T ^ (1 / 2 : ℝ) := by
    have h1 : Real.log (4 * T) ^ 2 ≤ (4 * (4 * T) ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    rw [mul_pow, hq] at h1
    linarith
  have hT12 : 1 ≤ T ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hTT : T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have h1 : 60 * (K * Real.log (4 * T) ^ 2) ≤ 60 * 32 * K * T ^ (1 / 2 : ℝ) := by nlinarith
  have h2 : 62 + 60 * 32 * K * T ^ (1 / 2 : ℝ) ≤ (60 * 32 * K + 62) * T ^ (1 / 2 : ℝ) := by
    nlinarith
  have h3 : (60 * 32 * K + 62) ≤ δ / 8 * B₀ := by
    rw [hB₀]
    have : δ / 8 * (8 * (60 * 32 * K + 62) / δ + 1) = (60 * 32 * K + 62) + δ / 8 := by
      field_simp
    linarith
  have h4 : (60 * 32 * K + 62) * T ^ (1 / 2 : ℝ) ≤ δ / 8 * B₀ * T ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  have h5 : δ / 8 * B₀ * T ^ (1 / 2 : ℝ) ≤ δ / 8 * T := by
    calc δ / 8 * B₀ * T ^ (1 / 2 : ℝ) ≤ δ / 8 * T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
          gcongr
      _ = δ / 8 * T := by rw [mul_assoc, hTT]
  linarith

theorem loglog_numeric_large {δ C₁ c V T : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hV1 : 1 ≤ V) (hV : 8 * C₁ / (c ^ 2 * δ) ≤ V) (hT : 0 < T) :
    2 * (C₁ * T / (c ^ 2 * V ^ 2)) ≤ δ * T / 4 := by
  have h1 : 8 * C₁ ≤ V * (c ^ 2 * δ) := (div_le_iff₀ (by positivity)).mp hV
  have hV2 : V ≤ V ^ 2 := by nlinarith
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  have h2 : V * (c ^ 2 * δ) * T ≤ V ^ 2 * (c ^ 2 * δ) * T := by
    have : 0 ≤ c ^ 2 * δ * T := by positivity
    nlinarith
  nlinarith

theorem loglog_numeric_small {δ C₂ T ℓ : ℝ} (hδ : 0 < δ) (hC₂ : 0 < C₂) (hℓ : 0 < ℓ) :
    2 * (C₂ * T * ℓ / (8 * C₂ * ℓ / δ)) = δ * T / 4 := by
  field_simp; ring

/-- **Slice positivity at orders `≥ C log log t` for almost every height.** For every `δ > 0`
there is `C` such that for all large `T`, the heights `t ∈ [T, 2T]` at which `c_{2k}(t)` is not
positive for some order `k ≥ C log log t` have measure at most `δT`. -/
theorem eventually_volume_xiSliceCoeff_nonpos_loglog_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, C * Real.log (Real.log t) ≤ k ∧
        ¬ 0 < xiSliceCoeff t (2 * k)} ≤ ENNReal.ofReal (δ * T) := by
  classical
  obtain ⟨k₁, hk₁1, hpos⟩ := exists_xiSliceCoeff_pos_of_scaleData
  obtain ⟨C₁, hC₁, hlarge⟩ := exists_volume_zetaLargeNearScale_le
  obtain ⟨C₂, hC₂, hsmall⟩ := exists_volume_logZeta_lt_neg_le
  obtain ⟨D, K, hD, hK, hshadow⟩ := exists_volume_zetaZeroShadowScaled_le
  set c : ℝ := 1 / 10 ^ 13 with hc
  set V : ℝ := 1 + 8 * C₁ / (c ^ 2 * δ) with hVdef
  have hV1 : 1 ≤ V := by rw [hVdef]; have : 0 ≤ 8 * C₁ / (c ^ 2 * δ) := by positivity
                         linarith
  set K₀ : ℝ := 10 ^ 12 * (Real.log V + 4 + 8 * C₂ / δ) + k₁ + 4800 * D / δ + 20 with hK₀def
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV1
  have hK₀0 : 0 < K₀ := by
    rw [hK₀def]; have : 0 ≤ 4800 * D / δ := by positivity
    have : 0 ≤ 10 ^ 12 * (Real.log V + 4 + 8 * C₂ / δ) := by positivity
    linarith
  refine ⟨6 * K₀, by positivity, ?_⟩
  set B₀ : ℝ := 8 * (60 * 32 * K + 62) / δ + 1 with hB₀
  have hsq : Tendsto (fun T : ℝ => T ^ (1 / 2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_volume_xiSliceCoeff_nonpos_le (η := 1 / 24) (δ := δ / 4)
      (by norm_num) (by positivity),
    (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).eventually hshadow,
    eventually_ge_atTop (Real.exp 10000), hsq.eventually_ge_atTop B₀] with T hE hSh hT hTB
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hL : 10000 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hT; rwa [Real.log_exp] at this
  have hT40 : 48 ≤ T := by
    have := Real.add_one_le_exp (10000 : ℝ); linarith
  set ℓ := Real.log (2 + Real.log T) with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by linarith)
  have hA : 0 ≤ 10 ^ 12 * (Real.log V + 4 + 8 * C₂ / δ) := by positivity
  have hDd : 0 ≤ 4800 * D / δ := by positivity
  have hK₀big : 10 ^ 12 * (Real.log V + 4 + 8 * C₂ / δ) ≤ K₀ := by rw [hK₀def]; linarith
  have hK₀k₁ : k₁ ≤ K₀ := by rw [hK₀def]; linarith
  have hK₀D : 4800 * D / δ ≤ K₀ := by rw [hK₀def]; linarith
  have hK₀20 : 20 ≤ K₀ := by rw [hK₀def]; linarith
  set k₀ := K₀ * (1 + ℓ) with hk₀
  have hk₀K : K₀ ≤ k₀ := le_mul_of_one_le_right hK₀0.le (by linarith)
  have hsub := loglog_bad_subset (k₁ := k₁) (k₀ := k₀) (T := T) (c := c) (V := V)
    (W₀ := 8 * C₂ * ℓ / δ) (η := 1 / 24) (thr := fun t => 6 * K₀ * Real.log (Real.log t))
    hpos (by linarith) (by linarith) (by linarith) hL (by norm_num)
    (fun j => loglog_budget hV1 hC₂ hδ (by linarith) hK₀big j)
    (fun t ht => loglog_threshold hK₀0.le hT ht.1)
  refine (measure_mono hsub).trans ?_
  have hv1 : volume (Icc T (T + 31) ∪ Icc (2 * T - 31) (2 * T)) ≤ ENNReal.ofReal 62 := by
    refine (measure_union_le _ _).trans ?_
    rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have ha : 2 / Real.log (4 * T) ≤ k₀ / Real.log T / 10 := by
    have hLT : 0 < Real.log T := by linarith
    have hL4 : Real.log T ≤ Real.log (4 * T) := Real.log_le_log hT0 (by linarith)
    rw [div_div, div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  have hv2 := hSh (k₀ / Real.log T / 10) 30 ha (by norm_num)
  simp only [id] at hv2
  rw [show 4 * T / 4 + 30 + 1 = T + 31 by ring, show 4 * T / 2 - 30 - 1 = 2 * T - 31 by ring]
    at hv2
  set S := (Finset.range (⌈Real.log T⌉₊ + 1)).filter
    (fun j : ℕ => (2 : ℝ) ^ j * k₀ / Real.log T ≤ 1 / 16) with hS
  have hv3 : volume (⋃ j ∈ S, (loglogLargeSet T k₀ c V j ∪ loglogSmallSet T k₀ (8 * C₂ * ℓ / δ) j))
      ≤ ENNReal.ofReal (2 * (C₁ * T / (c ^ 2 * V ^ 2)))
        + ENNReal.ofReal (2 * (C₂ * T * ℓ / (8 * C₂ * ℓ / δ))) := by
    have hsubU : (⋃ j ∈ S, (loglogLargeSet T k₀ c V j ∪ loglogSmallSet T k₀ (8 * C₂ * ℓ / δ) j))
        ⊆ (⋃ j ∈ S, loglogLargeSet T k₀ c V j) ∪ (⋃ j ∈ S, loglogSmallSet T k₀ (8 * C₂ * ℓ / δ) j) := by
      intro t ht
      simp only [mem_iUnion, mem_union, exists_prop] at ht ⊢
      obtain ⟨j, hj, h | h⟩ := ht
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr ⟨j, hj, h⟩
    calc _ ≤ volume ((⋃ j ∈ S, loglogLargeSet T k₀ c V j)
          ∪ (⋃ j ∈ S, loglogSmallSet T k₀ (8 * C₂ * ℓ / δ) j)) := measure_mono hsubU
      _ ≤ volume (⋃ j ∈ S, loglogLargeSet T k₀ c V j)
          + volume (⋃ j ∈ S, loglogSmallSet T k₀ (8 * C₂ * ℓ / δ) j) := measure_union_le _ _
      _ ≤ _ := add_le_add
          (volume_loglogLarge_le _ hlarge hC₁ (by positivity) (by norm_num) hV1 (by linarith)
            (by positivity) (by linarith))
          (volume_loglogSmall_le _ hsmall hC₂ (by positivity) (by linarith) (by positivity)
            (by linarith))
  have n1 := loglog_numeric_shadow (k₀ := k₀) (T := T) hδ hD (hK₀D.trans hk₀K) (by linarith)
    (by linarith)
  have n2 := loglog_numeric_log (T := T) hδ hK (by linarith) hB₀ hTB
  have n3 := loglog_numeric_large hδ (by positivity : (0 : ℝ) < c) hV1
    (show 8 * C₁ / (c ^ 2 * δ) ≤ 1 + 8 * C₁ / (c ^ 2 * δ) by linarith) hT0 (C₁ := C₁)
  have n4 := loglog_numeric_small (T := T) hδ hC₂ hℓ0
  have hx2 : 0 ≤ 2 * 30 * (D / (k₀ / Real.log T / 10 * Real.log (4 * T)) * (4 * T / 4)
      + K * Real.log (4 * T) ^ 2) := by
    have : 0 < Real.log (4 * T) := Real.log_pos (by linarith)
    have : 0 < Real.log T := by linarith
    positivity
  have hx3 : 0 ≤ 2 * (C₁ * T / (c ^ 2 * V ^ 2)) := by positivity
  have hx4 : 0 ≤ 2 * (C₂ * T * ℓ / (8 * C₂ * ℓ / δ)) := by positivity
  calc _ ≤ volume ((Icc T (T + 31) ∪ Icc (2 * T - 31) (2 * T))
          ∪ (zetaZeroShadowScaled (k₀ / Real.log T / 10) 30 ∩ Icc (T + 31) (2 * T - 31))
          ∪ (⋃ j ∈ S, (loglogLargeSet T k₀ c V j ∪ loglogSmallSet T k₀ (8 * C₂ * ℓ / δ) j)))
        + volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, 1 / 24 * Real.log t ≤ k ∧
            ¬ 0 < xiSliceCoeff t (2 * k)} := measure_union_le _ _
    _ ≤ (ENNReal.ofReal 62 + ENNReal.ofReal (2 * 30 * (D / (k₀ / Real.log T / 10
          * Real.log (4 * T)) * (4 * T / 4) + K * Real.log (4 * T) ^ 2))
          + (ENNReal.ofReal (2 * (C₁ * T / (c ^ 2 * V ^ 2)))
            + ENNReal.ofReal (2 * (C₂ * T * ℓ / (8 * C₂ * ℓ / δ)))))
        + ENNReal.ofReal (δ / 4 * T) := by
        gcongr
        exact (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add hv1 hv2)) hv3)
    _ = ENNReal.ofReal (62 + 2 * 30 * (D / (k₀ / Real.log T / 10 * Real.log (4 * T))
          * (4 * T / 4) + K * Real.log (4 * T) ^ 2)
          + (2 * (C₁ * T / (c ^ 2 * V ^ 2)) + 2 * (C₂ * T * ℓ / (8 * C₂ * ℓ / δ)))
          + δ / 4 * T) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by norm_num) hx2, ENNReal.ofReal_add hx3 hx4]
    _ ≤ ENNReal.ofReal (δ * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : 2 * 30 * (D / (k₀ / Real.log T / 10 * Real.log (4 * T)) * (4 * T / 4)
            + K * Real.log (4 * T) ^ 2)
            = 60 * (D / (k₀ / Real.log T / 10 * Real.log (4 * T)) * (4 * T / 4))
              + 60 * (K * Real.log (4 * T) ^ 2) := by ring
        rw [e]
        linarith

end

end RHTower
