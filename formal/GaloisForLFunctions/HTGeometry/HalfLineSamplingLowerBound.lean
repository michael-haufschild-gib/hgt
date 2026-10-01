import GaloisForLFunctions.HTGeometry.PartitionWeightedWirtinger
import GaloisForLFunctions.HTGeometry.IntervalPoincare

/-!
# A sampling lower bound on the half line

For `F ∈ C¹(0,∞)` with `∫|F'|² ≤ K²∫x²|F|²` and nodes `0 < p₀ < p₁ < ⋯ → ∞` obeying the
supercritical gap condition `max(p_j,p_{j+1})(p_{j+1}-p_j) ≤ a/2`, the weighted Wirtinger
inequality on each gap, summed and passed to the limit, together with the elementary estimate on
`(0,p₀]` gives

`(1 - ((1+ε)²(a/2π)² + 2p₀⁴)K²) ∫x²|F|² ≤ K_ε (a/2) Σ_j max(p_j,p_{j+1})(|F(p_j)|²+|F(p_{j+1})|²)
  + 2p₀³|F(p₀)|²`.

When `(a/2π)K < 1` and `p₀` is small, the bracket is positive and the node values control the
weighted norm: this is the lower frame bound in the Kulikov–Nazarov–Sodin sampling argument.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Complex increment bound: `‖F x − F α‖² ≤ (x − α) ∫_α^x ‖F'‖²`. -/
theorem norm_sub_sq_le_of_hasDerivAt {F F' : ℝ → ℂ} {α x : ℝ} (hαx : α ≤ x)
    (hF : ∀ y ∈ Icc α x, HasDerivAt F (F' y) y) (hF'c : ContinuousOn F' (Icc α x)) :
    ‖F x - F α‖ ^ 2 ≤ (x - α) * ∫ y in Ioc α x, ‖F' y‖ ^ 2 := by
  have hint : IntervalIntegrable F' volume α x := hF'c.intervalIntegrable_of_Icc hαx
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hF y (by rwa [uIcc_of_le hαx] at hy)) hint
  have hnorm : ‖F x - F α‖ ≤ ∫ y in Ioc α x, ‖F' y‖ := by
    rw [← hftc, intervalIntegral.integral_of_le hαx]
    exact norm_integral_le_integral_norm _
  have hn1 : IntegrableOn (fun y => ‖F' y‖) (Ioc α x) :=
    ((hF'c.norm).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hn2 : IntegrableOn (fun y => ‖F' y‖ ^ (2 : ℕ)) (Ioc α x) :=
    (((hF'c.norm).pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcs := sq_integral_le_length_mul hαx hn1 hn2
  have h0 : 0 ≤ ‖F x - F α‖ := norm_nonneg _
  calc ‖F x - F α‖ ^ 2 ≤ (∫ y in Ioc α x, ‖F' y‖) ^ 2 := pow_le_pow_left₀ h0 hnorm 2
    _ ≤ _ := hcs

/-- Near the origin: `∫_{(0,p₀]} x²|F|² ≤ 2p₀³|F(p₀)|² + 2p₀⁴ ∫_{(0,∞)} |F'|²`. -/
theorem integral_Ioc_sq_mul_norm_sq_le {F F' : ℝ → ℂ} {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hF : ∀ x, 0 < x → HasDerivAt F (F' x) x) (hF'c : ContinuousOn F' (Ioi 0))
    (hXF : IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0))
    (hF'2 : IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0)) :
    ∫ x in Ioc 0 p₀, x ^ 2 * ‖F x‖ ^ 2
      ≤ 2 * p₀ ^ 3 * ‖F p₀‖ ^ 2 + 2 * p₀ ^ 4 * ∫ x in Ioi 0, ‖F' x‖ ^ 2 := by
  set J := ∫ x in Ioi (0 : ℝ), ‖F' x‖ ^ 2 with hJ
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi (fun x _ => by positivity)
  have hpt : ∀ x ∈ Ioc (0 : ℝ) p₀, x ^ 2 * ‖F x‖ ^ 2 ≤ p₀ ^ 2 * (2 * ‖F p₀‖ ^ 2 + 2 * p₀ * J) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hinc := norm_sub_sq_le_of_hasDerivAt hx.2 (fun y hy => hF y (lt_of_lt_of_le hx0 hy.1))
      (hF'c.mono (fun y hy => lt_of_lt_of_le hx0 hy.1))
    have hsub : ∫ y in Ioc x p₀, ‖F' y‖ ^ 2 ≤ J :=
      setIntegral_mono_set hF'2 (Eventually.of_forall fun y => by positivity)
        (Eventually.of_forall fun y hy => lt_of_lt_of_le hx0 (le_of_lt hy.1))
    have h1 : ‖F x‖ ^ 2 ≤ 2 * ‖F p₀‖ ^ 2 + 2 * ‖F p₀ - F x‖ ^ 2 := by
      have htri : ‖F x‖ ≤ ‖F p₀‖ + ‖F p₀ - F x‖ := by
        calc ‖F x‖ = ‖F p₀ - (F p₀ - F x)‖ := by ring_nf
          _ ≤ ‖F p₀‖ + ‖F p₀ - F x‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (F x), norm_nonneg (F p₀), norm_nonneg (F p₀ - F x),
        sq_nonneg (‖F p₀‖ - ‖F p₀ - F x‖)]
    have h2 : ‖F p₀ - F x‖ ^ 2 ≤ p₀ * J := by
      calc ‖F p₀ - F x‖ ^ 2 ≤ (p₀ - x) * ∫ y in Ioc x p₀, ‖F' y‖ ^ 2 := hinc
        _ ≤ p₀ * J := by
          have hI0 : 0 ≤ ∫ y in Ioc x p₀, ‖F' y‖ ^ 2 :=
            setIntegral_nonneg measurableSet_Ioc (fun y _ => by positivity)
          nlinarith [hx0]
    have hx2 : x ^ 2 ≤ p₀ ^ 2 := pow_le_pow_left₀ hx0.le hx.2 2
    calc x ^ 2 * ‖F x‖ ^ 2 ≤ p₀ ^ 2 * (2 * ‖F p₀‖ ^ 2 + 2 * ‖F p₀ - F x‖ ^ 2) :=
          mul_le_mul hx2 h1 (by positivity) (by positivity)
      _ ≤ p₀ ^ 2 * (2 * ‖F p₀‖ ^ 2 + 2 * (p₀ * J)) := by gcongr
      _ = p₀ ^ 2 * (2 * ‖F p₀‖ ^ 2 + 2 * p₀ * J) := by ring
  have hconst : IntegrableOn (fun _ : ℝ => p₀ ^ 2 * (2 * ‖F p₀‖ ^ 2 + 2 * p₀ * J)) (Ioc 0 p₀) :=
    integrableOn_const (measure_Ioc_lt_top).ne
  calc ∫ x in Ioc 0 p₀, x ^ 2 * ‖F x‖ ^ 2
      ≤ ∫ _x in Ioc 0 p₀, p₀ ^ 2 * (2 * ‖F p₀‖ ^ 2 + 2 * p₀ * J) :=
        setIntegral_mono_on (hXF.mono_set Ioc_subset_Ioi_self) hconst measurableSet_Ioc hpt
    _ = p₀ * (p₀ ^ 2 * (2 * ‖F p₀‖ ^ 2 + 2 * p₀ * J)) := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hp₀.le, smul_eq_mul, sub_zero]
    _ = _ := by ring

/-- **Sampling lower bound.** Let `F` be `C¹` on `(0,∞)` with
`∫ |F'|² ≤ K² ∫ x²|F|²`, and let `p₀ < p₁ < ⋯ → ∞` satisfy the supercritical gap condition
`max(|p_j|, |p_{j+1}|)(p_{j+1} - p_j) ≤ a/2`. Then
`(1 - ((1+ε)²(a/2π)² + 2p₀⁴) K²) ∫ x²|F|² ≤ K_ε (a/2) Σ_j max(|p_j|,|p_{j+1}|)(|F(p_j)|² + |F(p_{j+1})|²)
  + 2p₀³ |F(p₀)|²`. -/
theorem sampling_lower_bound {F F' : ℝ → ℂ} (hF : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hF'c : ContinuousOn F' (Ioi 0))
    (hXF : IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0))
    (hF'2 : IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0))
    {K : ℝ} (hK : ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2)
    {p : ℕ → ℝ} (hp : StrictMono p) (hp0 : 0 < p 0) (hpinf : Tendsto p atTop atTop)
    {ε a : ℝ} (hε : 0 < ε)
    (hgap : ∀ j, max |p j| |p (j + 1)| * (p (j + 1) - p j) ≤ a / 2)
    (hsum : Summable fun j => max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2)) :
    (1 - ((1 + ε) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * p 0 ^ 4) * K ^ 2) *
        ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2
      ≤ (1 + ε⁻¹) * (2 + 2 * (1 + ε) / Real.pi ^ 2) * (a / 2) *
          ∑' j, max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2)
        + 2 * p 0 ^ 3 * ‖F (p 0)‖ ^ 2 := by
  set I := ∫ x in Ioi (0 : ℝ), x ^ 2 * ‖F x‖ ^ 2 with hI
  set J := ∫ x in Ioi (0 : ℝ), ‖F' x‖ ^ 2 with hJ
  set T := ∑' j, max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2) with hT
  set A := (1 + ε) ^ 2 * (a / (2 * Real.pi)) ^ 2 with hA
  set Kε := (1 + ε⁻¹) * (2 + 2 * (1 + ε) / Real.pi ^ 2) with hKε
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi (fun x _ => by positivity)
  have hKε0 : 0 ≤ Kε := by positivity
  have hpos : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hp0 (hp.monotone (Nat.zero_le j))
  have hterm0 : ∀ j, 0 ≤ max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2) :=
    fun j => by positivity
  have ha : 0 ≤ a := by
    have := hgap 0
    have h1 : 0 < max |p 0| |p 1| * (p 1 - p 0) :=
      mul_pos (lt_of_lt_of_le (abs_pos.mpr (hpos 0).ne') (le_max_left _ _))
        (sub_pos.mpr (hp (Nat.zero_lt_one)))
    linarith
  -- the tail `(p₀, ∞)`
  have htail : ∫ x in Ioi (p 0), x ^ 2 * ‖F x‖ ^ 2 ≤ A * J + Kε * (a / 2) * T := by
    have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (p 0)
      (hXF.mono_set (Ioi_subset_Ioi hp0.le)) hpinf
    refine le_of_tendsto' hlim (fun N => ?_)
    have hw := partition_weighted_wirtinger (ε := ε) (a := a) hε hp (N := N)
      (fun j _ => hgap j) (F := F) (F' := F')
      (fun x hx => hF x (lt_of_lt_of_le hp0 hx.1))
      (hF'c.mono (fun x hx => lt_of_lt_of_le hp0 hx.1))
    have hF'N : ∫ x in p 0..p N, ‖F' x‖ ^ 2 ≤ J := by
      rw [intervalIntegral.integral_of_le (hp.monotone (Nat.zero_le N))]
      exact setIntegral_mono_set hF'2 (Eventually.of_forall fun y => by positivity)
        (Eventually.of_forall fun y hy => lt_of_lt_of_le hp0 (le_of_lt hy.1))
    have hsumN : ∑ j ∈ Finset.range N, max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2)
        ≤ T := hsum.sum_le_tsum _ (fun j _ => hterm0 j)
    calc ∫ x in p 0..p N, x ^ 2 * ‖F x‖ ^ 2
        ≤ A * (∫ x in p 0..p N, ‖F' x‖ ^ 2) + Kε * (a / 2) *
            ∑ j ∈ Finset.range N, max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2) := hw
      _ ≤ A * J + Kε * (a / 2) * T := by
          gcongr
  -- the head `(0, p₀]`
  have hhead := integral_Ioc_sq_mul_norm_sq_le hp0 hF hF'c hXF hF'2
  rw [← hJ] at hhead
  have hsplit : I = (∫ x in Ioc 0 (p 0), x ^ 2 * ‖F x‖ ^ 2) + ∫ x in Ioi (p 0), x ^ 2 * ‖F x‖ ^ 2 := by
    rw [hI, ← Ioc_union_Ioi_eq_Ioi hp0.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hXF.mono_set Ioc_subset_Ioi_self) (hXF.mono_set (Ioi_subset_Ioi hp0.le))]
  have hsum_total : I ≤ (A + 2 * p 0 ^ 4) * J + Kε * (a / 2) * T + 2 * p 0 ^ 3 * ‖F (p 0)‖ ^ 2 := by
    rw [hsplit]; linarith
  have hAp : 0 ≤ A + 2 * p 0 ^ 4 := by positivity
  have hJK := mul_le_mul_of_nonneg_left hK hAp
  nlinarith [hsum_total, hJK]

end GaloisForLFunctions.HTGeometry
