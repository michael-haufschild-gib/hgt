import GaloisForLFunctions.HTGeometry.BohrBochnerEquivalence
import GaloisForLFunctions.HTGeometry.BohrSpectrum

/-!
# Recurrence through errors that are small in mean square

`recurrent_threshold_of_sparse_errors`: let `P, Q` be continuous Bohr almost periodic and let the
errors `E, F` have mean square `o(W)` on the shells `[W, 2W]`.  If far out `P + E < d` forces
`Q + F = 0`, then `P x < d` forces `Q x = 0`.

Common almost periods move `x` into `≍ W/L` disjoint windows of fixed length `ρ` inside
`[W, 2W]`, on which `P` and `Q` stay close to `P x` and `Q x`.  If every window met only large
errors, the shell would carry mean square `≍ W`; so some window contains a point where both errors
are small, and the floor transports `Q = 0` back to `x`.  Pointwise decay of the errors is not needed.
-/

open MeasureTheory Filter Topology Set

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- **Recurrence through sparse errors.** -/
theorem recurrent_threshold_of_sparse_errors {P Q E F : ℝ → ℝ}
    (hPc : Continuous P) (hPa : _root_.HTGeometry.IsBohrAlmostPeriodic P)
    (hQc : Continuous Q) (hQa : _root_.HTGeometry.IsBohrAlmostPeriodic Q)
    (hsparse : ∀ c : ℝ, 0 < c → ∀ᶠ W in atTop,
      ∫⁻ t in Icc W (2 * W), ENNReal.ofReal (E t ^ 2 + F t ^ 2) ≤ ENNReal.ofReal (c * W))
    {d T₀ : ℝ} (hfloor : ∀ t, T₀ ≤ t → P t + E t < d → Q t + F t = 0)
    {x : ℝ} (hx : P x < d) : Q x = 0 := by
  by_contra hQ
  have hQpos : 0 < |Q x| := abs_pos.mpr hQ
  set ε : ℝ := min ((d - P x) / 4) (|Q x| / 4) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hεP : ε ≤ (d - P x) / 4 := min_le_left _ _
  have hεQ : ε ≤ |Q x| / 4 := min_le_right _ _
  -- uniform continuity and common almost periods
  obtain ⟨δP, hδP, hP⟩ := exists_delta_of_isBohrAlmostPeriodic hPc hPa hε
  obtain ⟨δQ, hδQ, hQu⟩ := exists_delta_of_isBohrAlmostPeriodic hQc hQa hε
  obtain ⟨L, hL0, hL⟩ := exists_common_almostPeriods hPc hPa hQc hQa hε
  set ρ : ℝ := min (min δP δQ) 1 / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 / 2 := by rw [hρdef]; linarith [min_le_right (min δP δQ) 1]
  have hρP : ρ < δP := by
    rw [hρdef]; linarith [min_le_left (min δP δQ) 1, min_le_left δP δQ]
  have hρQ : ρ < δQ := by
    rw [hρdef]; linarith [min_le_left (min δP δQ) 1, min_le_right δP δQ]
  -- a window `[x + τ, x + τ + ρ]` far out only meets large errors
  have hbad : ∀ τ : ℝ, (∀ y, ‖P (y + τ) - P y‖ ≤ ε) → (∀ y, ‖Q (y + τ) - Q y‖ ≤ ε) →
      T₀ ≤ x + τ → ∀ t ∈ Icc (x + τ) (x + τ + ρ), ε ^ 2 ≤ E t ^ 2 + F t ^ 2 := by
    intro τ hτP hτQ hT t ht
    by_contra hsmall
    push Not at hsmall
    have hE : |E t| < ε := by
      rw [← abs_of_pos hε, ← sq_lt_sq]; nlinarith [sq_nonneg (F t)]
    have hF : |F t| < ε := by
      rw [← abs_of_pos hε, ← sq_lt_sq]; nlinarith [sq_nonneg (E t)]
    set r := t - x - τ with hr
    have hr0 : 0 ≤ r := by rw [hr]; linarith [ht.1]
    have hrρ : r ≤ ρ := by rw [hr]; linarith [ht.2]
    have htr : t = (x + r) + τ := by rw [hr]; ring
    have hPt : |P t - P x| ≤ 2 * ε := by
      have h1 := hτP (x + r)
      have h2 := hP (x + r) x (by rw [show x + r - x = r by ring, abs_of_nonneg hr0]; linarith)
      rw [Real.norm_eq_abs] at h1 h2
      rw [htr]
      calc |P (x + r + τ) - P x| ≤ |P (x + r + τ) - P (x + r)| + |P (x + r) - P x| :=
            abs_sub_le _ _ _
        _ ≤ 2 * ε := by linarith
    have hQt : |Q t - Q x| ≤ 2 * ε := by
      have h1 := hτQ (x + r)
      have h2 := hQu (x + r) x (by rw [show x + r - x = r by ring, abs_of_nonneg hr0]; linarith)
      rw [Real.norm_eq_abs] at h1 h2
      rw [htr]
      calc |Q (x + r + τ) - Q x| ≤ |Q (x + r + τ) - Q (x + r)| + |Q (x + r) - Q x| :=
            abs_sub_le _ _ _
        _ ≤ 2 * ε := by linarith
    have hfl := hfloor t (by linarith [ht.1]) (by
      have := (abs_le.mp hPt).2
      have := (abs_lt.mp hE).2
      linarith)
    have hQsmall : |Q t| < ε := by rw [show Q t = -F t by linarith, abs_neg]; exact hF
    have : |Q x| ≤ |Q x - Q t| + |Q t| := by
      calc |Q x| = |(Q x - Q t) + Q t| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_sub_comm] at this
    linarith
  -- choose the shell
  set c : ℝ := ρ * ε ^ 2 / (4 * (L + 1)) with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp (hsparse c hc)
  set W : ℝ := max (max W₀ T₀) (2 * (L + 1)) with hWdef
  have hWW₀ : W₀ ≤ W := le_trans (le_max_left _ _) (le_max_left _ _)
  have hWT : T₀ ≤ W := le_trans (le_max_right _ _) (le_max_left _ _)
  have hWL : 2 * (L + 1) ≤ W := le_max_right _ _
  have hW0 : 0 < W := by linarith
  have hint := hW₀ W hWW₀
  set K : ℕ := ⌊W / (L + 1)⌋₊ with hKdef
  have hKle : (K : ℝ) * (L + 1) ≤ W := by
    have := Nat.floor_le (show 0 ≤ W / (L + 1) by positivity)
    rwa [← hKdef, le_div_iff₀ (by linarith)] at this
  have hKgt : W / (L + 1) - 1 < K := by
    have := Nat.lt_floor_add_one (W / (L + 1)); rw [← hKdef] at this; linarith
  -- the windows
  have hchoose : ∀ k : ℕ, ∃ τ ∈ Icc (W - x + k * (L + 1)) (W - x + k * (L + 1) + L),
      (∀ y, ‖P (y + τ) - P y‖ ≤ ε) ∧ (∀ y, ‖Q (y + τ) - Q y‖ ≤ ε) := fun k => hL _
  choose τ hτmem hτP hτQ using hchoose
  set J : ℕ → Set ℝ := fun k => Icc (x + τ k) (x + τ k + ρ) with hJ
  have hJlo : ∀ k, W + k * (L + 1) ≤ x + τ k := fun k => by linarith [(hτmem k).1]
  have hJhi : ∀ k, x + τ k + ρ ≤ W + k * (L + 1) + L + 1 / 2 := fun k => by
    linarith [(hτmem k).2]
  have hsub : (⋃ k ∈ Finset.range K, J k) ⊆ Icc W (2 * W) := by
    intro t ht
    simp only [Set.mem_iUnion, Finset.mem_range] at ht
    obtain ⟨k, hk, htk⟩ := ht
    have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
    constructor
    · have := hJlo k; have : (0 : ℝ) ≤ k * (L + 1) := by positivity
      linarith [htk.1]
    · have := hJhi k
      nlinarith [htk.2]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range K)) J := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_iff]
    rintro t ⟨hti, htj⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      have := hJhi i; have := hJlo j
      nlinarith [hti.2, htj.1]
    · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      have := hJhi j; have := hJlo i
      nlinarith [htj.2, hti.1]
  -- every window carries mass at least `ρ ε²`
  have hwin : ∀ k, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal ρ ≤
      ∫⁻ t in J k, ENNReal.ofReal (E t ^ 2 + F t ^ 2) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k * (L + 1) := by positivity
    have hb := hbad (τ k) (hτP k) (hτQ k) (by linarith [hJlo k])
    calc ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal ρ
        = ∫⁻ _ in J k, ENNReal.ofReal (ε ^ 2) := by
          rw [setLIntegral_const, hJ, Real.volume_Icc, show x + τ k + ρ - (x + τ k) = ρ by ring]
      _ ≤ ∫⁻ t in J k, ENNReal.ofReal (E t ^ 2 + F t ^ 2) :=
          setLIntegral_mono' measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal (hb t ht)
  have htotal : (K : ENNReal) * (ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal ρ) ≤
      ENNReal.ofReal (c * W) := by
    calc (K : ENNReal) * (ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal ρ)
        = ∑ k ∈ Finset.range K, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal ρ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range K, ∫⁻ t in J k, ENNReal.ofReal (E t ^ 2 + F t ^ 2) :=
          Finset.sum_le_sum fun k _ => hwin k
      _ = ∫⁻ t in ⋃ k ∈ Finset.range K, J k, ENNReal.ofReal (E t ^ 2 + F t ^ 2) :=
          (lintegral_biUnion_finset hdisj (fun k _ => measurableSet_Icc) _).symm
      _ ≤ ∫⁻ t in Icc W (2 * W), ENNReal.ofReal (E t ^ 2 + F t ^ 2) := lintegral_mono_set hsub
      _ ≤ ENNReal.ofReal (c * W) := hint
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at htotal
  -- `K ≥ W/(2(L+1))` beats `c W = ρ ε² W / (4(L+1))`
  have hK2 : W / (2 * (L + 1)) ≤ K := by
    have : W / (2 * (L + 1)) ≤ W / (L + 1) - 1 := by
      rw [div_le_iff₀ (by positivity)]
      have : W / (L + 1) * (2 * (L + 1)) = 2 * W := by field_simp
      nlinarith
    linarith
  have hpos : 0 < ε ^ 2 * ρ := by positivity
  have : W / (2 * (L + 1)) * (ε ^ 2 * ρ) ≤ c * W := by
    calc W / (2 * (L + 1)) * (ε ^ 2 * ρ) ≤ K * (ε ^ 2 * ρ) := by gcongr
      _ ≤ c * W := htotal
  rw [hcdef] at this
  have hL1 : 0 < L + 1 := by linarith
  have : W * (ε ^ 2 * ρ) / (2 * (L + 1)) ≤ W * (ε ^ 2 * ρ) / (4 * (L + 1)) := by
    calc W * (ε ^ 2 * ρ) / (2 * (L + 1)) = W / (2 * (L + 1)) * (ε ^ 2 * ρ) := by ring
      _ ≤ ρ * ε ^ 2 / (4 * (L + 1)) * W := this
      _ = W * (ε ^ 2 * ρ) / (4 * (L + 1)) := by ring
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
  nlinarith [mul_pos hW0 hpos]

end GaloisForLFunctions.EulerFETransportTheory
