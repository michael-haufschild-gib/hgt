import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheMobiusProfilesCanBeReplacedInHarmonicMean

/-!
# Products of Möbius profiles in harmonic mean

The common profile bound turns two separate mean-error estimates into
a product estimate. Multiplication by a normalized logarithmic power
preserves the estimate. Polynomial harmonic averages then reduce to the
already proved logarithmic moments.
-/

open Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem normalizedHarmonicArray_abs_le_linear {c N : ℕ} (hN : 1 < N)
    {e f g : ℕ → ℝ} {A B : ℝ}
    (hb : ∀ d ∈ Finset.Icc 1 (N / c), |e d| ≤ A * f d + B * g d) :
    |normalizedHarmonicArray c N e| ≤
      A * normalizedHarmonicArray c N f + B * normalizedHarmonicArray c N g := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  rw [normalizedHarmonicArray, abs_div, abs_of_pos hlog]
  calc
    _ ≤ (∑ d ∈ Finset.Icc 1 (N / c), |e d / (d : ℝ)|) / Real.log N :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hlog.le
    _ ≤ (∑ d ∈ Finset.Icc 1 (N / c), (A * f d + B * g d) / (d : ℝ)) / Real.log N := by
      apply div_le_div_of_nonneg_right _ hlog.le
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      exact div_le_div_of_nonneg_right (hb d hd) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [normalizedHarmonicArray, add_div, mul_div_assoc,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- Products of shifted smooth profiles have the product of their limiting transforms
in harmonic mean, also after multiplication by any fixed logarithmic power. -/
theorem tendsto_harmonicMean_profile_product_error
    {P P₁ P₂ Q Q₁ Q₂ : ℝ → ℝ}
    (hP : ∀ x, HasDerivAt P (P₁ x) x) (hP₁ : ∀ x, HasDerivAt P₁ (P₂ x) x)
    (hcP₂ : Continuous P₂) (hP0 : P 0 = 0)
    (hQ : ∀ x, HasDerivAt Q (Q₁ x) x) (hQ₁ : ∀ x, HasDerivAt Q₁ (Q₂ x) x)
    (hcQ₂ : Continuous Q₂) (hQ0 : Q 0 = 0)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbc : b ≤ c)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (m : ℕ) :
    Tendsto (fun N : ℕ => normalizedHarmonicArray c N (fun d =>
      (Real.log d / Real.log N) ^ m *
        (normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) (v N) *
          normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) (v N) -
        (P₁ (1 - Real.log d / Real.log N) - v₀ * P (1 - Real.log d / Real.log N)) *
          (Q₁ (1 - Real.log d / Real.log N) - v₀ * Q (1 - Real.log d / Real.log N)))))
      atTop (𝓝 0) := by
  let KP (N d : ℕ) := normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) (v N)
  let KQ (N d : ℕ) := normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) (v N)
  let GP (N d : ℕ) := P₁ (1 - Real.log d / Real.log N) - v₀ * P (1 - Real.log d / Real.log N)
  let GQ (N d : ℕ) := Q₁ (1 - Real.log d / Real.log N) - v₀ * Q (1 - Real.log d / Real.log N)
  have heP := tendsto_harmonicMean_abs_profile_error hP hP₁ hcP₂ hP0 ha hac hv
  have heQ := tendsto_harmonicMean_abs_profile_error hQ hQ₁ hcQ₂ hQ0 hb hbc hv
  let V : ℝ := |v₀| + 1
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  obtain ⟨B, hB, hbound⟩ := (normalizedShiftedMobiusProfile_compact_uniform hP hP₁ hcP₂ hP0 hV).1
  have hvbound : ∀ᶠ N : ℕ in atTop, v N ∈ Icc (-V) V := by
    have hh := hv.eventually (Metric.ball_mem_nhds v₀ zero_lt_one)
    filter_upwards [hh] with N hN
    rw [Metric.mem_ball, Real.dist_eq] at hN
    obtain ⟨hl, hu⟩ := abs_lt.mp hN
    constructor <;> dsimp only [V] <;>
      linarith only [hl, hu, neg_abs_le v₀, le_abs_self v₀]
  have hcQ : Continuous Q := continuous_iff_continuousAt.mpr (fun x => (hQ x).continuousAt)
  have hcQ₁ : Continuous Q₁ := continuous_iff_continuousAt.mpr (fun x => (hQ₁ x).continuousAt)
  have hcg : Continuous (fun x => Q₁ x - v₀ * Q x) := by fun_prop
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hcg.continuousOn
  have hD0 : 0 ≤ D := (norm_nonneg (Q₁ 0 - v₀ * Q 0)).trans (hD 0 ⟨le_rfl, zero_le_one⟩)
  have hlimit : Tendsto (fun N : ℕ =>
      B * normalizedHarmonicArray c N (fun d => |KQ N d - GQ N d|) +
      D * normalizedHarmonicArray c N (fun d => |KP N d - GP N d|)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (heQ.const_mul B).add (heP.const_mul D)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [eventually_ge_atTop 2, hvbound, hlimit.eventually_lt_const hε] with N hN hvN hsmall
  rw [Real.dist_eq, sub_zero]
  refine (normalizedHarmonicArray_abs_le_linear (by omega : 1 < N) ?_).trans_lt hsmall
  intro d hd
  have hu := dilatedLogProfileCoordinate_mem_unit ha hac (by omega) hd
  have ht := harmonicLogCoordinate_mem_unit (by omega : 1 < N) hd
  have ht' : 1 - Real.log d / Real.log N ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith only [ht.1, ht.2]
  have hKP : |KP N d| ≤ B := hbound _ (Real.log_pos (by exact_mod_cast hN)) _ hu _ hvN
  have hGQ : |GQ N d| ≤ D := by simpa only [Real.norm_eq_abs] using hD _ ht'
  have he : KP N d * KQ N d - GP N d * GQ N d =
      KP N d * (KQ N d - GQ N d) + (KP N d - GP N d) * GQ N d := by ring
  have hprod : |KP N d * KQ N d - GP N d * GQ N d| ≤
      B * |KQ N d - GQ N d| + D * |KP N d - GP N d| := by
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hh := add_le_add (mul_le_mul_of_nonneg_right hKP (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hGQ (abs_nonneg _))
    simpa only [mul_comm] using hh
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 _)]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1 ht.2) (abs_nonneg _)).trans
    (by simpa only [one_mul] using hprod)

/-- A finite polynomial in the normalized harmonic logarithm has its unit-interval moment. -/
theorem tendsto_normalizedHarmonicArray_polynomial (s : Finset ℕ) (w : ℕ → ℝ)
    {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => normalizedHarmonicArray c N
      (fun d => ∑ j ∈ s, w j * (Real.log d / Real.log N) ^ j))
      atTop (𝓝 (∑ j ∈ s, w j / ((j : ℝ) + 1))) := by
  have hh := tendsto_finsetSum s (fun j _ => (tendsto_normalizedHarmonicLogMoment j hc).const_mul (w j))
  simp only [mul_one_div] at hh
  convert hh using 1
  funext N
  simp only [normalizedHarmonicArray, normalizedHarmonicLogMoment, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
