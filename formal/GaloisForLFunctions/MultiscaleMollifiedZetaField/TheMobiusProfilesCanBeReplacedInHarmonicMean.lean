import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheHarmonicEndpointHasVanishingMass
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedMobiusProfilesConvergeUniformly
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Replacing shifted Möbius profiles in harmonic mean

A fixed dilation translates the logarithmic coordinate by a quantity
that tends to zero. Compact uniform convergence handles the interior;
the bounded-profile estimate and high harmonic moments remove the endpoint.
The normalized power shift may vary with the cutoff.
-/

open Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The remaining logarithmic length after a fixed dilation and a harmonic atom. -/
def dilatedLogProfileCoordinate (a N d : ℕ) : ℝ :=
  1 - Real.log a / Real.log N - Real.log d / Real.log N

/-- Each retained dilated coordinate lies in the profile's unit interval. -/
theorem dilatedLogProfileCoordinate_mem_unit {a c N d : ℕ}
    (ha : 0 < a) (hac : a ≤ c) (hN : 1 < N) (hd : d ∈ Finset.Icc 1 (N / c)) :
    dilatedLogProfileCoordinate a N d ∈ Icc (0 : ℝ) 1 := by
  have hc : 0 < c := ha.trans_le hac
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have had : a * d ≤ N := by
    have hdc := (Nat.le_div_iff_mul_le hc).mp (Finset.mem_Icc.mp hd).2
    exact (Nat.mul_le_mul_right d hac).trans (by simpa only [Nat.mul_comm] using hdc)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hsum : Real.log (a : ℝ) + Real.log d ≤ Real.log N := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast had)
  have hdiv := (div_le_one hlog).mpr hsum
  have hapos := div_nonneg (Real.log_nonneg ha1) hlog.le
  have hdpos := div_nonneg (Real.log_nonneg hd1) hlog.le
  rw [add_div] at hdiv
  constructor <;> dsimp only [dilatedLogProfileCoordinate] <;> linarith only [hdiv, hapos, hdpos]

/-- A smooth shifted Möbius profile can be replaced by `P′−vP` in harmonic mean,
even when the normalized shift varies and the harmonic cutoff is dilated. -/
theorem tendsto_harmonicMean_abs_profile_error
    {P P₁ P₂ : ℝ → ℝ} (hP : ∀ x, HasDerivAt P (P₁ x) x)
    (hP₁ : ∀ x, HasDerivAt P₁ (P₂ x) x) (hc₂ : Continuous P₂) (hP0 : P 0 = 0)
    {a c : ℕ} (ha : 0 < a) (hac : a ≤ c)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun N : ℕ => normalizedHarmonicArray c N (fun d =>
      |normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) (v N) -
        (P₁ (1 - Real.log d / Real.log N) - v₀ * P (1 - Real.log d / Real.log N))|))
      atTop (𝓝 0) := by
  let V : ℝ := |v₀| + 1
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hv₀ : v₀ ∈ Icc (-V) V := by
    constructor <;> dsimp only [V]
    · linarith only [neg_abs_le v₀]
    · linarith only [le_abs_self v₀]
  have hvbound : ∀ᶠ N : ℕ in atTop, v N ∈ Icc (-V) V := by
    have hh := hv.eventually (Metric.ball_mem_nhds v₀ zero_lt_one)
    filter_upwards [hh] with N hN
    rw [Real.dist_eq] at hN
    obtain ⟨hl, hu⟩ := abs_lt.mp hN
    constructor <;> dsimp only [V] <;>
      linarith only [hl, hu, neg_abs_le v₀, le_abs_self v₀]
  have hcP : Continuous P := continuous_iff_continuousAt.mpr (fun x => (hP x).continuousAt)
  have hcP₁ : Continuous P₁ := continuous_iff_continuousAt.mpr (fun x => (hP₁ x).continuousAt)
  let g : ℝ × ℝ → ℝ := fun q => P₁ q.2 - q.1 * P q.2
  let K : Set (ℝ × ℝ) := Icc (-V) V ×ˢ Icc (0 : ℝ) 1
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have huc := hcompact.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨B, hB, hb⟩ := (normalizedShiftedMobiusProfile_compact_uniform hP hP₁ hc₂ hP0 hV).1
  have hi := (normalizedShiftedMobiusProfile_compact_uniform hP hP₁ hc₂ hP0 hV).2
  obtain ⟨D, hD⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  have hD0 : 0 ≤ D := (norm_nonneg (g (v₀, 0))).trans (hD (v₀, 0) ⟨hv₀, ⟨le_rfl, zero_le_one⟩⟩)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun N : ℕ => Real.log (a : ℝ) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  let e (N d : ℕ) :=
    normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) (v N) -
      g (v₀, 1 - Real.log d / Real.log N)
  change Tendsto (fun N : ℕ => normalizedHarmonicArray c N (fun d => |e N d|)) atTop (𝓝 0)
  apply tendsto_normalizedHarmonicArray_zero (ha.trans_le hac) (show 0 ≤ B + D by positivity)
  · filter_upwards [eventually_ge_atTop 2, hvbound] with N hN hvN
    intro d hd
    have hu := dilatedLogProfileCoordinate_mem_unit ha hac (by omega) hd
    have ht := harmonicLogCoordinate_mem_unit (by omega : 1 < N) hd
    have ht' : 1 - Real.log d / Real.log N ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith only [ht.1, ht.2]
    rw [abs_abs]
    exact (abs_sub _ _).trans (add_le_add
      (hb _ (Real.log_pos (by exact_mod_cast hN)) _ hu _ hvN)
      (by simpa only [Real.norm_eq_abs] using hD (v₀, _) ⟨hv₀, ht'⟩))
  · intro δ ε hδ hε
    obtain ⟨η, hη, hnear⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
    have hvnear : ∀ᶠ N : ℕ in atTop, dist (v N) v₀ < η :=
      hv.eventually (Metric.ball_mem_nhds v₀ hη)
    have hs : ∀ᶠ N : ℕ in atTop, Real.log (a : ℝ) / Real.log N < min (δ / 2) η :=
      hshift.eventually_lt_const (lt_min (half_pos hδ) hη)
    have hp := hlog.eventually (hi (δ / 2) (ε / 2) (half_pos hδ) (half_pos hε))
    filter_upwards [eventually_ge_atTop 2, hvbound, hvnear, hs, hp] with N hN hvN hvclose hsmall hprofile
    intro d hd haway
    have hu := dilatedLogProfileCoordinate_mem_unit ha hac (by omega) hd
    have ht := harmonicLogCoordinate_mem_unit (by omega : 1 < N) hd
    have ht' : 1 - Real.log d / Real.log N ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith only [ht.1, ht.2]
    have hshift0 : 0 ≤ Real.log (a : ℝ) / Real.log N :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast ha))
        (Real.log_pos (by exact_mod_cast hN)).le
    have hui : dilatedLogProfileCoordinate a N d ∈ Icc (δ / 2) 1 := by
      refine ⟨?_, hu.2⟩
      have hsδ := hsmall.trans_le (min_le_left _ _)
      dsimp only [dilatedLogProfileCoordinate]
      linarith only [haway, hsδ]
    have hdist : dist (v N, dilatedLogProfileCoordinate a N d)
        (v₀, 1 - Real.log d / Real.log N) < η := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨hvclose, ?_⟩
      rw [Real.dist_eq]
      have he : dilatedLogProfileCoordinate a N d - (1 - Real.log d / Real.log N) =
          -(Real.log a / Real.log N) := by dsimp only [dilatedLogProfileCoordinate]; ring
      rw [he, abs_neg, abs_of_nonneg hshift0]
      exact hsmall.trans_le (min_le_right _ _)
    have hgclose := hnear (v N, dilatedLogProfileCoordinate a N d) ⟨hvN, hu⟩
      (v₀, 1 - Real.log d / Real.log N) ⟨hv₀, ht'⟩ hdist
    have hpclose := hprofile _ hui _ hvN
    rw [Real.dist_eq] at hgclose
    rw [abs_abs]
    have he : e N d =
        (normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) (v N) -
          g (v N, dilatedLogProfileCoordinate a N d)) +
        (g (v N, dilatedLogProfileCoordinate a N d) - g (v₀, 1 - Real.log d / Real.log N)) := by
      dsimp only [e]; ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    have hh := add_lt_add hpclose hgclose
    dsimp only [g] at hh ⊢
    linarith only [hh]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
