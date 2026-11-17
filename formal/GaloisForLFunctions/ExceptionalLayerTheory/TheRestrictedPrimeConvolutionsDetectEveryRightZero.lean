import GaloisForLFunctions.ExceptionalLayerTheory.TheShortVaughanCofactorAtAZetaZero

/-!
# Detection of right-hand zeros by restricted prime convolutions

The long prime factor loses only an entire Dirichlet polynomial when a
finite head is removed. Its pole at a zero thus survives precisely when
the short cofactor has nonzero symbol there. For each right-hand zero,
one of the two cofactor cutoffs `V²` and `2V²` detects the pole for every
sufficiently large `V`, regardless of the long prime cutoff.
-/

noncomputable section

open Complex Finset ArithmeticFunction Filter Topology
open scoped LSeries.notation
open RHTower.Sieve hiding dirPoly
open RHTower.WeilFiniteType
open GaloisForLFunctions.TransHorizonIncidenceMechanics (partialSumRate)

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Continued Dirichlet series for the restricted long-prime, short-cofactor convolution. -/
def restrictedPrimeSeries (U V W : ℕ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s - dirPoly U vonMangoldt s) * dirPoly W (typeIIShort V) s

private theorem supported_truncation (f : ArithmeticFunction ℝ) (W : ℕ) :
    SupportedIn W (truncAF f W) := ⟨ArithmeticFunction.map_zero,
      fun _ h => truncAF_apply_of_gt h⟩

private theorem lseries_truncation (f : ArithmeticFunction ℝ) (W : ℕ) (s : ℂ) :
    LSeries (fun n => ((truncAF f W n : ℝ) : ℂ)) s = dirPoly W f s := by
  rw [LSeries_eq_dirPoly (supported_truncation f W)]
  unfold dirPoly
  exact sum_congr rfl fun n hn => by rw [truncAF_apply, if_pos (mem_Icc.mp hn).2]

/-- On the Euler half-plane the continuation is the literal Dirichlet series
of the same truncated convolution that occurs in the Gaussian prime current. -/
theorem lseries_restrictedPrimeConvolution {s : ℂ} (hs : 1 < s.re) (U V W : ℕ) :
    LSeries (fun n => (((typeIILong U * truncAF (typeIIShort V) W) n : ℝ) : ℂ)) s =
      restrictedPrimeSeries U V W s := by
  let head := truncAF (vonMangoldt : ArithmeticFunction ℝ) U
  let short := truncAF (typeIIShort V) W
  have hconv : (fun n => (((typeIILong U * short) n : ℝ) : ℂ)) =
      (fun n => ((typeIILong U n : ℝ) : ℂ)) ⍟ fun n => ((short n : ℝ) : ℂ) := by
    funext n
    rw [LSeries.convolution_def]
    exact coe_mul_apply _ _ _
  have hlong : (fun n => ((typeIILong U n : ℝ) : ℂ)) =
      (fun n => (vonMangoldt n : ℂ)) - fun n => ((head n : ℝ) : ℂ) := by
    funext n
    exact Complex.ofReal_sub _ _
  have hhead := LSeriesSummable_of_supportedIn (supported_truncation vonMangoldt U) s
  have hshort := LSeriesSummable_of_supportedIn (supported_truncation (typeIIShort V) W) s
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  change LSeries (fun n => (((typeIILong U * short) n : ℝ) : ℂ)) s = _
  rw [hconv, hlong, LSeries_convolution' (hΛ.sub hhead) hshort, LSeries_sub hΛ hhead,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact congrArg₂ (· * ·) (congrArg (_ - ·) (lseries_truncation vonMangoldt U s))
    (lseries_truncation (typeIIShort V) W s)

/-- One positive multiplicity works for every truncation of both factors. -/
theorem restrictedPrimeSeries_residue_at_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) :
    ∃ m : ℕ, 0 < m ∧ ∀ U V W : ℕ,
      Tendsto (fun s => (s - ρ) * restrictedPrimeSeries U V W s) (𝓝[≠] ρ)
        (𝓝 (-(m : ℂ) * dirPoly W (typeIIShort V) ρ)) := by
  obtain ⟨m, hm, hres⟩ := RHTower.neg_logDeriv_zeta_zero_residue hz
  refine ⟨m, hm, fun U V W => ?_⟩
  have hlin : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' ρ 0 (sub_self ρ)).mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hh := ((differentiable_dirPoly U vonMangoldt ρ).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hb := ((differentiable_dirPoly W (typeIIShort V) ρ).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have he : Tendsto (fun s => (s - ρ) * dirPoly U vonMangoldt s) (𝓝[≠] ρ) (𝓝 0) := by
    simpa only [zero_mul] using hlin.mul hh
  convert (hres.sub he).mul hb using 1
  · funext s
    unfold restrictedPrimeSeries
    ring
  · rw [sub_zero]

/-- At a right-hand strip zero the two raw cofactor symbols cannot both vanish
once the cofactor cutoff reaches the square of the Möbius cutoff. -/
theorem eventually_dyadic_shortCofactor_detects_zero {ρ : ℂ}
    (hhalf : 1 / 2 < ρ.re) (hone : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∀ᶠ V : ℕ in atTop, ∀ W : ℕ, V ^ 2 ≤ W →
      dirPoly W (typeIIShort V) ρ ≠ 0 ∨ dirPoly (2 * W) (typeIIShort V) ρ ≠ 0 := by
  let r := (2 : ℂ) ^ (1 - ρ)
  have hσ : 0 < ρ.re := by linarith only [hhalf]
  have hρ1 := RHTower.riemannZeta_zero_ne_one hz
  have hnorm : 1 < ‖r‖ := by
    change 1 < ‖((2 : ℝ) : ℂ) ^ (1 - ρ)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), sub_re, one_re]
    exact Real.one_lt_rpow (by norm_num) (sub_pos.mpr hone)
  have hgap : 0 < ‖1 - r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => by
    rw [← h, norm_one] at hnorm
    exact lt_irrefl _ hnorm))
  have hlim := (tendsto_rpow_neg_atTop (by linarith only [hhalf] : 0 < 2 * ρ.re - 1)).comp
    tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun v : ℕ => ((1 + ‖r‖) * partialSumRate ρ) *
      (v : ℝ) ^ (-(2 * ρ.re - 1))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using hlim.const_mul ((1 + ‖r‖) * partialSumRate ρ)
  filter_upwards [eventually_ge_atTop 1, herr.eventually_lt_const hgap] with V hV hsmall
  intro W hW
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hVW : V ≤ W := (Nat.le_self_pow (by decide : 2 ≠ 0) V).trans hW
  have hdec := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hV0)
    (by exact_mod_cast hW : (V : ℝ) ^ 2 ≤ W) (neg_nonpos.mpr hσ.le)
  have he := norm_dyadic_shortCofactor_sub_le (hV.trans hVW) hVW hσ hρ1 hz
  dsimp only at he
  by_contra! hboth
  simp only [hboth.1, hboth.2, mul_zero, sub_zero, zero_sub, norm_neg] at he
  have hcost : (V : ℝ) * (((V : ℝ) ^ 2) ^ (-ρ.re)) = (V : ℝ) ^ (-(2 * ρ.re - 1)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hV0.le, mul_comm, ← Real.rpow_add_one hV0.ne']
    congr 1
    ring
  have hupper := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hdec
      (TransHorizonIncidenceMechanics.partialSumRate_nonneg hσ)) hV0.le)
    (show 0 ≤ 1 + ‖r‖ by positivity)
  have hbound : ‖1 - r‖ ≤ ((1 + ‖r‖) * partialSumRate ρ) *
      (V : ℝ) ^ (-(2 * ρ.re - 1)) := by
    rw [← hcost]
    exact (he.trans hupper).trans_eq (by ring)
  exact (not_lt_of_ge hbound) hsmall

/-- RH is equivalent to simultaneous disappearance of the two prime residues
at arbitrarily large cutoffs, pointwise in the open right half of the strip.
The prime head may be removed at an arbitrary finite cutoff at each scale. -/
theorem riemannHypothesis_iff_cofinal_restrictedPrimeResidues (U : ℕ → ℕ) :
    RiemannHypothesis ↔ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
      ∃ᶠ V : ℕ in atTop, ∀ W ∈ ({V ^ 2, 2 * V ^ 2} : Finset ℕ),
        Tendsto (fun s => (s - ρ) * restrictedPrimeSeries (U V) V W s) (𝓝[≠] ρ) (𝓝 0) := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro hRH ρ hlo hhi
    have hρ1 : ρ ≠ 1 := fun h => by simp [h] at hhi
    have hreg := RHTower.differentiableAt_neg_logDeriv_riemannZeta hρ1 (hRH ρ hlo hhi)
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro V W _
    have hc : ContinuousAt (restrictedPrimeSeries (U V) V W) ρ := by
      unfold restrictedPrimeSeries
      exact (hreg.continuousAt.sub (differentiable_dirPoly (U V) vonMangoldt ρ).continuousAt).mul
        (differentiable_dirPoly W (typeIIShort V) ρ).continuousAt
    have hlin : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
      ((continuous_id.sub continuous_const).tendsto' ρ 0 (sub_self ρ)).mono_left
      (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
    simpa only [zero_mul] using hlin.mul
      (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ))))
  · intro hc ρ hlo hhi hz
    obtain ⟨m, hm, hres⟩ := restrictedPrimeSeries_residue_at_zero hz
    obtain ⟨V, hV, hdet⟩ := ((hc ρ hlo hhi).and_eventually
      (eventually_dyadic_shortCofactor_detects_zero hlo hhi hz)).exists
    have hzero (W : ℕ) (hW : W ∈ ({V ^ 2, 2 * V ^ 2} : Finset ℕ)) :
        dirPoly W (typeIIShort V) ρ = 0 := by
      have := tendsto_nhds_unique (hres (U V) V W) (hV W hW)
      exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne'))
    rcases hdet _ le_rfl with h | h
    · exact h (hzero _ (by simp))
    · exact h (hzero _ (by simp))

end GaloisForLFunctions.ExceptionalLayerTheory
