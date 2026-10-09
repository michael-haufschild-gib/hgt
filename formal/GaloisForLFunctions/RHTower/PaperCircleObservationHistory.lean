import GaloisForLFunctions.RHTower.PaperCircleEnergyLocalization
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Thermal.Posterior

/-! # Observation histories for native circle energies

Arbitrary finite histories of native Gibbs observations have positive likelihood and
a Fourier envelope determined by their summed energy. Normalizing these likelihoods
gives actual finite posterior laws, with no admissibility or positivity assumptions.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleObservationProfile (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) : Thermal.Profile M :=
  s.map fun u => (paperCircleLocalizedForm a M k u.1, u.2)

theorem paperCircleObservationProfile_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    ∀ u ∈ paperCircleObservationProfile a M k s, 0 ≤ u.1 := by
  intro u hu
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
  exact paperCircleLocalizedForm_nonneg a M k v.1

/-- The spectral envelope depends on the total coupling and number of observations. -/
theorem paperCircleObservationProfile_mix (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    Thermal.mixForm (paperCircleObservationProfile a M k s) =
      (s.length : ℝ) • Thermal.S M (paperCircleLocalizationWidth M k) +
        ((s.map fun u => (u.1 : ℝ)).sum) • paperCircleGridEnergy a M := by
  induction s with
  | nil => simp [paperCircleObservationProfile, Thermal.mixForm]
  | cons u s ih =>
    simp only [paperCircleObservationProfile, List.map_cons, Thermal.mix_cons] at *
    rw [ih]
    ext x
    simp [paperCircleLocalizedForm]
    ring

def paperCircleHistoryLikelihood (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) (x : Grid M) : ℝ :=
  Thermal.tune (paperCircleObservationProfile a M k s) x

theorem paperCircleHistoryLikelihood_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    0 < paperCircleHistoryLikelihood a M k s x := Thermal.tune_pos _ _

theorem paperCircleHistoryLikelihood_cons (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (t : ℝ≥0) (z x : Grid M) :
    paperCircleHistoryLikelihood a M k ((t,z)::s) x =
      Thermal.boltz (paperCircleLocalizedForm a M k t) (z-x) *
        paperCircleHistoryLikelihood a M k s x :=
  Thermal.tune_cons _ _ _ _

theorem paperCircleHistoryEnergy_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    0 ≤ Thermal.sumE (paperCircleObservationProfile a M k s) x := by
  induction s with
  | nil => simp [paperCircleObservationProfile, Thermal.sumE]
  | cons u s ih =>
    exact add_nonneg (Thermal.form_nonneg (paperCircleLocalizedForm_nonneg a M k u.1) _) ih

theorem paperCircleHistoryLikelihood_le_one (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    paperCircleHistoryLikelihood a M k s x ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (paperCircleHistoryEnergy_nonneg a M k s x))

theorem paperCircleHistoryLikelihood_append (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s t : List (ℝ≥0 × Grid M)) (x : Grid M) :
    paperCircleHistoryLikelihood a M k (s++t) x =
      paperCircleHistoryLikelihood a M k s x * paperCircleHistoryLikelihood a M k t x := by
  simp [paperCircleHistoryLikelihood, Thermal.tune, Thermal.sumE,
    paperCircleObservationProfile, List.map_append, List.sum_append, Real.exp_add, mul_comm]

/-- Source profile envelope applied to actual native energies and arbitrary observation locations. -/
theorem paperCircleHistoryLikelihood_fourier (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (u : Grid M) :
    ‖fc (fun x => (paperCircleHistoryLikelihood a M k s x : ℂ)) u‖ ≤
      Thermal.q (Thermal.mixForm (paperCircleObservationProfile a M k s)) u :=
  Thermal.profile_envelope (paperCircleObservationProfile_nonneg a M k s) u

def paperCircleHistoryEvidence (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) : ℝ := expU (paperCircleHistoryLikelihood a M k s)

private theorem likelihood_sum_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    0 < ∑ x, paperCircleHistoryLikelihood a M k s x :=
  Finset.sum_pos (fun x _ => paperCircleHistoryLikelihood_pos a M k s x) Finset.univ_nonempty

theorem paperCircleHistoryEvidence_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    0 < paperCircleHistoryEvidence a M k s :=
  mul_pos (Period.side_pos M) (likelihood_sum_pos a M k s)

theorem paperCircleHistoryEvidence_le_one (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    paperCircleHistoryEvidence a M k s ≤ 1 := by
  rw [paperCircleHistoryEvidence, expU_ex, ← Law.Ex_const (Law.uniform (Grid M)) 1]
  exact Law.Ex_mono _ (paperCircleHistoryLikelihood_le_one a M k s)

def paperCircleHistoryPosterior (a : ι → CCMCircleBoundedSymbol) (M k : ℕ)
    (s : List (ℝ≥0 × Grid M)) : Law (Grid M) :=
  Law.proportional (paperCircleHistoryLikelihood a M k s)
    (fun x => (paperCircleHistoryLikelihood_pos a M k s x).le) (likelihood_sum_pos a M k s)

theorem paperCircleHistoryPosterior_apply (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    paperCircleHistoryPosterior a M k s x =
      Period.side M * paperCircleHistoryLikelihood a M k s x /
        paperCircleHistoryEvidence a M k s := by
  change _ / _ = _ / (Period.side M * _)
  field_simp [(Period.side_pos M).ne']

theorem paperCircleHistoryPosterior_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    0 < paperCircleHistoryPosterior a M k s x :=
  div_pos (paperCircleHistoryLikelihood_pos a M k s x) (likelihood_sum_pos a M k s)

theorem paperCircleHistoryPosterior_append_comm (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s t : List (ℝ≥0 × Grid M)) :
    paperCircleHistoryPosterior a M k (s++t) = paperCircleHistoryPosterior a M k (t++s) := by
  have h : paperCircleHistoryLikelihood a M k (s++t) =
      paperCircleHistoryLikelihood a M k (t++s) := by
    funext x
    rw [paperCircleHistoryLikelihood_append, paperCircleHistoryLikelihood_append, mul_comm]
  apply Law.ext
  intro x
  change paperCircleHistoryLikelihood a M k (s++t) x /
      (∑ y, paperCircleHistoryLikelihood a M k (s++t) y) =
    paperCircleHistoryLikelihood a M k (t++s) x /
      (∑ y, paperCircleHistoryLikelihood a M k (t++s) y)
  rw [h]

/-- The likelihood is the product of genuine channel probabilities, up to an input-independent factor. -/
theorem paperCircleHistory_channel_product (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    (s.map fun v => Thermal.channel (paperCircleLocalizedForm a M k v.1) x v.2).prod =
      (s.map fun v => Period.side M / Thermal.q (paperCircleLocalizedForm a M k v.1) 0).prod *
        paperCircleHistoryLikelihood a M k s x := by
  induction s with
  | nil => simp [paperCircleHistoryLikelihood, paperCircleObservationProfile, Thermal.tune,
      Thermal.sumE]
  | cons v s ih =>
    obtain ⟨t,z⟩ := v
    simp only [List.map_cons, List.prod_cons]
    rw [ih, paperCircleHistoryLikelihood_cons, Thermal.channel_apply,
      Thermal.label_apply, Thermal.K]
    ring

private theorem channel_factor_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) :
    0 < (s.map fun v => Period.side M / Thermal.q (paperCircleLocalizedForm a M k v.1) 0).prod := by
  induction s with
  | nil => simp
  | cons v s ih =>
    exact mul_pos (div_pos (Period.side_pos M) (Thermal.q_origin_pos _)) ih

/-- Bayes normalization of the actual observation probabilities is exactly this posterior. -/
theorem paperCircleHistoryPosterior_channel_product (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (x : Grid M) :
    paperCircleHistoryPosterior a M k s x =
      (s.map fun v => Thermal.channel (paperCircleLocalizedForm a M k v.1) x v.2).prod /
        ∑ y, (s.map fun v => Thermal.channel (paperCircleLocalizedForm a M k v.1) y v.2).prod := by
  simp_rw [paperCircleHistory_channel_product]
  rw [← Finset.mul_sum]
  change paperCircleHistoryLikelihood a M k s x /
    (∑ y, paperCircleHistoryLikelihood a M k s y) = _
  field_simp [(channel_factor_pos a M k s).ne']

theorem paperCircleHistoryPosterior_cx (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (f : Grid M → ℂ) :
    (paperCircleHistoryPosterior a M k s).Cx f =
      expU (fun x => (paperCircleHistoryLikelihood a M k s x : ℂ) * f x) /
        (paperCircleHistoryEvidence a M k s : ℂ) := by
  simp only [Law.Cx, paperCircleHistoryPosterior_apply, Complex.ofReal_div,
    Complex.ofReal_mul, expU, Complex.real_smul, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- History normalization gives a quantitative bound on every posterior character. -/
theorem paperCircleHistoryPosterior_fourier (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (u : Grid M) :
    ‖(paperCircleHistoryPosterior a M k s).Cx (chi (-u))‖ ≤
      Thermal.q (Thermal.mixForm (paperCircleObservationProfile a M k s)) u /
        paperCircleHistoryEvidence a M k s := by
  rw [paperCircleHistoryPosterior_cx, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (paperCircleHistoryEvidence_pos a M k s)]
  exact div_le_div_of_nonneg_right (paperCircleHistoryLikelihood_fourier a M k s u)
    (paperCircleHistoryEvidence_pos a M k s).le

/-- The evidence ratio is the current posterior's expected likelihood of the next observation. -/
theorem paperCircleHistoryEvidence_update (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (t : ℝ≥0) (z : Grid M) :
    paperCircleHistoryEvidence a M k ((t,z)::s) =
      paperCircleHistoryEvidence a M k s * (paperCircleHistoryPosterior a M k s).Ex
        (fun x => Thermal.boltz (paperCircleLocalizedForm a M k t) (z-x)) := by
  rw [paperCircleHistoryEvidence, expU_ex]
  simp only [Law.Ex, paperCircleHistoryLikelihood_cons, uniform_side,
    paperCircleHistoryPosterior_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(paperCircleHistoryEvidence_pos a M k s).ne']

theorem paperCircleHistoryPosterior_update (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (s : List (ℝ≥0 × Grid M)) (t : ℝ≥0) (z x : Grid M) :
    paperCircleHistoryPosterior a M k ((t,z)::s) x =
      paperCircleHistoryPosterior a M k s x *
        Thermal.boltz (paperCircleLocalizedForm a M k t) (z-x) /
          (paperCircleHistoryPosterior a M k s).Ex
            (fun y => Thermal.boltz (paperCircleLocalizedForm a M k t) (z-y)) := by
  have h := paperCircleHistoryEvidence_update a M k s t z
  have hp := paperCircleHistoryEvidence_pos a M k ((t,z)::s)
  have hq := paperCircleHistoryEvidence_pos a M k s
  have he : 0 < (paperCircleHistoryPosterior a M k s).Ex
      (fun y => Thermal.boltz (paperCircleLocalizedForm a M k t) (z-y)) := by
    rw [h] at hp
    exact (mul_pos_iff_of_pos_left hq).mp hp
  rw [paperCircleHistoryPosterior_apply, paperCircleHistoryLikelihood_cons, h,
    paperCircleHistoryPosterior_apply]
  field_simp

end
end RHTower
