import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesSourceNoPositiveWinding
import GaloisForLFunctions.RHTower.HedenmalmStokesOrientedFirstTraceQuantizedJump
import GaloisForLFunctions.RHTower.AnharmonicChebyshevNoetherCasimir

/-!
# Completed prime--Gamma identification of native Stokes spectral flow

Raw critical reciprocal-gap carrier cannot equal completed CCM seam germ: its central and first
moments are already too large. Correct Fredholm invariant does not require false coefficient
identity. It requires continuous zero-avoiding homotopy after coefficient-faithful source
completion.

This module adds exact higher-valuation/Gamma countercurrent to valuation-one Stokes current. Sum
is pointwise existing completed prime--Gamma current, including removable wall. Only afterward it
is identified with completed Xi logarithmic derivative on real Euler ray. Positivity of real Xi
logarithmic derivative fixes downward orientation without zero-location input.

Native reflected Stokes path and completed source path have unique center zero, common winding
`-1`, and continuous convex homotopy preserving every noncentral sign on canonical half-chamber.
Thus source winding, completed CCM/prime--Gamma crossing winding, and Hardy/Fredholm index agree
exactly. No RH premise, numerical estimate, computation, or added postulate enters.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators

noncomputable section
namespace RHTower

def gammaSewnCriticalCompletedPrimeGammaCrossingFlow (t : ℝ) : ℝ :=
  gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t +
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t

def gammaSewnCriticalCompletedPrimeGammaCrossingWinding : ℤ :=
  scalarUniqueCrossingWinding
    (gammaSewnCriticalCompletedPrimeGammaCrossingFlow (-1 / 2))
    (gammaSewnCriticalCompletedPrimeGammaCrossingFlow (1 / 2))

def gammaSewnCriticalStokesCompletedCrossingHomotopy (u t : ℝ) : ℝ :=
  (1 - u) * gammaSewnCriticalStokesSpectralFlow t +
    u * gammaSewnCriticalCompletedPrimeGammaCrossingFlow t

theorem gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_completedCurrent
    (t : ℝ) :
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow t =
      gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent t := by
  by_cases ht : t = 0
  · subst t
    simp [gammaSewnCriticalCompletedPrimeGammaCrossingFlow,
      gammaSewnMobiusApertureStokesOrientedPolarCountercurrent]
  · exact (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_eq_firstTrace_add_counter
      t ht).symm

theorem gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_xiRealLogDeriv
    (t : ℝ) :
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow t =
      -8 * t * xiRealLogDeriv (1 / 2 + 2 * |t|) := by
  rw [gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_completedCurrent]
  by_cases ht : t = 0
  · subst t
    simp
  · have habs : 0 < |t| := abs_pos.mpr ht
    have hs : (1 : ℝ) < 1 + 2 * |t| := by linarith
    have hflux :
        completedPrimeGammaFlux (((1 + 2 * |t| : ℝ) : ℂ)) =
          seamFluxCochain (((1 + 2 * |t| : ℝ) : ℂ)) := by
      rw [completedPrimeGammaFlux,
        seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re]
      simpa using hs
    have harg :
        (1 / 2 : ℂ) + (((1 / 2 + 2 * |t| : ℝ) : ℂ)) =
          (((1 + 2 * |t| : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent,
      hflux, seamFluxCochain, xiRealLogDeriv, harg]
    simp only [Complex.neg_re]
    ring

theorem gammaSewnCriticalCompletedPrimeGammaCrossingFlow_pos_of_neg
    {t : ℝ} (ht : t < 0) :
    0 < gammaSewnCriticalCompletedPrimeGammaCrossingFlow t := by
  rw [gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_xiRealLogDeriv]
  have harg : 0 < 1 / 2 + 2 * |t| := by positivity
  have hxi := xiRealLogDeriv_pos harg
  nlinarith

theorem gammaSewnCriticalCompletedPrimeGammaCrossingFlow_neg_of_pos
    {t : ℝ} (ht : 0 < t) :
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow t < 0 := by
  rw [gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_xiRealLogDeriv]
  have harg : 0 < 1 / 2 + 2 * |t| := by positivity
  have hxi := xiRealLogDeriv_pos harg
  nlinarith

@[simp] theorem gammaSewnCriticalCompletedPrimeGammaCrossingFlow_zero :
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow 0 = 0 := by
  rw [gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_xiRealLogDeriv]
  ring

theorem gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_zero_iff
    (t : ℝ) :
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow t = 0 ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · exact (ne_of_gt
        (gammaSewnCriticalCompletedPrimeGammaCrossingFlow_pos_of_neg htneg)) h
    · exact (ne_of_lt
        (gammaSewnCriticalCompletedPrimeGammaCrossingFlow_neg_of_pos htpos)) h
  · rintro rfl
    exact gammaSewnCriticalCompletedPrimeGammaCrossingFlow_zero

@[simp] theorem gammaSewnCriticalCompletedPrimeGammaCrossingFlow_neg
    (t : ℝ) :
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow (-t) =
      -gammaSewnCriticalCompletedPrimeGammaCrossingFlow t := by
  simp [gammaSewnCriticalCompletedPrimeGammaCrossingFlow]
  ring

theorem gammaSewnCriticalCompletedPrimeGammaCrossingWinding_eq_neg_one :
    gammaSewnCriticalCompletedPrimeGammaCrossingWinding = -1 := by
  have hdown :
      0 < gammaSewnCriticalCompletedPrimeGammaCrossingFlow (-1 / 2) ∧
        gammaSewnCriticalCompletedPrimeGammaCrossingFlow (1 / 2) < 0 :=
    ⟨gammaSewnCriticalCompletedPrimeGammaCrossingFlow_pos_of_neg (by norm_num),
      gammaSewnCriticalCompletedPrimeGammaCrossingFlow_neg_of_pos (by norm_num)⟩
  rw [gammaSewnCriticalCompletedPrimeGammaCrossingWinding,
    scalarUniqueCrossingWinding, if_pos hdown]

theorem gammaSewnCriticalStokesSourceWinding_eq_completedPrimeGammaCrossingWinding :
    gammaSewnCriticalStokesSourceWinding =
      gammaSewnCriticalCompletedPrimeGammaCrossingWinding := by
  rw [gammaSewnCriticalStokesSourceWinding_eq_neg_one,
    gammaSewnCriticalCompletedPrimeGammaCrossingWinding_eq_neg_one]

private theorem gammaSewnCriticalStokes_denominator_three_quarters_le
    {t : ℝ} (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2))
    (pk : Nat.Primes × ℕ) :
    (3 / 4 : ℝ) ≤
      1 - (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2 := by
  have ha := gammaSewnCriticalStokesNormalizedNode_mem_unit pk
  have htAbs : |t| ≤ (1 / 2 : ℝ) :=
    (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
  have hatAbs :
      |gammaSewnCriticalStokesNormalizedNode pk * t| ≤ (1 / 2 : ℝ) := by
    rw [abs_mul, abs_of_pos ha.1]
    calc
      gammaSewnCriticalStokesNormalizedNode pk * |t| ≤ 1 * |t| := by
        exact mul_le_mul_of_nonneg_right ha.2 (abs_nonneg t)
      _ ≤ 1 / 2 := by simpa using htAbs
  have hsq :
      (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hatAbs
  nlinarith

theorem continuousOn_gammaSewnCriticalStokesSpectralFlow_halfChamber :
    ContinuousOn gammaSewnCriticalStokesSpectralFlow
      (Set.Icc (-1 / 2 : ℝ) (1 / 2)) := by
  change ContinuousOn
    (fun t : ℝ => ∑' pk : Nat.Primes × ℕ,
      gammaSewnCriticalStokesSpectralAtom t pk)
    (Set.Icc (-1 / 2 : ℝ) (1 / 2))
  have hweights :=
    summable_gammaSewnMobiusApertureStokesSignedWeight
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hbase :
      Summable (fun pk : Nat.Primes × ℕ =>
        gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk) := by
    have hcomp := hweights.comp_injective
      (fun _ _ h => Sum.inl.inj h)
    exact hcomp.congr (fun _ => rfl)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine continuousOn_tsum (u := fun pk : Nat.Primes × ℕ =>
      2 * Real.log 2 * gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk)
      (fun pk => ?_) (hbase.mul_left (2 * Real.log 2)) ?_
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      exact ne_of_gt ((by norm_num : (0 : ℝ) < 3 / 4).trans_le
        (gammaSewnCriticalStokes_denominator_three_quarters_le ht pk))
  · intro pk t ht
    have hdenLower :=
      gammaSewnCriticalStokes_denominator_three_quarters_le ht pk
    have hden :
        0 < 1 - (gammaSewnCriticalStokesNormalizedNode pk * t) ^ 2 :=
      (by norm_num : (0 : ℝ) < 3 / 4).trans_le hdenLower
    have htAbs : |t| ≤ (1 / 2 : ℝ) :=
      (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
    have hw := gammaSewnMobiusApertureStokesReflectedWeight_pos
      (s := (1 / 2 : ℝ)) (by norm_num) pk
    rw [gammaSewnCriticalStokesSpectralAtom, Real.norm_eq_abs, abs_div,
      abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hw, abs_of_pos hlog,
      abs_of_pos hden, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      div_le_iff₀ hden]
    nlinarith [mul_pos hw hlog]

private theorem continuous_xiRealLogDeriv : Continuous xiRealLogDeriv := by
  rw [continuous_iff_continuousAt]
  intro w
  change ContinuousAt
    (fun x : ℝ => (logDeriv xi ((1 / 2 : ℂ) + (x : ℂ))).re) w
  have harg : ContinuousAt
      (fun x : ℝ => (1 / 2 : ℂ) + (x : ℂ)) w := by
    fun_prop
  have hargReal :
      (1 / 2 : ℂ) + (w : ℂ) = (((1 / 2 + w : ℝ) : ℂ)) := by
    push_cast
    ring
  have hxi : xi ((1 / 2 : ℂ) + (w : ℂ)) ≠ 0 := by
    rw [hargReal]
    exact xi_ne_zero_of_real (1 / 2 + w)
  have hlog : ContinuousAt
      (fun x : ℝ => logDeriv xi ((1 / 2 : ℂ) + (x : ℂ))) w :=
    ContinuousAt.comp (g := logDeriv xi)
      (f := fun x : ℝ => (1 / 2 : ℂ) + (x : ℂ))
      (differentiableAt_logDeriv_xi hxi).continuousAt harg
  exact Complex.continuous_re.continuousAt.comp hlog

theorem continuous_gammaSewnCriticalCompletedPrimeGammaCrossingFlow :
    Continuous gammaSewnCriticalCompletedPrimeGammaCrossingFlow := by
  have hfun : gammaSewnCriticalCompletedPrimeGammaCrossingFlow =
      fun t : ℝ => -8 * t * xiRealLogDeriv (1 / 2 + 2 * |t|) := by
    funext t
    exact gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_xiRealLogDeriv t
  rw [hfun]
  exact (continuous_const.mul continuous_id).mul
    (continuous_xiRealLogDeriv.comp (by fun_prop))

theorem continuousOn_gammaSewnCriticalStokesCompletedCrossingHomotopy_halfChamber :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        gammaSewnCriticalStokesCompletedCrossingHomotopy p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2)) := by
  let S := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2)
  have hu : ContinuousOn (fun p : ℝ × ℝ => p.1) S :=
    continuous_fst.continuousOn
  have ht : ContinuousOn (fun p : ℝ × ℝ => p.2) S :=
    continuous_snd.continuousOn
  have hnative : ContinuousOn
      (fun p : ℝ × ℝ => gammaSewnCriticalStokesSpectralFlow p.2) S :=
    continuousOn_gammaSewnCriticalStokesSpectralFlow_halfChamber.comp ht
      (fun p hp => hp.2)
  have hcompleted : ContinuousOn
      (fun p : ℝ × ℝ =>
        gammaSewnCriticalCompletedPrimeGammaCrossingFlow p.2) S :=
    continuous_gammaSewnCriticalCompletedPrimeGammaCrossingFlow.continuousOn.comp ht
      (fun p _hp => Set.mem_univ p.2)
  change ContinuousOn
    (fun p : ℝ × ℝ =>
      (1 - p.1) * gammaSewnCriticalStokesSpectralFlow p.2 +
        p.1 * gammaSewnCriticalCompletedPrimeGammaCrossingFlow p.2) S
  exact ((continuousOn_const.sub hu).mul hnative).add (hu.mul hcompleted)

@[simp] theorem gammaSewnCriticalStokesCompletedCrossingHomotopy_zero_left
    (t : ℝ) :
    gammaSewnCriticalStokesCompletedCrossingHomotopy 0 t =
      gammaSewnCriticalStokesSpectralFlow t := by
  simp [gammaSewnCriticalStokesCompletedCrossingHomotopy]

@[simp] theorem gammaSewnCriticalStokesCompletedCrossingHomotopy_one_left
    (t : ℝ) :
    gammaSewnCriticalStokesCompletedCrossingHomotopy 1 t =
      gammaSewnCriticalCompletedPrimeGammaCrossingFlow t := by
  simp [gammaSewnCriticalStokesCompletedCrossingHomotopy]

theorem gammaSewnCriticalStokesCompletedCrossingHomotopy_pos_of_neg
    {u t : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    0 < gammaSewnCriticalStokesCompletedCrossingHomotopy u t := by
  have hnative := gammaSewnCriticalStokesSpectralFlow_center_sign.1 t ht
  have hcompleted :=
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow_pos_of_neg ht.2
  rw [gammaSewnCriticalStokesCompletedCrossingHomotopy]
  have hleft :
      0 ≤ (1 - u) * gammaSewnCriticalStokesSpectralFlow t :=
    mul_nonneg (sub_nonneg.mpr hu.2) hnative.le
  by_cases hu0 : u = 0
  · simp [hu0, hnative]
  · exact add_pos_of_nonneg_of_pos hleft
      (mul_pos (lt_of_le_of_ne hu.1 (Ne.symm hu0)) hcompleted)

theorem gammaSewnCriticalStokesCompletedCrossingHomotopy_neg_of_pos
    {u t : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    gammaSewnCriticalStokesCompletedCrossingHomotopy u t < 0 := by
  have hnative := gammaSewnCriticalStokesSpectralFlow_center_sign.2 t ht
  have hcompleted :=
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow_neg_of_pos ht.1
  rw [gammaSewnCriticalStokesCompletedCrossingHomotopy]
  have hleft :
      (1 - u) * gammaSewnCriticalStokesSpectralFlow t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu.2) hnative.le
  by_cases hu0 : u = 0
  · simp [hu0, hnative]
  · exact add_neg_of_nonpos_of_neg hleft
      (mul_neg_of_pos_of_neg (lt_of_le_of_ne hu.1 (Ne.symm hu0)) hcompleted)

@[simp] theorem gammaSewnCriticalStokesCompletedCrossingHomotopy_zero
    (u : ℝ) :
    gammaSewnCriticalStokesCompletedCrossingHomotopy u 0 = 0 := by
  rw [gammaSewnCriticalStokesCompletedCrossingHomotopy,
    gammaSewnCriticalStokesSpectralFlow_zero,
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow_zero]
  ring

theorem gammaSewnCriticalStokesCompletedCrossingHomotopy_eq_zero_iff
    {u t : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    gammaSewnCriticalStokesCompletedCrossingHomotopy u t = 0 ↔ t = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy t 0 with htneg | hzero | htpos
    · have hpos := gammaSewnCriticalStokesCompletedCrossingHomotopy_pos_of_neg
        hu ⟨ht.1, htneg⟩
      exact (ne_of_gt hpos h).elim
    · exact hzero
    · have hneg := gammaSewnCriticalStokesCompletedCrossingHomotopy_neg_of_pos
        hu ⟨htpos, ht.2⟩
      exact (ne_of_lt hneg h).elim
  · rintro rfl
    exact gammaSewnCriticalStokesCompletedCrossingHomotopy_zero u

theorem gammaSewnCriticalStokesCompletedPrimeGammaSpectralFlowIdentification :
    (∀ t : ℝ,
      gammaSewnCriticalCompletedPrimeGammaCrossingFlow t =
        gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent t) ∧
    (∀ t : ℝ,
      gammaSewnCriticalCompletedPrimeGammaCrossingFlow t =
        -8 * t * xiRealLogDeriv (1 / 2 + 2 * |t|)) ∧
    gammaSewnCriticalStokesSourceWinding =
      gammaSewnCriticalCompletedPrimeGammaCrossingWinding ∧
    gammaSewnCriticalCompletedPrimeGammaCrossingWinding = -1 ∧
    gammaSewnCriticalCompletedPrimeGammaCrossingWinding =
      gammaSewnCriticalStokesFredholmSpectralFlow ∧
    ContinuousOn
      (fun p : ℝ × ℝ =>
        gammaSewnCriticalStokesCompletedCrossingHomotopy p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2)) ∧
    (∀ t : ℝ,
      gammaSewnCriticalStokesCompletedCrossingHomotopy 0 t =
          gammaSewnCriticalStokesSpectralFlow t ∧
        gammaSewnCriticalStokesCompletedCrossingHomotopy 1 t =
          gammaSewnCriticalCompletedPrimeGammaCrossingFlow t) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      gammaSewnCriticalStokesCompletedCrossingHomotopy u t = 0 ↔ t = 0) := by
  refine ⟨gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_completedCurrent,
    gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_xiRealLogDeriv,
    gammaSewnCriticalStokesSourceWinding_eq_completedPrimeGammaCrossingWinding,
    gammaSewnCriticalCompletedPrimeGammaCrossingWinding_eq_neg_one, ?_,
    continuousOn_gammaSewnCriticalStokesCompletedCrossingHomotopy_halfChamber,
    ?_, ?_⟩
  · rw [gammaSewnCriticalCompletedPrimeGammaCrossingWinding_eq_neg_one,
      gammaSewnCriticalStokesFredholmSpectralFlow_eq_neg_one]
  · intro t
    exact ⟨gammaSewnCriticalStokesCompletedCrossingHomotopy_zero_left t,
      gammaSewnCriticalStokesCompletedCrossingHomotopy_one_left t⟩
  · intro u hu t ht
    exact gammaSewnCriticalStokesCompletedCrossingHomotopy_eq_zero_iff hu ht

end RHTower
