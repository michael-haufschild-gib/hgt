import GaloisForLFunctions.BiScaleUncertainty.PlasticCrossoverGramReceiver
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Centered source control of hyperbolic multiplier Gram leakage

Odd reflection turns sine-multiplier correlations into mixed correlations with
an actual centered cosine-weighted source. The off-diagonal multiplier defect
is then bounded by source Gram data on node differences. No inherited zeros,
unknown moment bound, or additional analytic premise is assumed.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.CenteredHyperbolicGram
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
variable {ι : Type*}

/-- Actual cosine-weighted source with arbitrary scalar centering. -/
def centeredSource (f : C_c(ℝ, ℝ)) (α c : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => (Real.cosh (2 * α * u) - c) * f u, by
    have hf := f.continuous
    fun_prop⟩, f.hasCompactSupport.mul_left⟩

private theorem integrable_weighted_pair (f : C_c(ℝ, ℝ)) (w : C(ℝ, ℝ)) (x : ℝ) :
    Integrable (fun u => w u * f u * f (u + x)) :=
  ((w.continuous.mul f.continuous).mul
    (f.continuous.comp (continuous_add_const x))).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_left.mul_right

private theorem cosh_pair_identity (α u x : ℝ) :
    Real.cosh (2 * α * u) + Real.cosh (2 * α * (u + x)) =
      2 * Real.cosh (α * x) *
        (2 * Real.sinh (α * u) * Real.sinh (α * (u + x)) + Real.cosh (α * x)) := by
  have h1 := Real.cosh_add (α * u + α * (u + x)) (α * x)
  have h2 := Real.cosh_sub (α * u + α * (u + x)) (α * x)
  have h3 := Real.cosh_add (α * u) (α * (u + x))
  have h4 := Real.cosh_sub (α * (u + x)) (α * u)
  rw [show α * u + α * (u + x) + α * x = 2 * α * (u + x) by ring] at h1
  rw [show α * u + α * (u + x) - α * x = 2 * α * u by ring] at h2
  rw [show α * (u + x) - α * u = α * x by ring] at h4
  linear_combination h1 + h2 + 2 * Real.cosh (α * x) * h3 -
    2 * Real.cosh (α * x) * h4

private theorem cosh_cross_identity (f : C_c(ℝ, ℝ))
    (ho : ∀ u, f (-u) = -f u) (α x : ℝ) :
    (∫ u, Real.cosh (2 * α * u) * f u * f (u + x)) =
      2 * Real.cosh (α * x) * autocorr (sinhCompact α f) x +
        Real.cosh (α * x) ^ 2 * autocorr f x := by
  let g : ℝ → ℝ := fun u => Real.cosh (2 * α * u) * f u * f (u + x)
  have hr : (∫ u, Real.cosh (2 * α * (u + x)) * f u * f (u + x)) = ∫ u, g u := by
    have hn := integral_neg_eq_self g volume
    have ht := integral_add_right_eq_self (μ := volume) (fun u => g (-u)) x
    have he (u : ℝ) : g (-(u + x)) =
        Real.cosh (2 * α * (u + x)) * f u * f (u + x) := by
      dsimp [g]
      rw [show 2 * α * -(u + x) = -(2 * α * (u + x)) by ring,
        show -(u + x) + x = -u by ring, Real.cosh_neg, ho, ho]
      ring
    simp_rw [he] at ht
    exact ht.trans hn
  have hi0 := integrable_weighted_pair f
    (⟨fun u => Real.cosh (2 * α * u), by fun_prop⟩ : C(ℝ, ℝ)) x
  have hi1 := integrable_weighted_pair f
    (⟨fun u => Real.cosh (2 * α * (u + x)), by fun_prop⟩ : C(ℝ, ℝ)) x
  change Integrable (fun u => Real.cosh (2 * α * u) * f u * f (u + x)) at hi0
  change Integrable (fun u => Real.cosh (2 * α * (u + x)) * f u * f (u + x)) at hi1
  have his := integrable_mul_shift (g := (sinhCompact α f : ℝ → ℝ)) (sinhCompact α f).continuous
    (sinhCompact α f).hasCompactSupport x
  have hif := integrable_mul_shift (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport x
  have he : (fun u => Real.cosh (2 * α * u) * f u * f (u + x) +
      Real.cosh (2 * α * (u + x)) * f u * f (u + x)) =
      fun u => (4 * Real.cosh (α * x)) *
        (sinhCompact α f u * sinhCompact α f (u + x)) +
        (2 * Real.cosh (α * x) ^ 2) * (f u * f (u + x)) := by
    funext u
    change _ = (4 * Real.cosh (α * x)) *
      ((Real.sinh (α * u) * f u) * (Real.sinh (α * (u + x)) * f (u + x))) + _
    linear_combination (f u * f (u + x)) * cosh_pair_identity α u x
  have heint := congrArg (fun p : ℝ → ℝ => ∫ u, p u) he
  rw [integral_add hi0 hi1, integral_add (his.const_mul _) (hif.const_mul _),
    integral_const_mul, integral_const_mul, hr] at heint
  change (∫ u, g u) + (∫ u, g u) =
    (4 * Real.cosh (α * x)) * autocorr (sinhCompact α f) x +
      (2 * Real.cosh (α * x) ^ 2) * autocorr f x at heint
  change (∫ u, g u) = _
  linarith

/-- Odd reflection gives an exact source cross-correlation for every sine sample. -/
theorem odd_centered_cross_identity (f : C_c(ℝ, ℝ)) (α c x : ℝ) :
    (∫ u, centeredSource (oddCompactSource f) α c u * oddCompactSource f (u + x)) =
      2 * Real.cosh (α * x) * autocorr (sinhCompact α (oddCompactSource f)) x +
        (Real.cosh (α * x) ^ 2 - c) * autocorr (oddCompactSource f) x := by
  let F := oddCompactSource f
  have hi := integrable_weighted_pair F
    (⟨fun u => Real.cosh (2 * α * u), by fun_prop⟩ : C(ℝ, ℝ)) x
  change Integrable (fun u => Real.cosh (2 * α * u) * F u * F (u + x)) at hi
  have hf := integrable_mul_shift (g := (F : ℝ → ℝ)) F.continuous F.hasCompactSupport x
  have he : (fun u => centeredSource F α c u * F (u + x)) =
      fun u => Real.cosh (2 * α * u) * F u * F (u + x) - c * (F u * F (u + x)) := by
    funext u
    change ((Real.cosh (2 * α * u) - c) * F u) * F (u + x) = _
    ring
  change (∫ u, centeredSource F α c u * F (u + x)) = _
  rw [he, integral_sub hi (hf.const_mul _), integral_const_mul,
    cosh_cross_identity F (oddCompactSource_odd f)]
  change _ - c * autocorr F x = _
  ring

/-- Mixed packet control by the source's actual Gram and the target's actual energy. -/
theorem mixedPacket_abs_le (f q : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    |∑ i ∈ s, w i * (∫ u, q u * f (u + t i))| ≤
      Real.sqrt (autocorr q 0 * translationGramEnergy f s w t) := by
  let P : ℝ → ℝ := fun u => ∑ i ∈ s, w i * f (u + t i)
  have hPc : Continuous P := continuous_finsetSum s fun i _ =>
    continuous_const.mul (f.continuous.comp (continuous_add_const (t i)))
  have hPs : HasCompactSupport P := by
    have hs := HasCompactSupport.finset_sum (s := s) (f := fun i u => w i * f (u + t i))
      (fun i _ => (hasCompactSupport_comp_add f.hasCompactSupport (t i)).mul_left)
    have he : (∑ i ∈ s, fun u => w i * f (u + t i)) = P := by
      funext u
      simp only [Finset.sum_apply, P]
    rwa [he] at hs
  have hs := HTGeometry.sq_integral_mul_le (f := (q : ℝ → ℝ)) (g := P)
    q.continuous.aestronglyMeasurable
    hPc.aestronglyMeasurable (integrable_sq (g := (q : ℝ → ℝ)) q.continuous q.hasCompactSupport)
    (integrable_sq hPc hPs)
  have he : (∫ u, q u * P u) = ∑ i ∈ s, w i * (∫ u, q u * f (u + t i)) := by
    have hint (i : ι) : Integrable (fun u => w i * (q u * f (u + t i))) :=
      ((q.continuous.mul (f.continuous.comp (continuous_add_const (t i)))).integrable_of_hasCompactSupport
        q.hasCompactSupport.mul_right).const_mul _
    have hp : (fun u => q u * P u) = fun u => ∑ i ∈ s, w i * (q u * f (u + t i)) := by
      funext u
      dsimp [P]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hp, integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [he, integral_sq_eq_autocorr_zero q] at hs
  have hp := translationGramEnergy_eq_integral f s w t
  change translationGramEnergy f s w t = ∫ u, P u ^ 2 at hp
  rw [← hp] at hs
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hs

private theorem gram_eq_diagonal_add_offDiag (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) :
    translationGramEnergy f s w t = autocorr f 0 * (∑ i ∈ s, w i ^ 2) +
      ∑ p ∈ s.offDiag, w p.1 * w p.2 * autocorr f (t p.2 - t p.1) := by
  classical
  unfold translationGramEnergy
  rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sub_self]
  ring

/-- Pair-difference nodes retain every repeated difference and cross correlation. -/
def differenceNode (t : ι → ℝ) (p : ι × ι) : ℝ := t p.2 - t p.1

def differenceWeight (α : ℝ) (w t : ι → ℝ) (p : ι × ι) : ℝ :=
  w p.1 * w p.2 / (2 * Real.cosh (α * differenceNode t p))

/-- Source-zero error, explicitly retained rather than assumed away. -/
def sourceCorrection (f : C_c(ℝ, ℝ)) (α c : ℝ)
    (s : Finset ι) (w t : ι → ℝ) : ℝ :=
  ∑ p ∈ s.offDiag, differenceWeight α w t p *
    (c - Real.cosh (α * differenceNode t p) ^ 2) * autocorr f (differenceNode t p)

/-- Exact centered decomposition of the actual multiplier clique defect. -/
theorem odd_defect_eq_source (f : C_c(ℝ, ℝ)) (α c : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    sinhCliqueGramDefect (oddCompactSource f) α s w t =
      sourceCorrection (oddCompactSource f) α c s w t +
        ∑ p ∈ s.offDiag, differenceWeight α w t p *
          (∫ u, centeredSource (oddCompactSource f) α c u *
            oddCompactSource f (u + differenceNode t p)) := by
  unfold sinhCliqueGramDefect
  rw [gram_eq_diagonal_add_offDiag]
  simp only [add_sub_cancel_left]
  unfold sourceCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [odd_centered_cross_identity]
  dsimp [differenceWeight, differenceNode]
  field_simp [(Real.cosh_pos (α * (t p.2 - t p.1))).ne']
  ring

/-- The entire off-diagonal multiplier defect is controlled by source difference Gram data. -/
theorem odd_defect_abs_sub_correction_le (f : C_c(ℝ, ℝ)) (α c : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    |sinhCliqueGramDefect (oddCompactSource f) α s w t -
        sourceCorrection (oddCompactSource f) α c s w t| ≤
      Real.sqrt (autocorr (centeredSource (oddCompactSource f) α c) 0 *
        translationGramEnergy (oddCompactSource f) s.offDiag
          (differenceWeight α w t) (differenceNode t)) := by
  rw [odd_defect_eq_source, add_sub_cancel_left]
  exact mixedPacket_abs_le _ _ _ _ _

/-- Computable source-data envelope for multiplier leakage. -/
def sourceDefectUpper (f : C_c(ℝ, ℝ)) (α c : ℝ)
    (s : Finset ι) (w t : ι → ℝ) : ℝ :=
  sourceCorrection f α c s w t +
    Real.sqrt (autocorr (centeredSource f α c) 0 *
      translationGramEnergy f s.offDiag (differenceWeight α w t) (differenceNode t))

theorem odd_defect_le_sourceDefectUpper (f : C_c(ℝ, ℝ)) (α c : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    sinhCliqueGramDefect (oddCompactSource f) α s w t ≤
      sourceDefectUpper (oddCompactSource f) α c s w t := by
  have h := (le_abs_self _).trans (odd_defect_abs_sub_correction_le f α c s w t)
  unfold sourceDefectUpper
  linarith

/-- First quadratic hyperbolic moment of the original source. -/
def coshMass (f : C_c(ℝ, ℝ)) (α : ℝ) : ℝ :=
  ∫ u, Real.cosh (2 * α * u) * f u ^ 2

/-- Second quadratic hyperbolic moment, as the energy of an actual weighted source. -/
def coshSquareMass (f : C_c(ℝ, ℝ)) (α : ℝ) : ℝ :=
  autocorr (coshCompact (2 * α) f) 0

def sourceVariance (f : C_c(ℝ, ℝ)) (α : ℝ) : ℝ :=
  autocorr f 0 * coshSquareMass f α - coshMass f α ^ 2

private theorem integrable_coshMass (f : C_c(ℝ, ℝ)) (α : ℝ) :
    Integrable (fun u => Real.cosh (2 * α * u) * f u ^ 2) := by
  have h := integrable_weighted_pair f
    (⟨fun u => Real.cosh (2 * α * u), by fun_prop⟩ : C(ℝ, ℝ)) 0
  simpa only [ContinuousMap.coe_mk, add_zero, sq, mul_assoc] using h

theorem sourceVariance_nonneg (f : C_c(ℝ, ℝ)) (α : ℝ) :
    0 ≤ sourceVariance f α := by
  have h := HTGeometry.sq_integral_mul_le (f := (f : ℝ → ℝ))
    (g := (coshCompact (2 * α) f : ℝ → ℝ)) f.continuous.aestronglyMeasurable
    (coshCompact (2 * α) f).continuous.aestronglyMeasurable
    (integrable_sq f.continuous f.hasCompactSupport)
    (integrable_sq (coshCompact (2 * α) f).continuous
      (coshCompact (2 * α) f).hasCompactSupport)
  have he : (fun u => f u * coshCompact (2 * α) f u) =
      fun u => Real.cosh (2 * α * u) * f u ^ 2 := by
    funext u
    change f u * (Real.cosh ((2 * α) * u) * f u) = _
    ring
  rw [he, integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero] at h
  exact sub_nonneg.mpr h

/-- Exact quadratic cost of choosing the centering parameter. -/
theorem centered_energy_eq (f : C_c(ℝ, ℝ)) (α c : ℝ) :
    autocorr (centeredSource f α c) 0 =
      coshSquareMass f α - 2 * c * coshMass f α + c ^ 2 * autocorr f 0 := by
  have hw := integrable_sq (g := (coshCompact (2 * α) f : ℝ → ℝ)) (coshCompact (2 * α) f).continuous
    (coshCompact (2 * α) f).hasCompactSupport
  have hm := integrable_coshMass f α
  have hf := integrable_sq (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have hi1 : Integrable (fun u => coshCompact (2 * α) f u ^ 2 -
      (2 * c) * (Real.cosh (2 * α * u) * f u ^ 2)) := hw.sub (hm.const_mul (2 * c))
  have hi2 : Integrable (fun u => c ^ 2 * (f u ^ 2)) := hf.const_mul (c ^ 2)
  have he : (fun u => centeredSource f α c u ^ 2) =
      fun u => (coshCompact (2 * α) f u ^ 2 -
        (2 * c) * (Real.cosh (2 * α * u) * f u ^ 2)) + c ^ 2 * (f u ^ 2) := by
    funext u
    change ((Real.cosh (2 * α * u) - c) * f u) ^ 2 =
      ((Real.cosh ((2 * α) * u) * f u) ^ 2 - _) + _
    ring
  rw [← integral_sq_eq_autocorr_zero, he,
    integral_add hi1 hi2,
    integral_sub hw (hm.const_mul (2 * c)), integral_const_mul, integral_const_mul,
    integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero]
  rfl

theorem centered_energy_variance_identity (f : C_c(ℝ, ℝ)) (α c : ℝ) :
    autocorr f 0 * autocorr (centeredSource f α c) 0 =
      (autocorr f 0 * c - coshMass f α) ^ 2 + sourceVariance f α := by
  rw [centered_energy_eq]
  unfold sourceVariance
  ring

/-- The actual source mean minimizes weighted energy, including the zero-energy case. -/
theorem centered_energy_minimizer (f : C_c(ℝ, ℝ)) (α c : ℝ) :
    autocorr (centeredSource f α (coshMass f α / autocorr f 0)) 0 +
        autocorr f 0 * (c - coshMass f α / autocorr f 0) ^ 2 =
      autocorr (centeredSource f α c) 0 := by
  rw [centered_energy_eq, centered_energy_eq]
  by_cases hR : autocorr f 0 = 0
  · have hm : coshMass f α = 0 := by
      have h := sourceVariance_nonneg f α
      unfold sourceVariance at h
      rw [hR] at h
      nlinarith [sq_nonneg (coshMass f α)]
    simp [hR, hm]
  · field_simp
    ring

theorem centered_energy_min_le (f : C_c(ℝ, ℝ)) (α c : ℝ) :
    autocorr (centeredSource f α (coshMass f α / autocorr f 0)) 0 ≤
      autocorr (centeredSource f α c) 0 := by
  have h := centered_energy_minimizer f α c
  have hn := mul_nonneg (autocorr_zero_nonneg f)
    (sq_nonneg (c - coshMass f α / autocorr f 0))
  linarith

/-- The uncompensated secant bound with source-controlled multiplier leakage. -/
def centeredJumpBound (f : C_c(ℝ, ℝ)) (c : ℝ)
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 *
      ((∑ i ∈ s, sinhJumpTransferWeights f b t y i * Real.cosh ((t i - y) / 2)) -
        Real.sqrt (∑ i ∈ s, sinhJumpTransferWeights f b t y i ^ 2)) -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
      max (sourceDefectUpper f (1 / 2) c s (sinhJumpTransferWeights f b t y) t) 0)

theorem odd_centeredJumpBound_le_gram (f : C_c(ℝ, ℝ)) (c : ℝ)
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    centeredJumpBound (oddCompactSource f) c s b t y ≤
      sinhJumpGramBound (oddCompactSource f) s b t y := by
  let F := oddCompactSource f
  let v := sinhJumpTransferWeights F b t y
  let R := autocorr (sinhCompact (1 / 2) F) 0
  let A := ∑ i ∈ s, v i ^ 2
  let D := sinhCliqueGramDefect F (1 / 2) s v t
  let U := sourceDefectUpper F (1 / 2) c s v t
  have hR : 0 ≤ R := autocorr_zero_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD : D ≤ U := odd_defect_le_sourceDefectUpper f (1 / 2) c s v t
  have hB : 0 ≤ R * max U 0 := mul_nonneg hR (le_max_right _ _)
  have hsq : (R * Real.sqrt A) ^ 2 = R * (R * A) := by
    rw [mul_pow, Real.sq_sqrt hA]
    ring
  have hroot : Real.sqrt (R * (R * A + D)) ≤
      R * Real.sqrt A + Real.sqrt (R * max U 0) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hcost : R * D ≤ R * max U 0 :=
      mul_le_mul_of_nonneg_left (hD.trans (le_max_left _ _)) hR
    have hcross : 0 ≤ (R * Real.sqrt A) * Real.sqrt (R * max U 0) := by positivity
    nlinarith [Real.sq_sqrt hB]
  unfold centeredJumpBound sinhJumpGramBound
  rw [sinhGram_eq_diagonal_add_defect]
  change R * ((∑ i ∈ s, v i * Real.cosh ((t i - y) / 2)) - Real.sqrt A) -
      Real.sqrt (R * max U 0) ≤
    R * (∑ i ∈ s, v i * Real.cosh ((t i - y) / 2)) - Real.sqrt (R * (R * A + D))
  linarith

theorem odd_secantJumpCollar_ge_centered (f : C_c(ℝ, ℝ)) (c : ℝ)
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    centeredJumpBound (oddCompactSource f) c s b t y ≤
      secantJumpCollar (oddCompactSource f) s b t y :=
  (odd_centeredJumpBound_le_gram f c s b t y).trans
    (secantJumpCollar_ge_gram _ _ _ _ _)

theorem continuous_centeredJumpBound (f : C_c(ℝ, ℝ)) (c : ℝ)
    (s : Finset ι) (b t : ι → ℝ) : Continuous (centeredJumpBound f c s b t) := by
  have hv := continuous_sinhJumpTransferWeights f b t
  have ha (p : ι × ι) : Continuous (fun y =>
      differenceWeight (1 / 2) (sinhJumpTransferWeights f b t y) t p) := by
    unfold differenceWeight
    exact ((hv p.1).mul (hv p.2)).div_const _
  have he : Continuous (fun y =>
      sourceCorrection f (1 / 2) c s (sinhJumpTransferWeights f b t y) t) := by
    unfold sourceCorrection
    exact continuous_finsetSum _ fun p _ => ((ha p).mul continuous_const).mul continuous_const
  have hg : Continuous (fun y => translationGramEnergy f s.offDiag
      (differenceWeight (1 / 2) (sinhJumpTransferWeights f b t y) t) (differenceNode t)) := by
    unfold translationGramEnergy
    exact continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ =>
      ((ha p).mul (ha q)).mul continuous_const
  have hu : Continuous (fun y =>
      sourceDefectUpper f (1 / 2) c s (sinhJumpTransferWeights f b t y) t) :=
    he.add (Real.continuous_sqrt.comp (continuous_const.mul hg))
  unfold centeredJumpBound
  exact (continuous_const.mul
    ((continuous_finsetSum _ fun i _ => (hv i).mul (by fun_prop)).sub
      (Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (hv i).pow 2)))).sub
    (Real.continuous_sqrt.comp (continuous_const.mul (hu.max continuous_const)))

private theorem integral_centered_le_gram (f : C_c(ℝ, ℝ)) (c δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, centeredJumpBound (oddCompactSource f) c (Finset.range K)
      (fun _ => 1) (fun k => (k : ℝ) * |δ|) (-y)) ≤
    ∫ y in (0 : ℝ)..|δ|, sinhJumpGramBound (oddCompactSource f) (Finset.range K)
      (fun _ => 1) (fun k => (k : ℝ) * |δ|) (-y) :=
  intervalIntegral.integral_mono_on (μ := volume) (abs_nonneg δ)
    (((continuous_centeredJumpBound _ _ _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (((continuous_sinhJumpGramBound _ _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (fun y _ => odd_centeredJumpBound_le_gram f c _ _ _ (-y))

/-- Full secant-energy receiver using source Gram data and a centered weighted source. -/
theorem odd_secantEnergy_ge_centered (f : C_c(ℝ, ℝ)) (c δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, centeredJumpBound (oddCompactSource f) c (Finset.range K)
      (fun _ => 1) (fun k => (k : ℝ) * |δ|) (-y)) ≤ biScaleSecantEnergy (oddCompactSource f) :=
  (integral_centered_le_gram f c δ K).trans (biScaleSecantEnergy_ge_sinhJumpGram _ _ _)

/-- Actual odd plastic crossover, retaining its positive remainder and negative moment,
with every multiplier off-diagonal entry controlled by original source data. -/
theorem odd_plasticCrossover_ge_centered (f : C_c(ℝ, ℝ)) (c δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, centeredJumpBound (oddCompactSource f) c (Finset.range K)
      (fun _ => 1) (fun k => (k : ℝ) * |δ|) (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      plasticCrossover (oddCompactSource f) := by
  have h := odd_secantEnergy_ge_centered f c δ K
  rw [plasticCrossover_eq_secant_add_remainder_add_moment, hyperbolicMomentEnergy_oddSource]
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty.CenteredHyperbolicGram
