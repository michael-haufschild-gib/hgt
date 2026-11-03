import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.GlobalCoreHeckeCorrection

/-!
# The retained boundary coordinate of the Lewis source carrier

Completed-period restoration loses exactly one zeta-axis direction. Retaining
that coordinate gives an invertible extension on which the corrected first-prime
operator is actual source transport.
-/

set_option autoImplicit false
noncomputable section
open Complex Set
open GaloisForLFunctions RenormalizedIntersectionTheory MayerScatteringCore

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


/-- Restore both completed-period boundary channels using physical evaluations. -/
def mayerBoundaryRestore (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  f a + mayerCoreZetaCoordinate s f * (1 + (a : ℂ) ^ (-(2 * s))) +
    mayerCoreScatteringCoordinate s f * scatteringPowers (2 * s) a

/-- Retaining the zeta-axis coordinate makes completed-period restoration invertible. -/
def mayerBoundaryReconstruct (s : ℂ) (g : ℝ → ℂ) (c : ℂ) (a : ℝ) : ℂ :=
  g a - c * (1 + (a : ℂ) ^ (-(2 * s))) -
    (g 1 / (2 * s - 1)) * scatteringPowers (2 * s) a

private theorem boundary_denominator_ne {s : ℂ} (hs1 : s.re < 1 / 2) : 2 * s - 1 ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith only [hr, hs1]

private theorem boundary_determinant_ne {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1 / 2) :
    1 - (2 * s + 1) * (2 : ℂ) ^ (-(2 * s)) ≠ 0 :=
  coreBoundaryDeterminant_ne_zero (by simp; linarith only [hs]) (by simp; linarith only [hs1])

private theorem restore_at_one (s : ℂ) (f : ℝ → ℂ) :
    mayerBoundaryRestore s f 1 = (2 * s - 1) * mayerCoreScatteringCoordinate s f := by
  simp only [mayerBoundaryRestore, mayerCoreZetaCoordinate, scatteringPowers,
    Complex.ofReal_one, Complex.one_cpow]
  ring

private theorem scatteringPowers_two (s : ℂ) :
    scatteringPowers (2 * s) 2 = (1 / 2 : ℂ) + 2 * (2 : ℂ) ^ (-(2 * s)) := by
  rw [scatteringPowers]
  norm_num only [Complex.ofReal_ofNat, Complex.cpow_neg_one]
  have hp : (2 : ℂ) * (2 : ℂ) ^ (-(2 * s)) = (2 : ℂ) ^ (1 - 2 * s) := by
    simpa using natCast_mul_cpow_neg (show (2 : ℕ) ≠ 0 by norm_num) (2 * s)
  rw [← hp]

/-- Every restored function satisfies the source boundary relation at `1` and `2`. -/
theorem mayerBoundaryRestore_boundary_relation {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (f : ℝ → ℂ) :
    2 * mayerBoundaryRestore s f 2 = mayerBoundaryRestore s f 1 := by
  have hd := boundary_determinant_ne hs hs1
  have hb : mayerCoreScatteringCoordinate s f *
      (1 - (2 * s + 1) * (2 : ℂ) ^ (-(2 * s))) =
        2 * f 2 - (1 + (2 : ℂ) ^ (-(2 * s))) * f 1 := div_mul_cancel₀ _ hd
  rw [restore_at_one]
  simp only [mayerBoundaryRestore, Complex.ofReal_ofNat, scatteringPowers_two,
    mayerCoreZetaCoordinate]
  linear_combination -hb

/-- The scattering coordinate of a reconstructed source is its normalized value at `1`. -/
theorem mayerCoreScatteringCoordinate_reconstruct {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (g : ℝ → ℂ) (c : ℂ)
    (hg : 2 * g 2 = g 1) :
    mayerCoreScatteringCoordinate s (mayerBoundaryReconstruct s g c) = g 1 / (2 * s - 1) := by
  have hd := boundary_determinant_ne hs hs1
  have hw := boundary_denominator_ne hs1
  have hg2 : g 2 = g 1 / 2 := by linear_combination hg / 2
  unfold mayerCoreScatteringCoordinate
  apply (div_eq_iff hd).mpr
  simp only [mayerBoundaryReconstruct, scatteringPowers_two,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.one_cpow]
  simp only [scatteringPowers, Complex.ofReal_one, Complex.one_cpow]
  rw [hg2]
  field_simp [hw]
  ring

/-- Reconstruction recovers the retained zeta coordinate exactly. -/
theorem mayerCoreZetaCoordinate_reconstruct {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (g : ℝ → ℂ) (c : ℂ)
    (hg : 2 * g 2 = g 1) :
    mayerCoreZetaCoordinate s (mayerBoundaryReconstruct s g c) = c := by
  have hw := boundary_denominator_ne hs1
  rw [mayerCoreZetaCoordinate, mayerCoreScatteringCoordinate_reconstruct hs hs1 g c hg]
  simp only [mayerBoundaryReconstruct, scatteringPowers, Complex.ofReal_one, Complex.one_cpow]
  field_simp [hw]
  ring

/-- Restoring a reconstructed boundary pair returns its completed source. -/
theorem mayerBoundaryRestore_reconstruct {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (g : ℝ → ℂ) (c : ℂ)
    (hg : 2 * g 2 = g 1) :
    mayerBoundaryRestore s (mayerBoundaryReconstruct s g c) = g := by
  funext a
  rw [mayerBoundaryRestore, mayerCoreZetaCoordinate_reconstruct hs hs1 g c hg,
    mayerCoreScatteringCoordinate_reconstruct hs hs1 g c hg, mayerBoundaryReconstruct]
  ring

/-- The restored function and its retained boundary coordinate determine the input exactly. -/
theorem mayerBoundaryReconstruct_restore {s : ℂ}
    (hs1 : s.re < 1 / 2) (f : ℝ → ℂ) :
    mayerBoundaryReconstruct s (mayerBoundaryRestore s f) (mayerCoreZetaCoordinate s f) = f := by
  have hw := boundary_denominator_ne hs1
  funext a
  rw [mayerBoundaryReconstruct, restore_at_one, mul_div_cancel_left₀ _ hw,
    mayerBoundaryRestore]
  ring

#print axioms mayerBoundaryRestore_boundary_relation
#print axioms mayerCoreZetaCoordinate_reconstruct
#print axioms mayerCoreScatteringCoordinate_reconstruct
#print axioms mayerBoundaryRestore_reconstruct
#print axioms mayerBoundaryReconstruct_restore


/-- The actual inversion-fixed, three-term Lewis source carrier on the positive axis. -/
def mayerCompletedLewisCarrier (s : ℂ) : Set (ℝ → ℂ) :=
  {g | (∀ a > 0, lewisModularInversion s g a = g a) ∧
    ∀ a > 0, lewisFarey s g a = g a}

/-- Restoring both boundary channels places a physical function in the completed source carrier. -/
def mayerBoundaryCoreCarrier (s : ℂ) : Set (ℝ → ℂ) :=
  {f | mayerBoundaryRestore s f ∈ mayerCompletedLewisCarrier s}

private theorem source_half_value {s : ℂ} {g : ℝ → ℂ}
    (hg : g ∈ mayerCompletedLewisCarrier s) :
    (2 : ℂ) ^ (-(2 * s)) * g (2 : ℝ)⁻¹ = g 2 := by
  simpa only [lewisModularInversion, Complex.ofReal_ofNat] using hg.1 2 (by norm_num)

/-- Inversion and the three-term equation force the boundary relation, without a
Hecke eigenfunction assumption. -/
theorem mayerCompletedLewisCarrier_boundary_relation {s : ℂ} {g : ℝ → ℂ}
    (hg : g ∈ mayerCompletedLewisCarrier s) : 2 * g 2 = g 1 := by
  have h := hg.2 1 (by norm_num)
  simp only [lewisFarey, lewisShift, lewisParabolic] at h
  norm_num only [Complex.ofReal_ofNat, one_div] at h
  simp only [one_div] at h
  rw [source_half_value hg] at h
  linear_combination h

/-- Boundary evaluation is an eigenfunctional of the actual source operator on the
whole completed Lewis carrier. -/
theorem mayerCompletedLewisCarrier_hecke_at_one {s : ℂ} {g : ℝ → ℂ}
    (hg : g ∈ mayerCompletedLewisCarrier s) :
    lewisHeckeT2 s g 1 = (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * g 1 := by
  have h := mayerCompletedLewisCarrier_boundary_relation hg
  rw [lewisHeckeT2]
  norm_num only [mul_one, div_self (by norm_num : (2 : ℝ) ≠ 0), Complex.ofReal_ofNat, one_div]
  simp only [one_div]
  rw [source_half_value hg]
  linear_combination h

/-- Exact inversion commutation and Farey-defect transport preserve the source carrier. -/
theorem mayerCompletedLewisCarrier_heckeT2 {s : ℂ} {g : ℝ → ℂ}
    (hg : g ∈ mayerCompletedLewisCarrier s) :
    lewisHeckeT2 s g ∈ mayerCompletedLewisCarrier s := by
  constructor
  · intro a ha
    rw [lewisModularInversion_heckeT2 s g ha]
    simp only [lewisHeckeT2]
    rw [hg.1 _ (by positivity : 0 < 2 * a), hg.1 _ (by positivity : 0 < a / 2),
      hg.1 _ (by positivity : 0 < (a + 1) / 2),
      hg.1 _ (by positivity : 0 < 2 * a / (a + 1))]
  · exact fun a ha => lewisFarey_heckeT2_of_fixed hg.2 ha

/-- Every actual upper-strip core belongs to the restored source carrier. -/
theorem mayerPeriodCore_mem_boundaryCarrier {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    mayerPeriodCore s ∈ mayerBoundaryCoreCarrier s := by
  have he (a : ℝ) (ha : 0 < a) :
      mayerBoundaryRestore s (mayerPeriodCore s) a = eisensteinLewisPeriod s a := by
    rw [mayerBoundaryRestore, mayerCoreZetaCoordinate_core hs hs1 him,
      mayerCoreScatteringCoordinate_core hs hs1 him,
      mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him ha]
    ring
  obtain ⟨_, _, hI, hF⟩ := eisensteinLewisPeriod_properties hs hs1
  constructor
  · intro a ha
    rw [lewisModularInversion, he _ (inv_pos.mpr ha), he a ha]
    exact hI a ha
  · intro a ha
    rw [lewisFarey, lewisShift, lewisParabolic,
      he _ (by positivity : 0 < a + 1), he _ (by positivity : 0 < a / (a + 1)), he a ha]
    exact hF a ha

/-- Corrected transport is actual source transport with the retained coordinate scaled
by the arithmetic boundary eigenvalue. -/
theorem mayerCorrectedHeckeT2_reconstruct {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) {g : ℝ → ℂ}
    (hg : g ∈ mayerCompletedLewisCarrier s) (c : ℂ) :
    mayerCorrectedHeckeT2 s (mayerBoundaryReconstruct s g c) =
      mayerBoundaryReconstruct s (lewisHeckeT2 s g)
        ((1 + 2 * (2 : ℂ) ^ (-(2 * s))) * c) := by
  have hv := mayerCompletedLewisCarrier_boundary_relation hg
  funext a
  rw [mayerCorrectedHeckeT2, mayerCoreZetaCoordinate_reconstruct hs hs1 g c hv,
    mayerCoreScatteringCoordinate_reconstruct hs hs1 g c hv]
  conv_rhs => rw [mayerBoundaryReconstruct, mayerCompletedLewisCarrier_hecke_at_one hg]
  simp only [lewisHeckeT2, mayerBoundaryReconstruct]
  ring

#print axioms mayerCompletedLewisCarrier_boundary_relation
#print axioms mayerCompletedLewisCarrier_hecke_at_one
#print axioms mayerCompletedLewisCarrier_heckeT2
#print axioms mayerPeriodCore_mem_boundaryCarrier
#print axioms mayerCorrectedHeckeT2_reconstruct


/-- Every completed boundary pair has exactly one physical preimage. -/
theorem mayerBoundaryRestore_unique_preimage {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (g : ℝ → ℂ) (c : ℂ)
    (hg : 2 * g 2 = g 1) :
    ∃! f : ℝ → ℂ, mayerBoundaryRestore s f = g ∧ mayerCoreZetaCoordinate s f = c := by
  refine ⟨mayerBoundaryReconstruct s g c,
    ⟨mayerBoundaryRestore_reconstruct hs hs1 g c hg,
      mayerCoreZetaCoordinate_reconstruct hs hs1 g c hg⟩, ?_⟩
  intro f hf
  have h := mayerBoundaryReconstruct_restore hs1 f
  rw [hf.1, hf.2] at h
  exact h.symm

/-- Restoration alone loses exactly the zeta-axis boundary direction. -/
theorem mayerBoundaryRestore_kernel_iff {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (f : ℝ → ℂ) :
    mayerBoundaryRestore s f = 0 ↔
      ∃ c : ℂ, f = fun a : ℝ => c * (1 + (a : ℂ) ^ (-(2 * s))) := by
  constructor
  · intro hf
    refine ⟨-mayerCoreZetaCoordinate s f, ?_⟩
    have hr := mayerBoundaryReconstruct_restore hs1 f
    rw [hf] at hr
    funext a
    have h := congrFun hr a
    simp only [mayerBoundaryReconstruct, Pi.zero_apply, zero_div, zero_mul, sub_zero, zero_sub] at h
    linear_combination -h
  · rintro ⟨c, rfl⟩
    have he : mayerBoundaryReconstruct s (0 : ℝ → ℂ) (-c) =
        fun a : ℝ => c * (1 + (a : ℂ) ^ (-(2 * s))) := by
      funext a
      simp only [mayerBoundaryReconstruct, Pi.zero_apply, zero_div, zero_mul]
      ring
    rw [← he]
    exact mayerBoundaryRestore_reconstruct hs hs1 (0 : ℝ → ℂ) (-c) (by simp)

/-- Corrected first-prime transport intertwines restoration with the actual source
operator and retains the exact arithmetic action on the extra boundary coordinate. -/
theorem mayerBoundaryRestore_correctedHeckeT2 {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) {f : ℝ → ℂ}
    (hf : f ∈ mayerBoundaryCoreCarrier s) :
    mayerBoundaryRestore s (mayerCorrectedHeckeT2 s f) =
        lewisHeckeT2 s (mayerBoundaryRestore s f) ∧
      mayerCoreZetaCoordinate s (mayerCorrectedHeckeT2 s f) =
        (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * mayerCoreZetaCoordinate s f := by
  have hg : mayerBoundaryRestore s f ∈ mayerCompletedLewisCarrier s := hf
  have hT := mayerCompletedLewisCarrier_heckeT2 hg
  have hv := mayerCompletedLewisCarrier_boundary_relation hT
  have he := mayerCorrectedHeckeT2_reconstruct hs hs1 hg (mayerCoreZetaCoordinate s f)
  rw [mayerBoundaryReconstruct_restore hs1 f] at he
  constructor
  · rw [he]
    exact mayerBoundaryRestore_reconstruct hs hs1 _ _ hv
  · rw [he]
    exact mayerCoreZetaCoordinate_reconstruct hs hs1 _ _ hv

/-- The explicit boundary extension is stable under corrected source Hecke transport. -/
theorem mayerBoundaryCoreCarrier_correctedHeckeT2 {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) {f : ℝ → ℂ}
    (hf : f ∈ mayerBoundaryCoreCarrier s) :
    mayerCorrectedHeckeT2 s f ∈ mayerBoundaryCoreCarrier s := by
  change mayerBoundaryRestore s (mayerCorrectedHeckeT2 s f) ∈ mayerCompletedLewisCarrier s
  rw [(mayerBoundaryRestore_correctedHeckeT2 hs hs1 hf).1]
  exact mayerCompletedLewisCarrier_heckeT2 hf

#print axioms mayerBoundaryRestore_unique_preimage
#print axioms mayerBoundaryRestore_kernel_iff
#print axioms mayerBoundaryRestore_correctedHeckeT2
#print axioms mayerBoundaryCoreCarrier_correctedHeckeT2

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
