import GaloisForLFunctions.RHTower.ThetaBVArithmeticAdmission
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization

/-! # The complete Weil form on the admitted arithmetic graph

Both polar moments are continuous in the actual source coordinate. Their
rank-two correction restores the full Weil form, with its original signs.
This gives a continuous extension of the literal compact-test form to every
admitted BV profile, not only its archimedean or prime component.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open Zeta23
open scoped InnerProductSpace

namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

def sinhRatio (x : ℝ) : ℝ := Real.tanh (x/2)

theorem continuous_sinhRatio : Continuous sinhRatio := by
  have he : sinhRatio = fun x => Real.sinh (x/2)/Real.cosh (x/2) :=
    funext fun x => Real.tanh_eq_sinh_div_cosh (x/2)
  rw [he]
  exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) fun x => (Real.cosh_pos _).ne'

theorem sinhRatio_memLp : MemLp sinhRatio 2 massMeasure := by
  apply (memLp_top_of_bound continuous_sinhRatio.aestronglyMeasurable 1 ?_).mono_exponent le_top
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_one_lt_tanh _).le, (Real.tanh_lt_one _).le⟩

def sourceCoshMoment (p : SourceGraph) : ℝ :=
  ⟪(constantLift 1).val.fst, sourceMap p⟫_ℝ

def sourceSinhMoment (p : SourceGraph) : ℝ :=
  ⟪sinhRatio_memLp.toLp sinhRatio, sourceMap p⟫_ℝ

theorem continuous_sourceCoshMoment : Continuous sourceCoshMoment :=
  continuous_const.inner sourceMap.continuous

theorem continuous_sourceSinhMoment : Continuous sourceSinhMoment :=
  continuous_const.inner sourceMap.continuous

theorem sourceCoshMoment_ofFunction (v : ℝ → ℝ) (hs : MemLp v 2 massMeasure)
    (hd : MemLp (difference v) 2 edgeMeasure) :
    sourceCoshMoment (ofFunction massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right v hs hd) = phiDoobCoshMass v := by
  rw [sourceCoshMoment, L2.inner_def]
  have he : (∫ x, inner ℝ ((constantLift 1).val.fst x) (hs.toLp v x) ∂massMeasure) =
      ∫ x, v x ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [(memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp,
      hs.coeFn_toLp] with x h1 hv
    change (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _ x = 1 at h1
    change inner ℝ ((memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).toLp _ x)
      (hs.toLp v x) = _
    rw [h1, hv]
    simp
  change (∫ x, inner ℝ ((constantLift 1).val.fst x) (hs.toLp v x) ∂massMeasure) = _
  rw [he, massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp [massDensity, phiDoobCoshMass, phiDoobTest]; ring

theorem sourceSinhMoment_ofFunction (v : ℝ → ℝ) (hs : MemLp v 2 massMeasure)
    (hd : MemLp (difference v) 2 edgeMeasure) :
    sourceSinhMoment (ofFunction massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right v hs hd) = phiDoobSinhMass v := by
  rw [sourceSinhMoment, L2.inner_def]
  change (∫ x, inner ℝ (sinhRatio_memLp.toLp sinhRatio x) (hs.toLp v x) ∂massMeasure) = _
  have he : (∫ x, inner ℝ (sinhRatio_memLp.toLp sinhRatio x) (hs.toLp v x) ∂massMeasure) =
      ∫ x, sinhRatio x*v x ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [sinhRatio_memLp.coeFn_toLp, hs.coeFn_toLp] with x hx hv
    simp [hx, hv, mul_comm]
  rw [he, massMeasure, integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [massDensity, sinhRatio, phiDoobSinhMass, phiDoobTest]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos (x/2)).ne']

/-- The full signed form, with both independent polar moments retained. -/
def sourceWeilPair (p q : SourceGraph) : ℝ :=
  sourcePair p q + 2*sourceCoshMoment p*sourceCoshMoment q -
    2*sourceSinhMoment p*sourceSinhMoment q

def sourceWeilEnergy (p : SourceGraph) : ℝ := sourceWeilPair p p

theorem continuous_sourceWeilPair :
    Continuous (fun p : SourceGraph × SourceGraph => sourceWeilPair p.1 p.2) := by
  exact (continuous_sourcePair.add ((continuous_const.mul
    (continuous_sourceCoshMoment.comp continuous_fst)).mul
      (continuous_sourceCoshMoment.comp continuous_snd))).sub
        ((continuous_const.mul (continuous_sourceSinhMoment.comp continuous_fst)).mul
          (continuous_sourceSinhMoment.comp continuous_snd))

theorem continuous_sourceWeilEnergy : Continuous sourceWeilEnergy :=
  continuous_sourceWeilPair.comp (continuous_id.prodMk continuous_id)

theorem sourceWeilEnergy_eq (p : SourceGraph) :
    sourceWeilEnergy p = sourceEnergy p + 2*sourceCoshMoment p^2 - 2*sourceSinhMoment p^2 := by
  simp only [sourceWeilEnergy, sourceWeilPair, sourcePair_self]
  ring

theorem sourceWeilEnergy_compactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hc : HasCompactSupport v) :
    sourceWeilEnergy (compactLift v hv hc) =
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun x => (phiDoobTest v x : ℂ)) (fun x => (phiDoobTest v x : ℂ)))).re := by
  rw [sourceWeilEnergy_eq, sourceEnergy_compactLift]
  change markovEnergy _ +
    2*sourceCoshMoment (ofFunction massMeasure edgeMeasure left right nonsingular_left
      nonsingular_right v (compact_memLp_mass hv.continuous hc) (compact_memLp_difference hv hc))^2 -
    2*sourceSinhMoment (ofFunction massMeasure edgeMeasure left right nonsingular_left
      nonsingular_right v (compact_memLp_mass hv.continuous hc) (compact_memLp_difference hv hc))^2 = _
  rw [sourceCoshMoment_ofFunction, sourceSinhMoment_ofFunction]
  have hp := phiDoob_pole hv.continuous hc
  dsimp only [markovEnergy]
  rw [Complex.sub_re]
  linarith

/-- The full arithmetic BV energy, including the polar rank-two contribution. -/
theorem sourceWeilEnergy_bvLift (v : ℝ → ℝ) (hv : BoundedVariationOn v univ) :
    sourceWeilEnergy (bvLift v hv) = phiDoobArchJumpEnergy v +
      (∑' n, ∫ x, phiDoobPrimeJump v n x) - phiDoobCoshMass (fun x => v x^2) +
        2*phiDoobCoshMass v^2 - 2*phiDoobSinhMass v^2 := by
  rw [sourceWeilEnergy_eq, sourceEnergy_bvLift]
  simp only [bvLift, sourceCoshMoment_ofFunction, sourceSinhMoment_ofFunction]

/-- Density makes this extension unique on the complete original source domain. -/
theorem sourceWeilEnergy_unique {F : SourceGraph → ℝ} (hF : Continuous F)
    (h : ∀ v hv hc, F (compactLift v hv hc) = sourceWeilEnergy (compactLift v hv hc)) :
    F = sourceWeilEnergy := by
  have hs : (compactTests : Set SourceGraph) ⊆ {p | F p = sourceWeilEnergy p} := by
    rintro p ⟨v, hv, hc, rfl⟩
    exact h v hv hc
  funext p
  exact closure_minimal hs (isClosed_eq hF continuous_sourceWeilEnergy) (dense_compactTests p)

theorem sourceWeilPair_symm (p q : SourceGraph) : sourceWeilPair p q = sourceWeilPair q p := by
  simp only [sourceWeilPair, sourcePair_symm p q]
  ring

theorem sourceWeilPair_add_left (p q r : SourceGraph) :
    sourceWeilPair (p+q) r = sourceWeilPair p r + sourceWeilPair q r := by
  simp only [sourceWeilPair, sourcePair_add_left, sourceCoshMoment, sourceSinhMoment,
    map_add, inner_add_right]
  ring

theorem sourceWeilPair_smul_left (a : ℝ) (p q : SourceGraph) :
    sourceWeilPair (a • p) q = a*sourceWeilPair p q := by
  simp only [sourceWeilPair, sourcePair_smul_left, sourceCoshMoment, sourceSinhMoment,
    map_smul, real_inner_smul_right]
  ring

/-- The extension retains every mixed term, not just individual diagonal energies. -/
theorem sourceWeilPair_polarization (p q : SourceGraph) :
    sourceWeilPair p q =
      (sourceWeilEnergy (p+q)-sourceWeilEnergy p-sourceWeilEnergy q)/2 := by
  simp only [sourceWeilEnergy, sourceWeilPair_add_left, sourceWeilPair_symm q (p+q),
    sourceWeilPair_symm p (p+q), sourceWeilPair_add_left]
  rw [sourceWeilPair_symm q p]
  ring

/-- Every admitted vector is approximated by original tests with the complete Weil value converging. -/
theorem exists_compact_Weil_approximation (p : SourceGraph) :
    ∃ (v : ℕ → ℝ → ℝ) (hv : ∀ n, ContDiff ℝ 2 (v n))
      (hc : ∀ n, HasCompactSupport (v n)),
      Tendsto (fun n => compactLift (v n) (hv n) (hc n)) atTop (𝓝 p) ∧
      Tendsto (fun n =>
        (weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
          (EF.weilTest (fun x => (phiDoobTest (v n) x : ℂ))
            (fun x => (phiDoobTest (v n) x : ℂ)))).re)
        atTop (𝓝 (sourceWeilEnergy p)) := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp (dense_compactTests p)
  have hex (n : ℕ) : ∃ v hv hc, u n = compactLift v hv hc := hu n
  choose v hv hc he using hex
  have heq : u = fun n => compactLift (v n) (hv n) (hc n) := funext he
  rw [heq] at ht
  refine ⟨v, hv, hc, ht, ?_⟩
  simpa only [Function.comp_def, sourceWeilEnergy_compactLift] using
    (continuous_sourceWeilEnergy.tendsto p).comp ht

end RHTower.CHMDDoobGraph
