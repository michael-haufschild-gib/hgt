import GaloisForLFunctions.RHTower.Suzuki.SuzukiForcedStripLineBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiStripTransportUniform
import GaloisForLFunctions.RHTower.StripFourierTranslation

/-!
# The glued forced Gamma solution is a strip datum, and `(16)`

The zero-trace forced solution on the upper unit strip is holomorphic there, grows at most
polynomially on every closed substrip, and — under the weighted source bound `(14)` — is square
integrable on every interior line.  Those are exactly the three properties of a `StripDatum`, so the
vector-valued Paley–Wiener translation applies and produces one frequency profile `F` with

`e^{2πσL}F(L) ∈ L²(ℝ;X)` for every `0 < σ < 1`.

Holomorphy is the homogeneous branch together with the branch cancellation of the particular
solution; the growth is the substrip-uniform transport bound; and the line `L²` bound is the
quantitative Hardy estimate, transported from the horizontal representation by the primitive
property of the segment integral.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal FourierTransform

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {b : ℂ → X} {T : X →L[ℂ] X}

/-- The glued forced solution on the upper unit strip. -/
def forcedStripSolution (E : ℂ → ℂ) (T : X →L[ℂ] X) (cp : X) (b : ℂ → X) (z : ℂ) : X :=
  stripSolution E T cp z + forcedParticular E T b z

/-- **The glued forced solution is a strip datum.** -/
theorem stripDatum_forcedStripSolution
    (hT : IsSelfAdjoint T) (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ w ∈ imStrip (-1) 1, E w ≠ 0)
    (hbd : DifferentiableOn ℂ b (imStrip (-1) 1))
    (hbgrow : ∀ σ₁ : ℝ, 0 ≤ σ₁ → σ₁ < 1 → ∃ (D : ℝ) (n : ℕ), 0 ≤ D ∧
      ∀ w : ℂ, w.im ∈ Icc (0 : ℝ) σ₁ → ‖b w‖ ≤ D * (1 + ‖w‖) ^ n)
    (hbint : ∀ σ : ℝ, σ ∈ Ioo (0 : ℝ) 1 →
      (∫⁻ t : ℝ, ENNReal.ofReal ((1 + |t|) ^ ((1 : ℝ) / 2 + σ)
        * ‖b ((t : ℂ) + (σ : ℂ) * Complex.I)‖)) < ⊤)
    (cp : X) :
    StripDatum (forcedStripSolution E T cp b) := by
  have hsub : imStrip 0 1 ⊆ imStrip (-1) 1 := fun z hz => ⟨by linarith [hz.1], hz.2⟩
  have hdiff : DifferentiableOn ℂ (forcedStripSolution E T cp b) (imStrip 0 1) :=
    (differentiableOn_stripSolution hEd T cp).add
      ((differentiableOn_forcedParticular_imStrip T hEd hEne hbd).mono hsub)
  refine ⟨hdiff, ?_, ?_⟩
  · -- polynomial growth on every closed substrip
    intro σ₀ σ₁ h0 h01 h1
    obtain ⟨D₁, hD₁0, hD₁⟩ := exists_bound_norm_stripSolution hT hE cp h0 h01 h1
    obtain ⟨Db, n, hDb0, hDb⟩ := hbgrow σ₁ (by linarith) h1
    obtain ⟨P, hP0, hP⟩ :=
      exists_bound_forcedParticular_substrip hT hE (by linarith : (0 : ℝ) ≤ σ₁) h1 hDb0 hDb
    refine ⟨D₁ + P, n + 2, by linarith, fun z hz => ?_⟩
    have hz0 : z.im ∈ Icc (0 : ℝ) σ₁ := ⟨by linarith [hz.1], hz.2⟩
    have hpow : (1 : ℝ) ≤ (1 + ‖z‖) ^ (n + 2) :=
      one_le_pow₀ (by linarith [norm_nonneg z])
    calc ‖forcedStripSolution E T cp b z‖
        ≤ ‖stripSolution E T cp z‖ + ‖forcedParticular E T b z‖ := norm_add_le _ _
      _ ≤ D₁ + P * (1 + ‖z‖) ^ (n + 2) := add_le_add (hD₁ z hz) (hP z hz0)
      _ ≤ (D₁ + P) * (1 + ‖z‖) ^ (n + 2) := by nlinarith [hpow, hD₁0, hP0]
  · -- square integrability on every interior line
    intro σ hσ
    have hmemline : ∀ x : ℝ, ((x : ℂ) + (σ : ℂ) * Complex.I) ∈ imStrip 0 1 := by
      intro x
      constructor <;> simp [hσ.1, hσ.2]
    have hcont : Continuous (fun x : ℝ => forcedStripSolution E T cp b
        ((x : ℂ) + (σ : ℂ) * Complex.I)) := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      have hline : ContinuousAt (fun u : ℝ => ((u : ℂ) + (σ : ℂ) * Complex.I)) x := by fun_prop
      have hd : DifferentiableAt ℂ (forcedStripSolution E T cp b)
          ((x : ℂ) + (σ : ℂ) * Complex.I) :=
        hdiff.differentiableAt ((isOpen_imStrip 0 1).mem_nhds (hmemline x))
      have hcomp : ContinuousAt ((forcedStripSolution E T cp b)
          ∘ (fun u : ℝ => ((u : ℂ) + (σ : ℂ) * Complex.I))) x :=
        ContinuousAt.comp hd.continuousAt hline
      exact hcomp
    have hbridge : ∀ x : ℝ, forcedStripSolution E T cp b ((x : ℂ) + (σ : ℂ) * Complex.I)
        = forcedStripLine E T (cp + forcedSegmentIntegral E T b ((0 : ℂ) + (σ : ℂ) * Complex.I))
            (fun t : ℝ => b ((t : ℂ) + (σ : ℂ) * Complex.I)) σ x := fun x =>
      stripSolution_add_forcedParticular_eq_forcedStripLine hEd hEne hbd cp hσ x
    have hfin : (∫⁻ x : ℝ,
        ‖forcedStripSolution E T cp b ((x : ℂ) + (σ : ℂ) * Complex.I)‖ₑ ^ 2) < ⊤ := by
      have := lintegral_enorm_sq_forcedStripLine_lt_top hT hE
        (cp + forcedSegmentIntegral E T b ((0 : ℂ) + (σ : ℂ) * Complex.I))
        (fun t : ℝ => b ((t : ℂ) + (σ : ℂ) * Complex.I)) hσ.1 hσ.2 (hbint σ hσ)
      refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) this
      rw [hbridge x]
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
    refine ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) hfin
    rw [Real.enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **`(16)`: one frequency profile carries every interior line of the forced solution.** -/
theorem exists_memLp_exp_smul_forcedStripFourier
    (hT : IsSelfAdjoint T) (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ w ∈ imStrip (-1) 1, E w ≠ 0)
    (hbd : DifferentiableOn ℂ b (imStrip (-1) 1))
    (hbgrow : ∀ σ₁ : ℝ, 0 ≤ σ₁ → σ₁ < 1 → ∃ (D : ℝ) (n : ℕ), 0 ≤ D ∧
      ∀ w : ℂ, w.im ∈ Icc (0 : ℝ) σ₁ → ‖b w‖ ≤ D * (1 + ‖w‖) ^ n)
    (hbint : ∀ σ : ℝ, σ ∈ Ioo (0 : ℝ) 1 →
      (∫⁻ t : ℝ, ENNReal.ofReal ((1 + |t|) ^ ((1 : ℝ) / 2 + σ)
        * ‖b ((t : ℂ) + (σ : ℂ) * Complex.I)‖)) < ⊤)
    (cp : X) :
    ∃ F : ℝ → X, ∀ σ : ℝ, ∀ hσ : σ ∈ Ioo (0 : ℝ) 1,
      (∀ᵐ L : ℝ,
          ((𝓕⁻ (stripDatumLp
              (stripDatum_forcedStripSolution hT hEd hE hEne hbd hbgrow hbint cp) hσ) :
            Lp X 2 (volume : Measure ℝ)) : ℝ → X) L
          = Real.exp (2 * Real.pi * σ * L) • F L)
        ∧ MemLp (fun L : ℝ => Real.exp (2 * Real.pi * σ * L) • F L) 2 (volume : Measure ℝ) :=
  exists_memLp_exp_smul_stripDatumFourier
    (stripDatum_forcedStripSolution hT hEd hE hEne hbd hbgrow hbint cp)

end GaloisForLFunctions.RHTower
