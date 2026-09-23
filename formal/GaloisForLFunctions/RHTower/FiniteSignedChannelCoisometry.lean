import Mathlib.Tactic

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Synthesis along a distinguished signed channel in a finite Hilbert direct sum. -/
def finiteSignedChannelSynthesis {ι : Type*} [Fintype ι]
    (w f : ι → ℂ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (w i) * f i

/-- The adjoint analysis map of a finite signed channel. -/
def finiteSignedChannelAnalysis {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (c : ℂ) (i : ι) : ℂ :=
  w i * c

/-- The rank-one channel projection `R*R`. -/
def finiteSignedChannelProjection {ι : Type*} [Fintype ι]
    (w f : ι → ℂ) (i : ι) : ℂ :=
  finiteSignedChannelAnalysis w (finiteSignedChannelSynthesis w f) i

theorem finiteSignedChannelSynthesis_analysis {ι : Type*} [Fintype ι]
    {w : ι → ℂ} (hw : ∑ i, ‖w i‖ ^ (2 : ℕ) = 1) (c : ℂ) :
    finiteSignedChannelSynthesis w (finiteSignedChannelAnalysis w c) = c := by
  simp only [finiteSignedChannelSynthesis, finiteSignedChannelAnalysis]
  simp_rw [← mul_assoc, Complex.conj_mul']
  rw [← Finset.sum_mul]
  have hwc : ∑ i, ((‖w i‖ : ℂ) ^ (2 : ℕ)) = 1 := by
    exact_mod_cast hw
  rw [hwc, one_mul]

theorem finiteSignedChannelProjection_idempotent {ι : Type*} [Fintype ι]
    {w : ι → ℂ} (hw : ∑ i, ‖w i‖ ^ (2 : ℕ) = 1) (f : ι → ℂ) :
    finiteSignedChannelProjection w (finiteSignedChannelProjection w f) =
      finiteSignedChannelProjection w f := by
  funext i
  change finiteSignedChannelAnalysis w
      (finiteSignedChannelSynthesis w
        (finiteSignedChannelAnalysis w (finiteSignedChannelSynthesis w f))) i =
    finiteSignedChannelAnalysis w (finiteSignedChannelSynthesis w f) i
  rw [finiteSignedChannelSynthesis_analysis hw]

theorem finiteSignedChannelSynthesis_projection {ι : Type*} [Fintype ι]
    {w : ι → ℂ} (hw : ∑ i, ‖w i‖ ^ (2 : ℕ) = 1) (f : ι → ℂ) :
    finiteSignedChannelSynthesis w (finiteSignedChannelProjection w f) =
      finiteSignedChannelSynthesis w f := by
  change finiteSignedChannelSynthesis w
    (finiteSignedChannelAnalysis w (finiteSignedChannelSynthesis w f)) = _
  rw [finiteSignedChannelSynthesis_analysis hw]

theorem finiteSignedChannelProjection_analysis {ι : Type*} [Fintype ι]
    {w : ι → ℂ} (hw : ∑ i, ‖w i‖ ^ (2 : ℕ) = 1) (c : ℂ) :
    finiteSignedChannelProjection w (finiteSignedChannelAnalysis w c) =
      finiteSignedChannelAnalysis w c := by
  funext i
  change finiteSignedChannelAnalysis w
      (finiteSignedChannelSynthesis w (finiteSignedChannelAnalysis w c)) i =
    finiteSignedChannelAnalysis w c i
  rw [finiteSignedChannelSynthesis_analysis hw]

/-- Exact incidence factorization: a coupled scalar feature sees only the signed projection. -/
theorem finiteSignedChannel_incidence_factorization {ι : Type*} [Fintype ι]
    {w : ι → ℂ} (hw : ∑ i, ‖w i‖ ^ (2 : ℕ) = 1)
    (Z : ℂ) (f : ι → ℂ) :
    Z * finiteSignedChannelSynthesis w f =
      Z * finiteSignedChannelSynthesis w (finiteSignedChannelProjection w f) := by
  rw [finiteSignedChannelSynthesis_projection hw]

end RHTower

