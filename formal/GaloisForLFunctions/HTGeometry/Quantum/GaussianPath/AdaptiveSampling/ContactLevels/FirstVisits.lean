import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.Periods
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Precision of the first affordable tick on a physical contact clock -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
open AccuracyScales.MaximumIntervals ExactContacts.CoarseVisits PrecisionReturns ResonantReturns
noncomputable section

/-- A Lipschitz distance maps exceptional periods to a null set of
contact heights even after translating the clock origin. -/
theorem ae_contact_transfer {P : ℝ → Prop} (hP : ∀ᵐ τ : ℝ ∂volume, P τ)
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) (o : ℝ) :
    ∀ᵐ e : ℝ ∂volume, ∀ t, f t=e → P (t-o) := by
  let Z := {τ | ¬ P τ}
  have hz : volume Z=0 := ae_iff.mp hP
  let g (τ : ℝ) := f (o+τ)
  have hnull : volume (g '' Z)=0 := by
    have hh := (hf.comp (isometry_add_left o).lipschitz).hausdorffMeasure_image_le (zero_le_one' ℝ) Z
    simpa only [hausdorffMeasure_real,hz,mul_zero,nonpos_iff_eq_zero] using hh
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with e he t ht
  by_contra h
  apply he
  exact ⟨t-o,h,by change f (o+(t-o))=e; rwa [show o+(t-o)=t by abel]⟩

/-- On each typical chain choose a countable family of time offsets,
which can include the actual first crossing. At almost every coarse
error, every positive elapsed time from an offset to a boundary contact
has the full discrete first-index exponent. -/
theorem gaussian_contact_clocks :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ b : ℕ → ℕ → ℝ, ∀ᵐ e : ℝ ∂volume,
      ∀ (k l s : ℕ) (t : ℝ), b k l < t → orbitCircuitDistance (chainGenerator ω k) s t=e →
        ∀ j : ℕ, j+1 < k+3 → Tendsto
          (fun ε => log (firstIndex (chainGenerator ω k) (t-b k l) j ε)/log (1/ε))
          (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
  filter_upwards [gaussian_clock_periods] with ω hω b
  have H := ae_all_iff.mpr fun k => ae_all_iff.mpr fun l => ae_all_iff.mpr fun s =>
    ae_contact_transfer (hω k) (orbitCircuitDistance_lipschitz (chainGenerator ω k) s) (b k l)
  filter_upwards [H] with e he k l s t hlt hd
  exact he k l s t hd (sub_pos.mpr hlt)

/-- At almost every coarse error, the first visit from any outside
origin gives the full D−1 fine precision exponent, for both its absolute
date and any positive elapsed date measured from the chosen offsets. -/
theorem gaussian_first_visit_clocks :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ b : ℕ → ℕ → ℝ, ∀ᵐ e : ℝ ∂volume, 0 < e →
      ∀ (k l s : ℕ) (a : ℝ), let H := chainGenerator ω k
        e < orbitCircuitDistance H s a → let v := firstVisit H a s e
          ∀ o ∈ ({0,b k l} : Set ℝ), o < v → ∀ j : ℕ, j+1 < k+3 →
            Tendsto (fun ε => log (firstIndex H (v-o) j ε)/log (1/ε))
              (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
  filter_upwards [gaussian_contact_clocks] with ω hω b
  filter_upwards [hω b,hω (fun _ _ => 0)] with e hb hz he k l s a
  intro H hout v o ho hv j hj
  have hd := firstVisit_distance H a s he hout
  rcases ho with h | h
  · subst o
    exact hz k l s v hv hd j hj
  · have heq : o=b k l := h
    subst o
    exact hb k l s v hv hd j hj

#print axioms gaussian_first_visit_clocks
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
