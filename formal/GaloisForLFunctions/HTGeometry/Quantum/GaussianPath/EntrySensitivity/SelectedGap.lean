import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-! # Density points of first-return gap levels in physical coefficient space -/
open Set MeasureTheory Matrix Filter Topology Metric
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity
noncomputable section
open PrescribedTimes
abbrev Labels (n : ℕ) := Fin (Fintype.card (Fin (n+2)→Bool))

/-- Ordered energy levels as functions of all physical coefficients. -/
def levels (n : ℕ) (x : PrefixIndex n→ℝ) : Labels n→ℝ :=
  sortedTuple ((prefixGenerator n x).2.isHermitian.eigenvalues ∘ (Fintype.equivFin _).symm)

theorem continuous_levels (n : ℕ) : Continuous (levels n) := by
  let e := Fintype.equivFin (Fin (n+2)→Bool)
  let F (x : PrefixIndex n→ℝ) := Matrix.reindex e e (numberedGenerator n x)
  have h : Continuous (numberedGenerator n) := by
    unfold numberedGenerator
    fun_prop
  have hF : Continuous F := by
    change Continuous (fun x => Matrix.reindex e e (numberedGenerator n x))
    exact continuous_pi fun j => continuous_pi fun l =>
      (continuous_apply (e.symm l)).comp ((continuous_apply (e.symm j)).comp h)
  have hh (x : PrefixIndex n→ℝ) : (F x).IsHermitian := (prefixGenerator n x).2.isHermitian.reindex e
  have hcont := continuous_sortedTuple_eigenvalues hF hh
  have he (x : PrefixIndex n→ℝ) : sortedTuple (hh x).eigenvalues=levels n x :=
    sortedTuple_eigenvalues_reindex e (prefixGenerator n x).2.isHermitian
  simpa only [he] using hcont

/-- Numbered energy levels are a permutation of the physical eigenvalues. -/
theorem level_labels (n : ℕ) (x : PrefixIndex n→ℝ) :
    ∃ p : Labels n ≃ (Fin (n+2)→Bool), ∀ j, levels n x j=(prefixGenerator n x).2.isHermitian.eigenvalues (p j) := by
  let e := Fintype.equivFin (Fin (n+2)→Bool)
  exact ⟨(Tuple.sort ((prefixGenerator n x).2.isHermitian.eigenvalues ∘ e.symm)).trans e.symm,fun _ => rfl⟩

/-- Both the near-Hilbert crossing and the subsequent first empty date
are selected afresh from the supplied coefficient vector. -/
def selectedDate (n : ℕ) (x : PrefixIndex n→ℝ) : ℝ :=
  crossingOrigin n (nearHilbertContinuousCircuitBudget (n+2)) (9/80) x+
    crossingWait n (nearHilbertContinuousCircuitBudget (n+2)) 0 x

theorem measurable_selectedDate (n : ℕ) : Measurable (selectedDate n) :=
  (measurable_crossingOrigin ..).add (measurable_crossingWait ..)

theorem selectedDate_eq (n : ℕ) (x : PrefixIndex n→ℝ) :
    selectedDate n x=PrecisionReturns.firstVisit (prefixGenerator n x)
      (crossingOrigin n (nearHilbertContinuousCircuitBudget (n+2)) (9/80) x) 0 (1/10) := by
  dsimp only [selectedDate,crossingWait,PrecisionReturns.firstVisit_physical_error]
  ring

/-- Density in shrinking coefficient cubes centered at x. -/
def fullDensityAt {n : ℕ} (S : Set (PrefixIndex n→ℝ)) (x : PrefixIndex n→ℝ) : Prop :=
  Tendsto (fun r : ℝ => volume (S∩closedBall x r)/volume (closedBall x r)) (𝓝[>] 0) (𝓝 1)

private theorem density_points {n : ℕ} {S : Set (PrefixIndex n→ℝ)} (hS : MeasurableSet S) :
    ∀ᵐ x ∂volume, x∈S → fullDensityAt S x := by
  apply (ae_restrict_iff' hS).mp
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div (volume : Measure (PrefixIndex n→ℝ)) S 1] with x hx
  apply hx (fun _ : ℝ => x) id tendsto_id
  filter_upwards [self_mem_nhdsWithin] with r hr
  apply mem_closedBall_self
  change 0 ≤ 1*r
  rw [one_mul]
  exact le_of_lt (show 0 < r from hr)

/-- Every countably indexed contact level which contains the sampled
prefix also has density one there. The label pair and winding can
therefore be selected after the crossing and its first return. -/
theorem gaussian_selected_gap_density (r : ℝ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      ∀ (i j : Labels n) (m : ℤ),
        let S := {y | selectedDate n y*(levels n y i-levels n y j)=2*Real.pi*((m:ℝ)+r)}
        x∈S → fullDensityAt S x := by
  apply ae_all_iff.mpr
  intro n
  have hp (i j : Labels n) (m : ℤ) :
      ∀ᵐ x ∂(volume : Measure (PrefixIndex n→ℝ)),
        let S := {y | selectedDate n y*(levels n y i-levels n y j)=2*Real.pi*((m:ℝ)+r)}
        x∈S → fullDensityAt S x := by
    apply density_points
    have hc (k : Labels n) : Continuous (fun y => levels n y k) := (continuous_apply k).comp (continuous_levels n)
    exact measurableSet_eq_fun ((measurable_selectedDate n).mul ((hc i).measurable.sub (hc j).measurable)) measurable_const
  have hall := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (hp i j)))
  have hac : centredProductGaussian (PrefixIndex n) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous (Fintype.card (ChainLabel (n+2))) one_ne_zero (fun _ => 0)
  exact (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae (hac.ae_le hall)

#print axioms gaussian_selected_gap_density
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity
