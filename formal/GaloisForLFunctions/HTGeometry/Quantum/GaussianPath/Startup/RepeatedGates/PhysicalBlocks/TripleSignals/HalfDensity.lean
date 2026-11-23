import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.WindowMeasure

/-! # Visit separation at half a gate per bond -/
open MeasureTheory Filter Set Matrix Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section

private abbrev Hpath (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- Two physical visits whose total budget approaches one gate per bond
cannot have a separation in any positive compact interval. -/
theorem gaussian_excluded_compact_lags {a T : ℝ} (ha : 0<a) :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v w : ℝ, |w-v| ∈ Icc a T →
      ∀ j s : ℕ, ∀ ε δ : ℝ, ε+δ≤1/4 →
      HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution (Hpath ω n).val v) →
      HasProjectiveCircuitApproximation (n+2) δ s (unitaryEvolution (Hpath ω n).val w) →
        (1+c)*(n+1:ℕ) < ((j+s:ℕ):ℝ) := by
  obtain ⟨c,hc,h⟩ := gaussian_strict_spanning_floor (T:=T) ha
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro v w hlag j s ε δ hsum hv hw
  have hfit := affordable_add_time (Hpath ω n) (x := -v) (y := w) (hv.neg_time _) hw
  rw [show -v+w=w-v by ring] at hfit
  obtain ⟨z,hz,C,hC,he⟩ := hfit
  exact hn (w-v) hlag (j+s) ⟨z,hz,C,hC,he.trans hsum⟩

/-- Every bounded observation window contains vanishing affordable
duration even when the budget exceeds half the bonds by o(N). Both
the budget and the window origin may be selected after the draw. -/
theorem gaussian_half_density_residence (T : ℝ) (hT : 0≤T) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (s : ℕ → ℕ) (v : ℕ → ℝ),
      (∀ c : ℝ, 0<c → ∀ᶠ n : ℕ in atTop, 2*(s n:ℝ)≤(1+c)*(n+1:ℕ)) →
      Tendsto (fun n => volume.real ({t | HasProjectiveCircuitApproximation (n+2) (1/10) (s n)
        (unitaryEvolution (Hpath ω n).val t)} ∩ Icc (v n) (v n+T))) atTop (𝓝 0) := by
  let j (m : ℕ) : ℝ := 1/((m:ℝ)+1)
  let B := max T 1
  have hB : 0<B := zero_lt_one.trans_le (le_max_right ..)
  have hj (m : ℕ) : 0<j m := by dsimp only [j]; positivity
  choose c hc h using fun m : ℕ => gaussian_excluded_compact_lags (T:=B) (hj m)
  filter_upwards [ae_all_iff.mpr h] with ω hw
  intro s v hs
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_gt (2/ε)
  have hsmall : j m < ε/2 := by
    apply (div_lt_iff₀ (by positivity : 0<(m:ℝ)+1)).mpr
    have hh := (div_lt_iff₀ hε).mp hm
    linarith only [hh,hε]
  filter_upwards [hw m,hs (c m) (hc m)] with n hn hb
  let E := {t | HasProjectiveCircuitApproximation (n+2) (1/10) (s n)
    (unitaryEvolution (Hpath ω n).val t)}
  have hg (u : ℝ) (hu : u∈E) (w : ℝ) (hw : w∈E) : |w-u|<j m ∨ B<|w-u| := by
    by_contra! hx
    have hh := hn u w hx (s n) (s n) (1/10) (1/10) (by norm_num) hu hw
    rw [Nat.cast_add] at hh
    linarith only [hh,hb]
  have hmass := SpanningDensity.LocalEcho.occupation_of_forbidden_lags E (j m) B (hj m).le hB hg (v n) T hT
  have hratio : T/B≤1 := (div_le_one hB).mpr (le_max_left ..)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  exact hmass.trans_lt (by linarith only [hsmall,mul_le_mul_of_nonneg_right hratio (hj m).le])

#print axioms gaussian_excluded_compact_lags
#print axioms gaussian_half_density_residence
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
