import GaloisForLFunctions.goldbach.LiLiu.Conclusions.Hypotheses
import GaloisForLFunctions.goldbach.LiLiu.Boundary.CorrelationForm
import GaloisForLFunctions.goldbach.LiLiu.Spectral.RelativeScale
import GaloisForLFunctions.goldbach.LiLiu.RepresentationBound
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! # Conditional binary Goldbach estimates of Li and Liu -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Filter
open scoped Topology Quaternion
noncomputable section

/-- The constants in both weighted estimates depend only on the test. The
prescribed function h is quantified after the constant has been chosen. -/
theorem conditional_weighted_estimates (φ : TestWeight) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ h : ℕ → ℝ, admissibleWidth h → eventualEvenGRH → hypothesisS h →
        ∀ᶠ N : ℕ in atTop, Even N →
          |correlation φ N - φ.mass * singularSeries N| ≤ C * (singularSeries N / h N)) ∧
      (eventualEvenGRH → hypothesisR → ∀ᶠ N : ℕ in atTop, Even N →
          |correlation φ N - φ.mass * singularSeries N| ≤ C * spectralScale N) := by
  obtain ⟨C,hC,herr⟩ := goldbach_error_le_hardyOperator φ
  refine ⟨C,hC,?_,?_⟩
  · intro h hh hgrh hS
    filter_upwards [eventually_large_strip,hh.2.2,hgrh,hS] with N hlarge hw hg hs he
    obtain ⟨hN,hl⟩ := hlarge
    obtain ⟨k,rfl⟩ : ∃ k, N=k+2 := ⟨N-2,by omega⟩
    have g := hg he
    have hedge := leftEdge_bounds hl
    let T := hardyOperator (n := k+1) hN g hedge.1 hedge.2.le
    have hsym := hardyOperator_symmetric (n := k+1) hN g hedge.1 hedge.2.le
    have hhs := hardyOperator_hilbertSchmidt (n := k+1) hN g hedge.1 hedge.2.le
    have hz : ∀ q : ℍ, 1-exclusionWidth h (k+2) < q.re →
        quaternionSpectralProduct T (spectralScale (k+2)) q ≠ 0 := hs he hN g hl
    apply (herr k hN g hedge.1 hedge.2 (by linarith only [hl])).trans
    exact mul_le_mul_of_nonneg_left (norm_le_singularSeries_div_of_exclusion (by omega) (hh.1 _) hw hsym
      (complex_zero_of_quaternion_zeroFree hsym hhs _ _ hz)) hC
  · intro hgrh hR
    filter_upwards [eventually_large_strip,hgrh,hR] with N hlarge hg hr he
    obtain ⟨hN,hl⟩ := hlarge
    obtain ⟨k,rfl⟩ : ∃ k, N=k+2 := ⟨N-2,by omega⟩
    have g := hg he
    have hedge := leftEdge_bounds hl
    let T := hardyOperator (n := k+1) hN g hedge.1 hedge.2.le
    have hsym := hardyOperator_symmetric (n := k+1) hN g hedge.1 hedge.2.le
    have hhs := hardyOperator_hilbertSchmidt (n := k+1) hN g hedge.1 hedge.2.le
    have hz : ∀ q : ℍ, quaternionSpectralProduct T (spectralScale (k+2)) q=0 → q.re=1/2 := hr he hN g hl
    apply (herr k hN g hedge.1 hedge.2 (by linarith only [hl])).trans
    exact mul_le_mul_of_nonneg_left (norm_bound_of_critical hsym (spectralScale_pos (by omega))
      (complex_critical_of_quaternion_critical hsym hhs _ hz)) hC

/-- Either spectral condition gives a relative error tending to zero on even targets. -/
theorem conditional_relative_error (φ : TestWeight) (hg : eventualEvenGRH)
    (hs : (∃ h, admissibleWidth h ∧ hypothesisS h) ∨ hypothesisR) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |correlation φ N - φ.mass * singularSeries N| ≤ ε * singularSeries N := by
  obtain ⟨C,hC,hS,hR⟩ := conditional_weighted_estimates φ
  rcases hs with ⟨h,hh,hs⟩ | hr
  · filter_upwards [hS h hh hg hs,hh.2.1.eventually_ge_atTop (C/ε)] with N he hb hEven
    have hc : C/h N ≤ ε := (div_le_iff₀ (hh.1 _)).mpr (by
      have H := (div_le_iff₀ hε).mp hb
      simpa only [mul_comm] using H)
    calc
      _ ≤ C * (singularSeries N / h N) := he hEven
      _ = (C/h N)*singularSeries N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (singularSeries_pos N).le
  · have hsmall : Tendsto (fun N : ℕ => C*(spectralScale N/singularSeries N)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := C)).mul spectralScale_div_singularSeries_tendsto
    filter_upwards [hR hg hr,hsmall.eventually_lt_const hε] with N he hb hEven
    exact (he hEven).trans ((div_le_iff₀ (singularSeries_pos N)).mp
      (by simpa only [mul_div_assoc] using hb.le))

/-- The weighted Goldbach correlation is asymptotic to its varying main term along the even integers. -/
theorem conditional_weighted_asymptotic (φ : TestWeight) (hg : eventualEvenGRH)
    (hs : (∃ h, admissibleWidth h ∧ hypothesisS h) ∨ hypothesisR) :
    Asymptotics.IsEquivalent (atTop ⊓ Filter.principal {N : ℕ | Even N})
      (correlation φ) (fun N => φ.mass * singularSeries N) := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro ε hε
  apply eventually_inf_principal.mpr
  filter_upwards [conditional_relative_error φ hg hs (mul_pos hε φ.mass_pos)] with N he hEven
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_pos (mul_pos φ.mass_pos (singularSeries_pos N)),
    mul_assoc] using he hEven

private theorem conditional_weighted_lower (φ : TestWeight) (hg : eventualEvenGRH)
    (hs : (∃ h, admissibleWidth h ∧ hypothesisS h) ∨ hypothesisR) :
    ∀ᶠ N : ℕ in atTop, Even N → φ.mass/2 * singularSeries N ≤ correlation φ N := by
  filter_upwards [conditional_relative_error φ hg hs (half_pos φ.mass_pos)] with N he hEven
  linarith only [(abs_le.mp (he hEven)).1]

/-- For all sufficiently large even N, at least (cφ/4) S(N)N/(log N)²
ordered prime pairs have both endpoints in [N/3,2N/3]. -/
theorem conditional_goldbach_count (φ : TestWeight) (hg : eventualEvenGRH)
    (hs : (∃ h, admissibleWidth h ∧ hypothesisS h) ∨ hypothesisR) :
    ∀ᶠ N : ℕ in atTop, Even N →
      φ.mass/4 * singularSeries N * N / Real.log N ^ 2 ≤ (centralPrimePairs N).card :=
  count_of_eventual_weighted_lower φ (conditional_weighted_lower φ hg hs)

/-- The existence conclusion uses one fixed smooth central bump. -/
theorem conditional_goldbach (hg : eventualEvenGRH)
    (hs : (∃ h, admissibleWidth h ∧ hypothesisS h) ∨ hypothesisR) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=N ∧
      (p : ℝ) ∈ Set.Icc ((N:ℝ)/3) (2*N/3) ∧ (q : ℝ) ∈ Set.Icc ((N:ℝ)/3) (2*N/3) :=
  prime_pair_of_eventual_weighted_lower centralBump (conditional_weighted_lower centralBump hg hs)

#print axioms conditional_weighted_estimates
#print axioms conditional_weighted_asymptotic
#print axioms conditional_goldbach_count
#print axioms conditional_goldbach
end
end GaloisForLFunctions.Goldbach.LiLiu
