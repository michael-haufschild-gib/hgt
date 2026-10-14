import GaloisForLFunctions.RHTower.JointAncestryLevelOneDensityConditional
import GaloisForLFunctions.RHTower.JointAncestryLevelOneDensityReal
import GaloisForLFunctions.RHTower.JointAncestryLevelOneCapstones
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Positivity of the actual signed level-one density

The construction, Fourier identification and conditional recovery are
unconditional. Nonnegativity of this particular density is equivalent to the
existing level-one JAS positivity criterion, hence to RH.
-/

namespace RHTower

open MeasureTheory Filter GaloisForLFunctions.HTGeometry
open scoped BigOperators Topology

noncomputable section

theorem continuous_jasZeroSumDensity_levelOne (P : Finset Nat.Primes) :
    Continuous (fun x : UnitAddTorus Nat.Primes =>
      jasZeroSumDensity (1 / 2) P (fun i => fourier 1 (x i))) :=
  (continuousOn_jasZeroSumDensity (by positivity) P).comp_continuous
    (by fun_prop) (fun x i => norm_fourier_unit 1 (x i))

theorem ae_re_jasLevelOneFiniteDensity_nonneg_of_psd
    (hpsd : JasDressedPSD 1) (P : Finset Nat.Primes) :
    ∀ᵐ x ∂torusHaar Nat.Primes, 0 ≤ (jasLevelOneFiniteDensity P x).re := by
  have h : JasDressedPSD ((1 / 2 : ℝ) + 1 / 2) := by
    simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by ring] using hpsd
  filter_upwards [coeFn_jasLevelOneFiniteDensity P] with x hx
  rw [hx]
  exact re_tsum_prod_jasHoloLocal_nonneg_of_psd (by positivity) h P
    (fun i => fourier 1 (x i)) (fun i => norm_fourier_unit 1 (x i))

theorem ae_re_jasLevelOneDensity_nonneg_of_psd (hpsd : JasDressedPSD 1) :
    ∀ᵐ x ∂torusHaar Nat.Primes, 0 ≤ (jasLevelOneDensity x).re := by
  obtain ⟨ns, _hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp tendsto_jasLevelOneFiniteDensity).exists_seq_tendsto_ae
  have hfinite : ∀ᵐ x ∂torusHaar Nat.Primes, ∀ N,
      0 ≤ (jasLevelOneFiniteDensity (jasPrimePrefix N) x).re :=
    ae_all_iff.mpr fun N => ae_re_jasLevelOneFiniteDensity_nonneg_of_psd hpsd _
  filter_upwards [hlim, hfinite] with x hx hn
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hx)
    (Eventually.of_forall fun N => hn (ns N))

theorem re_jasZeroSumDensity_levelOne_nonneg_of_density
    (h : ∀ᵐ x ∂torusHaar Nat.Primes, 0 ≤ (jasLevelOneDensity x).re)
    (P : Finset Nat.Primes) (x : UnitAddTorus Nat.Primes) :
    0 ≤ (jasZeroSumDensity (1 / 2) P (fun i => fourier 1 (x i))).re := by
  have hint := (Lp.memLp jasLevelOneDensity).integrable (show (1 : ENNReal) ≤ 2 by norm_num)
  have hc := ContinuousLinearMap.comp_condExp_comm (m := torusCoordinateSigma P)
    hint Complex.reCLM
  have hn := condExp_nonneg (m := torusCoordinateSigma P) h
  have hae : ∀ᵐ y ∂torusHaar Nat.Primes,
      0 ≤ (jasZeroSumDensity (1 / 2) P (fun i => fourier 1 (y i))).re := by
    filter_upwards [hc, hn, condExp_jasLevelOneDensity P] with y hy hny hdy
    change ((torusHaar Nat.Primes)[jasLevelOneDensity | torusCoordinateSigma P] y).re =
      (torusHaar Nat.Primes)[fun z => (jasLevelOneDensity z).re | torusCoordinateSigma P] y at hy
    rw [← hy, hdy] at hny
    exact hny
  have hdense := Measure.dense_of_ae (μ := torusHaar Nat.Primes) hae
  have hclosed : IsClosed {y : UnitAddTorus Nat.Primes |
      0 ≤ (jasZeroSumDensity (1 / 2) P (fun i => fourier 1 (y i))).re} :=
    isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_jasZeroSumDensity_levelOne P))
  have heq := dense_iff_closure_eq.mp hdense
  rw [hclosed.closure_eq] at heq
  exact Set.eq_univ_iff_forall.mp heq x

theorem jasDressedPSD_one_of_ae_re_jasLevelOneDensity_nonneg
    (h : ∀ᵐ x ∂torusHaar Nat.Primes, 0 ≤ (jasLevelOneDensity x).re) : JasDressedPSD 1 := by
  classical
  have hpt (P : Finset Nat.Primes) (w : ↥P → ℂ) (hw : ∀ i, ‖w i‖ = 1) :
      0 ≤ (jasZeroSumDensity (1 / 2) P w).re := by
    let z : ↥P → Circle := fun i => ⟨w i, mem_sphere_zero_iff_norm.mpr (hw i)⟩
    let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
    let θ : ↥P → UnitAddCircle := fun i => e.symm (z i)
    let x : UnitAddTorus Nat.Primes := fun p => if hp : p ∈ P then θ ⟨p, hp⟩ else 0
    have hx (i : ↥P) : fourier 1 (x i) = w i := by
      simp only [x, dif_pos i.2]
      rw [fourier_one, ← AddCircle.homeomorphCircle_apply one_ne_zero]
      exact congrArg (fun a : Circle => (a : ℂ)) (e.apply_symm_apply (z i))
    have hn := re_jasZeroSumDensity_levelOne_nonneg_of_density h P x
    simpa only [show (fun i : ↥P => fourier 1 (x i)) = w from funext hx] using hn
  simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by ring] using
    jasDressedPSD_of_pointwise (c := 1 / 2) (by positivity) hpt

theorem jasDressedPSD_one_iff_ae_re_jasLevelOneDensity_nonneg :
    JasDressedPSD 1 ↔ ∀ᵐ x ∂torusHaar Nat.Primes, 0 ≤ (jasLevelOneDensity x).re :=
  ⟨ae_re_jasLevelOneDensity_nonneg_of_psd, jasDressedPSD_one_of_ae_re_jasLevelOneDensity_nonneg⟩

theorem riemannHypothesis_iff_ae_re_jasLevelOneDensity_nonneg :
    RiemannHypothesis ↔ ∀ᵐ x ∂torusHaar Nat.Primes, 0 ≤ (jasLevelOneDensity x).re :=
  riemannHypothesis_iff_jasDressedPSD_one.trans
    jasDressedPSD_one_iff_ae_re_jasLevelOneDensity_nonneg

theorem re_integral_jasLevelOneDensity_pos :
    0 < (∫ x, jasLevelOneDensity x ∂torusHaar Nat.Primes).re := by
  rw [integral_jasLevelOneDensity, Complex.ofReal_re]
  exact poleSharpConstant_pos

end

end RHTower
