import GaloisForLFunctions.RHTower.ThetaDivisorDecayClass
import GaloisForLFunctions.RHTower.CHMDGraphDivisorPairing

/-!
# Exact finite Xi-divisor pairings in the completed CHMD graph

All regularity, decay, and domain obligations are discharged on the finite
divisor family. The last theorem supplies an unconditional nonzero instance.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

/-- A complex source and both its real signed pairings are realized in the actual graph. -/
theorem exists_complex_signed_graph {u : ℝ → ℂ} (hu : ExponentialFirstJet u)
    (hl : ∃ C, LipschitzWith C u)
    (hb : ∃ M, ∀ x, ‖u x‖ ≤ M * thetaCuspFullSource x) :
    ∃ p q : SourceGraph,
      p ∈ closure (compactTests : Set SourceGraph) ∧
      q ∈ closure (compactTests : Set SourceGraph) ∧
      p.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (u x).re) ∧
      q.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (u x).im) ∧
      complexSource p q =ᵐ[volume] u ∧
      sourceEnergy p = signedZeroEnergy (fun x => (u x).re) ∧
      sourceEnergy q = signedZeroEnergy (fun x => (u x).im) ∧
      sourcePair p q = signedZeroPair (fun x => (u x).re) (fun x => (u x).im) := by
  obtain ⟨p, q, hp, hq, hpr, hqi, hsource⟩ := exists_complex_relative_graph hl hb
  obtain ⟨C, hC⟩ := hl
  obtain ⟨M, hM⟩ := hb
  simp_rw [thetaCuspFullSource_eq_riemannKernelReal] at hM
  have hrl : ∃ A, LipschitzWith A (fun x => (u x).re) :=
    ⟨1*C, RCLike.lipschitzWith_re.comp hC⟩
  have hil : ∃ A, LipschitzWith A (fun x => (u x).im) :=
    ⟨1*C, RCLike.lipschitzWith_im.comp hC⟩
  have hrb : ∃ N, ∀ x, |(u x).re| ≤ N * riemannKernelReal x :=
    ⟨M, fun x => (Complex.abs_re_le_norm _).trans (hM x)⟩
  have hib : ∃ N, ∀ x, |(u x).im| ≤ N * riemannKernelReal x :=
    ⟨M, fun x => (Complex.abs_im_le_norm _).trans (hM x)⟩
  exact ⟨p, q, hp, hq, hpr, hqi, hsource,
    sourceEnergy_eq_signedZeroEnergy hu.re hrl hrb hpr,
    sourceEnergy_eq_signedZeroEnergy hu.im hil hib hqi,
    sourcePair_eq_signedZeroPair hu.re hu.im hrl hil hrb hib hpr hqi⟩

/-- Every admissible finite divisor quotient has its exact signed zero pairing
in the compact-test completion, with no residual analytic admission premise. -/
theorem finite_divisor_signed_graph {L : List ℂ} (hL : ThetaDivisionList L)
    (e : Polynomial ℂ) (he : e.natDegree ≤ L.length) :
    ∃ p q : SourceGraph,
      p ∈ closure (compactTests : Set SourceGraph) ∧
      q ∈ closure (compactTests : Set SourceGraph) ∧
      p.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (listComb thetaListDivision L e x).re) ∧
      q.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (listComb thetaListDivision L e x).im) ∧
      complexSource p q =ᵐ[volume] listComb thetaListDivision L e ∧
      sourceEnergy p = signedZeroEnergy (fun x => (listComb thetaListDivision L e x).re) ∧
      sourceEnergy q = signedZeroEnergy (fun x => (listComb thetaListDivision L e x).im) ∧
      sourcePair p q = signedZeroPair (fun x => (listComb thetaListDivision L e x).re)
        (fun x => (listComb thetaListDivision L e x).im) ∧
      ∀ z, sourceTransform (complexSource p q) z * listDivisor L z = XiC z * e.eval (z ^ 2) := by
  obtain ⟨_, _, hb, hT, _⟩ := listComb_spec hL e he
  obtain ⟨p, q, hp, hq, hpr, hqi, hsource, hE, hF, hB⟩ :=
    exists_complex_signed_graph (exponentialFirstJet_listComb hL e) (exists_lipschitz_listComb L e) hb
  refine ⟨p, q, hp, hq, hpr, hqi, hsource, hE, hF, hB, fun z => ?_⟩
  rw [sourceTransform_congr_ae hsource]
  exact hT z

/-- Unconditional nonzero divisor source, its exact Fourier division, and the
full signed energy and mixed pairing inside the original arithmetic graph. -/
theorem exists_exact_zero_division_signed_graph :
    ∃ (γ : ℝ) (p q : SourceGraph), 0 < γ ∧ XiC (γ : ℂ) = 0 ∧
      p ∈ closure (compactTests : Set SourceGraph) ∧
      q ∈ closure (compactTests : Set SourceGraph) ∧
      complexSource p q =ᵐ[volume] zeroDivision (γ : ℂ) thetaSourceC ∧
      sourceTransform (complexSource p q) 0 = XiC 0 ∧
      sourceTransform (complexSource p q) 0 ≠ 0 ∧
      sourceEnergy p = signedZeroEnergy (fun x => (zeroDivision (γ : ℂ) thetaSourceC x).re) ∧
      sourceEnergy q = signedZeroEnergy (fun x => (zeroDivision (γ : ℂ) thetaSourceC x).im) ∧
      sourcePair p q = signedZeroPair (fun x => (zeroDivision (γ : ℂ) thetaSourceC x).re)
        (fun x => (zeroDivision (γ : ℂ) thetaSourceC x).im) ∧
      ∀ z, ((γ : ℂ) ^ 2 - z ^ 2) * sourceTransform (complexSource p q) z =
        (γ : ℂ) ^ 2 * XiC z := by
  obtain ⟨γ, hγ, hzero, _, _⟩ := exists_positive_thetaZeroDivision
  have hdec := exponentialFirstJet_zeroDivision expMomentSource_thetaSourceC thetaSourceC_neg
    contDiff_thetaSourceC (show sourceTransform thetaSourceC (γ : ℂ) = 0 by
      rw [sourceTransform_thetaSourceC, hzero])
  obtain ⟨p, q, hp, hq, _, _, hsource, hE, hF, hB⟩ := exists_complex_signed_graph hdec
    (exists_lipschitz_thetaListDivision [(γ : ℂ)])
    (exists_norm_thetaListDivision_le [(γ : ℂ)])
  have hT (z : ℂ) : ((γ : ℂ) ^ 2 - z ^ 2) * sourceTransform (complexSource p q) z =
      (γ : ℂ) ^ 2 * XiC z := by
    rw [sourceTransform_congr_ae hsource]
    simpa only [sourceTransform_thetaSourceC, hzero, sub_zero] using
      expMomentSource_thetaSourceC.sourceTransform_zeroDivision thetaSourceC_neg (γ : ℂ) z
  have hγ0 : (γ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hγ.ne')
  have hmass : sourceTransform (complexSource p q) 0 = XiC 0 := by
    have hz : (γ : ℂ) ^ 2 * (sourceTransform (complexSource p q) 0 - XiC 0) = 0 := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_sub] using
        sub_eq_zero.mpr (hT 0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hγ0)
  exact ⟨γ, p, q, hγ, hzero, hp, hq, hsource, hmass, hmass ▸ XiC_zero_ne, hE, hF, hB, hT⟩

end RHTower.CHMDDoobGraph
