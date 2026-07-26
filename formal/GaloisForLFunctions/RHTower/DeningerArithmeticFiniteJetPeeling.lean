import GaloisForLFunctions.RHTower.DeningerArithmeticLocalTaylorApproximation
import GaloisForLFunctions.RHTower.DeningerArithmeticFiniteJetSection

/-!
# Finite jet peeling in compact-open arithmetic cohomology

For a compact-open entire source `F` and a geometric Xi window, finite Hermite interpolation
produces an entire polynomial `P` with the same multiplicity-bounded jets in that window.  The
difference `F - P` is locally divisible by Xi on the corresponding disk.  Cauchy--Taylor
approximation of that local quotient then makes

`(F - P) - XiC * Q_j`

converge locally uniformly to zero on every smaller disk.

Thus every source class is compact-open approximable, modulo an actual Xi coboundary, by a finite
jet representative.  This is the finite peeling core of `[DAC_LOCAL_QUOTIENT_OPENNESS]`.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/--
Finite geometric Hermite peeling followed by local Xi-quotient Taylor approximation.

The interpolation window has radius `n + 2`, the Cauchy radius is `n + 1`, and convergence is
asserted on the disk of radius `n`.
-/
theorem exists_deningerCompactOpenFiniteJetPeeling
    (F : DeningerCompactOpenEntire) (n : ℕ) :
    ∃ P : DeningerCompactOpenEntire,
      (∀ (rho :
          ↥(deningerXiSupportClosedBallFinset (n + 2)))
          (k : DeningerArithmeticJetIndex rho.1),
        deningerCompactOpenJet
            (xiSpectralPointSupport rho.1) k P =
          deningerCompactOpenJet
            (xiSpectralPointSupport rho.1) k F) ∧
      TendstoLocallyUniformlyOn
        (fun j z =>
          (F - P) z -
            XiC z *
              deningerLocalXiQuotientTaylorApprox
                (F - P) (n + 1) j z)
        (fun _ => 0)
        atTop (Metric.ball 0 n) := by
  let packet :=
    deningerXiSupportClosedBallFinset (n + 2)
  let target :
      (rho : ↥packet) →
        DeningerArithmeticJetIndex rho.1 → ℂ :=
    fun rho k =>
      deningerCompactOpenJet
        (xiSpectralPointSupport rho.1) k F
  obtain ⟨P, hP⟩ :=
    exists_deningerCompactOpenPolynomial_finiteXiScalarJets
      packet target
  refine ⟨P, ?_, ?_⟩
  · intro rho k
    exact hP rho k
  · apply
      deningerLocalXiTaylorCoboundaryError_tendstoLocallyUniformlyOn
        (F - P)
        (show (n : NNReal) < n + 1 by
          exact_mod_cast Nat.lt_succ_self n)
        (show (n + 1 : NNReal) < n + 2 by
          exact_mod_cast Nat.lt_succ_self (n + 1))
    intro rho hrho k
    have hrhoLe :
        ‖xiSpectralPointSupport rho‖ ≤ (n + 2 : ℝ) :=
      le_of_lt (by
        simpa only [Nat.cast_add, Nat.cast_ofNat,
          NNReal.coe_natCast] using hrho)
    have hrhoMem :
        rho ∈ packet := by
      change
        rho ∈
          deningerXiSupportClosedBallFinset
            (n + 2)
      exact
        (mem_deningerXiSupportClosedBallFinset
          (n + 2) rho).2 (by simpa using hrhoLe)
    have hPk :=
      hP ⟨rho, hrhoMem⟩ k
    change
      deningerCompactOpenJet
          (xiSpectralPointSupport rho) k
          (F - P) = 0
    calc
      deningerCompactOpenJet
          (xiSpectralPointSupport rho) k
          (F - P) =
          deningerCompactOpenJet
              (xiSpectralPointSupport rho) k F -
            deningerCompactOpenJet
              (xiSpectralPointSupport rho) k P :=
        (deningerCompactOpenJet
          (xiSpectralPointSupport rho) k).map_sub F P
      _ = 0 := by
        apply sub_eq_zero.mpr
        simpa only [target] using hPk.symm

/--
Canonical continuous-linear finite jet representative has the same local peeling property.

Unlike the existential version, this representative tends continuously to zero with its finite
jet packet.
-/
theorem deningerCompactOpenFiniteJetRepresentative_peeling
    (F : DeningerCompactOpenEntire) (n : ℕ) :
    let S := deningerXiSupportClosedBallFinset (n + 2)
    let P :=
      deningerCompactOpenFiniteJetRepresentative S F
    TendstoLocallyUniformlyOn
      (fun j z =>
        (F - P) z -
          XiC z *
            deningerLocalXiQuotientTaylorApprox
              (F - P) (n + 1) j z)
      (fun _ => 0)
      atTop (Metric.ball 0 n) := by
  dsimp only
  let packet :=
    deningerXiSupportClosedBallFinset (n + 2)
  let P :=
    deningerCompactOpenFiniteJetRepresentative
      packet F
  apply
    deningerLocalXiTaylorCoboundaryError_tendstoLocallyUniformlyOn
      (F - P)
      (show (n : NNReal) < n + 1 by
        exact_mod_cast Nat.lt_succ_self n)
      (show (n + 1 : NNReal) < n + 2 by
        exact_mod_cast Nat.lt_succ_self (n + 1))
  intro rho hrho k
  have hrhoLe :
      ‖xiSpectralPointSupport rho‖ ≤ (n + 2 : ℝ) :=
    le_of_lt (by
      simpa only [Nat.cast_add, Nat.cast_ofNat,
        NNReal.coe_natCast] using hrho)
  have hrhoMem :
      rho ∈ packet := by
    change
      rho ∈
        deningerXiSupportClosedBallFinset
          (n + 2)
    exact
      (mem_deningerXiSupportClosedBallFinset
        (n + 2) rho).2 (by simpa using hrhoLe)
  let idx :
      DeningerArithmeticFiniteJetCoordinate packet :=
    ⟨⟨rho, hrhoMem⟩, k⟩
  have hcoord :=
    congrFun
      (deningerCompactOpenFiniteJets_representative
        packet F) idx
  change
    deningerCompactOpenJet
        (xiSpectralPointSupport rho) k
        (F - P) = 0
  calc
    deningerCompactOpenJet
        (xiSpectralPointSupport rho) k
        (F - P) =
        deningerCompactOpenJet
            (xiSpectralPointSupport rho) k F -
          deningerCompactOpenJet
            (xiSpectralPointSupport rho) k P :=
      (deningerCompactOpenJet
        (xiSpectralPointSupport rho) k).map_sub F P
    _ = 0 := by
      apply sub_eq_zero.mpr
      exact hcoord.symm

end

end RHTower
