import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthSingularXiLanding
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Off-diagonal Krein realization of the joint-depth source-to-Xi landing

The primitive and reciprocal-promotion legs of the literal `(prime, depth)` source are not the
same Hilbert vector.  Treating either leg as a positive Gram square therefore changes the source
problem.  Their canonical carrier is instead the doubled Hilbert space with fundamental symmetry
swapping the two legs.  The resulting indefinite matrix coefficient is exactly the von Mangoldt
Laplace channel.

This supplies the signed/off-diagonal producer left alive by the positive-completion obstruction.
The two polar channels and the fixed Gamma connection then land this literal Krein coefficient in
the Xi relative resolvent.  The construction is Hilbert-valued on the positive Laplace chamber;
its scalar continuation across the balanced-reflection wall remains genuinely singular, as the
previous nonsummability theorem requires.

No Xi-zero coordinate, Riemann-hypothesis premise, or zero-location input enters the source.
-/

open Complex Function Set Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Literal joint `(prime, depth)` Hilbert carrier. -/
abbrev XiGammaEulerPrimitiveJointDepthHilbert : Type :=
  lp (fun _ : Nat.Primes × ℕ => ℂ) 2

/-- Genuine Hilbert direct sum on which source and reciprocal-promotion co-source remain resolved. -/
abbrev XiGammaEulerPrimitiveJointDepthKrein : Type :=
  PiLp 2 (fun _ : Fin 2 => XiGammaEulerPrimitiveJointDepthHilbert)

/-- The nontrivial involution of the two source slots. -/
def xiGammaEulerPrimitiveJointDepthKreinSlotSwap : Fin 2 ≃ Fin 2 :=
  Equiv.swap 0 1

/-- Unitary fundamental symmetry interchanging the two resolved source legs. -/
def xiGammaEulerPrimitiveJointDepthFundamentalSymmetry :
    XiGammaEulerPrimitiveJointDepthKrein ≃ₗᵢ[ℂ]
      XiGammaEulerPrimitiveJointDepthKrein :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ
    XiGammaEulerPrimitiveJointDepthHilbert
    xiGammaEulerPrimitiveJointDepthKreinSlotSwap

@[simp]
theorem xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_apply_zero
    (x : XiGammaEulerPrimitiveJointDepthKrein) :
    xiGammaEulerPrimitiveJointDepthFundamentalSymmetry x 0 = x 1 := by
  simp [xiGammaEulerPrimitiveJointDepthFundamentalSymmetry,
    xiGammaEulerPrimitiveJointDepthKreinSlotSwap,
    LinearIsometryEquiv.piLpCongrLeft_apply]

@[simp]
theorem xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_apply_one
    (x : XiGammaEulerPrimitiveJointDepthKrein) :
    xiGammaEulerPrimitiveJointDepthFundamentalSymmetry x 1 = x 0 := by
  simp [xiGammaEulerPrimitiveJointDepthFundamentalSymmetry,
    xiGammaEulerPrimitiveJointDepthKreinSlotSwap,
    LinearIsometryEquiv.piLpCongrLeft_apply]

/-- The source symmetry is an involution, so it is a genuine Krein fundamental symmetry. -/
theorem xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_sq
    (x : XiGammaEulerPrimitiveJointDepthKrein) :
    xiGammaEulerPrimitiveJointDepthFundamentalSymmetry
        (xiGammaEulerPrimitiveJointDepthFundamentalSymmetry x) = x := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp

/-- The unitary involution is self-adjoint.  This is the operator-theoretic condition omitted by a
mere Banach-product swap and makes the following form a genuine Krein form. -/
theorem xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_selfAdjoint
    (x y : XiGammaEulerPrimitiveJointDepthKrein) :
    inner ℂ x (xiGammaEulerPrimitiveJointDepthFundamentalSymmetry y) =
      inner ℂ (xiGammaEulerPrimitiveJointDepthFundamentalSymmetry x) y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two,
    xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_apply_zero,
    xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_apply_one]
  exact add_comm _ _

/-- Hermitian indefinite pairing selected by the source/co-source interchange. -/
def xiGammaEulerPrimitiveJointDepthKreinPair
    (x y : XiGammaEulerPrimitiveJointDepthKrein) : ℂ :=
  inner ℂ x (xiGammaEulerPrimitiveJointDepthFundamentalSymmetry y)

theorem xiGammaEulerPrimitiveJointDepthKreinPair_apply
    (x y : XiGammaEulerPrimitiveJointDepthKrein) :
    xiGammaEulerPrimitiveJointDepthKreinPair x y =
      inner ℂ (x 0) (y 1) + inner ℂ (x 1) (y 0) := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair, PiLp.inner_apply]
  simp only [Fin.sum_univ_two,
    xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_apply_zero,
    xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_apply_one]

/-- The swap pairing is Hermitian. -/
theorem xiGammaEulerPrimitiveJointDepthKreinPair_conj_symm
    (x y : XiGammaEulerPrimitiveJointDepthKrein) :
    star (xiGammaEulerPrimitiveJointDepthKreinPair y x) =
      xiGammaEulerPrimitiveJointDepthKreinPair x y := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_apply,
    xiGammaEulerPrimitiveJointDepthKreinPair_apply]
  change
    (starRingEnd ℂ) (inner ℂ (y 0) (x 1) + inner ℂ (y 1) (x 0)) =
      inner ℂ (x 0) (y 1) + inner ℂ (x 1) (y 0)
  rw [map_add, inner_conj_symm, inner_conj_symm]
  exact add_comm _ _

/-- Positive diagonal sector of the fundamental decomposition. -/
def xiGammaEulerPrimitiveJointDepthKreinDiagonal
    (h : XiGammaEulerPrimitiveJointDepthHilbert) :
    XiGammaEulerPrimitiveJointDepthKrein :=
  PiLp.single 2 0 h + PiLp.single 2 1 h

/-- Negative anti-diagonal sector of the fundamental decomposition. -/
def xiGammaEulerPrimitiveJointDepthKreinAntidiagonal
    (h : XiGammaEulerPrimitiveJointDepthHilbert) :
    XiGammaEulerPrimitiveJointDepthKrein :=
  PiLp.single 2 0 h - PiLp.single 2 1 h

/-- The diagonal source sector is strictly positive away from zero. -/
theorem xiGammaEulerPrimitiveJointDepthKreinPair_diagonal
    (h : XiGammaEulerPrimitiveJointDepthHilbert) :
    xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinDiagonal h)
        (xiGammaEulerPrimitiveJointDepthKreinDiagonal h) =
      2 * (‖h‖ : ℂ) ^ (2 : ℕ) := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_apply]
  simp [xiGammaEulerPrimitiveJointDepthKreinDiagonal]
  ring_nf

/-- The anti-diagonal source sector is strictly negative away from zero. -/
theorem xiGammaEulerPrimitiveJointDepthKreinPair_antidiagonal
    (h : XiGammaEulerPrimitiveJointDepthHilbert) :
    xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinAntidiagonal h)
        (xiGammaEulerPrimitiveJointDepthKreinAntidiagonal h) =
      -2 * (‖h‖ : ℂ) ^ (2 : ℕ) := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_apply]
  simp [xiGammaEulerPrimitiveJointDepthKreinAntidiagonal]
  ring_nf

theorem xiGammaEulerPrimitiveJointDepthKreinPair_antidiagonal_re_neg
    {h : XiGammaEulerPrimitiveJointDepthHilbert} (hh : h ≠ 0) :
    (xiGammaEulerPrimitiveJointDepthKreinPair
      (xiGammaEulerPrimitiveJointDepthKreinAntidiagonal h)
      (xiGammaEulerPrimitiveJointDepthKreinAntidiagonal h)).re < 0 := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_antidiagonal]
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hre : (-2 * (‖h‖ : ℂ) ^ (2 : ℕ)).re = -2 * ‖h‖ ^ (2 : ℕ) := by
    norm_num [Complex.mul_re, pow_two]
  rw [hre]
  nlinarith [sq_pos_of_pos hnorm]

/-- Resolved primitive source leg. -/
def xiGammaEulerPrimitiveJointDepthKreinSourceLeg
    (w : ℂ) (hw : 0 < w.re) : XiGammaEulerPrimitiveJointDepthKrein :=
  PiLp.single 2 0 (xiGammaEulerPrimitiveCommonTestSourceLp w hw)

/-- Resolved reciprocal-promotion co-source leg. -/
def xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg
    (v : ℂ) (hv : 0 < v.re) : XiGammaEulerPrimitiveJointDepthKrein :=
  PiLp.single 2 1 (xiGammaEulerPrimitiveCommonTestCoSourceLp v hv)

/-- **Literal off-diagonal Euler producer.**  The Krein cross-pair of the two actual source legs is
the complete prime-power von Mangoldt Laplace channel. -/
theorem xiGammaEulerPrimitiveJointDepthKreinPair_coSource_source_eq
    (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) :
    xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg v hv)
        (xiGammaEulerPrimitiveJointDepthKreinSourceLeg w hw) =
      vonMangoldtPrimeLaplaceChannelComplex (w + star v) := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_apply]
  simp [xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg,
    xiGammaEulerPrimitiveJointDepthKreinSourceLeg]
  exact inner_xiGammaEulerPrimitiveCommonTestCoSource_source_eq w v hw hv

/-- On the common Hilbert chamber the Krein coefficient is exactly the maximal scalar
codiagonal, not a substitute positive Gram. -/
theorem xiGammaEulerPrimitiveJointDepthKreinPair_eq_pairedCodiagonal
    (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) :
    xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg v hv)
        (xiGammaEulerPrimitiveJointDepthKreinSourceLeg w hw) =
      xiGammaEulerPrimitiveJointDepthPairedCodiagonal w v := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_coSource_source_eq]
  exact (xiGammaEulerPrimitiveJointDepthPairedCodiagonal_eq (by
    linarith)).symm

/-- Canonical equal-real-part split of a positive Laplace displacement. -/
def xiGammaEulerPrimitiveJointDepthKreinSourceParameter (u : ℂ) : ℂ :=
  u / 2

/-- Co-source parameter whose conjugate adds to the other half of `u`. -/
def xiGammaEulerPrimitiveJointDepthKreinCoSourceParameter (u : ℂ) : ℂ :=
  star u / 2

theorem xiGammaEulerPrimitiveJointDepthKreinSourceParameter_re
    (u : ℂ) :
    (xiGammaEulerPrimitiveJointDepthKreinSourceParameter u).re = u.re / 2 := by
  norm_num [xiGammaEulerPrimitiveJointDepthKreinSourceParameter,
    Complex.div_re]

theorem xiGammaEulerPrimitiveJointDepthKreinCoSourceParameter_re
    (u : ℂ) :
    (xiGammaEulerPrimitiveJointDepthKreinCoSourceParameter u).re =
      u.re / 2 := by
  norm_num [xiGammaEulerPrimitiveJointDepthKreinCoSourceParameter,
    Complex.div_re]

theorem xiGammaEulerPrimitiveJointDepthKreinParameter_codiagonal
    (u : ℂ) :
    xiGammaEulerPrimitiveJointDepthKreinSourceParameter u +
        star (xiGammaEulerPrimitiveJointDepthKreinCoSourceParameter u) = u := by
  change u / 2 + (starRingEnd ℂ) ((starRingEnd ℂ) u / 2) = u
  simp only [map_div₀, starRingEnd_self_apply, map_ofNat]
  ring

/-- Canonically split source leg for one positive Laplace displacement. -/
def xiGammaEulerPrimitiveJointDepthKreinSplitSource
    (u : ℂ) (hu : 0 < u.re) : XiGammaEulerPrimitiveJointDepthKrein :=
  xiGammaEulerPrimitiveJointDepthKreinSourceLeg
    (xiGammaEulerPrimitiveJointDepthKreinSourceParameter u) (by
      rw [xiGammaEulerPrimitiveJointDepthKreinSourceParameter_re]
      linarith)

/-- Canonically split co-source leg for one positive Laplace displacement. -/
def xiGammaEulerPrimitiveJointDepthKreinSplitCoSource
    (u : ℂ) (hu : 0 < u.re) : XiGammaEulerPrimitiveJointDepthKrein :=
  xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg
    (xiGammaEulerPrimitiveJointDepthKreinCoSourceParameter u) (by
      rw [xiGammaEulerPrimitiveJointDepthKreinCoSourceParameter_re]
      linarith)

/-- The canonical split retains the exact unsquared von Mangoldt channel. -/
theorem xiGammaEulerPrimitiveJointDepthKreinSplitPair_eq
    (u : ℂ) (hu : 0 < u.re) :
    xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinSplitCoSource u hu)
        (xiGammaEulerPrimitiveJointDepthKreinSplitSource u hu) =
      vonMangoldtPrimeLaplaceChannelComplex u := by
  rw [xiGammaEulerPrimitiveJointDepthKreinSplitCoSource,
    xiGammaEulerPrimitiveJointDepthKreinSplitSource,
    xiGammaEulerPrimitiveJointDepthKreinPair_coSource_source_eq,
    xiGammaEulerPrimitiveJointDepthKreinParameter_codiagonal]

/-- Polar fill of the canonical signed/off-diagonal Euler coefficient. -/
def xiGammaEulerPrimitiveJointDepthKreinPoleFilled
    (u : ℂ) (hu : 0 < u.re) : ℂ :=
  1 / u + 1 / (u + 1) -
    xiGammaEulerPrimitiveJointDepthKreinPair
      (xiGammaEulerPrimitiveJointDepthKreinSplitCoSource u hu)
      (xiGammaEulerPrimitiveJointDepthKreinSplitSource u hu)

/-- The polar-filled Krein coefficient is the regularized critical-Mellin defect. -/
theorem xiGammaEulerPrimitiveJointDepthKreinPoleFilled_eq_regularized
    (u : ℂ) (hu : 0 < u.re) :
    xiGammaEulerPrimitiveJointDepthKreinPoleFilled u hu =
      regularizedCriticalMellinDefect u := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPoleFilled,
    xiGammaEulerPrimitiveJointDepthKreinSplitPair_eq]
  have hland := xiGammaEulerPrimitiveJointDepthLaplaceDefect_eq_regularized
    (w := u) (v := 0) (by simpa using hu)
  rw [xiGammaEulerPrimitiveJointDepthLaplaceDefect,
    xiGammaEulerPrimitiveJointDepthPairedCodiagonal_eq (by simpa using hu)] at hland
  simpa using hland

/-- Gamma completion of the polar-filled literal Krein coefficient. -/
def xiGammaEulerPrimitiveJointDepthKreinCompletedTrace
    (u : ℂ) (hu : 0 < u.re) : ℂ :=
  I * (xiGammaEulerPrimitiveJointDepthKreinPoleFilled u hu +
    gammaRealLogConnection (u + 1))

/-- **Unconditional signed source-to-Xi landing.**  On the positive source chamber, the completed
Xi relative resolvent is the polar/Gamma completion of one explicit off-diagonal Krein matrix
coefficient of the literal joint `(prime, depth)` source. -/
theorem xiGammaEulerPrimitiveJointDepthKreinCompletedTrace_eq_xiRelativeResolventTrace
    {u : ℂ} (hu : 0 < u.re) (hzeta : riemannZeta (u + 1) ≠ 0) :
    xiGammaEulerPrimitiveJointDepthKreinCompletedTrace u hu =
      xiRelativeResolventTrace (criticalMellinToCenteredXi u) := by
  rw [xiGammaEulerPrimitiveJointDepthKreinCompletedTrace,
    xiGammaEulerPrimitiveJointDepthKreinPoleFilled_eq_regularized]
  exact
    xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_eq_xiRelativeResolventTrace
      (by linarith) (by
        intro hzero
        rw [hzero] at hu
        norm_num at hu) hzeta

/-- At balanced reflection the literal cross-term is not absolutely summable.  Therefore the
Krein landing cannot be extended across the wall by pretending its two Hilbert legs remain
ordinary vectors; the existing scalar continuation is essential. -/
theorem xiGammaEulerPrimitiveJointDepthKreinBalancedCrossTerm_not_summable
    (a : ℝ) :
    ¬Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveCommonTestSourceCoeff (a : ℂ) pe *
        star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff (-a : ℂ) pe)) :=
  not_summable_xiGammaEulerPrimitiveBalancedReflectionCoeff a

end

end RHTower
