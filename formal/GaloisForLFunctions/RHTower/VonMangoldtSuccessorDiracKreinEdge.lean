import GaloisForLFunctions.HTGeometry.TransportMomentKreinWeld
import GaloisForLFunctions.RHTower.VonMangoldtSuccessorPrincipalRelativeHankel

/-!
# Source-edge Dirac--Krein realization of the von Mangoldt successor current

The principal-relative successor current is lifted before prime contraction to the disjoint
logarithmic edges `[log n, log (n+1)]`.  Its two first-order channels carry the exchange form.
Every lifted jet has a summable positive Hilbert majorant, while its indefinite Gram is exactly
the cofinal successor Hankel current.

The realization is deliberately classified as formal closure: the two Gram identities below
identify it with the already existing principal-relative current.  It does not close the joint
prime--Jacobi/Euler-trace interface.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- One source-edge contribution to the lifted Dirac--Krein Gram. -/
def vonMangoldtSuccessorDiracKreinEdgeTerm (i j n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n *
    ∫ t in Real.log (n : ℝ)..Real.log (n + 1 : ℝ),
      HTGeometry.exchangePair
        (HTGeometry.transportDiracJet i t)
        (HTGeometry.transportDiracJet j t)

/-- The first-order edge lift reproduces the source-relative moment term before summation. -/
theorem vonMangoldtSuccessorDiracKreinEdgeTerm_eq
    (i j n : ℕ) :
    vonMangoldtSuccessorDiracKreinEdgeTerm i j n =
      vonMangoldtSuccessorRelativeMomentTerm (i + j + 2) n := by
  rw [vonMangoldtSuccessorDiracKreinEdgeTerm,
    HTGeometry.intervalIntegral_exchangePair_transportDiracJet]
  simp only [vonMangoldtSuccessorRelativeMomentTerm,
    vonMangoldtAdditiveLogJetDifference, vonMangoldtAdditiveLogJet,
    Nat.cast_add, Nat.cast_one]

/-- Every cofinal lifted exchange pairing is absolutely summable. -/
theorem summable_vonMangoldtSuccessorDiracKreinEdgeTerm
    (i j : ℕ) :
    Summable (vonMangoldtSuccessorDiracKreinEdgeTerm i j) := by
  rw [show vonMangoldtSuccessorDiracKreinEdgeTerm i j =
      vonMangoldtSuccessorRelativeMomentTerm (i + j + 2) by
    funext n
    exact vonMangoldtSuccessorDiracKreinEdgeTerm_eq i j n]
  exact summable_vonMangoldtSuccessorRelativeMomentTerm (i + j + 2)

/-- Finite-aperture source-edge Dirac--Krein Gram. -/
def finiteVonMangoldtSuccessorDiracKreinGram
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ p : Fin M,
    vonMangoldtSuccessorDiracKreinEdgeTerm i j ((p : ℕ) + 2)

/-- **Finite source-edge realization.**  Restricting the edge carrier to an aperture gives
exactly the existing principal-relative successor matrix. -/
theorem finiteVonMangoldtSuccessorDiracKreinGram_eq
    (M N : ℕ) :
    finiteVonMangoldtSuccessorDiracKreinGram M N =
      finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N := by
  ext i j
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply]
  simp only [finiteVonMangoldtSuccessorDiracKreinGram,
    finiteVonMangoldtSuccessorRelativeMoment,
    vonMangoldtSuccessorDiracKreinEdgeTerm_eq]

/-- Aperture growth is literal orthogonal edge adjunction: one new source edge contributes one
additional exchange-Gram term and leaves every old edge unchanged. -/
theorem finiteVonMangoldtSuccessorDiracKreinGram_succ_apply
    (M N : ℕ) (i j : Fin N) :
    finiteVonMangoldtSuccessorDiracKreinGram (M + 1) N i j =
      finiteVonMangoldtSuccessorDiracKreinGram M N i j +
        vonMangoldtSuccessorDiracKreinEdgeTerm i j (M + 2) := by
  rw [finiteVonMangoldtSuccessorDiracKreinGram,
    finiteVonMangoldtSuccessorDiracKreinGram, Fin.sum_univ_castSucc]
  rfl

/-- Cofinal source-edge Dirac--Krein Gram before finite jet restriction. -/
def vonMangoldtSuccessorDiracKreinGram (i j : ℕ) : ℝ :=
  ∑' m : ℕ, vonMangoldtSuccessorDiracKreinEdgeTerm i j (m + 2)

/-- **Cofinal source-edge realization.**  The lifted exchange Gram is the universal
principal-relative Hankel kernel. -/
theorem vonMangoldtSuccessorDiracKreinGram_eq
    (i j : ℕ) :
    vonMangoldtSuccessorDiracKreinGram i j =
      vonMangoldtSuccessorPrincipalRelativeKernel i j := by
  simp only [vonMangoldtSuccessorDiracKreinGram,
    vonMangoldtSuccessorDiracKreinEdgeTerm_eq,
    vonMangoldtSuccessorPrincipalRelativeKernel,
    vonMangoldtSuccessorRelativeMoment]

/-- Positive Hilbert-majorant mass of one lifted jet on one source edge. -/
def vonMangoldtSuccessorDiracMajorantEdgeTerm (i n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n *
    ∫ t in Real.log (n : ℝ)..Real.log (n + 1 : ℝ),
      HTGeometry.transportDiracMajorant i t

/-- The Hilbert-majorant edge mass is a fixed positive linear combination of two already
summable source-relative moments. -/
theorem vonMangoldtSuccessorDiracMajorantEdgeTerm_eq
    (i n : ℕ) :
    vonMangoldtSuccessorDiracMajorantEdgeTerm i n =
      ((((i + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / ((2 * i + 1 : ℕ) : ℝ)) *
          vonMangoldtSuccessorRelativeMomentTerm (2 * i + 1) n +
        (1 / ((2 * i + 3 : ℕ) : ℝ)) *
          vonMangoldtSuccessorRelativeMomentTerm (2 * i + 3) n := by
  rw [vonMangoldtSuccessorDiracMajorantEdgeTerm,
    HTGeometry.intervalIntegral_transportDiracMajorant]
  unfold vonMangoldtSuccessorRelativeMomentTerm
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  simp only [Nat.cast_add, Nat.cast_one]
  push_cast
  ring

/-- Every actual lifted jet has finite Hilbert-majorant mass on the complete source-edge carrier. -/
theorem summable_vonMangoldtSuccessorDiracMajorantEdgeTerm
    (i : ℕ) :
    Summable (vonMangoldtSuccessorDiracMajorantEdgeTerm i) := by
  rw [show vonMangoldtSuccessorDiracMajorantEdgeTerm i =
      fun n =>
        ((((i + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / ((2 * i + 1 : ℕ) : ℝ)) *
            vonMangoldtSuccessorRelativeMomentTerm (2 * i + 1) n +
          (1 / ((2 * i + 3 : ℕ) : ℝ)) *
            vonMangoldtSuccessorRelativeMomentTerm (2 * i + 3) n by
    funext n
    exact vonMangoldtSuccessorDiracMajorantEdgeTerm_eq i n]
  exact
    ((summable_vonMangoldtSuccessorRelativeMomentTerm (2 * i + 1)).mul_left
      ((((i + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / ((2 * i + 1 : ℕ) : ℝ))).add
      ((summable_vonMangoldtSuccessorRelativeMomentTerm (2 * i + 3)).mul_left
        (1 / ((2 * i + 3 : ℕ) : ℝ)))

/-- Majorant edge masses are nonnegative on the genuine source range. -/
theorem vonMangoldtSuccessorDiracMajorantEdgeTerm_nonneg
    (i n : ℕ) (hn : 2 ≤ n) :
    0 ≤ vonMangoldtSuccessorDiracMajorantEdgeTerm i n := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hns0 : (0 : ℝ) < n + 1 := by positivity
  have hlog : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hn0 hns0 (by norm_num)
  apply mul_nonneg (finiteVonMangoldtRealWeight_nonneg n)
  apply intervalIntegral.integral_nonneg hlog
  intro t ht
  unfold HTGeometry.transportDiracMajorant
  rw [show 2 * i = i + i by omega, pow_add,
    show i + i + 2 = (i + 1) + (i + 1) by omega, pow_add]
  exact add_nonneg
    (mul_nonneg (sq_nonneg _) (mul_self_nonneg _))
    (mul_self_nonneg _)

end

end RHTower
