import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBReducedTeukolskyHermitianDilationFidelityNoGo

/-!
# Arbitrary Hilbert--Schmidt Hermitian completion fidelity no-go

The canonical chiral dilation is not the only conservative completion of the reduced doubled-grade
Einstein--Teukolsky source.  One could add arbitrary diagonal blocks, infinitely many auxiliary
sectors, or nonlocal Hilbert--Schmidt counterterms while retaining one exact off-diagonal source
entry.  This module closes that entire loophole.

For an arbitrary self-adjoint Hilbert--Schmidt kernel `L`, its holomorphic square trace is the
positive energy `||L||_HS^(2 : ℕ)`.  If distinct entries `(i,j)` and `(j,i)` carry a faithful source
coefficient `c` and its adjoint, this energy is at least `2|c|^(2 : ℕ)`.  By contrast the rank-one
holomorphic source kernel `c e_00` has square trace `c^(2 : ℕ)`, whose modulus is only `|c|^(2 : ℕ)`.  Equality
of their entire Hilbert--Carleman determinants would equate the quadratic Taylor jets and hence
force `2|c|^(2 : ℕ) <= |c|^(2 : ℕ)`.

The exact reduced Teukolsky coefficient is nonzero precisely on tilted Xi fibres.  Therefore no
self-adjoint Hilbert--Schmidt completion, of any carrier size and with arbitrary extra
counterterms, can be simultaneously source-faithful and determinant-faithful there.  This kills
the arbitrary conservative-completion producer for the shared HB/FZZ-P/PW-B/RBH Ward endpoint.

The sharp positive survivor is representation-theoretic: any remaining construction must abandon
at least one of self-adjointness, Hilbert--Schmidt/Fredholm regularity, coefficient fidelity, or
determinant fidelity.

`[NEW] [HB ROUTE KILL] [ARBITRARY COMPLETION] [HILBERT-SCHMIDT] [QUADRATIC JET]
[TEUKOLSKY] [FOUR-ROUTE WARD] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry HilbertSchmidt

noncomputable section

/-- A self-adjoint Hilbert--Schmidt kernel has holomorphic square trace equal to its total
Hilbert--Schmidt energy. -/
theorem hsTraceSquare_eq_hsNormSq_of_selfAdjoint
    {κ : Type*} [DecidableEq κ]
    (L : κ × κ → ℂ) (hL : IsHS L) (hself : hsAdjoint L = L) :
    (∑' q, hsPow L 1 (q, q)) = (hsNormSq L : ℂ) := by
  calc
    (∑' q, hsPow L 1 (q, q)) = hsInner (hsAdjoint L) (hsPow L 0) := by
      simpa using hsTrace_hsPow_succ hL 0
    _ = hsInner L L := by rw [hself]; rfl
    _ = (hsNormSq L : ℂ) := hsInner_self L

/-- One faithful off-diagonal entry of a self-adjoint Hilbert--Schmidt kernel costs two copies of
its squared norm, independently of every other entry. -/
theorem two_mul_normSq_entry_le_hsNormSq_of_selfAdjoint
    {κ : Type*} [DecidableEq κ]
    (L : κ × κ → ℂ) (hL : IsHS L) (hself : hsAdjoint L = L)
    (i j : κ) (hij : i ≠ j) :
    2 * ‖L (i, j)‖ ^ (2 : ℕ) ≤ hsNormSq L := by
  have hreverse : L (j, i) = (starRingEnd ℂ) (L (i, j)) := by
    have h := congrFun hself (j, i)
    simpa [hsAdjoint] using h.symm
  have hpairs : (i, j) ≠ (j, i) := by
    intro h
    exact hij (congrArg Prod.fst h)
  have hsum := hL.sum_le_tsum ({(i, j), (j, i)} : Finset (κ × κ))
    (fun _ _ => by positivity)
  rw [hsNormSq]
  simpa [hpairs, hreverse, two_mul] using hsum

/-- Arbitrary-completion rigidity: a self-adjoint Hilbert--Schmidt kernel containing a faithful
nonzero off-diagonal source entry cannot preserve the rank-one holomorphic source determinant.
No locality, finite-rank, diagonal-block, or support hypothesis is used. -/
theorem selfAdjoint_sourceBlock_entireDet2_ne_diagKernel
    {κ : Type*} [DecidableEq κ]
    (L : κ × κ → ℂ) (hL : IsHS L) (hself : hsAdjoint L = L)
    (i j : κ) (hij : i ≠ j) (c : ℂ)
    (hentry : L (i, j) = c) (hc : c ≠ 0) :
    entireDet2 L ≠ entireDet2 (diagKernel 0 c) := by
  intro heq
  have hK : IsHS (diagKernel (0 : ℕ) c) := isHS_diagKernel 0 c
  have hcoeff := congrArg (fun f : ℂ → ℂ => taylorCoeff f 2) heq
  rw [taylorCoeff_entireDet2_two hL,
    taylorCoeff_entireDet2_two hK] at hcoeff
  have htraceL := hsTraceSquare_eq_hsNormSq_of_selfAdjoint L hL hself
  have htraceK :
      (∑' q : ℕ, hsPow (diagKernel 0 c) 1 (q, q)) = c ^ (2 : ℕ) := by
    rw [hsPow_diagKernel, tsum_diagKernel_diag]
  rw [htraceL, htraceK] at hcoeff
  have heqTrace : (hsNormSq L : ℂ) = c ^ (2 : ℕ) := by
    linear_combination -2 * hcoeff
  have hnorm := congrArg norm heqTrace
  have hnonneg := hsNormSq_nonneg L
  have hnormEq : hsNormSq L = ‖c‖ ^ (2 : ℕ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, norm_pow] using hnorm
  have hfloor := two_mul_normSq_entry_le_hsNormSq_of_selfAdjoint
    L hL hself i j hij
  rw [hentry, hnormEq] at hfloor
  have hczero : ‖c‖ ^ (2 : ℕ) = 0 := by nlinarith [sq_nonneg ‖c‖]
  exact hc (norm_eq_zero.mp (sq_eq_zero_iff.mp hczero))

/-- The coefficient used below is literally the actual mixed-horizon HB optical source projection,
not a target-fitted scalar. -/
theorem d4HBReducedTeukolskyHermitianDilationSourceCoefficient_eq_opticalSource
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q =
      d4BMMixedHorizonOpticalSourceProjection amplitude 0 q := by
  rw [d4HBReducedTeukolskyHermitianDilationSourceCoefficient]
  exact d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_eq_opticalSource
    amplitude mixed anti 0 q

/-- On a tilted Xi fibre, every arbitrary self-adjoint Hilbert--Schmidt completion faithfully
carrying the exact reduced Teukolsky source has the two-copy energy floor and necessarily loses
determinant fidelity. -/
theorem d4HBReducedTeukolskyArbitraryHermitianCompletion_tilted
    {κ : Type*} [DecidableEq κ]
    (L : κ × κ → ℂ) (hL : IsHS L) (hself : hsAdjoint L = L)
    (i j : κ) (hij : i ≠ j)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (hentry : L (i, j) =
      d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q) :
    2 * ‖d4HBReducedTeukolskyHermitianDilationSourceCoefficient
          amplitude mixed anti q‖ ^ (2 : ℕ) ≤ hsNormSq L ∧
      entireDet2 L ≠ entireDet2 (diagKernel (0 : ℕ)
        (d4HBReducedTeukolskyHermitianDilationSourceCoefficient
          amplitude mixed anti q)) := by
  let c := d4HBReducedTeukolskyHermitianDilationSourceCoefficient
    amplitude mixed anti q
  have hc : c ≠ 0 := by
    exact (d4ThetaReducedSecondOrderChiralTeukolskyGradeSource_sameGrade_ne_zero_iff
      ha mixed anti 0 q).2 htilt
  constructor
  · have hfloor := two_mul_normSq_entry_le_hsNormSq_of_selfAdjoint
      L hL hself i j hij
    simpa [c, hentry] using hfloor
  · exact selfAdjoint_sourceBlock_entireDet2_ne_diagKernel
      L hL hself i j hij c hentry hc

/-- Closed route class: arbitrary finite- or infinite-dimensional Hilbert--Schmidt counterterms
cannot make a self-adjoint angular completion both source-faithful and determinant-faithful on a
tilted Xi fibre. -/
def D4HBReducedTeukolskyArbitraryHermitianCompletionFidelityRouteKilled : Prop :=
  ∀ (κ : Type*) [DecidableEq κ]
    (L : κ × κ → ℂ), IsHS L → hsAdjoint L = L →
    ∀ i j : κ, i ≠ j →
    ∀ amplitude : ℂ, amplitude ≠ 0 → ∀ mixed anti : ℂ,
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      L (i, j) =
        d4HBReducedTeukolskyHermitianDilationSourceCoefficient amplitude mixed anti q →
      2 * ‖d4HBReducedTeukolskyHermitianDilationSourceCoefficient
            amplitude mixed anti q‖ ^ (2 : ℕ) ≤ hsNormSq L ∧
        entireDet2 L ≠ entireDet2 (diagKernel (0 : ℕ)
          (d4HBReducedTeukolskyHermitianDilationSourceCoefficient
            amplitude mixed anti q))

/-- Premise-free certificate killing arbitrary self-adjoint Hilbert--Schmidt completion as the
missing angular-leakage producer for the shared HB/FZZ-P/PW-B/RBH endpoint. -/
theorem d4HBReducedTeukolskyArbitraryHermitianCompletionFidelityRouteKilled :
    D4HBReducedTeukolskyArbitraryHermitianCompletionFidelityRouteKilled := by
  intro κ _ L hL hself i j hij amplitude ha mixed anti q htilt hentry
  exact d4HBReducedTeukolskyArbitraryHermitianCompletion_tilted
    L hL hself i j hij ha mixed anti q htilt hentry

end

end RHTower
