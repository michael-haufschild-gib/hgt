import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain

/-!
# A cut is a bottleneck iff its part binds more than its share

Let `φ > 0` be the ground vector of a symmetric matrix `N` with negative entries off the diagonal,
`N φ = λ φ`, `μ = −λ`, and let `π(S) = Σ_{i ∈ S} φ_i²` be the stationary weight of a set `S` of
blocks. Write `φ_S` for the ground vector restricted to `S`. The eigenvalue equation, summed over
`S` against `φ`, is an exact law for the conductance of the cut of `S` (`doobCut_eq`):

  `C(S) = μ π(S) + N(φ_S, φ_S)`.

The conductance is the binding energy that the part `S` receives from the whole window minus
the binding it holds itself. So the bottleneck test `C(S) π(W) < μ π(S) π(Sᶜ)` is exactly
(`doobCut_bottleneck_iff`)

  `−N(φ_S, φ_S) / π(S) > μ · π(S)/π(W)`:

**a cut is a bottleneck iff the part binds its piece of the ground state more strongly than its
share** `μ π(S)/π(W)` of the binding energy. With one bound state no part does
(`share_law_of_hermNegIndex_le_one`); under RH this holds for every set of blocks of every window
(`share_law_of_riemannHypothesis`). For the whole window the share law is an equality, and for a
part of small weight it says that the restricted ground state hardly binds at all.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ground vector restricted to a set of blocks. -/
def restrictTo (φ : ι → ℝ) (S : Finset ι) (i : ι) : ℝ := if i ∈ S then φ i else 0

/-- **The conductance of a cut is the binding the part receives minus the binding it holds**:
`C(S) = N(φ_S, φ_S) − λ π(S)`. -/
theorem doobCut_eq {G : Matrix ι ι ℝ} {φ : ι → ℝ} {lam : ℝ} (heig : G *ᵥ φ = lam • φ)
    (S : Finset ι) :
    doobCut G φ S = bilin G (restrictTo φ S) (restrictTo φ S) - lam * doobWeight φ S := by
  have h1 := bilin_eigen heig (restrictTo φ S)
  have hw : ∑ k, restrictTo φ S k * φ k = doobWeight φ S := by
    unfold doobWeight
    simp only [restrictTo, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hφ : ∀ j, φ j = restrictTo φ S j + restrictTo φ Sᶜ j := fun j => by
    unfold restrictTo
    by_cases hj : j ∈ S
    · rw [if_pos hj, if_neg (fun h => (Finset.mem_compl.mp h) hj), add_zero]
    · rw [if_neg hj, if_pos (Finset.mem_compl.mpr hj), zero_add]
  have hterm : ∀ i j, restrictTo φ S i * restrictTo φ Sᶜ j * G i j =
      if i ∈ S ∧ j ∈ Sᶜ then -doobConductance G φ i j else 0 := fun i j => by
    unfold restrictTo doobConductance
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      (simp [hi, hj, Finset.mem_compl]; ring)
  have hcross : ∑ i, ∑ j, restrictTo φ S i * restrictTo φ Sᶜ j * G i j = -doobCut G φ S := by
    simp only [hterm, sum_sum_ite_and]
    unfold doobCut
    simp only [Finset.sum_neg_distrib]
  have hsplit : bilin G (restrictTo φ S) φ = bilin G (restrictTo φ S) (restrictTo φ S) +
      ∑ i, ∑ j, restrictTo φ S i * restrictTo φ Sᶜ j * G i j := by
    unfold bilin
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hφ j]
    ring
  rw [hsplit, hcross, hw] at h1
  linarith

/-- **A cut is a bottleneck iff its part binds more than its share**:
`C(S) π(W) < μ π(S) π(Sᶜ)` iff `N(φ_S, φ_S) π(W) < λ π(S)²`. -/
theorem doobCut_bottleneck_iff {G : Matrix ι ι ℝ} {φ : ι → ℝ} {lam : ℝ}
    (heig : G *ᵥ φ = lam • φ) (S : Finset ι) :
    doobCut G φ S * doobWeight φ Finset.univ < -lam * doobWeight φ S * doobWeight φ Sᶜ ↔
      bilin G (restrictTo φ S) (restrictTo φ S) * doobWeight φ Finset.univ <
        lam * doobWeight φ S ^ 2 := by
  have hW : doobWeight φ Finset.univ = doobWeight φ S + doobWeight φ Sᶜ :=
    (Finset.sum_add_sum_compl S _).symm
  rw [doobCut_eq heig S, hW]
  constructor <;> intro h <;> nlinarith [h]

/-- **The share law.** With one bound state every set of blocks holds at most its share of the
binding: `λ π(S)² ≤ N(φ_S, φ_S) π(W)`. -/
theorem share_law_of_hermNegIndex_le_one {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i)
    (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {φ : ι → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : G *ᵥ φ = lam • φ) (h1 : hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ≤ 1)
    (S : Finset ι) :
    lam * doobWeight φ S ^ 2 ≤ bilin G (restrictTo φ S) (restrictTo φ S) *
      doobWeight φ Finset.univ := by
  by_contra hlt
  push Not at hlt
  have h2 := two_le_hermNegIndex_of_bottleneck hG hoff hφ heig S
    ((doobCut_bottleneck_iff heig S).mpr hlt)
  omega

/-- **Under RH no set of blocks of any window binds more than its share**: for the ground vector
`φ` of a window with `R ≤ J`, `R + J ≤ QR`, and every set `S` of its blocks,
`λ π(S)² ≤ N(φ_S, φ_S) π(W)`. -/
theorem share_law_of_riemannHypothesis (hRH : RiemannHypothesis) {Q R J : ℕ} (hR : 1 ≤ R)
    (hRJ : R ≤ J) (hQ : R + J ≤ Q * R) {φ : Fin J → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q R J *ᵥ φ = lam • φ) (S : Finset (Fin J)) :
    lam * doobWeight φ S ^ 2 ≤ bilin (neutralWindow Q R J) (restrictTo φ S) (restrictTo φ S) *
      doobWeight φ Finset.univ :=
  share_law_of_hermNegIndex_le_one (neutralWindow_symm Q R J)
    (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) hφ heig
    (riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one.mp hRH Q R J hR hRJ hQ).le S

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
