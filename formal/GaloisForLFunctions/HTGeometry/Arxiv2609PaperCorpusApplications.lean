import GaloisForLFunctions.HTGeometry.Arxiv2609KineticVariance
import GaloisForLFunctions.HTGeometry.Arxiv2609ThurstonIdentifiability
import GaloisForLFunctions.HTGeometry.CompleteComparisonReciprocity
import GaloisForLFunctions.HTGeometry.NoncommutativeQubitResponsePolarization
import GaloisForLFunctions.HTGeometry.SignedPermutationIsometry

/-!
# Corpus applications of the September 2026 papers

Theorem-level intersections between arXiv:2609.10085, arXiv:2609.09236, and existing corpus
machinery: finite Hankel rank, centered moment mechanics, complete-comparison dimension counts,
triangle cohomology, and Bernoulli relative entropy.
-/

open Polynomial
open scoped Matrix

namespace HTGeometry

noncomputable section

/-! ## Kinetic moments meet finite Hankel rank and centered mechanics -/

/-- Uniform kinetic energy on `n+1` velocities has Hankel rank at most `n+1`. -/
theorem uniformKineticMoment_hankel_det_zero {n : ℕ} (u : Fin (n + 1) → ℝ) :
    (momentHankelMatrix (uniformKineticMomentSequence u) (n + 2)).det = 0 := by
  simpa [uniformKineticMomentSequence] using
    det_momentHankelMatrix_finiteSpectralMoment_succ_eq_zero
      (uniformKineticMass n) (kineticEnergy u)

/-- Every normalized finite Schrödinger energy law has its spectral-width Hankel obstruction. -/
theorem finiteSchrodingerEnergyMoment_hankel_det_zero {d : ℕ}
    (state : FiniteSchrodingerState d) (energy : Fin d → ℝ) :
    (momentHankelMatrix (finiteSchrodingerEnergyMoment state energy) (d + 1)).det = 0 := by
  simpa [finiteSchrodingerEnergyMoment] using
    det_momentHankelMatrix_finiteSpectralMoment_succ_eq_zero
      (fun i ↦ Complex.normSq (state.amplitude i)) energy

/-- Canonically centered kinetic energy has the paper's exact fourth-moment variance. -/
theorem uniformKinetic_centeredSecondMoment_formula {n : ℕ} (u : Fin (n + 1) → ℝ) :
    momentNormalizedExpectation (uniformKineticMomentSequence u)
        ((momentVacuumCenteredPolynomial (uniformKineticMomentSequence u) X) ^ 2) =
      (uniformVelocityPowerMean u 4 - uniformVelocityPowerMean u 2 ^ 2) / 4 := by
  change momentNormalizedExpectation (uniformKineticMomentState u).sequence
      ((momentVacuumCenteredPolynomial (uniformKineticMomentState u).sequence X) ^ 2) = _
  rw [momentMechanics_centeredSecondMoment_eq_variance (uniformKineticMomentState u)]
  change momentNormalizedVariance (uniformKineticMomentSequence u) X = _
  exact uniformKineticVariance_formula u

/-- Cauchy--Schwarz makes the kinetic fourth-moment fluctuation numerator nonnegative. -/
theorem uniformVelocityPowerMean_two_sq_le_four {n : ℕ} (u : Fin (n + 1) → ℝ) :
    uniformVelocityPowerMean u 2 ^ 2 ≤ uniformVelocityPowerMean u 4 := by
  unfold uniformVelocityPowerMean
  calc
    ((∑ i, u i ^ 2) / (n + 1 : ℕ)) ^ 2 ≤
        (∑ i, (u i ^ 2) ^ 2) / (n + 1 : ℕ) := by
      simpa [Fintype.card_fin] using
        (sum_div_card_sq_le_sum_sq_div_card
          (s := Finset.univ) (f := fun i : Fin (n + 1) ↦ u i ^ 2))
    _ = (∑ i, u i ^ 4) / (n + 1 : ℕ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

end

end HTGeometry

namespace GaloisForLFunctions.HTGeometry

open SimpleGraph
open scoped Matrix

noncomputable section

/-! ## Thurston gauges meet comparison ranks and information geometry -/

/-- Real dimension of `N` Sol latent points after quotienting the four-dimensional gauge. -/
def solLatentQuotientDimension (n : ℕ) : ℝ := 3 * n - 4

/-- Paper's exact dimension-deficit range, now stated with the corpus pair-channel count. -/
theorem completeComparisonChannels_lt_solLatentQuotientDimension_iff (n : ℕ) :
    (completeComparisonChannels n : ℝ) < solLatentQuotientDimension n ↔
      2 ≤ n ∧ n ≤ 5 := by
  constructor
  · intro h
    have hn2 : 2 ≤ n := by
      by_contra hn
      have hn : n = 0 ∨ n = 1 := by omega
      rcases hn with rfl | rfl <;>
        norm_num [completeComparisonChannels, solLatentQuotientDimension, Nat.choose] at h
    have hn6 : n < 6 := by
      by_contra hn
      have hn6 : 6 ≤ n := by omega
      rw [completeComparisonChannels, Nat.cast_choose_two] at h
      change (n : ℝ) * ((n : ℝ) - 1) / 2 < 3 * (n : ℝ) - 4 at h
      have h6cast : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
      have h6 : 0 ≤ (n : ℝ) - 6 := by linarith
      have h1 : 0 ≤ (n : ℝ) - 1 := by linarith
      nlinarith [mul_nonneg h6 h1]
    omega
  · rintro ⟨hn2, hn5⟩
    interval_cases n <;>
      norm_num [completeComparisonChannels, solLatentQuotientDimension, Nat.choose]

/-- Nil area is the scalar obstruction carried by the corpus's one-dimensional triangle `H¹`. -/
theorem nilHolonomy_triangleCohomology_bridge (p q r : ThurstonPoint) :
    ((∃ r₀ r₁ r₂ : ℝ,
        nilVerticalOffset p q = r₁ - r₀ ∧
        nilVerticalOffset q r = r₂ - r₁ ∧
        nilVerticalOffset r p = r₀ - r₂) ↔
        nilTriangleArea p q r = 0) ∧
      Module.finrank ℝ
        ((orientedEdges (cycleGraph 3) → ℝ) ⧸
          LinearMap.range (orientedCoboundary (cycleGraph 3) ℝ)) = 1 := by
  exact ⟨nilVerticalOffset_is_coboundary_iff p q r,
    finrank_reducedH1_cycleGraph3 ℝ⟩

/-- Any twisted latent Bernoulli law has zero relative entropy from itself. -/
theorem bernoulliRelativeEntropy_twisted_self_zero
    (alpha beta tau distance : ℝ) :
    bernoulliRelativeEntropy (twistedEdgeProbability alpha beta tau distance)
      (twistedEdgeProbability alpha beta tau distance) = 0 := by
  have hp := twistedEdgeProbability_mem_unitInterval alpha beta tau distance
  have hp0 : twistedEdgeProbability alpha beta tau distance ≠ 0 := hp.1.ne'
  have h1p0 : 1 - twistedEdgeProbability alpha beta tau distance ≠ 0 := by
    linarith
  simp [bernoulliRelativeEntropy, hp0, h1p0]

/-- Twist/temperature rescaling produces exactly zero Bernoulli KL divergence. -/
theorem bernoulliRelativeEntropy_twistScale_eq_zero
    (alpha beta tau distance : ℝ) (scale : ℝˣ) :
    bernoulliRelativeEntropy
        (twistedEdgeProbability alpha ((scale : ℝ) * beta) ((scale : ℝ) * tau) distance)
        (twistedEdgeProbability alpha beta tau distance) = 0 := by
  rw [twistedEdgeProbability_unitScale_invariant]
  exact bernoulliRelativeEntropy_twisted_self_zero alpha beta tau distance

/-! ## Sol `D₄` stabilizer as the corpus signed-permutation isometry -/

/-- Eight-element Sol stabilizer data: optional `x/y` swap and two independent signs. -/
structure SolD4Element where
  swap : Bool
  signX : ℝ
  signY : ℝ
  signX_mem : signX = 1 ∨ signX = -1
  signY_mem : signY = 1 ∨ signY = -1

/-- Coordinate action of the Sol `D₄` stabilizer. A swap reverses the `z` coordinate. -/
def solD4Act (g : SolD4Element) (p : ThurstonPoint) : ThurstonPoint :=
  if g.swap then ⟨g.signX * p.y, g.signY * p.x, -p.z⟩
  else ⟨g.signX * p.x, g.signY * p.y, p.z⟩

private def solD4Perm (swap : Bool) : Equiv.Perm (Fin 3) :=
  if swap then Equiv.swap 0 1 else Equiv.refl _

private def solD4Sign (g : SolD4Element) (i : Fin 3) : ℝ :=
  if i = 0 then g.signX else if i = 1 then g.signY else if g.swap then -1 else 1

private theorem solD4Sign_mem (g : SolD4Element) (i : Fin 3) :
    solD4Sign g i = 1 ∨ solD4Sign g i = -1 := by
  fin_cases i
  · simpa [solD4Sign] using g.signX_mem
  · simpa [solD4Sign] using g.signY_mem
  · cases h : g.swap <;> simp [solD4Sign, h]

/-- Every Sol `D₄` action is literally an existing corpus signed-permutation isometry. -/
def solD4Isometry (g : SolD4Element) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  signedPermIsometry (solD4Perm g.swap) (solD4Sign_mem g)

/-- Coercion of Thurston coordinates into corpus Euclidean space. -/
def thurstonPointEuclidean (p : ThurstonPoint) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.x, p.y, p.z]

theorem solD4Isometry_apply (g : SolD4Element) (p : ThurstonPoint) :
    solD4Isometry g (thurstonPointEuclidean p) = thurstonPointEuclidean (solD4Act g p) := by
  have hswap2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  ext i
  fin_cases i <;> cases h : g.swap <;>
    simp [solD4Isometry, thurstonPointEuclidean, solD4Act, solD4Perm, solD4Sign, h,
      coe_signedPermIsometry, hswap2]

/-- Sign selecting the nonnegative representative of one real coordinate. -/
def solChamberSign (x : ℝ) : ℝ := if x < 0 then -1 else 1

theorem solChamberSign_mem (x : ℝ) : solChamberSign x = 1 ∨ solChamberSign x = -1 := by
  by_cases h : x < 0
  · exact Or.inr (by simp [solChamberSign, h])
  · exact Or.inl (by simp [solChamberSign, h])

theorem solChamberSign_mul (x : ℝ) : solChamberSign x * x = |x| := by
  by_cases h : x < 0
  · rw [solChamberSign, if_pos h, abs_of_neg h]
    ring
  · rw [solChamberSign, if_neg h, abs_of_nonneg (not_lt.mp h)]
    ring

/-- Canonical `D₄` element carrying a Sol anchor to the positive chamber. -/
def solCanonicalD4Element (p : ThurstonPoint) : SolD4Element where
  swap := decide (p.z < 0)
  signX := if p.z < 0 then solChamberSign p.y else solChamberSign p.x
  signY := if p.z < 0 then solChamberSign p.x else solChamberSign p.y
  signX_mem := by split <;> apply solChamberSign_mem
  signY_mem := by split <;> apply solChamberSign_mem

theorem solCanonicalD4Element_act (p : ThurstonPoint) :
    solD4Act (solCanonicalD4Element p) p = solCanonicalAnchor p := by
  by_cases h : p.z < 0
  · ext <;> simp [solD4Act, solCanonicalD4Element, solCanonicalAnchor, h,
      solChamberSign_mul, abs_of_neg h]
  · ext <;> simp [solD4Act, solCanonicalD4Element, solCanonicalAnchor, h,
      solChamberSign_mul, abs_of_nonneg (not_lt.mp h)]

/-- Positive-chamber normalization is certified by an actual signed-permutation isometry. -/
theorem solCanonicalAnchor_signedPermutation (p : ThurstonPoint) :
    solD4Isometry (solCanonicalD4Element p) (thurstonPointEuclidean p) =
      thurstonPointEuclidean (solCanonicalAnchor p) := by
  rw [solD4Isometry_apply, solCanonicalD4Element_act]

end

end GaloisForLFunctions.HTGeometry
