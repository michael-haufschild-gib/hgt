import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite matrix-valued spectral moments and block Hankel geometry

Several coupled fields or reporters observing the same finite spectrum produce matrix-valued
moments

`M_k(a,b) = sum_r mass_r coupling_r(a) coupling_r(b) node_r^k`.

The block Hankel matrix indexed by `(clock order, channel)` is exactly the Gram matrix of the
mass-weighted multi-channel spectral features.  Positive masses therefore give block positivity,
while nonsingularity is exactly joint feature independence.  The ambient spectral-line count
still caps total block rank: a block with more clock-channel coordinates than spectral lines is
singular.

Every scalar reporter of the channel matrix contracts the couplings first and produces an
ordinary finite spectral moment sequence.  Thus the existing scalar Hankel-rank obstruction is
discharged automatically for every channel combination.

Physics provenance: multi-field EFT positivity is naturally a matrix moment problem; see
Wan--Zhou, arXiv:2411.11964, and Li--Xu--Yang--Zhang--Zhou, arXiv:2101.01191.  Matrix-valued
Euclidean correlator moments are used in lattice spectroscopy; see Abbott--Jay--Oare,
arXiv:2508.01377.  The results below isolate the exact finite spectral algebra common to those
settings without assuming a field equation or temporal flow.
-/

open scoped BigOperators InnerProductSpace

namespace HTGeometry

noncomputable section

/-- Matrix-valued moment of a finite common spectrum with real channel couplings. -/
def finiteMatrixSpectralMoment {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (k : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun a b => ∑ r, mass r * coupling r a * coupling r b * node r ^ k

/-- Block Hankel matrix with one index for clock order and one for reporter/field channel. -/
def finiteMatrixSpectralBlockHankel {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (n : ℕ) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ :=
  fun ia jb => finiteMatrixSpectralMoment mass node coupling
    ((ia.1 : ℕ) + (jb.1 : ℕ)) ia.2 jb.2

/-- Mass-weighted joint clock-channel feature carried by one block-Hankel coordinate. -/
def finiteMatrixSpectralFeature {d m n : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (ia : Fin n × Fin m) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun r =>
    Real.sqrt (mass r) * coupling r ia.2 * node r ^ (ia.1 : ℕ)

/-- **Block spectral Gram identity.**  Positive spectral masses make the complete coupled-channel
block Hankel matrix a literal finite-dimensional Gram matrix. -/
theorem finiteMatrixSpectralBlockHankel_eq_gram {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (hmass : ∀ r, 0 ≤ mass r) (n : ℕ) :
    finiteMatrixSpectralBlockHankel mass node coupling n =
      Matrix.gram ℝ (finiteMatrixSpectralFeature mass node coupling) := by
  ext ia jb
  rw [Matrix.gram_apply, PiLp.inner_apply]
  simp only [finiteMatrixSpectralBlockHankel, finiteMatrixSpectralMoment,
    finiteMatrixSpectralFeature, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro r hr
  rw [pow_add]
  calc
    mass r * coupling r ia.2 * coupling r jb.2 *
          (node r ^ (ia.1 : ℕ) * node r ^ (jb.1 : ℕ)) =
        (Real.sqrt (mass r) * Real.sqrt (mass r)) *
          coupling r ia.2 * coupling r jb.2 *
          (node r ^ (ia.1 : ℕ) * node r ^ (jb.1 : ℕ)) := by
      rw [Real.mul_self_sqrt (hmass r)]
    _ = Real.sqrt (mass r) * coupling r jb.2 * node r ^ (jb.1 : ℕ) *
        (Real.sqrt (mass r) * coupling r ia.2 * node r ^ (ia.1 : ℕ)) := by
      ring

/-- Positive finite matrix-valued spectral data make every block Hankel matrix positive
semidefinite. -/
theorem finiteMatrixSpectralBlockHankel_posSemidef {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (hmass : ∀ r, 0 ≤ mass r) (n : ℕ) :
    (finiteMatrixSpectralBlockHankel mass node coupling n).PosSemidef := by
  rw [finiteMatrixSpectralBlockHankel_eq_gram mass node coupling hmass n]
  exact Matrix.posSemidef_gram ℝ _

/-- Joint clock-channel identifiability is exactly linear independence of the mass-weighted
spectral feature family. -/
theorem finiteMatrixSpectralBlockHankel_posDef_iff_linearIndependent {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (hmass : ∀ r, 0 ≤ mass r) (n : ℕ) :
    (finiteMatrixSpectralBlockHankel mass node coupling n).PosDef ↔
      LinearIndependent ℝ (finiteMatrixSpectralFeature mass node coupling :
        Fin n × Fin m → EuclideanSpace ℝ (Fin d)) := by
  rw [finiteMatrixSpectralBlockHankel_eq_gram mass node coupling hmass n,
    Matrix.posDef_gram_iff_linearIndependent]

/-- The maximal block determinant is nonzero exactly when all joint features are identifiable. -/
theorem det_finiteMatrixSpectralBlockHankel_ne_zero_iff_linearIndependent {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (hmass : ∀ r, 0 ≤ mass r) (n : ℕ) :
    (finiteMatrixSpectralBlockHankel mass node coupling n).det ≠ 0 ↔
      LinearIndependent ℝ (finiteMatrixSpectralFeature mass node coupling :
        Fin n × Fin m → EuclideanSpace ℝ (Fin d)) := by
  rw [finiteMatrixSpectralBlockHankel_eq_gram mass node coupling hmass n,
    Matrix.det_gram_ne_zero_iff_linearIndependent]

/-- Independent joint features make the block determinant strictly positive. -/
theorem det_finiteMatrixSpectralBlockHankel_pos_of_linearIndependent {d m n : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (hmass : ∀ r, 0 ≤ mass r)
    (hli : LinearIndependent ℝ (finiteMatrixSpectralFeature mass node coupling :
      Fin n × Fin m → EuclideanSpace ℝ (Fin d))) :
    0 < (finiteMatrixSpectralBlockHankel mass node coupling n).det := by
  rw [finiteMatrixSpectralBlockHankel_eq_gram mass node coupling hmass n]
  exact (Matrix.posDef_gram_of_linearIndependent hli).det_pos

/-- **Multi-field spectral capacity law.**  More clock-channel coordinates than common spectral
lines force singularity, regardless of the couplings. -/
theorem det_finiteMatrixSpectralBlockHankel_eq_zero_of_spectralLines_lt {d m n : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (hmass : ∀ r, 0 ≤ mass r) (hcapacity : d < n * m) :
    (finiteMatrixSpectralBlockHankel mass node coupling n).det = 0 := by
  by_contra hdet
  have hli : LinearIndependent ℝ
      (finiteMatrixSpectralFeature mass node coupling :
        Fin n × Fin m → EuclideanSpace ℝ (Fin d)) :=
    (det_finiteMatrixSpectralBlockHankel_ne_zero_iff_linearIndependent
      mass node coupling hmass n).mp hdet
  have hbound := hli.fintype_card_le_finrank
  simp only [Fintype.card_prod, Fintype.card_fin,
    finrank_euclideanSpace_fin] at hbound
  omega

/-- Coupling of one spectral line to a chosen scalar reporter. -/
def finiteMatrixSpectralEffectiveCoupling {d m : ℕ}
    (coupling : Fin d → Fin m → ℝ) (reporter : Fin m → ℝ)
    (r : Fin d) : ℝ :=
  ∑ a, reporter a * coupling r a

/-- Scalar moment observed by contracting both channel indices with one reporter. -/
def finiteMatrixSpectralScalarizedMoment {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (reporter : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ a, ∑ b, reporter a *
    finiteMatrixSpectralMoment mass node coupling k a b * reporter b

/-- **Scalarization law.**  Contracting a matrix-valued spectrum first contracts each mode's
coupling and squares it; no new spectral nodes are created. -/
theorem finiteMatrixSpectralScalarizedMoment_eq_finiteSpectralMoment {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (reporter : Fin m → ℝ) (k : ℕ) :
    finiteMatrixSpectralScalarizedMoment mass node coupling reporter k =
      finiteSpectralMoment
        (fun r => mass r *
          finiteMatrixSpectralEffectiveCoupling coupling reporter r ^ (2 : ℕ))
        node k := by
  unfold finiteMatrixSpectralScalarizedMoment finiteMatrixSpectralMoment
    finiteMatrixSpectralEffectiveCoupling finiteSpectralMoment
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  let F : Fin m → Fin m → Fin d → ℝ := fun a b r =>
    reporter a * (mass r * coupling r a * coupling r b * node r ^ k) * reporter b
  change (∑ a, ∑ b, ∑ r, F a b r) =
    ∑ r, mass r * (∑ a, reporter a * coupling r a) ^ (2 : ℕ) * node r ^ k
  calc
    (∑ a, ∑ b, ∑ r, F a b r) = ∑ a, ∑ r, ∑ b, F a b r := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ a, ∑ b, F a b r := by rw [Finset.sum_comm]
    _ = ∑ r, mass r * (∑ a, reporter a * coupling r a) ^ (2 : ℕ) * node r ^ k := by
      apply Finset.sum_congr rfl
      intro r hr
      dsimp only [F]
      calc
        (∑ a, ∑ b,
            reporter a * (mass r * coupling r a * coupling r b * node r ^ k) *
              reporter b) =
            mass r * node r ^ k *
              ∑ a, ∑ b,
                (reporter a * coupling r a) * (reporter b * coupling r b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = mass r * node r ^ k *
            ((∑ a, reporter a * coupling r a) *
              ∑ b, reporter b * coupling r b) := by
          rw [Fintype.sum_mul_sum]
        _ = mass r * (∑ a, reporter a * coupling r a) ^ (2 : ℕ) * node r ^ k := by
          ring

/-- Every scalar channel contraction has spectral width at most the common line count. -/
theorem finiteMatrixSpectralScalarizedMoment_spectralWidthAtMost {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (reporter : Fin m → ℝ) :
    SpectralWidthAtMost d
      (finiteMatrixSpectralScalarizedMoment mass node coupling reporter) := by
  refine ⟨fun r => mass r *
      finiteMatrixSpectralEffectiveCoupling coupling reporter r ^ (2 : ℕ), node, ?_⟩
  funext k
  exact finiteMatrixSpectralScalarizedMoment_eq_finiteSpectralMoment
    mass node coupling reporter k

/-- The existing scalar Hankel obstruction applies uniformly to every contraction of a
matrix-valued `d`-line spectrum. -/
theorem det_momentHankelMatrix_finiteMatrixSpectralScalarizedMoment_succ_eq_zero
    {d m : ℕ}
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ)
    (reporter : Fin m → ℝ) :
    (momentHankelMatrix
      (finiteMatrixSpectralScalarizedMoment mass node coupling reporter) (d + 1)).det = 0 := by
  rw [show finiteMatrixSpectralScalarizedMoment mass node coupling reporter =
      finiteSpectralMoment
        (fun r => mass r *
          finiteMatrixSpectralEffectiveCoupling coupling reporter r ^ (2 : ℕ)) node by
    funext k
    exact finiteMatrixSpectralScalarizedMoment_eq_finiteSpectralMoment
      mass node coupling reporter k]
  exact det_momentHankelMatrix_finiteSpectralMoment_succ_eq_zero _ _

end

end HTGeometry
