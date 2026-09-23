import GaloisForLFunctions.RHTower.XiShiftedParabolicDegreeHorizon
import GaloisForLFunctions.RHTower.XiShiftedMomentSourceJet
import GaloisForLFunctions.HTGeometry.FiniteGaussQuadrature

/-!
# Canonical theta-arithmetic trace-zero Hankel approximants

At degree `k`, use the explicit parabolic mass from the completed prime--Gamma estimate.  Normalize
the literal rational--Gamma-minus-von-Mangoldt reverse-Bessel jet to obtain a source-only moment
sequence.  The parabolic theorem makes its `(k+2)` Hankel block positive definite, so finite Gauss
quadrature supplies exactly `k+1` distinct real nodes.  Translating those nodes by their arithmetic
mean produces a canonical trace-zero diagonal stage.

Every finite unweighted power-trace Hankel block of this stage is positive semidefinite.  In
particular, the block indexed by `0 ≤ r,s ≤ 2 n_k + 1`, where `n_k = k+1` is the mode count,
is positive semidefinite unconditionally.

This module constructs finite source stages.  It does not identify their centered determinants
with the ordinary theta stages or assert compact-open convergence to `Xi`; that hard-edge landing
is a separate divisor-fidelity problem.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Explicit source-derived mass where the degree-`k` shifted moment block is positive. -/
def thetaArithmeticParabolicMass (k : ℕ) : ℝ :=
  routeUParabolicDegreeHorizon * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ))

/-- Positive reverse-Bessel radius associated with the parabolic mass. -/
def thetaArithmeticParabolicRadius (k : ℕ) : ℝ :=
  Real.sqrt (thetaArithmeticParabolicMass k)

/-- Literal completed arithmetic moment: rational--Gamma jet minus von Mangoldt jet, divided by
the exact positive reverse-Bessel normalization.  No Xi zero or divisor coordinate occurs. -/
def thetaArithmeticParabolicMoment (k m : ℕ) : ℝ :=
  ((squaredXiAlternatingRationalGammaJetPolynomial m
      (thetaArithmeticParabolicRadius k : ℂ)).re -
    (squaredXiPrimeJetPolynomial m
      (thetaArithmeticParabolicRadius k : ℂ)).re) /
    ((2 : ℝ) ^ m * (m.factorial : ℝ) *
      thetaArithmeticParabolicRadius k ^ (2 * m + 1))

/-- Degree-`k+1` Gauss nodes selected by the literal arithmetic moment block. -/
def thetaArithmeticParabolicNodes (k : ℕ) : Finset ℝ :=
  HTGeometry.gaussNodes (thetaArithmeticParabolicMoment k) k

/-- Arithmetic mean of the finite source nodes. -/
def thetaArithmeticParabolicNodeCenter (k : ℕ) : ℝ :=
  (∑ x ∈ thetaArithmeticParabolicNodes k, x) / (k + 1 : ℝ)

/-- Centered source-node packet. -/
def thetaArithmeticCenteredNodes (k : ℕ) : Finset ℝ :=
  (thetaArithmeticParabolicNodes k).image
    (fun x => x - thetaArithmeticParabolicNodeCenter k)

/-- Intrinsic mode index of the centered arithmetic stage. -/
def thetaArithmeticTraceZeroStageIndex (k : ℕ) :=
  {x : ℝ // x ∈ thetaArithmeticCenteredNodes k}

instance (k : ℕ) : Fintype (thetaArithmeticTraceZeroStageIndex k) :=
  Finset.fintypeCoeSort _

instance (k : ℕ) : DecidableEq (thetaArithmeticTraceZeroStageIndex k) :=
  Classical.decEq _

/-- Canonical finite source matrix: centered real Gauss nodes on the diagonal. -/
def thetaArithmeticTraceZeroStage (k : ℕ) :
    Matrix (thetaArithmeticTraceZeroStageIndex k)
      (thetaArithmeticTraceZeroStageIndex k) ℂ :=
  Matrix.diagonal (fun x => (x.1 : ℂ))

theorem thetaArithmeticParabolicMass_pos (k : ℕ) :
    0 < thetaArithmeticParabolicMass k := by
  exact mul_pos routeUParabolicDegreeHorizon_pos (sq_pos_of_pos (by positivity))

theorem thetaArithmeticParabolicRadius_sq (k : ℕ) :
    thetaArithmeticParabolicRadius k ^ (2 : ℕ) = thetaArithmeticParabolicMass k := by
  exact Real.sq_sqrt (thetaArithmeticParabolicMass_pos k).le

theorem thetaArithmeticParabolicRadius_gt_half (k : ℕ) :
    1 / 2 < thetaArithmeticParabolicRadius k := by
  have hK : 16 ≤ routeUParabolicDegreeHorizon := le_max_left _ _
  have hk : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hn : (1 : ℝ) ≤ (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (((k + 2 : ℕ) : ℝ) - 1)]
  have hmass : 16 ≤ thetaArithmeticParabolicMass k := by
    rw [thetaArithmeticParabolicMass]
    exact le_trans (by simpa using hK)
      (mul_le_mul_of_nonneg_left hn routeUParabolicDegreeHorizon_pos.le)
  have hr0 := Real.sqrt_nonneg (thetaArithmeticParabolicMass k)
  have hrsq := thetaArithmeticParabolicRadius_sq k
  unfold thetaArithmeticParabolicRadius at hrsq hr0 ⊢
  nlinarith

/-- Exact source/value weld at the chosen parabolic mass.  The left side is defined only from the
completed rational--Gamma and von Mangoldt jets. -/
theorem thetaArithmeticParabolicMoment_eq_shifted (k m : ℕ) :
    thetaArithmeticParabolicMoment k m =
      (xiShiftedReciprocalMoment (thetaArithmeticParabolicMass k) m).re := by
  let w := thetaArithmeticParabolicRadius k
  have hw : 0 < w := lt_trans (by norm_num : (0 : ℝ) < 1 / 2)
    (thetaArithmeticParabolicRadius_gt_half k)
  have hsource := completedSourceJet_eq_rationalGamma_sub_prime m
    (thetaArithmeticParabolicRadius_gt_half k)
  have hmoment := completedSourceJet_eq_xiShiftedReciprocalMoment m hw
  have hwSq : w ^ (2 : ℕ) = thetaArithmeticParabolicMass k :=
    thetaArithmeticParabolicRadius_sq k
  have hscale : (2 : ℝ) ^ m * (m.factorial : ℝ) * w ^ (2 * m + 1) ≠ 0 := by
    positivity
  unfold thetaArithmeticParabolicMoment
  change ((squaredXiAlternatingRationalGammaJetPolynomial m (w : ℂ)).re -
      (squaredXiPrimeJetPolynomial m (w : ℂ)).re) /
      ((2 : ℝ) ^ m * (m.factorial : ℝ) * w ^ (2 * m + 1)) = _
  rw [← hsource, hmoment, hwSq]
  field_simp

/-- The explicit source moment has a positive degree-matched Hankel block. -/
theorem thetaArithmeticParabolicMoment_hankel_posDef (k : ℕ) :
    (HTGeometry.momentHankelMatrix
      (thetaArithmeticParabolicMoment k) (k + 2)).PosDef := by
  have h :
      (xiShiftedMomentHankelMatrix
        (thetaArithmeticParabolicMass k) (k + 2)).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨xiShiftedMomentHankelMatrix_isHermitian _ _, ?_⟩
    intro c hc
    rw [star_trivial]
    change 0 < xiShiftedMomentHankelQuadratic
      (thetaArithmeticParabolicMass k) (k + 2) c
    rw [xiShiftedMomentHankelQuadratic_eq]
    exact xiShiftedReciprocalHankelQuadratic_pos_of_parabolic
      (k + 1) c hc le_rfl
  change (HTGeometry.momentHankelMatrix
    (thetaArithmeticParabolicMoment k) (k + 2)).PosDef
  convert h using 1
  ext i j
  exact thetaArithmeticParabolicMoment_eq_shifted k ((i : ℕ) + (j : ℕ))

/-- Finite Gauss theory gives the full expected node count, so no complex node is omitted. -/
theorem thetaArithmeticParabolicNodes_card (k : ℕ) :
    (thetaArithmeticParabolicNodes k).card = k + 1 := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef
    (thetaArithmeticParabolicMoment_hankel_posDef k)
  exact HTGeometry.gaussNodes_card_below hbelow k (by omega)

theorem thetaArithmeticCenteredNodes_card (k : ℕ) :
    (thetaArithmeticCenteredNodes k).card = k + 1 := by
  rw [thetaArithmeticCenteredNodes, Finset.card_image_of_injective]
  · exact thetaArithmeticParabolicNodes_card k
  · intro x y hxy
    linarith

/-- The stage has exactly `n_k = k+1` modes. -/
theorem thetaArithmeticTraceZeroStageIndex_card (k : ℕ) :
    Fintype.card (thetaArithmeticTraceZeroStageIndex k) = k + 1 := by
  simpa [thetaArithmeticTraceZeroStageIndex] using thetaArithmeticCenteredNodes_card k

theorem sum_thetaArithmeticCenteredNodes (k : ℕ) :
    ∑ x ∈ thetaArithmeticCenteredNodes k, x = 0 := by
  rw [thetaArithmeticCenteredNodes]
  rw [Finset.sum_image]
  · rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [thetaArithmeticParabolicNodes_card]
    unfold thetaArithmeticParabolicNodeCenter
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · intro x hx y hy hxy
    linarith

/-- Exact trace-zero law for every finite arithmetic stage. -/
theorem thetaArithmeticTraceZeroStage_trace (k : ℕ) :
    (thetaArithmeticTraceZeroStage k).trace = 0 := by
  rw [thetaArithmeticTraceZeroStage, Matrix.trace_diagonal]
  change (∑ i : {x : ℝ // x ∈ thetaArithmeticCenteredNodes k}, (i.1 : ℂ)) = 0
  rw [Finset.sum_coe_sort (thetaArithmeticCenteredNodes k)
    (fun x : ℝ => (x : ℂ))]
  rw [← Complex.ofReal_sum]
  rw [sum_thetaArithmeticCenteredNodes]
  simp

/-- Power traces are literal unweighted moments of the centered source-node packet. -/
theorem re_trace_pow_thetaArithmeticTraceZeroStage (k m : ℕ) :
    ((thetaArithmeticTraceZeroStage k ^ m).trace).re =
      ∑ x ∈ thetaArithmeticCenteredNodes k, x ^ m := by
  rw [thetaArithmeticTraceZeroStage, Matrix.diagonal_pow, Matrix.trace_diagonal]
  change ((∑ i : {x : ℝ // x ∈ thetaArithmeticCenteredNodes k},
    (i.1 : ℂ) ^ m)).re = _
  rw [Finset.sum_coe_sort (thetaArithmeticCenteredNodes k)
    (fun x : ℝ => (x : ℂ) ^ m)]
  change Complex.reCLM
    (∑ x ∈ thetaArithmeticCenteredNodes k, (x : ℂ) ^ m) = _
  rw [map_sum]
  simp only [Complex.reCLM_apply, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Finite unweighted trace-Hankel block of the arithmetic stage. -/
def thetaArithmeticTraceHankelBlock (k N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun r s => ((thetaArithmeticTraceZeroStage k ^ ((r : ℕ) + (s : ℕ))).trace).re

theorem thetaArithmeticTraceHankelBlock_eq_momentHankel (k N : ℕ) :
    thetaArithmeticTraceHankelBlock k N =
      HTGeometry.momentHankelMatrix
        (fun m => ∑ x ∈ thetaArithmeticCenteredNodes k, x ^ m) N := by
  ext r s
  exact re_trace_pow_thetaArithmeticTraceZeroStage k ((r : ℕ) + (s : ℕ))

private theorem finiteNodeMomentHankel_posSemidef
    (S : Finset ℝ) (N : ℕ) :
    (HTGeometry.momentHankelMatrix
      (fun m => ∑ x ∈ S, x ^ m) N).PosSemidef := by
  classical
  let atom (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
    fun i j => x ^ ((i : ℕ) + (j : ℕ))
  have hatom (x : ℝ) : (atom x).PosSemidef := by
    let v : Matrix (Fin N) (Fin 1) ℝ := fun i _ => x ^ (i : ℕ)
    have heq : atom x = v * vᴴ := by
      ext i j
      simp [atom, v, Matrix.mul_apply, pow_add]
    rw [heq]
    exact Matrix.posSemidef_self_mul_conjTranspose v
  have heq :
      HTGeometry.momentHankelMatrix (fun m => ∑ x ∈ S, x ^ m) N =
        ∑ x ∈ S, atom x := by
    ext i j
    simp [HTGeometry.momentHankelMatrix, Matrix.sum_apply, atom]
  rw [heq]
  exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun x _ => hatom x)

/-- Every finite power-trace Hankel block is positive semidefinite. -/
theorem thetaArithmeticTraceHankelBlock_posSemidef (k N : ℕ) :
    (thetaArithmeticTraceHankelBlock k N).PosSemidef := by
  rw [thetaArithmeticTraceHankelBlock_eq_momentHankel]
  exact finiteNodeMomentHankel_posSemidef (thetaArithmeticCenteredNodes k) N

/-- Requested finite Hermite window: indices are exactly `0, ..., 2 n_k + 1`. -/
theorem thetaArithmeticTraceHankelRequiredWindow_posSemidef (k : ℕ) :
    (thetaArithmeticTraceHankelBlock k
      (2 * Fintype.card (thetaArithmeticTraceZeroStageIndex k) + 2)).PosSemidef :=
  thetaArithmeticTraceHankelBlock_posSemidef _ _

end

end RHTower
