import GaloisForLFunctions.HTGeometry.ContinuumMatrixSpectralHankel

/-!
# Positive matrix-density spectral block Hankel geometry

The continuum spectral theorem in `ContinuumMatrixSpectralHankel` treats rank-one densities

`rho(omega)_{ab} = g_a(omega) * g_b(omega)`.

Passive multi-channel response theory naturally supplies a larger object: an arbitrary
positive-semidefinite matrix density `rho(omega)`.  Examples include the reciprocal oscillator
strength of an electromagnetic scattering matrix, matrix-valued Kallen--Lehmann densities,
multi-field susceptibilities, and coupled tidal-response channels.

This file proves the missing value relation.  Integrating a pointwise positive-semidefinite matrix
kernel preserves positive semidefiniteness.  Lifting a positive spectral density through all clock
monomials therefore makes every finite block Hankel matrix positive semidefinite.  Positive-measure
separation of every nonzero clock--channel observation upgrades the blocks, their determinants, and
every scalar channel to strict positivity.  Consequently a strictly observable channel cannot lie
in the local closure of any fixed finite spectral palette.

The theorem is about the observability structure of a clock: the clock orders are simultaneous
reporter coordinates of one static spectral density.  No temporal propagation law is assumed.

Physics provenance: Zhang--Monticone--Miller, *All electromagnetic scattering bodies are
matrix-valued oscillators*, Nature Communications 14 (2023), 7724, especially the representation
of the reciprocal oscillator-strength density `X(omega) >= 0`; Li--Xu--Yang--Zhang--Zhou,
*Positivity in Multi-Field EFTs*, Physical Review Letters 127 (2021), 121601.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

noncomputable section

variable {Omega iota : Type*} [MeasurableSpace Omega]

/-! ### Integrating a positive matrix kernel -/

/-- Entrywise integral of a finite real matrix-valued kernel. -/
def integralMatrixKernel
    (mu : Measure Omega) (kernel : Omega -> Matrix iota iota Real) : Matrix iota iota Real :=
  fun i j => ∫ omega, kernel omega i j ∂mu

/-- Quadratic observable of a matrix-valued kernel at one latent state. -/
def integralMatrixKernelQuadratic
    [Fintype iota] (kernel : Omega -> Matrix iota iota Real)
    (x : iota -> Real) (omega : Omega) : Real :=
  dotProduct (star x) ((kernel omega).mulVec x)

/-- Entrywise integration preserves Hermitian symmetry. -/
theorem integralMatrixKernel_isHermitian
    (mu : Measure Omega) (kernel : Omega -> Matrix iota iota Real)
    (hHermitian : forall omega, (kernel omega).IsHermitian) :
    (integralMatrixKernel mu kernel).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp only [integralMatrixKernel, star_trivial]
  apply integral_congr_ae
  exact ae_of_all mu fun omega => by
    simpa only [star_trivial] using (hHermitian omega).apply i j

variable [Fintype iota]

/-- The quadratic observable is integrable whenever every matrix entry is integrable. -/
theorem integrable_integralMatrixKernelQuadratic
    (mu : Measure Omega) (kernel : Omega -> Matrix iota iota Real)
    (hEntry : forall i j, Integrable (fun omega => kernel omega i j) mu)
    (x : iota -> Real) :
    Integrable (integralMatrixKernelQuadratic kernel x) mu := by
  unfold integralMatrixKernelQuadratic
  simp only [dotProduct, Matrix.mulVec, star_trivial]
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  have h := (hEntry i j).const_mul (x i * x j)
  simpa only [Pi.mul_apply] using h.congr (ae_of_all mu fun omega => by ring)

/-- The quadratic form of an entrywise integral is the integral of the pointwise quadratic
form. -/
theorem integralMatrixKernel_quadratic_eq_integral
    (mu : Measure Omega) (kernel : Omega -> Matrix iota iota Real)
    (hEntry : forall i j, Integrable (fun omega => kernel omega i j) mu)
    (x : iota -> Real) :
    dotProduct (star x) ((integralMatrixKernel mu kernel).mulVec x) =
      ∫ omega, integralMatrixKernelQuadratic kernel x omega ∂mu := by
  have hTerm : forall i j,
      Integrable (fun omega => x i * kernel omega i j * x j) mu := by
    intro i j
    have h := (hEntry i j).const_mul (x i * x j)
    simpa only [Pi.mul_apply] using h.congr (ae_of_all mu fun omega => by ring)
  calc
    dotProduct (star x) ((integralMatrixKernel mu kernel).mulVec x) =
        ∑ i, ∑ j, x i * (∫ omega, kernel omega i j ∂mu) * x j := by
      simp only [dotProduct, Matrix.mulVec, integralMatrixKernel, star_trivial]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j,
        ∫ omega, x i * kernel omega i j * x j ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      calc
        x i * (∫ omega, kernel omega i j ∂mu) * x j =
            (x i * x j) * (∫ omega, kernel omega i j ∂mu) := by ring
        _ = ∫ omega, (x i * x j) * kernel omega i j ∂mu := by
          rw [integral_const_mul]
        _ = ∫ omega, x i * kernel omega i j * x j ∂mu := by
          congr 1
          funext omega
          ring
    _ = ∫ omega, (∑ i, ∑ j,
          x i * kernel omega i j * x j) ∂mu := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ]
        exact fun j hj => hTerm i j
      · intro i hi
        exact integrable_finsetSum Finset.univ fun j hj => hTerm i j
    _ = ∫ omega, integralMatrixKernelQuadratic kernel x omega ∂mu := by
      congr 1
      funext omega
      simp only [integralMatrixKernelQuadratic, dotProduct, Matrix.mulVec, star_trivial,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Pointwise positive-semidefinite matrix densities remain positive semidefinite after
entrywise integration. -/
theorem integralMatrixKernel_posSemidef
    (mu : Measure Omega) (kernel : Omega -> Matrix iota iota Real)
    (hEntry : forall i j, Integrable (fun omega => kernel omega i j) mu)
    (hPSD : forall omega, (kernel omega).PosSemidef) :
    (integralMatrixKernel mu kernel).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact integralMatrixKernel_isHermitian mu kernel fun omega => (hPSD omega).isHermitian
  · intro x
    rw [integralMatrixKernel_quadratic_eq_integral mu kernel hEntry x]
    exact integral_nonneg fun omega => (hPSD omega).dotProduct_mulVec_nonneg x

/-- Positive-measure separation of every nonzero matrix observation upgrades the integral from
positive semidefinite to positive definite. -/
theorem integralMatrixKernel_posDef_of_support
    (mu : Measure Omega) (kernel : Omega -> Matrix iota iota Real)
    (hEntry : forall i j, Integrable (fun omega => kernel omega i j) mu)
    (hPSD : forall omega, (kernel omega).PosSemidef)
    (hSeparate : forall x : iota -> Real, x ≠ 0 ->
      0 < mu (Function.support (integralMatrixKernelQuadratic kernel x))) :
    (integralMatrixKernel mu kernel).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact integralMatrixKernel_isHermitian mu kernel fun omega => (hPSD omega).isHermitian
  · intro x hx
    rw [integralMatrixKernel_quadratic_eq_integral mu kernel hEntry x]
    have hNonneg : forall omega,
        0 <= integralMatrixKernelQuadratic kernel x omega := by
      intro omega
      exact (hPSD omega).dotProduct_mulVec_nonneg x
    have hPositive : 0 < ∫ omega, integralMatrixKernelQuadratic kernel x omega ∂mu :=
      (integral_pos_iff_support_of_nonneg hNonneg
        (integrable_integralMatrixKernelQuadratic mu kernel hEntry x)).2
          (hSeparate x hx)
    exact hPositive

/-! ### Arbitrary positive matrix-valued spectral densities -/

/-- The spectral lift sends joint clock--channel coefficients to physical channel amplitudes at
one spectral state. -/
def psdMatrixSpectralLift {m n : Nat}
    (node : Omega -> Real) (omega : Omega) :
    Matrix (Fin m) (Fin n × Fin m) Real :=
  fun a ia => if a = ia.2 then node omega ^ (ia.1 : Nat) else 0

/-- Pointwise block kernel obtained by lifting a channel density through all clock monomials. -/
def psdMatrixSpectralKernel {m : Nat}
    (node : Omega -> Real) (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (n : Nat) (omega : Omega) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) Real :=
  Matrix.conjTranspose (psdMatrixSpectralLift (m := m) (n := n) node omega) * density omega *
    psdMatrixSpectralLift (m := m) (n := n) node omega

/-- Entry value of the lifted spectral kernel. -/
theorem psdMatrixSpectralKernel_apply {m : Nat}
    (node : Omega -> Real) (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (n : Nat) (omega : Omega) (ia jb : Fin n × Fin m) :
    psdMatrixSpectralKernel node density n omega ia jb =
      node omega ^ (ia.1 : Nat) * density omega ia.2 jb.2 *
        node omega ^ (jb.1 : Nat) := by
  simp [psdMatrixSpectralKernel, psdMatrixSpectralLift, Matrix.mul_apply]

/-- A positive channel density remains positive after the clock-order lift. -/
theorem psdMatrixSpectralKernel_posSemidef {m : Nat}
    (node : Omega -> Real) (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (n : Nat) (omega : Omega) (hDensity : (density omega).PosSemidef) :
    (psdMatrixSpectralKernel node density n omega).PosSemidef := by
  exact hDensity.conjTranspose_mul_mul_same
    (psdMatrixSpectralLift (m := m) (n := n) node omega)

/-- Matrix-valued spectral moment of an arbitrary positive matrix density. -/
def psdMatrixSpectralMoment {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (k : Nat) : Matrix (Fin m) (Fin m) Real :=
  fun a b => ∫ omega, density omega a b * node omega ^ k ∂mu

/-- Block Hankel matrix indexed jointly by clock order and physical channel. -/
def psdMatrixSpectralBlockHankel {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (n : Nat) : Matrix (Fin n × Fin m) (Fin n × Fin m) Real :=
  fun ia jb => psdMatrixSpectralMoment mu node density
    ((ia.1 : Nat) + (jb.1 : Nat)) ia.2 jb.2

/-- The matrix-density spectral block is the entrywise integral of the lifted positive kernel. -/
theorem psdMatrixSpectralBlockHankel_eq_integralMatrixKernel {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real) (n : Nat) :
    psdMatrixSpectralBlockHankel mu node density n =
      integralMatrixKernel mu (psdMatrixSpectralKernel node density n) := by
  ext ia jb
  simp only [psdMatrixSpectralBlockHankel, psdMatrixSpectralMoment,
    integralMatrixKernel]
  congr 1
  funext omega
  rw [psdMatrixSpectralKernel_apply, pow_add]
  ring

/-- Integrability of the direct matrix moments is exactly enough for the lifted kernel entries. -/
theorem integrable_psdMatrixSpectralKernel_of_moments {m n : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (hMoment : forall ia jb : Fin n × Fin m,
      Integrable (fun omega => density omega ia.2 jb.2 *
        node omega ^ ((ia.1 : Nat) + (jb.1 : Nat))) mu) :
    forall ia jb : Fin n × Fin m,
      Integrable (fun omega => psdMatrixSpectralKernel node density n omega ia jb) mu := by
  intro ia jb
  exact (hMoment ia jb).congr (ae_of_all mu fun omega => by
    change density omega ia.2 jb.2 *
        node omega ^ ((ia.1 : Nat) + (jb.1 : Nat)) =
      psdMatrixSpectralKernel node density n omega ia jb
    rw [psdMatrixSpectralKernel_apply, pow_add]
    ring)

/-- **Positive matrix-density moment law.**  Every finite block Hankel matrix of a pointwise
positive-semidefinite spectral density is positive semidefinite. -/
theorem psdMatrixSpectralBlockHankel_posSemidef {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real) (n : Nat)
    (hMoment : forall ia jb : Fin n × Fin m,
      Integrable (fun omega => density omega ia.2 jb.2 *
        node omega ^ ((ia.1 : Nat) + (jb.1 : Nat))) mu)
    (hDensity : forall omega, (density omega).PosSemidef) :
    (psdMatrixSpectralBlockHankel mu node density n).PosSemidef := by
  rw [psdMatrixSpectralBlockHankel_eq_integralMatrixKernel]
  exact integralMatrixKernel_posSemidef mu
    (psdMatrixSpectralKernel node density n)
    (integrable_psdMatrixSpectralKernel_of_moments mu node density hMoment)
    (fun omega => psdMatrixSpectralKernel_posSemidef node density n omega (hDensity omega))

/-- Quadratic observation made by a joint clock--channel coefficient vector at one spectral
state. -/
def psdMatrixSpectralObservedQuadratic {m n : Nat}
    (node : Omega -> Real) (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (x : Fin n × Fin m -> Real) (omega : Omega) : Real :=
  integralMatrixKernelQuadratic (psdMatrixSpectralKernel node density n) x omega

/-- Positive-measure separation of every nonzero joint observation makes the whole spectral block
positive definite. -/
theorem psdMatrixSpectralBlockHankel_posDef_of_jointSeparation {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real) (n : Nat)
    (hMoment : forall ia jb : Fin n × Fin m,
      Integrable (fun omega => density omega ia.2 jb.2 *
        node omega ^ ((ia.1 : Nat) + (jb.1 : Nat))) mu)
    (hDensity : forall omega, (density omega).PosSemidef)
    (hSeparate : forall x : Fin n × Fin m -> Real, x ≠ 0 ->
      0 < mu (Function.support
        (psdMatrixSpectralObservedQuadratic node density x))) :
    (psdMatrixSpectralBlockHankel mu node density n).PosDef := by
  rw [psdMatrixSpectralBlockHankel_eq_integralMatrixKernel]
  exact integralMatrixKernel_posDef_of_support mu
    (psdMatrixSpectralKernel node density n)
    (integrable_psdMatrixSpectralKernel_of_moments mu node density hMoment)
    (fun omega => psdMatrixSpectralKernel_posSemidef node density n omega (hDensity omega))
    (by simpa only [psdMatrixSpectralObservedQuadratic] using hSeparate)

/-- Joint separation makes every finite matrix-density block determinant strictly positive. -/
theorem det_psdMatrixSpectralBlockHankel_pos_of_jointSeparation {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real) (n : Nat)
    (hMoment : forall ia jb : Fin n × Fin m,
      Integrable (fun omega => density omega ia.2 jb.2 *
        node omega ^ ((ia.1 : Nat) + (jb.1 : Nat))) mu)
    (hDensity : forall omega, (density omega).PosSemidef)
    (hSeparate : forall x : Fin n × Fin m -> Real, x ≠ 0 ->
      0 < mu (Function.support
        (psdMatrixSpectralObservedQuadratic node density x))) :
    0 < (psdMatrixSpectralBlockHankel mu node density n).det :=
  (psdMatrixSpectralBlockHankel_posDef_of_jointSeparation
    mu node density n hMoment hDensity hSeparate).det_pos

/-- Scalar moment sequence observed in one physical channel of a matrix density. -/
def psdMatrixSpectralChannelMoment {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (a : Fin m) (k : Nat) : Real :=
  psdMatrixSpectralMoment mu node density k a a

/-- A scalar matrix-density channel Hankel matrix is a principal submatrix of the joint block. -/
theorem momentHankelMatrix_psdMatrixSpectralChannelMoment_eq_submatrix {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (a : Fin m) (n : Nat) :
    momentHankelMatrix (psdMatrixSpectralChannelMoment mu node density a) n =
      (psdMatrixSpectralBlockHankel mu node density n).submatrix
        (fun i => (i, a)) (fun i => (i, a)) := by
  rfl

/-- Joint separation discharges strict scalar Hankel positivity in every physical channel. -/
theorem det_momentHankelMatrix_psdMatrixSpectralChannelMoment_pos_of_jointSeparation
    {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (a : Fin m) (n : Nat)
    (hMoment : forall ia jb : Fin n × Fin m,
      Integrable (fun omega => density omega ia.2 jb.2 *
        node omega ^ ((ia.1 : Nat) + (jb.1 : Nat))) mu)
    (hDensity : forall omega, (density omega).PosSemidef)
    (hSeparate : forall x : Fin n × Fin m -> Real, x ≠ 0 ->
      0 < mu (Function.support
        (psdMatrixSpectralObservedQuadratic node density x))) :
    0 < (momentHankelMatrix
      (psdMatrixSpectralChannelMoment mu node density a) n).det := by
  rw [momentHankelMatrix_psdMatrixSpectralChannelMoment_eq_submatrix]
  exact ((psdMatrixSpectralBlockHankel_posDef_of_jointSeparation
    mu node density n hMoment hDensity hSeparate).submatrix
      (fun i j h => congrArg Prod.fst h)).det_pos

/-- A strictly observable channel of a positive matrix density cannot lie in the local closure of
any fixed finite spectral palette. -/
theorem psdMatrixSpectralChannelMoment_not_fixedSpectralWidthLocalClosure
    {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (density : Omega -> Matrix (Fin m) (Fin m) Real)
    (a : Fin m) (d : Nat)
    (hMoment : forall ia jb : Fin (d + 1) × Fin m,
      Integrable (fun omega => density omega ia.2 jb.2 *
        node omega ^ ((ia.1 : Nat) + (jb.1 : Nat))) mu)
    (hDensity : forall omega, (density omega).PosSemidef)
    (hSeparate : forall x : Fin (d + 1) × Fin m -> Real, x ≠ 0 ->
      0 < mu (Function.support
        (psdMatrixSpectralObservedQuadratic node density x))) :
    ¬ FixedSpectralWidthLocalClosure d
      (psdMatrixSpectralChannelMoment mu node density a) := by
  apply not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt
    (det_momentHankelMatrix_psdMatrixSpectralChannelMoment_pos_of_jointSeparation
      mu node density a (d + 1) hMoment hDensity hSeparate)

/-! ### The previous rank-one density is an exact specialization -/

/-- Rank-one matrix density generated by one reporter-coupling vector. -/
def rankOneMatrixSpectralDensity {m : Nat}
    (coupling : Omega -> Fin m -> Real) (omega : Omega) :
    Matrix (Fin m) (Fin m) Real :=
  fun a b => coupling omega a * coupling omega b

/-- The arbitrary-density moment theorem strictly extends the existing rank-one continuum moment
definition without changing its values. -/
theorem psdMatrixSpectralMoment_rankOne_eq_continuumMatrixSpectralMoment {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (coupling : Omega -> Fin m -> Real) (k : Nat) :
    psdMatrixSpectralMoment mu node (rankOneMatrixSpectralDensity coupling) k =
      continuumMatrixSpectralMoment mu node coupling k := by
  ext a b
  simp only [psdMatrixSpectralMoment, rankOneMatrixSpectralDensity,
    continuumMatrixSpectralMoment]

/-- The whole rank-one block Hankel construction is recovered exactly. -/
theorem psdMatrixSpectralBlockHankel_rankOne_eq_continuumMatrixSpectralBlockHankel
    {m : Nat}
    (mu : Measure Omega) (node : Omega -> Real)
    (coupling : Omega -> Fin m -> Real) (n : Nat) :
    psdMatrixSpectralBlockHankel mu node (rankOneMatrixSpectralDensity coupling) n =
      continuumMatrixSpectralBlockHankel mu node coupling n := by
  ext ia jb
  exact congrFun (congrFun
    (psdMatrixSpectralMoment_rankOne_eq_continuumMatrixSpectralMoment
      mu node coupling ((ia.1 : Nat) + (jb.1 : Nat))) ia.2) jb.2

end

end HTGeometry
