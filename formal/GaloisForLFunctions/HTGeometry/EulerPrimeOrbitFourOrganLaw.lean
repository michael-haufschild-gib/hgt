import GaloisForLFunctions.HTGeometry.InfiniteTorusForwardDensity
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Euler prime-orbit prolongation, recurrence, polar loss, and cofinal wall

This module closes the finite spectral normal form and its primitive-prime specialization from
`euler-prime-orbit-prolongation-recurrence-polar-cofinal-law.md`.

The construction is source-side and unconditional.  A finite diagonal family has a full Krylov
basis by a weighted Vandermonde argument.  Rationally independent real frequencies have dense
forward phase tails, while the modulus observer is constant and the lifted phase energy is
unbounded.  For the Euler source, unique factorization supplies frequency independence and the
prime amplitudes `log p * p^{-sigma}` meet the sharp square-summability wall `sigma = 1/2`.
-/

open Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Finite diagonal spectral normal form -/

/-- The `k`-th vector in a weighted diagonal Krylov family. -/
def finiteDiagonalKrylovVector {ι : Type*}
    (node weight : ι → ℂ) (k : ℕ) : ι → ℂ :=
  fun i => weight i * node i ^ k

/-- A square weighted Vandermonde family is linearly independent. -/
theorem finiteDiagonalKrylovVector_linearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {node weight : ι → ℂ} (hnode : Function.Injective node)
    (hweight : ∀ i, weight i ≠ 0) :
    LinearIndependent ℂ
      (fun k : Fin (Fintype.card ι) =>
        finiteDiagonalKrylovVector node weight (k : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let beta : Fin (Fintype.card ι) → ℂ := fun j => node (e.symm j)
  have hbeta : Function.Injective beta := hnode.comp e.symm.injective
  have hmul : (Matrix.vandermonde beta).mulVec c = 0 := by
    funext j
    have hj := congrFun hc (e.symm j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      finiteDiagonalKrylovVector] at hj
    have hfactor :
        weight (e.symm j) *
            (∑ k : Fin (Fintype.card ι),
              node (e.symm j) ^ (k : ℕ) * c k) = 0 := by
      calc
        weight (e.symm j) *
            (∑ k : Fin (Fintype.card ι),
              node (e.symm j) ^ (k : ℕ) * c k) =
            ∑ k : Fin (Fintype.card ι),
              c k * (weight (e.symm j) * node (e.symm j) ^ (k : ℕ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                ring_nf
        _ = 0 := hj
    have hrow :
        ∑ k : Fin (Fintype.card ι),
          node (e.symm j) ^ (k : ℕ) * c k = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (hweight (e.symm j))
    simpa only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
      Pi.zero_apply, beta] using hrow
  have hdet : (Matrix.vandermonde beta).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    exact hbeta
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  exact fun i => congrFun hc0 i

/-- The full finite diagonal Krylov family, as a basis of the coordinate Hilbert space. -/
def finiteDiagonalKrylovBasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node weight : ι → ℂ) (hnode : Function.Injective node)
    (hweight : ∀ i, weight i ≠ 0) :
    Module.Basis (Fin (Fintype.card ι)) ℂ (ι → ℂ) := by
  let hli := finiteDiagonalKrylovVector_linearIndependent hnode hweight
  refine Module.Basis.mk hli ?_
  rw [hli.span_eq_top_of_card_eq_finrank' (by simp)]

@[simp]
theorem finiteDiagonalKrylovBasis_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node weight : ι → ℂ) (hnode : Function.Injective node)
    (hweight : ∀ i, weight i ≠ 0) (k : Fin (Fintype.card ι)) :
    finiteDiagonalKrylovBasis node weight hnode hweight k =
      finiteDiagonalKrylovVector node weight (k : ℕ) := by
  rw [finiteDiagonalKrylovBasis, Module.Basis.mk_apply]

/-- A fixed number of Krylov vectors cannot span coordinate spaces of unbounded dimension. -/
theorem finiteDiagonalKrylov_span_ne_top_of_lt_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node weight : ι → ℂ) (r : ℕ) (hr : r + 1 < Fintype.card ι) :
    Submodule.span ℂ
        (Set.range fun k : Fin (r + 1) =>
          finiteDiagonalKrylovVector node weight (k : ℕ)) ≠ ⊤ := by
  intro htop
  have hle := finrank_span_le_card (R := ℂ)
    (Set.range fun k : Fin (r + 1) =>
      finiteDiagonalKrylovVector node weight (k : ℕ))
  have hrange :
      (Set.range fun k : Fin (r + 1) =>
        finiteDiagonalKrylovVector node weight (k : ℕ)).toFinset.card ≤ r + 1 := by
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le
      (fun k : Fin (r + 1) => finiteDiagonalKrylovVector node weight (k : ℕ))
  have hdim : Fintype.card ι ≤ r + 1 := by
    calc
      Fintype.card ι = Module.finrank ℂ (ι → ℂ) := by simp
      _ = Module.finrank ℂ
          (Submodule.span ℂ
            (Set.range fun k : Fin (r + 1) =>
              finiteDiagonalKrylovVector node weight (k : ℕ))) := by rw [htop]; simp
      _ ≤ (Set.range fun k : Fin (r + 1) =>
          finiteDiagonalKrylovVector node weight (k : ℕ)).toFinset.card := hle
      _ ≤ r + 1 := hrange
  omega

/-- A diagonal phase orbit with the sign convention `exp(-i t lambda)`. -/
def finiteDiagonalPhaseOrbit {ι : Type*}
    (frequency : ι → ℝ) (weight : ι → ℂ) (t : ℝ) : ι → ℂ :=
  fun i => weight i * expChar (-frequency i) t

/-- Coordinatewise modulus energy of a finite vector. -/
def finiteDiagonalEnergy {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  ∑ i, ‖x i‖ ^ 2

/-- Unitary diagonal evolution preserves the complete modulus energy. -/
theorem finiteDiagonalEnergy_phaseOrbit
    {ι : Type*} [Fintype ι]
    (frequency : ι → ℝ) (weight : ι → ℂ) (t : ℝ) :
    finiteDiagonalEnergy (finiteDiagonalPhaseOrbit frequency weight t) =
      ∑ i, ‖weight i‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  simp [finiteDiagonalPhaseOrbit, norm_expChar]

/-- The same positive observer is constant on the entire fixed-radius phase torus. -/
theorem finiteDiagonalEnergy_eq_of_coordinate_norm_eq
    {ι : Type*} [Fintype ι] {x weight : ι → ℂ}
    (h : ∀ i, ‖x i‖ = ‖weight i‖) :
    finiteDiagonalEnergy x = ∑ i, ‖weight i‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]

/-- Squared Euclidean energy of the logarithmic phase lift. -/
def finitePhaseLiftEnergy {ι : Type*} [Fintype ι]
    (frequency : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (-t * frequency i) ^ 2

/-- One nonzero frequency makes the logarithmic phase lift unbounded. -/
theorem finitePhaseLiftEnergy_unbounded
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (frequency : ι → ℝ) (i₀ : ι) (hi₀ : frequency i₀ ≠ 0) :
    ∀ R : ℝ, ∃ t : ℝ, R < finitePhaseLiftEnergy frequency t := by
  intro R
  let t : ℝ := (|R| + 1) / |frequency i₀|
  have hfreq : 0 < |frequency i₀| := abs_pos.mpr hi₀
  have hcoord : (-t * frequency i₀) ^ 2 = (|R| + 1) ^ 2 := by
    calc
      (-t * frequency i₀) ^ 2 = t ^ 2 * frequency i₀ ^ 2 := by ring_nf
      _ = t ^ 2 * |frequency i₀| ^ 2 := by rw [sq_abs]
      _ = (|R| + 1) ^ 2 := by
        dsimp [t]
        field_simp
  refine ⟨t, lt_of_lt_of_le ?_ (Finset.single_le_sum
    (fun i _ => sq_nonneg (-t * frequency i)) (Finset.mem_univ i₀))⟩
  rw [hcoord]
  nlinarith [abs_nonneg R, le_abs_self R]

/-- Exact weighted Kronecker approximation of every point of a finite radius torus. -/
theorem finiteDiagonalPhaseOrbit_approx
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {frequency : ι → ℝ} (hfrequency : LinearIndependent ℚ frequency)
    {weight : ι → ℂ} (hweight : ∀ i, weight i ≠ 0)
    (theta : ι → ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, ∀ i,
      ‖finiteDiagonalPhaseOrbit frequency weight t i -
          weight i * Complex.exp ((theta i : ℝ) * Complex.I)‖ <
        ‖weight i‖ * epsilon := by
  obtain ⟨s, hs⟩ := kronecker_approx hfrequency theta hepsilon
  refine ⟨-s, fun i => ?_⟩
  have horbit : expChar (-frequency i) (-s) = expChar (frequency i) s := by
    unfold expChar
    congr 1
    push_cast
    ring_nf
  rw [finiteDiagonalPhaseOrbit, horbit, ← mul_sub, norm_mul]
  exact mul_lt_mul_of_pos_left (hs i) (norm_pos_iff.mpr (hweight i))

/-! ## Primitive-prime source orbit -/

/-- Primitive-prime coefficient of the Euler--Möbius logarithmic current. -/
def eulerPrimitivePrimeCurrent (p : Nat.Primes) : ℝ :=
  Real.log (p : ℕ)

/-- On a primitive prime, the source current is exactly the von Mangoldt coefficient. -/
theorem eulerPrimitivePrimeCurrent_eq_vonMangoldt (p : Nat.Primes) :
    eulerPrimitivePrimeCurrent p =
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) (p : ℕ) := by
  rw [eulerPrimitivePrimeCurrent,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]

/-- Prime-log spectral node. -/
def eulerPrimeLogNode (p : Nat.Primes) : ℂ :=
  (Real.log (p : ℕ) : ℂ)

/-- Primitive-prime amplitude `log p * p^{-sigma}` at real density `sigma`. -/
def eulerPrimeSigmaAmplitude (sigma : ℝ) (p : Nat.Primes) : ℂ :=
  ((Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-sigma) : ℝ) : ℂ)

/-- Half-density primitive-prime amplitude `log p / sqrt p`, in rpow coordinates. -/
def eulerPrimeHalfDensityAmplitude (p : Nat.Primes) : ℂ :=
  eulerPrimeSigmaAmplitude (1 / 2) p

/-- The rpow amplitude is literally the paper's `log p / sqrt p` normalization. -/
theorem eulerPrimeHalfDensityAmplitude_eq_log_div_sqrt (p : Nat.Primes) :
    eulerPrimeHalfDensityAmplitude p =
      ((Real.log (p : ℕ) / Real.sqrt ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [eulerPrimeHalfDensityAmplitude, eulerPrimeSigmaAmplitude]
  norm_cast
  have hp0 : 0 ≤ ((p : ℕ) : ℝ) := by positivity
  rw [Real.rpow_neg hp0, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

theorem eulerPrimeLogNode_injective : Function.Injective eulerPrimeLogNode := by
  intro p q hpq
  have hreal : Real.log ((p : ℕ) : ℝ) = Real.log ((q : ℕ) : ℝ) := by
    exact Complex.ofReal_injective hpq
  have hp0 : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hq0 : 0 < ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.pos
  have hcast : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) := by
    simpa [Real.exp_log hp0, Real.exp_log hq0] using congrArg Real.exp hreal
  apply Subtype.ext
  exact_mod_cast hcast

theorem eulerPrimeHalfDensityAmplitude_ne_zero (p : Nat.Primes) :
    eulerPrimeHalfDensityAmplitude p ≠ 0 := by
  have hp0 : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  rw [eulerPrimeHalfDensityAmplitude, eulerPrimeSigmaAmplitude]
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero hlog.ne' (ne_of_gt (Real.rpow_pos_of_pos hp0 _))

/-- The primitive-prime half-density vector on a finite source aperture. -/
def finiteEulerPrimeVector (F : Finset Nat.Primes) : F → ℂ :=
  fun p => eulerPrimeHalfDensityAmplitude p

/-- The finite prime-log diagonal generator. -/
def finiteEulerPrimeGenerator (F : Finset Nat.Primes) : (F → ℂ) →ₗ[ℂ] (F → ℂ) where
  toFun x p := eulerPrimeLogNode p * x p
  map_add' x y := by
    ext p
    simp only [Pi.add_apply]
    ring_nf
  map_smul' c x := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

@[simp]
theorem finiteEulerPrimeGenerator_apply
    (F : Finset Nat.Primes) (x : F → ℂ) (p : F) :
    finiteEulerPrimeGenerator F x p = eulerPrimeLogNode p * x p := rfl

/-- The first negative prime-log jet is the primitive-prime coefficient of the reflection-odd
Weil position torque. -/
theorem neg_finiteEulerPrimeGenerator_vector_apply
    (F : Finset Nat.Primes) (p : F) :
    -(finiteEulerPrimeGenerator F (finiteEulerPrimeVector F) p) =
      ((-(Real.log ((p : Nat.Primes) : ℕ) ^ 2 *
        (((p : Nat.Primes) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
  rw [finiteEulerPrimeGenerator_apply, finiteEulerPrimeVector,
    eulerPrimeLogNode, eulerPrimeHalfDensityAmplitude, eulerPrimeSigmaAmplitude]
  norm_cast
  ring_nf

/-- Powers of the source generator are exactly the weighted Krylov vectors. -/
theorem iterate_finiteEulerPrimeGenerator_vector
    (F : Finset Nat.Primes) (k : ℕ) :
    ((finiteEulerPrimeGenerator F : (F → ℂ) → (F → ℂ))^[k])
        (finiteEulerPrimeVector F) =
      finiteDiagonalKrylovVector
        (fun p : F => eulerPrimeLogNode p)
        (finiteEulerPrimeVector F) k := by
  induction k with
  | zero =>
      ext p
      simp [finiteEulerPrimeVector, finiteDiagonalKrylovVector]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      ext p
      simp only [finiteEulerPrimeGenerator_apply, finiteDiagonalKrylovVector]
      rw [pow_succ]
      ring_nf

/-- Full finite prolongation rank: the first `|F|` Euler prime-log jets form a basis. -/
def finiteEulerPrimeKrylovBasis (F : Finset Nat.Primes) :
    Module.Basis (Fin (Fintype.card F)) ℂ (F → ℂ) :=
  finiteDiagonalKrylovBasis
    (fun p : F => eulerPrimeLogNode p)
    (finiteEulerPrimeVector F)
    (eulerPrimeLogNode_injective.comp Subtype.coe_injective)
    (fun p => eulerPrimeHalfDensityAmplitude_ne_zero p)

@[simp]
theorem finiteEulerPrimeKrylovBasis_apply
    (F : Finset Nat.Primes) (k : Fin (Fintype.card F)) :
    finiteEulerPrimeKrylovBasis F k =
      ((finiteEulerPrimeGenerator F : (F → ℂ) → (F → ℂ))^[(k : ℕ)])
        (finiteEulerPrimeVector F) := by
  rw [finiteEulerPrimeKrylovBasis, finiteDiagonalKrylovBasis_apply,
    iterate_finiteEulerPrimeGenerator_vector]

/-- No fixed linear prolongation order spans all sufficiently large finite prime cutoffs. -/
theorem finiteEulerPrime_fixedOrder_span_ne_top
    (F : Finset Nat.Primes) (r : ℕ) (hr : r + 1 < F.card) :
    Submodule.span ℂ
        (Set.range fun k : Fin (r + 1) =>
          ((finiteEulerPrimeGenerator F : (F → ℂ) → (F → ℂ))^[(k : ℕ)])
            (finiteEulerPrimeVector F)) ≠ ⊤ := by
  simpa only [iterate_finiteEulerPrimeGenerator_vector] using
    finiteDiagonalKrylov_span_ne_top_of_lt_card
      (fun p : F => eulerPrimeLogNode p) (finiteEulerPrimeVector F) r
        (by simpa using hr)

/-- Finite primitive-prime Mellin/Fourier orbit. -/
def finiteEulerPrimeOrbit (F : Finset Nat.Primes) (t : ℝ) : F → ℂ :=
  finiteDiagonalPhaseOrbit
    (fun p : F => Real.log ((p : Nat.Primes) : ℕ))
    (finiteEulerPrimeVector F) t

theorem finiteEulerPrimeOrbit_apply
    (F : Finset Nat.Primes) (t : ℝ) (p : F) :
    finiteEulerPrimeOrbit F t p =
      finiteEulerPrimeVector F p *
        Complex.exp (((-t * Real.log ((p : Nat.Primes) : ℕ) : ℝ) : ℂ) * Complex.I) := by
  rw [finiteEulerPrimeOrbit, finiteDiagonalPhaseOrbit, expChar]
  congr 2
  push_cast
  ring_nf

/-- Every point of the finite radius torus can be approximated in all prime coordinates. -/
theorem finiteEulerPrimeOrbit_approx
    (F : Finset Nat.Primes) (theta : F → ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, ∀ p : F,
      ‖finiteEulerPrimeOrbit F t p -
          finiteEulerPrimeVector F p *
            Complex.exp ((theta p : ℝ) * Complex.I)‖ <
        ‖finiteEulerPrimeVector F p‖ * epsilon := by
  exact finiteDiagonalPhaseOrbit_approx
    (primeLogFiniteSlice_linearIndependent F)
    (fun p => eulerPrimeHalfDensityAmplitude_ne_zero p) theta hepsilon

/-- Every forward tail of the finite prime phase flow is dense in its phase torus. -/
theorem finiteEulerPrimePhase_forwardTail_dense
    (F : Finset Nat.Primes) (T : ℝ) :
    Dense {x : UnitAddTorus F |
      ∃ t : ℝ, T ≤ t ∧
        clockPhasePoint
          (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) t = x} := by
  apply dense_forwardOrbit
  apply rationallyIndependentSequence_of_linearIndependent_int
  exact logPrime_linearIndependent_int.comp
    (fun p : F => (p : Nat.Primes)) Subtype.coe_injective

/-- Every finite prime phase returns arbitrarily close to its initial point after any prescribed
positive time threshold. -/
theorem finiteEulerPrimePhase_recurrent
    (F : Finset Nat.Primes) (T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, T ≤ t ∧
      dist (clockPhasePoint
        (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) t) 0 < epsilon := by
  have hdense := finiteEulerPrimePhase_forwardTail_dense F T
  obtain ⟨x, hxball, t, ht, htx⟩ :=
    (dense_iff_inter_open.mp hdense) (Metric.ball 0 epsilon)
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self hepsilon⟩
  refine ⟨t, ht, ?_⟩
  rwa [htx]

/-- The logarithmic lift of every nonempty finite prime orbit has unbounded Euclidean energy. -/
theorem finiteEulerPrimePhaseLiftEnergy_unbounded
    (F : Finset Nat.Primes) (hF : F.Nonempty) :
    ∀ R : ℝ, ∃ t : ℝ,
      R < finitePhaseLiftEnergy
        (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) t := by
  let p₀ : F := ⟨hF.choose, hF.choose_spec⟩
  letI : Nonempty F := ⟨p₀⟩
  apply finitePhaseLiftEnergy_unbounded
    (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) p₀
  exact ne_of_gt (Real.log_pos (by exact_mod_cast (p₀ : Nat.Primes).prop.one_lt))

/-! ## Polar energy and cofinal half-density wall -/

/-- Static primitive-prime polar energy on a finite aperture. -/
def finiteEulerPrimePolarEnergy (F : Finset Nat.Primes) : ℝ :=
  ∑ p : F, Real.log ((p : Nat.Primes) : ℝ) ^ 2 / ((p : Nat.Primes) : ℝ)

theorem eulerPrimeHalfDensityAmplitude_norm_sq (p : Nat.Primes) :
    ‖eulerPrimeHalfDensityAmplitude p‖ ^ 2 =
      Real.log ((p : ℕ) : ℝ) ^ 2 / ((p : ℕ) : ℝ) := by
  have hp0 : 0 ≤ ((p : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).le
  rw [eulerPrimeHalfDensityAmplitude, eulerPrimeSigmaAmplitude,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg hlog (Real.rpow_nonneg hp0 _)), mul_pow,
    ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) 2,
    ← Real.rpow_mul hp0,
    show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring_nf,
    Real.rpow_neg_one]
  ring_nf

/-- Positive energy is constant along the entire finite source orbit. -/
theorem finiteEulerPrimeOrbit_polarEnergy
    (F : Finset Nat.Primes) (t : ℝ) :
    finiteDiagonalEnergy (finiteEulerPrimeOrbit F t) =
      finiteEulerPrimePolarEnergy F := by
  rw [finiteEulerPrimeOrbit,
    finiteDiagonalEnergy_phaseOrbit, finiteEulerPrimePolarEnergy]
  apply Finset.sum_congr rfl
  intro p _
  exact eulerPrimeHalfDensityAmplitude_norm_sq p

/-- Explicit finite Hermitian autocorrelation of the same source orbit. -/
def finiteEulerPrimeAutocorrelation (F : Finset Nat.Primes) (t : ℝ) : ℂ :=
  ∑ p : F, (starRingEnd ℂ) (finiteEulerPrimeVector F p) * finiteEulerPrimeOrbit F t p

theorem star_eulerPrimeHalfDensityAmplitude_mul_self (p : Nat.Primes) :
    (starRingEnd ℂ) (eulerPrimeHalfDensityAmplitude p) *
        eulerPrimeHalfDensityAmplitude p =
      ((Real.log ((p : ℕ) : ℝ) ^ 2 / ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [Complex.conj_mul']
  exact_mod_cast eulerPrimeHalfDensityAmplitude_norm_sq p

/-- The autocorrelation retains every discrete prime-log frequency, unlike its value at zero. -/
theorem finiteEulerPrimeAutocorrelation_eq
    (F : Finset Nat.Primes) (t : ℝ) :
    finiteEulerPrimeAutocorrelation F t =
      ∑ p : F,
        ((Real.log ((p : Nat.Primes) : ℝ) ^ 2 /
          ((p : Nat.Primes) : ℝ) : ℝ) : ℂ) *
          expChar (-Real.log ((p : Nat.Primes) : ℕ)) t := by
  rw [finiteEulerPrimeAutocorrelation]
  apply Finset.sum_congr rfl
  intro p _
  rw [finiteEulerPrimeOrbit, finiteDiagonalPhaseOrbit]
  calc
    (starRingEnd ℂ) (finiteEulerPrimeVector F p) *
        (finiteEulerPrimeVector F p *
          expChar (-Real.log ((p : Nat.Primes) : ℕ)) t) =
      ((starRingEnd ℂ) (finiteEulerPrimeVector F p) *
        finiteEulerPrimeVector F p) *
          expChar (-Real.log ((p : Nat.Primes) : ℕ)) t := by ring_nf
    _ = ((Real.log ((p : Nat.Primes) : ℝ) ^ 2 /
          ((p : Nat.Primes) : ℝ) : ℝ) : ℂ) *
          expChar (-Real.log ((p : Nat.Primes) : ℕ)) t := by
      rw [finiteEulerPrimeVector,
        star_eulerPrimeHalfDensityAmplitude_mul_self]

/-- Prime `sigma`-amplitude squared, the cofinal Hilbert mass density. -/
def eulerPrimeCofinalMass (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-2 * sigma)

theorem eulerPrimeCofinalMass_nonneg (sigma : ℝ) (p : Nat.Primes) :
    0 ≤ eulerPrimeCofinalMass sigma p := by
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)

/-- The cofinal mass is exactly the squared norm of the source amplitude. -/
theorem eulerPrimeSigmaAmplitude_norm_sq (sigma : ℝ) (p : Nat.Primes) :
    ‖eulerPrimeSigmaAmplitude sigma p‖ ^ 2 = eulerPrimeCofinalMass sigma p := by
  have hp0 : 0 ≤ ((p : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).le
  rw [eulerPrimeSigmaAmplitude, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hlog (Real.rpow_nonneg hp0 _)), mul_pow,
    ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-sigma)) 2,
    ← Real.rpow_mul hp0]
  rw [eulerPrimeCofinalMass]
  congr 1
  ring_nf

/-- Sharp prime Hilbert wall: `log p * p^{-sigma}` is square-summable exactly for `sigma > 1/2`. -/
theorem summable_eulerPrimeCofinalMass_iff (sigma : ℝ) :
    Summable (eulerPrimeCofinalMass sigma) ↔ 1 / 2 < sigma := by
  constructor
  · intro hsum
    by_contra hsigma
    have hsigma' : sigma ≤ 1 / 2 := le_of_not_gt hsigma
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hscaled : Summable (fun p : Nat.Primes =>
        Real.log 2 ^ 2 * (1 / ((p : ℕ) : ℝ))) := by
      apply Summable.of_nonneg_of_le
      · intro p
        positivity
      · intro p
        have hp0 : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
        have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
        have hp1 : 1 ≤ ((p : ℕ) : ℝ) := by linarith
        have hlogle : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) :=
          Real.strictMonoOn_log.monotoneOn (by norm_num) hp0 hp2
        have hlogpow : Real.log 2 ^ 2 ≤ Real.log ((p : ℕ) : ℝ) ^ 2 :=
          pow_le_pow_left₀ hlog2pos.le hlogle 2
        have hrpow : ((p : ℕ) : ℝ) ^ (-1 : ℝ) ≤
            ((p : ℕ) : ℝ) ^ (-2 * sigma) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        calc
          Real.log 2 ^ 2 * (1 / ((p : ℕ) : ℝ)) =
              Real.log 2 ^ 2 * ((p : ℕ) : ℝ) ^ (-1 : ℝ) := by
                rw [Real.rpow_neg_one, one_div]
          _ ≤ Real.log ((p : ℕ) : ℝ) ^ 2 *
              ((p : ℕ) : ℝ) ^ (-2 * sigma) :=
                mul_le_mul hlogpow hrpow (Real.rpow_nonneg hp0.le _)
                  (sq_nonneg _)
          _ = eulerPrimeCofinalMass sigma p := rfl
      · exact hsum
    have hharmonic : Summable (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ)) :=
      (summable_mul_left_iff (pow_ne_zero 2 hlog2pos.ne')).mp hscaled
    exact Nat.Primes.not_summable_one_div hharmonic
  · intro hsigma
    have hnat := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg
      2 (2 * sigma) (by linarith)
    have hprime := hnat.comp_injective
      (i := fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective
    refine hprime.congr fun p => ?_
    have hlog : 0 < Real.log ((p : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast p.prop.one_lt)
    simp only [Function.comp_apply, eulerPrimeCofinalMass, abs_of_pos hlog]
    ring_nf

/-- Exact `ell^(2 : ℕ)` admission criterion for the actual complex prime-amplitude family. -/
theorem summable_normSq_eulerPrimeSigmaAmplitude_iff (sigma : ℝ) :
    Summable (fun p : Nat.Primes => ‖eulerPrimeSigmaAmplitude sigma p‖ ^ 2) ↔
      1 / 2 < sigma := by
  rw [show (fun p : Nat.Primes => ‖eulerPrimeSigmaAmplitude sigma p‖ ^ 2) =
      eulerPrimeCofinalMass sigma by
    funext p
    exact eulerPrimeSigmaAmplitude_norm_sq sigma p]
  exact summable_eulerPrimeCofinalMass_iff sigma

/-- The critical half-density source is absent from the standard prime `ell^(2 : ℕ)` completion. -/
theorem not_summable_eulerPrimeHalfDensityMass :
    ¬ Summable (eulerPrimeCofinalMass (1 / 2)) := by
  rw [summable_eulerPrimeCofinalMass_iff]
  norm_num

/-- The compatible half-density source sequence defines no vector in standard prime `ell^(2 : ℕ)`. -/
theorem not_summable_normSq_eulerPrimeHalfDensityAmplitude :
    ¬ Summable (fun p : Nat.Primes => ‖eulerPrimeHalfDensityAmplitude p‖ ^ 2) := by
  simpa only [eulerPrimeHalfDensityAmplitude] using
    (show ¬ Summable
      (fun p : Nat.Primes => ‖eulerPrimeSigmaAmplitude (1 / 2) p‖ ^ 2) by
        rw [summable_normSq_eulerPrimeSigmaAmplitude_iff]
        norm_num)

/-- In the critical strip both reflected source vectors fail simultaneously only at half density. -/
theorem reflected_eulerPrimeCofinalMass_both_not_summable_iff
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    (¬ Summable (eulerPrimeCofinalMass sigma) ∧
      ¬ Summable (eulerPrimeCofinalMass (1 - sigma))) ↔
        sigma = 1 / 2 := by
  rw [not_congr (summable_eulerPrimeCofinalMass_iff sigma),
    not_congr (summable_eulerPrimeCofinalMass_iff (1 - sigma))]
  constructor
  · rintro ⟨hleft, hright⟩
    push Not at hleft hright
    linarith
  · rintro rfl
    norm_num

/-- One theorem packages all six exact shadows of the same finite prime source family. -/
theorem eulerPrimeOrbit_fourOrgan_law
    (F : Finset Nat.Primes) (hF : F.Nonempty) :
    (∀ k : Fin (Fintype.card F),
      finiteEulerPrimeKrylovBasis F k =
        ((finiteEulerPrimeGenerator F : (F → ℂ) → (F → ℂ))^[(k : ℕ)])
          (finiteEulerPrimeVector F)) ∧
    (∀ theta : F → ℝ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ t : ℝ, ∀ p : F,
        ‖finiteEulerPrimeOrbit F t p - finiteEulerPrimeVector F p *
          Complex.exp ((theta p : ℝ) * Complex.I)‖ <
            ‖finiteEulerPrimeVector F p‖ * epsilon) ∧
    (∀ t : ℝ,
      finiteDiagonalEnergy (finiteEulerPrimeOrbit F t) = finiteEulerPrimePolarEnergy F) ∧
    (∀ R : ℝ, ∃ t : ℝ,
      R < finitePhaseLiftEnergy
        (fun p : F => Real.log ((p : Nat.Primes) : ℕ)) t) ∧
    ¬ Summable (eulerPrimeCofinalMass (1 / 2)) := by
  exact ⟨finiteEulerPrimeKrylovBasis_apply F,
    fun theta epsilon hepsilon => finiteEulerPrimeOrbit_approx F theta hepsilon,
    finiteEulerPrimeOrbit_polarEnergy F,
    finiteEulerPrimePhaseLiftEnergy_unbounded F hF,
    not_summable_eulerPrimeHalfDensityMass⟩

end

end GaloisForLFunctions.HTGeometry
