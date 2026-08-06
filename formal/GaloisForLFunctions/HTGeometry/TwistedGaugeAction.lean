import GaloisForLFunctions.HTGeometry.TwistedSourceBoundary

/-!
# The gauge action on an affine source local system

A base-valued invertible matrix acts on an affine source local system: the observables are
transformed by the matrix, the increments by its source translate, and the adjoint linear part by
the twisted conjugation `M ↦ τ_i(P) M Q`.  This is the gauge groupoid of the local system, and the
flat case of the previous module is the orbit of the identity.

Two consequences are recorded.  A gauge solving the cocycle equation carries the local system to
the identity, which is the flattening theorem again.  A gauge carrying the local system to a
diagonal one splits the affine family into scalar affine families, one per diagonal entry: for a
diagonalizable adjoint local system the curved rank problem reduces to the rank-one twisted
problem.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K L : Type u} [Field C] [Field K] [Field L]
  [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L]
  {I : Type u} (tau : I → K ≃+* K) (sigma : I → L ≃+* L)

variable {κ : Type u} [Fintype κ]

/-- The gauge action on the adjoint linear part: twisted conjugation `τ_i(P) M_i Q`. -/
def gaugeLinearPart (P Q : κ → κ → K) (M : I → κ → κ → K) (i : I) (p q : κ) : K :=
  ∑ r, ∑ s, tau i (P p r) * M i r s * Q s q

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
/-- **The gauge action on an affine source local system.**  The gauge transform of an affine
family is again affine, with linear part the twisted conjugate and increment the source translate
of the old increment. -/
theorem gauge_shift_general [DecidableEq κ] {z : κ → L} {M : I → κ → κ → K} {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0)
    (i : I) (p : κ) :
    sigma i (gaugeFamily P z p)
      = (∑ q, algebraMap K L (gaugeLinearPart tau P Q M i p q) * gaugeFamily P z q)
        + algebraMap K L (gaugeIncrement tau P om i p) := by
  classical
  have hexpand : sigma i (gaugeFamily P z p)
      = ∑ q, algebraMap K L (tau i (P p q)) *
          ((∑ r, algebraMap K L (M i q r) * z r) + algebraMap K L (om i q)) := by
    rw [gaugeFamily, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, hcomp, hshift i q]
  have hsplit : ∀ q : κ, algebraMap K L (tau i (P p q)) *
        ((∑ r, algebraMap K L (M i q r) * z r) + algebraMap K L (om i q))
      = (∑ r, algebraMap K L (tau i (P p q) * M i q r) * z r)
        + algebraMap K L (tau i (P p q) * om i q) := by
    intro q
    rw [mul_add, Finset.mul_sum, map_mul]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun r _ => ?_) rfl
    rw [map_mul, mul_assoc]
  rw [hexpand, Finset.sum_congr rfl fun q _ => hsplit q, Finset.sum_add_distrib]
  have hinc : (∑ q, algebraMap K L (tau i (P p q) * om i q))
      = algebraMap K L (gaugeIncrement tau P om i p) := by
    rw [gaugeIncrement, map_sum]
  refine congrArg₂ (· + ·) ?_ hinc
  set A : κ → K := fun r => ∑ q, tau i (P p q) * M i q r with hA
  have hstep1 : (∑ q, ∑ r, algebraMap K L (tau i (P p q) * M i q r) * z r)
      = ∑ r, algebraMap K L (A r) * z r := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hA, map_sum, Finset.sum_mul]
  have hterm : ∀ r : κ, algebraMap K L (A r) * z r
      = ∑ s, algebraMap K L (A r * Q r s) * gaugeFamily P z s := by
    intro r
    rw [eq_gauge_combination hinv z r, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_mul, mul_assoc]
  have hstep2 : (∑ r, algebraMap K L (A r) * z r)
      = ∑ s, algebraMap K L (∑ r, A r * Q r s) * gaugeFamily P z s := by
    rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sum, Finset.sum_mul]
  have hmatch : ∀ s : κ, (∑ r, A r * Q r s) = gaugeLinearPart tau P Q M i p s := by
    intro s
    rw [gaugeLinearPart, hA]
    rw [Finset.sum_congr rfl fun r _ => Finset.sum_mul Finset.univ
      (fun q => tau i (P p q) * M i q r) (Q r s)]
    rw [Finset.sum_comm]
  rw [hstep1, hstep2]
  exact Finset.sum_congr rfl fun s _ => by rw [hmatch s]

/-! ### The flattening cocycle is the gauge orbit of the identity -/

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
/-- A gauge solving the cocycle equation carries the adjoint local system to the identity. -/
theorem gaugeLinearPart_eq_one_of_cocycle [DecidableEq κ] {M : I → κ → κ → K} {P Q : κ → κ → K}
    (hPQ : ∀ p q, (∑ s, P p s * Q s q) = if p = q then 1 else 0)
    (hcocycle : ∀ i p q, (∑ r, tau i (P p r) * M i r q) = P p q)
    (i : I) (p q : κ) :
    gaugeLinearPart tau P Q M i p q = if p = q then 1 else 0 := by
  classical
  have hstep : gaugeLinearPart tau P Q M i p q
      = ∑ s, (∑ r, tau i (P p r) * M i r s) * Q s q := by
    rw [gaugeLinearPart, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
  rw [hstep, Finset.sum_congr rfl fun s _ => by rw [hcocycle i p s], hPQ p q]

/-! ### Diagonal reduction -/

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
/-- **Diagonal reduction.**  If a gauge carries the adjoint local system to a diagonal one, every
gauged coordinate satisfies a scalar affine source law: the curved problem for a diagonalizable
adjoint local system is the rank-one twisted problem, one coordinate at a time. -/
theorem gauge_shift_scalar_of_diagonal [DecidableEq κ] {z : κ → L} {M : I → κ → κ → K}
    {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0)
    {m : I → κ → K}
    (hdiag : ∀ i p q, gaugeLinearPart tau P Q M i p q = if p = q then m i p else 0)
    (i : I) (p : κ) :
    sigma i (gaugeFamily P z p)
      = algebraMap K L (m i p) * gaugeFamily P z p
        + algebraMap K L (gaugeIncrement tau P om i p) := by
  classical
  rw [gauge_shift_general tau sigma hshift hcomp hinv i p]
  refine congrArg₂ (· + ·) ?_ rfl
  rw [Finset.sum_congr rfl fun q _ => by rw [hdiag i p q], Finset.sum_eq_single p]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb h.symm, map_zero, zero_mul]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
/-- **The flat case is the diagonal case with unit entries.**  A gauge solving the cocycle
equation gives the additive source law of the flat theory. -/
theorem gauge_shift_flat_of_cocycle [DecidableEq κ] {z : κ → L} {M : I → κ → κ → K}
    {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0)
    (hPQ : ∀ p q, (∑ s, P p s * Q s q) = if p = q then 1 else 0)
    (hcocycle : ∀ i p q, (∑ r, tau i (P p r) * M i r q) = P p q)
    (i : I) (p : κ) :
    sigma i (gaugeFamily P z p)
      = gaugeFamily P z p + algebraMap K L (gaugeIncrement tau P om i p) := by
  have h := gauge_shift_scalar_of_diagonal tau sigma hshift hcomp hinv
    (m := fun _ _ => (1 : K))
    (fun i p q => by
      rw [gaugeLinearPart_eq_one_of_cocycle tau hPQ hcocycle i p q]) i p
  rwa [map_one, one_mul] at h

end

end GaloisForLFunctions.HTGeometry
