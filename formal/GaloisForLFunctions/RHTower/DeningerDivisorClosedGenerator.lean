import GaloisForLFunctions.RHTower.DeningerClosedOperatorPolarization
import GaloisForLFunctions.RHTower.DeningerDivisorFlow
import GaloisForLFunctions.RHTower.XiDivisorHilbertCarrier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# Closed divisor generator for Deninger's arithmetic flow

The algebraic divisor flow has unbounded eigenvalues, so its Hilbert completion cannot use a
bounded `Module.End`. This file constructs the correct maximal diagonal `LinearPMap` on
`XiDivisorL2`:

`Dom(Theta) = {a in ell² | (rho_q a_q)_q in ell²}`.

Lean proves that this domain is dense, the operator is closed, and every canonical coordinate
vector is an eigenvector with the corresponding Xi zero. This supplies the topological
closed-operator target requested in Deninger's program.

The construction is still divisor-indexed. It is not the missing prime-geometric source
cohomology and supplies no positive Hodge star.
-/

noncomputable section

open HilbertSchmidt

namespace RHTower

/-- Maximal `ell²` domain of the unbounded divisor multiplication operator. -/
def deningerDivisorThetaDomain : Submodule ℂ XiDivisorL2 where
  carrier := {a | Memℓp
    (fun q : XiZeroCopy => deningerDivisorThetaEigen q * a q) 2}
  zero_mem' := by
    change Memℓp
      (fun q : XiZeroCopy => deningerDivisorThetaEigen q * (0 : XiDivisorL2) q) 2
    rw [show (fun q : XiZeroCopy =>
        deningerDivisorThetaEigen q * (0 : XiDivisorL2) q) =
        fun _ : XiZeroCopy => (0 : ℂ) by
      funext q
      change deningerDivisorThetaEigen q * 0 = 0
      ring]
    exact zero_memℓp
  add_mem' := by
    intro a b ha hb
    change Memℓp
      (fun q : XiZeroCopy => deningerDivisorThetaEigen q * (a + b) q) 2
    rw [show (fun q : XiZeroCopy =>
        deningerDivisorThetaEigen q * (a + b) q) =
        (fun q => deningerDivisorThetaEigen q * a q) +
          fun q => deningerDivisorThetaEigen q * b q by
      funext q
      change deningerDivisorThetaEigen q * (a q + b q) =
        deningerDivisorThetaEigen q * a q +
          deningerDivisorThetaEigen q * b q
      ring]
    exact ha.add hb
  smul_mem' := by
    intro c a ha
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      ha.const_smul c

/-- Closed maximal diagonal realization of the arithmetic divisor generator. -/
def deningerDivisorClosedTheta : XiDivisorL2 →ₗ.[ℂ] XiDivisorL2 where
  domain := deningerDivisorThetaDomain
  toFun :=
    { toFun := fun a =>
        ⟨fun q => deningerDivisorThetaEigen q * (a : XiDivisorL2) q,
          a.property⟩
      map_add' := by
        intro a b
        ext q
        change deningerDivisorThetaEigen q *
            ((a : XiDivisorL2) q + (b : XiDivisorL2) q) =
          deningerDivisorThetaEigen q * (a : XiDivisorL2) q +
            deningerDivisorThetaEigen q * (b : XiDivisorL2) q
        ring
      map_smul' := by
        intro c a
        ext q
        simp [smul_eq_mul]
        ring }

@[simp]
theorem deningerDivisorClosedTheta_apply
    (a : deningerDivisorClosedTheta.domain) (q : XiZeroCopy) :
    deningerDivisorClosedTheta a q =
      deningerDivisorThetaEigen q * (a : XiDivisorL2) q :=
  rfl

/-- Coordinate graph defect for the diagonal closed operator. -/
def deningerDivisorThetaGraphDefect (q : XiZeroCopy) :
    (XiDivisorL2 × XiDivisorL2) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q).comp
      (ContinuousLinearMap.snd ℂ XiDivisorL2 XiDivisorL2) -
    deningerDivisorThetaEigen q •
      (lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q).comp
        (ContinuousLinearMap.fst ℂ XiDivisorL2 XiDivisorL2)

theorem deningerDivisorClosedTheta_graph_eq :
    deningerDivisorClosedTheta.graph =
      ⨅ q : XiZeroCopy, (deningerDivisorThetaGraphDefect q).ker := by
  ext p
  constructor
  · intro hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨a, ha, hout⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro q
    change p.2 q - deningerDivisorThetaEigen q * p.1 q = 0
    rw [← ha, ← hout]
    simp
  · intro hp
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hp
    have hcoord : ∀ q : XiZeroCopy,
        p.2 q = deningerDivisorThetaEigen q * p.1 q := by
      intro q
      have hq := hp q
      change p.2 q - deningerDivisorThetaEigen q * p.1 q = 0 at hq
      exact sub_eq_zero.mp hq
    have hdom : p.1 ∈ deningerDivisorThetaDomain := by
      change Memℓp
        (fun q : XiZeroCopy => deningerDivisorThetaEigen q * p.1 q) 2
      rw [show (fun q : XiZeroCopy =>
          deningerDivisorThetaEigen q * p.1 q) = fun q => p.2 q by
        funext q
        exact (hcoord q).symm]
      exact lp.memℓp p.2
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨p.1, hdom⟩, rfl, ?_⟩
    ext q
    exact (hcoord q).symm

/-- The maximal divisor multiplication operator is closed. -/
theorem deningerDivisorClosedTheta_isClosed :
    deningerDivisorClosedTheta.IsClosed := by
  rw [LinearPMap.IsClosed, deningerDivisorClosedTheta_graph_eq]
  change IsClosed
    ((↑(⨅ q : XiZeroCopy, (deningerDivisorThetaGraphDefect q).ker) :
      Set (XiDivisorL2 × XiDivisorL2)))
  rw [show
      ((↑(⨅ q : XiZeroCopy, (deningerDivisorThetaGraphDefect q).ker) :
        Set (XiDivisorL2 × XiDivisorL2))) =
        ⋂ q : XiZeroCopy,
          ((deningerDivisorThetaGraphDefect q).ker :
            Set (XiDivisorL2 × XiDivisorL2)) by
    ext p
    simp]
  exact isClosed_iInter fun q =>
    (deningerDivisorThetaGraphDefect q).isClosed_ker

/-- Every canonical `ell²` coordinate vector belongs to the maximal domain. -/
theorem lpBasis_mem_deningerDivisorThetaDomain (q : XiZeroCopy) :
    lpBasis XiZeroCopy q ∈ deningerDivisorThetaDomain := by
  let y : XiDivisorL2 :=
    deningerDivisorThetaEigen q • lpBasis XiZeroCopy q
  change Memℓp
    (fun r : XiZeroCopy =>
      deningerDivisorThetaEigen r * (lpBasis XiZeroCopy q) r) 2
  rw [show (fun r : XiZeroCopy =>
      deningerDivisorThetaEigen r * (lpBasis XiZeroCopy q) r) =
      fun r => y r by
    funext r
    classical
    by_cases hr : r = q
    · subst r
      simp [y, lpBasis_apply, smul_eq_mul]
    · simp [y, lpBasis_apply, hr, smul_eq_mul]]
  exact lp.memℓp y

/-- The maximal diagonal generator has dense domain. -/
theorem deningerDivisorClosedTheta_dense :
    Dense (deningerDivisorClosedTheta.domain : Set XiDivisorL2) := by
  have hbasisDense :
      Dense (Submodule.span ℂ (Set.range (lpBasis XiZeroCopy)) :
        Set XiDivisorL2) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (lpBasis XiZeroCopy).dense_span
  have hle :
      Submodule.span ℂ (Set.range (lpBasis XiZeroCopy)) ≤
        deningerDivisorClosedTheta.domain := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, rfl⟩
    exact lpBasis_mem_deningerDivisorThetaDomain q
  exact hbasisDense.mono hle

/-- Canonical coordinate vector as an element of the closed generator domain. -/
def deningerDivisorClosedThetaEigenvector (q : XiZeroCopy) :
    deningerDivisorClosedTheta.domain :=
  ⟨lpBasis XiZeroCopy q, lpBasis_mem_deningerDivisorThetaDomain q⟩

/-- Every divisor copy is a genuine eigenvector of the closed generator. -/
theorem deningerDivisorClosedTheta_eigenvector (q : XiZeroCopy) :
    deningerDivisorClosedTheta (deningerDivisorClosedThetaEigenvector q) =
      deningerDivisorThetaEigen q •
        (deningerDivisorClosedThetaEigenvector q : XiDivisorL2) := by
  ext r
  classical
  by_cases hr : r = q
  · subst r
    simp [deningerDivisorClosedThetaEigenvector, lpBasis_apply, smul_eq_mul]
  · simp [deningerDivisorClosedThetaEigenvector, lpBasis_apply, hr, smul_eq_mul]

end RHTower
