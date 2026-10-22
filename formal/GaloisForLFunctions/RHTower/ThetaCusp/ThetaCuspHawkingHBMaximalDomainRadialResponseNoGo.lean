import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBCanonicalRadialGreenBoundedCoefficientFidelityNoGo
import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint

/-!
# Maximal-domain radial response is nonselective for HB

The canonical Birmingham--Mokhtari radial Green coefficients are unbounded, so the corpus rules
out their exact realization by a bounded operator.  This file closes the apparent unbounded
operator loophole at the level of abstract existence.

For every complex coefficient family `a` on every coordinate set, multiplication by `a` on its
maximal square-summability domain has a closed graph and dense domain.  Every coordinate vector
belongs to that domain, is an eigenvector, and recovers `a` as its diagonal matrix element.  The
construction applies to *every* requested target family, not only the canonical HB radial Green
weights.

Therefore existence of a closed, densely defined, coefficient-faithful unbounded response cannot
be the RH-bearing step in

`unbounded radial response existence` -> `two-leg Peierls incidence` ->
`radiative ++ extinction` -> `RH`.

The positive survivor is exact: a viable HB theorem must identify the graph and domain from the
literal Einstein--Teukolsky causal PDE and prove its independent source/left-QNM incidence.  Closed
maximal-domain operator theory plus coefficient fidelity alone imposes no arithmetic selection.

`[PROVED HERE] [LEAN-PROVED] [HB ROUTE-CLASS KILL] [UNIVERSAL REALIZATION]`
-/

open Complex Set
open scoped InnerProductSpace LinearPMap

namespace HTGeometry

noncomputable section

universe u

variable {ι : Type u}

/-- Maximal square-summability domain of an arbitrary complex diagonal family. -/
def maximalComplexDiagonalDomain (a : ι → ℂ) :
    Submodule ℂ (IndexedEllTwo ι) where
  carrier := {x | Memℓp (fun i => a i * x i) 2}
  zero_mem' := by
    change Memℓp (fun i => a i * (0 : IndexedEllTwo ι) i) 2
    rw [show (fun i => a i * (0 : IndexedEllTwo ι) i) =
        (0 : ι → ℂ) by
      funext i
      change a i * 0 = 0
      simp]
    exact zero_memℓp
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun i => a i * (x + y) i) 2
    rw [show (fun i => a i * (x + y) i) =
        (fun i => a i * x i) + fun i => a i * y i by
      funext i
      change a i * (x i + y i) = a i * x i + a i * y i
      ring]
    exact hx.add hy
  smul_mem' := by
    intro c x hx
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using!
      hx.const_smul c

/-- Coordinate multiplication by an arbitrary complex family on its maximal domain. -/
def maximalComplexDiagonal (a : ι → ℂ) :
    IndexedEllTwo ι →ₗ.[ℂ] IndexedEllTwo ι where
  domain := maximalComplexDiagonalDomain a
  toFun :=
    { toFun := fun x => ⟨fun i => a i * (x : IndexedEllTwo ι) i, x.property⟩
      map_add' := by
        intro x y
        ext i
        change a i * ((x : IndexedEllTwo ι) i + (y : IndexedEllTwo ι) i) =
          a i * (x : IndexedEllTwo ι) i + a i * (y : IndexedEllTwo ι) i
        ring
      map_smul' := by
        intro c x
        ext i
        change a i * (c * (x : IndexedEllTwo ι) i) =
          c * (a i * (x : IndexedEllTwo ι) i)
        ring }

@[simp] theorem maximalComplexDiagonal_apply
    (a : ι → ℂ) (x : (maximalComplexDiagonal a).domain) (i : ι) :
    maximalComplexDiagonal a x i = a i * (x : IndexedEllTwo ι) i :=
  rfl

/-- Coordinate defect whose common kernel is the graph of the maximal multiplier. -/
def maximalComplexDiagonalGraphDefect (a : ι → ℂ) (i : ι) :
    (IndexedEllTwo ι × IndexedEllTwo ι) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).comp
      (ContinuousLinearMap.snd ℂ (IndexedEllTwo ι) (IndexedEllTwo ι)) -
    a i • (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).comp
      (ContinuousLinearMap.fst ℂ (IndexedEllTwo ι) (IndexedEllTwo ι))

/-- Exact graph classification by continuous coordinate equations. -/
theorem maximalComplexDiagonal_graph_eq (a : ι → ℂ) :
    (maximalComplexDiagonal a).graph =
      ⨅ i : ι, (maximalComplexDiagonalGraphDefect a i).ker := by
  ext p
  constructor
  · intro hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨x, hx, hout⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro i
    change p.2 i - a i * p.1 i = 0
    rw [← hx, ← hout]
    simp
  · intro hp
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hp
    have hcoord : ∀ i : ι, p.2 i = a i * p.1 i := by
      intro i
      have hi := hp i
      change p.2 i - a i * p.1 i = 0 at hi
      exact sub_eq_zero.mp hi
    have hdom : p.1 ∈ maximalComplexDiagonalDomain a := by
      change Memℓp (fun i => a i * p.1 i) 2
      rw [show (fun i => a i * p.1 i) = fun i => p.2 i by
        funext i
        exact (hcoord i).symm]
      exact lp.memℓp p.2
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨p.1, hdom⟩, rfl, ?_⟩
    ext i
    exact (hcoord i).symm

/-- Arbitrary complex maximal diagonal multiplication is a closed operator. -/
theorem maximalComplexDiagonal_isClosed (a : ι → ℂ) :
    (maximalComplexDiagonal a).IsClosed := by
  rw [LinearPMap.IsClosed, maximalComplexDiagonal_graph_eq]
  change IsClosed
    ((↑(⨅ i : ι, (maximalComplexDiagonalGraphDefect a i).ker) :
      Set (IndexedEllTwo ι × IndexedEllTwo ι)))
  rw [show
      ((↑(⨅ i : ι, (maximalComplexDiagonalGraphDefect a i).ker) :
        Set (IndexedEllTwo ι × IndexedEllTwo ι))) =
        ⋂ i : ι, ((maximalComplexDiagonalGraphDefect a i).ker :
          Set (IndexedEllTwo ι × IndexedEllTwo ι)) by
    ext p
    simp]
  exact isClosed_iInter fun i =>
    (maximalComplexDiagonalGraphDefect a i).isClosed_ker

variable [DecidableEq ι]

/-- Every coordinate vector lies in the arbitrary complex maximal diagonal domain. -/
theorem ellTwoCoordinateBasis_mem_maximalComplexDiagonalDomain
    (a : ι → ℂ) (i : ι) :
    ellTwoCoordinateBasis ι i ∈ maximalComplexDiagonalDomain a := by
  let y : IndexedEllTwo ι := a i • ellTwoCoordinateBasis ι i
  change Memℓp (fun j => a j * (ellTwoCoordinateBasis ι i) j) 2
  rw [show (fun j => a j * (ellTwoCoordinateBasis ι i) j) =
      fun j => y j by
    funext j
    by_cases hji : j = i
    · subst j
      rfl
    · dsimp only [y]
      rw [ellTwoCoordinateBasis_apply]
      change a j * ((lp.single 2 i (1 : ℂ) : IndexedEllTwo ι) j) =
        a i * ((lp.single 2 i (1 : ℂ) : IndexedEllTwo ι) j)
      rw [lp.single_apply_ne _ _ _ hji]
      simp]
  exact lp.memℓp y

/-- The arbitrary complex maximal diagonal domain is dense. -/
theorem maximalComplexDiagonal_dense (a : ι → ℂ) :
    Dense ((maximalComplexDiagonal a).domain : Set (IndexedEllTwo ι)) := by
  have hbasis :
      Dense (Submodule.span ℂ (Set.range (ellTwoCoordinateBasis ι)) :
        Set (IndexedEllTwo ι)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (ellTwoCoordinateBasis ι).dense_span
  apply hbasis.mono
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact ellTwoCoordinateBasis_mem_maximalComplexDiagonalDomain a i

/-- Coordinate vector bundled with its maximal-domain proof. -/
def maximalComplexDiagonalEigenvector (a : ι → ℂ) (i : ι) :
    (maximalComplexDiagonal a).domain :=
  ⟨ellTwoCoordinateBasis ι i,
    ellTwoCoordinateBasis_mem_maximalComplexDiagonalDomain a i⟩

/-- Every coordinate vector is an eigenvector with the requested complex coefficient. -/
theorem maximalComplexDiagonal_eigenvector (a : ι → ℂ) (i : ι) :
    maximalComplexDiagonal a (maximalComplexDiagonalEigenvector a i) =
      a i • (maximalComplexDiagonalEigenvector a i : IndexedEllTwo ι) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [maximalComplexDiagonalEigenvector, ellTwoCoordinateBasis_apply]
  · simp [maximalComplexDiagonalEigenvector, ellTwoCoordinateBasis_apply, hji]

/-- Every requested complex coefficient is recovered as the corresponding matrix element. -/
theorem inner_ellTwoCoordinateBasis_maximalComplexDiagonal (a : ι → ℂ) (i : ι) :
    ⟪ellTwoCoordinateBasis ι i,
      maximalComplexDiagonal a (maximalComplexDiagonalEigenvector a i)⟫_ℂ = a i := by
  rw [ellTwoCoordinateBasis_apply,
    lp.inner_single_left (𝕜 := ℂ) (G := fun _ : ι => ℂ) i (1 : ℂ)]
  rw [maximalComplexDiagonal_apply]
  simp [maximalComplexDiagonalEigenvector, ellTwoCoordinateBasis_apply]

end

end HTGeometry

namespace RHTower

noncomputable section

/-- Closed, densely-defined diagonal realization of a requested Xi-copy coefficient profile. -/
def HBXiPeierlsClosedDenseDiagonalRealizable
    (target : XiZeroCopy → ℂ) : Prop :=
  ∃ K : HBXiPeierlsHilbertPacket →ₗ.[ℂ] HBXiPeierlsHilbertPacket,
    K.IsClosed ∧
      Dense (K.domain : Set HBXiPeierlsHilbertPacket) ∧
      ∀ q : XiZeroCopy,
        ∃ hq : HTGeometry.ellTwoCoordinateBasis XiZeroCopy q ∈ K.domain,
          ⟪HTGeometry.ellTwoCoordinateBasis XiZeroCopy q,
            K ⟨HTGeometry.ellTwoCoordinateBasis XiZeroCopy q, hq⟩⟫_ℂ = target q

/-- Universal target-fitting theorem: every complex profile has such a realization. -/
theorem hbXiPeierlsClosedDenseDiagonalRealizable
    (target : XiZeroCopy → ℂ) :
    HBXiPeierlsClosedDenseDiagonalRealizable target := by
  refine ⟨HTGeometry.maximalComplexDiagonal target,
    HTGeometry.maximalComplexDiagonal_isClosed target,
    HTGeometry.maximalComplexDiagonal_dense target, ?_⟩
  intro q
  let hq :=
    HTGeometry.ellTwoCoordinateBasis_mem_maximalComplexDiagonalDomain target q
  refine ⟨hq, ?_⟩
  exact HTGeometry.inner_ellTwoCoordinateBasis_maximalComplexDiagonal target q

/-- Specialization to the exact canonical BM radial Green-jump coefficients. -/
def HBXiPeierlsClosedDenseMaximalRadialCoefficientRealizable (n : ℕ) : Prop :=
  HBXiPeierlsClosedDenseDiagonalRealizable (hbXiPeierlsRadialWeight n)

/-- Every overtone's unbounded canonical radial coefficients have a closed dense exact model. -/
theorem hbXiPeierlsClosedDenseMaximalRadialCoefficientRealizable (n : ℕ) :
    HBXiPeierlsClosedDenseMaximalRadialCoefficientRealizable n := by
  exact hbXiPeierlsClosedDenseDiagonalRealizable (hbXiPeierlsRadialWeight n)

/-- Closed route class: abstract closed/dense/unbounded coefficient fidelity is universally
realizable and therefore cannot provide HB's missing source-selective Peierls incidence. -/
def D4HBUnboundedRadialCoefficientExistenceRouteKilled : Prop :=
  (∀ target : XiZeroCopy → ℂ,
    HBXiPeierlsClosedDenseDiagonalRealizable target) ∧
  ∀ n : ℕ, HBXiPeierlsClosedDenseMaximalRadialCoefficientRealizable n

/-- Premise-free certificate killing unbounded coefficient-faithful existence as an HB producer. -/
theorem d4HBUnboundedRadialCoefficientExistenceRouteKilled :
    D4HBUnboundedRadialCoefficientExistenceRouteKilled := by
  exact ⟨hbXiPeierlsClosedDenseDiagonalRealizable,
    hbXiPeierlsClosedDenseMaximalRadialCoefficientRealizable⟩

end

end RHTower
