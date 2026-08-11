import GaloisForLFunctions.HTGeometry.OrbitMarkerSourceFaceReconstruction
import GaloisForLFunctions.HTGeometry.PrincipalPartDifferentialOperator
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier

/-!
# Relative orbit leakage of the Route-T Wold pole

The four-shift Wold divisor is a cubic translation coboundary.  Its first pole in the physical
half-strip is therefore not an absolute orbit class: the other three shifts carry the opposite
orbit residue outside that strip.  This file proves the exact relative law.

After functional-equation/Schwarz reflection, the physical first-shift poles occur at
`rho - 1` and `-conj rho`.  Their anti-reflected pair is a finite shift-two coboundary exactly
when `Re rho = 1/2`.  Consequently a source proof cannot use global exactness of the cubic Wold
chain alone.  It must prove that no compensating principal part crosses the physical boundary.

This is an unconditional classification of the Route-T noncancellation obstruction, not an RH
proof or an assumed continuation theorem.
-/

open Complex Filter Topology

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Quadratic primitive whose translation boundary is the cubic Wold pole chain. -/
def xiHeatCassiniWoldCubicPolePrimitive
    (q x : ℂ) (c : ℕ →₀ ℂ) : ℂ →₀ (ℕ →₀ ℂ) :=
  -finiteOrbitCoboundary (-q)
    (finiteOrbitCoboundary (-q) (Finsupp.single x c))

/-- Formal four-shift principal-part chain of one Wold divisor pole. -/
def xiHeatCassiniWoldCubicPoleChain
    (q x : ℂ) (c : ℕ →₀ ℂ) : ℂ →₀ (ℕ →₀ ℂ) :=
  finiteOrbitCoboundary (-q) (xiHeatCassiniWoldCubicPolePrimitive q x c)

/-- The formal cubic Wold chain has coefficients `1,-3,3,-1` on four consecutive shifts. -/
theorem xiHeatCassiniWoldCubicPoleChain_eq_fourShift
    (q x : ℂ) (c : ℕ →₀ ℂ) :
    xiHeatCassiniWoldCubicPoleChain q x c =
      Finsupp.single x c -
        3 • Finsupp.single (x - q) c +
        3 • Finsupp.single (x - 2 * q) c -
        Finsupp.single (x - 3 * q) c := by
  rw [xiHeatCassiniWoldCubicPoleChain,
    xiHeatCassiniWoldCubicPolePrimitive]
  simp only [finiteOrbitCoboundary, translateFiniteSupport, neg_eq_zero_sub,
    Finsupp.mapDomain_sub, Finsupp.mapDomain_zero, Finsupp.mapDomain_single]
  ring_nf
  abel

/-- Globally, the complete cubic Wold chain has zero orbit residue. -/
theorem orbitResidueVector_xiHeatCassiniWoldCubicPoleChain_eq_zero
    (q x : ℂ) (c : ℕ →₀ ℂ) :
    orbitResidueVector (-q) (xiHeatCassiniWoldCubicPoleChain q x c) = 0 := by
  exact orbitResidueVector_finiteOrbitCoboundary _ _

/-- **Relative single-pole leakage law.**  Any finite translation-coboundary completion of one
visible pole must put its opposite orbit residue in the compensator. -/
theorem relativePoleHead_completion_orbitLeakage
    (q x : ℂ) (c : ℕ →₀ ℂ)
    (R E : ℂ →₀ (ℕ →₀ ℂ))
    (h : Finsupp.single x c + R = finiteOrbitCoboundary q E) :
    orbitResidueVector q R =
      -Finsupp.single (x : ℂ ⧸ AddSubgroup.zmultiples q) c := by
  have hv := congrArg (orbitResidueVector q) h
  rw [orbitResidueVector_finiteOrbitCoboundary] at hv
  simp only [orbitResidueVector, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single] at hv
  calc
    Finsupp.mapDomain (fun y : ℂ =>
        (y : ℂ ⧸ AddSubgroup.zmultiples q)) R =
        0 - Finsupp.single (x : ℂ ⧸ AddSubgroup.zmultiples q) c := by
          rw [← hv]
          abel
    _ = -Finsupp.single (x : ℂ ⧸ AddSubgroup.zmultiples q) c := by
      ext y k
      simp

/-- The three discarded Wold shifts carry exactly the negative orbit residue of the physical
first-shift pole. -/
theorem orbitResidueVector_xiHeatCassiniWoldCubicPoleTail
    (q x : ℂ) (c : ℕ →₀ ℂ) :
    orbitResidueVector (-q)
        (xiHeatCassiniWoldCubicPoleChain q x c - Finsupp.single x c) =
      -Finsupp.single
        (x : ℂ ⧸ AddSubgroup.zmultiples (-q)) c := by
  apply relativePoleHead_completion_orbitLeakage (-q) x c
    (xiHeatCassiniWoldCubicPoleChain q x c - Finsupp.single x c)
    (xiHeatCassiniWoldCubicPolePrimitive q x c)
  rw [← xiHeatCassiniWoldCubicPoleChain]
  abel

/-- **Relative pole-pair leakage law.**  Completing an anti-reflected pair by a translation
coboundary forces its entire opposite quotient-orbit vector into the compensator. -/
theorem relativePolePair_completion_orbitLeakage
    (q x y : ℂ) (c : ℕ →₀ ℂ)
    (R E : ℂ →₀ (ℕ →₀ ℂ))
    (h : (Finsupp.single x c - Finsupp.single y c) + R =
      finiteOrbitCoboundary q E) :
    orbitResidueVector q R =
      -(Finsupp.single (x : ℂ ⧸ AddSubgroup.zmultiples q) c -
        Finsupp.single (y : ℂ ⧸ AddSubgroup.zmultiples q) c) := by
  have hv := congrArg (orbitResidueVector q) h
  rw [orbitResidueVector_finiteOrbitCoboundary] at hv
  simp only [orbitResidueVector, Finsupp.mapDomain_add,
    Finsupp.mapDomain_sub, Finsupp.mapDomain_single] at hv
  calc
    Finsupp.mapDomain (fun z : ℂ =>
        (z : ℂ ⧸ AddSubgroup.zmultiples q)) R =
        0 - (Finsupp.single (x : ℂ ⧸ AddSubgroup.zmultiples q) c -
          Finsupp.single (y : ℂ ⧸ AddSubgroup.zmultiples q) c) := by
            rw [← hv]
            abel
    _ = -(Finsupp.single (x : ℂ ⧸ AddSubgroup.zmultiples q) c -
          Finsupp.single (y : ℂ ⧸ AddSubgroup.zmultiples q) c) := by
      ext z k
      simp

/-- Adjacent polarization of the cubic chain is automatically a step-two coboundary.  This
global exactness retains all compensating shifts and therefore does not imply physical
noncancellation. -/
theorem xiHeatCassiniWoldCubicPoleChain_shiftTwoPolarization
    (q x : ℂ) (c : ℕ →₀ ℂ) :
    translateFiniteSupport (-q) (xiHeatCassiniWoldCubicPoleChain q x c) +
        xiHeatCassiniWoldCubicPoleChain q x c =
      finiteOrbitCoboundary ((-q) + (-q))
        (xiHeatCassiniWoldCubicPolePrimitive q x c) := by
  rw [xiHeatCassiniWoldCubicPoleChain,
    finiteOrbitCoboundary, finiteOrbitCoboundary]
  simp only [translateFiniteSupport, Finsupp.mapDomain_sub,
    ← Finsupp.mapDomain_comp]
  change
    (Finsupp.mapDomain (fun y : ℂ => y + (-q) + (-q))
          (xiHeatCassiniWoldCubicPolePrimitive q x c) -
        Finsupp.mapDomain (fun y : ℂ => y + (-q))
          (xiHeatCassiniWoldCubicPolePrimitive q x c)) +
      (Finsupp.mapDomain (fun y : ℂ => y + (-q))
          (xiHeatCassiniWoldCubicPolePrimitive q x c) -
        xiHeatCassiniWoldCubicPolePrimitive q x c) =
    Finsupp.mapDomain (fun y : ℂ => y + ((-q) + (-q)))
        (xiHeatCassiniWoldCubicPolePrimitive q x c) -
      xiHeatCassiniWoldCubicPolePrimitive q x c
  have hmap :
      Finsupp.mapDomain (fun y : ℂ => y + (-q) + (-q))
          (xiHeatCassiniWoldCubicPolePrimitive q x c) =
        Finsupp.mapDomain (fun y : ℂ => y + ((-q) + (-q)))
          (xiHeatCassiniWoldCubicPolePrimitive q x c) := by
    apply Finsupp.mapDomain_congr
    intro y _
    ring
  rw [hmap]
  abel

/-- A reflected Route-T first-shift pole pair can be a finite shift-two coboundary only on the
critical line. -/
theorem routeTReflectedWoldPolePair_re_eq_half_of_finiteShiftTwoCoboundary
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {L : Polynomial ℂ} (hL : L ≠ 0)
    {c : ℂ} (hc : c ≠ 0)
    (E : ℂ →₀ (ℕ →₀ ℂ))
    (hcob :
      simplePolePairDifferentialOperator L c
          (rho - 1) (-(starRingEnd ℂ rho)) =
        finiteOrbitCoboundary (2 : ℂ) E) :
    rho.re = 1 / 2 := by
  have horbit :
      ((rho - 1 : ℂ) : ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ)) =
        ((-(starRingEnd ℂ rho) : ℂ) :
          ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ)) := by
    by_contra hne
    exact (simplePolePairDifferentialOperator_ne_finiteOrbitCoboundary
      (2 : ℂ) (rho - 1) (-(starRingEnd ℂ rho)) hL hc hne E) hcob
  rw [QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_zmultiples_iff] at horbit
  rcases horbit with ⟨n, hn⟩
  have hnre : 2 * (n : ℝ) = 2 * rho.re - 1 := by
    have hre := congrArg Complex.re hn
    norm_num at hre
    linarith
  have hnlowR : (-1 : ℝ) < (n : ℝ) := by
    linarith [hstrip.1]
  have hnhighR : (n : ℝ) < 1 := by
    linarith [hstrip.2]
  have hnlow : (-1 : ℤ) < n := by exact_mod_cast hnlowR
  have hnhigh : n < (1 : ℤ) := by exact_mod_cast hnhighR
  have hn0 : n = 0 := by omega
  subst n
  norm_num at hnre
  linarith

/-- Applying the constant differential operator `1` to a simple pole retains only its residue. -/
theorem simplePoleDifferentialOperator_one_eq_single (c : ℂ) :
    simplePoleDifferentialOperator (1 : Polynomial ℂ) c =
      Finsupp.single 1 c := by
  rw [show (1 : Polynomial ℂ) = Polynomial.monomial 0 1 by simp]
  rw [simplePoleDifferentialOperator, Polynomial.sum_monomial_index]
  · simp
  · simp

/-- Formal complete four-shift chain attached to a zeta zero of multiplicity `m`. -/
def xiHeatCassiniWoldFormalPoleChain
    (rho : ℂ) (m : ℕ) : ℂ →₀ (ℕ →₀ ℂ) :=
  xiHeatCassiniWoldCubicPoleChain 1 (rho - 1)
    (simplePoleDifferentialOperator 1 (-(m : ℂ)))

/-- Exact locations and residues of the four formal Wold shifts. -/
theorem xiHeatCassiniWoldFormalPoleChain_eq_fourShift
    (rho : ℂ) (m : ℕ) :
    xiHeatCassiniWoldFormalPoleChain rho m =
      Finsupp.single (rho - 1) (Finsupp.single 1 (-(m : ℂ))) -
        3 • Finsupp.single (rho - 2) (Finsupp.single 1 (-(m : ℂ))) +
        3 • Finsupp.single (rho - 3) (Finsupp.single 1 (-(m : ℂ))) -
        Finsupp.single (rho - 4) (Finsupp.single 1 (-(m : ℂ))) := by
  rw [xiHeatCassiniWoldFormalPoleChain,
    xiHeatCassiniWoldCubicPoleChain_eq_fourShift,
    simplePoleDifferentialOperator_one_eq_single]
  ring_nf

/-- Anti-reflected pair of physical first-shift Wold poles. -/
def xiHeatCassiniReflectedWoldPhysicalPoleHead
    (rho : ℂ) (m : ℕ) : ℂ →₀ (ℕ →₀ ℂ) :=
  simplePolePairDifferentialOperator 1 (-(m : ℂ))
    (rho - 1) (-(starRingEnd ℂ rho))

theorem xiHeatCassiniReflectedWoldPhysicalPoleHead_re_eq_half_of_coboundary
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {m : ℕ} (hm : 1 ≤ m) (E : ℂ →₀ (ℕ →₀ ℂ))
    (h : xiHeatCassiniReflectedWoldPhysicalPoleHead rho m =
      finiteOrbitCoboundary (2 : ℂ) E) :
    rho.re = 1 / 2 := by
  apply routeTReflectedWoldPolePair_re_eq_half_of_finiteShiftTwoCoboundary
    hstrip one_ne_zero (neg_ne_zero.mpr ?_) E h
  exact_mod_cast (Nat.ne_zero_of_lt hm)

theorem xiHeatCassiniReflectedWoldPhysicalPoleHead_eq_zero_of_re_eq_half
    {rho : ℂ} (hhalf : rho.re = 1 / 2) (m : ℕ) :
    xiHeatCassiniReflectedWoldPhysicalPoleHead rho m = 0 := by
  have hs : rho - 1 = -(starRingEnd ℂ rho) := by
    apply Complex.ext
    · simp
      linarith
    · simp
  rw [xiHeatCassiniReflectedWoldPhysicalPoleHead, hs]
  simp [simplePolePairDifferentialOperator]

/-- **Native Route-T orbit criterion.**  For a genuine pole multiplicity, the anti-reflected
physical Wold head is a finite completed shift-two coboundary exactly on the critical line. -/
theorem xiHeatCassiniReflectedWoldPhysicalPoleHead_coboundary_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    (∃ E : ℂ →₀ (ℕ →₀ ℂ),
      xiHeatCassiniReflectedWoldPhysicalPoleHead rho m =
        finiteOrbitCoboundary (2 : ℂ) E) ↔
      rho.re = 1 / 2 := by
  constructor
  · rintro ⟨E, hE⟩
    exact xiHeatCassiniReflectedWoldPhysicalPoleHead_re_eq_half_of_coboundary
      hstrip hm E hE
  · intro hhalf
    refine ⟨0, ?_⟩
    rw [xiHeatCassiniReflectedWoldPhysicalPoleHead_eq_zero_of_re_eq_half
      hhalf]
    simp [finiteOrbitCoboundary, translateFiniteSupport]

/-- **Analytic/formal relative-leakage package.**  Every off-critical zeta zero supplies the
already-proved analytic Wold residue `-m`.  Its complete four-shift formal divisor is globally
exact, while deleting the physical head leaves precisely its negative orbit residue in the tail. -/
theorem xiHeatCassiniWoldPole_relativeOrbitLeakage
    {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) * xiHeatCassiniWoldLaplaceContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) ∧
      orbitResidueVector (-(1 : ℂ))
          (xiHeatCassiniWoldFormalPoleChain rho m) = 0 ∧
      orbitResidueVector (-(1 : ℂ))
          (xiHeatCassiniWoldFormalPoleChain rho m -
            Finsupp.single (rho - 1) (Finsupp.single 1 (-(m : ℂ)))) =
        -Finsupp.single
          ((rho - 1 : ℂ) :
            ℂ ⧸ AddSubgroup.zmultiples (-(1 : ℂ)))
          (Finsupp.single 1 (-(m : ℂ))) := by
  obtain ⟨m, hm, hres⟩ :=
    xiHeatCassiniWoldLaplaceContinuation_zero_residue hrho hzeta
  refine ⟨m, hm, hres, ?_, ?_⟩
  · exact orbitResidueVector_xiHeatCassiniWoldCubicPoleChain_eq_zero
      1 (rho - 1) (simplePoleDifferentialOperator 1 (-(m : ℂ)))
  · simpa [xiHeatCassiniWoldFormalPoleChain,
      simplePoleDifferentialOperator_one_eq_single] using
      orbitResidueVector_xiHeatCassiniWoldCubicPoleTail
        1 (rho - 1) (simplePoleDifferentialOperator 1 (-(m : ℂ)))

end

end RHTower
