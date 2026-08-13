import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalSourceResistance
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveCofinalSpread

/-!
# Terminal-source amplification and polarization

Terminal resistance is not merely a probability attached to a finite Gauss observation.  Along an
actual shifted-Xi root worldline it is exactly the normalized hard-root mobility.  Dually, its
reciprocal is the inertia of the already-formed vacuum-free mixed/completed `P^sharp` source.

For every finite positive block, the dimensionless terminal source at a current node satisfies

`resistance * dimensionless source = hard coordinate ^ 4`.

Sedrakyan--Cauchy therefore makes total dimensionless source dominate the square of total
hard-root quadratic energy.  After exact reciprocal-mass transport this dominates squared
projective Gauss-root spread.  Hence admission-probability escape cannot be source extinction.
After subtracting moving-apex vacuum, actual source action is a positive factor times minus the
centered reciprocal hard coordinate; bounded super-apex leakage therefore survives cofinal
compactification.  Remaining obstruction is degree-renewal accounting for these signed nodal
actions.
-/

open Complex Matrix MeasureTheory Polynomial Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Terminal source in the intrinsic hard chart, normalized by the preceding admitted norm. -/
def gaussDimensionlessHardEdgeTerminalSourceMass
    (y : ℝ) (s : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  y ^ 3 * xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
      (HTGeometry.monicOrtho s (m + 1)) x /
    HTGeometry.monicOrthoNormSq s m

/-- **Mobility--inertia duality at one Gauss node.**  Terminal resistance times normalized
completed-source inertia is exactly the fourth power of intrinsic hard position. -/
theorem gaussTerminalSourceResistance_mul_dimensionlessTerminalSourceMass_eq
    {s : ℕ → ℝ} {N m : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hmN : m + 1 < N) {y x : ℝ}
    (hroot : (HTGeometry.monicOrtho s (m + 1)).eval x = 0) :
    HTGeometry.gaussTerminalSourceResistance s m x *
        gaussDimensionlessHardEdgeTerminalSourceMass y s m x =
      (y * x) ^ 4 := by
  have hsource := gaussTerminalSourceResistance_mul_hardEdgeTerminalMass_eq
    h hmN y hroot
  have hnorm : HTGeometry.monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below h (by omega))
  unfold gaussDimensionlessHardEdgeTerminalSourceMass
  calc
    HTGeometry.gaussTerminalSourceResistance s m x *
          (y ^ 3 * xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
              (HTGeometry.monicOrtho s (m + 1)) x /
            HTGeometry.monicOrthoNormSq s m) =
        y ^ 3 *
            (HTGeometry.gaussTerminalSourceResistance s m x *
              xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
                (HTGeometry.monicOrtho s (m + 1)) x) /
          HTGeometry.monicOrthoNormSq s m := by ring
    _ = y ^ 3 * (y * x ^ 4 * HTGeometry.monicOrthoNormSq s m) /
          HTGeometry.monicOrthoNormSq s m := by rw [hsource]
    _ = (y * x) ^ 4 := by field_simp [hnorm]

/-- **Super-apex source amplification.**  A current Gauss node beyond the moving hard apex
`y*x = 1` carries more than one full intrinsic terminal-source quantum.  The proof uses the
endogenous admission share itself: every share is at most one, while share times source is the
fourth hard-coordinate power.  Thus a vanishing admission share amplifies rather than hides a
super-apex source. -/
theorem one_lt_gaussDimensionlessHardEdgeTerminalSourceMass_of_superApex
    {s : ℕ → ℝ} {N m : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hmN : m + 1 < N) {y x : ℝ}
    (hroot : (HTGeometry.monicOrtho s (m + 1)).eval x = 0)
    (hsuper : 1 < y * x) :
    1 < gaussDimensionlessHardEdgeTerminalSourceMass y s m x := by
  let nodes := HTGeometry.gaussNodes s m
  let r : ℝ → ℝ := fun z => HTGeometry.gaussTerminalSourceResistance s m z
  let source := gaussDimensionlessHardEdgeTerminalSourceMass y s m x
  have hxnodes : x ∈ nodes := (HTGeometry.mem_gaussNodes_iff m x).2 hroot
  have hrpos : 0 < r x := HTGeometry.gaussTerminalSourceResistance_pos h hmN hroot
  have hrnonneg : ∀ z ∈ nodes, 0 ≤ r z := by
    intro z hz
    exact (HTGeometry.gaussTerminalSourceResistance_pos h hmN
      ((HTGeometry.mem_gaussNodes_iff m z).1 hz)).le
  have hrleSum : r x ≤ ∑ z ∈ nodes, r z := by
    exact Finset.single_le_sum (fun z hz => hrnonneg z hz) hxnodes
  have hrsum : ∑ z ∈ nodes, r z = 1 :=
    HTGeometry.sum_gaussTerminalSourceResistance_eq_one h hmN
  have hrle : r x ≤ 1 := by simpa only [hrsum] using hrleSum
  have hproduct : r x * source = (y * x) ^ 4 := by
    simpa only [r, source] using
      gaussTerminalSourceResistance_mul_dimensionlessTerminalSourceMass_eq
        h hmN (y := y) hroot
  have hsq : 1 < (y * x) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hsuper) (by linarith : 0 < y * x + 1)]
  have hfourth : 1 < (y * x) ^ 4 := by
    nlinarith [mul_pos (sub_pos.mpr hsq) (by linarith : 0 < (y * x) ^ 2 + 1)]
  by_contra hnot
  have hsourceLe : source ≤ 1 := le_of_not_gt hnot
  have hproductLe : r x * source ≤ 1 := by
    calc
      r x * source ≤ r x * 1 := mul_le_mul_of_nonneg_left hsourceLe hrpos.le
      _ = r x := mul_one _
      _ ≤ 1 := hrle
  rw [hproduct] at hproductLe
  linarith

/-- **All-root terminal-source amplification.** Total dimensionless completed source dominates
the square of total hard-root quadratic energy.  No node, source product, or hard coordinate is
divided by; zero hard nodes are permitted. -/
theorem hardCoordinateQuadraticEnergy_sq_le_sum_dimensionlessTerminalSourceMass
    {s : ℕ → ℝ} {N m : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hmN : m + 1 < N) (y : ℝ) :
    (∑ x ∈ HTGeometry.gaussNodes s m, (y * x) ^ 2) ^ 2 ≤
      ∑ x ∈ HTGeometry.gaussNodes s m,
        gaussDimensionlessHardEdgeTerminalSourceMass y s m x := by
  let nodes := HTGeometry.gaussNodes s m
  let r : ℝ → ℝ := fun x => HTGeometry.gaussTerminalSourceResistance s m x
  have hrpos : ∀ x ∈ nodes, 0 < r x := by
    intro x hx
    exact HTGeometry.gaussTerminalSourceResistance_pos h hmN
      ((HTGeometry.mem_gaussNodes_iff m x).mp hx)
  have hcauchy := Finset.sq_sum_div_le_sum_sq_div nodes
    (fun x => (y * x) ^ 2) hrpos
  have hrsum : ∑ x ∈ nodes, r x = 1 :=
    HTGeometry.sum_gaussTerminalSourceResistance_eq_one h hmN
  rw [hrsum, div_one] at hcauchy
  calc
    (∑ x ∈ HTGeometry.gaussNodes s m, (y * x) ^ 2) ^ 2 ≤
        ∑ x ∈ nodes, ((y * x) ^ 2) ^ 2 / r x := by
      simpa only [nodes, r] using hcauchy
    _ = ∑ x ∈ HTGeometry.gaussNodes s m,
        gaussDimensionlessHardEdgeTerminalSourceMass y s m x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hroot : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 :=
        (HTGeometry.mem_gaussNodes_iff m x).mp hx
      have hpoint := gaussTerminalSourceResistance_mul_dimensionlessTerminalSourceMass_eq
        h hmN (y := y) hroot
      have hrne : HTGeometry.gaussTerminalSourceResistance s m x ≠ 0 :=
        ne_of_gt (HTGeometry.gaussTerminalSourceResistance_pos h hmN hroot)
      rw [show ((y * x) ^ 2) ^ 2 = (y * x) ^ 4 by ring]
      apply (div_eq_iff hrne).2
      simpa only [mul_comm] using hpoint.symm

/-- Unnormalized source amplification.  For nonnegative mass, literal terminal source dominates
preceding norm times squared unscaled root energy. -/
theorem mass_mul_norm_mul_gaussNodeQuadraticEnergy_sq_le_sum_terminalSourceMass
    {s : ℕ → ℝ} {N m : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hmN : m + 1 < N) {y : ℝ} (hy : 0 ≤ y) :
    y * HTGeometry.monicOrthoNormSq s m *
        (∑ x ∈ HTGeometry.gaussNodes s m, x ^ 2) ^ 2 ≤
      ∑ x ∈ HTGeometry.gaussNodes s m,
        xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
          (HTGeometry.monicOrtho s (m + 1)) x := by
  let nodes := HTGeometry.gaussNodes s m
  let r : ℝ → ℝ := fun x => HTGeometry.gaussTerminalSourceResistance s m x
  have hrpos : ∀ x ∈ nodes, 0 < r x := by
    intro x hx
    exact HTGeometry.gaussTerminalSourceResistance_pos h hmN
      ((HTGeometry.mem_gaussNodes_iff m x).mp hx)
  have hcauchy := Finset.sq_sum_div_le_sum_sq_div nodes (fun x => x ^ 2) hrpos
  have hrsum : ∑ x ∈ nodes, r x = 1 :=
    HTGeometry.sum_gaussTerminalSourceResistance_eq_one h hmN
  rw [hrsum, div_one] at hcauchy
  have hnormnonneg : 0 ≤ HTGeometry.monicOrthoNormSq s m :=
    (HTGeometry.monicOrthoNorm_pos_below h (by omega)).le
  calc
    y * HTGeometry.monicOrthoNormSq s m *
          (∑ x ∈ HTGeometry.gaussNodes s m, x ^ 2) ^ 2 ≤
        y * HTGeometry.monicOrthoNormSq s m *
          (∑ x ∈ nodes, (x ^ 2) ^ 2 / r x) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [nodes, r] using hcauchy)
        (mul_nonneg hy hnormnonneg)
    _ = ∑ x ∈ HTGeometry.gaussNodes s m,
        xiShiftedHardEdgeGaussTerminalMass y s (m + 1)
          (HTGeometry.monicOrtho s (m + 1)) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hroot : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 :=
        (HTGeometry.mem_gaussNodes_iff m x).mp hx
      have hsource := gaussTerminalSourceResistance_mul_hardEdgeTerminalMass_eq
        h hmN y hroot
      have hrne : HTGeometry.gaussTerminalSourceResistance s m x ≠ 0 :=
        ne_of_gt (HTGeometry.gaussTerminalSourceResistance_pos h hmN hroot)
      rw [show (x ^ 2) ^ 2 = x ^ 4 by ring]
      dsimp only [r]
      field_simp [hrne]
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hsource.symm

/-- **Terminal resistance is normalized hard-root mobility.**  Dividing the two literal source
laws only after proving terminal mass nonzero identifies the actual reciprocal-root speed with its
current admission share. -/
theorem xiShiftedCanonicalAdmissionHardEdgeWorldline_eq_beta_mul_terminalResistance
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y) (hx0 : x y ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0) :
    (x y) ^ 2 * (-xdot / (x y) ^ 2 - 1) =
      2 * (n : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
        HTGeometry.gaussTerminalSourceResistance
          (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1) (x y) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s (m + 1)
  let Gamma := xiShiftedHardEdgeGaussTerminalMass y s (m + 1) P (x y)
  let r := HTGeometry.gaussTerminalSourceResistance s m (x y)
  let beta := HTGeometry.monicOrthoBeta s (m + 1)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : P = HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hroot0 : P.eval (x y) = 0 := hroot.eq_of_nhds
  have hrootOrtho : (HTGeometry.monicOrtho s (m + 1)).eval (x y) = 0 := by
    rw [← hP]
    exact hroot0
  have hworld :=
    xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_terminalMass_eq_normSq
      hy (by omega : 0 < m + 1) hH hx hx0 hroot
  have hres0 := gaussTerminalSourceResistance_mul_hardEdgeTerminalMass_eq
    hbelow (by omega : m + 1 < m + 3) y hrootOrtho
  have hres : r * Gamma = y * (x y) ^ 4 * HTGeometry.monicOrthoNormSq s m := by
    simpa only [r, Gamma, hP] using hres0
  have hnorm := HTGeometry.monicOrthoNormSq_mul_nextBeta hbelow
    (n := m) (by omega : m + 1 < m + 3)
  have hnormpos : 0 < HTGeometry.monicOrthoNormSq s m :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hGamma : Gamma ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hres
    have hrhs : 0 < y * (x y) ^ 4 * HTGeometry.monicOrthoNormSq s m := by
      positivity
    linarith
  apply (mul_right_cancel₀ hGamma)
  calc
    ((x y) ^ 2 * (-xdot / (x y) ^ 2 - 1)) * Gamma =
        (x y) ^ 2 *
          ((-xdot / (x y) ^ 2 - 1) * Gamma) := by ring
    _ = (x y) ^ 2 *
        (2 * ((m + 1 : ℕ) : ℝ) * y * (x y) ^ 2 *
          HTGeometry.monicOrthoNormSq s (m + 1)) := by
      simpa only [Gamma, P, s] using congrArg (fun z => (x y) ^ 2 * z) hworld
    _ = 2 * ((m + 1 : ℕ) : ℝ) * beta * (r * Gamma) := by
      rw [hres, ← hnorm]
      ring
    _ = (2 * ((m + 1 : ℕ) : ℝ) * beta * r) * Gamma := by ring

/-- **Resistance-free source action along an actual hard-root worldline.**  Mobility--inertia
duality cancels the endogenous terminal share completely: reciprocal hard-root velocity times
intrinsic completed-source mass is forced by current Jacobi edge, degree, mass, and squared node
position. -/
theorem xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_dimensionlessTerminalSourceMass_eq
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y) (hx0 : x y ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0) :
    (-xdot / (x y) ^ 2 - 1) *
        gaussDimensionlessHardEdgeTerminalSourceMass y
          (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1) (x y) =
      2 * (n : ℝ) *
        HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
        y ^ 4 * (x y) ^ 2 := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let r := HTGeometry.gaussTerminalSourceResistance s (n - 1) (x y)
  let source := gaussDimensionlessHardEdgeTerminalSourceMass y s (n - 1) (x y)
  let velocity := -xdot / (x y) ^ 2 - 1
  let beta := HTGeometry.monicOrthoBeta s n
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hroot0 : (HTGeometry.monicMomentAdmissionPolynomial s n).eval (x y) = 0 :=
    hroot.eq_of_nhds
  have hrootOrtho : (HTGeometry.monicOrtho s n).eval (x y) = 0 := by
    rw [← hP]
    exact hroot0
  have hmobility :=
    xiShiftedCanonicalAdmissionHardEdgeWorldline_eq_beta_mul_terminalResistance
      hy hn hH hx hx0 hroot
  have hmobility' : (x y) ^ 2 * velocity = 2 * (n : ℝ) * beta * r := by
    simpa only [velocity, beta, r, s] using hmobility
  have hrootOrtho' :
      (HTGeometry.monicOrtho s (n - 1 + 1)).eval (x y) = 0 := by
    simpa only [show n - 1 + 1 = n by omega] using hrootOrtho
  have hduality : r * source = (y * x y) ^ 4 := by
    simpa only [r, source, show n - 1 + 1 = n by omega, s] using
      gaussTerminalSourceResistance_mul_dimensionlessTerminalSourceMass_eq
        hbelow (m := n - 1) (by omega : n - 1 + 1 < n + 2)
          (y := y) hrootOrtho'
  apply mul_left_cancel₀ (pow_ne_zero 2 hx0)
  calc
    (x y) ^ 2 * (velocity * source) =
        ((x y) ^ 2 * velocity) * source := by ring
    _ = (2 * (n : ℝ) * beta * r) * source := by rw [hmobility']
    _ = 2 * (n : ℝ) * beta * (r * source) := by ring
    _ = 2 * (n : ℝ) * beta * (y * x y) ^ 4 := by rw [hduality]
    _ = (x y) ^ 2 *
        (2 * (n : ℝ) * beta * y ^ 4 * (x y) ^ 2) := by ring

namespace XiShiftedCanonicalAdmission

/-- Centered projective root spread is bounded by uncentered Gauss-node quadratic energy. -/
theorem projectiveGaussRootSpread_le_gaussNodeQuadraticEnergy
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n < N) :
    projectiveGaussRootSpread s n ≤
      ∑ x ∈ HTGeometry.gaussNodes s (n - 1), x ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one]
  rw [projectiveGaussRootSpread, HTGeometry.multisetQuadraticSpread,
    HTGeometry.gaussNodes, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr
      (HTGeometry.monicOrtho_roots_nodup_below h hnN)]
  have hcenter : 0 ≤
      (HTGeometry.monicOrtho s (m + 1)).roots.sum ^ 2 / ((m + 1 : ℕ) : ℝ) := by
    positivity
  linarith

/-- Reciprocal-mass coordinate transport gives projective root spread exact weight four. -/
theorem projectiveGaussRootSpread_normalized_eq_fourth_mul_actual
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 2 ≤ n)
    (hA : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    projectiveGaussRootSpread (xiShiftedFarRightNormalizedMoment w) n =
      w ^ 4 * projectiveGaussRootSpread (xiShiftedRealMomentSequence w) n := by
  have hN0 := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual hw (n + 2) hA
  have hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef := by
    simpa only [xiShiftedFarRightNormalizedHankelMatrix] using hN0
  let hNbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hN
  let hAbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hA
  have halpha : ∀ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j =
        w ^ 2 * HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hNj : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA
    change HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j =
      w ^ 2 * HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) j
    exact normalizedAlpha_eq_square_mul_actualAlpha hw j hNj hAj
  have hbeta : ∀ j ∈ Finset.range n,
      HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j =
        w ^ 4 * HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) j := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hNj : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA
    change HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j =
      w ^ 4 * HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) j
    exact normalizedBeta_eq_fourth_mul_actualBeta hw j hNj hAj
  have hsumAlpha :
      (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j) =
      w ^ 2 * ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [halpha j hj]
  have hsumAlphaSq :
      (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j ^ 2) =
      w ^ 4 * ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [halpha j hj]
    ring
  have hsumBeta :
      (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j) =
      w ^ 4 * ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbeta j hj]
  rw [projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory
      hNbelow hn (by omega),
    projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory
      hAbelow hn (by omega)]
  unfold projectiveJacobiLowerAlphaDispersion
  rw [hsumAlpha, hsumAlphaSq, hsumBeta]
  ring

/-- Dimensionless aggregate of terminal masses generated by the current shifted-Xi admission. -/
def xiShiftedCanonicalAdmissionDimensionlessTerminalSourceMassAggregate
    (w : ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
    gaussDimensionlessHardEdgeTerminalSourceMass (w ^ 2)
      (xiShiftedRealMomentSequence w) (n - 1) x

/-- **Projective spread forces completed-source amplification.**  In every finite positive
shifted-Xi chamber, squared dimensionless root spread is paid by total terminal source. -/
theorem projectiveGaussRootSpread_sq_le_dimensionlessTerminalSourceMassAggregate
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    projectiveGaussRootSpread (xiShiftedFarRightNormalizedMoment w) n ^ 2 ≤
      xiShiftedCanonicalAdmissionDimensionlessTerminalSourceMassAggregate w n := by
  let s := xiShiftedRealMomentSequence w
  let spread := projectiveGaussRootSpread s n
  let energy := ∑ x ∈ HTGeometry.gaussNodes s (n - 1), (w ^ 2 * x) ^ 2
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hspreadScale := projectiveGaussRootSpread_normalized_eq_fourth_mul_actual
    hw hn hH
  have hspreadLe := projectiveGaussRootSpread_le_gaussNodeQuadraticEnergy
    hbelow (by omega : 0 < n) (by omega : n < n + 2)
  have hspreadNonneg : 0 ≤ spread :=
    (projectiveGaussRootSpread_pos hbelow hn (by omega)).le
  have henergyNonneg : 0 ≤ energy := by
    dsimp only [energy]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have henergyEq : energy = w ^ 4 *
      (∑ x ∈ HTGeometry.gaussNodes s (n - 1), x ^ 2) := by
    dsimp only [energy]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hw4 : 0 ≤ w ^ 4 := by positivity
  have hscaledLe : w ^ 4 * spread ≤ energy := by
    rw [henergyEq]
    exact mul_le_mul_of_nonneg_left hspreadLe hw4
  have hscaledNonneg : 0 ≤ w ^ 4 * spread := mul_nonneg hw4 hspreadNonneg
  have hsquares : (w ^ 4 * spread) ^ 2 ≤ energy ^ 2 := by
    have hproduct : 0 ≤ (energy - w ^ 4 * spread) * (energy + w ^ 4 * spread) :=
      mul_nonneg (sub_nonneg.mpr hscaledLe) (add_nonneg henergyNonneg hscaledNonneg)
    nlinarith
  have haggregate := hardCoordinateQuadraticEnergy_sq_le_sum_dimensionlessTerminalSourceMass
    hbelow (m := n - 1) (by omega : n - 1 + 1 < n + 2) (w ^ 2)
  rw [hspreadScale]
  exact hsquares.trans (by
    simpa only [energy, spread, s,
      xiShiftedCanonicalAdmissionDimensionlessTerminalSourceMassAggregate] using haggregate)

/-- Intrinsic source quantum at one current node, formed as actual Padé residue times endogenous
capacity of the current/adjacent vacuum-free mixed/completed `P^sharp` producer before any
all-root aggregation. -/
def xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (w ^ 2) ^ 3 *
      (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
        xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
          w n x) /
    HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n - 1)

/-- **Literal super-apex arithmetic source floor.**  If an actual current shifted-Xi node lies
beyond the reciprocal hard apex, the already-formed current/adjacent vacuum-free completed
`P^sharp` source product at that node exceeds one intrinsic quantum.  No fixed reporter or
post-source orientation is introduced. -/
theorem one_lt_dimensionlessVacuumFreeCompletedSourceMass_of_superApex
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ}
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0)
    (hsuper : 1 < w ^ 2 * x) :
    1 < xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass w n x := by
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hrootOrtho : (HTGeometry.monicOrtho s n).eval x = 0 := by
    rw [← hP]
    exact hroot
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, mul_zero] at hsuper
    linarith
  have hgeneric := one_lt_gaussDimensionlessHardEdgeTerminalSourceMass_of_superApex
    hbelow (m := n - 1) (by omega : n - 1 + 1 < n + 2)
      (y := w ^ 2) (by simpa only [show n - 1 + 1 = n by omega] using hrootOrtho)
      hsuper
  have hsource :=
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
      (w := w) (n := n) hx0 hroot
  unfold xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass
  rw [hsource]
  simp only [xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass]
  rw [hP]
  simpa only [gaussDimensionlessHardEdgeTerminalSourceMass,
    show n - 1 + 1 = n by omega, s] using hgeneric

/-- Literal current/adjacent `P^sharp` form of the resistance-free worldline action.  The
endogenous admission share has disappeared from the product, so low mobility must be paid by high
completed-source inertia. -/
theorem hardEdgeWorldline_mul_dimensionlessVacuumFreeCompletedSourceMass_eq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hx0 : x (w ^ 2) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0) :
    (-xdot / (x (w ^ 2)) ^ 2 - 1) *
        xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass
          w n (x (w ^ 2)) =
      2 * (n : ℝ) *
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
      (w ^ 2) ^ 4 * (x (w ^ 2)) ^ 2 := by
  let s := xiShiftedRealMomentSequence w
  have hy : 0 < w ^ 2 := sq_pos_of_pos (lt_trans (by norm_num) hw)
  have hgeneric :=
    xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_dimensionlessTerminalSourceMass_eq
      hy hn hH hx hx0 hroot
  have hroot0 :
      (HTGeometry.monicMomentAdmissionPolynomial s n).eval (x (w ^ 2)) = 0 :=
    hroot.eq_of_nhds
  have hP : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hsource :=
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
      (w := w) (n := n) hx0 hroot0
  have hmassEq :
      xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass
          w n (x (w ^ 2)) =
        gaussDimensionlessHardEdgeTerminalSourceMass (w ^ 2) s (n - 1)
          (x (w ^ 2)) := by
    unfold xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass
    rw [hsource]
    simp only [xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass]
    rw [hP]
    unfold gaussDimensionlessHardEdgeTerminalSourceMass
    simp only [show n - 1 + 1 = n by omega, s]
  rw [hmassEq]
  change (-xdot / (x (w ^ 2)) ^ 2 - 1) *
      gaussDimensionlessHardEdgeTerminalSourceMass (w ^ 2)
        (xiShiftedRealMomentSequence w) (n - 1) (x (w ^ 2)) =
    2 * (n : ℝ) *
      HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
      (w ^ 2) ^ 4 * (x (w ^ 2)) ^ 2 at hgeneric
  exact hgeneric

/-- Source action after subtracting the intrinsic moving-apex vacuum.  This is built from the
literal current/adjacent completed-source product and actual root velocity, not from a fixed
orientation functional. -/
def apexCenteredDimensionlessVacuumFreeCompletedSourceAction
    (w : ℝ) (n : ℕ) (x xdot : ℝ) : ℝ :=
  (-xdot / x ^ 2 - 1) *
      xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass w n x -
    2 * (n : ℝ) *
      HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n * (w ^ 2) ^ 2

/-- Exact moving-apex polarization of literal completed-source work. -/
theorem apexCenteredDimensionlessVacuumFreeCompletedSourceAction_eq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hx0 : x (w ^ 2) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0) :
    apexCenteredDimensionlessVacuumFreeCompletedSourceAction
        w n (x (w ^ 2)) xdot =
      2 * (n : ℝ) *
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
        (w ^ 2) ^ 2 * ((w ^ 2 * x (w ^ 2)) ^ 2 - 1) := by
  rw [apexCenteredDimensionlessVacuumFreeCompletedSourceAction,
    hardEdgeWorldline_mul_dimensionlessVacuumFreeCompletedSourceMass_eq
      hw hn hH hx hx0 hroot]
  ring

/-- The centered arithmetic action is exactly a positive geometric factor times minus the
centered reciprocal hard coordinate.  This is the source-derived form of super-apex polarity. -/
theorem apexCenteredDimensionlessVacuumFreeCompletedSourceAction_eq_neg_hardCoordinate
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hx0 : x (w ^ 2) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0) :
    apexCenteredDimensionlessVacuumFreeCompletedSourceAction
        w n (x (w ^ 2)) xdot =
      -(2 * (n : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          (w ^ 2) ^ 2 * x (w ^ 2) * (w ^ 2 * x (w ^ 2) + 1)) *
        ((x (w ^ 2))⁻¹ - w ^ 2) := by
  rw [apexCenteredDimensionlessVacuumFreeCompletedSourceAction_eq
    hw hn hH hx hx0 hroot]
  have hcore :
      (w ^ 2 * x (w ^ 2)) ^ 2 - 1 =
        -x (w ^ 2) * (w ^ 2 * x (w ^ 2) + 1) *
          ((x (w ^ 2))⁻¹ - w ^ 2) := by
    have hlinear :
        w ^ 2 * x (w ^ 2) - 1 =
          -x (w ^ 2) * ((x (w ^ 2))⁻¹ - w ^ 2) := by
      calc
        w ^ 2 * x (w ^ 2) - 1 =
            w ^ 2 * x (w ^ 2) - x (w ^ 2) * (x (w ^ 2))⁻¹ := by
          rw [mul_inv_cancel₀ hx0]
        _ = -x (w ^ 2) * ((x (w ^ 2))⁻¹ - w ^ 2) := by ring
    calc
      (w ^ 2 * x (w ^ 2)) ^ 2 - 1 =
          (w ^ 2 * x (w ^ 2) - 1) *
            (w ^ 2 * x (w ^ 2) + 1) := by ring
      _ = -x (w ^ 2) * (w ^ 2 * x (w ^ 2) + 1) *
          ((x (w ^ 2))⁻¹ - w ^ 2) := by rw [hlinear]; ring
  rw [hcore]
  ring

/-- Negative reciprocal hard coordinate is equivalent to positive centered literal source action
on every positive current node. -/
theorem apexCenteredDimensionlessVacuumFreeCompletedSourceAction_pos_iff_neg_hardCoordinate
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hxpos : 0 < x (w ^ 2))
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0) :
    0 < apexCenteredDimensionlessVacuumFreeCompletedSourceAction
        w n (x (w ^ 2)) xdot ↔
      (x (w ^ 2))⁻¹ - w ^ 2 < 0 := by
  rw [apexCenteredDimensionlessVacuumFreeCompletedSourceAction_eq_neg_hardCoordinate
    hw hn hH hx hxpos.ne' hroot]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hbeta : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedRealMomentSequence w) n :=
    HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega)
  have hw2 : 0 < w ^ 2 := sq_pos_of_pos (lt_trans (by norm_num) hw)
  have hsum : 0 < w ^ 2 * x (w ^ 2) + 1 := by positivity
  have hfactor : 0 < 2 * (n : ℝ) *
      HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
      (w ^ 2) ^ 2 * x (w ^ 2) * (w ^ 2 * x (w ^ 2) + 1) := by
    positivity
  constructor
  · intro hpos
    by_contra hnot
    have hnonneg : 0 ≤ (x (w ^ 2))⁻¹ - w ^ 2 := le_of_not_gt hnot
    have : -(2 * (n : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          (w ^ 2) ^ 2 * x (w ^ 2) * (w ^ 2 * x (w ^ 2) + 1)) *
          ((x (w ^ 2))⁻¹ - w ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hfactor.le) hnonneg
    linarith
  · intro hneg
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hfactor) hneg

/-- Exact normalization of centered source action by its degree--edge--mass vacuum. -/
theorem apexCenteredDimensionlessVacuumFreeCompletedSourceAction_div_degreeEdgeMass_eq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hx0 : x (w ^ 2) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0) :
    apexCenteredDimensionlessVacuumFreeCompletedSourceAction
          w n (x (w ^ 2)) xdot /
        (2 * (n : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          (w ^ 2) ^ 2) =
      (w ^ 2 * x (w ^ 2)) ^ 2 - 1 := by
  rw [apexCenteredDimensionlessVacuumFreeCompletedSourceAction_eq
    hw hn hH hx hx0 hroot]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hbeta : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedRealMomentSequence w) n :=
    HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega)
  have hfactor : 2 * (n : ℝ) *
      HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
      (w ^ 2) ^ 2 ≠ 0 := by positivity
  exact mul_div_cancel_left₀ _ hfactor

/-- **Bounded hard-root survival in centered source coordinates.**  If mass tends to infinity and
the centered reciprocal hard coordinate tends to `d`, then mass times normalized apex-centered
source work tends to `-2d`.  In particular a bounded negative hard root leaves a strictly positive
finite source signature; vanishing Gauss weight cannot erase it. -/
theorem tendsto_mass_mul_apexCenteredHardSourceWork
    {y u : ℕ → ℝ} {d : ℝ}
    (hy : Tendsto y atTop atTop) (hu : Tendsto u atTop (nhds d)) :
    Tendsto (fun k =>
      y k * ((y k * (y k + u k)⁻¹) ^ 2 - 1))
      atTop (nhds (-2 * d)) := by
  have hyinv : Tendsto (fun k => (y k)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hy
  have huratio : Tendsto (fun k => u k * (y k)⁻¹) atTop (nhds 0) := by
    simpa only [Pi.mul_apply, mul_zero] using hu.mul hyinv
  have hunum : Tendsto (fun k => -(2 * u k + u k ^ 2 * (y k)⁻¹))
      atTop (nhds (-2 * d)) := by
    have husqinv : Tendsto (fun k => u k ^ 2 * (y k)⁻¹) atTop (nhds 0) := by
      simpa only [Pi.mul_apply, Pi.pow_apply, mul_zero] using
        (hu.pow 2).mul hyinv
    simpa only [Pi.neg_apply, Pi.add_apply, add_zero, neg_mul] using
      ((hu.const_mul 2).add husqinv).neg
  have hden : Tendsto (fun k => (1 + u k * (y k)⁻¹) ^ 2)
      atTop (nhds 1) := by
    simpa only [Pi.add_apply, Pi.pow_apply, add_zero, one_pow] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add huratio).pow 2
  have hquot : Tendsto (fun k =>
      -(2 * u k + u k ^ 2 * (y k)⁻¹) /
        (1 + u k * (y k)⁻¹) ^ 2) atTop (nhds (-2 * d)) := by
    change Tendsto
      ((fun k : ℕ => -(2 * u k + u k ^ 2 * (y k)⁻¹)) /
        (fun k : ℕ => (1 + u k * (y k)⁻¹) ^ 2))
      atTop (nhds (-2 * d))
    simpa only [div_one] using
      hunum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hyu : Tendsto (fun k => y k + u k) atTop atTop := hy.atTop_add hu
  apply hquot.congr'
  filter_upwards [hy.eventually_gt_atTop 0, hyu.eventually_gt_atTop 0] with k hypos hyupos
  field_simp [hypos.ne', hyupos.ne']
  ring

/-- **Literal bounded-super-apex source survival.**  Along any moving-degree shifted-Xi schedule,
if actual current roots have bounded centered reciprocal coordinate `u -> d`, then the
mass-rescaled, degree--edge-normalized, apex-centered action of the current/adjacent vacuum-free
completed `P^sharp` source tends to `-2d`.  This is the source-first finite ancestor of terminal
hard sign. -/
theorem tendsto_mass_mul_normalizedApexCenteredVacuumFreeCompletedSourceAction
    {w : ℕ → ℝ} {n : ℕ → ℕ} {x : ℕ → ℝ → ℝ}
    {xdot u : ℕ → ℝ} {d : ℝ}
    (hw : ∀ k, 1 / 2 < w k) (hn : ∀ k, 0 < n k)
    (hH : ∀ k, (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w k)) (n k + 2)).PosDef)
    (hx : ∀ k, HasDerivAt (x k) (xdot k) (w k ^ 2))
    (hx0 : ∀ k, x k (w k ^ 2) ≠ 0)
    (hroot : ∀ k,
      (fun v =>
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun j => (xiShiftedReciprocalMoment v j).re) (n k)).eval (x k v))
        =ᶠ[nhds (w k ^ 2)] fun _ => 0)
    (hcoord : ∀ k, x k (w k ^ 2) = (w k ^ 2 + u k)⁻¹)
    (hmass : Tendsto (fun k => w k ^ 2) atTop atTop)
    (hu : Tendsto u atTop (nhds d)) :
    Tendsto (fun k =>
      (w k ^ 2) *
        (apexCenteredDimensionlessVacuumFreeCompletedSourceAction
            (w k) (n k) (x k (w k ^ 2)) (xdot k) /
          (2 * (n k : ℝ) *
            HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence (w k)) (n k) *
            (w k ^ 2) ^ 2)))
      atTop (nhds (-2 * d)) := by
  have hlimit := tendsto_mass_mul_apexCenteredHardSourceWork hmass hu
  apply hlimit.congr'
  exact Eventually.of_forall fun k => by
    dsimp only
    rw [apexCenteredDimensionlessVacuumFreeCompletedSourceAction_div_degreeEdgeMass_eq
      (hw k) (hn k) (hH k) (hx k) (hx0 k) (hroot k), hcoord k]

/-- A super-apex worldline pays more than one degree--edge--mass quantum of literal completed
source action.  This is threshold-sensitive at `w²*x = 1`; ordinary total-source growth does not
imply it. -/
theorem degreeEdgeMassAction_lt_hardEdgeWorldline_mul_dimensionlessVacuumFreeCompletedSourceMass_of_superApex
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ 2))
    (hx0 : x (w ^ 2) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ 2)]
          fun _ => 0)
    (hsuper : 1 < w ^ 2 * x (w ^ 2)) :
    2 * (n : ℝ) *
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
        (w ^ 2) ^ 2 <
      (-xdot / (x (w ^ 2)) ^ 2 - 1) *
        xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass
          w n (x (w ^ 2)) := by
  have haction :=
    hardEdgeWorldline_mul_dimensionlessVacuumFreeCompletedSourceMass_eq
      hw hn hH hx hx0 hroot
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hbeta : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedRealMomentSequence w) n :=
    HTGeometry.monicOrthoBeta_pos_below hbelow hn (by omega)
  have hmass : 0 < w ^ 2 := sq_pos_of_pos (lt_trans (by norm_num) hw)
  have ht2 : 1 < (w ^ 2 * x (w ^ 2)) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hsuper)
      (by linarith : 0 < w ^ 2 * x (w ^ 2) + 1)]
  rw [haction]
  have hfactor : 0 < 2 * (n : ℝ) *
      HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n * (w ^ 2) ^ 2 := by
    positivity
  calc
    2 * (n : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          (w ^ 2) ^ 2 <
        (2 * (n : ℝ) *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
          (w ^ 2) ^ 2) * (w ^ 2 * x (w ^ 2)) ^ 2 := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left ht2 hfactor
    _ = 2 * (n : ℝ) *
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) n *
        (w ^ 2) ^ 4 * (x (w ^ 2)) ^ 2 := by ring

/-- Literal aggregate of Padé residue times endogenous vacuum-free mixed/completed `P^sharp`
capacity, normalized in the intrinsic hard chart. -/
def xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceAggregate
    (w : ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
    xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass w n x

/-- Source-first capstone: where the reciprocal hard chart is defined at every node, squared
projective spread is paid by the literal current/adjacent vacuum-free completed source aggregate. -/
theorem projectiveGaussRootSpread_sq_le_dimensionlessVacuumFreeCompletedSourceAggregate
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), x ≠ 0) :
    projectiveGaussRootSpread (xiShiftedFarRightNormalizedMoment w) n ^ 2 ≤
      xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceAggregate w n := by
  have hbase := projectiveGaussRootSpread_sq_le_dimensionlessTerminalSourceMassAggregate
    hw hn hH
  refine hbase.trans_eq ?_
  unfold xiShiftedCanonicalAdmissionDimensionlessTerminalSourceMassAggregate
  unfold xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceAggregate
  unfold xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceMass
  apply Finset.sum_congr rfl
  intro x hx
  have hx0 := hnodes x hx
  have hrootOrtho : (HTGeometry.monicOrtho
      (xiShiftedRealMomentSequence w) n).eval x = 0 := by
    simpa only [show n - 1 + 1 = n by omega] using
      (HTGeometry.mem_gaussNodes_iff (n - 1) x).mp hx
  have hP : HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n =
      HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hrootAdmission : (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence w) n).eval x = 0 := by
    rw [hP]
    exact hrootOrtho
  have hsource :=
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
      hx0 hrootAdmission
  unfold gaussDimensionlessHardEdgeTerminalSourceMass
  rw [show n - 1 + 1 = n by omega]
  rw [hsource]
  simp only [xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass]
  rw [hP]

/-- **Cofinal nonescape of total terminal source.** Along every cofinal schedule of actual positive
shifted-Xi blocks, total dimensionless terminal source tends to infinity.  Increasing degree cannot
make the whole source disappear. -/
theorem tendsto_dimensionlessTerminalSourceMassAggregate_along_cofinal_actual_positive_blocks
    (w : ℕ → ℝ) (n : ℕ → ℕ)
    (hw : Tendsto w atTop atTop) (hn : Tendsto n atTop atTop)
    (hH : ∀ l, (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef) :
    Tendsto (fun l =>
      xiShiftedCanonicalAdmissionDimensionlessTerminalSourceMassAggregate (w l) (n l))
      atTop atTop := by
  have hspread := tendsto_projectiveGaussRootSpread_along_cofinal_actual_positive_blocks
    w n hw hn hH
  apply tendsto_atTop.2
  intro A
  have hspreadLarge : ∀ᶠ l in atTop,
      max 1 A ≤ projectiveGaussRootSpread
        (xiShiftedFarRightNormalizedMoment (w l)) (n l) :=
    (tendsto_atTop.1 hspread) (max 1 A)
  have hwLarge : ∀ᶠ l in atTop, 1 < w l := hw.eventually_gt_atTop 1
  have hnLarge : ∀ᶠ l in atTop, 2 ≤ n l := (tendsto_atTop.1 hn) 2
  filter_upwards [hspreadLarge, hwLarge, hnLarge] with l hlarge hwl hnl
  let spread := projectiveGaussRootSpread
    (xiShiftedFarRightNormalizedMoment (w l)) (n l)
  have hsource := projectiveGaussRootSpread_sq_le_dimensionlessTerminalSourceMassAggregate
    hwl hnl (hH l)
  have hspreadOne : 1 ≤ spread := le_trans (le_max_left 1 A) hlarge
  have hspreadA : A ≤ spread := le_trans (le_max_right 1 A) hlarge
  have hspreadZero : 0 ≤ spread := le_trans (by norm_num) hspreadOne
  have hsq : spread ≤ spread ^ 2 := by
    have hproduct : 0 ≤ spread * (spread - 1) :=
      mul_nonneg hspreadZero (sub_nonneg.mpr hspreadOne)
    nlinarith
  exact hspreadA.trans (hsq.trans hsource)

/-- On cofinal schedules whose nodes stay inside the reciprocal hard chart, the literal
Padé-residue/current-adjacent completed-capacity aggregate itself tends to infinity. -/
theorem tendsto_dimensionlessVacuumFreeCompletedSourceAggregate_along_cofinal_actual_positive_blocks
    (w : ℕ → ℝ) (n : ℕ → ℕ)
    (hw : Tendsto w atTop atTop) (hn : Tendsto n atTop atTop)
    (hH : ∀ l, (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef)
    (hnodes : ∀ l x, x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence (w l)) (n l - 1) → x ≠ 0) :
    Tendsto (fun l =>
      xiShiftedCanonicalAdmissionDimensionlessVacuumFreeCompletedSourceAggregate
        (w l) (n l)) atTop atTop := by
  have hspread := tendsto_projectiveGaussRootSpread_along_cofinal_actual_positive_blocks
    w n hw hn hH
  apply tendsto_atTop.2
  intro A
  have hspreadLarge : ∀ᶠ l in atTop,
      max 1 A ≤ projectiveGaussRootSpread
        (xiShiftedFarRightNormalizedMoment (w l)) (n l) :=
    (tendsto_atTop.1 hspread) (max 1 A)
  have hwLarge : ∀ᶠ l in atTop, 1 < w l := hw.eventually_gt_atTop 1
  have hnLarge : ∀ᶠ l in atTop, 2 ≤ n l := (tendsto_atTop.1 hn) 2
  filter_upwards [hspreadLarge, hwLarge, hnLarge] with l hlarge hwl hnl
  let spread := projectiveGaussRootSpread
    (xiShiftedFarRightNormalizedMoment (w l)) (n l)
  have hsource :=
    projectiveGaussRootSpread_sq_le_dimensionlessVacuumFreeCompletedSourceAggregate
      hwl hnl (hH l) (hnodes l)
  have hspreadOne : 1 ≤ spread := le_trans (le_max_left 1 A) hlarge
  have hspreadA : A ≤ spread := le_trans (le_max_right 1 A) hlarge
  have hspreadZero : 0 ≤ spread := le_trans (by norm_num) hspreadOne
  have hsq : spread ≤ spread ^ 2 := by
    have hproduct : 0 ≤ spread * (spread - 1) :=
      mul_nonneg hspreadZero (sub_nonneg.mpr hspreadOne)
    nlinarith
  exact hspreadA.trans (hsq.trans hsource)

end XiShiftedCanonicalAdmission

end

end RHTower
