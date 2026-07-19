import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinDividedPowerStability
import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinPresentationRigidity
import GaloisForLFunctions.HTGeometry.ConfocalEnvelopeHull

/-!
# Positive-field bicompletion law

A scale-covariant Bernstein--confocal positive field has two canonical completions.  The positive
divided-power square root is exactly its pointed analytic source, while the confocal upper field
is exactly its maximal Lorentz hull.  Equality of the observations is equivalent to equality of
this ordered pair of completions.
-/

namespace RHTower

noncomputable section

open Complex Filter Topology
open scoped BigOperators Real ComplexOrder

/-- **Positive-field bicompletion law.**  On the positive-mass chamber and for realized confocal
upper fields, equality of the analytic and geometric observations is equivalent to equality of
the pointed moment prefix and of the maximal canonical hull. -/
theorem positiveField_bicompletion_law
    {m m' : ℕ → ℝ} {N : ℕ} (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    {D : Set ℝ} {S T : Set (ℝ × ℝ)} {G H : ℝ → ℝ}
    (hconeS : S ⊆ HTGeometry.confocalLorentzCone)
    (hconeT : T ⊆ HTGeometry.confocalLorentzCone)
    (hG : HTGeometry.IsConfocalEnvelopeOn D S G)
    (hH : HTGeometry.IsConfocalEnvelopeOn D T H) :
    (bernsteinScalePurityPolynomial m N = bernsteinScalePurityPolynomial m' N ∧
        Set.EqOn G H D) ↔
      ((∀ r ≤ N, m r = m' r) ∧
        HTGeometry.confocalHullOfField D G = HTGeometry.confocalHullOfField D H) := by
  have hGh : HTGeometry.IsConfocalEnvelopeOn D
      (HTGeometry.confocalHullOfField D G) G :=
    HTGeometry.isConfocalEnvelopeOn_confocalHullOfField hconeS hG
  have hHh : HTGeometry.IsConfocalEnvelopeOn D
      (HTGeometry.confocalHullOfField D H) H :=
    HTGeometry.isConfocalEnvelopeOn_confocalHullOfField hconeT hH
  constructor
  · rintro ⟨hpoly, hfield⟩
    exact ⟨(bernsteinScalePurityPolynomial_eq_iff_moment_prefix_eq hm0 hm0').mp hpoly,
      (HTGeometry.eqOn_iff_confocalHullOfField_eq hGh hHh).mp hfield⟩
  · rintro ⟨hprefix, hhull⟩
    exact ⟨(bernsteinScalePurityPolynomial_eq_iff_moment_prefix_eq hm0 hm0').mpr hprefix,
      (HTGeometry.eqOn_iff_confocalHullOfField_eq hGh hHh).mpr hhull⟩

/-- The analytic factor of bicompletion is uniformly stable in the exact degree-adapted tail
norm, with a constant independent of the Bernstein degree. -/
theorem positiveField_bicompletion_analytic_stability
    (m m' : ℕ → ℝ) (N : ℕ) {T tau mu theta : ℝ}
    (hmu : 0 < mu) (htheta1 : theta < 1)
    (hm0 : mu ≤ m 0) (hm0' : mu ≤ m' 0)
    (hT : |T| ≤ tau)
    (hmTail : bernsteinDividedPowerTailNorm m N tau ≤ theta * mu)
    (hm'Tail : bernsteinDividedPowerTailNorm m' N tau ≤ theta * mu) :
    |bernsteinDividedPowerChart m N T - bernsteinDividedPowerChart m' N T| ≤
      |(bernsteinDividedPowerChart m N T) ^ 2 -
        (bernsteinDividedPowerChart m' N T) ^ 2| / (2 * (1 - theta) * mu) :=
  bernsteinDividedPowerChart_stability m m' N hmu htheta1 hm0 hm0' hT hmTail hm'Tail

/-- The geometric factor is maximal: adjoining any point of the canonical hull preserves the
complete realized confocal field. -/
theorem positiveField_bicompletion_geometric_maximality
    {D : Set ℝ} {S : Set (ℝ × ℝ)} {G : ℝ → ℝ}
    (hG : HTGeometry.IsConfocalEnvelopeOn D S G)
    {q : ℝ × ℝ} (hq : q ∈ HTGeometry.confocalHullOfField D G) :
    HTGeometry.IsConfocalEnvelopeOn D (insert q S) G :=
  HTGeometry.isConfocalEnvelopeOn_insert_of_mem_hull hG hq

/-- **Single-observable local-to-global completion law.**  Equality of the positive Bernstein
field on any nonempty open scale interval first recovers the complete pointed moment source.
For any two admissible atomic presentations of those moments it then forces equality of the whole
exterior confocal upper field and hence equality of its maximal canonical hull. -/
theorem localPositiveScaleField_selects_maximalConfocalHull
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m m' : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    {M N a b : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hab : a < b)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m' n : ℂ) = atomicPowerMoment d w n)
    (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    (hobs : ∀ K : ℕ, ∀ x ∈ Set.Ioo a b,
      bernsteinCoefficientPurity (fun r => x ^ r * m r) K =
        bernsteinCoefficientPurity (fun r => x ^ r * m' r) K) :
    m = m' ∧
      HTGeometry.IsConfocalEnvelopeOn (Set.Ioi (max M N))
        (HTGeometry.confocalLorentzLift ''
          Set.range (atomicAggregateNode c z))
        (HTGeometry.confocalUpperField
          (Set.range (atomicAggregateNode c z))) ∧
      HTGeometry.IsConfocalEnvelopeOn (Set.Ioi (max M N))
        (HTGeometry.confocalLorentzLift ''
          Set.range (atomicAggregateNode d w))
        (HTGeometry.confocalUpperField
          (Set.range (atomicAggregateNode d w))) ∧
      Set.EqOn
        (HTGeometry.confocalUpperField
          (Set.range (atomicAggregateNode c z)))
        (HTGeometry.confocalUpperField
          (Set.range (atomicAggregateNode d w)))
        (Set.Ioi (max M N)) ∧
      HTGeometry.confocalHullOfField (Set.Ioi (max M N))
          (HTGeometry.confocalUpperField
            (Set.range (atomicAggregateNode c z))) =
        HTGeometry.confocalHullOfField (Set.Ioi (max M N))
          (HTGeometry.confocalUpperField
            (Set.range (atomicAggregateNode d w))) := by
  have hmm : m = m' :=
    bernsteinScalePurityField_interval_source_faithful hm0 hm0' hab hobs
  subst m'
  letI : Nonempty (AtomicAggregateSupport c z) :=
    nonempty_atomicAggregateSupport_of_positive_real_moment hc hboundZ hmomentZ hm0
  letI : Nonempty (AtomicAggregateSupport d w) :=
    nonempty_atomicAggregateSupport_of_positive_real_moment hd hboundW hmomentW hm0
  have hbz : ∀ u, ‖atomicAggregateNode c z u‖ ≤ M :=
    norm_atomicAggregateNode_le hboundZ
  have hbw : ∀ v, ‖atomicAggregateNode d w v‖ ≤ N :=
    norm_atomicAggregateNode_le hboundW
  have hrealizeZ : HTGeometry.IsConfocalEnvelopeOn (Set.Ioi (max M N))
      (HTGeometry.confocalLorentzLift '' Set.range (atomicAggregateNode c z))
      (HTGeometry.confocalUpperField (Set.range (atomicAggregateNode c z))) := by
    apply HTGeometry.isConfocalEnvelopeOn_confocalLorentzLift_image
      (Set.range_nonempty (atomicAggregateNode c z)) hM
      (by rintro _ ⟨u, rfl⟩; exact hbz u)
    intro R hR
    exact hM.trans_lt ((le_max_left M N).trans_lt hR)
  have hrealizeW : HTGeometry.IsConfocalEnvelopeOn (Set.Ioi (max M N))
      (HTGeometry.confocalLorentzLift '' Set.range (atomicAggregateNode d w))
      (HTGeometry.confocalUpperField (Set.range (atomicAggregateNode d w))) := by
    apply HTGeometry.isConfocalEnvelopeOn_confocalLorentzLift_image
      (Set.range_nonempty (atomicAggregateNode d w)) hN
      (by rintro _ ⟨v, rfl⟩; exact hbw v)
    intro R hR
    exact hN.trans_lt ((le_max_right M N).trans_lt hR)
  have hfield : Set.EqOn
      (HTGeometry.confocalUpperField (Set.range (atomicAggregateNode c z)))
      (HTGeometry.confocalUpperField (Set.range (atomicAggregateNode d w)))
      (Set.Ioi (max M N)) := by
    intro R hR
    have hMR : M < R := (le_max_left M N).trans_lt hR
    have hNR : N < R := (le_max_right M N).trans_lt hR
    have hrigid := aggregatePresentationFullRigidity_of_common_pointed_moments
      c z d w m hc hd htransZ htransW hM hN hboundZ hboundW hMR hNR
      hrealZ hrealW hmomentZ hmomentW hm0
    exact congrArg (fun B : ℝ => R * B) hrigid.2.1
  exact ⟨rfl, hrealizeZ, hrealizeW, hfield,
    HTGeometry.confocalHullOfField_eq_of_eqOn hfield⟩

/-- Agreement of two positive Bernstein fields on one open scale interval. -/
def LocalPositiveScaleFieldAgrees (m m' : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ K : ℕ, ∀ x ∈ Set.Ioo a b,
    bernsteinCoefficientPurity (fun r => x ^ r * m r) K =
      bernsteinCoefficientPurity (fun r => x ^ r * m' r) K

/-- **Exact local-field quotient law.**  For admissible presentations, equality on any open
scale window is equivalent to equality of the complete pointed source and of the maximal exterior
confocal hull. -/
theorem localPositiveScaleField_agrees_iff_source_and_maximalHull_eq
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m m' : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    {M N a b : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hab : a < b)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m' n : ℂ) = atomicPowerMoment d w n)
    (hm0 : 0 < m 0) (hm0' : 0 < m' 0) :
    LocalPositiveScaleFieldAgrees m m' a b ↔
      m = m' ∧
        HTGeometry.confocalHullOfField (Set.Ioi (max M N))
            (HTGeometry.confocalUpperField
              (Set.range (atomicAggregateNode c z))) =
          HTGeometry.confocalHullOfField (Set.Ioi (max M N))
            (HTGeometry.confocalUpperField
              (Set.range (atomicAggregateNode d w))) := by
  constructor
  · intro hobs
    have hsel := localPositiveScaleField_selects_maximalConfocalHull
      c z d w m m' hc hd htransZ htransW hM hN hboundZ hboundW hab
      hrealZ hrealW hmomentZ hmomentW hm0 hm0' hobs
    exact ⟨hsel.1, hsel.2.2.2.2⟩
  · rintro ⟨hmm, _hhull⟩
    subst m'
    intro K x hx
    rfl

end

end RHTower
