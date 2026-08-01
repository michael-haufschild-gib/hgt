import GaloisForLFunctions.RHTower.SuzukiEdgeDataInterface
import GaloisForLFunctions.HTGeometry.CompactIntervalL2Pairing
import GaloisForLFunctions.RHTower.IntervalL2ResolventCoordinate

/-!
# Edge data on `L²` of the interval, with pairing vectors that are named weights

The edge-data interface is satisfiable by free vectors, so satisfying it proves nothing on its own.
This file exhibits edge data whose pairing vectors are *not* free: they are the `L²` elements of the
explicit edge numerator and denominator weights, and their value equations are the integral
identities proved for those weights.

The resolvent coordinate here is the identity, which is admissible for the interface but carries no
resolvent content; what the construction demonstrates is that the two value equations are met by
named weights rather than by a choice.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

/-- The constant function is a nonzero element of `L²` of a nondegenerate interval. -/
theorem oneIntervalL2_ne_zero (a : ℝ) (ha : 0 < a) : oneIntervalL2 a ≠ 0 := by
  intro h
  have hcoe : ((oneIntervalL2 a : IntervalL2 a) : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Icc (-a) a)] 0 := by
    rw [h]
    exact Lp.coeFn_zero ℂ 2 _
  have hone : ((oneIntervalL2 a : IntervalL2 a) : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Icc (-a) a)] (fun _ : ℝ => (1 : ℂ)) :=
    (memLp_two_of_continuous a (continuous_const : Continuous (fun _ : ℝ => (1 : ℂ)))).coeFn_toLp
  have h1 : (fun _ : ℝ => (1 : ℂ)) =ᵐ[volume.restrict (Set.Icc (-a) a)] 0 :=
    hone.symm.trans hcoe
  have h3 := ae_iff.mp h1
  simp only [Pi.zero_apply, one_ne_zero, not_false_eq_true, Set.setOf_true] at h3
  rw [Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.ofReal_eq_zero] at h3
  linarith

theorem nontrivial_intervalL2 (a : ℝ) (ha : 0 < a) : Nontrivial (IntervalL2 a) :=
  ⟨⟨oneIntervalL2 a, 0, oneIntervalL2_ne_zero a ha⟩⟩

/-- **The numerator pairing vector and its value.**  Scaling by `-i` turns the endpoint-atom value
into the form the edge data requires. -/
theorem inner_edgeNumeratorVector_one (a : ℝ) (ha : 0 < a) {H H' : ℝ → ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x) (hH'c : Continuous H') (hH0 : H 0 = 0) :
    inner ℂ ((-Complex.I) • toIntervalL2 a (continuous_edgeNumeratorWeightC hH hH'c a))
        (oneIntervalL2 a)
      = Complex.I * (2 * ((Real.cosh a : ℝ) : ℂ)) * ((H (2 * a) : ℝ) : ℂ) := by
  rw [inner_smul_left, inner_edgeNumeratorWeight_one a ha.le hH hH'c hH0]
  simp only [map_neg, Complex.conj_I, neg_neg]
  push_cast
  ring

/-- **The denominator pairing vector and its value.** -/
theorem inner_edgeDenominatorVector_one (a : ℝ) (ha : 0 < a) :
    inner ℂ (toIntervalL2 a continuous_edgeDenominatorWeight) (oneIntervalL2 a)
      = 4 * ((a : ℝ) : ℂ) * ((Real.cosh a : ℝ) : ℂ) := by
  rw [inner_edgeDenominatorWeight_one a ha.le]
  push_cast
  ring

/-- **Edge data whose pairing vectors are named weights.**  The numerator and denominator vectors
are the `L²` elements of `edgeNumeratorWeight` and `edgeDenominatorWeight`, and the two value
equations hold because of the integral identities proved for those weights — not by choice.

The resolvent coordinate is the identity, which is admissible but carries no resolvent content: the
point is the provenance of the pairing vectors. -/
theorem nonempty_intervalEdgeData (a : ℝ) (ha : 0 < a) {H H' : ℝ → ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x) (hH'c : Continuous H') (hH0 : H 0 = 0) :
    Nonempty (@SuzukiEdgeData (IntervalL2 a) _ _ _ (nontrivial_intervalL2 a ha)) := by
  letI := nontrivial_intervalL2 a ha
  exact ⟨{ B := 1
           selfAdjoint := IsSelfAdjoint.one _
           injective := fun x y hxy => by simpa using hxy
           specBound := 1
           spectrum_subset := by
             intro r hr
             rw [spectrum.one_eq] at hr
             simp only [Set.mem_singleton_iff] at hr
             subst hr
             exact ⟨zero_le_one, le_rfl⟩
           v := oneIntervalL2 a
           gnum := (-Complex.I) • toIntervalL2 a (continuous_edgeNumeratorWeightC hH hH'c a)
           gden := toIntervalL2 a continuous_edgeDenominatorWeight
           aperture := a
           aperture_ne := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
           edgeWeight := ((Real.cosh a : ℝ) : ℂ)
           edgeWeight_ne := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos a))
           primitiveValue := ((H (2 * a) : ℝ) : ℂ)
           num_value := inner_edgeNumeratorVector_one a ha hH hH'c hH0
           den_value := inner_edgeDenominatorVector_one a ha }⟩

/-! ## Edge data with a compact resolvent coordinate

The earlier construction used the identity as the resolvent coordinate, which the interface admits
but which carries no resolvent content.  With a compact, self-adjoint, injective coordinate now
available on the same space, the identity can be replaced: this edge data has a genuine resolvent
coordinate *and* pairing vectors that are named weights. -/

/-- **Edge data on `L²[-a,a]` with a compact resolvent coordinate and named pairing weights.**  The
coordinate is the harmonic multiplier along the polynomial Hilbert basis — compact, self-adjoint,
injective, with spectrum in `Icc 0 M` — and the pairing vectors are the `L²` elements of the edge
numerator and denominator weights, whose values are the integral identities. -/
theorem nonempty_intervalEdgeData_compact (a : ℝ) (ha : 0 < a) {H H' : ℝ → ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x) (hH'c : Continuous H') (hH0 : H 0 = 0) :
    Nonempty (@SuzukiEdgeData (IntervalL2 a) _ _ _ (nontrivial_intervalL2 a ha)) := by
  letI := nontrivial_intervalL2 a ha
  exact ⟨{ B := intervalHarmonicCoordinate a ha
           selfAdjoint := isSelfAdjoint_intervalHarmonicCoordinate a ha
           injective := injective_intervalHarmonicCoordinate a ha
           specBound := ‖_root_.RHTower.diagonalOperator
             (fun n => ((harmonicMultiplier n : ℝ) : ℂ)) norm_harmonicMultiplier_le‖
           spectrum_subset := spectrum_intervalHarmonicCoordinate_subset a ha
           v := oneIntervalL2 a
           gnum := (-Complex.I) • toIntervalL2 a (continuous_edgeNumeratorWeightC hH hH'c a)
           gden := toIntervalL2 a continuous_edgeDenominatorWeight
           aperture := a
           aperture_ne := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
           edgeWeight := ((Real.cosh a : ℝ) : ℂ)
           edgeWeight_ne := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos a))
           primitiveValue := ((H (2 * a) : ℝ) : ℂ)
           num_value := inner_edgeNumeratorVector_one a ha hH hH'c hH0
           den_value := inner_edgeDenominatorVector_one a ha }⟩

end GaloisForLFunctions.RHTower
