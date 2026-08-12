import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierAllContactSourceWallResidue

/-!
# Raw Christoffel source walls cannot form a finite positive trace

The adaptive source wall contains a universal newborn-edge dimension tax.  In every positive
shifted-Xi moment chamber its degree-`n` value is strictly larger than `(n+1)/16`.  Therefore a
fully positive infinite moment tower makes the raw wall sequence diverge to infinity rather than
form a summable positive diagonal.

The forced counterterm is regular in mass.  Subtracting it leaves every exact all-contact
strict-frontier residue unchanged.  Thus any viable common cross-degree action must be
counterterm-renormalized before degree reporting; the renormalization does not erase the local
arithmetic source obstruction.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

/-- Universal newborn-edge counterterm in source-wall degree `n`. -/
def xiShiftedChristoffelSourceWallDimensionTax (n : ℕ) : ℝ :=
  (n + 1 : ℝ) / 16

/-- Counterterm-renormalized actual adaptive Christoffel source wall. -/
def xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionChristoffelSourceWall y n -
    xiShiftedChristoffelSourceWallDimensionTax n

/-- Exact Jacobi-coordinate form of the actual source wall inside a positive finite chamber. -/
theorem xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_jacobiEnergy_div_beta
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionChristoffelSourceWall y n =
      HTGeometry.adaptiveOrthoJacobiEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) n /
        (16 * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 < HTGeometry.monicOrthoNormSq s n :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hnext : 0 < HTGeometry.monicOrthoNormSq s (n + 1) :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hheadN : (HTGeometry.momentHankelMatrix s n).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hheadNext : (HTGeometry.momentHankelMatrix s (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionChristoffelSourceWall,
    xiShiftedCanonicalAdmissionAdaptiveShear_eq_norm_mul_jacobiEnergy hn hH,
    xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hheadN,
    xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hheadNext]
  change HTGeometry.monicOrthoNormSq s n *
      HTGeometry.adaptiveOrthoJacobiEnergy s n /
        (16 * HTGeometry.monicOrthoNormSq s (n + 1)) =
    HTGeometry.adaptiveOrthoJacobiEnergy s n /
      (16 * HTGeometry.monicOrthoBeta s (n + 1))
  simp only [HTGeometry.monicOrthoBeta]
  field_simp [ne_of_gt hnorm, ne_of_gt hnext]

/-- The completed-square energy strictly exceeds the next, newborn Jacobi edge. -/
theorem adaptiveOrthoJacobiEnergy_gt_succ_mul_nextBeta
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) <
      HTGeometry.adaptiveOrthoJacobiEnergy s n := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha s j +
          HTGeometry.monicOrthoAlpha s n / 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1) *
        HTGeometry.monicOrthoAlpha s n ^ 2 := by positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hcurrent :
      0 < (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n :=
    mul_pos (by positivity)
      (HTGeometry.monicOrthoBeta_pos_below h hn (by omega))
  unfold HTGeometry.adaptiveOrthoJacobiEnergy
  nlinarith

/-- **Universal dimension tax.** Every positive finite moment chamber makes the raw adaptive
source wall strictly larger than `(n+1)/16`. -/
theorem xiShiftedChristoffelSourceWallDimensionTax_lt
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedChristoffelSourceWallDimensionTax n <
      xiShiftedCanonicalAdmissionChristoffelSourceWall y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have henergy := adaptiveOrthoJacobiEnergy_gt_succ_mul_nextBeta
    hbelow hn le_rfl
  have hbeta : 0 < HTGeometry.monicOrthoBeta s (n + 1) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  rw [xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_jacobiEnergy_div_beta
    hn hH]
  unfold xiShiftedChristoffelSourceWallDimensionTax
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 16)
    (mul_pos (by positivity) hbeta)).2
  field_simp [ne_of_gt hbeta]
  nlinarith

/-- The counterterm-renormalized wall remains strictly positive throughout every positive finite
moment chamber. -/
theorem xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall_pos
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall y n := by
  rw [xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall]
  exact sub_pos.mpr (xiShiftedChristoffelSourceWallDimensionTax_lt hn hH)

/-- **Raw positive-trace no-go.** If every finite shifted-Xi moment block at one mass is positive
definite, raw source walls diverge with degree. -/
theorem tendsto_xiShiftedCanonicalAdmissionChristoffelSourceWall_atTop
    {y : ℝ}
    (hH : ∀ N : ℕ, (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) N).PosDef) :
    Tendsto (fun n : ℕ =>
      xiShiftedCanonicalAdmissionChristoffelSourceWall y (n + 1))
      atTop atTop := by
  have hlower : Tendsto (fun n : ℕ => (n : ℝ) / 16) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  exact Filter.tendsto_atTop_mono
    (f := fun n : ℕ => (n : ℝ) / 16)
    (g := fun n : ℕ =>
      xiShiftedCanonicalAdmissionChristoffelSourceWall y (n + 1))
    (fun n => by
      have htax := xiShiftedChristoffelSourceWallDimensionTax_lt
        (y := y) (n := n + 1) (by omega) (hH (n + 3))
      unfold xiShiftedChristoffelSourceWallDimensionTax at htax
      norm_num [Nat.cast_add, Nat.cast_one] at htax
      have hlow : (n : ℝ) / 16 ≤ ((n : ℝ) + 1 + 1) / 16 := by
        linarith
      exact hlow.trans htax.le)
    hlower

/-- Raw wall values cannot be a summable diagonal in a fully positive moment tower. -/
theorem not_summable_xiShiftedCanonicalAdmissionChristoffelSourceWall
    {y : ℝ}
    (hH : ∀ N : ℕ, (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) N).PosDef) :
    ¬Summable (fun n : ℕ =>
      xiShiftedCanonicalAdmissionChristoffelSourceWall y (n + 1)) := by
  intro hsum
  have hsmall := hsum.tendsto_atTop_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  let m := max N 16
  have hsmallM := hN m (le_max_left N 16)
  have htax := xiShiftedChristoffelSourceWallDimensionTax_lt
    (y := y) (n := m + 1) (by omega) (hH (m + 3))
  unfold xiShiftedChristoffelSourceWallDimensionTax at htax
  norm_num [Nat.cast_add, Nat.cast_one] at htax
  have hm : (16 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_max_right N 16)
  linarith

/-- Intrinsic contact-order scaling of the counterterm-renormalized actual wall. -/
def xiShiftedStrictFrontierAllContactScaledRenormalizedSourceWall
    (n d : ℕ) (u : ℝ) : ℝ :=
  u ^ d * xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall
    (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1)

/-- **Residue-stable renormalization.** Subtracting the forced dimension tax leaves the exact
finite positive all-contact strict-frontier residue unchanged. -/
theorem tendsto_xiShiftedStrictFrontierAllContactScaledRenormalizedSourceWall
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    Tendsto (xiShiftedStrictFrontierAllContactScaledRenormalizedSourceWall n d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) := by
  have hwall := tendsto_xiShiftedStrictFrontierAllContactScaledSourceWall
    hne hstrict hd hzero hsigned
  have htaxFull : Tendsto
      (fun u : ℝ => u ^ d * xiShiftedChristoffelSourceWallDimensionTax (n + 1))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hp : Tendsto (fun u : ℝ => u ^ d) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun u : ℝ => u) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
      simpa [Nat.ne_of_gt hd] using (hid.pow d)
    simpa using hp.mul_const (xiShiftedChristoffelSourceWallDimensionTax (n + 1))
  have htax : Tendsto
      (fun u : ℝ => u ^ d * xiShiftedChristoffelSourceWallDimensionTax (n + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    htaxFull.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto
      (fun u : ℝ =>
        xiShiftedStrictFrontierAllContactScaledSourceWall n d u -
          u ^ d * xiShiftedChristoffelSourceWallDimensionTax (n + 1))
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) := by
    simpa using hwall.sub htax
  exact hsub.congr' (Filter.Eventually.of_forall fun u => by
    rw [xiShiftedStrictFrontierAllContactScaledRenormalizedSourceWall,
      xiShiftedStrictFrontierAllContactScaledSourceWall,
      xiShiftedCanonicalAdmissionRenormalizedChristoffelSourceWall]
    ring)

end

end RHTower
