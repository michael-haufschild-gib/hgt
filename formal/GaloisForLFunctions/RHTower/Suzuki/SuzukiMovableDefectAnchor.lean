import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEdgeCayleyUniversality

/-!
# Suzuki movable-defect-anchor selection

Suzuki's deficiency points may be based at `±ic`, producing the literal source pair
`exp (±c x)`.  If the projection of that source onto the finite-aperture bottom eigenspace has a
first nonzero Taylor coefficient of definite reflection parity, the opposite parity is lower
order as `c ↓ 0`.  The corresponding projective defect angle therefore tends to `+1` or `-1`.

The operator realization of Suzuki's unbounded restricted-Weil operator is not yet present in the
Lean corpus.  This module formalizes the exact analytic consumer of its Hilbert-valued Taylor
expansion: scaled parity energies, phase-invariant purification, every strict threshold below one,
and stability under the subsequent ground-pole limit.  There are no axioms, RH assumptions, or
computations.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## One fixed interior anchor for a countable cofinal family -/

/-- **Countable bad-anchor avoidance.**  A countable family of countable symmetric zero sets
cannot exhaust the positive defect anchors.  In the Suzuki application each set is the positive
real zero divisor of the bilateral Laplace transform of one compactly supported pure-parity
ground vector. -/
theorem exists_fixed_positive_anchor_avoiding_countable_zeroSets
    (badAnchor : ℕ → Set ℝ)
    (hcountable : ∀ n, (badAnchor n).Countable)
    (hsymmetric : ∀ n c, -c ∈ badAnchor n ↔ c ∈ badAnchor n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, c ∉ badAnchor n := by
  let bad : Set ℝ := {0} ∪ ⋃ n, badAnchor n
  have hbadCountable : bad.Countable := by
    exact (Set.countable_singleton 0).union (Set.countable_iUnion hcountable)
  have hbadNe : bad ≠ Set.univ := by
    intro hbad
    have huniv : (Set.univ : Set ℝ).Countable := by
      rwa [← hbad]
    exact Set.not_countable_univ huniv
  obtain ⟨r, hr⟩ := (Set.ne_univ_iff_exists_notMem bad).mp hbadNe
  have hr0 : r ≠ 0 := by
    intro hrzero
    apply hr
    simp [bad, hrzero]
  refine ⟨|r|, abs_pos.mpr hr0, ?_⟩
  intro n habs
  apply hr
  refine Set.mem_union_right {0} ?_
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  by_cases hrnonneg : 0 ≤ r
  · simpa [abs_of_nonneg hrnonneg] using habs
  · have hrneg : r < 0 := lt_of_not_ge hrnonneg
    have hneg : -r ∈ badAnchor n := by
      simpa [abs_of_neg hrneg] using habs
    exact (hsymmetric n r).mp hneg

section ReflectionPolarization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Signed reflection expectation of a nonzero projected source.  Totalization at the zero vector
is harmless because every selection theorem carries a nonzero leading coefficient. -/
def suzukiReflectionPolarization (J : V →L[ℝ] V) (v : V) : ℝ :=
  inner ℝ (J v) v / inner ℝ v v

/-- Reflection polarization is unchanged by a nonzero real rescaling of the source vector. -/
theorem suzukiReflectionPolarization_smul (J : V →L[ℝ] V) (scale : ℝ) (v : V)
    (hscale : scale ≠ 0) :
    suzukiReflectionPolarization J (scale • v) =
      suzukiReflectionPolarization J v := by
  rw [suzukiReflectionPolarization, suzukiReflectionPolarization, map_smul,
    inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  field_simp [hscale]

/-- **Hilbert-valued first-visible-moment theorem.**  If a rescaled projected source converges to
a nonzero reflection eigenvector, its signed reflection expectation converges to that parity.
For Suzuki, the input is the Taylor law
`c⁻ᵐ P_a(exp(cX)) → P_a(X^m)/m!`. -/
theorem tendsto_suzukiReflectionPolarization_of_scaled_source
    {ι : Type*} {l : Filter ι} {scale : ι → ℝ} {source : ι → V}
    {leading : V} {parity : ℝ} (J : V →L[ℝ] V)
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (hsource : Tendsto (fun i => scale i • source i) l (𝓝 leading))
    (hleading : leading ≠ 0) (hparity : J leading = parity • leading) :
    Tendsto (fun i => suzukiReflectionPolarization J (source i)) l (𝓝 parity) := by
  have hJ : Tendsto (fun i => J (scale i • source i)) l (𝓝 (J leading)) :=
    J.continuous.continuousAt.tendsto.comp hsource
  have hnum := hJ.inner (𝕜 := ℝ) hsource
  have hden := hsource.inner (𝕜 := ℝ) hsource
  have hinner : inner ℝ leading leading ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    positivity
  have hscaled : Tendsto
      (fun i => suzukiReflectionPolarization J (scale i • source i)) l
      (𝓝 parity) := by
    have hquot := hnum.div hden hinner
    rw [hparity, inner_smul_left] at hquot
    simp only [starRingEnd_apply, star_trivial] at hquot
    have hvalue : parity * inner ℝ leading leading / inner ℝ leading leading = parity := by
      exact mul_div_cancel_right₀ parity hinner
    rw [hvalue] at hquot
    exact hquot
  apply hscaled.congr'
  filter_upwards [hscale] with i hi
  exact suzukiReflectionPolarization_smul J (scale i) (source i) hi

/-- The phase-invariant reflection expectation tends to one for either pure parity. -/
theorem tendsto_abs_suzukiReflectionPolarization_of_scaled_source
    {ι : Type*} {l : Filter ι} {scale : ι → ℝ} {source : ι → V}
    {leading : V} {parity : ℝ} (J : V →L[ℝ] V)
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (hsource : Tendsto (fun i => scale i • source i) l (𝓝 leading))
    (hleading : leading ≠ 0) (hparity : J leading = parity • leading)
    (habs : |parity| = 1) :
    Tendsto (fun i => |suzukiReflectionPolarization J (source i)|) l (𝓝 1) := by
  have hsigned := tendsto_suzukiReflectionPolarization_of_scaled_source
    J hscale hsource hleading hparity
  simpa [habs] using hsigned.abs

/-- Every strict projective wall below one is eventually crossed by a source whose first visible
scaled moment has pure reflection parity. -/
theorem eventually_lt_abs_suzukiReflectionPolarization_of_scaled_source
    {ι : Type*} {l : Filter ι} {scale : ι → ℝ} {source : ι → V}
    {leading : V} {parity kappa : ℝ} (J : V →L[ℝ] V)
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (hsource : Tendsto (fun i => scale i • source i) l (𝓝 leading))
    (hleading : leading ≠ 0) (hparity : J leading = parity • leading)
    (habs : |parity| = 1) (hkappa : kappa < 1) :
    ∀ᶠ i in l, kappa < |suzukiReflectionPolarization J (source i)| := by
  exact (tendsto_abs_suzukiReflectionPolarization_of_scaled_source
    J hscale hsource hleading hparity habs).eventually (eventually_gt_nhds hkappa)

end ReflectionPolarization

/-- Projectively invariant magnitude of the signed even/odd defect angle.  The modulus is the
nondegeneration datum retained after relabelling a two-angle characteristic family. -/
def suzukiPhaseInvariantDefectAngle (evenEnergy oddEnergy : ℝ) : ℝ :=
  |suzukiDefectAngle evenEnergy oddEnergy|

@[simp] theorem suzukiPhaseInvariantDefectAngle_nonneg (evenEnergy oddEnergy : ℝ) :
    0 ≤ suzukiPhaseInvariantDefectAngle evenEnergy oddEnergy :=
  abs_nonneg _

/-- A common nonzero scale cancels from the signed projective defect. -/
theorem suzukiDefectAngle_mul_left (scale evenEnergy oddEnergy : ℝ)
    (hscale : scale ≠ 0) :
    suzukiDefectAngle (scale * evenEnergy) (scale * oddEnergy) =
      suzukiDefectAngle evenEnergy oddEnergy := by
  rw [suzukiDefectAngle, suzukiDefectAngle]
  have hnum : scale * evenEnergy - scale * oddEnergy =
      scale * (evenEnergy - oddEnergy) := by ring
  have hden : scale * evenEnergy + scale * oddEnergy =
      scale * (evenEnergy + oddEnergy) := by ring
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hscale

/-- A common nonzero scale also cancels from the phase-invariant defect. -/
theorem suzukiPhaseInvariantDefectAngle_mul_left (scale evenEnergy oddEnergy : ℝ)
    (hscale : scale ≠ 0) :
    suzukiPhaseInvariantDefectAngle (scale * evenEnergy) (scale * oddEnergy) =
      suzukiPhaseInvariantDefectAngle evenEnergy oddEnergy := by
  rw [suzukiPhaseInvariantDefectAngle, suzukiPhaseInvariantDefectAngle,
    suzukiDefectAngle_mul_left scale evenEnergy oddEnergy hscale]

/-- **Scaled parity-energy limit.**  Any common blow-up or vanishing scale may be removed before
taking the projective defect limit.  This is the exact two-stage consumer for both a small-anchor
Taylor scale and a ground-pole scale. -/
theorem tendsto_suzukiDefectAngle_of_scaled_energies
    {ι : Type*} {l : Filter ι}
    {scale evenEnergy oddEnergy : ι → ℝ} {evenLimit oddLimit : ℝ}
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (heven : Tendsto (fun i => scale i * evenEnergy i) l (𝓝 evenLimit))
    (hodd : Tendsto (fun i => scale i * oddEnergy i) l (𝓝 oddLimit))
    (hsum : evenLimit + oddLimit ≠ 0) :
    Tendsto (fun i => suzukiDefectAngle (evenEnergy i) (oddEnergy i)) l
      (𝓝 ((evenLimit - oddLimit) / (evenLimit + oddLimit))) := by
  have hscaled :
      Tendsto
        (fun i => suzukiDefectAngle
          (scale i * evenEnergy i) (scale i * oddEnergy i)) l
        (𝓝 ((evenLimit - oddLimit) / (evenLimit + oddLimit))) := by
    change Tendsto
      (((fun i => scale i * evenEnergy i) - (fun i => scale i * oddEnergy i)) /
        ((fun i => scale i * evenEnergy i) + (fun i => scale i * oddEnergy i))) l
      (𝓝 ((evenLimit - oddLimit) / (evenLimit + oddLimit)))
    exact (heven.sub hodd).div (heven.add hodd) hsum
  apply hscaled.congr'
  filter_upwards [hscale] with i hi
  exact suzukiDefectAngle_mul_left (scale i) (evenEnergy i) (oddEnergy i) hi

/-- If the even energy has a positive leading coefficient and the odd energy is lower order, the
signed defect tends to pure even parity. -/
theorem tendsto_suzukiDefectAngle_one_of_scaled_even_dominant
    {ι : Type*} {l : Filter ι}
    {scale evenEnergy oddEnergy : ι → ℝ} {leading : ℝ}
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (hleading : 0 < leading)
    (heven : Tendsto (fun i => scale i * evenEnergy i) l (𝓝 leading))
    (hodd : Tendsto (fun i => scale i * oddEnergy i) l (𝓝 0)) :
    Tendsto (fun i => suzukiDefectAngle (evenEnergy i) (oddEnergy i)) l (𝓝 1) := by
  simpa [div_self hleading.ne'] using tendsto_suzukiDefectAngle_of_scaled_energies
    hscale heven hodd (by positivity : leading + 0 ≠ 0)

/-- If the odd energy has a positive leading coefficient and the even energy is lower order, the
signed defect tends to pure odd parity. -/
theorem tendsto_suzukiDefectAngle_neg_one_of_scaled_odd_dominant
    {ι : Type*} {l : Filter ι}
    {scale evenEnergy oddEnergy : ι → ℝ} {leading : ℝ}
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (hleading : 0 < leading)
    (heven : Tendsto (fun i => scale i * evenEnergy i) l (𝓝 0))
    (hodd : Tendsto (fun i => scale i * oddEnergy i) l (𝓝 leading)) :
    Tendsto (fun i => suzukiDefectAngle (evenEnergy i) (oddEnergy i)) l (𝓝 (-1)) := by
  have h := tendsto_suzukiDefectAngle_of_scaled_energies
    hscale heven hodd (by positivity : 0 + leading ≠ 0)
  have hvalue : (-leading) / leading = (-1 : ℝ) := by
    field_simp
  simpa [hvalue] using h

/-- Both possible first visible parities give the same projective nondegeneration limit. -/
theorem tendsto_suzukiPhaseInvariantDefectAngle_one_of_scaled_dominant
    {ι : Type*} {l : Filter ι}
    {scale evenEnergy oddEnergy : ι → ℝ} {leading : ℝ}
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (hleading : 0 < leading)
    (hdominant :
      (Tendsto (fun i => scale i * evenEnergy i) l (𝓝 leading) ∧
        Tendsto (fun i => scale i * oddEnergy i) l (𝓝 0)) ∨
      (Tendsto (fun i => scale i * evenEnergy i) l (𝓝 0) ∧
        Tendsto (fun i => scale i * oddEnergy i) l (𝓝 leading))) :
    Tendsto (fun i => suzukiPhaseInvariantDefectAngle (evenEnergy i) (oddEnergy i))
      l (𝓝 1) := by
  rcases hdominant with hEven | hOdd
  · have hsigned := tendsto_suzukiDefectAngle_one_of_scaled_even_dominant
      hscale hleading hEven.1 hEven.2
    simpa [suzukiPhaseInvariantDefectAngle] using hsigned.abs
  · have hsigned := tendsto_suzukiDefectAngle_neg_one_of_scaled_odd_dominant
      hscale hleading hOdd.1 hOdd.2
    simpa [suzukiPhaseInvariantDefectAngle] using hsigned.abs

/-- **Movable-anchor threshold crossing.**  Parity purification crosses every prescribed strict
projective wall below one, including the Xi first-defect wall. -/
theorem eventually_lt_suzukiPhaseInvariantDefectAngle_of_scaled_dominant
    {ι : Type*} {l : Filter ι}
    {scale evenEnergy oddEnergy : ι → ℝ} {leading kappa : ℝ}
    (hscale : ∀ᶠ i in l, scale i ≠ 0)
    (hleading : 0 < leading) (hkappa : kappa < 1)
    (hdominant :
      (Tendsto (fun i => scale i * evenEnergy i) l (𝓝 leading) ∧
        Tendsto (fun i => scale i * oddEnergy i) l (𝓝 0)) ∨
      (Tendsto (fun i => scale i * evenEnergy i) l (𝓝 0) ∧
        Tendsto (fun i => scale i * oddEnergy i) l (𝓝 leading))) :
    ∀ᶠ i in l, kappa <
      suzukiPhaseInvariantDefectAngle (evenEnergy i) (oddEnergy i) := by
  exact (tendsto_suzukiPhaseInvariantDefectAngle_one_of_scaled_dominant
    hscale hleading hdominant).eventually (eventually_gt_nhds hkappa)

/-- A later ground-pole approximation preserves any already-selected phase-invariant bottom
polarization. -/
theorem tendsto_suzukiPhaseInvariantDefectAngle_of_groundPole
    {ι : Type*} {l : Filter ι}
    {poleScale evenEnergy oddEnergy : ι → ℝ} {evenBottom oddBottom : ℝ}
    (hscale : ∀ᶠ i in l, poleScale i ≠ 0)
    (heven : Tendsto (fun i => poleScale i * evenEnergy i) l (𝓝 evenBottom))
    (hodd : Tendsto (fun i => poleScale i * oddEnergy i) l (𝓝 oddBottom))
    (hsum : evenBottom + oddBottom ≠ 0) :
    Tendsto
      (fun i => suzukiPhaseInvariantDefectAngle (evenEnergy i) (oddEnergy i)) l
      (𝓝 |(evenBottom - oddBottom) / (evenBottom + oddBottom)|) := by
  have hsigned := tendsto_suzukiDefectAngle_of_scaled_energies
    hscale heven hodd hsum
  simpa [suzukiPhaseInvariantDefectAngle] using hsigned.abs

/-- If a bottom projection already lies beyond a strict projective wall, sufficiently close
admissible ground shifts remain beyond the same wall. -/
theorem eventually_lt_suzukiPhaseInvariantDefectAngle_of_groundPole
    {ι : Type*} {l : Filter ι}
    {poleScale evenEnergy oddEnergy : ι → ℝ}
    {evenBottom oddBottom kappa : ℝ}
    (hscale : ∀ᶠ i in l, poleScale i ≠ 0)
    (heven : Tendsto (fun i => poleScale i * evenEnergy i) l (𝓝 evenBottom))
    (hodd : Tendsto (fun i => poleScale i * oddEnergy i) l (𝓝 oddBottom))
    (hsum : evenBottom + oddBottom ≠ 0)
    (hwall : kappa < |(evenBottom - oddBottom) / (evenBottom + oddBottom)|) :
    ∀ᶠ i in l, kappa <
      suzukiPhaseInvariantDefectAngle (evenEnergy i) (oddEnergy i) := by
  exact (tendsto_suzukiPhaseInvariantDefectAngle_of_groundPole
    hscale heven hodd hsum).eventually (eventually_gt_nhds hwall)

end GaloisForLFunctions.RHTower
