import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography
import GaloisForLFunctions.HTGeometry.SourceLinearClosedRelationSplitting

/-!
# Closed-relation PW endpoint tomography

The physical PW endpoint nodes `q_j = exp(-(j+1))` define geometric packets
`v_j(n)=q_j^(n+1)` in complex `ℓ²`.  Their complex span is norm-dense: orthogonality gives a
bounded complex power series vanishing on the node sequence, and coefficient peeling kills every
coordinate.

Consequently, any closed linear relation containing `(v_j,0)` for every physical scale is
source-nonselective: membership depends only on its vertical fibre.  If single-valued, it is exactly
the everywhere-defined zero graph.  This removes the closed unbounded/multivalued/singular
linear-response escape from PW endpoint darkness; no boundedness or coercivity premise is used.

`[NEW] [PW ENDPOINT TOTALITY] [CLOSED RELATION RIGIDITY]
[UNBOUNDED/SINGULAR ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Filter Topology
open scoped InnerProductSpace BigOperators

namespace RHTower

noncomputable section

/-- Complex `ℓ²` source space for PW grade packets. -/
abbrev SchwarzschildParikhWilczekEndpointHilbert := lp (fun _ : ℕ => ℂ) 2

private theorem schwarzschildParikhWilczekEndpointPacket_memℓp (j : ℕ) :
    Memℓp
      (fun n : ℕ =>
        (schwarzschildParikhWilczekEndpointTomographyNode j : ℂ) ^ n) 2 := by
  let q := schwarzschildParikhWilczekEndpointTomographyNode j
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    change Real.exp (-((j : ℝ) + 1)) < 1
    rw [Real.exp_lt_one_iff]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  apply memℓp_gen
  have hgeom : Summable (fun n : ℕ => (q ^ 2) ^ n) :=
    summable_geometric_of_lt_one (sq_nonneg q) (by nlinarith)
  refine hgeom.congr fun n => ?_
  simp only [ENNReal.toReal_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    show |schwarzschildParikhWilczekEndpointTomographyNode j| = q by
      simpa [q] using abs_of_pos hq0]
  have hpn : (q ^ 2) ^ n = (q ^ n) ^ 2 := by
    calc
      (q ^ 2) ^ n = q ^ (2 * n) := (pow_mul q 2 n).symm
      _ = q ^ (n * 2) := by rw [Nat.mul_comm]
      _ = (q ^ n) ^ 2 := pow_mul q n 2
  simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using hpn

private def schwarzschildParikhWilczekEndpointKernel (j : ℕ) :
    SchwarzschildParikhWilczekEndpointHilbert :=
  ⟨fun n =>
    (schwarzschildParikhWilczekEndpointTomographyNode j : ℂ) ^ n,
    schwarzschildParikhWilczekEndpointPacket_memℓp j⟩

/-- Geometric endpoint packet at the `j`-th physical PW scale. -/
def schwarzschildParikhWilczekEndpointPacket (j : ℕ) :
    SchwarzschildParikhWilczekEndpointHilbert :=
  (schwarzschildParikhWilczekEndpointTomographyNode j : ℂ) •
    schwarzschildParikhWilczekEndpointKernel j

@[simp] theorem schwarzschildParikhWilczekEndpointPacket_apply (j n : ℕ) :
    schwarzschildParikhWilczekEndpointPacket j n =
      (schwarzschildParikhWilczekEndpointTomographyNode j : ℂ) ^ (n + 1) := by
  change (schwarzschildParikhWilczekEndpointTomographyNode j : ℂ) *
      (schwarzschildParikhWilczekEndpointTomographyNode j : ℂ) ^ n = _
  rw [mul_comm, pow_succ]

private theorem summable_complexPowerSeries_of_bounded
    {c : ℕ → ℂ} {C t : ℝ} (hbound : ∀ n, ‖c n‖ ≤ C) (ht : |t| < 1) :
    Summable fun n : ℕ => c n * (t : ℂ) ^ n := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => C * |t| ^ n)
    ((summable_geometric_of_lt_one (abs_nonneg t) ht).mul_left C) ?_
  intro n
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)

/-- Complex bounded power-series uniqueness on a positive zero sequence. -/
theorem boundedComplexPowerSeries_coeff_eq_zero_of_zeroSequence
    {c : ℕ → ℂ} {C : ℝ} {q : ℕ → ℝ}
    (hbound : ∀ n, ‖c n‖ ≤ C)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, |q j| < 1)
    (hqlim : Tendsto q atTop (𝓝 0))
    (hzero : ∀ j, ∑' n : ℕ, c n * (q j : ℂ) ^ n = 0) :
    ∀ n, c n = 0 := by
  have hreBound : ∀ n, |(c n).re| ≤ C := fun n =>
    (Complex.abs_re_le_norm (c n)).trans (hbound n)
  have himBound : ∀ n, |(c n).im| ≤ C := fun n =>
    (Complex.abs_im_le_norm (c n)).trans (hbound n)
  have hreZero : ∀ j, ∑' n : ℕ, (c n).re * q j ^ n = 0 := by
    intro j
    have hs := summable_complexPowerSeries_of_bounded hbound (hq1 j)
    have hm := Complex.reCLM.map_tsum hs
    rw [hzero j] at hm
    calc
      (∑' n : ℕ, (c n).re * q j ^ n) =
          ∑' n : ℕ, (c n * (q j : ℂ) ^ n).re := by
            apply tsum_congr
            intro n
            have hpow : (q j : ℂ) ^ n = (q j ^ n : ℝ) := by norm_cast
            rw [hpow, Complex.mul_re]
            change (c n).re * q j ^ n = (c n).re * q j ^ n - (c n).im * 0
            ring
      _ = 0 := hm.symm
  have himZero : ∀ j, ∑' n : ℕ, (c n).im * q j ^ n = 0 := by
    intro j
    have hs := summable_complexPowerSeries_of_bounded hbound (hq1 j)
    have hm := Complex.imCLM.map_tsum hs
    rw [hzero j] at hm
    calc
      (∑' n : ℕ, (c n).im * q j ^ n) =
          ∑' n : ℕ, (c n * (q j : ℂ) ^ n).im := by
            apply tsum_congr
            intro n
            have hpow : (q j : ℂ) ^ n = (q j ^ n : ℝ) := by norm_cast
            rw [hpow, Complex.mul_im]
            change (c n).im * q j ^ n = (c n).re * 0 + (c n).im * q j ^ n
            ring
      _ = 0 := hm.symm
  have hre := boundedPowerSeries_coeff_eq_zero_of_zeroSequence
    hreBound hq0 hq1 hqlim hreZero
  have him := boundedPowerSeries_coeff_eq_zero_of_zeroSequence
    himBound hq0 hq1 hqlim himZero
  intro n
  exact Complex.ext (hre n) (him n)

/-- Complex span of all physical PW endpoint packets. -/
def schwarzschildParikhWilczekEndpointPacketSpan :
    Submodule ℂ SchwarzschildParikhWilczekEndpointHilbert :=
  Submodule.span ℂ (Set.range schwarzschildParikhWilczekEndpointPacket)

/-- No nonzero `ℓ²` packet is orthogonal to every physical PW endpoint packet. -/
theorem schwarzschildParikhWilczekEndpointPacketSpan_orthogonal_eq_bot :
    schwarzschildParikhWilczekEndpointPacketSpanᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro h hh
  have hpacket : ∀ j : ℕ,
      inner ℂ (schwarzschildParikhWilczekEndpointPacket j) h = 0 := by
    intro j
    exact (Submodule.mem_orthogonal _ _).mp hh _
      (Submodule.subset_span (Set.mem_range_self j))
  let q : ℕ → ℝ := schwarzschildParikhWilczekEndpointTomographyNode
  have hq0 (j : ℕ) : 0 < q j := Real.exp_pos _
  have hq1 (j : ℕ) : |q j| < 1 := by
    rw [abs_of_pos (hq0 j)]
    change Real.exp (-((j : ℝ) + 1)) < 1
    rw [Real.exp_lt_one_iff]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hzero : ∀ j : ℕ, ∑' n : ℕ, h n * (q j : ℂ) ^ n = 0 := by
    intro j
    have hs : Summable fun n : ℕ => h n * (q j : ℂ) ^ n :=
      summable_complexPowerSeries_of_bounded
        (fun n => lp.norm_apply_le_norm (by norm_num) h n) (hq1 j)
    have hinner := hpacket j
    rw [lp.inner_eq_tsum] at hinner
    have hphysical : ∑' n : ℕ, h n * (q j : ℂ) ^ (n + 1) = 0 := by
      rw [← hinner]
      apply tsum_congr
      intro n
      rw [schwarzschildParikhWilczekEndpointPacket_apply, RCLike.inner_apply']
      change h n * (q j : ℂ) ^ (n + 1) = _
      simp [q]
      ring
    have hfactor : ∑' n : ℕ, h n * (q j : ℂ) ^ (n + 1) =
        (q j : ℂ) * ∑' n : ℕ, h n * (q j : ℂ) ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [pow_succ]
      ring
    rw [hfactor] at hphysical
    exact (mul_eq_zero.mp hphysical).resolve_left
      (Complex.ofReal_ne_zero.mpr (hq0 j).ne')
  have hcoeff := boundedComplexPowerSeries_coeff_eq_zero_of_zeroSequence
    (fun n => lp.norm_apply_le_norm (by norm_num) h n) hq0 hq1
    tendsto_schwarzschildParikhWilczekEndpointTomographyNode_zero hzero
  apply lp.ext
  funext n
  exact hcoeff n

/-- **PW endpoint totality.** Physical endpoint packets at the explicit scales
`epsilon_j = 1/(4(j+1))` have norm-dense complex span in `ℓ²`. -/
theorem dense_schwarzschildParikhWilczekEndpointPacketSpan :
    Dense (schwarzschildParikhWilczekEndpointPacketSpan :
      Set SchwarzschildParikhWilczekEndpointHilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hclosure :=
    Submodule.orthogonal_orthogonal_eq_closure
      schwarzschildParikhWilczekEndpointPacketSpan
  rw [schwarzschildParikhWilczekEndpointPacketSpan_orthogonal_eq_bot,
    Submodule.bot_orthogonal_eq_top] at hclosure
  exact hclosure.symm

open GaloisForLFunctions.HTGeometry

/-- A closed Hilbert relation dark on every physical PW endpoint packet carries no source
information: membership depends only on the vertical output fibre. -/
theorem closedRelation_mem_iff_vertical_mem_of_PWEndpointDark
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (R : Submodule ℂ (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K))
    (hclosed : IsClosed (R : Set (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)))
    (hdark : ∀ j : ℕ, hilbertSumInl (schwarzschildParikhWilczekEndpointPacket j) ∈ R)
    (z : HilbertSum SchwarzschildParikhWilczekEndpointHilbert K) :
    z ∈ R ↔ hilbertSumInr (hilbertSumSnd z) ∈ R := by
  let Z : Submodule ℂ SchwarzschildParikhWilczekEndpointHilbert :=
    R.comap hilbertSumInl.toLinearMap
  have hZclosed : IsClosed (Z : Set SchwarzschildParikhWilczekEndpointHilbert) := by
    change IsClosed ((fun x : SchwarzschildParikhWilczekEndpointHilbert => hilbertSumInl x) ⁻¹'
      (R : Set (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)))
    exact hclosed.preimage hilbertSumInl.continuous
  have hspan : schwarzschildParikhWilczekEndpointPacketSpan ≤ Z := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hdark j
  have hZtop : Z = ⊤ := by
    apply top_unique
    intro x _
    have hclosureSubset : closure
        (schwarzschildParikhWilczekEndpointPacketSpan :
          Set SchwarzschildParikhWilczekEndpointHilbert) ⊆ (Z : Set _) :=
      hZclosed.closure_subset_iff.mpr (SetLike.coe_subset_coe.mpr hspan)
    exact hclosureSubset (dense_schwarzschildParikhWilczekEndpointPacketSpan x)
  have hallzero (x : SchwarzschildParikhWilczekEndpointHilbert) :
      hilbertSumInl x ∈ R := by
    have hx : x ∈ Z := by rw [hZtop]; exact Submodule.mem_top
    exact hx
  constructor
  · intro hz
    have hsub := R.sub_mem hz (hallzero (hilbertSumFst z))
    have heq : z - hilbertSumInl (hilbertSumFst z) =
        hilbertSumInr (hilbertSumSnd z) := by
      apply hilbertSum_ext
      · rw [map_sub, hilbertSumFst_inl, hilbertSumFst_inr, sub_self]
      · rw [map_sub, hilbertSumSnd_inl, hilbertSumSnd_inr, sub_zero]
    rwa [heq] at hsub
  · intro hv
    rw [← hilbertSum_inl_add_inr z]
    exact R.add_mem (hallzero _) hv

/-- Closed multivalued PW endpoint-dark relations are universally source-nonselective. -/
def SchwarzschildParikhWilczekClosedRelationEndpointDarkNonselective : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (R : Submodule ℂ (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)),
    IsClosed (R : Set (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)) →
    (∀ j : ℕ, hilbertSumInl (schwarzschildParikhWilczekEndpointPacket j) ∈ R) →
    ∀ z, z ∈ R ↔ hilbertSumInr (hilbertSumSnd z) ∈ R

/-- **PW closed-relation no-go.** Every closed endpoint-dark linear relation loses all dependence
on its source coordinate, even when it is multivalued. -/
theorem schwarzschildParikhWilczekClosedRelationEndpointDarkNonselective :
    SchwarzschildParikhWilczekClosedRelationEndpointDarkNonselective := by
  intro K _ _ R hclosed hdark z
  exact closedRelation_mem_iff_vertical_mem_of_PWEndpointDark R hclosed hdark z

/-- A closed single-valued Hilbert relation dark on every physical PW endpoint packet is exactly
the everywhere-defined zero graph. -/
theorem closedSingleValuedRelation_mem_iff_output_zero_of_PWEndpointDark
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (R : Submodule ℂ (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K))
    (hclosed : IsClosed (R : Set (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)))
    (hsingle : HilbertRelationSingleValued R)
    (hdark : ∀ j : ℕ, hilbertSumInl (schwarzschildParikhWilczekEndpointPacket j) ∈ R)
    (z : HilbertSum SchwarzschildParikhWilczekEndpointHilbert K) :
    z ∈ R ↔ hilbertSumSnd z = 0 := by
  let Z : Submodule ℂ SchwarzschildParikhWilczekEndpointHilbert :=
    R.comap hilbertSumInl.toLinearMap
  have hZclosed : IsClosed (Z : Set SchwarzschildParikhWilczekEndpointHilbert) := by
    change IsClosed ((fun x : SchwarzschildParikhWilczekEndpointHilbert => hilbertSumInl x) ⁻¹'
      (R : Set (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)))
    exact hclosed.preimage hilbertSumInl.continuous
  have hspan : schwarzschildParikhWilczekEndpointPacketSpan ≤ Z := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hdark j
  have hZtop : Z = ⊤ := by
    apply top_unique
    intro x _
    have hclosureSubset : closure
        (schwarzschildParikhWilczekEndpointPacketSpan :
          Set SchwarzschildParikhWilczekEndpointHilbert) ⊆ (Z : Set _) :=
      hZclosed.closure_subset_iff.mpr (SetLike.coe_subset_coe.mpr hspan)
    exact hclosureSubset (dense_schwarzschildParikhWilczekEndpointPacketSpan x)
  have hallzero (x : SchwarzschildParikhWilczekEndpointHilbert) :
      hilbertSumInl x ∈ R := by
    have hx : x ∈ Z := by rw [hZtop]; exact Submodule.mem_top
    exact hx
  have hout {w : HilbertSum SchwarzschildParikhWilczekEndpointHilbert K} (hw : w ∈ R) :
      hilbertSumSnd w = 0 := by
    have hsub := R.sub_mem hw (hallzero (hilbertSumFst w))
    have heq : w - hilbertSumInl (hilbertSumFst w) =
        hilbertSumInr (hilbertSumSnd w) := by
      apply hilbertSum_ext
      · rw [map_sub, hilbertSumFst_inl, hilbertSumFst_inr, sub_self]
      · rw [map_sub, hilbertSumSnd_inl, hilbertSumSnd_inr, sub_zero]
    rw [heq] at hsub
    exact hsingle _ hsub
  constructor
  · exact hout
  · intro hz
    have heq : z = hilbertSumInl (hilbertSumFst z) := by
      apply hilbertSum_ext
      · rw [hilbertSumFst_inl]
      · rw [hilbertSumSnd_inl, hz]
    rw [heq]
    exact hallzero _

/-- Closed possibly unbounded or singular linear positive-response PW models cannot be dark at all
physical endpoint scales unless their response is the zero operator on the full source Hilbert
space. -/
def SchwarzschildParikhWilczekClosedRelationEndpointDarkRouteKilled : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (R : Submodule ℂ (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)),
    IsClosed (R : Set (HilbertSum SchwarzschildParikhWilczekEndpointHilbert K)) →
    HilbertRelationSingleValued R →
    (∀ j : ℕ, hilbertSumInl (schwarzschildParikhWilczekEndpointPacket j) ∈ R) →
    ∀ z, z ∈ R ↔ hilbertSumSnd z = 0

/-- **PW-CRET route kill.** Endpoint darkness eliminates the entire closed single-valued linear
relation class, including unbounded and singular graph candidates. -/
theorem schwarzschildParikhWilczekClosedRelationEndpointDarkRouteKilled :
    SchwarzschildParikhWilczekClosedRelationEndpointDarkRouteKilled := by
  intro K _ _ R hclosed hsingle hdark z
  exact closedSingleValuedRelation_mem_iff_output_zero_of_PWEndpointDark
    R hclosed hsingle hdark z

end

end RHTower
