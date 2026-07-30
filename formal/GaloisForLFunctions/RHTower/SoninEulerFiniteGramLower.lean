import GaloisForLFunctions.RHTower.SoninEulerFiniteL2Lower
import GaloisForLFunctions.Core

/-!
# Finite prime Sonin Gram systems modulo compact operators

Finite prime-indexed Sonin dilation corners have paired exterior preimages of one narrow interior
shell.  Their limiting compression table is controlled by prime ratios.  Unique factorization then
removes every off-diagonal ratio collision, while the diagonal collisions form an invertible tail
transform.  The resulting quadratic Gram family is linearly independent modulo compact operators.
-/

noncomputable section

open MeasureTheory Set
open Filter Topology
open scoped InnerProduct InnerProductSpace BigOperators

namespace RHTower

theorem exists_forall_lt_between_fintype
    {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ) (a : ℝ)
    (hu : ∀ i, u i < a) :
    ∃ c : ℝ, (∀ i, u i < c) ∧ c < a := by
  classical
  let U : Finset ℝ := Finset.univ.image u
  have hUne : U.Nonempty := Finset.univ_nonempty.image u
  let m : ℝ := U.max' hUne
  have hma : m < a := by
    rw [Finset.max'_lt_iff]
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hu i
  let c : ℝ := (m + a) / 2
  refine ⟨c, ?_, by dsimp [c]; linarith⟩
  intro i
  have him : u i ≤ m := Finset.le_max' U (u i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  dsimp [c]
  linarith

def finiteGramLowerConstraint {n : ℕ} (r : Fin n → ℝ) : Type :=
  Sum (Fin n) {ij : Fin n × Fin n // r ij.1 < r ij.2}

noncomputable instance {n : ℕ} (r : Fin n → ℝ) :
    Fintype (finiteGramLowerConstraint r) := by
  classical
  unfold finiteGramLowerConstraint
  infer_instance

instance {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) :
    Nonempty (finiteGramLowerConstraint r) :=
  ⟨Sum.inl (Classical.choice inferInstance)⟩

def finiteGramLowerValue {n : ℕ} (a : ℝ) (r : Fin n → ℝ) :
    finiteGramLowerConstraint r → ℝ
  | Sum.inl i => a / r i
  | Sum.inr ij => a * r ij.1.1 / r ij.1.2

def finiteActiveScaleRatioIndex {n : ℕ} (r : Fin n → ℝ) : Type :=
  {ij : Fin n × Fin n // r ij.2 ≤ r ij.1}

noncomputable instance {n : ℕ} (r : Fin n → ℝ) :
    Fintype (finiteActiveScaleRatioIndex r) := by
  classical
  unfold finiteActiveScaleRatioIndex
  infer_instance

instance {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) :
    Nonempty (finiteActiveScaleRatioIndex r) := by
  let i : Fin n := Classical.choice inferInstance
  exact ⟨⟨(i, i), le_rfl⟩⟩

def finiteActiveScaleRatio {n : ℕ} (r : Fin n → ℝ)
    (z : finiteActiveScaleRatioIndex r) : ℝ :=
  r z.1.1 / r z.1.2

def finiteGramUpperConstraint {n : ℕ} (r : Fin n → ℝ) : Type :=
  Sum Unit {zw : finiteActiveScaleRatioIndex r × finiteActiveScaleRatioIndex r //
    finiteActiveScaleRatio r zw.1 < finiteActiveScaleRatio r zw.2}

noncomputable instance {n : ℕ} (r : Fin n → ℝ) :
    Fintype (finiteGramUpperConstraint r) := by
  classical
  unfold finiteGramUpperConstraint
  infer_instance

instance {n : ℕ} (r : Fin n → ℝ) :
    Nonempty (finiteGramUpperConstraint r) :=
  ⟨Sum.inl ()⟩

def finiteGramUpperValue {n : ℕ} (a c : ℝ) (r : Fin n → ℝ) :
    finiteGramUpperConstraint r → ℝ
  | Sum.inl _ => a
  | Sum.inr zw =>
      c * finiteActiveScaleRatio r zw.1.2 / finiteActiveScaleRatio r zw.1.1

/-- A finite positive scale family admits one narrow interior shell which separates all active
scale ratios and sends every inactive ratio beyond the physical cutoff. -/
theorem exists_finiteScale_gramSeparatingInteriorShell
    {n : ℕ} [Nonempty (Fin n)] (a : ℝ) (ha : 0 < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) :
    ∃ c d : ℝ,
      0 < c ∧ c < d ∧ d < a ∧
      (∀ i, a < r i * c) ∧
      (∀ i j, r i < r j → a * r i < c * r j) ∧
      (∀ z w : finiteActiveScaleRatioIndex r,
        finiteActiveScaleRatio r z < finiteActiveScaleRatio r w →
          d * finiteActiveScaleRatio r z < c * finiteActiveScaleRatio r w) := by
  have hlower : ∀ z : finiteGramLowerConstraint r,
      finiteGramLowerValue a r z < a := by
    intro z
    rcases z with i | ij
    · dsimp [finiteGramLowerValue]
      have hri : 0 < r i := zero_lt_one.trans (hr i)
      rw [div_lt_iff₀ hri]
      nlinarith [hr i]
    · rcases ij with ⟨⟨i, j⟩, hij⟩
      dsimp [finiteGramLowerValue]
      have hrj : 0 < r j := zero_lt_one.trans (hr j)
      rw [div_lt_iff₀ hrj]
      nlinarith
  obtain ⟨c, hcLower, hca⟩ :=
    exists_forall_lt_between_fintype (finiteGramLowerValue a r) a hlower
  have hc : 0 < c := by
    let i : Fin n := Classical.choice inferInstance
    have h := hcLower (Sum.inl i)
    dsimp [finiteGramLowerValue] at h
    exact (div_pos ha (zero_lt_one.trans (hr i))).trans h
  have hupper : ∀ z : finiteGramUpperConstraint r,
      c < finiteGramUpperValue a c r z := by
    intro z
    rcases z with _ | zw
    · simpa [finiteGramUpperValue] using hca
    · rcases zw with ⟨⟨z, w⟩, hzw⟩
      dsimp [finiteGramUpperValue]
      have hzpos : 0 < finiteActiveScaleRatio r z :=
        div_pos (zero_lt_one.trans (hr z.1.1)) (zero_lt_one.trans (hr z.1.2))
      rw [lt_div_iff₀ hzpos]
      nlinarith
  obtain ⟨d, hcd, hdUpper⟩ :=
    exists_between_forall_fintype c (finiteGramUpperValue a c r) hupper
  refine ⟨c, d, hc, hcd, ?_, ?_, ?_, ?_⟩
  · exact hdUpper (Sum.inl ())
  · intro i
    have h := hcLower (Sum.inl i)
    dsimp [finiteGramLowerValue] at h
    have hri : 0 < r i := zero_lt_one.trans (hr i)
    rw [div_lt_iff₀ hri] at h
    simpa [mul_comm] using h
  · intro i j hij
    have h := hcLower (Sum.inr ⟨(i, j), hij⟩)
    dsimp [finiteGramLowerValue] at h
    have hrj : 0 < r j := zero_lt_one.trans (hr j)
    rwa [div_lt_iff₀ hrj] at h
  · intro z w hzw
    have h := hdUpper (Sum.inr ⟨(z, w), hzw⟩)
    dsimp [finiteGramUpperValue] at h
    have hzpos : 0 < finiteActiveScaleRatio r z :=
      div_pos (zero_lt_one.trans (hr z.1.1)) (zero_lt_one.trans (hr z.1.2))
    rwa [lt_div_iff₀ hzpos] at h

theorem scaledEvenShellBand_subset_Icc_of_upper
    {s c d a : ℝ} (hs : 0 < s) (hc : 0 < c) (hds : d ≤ s * a) :
    scaledEvenShellBand s c d ⊆ Set.Icc (-a) a := by
  intro x hx
  have hxabs : |s * x| ≤ d := by
    rcases hx with hx | hx
    · have hxneg : s * x ≤ -c := hx.2
      have hxneg' : s * x < 0 := lt_of_le_of_lt hxneg (neg_lt_zero.mpr hc)
      rw [abs_of_neg hxneg']
      linarith [hx.1]
    · have hxpos : 0 < s * x := lt_of_lt_of_le hc hx.1
      rw [abs_of_pos hxpos]
      exact hx.2
  rw [abs_mul, abs_of_pos hs] at hxabs
  have hxa : |x| ≤ a := by nlinarith
  exact abs_le.mp hxa

/-- An inward image of an interior shell lies in the physical forbidden space whenever its upper
edge is below the cutoff after scaling. -/
theorem inwardDilatedEvenShell_mem_centralPhysicalForbidden_of_upper
    (a c d s : ℝ) (hc : 0 < c) (hcd : c < d) (hs : 0 < s)
    (hds : d < s * a) (m : ℕ) :
    inwardDilatedEvenShell c d s hcd hs m ∈ centralPhysicalForbidden a := by
  rw [centralPhysicalForbidden]
  apply (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection_eq_self_iff.mp
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
  dsimp [inwardDilatedEvenShell, evenShellVector]
  apply indicatorCutoff_dilation_normalizedIndicator_eq_self
  exact (evenShellCell_preimage_subset_scaledEvenShellBand hcd m).trans
    (scaledEvenShellBand_subset_Icc_of_upper hs hc hds.le)

/-- If the acting scale is at least the preimage scale, the Sonin corner sends the corrected
inverse-dilated shell to the corresponding inward ratio shell. -/
theorem centralSoninDilationCorner_inverseDilatedEvenShell_tendsto_ratio_of_le
    (a c d p q : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) (hapc : a < p * c) :
    Tendsto (fun m =>
      ‖(crossBoundary (centralSoninProjection a) (dilationSum q hq) :
          SoninL2 →L[ℂ] SoninL2)
          (centralSoninProjection a (inverseDilatedEvenShell c d p hcd hp m)) -
        inwardDilatedEvenShell c d (q / p) hcd
          (div_pos (zero_lt_one.trans hq) (zero_lt_one.trans hp)) m‖)
      atTop (𝓝 0) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let D : SoninL2 →L[ℂ] SoninL2 := dilationSum q hq
  let B : SoninL2 →L[ℂ] SoninL2 := 1 - Q
  let v : ℕ → SoninL2 := evenShellVector c d hcd
  let g : ℕ → SoninL2 := inverseDilatedEvenShell c d p hcd hp
  let e : ℕ → SoninL2 := fun m => Q (g m)
  let t : ℕ → SoninL2 := fun m =>
    inwardDilatedEvenShell c d (q / p) hcd
      (div_pos (zero_lt_one.trans hq) (zero_lt_one.trans hp)) m
  have hpqOne : 1 < p * q := by nlinarith [hp, hq]
  let w : ℕ → SoninL2 := inverseDilatedEvenShell c d (p * q) hcd hpqOne
  have hgeNorm : Tendsto (fun m => ‖e m - g m‖) atTop (𝓝 0) := by
    simpa [e, g, Q] using
      centralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d p ha hc hcd hp hapc
  have hge : Tendsto (fun m => e m - g m) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hgeNorm
  have hapqc : a < (p * q) * c := by
    have hq0 : 0 < q := zero_lt_one.trans hq
    nlinarith [hapc, hc]
  have hQwNorm : Tendsto (fun m => ‖Q (w m) - w m‖) atTop (𝓝 0) := by
    simpa [Q, w] using
      centralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d (p * q) ha hc hcd hpqOne hapqc
  have hw : Tendsto (fun m => w m - Q (w m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hQwNorm using 1
    funext m
    rw [← norm_neg]
    congr 2
    module
  have hfirst : Tendsto (fun m => B (D (e m - g m))) atTop (𝓝 0) := by
    simpa only [map_zero] using! (B ∘L D).continuous.continuousAt.tendsto.comp hge
  have hsum : Tendsto (fun m => B (D (e m - g m)) + (w m - Q (w m)))
      atTop (𝓝 0) := by
    simpa only [add_zero] using hfirst.add hw
  have hQe : ∀ m, Q (e m) = e m := by
    intro m
    dsimp [e, Q]
    rw [centralSoninProjection_eq_soninIntersectionProjection]
    apply ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_eq_self_iff.mpr
    exact ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_apply_mem _
  have hratioOne : 1 ≤ q / p := by
    rw [le_div_iff₀ (zero_lt_one.trans hp)]
    simpa [one_mul] using hpq
  have hdt : d < (q / p) * a := by
    have hqa : a ≤ (q / p) * a := by nlinarith [ha, hratioOne]
    exact hda.trans_le hqa
  have hQt : ∀ m, Q (t m) = 0 := by
    intro m
    exact centralSoninProjection_eq_zero_of_mem_physicalForbidden a
      (inwardDilatedEvenShell_mem_centralPhysicalForbidden_of_upper
        a c d (q / p) hc hcd
          (div_pos (zero_lt_one.trans hq) (zero_lt_one.trans hp)) hdt m)
  have hDg : ∀ m, D (g m) = t m + w m := by
    intro m
    dsimp [D, g, t, w, inverseDilatedEvenShell, inwardDilatedEvenShell]
    rw [dilationSum_apply, dilation_comp_apply, dilation_comp_apply]
    congr 1
    · congr 2
      field_simp
  have hvec : Tendsto (fun m =>
      (crossBoundary Q D : SoninL2 →L[ℂ] SoninL2) (e m) - t m)
      atTop (𝓝 0) := by
    convert hsum using 1
    funext m
    simp only [crossBoundary, mul_apply_eq_comp,
      one_apply_eq_self, _root_.sub_apply]
    rw [hQe m]
    have hDe : D (e m) = D (e m - g m) + D (g m) := by
      rw [map_sub, sub_add_cancel]
    rw [hDe, hDg m, map_add, map_add, hQt m]
    dsimp [B]
    simp only [one_apply_eq_self, _root_.sub_apply]
    module
  exact tendsto_zero_iff_norm_tendsto_zero.mp hvec

/-- If the acting scale is smaller than the preimage scale and the ratio shell lies beyond the
cutoff, the corresponding Sonin corner output tends to zero. -/
theorem centralSoninDilationCorner_inverseDilatedEvenShell_tendsto_zero_of_lt
    (a c d p q : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hp : 1 < p) (hq : 1 < q) (hqp : q < p) (haqcp : a * q < c * p) :
    Tendsto (fun m =>
      ‖(crossBoundary (centralSoninProjection a) (dilationSum q hq) :
          SoninL2 →L[ℂ] SoninL2)
          (centralSoninProjection a (inverseDilatedEvenShell c d p hcd hp m))‖)
      atTop (𝓝 0) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let D : SoninL2 →L[ℂ] SoninL2 := dilationSum q hq
  let B : SoninL2 →L[ℂ] SoninL2 := 1 - Q
  let g : ℕ → SoninL2 := inverseDilatedEvenShell c d p hcd hp
  let e : ℕ → SoninL2 := fun m => Q (g m)
  have hpqRatio : 1 < p / q := by
    rw [one_lt_div (zero_lt_one.trans hq)]
    exact hqp
  let t : ℕ → SoninL2 := inverseDilatedEvenShell c d (p / q) hcd hpqRatio
  have hpqOne : 1 < p * q := by nlinarith [hp, hq]
  let w : ℕ → SoninL2 := inverseDilatedEvenShell c d (p * q) hcd hpqOne
  have hgeNorm : Tendsto (fun m => ‖e m - g m‖) atTop (𝓝 0) := by
    have hapc : a < p * c := by
      have hq1 : 1 < q := hq
      nlinarith [haqcp, ha]
    simpa [e, g, Q] using
      centralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d p ha hc hcd hp hapc
  have hge : Tendsto (fun m => e m - g m) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hgeNorm
  have hatc : a < (p / q) * c := by
    have h : a < c * p / q :=
      (lt_div_iff₀ (zero_lt_one.trans hq)).2 haqcp
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hQtNorm : Tendsto (fun m => ‖Q (t m) - t m‖) atTop (𝓝 0) := by
    simpa [Q, t] using
      centralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d (p / q) ha hc hcd hpqRatio hatc
  have ht : Tendsto (fun m => t m - Q (t m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hQtNorm using 1
    funext m
    rw [← norm_neg]
    congr 2
    module
  have hapqc : a < (p * q) * c := by
    have hpc : a < p * c := by
      nlinarith [haqcp, hq, ha]
    nlinarith [hpc, hq, hc]
  have hQwNorm : Tendsto (fun m => ‖Q (w m) - w m‖) atTop (𝓝 0) := by
    simpa [Q, w] using
      centralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d (p * q) ha hc hcd hpqOne hapqc
  have hw : Tendsto (fun m => w m - Q (w m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hQwNorm using 1
    funext m
    rw [← norm_neg]
    congr 2
    module
  have hfirst : Tendsto (fun m => B (D (e m - g m))) atTop (𝓝 0) := by
    simpa only [map_zero] using! (B ∘L D).continuous.continuousAt.tendsto.comp hge
  have hsum : Tendsto (fun m =>
      B (D (e m - g m)) + (t m - Q (t m)) + (w m - Q (w m)))
      atTop (𝓝 0) := by
    simpa only [add_zero] using (hfirst.add ht).add hw
  have hQe : ∀ m, Q (e m) = e m := by
    intro m
    dsimp [e, Q]
    rw [centralSoninProjection_eq_soninIntersectionProjection]
    apply ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_eq_self_iff.mpr
    exact ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_apply_mem _
  have hDg : ∀ m, D (g m) = t m + w m := by
    intro m
    dsimp [D, g, t, w, inverseDilatedEvenShell]
    rw [dilationSum_apply, dilation_comp_apply, dilation_comp_apply]
    apply congrArg₂ (fun x y : SoninL2 => x + y)
    · congr 2
      field_simp
    · congr 2
      field_simp
  have hvec : Tendsto (fun m =>
      (crossBoundary Q D : SoninL2 →L[ℂ] SoninL2) (e m)) atTop (𝓝 0) := by
    convert hsum using 1
    funext m
    simp only [crossBoundary, mul_apply_eq_comp,
      one_apply_eq_self, _root_.sub_apply]
    rw [hQe m]
    have hDe : D (e m) = D (e m - g m) + D (g m) := by
      rw [map_sub, sub_add_cancel]
    rw [hDe, hDg m, map_add, map_add]
    dsimp [B]
    simp only [one_apply_eq_self, _root_.sub_apply]
    module
  exact tendsto_zero_iff_norm_tendsto_zero.mp hvec

/-- The corrected inverse-dilated input associated with one scale. -/
def finitePairedEvenSoninInput
    {n : ℕ} (a c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hcd : c < d) (k : Fin n) (m : ℕ) : evenSubspace :=
  evenCentralSoninProjection a
    (inverseDilatedEvenShellEven c d (r k) hcd (hr k) m)

/-- The active inward ratio shell; inactive ratios are represented by zero. -/
def finiteSoninRatioOutput
    {n : ℕ} (c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hcd : c < d) (j k : Fin n) (m : ℕ) : evenSubspace :=
  if _h : r k ≤ r j then
    inwardDilatedEvenShellEven c d (r j / r k) hcd
      (div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k))) m
  else 0

/-- The finite paired-input table: a corner at scale `j` applied to the preimage for scale `k`
converges to the active ratio shell `r_j/r_k`, or to zero below the scale diagonal. -/
theorem evenCentralSoninDilationCorner_finitePairedInput_tendsto
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (harc : ∀ i, a < r i * c)
    (hout : ∀ i j, r i < r j → a * r i < c * r j)
    (j k : Fin n) :
    Tendsto (fun m =>
      ‖evenCentralSoninDilationCorner a (r j) (hr j)
          (finitePairedEvenSoninInput a c d r hr hcd k m) -
        finiteSoninRatioOutput c d r hr hcd j k m‖) atTop (𝓝 0) := by
  by_cases hkj : r k ≤ r j
  · simp only [finitePairedEvenSoninInput, finiteSoninRatioOutput, dif_pos hkj]
    change Tendsto (fun m =>
      ‖(crossBoundary (centralSoninProjection a) (dilationSum (r j) (hr j)) :
          SoninL2 →L[ℂ] SoninL2)
          (centralSoninProjection a
            (inverseDilatedEvenShell c d (r k) hcd (hr k) m)) -
        inwardDilatedEvenShell c d (r j / r k) hcd
          (div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k))) m‖)
      atTop (𝓝 0)
    exact centralSoninDilationCorner_inverseDilatedEvenShell_tendsto_ratio_of_le
      a c d (r k) (r j) ha hc hcd hda (hr k) (hr j) hkj (harc k)
  · have hjk : r j < r k := lt_of_not_ge hkj
    simp only [finitePairedEvenSoninInput, finiteSoninRatioOutput, dif_neg hkj, sub_zero]
    change Tendsto (fun m =>
      ‖(crossBoundary (centralSoninProjection a) (dilationSum (r j) (hr j)) :
          SoninL2 →L[ℂ] SoninL2)
          (centralSoninProjection a
            (inverseDilatedEvenShell c d (r k) hcd (hr k) m))‖)
      atTop (𝓝 0)
    exact centralSoninDilationCorner_inverseDilatedEvenShell_tendsto_zero_of_lt
      a c d (r k) (r j) ha hc hcd (hr k) (hr j) hjk (hout j k hjk)

theorem norm_finiteSoninRatioOutput_le_one
    {n : ℕ} (c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (j k : Fin n) (m : ℕ) :
    ‖finiteSoninRatioOutput c d r hr hcd j k m‖ ≤ 1 := by
  by_cases hkj : r k ≤ r j
  · rw [finiteSoninRatioOutput, dif_pos hkj]
    let hratio : 0 < r j / r k :=
      div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k))
    change ‖inwardDilatedEvenShell c d (r j / r k) hcd
      hratio m‖ ≤ 1
    rw [norm_inwardDilatedEvenShell c d (r j / r k) hc hcd hratio m]
  · rw [finiteSoninRatioOutput, dif_neg hkj]
    simp

theorem norm_finiteSoninRatioOutput_eq_one_of_le
    {n : ℕ} (c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (j k : Fin n) (hkj : r k ≤ r j) (m : ℕ) :
    ‖finiteSoninRatioOutput c d r hr hcd j k m‖ = 1 := by
  rw [finiteSoninRatioOutput, dif_pos hkj]
  let hratio : 0 < r j / r k :=
    div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k))
  change ‖inwardDilatedEvenShell c d (r j / r k) hcd hratio m‖ = 1
  exact norm_inwardDilatedEvenShell c d (r j / r k) hc hcd hratio m

/-- Active ratio shells have inner product one exactly at equal ratios and zero at distinct ratios
for a shell separating the finite ratio family. -/
theorem inner_finiteSoninRatioOutput_active
    {n : ℕ} (c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex r,
      finiteActiveScaleRatio r z < finiteActiveScaleRatio r w →
        d * finiteActiveScaleRatio r z < c * finiteActiveScaleRatio r w)
    (j k i l : Fin n) (hkj : r k ≤ r j) (hli : r l ≤ r i) (m : ℕ) :
    inner ℂ (finiteSoninRatioOutput c d r hr hcd i l m)
      (finiteSoninRatioOutput c d r hr hcd j k m) =
        if r i / r l = r j / r k then 1 else 0 := by
  let z : finiteActiveScaleRatioIndex r := ⟨(i, l), hli⟩
  let w : finiteActiveScaleRatioIndex r := ⟨(j, k), hkj⟩
  by_cases heq : r i / r l = r j / r k
  · rw [if_pos heq]
    have hv : finiteSoninRatioOutput c d r hr hcd i l m =
        finiteSoninRatioOutput c d r hr hcd j k m := by
      rw [finiteSoninRatioOutput, dif_pos hli,
        finiteSoninRatioOutput, dif_pos hkj]
      congr 2
    rw [hv, inner_self_eq_norm_sq_to_K,
      norm_finiteSoninRatioOutput_eq_one_of_le c d r hr hc hcd j k hkj m]
    norm_num
  · rw [if_neg heq]
    have hne : finiteActiveScaleRatio r z ≠ finiteActiveScaleRatio r w := by
      simpa [z, w, finiteActiveScaleRatio] using heq
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [finiteSoninRatioOutput, dif_pos hli,
        finiteSoninRatioOutput, dif_pos hkj]
      change inner ℂ
        (inwardDilatedEvenShell c d (finiteActiveScaleRatio r z) hcd
          (div_pos (zero_lt_one.trans (hr i)) (zero_lt_one.trans (hr l))) m)
        (inwardDilatedEvenShell c d (finiteActiveScaleRatio r w) hcd
          (div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k))) m) = 0
      exact inner_inwardDilatedEvenShell_eq_zero_of_lt hc hcd
        (div_pos (zero_lt_one.trans (hr i)) (zero_lt_one.trans (hr l)))
        (div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k)))
        (hsep z w hlt) m
    · rw [finiteSoninRatioOutput, dif_pos hli,
        finiteSoninRatioOutput, dif_pos hkj, ← inner_conj_symm]
      change star (inner ℂ
        (inwardDilatedEvenShell c d (finiteActiveScaleRatio r w) hcd
          (div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k))) m)
        (inwardDilatedEvenShell c d (finiteActiveScaleRatio r z) hcd
          (div_pos (zero_lt_one.trans (hr i)) (zero_lt_one.trans (hr l))) m)) = 0
      have hzero : inner ℂ
          (inwardDilatedEvenShell c d (finiteActiveScaleRatio r w) hcd
            (div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k))) m)
          (inwardDilatedEvenShell c d (finiteActiveScaleRatio r z) hcd
            (div_pos (zero_lt_one.trans (hr i)) (zero_lt_one.trans (hr l))) m) = 0 :=
        inner_inwardDilatedEvenShell_eq_zero_of_lt hc hcd
          (div_pos (zero_lt_one.trans (hr j)) (zero_lt_one.trans (hr k)))
          (div_pos (zero_lt_one.trans (hr i)) (zero_lt_one.trans (hr l)))
          (hsep w z hgt) m
      rw [hzero]
      simp

theorem norm_inner_sub_inner_tendsto_zero_of_paired_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {x y v w : ℕ → H} (hv : ∀ m, ‖v m‖ ≤ 1) (hw : ∀ m, ‖w m‖ ≤ 1)
    (hx : Tendsto (fun m => ‖x m - v m‖) atTop (𝓝 0))
    (hy : Tendsto (fun m => ‖y m - w m‖) atTop (𝓝 0)) :
    Tendsto (fun m => ‖inner ℂ (x m) (y m) - inner ℂ (v m) (w m)‖)
      atTop (𝓝 0) := by
  let ex : ℕ → ℝ := fun m => ‖x m - v m‖
  let ey : ℕ → ℝ := fun m => ‖y m - w m‖
  have hyNorm : ∀ m, ‖y m‖ ≤ ey m + 1 := by
    intro m
    calc
      ‖y m‖ = ‖(y m - w m) + w m‖ := by rw [sub_add_cancel]
      _ ≤ ‖y m - w m‖ + ‖w m‖ := norm_add_le _ _
      _ ≤ ey m + 1 := by
        dsimp [ey]
        linarith [hw m]
  have herr : ∀ m,
      ‖inner ℂ (x m) (y m) - inner ℂ (v m) (w m)‖ ≤
        ex m * (ey m + 1) + ey m := by
    intro m
    have hid : inner ℂ (x m) (y m) - inner ℂ (v m) (w m) =
        inner ℂ (x m - v m) (y m) + inner ℂ (v m) (y m - w m) := by
      rw [inner_sub_left, inner_sub_right]
      module
    rw [hid]
    calc
      ‖inner ℂ (x m - v m) (y m) + inner ℂ (v m) (y m - w m)‖
          ≤ ‖inner ℂ (x m - v m) (y m)‖ +
              ‖inner ℂ (v m) (y m - w m)‖ := norm_add_le _ _
      _ ≤ ‖x m - v m‖ * ‖y m‖ + ‖v m‖ * ‖y m - w m‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ex m * (ey m + 1) + ey m := by
        dsimp [ex, ey]
        have hfirst := mul_le_mul_of_nonneg_left (hyNorm m) (norm_nonneg (x m - v m))
        have hsecond := mul_le_mul_of_nonneg_right (hv m) (norm_nonneg (y m - w m))
        nlinarith
  have hupper : Tendsto (fun m => ex m * (ey m + 1) + ey m) atTop (𝓝 0) := by
    have hey1 : Tendsto (fun m => ey m + 1) atTop (𝓝 (0 + 1)) := by
      simpa [ey] using hy.add tendsto_const_nhds
    have hprod : Tendsto (fun m => ex m * (ey m + 1)) atTop (𝓝 (0 * (0 + 1))) := by
      simpa [ex] using hx.mul hey1
    have h := hprod.add hy
    simpa [ex, ey] using h
  exact squeeze_zero (fun _ => norm_nonneg _) herr hupper

/-- A finite matrix combination of the quadratic Sonin Gram entries. -/
def finiteEvenDilationGramCombination
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (A : Matrix (Fin n) (Fin n) ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i, ∑ j, A i j •
    ((evenCentralSoninDilationCorner a (r i) (hr i))† ∘L
      evenCentralSoninDilationCorner a (r j) (hr j))

/-- The finite-shell compression coefficient predicted by the active scale-ratio table. -/
def finiteGramShellCoefficient
    {n : ℕ} (c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hcd : c < d) (A : Matrix (Fin n) (Fin n) ℂ)
    (k l : Fin n) (m : ℕ) : ℂ :=
  ∑ i, ∑ j, A i j *
    inner ℂ (finiteSoninRatioOutput c d r hr hcd i l m)
      (finiteSoninRatioOutput c d r hr hcd j k m)

theorem inner_adjointComp_eq_corner_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Li Lj : H →L[ℂ] H) (x y : H) :
    inner ℂ y ((Li† ∘L Lj) x) = inner ℂ (Li y) (Lj x) := by
  have h := Li.adjoint_inner_left y (Lj x)
  rw [← inner_conj_symm]
  rw [show inner ℂ ((Li† ∘L Lj) x) y = inner ℂ (Lj x) (Li y) by simpa using h]
  rw [inner_conj_symm]

theorem inner_finiteEvenDilationGramCombination
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (A : Matrix (Fin n) (Fin n) ℂ) (x y : evenSubspace) :
    inner ℂ y (finiteEvenDilationGramCombination a r hr A x) =
      ∑ i, ∑ j, A i j * inner ℂ
        (evenCentralSoninDilationCorner a (r i) (hr i) y)
        (evenCentralSoninDilationCorner a (r j) (hr j) x) := by
  classical
  rw [finiteEvenDilationGramCombination, _root_.sum_apply]
  change (innerSL ℂ y) (∑ i, (∑ j, A i j •
    ((evenCentralSoninDilationCorner a (r i) (hr i))† ∘L
      evenCentralSoninDilationCorner a (r j) (hr j))) x) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.sum_apply]
  change (innerSL ℂ y) (∑ j, (A i j •
    ((evenCentralSoninDilationCorner a (r i) (hr i))† ∘L
      evenCentralSoninDilationCorner a (r j) (hr j))) x) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [_root_.smul_apply, map_smul]
  congr 1
  exact inner_adjointComp_eq_corner_inner
    (evenCentralSoninDilationCorner a (r i) (hr i))
    (evenCentralSoninDilationCorner a (r j) (hr j)) x y

/-- The actual finite Gram matrix coefficient converges to its ratio-shell compression
coefficient. -/
theorem finiteEvenDilationGramCombination_pairedShell_inner_tendsto
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (harc : ∀ i, a < r i * c)
    (hout : ∀ i j, r i < r j → a * r i < c * r j)
    (A : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) :
    Tendsto (fun m =>
      ‖inner ℂ (finitePairedEvenSoninInput a c d r hr hcd l m)
          (finiteEvenDilationGramCombination a r hr A
            (finitePairedEvenSoninInput a c d r hr hcd k m)) -
        finiteGramShellCoefficient c d r hr hcd A k l m‖)
      atTop (𝓝 0) := by
  classical
  let f : Fin n → ℕ → evenSubspace := fun k m =>
    finitePairedEvenSoninInput a c d r hr hcd k m
  let L : Fin n → evenSubspace →L[ℂ] evenSubspace := fun i =>
    evenCentralSoninDilationCorner a (r i) (hr i)
  let v : Fin n → Fin n → ℕ → evenSubspace := fun i k m =>
    finiteSoninRatioOutput c d r hr hcd i k m
  have hij : ∀ i j, Tendsto (fun m =>
      ‖inner ℂ (L i (f l m)) (L j (f k m)) - inner ℂ (v i l m) (v j k m)‖)
      atTop (𝓝 0) := by
    intro i j
    have hi : Tendsto (fun m => ‖L i (f l m) - v i l m‖) atTop (𝓝 0) := by
      dsimp [L, f, v]
      exact evenCentralSoninDilationCorner_finitePairedInput_tendsto
        a c d ha hc hcd hda r hr harc hout i l
    have hj : Tendsto (fun m => ‖L j (f k m) - v j k m‖) atTop (𝓝 0) := by
      dsimp [L, f, v]
      exact evenCentralSoninDilationCorner_finitePairedInput_tendsto
        a c d ha hc hcd hda r hr harc hout j k
    exact norm_inner_sub_inner_tendsto_zero_of_paired_approx
      (fun m => norm_finiteSoninRatioOutput_le_one c d r hr hc hcd i l m)
      (fun m => norm_finiteSoninRatioOutput_le_one c d r hr hc hcd j k m)
      hi hj
  have hsum : Tendsto (fun m =>
      ∑ i, ∑ j, A i j *
        (inner ℂ (L i (f l m)) (L j (f k m)) - inner ℂ (v i l m) (v j k m)))
      atTop (𝓝 0) := by
    have hinner : ∀ i, Tendsto (fun m => ∑ j, A i j *
        (inner ℂ (L i (f l m)) (L j (f k m)) - inner ℂ (v i l m) (v j k m)))
        atTop (𝓝 0) := by
      intro i
      have h := tendsto_finsetSum Finset.univ (fun j _ => by
        have hvec : Tendsto (fun m =>
            inner ℂ (L i (f l m)) (L j (f k m)) - inner ℂ (v i l m) (v j k m))
            atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (hij i j)
        simpa only [mul_zero] using hvec.const_mul (A i j))
      simpa using h
    have h := tendsto_finsetSum Finset.univ (fun i _ => hinner i)
    simpa using h
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  convert hsum using 1
  funext m
  rw [inner_finiteEvenDilationGramCombination]
  simp only [finiteGramShellCoefficient, f, L, v]
  simp_rw [mul_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]

theorem primePairProduct_eq_cases
    {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {i j k l : Fin n} (hprod : p i * p k = p j * p l) :
    (i = j ∧ k = l) ∨ (i = l ∧ k = j) := by
  have hdvd : p i ∣ p j * p l := by
    refine ⟨p k, ?_⟩
    exact hprod.symm
  rcases (hp i).dvd_mul.mp hdvd with hij | hil
  · have hpij : p j = p i := ((hp j).dvd_iff_eq (hp i).ne_one).mp hij
    have hijIndex : i = j := hinj hpij.symm
    left
    refine ⟨hijIndex, ?_⟩
    subst j
    exact hinj (Nat.eq_of_mul_eq_mul_left (hp i).pos hprod)
  · have hpil : p l = p i := ((hp l).dvd_iff_eq (hp i).ne_one).mp hil
    have hilIndex : i = l := hinj hpil.symm
    right
    refine ⟨hilIndex, ?_⟩
    subst l
    apply hinj
    apply Nat.eq_of_mul_eq_mul_left (hp i).pos
    simpa [mul_comm] using hprod

theorem primeRatio_eq_cases
    {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {i j k l : Fin n}
    (hratio : (p i : ℝ) / (p k : ℝ) = (p j : ℝ) / (p l : ℝ)) :
    (i = j ∧ k = l) ∨ (i = k ∧ l = j) := by
  have hk0 : (p k : ℝ) ≠ 0 := by exact_mod_cast (hp k).ne_zero
  have hl0 : (p l : ℝ) ≠ 0 := by exact_mod_cast (hp l).ne_zero
  have hreal : (p i : ℝ) * p l = (p j : ℝ) * p k :=
    (div_eq_div_iff hk0 hl0).mp hratio
  have hnat : p i * p l = p j * p k := by exact_mod_cast hreal
  rcases primePairProduct_eq_cases p hp hinj hnat with h | h
  · exact Or.inl ⟨h.1, h.2.symm⟩
  · exact Or.inr h

/-- Distinct prime indices remove every off-diagonal collision in the ratio-shell table. -/
theorem inner_finiteSoninRatioOutput_prime_offDiagonal
    {n : ℕ} (c d : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hc : 0 < c) (hcd : c < d)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex (fun i => (p i : ℝ)),
      finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          finiteActiveScaleRatio (fun i => (p i : ℝ)) w →
        d * finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          c * finiteActiveScaleRatio (fun i => (p i : ℝ)) w)
    (k l : Fin n) (hkl : k ≠ l) (i j : Fin n) (m : ℕ) :
    inner ℂ
      (finiteSoninRatioOutput c d (fun x => (p x : ℝ))
        (fun x => by
          change (1 : ℝ) < (p x : ℝ)
          exact_mod_cast (hp x).one_lt) hcd i l m)
      (finiteSoninRatioOutput c d (fun x => (p x : ℝ))
        (fun x => by
          change (1 : ℝ) < (p x : ℝ)
          exact_mod_cast (hp x).one_lt) hcd j k m) =
      if i = l ∧ j = k then 1 else 0 := by
  let r : Fin n → ℝ := fun x => (p x : ℝ)
  let hr : ∀ x, 1 < r x := fun x => by
    change (1 : ℝ) < (p x : ℝ)
    exact_mod_cast (hp x).one_lt
  change inner ℂ
      (finiteSoninRatioOutput c d r hr hcd i l m)
      (finiteSoninRatioOutput c d r hr hcd j k m) =
    if i = l ∧ j = k then 1 else 0
  by_cases hli : r l ≤ r i
  · by_cases hkj : r k ≤ r j
    · rw [inner_finiteSoninRatioOutput_active c d r hr hc hcd hsep j k i l hkj hli m]
      by_cases heq : r i / r l = r j / r k
      · have hcases := primeRatio_eq_cases p hp hinj heq
        have hiljk : i = l ∧ j = k := by
          rcases hcases with ⟨hij, hlk⟩ | ⟨hil, hkj'⟩
          · exact False.elim (hkl hlk.symm)
          · exact ⟨hil, hkj'.symm⟩
        rw [if_pos heq, if_pos hiljk]
      · have hnot : ¬(i = l ∧ j = k) := by
          intro h
          have hl0 : r l ≠ 0 := ne_of_gt (zero_lt_one.trans (hr l))
          have hk0 : r k ≠ 0 := ne_of_gt (zero_lt_one.trans (hr k))
          apply heq
          rw [h.1, h.2, div_self hl0, div_self hk0]
        rw [if_neg heq, if_neg hnot]
    · have hnot : ¬(i = l ∧ j = k) := by
        intro h
        exact hkj (by simp [h.2])
      have hvzero : finiteSoninRatioOutput c d r hr hcd j k m = 0 := by
        rw [finiteSoninRatioOutput, dif_neg hkj]
      rw [hvzero, inner_zero_right, if_neg hnot]
  · have hnot : ¬(i = l ∧ j = k) := by
      intro h
      exact hli (by simp [h.1])
    have hvzero : finiteSoninRatioOutput c d r hr hcd i l m = 0 := by
      rw [finiteSoninRatioOutput, dif_neg hli]
    rw [hvzero, inner_zero_left, if_neg hnot]

theorem finiteGramShellCoefficient_prime_offDiagonal_eq
    {n : ℕ} (c d : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hc : 0 < c) (hcd : c < d)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex (fun i => (p i : ℝ)),
      finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          finiteActiveScaleRatio (fun i => (p i : ℝ)) w →
        d * finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          c * finiteActiveScaleRatio (fun i => (p i : ℝ)) w)
    (A : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) (hkl : k ≠ l) (m : ℕ) :
    finiteGramShellCoefficient c d (fun i => (p i : ℝ))
      (fun i => by
        change (1 : ℝ) < (p i : ℝ)
        exact_mod_cast (hp i).one_lt) hcd A k l m = A l k := by
  classical
  unfold finiteGramShellCoefficient
  simp_rw [inner_finiteSoninRatioOutput_prime_offDiagonal
    c d p hp hinj hc hcd hsep k l hkl]
  simp_rw [mul_ite, mul_one, mul_zero]
  calc
    (∑ i, ∑ j, if i = l ∧ j = k then A i j else 0) =
        ∑ i, if i = l then A l k else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hil : i = l
      · subst i
        simp
      · simp [hil]
    _ = A l k := by simp

/-- Every off-diagonal coefficient of a finite prime Gram combination survives every compact
perturbation with its full modulus. -/
theorem norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) (hkl : k ≠ l)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    ‖A l k‖ ≤
      ‖finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) A - K‖ := by
  letI : Nonempty (Fin n) := ⟨k⟩
  let r : Fin n → ℝ := fun i => (p i : ℝ)
  let hr : ∀ i, 1 < r i := fun i => by
    change (1 : ℝ) < (p i : ℝ)
    exact_mod_cast (hp i).one_lt
  obtain ⟨c, d, hc, hcd, hda, harc, hout, hsep⟩ :=
    exists_finiteScale_gramSeparatingInteriorShell a ha r hr
  let f : Fin n → ℕ → evenSubspace := fun i m =>
    finitePairedEvenSoninInput a c d r hr hcd i m
  let T : evenSubspace →L[ℂ] evenSubspace := finiteEvenDilationGramCombination a r hr A
  have hinnerApprox : Tendsto (fun m =>
      ‖inner ℂ (f l m) (T (f k m)) - A l k‖) atTop (𝓝 0) := by
    have h := finiteEvenDilationGramCombination_pairedShell_inner_tendsto
      a c d ha hc hcd hda r hr harc hout A k l
    convert h using 1
    funext m
    rw [finiteGramShellCoefficient_prime_offDiagonal_eq
      c d p hp hinj hc hcd (by simpa [r] using hsep) A k l hkl m]
  have hinnerNorm : Tendsto (fun m => ‖inner ℂ (f l m) (T (f k m))‖)
      atTop (𝓝 ‖A l k‖) :=
    tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq hinnerApprox (fun _ => rfl)
  have hfWeak : ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun m => ℓ (f k m)) atTop (𝓝 0) := by
    let g : ℕ → evenSubspace := inverseDilatedEvenShellEven c d (r k) hcd (hr k)
    have hg : Orthonormal ℂ g := by
      simpa [g] using inverseDilatedEvenShellEven_orthonormal c d (r k) hc hcd (hr k)
    have hfApprox : Tendsto (fun m => ‖f k m - g m‖) atTop (𝓝 0) := by
      simpa [f, g, finitePairedEvenSoninInput] using
        evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
          a c d (r k) ha hc hcd (hr k) (harc k)
    exact weakly_tendsto_zero_of_norm_sub_tendsto_zero
      (Orthonormal.weakly_tendsto_zero hg) hfApprox
  have hfBound : ∀ m, ‖f k m‖ ≤ 1 := by
    intro m
    calc
      ‖f k m‖ ≤ ‖inverseDilatedEvenShellEven c d (r k) hcd (hr k) m‖ := by
        change ‖evenCentralSoninProjection a
          (inverseDilatedEvenShellEven c d (r k) hcd (hr k) m)‖ ≤ _
        rw [evenCentralSoninProjection_eq_starProjection]
        exact (evenCentralSoninCarrier a).norm_starProjection_apply_le _
      _ = 1 :=
        (inverseDilatedEvenShellEven_orthonormal c d (r k) hc hcd (hr k)).norm_eq_one m
  have hlBound : ∀ m, ‖f l m‖ ≤ 1 := by
    intro m
    calc
      ‖f l m‖ ≤ ‖inverseDilatedEvenShellEven c d (r l) hcd (hr l) m‖ := by
        change ‖evenCentralSoninProjection a
          (inverseDilatedEvenShellEven c d (r l) hcd (hr l) m)‖ ≤ _
        rw [evenCentralSoninProjection_eq_starProjection]
        exact (evenCentralSoninCarrier a).norm_starProjection_apply_le _
      _ = 1 :=
        (inverseDilatedEvenShellEven_orthonormal c d (r l) hc hcd (hr l)).norm_eq_one m
  have hKzero : Tendsto (fun m => ‖K (f k m)‖) atTop (𝓝 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      K hK (f k) 1 hfBound hfWeak
  have hupper : Tendsto (fun m => ‖T - K‖ + ‖K (f k m)‖)
      atTop (𝓝 (‖T - K‖ + 0)) := tendsto_const_nhds.add hKzero
  have hle : ∀ m, ‖inner ℂ (f l m) (T (f k m))‖ ≤
      ‖T - K‖ + ‖K (f k m)‖ := by
    intro m
    have hdecomp : T (f k m) = (T - K) (f k m) + K (f k m) := by simp
    rw [hdecomp, inner_add_right]
    calc
      ‖inner ℂ (f l m) ((T - K) (f k m)) + inner ℂ (f l m) (K (f k m))‖
          ≤ ‖inner ℂ (f l m) ((T - K) (f k m))‖ +
              ‖inner ℂ (f l m) (K (f k m))‖ := norm_add_le _ _
      _ ≤ ‖f l m‖ * ‖(T - K) (f k m)‖ + ‖f l m‖ * ‖K (f k m)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖T - K‖ + ‖K (f k m)‖ := by
        have hTf := (T - K).le_opNorm (f k m)
        have hfl := hlBound m
        have hfk := hfBound m
        have hTK : 0 ≤ ‖T - K‖ := norm_nonneg (T - K)
        have hKf : 0 ≤ ‖K (f k m)‖ := norm_nonneg _
        have hfl0 : 0 ≤ ‖f l m‖ := norm_nonneg _
        have hfk0 : 0 ≤ ‖f k m‖ := norm_nonneg _
        have hfirst : ‖f l m‖ * ‖(T - K) (f k m)‖ ≤ ‖T - K‖ := by
          calc
            ‖f l m‖ * ‖(T - K) (f k m)‖
                ≤ ‖f l m‖ * (‖T - K‖ * ‖f k m‖) :=
              mul_le_mul_of_nonneg_left hTf hfl0
            _ ≤ 1 * (‖T - K‖ * 1) :=
              mul_le_mul hfl (mul_le_mul_of_nonneg_left hfk hTK)
                (mul_nonneg hTK hfk0) zero_le_one
            _ = ‖T - K‖ := by ring
        have hsecond : ‖f l m‖ * ‖K (f k m)‖ ≤ ‖K (f k m)‖ := by
          calc
            ‖f l m‖ * ‖K (f k m)‖ ≤ 1 * ‖K (f k m)‖ :=
              mul_le_mul_of_nonneg_right hfl hKf
            _ = ‖K (f k m)‖ := one_mul _
        exact add_le_add hfirst hsecond
  have hlimit := le_of_tendsto_of_tendsto hinnerNorm hupper (Eventually.of_forall hle)
  simpa [T, r, hr] using hlimit

theorem finitePairedEvenSoninInput_weakly_tendsto_zero
    {n : ℕ} (a c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (harc : ∀ i, a < r i * c)
    (k : Fin n) :
    ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun m => ℓ (finitePairedEvenSoninInput a c d r hr hcd k m))
        atTop (𝓝 0) := by
  let g : ℕ → evenSubspace := inverseDilatedEvenShellEven c d (r k) hcd (hr k)
  let f : ℕ → evenSubspace := finitePairedEvenSoninInput a c d r hr hcd k
  have hg : Orthonormal ℂ g := by
    simpa [g] using inverseDilatedEvenShellEven_orthonormal c d (r k) hc hcd (hr k)
  have hfApprox : Tendsto (fun m => ‖f m - g m‖) atTop (𝓝 0) := by
    simpa [f, g, finitePairedEvenSoninInput] using
      evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d (r k) ha hc hcd (hr k) (harc k)
  exact weakly_tendsto_zero_of_norm_sub_tendsto_zero
    (Orthonormal.weakly_tendsto_zero hg) hfApprox

theorem norm_finitePairedEvenSoninInput_le_one
    {n : ℕ} (a c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (k : Fin n) (m : ℕ) :
    ‖finitePairedEvenSoninInput a c d r hr hcd k m‖ ≤ 1 := by
  calc
    ‖finitePairedEvenSoninInput a c d r hr hcd k m‖ ≤
        ‖inverseDilatedEvenShellEven c d (r k) hcd (hr k) m‖ := by
      rw [finitePairedEvenSoninInput, evenCentralSoninProjection_eq_starProjection]
      exact (evenCentralSoninCarrier a).norm_starProjection_apply_le _
    _ = 1 :=
      (inverseDilatedEvenShellEven_orthonormal c d (r k) hc hcd (hr k)).norm_eq_one m

theorem norm_shellCoefficient_le_norm_finiteEvenDilationGram_sub_compact_of_shell
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (harc : ∀ i, a < r i * c)
    (hout : ∀ i j, r i < r j → a * r i < c * r j)
    (A : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) (z : ℂ)
    (hz : ∀ m, finiteGramShellCoefficient c d r hr hcd A k l m = z)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    ‖z‖ ≤ ‖finiteEvenDilationGramCombination a r hr A - K‖ := by
  let f : Fin n → ℕ → evenSubspace := fun i m =>
    finitePairedEvenSoninInput a c d r hr hcd i m
  let T : evenSubspace →L[ℂ] evenSubspace := finiteEvenDilationGramCombination a r hr A
  have hinnerApprox : Tendsto (fun m =>
      ‖inner ℂ (f l m) (T (f k m)) - z‖) atTop (𝓝 0) := by
    have h := finiteEvenDilationGramCombination_pairedShell_inner_tendsto
      a c d ha hc hcd hda r hr harc hout A k l
    convert h using 1
    funext m
    rw [hz m]
  have hinnerNorm : Tendsto (fun m => ‖inner ℂ (f l m) (T (f k m))‖)
      atTop (𝓝 ‖z‖) :=
    tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq hinnerApprox (fun _ => rfl)
  have hfWeak : ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun m => ℓ (f k m)) atTop (𝓝 0) := by
    simpa [f] using finitePairedEvenSoninInput_weakly_tendsto_zero
      a c d r hr ha hc hcd harc k
  have hfBound : ∀ m, ‖f k m‖ ≤ 1 := fun m =>
    norm_finitePairedEvenSoninInput_le_one a c d r hr hc hcd k m
  have hlBound : ∀ m, ‖f l m‖ ≤ 1 := fun m =>
    norm_finitePairedEvenSoninInput_le_one a c d r hr hc hcd l m
  have hKzero : Tendsto (fun m => ‖K (f k m)‖) atTop (𝓝 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      K hK (f k) 1 hfBound hfWeak
  have hupper : Tendsto (fun m => ‖T - K‖ + ‖K (f k m)‖)
      atTop (𝓝 (‖T - K‖ + 0)) := tendsto_const_nhds.add hKzero
  have hle : ∀ m, ‖inner ℂ (f l m) (T (f k m))‖ ≤
      ‖T - K‖ + ‖K (f k m)‖ := by
    intro m
    have hdecomp : T (f k m) = (T - K) (f k m) + K (f k m) := by simp
    rw [hdecomp, inner_add_right]
    calc
      ‖inner ℂ (f l m) ((T - K) (f k m)) + inner ℂ (f l m) (K (f k m))‖
          ≤ ‖inner ℂ (f l m) ((T - K) (f k m))‖ +
              ‖inner ℂ (f l m) (K (f k m))‖ := norm_add_le _ _
      _ ≤ ‖f l m‖ * ‖(T - K) (f k m)‖ + ‖f l m‖ * ‖K (f k m)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖T - K‖ + ‖K (f k m)‖ := by
        have hTf := (T - K).le_opNorm (f k m)
        have hfl := hlBound m
        have hfk := hfBound m
        have hTK : 0 ≤ ‖T - K‖ := norm_nonneg (T - K)
        have hKf : 0 ≤ ‖K (f k m)‖ := norm_nonneg _
        have hfl0 : 0 ≤ ‖f l m‖ := norm_nonneg _
        have hfk0 : 0 ≤ ‖f k m‖ := norm_nonneg _
        have hfirst : ‖f l m‖ * ‖(T - K) (f k m)‖ ≤ ‖T - K‖ := by
          calc
            ‖f l m‖ * ‖(T - K) (f k m)‖
                ≤ ‖f l m‖ * (‖T - K‖ * ‖f k m‖) :=
              mul_le_mul_of_nonneg_left hTf hfl0
            _ ≤ 1 * (‖T - K‖ * 1) :=
              mul_le_mul hfl (mul_le_mul_of_nonneg_left hfk hTK)
                (mul_nonneg hTK hfk0) zero_le_one
            _ = ‖T - K‖ := by ring
        have hsecond : ‖f l m‖ * ‖K (f k m)‖ ≤ ‖K (f k m)‖ := by
          calc
            ‖f l m‖ * ‖K (f k m)‖ ≤ 1 * ‖K (f k m)‖ :=
              mul_le_mul_of_nonneg_right hfl hKf
            _ = ‖K (f k m)‖ := one_mul _
        exact add_le_add hfirst hsecond
  have hlimit := le_of_tendsto_of_tendsto hinnerNorm hupper (Eventually.of_forall hle)
  simpa [T] using hlimit

theorem inner_finiteSoninRatioOutput_prime_diagonal
    {n : ℕ} (c d : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hc : 0 < c) (hcd : c < d)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex (fun i => (p i : ℝ)),
      finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          finiteActiveScaleRatio (fun i => (p i : ℝ)) w →
        d * finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          c * finiteActiveScaleRatio (fun i => (p i : ℝ)) w)
    (k i j : Fin n) (m : ℕ) :
    inner ℂ
      (finiteSoninRatioOutput c d (fun x => (p x : ℝ))
        (fun x => by
          change (1 : ℝ) < (p x : ℝ)
          exact_mod_cast (hp x).one_lt) hcd i k m)
      (finiteSoninRatioOutput c d (fun x => (p x : ℝ))
        (fun x => by
          change (1 : ℝ) < (p x : ℝ)
          exact_mod_cast (hp x).one_lt) hcd j k m) =
      if i = j ∧ p k ≤ p i then 1 else 0 := by
  let r : Fin n → ℝ := fun x => (p x : ℝ)
  let hr : ∀ x, 1 < r x := fun x => by
    change (1 : ℝ) < (p x : ℝ)
    exact_mod_cast (hp x).one_lt
  change inner ℂ
      (finiteSoninRatioOutput c d r hr hcd i k m)
      (finiteSoninRatioOutput c d r hr hcd j k m) =
    if i = j ∧ p k ≤ p i then 1 else 0
  by_cases hki : r k ≤ r i
  · by_cases hkj : r k ≤ r j
    · rw [inner_finiteSoninRatioOutput_active c d r hr hc hcd hsep j k i k hkj hki m]
      by_cases heq : r i / r k = r j / r k
      · have hcases := primeRatio_eq_cases p hp hinj heq
        have hij : i = j := by
          rcases hcases with ⟨hij, _⟩ | ⟨hik, hkj'⟩
          · exact hij
          · exact hik.trans hkj'
        have hkiNat : p k ≤ p i := by
          change (p k : ℝ) ≤ (p i : ℝ) at hki
          exact_mod_cast hki
        rw [if_pos heq, if_pos ⟨hij, hkiNat⟩]
      · have hnot : ¬(i = j ∧ p k ≤ p i) := by
          intro h
          apply heq
          rw [h.1]
        rw [if_neg heq, if_neg hnot]
    · have hnot : ¬(i = j ∧ p k ≤ p i) := by
        intro h
        apply hkj
        rw [← h.1]
        exact hki
      have hvzero : finiteSoninRatioOutput c d r hr hcd j k m = 0 := by
        rw [finiteSoninRatioOutput, dif_neg hkj]
      rw [hvzero, inner_zero_right, if_neg hnot]
  · have hnot : ¬(i = j ∧ p k ≤ p i) := by
      intro h
      apply hki
      change (p k : ℝ) ≤ (p i : ℝ)
      exact_mod_cast h.2
    have hvzero : finiteSoninRatioOutput c d r hr hcd i k m = 0 := by
      rw [finiteSoninRatioOutput, dif_neg hki]
    rw [hvzero, inner_zero_left, if_neg hnot]

def finitePrimeDiagonalTail
    {n : ℕ} (p : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) : ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => p k ≤ p i), A i i

theorem finiteGramShellCoefficient_prime_diagonal_eq
    {n : ℕ} (c d : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hc : 0 < c) (hcd : c < d)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex (fun i => (p i : ℝ)),
      finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          finiteActiveScaleRatio (fun i => (p i : ℝ)) w →
        d * finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          c * finiteActiveScaleRatio (fun i => (p i : ℝ)) w)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (m : ℕ) :
    finiteGramShellCoefficient c d (fun i => (p i : ℝ))
      (fun i => by
        change (1 : ℝ) < (p i : ℝ)
        exact_mod_cast (hp i).one_lt) hcd A k k m =
      finitePrimeDiagonalTail p A k := by
  classical
  unfold finiteGramShellCoefficient
  simp_rw [inner_finiteSoninRatioOutput_prime_diagonal
    c d p hp hinj hc hcd hsep k]
  simp_rw [mul_ite, mul_one, mul_zero]
  calc
    (∑ i, ∑ j, if i = j ∧ p k ≤ p i then A i j else 0) =
        ∑ i, if p k ≤ p i then A i i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hki : p k ≤ p i
      · simp [hki]
      · simp [hki]
    _ = finitePrimeDiagonalTail p A k := by
      rw [finitePrimeDiagonalTail, Finset.sum_filter]

/-- Every diagonal prime tail is a quantitative compact-distance lower bound for the finite Gram
combination. -/
theorem norm_finitePrimeDiagonalTail_le_norm_finitePrimeEvenDilationGram_sub_compact
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : Fin n)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    ‖finitePrimeDiagonalTail p A k‖ ≤
      ‖finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) A - K‖ := by
  letI : Nonempty (Fin n) := ⟨k⟩
  let r : Fin n → ℝ := fun i => (p i : ℝ)
  let hr : ∀ i, 1 < r i := fun i => by
    change (1 : ℝ) < (p i : ℝ)
    exact_mod_cast (hp i).one_lt
  obtain ⟨c, d, hc, hcd, hda, harc, hout, hsep⟩ :=
    exists_finiteScale_gramSeparatingInteriorShell a ha r hr
  have hz : ∀ m, finiteGramShellCoefficient c d r hr hcd A k k m =
      finitePrimeDiagonalTail p A k := by
    intro m
    exact finiteGramShellCoefficient_prime_diagonal_eq
      c d p hp hinj hc hcd (by simpa [r] using hsep) A k m
  simpa [r, hr] using
    norm_shellCoefficient_le_norm_finiteEvenDilationGram_sub_compact_of_shell
      a c d ha hc hcd hda r hr harc hout A k k
        (finitePrimeDiagonalTail p A k) hz K hK

/-- **Finite prime quadratic Calkin injectivity.** No nonzero complex matrix combination of the
prime-indexed Sonin Gram entries is compact. -/
theorem finitePrimeEvenDilationGram_not_isCompactOperator_of_ne_zero
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ≠ 0) :
    ¬ IsCompactOperator
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) A) := by
  classical
  let r : Fin n → ℝ := fun i => (p i : ℝ)
  let hr : ∀ i, 1 < r i := fun i => by
    change (1 : ℝ) < (p i : ℝ)
    exact_mod_cast (hp i).one_lt
  let T : evenSubspace →L[ℂ] evenSubspace := finiteEvenDilationGramCombination a r hr A
  intro hcompact
  by_cases hoff : ∃ i j, i ≠ j ∧ A i j ≠ 0
  · obtain ⟨i, j, hij, hAij⟩ := hoff
    have hle := norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
      a ha p hp hinj A j i hij.symm T hcompact
    change ‖A i j‖ ≤ ‖T - T‖ at hle
    rw [sub_self] at hle
    have hnormZero : ‖(0 : evenSubspace →L[ℂ] evenSubspace)‖ = 0 :=
      ContinuousLinearMap.opNorm_zero
    rw [hnormZero] at hle
    have hzero : ‖A i j‖ = 0 := by
      exact le_antisymm hle (norm_nonneg _)
    exact hAij (norm_eq_zero.mp hzero)
  · have hdiag : ∃ i, A i i ≠ 0 := by
      by_contra h
      push Not at h
      apply hA
      ext i j
      by_cases hij : i = j
      · subst j
        exact h i
      · by_contra hne
        exact hoff ⟨i, j, hij, hne⟩
    let S : Finset (Fin n) := Finset.univ.filter fun i => A i i ≠ 0
    have hSne : S.Nonempty := by
      obtain ⟨i, hi⟩ := hdiag
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨k, hkS, hkmax⟩ := S.exists_max_image p hSne
    have hkne : A k k ≠ 0 := (Finset.mem_filter.mp hkS).2
    have htail : finitePrimeDiagonalTail p A k = A k k := by
      unfold finitePrimeDiagonalTail
      rw [Finset.sum_eq_single k]
      · intro i hi hik
        have hpki : p k ≤ p i := (Finset.mem_filter.mp hi).2
        by_contra hAii
        have hiS : i ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAii⟩
        have hpik : p i ≤ p k := hkmax i hiS
        exact hik (hinj (le_antisymm hpik hpki))
      · intro hknot
        exact False.elim (hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩))
    have hle :=
      norm_finitePrimeDiagonalTail_le_norm_finitePrimeEvenDilationGram_sub_compact
        a ha p hp hinj A k T hcompact
    rw [htail] at hle
    change ‖A k k‖ ≤ ‖T - T‖ at hle
    rw [sub_self] at hle
    have hnormZero : ‖(0 : evenSubspace →L[ℂ] evenSubspace)‖ = 0 :=
      ContinuousLinearMap.opNorm_zero
    rw [hnormZero] at hle
    have hzero : ‖A k k‖ = 0 := by
      exact le_antisymm hle (norm_nonneg _)
    exact hkne (norm_eq_zero.mp hzero)

theorem finitePrimeEvenDilationGram_isCompactOperator_iff
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    IsCompactOperator
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) A) ↔ A = 0 := by
  constructor
  · intro hcompact
    by_contra hA
    exact finitePrimeEvenDilationGram_not_isCompactOperator_of_ne_zero
      a ha p hp hinj A hA hcompact
  · rintro rfl
    simpa [finiteEvenDilationGramCombination] using!
      (isCompactOperator_zero : IsCompactOperator
        (0 : evenSubspace →L[ℂ] evenSubspace))

def finiteEulerGramRescale
    {n : ℕ} (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i j * star (-((Real.sqrt (r i) : ℂ)⁻¹)) *
    (-((Real.sqrt (r j) : ℂ)⁻¹))

def finiteEvenPositiveEulerGramCombination
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (A : Matrix (Fin n) (Fin n) ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i, ∑ j, A i j • evenCentralPositiveEulerQuadraticCorner
    a (r i) (r j) (hr i) (hr j)

theorem finiteEvenPositiveEulerGramCombination_eq_dilation
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finiteEvenPositiveEulerGramCombination a r hr A =
      finiteEvenDilationGramCombination a r hr (finiteEulerGramRescale r A) := by
  classical
  unfold finiteEvenPositiveEulerGramCombination finiteEvenDilationGramCombination
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [evenCentralPositiveEulerQuadraticCorner_eq_smul]
  simp only [finiteEulerGramRescale, smul_smul]
  congr 1
  ring

theorem finiteEulerGramRescale_ne_zero
    {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ≠ 0) :
    finiteEulerGramRescale r A ≠ 0 := by
  intro hzero
  apply hA
  ext i j
  have hij := congrFun (congrFun hzero i) j
  change A i j * star (-((Real.sqrt (r i) : ℂ)⁻¹)) *
      (-((Real.sqrt (r j) : ℂ)⁻¹)) = 0 at hij
  rcases mul_eq_zero.mp hij with hleft | hj
  · rcases mul_eq_zero.mp hleft with hAij | hi
    · exact hAij
    · exfalso
      apply (star_ne_zero.mpr ?_) hi
      simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans (hr i))]
  · exfalso
    have hs : (Real.sqrt (r j) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (zero_lt_one.trans (hr j)))
    exact (neg_ne_zero.mpr (inv_ne_zero hs)) hj

/-- Positive Euler scaling preserves the full finite prime quadratic Calkin injection. -/
theorem finitePrimeEvenPositiveEulerGram_not_isCompactOperator_of_ne_zero
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ≠ 0) :
    ¬ IsCompactOperator
      (finiteEvenPositiveEulerGramCombination a (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) A) := by
  rw [finiteEvenPositiveEulerGramCombination_eq_dilation]
  exact finitePrimeEvenDilationGram_not_isCompactOperator_of_ne_zero
    a ha p hp hinj (finiteEulerGramRescale (fun i => (p i : ℝ)) A)
      (finiteEulerGramRescale_ne_zero (fun i => (p i : ℝ))
        (fun i => by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) A hA)

theorem unitaryPush_fintype_sum
    {ι H K : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : H ≃ₗᵢ[ℂ] K) (T : ι → H →L[ℂ] H) :
    unitaryPush u (∑ i, T i) = ∑ i, unitaryPush u (T i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [unitaryPush]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, unitaryPush_add, ih]

def finiteArchimedeanPrimeEulerGramCombination
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  ∑ i, ∑ j, A i j • archimedeanPrimeEulerQuadraticCorner a (r i) (r j)

theorem finiteArchimedeanPrimeEulerGramCombination_eq_unitaryPush
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finiteArchimedeanPrimeEulerGramCombination a r A =
      unitaryPush archimedeanDualHardyTitchmarshUnitary
        (finiteEvenPositiveEulerGramCombination a r hr A) := by
  classical
  unfold finiteArchimedeanPrimeEulerGramCombination finiteEvenPositiveEulerGramCombination
  rw [unitaryPush_fintype_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [unitaryPush_fintype_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [unitaryPush_smul, archimedeanPrimeEulerQuadraticCorner_eq_unitaryPush]

/-- **Concrete source quadratic Calkin injectivity.** Every nonzero finite matrix combination of
literal prime Euler Gram corners on the Hardy--Titchmarsh line is noncompact. -/
theorem finitePrimeArchimedeanEulerGram_not_isCompactOperator_of_ne_zero
    {n : ℕ} (a : ℝ) (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ≠ 0) :
    ¬ IsCompactOperator
      (finiteArchimedeanPrimeEulerGramCombination a (fun i => (p i : ℝ)) A) := by
  let r : Fin n → ℝ := fun i => (p i : ℝ)
  let hr : ∀ i, 1 < r i := fun i => by
    change (1 : ℝ) < (p i : ℝ)
    exact_mod_cast (hp i).one_lt
  rw [finiteArchimedeanPrimeEulerGramCombination_eq_unitaryPush a r hr A]
  intro hcompact
  apply finitePrimeEvenPositiveEulerGram_not_isCompactOperator_of_ne_zero
    a ha p hp hinj A hA
  have hpull := IsCompactOperator.unitaryPush
    archimedeanDualHardyTitchmarshUnitary.symm _ hcompact
  simpa [unitaryPush_symm_unitaryPush] using hpull

end RHTower
