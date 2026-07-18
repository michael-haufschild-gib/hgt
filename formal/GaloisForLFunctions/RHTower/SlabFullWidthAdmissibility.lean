import GaloisForLFunctions.RHTower.SlabGermResidueTransport
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion

/-!
# Full-width slab admissibility

The germ-residue transport layer (`SlabGermResidueTransport`) reads the height-`γ` packet of
centered Xi zeros through contour moments on slabs `S(γ, h) = [γ − h, γ + h] × [−c, c]` in
the centered spectral frame, carrying pointwise admissibility of the four boundary edges as
a hypothesis (`SlabAdmissible`).  This module discharges that hypothesis.

* `XiC_ne_zero_of_half_le_abs_im` — the centered Xi function has no zeros on or beyond the
  horizontal lines `Im z = ±1/2`; in the Xi coordinate `s = 1/2 + z·I` these are the
  classical zero-free boundary lines `Re s = 1` and its functional-equation reflection
  `Re s = 0`;
* `exists_fullWidthSlabEdgeNonvanishing` — below the discreteness gap the **full-width**
  slab (band `c = 1/2`) has all four edges free of centered Xi zeros: the horizontal edges
  unconditionally by the strip bound, the vertical edges because the packet collapses onto
  the height fiber;
* `XiExplicitAdmissible_of_abs_im_lt_half` / `XiExplicitAdmissible_of_im_eq_neg_half` —
  pointwise admissibility of the continued trace at every strip-interior point avoiding
  the divisor, and along the entire line `Im z = −1/2` (`Re s = 1`) away from the
  completed pole;
* `slabAdmissible_of_slabEdgeNonvanishing` — on bands `c < 1/2` edge nonvanishing upgrades
  to full slab admissibility;
* `exists_slabAdmissible_family` — **the unconditional admissible family**: at every height
  there is a band strictly wider than every offset of the height fiber yet strictly inside
  the critical strip, so the fiber over the band is the full height fiber and every slab
  below the discreteness gap is admissible outright;
* `exists_germResidueTransport_unconditional`, `exists_slabContourGram_germ_unconditional`,
  `exists_slabContourGram_germ_eq_zero_iff`, `tendsto_slabContourGram_unconditional` — the
  germ-residue transport, the Gram germ, and the boundary-computable single-point
  criterion with the admissibility hypothesis discharged.

At `c = 1/2` the top edge lies on `Re s = 0`, outside the positive-half-plane domain of the
continued trace surface, so the contour on the literal full-width slab requires the
functional-equation reflection of the trace itself.  The sub-critical family above already
captures the complete height fiber, so no transport content is lost by staying strictly
inside the strip.
-/


open Complex Set Filter Topology

namespace RHTower
namespace SlabFullWidthAdmissibility

open SlabGermResidueTransport

noncomputable section

/-! ## §1 The classical boundary lines are free of centered Xi zeros -/

/-- The centered Xi function has no zeros on or beyond the horizontal lines `Im z = ±1/2`:
the closed exterior of the open critical band is zero-free. -/
theorem XiC_ne_zero_of_half_le_abs_im {z : ℂ} (hz : 1 / 2 ≤ |z.im|) : XiC z ≠ 0 := by
  intro h0
  obtain ⟨h1, h2⟩ := xiC_zero_im_mem_openHalf h0
  have habs : |z.im| < 1 / 2 := abs_lt.mpr ⟨by linarith, h2⟩
  linarith

/-- No centered Xi zeros on the line `Im z = −1/2`, the classical zero-free line
`Re s = 1`. -/
theorem XiC_ne_zero_of_im_eq_neg_half {z : ℂ} (him : z.im = -(1 / 2)) : XiC z ≠ 0 :=
  XiC_ne_zero_of_half_le_abs_im (by rw [him]; norm_num)

/-- No centered Xi zeros on the line `Im z = 1/2`, the functional-equation reflection
`Re s = 0` of the classical zero-free line. -/
theorem XiC_ne_zero_of_im_eq_half {z : ℂ} (him : z.im = 1 / 2) : XiC z ≠ 0 :=
  XiC_ne_zero_of_half_le_abs_im (by rw [him]; norm_num)

/-! ## §2 Pointwise admissibility of the trace surface -/

/-- Away from `Im z = −1/2` the Xi coordinate `1/2 + z·I` avoids the completed pole `1`. -/
theorem xiCoord_ne_one_of_im_ne {z : ℂ} (him : z.im ≠ -(1 / 2)) :
    (1 / 2 : ℂ) + z * I ≠ 1 := by
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  apply him
  linarith

/-- Every strip-interior point avoiding the centered Xi divisor is admissible for the
continued Guinand–Weil trace. -/
theorem XiExplicitAdmissible_of_abs_im_lt_half {z : ℂ} (him : |z.im| < 1 / 2)
    (hXi : XiC z ≠ 0) : XiExplicitAdmissible z := by
  obtain ⟨h1, h2⟩ := abs_lt.mp him
  refine XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero h2 ?_ hXi
  refine xiCoord_ne_one_of_im_ne fun h => ?_
  rw [h] at h1
  exact lt_irrefl _ h1

/-- **The `Re s = 1` edge is admissible.**  Every point of the classical line `Im z = −1/2`
away from the completed pole (`Re z ≠ 0`) is admissible: the zeta nonvanishing on `Re s = 1`
is carried by the zero-freeness of the completed Xi there. -/
theorem XiExplicitAdmissible_of_im_eq_neg_half {z : ℂ} (him : z.im = -(1 / 2))
    (hre : z.re ≠ 0) : XiExplicitAdmissible z := by
  refine XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    (by rw [him]; norm_num) ?_ (XiC_ne_zero_of_im_eq_neg_half him)
  intro h
  have h' := congrArg Complex.im h
  simp at h'
  exact hre h'

/-! ## §3 Edge nonvanishing and the full-width slab -/

/-- Freedom of the four slab edges from centered Xi zeros. -/
structure SlabEdgeNonvanishing (γ h c : ℝ) : Prop where
  bottom : ∀ x ∈ uIcc (γ - h) (γ + h), XiC ((x : ℂ) + ((-c : ℝ) : ℂ) * I) ≠ 0
  top : ∀ x ∈ uIcc (γ - h) (γ + h), XiC ((x : ℂ) + ((c : ℝ) : ℂ) * I) ≠ 0
  right : ∀ y ∈ uIcc (-c) c, XiC (((γ + h : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0
  left : ∀ y ∈ uIcc (-c) c, XiC (((γ - h : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0

/-- **Full-width slab edge nonvanishing.**  Below the discreteness gap the full-width slab
(band `c = 1/2`, edges on the classical zero-free lines) has all four edges free of
centered Xi zeros: the horizontal edges unconditionally by the strip bound, the vertical
edges because the packet collapses onto the height fiber. -/
theorem exists_fullWidthSlabEdgeNonvanishing (γ : ℝ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → SlabEdgeNonvanishing γ h (1 / 2) := by
  obtain ⟨h₀, hh₀pos, _, hgap⟩ := exists_slabGap γ (1 / 2) (by norm_num)
  refine ⟨h₀, hh₀pos, fun h hh0 hh => ?_⟩
  have hc0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _
    exact XiC_ne_zero_of_im_eq_neg_half (by simp)
  · intro x _
    exact XiC_ne_zero_of_im_eq_half (by simp)
  · intro y hy
    rw [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] at hy
    intro h0
    have hpre : (((γ + h : ℝ) : ℂ) + (y : ℂ) * I).re = γ + h := by simp
    have hpim : (((γ + h : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    have hin : (((γ + h : ℝ) : ℂ) + (y : ℂ) * I) ∈ slabPacket γ h (1 / 2) :=
      (mem_slabPacket hh0.le hc0).mpr
        ⟨⟨⟨by rw [hpre]; linarith, by rw [hpre]⟩,
          by rw [hpim]; exact hy.1, by rw [hpim]; exact hy.2⟩, h0⟩
    rw [hgap h hh0 hh] at hin
    have hfre := ((mem_heightFiber hc0).mp hin).1
    rw [hpre] at hfre
    linarith
  · intro y hy
    rw [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] at hy
    intro h0
    have hpre : (((γ - h : ℝ) : ℂ) + (y : ℂ) * I).re = γ - h := by simp
    have hpim : (((γ - h : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    have hin : (((γ - h : ℝ) : ℂ) + (y : ℂ) * I) ∈ slabPacket γ h (1 / 2) :=
      (mem_slabPacket hh0.le hc0).mpr
        ⟨⟨⟨by rw [hpre], by rw [hpre]; linarith⟩,
          by rw [hpim]; exact hy.1, by rw [hpim]; exact hy.2⟩, h0⟩
    rw [hgap h hh0 hh] at hin
    have hfre := ((mem_heightFiber hc0).mp hin).1
    rw [hpre] at hfre
    linarith

/-! ## §4 From edge nonvanishing to slab admissibility on sub-critical bands -/

/-- On a band strictly inside the critical strip, edge nonvanishing upgrades to full slab
admissibility of the continued trace. -/
theorem slabAdmissible_of_slabEdgeNonvanishing {γ h c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2)
    (hedge : SlabEdgeNonvanishing γ h c) : SlabAdmissible γ h c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    refine XiExplicitAdmissible_of_abs_im_lt_half ?_ (hedge.bottom x hx)
    have him : ((x : ℂ) + ((-c : ℝ) : ℂ) * I).im = -c := by simp
    rw [him, abs_neg, abs_of_nonneg hc0]
    exact hc
  · intro x hx
    refine XiExplicitAdmissible_of_abs_im_lt_half ?_ (hedge.top x hx)
    have him : ((x : ℂ) + ((c : ℝ) : ℂ) * I).im = c := by simp
    rw [him, abs_of_nonneg hc0]
    exact hc
  · intro y hy
    have hy' := hy
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hy'
    refine XiExplicitAdmissible_of_abs_im_lt_half ?_ (hedge.right y hy)
    have him : (((γ + h : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [him]
    have habs : |y| ≤ c := abs_le.mpr ⟨hy'.1, hy'.2⟩
    linarith
  · intro y hy
    have hy' := hy
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hy'
    refine XiExplicitAdmissible_of_abs_im_lt_half ?_ (hedge.left y hy)
    have him : (((γ - h : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [him]
    have habs : |y| ≤ c := abs_le.mpr ⟨hy'.1, hy'.2⟩
    linarith

/-! ## §5 The unconditional admissible slab family -/

/-- **The unconditional admissible slab family.**  At every height there is a band strictly
wider than every offset of the height fiber yet strictly inside the critical strip; over
that band the fiber equals the full height fiber, and every slab below the discreteness gap
is admissible outright. -/
theorem exists_slabAdmissible_family (γ : ℝ) :
    ∃ c h₀ : ℝ, 0 < c ∧ c < 1 / 2 ∧ 0 < h₀ ∧
      heightFiber γ c = heightFiber γ (1 / 2) ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ → SlabAdmissible γ h c := by
  classical
  have h012 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  obtain ⟨M, hM0, hMlt, hMbound⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ M < 1 / 2 ∧ ∀ w ∈ heightFiber γ (1 / 2), |w.im| ≤ M := by
    by_cases hF : (heightFiber γ (1 / 2)).Nonempty
    · refine ⟨(heightFiber γ (1 / 2)).sup' hF fun w : ℂ => |w.im|, ?_, ?_, ?_⟩
      · obtain ⟨w0, hw0⟩ := hF
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun w : ℂ => |w.im|) hw0)
      · rw [Finset.sup'_lt_iff]
        intro w hw
        have hzero := ((mem_heightFiber h012).mp hw).2.2
        obtain ⟨hlow, hhigh⟩ := xiC_zero_im_mem_openHalf hzero
        rw [abs_lt]
        constructor <;> linarith
      · intro w hw
        exact Finset.le_sup' (fun w : ℂ => |w.im|) hw
    · exact ⟨0, le_refl 0, by norm_num, fun w hw => absurd ⟨w, hw⟩ hF⟩
  obtain ⟨c, hc0, hcM, hc12⟩ : ∃ c : ℝ, 0 < c ∧ M < c ∧ c < 1 / 2 :=
    ⟨(M + 1 / 2) / 2, by linarith, by linarith, by linarith⟩
  have hfib : heightFiber γ c = heightFiber γ (1 / 2) := by
    apply Finset.ext
    intro w
    rw [mem_heightFiber hc0.le, mem_heightFiber h012]
    constructor
    · rintro ⟨hre, ⟨hl, hr⟩, hXi⟩
      exact ⟨hre, ⟨by linarith, by linarith⟩, hXi⟩
    · rintro ⟨hre, hband, hXi⟩
      have hwF : w ∈ heightFiber γ (1 / 2) :=
        (mem_heightFiber h012).mpr ⟨hre, hband, hXi⟩
      obtain ⟨hl, hr⟩ := abs_le.mp (hMbound w hwF)
      exact ⟨hre, ⟨by linarith, by linarith⟩, hXi⟩
  obtain ⟨h₀, hh₀pos, _, hgap⟩ := exists_slabGap γ c hc0.le
  refine ⟨c, h₀, hc0, hc12, hh₀pos, hfib, ?_⟩
  intro h hh0 hh
  apply slabAdmissible_of_slabEdgeNonvanishing hc0.le hc12
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx h0
    rw [uIcc_of_le (by linarith : γ - h ≤ γ + h)] at hx
    have hpre : ((x : ℂ) + ((-c : ℝ) : ℂ) * I).re = x := by simp
    have hpim : ((x : ℂ) + ((-c : ℝ) : ℂ) * I).im = -c := by simp
    have hin : ((x : ℂ) + ((-c : ℝ) : ℂ) * I) ∈ slabPacket γ h c :=
      (mem_slabPacket hh0.le hc0.le).mpr
        ⟨⟨⟨by rw [hpre]; exact hx.1, by rw [hpre]; exact hx.2⟩,
          by rw [hpim], by rw [hpim]; linarith⟩, h0⟩
    rw [hgap h hh0 hh, hfib] at hin
    have habs := hMbound _ hin
    rw [hpim, abs_neg, abs_of_nonneg hc0.le] at habs
    linarith
  · intro x hx h0
    rw [uIcc_of_le (by linarith : γ - h ≤ γ + h)] at hx
    have hpre : ((x : ℂ) + ((c : ℝ) : ℂ) * I).re = x := by simp
    have hpim : ((x : ℂ) + ((c : ℝ) : ℂ) * I).im = c := by simp
    have hin : ((x : ℂ) + ((c : ℝ) : ℂ) * I) ∈ slabPacket γ h c :=
      (mem_slabPacket hh0.le hc0.le).mpr
        ⟨⟨⟨by rw [hpre]; exact hx.1, by rw [hpre]; exact hx.2⟩,
          by rw [hpim]; linarith, by rw [hpim]⟩, h0⟩
    rw [hgap h hh0 hh, hfib] at hin
    have habs := hMbound _ hin
    rw [hpim, abs_of_nonneg hc0.le] at habs
    linarith
  · intro y hy h0
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hy
    have hpre : (((γ + h : ℝ) : ℂ) + (y : ℂ) * I).re = γ + h := by simp
    have hpim : (((γ + h : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    have hin : (((γ + h : ℝ) : ℂ) + (y : ℂ) * I) ∈ slabPacket γ h c :=
      (mem_slabPacket hh0.le hc0.le).mpr
        ⟨⟨⟨by rw [hpre]; linarith, by rw [hpre]⟩,
          by rw [hpim]; exact hy.1, by rw [hpim]; exact hy.2⟩, h0⟩
    rw [hgap h hh0 hh] at hin
    have hfre := ((mem_heightFiber hc0.le).mp hin).1
    rw [hpre] at hfre
    linarith
  · intro y hy h0
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hy
    have hpre : (((γ - h : ℝ) : ℂ) + (y : ℂ) * I).re = γ - h := by simp
    have hpim : (((γ - h : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    have hin : (((γ - h : ℝ) : ℂ) + (y : ℂ) * I) ∈ slabPacket γ h c :=
      (mem_slabPacket hh0.le hc0.le).mpr
        ⟨⟨⟨by rw [hpre], by rw [hpre]; linarith⟩,
          by rw [hpim]; exact hy.1, by rw [hpim]; exact hy.2⟩, h0⟩
    rw [hgap h hh0 hh] at hin
    have hfre := ((mem_heightFiber hc0.le).mp hin).1
    rw [hpre] at hfre
    linarith

/-! ## §6 The transport with the admissibility hypothesis discharged -/

/-- **Unconditional germ-residue transport.**  At every height there are a band and a gap
below which every slab contour moment equals the divisor moment of the full height fiber. -/
theorem exists_germResidueTransport_unconditional (γ : ℝ) :
    ∃ c h₀ : ℝ, 0 < c ∧ c < 1 / 2 ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℕ,
      slabContourMoment k γ h c = packetDivisorMoment (heightFiber γ (1 / 2)) k := by
  obtain ⟨c, h₁, hc0, hc12, hh₁pos, hfib, hadm⟩ := exists_slabAdmissible_family γ
  obtain ⟨h₀, hh₀pos, _, htrans⟩ := exists_germResidueTransport hc0 hh₁pos hadm
  refine ⟨c, h₀, hc0, hc12, hh₀pos, fun h hh0 hh k => ?_⟩
  rw [htrans h hh0 hh k, hfib]

/-- **Unconditional Gram germ.**  At every height, below the gap the slab contour Gram
expression `p₀p₂ − p₁²` equals the full height-fiber packet Gram expression — a
nonpositive real number. -/
theorem exists_slabContourGram_germ_unconditional (γ : ℝ) :
    ∃ c h₀ : ℝ, 0 < c ∧ c < 1 / 2 ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      slabContourGram γ h c = heightFiberGram γ (1 / 2) ∧
        (slabContourGram γ h c).re ≤ 0 ∧ (slabContourGram γ h c).im = 0 := by
  obtain ⟨c, h₁, hc0, hc12, hh₁pos, hfib, hadm⟩ := exists_slabAdmissible_family γ
  obtain ⟨h₀, hh₀pos, _, hgram⟩ := exists_slabContourGram_germ hc0 hh₁pos hadm
  have hfg : heightFiberGram γ c = heightFiberGram γ (1 / 2) := by
    simp only [heightFiberGram]
    rw [hfib]
  refine ⟨c, h₀, hc0, hc12, hh₀pos, fun h hh0 hh => ?_⟩
  obtain ⟨he, hre, him⟩ := hgram h hh0 hh
  exact ⟨he.trans hfg, hre, him⟩

/-- **Boundary-computable single-point criterion, unconditional form.**  Below the gap the
slab contour Gram expression vanishes iff the full height fiber is a single point. -/
theorem exists_slabContourGram_germ_eq_zero_iff (γ : ℝ) :
    ∃ c h₀ : ℝ, 0 < c ∧ c < 1 / 2 ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      (slabContourGram γ h c = 0 ↔
        ∀ w ∈ heightFiber γ (1 / 2), ∀ w' ∈ heightFiber γ (1 / 2), w = w') := by
  obtain ⟨c, h₀, hc0, hc12, hh₀pos, hgram⟩ := exists_slabContourGram_germ_unconditional γ
  refine ⟨c, h₀, hc0, hc12, hh₀pos, fun h hh0 hh => ?_⟩
  rw [(hgram h hh0 hh).1]
  exact heightFiberGram_eq_zero_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- **Unconditional limit form.**  At every height there is a band on which the slab
contour Gram expression converges, as the half-width shrinks, to the full height-fiber
Gram expression. -/
theorem tendsto_slabContourGram_unconditional (γ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      Tendsto (fun h : ℝ => slabContourGram γ h c) (𝓝[>] (0 : ℝ))
        (𝓝 (heightFiberGram γ (1 / 2))) := by
  obtain ⟨c, h₁, hc0, hc12, hh₁pos, hfib, hadm⟩ := exists_slabAdmissible_family γ
  have hfg : heightFiberGram γ c = heightFiberGram γ (1 / 2) := by
    simp only [heightFiberGram]
    rw [hfib]
  refine ⟨c, hc0, hc12, ?_⟩
  rw [← hfg]
  exact tendsto_slabContourGram_heightFiberGram hc0 hh₁pos hadm

end

end SlabFullWidthAdmissibility
end RHTower
