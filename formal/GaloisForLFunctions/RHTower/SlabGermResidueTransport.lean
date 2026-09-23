import GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling
import GaloisForLFunctions.RHTower.CoHighPacketGramCollapse

/-!
# The slab germ-residue transport layer

The slab-germ certificate reads the height-`γ` packet of centered Xi zeros through contour
moments on a shrinking slab.  In the centered spectral frame (`XiC z = xi (1/2 + z·I)`,
heights on the real axis, the critical strip the horizontal band `|Im z| < 1/2`) the slab
`S(γ, h)` is the closed rectangle `[γ − h, γ + h] × [−c, c]`, and the `k`-th contour moment
is `p_k = (2πi)⁻¹ ∮_{∂S} z^k · (continued prime–archimedean source trace)`.

This module is the transport layer between the boundary integrals and the divisor packet:

* `slabContourMoment_eq_packetDivisorMoment` — **argument-principle reading**: on a slab
  with pointwise admissible boundary the contour moment equals the multiplicity-weighted
  divisor moment `∑_{ρ ∈ packet} m_ρ · ρ^k`, by specializing the closed-rectangle
  Guinand–Weil extraction to the monomial weight `z^k`;
* `exists_slabGap` — **eventual constancy**: by discreteness of the Xi divisor the slab
  packet is constant for all slab half-heights below an explicit gap, equal to the
  height fiber `{ρ : Re ρ = γ}` of the divisor;
* `exists_germResidueTransport` / `tendsto_slabContourMoment_heightFiberMoment` — the
  **germ-residue transport**: for every `k` the contour moment is eventually constant as
  `h → 0⁺` and its germ value is the height-fiber divisor moment;
* `slabContourGram` / `heightFiberGram` — the Gram combination `p₀p₂ − p₁²` transports to
  the fiber packet Gram expression, which by the co-high collapse
  (`CoHighPacketGramCollapse`) is a **nonpositive real number**, vanishing iff the height
  fiber is a single point: `heightFiberGram_re_nonpos`, `heightFiberGram_im`,
  `heightFiberGram_eq_zero_iff`, and the glued germ statement
  `exists_slabContourGram_germ`.

Admissibility of the slab boundary is carried as a hypothesis (`SlabAdmissible`): the
`XiExplicitAdmissible` trace surface requires `Re (1/2 + z·I) > 0`, i.e. `Im z < 1/2`
strictly, so the full-width slab with edges on the classical zero-free lines
(`Im z = ±1/2`) needs the functional-equation reflection of the trace — that adapter is
the remaining surface, not built here.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.RHTower.CoHighPacketGramCollapse

namespace RHTower
namespace SlabGermResidueTransport

noncomputable section

/-! ## §1 Slab geometry in the centered spectral frame -/

/-- Lower-left corner of the slab `S(γ, h)` with strip half-width `c`. -/
def slabLower (γ h c : ℝ) : ℂ := ((γ - h : ℝ) : ℂ) - (c : ℂ) * I

/-- Upper-right corner of the slab `S(γ, h)` with strip half-width `c`. -/
def slabUpper (γ h c : ℝ) : ℂ := ((γ + h : ℝ) : ℂ) + (c : ℂ) * I

@[simp] theorem slabLower_re (γ h c : ℝ) : (slabLower γ h c).re = γ - h := by
  simp [slabLower]

@[simp] theorem slabLower_im (γ h c : ℝ) : (slabLower γ h c).im = -c := by
  simp [slabLower]

@[simp] theorem slabUpper_re (γ h c : ℝ) : (slabUpper γ h c).re = γ + h := by
  simp [slabUpper]

@[simp] theorem slabUpper_im (γ h c : ℝ) : (slabUpper γ h c).im = c := by
  simp [slabUpper]

/-! ## §2 The slab packet and the height fiber -/

/-- The finite packet of centered Xi zeros in the closed slab. -/
def slabPacket (γ h c : ℝ) : Finset ℂ :=
  xiCClosedRectangleZeros (slabLower γ h c) (slabUpper γ h c)

theorem mem_slabPacket {γ h c : ℝ} (hh : 0 ≤ h) (hc : 0 ≤ c) {z : ℂ} :
    z ∈ slabPacket γ h c ↔
      ((γ - h ≤ z.re ∧ z.re ≤ γ + h) ∧ (-c ≤ z.im ∧ z.im ≤ c)) ∧ XiC z = 0 := by
  rw [slabPacket, mem_xiCClosedRectangleZeros, slabLower_re, slabLower_im, slabUpper_re,
    slabUpper_im, Set.uIcc_of_le (by linarith : γ - h ≤ γ + h),
    Set.uIcc_of_le (by linarith : -c ≤ c), Complex.mem_reProdIm, Set.mem_Icc, Set.mem_Icc]

/-- The height fiber: the centered Xi zeros at exact height `γ` within the strip band
`|Im z| ≤ c`. -/
def heightFiber (γ c : ℝ) : Finset ℂ :=
  (slabPacket γ 1 c).filter fun z => z.re = γ

theorem mem_heightFiber {γ c : ℝ} (hc : 0 ≤ c) {z : ℂ} :
    z ∈ heightFiber γ c ↔ z.re = γ ∧ (-c ≤ z.im ∧ z.im ≤ c) ∧ XiC z = 0 := by
  rw [heightFiber, Finset.mem_filter, mem_slabPacket zero_le_one hc]
  constructor
  · rintro ⟨⟨⟨_, him⟩, hXi⟩, hre⟩
    exact ⟨hre, him, hXi⟩
  · rintro ⟨hre, him, hXi⟩
    exact ⟨⟨⟨⟨by rw [hre]; linarith, by rw [hre]; linarith⟩, him⟩, hXi⟩, hre⟩

/-! ## §3 Eventual constancy: the slab packet below the discreteness gap -/

/-- **The slab gap.**  By discreteness of the centered Xi divisor there is a positive gap
`h₀` below which the slab packet is exactly the height fiber: the packet Finset of
`S(γ, h)` is constant for all `0 < h ≤ h₀`. -/
theorem exists_slabGap (γ c : ℝ) (hc : 0 ≤ c) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      slabPacket γ h c = heightFiber γ c := by
  classical
  by_cases hFne : ((slabPacket γ 1 c).filter fun z => z.re ≠ γ).Nonempty
  · refine ⟨min 1 (((slabPacket γ 1 c).filter fun z => z.re ≠ γ).inf' hFne
        (fun z => |z.re - γ|) / 2), ?_, min_le_left _ _, ?_⟩
    · have hεpos : 0 < ((slabPacket γ 1 c).filter fun z => z.re ≠ γ).inf' hFne
          (fun z => |z.re - γ|) := by
        refine (Finset.lt_inf'_iff hFne).mpr fun z hz => ?_
        rw [Finset.mem_filter] at hz
        exact abs_pos.mpr (sub_ne_zero.mpr hz.2)
      exact lt_min one_pos (by linarith)
    · intro h hh0 hh
      have hh1 : h ≤ 1 := hh.trans (min_le_left _ _)
      apply Finset.ext
      intro z
      rw [mem_slabPacket hh0.le hc, mem_heightFiber hc]
      constructor
      · rintro ⟨⟨⟨hre1, hre2⟩, him⟩, hXi⟩
        refine ⟨?_, him, hXi⟩
        by_contra hne
        have hzF : z ∈ (slabPacket γ 1 c).filter fun z => z.re ≠ γ :=
          Finset.mem_filter.mpr
            ⟨(mem_slabPacket zero_le_one hc).mpr
              ⟨⟨⟨by linarith, by linarith⟩, him⟩, hXi⟩, hne⟩
        have hle : ((slabPacket γ 1 c).filter fun z => z.re ≠ γ).inf' hFne
            (fun z => |z.re - γ|) ≤ |z.re - γ| := Finset.inf'_le _ hzF
        have habs : |z.re - γ| ≤ h := abs_le.mpr ⟨by linarith, by linarith⟩
        have hh2 : h ≤ ((slabPacket γ 1 c).filter fun z => z.re ≠ γ).inf' hFne
            (fun z => |z.re - γ|) / 2 := hh.trans (min_le_right _ _)
        linarith
      · rintro ⟨hre, him, hXi⟩
        exact ⟨⟨⟨by rw [hre]; linarith, by rw [hre]; linarith⟩, him⟩, hXi⟩
  · refine ⟨1, one_pos, le_refl 1, ?_⟩
    intro h hh0 hh
    apply Finset.ext
    intro z
    rw [mem_slabPacket hh0.le hc, mem_heightFiber hc]
    constructor
    · rintro ⟨⟨⟨hre1, hre2⟩, him⟩, hXi⟩
      refine ⟨?_, him, hXi⟩
      by_contra hne
      exact hFne ⟨z, Finset.mem_filter.mpr
        ⟨(mem_slabPacket zero_le_one hc).mpr
          ⟨⟨⟨by linarith, by linarith⟩, him⟩, hXi⟩, hne⟩⟩
    · rintro ⟨hre, him, hXi⟩
      exact ⟨⟨⟨by rw [hre]; linarith, by rw [hre]; linarith⟩, him⟩, hXi⟩

/-! ## §4 Divisor moments and packet masses -/

/-- The real mass of a divisor point: the analytic multiplicity of `XiC`. -/
def xiPacketMass (w : ℂ) : ℝ := ((analyticOrderAt XiC w).toNat : ℝ)

/-- Divisor points carry positive mass. -/
theorem xiPacketMass_pos {w : ℂ} (hw : XiC w = 0) : 0 < xiPacketMass w := by
  have h0 : analyticOrderAt XiC w ≠ 0 := by
    intro h
    rcases analyticOrderAt_eq_zero.mp h with h' | h'
    · exact h' (XiC_analytic w (Set.mem_univ w))
    · exact h' hw
  have hpos : 0 < (analyticOrderAt XiC w).toNat := by
    refine Nat.pos_of_ne_zero fun hz => ?_
    rcases ENat.toNat_eq_zero.mp hz with h | h
    · exact h0 h
    · exact XiC_order_ne_top w h
  simpa [xiPacketMass] using hpos

/-- The `k`-th multiplicity-weighted divisor moment of a finite packet of centered Xi
zeros: `∑_ρ m_ρ · ρ^k` in the spectral frame. -/
def packetDivisorMoment (P : Finset ℂ) (k : ℕ) : ℂ :=
  ∑ w ∈ P, ((analyticOrderAt XiC w).toNat : ℂ) * w ^ k

/-- The divisor moment is the abstract packet moment of `CoHighPacketGramCollapse` at the
identity point family with the multiplicity masses. -/
theorem packetDivisorMoment_eq_packetMoment (P : Finset ℂ) (k : ℕ) :
    packetDivisorMoment P k = packetMoment P xiPacketMass id k := by
  unfold packetDivisorMoment packetMoment xiPacketMass
  refine Finset.sum_congr rfl fun w _ => ?_
  push_cast
  rfl

/-! ## §5 The contour moments and the argument-principle reading -/

/-- Pointwise admissibility of the four slab edges for the continued Guinand–Weil trace. -/
structure SlabAdmissible (γ h c : ℝ) : Prop where
  bottom : ∀ x ∈ uIcc (γ - h) (γ + h), XiExplicitAdmissible ((x : ℂ) + ((-c : ℝ) : ℂ) * I)
  top : ∀ x ∈ uIcc (γ - h) (γ + h), XiExplicitAdmissible ((x : ℂ) + ((c : ℝ) : ℂ) * I)
  right : ∀ y ∈ uIcc (-c) c, XiExplicitAdmissible (((γ + h : ℝ) : ℂ) + (y : ℂ) * I)
  left : ∀ y ∈ uIcc (-c) c, XiExplicitAdmissible (((γ - h : ℝ) : ℂ) + (y : ℂ) * I)

/-- The `k`-th slab contour moment
`p_k(S(γ,h)) = (2πi)⁻¹ ∮_{∂S} z^k · (continued prime–archimedean source trace)`. -/
def slabContourMoment (k : ℕ) (γ h c : ℝ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral (fun z => z ^ k * continuedPrimeArchSourceRelativeTrace z)
      (slabLower γ h c) (slabUpper γ h c)

private theorem two_pi_I_ne_zero : (2 * Real.pi * I : ℂ) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
  exact_mod_cast Real.pi_ne_zero

/-- **Argument-principle transport.**  On an admissible slab the `k`-th contour moment is
the multiplicity-weighted divisor moment of the enclosed packet. -/
theorem slabContourMoment_eq_packetDivisorMoment {γ h c : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hadm : SlabAdmissible γ h c) (k : ℕ) :
    slabContourMoment k γ h c = packetDivisorMoment (slabPacket γ h c) k := by
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => z ^ k) Set.univ :=
    (differentiable_id.pow k).differentiableOn.analyticOnNhd isOpen_univ
  have hre : (slabLower γ h c).re < (slabUpper γ h c).re := by
    rw [slabLower_re, slabUpper_re]; linarith
  have him : (slabLower γ h c).im < (slabUpper γ h c).im := by
    rw [slabLower_im, slabUpper_im]; linarith
  have hbot : ∀ x ∈ uIcc (slabLower γ h c).re (slabUpper γ h c).re,
      XiExplicitAdmissible ((x : ℂ) + ((slabLower γ h c).im : ℂ) * I) := by
    intro x hx
    rw [slabLower_re, slabUpper_re] at hx
    rw [slabLower_im]
    exact hadm.bottom x hx
  have htop : ∀ x ∈ uIcc (slabLower γ h c).re (slabUpper γ h c).re,
      XiExplicitAdmissible ((x : ℂ) + ((slabUpper γ h c).im : ℂ) * I) := by
    intro x hx
    rw [slabLower_re, slabUpper_re] at hx
    rw [slabUpper_im]
    exact hadm.top x hx
  have hrig : ∀ y ∈ uIcc (slabLower γ h c).im (slabUpper γ h c).im,
      XiExplicitAdmissible (((slabUpper γ h c).re : ℂ) + (y : ℂ) * I) := by
    intro y hy
    rw [slabLower_im, slabUpper_im] at hy
    rw [slabUpper_re]
    exact hadm.right y hy
  have hlef : ∀ y ∈ uIcc (slabLower γ h c).im (slabUpper γ h c).im,
      XiExplicitAdmissible (((slabLower γ h c).re : ℂ) + (y : ℂ) * I) := by
    intro y hy
    rw [slabLower_im, slabUpper_im] at hy
    rw [slabLower_re]
    exact hadm.left y hy
  have hmain := rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
    hg hre him hbot htop hrig hlef
  unfold slabContourMoment
  rw [hmain, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  rfl

/-! ## §6 The germ-residue transport -/

/-- **Germ-residue transport, eventual form.**  Below the discreteness gap every slab
contour moment equals the height-fiber divisor moment: the map `h ↦ p_k(S(γ,h))` is
eventually constant as `h → 0⁺`, with germ value `∑_{Re ρ = γ} m_ρ · ρ^k`. -/
theorem exists_germResidueTransport {γ c h₁ : ℝ} (hc : 0 < c) (hh₁ : 0 < h₁)
    (hadm : ∀ h : ℝ, 0 < h → h ≤ h₁ → SlabAdmissible γ h c) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ h₁ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℕ,
      slabContourMoment k γ h c = packetDivisorMoment (heightFiber γ c) k := by
  obtain ⟨g₀, hg₀pos, _, hg₀⟩ := exists_slabGap γ c hc.le
  refine ⟨min g₀ h₁, lt_min hg₀pos hh₁, min_le_right _ _, ?_⟩
  intro h hh0 hh k
  rw [slabContourMoment_eq_packetDivisorMoment hh0 hc
      (hadm h hh0 (hh.trans (min_le_right _ _))) k,
    hg₀ h hh0 (hh.trans (min_le_left _ _))]

/-- **Germ-residue transport, limit form.**  The slab contour moment converges as
`h → 0⁺` to the height-fiber divisor moment. -/
theorem tendsto_slabContourMoment_heightFiberMoment {γ c h₁ : ℝ} (hc : 0 < c)
    (hh₁ : 0 < h₁) (hadm : ∀ h : ℝ, 0 < h → h ≤ h₁ → SlabAdmissible γ h c) (k : ℕ) :
    Tendsto (fun h : ℝ => slabContourMoment k γ h c) (𝓝[>] (0 : ℝ))
      (𝓝 (packetDivisorMoment (heightFiber γ c) k)) := by
  obtain ⟨h₀, hh₀pos, _, hh₀⟩ := exists_germResidueTransport hc hh₁ hadm
  have hevent : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      slabContourMoment k γ h c = packetDivisorMoment (heightFiber γ c) k := by
    have hupper : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h ≤ h₀ :=
      Filter.Eventually.filter_mono inf_le_left (Iic_mem_nhds hh₀pos)
    filter_upwards [self_mem_nhdsWithin, hupper] with h hh0 hhle
    exact hh₀ h hh0 hhle k
  exact tendsto_const_nhds.congr' (hevent.mono fun h hh => hh.symm)

/-! ## §7 The Gram combination and the co-high collapse of the fiber -/

/-- The slab contour Gram expression `p₀p₂ − p₁²` of the three boundary moments. -/
def slabContourGram (γ h c : ℝ) : ℂ :=
  slabContourMoment 0 γ h c * slabContourMoment 2 γ h c - slabContourMoment 1 γ h c ^ (2 : ℕ)

/-- The height-fiber packet Gram expression with multiplicity masses. -/
def heightFiberGram (γ c : ℝ) : ℂ :=
  packetGram (heightFiber γ c) xiPacketMass id

private theorem packetMoment_congr {ι : Type*} (s : Finset ι) (m : ι → ℝ) {u v : ι → ℂ}
    (huv : ∀ i ∈ s, u i = v i) (k : ℕ) :
    packetMoment s m u k = packetMoment s m v k :=
  Finset.sum_congr rfl fun i hi => by rw [huv i hi]

private theorem packetGram_congr {ι : Type*} (s : Finset ι) (m : ι → ℝ) {u v : ι → ℂ}
    (huv : ∀ i ∈ s, u i = v i) :
    packetGram s m u = packetGram s m v := by
  unfold packetGram
  rw [packetMoment_congr s m huv 0, packetMoment_congr s m huv 1,
    packetMoment_congr s m huv 2]

/-- On the height fiber the identity family is the co-high family at common height `γ`
with offsets `δ = −Im`. -/
theorem heightFiber_coHigh {γ c : ℝ} (hc : 0 ≤ c) :
    ∀ w ∈ heightFiber γ c, (id w : ℂ) = coHighFamily γ (fun z : ℂ => -z.im) w := by
  intro w hw
  obtain ⟨hre, _, _⟩ := (mem_heightFiber hc).mp hw
  apply Complex.ext <;> simp [coHighFamily, hre]

/-- An auxiliary linear order on `ℂ` (lexicographic), used only to invoke the ordered-pair
machinery of `CoHighPacketGramCollapse`; no statement depends on it. -/
@[reducible] private def complexLex : LinearOrder ℂ :=
  LinearOrder.lift' (fun z : ℂ => toLex (z.re, z.im))
    (fun a b hab => by
      have h : (a.re, a.im) = (b.re, b.im) := hab
      exact Complex.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- The height-fiber Gram expression is real. -/
theorem heightFiberGram_im {γ c : ℝ} (hc : 0 ≤ c) : (heightFiberGram γ c).im = 0 := by
  letI := complexLex
  rw [heightFiberGram, packetGram_congr _ _ (heightFiber_coHigh hc)]
  exact packetGram_coHigh_im _ _ _ _

/-- The height-fiber Gram expression is a nonpositive real: the co-high collapse of the
fiber packet. -/
theorem heightFiberGram_re_nonpos {γ c : ℝ} (hc : 0 ≤ c) :
    (heightFiberGram γ c).re ≤ 0 := by
  letI := complexLex
  rw [heightFiberGram, packetGram_congr _ _ (heightFiber_coHigh hc)]
  exact packetGram_coHigh_re_nonpos _ _ _
    fun w hw => (xiPacketMass_pos ((mem_heightFiber hc).mp hw).2.2).le

/-- **Single-point characterization of the fiber.**  The height-fiber Gram expression
vanishes iff the fiber is a single point — the Cauchy–Schwarz equality case of the
slab-germ certificate at height `γ`. -/
theorem heightFiberGram_eq_zero_iff {γ c : ℝ} (hc : 0 ≤ c) :
    heightFiberGram γ c = 0 ↔
      ∀ w ∈ heightFiber γ c, ∀ w' ∈ heightFiber γ c, w = w' := by
  letI := complexLex
  rw [heightFiberGram, packetGram_congr _ _ (heightFiber_coHigh hc),
    packetGram_coHigh_eq_zero_iff _ _ _
      fun w hw => xiPacketMass_pos ((mem_heightFiber hc).mp hw).2.2]
  constructor
  · intro hδ w hw w' hw'
    have him : -w.im = -w'.im := hδ w hw w' hw'
    have hre : w.re = w'.re := by
      rw [((mem_heightFiber hc).mp hw).1, ((mem_heightFiber hc).mp hw').1]
    exact Complex.ext hre (by linarith)
  · intro hpt w hw w' hw'
    rw [hpt w hw w' hw']

/-- **The germ of the slab Gram expression.**  Below the discreteness gap the contour Gram
expression `p₀p₂ − p₁²` of the slab equals the height-fiber packet Gram expression — in
particular it is a nonpositive real number, vanishing iff the fiber is a single point. -/
theorem exists_slabContourGram_germ {γ c h₁ : ℝ} (hc : 0 < c) (hh₁ : 0 < h₁)
    (hadm : ∀ h : ℝ, 0 < h → h ≤ h₁ → SlabAdmissible γ h c) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ h₁ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      slabContourGram γ h c = heightFiberGram γ c ∧
      (slabContourGram γ h c).re ≤ 0 ∧ (slabContourGram γ h c).im = 0 := by
  obtain ⟨h₀, hh₀pos, hh₀le, hh₀⟩ := exists_germResidueTransport hc hh₁ hadm
  refine ⟨h₀, hh₀pos, hh₀le, fun h hh0 hhle => ?_⟩
  have hgram : slabContourGram γ h c = heightFiberGram γ c := by
    rw [slabContourGram, hh₀ h hh0 hhle 0, hh₀ h hh0 hhle 1, hh₀ h hh0 hhle 2,
      packetDivisorMoment_eq_packetMoment, packetDivisorMoment_eq_packetMoment,
      packetDivisorMoment_eq_packetMoment, heightFiberGram, packetGram]
  exact ⟨hgram, hgram ▸ heightFiberGram_re_nonpos hc.le,
    hgram ▸ heightFiberGram_im hc.le⟩

/-- **Germ-residue transport of the Gram expression, limit form.** -/
theorem tendsto_slabContourGram_heightFiberGram {γ c h₁ : ℝ} (hc : 0 < c)
    (hh₁ : 0 < h₁) (hadm : ∀ h : ℝ, 0 < h → h ≤ h₁ → SlabAdmissible γ h c) :
    Tendsto (fun h : ℝ => slabContourGram γ h c) (𝓝[>] (0 : ℝ))
      (𝓝 (heightFiberGram γ c)) := by
  obtain ⟨h₀, hh₀pos, _, hh₀⟩ := exists_slabContourGram_germ hc hh₁ hadm
  have hevent : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      slabContourGram γ h c = heightFiberGram γ c := by
    have hupper : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h ≤ h₀ :=
      Filter.Eventually.filter_mono inf_le_left (Iic_mem_nhds hh₀pos)
    filter_upwards [self_mem_nhdsWithin, hupper] with h hh0 hhle
    exact (hh₀ h hh0 hhle).1
  exact tendsto_const_nhds.congr' (hevent.mono fun h hh => hh.symm)

end

end SlabGermResidueTransport
end RHTower
