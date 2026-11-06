import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTracesHaveTheirSoftKick

/-!
# The Green corner reads the potential

At `z = iy`, `y > 0`, the Riesz source of the window `[-x, x]` is driven by `e^{-y(t+x)}`, a source
concentrated at the left endpoint. Its right trace `τ_R(x,iy)` is the corner of the Green operator,
regularized at scale `1/y`, and its left trace `τ_L(x,iy)` is the normalization. Both are real, and
`τ_L² − τ_R² = 2y K_x(iy,iy)`, so `r_y = τ_R/τ_L` lies in `(−1,1)`.

* **Universality** (`artanh_spectralReflection_sub`): every `y` sees the same potential:
  `artanh r_y(b) − artanh r_y(a) = Ψ(b) − Ψ(a) − ∫_a^b q_y`, where
  `q_y = 2y r_y/(1−r_y²) = τ_L τ_R / K (x,iy)` (`spectralDrift_eq_traces`).
* **Coming down from infinity** (`le_of_strong_restoring`): the flow `L′ = dΨ − y sinh 2L` forgets its
  initial value, and `Ψ` is continuous, so `r_y(x) → 0` as `y → ∞`
  (`tendsto_artanh_spectralReflection_zero`).
* **The Gelfand–Levitan formula** (`tendsto_integral_spectralDrift`):
  `Ψ(b) − Ψ(a) = lim_{y→∞} ∫_a^b τ_L τ_R / K (x,iy) dx`. The potential is the Abel limit of the
  normalized corner of the Green operator. Its singular terms at `2a = log n` are
  `tendsto_canonicalPotential_right_kick`.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open _root_.RHTower
open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open SquareRootThreshold WindowVisibilityLaw Zeta23

/-! ### Coming down from infinity -/

/-- **Coming down from infinity.** A flow `D′ = −y sinh 2(D + ω)` with `ω ≥ −ε` lies below
`2ε + artanh e^{−2y(x−x₀)}` at time `x`, whatever its initial value: `artanh(c e^{−2y(s−x₀)})` solves
`w′ = −y sinh 2w`, and it starts arbitrarily high as `c ↑ 1`. -/
theorem le_of_strong_restoring {D ω : ℝ → ℝ} {y x₀ x ε : ℝ} (hy : 0 < y) (hx : x₀ < x) (hε : 0 < ε)
    (hDc : ContinuousOn D (Icc x₀ x)) (hω : ∀ s ∈ Icc x₀ x, -ε ≤ ω s)
    (hD : ∀ s ∈ Ico x₀ x, HasDerivWithinAt D (-y * Real.sinh (2 * (D s + ω s))) (Ici s) s) :
    D x ≤ 2 * ε + Real.artanh (Real.exp (-(2 * y * (x - x₀)))) := by
  have hM : 0 < max (D x₀) 1 := lt_max_of_lt_right one_pos
  obtain ⟨c, hc⟩ : ∃ c, c = Real.tanh (max (D x₀) 1) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hM) (Real.cosh_pos _)
  have hc1 : c < 1 := hc ▸ Real.tanh_lt_one _
  let t : ℝ → ℝ := fun s => c * Real.exp (-(2 * y * (s - x₀)))
  have htpos (s : ℝ) : 0 < t s := mul_pos hc0 (Real.exp_pos _)
  have htle {s : ℝ} (hs : x₀ ≤ s) : t s < 1 := by
    have hnn : 0 ≤ 2 * y * (s - x₀) := mul_nonneg (mul_nonneg zero_le_two hy.le) (sub_nonneg.mpr hs)
    have he : Real.exp (-(2 * y * (s - x₀))) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnn)
    calc
      t s ≤ c * 1 := mul_le_mul_of_nonneg_left he hc0.le
      _ < 1 := by rwa [mul_one]
  have htmem {s : ℝ} (hs : x₀ ≤ s) : t s ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith only [htpos s], htle hs⟩
  have htd (s : ℝ) : HasDerivAt t (-(2 * y) * t s) s := by
    have h1 : HasDerivAt (fun s : ℝ => -(2 * y * (s - x₀))) (-(2 * y * 1)) s :=
      (((hasDerivAt_id' s).sub_const x₀).const_mul (2 * y)).neg
    refine (h1.exp.const_mul c).congr_deriv ?_
    dsimp only [t]
    ring
  let B : ℝ → ℝ := fun s => 2 * ε + Real.artanh (t s)
  let B' : ℝ → ℝ := fun s => -y * (2 * t s / (1 - t s ^ 2))
  have hBd {s : ℝ} (hs : x₀ ≤ s) : HasDerivAt B (B' s) s := by
    have h1 := (hasDerivAt_artanh (htmem hs)).comp s (htd s)
    refine (h1.const_add (2 * ε)).congr_deriv ?_
    dsimp only [B']
    ring
  have hstart : D x₀ ≤ B x₀ := by
    have h1 : D x₀ ≤ max (D x₀) 1 := le_max_left _ _
    have h2 : t x₀ = c := by
      dsimp only [t]
      rw [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    have h3 : Real.artanh (t x₀) = max (D x₀) 1 := by rw [h2, hc, Real.artanh_tanh]
    dsimp only [B]
    rw [h3]
    linarith only [h1, hε]
  have hBc : ContinuousOn B (Icc x₀ x) := fun s hs => (hBd hs.1).continuousAt.continuousWithinAt
  have hbound : ∀ s ∈ Ico x₀ x, D s = B s → -y * Real.sinh (2 * (D s + ω s)) < B' s := by
    intro s hs heq
    have hw := hω s ⟨hs.1, hs.2.le⟩
    have hlt : 2 * Real.artanh (t s) < 2 * (D s + ω s) := by
      rw [heq]
      dsimp only [B]
      linarith only [hw, hε]
    have hsinh := Real.sinh_lt_sinh.mpr hlt
    rw [sinh_two_mul_artanh (htmem hs.1)] at hsinh
    dsimp only [B']
    linarith only [mul_lt_mul_of_pos_left hsinh hy]
  have hmain := image_le_of_deriv_right_lt_deriv_boundary'
    (f' := fun s => -y * Real.sinh (2 * (D s + ω s))) hDc hD hstart hBc
    (fun s hs => (hBd hs.1).hasDerivWithinAt) hbound (show x ∈ Icc x₀ x from ⟨hx.le, le_rfl⟩)
  have hexp : Real.exp (-(2 * y * (x - x₀))) < 1 :=
    Real.exp_lt_one (neg_lt_zero.mpr (mul_pos (mul_pos two_pos hy) (sub_pos.mpr hx)))
  have hlt : t x < Real.exp (-(2 * y * (x - x₀))) := mul_lt_of_lt_one_left (Real.exp_pos _) hc1
  have hart := Real.artanh_lt_artanh (by linarith only [htpos x]) hexp hlt
  have hBx : B x = 2 * ε + Real.artanh (t x) := rfl
  linarith only [hmain, hart, hBx]

/-! ### The traces at `iy` -/

/-- The spectral point `iy`. -/
def spectralPoint (y : ℝ) : ℂ := (y : ℂ) * I

theorem conj_spectralPoint (y : ℝ) : (starRingEnd ℂ) (spectralPoint y) = -spectralPoint y := by
  simp only [spectralPoint, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

theorem spectralLeftTrace_im (a : PrecontactAperture) (y : ℝ) :
    (evalVectorLeftTrace a (spectralPoint y)).im = 0 := by
  have h := evalVectorLeftTrace_conj a (-spectralPoint y)
  rw [map_neg, conj_spectralPoint, neg_neg, evalVectorRightTrace_eq_leftTrace_neg, neg_neg] at h
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  linarith only [hi]

theorem spectralRightTrace_im (a : PrecontactAperture) (y : ℝ) :
    (evalVectorRightTrace a (spectralPoint y)).im = 0 := by
  have h := evalVectorLeftTrace_conj a (spectralPoint y)
  rw [conj_spectralPoint, ← evalVectorRightTrace_eq_leftTrace_neg] at h
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  linarith only [hi]

/-- The left trace at `iy`, as a real number. -/
def spectralLeft (a : PrecontactAperture) (y : ℝ) : ℝ := (evalVectorLeftTrace a (spectralPoint y)).re

/-- The right trace at `iy`, as a real number: the corner of the Green operator at scale `1/y`. -/
def spectralRight (a : PrecontactAperture) (y : ℝ) : ℝ :=
  (evalVectorRightTrace a (spectralPoint y)).re

theorem spectralLeft_coe (a : PrecontactAperture) (y : ℝ) :
    ((spectralLeft a y : ℝ) : ℂ) = evalVectorLeftTrace a (spectralPoint y) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, spectralLeftTrace_im]

theorem spectralRight_coe (a : PrecontactAperture) (y : ℝ) :
    ((spectralRight a y : ℝ) : ℂ) = evalVectorRightTrace a (spectralPoint y) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, spectralRightTrace_im]

private theorem anchorLeft_coe' (a : PrecontactAperture) :
    (((evalVectorLeftTrace a I).re : ℝ) : ℂ) = evalVectorLeftTrace a I := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, evalVectorLeftTrace_I_im]

private theorem anchorRight_coe' (a : PrecontactAperture) :
    (((evalVectorRightTrace a I).re : ℝ) : ℂ) = evalVectorRightTrace a I := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, evalVectorRightTrace_I_im]

private theorem trace_flux (a : PrecontactAperture) (w z : ℂ) :
    (starRingEnd ℂ) (evalVectorLeftTrace a z) * evalVectorLeftTrace a w -
      (starRingEnd ℂ) (evalVectorRightTrace a z) * evalVectorRightTrace a w =
      I * ((starRingEnd ℂ) w - z) * kernel a w z := by
  have hp : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  have h := evalVector_endpoint_flux w z hp
  rw [precontactKernel, dif_pos hp] at h
  exact h

/-- The flux identity at `iy`: `τ_L² − τ_R² = 2y K(iy,iy)`. -/
theorem spectral_trace_identity (a : PrecontactAperture) (y : ℝ) :
    spectralLeft a y ^ 2 - spectralRight a y ^ 2 =
      2 * (y * ‖evalVector a (spectralPoint y)‖ ^ 2) := by
  have h := trace_flux a (spectralPoint y) (spectralPoint y)
  obtain ⟨N, hN⟩ : ∃ N, N = ‖evalVector a (spectralPoint y)‖ := ⟨_, rfl⟩
  have hk : kernel a (spectralPoint y) (spectralPoint y) = (N : ℂ) ^ 2 := by
    rw [hN]
    exact evalVector_self _ _
  rw [hk, conj_spectralPoint, ← spectralLeft_coe, ← spectralRight_coe, Complex.conj_ofReal,
    Complex.conj_ofReal, show spectralPoint y = (y : ℂ) * I from rfl] at h
  rw [← hN]
  apply Complex.ofReal_injective
  push_cast
  linear_combination h - 2 * (y : ℂ) * (N : ℂ) ^ 2 * Complex.I_sq

theorem spectral_pos {y : ℝ} (hy : 0 < y) (a : PrecontactAperture) :
    0 < y * ‖evalVector a (spectralPoint y)‖ ^ 2 :=
  mul_pos hy (sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero _ _)))

/-- The normalized corner `r_y = τ_R/τ_L` at `iy`, extended by zero outside precontact. -/
def spectralReflection (y a : ℝ) : ℝ :=
  open Classical in
  if h : a ∈ precontactSet then
    spectralRight (toPrecontact h) y / spectralLeft (toPrecontact h) y
  else 0

/-- The spectral drift `q_y = 2y r_y/(1−r_y²)`. -/
def spectralDrift (y a : ℝ) : ℝ :=
  2 * y * spectralReflection y a / (1 - spectralReflection y a ^ 2)

theorem spectralReflection_coe (y : ℝ) (b : PrecontactAperture) :
    spectralReflection y b.1.1 = spectralRight b y / spectralLeft b y := by
  have hb : b.1.1 ∈ precontactSet := ⟨b.1.2, b.2⟩
  rw [spectralReflection, dif_pos hb]
  rfl

theorem spectralLeft_ne_zero {y : ℝ} (hy : 0 < y) (b : PrecontactAperture) :
    spectralLeft b y ≠ 0 :=
  (traceReflection_algebra (spectral_pos hy b) (spectral_trace_identity b y)).1

theorem spectralReflection_mem {y : ℝ} (hy : 0 < y) (b : PrecontactAperture) :
    spectralReflection y b.1.1 ∈ Ioo (-1 : ℝ) 1 := by
  rw [spectralReflection_coe]
  exact (traceReflection_algebra (spectral_pos hy b) (spectral_trace_identity b y)).2.1

/-- The spectral drift is the normalized product of the two traces, `q_y = τ_L τ_R / K(iy,iy)`. -/
theorem spectralDrift_eq_traces {y : ℝ} (hy : 0 < y) (b : PrecontactAperture) :
    spectralDrift y b.1.1 =
      spectralLeft b y * spectralRight b y / ‖evalVector b (spectralPoint y)‖ ^ 2 := by
  have h := (traceReflection_algebra (spectral_pos hy b) (spectral_trace_identity b y)).2.2.2.1
  have hN : ‖evalVector b (spectralPoint y)‖ ^ 2 ≠ 0 :=
    (sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero _ _))).ne'
  rw [spectralDrift, spectralReflection_coe]
  rw [← mul_div_assoc, mul_assoc y] at *
  have hy' := hy.ne'
  have h2 : 2 * (spectralRight b y / spectralLeft b y) /
      (1 - (spectralRight b y / spectralLeft b y) ^ 2) =
      spectralLeft b y * spectralRight b y / (y * ‖evalVector b (spectralPoint y)‖ ^ 2) := h.symm
  calc
    _ = y * (2 * (spectralRight b y / spectralLeft b y) /
        (1 - (spectralRight b y / spectralLeft b y) ^ 2)) := by ring
    _ = _ := by
      rw [h2]
      field_simp

/-- The spectral drift is the hyperbolic restoring term at `iy`. -/
theorem spectralDrift_eq_sinh {y : ℝ} (hy : 0 < y) (b : PrecontactAperture) :
    spectralDrift y b.1.1 = y * Real.sinh (2 * Real.artanh (spectralReflection y b.1.1)) := by
  rw [sinh_two_mul_artanh (spectralReflection_mem hy b), spectralDrift]
  ring

/-! ### Continuity -/

private theorem range_val_mem_nhds' (a : PrecontactAperture) :
    range (fun b : PrecontactAperture => b.1.1) ∈ 𝓝 a.1.1 :=
  mem_of_superset (precontactSet_mem_nhds a) fun _ hx => ⟨toPrecontact hx, rfl⟩

private theorem tendsto_spectralReflection_of_traces {y : ℝ} (hy : 0 < y)
    {l : Filter PrecontactAperture} (a : PrecontactAperture)
    (hcont : ∀ z, Tendsto (fun b => evalVectorLeftTrace b z) l (𝓝 (evalVectorLeftTrace a z))) :
    Tendsto (fun b : PrecontactAperture => spectralReflection y b.1.1) l
      (𝓝 (spectralReflection y a.1.1)) := by
  have hu : Tendsto (fun b => spectralLeft b y) l (𝓝 (spectralLeft a y)) :=
    Complex.continuous_re.continuousAt.tendsto.comp (hcont (spectralPoint y))
  have hv : Tendsto (fun b => spectralRight b y) l (𝓝 (spectralRight a y)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (hcont (-spectralPoint y))
    simp only [spectralRight, evalVectorRightTrace_eq_leftTrace_neg]
    exact h
  simp only [spectralReflection_coe]
  exact hv.div hu (spectralLeft_ne_zero hy a)

theorem continuousAt_spectralReflection {y : ℝ} (hy : 0 < y) (a : PrecontactAperture) :
    ContinuousAt (spectralReflection y) a.1.1 := by
  have hright := tendsto_spectralReflection_of_traces hy a (fun z => tendsto_leftTrace_right a z)
  have hleft := tendsto_spectralReflection_of_traces hy a (fun z => tendsto_leftTrace_left a z)
  refine continuousAt_iff_continuous_left'_right'.mpr ⟨?_, ?_⟩
  · exact (tendsto_comap'_iff (m := spectralReflection y)
      (i := fun b : PrecontactAperture => b.1.1) (f := 𝓝[<] a.1.1)
      (mem_nhdsWithin_of_mem_nhds (range_val_mem_nhds' a))).mp hleft
  · exact (tendsto_comap'_iff (m := spectralReflection y)
      (i := fun b : PrecontactAperture => b.1.1) (f := 𝓝[>] a.1.1)
      (mem_nhdsWithin_of_mem_nhds (range_val_mem_nhds' a))).mp hright

theorem continuousAt_spectralDrift {y : ℝ} (hy : 0 < y) (a : PrecontactAperture) :
    ContinuousAt (spectralDrift y) a.1.1 := by
  have hmem := spectralReflection_mem hy a
  have hne : 1 - spectralReflection y a.1.1 ^ 2 ≠ 0 := by nlinarith only [hmem.1, hmem.2]
  have hc := continuousAt_spectralReflection hy a
  exact (continuousAt_const.mul hc).div (continuousAt_const.sub (hc.pow 2)) hne

theorem continuousAt_artanh_spectralReflection {y : ℝ} (hy : 0 < y) (a : PrecontactAperture) :
    ContinuousAt (fun x => Real.artanh (spectralReflection y x)) a.1.1 :=
  ContinuousAt.comp (f := spectralReflection y) (g := Real.artanh)
    (hasDerivAt_artanh (spectralReflection_mem hy a)).continuousAt
    (continuousAt_spectralReflection hy a)

theorem continuousAt_artanh_anchorReflection (a : PrecontactAperture) :
    ContinuousAt (fun x => Real.artanh (anchorReflection x)) a.1.1 :=
  ContinuousAt.comp (f := anchorReflection) (g := Real.artanh)
    (hasDerivAt_artanh (anchorReflection_mem ⟨a.1.2, a.2⟩)).continuousAt
    (continuousAt_anchorReflection a)

theorem continuousAt_precontactCanonicalDrift (a : PrecontactAperture) :
    ContinuousAt precontactCanonicalDrift a.1.1 := by
  have hap : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  have hmem := anchorReflection_mem hap
  have hne : 1 - anchorReflection a.1.1 ^ 2 ≠ 0 := by nlinarith only [hmem.1, hmem.2]
  have hc := continuousAt_anchorReflection a
  have hf : ContinuousAt (fun t => 2 * anchorReflection t / (1 - anchorReflection t ^ 2)) a.1.1 :=
    (continuousAt_const.mul hc).div (continuousAt_const.sub (hc.pow 2)) hne
  refine hf.congr ?_
  filter_upwards [precontactSet_mem_nhds a] with t ht
  exact (precontactCanonicalDrift_eq ht).symm

theorem isOpen_precontactSet : IsOpen precontactSet :=
  isOpen_iff_mem_nhds.mpr fun _ hx => precontactSet_mem_nhds (toPrecontact hx)

private theorem Icc_subset_precontactSet {l h : ℝ} (hl : l ∈ precontactSet)
    (hh : h ∈ precontactSet) : Icc l h ⊆ precontactSet := fun _ ht =>
  ⟨hl.1.trans_le ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt hh.2⟩

/-- Before contact the gauge has the drift as its derivative. -/
theorem hasDerivAt_precontactCanonicalGauge {base x : ℝ} (hb : base ∈ precontactSet)
    (hx : x ∈ precontactSet) :
    HasDerivAt (precontactCanonicalGauge base) (precontactCanonicalDrift x) x := by
  have hi : IntervalIntegrable precontactCanonicalDrift volume base x := by
    rcases le_total base x with h | h
    · exact intervalIntegrable_precontactCanonicalDrift h (Icc_subset_precontactSet hb hx)
    · exact (intervalIntegrable_precontactCanonicalDrift h (Icc_subset_precontactSet hx hb)).symm
  have hc : ContinuousOn precontactCanonicalDrift precontactSet := fun t ht =>
    (continuousAt_precontactCanonicalDrift (toPrecontact ht)).continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hc.stronglyMeasurableAtFilter isOpen_precontactSet x hx)
    (continuousAt_precontactCanonicalDrift (toPrecontact hx))

/-- **The canonical potential is continuous before contact.** -/
theorem continuousAt_canonicalPotential {base : ℝ} (hb : base ∈ precontactSet)
    (a : PrecontactAperture) : ContinuousAt (canonicalPotential base) a.1.1 := by
  have hθ := (hasDerivAt_precontactCanonicalGauge hb (show a.1.1 ∈ precontactSet from
    ⟨a.1.2, a.2⟩)).continuousAt
  refine ((continuousAt_artanh_anchorReflection a).add hθ).congr ?_
  filter_upwards [precontactSet_mem_nhds a] with t ht
  exact (canonicalPotential_eq base ht).symm

/-! ### The Hermite–Biehler pair at `iy` -/

/-- The imaginary part of the normalized Hermite–Biehler function at `iy`. -/
def spectralPlus (y x : ℝ) : ℝ := (normalizedHermiteBiehler (spectralPoint y) x).im

/-- The imaginary part of its reflection at `iy`. -/
def spectralMinus (y x : ℝ) : ℝ := (normalizedHermiteBiehlerSharp (spectralPoint y) x).im

theorem spectralPlus_coe (y : ℝ) (a : PrecontactAperture) :
    spectralPlus y a.1.1 = (spectralLeft a y * (evalVectorLeftTrace a I).re -
      spectralRight a y * (evalVectorRightTrace a I).re) /
        Real.sqrt (diagonalEvalGram I a.1.1) := by
  have hp : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  have h := trace_flux a I (spectralPoint y)
  obtain ⟨K, hK⟩ : ∃ K, K = kernel a I (spectralPoint y) := ⟨_, rfl⟩
  rw [← hK, ← spectralLeft_coe, ← spectralRight_coe, ← anchorLeft_coe' a, ← anchorRight_coe' a,
    Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    show spectralPoint y = (y : ℂ) * I from rfl] at h
  have hkern : precontactKernel I (spectralPoint y) a.1.1 = K := by
    rw [precontactKernel, dif_pos hp, hK]
    rfl
  have hE : normalizedHermiteBiehler (spectralPoint y) a.1.1 =
      I * (((spectralLeft a y * (evalVectorLeftTrace a I).re -
        spectralRight a y * (evalVectorRightTrace a I).re) /
          Real.sqrt (diagonalEvalGram I a.1.1) : ℝ) : ℂ) := by
    rw [normalizedHermiteBiehler, hkern, show spectralPoint y = (y : ℂ) * I from rfl]
    push_cast
    linear_combination (-I / ((Real.sqrt (diagonalEvalGram I a.1.1) : ℝ) : ℂ)) * h +
      (((y : ℂ) + 1) * K / ((Real.sqrt (diagonalEvalGram I a.1.1) : ℝ) : ℂ)) * I * Complex.I_sq
  rw [spectralPlus, hE, Complex.I_mul_im, Complex.ofReal_re]

theorem spectralMinus_coe (y : ℝ) (a : PrecontactAperture) :
    spectralMinus y a.1.1 = (spectralLeft a y * (evalVectorRightTrace a I).re -
      spectralRight a y * (evalVectorLeftTrace a I).re) /
        Real.sqrt (diagonalEvalGram I a.1.1) := by
  have hp : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  have h := trace_flux a (-I) (spectralPoint y)
  have hln : evalVectorLeftTrace a (-I) = evalVectorRightTrace a I :=
    (evalVectorRightTrace_eq_leftTrace_neg a I).symm
  have hrn : evalVectorRightTrace a (-I) = evalVectorLeftTrace a I := by
    rw [evalVectorRightTrace_eq_leftTrace_neg, neg_neg]
  obtain ⟨K, hK⟩ : ∃ K, K = kernel a (-I) (spectralPoint y) := ⟨_, rfl⟩
  rw [hln, hrn, ← hK, ← spectralLeft_coe, ← spectralRight_coe, ← anchorLeft_coe' a,
    ← anchorRight_coe' a, Complex.conj_ofReal, Complex.conj_ofReal, map_neg, Complex.conj_I,
    neg_neg, show spectralPoint y = (y : ℂ) * I from rfl] at h
  have hkern : precontactKernel (-I) (spectralPoint y) a.1.1 = K := by
    rw [precontactKernel, dif_pos hp, hK]
    rfl
  have hE : normalizedHermiteBiehlerSharp (spectralPoint y) a.1.1 =
      I * (((spectralLeft a y * (evalVectorRightTrace a I).re -
        spectralRight a y * (evalVectorLeftTrace a I).re) /
          Real.sqrt (diagonalEvalGram I a.1.1) : ℝ) : ℂ) := by
    rw [normalizedHermiteBiehlerSharp, hkern, show spectralPoint y = (y : ℂ) * I from rfl]
    push_cast
    linear_combination (-I / ((Real.sqrt (diagonalEvalGram I a.1.1) : ℝ) : ℂ)) * h +
      (((y : ℂ) - 1) * K / ((Real.sqrt (diagonalEvalGram I a.1.1) : ℝ) : ℂ)) * I * Complex.I_sq
  rw [spectralMinus, hE, Complex.I_mul_im, Complex.ofReal_re]

theorem hasDerivWithinAt_spectralPlus (y : ℝ) {x : ℝ} (hx : x ∈ precontactSet) :
    HasDerivWithinAt (spectralPlus y)
      (y * precontactCanonicalMass x * spectralPlus y x -
        (y + 1) * precontactCanonicalDrift x * spectralMinus y x) (Ioi x) x := by
  have h := hasDerivWithinAt_normalizedHermiteBiehler_right (spectralPoint y) hx
  have h' : HasDerivWithinAt (spectralPlus y) (Complex.imCLM _) (Ioi x) x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt x h
  refine h'.congr_deriv ?_
  obtain ⟨E, hE⟩ : ∃ E, E = normalizedHermiteBiehler (spectralPoint y) x := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = normalizedHermiteBiehlerSharp (spectralPoint y) x := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = precontactCanonicalMass x := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = precontactCanonicalDrift x := ⟨_, rfl⟩
  rw [← hE, ← hS, ← hm, ← hs]
  have hc : -I * spectralPoint y * (m : ℂ) * E + (I * spectralPoint y - 1) * (s : ℂ) * S =
      ((y * m : ℝ) : ℂ) * E - (((y + 1) * s : ℝ) : ℂ) * S := by
    rw [show spectralPoint y = (y : ℂ) * I from rfl]
    push_cast
    linear_combination (-(y : ℂ) * (m : ℂ) * E + (y : ℂ) * (s : ℂ) * S) * Complex.I_sq
  rw [hc]
  change (_ - _ : ℂ).im = _
  rw [Complex.sub_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  change y * m * E.im - (y + 1) * s * S.im = y * m * spectralPlus y x - _
  rw [spectralPlus, spectralMinus, hE, hS]

theorem hasDerivWithinAt_spectralMinus (y : ℝ) {x : ℝ} (hx : x ∈ precontactSet) :
    HasDerivWithinAt (spectralMinus y)
      (-(y * precontactCanonicalMass x * spectralMinus y x) +
        (y - 1) * precontactCanonicalDrift x * spectralPlus y x) (Ioi x) x := by
  have hf : spectralMinus y = fun t => -(normalizedHermiteBiehler (-spectralPoint y) t).im := by
    funext t
    rw [spectralMinus, normalizedHermiteBiehlerSharp_eq_conj, conj_spectralPoint, Complex.conj_im]
  have h := hasDerivWithinAt_normalizedHermiteBiehler_right (-spectralPoint y) hx
  have h' : HasDerivWithinAt (fun t => (normalizedHermiteBiehler (-spectralPoint y) t).im)
      (Complex.imCLM _) (Ioi x) x := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt x h
  have hE : (normalizedHermiteBiehler (-spectralPoint y) x).im = -spectralMinus y x := by
    rw [hf]
    ring
  have hS : (normalizedHermiteBiehlerSharp (-spectralPoint y) x).im = -spectralPlus y x := by
    rw [normalizedHermiteBiehlerSharp_eq_conj, map_neg, conj_spectralPoint, neg_neg,
      Complex.conj_im, spectralPlus]
  rw [hf] at *
  refine (HasDerivWithinAt.neg h').congr_deriv ?_
  obtain ⟨E, hEd⟩ : ∃ E, E = normalizedHermiteBiehler (-spectralPoint y) x := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S, S = normalizedHermiteBiehlerSharp (-spectralPoint y) x := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = precontactCanonicalMass x := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = precontactCanonicalDrift x := ⟨_, rfl⟩
  rw [← hEd, ← hSd, ← hm, ← hs]
  rw [← hEd] at hE
  rw [← hSd] at hS
  have hc : -I * -spectralPoint y * (m : ℂ) * E + (I * -spectralPoint y - 1) * (s : ℂ) * S =
      ((-(y * m) : ℝ) : ℂ) * E + (((y - 1) * s : ℝ) : ℂ) * S := by
    rw [show spectralPoint y = (y : ℂ) * I from rfl]
    push_cast
    linear_combination ((y : ℂ) * (m : ℂ) * E - (y : ℂ) * (s : ℂ) * S) * Complex.I_sq
  rw [hc]
  change -((_ + _ : ℂ).im) = _
  rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  change -(-(y * m) * E.im + (y - 1) * s * S.im) = _
  rw [hE, hS]
  ring

/-! ### Universality -/

private theorem artanh_div_eq {u w : ℝ} (hu : u ≠ 0) (hr : w / u ∈ Ioo (-1 : ℝ) 1) :
    u + w ≠ 0 ∧ u - w ≠ 0 ∧ Real.artanh (w / u) = (Real.log (u + w) - Real.log (u - w)) / 2 := by
  have h1 : 1 + w / u ≠ 0 := (by linarith only [hr.1] : 0 < 1 + w / u).ne'
  have h2 : 1 - w / u ≠ 0 := (by linarith only [hr.2] : 0 < 1 - w / u).ne'
  have e1 : u + w = u * (1 + w / u) := by field_simp
  have e2 : u - w = u * (1 - w / u) := by field_simp
  have hp : u + w ≠ 0 := e1 ▸ mul_ne_zero hu h1
  have hm : u - w ≠ 0 := e2 ▸ mul_ne_zero hu h2
  refine ⟨hp, hm, ?_⟩
  have e3 : (1 + w / u) / (1 - w / u) = (u + w) / (u - w) := by
    rw [e1, e2]
    field_simp
  rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self hr), e3, Real.log_div hp hm]
  ring

private theorem slope_algebra {r R κ y : ℝ} (hκ : κ ≠ 0) (hr₁ : 1 + r ≠ 0) (hr₂ : 1 - r ≠ 0)
    (hR₁ : 1 + R ≠ 0) (hR₂ : 1 - R ≠ 0) (hr : 1 - r ^ 2 ≠ 0) (hR : 1 - R ^ 2 ≠ 0) {m s fp fm : ℝ}
    (hm : m = (1 + r ^ 2) / (1 - r ^ 2)) (hs : s = 2 * r / (1 - r ^ 2))
    (hfp : fp = κ * (1 - R * r)) (hfm : fm = κ * (r - R)) :
    ((y * m * fp - (y + 1) * s * fm + (-(y * m * fm) + (y - 1) * s * fp)) / (fp + fm) -
      (y * m * fp - (y + 1) * s * fm - (-(y * m * fm) + (y - 1) * s * fp)) / (fp - fm)) / 2 =
      2 * y * R / (1 - R ^ 2) - s := by
  have e1 : fp + fm = κ * ((1 - R) * (1 + r)) := by rw [hfp, hfm]; ring
  have e2 : fp - fm = κ * ((1 + R) * (1 - r)) := by rw [hfp, hfm]; ring
  rw [e1, e2, hm, hs, hfp, hfm]
  field_simp
  ring

/-- **The spectral flow, from the right.** The difference of the two hyperbolic angles has one-sided
derivative `q_y − q_1`. -/
theorem hasDerivWithinAt_artanh_sub_spectral {y : ℝ} (hy : 0 < y) {x : ℝ}
    (hx : x ∈ precontactSet) :
    HasDerivWithinAt (fun t => Real.artanh (anchorReflection t) -
        Real.artanh (spectralReflection y t))
      (spectralDrift y x - precontactCanonicalDrift x) (Ioi x) x := by
  -- Values of the angles in terms of the two trace pairs.
  have hval (b : PrecontactAperture) :
      spectralPlus y b.1.1 + spectralMinus y b.1.1 ≠ 0 ∧
      spectralPlus y b.1.1 - spectralMinus y b.1.1 ≠ 0 ∧
      Real.artanh (anchorReflection b.1.1) - Real.artanh (spectralReflection y b.1.1) =
        (Real.log (spectralPlus y b.1.1 + spectralMinus y b.1.1) -
          Real.log (spectralPlus y b.1.1 - spectralMinus y b.1.1)) / 2 := by
    have hbp : b.1.1 ∈ precontactSet := ⟨b.1.2, b.2⟩
    obtain ⟨u, hu⟩ : ∃ u, u = (evalVectorLeftTrace b I).re := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = (evalVectorRightTrace b I).re := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p, p = spectralLeft b y := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = spectralRight b y := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N, N = Real.sqrt (diagonalEvalGram I b.1.1) := ⟨_, rfl⟩
    have hNpos : N ≠ 0 := by
      rw [hN]
      refine (Real.sqrt_pos.mpr ?_).ne'
      rw [diagonalEvalGram_eq_norm I b]
      exact sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero _ _))
    have hu0 : u ≠ 0 := hu ▸ anchorLeftTrace_re_ne_zero b
    have hp0 : p ≠ 0 := hp ▸ spectralLeft_ne_zero hy b
    have hrm : w / u ∈ Ioo (-1 : ℝ) 1 := by
      have h := anchorReflection_mem hbp
      rwa [anchorReflection_coe, ← hu, ← hw] at h
    have hRm : q / p ∈ Ioo (-1 : ℝ) 1 := by
      have h := spectralReflection_mem hy b
      rwa [spectralReflection_coe, ← hp, ← hq] at h
    obtain ⟨h1, h2, h3⟩ := artanh_div_eq hu0 hrm
    obtain ⟨h4, h5, h6⟩ := artanh_div_eq hp0 hRm
    have hP : spectralPlus y b.1.1 + spectralMinus y b.1.1 = (p - q) * (u + w) / N := by
      rw [spectralPlus_coe, spectralMinus_coe, ← hu, ← hw, ← hp, ← hq, ← hN]
      ring
    have hQ : spectralPlus y b.1.1 - spectralMinus y b.1.1 = (p + q) * (u - w) / N := by
      rw [spectralPlus_coe, spectralMinus_coe, ← hu, ← hw, ← hp, ← hq, ← hN]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hP]
      exact div_ne_zero (mul_ne_zero h5 h1) hNpos
    · rw [hQ]
      exact div_ne_zero (mul_ne_zero h4 h2) hNpos
    · rw [hP, hQ, anchorReflection_coe, spectralReflection_coe, ← hu, ← hw, ← hp, ← hq, h3, h6,
        Real.log_div (mul_ne_zero h5 h1) hNpos, Real.log_div (mul_ne_zero h4 h2) hNpos,
        Real.log_mul h5 h1, Real.log_mul h4 h2]
      ring
  let b := toPrecontact hx
  have hbx : b.1.1 = x := rfl
  obtain ⟨hPne, hQne, -⟩ := hval b
  rw [hbx] at hPne hQne
  have hdp := hasDerivWithinAt_spectralPlus y hx
  have hdm := hasDerivWithinAt_spectralMinus y hx
  have hlogP := (hdp.add hdm).log hPne
  have hlogQ := (hdp.sub hdm).log hQne
  have hΦ := (hlogP.sub hlogQ).div_const 2
  -- The eventual identification of the two functions.
  have hevent : (fun t => Real.artanh (anchorReflection t) -
      Real.artanh (spectralReflection y t)) =ᶠ[𝓝[Ioi x] x]
      fun t => (Real.log ((spectralPlus y + spectralMinus y) t) -
        Real.log ((spectralPlus y - spectralMinus y) t)) / 2 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (precontactSet_mem_nhds b)] with t ht
    exact (hval (toPrecontact ht)).2.2
  refine (hΦ.congr_of_eventuallyEq hevent (hval b).2.2).congr_deriv ?_
  -- The slope.
  have hbp : x ∈ precontactSet := hx
  obtain ⟨u, hu⟩ : ∃ u, u = (evalVectorLeftTrace b I).re := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = (evalVectorRightTrace b I).re := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = spectralLeft b y := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = spectralRight b y := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = Real.sqrt (diagonalEvalGram I b.1.1) := ⟨_, rfl⟩
  have hNne : N ≠ 0 := by
    rw [hN]
    refine (Real.sqrt_pos.mpr ?_).ne'
    rw [diagonalEvalGram_eq_norm I b]
    exact sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero _ _))
  have hu0 : u ≠ 0 := hu ▸ anchorLeftTrace_re_ne_zero b
  have hp0 : p ≠ 0 := hp ▸ spectralLeft_ne_zero hy b
  obtain ⟨r, hr⟩ : ∃ r, r = anchorReflection x := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = spectralReflection y x := ⟨_, rfl⟩
  have hrm : r ∈ Ioo (-1 : ℝ) 1 := hr ▸ anchorReflection_mem hx
  have hRm : R ∈ Ioo (-1 : ℝ) 1 := hR ▸ spectralReflection_mem hy b
  have hrv : r = w / u := by rw [hr, hu, hw]; exact anchorReflection_coe b
  have hRv : R = q / p := by rw [hR, hp, hq]; exact spectralReflection_coe y b
  have hfp : spectralPlus y x = p * u / N * (1 - R * r) := by
    have h := spectralPlus_coe y b
    rw [hbx, ← hu, ← hw, ← hp, ← hq, ← hN] at h
    rw [h, hrv, hRv]
    field_simp
  have hfm : spectralMinus y x = p * u / N * (r - R) := by
    have h := spectralMinus_coe y b
    rw [hbx, ← hu, ← hw, ← hp, ← hq, ← hN] at h
    rw [h, hrv, hRv]
    field_simp
  have hmass : precontactCanonicalMass x = (1 + r ^ 2) / (1 - r ^ 2) := by
    rw [precontactCanonicalMass_eq_anchorMassRatio hx, anchorMassRatio, hr]
  have hdrift : precontactCanonicalDrift x = 2 * r / (1 - r ^ 2) := by
    rw [precontactCanonicalDrift_eq hx, hr]
  have hκ : p * u / N ≠ 0 := div_ne_zero (mul_ne_zero hp0 hu0) hNne
  have hslope := slope_algebra (y := y) hκ
    (by linarith only [hrm.1] : (0 : ℝ) < 1 + r).ne' (by linarith only [hrm.2] : (0 : ℝ) < 1 - r).ne'
    (by linarith only [hRm.1] : (0 : ℝ) < 1 + R).ne' (by linarith only [hRm.2] : (0 : ℝ) < 1 - R).ne'
    (by nlinarith only [hrm.1, hrm.2] : (0 : ℝ) < 1 - r ^ 2).ne'
    (by nlinarith only [hRm.1, hRm.2] : (0 : ℝ) < 1 - R ^ 2).ne' hmass hdrift hfp hfm
  rw [spectralDrift, ← hR]
  rw [← hslope]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- **Universality.** Every spectral parameter sees the one potential:
`artanh r_y(b) − artanh r_y(a) = Ψ(b) − Ψ(a) − ∫_a^b q_y`. -/
theorem artanh_spectralReflection_sub {y : ℝ} (hy : 0 < y) {base a b : ℝ}
    (hbase : base ∈ precontactSet) (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    Real.artanh (spectralReflection y b) - Real.artanh (spectralReflection y a) =
      canonicalPotential base b - canonicalPotential base a - ∫ x in a..b, spectralDrift y x := by
  have hD : ContinuousOn (fun x => spectralDrift y x - precontactCanonicalDrift x) (Icc a b) :=
    fun x hx => ((continuousAt_spectralDrift hy (toPrecontact (hs hx))).sub
      (continuousAt_precontactCanonicalDrift (toPrecontact (hs hx)))).continuousWithinAt
  have hDy : ContinuousOn (spectralDrift y) (Icc a b) := fun x hx =>
    (continuousAt_spectralDrift hy (toPrecontact (hs hx))).continuousWithinAt
  have hs0 : ContinuousOn precontactCanonicalDrift (Icc a b) := fun x hx =>
    (continuousAt_precontactCanonicalDrift (toPrecontact (hs hx))).continuousWithinAt
  have hcont : ContinuousOn (fun t => Real.artanh (anchorReflection t) -
      Real.artanh (spectralReflection y t)) (Icc a b) := fun x hx =>
    ((continuousAt_artanh_anchorReflection (toPrecontact (hs hx))).sub
      (continuousAt_artanh_spectralReflection hy (toPrecontact (hs hx)))).continuousWithinAt
  have hi : IntervalIntegrable (fun x => spectralDrift y x - precontactCanonicalDrift x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  have hiD : IntervalIntegrable (spectralDrift y) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  have hiS : IntervalIntegrable precontactCanonicalDrift volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont
    (fun x hx => hasDerivWithinAt_artanh_sub_spectral hy (hs ⟨hx.1.le, hx.2.le⟩)) hi
  rw [intervalIntegral.integral_sub hiD hiS] at hFTC
  have hpot := canonicalPotential_sub_eq hbase (hs ⟨le_rfl, hab⟩) (hs ⟨hab, le_rfl⟩)
  linarith only [hFTC, hpot]

/-! ### The Abel limit -/

/-- The derivative of the distance between the potential and the spectral angle. -/
private theorem hasDerivWithinAt_spectral_distance {y : ℝ} (hy : 0 < y) {base c s : ℝ}
    (hbase : base ∈ precontactSet) (hs : s ∈ precontactSet) :
    HasDerivWithinAt (fun t => Real.artanh (spectralReflection y t) - canonicalPotential base t + c)
      (-y * Real.sinh (2 * Real.artanh (spectralReflection y s))) (Ioi s) s := by
  have h1 := hasDerivWithinAt_artanh_sub_spectral hy hs
  have h2 := (hasDerivAt_precontactCanonicalGauge hbase hs).hasDerivWithinAt (s := Ioi s)
  have h3 := ((h1.neg).sub h2).add_const c
  have hev : (fun t => Real.artanh (spectralReflection y t) - canonicalPotential base t + c) =ᶠ[𝓝[Ioi s] s]
      fun t => -(Real.artanh (anchorReflection t) - Real.artanh (spectralReflection y t)) -
        precontactCanonicalGauge base t + c := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (precontactSet_mem_nhds (toPrecontact hs))] with t ht
    rw [canonicalPotential_eq base ht]
    ring
  have hsv : Real.artanh (spectralReflection y s) - canonicalPotential base s + c =
      -(Real.artanh (anchorReflection s) - Real.artanh (spectralReflection y s)) -
        precontactCanonicalGauge base s + c := by
    rw [canonicalPotential_eq base hs]
    ring
  refine (h3.congr_of_eventuallyEq hev hsv).congr_deriv ?_
  have hd := spectralDrift_eq_sinh hy (toPrecontact hs)
  change spectralDrift y s = _ at hd
  rw [hd]
  ring

/-- **The normalized corner tends to zero.** The flow at `iy` restores with strength `y`, while the
potential driving it is continuous, so `artanh r_y(x) → 0` as `y → ∞`. -/
theorem tendsto_artanh_spectralReflection_zero (a : PrecontactAperture) :
    Tendsto (fun y : ℝ => Real.artanh (spectralReflection y a.1.1)) atTop (𝓝 0) := by
  have hap : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  rw [Metric.tendsto_nhds]
  intro e he
  have hε : 0 < e / 4 := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (continuousAt_canonicalPotential hap a)
    (e / 4) hε
  obtain ⟨c, hc⟩ := exists_precontact_lt a
  let x₀ := max c.1.1 (a.1.1 - δ / 2)
  have hx₀ : x₀ < a.1.1 := max_lt hc (by linarith only [hδ])
  have hx₀p : x₀ ∈ precontactSet :=
    ⟨c.1.2.trans_le (le_max_left _ _), (EReal.coe_le_coe_iff.mpr hx₀.le).trans_lt a.2⟩
  have hsub : Icc x₀ a.1.1 ⊆ precontactSet := Icc_subset_precontactSet hx₀p hap
  have hω (s : ℝ) (hs : s ∈ Icc x₀ a.1.1) : |canonicalPotential a.1.1 s - canonicalPotential a.1.1 a.1.1| < e / 4 := by
    have hd : dist s a.1.1 < δ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.2)]
      have := (le_max_right c.1.1 (a.1.1 - δ / 2)).trans hs.1
      linarith only [this, hδ]
    have := hball hd
    rwa [Real.dist_eq] at this
  -- The barrier tends to zero.
  have hgap : 0 < a.1.1 - x₀ := sub_pos.mpr hx₀
  have htop : Tendsto (fun y : ℝ => 2 * y * (a.1.1 - x₀)) atTop atTop :=
    (tendsto_id.const_mul_atTop two_pos).atTop_mul_const hgap
  have hexp : Tendsto (fun y : ℝ => Real.exp (-(2 * y * (a.1.1 - x₀)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop)
  have hart0 : ContinuousAt Real.artanh 0 :=
    (hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num)).continuousAt
  have hbar : Tendsto (fun y : ℝ => Real.artanh (Real.exp (-(2 * y * (a.1.1 - x₀))))) atTop (𝓝 0) := by
    have h := hart0.tendsto.comp hexp
    rwa [Real.artanh_zero] at h
  filter_upwards [eventually_gt_atTop 0, hbar.eventually_lt_const (show (0 : ℝ) < e / 2 by positivity)]
    with y hy hsmall
  have hcont (c' : ℝ) : ContinuousOn (fun t => Real.artanh (spectralReflection y t) -
      canonicalPotential a.1.1 t + c') (Icc x₀ a.1.1) := fun s hs =>
    (((continuousAt_artanh_spectralReflection hy (toPrecontact (hsub hs))).sub
      (continuousAt_canonicalPotential hap (toPrecontact (hsub hs)))).add_const c').continuousWithinAt
  -- The upper bound.
  have hupper := le_of_strong_restoring (D := fun t => Real.artanh (spectralReflection y t) -
      canonicalPotential a.1.1 t + canonicalPotential a.1.1 a.1.1)
    (ω := fun t => canonicalPotential a.1.1 t - canonicalPotential a.1.1 a.1.1)
    hy hx₀ hε (hcont _) (fun s hs => by
      have := abs_lt.mp (hω s hs)
      exact this.1.le) (fun s hs => by
      have hsp := hsub ⟨hs.1, hs.2.le⟩
      have h := (hasDerivWithinAt_spectral_distance hy (c := canonicalPotential a.1.1 a.1.1)
        hap hsp)
      refine (hasDerivWithinAt_Ioi_iff_Ici.mp h).congr_deriv ?_
      congr 3
      ring)
  -- The lower bound.
  have hlower := le_of_strong_restoring (D := fun t => -(Real.artanh (spectralReflection y t) -
      canonicalPotential a.1.1 t + canonicalPotential a.1.1 a.1.1))
    (ω := fun t => -(canonicalPotential a.1.1 t - canonicalPotential a.1.1 a.1.1))
    hy hx₀ hε (hcont _).neg (fun s hs => by
      have := abs_lt.mp (hω s hs)
      linarith only [this.2]) (fun s hs => by
      have hsp := hsub ⟨hs.1, hs.2.le⟩
      have h := (hasDerivWithinAt_spectral_distance hy (c := canonicalPotential a.1.1 a.1.1)
        hap hsp)
      refine (HasDerivWithinAt.neg (hasDerivWithinAt_Ioi_iff_Ici.mp h)).congr_deriv ?_
      have he : 2 * (-(Real.artanh (spectralReflection y s) - canonicalPotential a.1.1 s +
          canonicalPotential a.1.1 a.1.1) + -(canonicalPotential a.1.1 s -
            canonicalPotential a.1.1 a.1.1)) = -(2 * Real.artanh (spectralReflection y s)) := by
        ring
      rw [he, Real.sinh_neg]
      ring)
  have hval : Real.artanh (spectralReflection y a.1.1) - canonicalPotential a.1.1 a.1.1 +
      canonicalPotential a.1.1 a.1.1 = Real.artanh (spectralReflection y a.1.1) := by ring
  simp only [hval] at hupper hlower
  rw [Real.dist_eq, sub_zero]
  refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith only [hupper, hlower, hsmall]

/-- `r_y(x) → 0` as `y → ∞`: the corner is small relative to the left trace. -/
theorem tendsto_spectralReflection_zero (a : PrecontactAperture) :
    Tendsto (fun y : ℝ => spectralReflection y a.1.1) atTop (𝓝 0) := by
  have h := (Real.continuous_tanh.tendsto 0).comp (tendsto_artanh_spectralReflection_zero a)
  rw [Real.tanh_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  exact Real.tanh_artanh (spectralReflection_mem hy a)

/-- **The Gelfand–Levitan formula.** The potential is the Abel limit of the normalized corner of the
Green operator: `Ψ(b) − Ψ(a) = lim_{y→∞} ∫_a^b τ_L τ_R / K (x,iy) dx`. -/
theorem tendsto_integral_spectralDrift {base : ℝ} (hbase : base ∈ precontactSet)
    (a b : PrecontactAperture) (hab : a.1.1 ≤ b.1.1) :
    Tendsto (fun y : ℝ => ∫ x in a.1.1..b.1.1, spectralDrift y x) atTop
      (𝓝 (canonicalPotential base b.1.1 - canonicalPotential base a.1.1)) := by
  have hs : Icc a.1.1 b.1.1 ⊆ precontactSet := fun _ ht =>
    ⟨a.1.2.trans_le ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt b.2⟩
  have h := (tendsto_artanh_spectralReflection_zero b).sub
    (tendsto_artanh_spectralReflection_zero a)
  have hlim := h.const_sub (canonicalPotential base b.1.1 - canonicalPotential base a.1.1)
  simp only [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hT := artanh_spectralReflection_sub hy hbase hab hs
  linarith only [hT]

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
