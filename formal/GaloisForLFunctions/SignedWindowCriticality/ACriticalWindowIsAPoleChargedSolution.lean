import GaloisForLFunctions.SignedWindowCriticality.ThePoleChargesTheSupersolution

/-!
# A critical window is a pole-charged solution

The Weil form `Ẑ` (ACT `fullZeroForm`) polarizes through one operator on gauges, the **Weil source**
`𝒮(a) = (𝓛_D a − Φ cosh(x/2) a) − 2B(Φa) Φ sinh(x/2) + 2A(Φa) Φ cosh(x/2)`, with `A = ∫F cosh(x/2)`,
`B = ∫F sinh(x/2)` (`fullZeroForm_phiDoob_add`):

    Ẑ(Φ(a + b)) = Ẑ(Φa) + Ẑ(Φb) + 2 ∫ b 𝒮(a).

* **Source law** (`weilSource_eq_of_rayleighCritical`). Let `S = (b, c)`. If `a ∈ C²_c` vanishes off
  `S` and attains the Rayleigh bound `Ẑ(Φv) ≥ μ‖Φv‖²` of the window (over `C²_c` tests vanishing off
  `S`), then on `S` its Weil source is `μΦ²a`: the Markov defect of the gauge `a` equals the pole
  charges read from its own moments, plus `μΦ²a`.
* **Own-gauge representation** (`fullZeroForm_phiDoob_mul_eq_of_rayleighCritical`). In the gauge of
  such an `a`, `Ẑ(Φau) = J_{Φa}(u) + μ∫u²(Φa)² + 2V_s(u) − 2V_c(u)` for every `u ∈ C²_c` vanishing
  off `S`: the window form is a signed Dirichlet form plus `μ` times mass.
* **Zero modes** (`weilSource_eq_zero_of_zeroMode`, `fullZeroForm_phiDoob_mul_eq_of_zeroMode`). A
  `C²_c` zero mode of a nonnegative window is a *pole-charged harmonic* gauge: its Markov defect is
  exactly `2B Φ sinh − 2A Φ cosh` on the window, and in its gauge the window form is
  `J_{Φa} + 2V_s − 2V_c` with no potential.

The Weil source vanishes on the window exactly when the gauge is a critical point; the charges are
the gauge's own pole moments. This is the critical (zero-margin) case of the pole-charged
Allegretto–Piepenbrink theorem (`ThePoleChargesTheSupersolution`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The Weil source of a gauge: its Markov defect plus the pole charges read from its moments. -/
def weilSource (a : ℝ → ℝ) (x : ℝ) : ℝ :=
  markovDefect a x - 2 * oddPoleMoment (phiDoobTest a) * (riemannKernelReal x * Real.sinh (x / 2)) +
    2 * evenPoleMoment (phiDoobTest a) * (riemannKernelReal x * Real.cosh (x / 2))

variable {a b' u : ℝ → ℝ} {b c μ : ℝ}

theorem continuous_weilSource (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a) :
    Continuous (weilSource a) := by
  unfold weilSource
  have hs : Continuous fun x => riemannKernelReal x * Real.sinh (x / 2) :=
    continuous_riemannKernelReal.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hc : Continuous fun x => riemannKernelReal x * Real.cosh (x / 2) :=
    continuous_riemannKernelReal.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))
  exact ((continuous_markovDefect ha hac).sub (continuous_const.mul hs)).add
    (continuous_const.mul hc)

theorem oddPoleMoment_phiDoobTest (v : ℝ → ℝ) :
    oddPoleMoment (phiDoobTest v) = ∫ x, v x * (riemannKernelReal x * Real.sinh (x / 2)) := by
  unfold oddPoleMoment phiDoobTest
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

theorem evenPoleMoment_phiDoobTest (v : ℝ → ℝ) :
    evenPoleMoment (phiDoobTest v) = ∫ x, v x * (riemannKernelReal x * Real.cosh (x / 2)) := by
  unfold evenPoleMoment phiDoobTest
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

theorem integrable_mul_kernel_sinh {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable fun x => v x * (riemannKernelReal x * Real.sinh (x / 2)) :=
  (hv.mul (continuous_riemannKernelReal.mul (Real.continuous_sinh.comp
    (continuous_id.div_const 2)))).integrable_of_hasCompactSupport hvc.mul_right

theorem integrable_mul_kernel_cosh {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable fun x => v x * (riemannKernelReal x * Real.cosh (x / 2)) :=
  (hv.mul (continuous_riemannKernelReal.mul (Real.continuous_cosh.comp
    (continuous_id.div_const 2)))).integrable_of_hasCompactSupport hvc.mul_right

/-- **Polarization through the Weil source.** -/
theorem fullZeroForm_phiDoob_add (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b') (hbc : HasCompactSupport b') :
    fullZeroForm (phiDoobTest fun y => a y + b' y) =
      fullZeroForm (phiDoobTest a) + fullZeroForm (phiDoobTest b') +
        2 * ∫ x, b' x * weilSource a x := by
  have hO : oddPoleMoment (phiDoobTest fun y => a y + b' y) =
      oddPoleMoment (phiDoobTest a) + oddPoleMoment (phiDoobTest b') := by
    rw [oddPoleMoment_phiDoobTest, oddPoleMoment_phiDoobTest, oddPoleMoment_phiDoobTest,
      ← integral_add (integrable_mul_kernel_sinh ha.continuous hac)
        (integrable_mul_kernel_sinh hb.continuous hbc)]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hE : evenPoleMoment (phiDoobTest fun y => a y + b' y) =
      evenPoleMoment (phiDoobTest a) + evenPoleMoment (phiDoobTest b') := by
    rw [evenPoleMoment_phiDoobTest, evenPoleMoment_phiDoobTest, evenPoleMoment_phiDoobTest,
      ← integral_add (integrable_mul_kernel_cosh ha.continuous hac)
        (integrable_mul_kernel_cosh hb.continuous hbc)]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hD : Integrable fun x => b' x * markovDefect a x :=
    (hb.continuous.mul (continuous_markovDefect ha hac)).integrable_of_hasCompactSupport
      hbc.mul_right
  have hS : (∫ x, b' x * weilSource a x) =
      (∫ x, b' x * markovDefect a x) -
        2 * oddPoleMoment (phiDoobTest a) * oddPoleMoment (phiDoobTest b') +
        2 * evenPoleMoment (phiDoobTest a) * evenPoleMoment (phiDoobTest b') := by
    rw [oddPoleMoment_phiDoobTest b', evenPoleMoment_phiDoobTest b', ← integral_const_mul,
      ← integral_const_mul]
    have h1 := hD.sub ((integrable_mul_kernel_sinh hb.continuous hbc).const_mul
      (2 * oddPoleMoment (phiDoobTest a)))
    have h2 := (integrable_mul_kernel_cosh hb.continuous hbc).const_mul
      (2 * evenPoleMoment (phiDoobTest a))
    rw [← integral_sub hD ((integrable_mul_kernel_sinh hb.continuous hbc).const_mul _),
      ← integral_add h1 h2]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only [weilSource, Pi.sub_apply, Pi.add_apply]; ring)
  unfold fullZeroForm
  rw [markovEnergy_phiDoob_add ha hac hb hbc, hO, hE, hS]
  unfold markovDefect
  ring

/-- **Homogeneity.** `Ẑ(Φ(t b)) = t² Ẑ(Φ b)`. -/
theorem fullZeroForm_phiDoob_const_mul (hb : ContDiff ℝ 2 b') (hbc : HasCompactSupport b')
    (t : ℝ) :
    fullZeroForm (phiDoobTest fun y => t * b' y) = t ^ 2 * fullZeroForm (phiDoobTest b') := by
  have hO : oddPoleMoment (phiDoobTest fun y => t * b' y) = t * oddPoleMoment (phiDoobTest b') := by
    rw [oddPoleMoment_phiDoobTest, oddPoleMoment_phiDoobTest, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hE : evenPoleMoment (phiDoobTest fun y => t * b' y) =
      t * evenPoleMoment (phiDoobTest b') := by
    rw [evenPoleMoment_phiDoobTest, evenPoleMoment_phiDoobTest, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  unfold fullZeroForm
  rw [markovEnergy_phiDoob_const_mul hb hbc t, hO, hE]
  ring

/-- **Source law of a Rayleigh-critical gauge.** If `a ∈ C²_c` vanishes off `S = (b, c)` and attains
the Rayleigh bound `μ` of the window, then `𝒮(a) = μΦ²a` on `S`. -/
theorem weilSource_eq_of_rayleighCritical (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hab : ∀ x, x ∉ Ioo b c → a x = 0)
    (hbound : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, x ∉ Ioo b c → v x = 0) →
      μ * ∫ x, phiDoobTest v x ^ 2 ≤ fullZeroForm (phiDoobTest v))
    (hcrit : fullZeroForm (phiDoobTest a) = μ * ∫ x, phiDoobTest a x ^ 2) :
    ∀ x ∈ Ioo b c, weilSource a x = μ * (riemannKernelReal x ^ 2 * a x) := by
  set K : ℝ → ℝ := fun x => weilSource a x - μ * (riemannKernelReal x ^ 2 * a x)
  have hK : Continuous K :=
    (continuous_weilSource ha hac).sub (continuous_const.mul
      ((continuous_riemannKernelReal.pow 2).mul ha.continuous))
  have hint : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo b c →
      ∫ x, g x • K x = 0 := by
    intro g hg hgc hgs
    have hg2 : ContDiff ℝ 2 g := hg.of_le (by exact_mod_cast le_top)
    have hgb : ∀ x, x ∉ Ioo b c → g x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hgs h)
    have hAg : Integrable fun x => g x * weilSource a x :=
      (hg2.continuous.mul (continuous_weilSource ha hac)).integrable_of_hasCompactSupport
        hgc.mul_right
    have hPg : Integrable fun x => riemannKernelReal x ^ 2 * a x * g x :=
      (((continuous_riemannKernelReal.pow 2).mul ha.continuous).mul hg2.continuous)
        .integrable_of_hasCompactSupport hgc.mul_left
    have hPa : Integrable fun x => phiDoobTest a x ^ 2 :=
      ((continuous_riemannKernelReal.mul ha.continuous).pow 2).integrable_of_hasCompactSupport
        (by simpa [phiDoobTest] using (hac.mul_left (f' := riemannKernelReal)).comp_left
          (g := fun z : ℝ => z ^ 2) (by norm_num))
    have hPg2 : Integrable fun x => phiDoobTest g x ^ 2 :=
      ((continuous_riemannKernelReal.mul hg2.continuous).pow 2).integrable_of_hasCompactSupport
        (by simpa [phiDoobTest] using (hgc.mul_left (f' := riemannKernelReal)).comp_left
          (g := fun z : ℝ => z ^ 2) (by norm_num))
    set α := fullZeroForm (phiDoobTest g) - μ * ∫ x, phiDoobTest g x ^ 2
    set β := (∫ x, g x * weilSource a x) - μ * ∫ x, riemannKernelReal x ^ 2 * a x * g x
    have hq : ∀ t : ℝ, 0 ≤ α * (t * t) + (2 * β) * t + 0 := by
      intro t
      have hv : ContDiff ℝ 2 fun y => a y + t * g y := ha.add (contDiff_const.mul hg2)
      have hvc : HasCompactSupport fun y => a y + t * g y := hac.add (hgc.mul_left)
      have hvb : ∀ x, x ∉ Ioo b c → a x + t * g x = 0 := fun x hx => by
        rw [hab x hx, hgb x hx]; ring
      have h1 := hbound _ hv hvc hvb
      have hpol := fullZeroForm_phiDoob_add ha hac (contDiff_const.mul hg2) (hgc.mul_left (f' :=
        fun _ => t))
      rw [fullZeroForm_phiDoob_const_mul hg2 hgc t] at hpol
      have hcross : (∫ x, t * g x * weilSource a x) = t * ∫ x, g x * weilSource a x := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
      have hL2 : (∫ x, phiDoobTest (fun y => a y + t * g y) x ^ 2) =
          (∫ x, phiDoobTest a x ^ 2) + 2 * t * (∫ x, riemannKernelReal x ^ 2 * a x * g x) +
            t ^ 2 * ∫ x, phiDoobTest g x ^ 2 := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add hPa (hPg.const_mul _),
          ← integral_add (hPa.add (hPg.const_mul _)) (hPg2.const_mul _)]
        exact integral_congr_ae (Eventually.of_forall fun x => by
          simp only [phiDoobTest, Pi.add_apply]; ring)
      rw [hpol, hcross, hcrit, hL2] at h1
      nlinarith
    have hd := discrim_le_zero hq
    unfold discrim at hd
    have hβ : β = 0 := by nlinarith [sq_nonneg β]
    have hsplit : (∫ x, g x • K x) = β := by
      simp only [smul_eq_mul, K, β]
      rw [← integral_const_mul, ← integral_sub hAg (hPg.const_mul _)]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    rw [hsplit, hβ]
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hK.locallyIntegrable.locallyIntegrableOn hint
  have hres : K =ᵐ[volume.restrict (Ioo b c)] fun _ => 0 :=
    (ae_restrict_iff' measurableSet_Ioo).mpr hae
  have heq := Measure.eqOn_open_of_ae_eq hres isOpen_Ioo hK.continuousOn continuousOn_const
  intro x hx
  have := heq hx
  simp only [K] at this
  linarith

/-- The charges of a gauge vanishing off the window are its pole moments. -/
theorem sinhCharge_eq_oddPoleMoment (hab : ∀ x, x ∉ Ioo b c → a x = 0) :
    sinhCharge a (Ioo b c) = oddPoleMoment (phiDoobTest a) := by
  unfold sinhCharge oddPoleMoment phiDoobTest
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hab x hx]

theorem coshCharge_eq_evenPoleMoment (hab : ∀ x, x ∉ Ioo b c → a x = 0) :
    coshCharge a (Ioo b c) = evenPoleMoment (phiDoobTest a) := by
  unfold coshCharge evenPoleMoment phiDoobTest
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hab x hx]

/-- **Own-gauge representation of a Rayleigh-critical gauge.** -/
theorem fullZeroForm_phiDoob_mul_eq_of_rayleighCritical (ha : ContDiff ℝ 2 a)
    (hac : HasCompactSupport a) (hab : ∀ x, x ∉ Ioo b c → a x = 0)
    (hbound : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, x ∉ Ioo b c → v x = 0) →
      μ * ∫ x, phiDoobTest v x ^ 2 ≤ fullZeroForm (phiDoobTest v))
    (hcrit : fullZeroForm (phiDoobTest a) = μ * ∫ x, phiDoobTest a x ^ 2)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (hub : ∀ x, x ∉ Ioo b c → u x = 0) :
    fullZeroForm (phiDoobTest fun y => a y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y * a y) u +
        μ * (∫ x, u x ^ 2 * (riemannKernelReal x * a x) ^ 2) +
        2 * chargeVariance (fun x => riemannKernelReal x * a x * Real.sinh (x / 2)) (Ioo b c) u -
        2 * chargeVariance (fun x => riemannKernelReal x * a x * Real.cosh (x / 2)) (Ioo b c) u := by
  have hlaw := weilSource_eq_of_rayleighCritical ha hac hab hbound hcrit
  rw [fullZeroForm_phiDoob_mul_eq (b := b) (c := c) ha hac hu huc]
  have hpot : (∫ x, u x ^ 2 * a x * poleChargedDefect a (Ioo b c) x) =
      μ * ∫ x, u x ^ 2 * (riemannKernelReal x * a x) ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    by_cases hx : x ∈ Ioo b c
    · have h1 : poleChargedDefect a (Ioo b c) x = weilSource a x := by
        unfold poleChargedDefect weilSource
        rw [sinhCharge_eq_oddPoleMoment hab, coshCharge_eq_evenPoleMoment hab]
      rw [h1, hlaw x hx]; ring
    · rw [hub x hx]; ring
  rw [hpot]

/-- **A zero mode of a nonnegative window is a pole-charged harmonic gauge.** -/
theorem weilSource_eq_zero_of_zeroMode (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hab : ∀ x, x ∉ Ioo b c → a x = 0)
    (hpos : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, x ∉ Ioo b c → v x = 0) →
      0 ≤ fullZeroForm (phiDoobTest v))
    (h0 : fullZeroForm (phiDoobTest a) = 0) :
    ∀ x ∈ Ioo b c, weilSource a x = 0 := by
  intro x hx
  have h := weilSource_eq_of_rayleighCritical (μ := 0) ha hac hab
    (fun v hv hvc hvb => by simpa using hpos v hv hvc hvb) (by simpa using h0) x hx
  simpa using h

/-- **In the gauge of a zero mode the window form is a signed Dirichlet form.** -/
theorem fullZeroForm_phiDoob_mul_eq_of_zeroMode (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hab : ∀ x, x ∉ Ioo b c → a x = 0)
    (hpos : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, x ∉ Ioo b c → v x = 0) →
      0 ≤ fullZeroForm (phiDoobTest v))
    (h0 : fullZeroForm (phiDoobTest a) = 0)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (hub : ∀ x, x ∉ Ioo b c → u x = 0) :
    fullZeroForm (phiDoobTest fun y => a y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y * a y) u +
        2 * chargeVariance (fun x => riemannKernelReal x * a x * Real.sinh (x / 2)) (Ioo b c) u -
        2 * chargeVariance (fun x => riemannKernelReal x * a x * Real.cosh (x / 2)) (Ioo b c) u := by
  have h := fullZeroForm_phiDoob_mul_eq_of_rayleighCritical (μ := 0) ha hac hab
    (fun v hv hvc hvb => by simpa using hpos v hv hvc hvb) (by simpa using h0) hu huc hub
  rw [h]; ring

end GaloisForLFunctions.SignedWindowCriticality

end
