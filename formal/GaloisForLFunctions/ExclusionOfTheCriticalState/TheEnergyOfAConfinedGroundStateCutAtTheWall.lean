import GaloisForLFunctions.ExclusionOfTheCriticalState.EveryConfinedGroundStateHasAnAmplitudeAtTheWall
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergyTranslation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeightedSourceTruncation

/-!
# The energy of a confined ground state cut at the wall

Let `F` minimize the confined half-line form `Q_R` at a ratio `R > 0`, with ground energy
`λ(R)` and confinement coefficient `a(R)`. Cut `F` at `−k`: `E = F 1_{u < −k}`
(`wallExterior`) and `T = F − E` (`wallCollar`).

* **A terminal gap costs confinement energy at every ratio**
  (`criticalHalfLineFullEnergy_ge_ground_add_terminal_wall`). A profile `H` of the domain
  vanishing on `[−h, ∞)` has `Q_R(H) ≥ λ(R) ∫ H² + a(R) (1 − e^{−8h}) ∫ H² e^{−8u}`: its right
  translate by `h` is admissible, has the same mass and the same translation invariant rows, and
  a confinement term smaller by the factor `e^{−8h}`.
* **Sharp cuts of bounded profiles stay in the energy domain**
  (`criticalHalfLineEnergyDomain_wallExterior`): the jump created at the cut adds at most
  `∫ ω(x) min(C² x, ‖F‖²) dx` to the Lévy energy.
* **The energy of the cut state is its pairing across the cut**
  (`halfLineEnergyMinimizer_fullEnergy_eq_sub_mixed`): by the weak equation
  `Q_R(E) = λ ∫ F E − Q_R(E, F − E)`.
* **The pairing across the cut is carried by the logarithmic moment**
  (`neg_mixedEnergy_wallExterior_wallCollar_le`). The two pieces have disjoint supports, so the
  Lévy part of the pairing is `−∫∫ ω(v − u) E(u) T(v)`. Jumps longer than `k` see the collar
  through `L_F(k)/2 + O(1)`; the shorter jumps, the prime row and the pole row are bounded by
  the size of `F` on `(−2k, 0)`.

Together (`halfLineEnergyMinimizer_exists_wall_energy_le`): if `|F| ≤ B` on `(−2k, 0)`, then

  `a(R) (1 − e^{−8k}) ∫_{u<−k} F² e^{−8u} ≤ (L_F(k)/2) ∫_{−k}^0 F + K B k + B² k`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### A terminal gap costs confinement energy -/

/-- **A terminal gap costs confinement energy at every ratio.** A profile of the domain vanishing
on `[−h, ∞)` has energy at least `λ(R)` times its mass plus `a(R)(1 − e^{−8h})` times its
exponential mass. The right translate by `h` is admissible; the translation changes only the
confinement term. -/
theorem criticalHalfLineFullEnergy_ge_ground_add_terminal_wall {R : ℝ} (hR : 0 < R) {H : ℝ → ℝ}
    (hH : CriticalHalfLineEnergyDomain H) {h : ℝ} (hh : 0 ≤ h) (hgap : ∀ u, -h ≤ u → H u = 0) :
    criticalHalfLineGroundEnergy R * (∫ u, H u ^ 2) +
        criticalAliasCoefficient R * (1 - Real.exp (-(8 * h))) *
          (∫ u, H u ^ 2 * Real.exp (-(8 * u))) ≤ criticalHalfLineFullEnergy R H := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun u => H (u + (-h)) := ⟨_, rfl⟩
  have hdG : CriticalHalfLineEnergyDomain G := by
    rw [hGdef]
    exact hH.comp_add_right (-h) (fun u hu => hgap _ (by linarith only [hu]))
  have hback : (fun u => G (u + h)) = H := by
    rw [hGdef]
    funext u
    show H (u + h + (-h)) = H u
    rw [add_neg_cancel_right]
  have he := criticalHalfLineFullEnergy_comp_add_right hdG h R
    (fun u hu => hdG.support _ (add_nonneg hu hh))
  have hm := criticalHalfLineExponentialPair_comp_add_right G G h
  rw [hback] at he hm
  rw [criticalHalfLineExponentialPair_self, criticalHalfLineExponentialPair_self] at hm
  have hmass : (∫ u, G u ^ 2) = ∫ u, H u ^ 2 := by
    rw [hGdef]
    exact integral_add_right_eq_self (fun u => H u ^ 2) (-h)
  have hlow := criticalHalfLineGroundEnergy_mul_mass_le_all hR hdG
  rw [hmass] at hlow
  have hcoef : (1 - Real.exp (-(8 * h))) * Real.exp (8 * h) = Real.exp (8 * h) - 1 := by
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have e : criticalAliasCoefficient R * (1 - Real.exp (-(8 * h))) *
      (Real.exp (8 * h) * ∫ u, G u ^ 2 * Real.exp (-(8 * u))) =
      criticalAliasCoefficient R * (Real.exp (8 * h) - 1) *
        ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
    rw [← hcoef]
    ring
  rw [he, hm, e]
  linarith only [hlow]

/-! ### The two pieces of a profile cut at the wall -/

/-- The part of a profile left of `−k`. -/
def wallExterior (k : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := (Iio (-k)).indicator F

/-- The part of a profile on `[−k, ∞)`. -/
def wallCollar (k : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun u => F u + (-1) * wallExterior k F u

theorem wallExterior_of_lt {F : ℝ → ℝ} {k u : ℝ} (hu : u < -k) : wallExterior k F u = F u :=
  indicator_of_mem (mem_Iio.mpr hu) _

theorem wallExterior_of_ge {F : ℝ → ℝ} {k u : ℝ} (hu : -k ≤ u) : wallExterior k F u = 0 :=
  indicator_of_notMem (show u ∉ Iio (-k) from not_lt.mpr hu) _

theorem wallCollar_of_lt {F : ℝ → ℝ} {k u : ℝ} (hu : u < -k) : wallCollar k F u = 0 := by
  show F u + (-1) * wallExterior k F u = 0
  rw [wallExterior_of_lt hu]
  ring

theorem wallCollar_of_ge {F : ℝ → ℝ} {k u : ℝ} (hu : -k ≤ u) : wallCollar k F u = F u := by
  show F u + (-1) * wallExterior k F u = F u
  rw [wallExterior_of_ge hu]
  ring

theorem abs_wallExterior_le (F : ℝ → ℝ) (k u : ℝ) : |wallExterior k F u| ≤ |F u| := by
  rcases lt_or_ge u (-k) with h | h
  · rw [wallExterior_of_lt h]
  · rw [wallExterior_of_ge h, abs_zero]
    exact abs_nonneg _

theorem abs_wallCollar_le (F : ℝ → ℝ) (k u : ℝ) : |wallCollar k F u| ≤ |F u| := by
  rcases lt_or_ge u (-k) with h | h
  · rw [wallCollar_of_lt h, abs_zero]
    exact abs_nonneg _
  · rw [wallCollar_of_ge h]

/-- The two pieces have disjoint supports. -/
theorem wallExterior_mul_wallCollar (F : ℝ → ℝ) (k u : ℝ) :
    wallExterior k F u * wallCollar k F u = 0 := by
  rcases lt_or_ge u (-k) with h | h
  · rw [wallCollar_of_lt h, mul_zero]
  · rw [wallExterior_of_ge h, zero_mul]

/-- The square of the exterior piece is the cut of the square. -/
theorem sq_wallExterior (F : ℝ → ℝ) (k : ℝ) :
    (fun u => wallExterior k F u ^ 2) = (Iio (-k)).indicator fun u => F u ^ 2 := by
  funext u
  by_cases hu : u ∈ Iio (-k)
  · rw [indicator_of_mem hu, wallExterior_of_lt (mem_Iio.mp hu)]
  · rw [indicator_of_notMem hu, wallExterior_of_ge (not_lt.mp hu), zero_pow two_ne_zero]

/-! ### Sharp cuts of bounded profiles -/

/-- The increments of the exterior piece: only the jumps across the cut are new,
`∫ (ΔE)² ≤ ∫ (ΔF)² + ∫_{[−k−x, −k]} F²`. -/
theorem integral_sq_increment_wallExterior_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (k : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ u, (wallExterior k F u - wallExterior k F (u + x)) ^ 2 ≤
      (∫ u, (F u - F (u + x)) ^ 2) + ∫ u in Icc (-k - x) (-k), F u ^ 2 := by
  have hEm : Measurable (wallExterior k F) := hF.meas.indicator measurableSet_Iio
  have hE2 : Integrable fun u => wallExterior k F u ^ 2 := by
    rw [sq_wallExterior]
    exact hF.sq.indicator measurableSet_Iio
  have hEmem : MemLp (wallExterior k F) 2 volume :=
    (memLp_two_iff_integrable_sq hEm.aestronglyMeasurable).mpr hE2
  have hi : Integrable fun u => (wallExterior k F u - wallExterior k F (u + x)) ^ 2 :=
    integrable_sq_of_memLp (hEmem.sub (memLp_two_shift hEmem x))
  have hd1 : Integrable fun u => (F u - F (u + x)) ^ 2 :=
    integrable_sq_of_memLp (hF.memLp_real.sub (memLp_two_shift hF.memLp_real x))
  have hd2 : Integrable ((Icc (-k - x) (-k)).indicator fun u => F u ^ 2) :=
    hF.sq.indicator measurableSet_Icc
  have hpt : ∀ u, (wallExterior k F u - wallExterior k F (u + x)) ^ 2 ≤
      (F u - F (u + x)) ^ 2 + (Icc (-k - x) (-k)).indicator (fun u => F u ^ 2) u := by
    intro u
    have hind : 0 ≤ (Icc (-k - x) (-k)).indicator (fun u => F u ^ 2) u :=
      indicator_nonneg (fun v _ => sq_nonneg (F v)) u
    rcases lt_or_ge (u + x) (-k) with h1 | h1
    · rw [wallExterior_of_lt (show u < -k by linarith only [h1, hx]), wallExterior_of_lt h1]
      linarith only [hind]
    · rw [wallExterior_of_ge h1, sub_zero]
      rcases lt_or_ge u (-k) with h2 | h2
      · rw [wallExterior_of_lt h2,
          indicator_of_mem (show u ∈ Icc (-k - x) (-k) from ⟨by linarith only [h1], h2.le⟩)]
        linarith only [sq_nonneg (F u - F (u + x))]
      · rw [wallExterior_of_ge h2, zero_pow two_ne_zero]
        linarith only [hind, sq_nonneg (F u - F (u + x))]
  have hmono : ∫ u, (wallExterior k F u - wallExterior k F (u + x)) ^ 2 ≤
      ∫ u, ((F u - F (u + x)) ^ 2 + (Icc (-k - x) (-k)).indicator (fun u => F u ^ 2) u) :=
    integral_mono hi (hd1.add hd2) hpt
  rw [integral_add hd1 hd2, integral_indicator measurableSet_Icc] at hmono
  exact hmono

/-- **Sharp cuts of bounded profiles lie in the energy domain.** The jump created at the cut has
Lévy energy at most `∫ ω(x) min(C² x, ‖F‖²) dx`. -/
theorem criticalHalfLineEnergyDomain_wallExterior {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {C : ℝ} (hC : ∀ᵐ u : ℝ, |F u| ≤ C) (k : ℝ) :
    CriticalHalfLineEnergyDomain (wallExterior k F) := by
  have hEm : Measurable (wallExterior k F) := hF.meas.indicator measurableSet_Iio
  have hE1 : Integrable (wallExterior k F) := hF.integrable.indicator measurableSet_Iio
  have hE2 : Integrable fun u => wallExterior k F u ^ 2 := by
    rw [sq_wallExterior]
    exact hF.sq.indicator measurableSet_Iio
  have hexp : Integrable fun u => wallExterior k F u ^ 2 * Real.exp (-(8 * u)) := by
    have e : (fun u => wallExterior k F u ^ 2 * Real.exp (-(8 * u))) =
        (Iio (-k)).indicator fun u => F u ^ 2 * Real.exp (-(8 * u)) := by
      funext u
      by_cases hu : u ∈ Iio (-k)
      · rw [indicator_of_mem hu, wallExterior_of_lt (mem_Iio.mp hu)]
      · rw [indicator_of_notMem hu, wallExterior_of_ge (not_lt.mp hu), zero_pow two_ne_zero,
          zero_mul]
    rw [e]
    exact hF.exponential.indicator measurableSet_Iio
  have hsupp : ∀ u, 0 ≤ u → wallExterior k F u = 0 := fun u hu => by
    rcases lt_or_ge u (-k) with h | h
    · rw [wallExterior_of_lt h]
      exact hF.support u hu
    · exact wallExterior_of_ge h
  refine ⟨hEm, hE1, hE2, hexp, hsupp, ?_⟩
  apply integrable_gamma_of_lintegral_levy_ne_top hE1 hE2
  have hS0 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun u => sq_nonneg _
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 2 * C ^ 2 + 2 * ∫ u, F u ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact add_nonneg (mul_nonneg zero_le_two (sq_nonneg C)) (mul_nonneg zero_le_two hS0)
  have hDi : IntegrableOn (fun x : ℝ =>
      archLevyDensity x * (∫ u, (F u - F (u + x)) ^ 2) + D * Real.exp (-(x / 2))) (Ioi 0) :=
    hF.integrableOn_levyIntegrand.add (integrableOn_exp_neg_half.const_mul D)
  have hle : ∀ x ∈ Ioi (0 : ℝ), archLevyDensity x *
      (∫ u, (wallExterior k F u - wallExterior k F (u + x)) ^ 2) ≤
      archLevyDensity x * (∫ u, (F u - F (u + x)) ^ 2) + D * Real.exp (-(x / 2)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hω := (archLevyDensity_pos hx0).le
    have he := Real.exp_pos (-(x / 2))
    have h1 := mul_le_mul_of_nonneg_left (integral_sq_increment_wallExterior_le hF k hx0) hω
    rw [mul_add] at h1
    have hpart : archLevyDensity x * (∫ u in Icc (-k - x) (-k), F u ^ 2) ≤
        D * Real.exp (-(x / 2)) := by
      rcases le_total x 1 with hx1 | hx1
      · -- short jumps: the cut removes a bounded profile on an interval of length `x`
        have hI : ∫ u in Icc (-k - x) (-k), F u ^ 2 ≤ C ^ 2 * x := by
          have h := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
            (s := Icc (-k - x) (-k)) (f := fun u => F u ^ 2) (C := C ^ 2) measure_Icc_lt_top
            (ae_restrict_of_ae (hC.mono fun u hu => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) hu 2))
          rw [Real.volume_real_Icc_of_le (by linarith only [hx0]), Real.norm_eq_abs] at h
          have h' := (le_abs_self _).trans h
          linarith only [h']
        have hωx := archLevyDensity_mul_self_le_one hx0 (by linarith only [hx1])
        have hexp2 : (1 : ℝ) / 2 ≤ Real.exp (-(x / 2)) := by
          have h := Real.add_one_le_exp (-(x / 2))
          linarith only [h, hx1]
        calc archLevyDensity x * (∫ u in Icc (-k - x) (-k), F u ^ 2)
            ≤ archLevyDensity x * (C ^ 2 * x) := mul_le_mul_of_nonneg_left hI hω
          _ = C ^ 2 * (archLevyDensity x * x) := by ring
          _ ≤ C ^ 2 * 1 := mul_le_mul_of_nonneg_left hωx (sq_nonneg C)
          _ ≤ D * Real.exp (-(x / 2)) := by
              rw [hDdef]
              nlinarith only [mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hexp2),
                mul_nonneg hS0 he.le]
      · -- long jumps: the mass against the exponential decay of `ω`
        have hfar := archLevyDensity_le_far hx1
        have hI : ∫ u in Icc (-k - x) (-k), F u ^ 2 ≤ ∫ u, F u ^ 2 :=
          setIntegral_le_integral hF.sq (Eventually.of_forall fun u => sq_nonneg (F u))
        have hI0 : 0 ≤ ∫ u in Icc (-k - x) (-k), F u ^ 2 := integral_nonneg fun u => sq_nonneg _
        calc archLevyDensity x * (∫ u in Icc (-k - x) (-k), F u ^ 2)
            ≤ 2 * Real.exp (-(x / 2)) * (∫ u, F u ^ 2) := mul_le_mul hfar hI hI0 (by positivity)
          _ ≤ D * Real.exp (-(x / 2)) := by
              rw [hDdef]
              nlinarith only [mul_nonneg (sq_nonneg C) he.le]
    linarith only [h1, hpart]
  have hDnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x : ℝ =>
      archLevyDensity x * (∫ u, (F u - F (u + x)) ^ 2) + D * Real.exp (-(x / 2)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx => add_nonneg
      (mul_nonneg (archLevyDensity_pos (show (0 : ℝ) < x from hx)).le
        (integral_nonneg fun u => sq_nonneg _))
      (mul_nonneg hD0 (Real.exp_pos _).le)
  refine (lt_of_le_of_lt (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono
    fun x hx => ENNReal.ofReal_le_ofReal (hle x hx))) ?_).ne
  rw [← ofReal_integral_eq_lintegral_ofReal hDi hDnn]
  exact ENNReal.ofReal_lt_top

/-- The collar piece of a bounded profile of the domain lies in the domain. -/
theorem criticalHalfLineEnergyDomain_wallCollar {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {C : ℝ} (hC : ∀ᵐ u : ℝ, |F u| ≤ C) (k : ℝ) :
    CriticalHalfLineEnergyDomain (wallCollar k F) :=
  hF.add_const_mul (criticalHalfLineEnergyDomain_wallExterior hF hC k) (-1)

/-! ### The energy of a piece of a minimizer -/

/-- **The energy of a piece of a minimizer is its pairing with the rest.** For a minimizer `F` at
ratio `R` and any `E` of the domain, the weak equation gives
`Q_R(E) = λ(R) ∫ F E − Q_R(E, F − E)`. -/
theorem halfLineEnergyMinimizer_fullEnergy_eq_sub_mixed {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {E : ℝ → ℝ} (hE : CriticalHalfLineEnergyDomain E) :
    criticalHalfLineFullEnergy R E =
      criticalHalfLineGroundEnergy R * (∫ u, F u * E u) -
        criticalHalfLineMixedEnergy R E (fun u => F u + (-1) * E u) := by
  have hT : CriticalHalfLineEnergyDomain (fun u => F u + (-1) * E u) := hF.1.add_const_mul hE (-1)
  have h1 := criticalHalfLineFullEnergy_add_const_mul R hF.1 hE (-1)
  have h2 := criticalHalfLineFullEnergy_add_const_mul R hE hT 1
  have hback : (fun u => E u + 1 * (F u + (-1) * E u)) = F := by
    funext u
    ring
  rw [hback, hF.2.2] at h2
  rw [hF.2.2, hF.weakEquation hR hE] at h1
  linear_combination (-1 / 2 : ℝ) * h2 - (1 / 2 : ℝ) * h1

/-! ### The pairing across the cut -/

/-- At the lags inside the cutoff the symmetric kernel vanishes. -/
theorem symCutoffKernel_of_nonneg_of_le {δ s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ δ) :
    symCutoffKernel δ s = 0 := by
  unfold symCutoffKernel halfLineGammaCutoffKernel
  have h1 : s ∉ Ioi δ := by
    rw [mem_Ioi, not_lt]
    exact hs
  have h2 : -s ∉ Ioi δ := by
    rw [mem_Ioi, not_lt]
    linarith only [hs0, hs]
  rw [indicator_of_notMem h1, indicator_of_notMem h2, add_zero]

/-- **Jumps longer than the collar see it through the logarithmic moment.** For `0 < t ≤ k` the
kernel cut at the lag `k`, applied to the exterior piece at `−t`, is `L_F(k)/2` up to
`‖F‖₁/4 + C`. -/
theorem abs_cutExterior_sub_half_wallLogMoment_le {F : ℝ → ℝ} (hFm : Measurable F)
    (hF1 : Integrable F) (hF2 : Integrable fun u => F u ^ 2) {C : ℝ} (hC0 : 0 ≤ C)
    (hFC : ∀ᵐ u : ℝ, |F u| ≤ C) {k t : ℝ} (ht : 0 < t) (htk : t ≤ k) :
    |lineConvolution (symCutoffKernel k) (wallExterior k F) (-t) - wallLogMoment F k / 2| ≤
      (∫ u, |F u|) / 4 + C := by
  have hk : 0 < k := lt_of_lt_of_le ht htk
  have hXm : Measurable (wallExterior k F) := hFm.indicator measurableSet_Iio
  have hX2 : Integrable fun u => wallExterior k F u ^ 2 := by
    rw [sq_wallExterior]
    exact hF2.indicator measurableSet_Iio
  have hI1 : Integrable fun s => symCutoffKernel k s * wallExterior k F (-t - s) :=
    integrable_symCutoffKernel_mul_translate hk hXm hX2 (-t)
  have hdiv : IntegrableOn (fun v => F (-v) / v) (Ioi k) :=
    integrableOn_div_self (f := fun v => F (-v)) (hFm.comp measurable_neg) hF1.comp_neg hk
  have hI2 : Integrable fun s => (Ioi k).indicator (fun v => F (-v) / v) (s + t) :=
    (hdiv.integrable_indicator measurableSet_Ioi).comp_add_right t
  have hmom : wallLogMoment F k = ∫ s, (Ioi k).indicator (fun v => F (-v) / v) (s + t) := by
    rw [integral_add_right_eq_self ((Ioi k).indicator fun v => F (-v) / v) t,
      integral_indicator measurableSet_Ioi, wallLogMoment]
  have hdiff : lineConvolution (symCutoffKernel k) (wallExterior k F) (-t) -
      wallLogMoment F k / 2 = ∫ s, (symCutoffKernel k s * wallExterior k F (-t - s) -
        (Ioi k).indicator (fun v => F (-v) / v) (s + t) / 2) := by
    rw [hmom, integral_sub hI1 (hI2.div_const 2), integral_div]
    rfl
  have hFC' : ∀ᵐ s : ℝ, |F (-t - s)| ≤ C := ae_comp_const_sub hFC (-t)
  have hpow : IntegrableOn (fun s : ℝ => s ^ (-(2 : ℝ))) (Ioi k) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hk
  have hg1 : Integrable fun s => |F (-t - s)| / 4 := (hF1.abs.comp_sub_left (-t)).div_const 4
  have hg2 : Integrable fun s =>
      C * (t / 2) * (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s :=
    (hpow.integrable_indicator measurableSet_Ioi).const_mul _
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (k - t) k) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hg3 : Integrable fun s =>
      C / (2 * k) * (Ioc (k - t) k).indicator (fun _ : ℝ => (1 : ℝ)) s :=
    (hone.integrable_indicator measurableSet_Ioc).const_mul _
  have hg12 : Integrable fun s => |F (-t - s)| / 4 +
      C * (t / 2) * (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s := hg1.add hg2
  have hg : Integrable fun s => |F (-t - s)| / 4 +
      C * (t / 2) * (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s +
      C / (2 * k) * (Ioc (k - t) k).indicator (fun _ : ℝ => (1 : ℝ)) s := hg12.add hg3
  have hbound : ∀ᵐ s : ℝ, ‖symCutoffKernel k s * wallExterior k F (-t - s) -
      (Ioi k).indicator (fun v => F (-v) / v) (s + t) / 2‖ ≤ |F (-t - s)| / 4 +
        C * (t / 2) * (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s +
        C / (2 * k) * (Ioc (k - t) k).indicator (fun _ : ℝ => (1 : ℝ)) s := by
    filter_upwards [hFC'] with s hs
    have hF0 : 0 ≤ |F (-t - s)| / 4 := div_nonneg (abs_nonneg _) (by norm_num)
    rcases le_or_gt s (k - t) with h1 | h1
    · -- lags that stay right of the cut: everything vanishes
      have e1 : wallExterior k F (-t - s) = 0 := wallExterior_of_ge (by linarith only [h1])
      have e2 : (Ioi k).indicator (fun v => F (-v) / v) (s + t) = 0 :=
        indicator_of_notMem (by
          rw [mem_Ioi, not_lt]
          linarith only [h1]) _
      have e3 : (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s = 0 :=
        indicator_of_notMem (by
          rw [mem_Ioi, not_lt]
          linarith only [h1, ht]) _
      have e4 : (Ioc (k - t) k).indicator (fun _ : ℝ => (1 : ℝ)) s = 0 :=
        indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr h1)) _
      rw [e1, e2, e3, e4]
      simp only [mul_zero, zero_div, sub_zero, norm_zero, add_zero]
      exact hF0
    · have hst : k < s + t := by linarith only [h1]
      have hst0 : 0 < s + t := lt_trans hk hst
      have e1 : wallExterior k F (-t - s) = F (-t - s) :=
        wallExterior_of_lt (by linarith only [h1])
      have e2 : (Ioi k).indicator (fun v => F (-v) / v) (s + t) = F (-(s + t)) / (s + t) :=
        indicator_of_mem (mem_Ioi.mpr hst) _
      rw [e1, e2, show -(s + t) = -t - s by ring]
      rcases le_or_gt s k with h2 | h2
      · -- lags inside the cutoff: only the logarithmic moment contributes
        have hs0 : 0 ≤ s := by linarith only [h1, htk]
        have e3 : (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s = 0 :=
          indicator_of_notMem (by
            rw [mem_Ioi, not_lt]
            exact h2) _
        have e4 : (Ioc (k - t) k).indicator (fun _ : ℝ => (1 : ℝ)) s = 1 :=
          indicator_of_mem (show s ∈ Ioc (k - t) k from ⟨h1, h2⟩) _
        rw [symCutoffKernel_of_nonneg_of_le hs0 h2, e3, e4, zero_mul, zero_sub, norm_neg,
          mul_zero, add_zero, mul_one, Real.norm_eq_abs, abs_div, abs_div, abs_two,
          abs_of_pos hst0]
        have h3 : |F (-t - s)| / (s + t) / 2 ≤ C / (2 * k) := by
          rw [div_div, div_le_div_iff₀ (mul_pos hst0 two_pos) (mul_pos two_pos hk)]
          nlinarith only [mul_nonneg (sub_nonneg.mpr hs) hk.le,
            mul_nonneg hC0 (sub_nonneg.mpr hst.le)]
        linarith only [h3, hF0]
      · have hs0 : 0 < s := lt_trans hk h2
        have e3 : (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s = s ^ (-(2 : ℝ)) :=
          indicator_of_mem (mem_Ioi.mpr h2) _
        have e4 : (Ioc (k - t) k).indicator (fun _ : ℝ => (1 : ℝ)) s = 0 :=
          indicator_of_notMem (fun h => absurd h.2 (not_le.mpr h2)) _
        rw [symCutoffKernel_of_lt hk h2, e3, e4, mul_zero, add_zero]
        have hker := abs_archLevyDensity_sub_half_inv_add_le hs0 ht.le
        have e : archLevyDensity s * F (-t - s) - F (-t - s) / (s + t) / 2 =
            (archLevyDensity s - 1 / (2 * (s + t))) * F (-t - s) := by
          rw [show (1 : ℝ) / (2 * (s + t)) = 1 / (s + t) / 2 by rw [div_div, mul_comm]]
          ring
        rw [e, Real.norm_eq_abs, abs_mul]
        have hp : 0 ≤ s ^ (-(2 : ℝ)) := Real.rpow_nonneg hs0.le _
        have h3 : |archLevyDensity s - 1 / (2 * (s + t))| * |F (-t - s)| ≤
            (1 / 4 + t / 2 * s ^ (-(2 : ℝ))) * |F (-t - s)| :=
          mul_le_mul_of_nonneg_right hker (abs_nonneg _)
        have h4 : t / 2 * s ^ (-(2 : ℝ)) * |F (-t - s)| ≤ t / 2 * s ^ (-(2 : ℝ)) * C :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg (by linarith only [ht]) hp)
        linarith only [h3, h4]
  have hgint : ∫ s, (|F (-t - s)| / 4 +
      C * (t / 2) * (Ioi k).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s +
      C / (2 * k) * (Ioc (k - t) k).indicator (fun _ : ℝ => (1 : ℝ)) s) =
      (∫ u, |F u|) / 4 + C * (t / 2) * k⁻¹ + C / (2 * k) * t := by
    rw [integral_add hg12 hg3, integral_add hg1 hg2, integral_div, integral_const_mul,
      integral_const_mul, integral_indicator measurableSet_Ioi,
      integral_Ioi_rpow_neg_two_eq_inv hk, integral_indicator_const (1 : ℝ) measurableSet_Ioc,
      Real.volume_real_Ioc_of_le (by linarith only [ht]),
      integral_sub_left_eq_self (fun u => |F u|) volume (-t), smul_eq_mul, mul_one]
    ring
  have hfin : C * (t / 2) * k⁻¹ + C / (2 * k) * t ≤ C := by
    have h1 : t * k⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hk]
      exact htk
    have e : C * (t / 2) * k⁻¹ + C / (2 * k) * t = C * (t * k⁻¹) := by ring
    rw [e]
    exact mul_le_of_le_one_right hC0 h1
  rw [hdiff, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg hbound).trans (hgint.le.trans ?_)
  linarith only [hfin]

/-- **Short jumps across the cut.** The jumps of length at most `k` pair the two pieces only
through a strip of that length on each side of the cut, where `|F| ≤ B`. -/
theorem abs_setIntegral_mixedJump_wall_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {k : ℝ} (hk : 0 < k) (hk2 : k ≤ 2) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ u : ℝ, -(2 * k) ≤ u → u < 0 → |F u| ≤ B) :
    |∫ x in Ioc 0 k, halfLineGammaMixedJump (wallExterior k F) (wallCollar k F) x| ≤
      B ^ 2 * k := by
  have hpt : ∀ x ∈ Ioc (0 : ℝ) k,
      ‖halfLineGammaMixedJump (wallExterior k F) (wallCollar k F) x‖ ≤ B ^ 2 := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hω := (archLevyDensity_pos hx0).le
    have hBx : ∀ᵐ u : ℝ, -(2 * k) ≤ u + x → u + x < 0 → |F (u + x)| ≤ B := by
      have h := ae_comp_sub_right hB (-x)
      filter_upwards [h] with u hu
      rw [sub_neg_eq_add] at hu
      exact hu
    have hint : |∫ u, (wallExterior k F u - wallExterior k F (u + x)) *
        (wallCollar k F u - wallCollar k F (u + x))| ≤ B ^ 2 * x := by
      have hconst : IntegrableOn (fun _ : ℝ => B ^ 2) (Icc (-k - x) (-k)) :=
        integrableOn_const (hs := measure_Icc_lt_top.ne)
      have hle := norm_integral_le_of_norm_le (hconst.integrable_indicator measurableSet_Icc)
        (f := fun u => (wallExterior k F u - wallExterior k F (u + x)) *
          (wallCollar k F u - wallCollar k F (u + x))) (by
          filter_upwards [hB, hBx] with u hu hux
          have e : (wallExterior k F u - wallExterior k F (u + x)) *
              (wallCollar k F u - wallCollar k F (u + x)) =
              -(wallExterior k F u * wallCollar k F (u + x)) := by
            rcases lt_or_ge u (-k) with h1 | h1
            · rw [wallCollar_of_lt h1]
              rcases lt_or_ge (u + x) (-k) with h2 | h2
              · rw [wallCollar_of_lt h2]
                ring
              · rw [wallExterior_of_ge h2]
                ring
            · rw [wallExterior_of_ge h1, wallExterior_of_ge (by linarith only [h1, hx0])]
              ring
          rw [e, norm_neg, Real.norm_eq_abs, abs_mul]
          by_cases hmem : u ∈ Icc (-k - x) (-k)
          · rw [indicator_of_mem hmem, pow_two]
            have h1 : |wallExterior k F u| ≤ B :=
              (abs_wallExterior_le F k u).trans
                (hu (by linarith only [hmem.1, hx.2]) (by linarith only [hmem.2, hk]))
            have h2 : |wallCollar k F (u + x)| ≤ B := by
              rcases le_or_gt 0 (u + x) with h0 | h0
              · rw [wallCollar_of_ge (by linarith only [h0, hk]), hF.support _ h0, abs_zero]
                exact hB0
              · exact (abs_wallCollar_le F k _).trans
                  (hux (by linarith only [hmem.1, hk]) h0)
            exact mul_le_mul h1 h2 (abs_nonneg _) hB0
          · rw [indicator_of_notMem hmem]
            rcases lt_or_ge u (-k - x) with h1 | h1
            · rw [wallCollar_of_lt (by linarith only [h1]), abs_zero, mul_zero]
            · have h2 : -k < u := by
                by_contra hn
                exact hmem ⟨h1, not_lt.mp hn⟩
              rw [wallExterior_of_ge h2.le, abs_zero, zero_mul])
      rw [integral_indicator_const (B ^ 2) measurableSet_Icc,
        Real.volume_real_Icc_of_le (by linarith only [hx0]), smul_eq_mul,
        Real.norm_eq_abs] at hle
      linarith only [hle]
    have hωx := archLevyDensity_mul_self_le_one hx0 (by linarith only [hx.2, hk2])
    unfold halfLineGammaMixedJump
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hω]
    refine (mul_le_mul_of_nonneg_left hint hω).trans ?_
    calc archLevyDensity x * (B ^ 2 * x) = B ^ 2 * (archLevyDensity x * x) := by ring
      _ ≤ B ^ 2 * 1 := mul_le_mul_of_nonneg_left hωx (sq_nonneg B)
      _ = B ^ 2 := mul_one _
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hpt
  rw [Real.volume_real_Ioc_of_le hk.le, sub_zero, Real.norm_eq_abs] at h
  exact h

/-- **The prime row across the cut.** Against a profile carried by `[−1/2, 0)` only the backward
shifts of the prime row are present, and an exponentially bounded profile makes them summable. -/
theorem abs_primeMixedForm_le_of_terminal {X T : ℝ → ℝ} (hX : CriticalHalfLineEnergyDomain X)
    (hT : CriticalHalfLineEnergyDomain T) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hX1 : ∀ᵐ u : ℝ, |X u| ≤ C₁ * Real.exp (1 * u)) (hTs : ∀ u, u < -(1 / 2) → T u = 0) :
    |primeMixedForm X T| ≤ C₁ * halfLineExponentialPrimeTail 1 * ∫ u, |T u| := by
  have hterm : ∀ n : ℕ, |primePairTerm X T n| ≤
      vonMangoldtAtom n * Real.exp (-(1 * Real.log (n : ℝ))) * (C₁ * ∫ u, |T u|) := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · have h0 : vonMangoldtAtom n = 0 := by
        unfold vonMangoldtAtom
        rw [if_neg (not_le.mpr hn)]
      unfold primePairTerm
      rw [h0, zero_mul, zero_mul, zero_mul, abs_zero]
    · have hlog2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
      have hlog : 1 / 2 < Real.log (n : ℝ) :=
        lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
      have ha0 : 0 ≤ vonMangoldtAtom n := by
        unfold vonMangoldtAtom
        rw [if_pos hn]
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      have hfirst : ∫ t, X t * T (t - Real.log n) = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
        show X t * T (t - Real.log n) = 0
        rcases le_or_gt 0 t with ht | ht
        · rw [hX.support t ht, zero_mul]
        · rw [hTs _ (by linarith only [ht, hlog]), mul_zero]
      have hsecond : |∫ t, X t * T (t + Real.log n)| ≤
          C₁ * Real.exp (-(1 * Real.log (n : ℝ))) * ∫ u, |T u| := by
        have hTt : Integrable fun t => |T (t + Real.log n)| :=
          hT.integrable.abs.comp_add_right _
        have h := norm_integral_le_of_norm_le
          (hTt.const_mul (C₁ * Real.exp (-(1 * Real.log (n : ℝ)))))
          (f := fun t => X t * T (t + Real.log n)) (by
            filter_upwards [hX1] with t ht
            rw [Real.norm_eq_abs, abs_mul]
            rcases le_or_gt 0 (t + Real.log n) with h | h
            · rw [hT.support _ h, abs_zero, mul_zero, mul_zero]
            · have he : Real.exp (1 * t) ≤ Real.exp (-(1 * Real.log (n : ℝ))) :=
                Real.exp_le_exp.mpr (by linarith only [h])
              exact mul_le_mul_of_nonneg_right
                (ht.trans (mul_le_mul_of_nonneg_left he hC₁0)) (abs_nonneg _))
        rw [Real.norm_eq_abs, integral_const_mul,
          integral_add_right_eq_self (fun u => |T u|) (Real.log n)] at h
        exact h
      unfold primePairTerm
      rw [hfirst, zero_add, abs_mul, abs_of_nonneg ha0]
      calc vonMangoldtAtom n * |∫ t, X t * T (t + Real.log n)|
          ≤ vonMangoldtAtom n * (C₁ * Real.exp (-(1 * Real.log (n : ℝ))) * ∫ u, |T u|) :=
            mul_le_mul_of_nonneg_left hsecond ha0
        _ = _ := by ring
  have hs := summable_primePairTerm hX.weighted hT.weighted
  have hsumB := (summable_exponentialBarrier_prime_backward (β := 1) (by norm_num)).mul_right
    (C₁ * ∫ u, |T u|)
  have hnorm := norm_tsum_le_tsum_norm hs.norm
  simp only [Real.norm_eq_abs] at hnorm
  unfold primeMixedForm
  refine hnorm.trans ((hs.abs.tsum_le_tsum hterm hsumB).trans_eq ?_)
  rw [tsum_mul_right]
  unfold halfLineExponentialPrimeTail
  ring

/-- **The pole row across the cut.** Both hyperbolic moments of a profile carried by
`[−1/2, 0)` are bounded by its mass. -/
theorem abs_polarMixed_le_of_terminal {X T : ℝ → ℝ} (hX : CriticalHalfLineEnergyDomain X)
    (hT : CriticalHalfLineEnergyDomain T) (hTs : ∀ u, u < -(1 / 2) → T u = 0) :
    |2 * coshHalfMoment X * coshHalfMoment T - 2 * sinhHalfMoment X * sinhHalfMoment T| ≤
      4 * Real.exp (1 / 4) * (Real.sqrt (exponentialSourceMass X) *
        Real.sqrt (∫ u, Real.exp (-|u|))) * ∫ u, |T u| := by
  have hcc : Continuous fun u : ℝ => Real.cosh (u / 2) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  have hsc : Continuous fun u : ℝ => Real.sinh (u / 2) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Real.sqrt (exponentialSourceMass X) *
      Real.sqrt (∫ u, Real.exp (-|u|)) := ⟨_, rfl⟩
  have hXc : |coshHalfMoment X| ≤ P := by
    rw [hPdef]
    exact (abs_integral_mul_kernel_le hX.weighted hcc abs_cosh_half_le_exp).2
  have hXs : |sinhHalfMoment X| ≤ P := by
    rw [hPdef]
    exact (abs_integral_mul_kernel_le hX.weighted hsc abs_sinh_half_le_exp).2
  have hker : ∀ κ : ℝ → ℝ, (∀ u, |κ u| ≤ Real.exp (|u| / 2)) →
      |∫ u, T u * κ u| ≤ Real.exp (1 / 4) * ∫ u, |T u| := by
    intro κ hκ
    have h := norm_integral_le_of_norm_le (hT.integrable.abs.const_mul (Real.exp (1 / 4)))
      (f := fun u => T u * κ u) (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm |T u|]
        rcases lt_or_ge u (-(1 / 2)) with h | h
        · rw [hTs u h, abs_zero, mul_zero, mul_zero]
        · rcases le_or_gt 0 u with h0 | h0
          · rw [hT.support u h0, abs_zero, mul_zero, mul_zero]
          · have he : Real.exp (|u| / 2) ≤ Real.exp (1 / 4) :=
              Real.exp_le_exp.mpr (by
                rw [abs_of_neg h0]
                linarith only [h])
            exact mul_le_mul_of_nonneg_right ((hκ u).trans he) (abs_nonneg _))
    rwa [Real.norm_eq_abs, integral_const_mul] at h
  have hTc : |coshHalfMoment T| ≤ Real.exp (1 / 4) * ∫ u, |T u| :=
    hker (fun u => Real.cosh (u / 2)) abs_cosh_half_le_exp
  have hTsn : |sinhHalfMoment T| ≤ Real.exp (1 / 4) * ∫ u, |T u| :=
    hker (fun u => Real.sinh (u / 2)) abs_sinh_half_le_exp
  have hP0 : 0 ≤ P := (abs_nonneg _).trans hXc
  rw [← hPdef]
  have h1 : |coshHalfMoment X * coshHalfMoment T| ≤ P * (Real.exp (1 / 4) * ∫ u, |T u|) := by
    rw [abs_mul]
    exact mul_le_mul hXc hTc (abs_nonneg _) hP0
  have h2 : |sinhHalfMoment X * sinhHalfMoment T| ≤ P * (Real.exp (1 / 4) * ∫ u, |T u|) := by
    rw [abs_mul]
    exact mul_le_mul hXs hTsn (abs_nonneg _) hP0
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

/-- **The pairing across the cut is carried by the logarithmic moment.** For a bounded,
exponentially bounded profile `F` of the domain with `|F| ≤ B` on `[−2k, 0)`, the pairing of
the two pieces of `F` cut at `−k` is `−(L_F(k)/2) ∫_{−k}^0 F` up to `K B k + B² k`. -/
theorem neg_mixedEnergy_wallExterior_wallCollar_le (R : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ u : ℝ, |F u| ≤ C)
    {C₁ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₁ : ∀ᵐ u : ℝ, |F u| ≤ C₁ * Real.exp (1 * u)) {k : ℝ}
    (hk : 0 < k) (hk2 : k ≤ 1 / 2) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ u : ℝ, -(2 * k) ≤ u → u < 0 → |F u| ≤ B) :
    -criticalHalfLineMixedEnergy R (wallExterior k F) (wallCollar k F) ≤
      wallLogMoment F k / 2 * (∫ u in Ioo (-k) 0, F u) +
        ((∫ u, |F u|) / 4 + C + C₁ * halfLineExponentialPrimeTail 1 +
          4 * Real.exp (1 / 4) * (Real.sqrt (exponentialSourceMass F) *
            Real.sqrt (∫ u, Real.exp (-|u|)))) * (B * k) + B ^ 2 * k := by
  have hE := criticalHalfLineEnergyDomain_wallExterior hF hC k
  have hT := criticalHalfLineEnergyDomain_wallCollar hF hC k
  have hTs : ∀ u, u < -(1 / 2) → wallCollar k F u = 0 := fun u hu =>
    wallCollar_of_lt (by linarith only [hu, hk2])
  -- the mass and the integral of the collar piece
  have hTabs : ∫ u, |wallCollar k F u| ≤ B * k := by
    have hconst : IntegrableOn (fun _ : ℝ => B) (Icc (-k) 0) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)
    have h := norm_integral_le_of_norm_le (hconst.integrable_indicator measurableSet_Icc)
      (f := fun u => |wallCollar k F u|) (by
        filter_upwards [hB] with u hu
        rw [Real.norm_eq_abs, abs_abs]
        by_cases hmem : u ∈ Icc (-k) (0 : ℝ)
        · rw [indicator_of_mem hmem, wallCollar_of_ge hmem.1]
          rcases eq_or_lt_of_le hmem.2 with h0 | h0
          · rw [hF.support u h0.ge, abs_zero]
            exact hB0
          · exact hu (by linarith only [hmem.1, hk]) h0
        · rw [indicator_of_notMem hmem]
          rcases lt_or_ge u (-k) with h1 | h1
          · rw [wallCollar_of_lt h1, abs_zero]
          · have h0 : 0 < u := by
              by_contra hn
              exact hmem ⟨h1, not_lt.mp hn⟩
            rw [wallCollar_of_ge h1, hF.support u h0.le, abs_zero])
    rw [integral_indicator_const B measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith only [hk]), smul_eq_mul, Real.norm_eq_abs] at h
    have h' := (le_abs_self _).trans h
    linarith only [h']
  have hTint : ∫ u, wallCollar k F u = ∫ u in Ioo (-k) 0, F u := by
    rw [← integral_Ico_eq_integral_Ioo, ← integral_indicator measurableSet_Ico]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show wallCollar k F u = (Ico (-k) 0).indicator F u
    by_cases hmem : u ∈ Ico (-k) (0 : ℝ)
    · rw [indicator_of_mem hmem, wallCollar_of_ge hmem.1]
    · rw [indicator_of_notMem hmem]
      rcases lt_or_ge u (-k) with h1 | h1
      · exact wallCollar_of_lt h1
      · rw [wallCollar_of_ge h1]
        exact hF.support u (not_lt.mp fun h0 => hmem ⟨h1, h0⟩)
  have hI0 : 0 ≤ ∫ u, |wallCollar k F u| := integral_nonneg fun u => abs_nonneg _
  -- the prime and pole rows
  have hprime := abs_primeMixedForm_le_of_terminal hE hT hC₁0
    (hC₁.mono fun u hu => (abs_wallExterior_le F k u).trans hu) hTs
  have hpole := abs_polarMixed_le_of_terminal hE hT hTs
  have hroot : Real.sqrt (exponentialSourceMass (wallExterior k F)) *
      Real.sqrt (∫ u, Real.exp (-|u|)) ≤
      Real.sqrt (exponentialSourceMass F) * Real.sqrt (∫ u, Real.exp (-|u|)) :=
    mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (exponentialSourceMass_indicator_le hF.weighted measurableSet_Iio))
      (Real.sqrt_nonneg _)
  have hpole' : |2 * coshHalfMoment (wallExterior k F) * coshHalfMoment (wallCollar k F) -
      2 * sinhHalfMoment (wallExterior k F) * sinhHalfMoment (wallCollar k F)| ≤
      4 * Real.exp (1 / 4) * (Real.sqrt (exponentialSourceMass F) *
        Real.sqrt (∫ u, Real.exp (-|u|))) * ∫ u, |wallCollar k F u| :=
    hpole.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num) (Real.exp_pos _).le)) hI0)
  -- the Gamma row in Lévy form
  have hgm := gammaMixedForm_eq_halfLineGammaMixedJump hE hT
  have hzero : (∫ u, wallExterior k F u * wallCollar k F u) = 0 :=
    integral_eq_zero_of_ae (Eventually.of_forall fun u => wallExterior_mul_wallCollar F k u)
  have hconf : (∫ u in Iio (0 : ℝ),
      wallExterior k F u * wallCollar k F u * Real.exp (-(8 * u))) = 0 :=
    integral_eq_zero_of_ae (Eventually.of_forall fun u => by
      show wallExterior k F u * wallCollar k F u * Real.exp (-(8 * u)) = 0
      rw [wallExterior_mul_wallCollar F k u, zero_mul])
  have hJi := integrableOn_halfLineGammaMixedJump hE hT
  have hJsplit : ∫ x in Ioi (0 : ℝ), halfLineGammaMixedJump (wallExterior k F) (wallCollar k F) x =
      (∫ x in Ioc 0 k, halfLineGammaMixedJump (wallExterior k F) (wallCollar k F) x) +
        ∫ x in Ioi k, halfLineGammaMixedJump (wallExterior k F) (wallCollar k F) x := by
    rw [← Ioc_union_Ioi_eq_Ioi hk.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hJi.mono_set Ioc_subset_Ioi_self) (hJi.mono_set (Ioi_subset_Ioi hk.le))
  have hJnear := abs_setIntegral_mixedJump_wall_le hF hk (by linarith only [hk2]) hB0 hB
  have hJfar : ∫ x in Ioi k, halfLineGammaMixedJump (wallExterior k F) (wallCollar k F) x =
      -∫ u, lineConvolution (symCutoffKernel k) (wallExterior k F) u * wallCollar k F u := by
    rw [← integral_cutoffLevy_mul hk hE hT, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show cutoffLevy k (wallExterior k F) u * wallCollar k F u =
      -(lineConvolution (symCutoffKernel k) (wallExterior k F) u * wallCollar k F u)
    unfold cutoffLevy
    linear_combination 2 * (∫ x in Ioi k, archLevyDensity x) * wallExterior_mul_wallCollar F k u
  have hlc : Integrable fun u =>
      lineConvolution (symCutoffKernel k) (wallExterior k F) u * wallCollar k F u :=
    integrable_lineConvolution_symCutoffKernel_mul hk hE.meas hE.sq hT.meas hT.integrable
  have hfar : |(∫ u, lineConvolution (symCutoffKernel k) (wallExterior k F) u *
      wallCollar k F u) - wallLogMoment F k / 2 * ∫ u, wallCollar k F u| ≤
      ((∫ u, |F u|) / 4 + C) * ∫ u, |wallCollar k F u| := by
    have hsub : (∫ u, lineConvolution (symCutoffKernel k) (wallExterior k F) u *
        wallCollar k F u) - wallLogMoment F k / 2 * ∫ u, wallCollar k F u =
        ∫ u, (lineConvolution (symCutoffKernel k) (wallExterior k F) u * wallCollar k F u -
          wallLogMoment F k / 2 * wallCollar k F u) := by
      rw [integral_sub hlc (hT.integrable.const_mul _), integral_const_mul]
    have hrhs : ((∫ u, |F u|) / 4 + C) * ∫ u, |wallCollar k F u| =
        ∫ u, ((∫ u, |F u|) / 4 + C) * |wallCollar k F u| := (integral_const_mul _ _).symm
    rw [hsub, hrhs, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hT.integrable.abs.const_mul _)
      (Eventually.of_forall fun u => ?_)
    show ‖lineConvolution (symCutoffKernel k) (wallExterior k F) u * wallCollar k F u -
      wallLogMoment F k / 2 * wallCollar k F u‖ ≤ ((∫ u, |F u|) / 4 + C) * |wallCollar k F u|
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    rcases lt_or_ge u (-k) with h1 | h1
    · rw [wallCollar_of_lt h1, abs_zero, mul_zero, mul_zero]
    · rcases le_or_gt 0 u with h0 | h0
      · rw [wallCollar_of_ge h1, hF.support u h0, abs_zero, mul_zero, mul_zero]
      · have h := abs_cutExterior_sub_half_wallLogMoment_le hF.meas hF.integrable hF.sq hC0 hC
          (t := -u) (k := k) (by linarith only [h0]) (by linarith only [h1])
        rw [neg_neg] at h
        exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  -- assembly
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (∫ u, |F u|) / 4 + C + C₁ * halfLineExponentialPrimeTail 1 +
      4 * Real.exp (1 / 4) * (Real.sqrt (exponentialSourceMass F) *
        Real.sqrt (∫ u, Real.exp (-|u|))) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact add_nonneg (add_nonneg (add_nonneg
      (div_nonneg (integral_nonneg fun u => abs_nonneg _) (by norm_num)) hC0)
      (mul_nonneg hC₁0 (halfLineExponentialPrimeTail_nonneg 1)))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have hKT := mul_le_mul_of_nonneg_left hTabs hK0
  rw [← hKdef]
  unfold criticalHalfLineMixedEnergy
  rw [primeMixedForm_symm (wallCollar k F) (wallExterior k F), hgm, hzero, hconf, hJsplit, hJfar,
    ← hTint]
  rw [abs_le] at hJnear hfar hprime hpole'
  rw [hKdef] at hKT
  rw [hKdef]
  linarith only [hJnear.1, hfar.2, hprime.2, hpole'.1, hKT]

/-! ### The wall energy inequality -/

/-- **The wall energy inequality.** For a minimizer `F` at a ratio `R > 0` there is a constant
`K` such that, whenever `|F| ≤ B` almost everywhere on `[−2k, 0)`, `k ≤ 1/2`,

`a(R) (1 − e^{−8k}) ∫_{u<−k} F² e^{−8u} ≤ (L_F(k)/2) ∫_{−k}^0 F + K B k + B² k`.

The left side is the confinement energy that the terminal gap of the cut state costs; the right
side is the pairing of the cut state with the collar piece. -/
theorem halfLineEnergyMinimizer_exists_wall_energy_le {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℝ, 0 < k → k ≤ 1 / 2 → ∀ B : ℝ, 0 ≤ B →
      (∀ᵐ u : ℝ, -(2 * k) ≤ u → u < 0 → |F u| ≤ B) →
      criticalAliasCoefficient R * (1 - Real.exp (-(8 * k))) *
          (∫ u in Iio (-k), F u ^ 2 * Real.exp (-(8 * u))) ≤
        wallLogMoment F k / 2 * (∫ u in Ioo (-k) 0, F u) + K * (B * k) + B ^ 2 * k := by
  obtain ⟨C, hC0, hC⟩ := hF.exists_uniform_abs_bound hR
  obtain ⟨C₁, hC₁0, hC₁⟩ := hF.exists_exponential_barrier hR
    (show (1 / 2 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 15 / 2 by norm_num)
  refine ⟨(∫ u, |F u|) / 4 + C + C₁ * halfLineExponentialPrimeTail 1 +
      4 * Real.exp (1 / 4) * (Real.sqrt (exponentialSourceMass F) *
        Real.sqrt (∫ u, Real.exp (-|u|))), ?_, ?_⟩
  · exact add_nonneg (add_nonneg (add_nonneg
      (div_nonneg (integral_nonneg fun u => abs_nonneg _) (by norm_num)) hC0)
      (mul_nonneg hC₁0 (halfLineExponentialPrimeTail_nonneg 1)))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  intro k hk hk2 B hB0 hB
  have hE := criticalHalfLineEnergyDomain_wallExterior hF.1 hC k
  have hpair := neg_mixedEnergy_wallExterior_wallCollar_le R hF.1 hC0 hC hC₁0 hC₁ hk hk2 hB0 hB
  have hgap := criticalHalfLineFullEnergy_ge_ground_add_terminal_wall hR hE hk.le
    (fun u hu => wallExterior_of_ge hu)
  have hid : criticalHalfLineFullEnergy R (wallExterior k F) =
      criticalHalfLineGroundEnergy R * (∫ u, F u * wallExterior k F u) -
        criticalHalfLineMixedEnergy R (wallExterior k F) (wallCollar k F) :=
    halfLineEnergyMinimizer_fullEnergy_eq_sub_mixed hR hF hE
  have hFE : (∫ u, F u * wallExterior k F u) = ∫ u, wallExterior k F u ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun u => by
      show F u * wallExterior k F u = wallExterior k F u ^ 2
      rcases lt_or_ge u (-k) with h | h
      · rw [wallExterior_of_lt h]
        ring
      · rw [wallExterior_of_ge h]
        ring)
  have hW : (∫ u, wallExterior k F u ^ 2 * Real.exp (-(8 * u))) =
      ∫ u in Iio (-k), F u ^ 2 * Real.exp (-(8 * u)) := by
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show wallExterior k F u ^ 2 * Real.exp (-(8 * u)) =
      (Iio (-k)).indicator (fun u => F u ^ 2 * Real.exp (-(8 * u))) u
    by_cases hu : u ∈ Iio (-k)
    · rw [indicator_of_mem hu, wallExterior_of_lt (mem_Iio.mp hu)]
    · rw [indicator_of_notMem hu, wallExterior_of_ge (not_lt.mp hu), zero_pow two_ne_zero,
        zero_mul]
  rw [hid, hFE, hW] at hgap
  linarith only [hgap, hpair]

end GaloisForLFunctions.ExclusionOfTheCriticalState
