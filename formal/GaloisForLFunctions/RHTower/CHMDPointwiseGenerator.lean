import GaloisForLFunctions.RHTower.CHMDThetaHarmonicIdentity
import GaloisForLFunctions.RHTower.CHMDArithmeticResolvent
import GaloisForLFunctions.RHTower.CHMDCompactSourceClass

/-!
# The pointwise generator of the arithmetic jump form on compact tests

For compact `C²` profiles `v`, `w` the edge pairing of their Doob lifts is an integral of `w`
against the explicit symmetrized jump image of `v`:

`⟨edge v, edge w⟩ = ∫ w(y) Θ(y) [∫_0^∞ ω(t) J_t v(y) dt + Σ_n Λ(n) n^{−1/2} J_{log n} v(y)] dy`,

with `J_s v(y) = Θ(y+s)(v(y) − v(y+s)) + Θ(y−s)(v(y) − v(y−s))`. Every archimedean and
prime-power edge is kept. The identity comes from splitting each product of differences at its two
endpoints, translating the second endpoint, and exchanging the edge integrals by Fubini; the
exchange of the prime sum uses the quadratic decay of the theta kernel along the shifts, and the
archimedean exchange uses the first displacement moment of the Lévy density together with the
Lipschitz bound of `v`. Consequently the signed Doob pairing of two compact tests is
`∫ w · (J v / cosh(·/2) − v) dμ`: the generator of the arithmetic form acts on compact tests as an
explicit integro-difference operator.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump ThetaSourceWard

/-- The symmetrized theta-weighted jump of a profile across the displacement `s`. -/
def symJump (v : ℝ → ℝ) (s y : ℝ) : ℝ :=
  riemannKernelReal (y + s) * (v y - v (y + s)) + riemannKernelReal (y - s) * (v y - v (y - s))

/-- The archimedean jump image. -/
def genArch (v : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), archLevyDensity t * symJump v t y

/-- The prime jump image. -/
def genPrime (v : ℝ → ℝ) (y : ℝ) : ℝ := ∑' n : ℕ, vonMangoldtAtom n * symJump v (Real.log n) y

/-- The complete jump image. -/
def genTotal (v : ℝ → ℝ) (y : ℝ) : ℝ := genArch v y + genPrime v y

theorem continuous_symJump {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous (fun p : ℝ × ℝ => symJump v p.1 p.2) := by
  unfold symJump
  have h1 : Continuous fun p : ℝ × ℝ => p.2 + p.1 := continuous_snd.add continuous_fst
  have h2 : Continuous fun p : ℝ × ℝ => p.2 - p.1 := continuous_snd.sub continuous_fst
  exact ((continuous_riemannKernelReal.comp h1).mul ((hv.comp continuous_snd).sub (hv.comp h1))).add
    ((continuous_riemannKernelReal.comp h2).mul ((hv.comp continuous_snd).sub (hv.comp h2)))

theorem continuous_symJump_right {v : ℝ → ℝ} (hv : Continuous v) (s : ℝ) :
    Continuous (symJump v s) :=
  (continuous_symJump hv).comp (continuous_const.prodMk continuous_id)

theorem continuous_symJump_left {v : ℝ → ℝ} (hv : Continuous v) (y : ℝ) :
    Continuous fun t => symJump v t y :=
  (continuous_symJump hv).comp (continuous_id.prodMk continuous_const)

/-! ## Elementary bounds -/

theorem exists_theta_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, riemannKernelReal x ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  refine ⟨C, hC0, fun x => (hC x).trans ?_⟩
  have : Real.exp (-(4 * |x|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x])
  nlinarith

/-- The sup bound of the symmetrized jump. -/
theorem abs_symJump_le_sup {v : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |v x| ≤ M) (s y : ℝ) :
    |symJump v s y| ≤ 2 * M * (riemannKernelReal (y + s) + riemannKernelReal (y - s)) := by
  unfold symJump
  have h1 : |v y - v (y + s)| ≤ 2 * M := by
    calc |v y - v (y + s)| ≤ |v y| + |v (y + s)| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM _) (hM _)
      _ = 2 * M := by ring
  have h2 : |v y - v (y - s)| ≤ 2 * M := by
    calc |v y - v (y - s)| ≤ |v y| + |v (y - s)| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM _) (hM _)
      _ = 2 * M := by ring
  have hp := riemannKernelReal_pos (y + s)
  have hm := riemannKernelReal_pos (y - s)
  calc |riemannKernelReal (y + s) * (v y - v (y + s)) + riemannKernelReal (y - s) * (v y - v (y - s))|
      ≤ |riemannKernelReal (y + s) * (v y - v (y + s))| +
          |riemannKernelReal (y - s) * (v y - v (y - s))| := abs_add_le _ _
    _ = riemannKernelReal (y + s) * |v y - v (y + s)| +
          riemannKernelReal (y - s) * |v y - v (y - s)| := by
        rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hm]
    _ ≤ riemannKernelReal (y + s) * (2 * M) + riemannKernelReal (y - s) * (2 * M) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hp.le) (mul_le_mul_of_nonneg_left h2 hm.le)
    _ = 2 * M * (riemannKernelReal (y + s) + riemannKernelReal (y - s)) := by ring

/-- The Lipschitz bound of the symmetrized jump. -/
theorem abs_symJump_le_lipschitz {v : ℝ → ℝ} {L : NNReal} (hL : LipschitzWith L v)
    {C : ℝ} (hC : ∀ x, riemannKernelReal x ≤ C) (s y : ℝ) :
    |symJump v s y| ≤ 2 * C * L * |s| := by
  unfold symJump
  have hp := riemannKernelReal_pos (y + s)
  have hm := riemannKernelReal_pos (y - s)
  have h1 : |v y - v (y + s)| ≤ L * |s| := by
    have := hL.dist_le_mul y (y + s)
    rw [Real.dist_eq, Real.dist_eq] at this
    simpa only [sub_add_cancel_left, abs_neg] using this
  have h2 : |v y - v (y - s)| ≤ L * |s| := by
    have := hL.dist_le_mul y (y - s)
    rw [Real.dist_eq, Real.dist_eq] at this
    simpa only [sub_sub_cancel] using this
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  calc |riemannKernelReal (y + s) * (v y - v (y + s)) + riemannKernelReal (y - s) * (v y - v (y - s))|
      ≤ |riemannKernelReal (y + s) * (v y - v (y + s))| +
          |riemannKernelReal (y - s) * (v y - v (y - s))| := abs_add_le _ _
    _ = riemannKernelReal (y + s) * |v y - v (y + s)| +
          riemannKernelReal (y - s) * |v y - v (y - s)| := by
        rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hm]
    _ ≤ C * (L * |s|) + C * (L * |s|) :=
        add_le_add (mul_le_mul (hC _) h1 (abs_nonneg _) (hp.le.trans (hC _)))
          (mul_le_mul (hC _) h2 (abs_nonneg _) (hm.le.trans (hC _)))
    _ = 2 * C * L * |s| := by ring

/-- The first displacement moment of the archimedean Lévy density. -/
theorem archLevyDensity_mul_le (t : ℝ) (ht : 0 < t) :
    archLevyDensity t * t ≤ (1 + 2 * t) * Real.exp (-t / 2) / 2 := by
  unfold archLevyDensity
  have hpos : 0 < 1 - Real.exp (-2 * t) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -2 * t < 0)
    linarith
  have key : (1 + 2 * t) * Real.exp (-2 * t) ≤ 1 := by
    have h1 := Real.add_one_le_exp (2 * t)
    have h2 : Real.exp (-2 * t) = (Real.exp (2 * t))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [h2, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith
  have hexp : 0 < Real.exp (-t / 2) := Real.exp_pos _
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have hid : (1 + 2 * t) * Real.exp (-t / 2) / 2 * (1 - Real.exp (-2 * t)) - Real.exp (-t / 2) * t =
      Real.exp (-t / 2) / 2 * (1 - (1 + 2 * t) * Real.exp (-2 * t)) := by ring
  have hnn : 0 ≤ Real.exp (-t / 2) / 2 * (1 - (1 + 2 * t) * Real.exp (-2 * t)) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

theorem integrableOn_archMoment : IntegrableOn (fun t : ℝ => archLevyDensity t * t) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2) * t) / 2 + 4 * Real.exp (-(1 / 4) * t))
      (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).div_const 2).add
      ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 4)
  refine hb.mono' (measurable_archLevyDensity.mul measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  have h0 : 0 ≤ archLevyDensity t * t := mul_nonneg (archLevyDensity_pos ht').le ht'.le
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  refine (archLevyDensity_mul_le t ht').trans ?_
  have h1 : t ≤ 4 * Real.exp (t / 4) := by
    have := Real.add_one_le_exp (t / 4)
    linarith
  have e1 : Real.exp (-t / 2) = Real.exp (-(1 / 2) * t) := by ring_nf
  have e2 : Real.exp (-(1 / 4) * t) = Real.exp (t / 4) * Real.exp (-(1 / 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2]
  have hexp : 0 < Real.exp (-(1 / 2) * t) := Real.exp_pos _
  have := mul_le_mul_of_nonneg_right h1 hexp.le
  nlinarith

theorem integral_archMoment_nonneg : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * t :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht =>
    mul_nonneg (archLevyDensity_pos ht).le (le_of_lt ht)

/-! ## Measurability of the jump images -/

theorem measurable_genArch {v : ℝ → ℝ} (hv : Continuous v) : Measurable (genArch v) := by
  have hF : StronglyMeasurable (fun p : ℝ × ℝ => archLevyDensity p.2 * symJump v p.2 p.1) :=
    ((measurable_archLevyDensity.comp measurable_snd).mul
      ((continuous_symJump hv).measurable.comp (measurable_snd.prodMk measurable_fst))).stronglyMeasurable
  exact (hF.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

theorem measurable_genPrime {v : ℝ → ℝ} (hv : Continuous v) : Measurable (genPrime v) := by
  unfold genPrime
  exact Measurable.tsum fun n => (continuous_symJump_right hv (Real.log n)).measurable.const_mul _

theorem measurable_genTotal {v : ℝ → ℝ} (hv : Continuous v) : Measurable (genTotal v) :=
  (measurable_genArch hv).add (measurable_genPrime hv)

/-! ## Products of differences on the edge measures -/

theorem difference_polarization (v w : ℝ → ℝ) (e : ℝ × ℝ) :
    difference v e * difference w e =
      (1 / 2 : ℝ) * (difference (fun x => v x + w x) e ^ 2 - difference v e ^ 2 - difference w e ^ 2) := by
  simp only [difference]
  ring

theorem integrable_arch_mul {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    Integrable (fun e => difference v e * difference w e) archMeasure := by
  have h1 := integrable_arch_sq (v := fun x => v x + w x) (hv.add hw) (hvc.add hwc)
  have h2 := integrable_arch_sq hv hvc
  have h3 := integrable_arch_sq hw hwc
  simp_rw [difference_polarization v w]
  exact ((h1.sub h2).sub h3).const_mul _

theorem integrable_arch_weighted_mul {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    Integrable (fun e => archWeight e * (difference v e * difference w e)) archBase := by
  have h := integrable_arch_mul hv hvc hw hwc
  rwa [archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae] at h

theorem integrable_prime_mul {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (n : ℕ) :
    Integrable (fun e => difference v e * difference w e) (primeMeasure n) := by
  have h1 := integrable_prime_sq (v := fun x => v x + w x) (hv.continuous.add hw.continuous)
    (hvc.add hwc) n
  have h2 := integrable_prime_sq hv.continuous hvc n
  have h3 := integrable_prime_sq hw.continuous hwc n
  simp_rw [difference_polarization v w]
  exact ((h1.sub h2).sub h3).const_mul _

theorem integrable_allPrime_mul {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    Integrable (fun e => difference v e * difference w e) (Measure.sum primeMeasure) := by
  have h1 := integrable_all_prime_sq (v := fun x => v x + w x) (hv.continuous.add hw.continuous)
    (hvc.add hwc)
  have h2 := integrable_all_prime_sq hv.continuous hvc
  have h3 := integrable_all_prime_sq hw.continuous hwc
  simp_rw [difference_polarization v w]
  exact ((h1.sub h2).sub h3).const_mul _

theorem integral_prime_mul {v w : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w) (n : ℕ) :
    (∫ e, difference v e * difference w e ∂primeMeasure n) =
      ∫ x, primeWeight n x * ((v x - v (x + Real.log n)) * (w x - w (x + Real.log n))) := by
  have hc : Continuous (fun e => difference v e * difference w e) :=
    (continuous_difference hv).mul (continuous_difference hw)
  rw [primeMeasure, integral_map (by fun_prop) hc.aestronglyMeasurable,
    integral_weighted volume (continuous_primeWeight n).measurable
      (Eventually.of_forall (primeWeight_nonneg n))]
  rfl

/-! ## The endpoint split -/

/-- Splitting a product of differences at its two endpoints and translating the second one. -/
theorem integral_shift_product {v w : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w)
    (hwc : HasCompactSupport w) (s : ℝ) :
    (∫ x, riemannKernelReal x * riemannKernelReal (x + s) *
        ((v x - v (x + s)) * (w x - w (x + s)))) =
      ∫ y, w y * riemannKernelReal y * symJump v s y := by
  have hΘ := continuous_riemannKernelReal
  have hws : HasCompactSupport (fun x => w (x + s)) := hwc.comp_homeomorph (Homeomorph.addRight s)
  have hI1 : Integrable (fun x => riemannKernelReal x * riemannKernelReal (x + s) *
      (v x - v (x + s)) * w x) :=
    (by fun_prop : Continuous fun x => riemannKernelReal x * riemannKernelReal (x + s) *
      (v x - v (x + s)) * w x).integrable_of_hasCompactSupport hwc.mul_left
  have hI2 : Integrable (fun x => riemannKernelReal x * riemannKernelReal (x + s) *
      (v x - v (x + s)) * w (x + s)) :=
    (by fun_prop : Continuous fun x => riemannKernelReal x * riemannKernelReal (x + s) *
      (v x - v (x + s)) * w (x + s)).integrable_of_hasCompactSupport hws.mul_left
  have hsplit : (fun x => riemannKernelReal x * riemannKernelReal (x + s) *
      ((v x - v (x + s)) * (w x - w (x + s)))) =
      fun x => riemannKernelReal x * riemannKernelReal (x + s) * (v x - v (x + s)) * w x -
        riemannKernelReal x * riemannKernelReal (x + s) * (v x - v (x + s)) * w (x + s) := by
    funext x; ring
  rw [hsplit, integral_sub hI1 hI2]
  have h2 : (∫ x, riemannKernelReal x * riemannKernelReal (x + s) * (v x - v (x + s)) * w (x + s)) =
      ∫ y, riemannKernelReal (y - s) * riemannKernelReal y * (v (y - s) - v y) * w y := by
    rw [← integral_add_right_eq_self
      (fun y => riemannKernelReal (y - s) * riemannKernelReal y * (v (y - s) - v y) * w y) s]
    congr 1
    funext x
    simp only [add_sub_cancel_right]
  have hI3 : Integrable (fun y => riemannKernelReal (y - s) * riemannKernelReal y *
      (v (y - s) - v y) * w y) :=
    (by fun_prop : Continuous fun y => riemannKernelReal (y - s) * riemannKernelReal y *
      (v (y - s) - v y) * w y).integrable_of_hasCompactSupport hwc.mul_left
  rw [h2, ← integral_sub hI1 hI3]
  congr 1
  funext y
  unfold symJump
  ring

/-- The prime edge of displacement `log n`. -/
theorem integral_prime_mul_eq {v w : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w)
    (hwc : HasCompactSupport w) (n : ℕ) :
    (∫ e, difference v e * difference w e ∂primeMeasure n) =
      ∫ y, w y * riemannKernelReal y * (vonMangoldtAtom n * symJump v (Real.log n) y) := by
  rw [integral_prime_mul hv hw n]
  have hpt : (fun x => primeWeight n x * ((v x - v (x + Real.log n)) * (w x - w (x + Real.log n)))) =
      fun x => vonMangoldtAtom n * (riemannKernelReal x * riemannKernelReal (x + Real.log n) *
        ((v x - v (x + Real.log n)) * (w x - w (x + Real.log n)))) := by
    funext x
    unfold primeWeight
    ring
  rw [hpt, integral_const_mul, integral_shift_product hv hw hwc, ← integral_const_mul]
  congr 1
  funext y
  ring

/-! ## The archimedean edges -/

theorem integrable_archPair {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    Integrable (Function.uncurry fun t y =>
      archLevyDensity t * (w y * riemannKernelReal y * symJump v t y))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨L, hL⟩ := compact_source_lipschitz hv hvc
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound
  have hmeas : AEStronglyMeasurable (Function.uncurry fun t y =>
      archLevyDensity t * (w y * riemannKernelReal y * symJump v t y))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (measurable_archLevyDensity.comp measurable_fst).mul
      (((hw.measurable.comp measurable_snd).mul
        (continuous_riemannKernelReal.measurable.comp measurable_snd)).mul
        (continuous_symJump hv.continuous).measurable)
  have hbound : Integrable (fun p : ℝ × ℝ => (|archLevyDensity p.1 * p.1|) *
      ((2 * C * L) * (|w p.2| * riemannKernelReal p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Integrable.mul_prod (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume)
      (f := fun t => |archLevyDensity t * t|)
      (g := fun y => (2 * C * L) * (|w y| * riemannKernelReal y)) ?_ ?_
    · simpa only [Real.norm_eq_abs] using integrableOn_archMoment.norm
    · exact ((hw.abs.mul continuous_riemannKernelReal).integrable_of_hasCompactSupport
        hwc.abs.mul_right).const_mul _
  refine hbound.mono' hmeas (Eventually.of_forall fun p => ?_)
  change ‖archLevyDensity p.1 * (w p.2 * riemannKernelReal p.2 * symJump v p.1 p.2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  have hs := abs_symJump_le_lipschitz hL hC p.1 p.2
  have hΘ := riemannKernelReal_pos p.2
  rw [abs_of_pos hΘ]
  calc |archLevyDensity p.1| * (|w p.2| * riemannKernelReal p.2 * |symJump v p.1 p.2|)
      ≤ |archLevyDensity p.1| * (|w p.2| * riemannKernelReal p.2 * (2 * C * L * |p.1|)) := by
        gcongr
    _ = |archLevyDensity p.1| * |p.1| * (2 * C * L * (|w p.2| * riemannKernelReal p.2)) := by ring
    _ = |archLevyDensity p.1 * p.1| * (2 * C * L * (|w p.2| * riemannKernelReal p.2)) := by
        rw [abs_mul]

/-- The archimedean edges give the archimedean jump image. -/
theorem integral_arch_mul_eq {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    (∫ e, difference v e * difference w e ∂archMeasure) =
      ∫ y, w y * riemannKernelReal y * genArch v y := by
  rw [archMeasure, integral_weighted archBase measurable_archWeight archWeight_nonneg_ae, archBase,
    integral_prod _ (integrable_arch_weighted_mul hv hvc hw hwc)]
  have hinner : ∀ t : ℝ, (∫ x, archWeight (t, x) * (difference v (t, x) * difference w (t, x))) =
      archLevyDensity t * ∫ y, w y * riemannKernelReal y * symJump v t y := by
    intro t
    rw [← integral_shift_product hv.continuous hw.continuous hwc t, ← integral_const_mul]
    congr 1
    funext x
    unfold archWeight difference left right
    ring
  simp_rw [hinner, ← integral_const_mul]
  rw [integral_integral_swap (integrable_archPair hv hvc hw.continuous hwc)]
  unfold genArch
  congr 1
  funext y
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

/-! ## The complete edge pairing -/

theorem summable_primeKernelSum_shift (y : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * (riemannKernelReal (y + Real.log n) +
      riemannKernelReal (y - Real.log n)) :=
  summable_primeKernelSum y

theorem vonMangoldtAtom_le_vonMangoldt (n : ℕ) :
    vonMangoldtAtom n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  unfold vonMangoldtAtom
  split_ifs with hn
  · have h1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]
      exact_mod_cast (by omega : 1 ≤ n)
    exact div_le_self (ArithmeticFunction.vonMangoldt_nonneg (n := n)) h1
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem summable_atom_div_sq : Summable fun n : ℕ => vonMangoldtAtom n / (n : ℝ) ^ 2 := by
  refine summable_vonMangoldt_abs_div_sq.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact div_nonneg (vonMangoldtAtom_nonneg n) (sq_nonneg _)
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact vonMangoldtAtom_le_vonMangoldt n

/-- The prime jump series integrates termwise against a compact weight. -/
theorem integral_genPrime_eq_tsum {v w : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    (∫ y, w y * riemannKernelReal y * genPrime v y) =
      ∑' n : ℕ, ∫ y, w y * riemannKernelReal y * (vonMangoldtAtom n * symJump v (Real.log n) y) := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv
  have hM' : ∀ x, |v x| ≤ M := fun x => by simpa only [Real.norm_eq_abs] using hM x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  obtain ⟨R, hR0, hR⟩ := CHMDTranslation.support_interval hwc
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  have hΘc := continuous_riemannKernelReal
  have hint : ∀ n : ℕ, Integrable fun y =>
      w y * riemannKernelReal y * (vonMangoldtAtom n * symJump v (Real.log n) y) := fun n => by
    have hsc := continuous_symJump_right hv (Real.log n)
    exact (by fun_prop : Continuous fun y =>
      w y * riemannKernelReal y * (vonMangoldtAtom n * symJump v (Real.log n) y)).integrable_of_hasCompactSupport
      (hwc.mul_right.mul_right)
  have hwint : Integrable fun y => |w y| * riemannKernelReal y :=
    (hw.abs.mul continuous_riemannKernelReal).integrable_of_hasCompactSupport hwc.abs.mul_right
  set K : ℝ := (∫ y, |w y| * riemannKernelReal y) * (2 * M * (2 * (C * Real.exp (4 * R)))) with hK
  have hnorm : ∀ n : ℕ, (∫ y, ‖w y * riemannKernelReal y *
      (vonMangoldtAtom n * symJump v (Real.log n) y)‖) ≤ K * (vonMangoldtAtom n / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [vonMangoldtAtom]
    have hpt : ∀ y, ‖w y * riemannKernelReal y * (vonMangoldtAtom n * symJump v (Real.log n) y)‖ ≤
        (|w y| * riemannKernelReal y) * (2 * M * (2 * (C * Real.exp (4 * R))) *
          (vonMangoldtAtom n / (n : ℝ) ^ 2)) := by
      intro y
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (riemannKernelReal_pos y),
        abs_of_nonneg (vonMangoldtAtom_nonneg n)]
      by_cases hy : w y = 0
      · simp [hy]
      · have hyR := hR y hy
        have hs := abs_symJump_le_sup hM' (Real.log n) y
        have hsh := riemannKernelReal_shift_le hC hC0 (abs_le.mpr hyR) hn
        have hΘ := riemannKernelReal_pos y
        have ha : 0 ≤ vonMangoldtAtom n := vonMangoldtAtom_nonneg n
        have hw0 : 0 ≤ |w y| := abs_nonneg _
        calc |w y| * riemannKernelReal y * (vonMangoldtAtom n * |symJump v (Real.log n) y|)
            ≤ |w y| * riemannKernelReal y * (vonMangoldtAtom n *
                (2 * M * (riemannKernelReal (y + Real.log n) + riemannKernelReal (y - Real.log n)))) := by
              gcongr
          _ ≤ |w y| * riemannKernelReal y * (vonMangoldtAtom n *
                (2 * M * (2 * (C * Real.exp (4 * R)) * (1 / (n : ℝ) ^ 2)))) := by
              gcongr
          _ = (|w y| * riemannKernelReal y) * (2 * M * (2 * (C * Real.exp (4 * R))) *
                (vonMangoldtAtom n / (n : ℝ) ^ 2)) := by ring
    calc (∫ y, ‖w y * riemannKernelReal y * (vonMangoldtAtom n * symJump v (Real.log n) y)‖)
        ≤ ∫ y, (|w y| * riemannKernelReal y) * (2 * M * (2 * (C * Real.exp (4 * R))) *
            (vonMangoldtAtom n / (n : ℝ) ^ 2)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
            (hwint.mul_const _) (Eventually.of_forall hpt)
      _ = K * (vonMangoldtAtom n / (n : ℝ) ^ 2) := by
          rw [integral_mul_const, hK]
          ring
  have hsum : Summable fun n : ℕ => ∫ y, ‖w y * riemannKernelReal y *
      (vonMangoldtAtom n * symJump v (Real.log n) y)‖ :=
    (summable_atom_div_sq.mul_left K).of_nonneg_of_le
      (fun n => integral_nonneg fun y => norm_nonneg _) hnorm
  have h := integral_tsum_of_summable_integral_norm hint hsum
  unfold genPrime
  simp_rw [← tsum_mul_left]
  exact h.symm

/-- Uniform bound of the archimedean jump image. -/
theorem exists_genArch_bound {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |genArch v y| ≤ K := by
  obtain ⟨L, hL⟩ := compact_source_lipschitz hv hvc
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound
  refine ⟨2 * C * L * ∫ t in Ioi (0 : ℝ), archLevyDensity t * t,
    mul_nonneg (by positivity) integral_archMoment_nonneg, fun y => ?_⟩
  unfold genArch
  have hn : ‖∫ t in Ioi (0 : ℝ), archLevyDensity t * symJump v t y‖ ≤
      ∫ t in Ioi (0 : ℝ), ‖archLevyDensity t * symJump v t y‖ :=
    norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ))) _
  rw [Real.norm_eq_abs] at hn
  refine hn.trans ?_
  rw [← integral_const_mul]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖archLevyDensity t * symJump v t y‖ ≤
      2 * C * L * (archLevyDensity t * t) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht')]
    have hs := abs_symJump_le_lipschitz hL hC t y
    rw [abs_of_pos ht'] at hs
    calc archLevyDensity t * |symJump v t y| ≤ archLevyDensity t * (2 * C * L * t) :=
          mul_le_mul_of_nonneg_left hs (archLevyDensity_pos ht').le
      _ = 2 * C * L * (archLevyDensity t * t) := by ring
  refine setIntegral_mono_on ?_ (integrableOn_archMoment.const_mul _) measurableSet_Ioi hpt
  refine (integrableOn_archMoment.const_mul (2 * C * L)).mono' ?_ ?_
  · exact (measurable_archLevyDensity.mul
      (continuous_symJump_left hv.continuous y).measurable).norm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_norm]
    exact hpt t ht

/-- The prime jump image is dominated by the symmetric prime shift sum of the kernel. -/
theorem abs_genPrime_le {v : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |v x| ≤ M) (y : ℝ) :
    |genPrime v y| ≤ 2 * M * primeKernelSum y := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  unfold genPrime primeKernelSum
  rw [← tsum_mul_left]
  have hterm : ∀ n : ℕ, ‖vonMangoldtAtom n * symJump v (Real.log n) y‖ ≤
      2 * M * (vonMangoldtAtom n * (riemannKernelReal (y + Real.log n) +
        riemannKernelReal (y - Real.log n))) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
    have := abs_symJump_le_sup hM (Real.log n) y
    calc vonMangoldtAtom n * |symJump v (Real.log n) y|
        ≤ vonMangoldtAtom n * (2 * M * (riemannKernelReal (y + Real.log n) +
            riemannKernelReal (y - Real.log n))) :=
          mul_le_mul_of_nonneg_left this (vonMangoldtAtom_nonneg n)
      _ = _ := by ring
  have hsum : Summable fun n : ℕ => ‖vonMangoldtAtom n * symJump v (Real.log n) y‖ :=
    ((summable_primeKernelSum y).mul_left (2 * M)).of_nonneg_of_le
      (fun n => norm_nonneg _) hterm
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  exact hsum.tsum_le_tsum hterm ((summable_primeKernelSum y).mul_left (2 * M))

/-- The symmetric prime shift sum is the polar rate up to a uniform constant. -/
theorem exists_primeKernelSum_bound : ∃ K : ℝ, ∀ y, primeKernelSum y ≤ Real.cosh (y / 2) + K := by
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound
  refine ⟨2 * |archConstantReal| * C + 2 * ∫ u in Ioi (0 : ℝ), gammaSourceBound u, fun y => ?_⟩
  rw [theta_harmonic_identity]
  have h1 : -(2 * archConstantReal * riemannKernelReal y) ≤ 2 * |archConstantReal| * C := by
    have := riemannKernelReal_pos y
    have h := neg_abs_le archConstantReal
    nlinarith [hC y, abs_nonneg archConstantReal]
  have h2 : (∫ u in Ioi (0 : ℝ), symArchTerm y u) ≤ 2 * ∫ u in Ioi (0 : ℝ), gammaSourceBound u := by
    have hn : ‖∫ u in Ioi (0 : ℝ), symArchTerm y u‖ ≤ ∫ u in Ioi (0 : ℝ), ‖symArchTerm y u‖ :=
      norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ))) _
    rw [Real.norm_eq_abs] at hn
    refine (le_abs_self _).trans (hn.trans ?_)
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_symArchTerm y).norm
      (gammaSourceBound_integrable.const_mul 2) measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have he : symArchTerm y u = gammaSourceTerm y u + gammaSourceTerm (-y) u := by
      simp only [gammaSourceTerm_eq, symArchTerm, WeilExcess.riemannKernelReal_neg]
      rw [show -y + u = -(y - u) by ring, WeilExcess.riemannKernelReal_neg]
      ring
    rw [Real.norm_eq_abs, he]
    calc |gammaSourceTerm y u + gammaSourceTerm (-y) u|
        ≤ |gammaSourceTerm y u| + |gammaSourceTerm (-y) u| := abs_add_le _ _
      _ ≤ gammaSourceBound u + gammaSourceBound u :=
          add_le_add (abs_gammaSourceTerm_le_bound y hu') (abs_gammaSourceTerm_le_bound (-y) hu')
      _ = 2 * gammaSourceBound u := by ring
  linarith

theorem integrable_weight_genArch {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    Integrable fun y => w y * riemannKernelReal y * genArch v y := by
  obtain ⟨K, hK0, hK⟩ := exists_genArch_bound hv hvc
  have hb : Integrable fun y => |w y| * riemannKernelReal y * K :=
    ((hw.abs.mul continuous_riemannKernelReal).mul continuous_const).integrable_of_hasCompactSupport
      (hwc.abs.mul_right.mul_right)
  refine hb.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((hw.measurable.mul continuous_riemannKernelReal.measurable).mul
      (measurable_genArch hv.continuous)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (riemannKernelReal_pos y)]
    exact mul_le_mul_of_nonneg_left (hK y)
      (mul_nonneg (abs_nonneg _) (riemannKernelReal_pos y).le)

theorem integrable_weight_genPrime {v w : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    Integrable fun y => w y * riemannKernelReal y * genPrime v y := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv
  have hM' : ∀ x, |v x| ≤ M := fun x => by simpa only [Real.norm_eq_abs] using hM x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  obtain ⟨K, hK⟩ := exists_primeKernelSum_bound
  have hb : Integrable fun y => |w y| * riemannKernelReal y * (2 * M * (Real.cosh (y / 2) + K)) :=
    ((hw.abs.mul continuous_riemannKernelReal).mul (continuous_const.mul
      ((Real.continuous_cosh.comp (continuous_id.div_const 2)).add
        continuous_const))).integrable_of_hasCompactSupport (hwc.abs.mul_right.mul_right)
  refine hb.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((hw.measurable.mul continuous_riemannKernelReal.measurable).mul
      (measurable_genPrime hv)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (riemannKernelReal_pos y)]
    refine mul_le_mul_of_nonneg_left ((abs_genPrime_le hM' y).trans ?_)
      (mul_nonneg (abs_nonneg _) (riemannKernelReal_pos y).le)
    exact mul_le_mul_of_nonneg_left (hK y) (by positivity)

/-- **The edge pairing of two compact tests is the integral of one against the complete jump image
of the other.** -/
theorem inner_edge_compactLift {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    ⟪(compactLift v hv hvc).val.snd, (compactLift w hw hwc).val.snd⟫_ℝ =
      ∫ y, w y * riemannKernelReal y * genTotal v y := by
  have hae : ⟪(compactLift v hv hvc).val.snd, (compactLift w hw hwc).val.snd⟫_ℝ =
      ∫ e, difference v e * difference w e ∂edgeMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(compact_memLp_difference hv hvc).coeFn_toLp,
      (compact_memLp_difference hw hwc).coeFn_toLp] with e h1 h2
    change inner ℝ ((compact_memLp_difference hv hvc).toLp (difference v) e)
      ((compact_memLp_difference hw hwc).toLp (difference w) e) = _
    rw [h1, h2]
    simp [mul_comm]
  rw [hae, edgeMeasure, integral_add_measure (integrable_arch_mul hv hvc hw hwc)
    (integrable_allPrime_mul hv hvc hw hwc), integral_arch_mul_eq hv hvc hw hwc,
    integral_sum_measure (integrable_allPrime_mul hv hvc hw hwc)]
  simp_rw [integral_prime_mul_eq hv.continuous hw.continuous hwc]
  rw [← integral_genPrime_eq_tsum hv.continuous hvc hw.continuous hwc]
  rw [← integral_add (integrable_weight_genArch hv hvc hw.continuous hwc)
    (integrable_weight_genPrime hv.continuous hvc hw.continuous hwc)]
  unfold genTotal
  congr 1
  funext y
  ring

end RHTower.CHMDPolar
