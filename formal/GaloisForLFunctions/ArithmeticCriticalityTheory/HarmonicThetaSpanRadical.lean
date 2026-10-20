import GaloisForLFunctions.ArithmeticCriticalityTheory.TranslateGroundStateLorentzLaw

/-!
# The harmonic theta span is the radical of the Markov form

A gauge `ω` is **harmonic** if it solves the two-sided arithmetic Schrödinger equation exactly,
`𝓛_D ω = Φ cosh(x/2) ω`. On the theta span the source of `Σ_j α_j τ_{b_j}` is
`−Φ(x)(A cosh(x/2) − B sinh(x/2))`, so the harmonic elements are exactly those with `A = B = 0`
(for the odd superpositions `Σ c_j ω_{a_j}`: `σ = 0`). They form an infinite-dimensional space of
solutions whose test coordinates decay like `e^{−24|x|}`, and none of them is positive on the half
line (a nonnegative superposition has `σ > 0`).

**Theorem** (`abs_markovEnergy_add_harmonicPlateau_sub_le`). For a harmonic gauge `ω` with
`|Φω| ≤ C e^{−24|·|}` and every test `v ∈ C²_c(ℝ)` supported in `[−R, R]`,

    | markovEnergy(Φ(v + ω u_L)) − markovEnergy(Φ v) | ≤ K e^{−8L}       for L ≥ R.

So the Markov form, on every test, does not see the harmonic theta span: it descends to the
quotient by it. Both the polarisation and the pairing are computed with the generator calculus:
`markovEnergy(Φ(a + b)) = markovEnergy(Φa) + markovEnergy(Φb) + 2 ∫ b (𝓛_D a − ρ a)`
(`markovEnergy_phiDoob_add`, by symmetry of the weak form `∫ b 𝓛_D a = ∫ a 𝓛_D b`), and
`𝓛_D(ω u_L) − ρ ω u_L = Φ · Comm_L` is localised beyond the plateau.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Bilinear summation by parts -/

/-- `∫ Φ(x)Φ(x+t)(v(x) − v(x+t))(z(x) − z(x+t)) dx = ∫ v(x) 𝓛_D^t z(x) dx`. -/
theorem integral_bilinearShiftJump_eq_integral_mul_twoSidedShiftGenerator {v z : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (hz : Continuous z) (t : ℝ) :
    (∫ x, riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) * (z x - z (x + t))) =
      ∫ x, v x * twoSidedShiftGenerator z t x := by
  have hΦ := continuous_riemannKernelReal
  set f : ℝ → ℝ := fun x =>
    riemannKernelReal x * riemannKernelReal (x + t) * v x * (z x - z (x + t)) with hf_def
  set g : ℝ → ℝ := fun y =>
    riemannKernelReal (y - t) * riemannKernelReal y * v y * (z y - z (y - t)) with hg_def
  have hf : Integrable f := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hΦ.mul (hΦ.comp (continuous_id.add continuous_const))).mul hv).mul
        (hz.sub (hz.comp (continuous_id.add continuous_const)))
    · exact hvc.mul_left.mul_right
  have hg : Integrable g := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (((hΦ.comp (continuous_id.sub continuous_const)).mul hΦ).mul hv).mul
        (hz.sub (hz.comp (continuous_id.sub continuous_const)))
    · exact hvc.mul_left.mul_right
  have hgt : Integrable fun x => g (x + t) := hg.comp_add_right t
  have h1 : (∫ x, riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) *
      (z x - z (x + t))) = ∫ x, (f x + g (x + t)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hf_def, hg_def, add_sub_cancel_right]
    ring
  have h2 : (∫ x, v x * twoSidedShiftGenerator z t x) = ∫ x, (f x + g x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [twoSidedShiftGenerator, hf_def, hg_def]
    ring
  rw [h1, h2, integral_add hf hgt, integral_add hf hg, integral_add_right_eq_self g t]

/-! ### Mixed integrability -/

theorem integrable_archLevy_mul_mul_twoSidedShiftGenerator {v z : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    Integrable (Function.uncurry fun t x => archLevyDensity t * (v x * twoSidedShiftGenerator z t x))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_lipschitz_bound_of_compactSupport (hz.of_le (by norm_num)) hzc
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (archLevyDensity p.1 * p.1) * (2 * riemannKernelReal 0 ^ 2 * Λ * |v p.2|))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    integrableOn_archLevyDensity_mul_id.mul_prod
      ((hv.integrable_of_hasCompactSupport hvc).abs.const_mul _)
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_archLevyDensity.comp measurable_fst).mul
      ((hv.comp continuous_snd).mul
        (continuous_twoSidedShiftGenerator_uncurry hz.continuous)).measurable).aestronglyMeasurable
  · rw [Measure.restrict_prod_eq_prod_univ]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
    have ht : 0 < p.1 := hp.1
    have hb := abs_twoSidedShiftGenerator_le_lipschitz hΛ ht.le p.2
    show ‖archLevyDensity p.1 * (v p.2 * twoSidedShiftGenerator z p.1 p.2)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht), abs_mul]
    have hA := archLevyDensity_pos ht
    have hv0 := abs_nonneg (v p.2)
    nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg hA.le hv0)]

/-- The mixed archimedean pairing is the shift integral of the bilinear jump. -/
theorem integral_mul_archTwoSidedGenerator_eq {v z : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    (∫ x, v x * archTwoSidedGenerator z x) =
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, riemannKernelReal x *
        riemannKernelReal (x + t) * (v x - v (x + t)) * (z x - z (x + t)) := by
  have hint := integrable_archLevy_mul_mul_twoSidedShiftGenerator hv hvc hz hzc
  unfold archTwoSidedGenerator
  have h1 : (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, riemannKernelReal x *
      riemannKernelReal (x + t) * (v x - v (x + t)) * (z x - z (x + t))) =
      ∫ t in Ioi (0 : ℝ), ∫ x : ℝ, archLevyDensity t * (v x * twoSidedShiftGenerator z t x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [integral_bilinearShiftJump_eq_integral_mul_twoSidedShiftGenerator hv hvc hz.continuous,
      integral_const_mul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

theorem integrable_mul_archTwoSidedGenerator_of {v z : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    Integrable fun x => v x * archTwoSidedGenerator z x := by
  have h := (integrable_archLevy_mul_mul_twoSidedShiftGenerator hv hvc hz hzc).integral_prod_right
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Function.uncurry_apply_pair, archTwoSidedGenerator]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- On the support radius `R` of `v` the mixed prime atoms are dominated by a summable weight. -/
theorem abs_atom_mul_mul_twoSidedShiftGenerator_le {v z : ℝ → ℝ} {Z R : ℝ}
    (hZ : ∀ x, |z x| ≤ Z) (hsupp : ∀ x, R < |x| → v x = 0) (n : ℕ) (x : ℝ) :
    |vonMangoldtAtom n * (v x * twoSidedShiftGenerator z (Real.log n) x)| ≤
      (4 * Z * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal R)) *
        (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * |v x| := by
  have hΛ := vonMangoldtAtom_nonneg n
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ x)
  by_cases hx : |x| ≤ R
  · have hb := abs_twoSidedShiftGenerator_le_kernel hZ (Real.log n) x
    have hk := riemannKernelReal_add_add_sub_le hx n
    have hc : 0 ≤ 2 * Z * riemannKernelReal 0 := by
      have := riemannKernelReal_pos 0
      positivity
    have hG : |twoSidedShiftGenerator z (Real.log n) x| ≤
        2 * Z * riemannKernelReal 0 *
          (2 * (riemannKernelReal 0 / riemannKernelReal R) * riemannKernelReal (R - Real.log n)) :=
      hb.trans (mul_le_mul_of_nonneg_left hk hc)
    rw [abs_mul, abs_of_nonneg hΛ, abs_mul]
    calc vonMangoldtAtom n * (|v x| * |twoSidedShiftGenerator z (Real.log n) x|)
        ≤ vonMangoldtAtom n * (|v x| * (2 * Z * riemannKernelReal 0 *
          (2 * (riemannKernelReal 0 / riemannKernelReal R) * riemannKernelReal (R - Real.log n)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG (abs_nonneg _)) hΛ
      _ = _ := by ring
  · rw [hsupp x (not_le.mp hx)]
    simp

/-- The mixed prime pairing is the prime sum of the bilinear jumps. -/
theorem integral_mul_primeTwoSidedGenerator_eq {v z : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    (∫ x, v x * primeTwoSidedGenerator z x) =
      ∑' n : ℕ, vonMangoldtAtom n * ∫ x, riemannKernelReal x * riemannKernelReal (x + Real.log n) *
        (v x - v (x + Real.log n)) * (z x - z (x + Real.log n)) := by
  obtain ⟨Z, hZ⟩ := hzc.exists_bound_of_continuous hz.continuous
  have hZ' : ∀ x, |z x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hvc
  set F : ℕ → ℝ → ℝ := fun n x => vonMangoldtAtom n * (v x * twoSidedShiftGenerator z (Real.log n) x)
    with hF_def
  have hvi : Integrable fun x => |v x| := (hv.integrable_of_hasCompactSupport hvc).abs
  have hFint : ∀ n, Integrable (F n) := fun n => by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_const.mul (hv.mul (continuous_twoSidedShiftGenerator hz.continuous _))
    · exact (hvc.mul_right).mul_left
  set K := 4 * Z * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal R)
  have hsum : Summable fun n => ∫ x, ‖F n x‖ := by
    have hmaj : Summable fun n : ℕ =>
        K * (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * ∫ x, |v x| :=
      ((summable_atom_mul_kernel_sub R).mul_left K).mul_right _
    refine hmaj.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) fun n => ?_
    rw [← integral_const_mul]
    refine integral_mono (hFint n).norm (hvi.const_mul _) fun x => ?_
    simp only [Real.norm_eq_abs]
    exact abs_atom_mul_mul_twoSidedShiftGenerator_le hZ' hsupp n x
  have h1 : (∑' n : ℕ, vonMangoldtAtom n * ∫ x, riemannKernelReal x *
      riemannKernelReal (x + Real.log n) * (v x - v (x + Real.log n)) * (z x - z (x + Real.log n))) =
      ∑' n : ℕ, ∫ x, F n x := by
    refine tsum_congr fun n => ?_
    rw [integral_bilinearShiftJump_eq_integral_mul_twoSidedShiftGenerator hv hvc hz.continuous,
      ← integral_const_mul]
  rw [h1, integral_tsum_of_summable_integral_norm hFint hsum]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF_def, primeTwoSidedGenerator]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem integrable_mul_primeTwoSidedGenerator_of {v z : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    Integrable fun x => v x * primeTwoSidedGenerator z x := by
  obtain ⟨Z, hZ⟩ := hzc.exists_bound_of_continuous hz.continuous
  have hZ' : ∀ x, |z x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hvc
  set K := 4 * Z * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal R)
  set S := ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (R - Real.log n)
  have hvi : Integrable fun x => |v x| := (hv.integrable_of_hasCompactSupport hvc).abs
  have hmeas : AEStronglyMeasurable (fun x => v x * primeTwoSidedGenerator z x) volume := by
    refine aestronglyMeasurable_of_tendsto_ae (f := fun N x => v x *
      ∑ n ∈ Finset.range N, vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)
      atTop (fun N => ?_) (Eventually.of_forall fun x => ?_)
    · exact (hv.mul (continuous_finsetSum _ fun n _ =>
        continuous_const.mul (continuous_twoSidedShiftGenerator hz.continuous _))).aestronglyMeasurable
    · exact ((summable_atom_twoSidedShiftGenerator hZ' x).hasSum.tendsto_sum_nat).const_mul _
  refine (hvi.const_mul (K * S)).mono' hmeas (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, primeTwoSidedGenerator, ← tsum_mul_left]
  have hterm := abs_atom_mul_mul_twoSidedShiftGenerator_le hZ' hsupp
  have hB : Summable fun n : ℕ =>
      K * (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * |v x| :=
    ((summable_atom_mul_kernel_sub R).mul_left K).mul_right _
  have hrw : ∀ n : ℕ, v x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x) =
      vonMangoldtAtom n * (v x * twoSidedShiftGenerator z (Real.log n) x) := fun n => by ring
  have hnorm : Summable fun n : ℕ =>
      ‖v x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)‖ :=
    hB.of_nonneg_of_le (fun n => norm_nonneg _) fun n => by
      rw [Real.norm_eq_abs, hrw]
      exact hterm n x
  calc |∑' n : ℕ, v x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)|
      ≤ ∑' n : ℕ, ‖v x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, K * (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * |v x| :=
        Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs, hrw]; exact hterm n x) hnorm hB
    _ = K * S * |v x| := by rw [tsum_mul_right, tsum_mul_left]

/-! ### Symmetry and polarisation -/

/-- **Symmetry of the weak form.** `∫ v 𝓛_D z = ∫ z 𝓛_D v` for `v, z ∈ C²_c(ℝ)`. -/
theorem integral_mul_twoSidedGenerator_comm {v z : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    (∫ x, v x * twoSidedGenerator z x) = ∫ x, z x * twoSidedGenerator v x := by
  have hsplit : ∀ {a b : ℝ → ℝ}, ContDiff ℝ 2 a → HasCompactSupport a → ContDiff ℝ 2 b →
      HasCompactSupport b → (∫ x, a x * twoSidedGenerator b x) =
        (∫ x, a x * archTwoSidedGenerator b x) + ∫ x, a x * primeTwoSidedGenerator b x := by
    intro a b ha hac hb hbc
    rw [← integral_add (integrable_mul_archTwoSidedGenerator_of ha.continuous hac hb hbc)
      (integrable_mul_primeTwoSidedGenerator_of ha.continuous hac hb hbc)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [twoSidedGenerator_eq_arch_add_prime]
    ring
  rw [hsplit hv hvc hz hzc, hsplit hz hzc hv hvc,
    integral_mul_archTwoSidedGenerator_eq hv.continuous hvc hz hzc,
    integral_mul_archTwoSidedGenerator_eq hz.continuous hzc hv hvc,
    integral_mul_primeTwoSidedGenerator_eq hv.continuous hvc hz hzc,
    integral_mul_primeTwoSidedGenerator_eq hz.continuous hzc hv hvc]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  · refine tsum_congr fun n => ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring

theorem twoSidedShiftGenerator_add (a b : ℝ → ℝ) (t x : ℝ) :
    twoSidedShiftGenerator (fun y => a y + b y) t x =
      twoSidedShiftGenerator a t x + twoSidedShiftGenerator b t x := by
  unfold twoSidedShiftGenerator
  ring

theorem integrableOn_archLevy_twoSidedShiftGenerator_of_contDiff {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (hzc : HasCompactSupport z) (x : ℝ) :
    IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator z t x) (Ioi 0) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_lipschitz_bound_of_compactSupport (hz.of_le (by norm_num)) hzc
  refine (integrableOn_archLevyDensity_mul_id.const_mul (2 * riemannKernelReal 0 ^ 2 * Λ)).mono'
    (measurable_archLevyDensity.mul (continuous_twoSidedShiftGenerator_uncurry hz.continuous |>.comp
      (continuous_id.prodMk continuous_const)).measurable |>.aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht0)]
  have hb := abs_twoSidedShiftGenerator_le_lipschitz hΛ ht0.le x
  nlinarith [mul_le_mul_of_nonneg_left hb (archLevyDensity_pos ht0).le]

/-- The generator is additive on `C²_c(ℝ)`. -/
theorem twoSidedGenerator_add {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) (x : ℝ) :
    twoSidedGenerator (fun y => a y + b y) x = twoSidedGenerator a x + twoSidedGenerator b x := by
  obtain ⟨Za, hZa⟩ := hac.exists_bound_of_continuous ha.continuous
  obtain ⟨Zb, hZb⟩ := hbc.exists_bound_of_continuous hb.continuous
  have hPa := summable_atom_twoSidedShiftGenerator (z := a) (Z := Za)
    (fun y => by simpa [Real.norm_eq_abs] using hZa y) x
  have hPb := summable_atom_twoSidedShiftGenerator (z := b) (Z := Zb)
    (fun y => by simpa [Real.norm_eq_abs] using hZb y) x
  unfold twoSidedGenerator
  simp_rw [twoSidedShiftGenerator_add, mul_add]
  rw [integral_add (integrableOn_archLevy_twoSidedShiftGenerator_of_contDiff ha hac x)
    (integrableOn_archLevy_twoSidedShiftGenerator_of_contDiff hb hbc x), hPa.tsum_add hPb]
  ring

/-- **Polarisation of the Markov energy through the generator.** For `a, b ∈ C²_c(ℝ)`,
`markovEnergy(Φ(a + b)) = markovEnergy(Φa) + markovEnergy(Φb) + 2 ∫ b (𝓛_D a − ρ a)`. -/
theorem markovEnergy_phiDoob_add {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) :
    markovEnergy (fun x => (phiDoobTest (fun y => a y + b y) x : ℂ)) =
      markovEnergy (fun x => (phiDoobTest a x : ℂ)) + markovEnergy (fun x => (phiDoobTest b x : ℂ)) +
        2 * ∫ x, b x * (twoSidedGenerator a x - riemannKernelReal x * Real.cosh (x / 2) * a x) := by
  have hab : ContDiff ℝ 2 fun y => a y + b y := ha.add hb
  have habc : HasCompactSupport fun y => a y + b y := hac.add hbc
  rw [markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential hab habc,
    markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential ha hac,
    markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential hb hbc]
  have hρ : ∀ {p q : ℝ → ℝ}, Continuous p → HasCompactSupport p → Continuous q →
      Integrable fun x => p x * (riemannKernelReal x * Real.cosh (x / 2) * q x) := by
    intro p q hp hpc hq
    refine Continuous.integrable_of_hasCompactSupport ?_ hpc.mul_right
    exact hp.mul ((continuous_riemannKernelReal.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul hq)
  have hI : ∀ {p q : ℝ → ℝ}, ContDiff ℝ 2 p → HasCompactSupport p → ContDiff ℝ 2 q →
      HasCompactSupport q → Integrable fun x => p x * (twoSidedGenerator q x -
        riemannKernelReal x * Real.cosh (x / 2) * q x) := by
    intro p q hp hpc hq hqc
    refine (((integrable_mul_archTwoSidedGenerator_of hp.continuous hpc hq hqc).add
      (integrable_mul_primeTwoSidedGenerator_of hp.continuous hpc hq hqc)).sub
        (hρ hp.continuous hpc hq.continuous)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, twoSidedGenerator_eq_arch_add_prime]
    ring
  have hsym : (∫ x, a x * (twoSidedGenerator b x - riemannKernelReal x * Real.cosh (x / 2) * b x)) =
      ∫ x, b x * (twoSidedGenerator a x - riemannKernelReal x * Real.cosh (x / 2) * a x) := by
    have e1 : (∫ x, a x * (twoSidedGenerator b x - riemannKernelReal x * Real.cosh (x / 2) * b x)) =
        (∫ x, a x * twoSidedGenerator b x) -
          ∫ x, a x * (riemannKernelReal x * Real.cosh (x / 2) * b x) := by
      rw [← integral_sub ((integrable_mul_archTwoSidedGenerator_of ha.continuous hac hb hbc).add
        (integrable_mul_primeTwoSidedGenerator_of ha.continuous hac hb hbc) |>.congr
          (Eventually.of_forall fun x => by
            simp only [Pi.add_apply, twoSidedGenerator_eq_arch_add_prime]; ring))
        (hρ ha.continuous hac hb.continuous)]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    have e2 : (∫ x, b x * (twoSidedGenerator a x - riemannKernelReal x * Real.cosh (x / 2) * a x)) =
        (∫ x, b x * twoSidedGenerator a x) -
          ∫ x, b x * (riemannKernelReal x * Real.cosh (x / 2) * a x) := by
      rw [← integral_sub ((integrable_mul_archTwoSidedGenerator_of hb.continuous hbc ha hac).add
        (integrable_mul_primeTwoSidedGenerator_of hb.continuous hbc ha hac) |>.congr
          (Eventually.of_forall fun x => by
            simp only [Pi.add_apply, twoSidedGenerator_eq_arch_add_prime]; ring))
        (hρ hb.continuous hbc ha.continuous)]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [e1, e2, integral_mul_twoSidedGenerator_comm ha hac hb hbc]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hpt : (fun x => (a x + b x) * (twoSidedGenerator (fun y => a y + b y) x -
      riemannKernelReal x * Real.cosh (x / 2) * (a x + b x))) =
      fun x => ((a x * (twoSidedGenerator a x - riemannKernelReal x * Real.cosh (x / 2) * a x) +
        b x * (twoSidedGenerator b x - riemannKernelReal x * Real.cosh (x / 2) * b x)) +
        a x * (twoSidedGenerator b x - riemannKernelReal x * Real.cosh (x / 2) * b x)) +
        b x * (twoSidedGenerator a x - riemannKernelReal x * Real.cosh (x / 2) * a x) := by
    funext x
    rw [twoSidedGenerator_add ha hac hb hbc]
    ring
  set Gaa := fun x => a x * (twoSidedGenerator a x - riemannKernelReal x * Real.cosh (x / 2) * a x)
  set Gbb := fun x => b x * (twoSidedGenerator b x - riemannKernelReal x * Real.cosh (x / 2) * b x)
  set Gab := fun x => a x * (twoSidedGenerator b x - riemannKernelReal x * Real.cosh (x / 2) * b x)
  set Gba := fun x => b x * (twoSidedGenerator a x - riemannKernelReal x * Real.cosh (x / 2) * a x)
  have i1 : Integrable Gaa := hI ha hac ha hac
  have i2 : Integrable Gbb := hI hb hbc hb hbc
  have i3 : Integrable Gab := hI ha hac hb hbc
  have i4 : Integrable Gba := hI hb hbc ha hac
  have i12 : Integrable fun x => Gaa x + Gbb x := i1.add i2
  have i123 : Integrable fun x => Gaa x + Gbb x + Gab x := i12.add i3
  rw [hpt, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, hsym]
  ring

/-! ### The pairing of a plateau-truncated gauge with a fixed test -/

/-- One-sided localisation: for `|x| ≤ L` the plateau varies only where `y` is beyond `L`. -/
theorem abs_mul_abs_smoothPlateau_sub_le_of_abs_le {M : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|))) {L x : ℝ} (hxL : |x| ≤ L) (y : ℝ) {D : ℝ}
    (hD : |smoothPlateau L x - smoothPlateau L y| ≤ D) :
    |M y| * |smoothPlateau L x - smoothPlateau L y| ≤
      C * Real.exp (-(8 * L)) * Real.exp (-(16 * |y|)) * D := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  by_cases hyL : |y| ≤ L
  · rw [smoothPlateau_eq_one hxL, smoothPlateau_eq_one hyL, sub_self, abs_zero, mul_zero]
    positivity
  · have hy := exp_neg_mul_abs_le_of_lt (not_le.mp hyL)
    have h2 : |M y| ≤ C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |y|))) :=
      (hM y).trans (mul_le_mul_of_nonneg_left hy hC0)
    calc |M y| * |smoothPlateau L x - smoothPlateau L y|
        ≤ C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |y|))) * D :=
          mul_le_mul h2 hD (abs_nonneg _) (by positivity)
      _ = _ := by ring

/-- Inside the plateau the commutator is `O(e^{−8L})`:
`|Comm_L(x)| ≤ C e^{−8L} (2Λ A₁ + 2 e^{8|x|} P₈)` for `|x| ≤ L`. -/
theorem abs_plateauCommutator_le_of_abs_le {M : ℝ → ℝ} {C Λ : ℝ} (hC0 : 0 ≤ C) (hΛ0 : 0 ≤ Λ)
    (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|)))
    (hΛ : ∀ L x y, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x|) {L x : ℝ}
    (hxL : |x| ≤ L) :
    |plateauCommutator M (smoothPlateau L) x| ≤
      C * Real.exp (-(8 * L)) * (2 * Λ * archFirstMoment +
        2 * Real.exp (8 * |x|) * primeEighthMoment) := by
  set E := C * Real.exp (-(8 * L)) with hE
  have hE0 : 0 ≤ E := by positivity
  have harch : |∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftCommutator M (smoothPlateau L) t x| ≤
      2 * Λ * E * archFirstMoment := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le
      (integrableOn_archLevyDensity_mul_id.const_mul (2 * Λ * E)) ?_).trans_eq ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      have hA := archLevyDensity_pos ht0
      have hd1 : |smoothPlateau L x - smoothPlateau L (x + t)| ≤ Λ * t := by
        have := hΛ L (x + t) x
        rwa [show x - (x + t) = -t by ring, abs_neg, abs_of_pos ht0] at this
      have hd2 : |smoothPlateau L x - smoothPlateau L (x - t)| ≤ Λ * t := by
        have := hΛ L (x - t) x
        rwa [show x - (x - t) = t by ring, abs_of_pos ht0] at this
      have k1 := abs_mul_abs_smoothPlateau_sub_le_of_abs_le hC0 hM hxL (x + t) hd1
      have k2 := abs_mul_abs_smoothPlateau_sub_le_of_abs_le hC0 hM hxL (x - t) hd2
      have e1 : Real.exp (-(16 * |x + t|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [abs_nonneg (x + t)])
      have e2 : Real.exp (-(16 * |x - t|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [abs_nonneg (x - t)])
      have hΛt : 0 ≤ Λ * t := by positivity
      have hsc : |shiftCommutator M (smoothPlateau L) t x| ≤ 2 * Λ * E * t := by
        unfold shiftCommutator
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have hCE : 0 ≤ C * Real.exp (-(8 * L)) * (Λ * t) := by positivity
        have k1' : |M (x + t)| * |smoothPlateau L x - smoothPlateau L (x + t)| ≤ E * (Λ * t) := by
          refine k1.trans ?_
          rw [hE]
          calc C * Real.exp (-(8 * L)) * Real.exp (-(16 * |x + t|)) * (Λ * t)
              = C * Real.exp (-(8 * L)) * (Λ * t) * Real.exp (-(16 * |x + t|)) := by ring
            _ ≤ C * Real.exp (-(8 * L)) * (Λ * t) * 1 := mul_le_mul_of_nonneg_left e1 hCE
            _ = _ := by ring
        have k2' : |M (x - t)| * |smoothPlateau L x - smoothPlateau L (x - t)| ≤ E * (Λ * t) := by
          refine k2.trans ?_
          rw [hE]
          calc C * Real.exp (-(8 * L)) * Real.exp (-(16 * |x - t|)) * (Λ * t)
              = C * Real.exp (-(8 * L)) * (Λ * t) * Real.exp (-(16 * |x - t|)) := by ring
            _ ≤ C * Real.exp (-(8 * L)) * (Λ * t) * 1 := mul_le_mul_of_nonneg_left e2 hCE
            _ = _ := by ring
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hA]
      calc archLevyDensity t * |shiftCommutator M (smoothPlateau L) t x|
          ≤ archLevyDensity t * (2 * Λ * E * t) := mul_le_mul_of_nonneg_left hsc hA.le
        _ = _ := by ring
    · rw [integral_const_mul]
      rfl
  have hprime : |∑' n : ℕ, vonMangoldtAtom n * shiftCommutator M (smoothPlateau L) (Real.log n) x|
      ≤ 2 * E * Real.exp (8 * |x|) * primeEighthMoment := by
    rw [← Real.norm_eq_abs]
    refine tsum_of_norm_bounded
      ((summable_atom_mul_exp_neg_eight_log.mul_left (2 * E * Real.exp (8 * |x|))).hasSum.trans_eq
        (by rw [tsum_mul_left]; rfl)) fun n => ?_
    have hΛn := vonMangoldtAtom_nonneg n
    have k1 := abs_mul_abs_smoothPlateau_sub_le_of_abs_le hC0 hM hxL (x + Real.log n)
      (abs_smoothPlateau_sub_le_one L x (x + Real.log n))
    have k2 := abs_mul_abs_smoothPlateau_sub_le_of_abs_le hC0 hM hxL (x - Real.log n)
      (abs_smoothPlateau_sub_le_one L x (x - Real.log n))
    have ep : Real.exp (-(16 * |x + Real.log n|)) ≤
        Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) :=
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (x + Real.log n)])).trans
        (exp_neg_eight_mul_abs_add_log_le x n)
    have em : Real.exp (-(16 * |x - Real.log n|)) ≤
        Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) :=
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (x - Real.log n)])).trans
        (exp_neg_eight_mul_abs_sub_log_le x n)
    have hsc : |shiftCommutator M (smoothPlateau L) (Real.log n) x| ≤
        2 * (E * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)))) := by
      unfold shiftCommutator
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have k1' : |M (x + Real.log n)| * |smoothPlateau L x - smoothPlateau L (x + Real.log n)| ≤
          E * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
        k1.trans (by rw [hE, mul_one]; exact mul_le_mul_of_nonneg_left ep (by positivity))
      have k2' : |M (x - Real.log n)| * |smoothPlateau L x - smoothPlateau L (x - Real.log n)| ≤
          E * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
        k2.trans (by rw [hE, mul_one]; exact mul_le_mul_of_nonneg_left em (by positivity))
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛn]
    calc vonMangoldtAtom n * |shiftCommutator M (smoothPlateau L) (Real.log n) x|
        ≤ vonMangoldtAtom n * (2 * (E * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))))) :=
          mul_le_mul_of_nonneg_left hsc hΛn
      _ = _ := by ring
  unfold plateauCommutator
  refine (abs_add_le _ _).trans ?_
  rw [hE] at harch hprime
  linarith

/-- **Pairing law.** For a gauge `ω` with source `𝓛_D ω − ρω = Φ g` and a test `v ∈ C²_c`
supported in `[−R, R]`, the plateau truncations pair with `v` through the source only:
`|∫ v (𝓛_D(ω u_L) − ρ ω u_L) − ∫ v Φ g| ≤ K e^{−8L}` for `L ≥ R`. -/
theorem abs_integral_mul_generator_plateau_sub_le {ω g v : ℝ → ℝ} {C Λ R : ℝ}
    (hω : ContDiff ℝ 2 ω) (hC0 : 0 ≤ C)
    (hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)))
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ L x y, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x|)
    (hA : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * g x) (hg : Continuous g)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hsupp : ∀ x, R < |x| → v x = 0)
    {L : ℝ} (hRL : R ≤ L) :
    |(∫ x, v x * (twoSidedGenerator (fun y => ω y * smoothPlateau L y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (ω x * smoothPlateau L x))) -
      ∫ x, v x * (riemannKernelReal x * g x)| ≤
      riemannKernelReal 0 * C * (2 * Λ * archFirstMoment +
        2 * Real.exp (8 * R) * primeEighthMoment) * (∫ x, |v x|) * Real.exp (-(8 * L)) := by
  set z : ℝ → ℝ := fun y => ω y * smoothPlateau L y with hz_def
  have hz : ContDiff ℝ 2 z := hω.mul (contDiff_smoothPlateau L)
  have hzc : HasCompactSupport z := (hasCompactSupport_smoothPlateau L).mul_left
  have hMc : Continuous fun y => riemannKernelReal y * ω y := continuous_riemannKernelReal.mul hω.continuous
  have hMb : ∀ y, |riemannKernelReal y * ω y| ≤ C := fun y => by
    have h2 : Real.exp (-(24 * |y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])
    nlinarith [hM y, mul_le_mul_of_nonneg_left h2 hC0]
  have hI : Integrable fun x => v x * (twoSidedGenerator z x -
      riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    have hρ : Integrable fun x => v x * (riemannKernelReal x * Real.cosh (x / 2) * z x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ hvc.mul_right
      exact hv.continuous.mul ((continuous_riemannKernelReal.mul
        (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul hz.continuous)
    refine (((integrable_mul_archTwoSidedGenerator_of hv.continuous hvc hz hzc).add
      (integrable_mul_primeTwoSidedGenerator_of hv.continuous hvc hz hzc)).sub hρ).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, twoSidedGenerator_eq_arch_add_prime]
    ring
  have hJ : Integrable fun x => v x * (riemannKernelReal x * g x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hvc.mul_right
    exact hv.continuous.mul (continuous_riemannKernelReal.mul hg)
  have hvi : Integrable fun x => |v x| := (hv.continuous.integrable_of_hasCompactSupport hvc).abs
  rw [← integral_sub hI hJ, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hvi.const_mul (riemannKernelReal 0 * C *
    (2 * Λ * archFirstMoment + 2 * Real.exp (8 * R) * primeEighthMoment) * Real.exp (-(8 * L))))
    (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs]
    by_cases hvx : v x = 0
    · rw [hvx]
      simp only [zero_mul, sub_zero, abs_zero]
      have := riemannKernelReal_pos 0
      have := archFirstMoment_nonneg
      have := primeEighthMoment_nonneg
      positivity
    · have hxR : |x| ≤ R := by
        by_contra h
        exact hvx (hsupp x (not_le.mp h))
      have hxL : |x| ≤ L := hxR.trans hRL
      have hL := twoSidedGenerator_mul (hA x) (hP x)
        (integrableOn_archLevy_shiftCommutator hMc (contDiff_smoothPlateau L).continuous hMb (hΛ L) x)
        (summable_atom_mul_shiftCommutator hC0 hM (abs_smoothPlateau_sub_le_one L) x)
      have hpt : v x * (twoSidedGenerator z x - riemannKernelReal x * Real.cosh (x / 2) * z x) -
          v x * (riemannKernelReal x * g x) = v x * riemannKernelReal x *
            plateauCommutator (fun y => riemannKernelReal y * ω y) (smoothPlateau L) x := by
        simp only [hz_def]
        rw [hL, smoothPlateau_eq_one hxL]
        linear_combination v x * hsrc x
      rw [hpt, abs_mul, abs_mul, abs_of_pos (riemannKernelReal_pos x)]
      have hc := abs_plateauCommutator_le_of_abs_le hC0 hΛ0 hM hΛ hxL
      have h8 : Real.exp (8 * |x|) ≤ Real.exp (8 * R) := Real.exp_le_exp.mpr (by linarith)
      have hP0 := primeEighthMoment_nonneg
      have hA0 := archFirstMoment_nonneg
      have hc' : |plateauCommutator (fun y => riemannKernelReal y * ω y) (smoothPlateau L) x| ≤
          C * Real.exp (-(8 * L)) * (2 * Λ * archFirstMoment +
            2 * Real.exp (8 * R) * primeEighthMoment) :=
        hc.trans (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))
      have hΦ := riemannKernelReal_le_zero_point x
      have hΦ0 := riemannKernelReal_pos x
      calc |v x| * riemannKernelReal x *
            |plateauCommutator (fun y => riemannKernelReal y * ω y) (smoothPlateau L) x|
          ≤ |v x| * riemannKernelReal 0 * (C * Real.exp (-(8 * L)) * (2 * Λ * archFirstMoment +
              2 * Real.exp (8 * R) * primeEighthMoment)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hΦ (abs_nonneg _)) hc' (abs_nonneg _)
              (mul_nonneg (abs_nonneg _) (riemannKernelReal_pos 0).le)
        _ = _ := by ring
  · rw [integral_const_mul]
    ring

/-! ### The radical -/

/-- **The harmonic theta span is the radical of the Markov form.** If `ω` is harmonic
(`𝓛_D ω = Φ cosh(x/2) ω`) with test coordinate `|Φω| ≤ C e^{−24|·|}`, then for every
`v ∈ C²_c(ℝ)` there are `K, R` with `|markovEnergy(Φ(ω u_L + v)) − markovEnergy(Φ v)| ≤ K e^{−8L}`
for all `L ≥ R`. -/
theorem abs_markovEnergy_add_harmonicPlateau_sub_le {ω v : ℝ → ℝ} {C : ℝ} (hω : ContDiff ℝ 2 ω)
    (hC0 : 0 ≤ C) (hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)))
    (hA : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hharm : ∀ x, twoSidedGenerator ω x = riemannKernelReal x * Real.cosh (x / 2) * ω x)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ K R : ℝ, 0 ≤ K ∧ ∀ L, R ≤ L →
      |markovEnergy (fun x => (phiDoobTest (fun y => ω y * smoothPlateau L y + v y) x : ℂ)) -
        markovEnergy (fun x => (phiDoobTest v x : ℂ))| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hvc
  have hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * (fun _ => (0 : ℝ)) x := fun x => by rw [hharm x]; ring
  set K₁ := C ^ 2 * (2 * Λ * archFirstMoment + 2 * primeEighthMoment) *
    (∫ x : ℝ, Real.exp (-(8 * |x|)))
  set K₂ := riemannKernelReal 0 * C * (2 * Λ * archFirstMoment +
    2 * Real.exp (8 * R) * primeEighthMoment) * (∫ x, |v x|)
  have hK₁ : 0 ≤ K₁ := by
    have := archFirstMoment_nonneg
    have := primeEighthMoment_nonneg
    have : 0 ≤ ∫ x : ℝ, Real.exp (-(8 * |x|)) := integral_nonneg fun x => (Real.exp_pos _).le
    positivity
  have hK₂ : 0 ≤ K₂ := by
    have := archFirstMoment_nonneg
    have := primeEighthMoment_nonneg
    have := riemannKernelReal_pos 0
    have : 0 ≤ ∫ x, |v x| := integral_nonneg fun x => abs_nonneg _
    positivity
  refine ⟨K₁ + 2 * K₂, R, by positivity, fun L hRL => ?_⟩
  have hz : ContDiff ℝ 2 fun y => ω y * smoothPlateau L y := hω.mul (contDiff_smoothPlateau L)
  have hzc : HasCompactSupport fun y => ω y * smoothPlateau L y :=
    (hasCompactSupport_smoothPlateau L).mul_left
  have hpol := markovEnergy_phiDoob_add hz hzc hv hvc
  have hplat := abs_markovEnergy_plateau_sub_integral_le hω hC0 hM hΛ0 hΛ hA hP hsrc
    continuous_const L
  have hpair := abs_integral_mul_generator_plateau_sub_le hω hC0 hM hΛ0 hΛ hA hP hsrc
    continuous_const hv hvc hsupp hRL
  simp only [mul_zero, integral_zero, sub_zero] at hplat hpair
  rw [hpol]
  calc |markovEnergy (fun x => (phiDoobTest (fun y => ω y * smoothPlateau L y) x : ℂ)) +
        markovEnergy (fun x => (phiDoobTest v x : ℂ)) +
        2 * (∫ x, v x * (twoSidedGenerator (fun y => ω y * smoothPlateau L y) x -
          riemannKernelReal x * Real.cosh (x / 2) * (ω x * smoothPlateau L x))) -
        markovEnergy (fun x => (phiDoobTest v x : ℂ))|
      = |markovEnergy (fun x => (phiDoobTest (fun y => ω y * smoothPlateau L y) x : ℂ)) +
          2 * (∫ x, v x * (twoSidedGenerator (fun y => ω y * smoothPlateau L y) x -
            riemannKernelReal x * Real.cosh (x / 2) * (ω x * smoothPlateau L x)))| := by
        congr 1
        ring
    _ ≤ K₁ * Real.exp (-(8 * L)) + 2 * (K₂ * Real.exp (-(8 * L))) := by
        refine (abs_add_le _ _).trans (add_le_add hplat ?_)
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left hpair zero_le_two
    _ = (K₁ + 2 * K₂) * Real.exp (-(8 * L)) := by ring

/-- **Instance: pole-free superpositions of shifted ground states.** If `σ = Σ c_j sinh(a_j/2) = 0`,
adding `Φ(ω u_L)` to any test changes its Markov energy by `O(e^{−8L})`. -/
theorem exists_abs_markovEnergy_add_spanPlateau_sub_le_of_poleFree {ι : Type*} {s : Finset ι}
    {c a : ι → ℝ} (hσ : spanSourceCoefficient s c a = 0) {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    ∃ K R : ℝ, 0 ≤ K ∧ ∀ L, R ≤ L →
      |markovEnergy (fun x =>
          (phiDoobTest (fun y => spanGroundState s c a y * smoothPlateau L y + v y) x : ℂ)) -
        markovEnergy (fun x => (phiDoobTest v x : ℂ))| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_spanShiftDifference_le s c a
  refine abs_markovEnergy_add_harmonicPlateau_sub_le (contDiff_spanGroundState s c a) hC0
    (fun y => by rw [riemannKernelReal_mul_spanGroundState]; exact hC y)
    (integrableOn_archLevy_twoSidedShiftGenerator_spanGroundState s c a)
    (summable_atom_twoSidedShiftGenerator_spanGroundState s c a) (fun x => ?_) hv hvc
  have h := twoSidedGenerator_spanGroundState_sub_potential s c a x
  rw [hσ] at h
  linarith

/-- **Instance: harmonic combinations of translates** (`A = B = 0`). -/
theorem exists_abs_markovEnergy_add_translatePlateau_sub_le_of_harmonic {ι : Type*} {s : Finset ι}
    {α b : ι → ℝ} (hA : translateCoshCoefficient s α b = 0) (hB : translateSinhCoefficient s α b = 0)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ K R : ℝ, 0 ≤ K ∧ ∀ L, R ≤ L →
      |markovEnergy (fun x =>
          (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y + v y) x : ℂ)) -
        markovEnergy (fun x => (phiDoobTest v x : ℂ))| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_riemannKernelReal_mul_translateSpan_le s α b
  refine abs_markovEnergy_add_harmonicPlateau_sub_le (contDiff_translateSpan s α b) hC0 hC
    (integrableOn_archLevy_twoSidedShiftGenerator_translateSpan s α b)
    (summable_atom_twoSidedShiftGenerator_translateSpan s α b) (fun x => ?_) hv hvc
  have h := twoSidedGenerator_translateSpan_sub_potential s α b x
  unfold translateSource at h
  rw [hA, hB] at h
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
