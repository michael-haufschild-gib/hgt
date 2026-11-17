import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeHeadHasAnAveragedLeadingTerm

/-!
# The prime head is the Abel mean of the prime-averaged profile

For a profile `F` of the energy domain `H` let

  `S_F(h) = Σ_n Λ(n) n^{−½} h⁻¹ ∫_{−log n}^{−log n + h} F`   (`primeAveragedProfile`),

the prime-weighted right averages of `F` at the prime points, at scale `h`.

* **Exact averaged form** (`mul_primeHead_neg_eq_integral`). For every `F ∈ H` and `t ≥ 16`,
  `t · ŜF(−t) = ∫_0^∞ s e^{−s} S_F(s/t) ds`. At one prime point this is the Laplace transform of
  the primitive after `T = s/t`; the sum over `n` is exchanged with the integral through the bound
  `|h⁻¹ ∫_{−L}^{−L+h} F| ≤ e^{−4L}(e^{8h} ∫F²e^{−8u} + 1/h)/2` (Cauchy–Schwarz against the
  confinement weight and the arithmetic–geometric mean inequality).
* **Leading term** (`tendsto_mul_primeHead_neg_of_primeAveragedProfile`). If `S_F(h) → ℓ` as
  `h → 0⁺`, then `t · ŜF(−t) → ℓ`.

So the scaled prime head is, for every profile, an exponential average of `S_F` at scale `1/t`; it
converges exactly when these averages do.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem atom_nonneg_pa (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The right average `h⁻¹ ∫_{−L}^{−L+h} F` of `F` at `−L`. -/
def rightAverage (F : ℝ → ℝ) (L h : ℝ) : ℝ := (∫ u in (-L)..(-L + h), F u) / h

/-- The prime-averaged profile `S_F(h) = Σ_n Λ(n) n^{−½} h⁻¹ ∫_{−log n}^{−log n+h} F`. -/
def primeAveragedProfile (F : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * rightAverage F (Real.log n) h

/-! ## Elementary bounds -/

theorem abs_le_of_mul_sq (x : ℝ) {c : ℝ} (hc : 0 < c) : |x| ≤ (c * x ^ 2 + c⁻¹) / 2 := by
  have h1 := mul_inv_cancel₀ hc.ne'
  -- `c (c x² + c⁻¹ − 2|x|) = (c|x| − 1)²`
  have key : c * (c * x ^ 2 + c⁻¹ - |x| * 2) = (c * |x| - 1) ^ 2 := by
    have e : c * (c * x ^ 2 + c⁻¹ - |x| * 2) = c ^ 2 * |x| ^ 2 + c * c⁻¹ - 2 * (c * |x|) := by
      rw [sq_abs]; ring
    rw [e, h1]; ring
  have h2 : 0 ≤ c * (c * x ^ 2 + c⁻¹ - |x| * 2) := by rw [key]; exact sq_nonneg _
  have h3 := (mul_nonneg_iff_of_pos_left hc).mp h2
  rw [le_div_iff₀ two_pos]
  linarith

theorem exp_neg_mul_exp_le {t s : ℝ} (ht : 16 ≤ t) (hs : 0 < s) :
    Real.exp (-s) * Real.exp (8 * (s / t)) ≤ Real.exp (-(1 / 2) * s) := by
  have htpos : 0 < t := by linarith
  have h8 : 8 * (s / t) ≤ s / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ htpos two_pos]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr ht)]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem mul_exp_neg_half_le_four_exp (s : ℝ) :
    s * Real.exp (-(1 / 2) * s) ≤ 4 * Real.exp (-(1 / 4) * s) := by
  have h4 : s ≤ 4 * Real.exp (s / 4) := by linarith [Real.add_one_le_exp (s / 4)]
  calc s * Real.exp (-(1 / 2) * s) ≤ 4 * Real.exp (s / 4) * Real.exp (-(1 / 2) * s) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 4 * Real.exp (-(1 / 4) * s) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-! ## One prime point -/

/-- **The Abel integral is an average of right averages.** -/
theorem mul_abelHead_eq_integral_rightAverage {F : ℝ → ℝ} (hF : Integrable F) {t : ℝ}
    (ht : 0 < t) (L : ℝ) :
    t * abelHead F t L = ∫ s in Ioi (0 : ℝ), s * Real.exp (-s) * rightAverage F L (s / t) := by
  have h1 := integral_exp_mul_primitive_of_integrable (hF.comp_sub_right L) ht
  simp only [neg_mul] at h1
  have h2 := integral_comp_mul_left_Ioi
    (fun s => Real.exp (-s) * ∫ v in (0 : ℝ)..s / t, F (v - L)) 0 ht
  simp only [mul_zero, smul_eq_mul, mul_div_cancel_left₀ _ ht.ne'] at h2
  rw [abelHead_eq_shift, h1, h2, mul_inv_cancel_left₀ ht.ne', ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : s ≠ 0 := (show (0 : ℝ) < s from hs).ne'
  simp only [rightAverage]
  rw [intervalIntegral.integral_comp_sub_right F L, zero_sub, sub_eq_neg_add,
    show s * Real.exp (-s) * ((∫ u in (-L)..(-L + s / t), F u) / (s / t)) =
      s / (s / t) * (Real.exp (-s) * ∫ u in (-L)..(-L + s / t), F u) by ring,
    div_div_cancel₀ hs0]

/-- Cauchy–Schwarz against the confinement weight: `(h⁻¹∫_{−L}^{−L+h} F)² h ≤ e^{8(h−L)} ∫F²e^{−8u}`. -/
theorem sq_rightAverage_mul_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (L : ℝ) {h : ℝ}
    (hh : 0 < h) :
    rightAverage F L h ^ 2 * h ≤ Real.exp (8 * (h - L)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hab : -L ≤ -L + h := by linarith
  have hone : ∫ _ in Ioc (-L) (-L + h), (1 : ℝ) = h := by
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  have hcs := sq_integral_mul_le (μ := volume.restrict (Ioc (-L) (-L + h))) (f := F)
    (g := fun _ => (1 : ℝ)) hF.meas.aestronglyMeasurable aestronglyMeasurable_const
    hF.sq.integrableOn (by fun_prop : Continuous fun _ : ℝ => (1 : ℝ) ^ 2).integrableOn_Ioc
  simp only [mul_one, one_pow, hone] at hcs
  -- on the interval `F² ≤ e^{8(h−L)} F² e^{−8u}`
  have hloc : ∫ u in Ioc (-L) (-L + h), F u ^ 2 ≤
      Real.exp (8 * (h - L)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
    calc ∫ u in Ioc (-L) (-L + h), F u ^ 2
        ≤ ∫ u in Ioc (-L) (-L + h), Real.exp (8 * (h - L)) * (F u ^ 2 * Real.exp (-(8 * u))) := by
          refine setIntegral_mono_on hF.sq.integrableOn (hF.exponential.const_mul _).integrableOn
            measurableSet_Ioc fun u hu => ?_
          have h1 : 1 ≤ Real.exp (8 * (h - L)) * Real.exp (-(8 * u)) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [hu.2])
          calc F u ^ 2 = F u ^ 2 * 1 := by ring
            _ ≤ F u ^ 2 * (Real.exp (8 * (h - L)) * Real.exp (-(8 * u))) :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
            _ = _ := by ring
      _ ≤ Real.exp (8 * (h - L)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hF.exponential
            (Eventually.of_forall fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
            (Real.exp_pos _).le
  unfold rightAverage
  rw [intervalIntegral.integral_of_le hab, div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hh 2)]
  calc (∫ u in Ioc (-L) (-L + h), F u) ^ 2 * h ≤ (∫ u in Ioc (-L) (-L + h), F u ^ 2) * h * h :=
        mul_le_mul_of_nonneg_right hcs hh.le
    _ ≤ (Real.exp (8 * (h - L)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u))) * h * h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hloc hh.le) hh.le
    _ = _ := by ring

/-- **The right averages decay like `e^{−4L}`.** -/
theorem abs_rightAverage_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (L : ℝ) {h : ℝ}
    (hh : 0 < h) :
    |rightAverage F L h| ≤ Real.exp (-4 * L) *
      ((Real.exp (8 * h) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / h) / 2) := by
  have hx2 := sq_rightAverage_mul_le hF L hh
  have hamgm := abs_le_of_mul_sq (rightAverage F L h) (mul_pos (Real.exp_pos (4 * L)) hh)
  have hexp : Real.exp (4 * L) * Real.exp (8 * (h - L)) =
      Real.exp (-4 * L) * Real.exp (8 * h) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (4 * L) * h * rightAverage F L h ^ 2 ≤
      Real.exp (-4 * L) * (Real.exp (8 * h) * ∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
    calc Real.exp (4 * L) * h * rightAverage F L h ^ 2
        = Real.exp (4 * L) * (rightAverage F L h ^ 2 * h) := by ring
      _ ≤ Real.exp (4 * L) * (Real.exp (8 * (h - L)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u))) :=
          mul_le_mul_of_nonneg_left hx2 (Real.exp_pos _).le
      _ = Real.exp (4 * L) * Real.exp (8 * (h - L)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
          ring
      _ = _ := by rw [hexp]; ring
  have h2 : (Real.exp (4 * L) * h)⁻¹ = Real.exp (-4 * L) * (1 / h) := by
    rw [mul_inv, ← Real.exp_neg, one_div, neg_mul]
  rw [h2] at hamgm
  calc |rightAverage F L h|
      ≤ (Real.exp (-4 * L) * (Real.exp (8 * h) * ∫ u, F u ^ 2 * Real.exp (-(8 * u))) +
          Real.exp (-4 * L) * (1 / h)) / 2 := by linarith
    _ = _ := by ring

theorem abs_mul_rightAverage_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (L : ℝ)
    {t s : ℝ} (ht : 16 ≤ t) (hs : 0 < s) :
    |s * Real.exp (-s) * rightAverage F L (s / t)| ≤ Real.exp (-4 * L) *
      ((4 * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) * Real.exp (-(1 / 4) * s) +
        t * Real.exp (-s)) / 2) := by
  obtain ⟨E, hE_def⟩ : ∃ E, E = ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := ⟨_, rfl⟩
  have hE : 0 ≤ E := by
    rw [hE_def]; exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have htpos : 0 < t := by linarith
  have hx := abs_rightAverage_le hF L (div_pos hs htpos)
  rw [← hE_def, one_div, inv_div] at hx
  rw [← hE_def, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos (Real.exp_pos _)]
  have hst : s * (t / s) = t := by rw [mul_div_assoc', mul_div_cancel_left₀ t hs.ne']
  have h7 : s * (Real.exp (-s) * Real.exp (8 * (s / t))) * E ≤
      4 * E * Real.exp (-(1 / 4) * s) := by
    calc s * (Real.exp (-s) * Real.exp (8 * (s / t))) * E ≤ s * Real.exp (-(1 / 2) * s) * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_neg_mul_exp_le ht hs) hs.le) hE
      _ ≤ 4 * Real.exp (-(1 / 4) * s) * E :=
          mul_le_mul_of_nonneg_right (mul_exp_neg_half_le_four_exp s) hE
      _ = 4 * E * Real.exp (-(1 / 4) * s) := by ring
  calc s * Real.exp (-s) * |rightAverage F L (s / t)|
      ≤ s * Real.exp (-s) * (Real.exp (-4 * L) * ((Real.exp (8 * (s / t)) * E + t / s) / 2)) :=
        mul_le_mul_of_nonneg_left hx (mul_nonneg hs.le (Real.exp_pos _).le)
    _ = Real.exp (-4 * L) * ((s * (Real.exp (-s) * Real.exp (8 * (s / t))) * E +
          Real.exp (-s) * (s * (t / s))) / 2) := by ring
    _ = Real.exp (-4 * L) * ((s * (Real.exp (-s) * Real.exp (8 * (s / t))) * E +
          Real.exp (-s) * t) / 2) := by rw [hst]
    _ ≤ Real.exp (-4 * L) * ((4 * E * Real.exp (-(1 / 4) * s) + t * Real.exp (-s)) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        linarith

theorem measurable_rightAverage_div {F : ℝ → ℝ} (hF : Integrable F) (L t : ℝ) :
    Measurable fun s => rightAverage F L (s / t) := by
  unfold rightAverage
  exact ((intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable) (-L)).comp
    (continuous_const.add (continuous_id.div_const t))).measurable.div (measurable_id.div_const t)

/-! ## The prime-averaged profile -/

theorem summable_primeAveragedProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {h : ℝ}
    (hh : 0 < h) : Summable fun n : ℕ => vonMangoldtAtom n * rightAverage F (Real.log n) h :=
  Summable.of_norm_bounded ((summable_primeHead_damping (c := 4) (by norm_num)).mul_right _)
    fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (atom_nonneg_pa n), mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_rightAverage_le hF _ hh) (atom_nonneg_pa n)

theorem abs_primeAveragedProfile_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {h : ℝ}
    (hh : 0 < h) :
    |primeAveragedProfile F h| ≤ (∑' n : ℕ, vonMangoldtAtom n * Real.exp (-4 * Real.log n)) *
      ((Real.exp (8 * h) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / h) / 2) := by
  have hD := summable_primeHead_damping (c := 4) (by norm_num)
  have hb : ∀ n : ℕ, |vonMangoldtAtom n * rightAverage F (Real.log n) h| ≤
      vonMangoldtAtom n * Real.exp (-4 * Real.log n) *
        ((Real.exp (8 * h) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / h) / 2) := fun n => by
    rw [abs_mul, abs_of_nonneg (atom_nonneg_pa n), mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_rightAverage_le hF _ hh) (atom_nonneg_pa n)
  have hsa := (summable_primeAveragedProfile hF hh).abs
  unfold primeAveragedProfile
  rw [← tsum_mul_right]
  calc |∑' n : ℕ, vonMangoldtAtom n * rightAverage F (Real.log n) h|
      ≤ ∑' n : ℕ, |vonMangoldtAtom n * rightAverage F (Real.log n) h| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun n : ℕ => vonMangoldtAtom n * rightAverage F (Real.log n) h)
          (by simpa only [Real.norm_eq_abs] using hsa)
    _ ≤ _ := hasSum_le hb hsa.hasSum (hD.mul_right _).hasSum

/-! ## The exact averaged form -/

/-- **The scaled prime head is an exponential average of the prime-averaged profile**, for every
profile of the energy domain. -/
theorem mul_tsum_abelHead_eq_integral {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ}
    (ht : 16 ≤ t) :
    t * ∑' n : ℕ, vonMangoldtAtom n * abelHead F t (Real.log n) =
      ∫ s in Ioi (0 : ℝ), s * Real.exp (-s) * primeAveragedProfile F (s / t) := by
  have htpos : 0 < t := by linarith
  obtain ⟨E, hE_def⟩ : ∃ E, E = ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := ⟨_, rfl⟩
  -- the majorant `b(s) = (4E e^{−s/4} + t e^{−s})/2`
  have hexp1 : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun s _ => by simp) measurableSet_Ioi
  have hb : IntegrableOn
      (fun s : ℝ => (4 * E * Real.exp (-(1 / 4) * s) + t * Real.exp (-s)) / 2) (Ioi 0) :=
    (((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (4 * E)).add
      (hexp1.const_mul t)).div_const 2
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ → ℝ, f = fun n s =>
      vonMangoldtAtom n * (s * Real.exp (-s) * rightAverage F (Real.log n) (s / t)) := ⟨_, rfl⟩
  have hbound : ∀ n, ∀ s ∈ Ioi (0 : ℝ), ‖f n s‖ ≤ vonMangoldtAtom n *
      Real.exp (-4 * Real.log n) * ((4 * E * Real.exp (-(1 / 4) * s) + t * Real.exp (-s)) / 2) := by
    intro n s hs
    rw [hf, Real.norm_eq_abs, abs_mul, abs_of_nonneg (atom_nonneg_pa n),
      mul_assoc (vonMangoldtAtom n)]
    refine mul_le_mul_of_nonneg_left ?_ (atom_nonneg_pa n)
    have h := abs_mul_rightAverage_le hF (Real.log n) ht hs
    rwa [← hE_def] at h
  have hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioi 0)) := fun n => by
    rw [hf]
    exact (measurable_const.mul ((measurable_id.mul
      (by fun_prop : Measurable fun s : ℝ => Real.exp (-s))).mul
      (measurable_rightAverage_div hF.integrable _ t))).aestronglyMeasurable
  have hint : ∀ n, Integrable (f n) (volume.restrict (Ioi 0)) := fun n =>
    (hb.const_mul (vonMangoldtAtom n * Real.exp (-4 * Real.log n))).mono' (hmeas n)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hbound n)))
  have hsum : Summable fun n => ∫ s in Ioi (0 : ℝ), ‖f n s‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_primeHead_damping (c := 4) (by norm_num)).mul_right
        (∫ s in Ioi (0 : ℝ), (4 * E * Real.exp (-(1 / 4) * s) + t * Real.exp (-s)) / 2))
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hb.const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hbound n)))
  have hterm : ∀ n : ℕ, t * (vonMangoldtAtom n * abelHead F t (Real.log n)) =
      ∫ s in Ioi (0 : ℝ), f n s := fun n => by
    rw [hf, integral_const_mul, ← mul_abelHead_eq_integral_rightAverage hF.integrable htpos]
    ring
  rw [← tsum_mul_left, tsum_congr hterm, integral_tsum_of_summable_integral_norm hint hsum]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [hf, primeAveragedProfile]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- **Exact averaged form of the prime head.** For every `F ∈ H` and `t ≥ 16`,
`t · ŜF(−t) = ∫_0^∞ s e^{−s} S_F(s/t) ds`. -/
theorem mul_primeHead_neg_eq_integral {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ}
    (ht : 16 ≤ t) :
    (t : ℂ) * primeHead F (-(t : ℂ)) =
      ((∫ s in Ioi (0 : ℝ), s * Real.exp (-s) * primeAveragedProfile F (s / t) : ℝ) : ℂ) := by
  rw [← mul_tsum_abelHead_eq_integral hF ht, primeHead_neg_ofReal, Complex.ofReal_mul,
    Complex.ofReal_tsum]

/-! ## The leading term -/

/-- **The leading term of the prime head is the limit of the prime-averaged profile.** If
`S_F(h) → ℓ` as `h → 0⁺` then `t · ŜF(−t) → ℓ`. -/
theorem tendsto_mul_primeHead_neg_of_primeAveragedProfile {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ℓ : ℝ}
    (hS : Tendsto (primeAveragedProfile F) (𝓝[>] 0) (𝓝 ℓ)) :
    Tendsto (fun t : ℝ => (t : ℂ) * primeHead F (-(t : ℂ))) atTop (𝓝 (ℓ : ℂ)) := by
  obtain ⟨E, hE_def⟩ : ∃ E, E = ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := ⟨_, rfl⟩
  have hE : 0 ≤ E := by
    rw [hE_def]; exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  obtain ⟨D, hD_def⟩ : ∃ D, D = ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-4 * Real.log n) :=
    ⟨_, rfl⟩
  have hD : 0 ≤ D := by
    rw [hD_def]; exact tsum_nonneg fun n => mul_nonneg (atom_nonneg_pa n) (Real.exp_pos _).le
  -- near `0` the profile is within `1` of `ℓ`
  obtain ⟨δ, hδ, hδS⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Ioo 0 δ, |primeAveragedProfile F h - ℓ| < 1 := by
    obtain ⟨u, hu, hsub⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.mp (Metric.tendsto_nhds.mp hS 1 one_pos)
    exact ⟨u, hu, fun h hh => by simpa [Real.dist_eq] using hsub hh⟩
  -- a global bound `|S_F(h)| ≤ B e^{8h}`
  have hX : 0 ≤ D * ((E + 1 / δ) / 2) :=
    mul_nonneg hD (div_nonneg (add_nonneg hE (one_div_pos.mpr hδ).le) two_pos.le)
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ h : ℝ, 0 < h → |primeAveragedProfile F h| ≤ B * Real.exp (8 * h) := by
    refine ⟨|ℓ| + 1 + D * ((E + 1 / δ) / 2), by linarith [abs_nonneg ℓ], fun h hh => ?_⟩
    have he : 1 ≤ Real.exp (8 * h) := Real.one_le_exp (by linarith)
    have hB1 : 0 ≤ |ℓ| + 1 + D * ((E + 1 / δ) / 2) := by linarith [abs_nonneg ℓ]
    rcases lt_or_ge h δ with hlt | hge
    · have h1 := hδS h ⟨hh, hlt⟩
      have h2 := abs_sub_abs_le_abs_sub (primeAveragedProfile F h) ℓ
      nlinarith [mul_nonneg hB1 (sub_nonneg.mpr he)]
    · have h1 := abs_primeAveragedProfile_le hF hh
      rw [← hE_def, ← hD_def] at h1
      have h2 : 1 / h ≤ Real.exp (8 * h) / δ := by
        rw [div_le_div_iff₀ hh hδ]
        nlinarith [mul_nonneg (sub_nonneg.mpr he) hh.le]
      have h3 : (Real.exp (8 * h) * E + 1 / h) / 2 ≤ (E + 1 / δ) / 2 * Real.exp (8 * h) := by
        have : Real.exp (8 * h) / δ = 1 / δ * Real.exp (8 * h) := by ring
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 hD
      nlinarith [mul_nonneg (by linarith [abs_nonneg ℓ] : (0 : ℝ) ≤ |ℓ| + 1)
        (Real.exp_pos (8 * h)).le]
  -- domination for `t ≥ 16`
  have hdom : ∀ t : ℝ, 16 ≤ t → ∀ s : ℝ, 0 < s →
      ‖s * Real.exp (-s) * primeAveragedProfile F (s / t)‖ ≤ 4 * B * Real.exp (-(1 / 4) * s) := by
    intro t ht s hs
    have htpos : 0 < t := by linarith
    have h1 := hB (s / t) (div_pos hs htpos)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos (Real.exp_pos _)]
    calc s * Real.exp (-s) * |primeAveragedProfile F (s / t)|
        ≤ s * Real.exp (-s) * (B * Real.exp (8 * (s / t))) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hs.le (Real.exp_pos _).le)
      _ = B * (s * (Real.exp (-s) * Real.exp (8 * (s / t)))) := by ring
      _ ≤ B * (s * Real.exp (-(1 / 2) * s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (exp_neg_mul_exp_le ht hs) hs.le) hB0
      _ ≤ B * (4 * Real.exp (-(1 / 4) * s)) :=
          mul_le_mul_of_nonneg_left (mul_exp_neg_half_le_four_exp s) hB0
      _ = 4 * B * Real.exp (-(1 / 4) * s) := by ring
  -- measurability: `S_F` is the pointwise limit of its partial sums on `s > 0`
  have hmeas : ∀ t : ℝ, 0 < t → AEStronglyMeasurable
      (fun s => s * Real.exp (-s) * primeAveragedProfile F (s / t)) (volume.restrict (Ioi 0)) := by
    intro t ht
    have hSm : AEStronglyMeasurable (fun s => primeAveragedProfile F (s / t))
        (volume.restrict (Ioi 0)) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N s =>
        ∑ n ∈ Finset.range N, vonMangoldtAtom n * rightAverage F (Real.log n) (s / t))
        (fun N => (Finset.measurable_sum _ fun n _ => measurable_const.mul
          (measurable_rightAverage_div hF.integrable _ t)).aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
      exact (summable_primeAveragedProfile hF (div_pos hs ht)).hasSum.tendsto_sum_nat
    exact ((measurable_id.mul (by fun_prop : Measurable fun s : ℝ => Real.exp (-s))
      ).aestronglyMeasurable).mul hSm
  have hlim : ∀ s : ℝ, 0 < s → Tendsto (fun t : ℝ => s * Real.exp (-s) *
      primeAveragedProfile F (s / t)) atTop (𝓝 (s * Real.exp (-s) * ℓ)) := by
    intro s hs
    have h0 : Tendsto (fun t : ℝ => s / t) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr
        ⟨?_, (eventually_gt_atTop 0).mono fun t ht => div_pos hs ht⟩
      simpa using tendsto_const_nhds.div_atTop tendsto_id
    exact (hS.comp h0).const_mul _
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (l := atTop) (F := fun t s => s * Real.exp (-s) * primeAveragedProfile F (s / t))
    (f := fun s => s * Real.exp (-s) * ℓ) (fun s => 4 * B * Real.exp (-(1 / 4) * s))
    ((eventually_gt_atTop 0).mono fun t ht => hmeas t ht)
    ((eventually_ge_atTop 16).mono fun t ht => (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs => hdom t ht s hs))
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => hlim s hs))
  have hval : ∫ s in Ioi (0 : ℝ), s * Real.exp (-s) * ℓ = ℓ := by
    rw [integral_mul_const, integral_Ioi_mul_exp_neg_eq_one, one_mul]
  rw [hval] at h
  refine ((Complex.continuous_ofReal.tendsto ℓ).comp h).congr'
    ((eventually_ge_atTop 16).mono fun t ht => ?_)
  exact (mul_primeHead_neg_eq_integral hF ht).symm

#print axioms mul_primeHead_neg_eq_integral
#print axioms tendsto_mul_primeHead_neg_of_primeAveragedProfile

end GaloisForLFunctions.ExclusionOfTheCriticalState
