import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadResolvesTheWallCharges
import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePrimeHeadsAreHardyTransforms
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The wall seen from the left

Left of the strip the left formula of a profile `F` carries a Lévy head `JF` and a prime head `ŜF`.
At `p = −t`, `t → ∞`, both are Abel means: of `F` at the wall and of `F` just right of the prime
points `−log n`.

* **Prime head.** `ŜF(−t) = Σ_n Λ(n) n^{−½} ∫_{u > −log n} e^{−t(log n + u)} F(u) du`
  (`primeHead_neg_ofReal`), and `t ∫_{u > −L} e^{−t(L+u)} F(u) du = ∫_{s > 0} e^{−s} F(s/t − L) ds`
  (`mul_abelHead_eq`).
  - For every `F ∈ H`, `√t · ŜF(−t) → 0` (`tendsto_sqrt_mul_primeHead_neg`): Cauchy–Schwarz on each
    Abel integral, and the `F²`-mass seen by the Abel weight vanishes.
  - If `F` is right-continuous at the prime points and `|F(u)| ≤ C e^{cu}` with `c > ½`, then
    `t · ŜF(−t) → Σ_n Λ(n) n^{−½} F(−log n)` (`tendsto_mul_primeHead_neg_of_regular`).
* **Lévy head.** `t · JF(−t) = Σ_k LF(2k+½) · t/(2k+½+t)` (`hasSum_mul_levyHeadTerm_neg`).
  - If the trivial-zero moments `LF(2k+½)` are absolutely summable, `t · JF(−t) → Σ_k LF(2k+½)`
    (`tendsto_mul_levyHeadTerm_neg`).
  - For the critical state every moment has the sign of `LF(½)`, so the oriented scaled head
    `LF(½) · t · JF(−t)` tends to the positive mass `Σ_k LF(½) LF(2k+½)` or to `+∞`
    (`criticalState_levyHead_asymptotic`).

Point values of a profile of `H` at `−log n` are not defined, so for a general profile the leading
term of `ŜF` exists only through these Abel means; `o(t^{−½})` is what holds without regularity.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem atom_nonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-! ## The prime head as a sum of Abel integrals -/

/-- The Abel integral `∫_{u > −L} e^{−t(L + u)} F(u) du` that the prime point `−L` contributes. -/
def abelHead (F : ℝ → ℝ) (t L : ℝ) : ℝ := ∫ u in Ioi (-L), Real.exp (-(t * (L + u))) * F u

theorem primeHead_term_neg_ofReal (F : ℝ → ℝ) (t : ℝ) (n : ℕ) :
    (vonMangoldtAtom n : ℂ) *
        (cexp (-(t : ℂ) * Real.log n) * levyHead F (-(t : ℂ)) (Real.log n)) =
      ((vonMangoldtAtom n * abelHead F t (Real.log n) : ℝ) : ℂ) := by
  unfold levyHead abelHead
  rw [integral_Ici_eq_integral_Ioi, Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The prime head at `p = −t` is a sum of Abel integrals.** -/
theorem primeHead_neg_ofReal (F : ℝ → ℝ) (t : ℝ) :
    primeHead F (-(t : ℂ)) =
      ∑' n : ℕ, ((vonMangoldtAtom n * abelHead F t (Real.log n) : ℝ) : ℂ) := by
  unfold primeHead
  exact tsum_congr fun n => primeHead_term_neg_ofReal F t n

theorem integral_abelWeight {t : ℝ} (ht : 0 < t) (L : ℝ) :
    ∫ u in Ioi (-L), Real.exp (-(t * (L + u))) = 1 / t := by
  have e : ∀ u : ℝ, Real.exp (-(t * (L + u))) = Real.exp (-(t * L)) * Real.exp (-t * u) :=
    fun u => by rw [← Real.exp_add]; congr 1; ring
  simp_rw [e]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -t < 0), neg_div_neg_eq,
    mul_div_assoc', ← Real.exp_add, show -(t * L) + -t * -L = 0 by ring, Real.exp_zero]

theorem integrableOn_abelWeight {t : ℝ} (ht : 0 < t) (L : ℝ) :
    IntegrableOn (fun u => Real.exp (-(t * (L + u)))) (Ioi (-L)) := by
  refine IntegrableOn.congr_fun
    (Integrable.const_mul (exp_neg_integrableOn_Ioi (-L) ht) (Real.exp (-(t * L))))
    (fun u _ => ?_) measurableSet_Ioi
  show Real.exp (-(t * L)) * Real.exp (-t * u) = Real.exp (-(t * (L + u)))
  rw [← Real.exp_add]; congr 1; ring

theorem abelWeight_le_one {t L u : ℝ} (ht : 0 ≤ t) (hu : -L < u) :
    Real.exp (-(t * (L + u))) ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (by linarith)))

theorem integrableOn_abelWeight_mul_sq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ}
    (ht : 0 ≤ t) (L : ℝ) :
    IntegrableOn (fun u => Real.exp (-(t * (L + u))) * F u ^ 2) (Ioi (-L)) := by
  refine hF.sq.integrableOn.mono' ((by fun_prop : Measurable fun u : ℝ =>
    Real.exp (-(t * (L + u)))).mul (hF.meas.pow_const 2)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (abelWeight_le_one ht hu)

/-- Cauchy–Schwarz for an Abel integral: `(∫ e^{−t(L+u)} F)² ≤ t^{−1} ∫ e^{−t(L+u)} F²`. -/
theorem sq_abelHead_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 < t)
    (L : ℝ) :
    abelHead F t L ^ 2 ≤ (1 / t) * ∫ u in Ioi (-L), Real.exp (-(t * (L + u))) * F u ^ 2 := by
  have e1 : ∀ u : ℝ, Real.exp (-(t * (L + u)) / 2) * (Real.exp (-(t * (L + u)) / 2) * F u) =
      Real.exp (-(t * (L + u))) * F u := fun u => by
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have e2 : ∀ u : ℝ, Real.exp (-(t * (L + u)) / 2) ^ 2 = Real.exp (-(t * (L + u))) :=
    fun u => by rw [sq, ← Real.exp_add]; congr 1; ring
  have e3 : ∀ u : ℝ, (Real.exp (-(t * (L + u)) / 2) * F u) ^ 2 =
      Real.exp (-(t * (L + u))) * F u ^ 2 := fun u => by rw [mul_pow, e2]
  have i1 : Integrable (fun u => Real.exp (-(t * (L + u)) / 2) ^ 2)
      (volume.restrict (Ioi (-L))) := by
    simp only [e2]; exact integrableOn_abelWeight ht L
  have i2 : Integrable (fun u => (Real.exp (-(t * (L + u)) / 2) * F u) ^ 2)
      (volume.restrict (Ioi (-L))) := by
    simp only [e3]; exact integrableOn_abelWeight_mul_sq hF ht.le L
  have h := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := volume.restrict (Ioi (-L)))
    (f := fun u => Real.exp (-(t * (L + u)) / 2))
    (g := fun u => Real.exp (-(t * (L + u)) / 2) * F u)
    (by fun_prop : Measurable fun u : ℝ => Real.exp (-(t * (L + u)) / 2)).aestronglyMeasurable
    ((by fun_prop : Measurable fun u : ℝ => Real.exp (-(t * (L + u)) / 2)).mul
      hF.meas).aestronglyMeasurable i1 i2
  simp only [e1, e2, e3] at h
  rw [integral_abelWeight ht L] at h
  exact h

/-- For `t ≥ 8` the Abel weight on `u > −L` is at most the confinement weight `e^{−8L} e^{−8u}`. -/
theorem integral_abelWeight_mul_sq_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ}
    (ht : 8 ≤ t) (L : ℝ) :
    ∫ u in Ioi (-L), Real.exp (-(t * (L + u))) * F u ^ 2 ≤
      Real.exp (-(8 * L)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  rw [← integral_const_mul]
  refine (setIntegral_mono_on (integrableOn_abelWeight_mul_sq hF (by linarith) L)
    (hF.exponential.const_mul _).integrableOn measurableSet_Ioi fun u hu => ?_).trans
    (setIntegral_le_integral (hF.exponential.const_mul _) (Eventually.of_forall fun u =>
      mul_nonneg (Real.exp_pos _).le (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)))
  have hu' : 0 < L + u := by have : -L < u := hu; linarith
  have he : Real.exp (-(t * (L + u))) ≤ Real.exp (-(8 * L)) * Real.exp (-(8 * u)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr ht) hu'.le])
  calc Real.exp (-(t * (L + u))) * F u ^ 2
      ≤ Real.exp (-(8 * L)) * Real.exp (-(8 * u)) * F u ^ 2 :=
        mul_le_mul_of_nonneg_right he (sq_nonneg _)
    _ = Real.exp (-(8 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) := by ring

/-- The `F²`-mass seen by an Abel weight vanishes as `t → ∞`. -/
theorem tendsto_integral_abelWeight_mul_sq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (L : ℝ) :
    Tendsto (fun t : ℝ => ∫ u in Ioi (-L), Real.exp (-(t * (L + u))) * F u ^ 2) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (-L)))
    (l := atTop) (F := fun t u => Real.exp (-(t * (L + u))) * F u ^ 2) (f := fun _ => (0 : ℝ))
    (fun u => F u ^ 2)
    (Eventually.of_forall fun t => ((by fun_prop : Measurable fun u : ℝ =>
      Real.exp (-(t * (L + u)))).mul (hF.meas.pow_const 2)).aestronglyMeasurable)
    ((eventually_ge_atTop 0).mono fun t ht => (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => by
        rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
        exact mul_le_of_le_one_left (sq_nonneg _) (abelWeight_le_one ht hu)))
    hF.sq.integrableOn
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
      have hu' : 0 < L + u := by have : -L < u := hu; linarith
      have h1 : Tendsto (fun t : ℝ => t * (L + u)) atTop atTop := tendsto_id.atTop_mul_const hu'
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const (F u ^ 2)))
  simpa using h

/-- **The prime head decays faster than `t^{−½}`** for every profile of the domain. -/
theorem tendsto_sqrt_mul_primeHead_neg {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) * primeHead F (-(t : ℂ))) atTop (𝓝 0) := by
  have hroot : ∀ t : ℝ, 0 < t → ∀ L : ℝ, |Real.sqrt t * abelHead F t L| ≤
      Real.sqrt (∫ u in Ioi (-L), Real.exp (-(t * (L + u))) * F u ^ 2) := by
    intro t ht L
    rw [← Real.sqrt_sq_eq_abs, mul_pow, Real.sq_sqrt ht.le]
    refine Real.sqrt_le_sqrt ?_
    calc t * abelHead F t L ^ 2
        ≤ t * ((1 / t) * ∫ u in Ioi (-L), Real.exp (-(t * (L + u))) * F u ^ 2) :=
          mul_le_mul_of_nonneg_left (sq_abelHead_le hF ht L) ht.le
      _ = _ := by rw [← mul_assoc, mul_one_div_cancel ht.ne', one_mul]
  have hpt : ∀ n : ℕ, Tendsto (fun t : ℝ =>
      ((vonMangoldtAtom n * (Real.sqrt t * abelHead F t (Real.log n)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    intro n
    have h1 := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_integral_abelWeight_mul_sq hF (Real.log n))
    rw [Real.sqrt_zero] at h1
    have h2 := h1.const_mul (vonMangoldtAtom n)
    rw [mul_zero] at h2
    refine squeeze_zero_norm' (a := fun t => vonMangoldtAtom n * Real.sqrt
      (∫ u in Ioi (-Real.log n), Real.exp (-(t * (Real.log n + u))) * F u ^ 2))
      ((eventually_gt_atTop 0).mono fun t ht => ?_) h2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (atom_nonneg n)]
    exact mul_le_mul_of_nonneg_left (hroot t ht _) (atom_nonneg n)
  have hbd : ∀ t : ℝ, 8 ≤ t → ∀ n : ℕ,
      ‖((vonMangoldtAtom n * (Real.sqrt t * abelHead F t (Real.log n)) : ℝ) : ℂ)‖ ≤
        vonMangoldtAtom n * Real.exp (-4 * Real.log n) *
          Real.sqrt (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
    intro t ht n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (atom_nonneg n), mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hroot t (by linarith) _).trans ?_) (atom_nonneg n)
    calc Real.sqrt (∫ u in Ioi (-Real.log n), Real.exp (-(t * (Real.log n + u))) * F u ^ 2)
        ≤ Real.sqrt (Real.exp (-(8 * Real.log n)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u))) :=
          Real.sqrt_le_sqrt (integral_abelWeight_mul_sq_le hF ht _)
      _ = Real.exp (-4 * Real.log n) * Real.sqrt (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
          rw [Real.sqrt_mul (Real.exp_pos _).le, show Real.exp (-(8 * Real.log n)) =
            Real.exp (-4 * Real.log n) ^ 2 by rw [sq, ← Real.exp_add]; congr 1; ring,
            Real.sqrt_sq (Real.exp_pos _).le]
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (n : ℕ) =>
      ((vonMangoldtAtom n * (Real.sqrt t * abelHead F t (Real.log n)) : ℝ) : ℂ))
    (g := fun _ => (0 : ℂ))
    (bound := fun n => vonMangoldtAtom n * Real.exp (-4 * Real.log n) *
      Real.sqrt (∫ u, F u ^ 2 * Real.exp (-(8 * u))))
    ((summable_primeHead_damping (c := 4) (by norm_num)).mul_right _) hpt
    ((eventually_ge_atTop 8).mono fun t ht n => hbd t ht n)
  simp only [tsum_zero] at hlim
  refine hlim.congr fun t => ?_
  rw [primeHead_neg_ofReal, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  push_cast
  ring

/-! ## The leading term at regular profiles -/

/-- Translating to the prime point and rescaling: the scaled Abel integral is an exponential average
of `F` just right of `−L`. -/
theorem mul_abelHead_eq (F : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (L : ℝ) :
    t * abelHead F t L = ∫ s in Ioi (0 : ℝ), Real.exp (-s) * F (s / t - L) := by
  have h1 : abelHead F t L = ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * F (v - L) := by
    unfold abelHead
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
      ← integral_sub_right_eq_self ((Ioi (-L)).indicator
        fun u => Real.exp (-(t * (L + u))) * F u) L]
    congr 1
    funext v
    simp only [Set.indicator_apply, mem_Ioi, show L + (v - L) = v by ring]
    by_cases hv : 0 < v
    · rw [if_pos (show -L < v - L by linarith), if_pos hv]
    · rw [if_neg (show ¬ -L < v - L by intro h; exact hv (by linarith)), if_neg hv]
  have h2 := integral_comp_mul_left_Ioi (fun s => Real.exp (-s) * F (s / t - L)) 0 ht
  simp only [mul_zero, smul_eq_mul, mul_div_cancel_left₀ _ ht.ne'] at h2
  rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

theorem norm_abelIntegrand_le {F : ℝ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hbd : ∀ u, |F u| ≤ C * Real.exp (c * u)) {L t : ℝ} (ht : 2 * c ≤ t) {s : ℝ} (hs : 0 < s) :
    ‖Real.exp (-s) * F (s / t - L)‖ ≤ C * Real.exp (-(c * L)) * Real.exp (-(1 / 2) * s) := by
  have hC : 0 ≤ C := by
    have h0 := hbd 0
    rw [mul_zero, Real.exp_zero, mul_one] at h0
    exact (abs_nonneg _).trans h0
  have htpos : 0 < t := by linarith
  have hct : c / t ≤ 1 / 2 := by rw [div_le_iff₀ htpos]; linarith
  have hcs : c * (s / t) ≤ s / 2 := by
    calc c * (s / t) = c / t * s := by ring
      _ ≤ 1 / 2 * s := mul_le_mul_of_nonneg_right hct hs.le
      _ = s / 2 := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-s) * |F (s / t - L)| ≤ Real.exp (-s) * (C * Real.exp (c * (s / t - L))) :=
        mul_le_mul_of_nonneg_left (hbd _) (Real.exp_pos _).le
    _ = C * Real.exp (-s + c * (s / t) - c * L) := by
        rw [show -s + c * (s / t) - c * L = -s + c * (s / t - L) by ring, Real.exp_add]; ring
    _ ≤ C * Real.exp (-(c * L) + -(1 / 2) * s) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC
    _ = C * Real.exp (-(c * L)) * Real.exp (-(1 / 2) * s) := by rw [Real.exp_add]; ring

/-- At a point of right-continuity the scaled Abel integral tends to the value of `F`. -/
theorem tendsto_mul_abelHead {F : ℝ → ℝ} (hFm : Measurable F) {C c : ℝ} (hc : 0 < c)
    (hbd : ∀ u, |F u| ≤ C * Real.exp (c * u)) {L : ℝ}
    (hcont : ContinuousWithinAt F (Ioi (-L)) (-L)) :
    Tendsto (fun t : ℝ => t * abelHead F t L) atTop (𝓝 (F (-L))) := by
  have hl : ∀ s : ℝ, 0 < s → Tendsto (fun t : ℝ => Real.exp (-s) * F (s / t - L)) atTop
      (𝓝 (Real.exp (-s) * F (-L))) := by
    intro s hs
    have h0 : Tendsto (fun t : ℝ => s / t - L) atTop (𝓝[>] (-L)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, (eventually_gt_atTop 0).mono fun t ht => ?_⟩
      · simpa using (tendsto_const_nhds.div_atTop tendsto_id).sub_const L
      · show -L < s / t - L
        have := div_pos hs ht
        linarith
    exact (hcont.tendsto.comp h0).const_mul _
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (l := atTop) (F := fun t s => Real.exp (-s) * F (s / t - L))
    (f := fun s => Real.exp (-s) * F (-L))
    (fun s => C * Real.exp (-(c * L)) * Real.exp (-(1 / 2) * s))
    (Eventually.of_forall fun t => ((by fun_prop : Measurable fun s : ℝ => Real.exp (-s)).mul
      (hFm.comp (by fun_prop : Measurable fun s : ℝ => s / t - L))).aestronglyMeasurable)
    ((eventually_ge_atTop (2 * c)).mono fun t ht => (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs => norm_abelIntegrand_le hc hbd ht hs))
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => hl s hs))
  simp only [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul] at h
  exact h.congr' ((eventually_gt_atTop 0).mono fun t ht => (mul_abelHead_eq F ht L).symm)

theorem abs_mul_abelHead_le {F : ℝ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hbd : ∀ u, |F u| ≤ C * Real.exp (c * u)) {t : ℝ} (ht : 2 * c ≤ t) (L : ℝ) :
    |t * abelHead F t L| ≤
      C * Real.exp (-(c * L)) * ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 2) * s) := by
  have htpos : 0 < t := by linarith
  rw [mul_abelHead_eq F htpos L, ← integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs =>
      norm_abelIntegrand_le hc hbd ht hs))

/-- **The leading term of the prime head.** If `F` is right-continuous at every prime point and
`|F(u)| ≤ C e^{cu}` with `c > ½`, then `t · ŜF(−t) → Σ_n Λ(n) n^{−½} F(−log n)`. -/
theorem tendsto_mul_primeHead_neg_of_regular {F : ℝ → ℝ} (hFm : Measurable F) {C c : ℝ}
    (hc : 1 / 2 < c) (hbd : ∀ u, |F u| ≤ C * Real.exp (c * u))
    (hcont : ∀ n : ℕ, ContinuousWithinAt F (Ioi (-Real.log n)) (-Real.log n)) :
    Tendsto (fun t : ℝ => (t : ℂ) * primeHead F (-(t : ℂ))) atTop
      (𝓝 (∑' n : ℕ, ((vonMangoldtAtom n * F (-Real.log n) : ℝ) : ℂ))) := by
  have hc0 : 0 < c := by linarith
  have hpt : ∀ n : ℕ, Tendsto (fun t : ℝ =>
      ((vonMangoldtAtom n * (t * abelHead F t (Real.log n)) : ℝ) : ℂ))
      atTop (𝓝 ((vonMangoldtAtom n * F (-Real.log n) : ℝ) : ℂ)) := fun n =>
    (Complex.continuous_ofReal.tendsto _).comp
      ((tendsto_mul_abelHead hFm hc0 hbd (hcont n)).const_mul (vonMangoldtAtom n))
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (n : ℕ) => ((vonMangoldtAtom n * (t * abelHead F t (Real.log n)) : ℝ) : ℂ))
    (bound := fun n : ℕ => vonMangoldtAtom n * Real.exp (-c * Real.log n) *
      (C * ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 2) * s)))
    ((summable_primeHead_damping hc).mul_right _) hpt
    ((eventually_ge_atTop (2 * c)).mono fun t ht n => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (atom_nonneg n)]
      calc vonMangoldtAtom n * |t * abelHead F t (Real.log n)|
          ≤ vonMangoldtAtom n * (C * Real.exp (-(c * Real.log n)) *
              ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 2) * s)) :=
            mul_le_mul_of_nonneg_left (abs_mul_abelHead_le hc0 hbd ht _) (atom_nonneg n)
        _ = _ := by rw [neg_mul]; ring)
  refine hlim.congr fun t => ?_
  rw [primeHead_neg_ofReal, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  push_cast
  ring

/-! ## The Lévy head -/

theorem tendsto_abelResolvent {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun t : ℝ => t / (r + t)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => r / (r + t)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ r tendsto_id)
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  rw [sub_zero] at h1
  refine h1.congr' ((eventually_gt_atTop 0).mono fun t ht => ?_)
  have hd : r + t ≠ 0 := by linarith
  rw [eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd]
  ring

/-- At `p = −t` the scaled Lévy head is the Abel mean `Σ_k LF(2k+½) · t/(2k+½+t)` of the trivial-zero
moments. -/
theorem hasSum_mul_levyHeadTerm_neg {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ}
    (ht : 0 < t) :
    HasSum (fun k : ℕ => negativeHalfLineLaplace (cx F) (2 * k + 1 / 2) *
      ((t / (2 * k + 1 / 2 + t) : ℝ) : ℂ)) ((t : ℂ) * levyHeadTerm F (-(t : ℂ))) := by
  have h := (hasSum_levyHead_resolvents hF (p := -(t : ℂ))
    (by simp only [neg_re, ofReal_re]; linarith)).mul_left (t : ℂ)
  refine h.congr_fun fun k => ?_
  rw [sub_neg_eq_add]
  push_cast
  ring

/-- **Leading term of the Lévy head.** If the trivial-zero moments `LF(2k+½)` are absolutely
summable, then `t · JF(−t) → Σ_k LF(2k+½)`. -/
theorem tendsto_mul_levyHeadTerm_neg {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hs : Summable fun k : ℕ => ‖negativeHalfLineLaplace (cx F) (2 * k + 1 / 2)‖) :
    Tendsto (fun t : ℝ => (t : ℂ) * levyHeadTerm F (-(t : ℂ))) atTop
      (𝓝 (∑' k : ℕ, negativeHalfLineLaplace (cx F) (2 * k + 1 / 2))) := by
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (k : ℕ) => negativeHalfLineLaplace (cx F) (2 * k + 1 / 2) *
      ((t / (2 * k + 1 / 2 + t) : ℝ) : ℂ))
    (g := fun k : ℕ => negativeHalfLineLaplace (cx F) (2 * k + 1 / 2)) hs
    (fun k => by
      have h := (Complex.continuous_ofReal.tendsto _).comp
        (tendsto_abelResolvent (r := 2 * (k : ℝ) + 1 / 2) (by positivity))
      simpa using h.const_mul (negativeHalfLineLaplace (cx F) (2 * k + 1 / 2)))
    ((eventually_gt_atTop 0).mono fun t ht k => by
      have hd : 0 < 2 * (k : ℝ) + 1 / 2 + t := by
        have := Nat.cast_nonneg (α := ℝ) k; linarith
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos ht hd).le]
      exact mul_le_of_le_one_right (norm_nonneg _) ((div_le_one hd).mpr (by linarith)))
  exact hlim.congr' ((eventually_gt_atTop 0).mono fun t ht =>
    (hasSum_mul_levyHeadTerm_neg hF ht).tsum_eq)

/-- The trivial-zero weight `LF(½) · LF(2k + ½)`, oriented by the half-charge. -/
def levyWallWeight (F : ℝ → ℝ) (k : ℕ) : ℝ :=
  (negativeHalfLineLaplace (cx F) (1 / 2)).re *
    (negativeHalfLineLaplace (cx F) (2 * k + 1 / 2)).re

theorem hasSum_oriented_mul_levyHeadTerm_neg {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => levyWallWeight F k * (t / (2 * k + 1 / 2 + t)))
      ((negativeHalfLineLaplace (cx F) (1 / 2)).re *
        ((t : ℂ) * levyHeadTerm F (-(t : ℂ))).re) := by
  have h := (Complex.reCLM.hasSum (hasSum_mul_levyHeadTerm_neg hF ht)).mul_left
    (negativeHalfLineLaplace (cx F) (1 / 2)).re
  refine h.congr_fun fun k => ?_
  simp only [Complex.reCLM_apply, Complex.re_mul_ofReal, levyWallWeight]
  ring

theorem criticalState_levyWallWeight_pos {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (k : ℕ) :
    0 < levyWallWeight F k := by
  have h := criticalState_laplace_half_mul_pos hW hthreshold hF (s := 2 * k + 1 / 2)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hc : ((2 * (k : ℝ) + 1 / 2 : ℝ) : ℂ) = 2 * (k : ℂ) + 1 / 2 := by push_cast; ring
  rw [hc] at h
  exact h

/-- **The critical state's Lévy head seen from the left.** Every trivial-zero weight
`LF(½) LF(2k+½)` of the state is positive, so the oriented scaled head
`LF(½) · t · JF(−t)` either tends to the positive mass `Σ_k LF(½) LF(2k+½)` or diverges to `+∞`:
`JF(−t)` is never `o(1/t)`. -/
theorem criticalState_levyHead_asymptotic {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (Summable (levyWallWeight F) ∧ 0 < ∑' k, levyWallWeight F k ∧
      Tendsto (fun t : ℝ => (negativeHalfLineLaplace (cx F) (1 / 2)).re *
        ((t : ℂ) * levyHeadTerm F (-(t : ℂ))).re) atTop (𝓝 (∑' k, levyWallWeight F k))) ∨
    (¬ Summable (levyWallWeight F) ∧
      Tendsto (fun t : ℝ => (negativeHalfLineLaplace (cx F) (1 / 2)).re *
        ((t : ℂ) * levyHeadTerm F (-(t : ℂ))).re) atTop atTop) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hpos := criticalState_levyWallWeight_pos hW hthreshold hF
  have hden : ∀ (t : ℝ), 0 < t → ∀ k : ℕ, 0 < 2 * (k : ℝ) + 1 / 2 + t := fun t ht k => by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have he : (fun t : ℝ => ∑' k, levyWallWeight F k * (t / (2 * k + 1 / 2 + t))) =ᶠ[atTop]
      fun t => (negativeHalfLineLaplace (cx F) (1 / 2)).re *
        ((t : ℂ) * levyHeadTerm F (-(t : ℂ))).re :=
    (eventually_gt_atTop 0).mono fun t ht => (hasSum_oriented_mul_levyHeadTerm_neg hd ht).tsum_eq
  by_cases hs : Summable (levyWallWeight F)
  · refine Or.inl ⟨hs, hs.tsum_pos (fun k => (hpos k).le) 0 (hpos 0), ?_⟩
    refine (tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (t : ℝ) (k : ℕ) => levyWallWeight F k * (t / (2 * k + 1 / 2 + t)))
      (g := levyWallWeight F) (bound := levyWallWeight F) hs (fun k => ?_)
      ((eventually_gt_atTop 0).mono fun t ht k => ?_)).congr' he
    · simpa using (tendsto_abelResolvent (r := 2 * (k : ℝ) + 1 / 2) (by positivity)).const_mul
        (levyWallWeight F k)
    · rw [Real.norm_of_nonneg (mul_nonneg (hpos k).le (div_pos ht (hden t ht k)).le)]
      exact mul_le_of_le_one_right (hpos k).le ((div_le_one (hden t ht k)).mpr (by linarith))
  · refine Or.inr ⟨hs, (tendsto_atTop.mpr fun C => ?_).congr' he⟩
    have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun k => (hpos k).le).mp hs
    obtain ⟨N, hN⟩ := (hdiv.eventually_gt_atTop C).exists
    have hfin : Tendsto (fun t : ℝ => ∑ k ∈ Finset.range N,
        levyWallWeight F k * (t / (2 * k + 1 / 2 + t))) atTop
        (𝓝 (∑ k ∈ Finset.range N, levyWallWeight F k)) := by
      have := tendsto_finsetSum (Finset.range N) fun k _ =>
        (tendsto_abelResolvent (r := 2 * (k : ℝ) + 1 / 2) (by positivity)).const_mul
          (levyWallWeight F k)
      simpa using this
    filter_upwards [hfin.eventually (lt_mem_nhds hN), eventually_gt_atTop 0] with t h1 h2
    exact h1.le.trans (sum_le_hasSum _ (fun k _ => mul_nonneg (hpos k).le
      (div_pos h2 (hden t h2 k)).le)
      (hasSum_oriented_mul_levyHeadTerm_neg hd h2).summable.hasSum)

#print axioms tendsto_sqrt_mul_primeHead_neg
#print axioms tendsto_mul_primeHead_neg_of_regular
#print axioms tendsto_mul_levyHeadTerm_neg
#print axioms criticalState_levyHead_asymptotic

end GaloisForLFunctions.ExclusionOfTheCriticalState
