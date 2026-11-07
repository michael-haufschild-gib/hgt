import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePhysicalCollarHasBoundedExponentialMass
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeShiftsAreInfinitesimalInTheExponentialWeight

/-!
# Unrestricted atomic Gårding fails and collar atomic Gårding holds

At a fixed critical ratio `R = lim c_N⁸ / log N > 0`, the unrestricted atomic Gårding inequality
`Q(U) + B_R ‖U‖₂² ≥ a_R ∫ U(y)² e^{−8y} dy` (`a_R > 0`) on `(conductorSubspace 1 N)ᗮ` is false:
the unit-norm pole-orthogonal deep difference `z_N = (e_1 − √2 e_2) / √3` sits at `y ≈ −log N`,
where its Weil energy is `O(log N)` in unit-`L²` normalization while its eighth-power exponential
mass is `≍ N⁸` (`not_unrestricted_atomic_garding_on_poleOrthogonal`,
`not_unrestricted_unitL2_atomic_garding_on_poleOrthogonal`).

On the overlapping top collar `Ioc (N / linearDefectCutoff c) N`, by contrast, atomic Gårding holds
unconditionally at every critical ratio `R > 0` (`exists_collar_atomic_garding_below_ratio`,
`exists_collar_atomic_garding_along_critical_curve`). Interpolating the Lévy kernel between its
`H¹` control near `0` and its `L²` control away from `0` (`levyEnergy_le_interpolated`) upgrades the
dyadic shell commutator from `O(c G S)` to `O((c² / N) G S)` while keeping all shell partition and
low-frequency Gamma costs in pure `L²` norm (`exists_top_archForm_dyadic_seventh_reserve_garding`).
Combining this archimedean reserve with `normalized_tail_exponential_mass_le` and exponential
absorption of the prime and `sinh` pole terms yields collar Gårding with simultaneous control of
both `topCollarSeventhMass` and `∫ U² e^{−8y}`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23
open scoped Classical BigOperators RealInnerProductSpace CompactlySupported

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics
  ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory

/-! ### 1. Homogeneity and exponential absorption of the prime and pole forms -/

theorem levyEnergy_const_mul (α : ℝ) (f : ℝ → ℝ) :
    levyEnergy (fun u => α * f u) = α ^ 2 * levyEnergy f := by
  unfold levyEnergy
  have hpt : ∀ y : ℝ, archLevyDensity y * (∫ u, (α * f u - α * f (u + y)) ^ 2) =
      α ^ 2 * (archLevyDensity y * ∫ u, (f u - f (u + y)) ^ 2) := fun y => by
    have hsub : (fun u => (α * f u - α * f (u + y)) ^ 2) =
        fun u => α ^ 2 * (f u - f (u + y)) ^ 2 := funext fun u => by ring
    rw [hsub, integral_const_mul]
    ring
  simp_rw [hpt]
  exact integral_const_mul (α ^ 2) _

theorem primeSum_const_mul (α : ℝ) (f : ℝ → ℝ) :
    primeSum (fun u => α * f u) = α ^ 2 * primeSum f := by
  unfold primeSum
  have hterm : ∀ n : ℕ,
      vonMangoldtAtom n * ((∫ y, (α * f y) * (α * f (y - Real.log n))) +
        ∫ y, (α * f y) * (α * f (y + Real.log n))) =
      α ^ 2 * (vonMangoldtAtom n * ((∫ y, f y * f (y - Real.log n)) +
        ∫ y, f y * f (y + Real.log n))) := fun n => by
    have h1 : (fun y => (α * f y) * (α * f (y - Real.log n))) =
        fun y => α ^ 2 * (f y * f (y - Real.log n)) := funext fun y => by ring
    have h2 : (fun y => (α * f y) * (α * f (y + Real.log n))) =
        fun y => α ^ 2 * (f y * f (y + Real.log n)) := funext fun y => by ring
    rw [h1, h2, integral_const_mul, integral_const_mul]
    ring
  simp_rw [hterm]
  exact tsum_mul_left

theorem coshHalfMoment_const_mul (α : ℝ) (f : ℝ → ℝ) :
    coshHalfMoment (fun u => α * f u) = α * coshHalfMoment f := by
  unfold coshHalfMoment
  have h : (fun u => α * f u * Real.cosh (u / 2)) =
      fun u => α * (f u * Real.cosh (u / 2)) := funext fun u => by ring
  rw [h, integral_const_mul]

theorem sinhHalfMoment_const_mul (α : ℝ) (f : ℝ → ℝ) :
    sinhHalfMoment (fun u => α * f u) = α * sinhHalfMoment f := by
  unfold sinhHalfMoment
  have h : (fun u => α * f u * Real.sinh (u / 2)) =
      fun u => α * (f u * Real.sinh (u / 2)) := funext fun u => by ring
  rw [h, integral_const_mul]

theorem archForm_const_mul {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (α : ℝ) :
    archForm (fun u => α * f u) = α ^ 2 * archForm f := by
  have hαf : ContDiff ℝ 2 (fun u => α * f u) := contDiff_const.mul hf
  have hαfc : HasCompactSupport (fun u => α * f u) := hfc.mul_left
  have hsq : (∫ u, (α * f u) ^ 2) = α ^ 2 * ∫ u, f u ^ 2 := by
    simp_rw [mul_pow]
    exact integral_const_mul (α ^ 2) _
  rw [archForm_eq_levyEnergy hαf hαfc, archForm_eq_levyEnergy hf hfc, levyEnergy_const_mul, hsq]
  ring

theorem weilQuad_const_mul {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (α : ℝ) :
    weilQuad (fun u => α * f u) = α ^ 2 * weilQuad f := by
  have hαf : ContDiff ℝ 2 (fun u => α * f u) := contDiff_const.mul hf
  have hαfc : HasCompactSupport (fun u => α * f u) := hfc.mul_left
  have hsq : (∫ u, (α * f u) ^ 2) = α ^ 2 * ∫ u, f u ^ 2 := by
    simp_rw [mul_pow]
    exact integral_const_mul (α ^ 2) _
  rw [weilQuad_eq hαf hαfc, weilQuad_eq hf hfc, hsq, levyEnergy_const_mul, primeSum_const_mul,
    coshHalfMoment_const_mul, sinhHalfMoment_const_mul]
  ring

theorem primeSum_comp_add_right (H : ℝ → ℝ) (w : ℝ) :
    primeSum (fun u => H (u + w)) = primeSum H := by
  unfold primeSum
  congr 1
  ext n
  congr 1
  have h1 : (∫ y, H (y + w) * H (y - Real.log n + w)) =
      ∫ y, H y * H (y - Real.log n) := by
    have heq : (fun y => H (y + w) * H (y - Real.log n + w)) =
        fun y => (fun u => H u * H (u - Real.log n)) (y + w) :=
      funext fun y => by dsimp only; congr 2; ring
    rw [heq]
    exact integral_add_right_eq_self (fun u => H u * H (u - Real.log n)) w
  have h2 : (∫ y, H (y + w) * H (y + Real.log n + w)) =
      ∫ y, H y * H (y + Real.log n) := by
    have heq : (fun y => H (y + w) * H (y + Real.log n + w)) =
        fun y => (fun u => H u * H (u + Real.log n)) (y + w) :=
      funext fun y => by dsimp only; congr 2; ring
    rw [heq]
    exact integral_add_right_eq_self (fun u => H u * H (u + Real.log n)) w
  rw [h1, h2]

/-- Any compactly supported continuous source vanishing above `1` has its prime form absorbed by
an arbitrarily small fraction of `∫ H(y)² e^{−8y} dy` plus an `L²` remainder. -/
theorem exists_abs_primeSum_le_exponential_mass_of_le_one {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {H : ℝ → ℝ}, Continuous H → HasCompactSupport H →
      (∀ y, 1 < y → H y = 0) →
      |primeSum H| ≤ ε * (∫ y, H y ^ 2 * Real.exp (-(8 * y))) + B * ∫ y, H y ^ 2 := by
  have hε' : 0 < ε / Real.exp 8 := div_pos hε (Real.exp_pos 8)
  obtain ⟨B, hB0, hB⟩ := exists_abs_primeSum_le_exponential_mass hε'
  refine ⟨B, hB0, ?_⟩
  intro H hH hHc hs
  let H₁ : ℝ → ℝ := fun t => H (t + 1)
  have hH₁ : Continuous H₁ := hH.comp (continuous_add_const 1)
  have hH₁c : HasCompactSupport H₁ := hHc.comp_homeomorph (Homeomorph.addRight 1)
  have hs₁ : ∀ t, 0 < t → H₁ t = 0 := fun t ht => hs (t + 1) (by linarith)
  have hbound := hB hH₁ hH₁c hs₁
  have hp : primeSum H₁ = primeSum H := primeSum_comp_add_right H 1
  have hsq : (∫ t, H₁ t ^ 2) = ∫ y, H y ^ 2 :=
    integral_add_right_eq_self (fun y => H y ^ 2) 1
  have hexp : (∫ t, H₁ t ^ 2 * Real.exp (-(8 * t))) =
      Real.exp 8 * ∫ y, H y ^ 2 * Real.exp (-(8 * y)) := by
    have hpt : (fun t => H₁ t ^ 2 * Real.exp (-(8 * t))) =
        fun t => Real.exp 8 * ((fun y => H y ^ 2 * Real.exp (-(8 * y))) (t + 1)) := by
      funext t
      dsimp only [H₁]
      have he : Real.exp (-(8 * t)) = Real.exp 8 * Real.exp (-(8 * (t + 1))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    rw [hpt, integral_const_mul,
      integral_add_right_eq_self (fun y => H y ^ 2 * Real.exp (-(8 * y))) 1]
  rw [hp, hsq, hexp] at hbound
  have hcancel : ε / Real.exp 8 * (Real.exp 8 * ∫ y, H y ^ 2 * Real.exp (-(8 * y))) =
      ε * ∫ y, H y ^ 2 * Real.exp (-(8 * y)) := by
    field_simp [(Real.exp_pos 8).ne']
  linarith only [hbound, hcancel]

private theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have he1 : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

/-- Any compactly supported continuous source vanishing above `1` has `2 sinhHalfMoment(U)²`
absorbed by `ε ∫ U(u)² e^{−8u} du + B ∫ U(u)² du`. -/
theorem exists_two_mul_sinhHalfMoment_sq_le_exponential_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {U : ℝ → ℝ}, Continuous U → HasCompactSupport U →
      (∀ u, 1 < u → U u = 0) →
      2 * sinhHalfMoment U ^ 2 ≤
        ε * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) + B * ∫ u, U u ^ 2 := by
  let B₀ : ℝ := max 6 (2 / ε)
  have hB₆ : 6 ≤ B₀ := le_max_left _ _
  have hBε : 2 / ε ≤ B₀ := le_max_right _ _
  have hB0 : 0 < B₀ := by linarith
  have hεB : 1 ≤ (ε / 2) * B₀ := by
    have hm := (div_le_iff₀ hε).mp hBε
    linarith
  refine ⟨B₀, hB0.le, ?_⟩
  intro U hU hUc hs
  let W : ℝ → ℝ := fun u => (ε / 2) * Real.exp (-(8 * u)) + B₀
  have hW_pos : ∀ u, 0 < W u := fun u => by dsimp only [W]; positivity
  let Φ : ℝ → ℝ := fun u =>
    (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u +
      (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 6 : ℝ)) u
  have hΦ_bound : ∀ u, u ≤ 1 → Real.sinh (u / 2) ^ 2 / W u ≤ Φ u := by
    intro u hu1
    by_cases hu0 : u ≤ 0
    · have hind : Φ u = (1 / 2 : ℝ) * Real.exp (3 * u) := by
        dsimp only [Φ]
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr hu0),
          Set.indicator_of_notMem (fun h => not_lt.mpr hu0 h.1), add_zero]
      rw [hind]
      have hsinh : Real.sinh (u / 2) ^ 2 ≤ Real.exp (-u) := by
        have h1 : Real.exp (u / 2) ≤ Real.exp (-(u / 2)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : |Real.sinh (u / 2)| ≤ Real.exp (-(u / 2)) := by
          rw [Real.sinh_eq, abs_div, abs_two,
            abs_of_nonpos (by linarith : Real.exp (u / 2) - Real.exp (-(u / 2)) ≤ 0)]
          linarith [Real.exp_pos (u / 2)]
        calc Real.sinh (u / 2) ^ 2 = |Real.sinh (u / 2)| ^ 2 := (sq_abs _).symm
          _ ≤ Real.exp (-(u / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
          _ = Real.exp (-u) := by
              rw [← Real.exp_nat_mul]
              congr 1
              push_cast
              ring
      have hW_lo : 2 * Real.exp (-(4 * u)) ≤ W u := by
        let a := Real.sqrt (ε / 2) * Real.exp (-(4 * u))
        let b := Real.sqrt B₀
        have ha2 : a ^ 2 = (ε / 2) * Real.exp (-(8 * u)) := by
          dsimp only [a]
          rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
        have hb2 : b ^ 2 = B₀ := Real.sq_sqrt hB0.le
        have hab : 1 ≤ Real.sqrt (ε / 2) * Real.sqrt B₀ := by
          rw [← Real.sqrt_mul (by positivity)]
          exact Real.one_le_sqrt.mpr hεB
        have hprod : Real.exp (-(4 * u)) ≤ a * b := by
          have : a * b = (Real.sqrt (ε / 2) * Real.sqrt B₀) * Real.exp (-(4 * u)) := by
            dsimp only [a, b]; ring
          rw [this]
          exact le_mul_of_one_le_left (Real.exp_pos _).le hab
        have hsq0 := sq_nonneg (a - b)
        dsimp only [W]
        nlinarith only [ha2, hb2, hprod, hsq0]
      calc Real.sinh (u / 2) ^ 2 / W u
          ≤ Real.exp (-u) / (2 * Real.exp (-(4 * u))) :=
            div_le_div₀ (Real.exp_pos (-u)).le hsinh (by positivity) hW_lo
        _ = (1 / 2 : ℝ) * Real.exp (3 * u) := by
            rw [div_mul_eq_div_div_swap, ← Real.exp_sub]
            ring_nf
    · push Not at hu0
      have hind : Φ u = 1 / 6 := by
        have hnot : u ∉ Set.Iic (0 : ℝ) := fun h => not_le.mpr hu0 (Set.mem_Iic.mp h)
        dsimp only [Φ]
        rw [Set.indicator_of_notMem hnot,
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu0, hu1⟩), zero_add]
      rw [hind]
      have hsinh1 : Real.sinh (u / 2) ^ 2 ≤ 1 := by
        have he_up : Real.exp (u / 2) ≤ 2 :=
          (Real.exp_le_exp.mpr (by linarith : u / 2 ≤ 1 / 2)).trans exp_half_le_two
        have hs0 : 0 ≤ Real.sinh (u / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
        have hs1 : Real.sinh (u / 2) ≤ 1 := by
          rw [Real.sinh_eq]
          linarith [Real.exp_pos (-(u / 2))]
        nlinarith
      have hW6 : 6 ≤ W u := by
        dsimp only [W]
        linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 2) (Real.exp_pos (-(8 * u))).le, hB₆]
      exact div_le_div₀ zero_le_one hsinh1 (by norm_num) hW6
  have hi_Iic : Integrable ((Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v))) := by
    have hneg : IntegrableOn (fun v : ℝ => (1 / 2 : ℝ) * Real.exp (-(3 * v))) (Set.Ioi 0) := by
      have h1 := integrableOn_exp_mul_Ioi (by norm_num : -(3 : ℝ) < 0) 0
      change Integrable _ _
      simpa only [neg_mul] using h1.const_mul (1 / 2 : ℝ)
    have hcomp : Integrable (fun v : ℝ =>
        (Set.Ioi (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (-(3 * x))) (-v)) :=
      (hneg.integrable_indicator measurableSet_Ioi).comp_neg
    refine hcomp.congr ?_
    have hsub : {v : ℝ | ¬((Set.Ioi (0 : ℝ)).indicator
        (fun x => (1 / 2 : ℝ) * Real.exp (-(3 * x))) (-v) =
        (Set.Iic (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (3 * x)) v)} ⊆ {(0 : ℝ)} := by
      intro v hv
      by_contra hne
      apply hv
      rcases lt_trichotomy v 0 with hlt | rfl | hgt
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr (neg_pos.mpr hlt)),
          Set.indicator_of_mem (Set.mem_Iic.mpr hlt.le)]
        ring_nf
      · exact (hne rfl).elim
      · rw [Set.indicator_of_notMem (fun h => by simp at h; linarith),
          Set.indicator_of_notMem (fun h => by simp at h; linarith)]
    exact ae_iff.mpr (measure_mono_null hsub (measure_singleton 0))
  have hi_Ioc : Integrable ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 6 : ℝ))) :=
    (integrableOn_const (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hiΦ : Integrable Φ := hi_Iic.add hi_Ioc
  have hint_Φ : ∫ u, Φ u ≤ 1 / 2 := by
    have h1 : (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u) =
        1 / 6 := by
      have heq : (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u) =
          ∫ v in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * Real.exp (-(3 : ℝ) * v) := by
        rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
          (MeasurableEquiv.neg ℝ).measurableEmbedding
          (fun u => (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u)]
        have hae : (fun v : ℝ =>
            (Set.Iic (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (3 * x)) (-v)) =ᵐ[volume]
            (Set.Ioi (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (-(3 : ℝ) * v)) := by
          have hsub : {v : ℝ | ¬((Set.Iic (0 : ℝ)).indicator
              (fun x => (1 / 2 : ℝ) * Real.exp (3 * x)) (-v) =
              (Set.Ioi (0 : ℝ)).indicator (fun x => (1 / 2 : ℝ) * Real.exp (-(3 : ℝ) * x)) v)} ⊆
              {(0 : ℝ)} := by
            intro v hv
            by_contra hne
            apply hv
            rcases lt_trichotomy v 0 with hlt | rfl | hgt
            · rw [Set.indicator_of_notMem (fun h => by simp at h; linarith),
                Set.indicator_of_notMem (fun h => by simp at h; linarith)]
            · exact (hne rfl).elim
            · rw [Set.indicator_of_mem (by simp; linarith),
                Set.indicator_of_mem (Set.mem_Ioi.mpr hgt)]
              ring_nf
          exact ae_iff.mpr (measure_mono_null hsub (measure_singleton 0))
        rw [integral_congr_ae hae, MeasureTheory.integral_indicator measurableSet_Ioi]
      rw [heq, integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(3 : ℝ) < 0) 0]
      norm_num
    have h2 : (∫ u, (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 6 : ℝ)) u) = 1 / 6 := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Ioc_of_le zero_le_one]
      norm_num
    have hadd : ∫ u, Φ u =
        (∫ u, (Set.Iic (0 : ℝ)).indicator (fun v => (1 / 2 : ℝ) * Real.exp (3 * v)) u) +
          ∫ u, (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 6 : ℝ)) u :=
      integral_add hi_Iic hi_Ioc
    linarith
  have hU2c : HasCompactSupport (fun u => U u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun u hu => by change U u = 0 at hu; change U u ^ 2 = 0; rw [hu]; norm_num
  have hi8 : Integrable (fun u => U u ^ 2 * Real.exp (-(8 * u))) :=
    ((hU.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hU2c.mul_right
  have hi0 : Integrable (fun u => U u ^ 2) :=
    (hU.pow 2).integrable_of_hasCompactSupport hU2c
  have hiUW : Integrable (fun u => U u ^ 2 * W u) :=
    ((hU.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hU2c.mul_right
  have hiUS : Integrable (fun u => U u * Real.sinh (u / 2)) :=
    (hU.mul (by fun_prop)).integrable_of_hasCompactSupport hUc.mul_right
  set A := ∫ u, U u ^ 2 * W u
  have hA0 : 0 ≤ A := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (hW_pos u).le
  have hquad : ∀ t : ℝ, 0 ≤ A * (t * t) + 2 * sinhHalfMoment U * t + ∫ u, Φ u := fun t => by
    have hpt : ∀ u : ℝ, 0 ≤ (t * t) * (U u ^ 2 * W u) + 2 * t * (U u * Real.sinh (u / 2)) + Φ u := by
      intro u
      by_cases hu1 : u ≤ 1
      · have hw0 := hW_pos u
        have hsw : Real.sqrt (W u) ≠ 0 := (Real.sqrt_pos.mpr hw0).ne'
        have hsq := sq_nonneg (t * U u * Real.sqrt (W u) + Real.sinh (u / 2) / Real.sqrt (W u))
        have hexp_sq : (t * U u * Real.sqrt (W u) + Real.sinh (u / 2) / Real.sqrt (W u)) ^ 2 =
            (t * t) * (U u ^ 2 * W u) + 2 * t * (U u * Real.sinh (u / 2)) +
              Real.sinh (u / 2) ^ 2 / W u := by
          have h1 : Real.sqrt (W u) ^ 2 = W u := Real.sq_sqrt hw0.le
          field_simp [hsw]
          rw [h1]
          ring
        linarith only [hsq, hexp_sq, hΦ_bound u hu1]
      · push Not at hu1
        have hUu : U u = 0 := hs u hu1
        have hΦ0 : Φ u = 0 := by
          dsimp only [Φ]
          rw [Set.indicator_of_notMem (fun h => by simp at h; linarith),
            Set.indicator_of_notMem (fun h => by simp at h; linarith), add_zero]
        rw [hUu, hΦ0]
        norm_num
    have hint_nn : 0 ≤ ∫ u, ((t * t) * (U u ^ 2 * W u) + 2 * t * (U u * Real.sinh (u / 2)) + Φ u) :=
      integral_nonneg hpt
    rw [integral_lin3 hiUW hiUS hiΦ (t * t) (2 * t)] at hint_nn
    change 0 ≤ (t * t) * A + 2 * t * sinhHalfMoment U + ∫ u, Φ u at hint_nn
    linarith
  have hquad' : ∀ t : ℝ, 0 ≤ A * (t * t) + 2 * sinhHalfMoment U * t + 1 / 2 := fun t =>
    (hquad t).trans (by linarith only [hint_Φ])
  have hcs := abs_le_sqrt_mul_sqrt_of_quadratic_nonneg hA0 hquad'
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [sq_abs, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsq
  have hA_eq : A = (ε / 2) * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) + B₀ * ∫ u, U u ^ 2 := by
    have hpt : (fun u => U u ^ 2 * W u) =
        fun u => (ε / 2) * (U u ^ 2 * Real.exp (-(8 * u))) + B₀ * U u ^ 2 :=
      funext fun u => by dsimp only [W]; ring
    dsimp only [A]
    rw [hpt, integral_add (hi8.const_mul _) (hi0.const_mul _),
      integral_const_mul, integral_const_mul]
  have hε0 : 0 ≤ ∫ u, U u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  nlinarith only [hsq, hA_eq, hε, hε0]

/-! ### 2. Refutation of unrestricted atomic Gårding (A10) on `(conductorSubspace 1 N)ᗮ` -/

/-- Explicit pole-orthogonal deep coefficient sequence `(1 / √3) e_1 − √(2 / 3) e_2`. -/
def deepPoleOrthogonalCoeffs (n : ℕ) : ℝ :=
  if n = 1 then 1 / Real.sqrt 3 else if n = 2 then -Real.sqrt (2 / 3 : ℝ) else 0

/-- Unit-norm horizon vector `(1 / √3) e_1 − √(2 / 3) e_2` on `PrimeHorizonIndex N`. -/
def deepPoleOrthogonalVector (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector deepPoleOrthogonalCoeffs N

theorem primeHorizonExtension_deepPoleOrthogonalVector {N : ℕ} (hN : 2 ≤ N) :
    primeHorizonExtension (deepPoleOrthogonalVector N) = deepPoleOrthogonalCoeffs := by
  funext n
  by_cases hn : n ∈ Icc 1 N
  · exact primeHorizonExtension_coe (horizonProfileVector deepPoleOrthogonalCoeffs N) ⟨n, hn⟩
  · have hnot1 : n ≠ 1 := fun h => hn (by subst h; exact mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have hnot2 : n ≠ 2 := fun h => hn (by subst h; exact mem_Icc.mpr ⟨by omega, hN⟩)
    simp only [primeHorizonExtension, hn, ↓reduceDIte, deepPoleOrthogonalCoeffs,
      if_neg hnot1, if_neg hnot2]

theorem norm_deepPoleOrthogonalVector {N : ℕ} (hN : 2 ≤ N) :
    ‖deepPoleOrthogonalVector N‖ = 1 := by
  have hsq : ‖deepPoleOrthogonalVector N‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change ∑ i : PrimeHorizonIndex N, ‖deepPoleOrthogonalCoeffs i.1‖ ^ 2 = 1
    rw [sum_coe_sort (Icc 1 N) (fun n => ‖deepPoleOrthogonalCoeffs n‖ ^ 2)]
    have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 N := by
      intro n hn
      simp only [mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact mem_Icc.mpr ⟨le_rfl, by omega⟩
      · exact mem_Icc.mpr ⟨by omega, hN⟩
    rw [← sum_subset hsub fun n _ hnot => by
      simp only [mem_insert, mem_singleton, not_or] at hnot
      simp only [deepPoleOrthogonalCoeffs, if_neg hnot.1, if_neg hnot.2, norm_zero, sq, mul_zero]]
    rw [sum_pair (by decide : (1 : ℕ) ≠ 2)]
    simp only [Real.norm_eq_abs, sq_abs, deepPoleOrthogonalCoeffs]
    norm_num [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  nlinarith [norm_nonneg (deepPoleOrthogonalVector N)]

theorem deepPoleOrthogonalVector_mem_orthogonal {N : ℕ} (hN : 2 ≤ N) :
    deepPoleOrthogonalVector N ∈ (conductorSubspace 1 N)ᗮ := by
  have horth1 : ⟪normalizedRamanujanHorizonVector 1 N, deepPoleOrthogonalVector N⟫ = 0 := by
    have hpack : normalizedRamanujanHorizonVector 1 N =
        (Real.sqrt (Real.log N))⁻¹ • horizonProfileVector (fun n => 1 / Real.sqrt n) N := by
      have hp := normalizedRamanujanPacketVector_eq_smul_profile (Icc 1 1) (fun _ => (1 : ℝ)) N
      simp only [normalizedRamanujanPacketVector, Icc_self, sum_singleton, one_smul] at hp
      rw [hp]
      congr 1
      ext n
      simp only [horizonProfileVector, ramanujanPacketProfile, sum_singleton, one_mul,
        ramanujanPoleProfile, normalizedRamanujanMode_one]
    rw [hpack, real_inner_smul_left]
    suffices h0 : ⟪horizonProfileVector (fun n => 1 / Real.sqrt n) N,
        deepPoleOrthogonalVector N⟫ = 0 by
      rw [h0, mul_zero]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i : PrimeHorizonIndex N,
        deepPoleOrthogonalCoeffs i.1 * (1 / Real.sqrt i.1)) = 0
    rw [sum_coe_sort (Icc 1 N) (fun n => deepPoleOrthogonalCoeffs n * (1 / Real.sqrt n))]
    have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 N := by
      intro n hn
      simp only [mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact mem_Icc.mpr ⟨le_rfl, by omega⟩
      · exact mem_Icc.mpr ⟨by omega, hN⟩
    rw [← sum_subset hsub fun n _ hnot => by
      simp only [mem_insert, mem_singleton, not_or] at hnot
      simp only [deepPoleOrthogonalCoeffs, if_neg hnot.1, if_neg hnot.2, zero_mul]]
    rw [sum_pair (by decide : (1 : ℕ) ≠ 2)]
    simp only [deepPoleOrthogonalCoeffs, ↓reduceIte, if_neg (show (2 : ℕ) ≠ 1 by decide),
      Nat.cast_one, Real.sqrt_one, div_one, mul_one, Nat.cast_ofNat]
    have hsqrt : Real.sqrt (2 / 3 : ℝ) * (1 / Real.sqrt 2) = 1 / Real.sqrt 3 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [(Real.sqrt_pos.mpr zero_lt_two).ne',
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
    linarith only [hsqrt, (by simp only [one_div] : (Real.sqrt 3)⁻¹ = 1 / Real.sqrt 3)]
  rw [conductorSubspace, Submodule.mem_orthogonal]
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨⟨m, hm⟩, rfl⟩
    have hm1 : m = 1 := by
      have := mem_Icc.mp hm
      omega
    subst hm1
    exact horth1
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_left, hx, hy, add_zero]
  · intro a x _ hx
    rw [real_inner_smul_left, hx, mul_zero]

private theorem atomicTest_deepPoleOrthogonal_eq {N : ℕ} (hN : 2 ≤ N) (g : ℝ → ℝ) (u : ℝ) :
    atomicTest N deepPoleOrthogonalCoeffs g u =
      (1 / Real.sqrt 3) * g u - Real.sqrt (2 / 3 : ℝ) * g (u - Real.log 2) := by
  unfold atomicTest
  have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 N := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact mem_Icc.mpr ⟨le_rfl, by omega⟩
    · exact mem_Icc.mpr ⟨by omega, hN⟩
  rw [← sum_subset hsub fun n _ hnot => by
    simp only [mem_insert, mem_singleton, not_or] at hnot
    simp only [deepPoleOrthogonalCoeffs, if_neg hnot.1, if_neg hnot.2, zero_mul]]
  rw [sum_pair (by decide : (1 : ℕ) ≠ 2)]
  simp only [deepPoleOrthogonalCoeffs, ↓reduceIte, if_neg (show (2 : ℕ) ≠ 1 by decide),
    Nat.cast_one, Real.log_one, sub_zero, Nat.cast_ofNat, one_div]
  ring

private theorem atomicTest_deepPoleOrthogonal_sq {φ : ℝ → ℝ}
    (hφs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hN4c : 4 * c ≤ N) (u : ℝ) :
    atomicTest N deepPoleOrthogonalCoeffs (atomDilate φ (c / N)) u ^ 2 =
      (1 / 3 : ℝ) * atomDilate φ (c / N) u ^ 2 +
        (2 / 3 : ℝ) * atomDilate φ (c / N) (u - Real.log 2) ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < N := by linarith
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hN_pos
  have hw4 : w ≤ 1 / 4 := by
    dsimp only [w]
    rw [div_le_iff₀ hN_pos]
    linarith
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  let g := atomDilate φ w
  have hgs : ∀ v, v ∉ Set.Icc 0 w → g v = 0 := fun v hv =>
    hφs (v / w) fun hm => hv ⟨(le_div_iff₀ hw).mp hm.1 |>.trans_eq' (zero_mul w),
      (div_le_one hw).mp hm.2⟩
  have hprod0 : g u * g (u - Real.log 2) = 0 := by
    by_cases hu : u ∈ Set.Icc 0 w
    · have hnot : u - Real.log 2 ∉ Set.Icc 0 w := fun hm => by linarith [hu.2, hm.1]
      rw [hgs _ hnot, mul_zero]
    · rw [hgs u hu, zero_mul]
  rw [atomicTest_deepPoleOrthogonal_eq hN2 g u]
  have hs3 : (1 / Real.sqrt 3) ^ 2 = (1 / 3 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hs23 : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  change ((1 / Real.sqrt 3) * g u - Real.sqrt (2 / 3 : ℝ) * g (u - Real.log 2)) ^ 2 =
    (1 / 3 : ℝ) * g u ^ 2 + (2 / 3 : ℝ) * g (u - Real.log 2) ^ 2
  calc ((1 / Real.sqrt 3) * g u - Real.sqrt (2 / 3 : ℝ) * g (u - Real.log 2)) ^ 2
      = (1 / Real.sqrt 3) ^ 2 * g u ^ 2 + Real.sqrt (2 / 3 : ℝ) ^ 2 * g (u - Real.log 2) ^ 2 -
          2 * (1 / Real.sqrt 3) * Real.sqrt (2 / 3 : ℝ) * (g u * g (u - Real.log 2)) := by ring
    _ = (1 / 3 : ℝ) * g u ^ 2 + (2 / 3 : ℝ) * g (u - Real.log 2) ^ 2 := by
          rw [hs3, hs23, hprod0]; ring

/-- Exact `L²` norm of the normalized deep pole-orthogonal source once `N ≥ 4 c`. -/
theorem integral_normalized_deepPoleOrthogonal_sq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hN4c : 4 * c ≤ N) :
    ∫ u, normalizedCentredAtomicTest φ deepPoleOrthogonalCoeffs c N u ^ 2 =
      (1 / c) * ∫ u, φ u ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN_pos : (0 : ℝ) < N := by linarith
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hN_pos
  let g := atomDilate φ w
  have hg : Continuous g := hφ.comp (continuous_id.div_const _)
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun v hv =>
      hφs (v / w) fun hm => hv ⟨(le_div_iff₀ hw).mp hm.1 |>.trans_eq' (zero_mul w),
        (div_le_one hw).mp hm.2⟩
  have hig2 : Integrable (fun u => g u ^ 2) := integrable_sq_of_continuous hg hgc
  have hshift : (∫ u, normalizedCentredAtomicTest φ deepPoleOrthogonalCoeffs c N u ^ 2) =
      ((N : ℝ) / c ^ 2) *
        ∫ u, atomicTest N deepPoleOrthogonalCoeffs g u ^ 2 := by
    have hpt : (fun u => normalizedCentredAtomicTest φ deepPoleOrthogonalCoeffs c N u ^ 2) =
        fun u => ((N : ℝ) / c ^ 2) *
          (atomicTest N deepPoleOrthogonalCoeffs g (u + Real.log N) ^ 2) := by
      funext u
      dsimp only [normalizedCentredAtomicTest, centredAtomicTest, g, w]
      rw [mul_pow, div_pow, Real.sq_sqrt hN_pos.le]
    rw [hpt, integral_const_mul,
      integral_add_right_eq_self (fun u => atomicTest N deepPoleOrthogonalCoeffs g u ^ 2)
        (Real.log N)]
  rw [hshift]
  have hsq_g : ∀ u, atomicTest N deepPoleOrthogonalCoeffs g u ^ 2 =
      (1 / 3 : ℝ) * g u ^ 2 + (2 / 3 : ℝ) * g (u - Real.log 2) ^ 2 :=
    atomicTest_deepPoleOrthogonal_sq hφs hc1 hN4c
  simp_rw [hsq_g]
  rw [integral_add (hig2.const_mul _) ((hig2.comp_sub_right (Real.log 2)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log 2)]
  have hsum : (1 / 3 : ℝ) * (∫ u, g u ^ 2) + (2 / 3 : ℝ) * ∫ u, g u ^ 2 = ∫ u, g u ^ 2 := by ring
  rw [hsum, integral_atomDilate_sq hw]
  dsimp only [w]
  field_simp [hc0.ne', hN_pos.ne']

/-- Lower bound `≍ c⁻¹ N⁸` on the eighth-power exponential mass of the deep pole-orthogonal source. -/
theorem exponentialMass_normalized_deepPoleOrthogonal_ge {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hN4c : 4 * c ≤ N) :
    (Real.exp (-8) / (3 * c)) * (∫ u, φ u ^ 2) * (N : ℝ) ^ 8 ≤
      ∫ y, normalizedCentredAtomicTest φ deepPoleOrthogonalCoeffs c N y ^ 2 *
        Real.exp (-(8 * y)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN_pos : (0 : ℝ) < N := by linarith
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hN_pos
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    rw [div_le_one hN_pos]
    linarith
  let g := atomDilate φ w
  have hg : Continuous g := hφ.comp (continuous_id.div_const _)
  have hgs : ∀ v, v ∉ Set.Icc 0 w → g v = 0 := fun v hv =>
    hφs (v / w) fun hm => hv ⟨(le_div_iff₀ hw).mp hm.1 |>.trans_eq' (zero_mul w),
      (div_le_one hw).mp hm.2⟩
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgs
  let U := normalizedCentredAtomicTest φ deepPoleOrthogonalCoeffs c N
  have hU_cd : Continuous U := by
    dsimp only [U, normalizedCentredAtomicTest, centredAtomicTest]
    have hatom : Continuous (atomicTest N deepPoleOrthogonalCoeffs g) := by
      unfold atomicTest
      exact continuous_finsetSum _ fun n _ =>
        continuous_const.mul (hg.comp (continuous_id.sub continuous_const))
    exact continuous_const.mul (hatom.comp (continuous_id.add continuous_const))
  have hU_cs : HasCompactSupport U := by
    dsimp only [U, normalizedCentredAtomicTest, centredAtomicTest]
    exact ((hasCompactSupport_atomicTest hgs N _).comp_homeomorph
      (Homeomorph.addRight (Real.log N))).mul_left
  have hU2_cs : HasCompactSupport (fun y => U y ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hU_cs ⊢
    exact hU_cs.mono fun y hy => by change U y = 0 at hy; change U y ^ 2 = 0; rw [hy]; norm_num
  have hi_rhs : Integrable (fun y => U y ^ 2 * Real.exp (-(8 * y))) :=
    ((hU_cd.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hU2_cs.mul_right
  have hi_lhs : Integrable (fun y =>
      ((N : ℝ) / c ^ 2) * (1 / 3 : ℝ) * (Real.exp (-8) * (N : ℝ) ^ 8) *
        g (y + Real.log N) ^ 2) :=
    ((integrable_sq_of_continuous hg hgc).comp_add_right (Real.log N)).const_mul _
  have heN : Real.exp (8 * Real.log (N : ℝ)) = (N : ℝ) ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) from rfl, Real.exp_nat_mul, Real.exp_log hN_pos]
  have hpt : ∀ y : ℝ,
      ((N : ℝ) / c ^ 2) * (1 / 3 : ℝ) * (Real.exp (-8) * (N : ℝ) ^ 8) *
        g (y + Real.log N) ^ 2 ≤
      U y ^ 2 * Real.exp (-(8 * y)) := by
    intro y
    by_cases hy : y + Real.log N ∈ Set.Icc 0 w
    · have hexp_ge : Real.exp (-8) * (N : ℝ) ^ 8 ≤ Real.exp (-(8 * y)) := by
        rw [← heN, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [hy.2, hw1])
      have hU2_ge : ((N : ℝ) / c ^ 2) * (1 / 3 : ℝ) * g (y + Real.log N) ^ 2 ≤ U y ^ 2 := by
        dsimp only [U, normalizedCentredAtomicTest, centredAtomicTest]
        rw [mul_pow, div_pow, Real.sq_sqrt hN_pos.le,
          atomicTest_deepPoleOrthogonal_sq hφs hc1 hN4c (y + Real.log N)]
        have hnn : 0 ≤ ((N : ℝ) / c ^ 2) *
            ((2 / 3 : ℝ) * g (y + Real.log N - Real.log 2) ^ 2) := by positivity
        linarith only [hnn,
          (by ring : ((N : ℝ) / c ^ 2) * ((1 / 3 : ℝ) * g (y + Real.log N) ^ 2 +
            (2 / 3 : ℝ) * g (y + Real.log N - Real.log 2) ^ 2) =
            ((N : ℝ) / c ^ 2) * (1 / 3 : ℝ) * g (y + Real.log N) ^ 2 +
              ((N : ℝ) / c ^ 2) * ((2 / 3 : ℝ) * g (y + Real.log N - Real.log 2) ^ 2))]
      calc ((N : ℝ) / c ^ 2) * (1 / 3 : ℝ) * (Real.exp (-8) * (N : ℝ) ^ 8) *
            g (y + Real.log N) ^ 2
          = (((N : ℝ) / c ^ 2) * (1 / 3 : ℝ) * g (y + Real.log N) ^ 2) *
              (Real.exp (-8) * (N : ℝ) ^ 8) := by ring
        _ ≤ U y ^ 2 * Real.exp (-(8 * y)) :=
            mul_le_mul hU2_ge hexp_ge (by positivity) (sq_nonneg _)
    · rw [hgs _ hy]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hmono := integral_mono hi_lhs hi_rhs hpt
  rw [integral_const_mul, integral_add_right_eq_self (fun u => g u ^ 2) (Real.log N),
    integral_atomDilate_sq hw] at hmono
  refine le_trans (le_of_eq ?_) hmono
  dsimp only [w]
  field_simp [hc0.ne', hN_pos.ne']

/-- Sharp `O((log N) / c)` upper bound on `weilQuad` of the normalized deep pole-orthogonal source. -/
theorem exists_weilQuad_normalized_deepPoleOrthogonal_le_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ C_deep : ℝ, 0 ≤ C_deep ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → 4 * c ≤ N →
        weilQuad (normalizedCentredAtomicTest φ deepPoleOrthogonalCoeffs c N) ≤
          (C_deep / c) * (Real.log N + 1) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hφs
  obtain ⟨C₁, hC₁⟩ := hφc.deriv.exists_bound_of_continuous (hφ.continuous_deriv (by norm_num))
  set M₁ := max C₁ 0
  have hM₁0 : 0 ≤ M₁ := le_max_right _ _
  have hb1 : ∀ t, |deriv φ t| ≤ M₁ := fun t => by
    have := hC₁ t; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hdiff_φ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hlip_φ : ∀ a b, |φ a - φ b| ≤ M₁ * |a - b| := fun a b => by
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
      (fun x _ => hdiff_φ.differentiableAt)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hb1 x) convex_univ
      (Set.mem_univ b) (Set.mem_univ a)
    simpa only [Real.norm_eq_abs] using hmvt
  have hC_lip_nn : 0 ≤ levyLipConstant := by
    unfold levyLipConstant
    have h2 : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hd : 0 < 1 - Real.exp (-2 : ℝ) := by linarith
    positivity
  set I₂ := ∫ u, φ u ^ 2
  set I₁ := ∫ u, |φ u|
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun _ => sq_nonneg _
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun _ => abs_nonneg _
  set C_deep := 2 * I₂ + (2 * |gammaHardyPhaseRate 0| + levyLipConstant +
    2 * vonMangoldtThreeHalvesMass * Real.exp 2) * I₂ +
    4 * Real.exp (1 / 2) * M₁ * I₁ + 8 * Real.cosh (1 / 2) ^ 2 * I₁ ^ 2
  have hC_deep0 : 0 ≤ C_deep := by
    have := vonMangoldtThreeHalvesMass_nonneg
    positivity
  refine ⟨C_deep, hC_deep0, ?_⟩
  intro c N hc1 hN4c
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < N := by linarith
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hN_pos
  have hw4 : w ≤ 1 / 4 := by
    dsimp only [w]
    rw [div_le_iff₀ hN_pos]
    linarith
  have hw1 : w ≤ 1 := by linarith
  let g := atomDilate φ w
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hφs hw
  let f := atomicTest N deepPoleOrthogonalCoeffs g
  have hf_cd : ContDiff ℝ 2 f := contDiff_atomicTest hg N _
  have hf_cs : HasCompactSupport f := hasCompactSupport_atomicTest hgs N _
  have hf_eq : ∀ u, f u = (1 / Real.sqrt 3) * g u - Real.sqrt (2 / 3 : ℝ) * g (u - Real.log 2) :=
    atomicTest_deepPoleOrthogonal_eq hN2 g
  have hf_supp1 : SupportedIn 1 f := by
    intro u hu
    rw [hf_eq u]
    have hl2 : Real.log 2 < 3 / 4 := by
      have := Real.log_two_lt_d9
      linarith
    have hg1 : g u = 0 := hgs u fun hm => by
      have : |u| ≤ 1 := by rw [abs_of_nonneg hm.1]; linarith [hm.2]
      linarith
    have hg2 : g (u - Real.log 2) = 0 := hgs (u - Real.log 2) fun hm => by
      have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have : |u| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [hm.1])]
        linarith [hm.2]
      linarith
    rw [hg1, hg2]
    ring
  have hf_L2 : ∫ u, f u ^ 2 = w * I₂ := by
    have hig2 : Integrable (fun u => g u ^ 2) := integrable_sq_of_continuous hg.continuous hgc
    have hsq_g : ∀ u, f u ^ 2 =
        (1 / 3 : ℝ) * g u ^ 2 + (2 / 3 : ℝ) * g (u - Real.log 2) ^ 2 :=
      atomicTest_deepPoleOrthogonal_sq hφs hc1 hN4c
    simp_rw [hsq_g]
    rw [integral_add (hig2.const_mul _) ((hig2.comp_sub_right (Real.log 2)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log 2)]
    have hsum : (1 / 3 : ℝ) * (∫ u, g u ^ 2) + (2 / 3 : ℝ) * ∫ u, g u ^ 2 = ∫ u, g u ^ 2 := by ring
    rw [hsum, integral_atomDilate_sq hw]
  have hc1_le : |1 / Real.sqrt 3| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one (Real.sqrt_pos.mpr (by norm_num))]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc2_le : |Real.sqrt (2 / 3 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hf_L1 : ∫ u, |f u| ≤ 2 * w * I₁ := by
    have hig1 : Integrable (fun u => |g u|) :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).abs
    have hpt : ∀ u, |f u| ≤ |g u| + |g (u - Real.log 2)| := fun u => by
      rw [hf_eq u, sub_eq_add_neg]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hc1_le
      · rw [abs_neg, abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hc2_le
    have hmono := integral_mono (hf_cd.continuous.integrable_of_hasCompactSupport hf_cs).abs
      (hig1.add (hig1.comp_sub_right (Real.log 2))) hpt
    change (∫ x, |f x|) ≤ ∫ x, (|g x| + |g (x - Real.log 2)|) at hmono
    have hg_L1 : ∫ u, |g u| = w * I₁ := by
      simpa only [g, atomDilate, abs_of_pos hw, smul_eq_mul] using
        Measure.integral_comp_div (fun u => |φ u|) w
    rw [integral_add hig1 (hig1.comp_sub_right (Real.log 2)),
      integral_sub_right_eq_self (fun u => |g u|) (Real.log 2), hg_L1] at hmono
    linarith only [hmono]
  have hf_lip : ∀ u v, |f u - f v| ≤ (2 * M₁ / w) * |u - v| := by
    intro u v
    have hg_lip : ∀ a b, |g a - g b| ≤ (M₁ / w) * |a - b| := fun a b => by
      have h := hlip_φ (a / w) (b / w)
      rw [← sub_div, abs_div, abs_of_pos hw] at h
      calc |g a - g b| ≤ M₁ * (|a - b| / w) := h
        _ = (M₁ / w) * |a - b| := by ring
    have hsub : f u - f v = (1 / Real.sqrt 3) * (g u - g v) -
        Real.sqrt (2 / 3 : ℝ) * (g (u - Real.log 2) - g (v - Real.log 2)) := by
      rw [hf_eq u, hf_eq v]; ring
    rw [hsub, sub_eq_add_neg]
    have h1 : |(1 / Real.sqrt 3) * (g u - g v)| ≤ (M₁ / w) * |u - v| := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hc1_le).trans (hg_lip u v)
    have h2 : |-(Real.sqrt (2 / 3 : ℝ) * (g (u - Real.log 2) - g (v - Real.log 2)))| ≤
        (M₁ / w) * |u - v| := by
      rw [abs_neg, abs_mul]
      have hsh : |(u - Real.log 2) - (v - Real.log 2)| = |u - v| := by ring_nf
      exact (mul_le_of_le_one_left (abs_nonneg _) hc2_le).trans
        ((hg_lip _ _).trans_eq (by rw [hsh]))
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hlev := levyEnergy_le_lipschitz hf_cd hf_cs hf_lip hw hw1
  have hlogw : Real.log (1 / w) ≤ Real.log N := by
    have h1w : 1 / w = (N : ℝ) / c := by dsimp only [w]; field_simp [hc0.ne', hN_pos.ne']
    rw [h1w]
    exact Real.log_le_log (div_pos hN_pos hc0) (div_le_self hN_pos.le hc1)
  have hlev' : levyEnergy f ≤
      (4 * Real.exp (1 / 2) * M₁ * I₁ + (2 * Real.log N + levyLipConstant) * I₂) * w := by
    have h1 : Real.exp (1 / 2) * (2 * M₁ / w) * w * (∫ u, |f u|) ≤
        4 * Real.exp (1 / 2) * M₁ * I₁ * w := by
      have hcancel : Real.exp (1 / 2) * (2 * M₁ / w) * w = 2 * Real.exp (1 / 2) * M₁ := by
        field_simp [hw.ne']
      rw [hcancel]
      exact (mul_le_mul_of_nonneg_left hf_L1 (by positivity)).trans_eq (by ring)
    have h2 : (2 * Real.log (1 / w) + levyLipConstant) * (∫ u, f u ^ 2) ≤
        (2 * Real.log N + levyLipConstant) * I₂ * w := by
      rw [hf_L2]
      have hcoef : 2 * Real.log (1 / w) + levyLipConstant ≤ 2 * Real.log N + levyLipConstant := by
        linarith only [hlogw]
      exact (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hw.le hI₂0)).trans_eq (by ring)
    linarith only [hlev, h1, h2,
      (by ring : 4 * Real.exp (1 / 2) * M₁ * I₁ * w +
        (2 * Real.log N + levyLipConstant) * I₂ * w =
        (4 * Real.exp (1 / 2) * M₁ * I₁ + (2 * Real.log N + levyLipConstant) * I₂) * w)]
  have hexp_f : exponentialSourceMass f ≤ Real.exp 2 * (w * I₂) := by
    have hf2c : HasCompactSupport (fun y => f y ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hf_cs ⊢
      exact hf_cs.mono fun y hy => by change f y = 0 at hy; change f y ^ 2 = 0; rw [hy]; norm_num
    have hi_l : Integrable (fun y => (Real.exp |y| * f y) ^ 2) :=
      (((Real.continuous_exp.comp continuous_abs).mul hf_cd.continuous).pow 2).integrable_of_hasCompactSupport
        (by
          rw [hasCompactSupport_iff_eventuallyEq] at hf2c ⊢
          exact hf2c.mono fun y hy => by
            change f y ^ 2 = 0 at hy; change (Real.exp |y| * f y) ^ 2 = 0; rw [mul_pow, hy, mul_zero])
    have hi_r : Integrable (fun y => Real.exp 2 * f y ^ 2) :=
      (integrable_sq_of_continuous hf_cd.continuous hf_cs).const_mul (Real.exp 2)
    have hpt : ∀ y, (Real.exp |y| * f y) ^ 2 ≤ Real.exp 2 * f y ^ 2 := fun y => by
      by_cases hy : 1 < |y|
      · rw [hf_supp1 y hy]; norm_num
      · push Not at hy
        rw [mul_pow, ← Real.exp_nat_mul]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by push_cast; linarith)) (sq_nonneg _)
    have hm := integral_mono hi_l hi_r hpt
    rwa [integral_const_mul, hf_L2] at hm
  have hprime : -primeSum f ≤ 2 * vonMangoldtThreeHalvesMass * Real.exp 2 * I₂ * w := by
    have habs := (neg_le_abs _).trans
      (abs_primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass hf_cd.continuous hf_cs)
    have hm := mul_le_mul_of_nonneg_left hexp_f
      (mul_nonneg zero_le_two vonMangoldtThreeHalvesMass_nonneg)
    linarith only [habs, hm,
      (by ring : 2 * vonMangoldtThreeHalvesMass * (Real.exp 2 * (w * I₂)) =
        2 * vonMangoldtThreeHalvesMass * Real.exp 2 * I₂ * w)]
  have hpole : 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 ≤
      8 * Real.cosh (1 / 2) ^ 2 * I₁ ^ 2 * w := by
    have hCf : |coshHalfMoment f| ≤ Real.cosh (1 / 2) * (2 * w * I₁) :=
      (abs_moment_le hf_cd.continuous hf_cs hf_supp1
        (Real.continuous_cosh.comp (continuous_id.div_const 2))
        fun u hu => abs_cosh_half_le hu).trans
        (mul_le_mul_of_nonneg_left hf_L1 (Real.cosh_pos _).le)
    have hCf2 : coshHalfMoment f ^ 2 ≤ 4 * Real.cosh (1 / 2) ^ 2 * I₁ ^ 2 * w ^ 2 := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hCf 2
      rw [sq_abs] at hsq
      exact hsq.trans_eq (by ring)
    have hw2_le : w ^ 2 ≤ w := by nlinarith
    have hC0 : 0 ≤ 4 * Real.cosh (1 / 2) ^ 2 * I₁ ^ 2 := by positivity
    have hw_step := mul_le_mul_of_nonneg_left hw2_le hC0
    nlinarith [sq_nonneg (sinhHalfMoment f), hCf2, hw_step]
  have hγ : 2 * gammaHardyPhaseRate 0 * ∫ u, f u ^ 2 ≤
      2 * |gammaHardyPhaseRate 0| * I₂ * w := by
    rw [hf_L2]
    have h1 : gammaHardyPhaseRate 0 ≤ |gammaHardyPhaseRate 0| := le_abs_self _
    nlinarith [mul_nonneg hw.le hI₂0]
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hwf : weilQuad f ≤ C_deep * w * (Real.log N + 1) := by
    rw [weilQuad_eq hf_cd hf_cs]
    let K_const := (2 * |gammaHardyPhaseRate 0| + levyLipConstant +
      2 * vonMangoldtThreeHalvesMass * Real.exp 2) * I₂ +
      4 * Real.exp (1 / 2) * M₁ * I₁ + 8 * Real.cosh (1 / 2) ^ 2 * I₁ ^ 2
    have hK_nn : 0 ≤ K_const := by
      have := vonMangoldtThreeHalvesMass_nonneg
      dsimp only [K_const]
      positivity
    have hbase : 2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) + levyEnergy f - primeSum f +
        (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) ≤
        2 * I₂ * w * Real.log N + K_const * w := by
      dsimp only [K_const]
      linarith only [hγ, hlev', hprime, hpole,
        (by ring : 2 * |gammaHardyPhaseRate 0| * I₂ * w +
            (4 * Real.exp (1 / 2) * M₁ * I₁ + (2 * Real.log N + levyLipConstant) * I₂) * w +
            2 * vonMangoldtThreeHalvesMass * Real.exp 2 * I₂ * w +
            8 * Real.cosh (1 / 2) ^ 2 * I₁ ^ 2 * w =
          2 * I₂ * w * Real.log N +
            ((2 * |gammaHardyPhaseRate 0| + levyLipConstant +
                2 * vonMangoldtThreeHalvesMass * Real.exp 2) * I₂ +
              4 * Real.exp (1 / 2) * M₁ * I₁ + 8 * Real.cosh (1 / 2) ^ 2 * I₁ ^ 2) * w)]
    have hK_grow : K_const * w ≤ K_const * w * (Real.log N + 1) :=
      le_mul_of_one_le_right (mul_nonneg hK_nn hw.le) (by linarith only [hlogN0])
    have h2I_nn : 0 ≤ 2 * I₂ * w := by positivity
    have hC_def : C_deep = 2 * I₂ + K_const := by dsimp only [C_deep, K_const]; ring
    have hC_eq : C_deep * w * (Real.log N + 1) =
        2 * I₂ * w * Real.log N + 2 * I₂ * w + K_const * w * (Real.log N + 1) := by
      rw [hC_def]; ring
    linarith only [hbase, hK_grow, h2I_nn, hC_eq]
  have hcd_cent : ContDiff ℝ 2 (centredAtomicTest φ deepPoleOrthogonalCoeffs c N) :=
    contDiff_centredAtomicTest hφ _ c N
  have hcs_cent : HasCompactSupport (centredAtomicTest φ deepPoleOrthogonalCoeffs c N) := by
    unfold centredAtomicTest
    exact hf_cs.comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hU_eq : weilQuad (normalizedCentredAtomicTest φ deepPoleOrthogonalCoeffs c N) =
      ((N : ℝ) / c ^ 2) * weilQuad f := by
    unfold normalizedCentredAtomicTest
    rw [weilQuad_const_mul hcd_cent hcs_cent, weilQuad_centredAtomicTest,
      div_pow, Real.sq_sqrt hN_pos.le]
  rw [hU_eq]
  calc ((N : ℝ) / c ^ 2) * weilQuad f
      ≤ ((N : ℝ) / c ^ 2) * (C_deep * w * (Real.log N + 1)) :=
        mul_le_mul_of_nonneg_left hwf (by positivity)
    _ = (C_deep / c) * (Real.log N + 1) := by
        dsimp only [w]
        field_simp [hc0.ne', hN_pos.ne']

/-- **Refutation of unrestricted atomic Gårding (A10) on `(conductorSubspace 1 N)ᗮ`.**
Along any critical schedule `c_N ≥ 1` with `c_N⁸ / log N → R` (`R > 0`), for every shift `B : ℝ`
and every positive weight coefficient `a > 0`, eventually in `N` there exists a unit-`ℓ²` vector
`z ∈ (conductorSubspace 1 N)ᗮ` whose `ℓ²`-normalized atomic source `U` violates
`a ∫ U(y)² e^{−8y} dy ≤ weilQuad U + B ∫ U(y)² du`. -/
theorem not_unrestricted_atomic_garding_on_poleOrthogonal
    {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R))
    (B : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      ∃ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
        z ∈ (conductorSubspace 1 N)ᗮ ∧ ‖z‖ = 1 ∧
        weilQuad (normalizedCentredAtomicTest tiltedUnitSpline
            (primeHorizonExtension z) (c N) N) +
          B * (∫ u, normalizedCentredAtomicTest tiltedUnitSpline
            (primeHorizonExtension z) (c N) N u ^ 2) <
        a * ∫ y, normalizedCentredAtomicTest tiltedUnitSpline
          (primeHorizonExtension z) (c N) N y ^ 2 * Real.exp (-(8 * y)) := by
  obtain ⟨C_deep, hC_deep0, hdeep⟩ :=
    exists_weilQuad_normalized_deepPoleOrthogonal_le_log
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
  set I₂ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  have hc_up : ∀ᶠ N : ℕ in atTop, c N ^ 8 ≤ (R + 1) * Real.log (N : ℝ) := by
    have hev := htend.eventually (gt_mem_nhds (by linarith : R < R + 1))
    filter_upwards [hev, eventually_ge_atTop 3] with N hlt hN3
    have hL0 : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact ((div_lt_iff₀ hL0).mp hlt).le
  have hL_le : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) / (4 * (R + 1)) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hev := (h0.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * (R + 1))))
    filter_upwards [hev, eventually_ge_atTop 1] with N hlt hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hm := (div_lt_iff₀ hN0).mp hlt
    linarith [
      (by field_simp [(by positivity : (4 * (R + 1)) ≠ 0)] :
        1 / (4 * (R + 1)) * (N : ℝ) = (N : ℝ) / (4 * (R + 1)))]
  set M_const := (C_deep + |B| * I₂ + 1) / (a * Real.exp (-8) * I₂ / 3)
  have hN7_large : ∀ᶠ N : ℕ in atTop, M_const ≤ (N : ℝ) ^ 7 := by
    have hp7 : Tendsto (fun N : ℕ => (N : ℝ) ^ 7) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 7 ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact hp7.eventually_ge_atTop M_const
  filter_upwards [hc1, hc_up, hL_le, hN7_large, eventually_ge_atTop 3] with
    N hcN hc8 hLN hN7 hN3
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  have hN2 : 2 ≤ N := by omega
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc8_c : c N ≤ c N ^ 8 := le_self_pow₀ hcN (by norm_num)
  have h4cN : 4 * c N ≤ N := by
    have h1 : 4 * c N ≤ 4 * ((R + 1) * Real.log (N : ℝ)) := by linarith
    have h2 : 4 * ((R + 1) * Real.log (N : ℝ)) ≤ N := by
      have hm := (le_div_iff₀ (by positivity : 0 < 4 * (R + 1))).mp hLN
      linarith
    linarith
  refine ⟨deepPoleOrthogonalVector N, deepPoleOrthogonalVector_mem_orthogonal hN2,
    norm_deepPoleOrthogonalVector hN2, ?_⟩
  rw [primeHorizonExtension_deepPoleOrthogonalVector hN2]
  have hw := hdeep hcN h4cN
  have hsq := integral_normalized_deepPoleOrthogonal_sq
    contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero hcN h4cN
  have hexp := exponentialMass_normalized_deepPoleOrthogonal_ge
    contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero hcN h4cN
  have hlog_le_N : Real.log (N : ℝ) + 1 ≤ N := by
    have h1 : Real.log (N : ℝ) ≤ (N : ℝ) - 1 := by
      have := Real.log_le_sub_one_of_pos hN_pos
      linarith
    linarith
  have hlhs_le : weilQuad (normalizedCentredAtomicTest tiltedUnitSpline
        deepPoleOrthogonalCoeffs (c N) N) +
      B * (∫ u, normalizedCentredAtomicTest tiltedUnitSpline
        deepPoleOrthogonalCoeffs (c N) N u ^ 2) ≤
      ((C_deep + |B| * I₂) / c N) * N := by
    rw [hsq]
    have hB_le : B * ((1 / c N) * I₂) ≤ (|B| * I₂ / c N) * N := by
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have h1 : B ≤ |B| := le_abs_self B
      have h2 : B * ((1 / c N) * I₂) ≤ |B| * ((1 / c N) * I₂) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : |B| * ((1 / c N) * I₂) ≤ (|B| * ((1 / c N) * I₂)) * N :=
        le_mul_of_one_le_right (by positivity) hN1R
      exact h2.trans (h3.trans_eq (by ring))
    have hw_N : (C_deep / c N) * (Real.log N + 1) ≤ (C_deep / c N) * N :=
      mul_le_mul_of_nonneg_left hlog_le_N (by positivity)
    linarith only [hw, hw_N, hB_le,
      (by ring : (C_deep / c N) * N + (|B| * I₂ / c N) * N =
        ((C_deep + |B| * I₂) / c N) * N)]
  have hrhs_ge : (a * Real.exp (-8) * I₂ / (3 * c N)) * (N : ℝ) ^ 8 ≤
      a * ∫ y, normalizedCentredAtomicTest tiltedUnitSpline
        deepPoleOrthogonalCoeffs (c N) N y ^ 2 * Real.exp (-(8 * y)) := by
    have hm := mul_le_mul_of_nonneg_left hexp ha.le
    exact hm.trans_eq' (by ring)
  have hstrict : ((C_deep + |B| * I₂) / c N) * N <
      (a * Real.exp (-8) * I₂ / (3 * c N)) * (N : ℝ) ^ 8 := by
    have hden_pos : 0 < a * Real.exp (-8) * I₂ / 3 := by positivity
    have hm := (div_le_iff₀ hden_pos).mp hN7
    have h1 : C_deep + |B| * I₂ < (a * Real.exp (-8) * I₂ / 3) * (N : ℝ) ^ 7 := by linarith
    have h2 := mul_lt_mul_of_pos_right h1 (div_pos hN_pos hc0)
    exact h2.trans_eq' (by field_simp [hc0.ne']) |>.trans_eq (by
      rw [show (N : ℝ) ^ 8 = (N : ℝ) ^ 7 * N by ring]
      field_simp [hc0.ne'])
  exact hlhs_le.trans_lt (hstrict.trans_le hrhs_ge)

/-- **Refutation of unrestricted unit-`L²` atomic Gårding on `(conductorSubspace 1 N)ᗮ`.**
Rescaling the deep pole-orthogonal witness to unit `L²(ℝ)` norm (`∫ Ũ² = 1`) still violates
`a ∫ Ũ(y)² e^{−8y} dy ≤ weilQuad Ũ + B` eventually for every `B : ℝ` and `a > 0`. -/
theorem not_unrestricted_unitL2_atomic_garding_on_poleOrthogonal
    {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R))
    (B : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (z : EuclideanSpace ℝ (PrimeHorizonIndex N)) (α : ℝ),
        z ∈ (conductorSubspace 1 N)ᗮ ∧ ‖z‖ = 1 ∧ 0 < α ∧
        (∫ u, (α * normalizedCentredAtomicTest tiltedUnitSpline
          (primeHorizonExtension z) (c N) N u) ^ 2) = 1 ∧
        weilQuad (fun u => α * normalizedCentredAtomicTest tiltedUnitSpline
            (primeHorizonExtension z) (c N) N u) + B <
          a * ∫ y, (α * normalizedCentredAtomicTest tiltedUnitSpline
            (primeHorizonExtension z) (c N) N y) ^ 2 * Real.exp (-(8 * y)) := by
  obtain ⟨C_deep, hC_deep0, hdeep⟩ :=
    exists_weilQuad_normalized_deepPoleOrthogonal_le_log
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
  set I₂ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  have hc_up : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    have hevR := htend.eventually (gt_mem_nhds (by linarith : R < R + 1))
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hevL := (h0.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * (R + 1))))
    filter_upwards [hc1, hevR, hevL, eventually_ge_atTop 3] with N hcN hltR hltL hN3
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hc8 : c N ≤ (R + 1) * Real.log (N : ℝ) :=
      (le_self_pow₀ hcN (by norm_num : 8 ≠ 0)).trans ((div_lt_iff₀ hL0).mp hltR).le
    have hLN : 4 * (R + 1) * Real.log (N : ℝ) ≤ N := by
      have hm := (div_lt_iff₀ hN0).mp hltL
      have hdiv : 1 / (4 * (R + 1)) * (N : ℝ) = (N : ℝ) / (4 * (R + 1)) := by
        field_simp [(by positivity : (4 * (R + 1)) ≠ 0)]
      have hm' : Real.log (N : ℝ) < (N : ℝ) / (4 * (R + 1)) := by linarith
      exact ((le_div_iff₀ (by positivity : 0 < 4 * (R + 1))).mp hm'.le).trans_eq' (by ring)
    linarith
  set M_const := (C_deep / I₂ + |B| + 1) / (a * Real.exp (-8) / 3)
  have hN7_large : ∀ᶠ N : ℕ in atTop, M_const ≤ (N : ℝ) ^ 7 :=
    ((tendsto_pow_atTop (by norm_num : 7 ≠ 0)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop M_const
  filter_upwards [hc1, hc_up, hN7_large, eventually_ge_atTop 3] with N hcN h4cN hN7 hN3
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  have hN2 : 2 ≤ N := by omega
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let α := Real.sqrt (c N / I₂)
  have hα_pos : 0 < α := Real.sqrt_pos.mpr (div_pos hc0 hI₂)
  have hα2 : α ^ 2 = c N / I₂ := Real.sq_sqrt (div_nonneg hc0.le hI₂.le)
  refine ⟨deepPoleOrthogonalVector N, α, deepPoleOrthogonalVector_mem_orthogonal hN2,
    norm_deepPoleOrthogonalVector hN2, hα_pos, ?_, ?_⟩
  · rw [primeHorizonExtension_deepPoleOrthogonalVector hN2]
    simp_rw [mul_pow]
    rw [integral_const_mul,
      integral_normalized_deepPoleOrthogonal_sq contDiff_tiltedUnitSpline.continuous
        tiltedUnitSpline_eq_zero hcN h4cN,
      hα2]
    change (c N / I₂) * ((1 / c N) * I₂) = 1
    field_simp [hc0.ne', hI₂.ne']
  · rw [primeHorizonExtension_deepPoleOrthogonalVector hN2]
    let U := normalizedCentredAtomicTest tiltedUnitSpline deepPoleOrthogonalCoeffs (c N) N
    have hw : 0 < c N / N := div_pos hc0 hN_pos
    obtain ⟨_, hgs, _⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
    have hU_cd : ContDiff ℝ 2 U :=
      contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline _ (c N) N)
    have hU_cs : HasCompactSupport U := by
      dsimp only [U, normalizedCentredAtomicTest, centredAtomicTest]
      exact ((hasCompactSupport_atomicTest hgs N _).comp_homeomorph
        (Homeomorph.addRight (Real.log N))).mul_left
    rw [weilQuad_const_mul hU_cd hU_cs α]
    have hexp_mul : (∫ y, (α * U y) ^ 2 * Real.exp (-(8 * y))) =
        α ^ 2 * ∫ y, U y ^ 2 * Real.exp (-(8 * y)) := by
      have hpt : (fun y => (α * U y) ^ 2 * Real.exp (-(8 * y))) =
          fun y => α ^ 2 * (U y ^ 2 * Real.exp (-(8 * y))) := funext fun y => by ring
      rw [hpt, integral_const_mul]
    rw [hexp_mul, hα2]
    have hwU := hdeep hcN h4cN
    have hexpU := exponentialMass_normalized_deepPoleOrthogonal_ge
      contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero hcN h4cN
    have hlog_le_N : Real.log (N : ℝ) + 1 ≤ N := by
      have := Real.log_le_sub_one_of_pos hN_pos
      linarith
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hlhs : c N / I₂ * weilQuad U + B ≤ (C_deep / I₂ + |B|) * N := by
      have h1 : c N / I₂ * weilQuad U ≤ (C_deep / I₂) * N := by
        calc c N / I₂ * weilQuad U
            ≤ c N / I₂ * ((C_deep / c N) * (Real.log N + 1)) :=
              mul_le_mul_of_nonneg_left hwU (by positivity)
          _ = (C_deep / I₂) * (Real.log N + 1) := by field_simp [hc0.ne', hI₂.ne']
          _ ≤ (C_deep / I₂) * N := mul_le_mul_of_nonneg_left hlog_le_N (by positivity)
      have h2 : B ≤ |B| * N := (le_abs_self B).trans (le_mul_of_one_le_right (abs_nonneg B) hN1R)
      linarith only [h1, h2, (by ring : (C_deep / I₂) * N + |B| * N = (C_deep / I₂ + |B|) * N)]
    have hrhs : (a * Real.exp (-8) / 3) * (N : ℝ) ^ 8 ≤
        a * (c N / I₂ * ∫ y, U y ^ 2 * Real.exp (-(8 * y))) := by
      have hm := mul_le_mul_of_nonneg_left hexpU (mul_nonneg ha.le (div_nonneg hc0.le hI₂.le))
      have hid : a * (c N / I₂) * ((Real.exp (-8) / (3 * c N)) * I₂ * (N : ℝ) ^ 8) =
          (a * Real.exp (-8) / 3) * (N : ℝ) ^ 8 := by
        field_simp [hc0.ne', hI₂.ne']
      linarith only [hm, hid,
        (by ring : a * (c N / I₂ * ∫ y, U y ^ 2 * Real.exp (-(8 * y))) =
          a * (c N / I₂) * ∫ y, U y ^ 2 * Real.exp (-(8 * y)))]
    have hstrict : (C_deep / I₂ + |B|) * N < (a * Real.exp (-8) / 3) * (N : ℝ) ^ 8 := by
      have hden_pos : 0 < a * Real.exp (-8) / 3 := by positivity
      have hm := (div_le_iff₀ hden_pos).mp hN7
      have h1 : C_deep / I₂ + |B| < (a * Real.exp (-8) / 3) * (N : ℝ) ^ 7 := by linarith
      exact (mul_lt_mul_of_pos_right h1 hN_pos).trans_eq (by ring)
    exact hlhs.trans_lt (hstrict.trans_le hrhs)

/-! ### 3. Interpolated `H¹`/`L²` Lévy bound -/

/-- **Interpolated `H¹`/`L²` bound for `levyEnergy`.**
Splitting `(0, ∞)` at `δ ∈ (0, 1]` bounds small jumps by `δ² ∫ (h')²` via the first-order behavior
`ω(y) ≤ 1 / y` of `archLevyDensity` on `(0, 1]` and large jumps by `((2 + C₁) / δ) ∫ h²`. -/
theorem levyEnergy_le_interpolated {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    levyEnergy h ≤ δ ^ 2 * (∫ u, deriv h u ^ 2) +
      ((2 + levyLipConstant) / δ) * ∫ u, h u ^ 2 := by
  set M := ∫ u, h u ^ 2
  set D := ∫ u, deriv h u ^ 2
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hD : 0 ≤ D := integral_nonneg fun _ => sq_nonneg _
  set L : ℝ → ℝ := fun y => archLevyDensity y * ∫ u, (h u - h (u + y)) ^ 2
  have hLint : IntegrableOn L (Set.Ioi 0) := integrableOn_levyIntegrand hh hhc
  have hfar : ∀ y, 0 < y → L y ≤ 4 * M * archLevyDensity y := fun y hy => by
    dsimp only [L]
    have := integral_sub_shift_sq_le_four hh.continuous hhc y
    nlinarith [(archLevyDensity_pos hy).le]
  have hsplit1 : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hsplit2 : Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 δ ∪ Set.Ioc δ 1 :=
    (Set.Ioc_union_Ioc_eq_Ioc hδ0.le hδ1).symm
  have hI1 : IntegrableOn L (Set.Ioc 0 1) := hLint.mono_set fun _ hy => hy.1
  have hI2 : IntegrableOn L (Set.Ioi 1) :=
    hLint.mono_set fun _ hy => Set.mem_Ioi.mpr (lt_trans one_pos (Set.mem_Ioi.mp hy))
  have hI3 : IntegrableOn L (Set.Ioc 0 δ) := hI1.mono_set fun _ hy => ⟨hy.1, hy.2.trans hδ1⟩
  have hI4 : IntegrableOn L (Set.Ioc δ 1) := hI1.mono_set fun _ hy => ⟨lt_trans hδ0 hy.1, hy.2⟩
  have hunion : ∫ y in Set.Ioi 0, L y =
      (∫ y in Set.Ioc 0 δ, L y) + (∫ y in Set.Ioc δ 1, L y) + ∫ y in Set.Ioi 1, L y := by
    rw [hsplit1, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2,
      hsplit2, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI3 hI4]
  have hnear : ∫ y in Set.Ioc 0 δ, L y ≤ δ ^ 2 * D := by
    let hc : C_c(ℝ, ℝ) := ⟨⟨h, hh.continuous⟩, hhc⟩
    have hb : ∀ y ∈ Set.Ioc 0 δ, L y ≤ δ * D := by
      intro y hy
      have hy0 : 0 < y := hy.1
      have hdens : archLevyDensity y ≤ 1 / y := by
        have h1 := archLevyDensity_le_sqrt_e_div hy0 (hy.2.trans hδ1)
        have h2 : Real.exp (1 / 2 : ℝ) / (2 * y) ≤ 2 / (2 * y) :=
          div_le_div_of_nonneg_right exp_half_le_two (by positivity)
        exact h1.trans (h2.trans_eq (by field_simp [hy0.ne']))
      have htr := BiScaleUncertainty.SobolevShear.integral_compactSource_translation_sq_le hc hh y
      have heq : (∫ u, (h u - h (u + y)) ^ 2) = ∫ u, (hc (u + y) - hc u) ^ 2 :=
        integral_congr_ae (Eventually.of_forall fun u => by
          change (h u - h (u + y)) ^ 2 = (h (u + y) - h u) ^ 2; ring)
      dsimp only [L]
      rw [heq]
      calc archLevyDensity y * ∫ u, (hc (u + y) - hc u) ^ 2
          ≤ (1 / y) * (y ^ 2 * D) :=
            mul_le_mul hdens htr (integral_nonneg fun _ => sq_nonneg _) (by positivity)
        _ = y * D := by field_simp [hy0.ne']
        _ ≤ δ * D := mul_le_mul_of_nonneg_right hy.2 hD
    have hm := setIntegral_mono_on hI3 (integrableOn_const (by simp)) measurableSet_Ioc hb
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hδ0.le, sub_zero] at hm
    nlinarith only [hm]
  have hmid : ∫ y in Set.Ioc δ 1, L y ≤ (2 * Real.log (1 / δ) + Real.exp (1 / 2)) * M := by
    have hinv : IntegrableOn (fun y : ℝ => y⁻¹) (Set.Ioc δ 1) := by
      have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Icc δ 1) :=
        continuousOn_inv₀.mono fun y hy => ne_of_gt (lt_of_lt_of_le hδ0 hy.1)
      exact (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hU : IntegrableOn (fun y : ℝ => 2 * M * y⁻¹ + M * Real.exp (1 / 2)) (Set.Ioc δ 1) :=
      (hinv.const_mul _).add (integrableOn_const (by simp))
    have hb : ∀ y ∈ Set.Ioc δ 1, L y ≤ 2 * M * y⁻¹ + M * Real.exp (1 / 2) := by
      intro y hy
      have hy0 : 0 < y := lt_trans hδ0 hy.1
      have hdens := archLevyDensity_le_inv_two_mul_add hy0 hy.2
      have e : 4 * M * (1 / (2 * y) + Real.exp (1 / 2) / 4) =
          2 * M * y⁻¹ + M * Real.exp (1 / 2) := by
        field_simp; ring
      nlinarith [hfar y hy0, mul_le_mul_of_nonneg_left hdens (by linarith : (0 : ℝ) ≤ 4 * M)]
    have hval : ∫ y in Set.Ioc δ 1, (2 * M * y⁻¹ + M * Real.exp (1 / 2)) =
        2 * M * Real.log (1 / δ) + M * Real.exp (1 / 2) * (1 - δ) := by
      rw [integral_add (hinv.const_mul _) (integrableOn_const (by simp)), integral_const_mul,
        setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hδ1,
        ← intervalIntegral.integral_of_le hδ1, integral_inv_of_pos hδ0 one_pos, one_div]
      ring
    have hm := setIntegral_mono_on hI4 hU measurableSet_Ioc hb
    rw [hval] at hm
    have hsub : M * Real.exp (1 / 2) * (1 - δ) ≤ M * Real.exp (1 / 2) := by
      have : 0 ≤ M * Real.exp (1 / 2) := by positivity
      nlinarith
    nlinarith
  have htail : ∫ y in Set.Ioi 1, L y ≤
      8 * Real.exp (-(1 / 2)) / (1 - Real.exp (-2)) * M := by
    have h2 : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hden : 0 < 1 - Real.exp (-2 : ℝ) := by linarith
    have hexp : IntegrableOn (fun y : ℝ => Real.exp (-(1 / 2) * y)) (Set.Ioi 1) :=
      integrableOn_exp_mul_Ioi (by norm_num) 1
    have hU : IntegrableOn
        (fun y : ℝ => 4 * M / (1 - Real.exp (-2)) * Real.exp (-(1 / 2) * y)) (Set.Ioi 1) :=
      hexp.const_mul _
    have hb : ∀ y ∈ Set.Ioi 1, L y ≤
        4 * M / (1 - Real.exp (-2)) * Real.exp (-(1 / 2) * y) := by
      intro y hy
      have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
      have hdens := archLevyDensity_le_exp_tail hy1
      rw [show -y / 2 = -(1 / 2) * y by ring] at hdens
      calc L y ≤ 4 * M * archLevyDensity y := hfar y (lt_of_lt_of_le one_pos hy1)
        _ ≤ 4 * M * (Real.exp (-(1 / 2) * y) / (1 - Real.exp (-2))) :=
            mul_le_mul_of_nonneg_left hdens (by linarith)
        _ = _ := by ring
    have hm := setIntegral_mono_on hI2 hU measurableSet_Ioi hb
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) 1] at hm
    have e : 4 * M / (1 - Real.exp (-2)) * (-Real.exp (-(1 / 2) * 1) / -(1 / 2)) =
        8 * Real.exp (-(1 / 2)) / (1 - Real.exp (-2)) * M := by
      field_simp; ring_nf
    linarith
  have hlog_inv : 2 * Real.log (1 / δ) + levyLipConstant ≤ (2 + levyLipConstant) / δ := by
    have h1 : Real.log (1 / δ) ≤ 1 / δ - 1 :=
      Real.log_le_sub_one_of_pos (one_div_pos.mpr hδ0)
    have h1d : 1 ≤ 1 / δ := one_le_one_div hδ0 hδ1
    have hC0 : 0 ≤ levyLipConstant := by
      unfold levyLipConstant
      have h2 : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      have hd : 0 < 1 - Real.exp (-2 : ℝ) := by linarith
      positivity
    have h2 : levyLipConstant ≤ levyLipConstant * (1 / δ) :=
      le_mul_of_one_le_right hC0 h1d
    have hdiv : 2 * (1 / δ) + levyLipConstant * (1 / δ) = (2 + levyLipConstant) / δ := by ring
    linarith
  have hM_step := mul_le_mul_of_nonneg_right hlog_inv hM
  unfold levyEnergy
  change (∫ y in Set.Ioi 0, L y) ≤ _
  rw [hunion]
  unfold levyLipConstant at hM_step ⊢
  linarith

/-! ### 4. Refined dyadic seventh-power archimedean Gårding reserve -/

private theorem two_pow_le_linearDefectCutoff' {c : ℝ} (hc1 : 1 ≤ c) {k : ℕ}
    (hk : k ∈ range (dyadicShellCount c)) :
    (2 : ℝ) ^ k ≤ linearDefectCutoff c := by
  obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
  have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
  have hk_le : (k : ℝ) ≤ Real.log (linearDefectCutoff c) / Real.log 2 := by
    have hk_nat : k ≤ ⌊Real.log (linearDefectCutoff c) / Real.log 2⌋₊ :=
      Nat.lt_succ_iff.mp (mem_range.mp hk)
    exact (Nat.cast_le.mpr hk_nat).trans (Nat.floor_le
      (div_nonneg (Real.log_nonneg (by linarith)) (Real.log_pos one_lt_two).le))
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul : (k : ℝ) * Real.log 2 ≤ Real.log (linearDefectCutoff c) := (le_div_iff₀ hl2).mp hk_le
  calc (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
    _ ≤ Real.exp (Real.log (linearDefectCutoff c)) := Real.exp_le_exp.mpr hmul
    _ = linearDefectCutoff c := Real.exp_log (by linarith)

private theorem dyadicShell_seventh_coverage_ge' {c : ℝ} {N : ℕ} (hc1 : 1 ≤ c)
    (hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N) {n : ℕ}
    (hn : n ∈ Ioc (N / linearDefectCutoff c) N) :
    (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) ≤
      ∑ k ∈ range (dyadicShellCount c), (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        dyadicShellBump N k (Real.log n) ^ 2 := by
  obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
  let Lc := linearDefectCutoff c
  let M := N / Lc
  have hL_pos : 0 < Lc := by omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLc_R : (3 : ℝ) ≤ Lc := by exact_mod_cast hL3
  have hNR : (9 : ℝ) ≤ N := (by norm_num : (9 : ℝ) ≤ 3 ^ 2).trans
    ((pow_le_pow_left₀ (by norm_num) hLc_R 2).trans hL2N)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < N := by linarith
  obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) hMn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrat1 : 1 ≤ (N : ℝ) / n := (one_le_div hn0).mpr (by exact_mod_cast hnN)
  have hrat_lt : (N : ℝ) / n < Lc := by
    rw [div_lt_iff₀ hn0]
    have h1 : N < Lc * (M + 1) := Nat.lt_mul_div_succ N hL_pos
    have h2 : Lc * (M + 1) ≤ Lc * n := Nat.mul_le_mul_left Lc hMn
    have h3 : (N : ℝ) < (Lc : ℝ) * n := by exact_mod_cast h1.trans_le h2
    linarith only [h3, (by ring : (Lc : ℝ) * n = (Lc : ℝ) * (n : ℝ))]
  let t := Real.log ((N : ℝ) / n) / Real.log 2
  have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg hrat1) hl2.le
  let k₀ := ⌊t⌋₊
  have hk₀_mem : k₀ ∈ range (dyadicShellCount c) := by
    refine mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono ?_))
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (lt_of_lt_of_le zero_lt_one hrat1) hrat_lt.le) hl2.le
  have hk₀_lo : (k₀ : ℝ) * Real.log 2 ≤ Real.log N - Real.log n := by
    rw [← Real.log_div hN_pos.ne' hn0.ne']
    exact (le_div_iff₀ hl2).mp (Nat.floor_le ht0)
  have hk₀_hi : Real.log N - Real.log n < ((k₀ : ℝ) + 1) * Real.log 2 := by
    rw [← Real.log_div hN_pos.ne' hn0.ne']
    exact (div_lt_iff₀ hl2).mp (Nat.lt_floor_add_one t)
  have hbump1 : dyadicShellBump N k₀ (Real.log n) = 1 := by
    apply dyadicShellBump_eq_one
    have hid : Real.log n - shellCenter N k₀ =
        ((k₀ : ℝ) + 1) * Real.log 2 - (Real.log N - Real.log n) := by
      unfold shellCenter; ring
    rw [hid, abs_of_nonneg (by linarith)]
    have hl2_le1 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hck₀_ub : c * (dyadicShellHorizon N k₀ : ℝ) / N ≤ 8 * c * n / N := by
    have h2k₀_gt : (N : ℝ) / n < 2 * (2 : ℝ) ^ k₀ := by
      have hexp := Real.exp_lt_exp.mpr hk₀_hi
      rw [Real.exp_sub, Real.exp_log hN_pos, Real.exp_log hn0, add_mul, one_mul,
        Real.exp_add, Real.exp_log zero_lt_two,
        show (k₀ : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k₀) by rw [Real.log_pow],
        Real.exp_log (by positivity)] at hexp
      linarith
    have hNk₀ : (dyadicShellHorizon N k₀ : ℝ) ≤ 8 * n := by
      have h1 : (dyadicShellHorizon N k₀ : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k₀ :=
        (Nat.cast_le.mpr (min_le_right N _)).trans (Nat.floor_le (by positivity))
      have h2 : 4 * (N : ℝ) / (2 : ℝ) ^ k₀ ≤ 8 * n := by
        rw [div_le_iff₀ (by positivity)]
        have := (div_lt_iff₀ hn0).mp h2k₀_gt
        linarith
      exact h1.trans h2
    calc c * (dyadicShellHorizon N k₀ : ℝ) / N
        ≤ c * (8 * n) / N := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNk₀ hc0.le) hN_pos.le
      _ = 8 * c * n / N := by ring
  have hNk₀_pos : (0 : ℝ) < dyadicShellHorizon N k₀ := by
    have hdiv1 : (1 : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k₀ := by
      rw [one_le_div (by positivity)]
      have hLc_4N : (Lc : ℝ) ≤ 4 * N := by nlinarith only [hLc_R, hL2N]
      exact (two_pow_le_linearDefectCutoff' hc1 hk₀_mem).trans hLc_4N
    have hpos : 1 ≤ dyadicShellHorizon N k₀ := le_min hN1 ((Nat.one_le_floor_iff _).mpr hdiv1)
    exact_mod_cast hpos
  have hsingle : (1 / (c * (dyadicShellHorizon N k₀ : ℝ) / N) ^ 7) *
        dyadicShellBump N k₀ (Real.log n) ^ 2 ≤
      ∑ k ∈ range (dyadicShellCount c), (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        dyadicShellBump N k (Real.log n) ^ 2 :=
    single_le_sum (f := fun k => (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        dyadicShellBump N k (Real.log n) ^ 2)
      (fun k _ => mul_nonneg (one_div_nonneg.mpr (pow_nonneg (by positivity) 7)) (sq_nonneg _))
      hk₀_mem
  refine le_trans ?_ hsingle
  have hid_inv : ((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7) = 1 / (8 * c * n / N) ^ 7 := by
    field_simp [hN_pos.ne', hn0.ne', hc0.ne']
  rw [hbump1, one_pow, mul_one, hid_inv]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hck₀_ub 7)

/-- Single-shell Lévy reserve retaining the exact `L²` counterterm rather than bounding it by `O(c)`. -/
private theorem levyEnergy_atomicTest_garding_ge {c : ℝ} (hc0 : 1 / 2052 ≤ c) {N : ℕ}
    (hcN : c ≤ N) (z : ℕ → ℝ) :
    ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) * Real.log N *
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, z n ^ 2) -
      (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
        (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) ≤
      levyEnergy (atomicTest N z (atomDilate tiltedUnitSpline (c / N))) := by
  have hc_pos : 0 < c := lt_of_lt_of_le (by norm_num) hc0
  have hNR : (0 : ℝ) < N := hc_pos.trans_le hcN
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this; simp at hNR
  have hw : 0 < c / (N : ℝ) := div_pos hc_pos hNR
  obtain ⟨hg, hgsupp, _⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  have hf := contDiff_atomicTest hg N z
  have hfc := hasCompactSupport_atomicTest hgsupp N z
  have hgamma := archForm_ge_log_band_sub_mass hf hfc hNR
  have hband := noRealZero_highBand_mass contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hc_pos
    (splineBandFloor_pos c) (tiltedUnitSpline_band_floor hc_pos) hN1 z
  have hlev_eq := archForm_eq_levyEnergy hf hfc
  have hM := integral_tiltedUnitSpline_sq_pos
  have hZ : 0 ≤ ∑ n ∈ Icc 1 N, z n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hfl := splineBandFloor_ge_of_ge (by norm_num : (0 : ℝ) < 1 / 2052) (by norm_num) hc0
  have hcoef : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) *
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤
      1 / (2 * Real.pi) * (48 * (c / N) ^ 2 * splineBandFloor c * N) := by
    have hl : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) *
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) =
        24 * ((1 / 2052 : ℝ) ^ 8 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4))) /
          (Real.pi * c ^ 6 * N) := by
      unfold growingMassConstant
      field_simp [hM.ne', hNR.ne', hc_pos.ne', Real.pi_ne_zero]
    have hr : 1 / (2 * Real.pi) * (48 * (c / N) ^ 2 * splineBandFloor c * N) =
        24 * (c ^ 8 * splineBandFloor c) / (Real.pi * c ^ 6 * N) := by
      field_simp [hNR.ne', hc_pos.ne', Real.pi_ne_zero]; ring
    rw [hl, hr]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfl (by norm_num)) (by positivity)
  have hbandTerm : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) * Real.log N *
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, z n ^ 2) ≤
      Real.log N / (2 * Real.pi) * ∫ t in (N : ℝ)..101 * N,
        ‖Zeta23.paperFT (ArithmeticCastelnuovoSeveri.cx
          (atomicTest N z (atomDilate tiltedUnitSpline (c / N)))) (t : ℂ)‖ ^ 2 := by
    calc _ = Real.log N * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) *
          ((c / N) * ∫ u, tiltedUnitSpline u ^ 2)) * (∑ n ∈ Icc 1 N, z n ^ 2) := by ring
      _ ≤ Real.log N * (1 / (2 * Real.pi) * (48 * (c / N) ^ 2 * splineBandFloor c * N)) *
          (∑ n ∈ Icc 1 N, z n ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hlogN) hZ
      _ = Real.log N / (2 * Real.pi) *
          ((48 * (c / N) ^ 2 * splineBandFloor c * N) * (∑ n ∈ Icc 1 N, z n ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hband (by positivity)
  have hf_nn : 0 ≤ ∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hγ : 2 * gammaHardyPhaseRate 0 *
      (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) ≤
      2 * |gammaHardyPhaseRate 0| *
        (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) :=
    mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self (gammaHardyPhaseRate 0)]) hf_nn
  linarith only [hgamma, hlev_eq, hbandTerm, hγ,
    (by ring : (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
      (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) =
      (factorialSpanGammaOffset + Real.log 2) *
        (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) +
      2 * |gammaHardyPhaseRate 0| *
        (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2))]

private theorem dyadicShell_levyEnergy_garding_ge {c : ℝ} {N : ℕ} (hc1 : 1 ≤ c)
    (hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N) (y : ℕ → ℝ) {k : ℕ}
    (hk : k ∈ range (dyadicShellCount c)) :
    ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        (Real.log N / 2) * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) -
      (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
        (∫ u, atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n)
          (atomDilate tiltedUnitSpline (c / N)) u ^ 2) ≤
      levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n)
        (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  let Lc := linearDefectCutoff c
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLc_R : (3 : ℝ) ≤ Lc := by exact_mod_cast hL3
  have hNR : (9 : ℝ) ≤ N := (by norm_num : (9 : ℝ) ≤ 3 ^ 2).trans
    ((pow_le_pow_left₀ (by norm_num) hLc_R 2).trans hL2N)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < N := by linarith
  have hcN : c ≤ (N : ℝ) := by nlinarith [h4c]
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hN_pos
  have hG : 0 < (c / (N : ℝ)) * ∫ u, tiltedUnitSpline u ^ 2 :=
    mul_pos hw integral_tiltedUnitSpline_sq_pos
  have h2k : (2 : ℝ) ^ k ≤ Lc := two_pow_le_linearDefectCutoff' hc1 hk
  let Nk := dyadicShellHorizon N k
  have hsqrt_le : Real.sqrt N ≤ Nk := by
    have hsq : Real.sqrt N * Lc ≤ N := by
      have h1 : (Lc : ℝ) ≤ Real.sqrt N := by
        rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ Lc)]
        exact Real.sqrt_le_sqrt hL2N
      calc Real.sqrt N * Lc ≤ Real.sqrt N * Real.sqrt N :=
            mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
        _ = N := Real.mul_self_sqrt hN_pos.le
    have h4N : Real.sqrt N + 1 ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
      have hdiv : Real.sqrt N ≤ (N : ℝ) / (2 : ℝ) ^ k := by
        rw [le_div_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_left h2k (Real.sqrt_nonneg _)).trans hsq
      have hsq3 : 3 ≤ Real.sqrt N := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_le_sqrt (by linarith)
      calc Real.sqrt N + 1 ≤ 4 * Real.sqrt N := by linarith only [hsq3]
        _ ≤ 4 * ((N : ℝ) / (2 : ℝ) ^ k) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := (mul_div_assoc _ _ _).symm
    have hfl : Real.sqrt N ≤ ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ := by
      have := Nat.lt_floor_add_one (4 * (N : ℝ) / (2 : ℝ) ^ k)
      linarith
    have hN_sq : Real.sqrt N ≤ N := by
      have hsq1 : 1 ≤ Real.sqrt N := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      calc Real.sqrt N = Real.sqrt N * 1 := (mul_one _).symm
        _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
        _ = N := Real.mul_self_sqrt hN_pos.le
    simp only [Nk, dyadicShellHorizon]
    rw [Nat.cast_min, le_min_iff]
    exact ⟨hN_sq, hfl⟩
  have hNk_lb : (N : ℝ) / (2 : ℝ) ^ k ≤ Nk := by
    have hdiv3 : 3 ≤ (N : ℝ) / (2 : ℝ) ^ k := by
      rw [le_div_iff₀ (by positivity)]
      have : 3 * (2 : ℝ) ^ k ≤ (Lc : ℝ) * Lc :=
        mul_le_mul hLc_R h2k (by positivity) (by linarith)
      nlinarith [hL2N]
    have hfl : (N : ℝ) / (2 : ℝ) ^ k ≤ ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ := by
      have h4 : (N : ℝ) / (2 : ℝ) ^ k + 1 ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
        calc (N : ℝ) / (2 : ℝ) ^ k + 1 ≤ 4 * ((N : ℝ) / (2 : ℝ) ^ k) := by linarith only [hdiv3]
          _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := (mul_div_assoc _ _ _).symm
      have := Nat.lt_floor_add_one (4 * (N : ℝ) / (2 : ℝ) ^ k)
      linarith
    have hN_div : (N : ℝ) / (2 : ℝ) ^ k ≤ N :=
      div_le_self hN_pos.le (one_le_pow₀ one_le_two)
    simp only [Nk, dyadicShellHorizon]
    rw [Nat.cast_min, le_min_iff]
    exact ⟨hN_div, hfl⟩
  let ck := c * (Nk : ℝ) / N
  have hNk_pos : (0 : ℝ) < Nk := lt_of_lt_of_le (Real.sqrt_pos.mpr hN_pos) hsqrt_le
  have hck_min : 1 / 2052 ≤ ck := by
    have he2 : Real.exp 2 < 8 := by
      have he1 : Real.exp 1 < 11 / 4 := by have := Real.exp_one_lt_d9; linarith
      have he2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he2']; nlinarith [Real.exp_pos 1]
    have hLc_ub : (Lc : ℝ) ≤ 2052 * c := by nlinarith [hLup, hc0]
    have h1 : c / (2 : ℝ) ^ k ≤ ck := by
      simp only [ck]
      rw [div_le_div_iff₀ (by positivity) hN_pos]
      have := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).mp hNk_lb) hc0.le
      linarith
    have h2 : 1 / 2052 ≤ c / (2 : ℝ) ^ k := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity), one_mul]
      linarith only [h2k, hLc_ub]
    exact h2.trans h1
  have hck_Nk : ck ≤ Nk := by
    simp only [ck]
    rw [div_le_iff₀ hN_pos]
    nlinarith [hcN, hNk_pos]
  have hck_div : ck / Nk = c / N := by
    simp only [ck]
    field_simp [hN_pos.ne', hNk_pos.ne']
  have hlogNk : Real.log N / 2 ≤ Real.log Nk := by
    have h1 := Real.log_le_log (Real.sqrt_pos.mpr hN_pos) hsqrt_le
    rwa [Real.log_sqrt hN_pos.le] at h1
  have hsum_eq : ∑ n ∈ Icc 1 Nk, (dyadicShellBump N k (Real.log n) * y n) ^ 2 =
      ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 := by
    have hsub := sum_subset (Icc_subset_Icc (le_rfl : 1 ≤ 1) (min_le_left N _))
      (f := fun n : ℕ => dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) fun n hn hnot => by
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        have hgt : Nk < n := by
          by_contra hle; exact hnot (mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
        rw [dyadicShellBump_log_eq_zero_of_gt_horizon hN1 hnN hgt, sq, zero_mul, zero_mul]
    rw [← hsub]
    exact sum_congr rfl fun n _ => mul_pow _ _ 2
  have hlev0 := levyEnergy_atomicTest_garding_ge hck_min hck_Nk
    (fun n => dyadicShellBump N k (Real.log n) * y n)
  rw [hck_div, hsum_eq] at hlev0
  have hZ : 0 ≤ ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpos_gain : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / ck ^ 7) * (Real.log N / 2) *
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
      (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) ≤
      ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / ck ^ 7) * Real.log Nk *
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogNk
          (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2052 : ℝ) ^ 8)
            growingMassConstant_pos.le)
            (pow_nonneg (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2052) hck_min).le 7)))
        hG.le)
      hZ
  linarith only [hlev0, hpos_gain]

/-- **Sharpened `O((c² / N) G S)` dyadic commutator bound in `L²` and `levyEnergy`.**
Applying `levyEnergy_le_interpolated` at jump cutoff `δ = c / N` gains a full factor `c / N` over
the pure `H¹` bound `exists_sum_levyEnergy_dyadicCommutator_le`. -/
theorem exists_sum_dyadicCommutator_L2_and_levyEnergy_le :
    ∃ C_comm_g : ℝ, 0 ≤ C_comm_g ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → c ≤ N → ∀ (s : Finset ℕ) (y : ℕ → ℝ),
        (∑ k ∈ s, ∫ u, (dyadicShellBump N k u *
              atomicTest N y (atomDilate tiltedUnitSpline (c / N)) u -
            atomicTest (dyadicShellHorizon N k)
              (fun n => dyadicShellBump N k (Real.log n) * y n)
              (atomDilate tiltedUnitSpline (c / N)) u) ^ 2) ≤
          C_comm_g * (c ^ 2 / N) * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
            (∑ n ∈ Icc 1 N, y n ^ 2) ∧
        (∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u *
              atomicTest N y (atomDilate tiltedUnitSpline (c / N)) u -
            atomicTest (dyadicShellHorizon N k)
              (fun n => dyadicShellBump N k (Real.log n) * y n)
              (atomDilate tiltedUnitSpline (c / N)) u)) ≤
          C_comm_g * (c ^ 2 / N) * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
            (∑ n ∈ Icc 1 N, y n ^ 2) := by
  obtain ⟨L_B, hLB0, hdB, hlipB⟩ := exists_baseShellBump_deriv_bound
  obtain ⟨C₀, hC₀⟩ := hasCompactSupport_tiltedUnitSpline.exists_bound_of_continuous
    contDiff_tiltedUnitSpline.continuous
  obtain ⟨C₁, hC₁⟩ := hasCompactSupport_tiltedUnitSpline.deriv.exists_bound_of_continuous
    (contDiff_tiltedUnitSpline.continuous_deriv (by norm_num))
  set M₀ := max C₀ 0
  set M₁ := max C₁ 0
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hM₁0 : 0 ≤ M₁ := le_max_right _ _
  have hb0 : ∀ t, |tiltedUnitSpline t| ≤ M₀ := fun t => by
    have := hC₀ t; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hb1 : ∀ t, |deriv tiltedUnitSpline t| ≤ M₁ := fun t => by
    have := hC₁ t; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  set K₀ := L_B * (M₀ + M₁)
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hφ2 : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  have hC_lip_nn : 0 ≤ levyLipConstant := by
    unfold levyLipConstant
    have h2 : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hd : 0 < 1 - Real.exp (-2 : ℝ) := by linarith
    positivity
  set C_shell := K₀ ^ 2 + (3 + levyLipConstant) * (L_B * M₀) ^ 2
  have hC_shell0 : 0 ≤ C_shell := by positivity
  set C_comm_g := 13 * C_shell * (Real.exp 1 + 1) / ∫ u, tiltedUnitSpline u ^ 2
  refine ⟨C_comm_g, by positivity, ?_⟩
  intro c N hc1 hcN s y
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by exact_mod_cast hc1.trans hcN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hdiff_φ : Differentiable ℝ tiltedUnitSpline :=
    contDiff_tiltedUnitSpline.differentiable (by norm_num)
  have hdiff_B : Differentiable ℝ (baseShellBump : ℝ → ℝ) :=
    (contDiff_baseShellBump (n := 2)).differentiable (by norm_num)
  have hoverlap : ∀ (S_k : Finset ℕ), S_k ⊆ Icc 1 N → ∀ u : ℝ,
      ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u ≤
        (Real.exp 1 + 1) * c := by
    intro S_k hSub u
    by_cases hu_hi : Real.log N + w < u
    · have hz : ∑ n ∈ S_k,
          (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u = 0 := by
        refine sum_eq_zero fun n hn => Set.indicator_of_notMem ?_ _
        intro hmem
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp (hSub hn)).2
        have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (hSub hn)).1
        have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
        linarith [hmem.2]
      rw [hz]; positivity
    · push Not at hu_hi
      have hsub : S_k.filter (fun n : ℕ => u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)) ⊆
          S_k.filter (fun n : ℕ => Real.exp (u - w) ≤ (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u) := by
        intro n hn
        obtain ⟨hnS, hmem⟩ := mem_filter.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (hSub hnS)).1
        refine mem_filter.mpr ⟨hnS, ?_, ?_⟩
        · rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr (by linarith [hmem.2])
        · rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hmem.1
      have hsum_ind : ∑ n ∈ S_k,
          (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u =
          ((S_k.filter fun n : ℕ =>
            u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)).card : ℝ) := by
        have heq : ∑ n ∈ S_k,
            (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u =
            ∑ _n ∈ S_k.filter (fun n : ℕ =>
              u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)), (1 : ℝ) := by
          symm
          rw [sum_filter (s := S_k)]
          refine sum_congr rfl fun n _ => ?_
          by_cases hm : u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w) <;> simp [hm]
        rw [heq, sum_const, nsmul_eq_mul, mul_one]
      rw [hsum_ind]
      have hcard := (Nat.cast_le.mpr (card_le_card hsub)).trans
        (card_filter_mem_Icc_real_le S_k (Real.exp_le_exp.mpr (by linarith)))
      have hexpu : Real.exp u ≤ Real.exp 1 * N := by
        calc Real.exp u ≤ Real.exp (Real.log N + w) := Real.exp_le_exp.mpr hu_hi
          _ = (N : ℝ) * Real.exp w := by rw [Real.exp_add, Real.exp_log hNR]
          _ ≤ (N : ℝ) * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hNR.le
          _ = Real.exp 1 * N := by ring
      have hdiff_exp : Real.exp u - Real.exp (u - w) ≤ Real.exp 1 * c := by
        have h1 : 1 - Real.exp (-w) ≤ w := by linarith [Real.add_one_le_exp (-w)]
        have h0 : 0 ≤ 1 - Real.exp (-w) := by
          have := Real.exp_le_one_iff.mpr (show -w ≤ 0 by linarith); linarith
        calc Real.exp u - Real.exp (u - w)
            = Real.exp u * (1 - Real.exp (-w)) := by
              rw [show u - w = u + (-w) by ring, Real.exp_add]; ring
          _ ≤ (Real.exp 1 * N) * w := mul_le_mul hexpu h1 h0 (by positivity)
          _ = Real.exp 1 * c := by dsimp only [w]; field_simp [hNR.ne']
      linarith only [hcard, hdiff_exp, hc1]
  have hshell : ∀ k ∈ s,
      (∫ u, (dyadicShellBump N k u * atomicTest N y g u -
          atomicTest (dyadicShellHorizon N k)
            (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ^ 2) ≤
        C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 *
          (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
            y n ^ 2) ∧
      levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
          atomicTest (dyadicShellHorizon N k)
            (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ≤
        C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 *
          (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
            y n ^ 2) := by
    intro k _
    rw [atomicTest_dyadicShellHorizon_eq hN1 y g]
    let S_k : Finset ℕ :=
      (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3)
    let h_atom : ℕ → ℝ → ℝ := fun n u =>
      (dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) * g (u - Real.log n)
    have hR_eq : (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) =
        fun u => ∑ n ∈ S_k, y n * h_atom n u := by
      funext u
      unfold atomicTest
      rw [mul_sum, ← sum_sub_distrib]
      have hfull : ∑ x ∈ Icc 1 N, (dyadicShellBump N k u * (y x * g (u - Real.log x)) -
          dyadicShellBump N k (Real.log x) * y x * g (u - Real.log x)) =
          ∑ x ∈ Icc 1 N, y x * h_atom x u :=
        sum_congr rfl fun n _ => by dsimp only [h_atom]; ring
      rw [hfull]
      refine (sum_subset (filter_subset _ _) fun n hn hnot => ?_).symm
      have hgt3 : 3 < |Real.log (n : ℝ) - shellCenter N k| :=
        lt_of_not_ge fun hle => hnot (mem_filter.mpr ⟨hn, hle⟩)
      dsimp only [h_atom]
      by_cases huw : u - Real.log n ∈ Set.Icc 0 w
      · obtain ⟨hu0, huw'⟩ := Set.mem_Icc.mp huw
        have h1 : 2 ≤ |Real.log (n : ℝ) - shellCenter N k| := by linarith
        have h2 : 2 ≤ |u - shellCenter N k| := by
          have htri := abs_sub_abs_le_abs_sub (Real.log (n : ℝ) - shellCenter N k)
            (Real.log (n : ℝ) - u)
          have hdu : |Real.log (n : ℝ) - u| ≤ 1 := by
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          have hid : (Real.log (n : ℝ) - shellCenter N k) - (Real.log (n : ℝ) - u) =
              u - shellCenter N k := by ring
          rw [hid] at htri; linarith
        rw [dyadicShellBump_eq_zero h2, dyadicShellBump_eq_zero h1, sub_self, zero_mul, mul_zero]
      · dsimp only [g]
        rw [hsupp _ huw, mul_zero, mul_zero]
    have hR_pt : ∀ u, dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u =
        ∑ n ∈ S_k, y n * h_atom n u := congrFun hR_eq
    have hRk_cd : ContDiff ℝ 2 (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) :=
      ((contDiff_dyadicShellBump N k).mul (contDiff_atomicTest hg N y)).sub
        (contDiff_atomicTest hg N _)
    have hRk_cs : HasCompactSupport (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) :=
      ((hasCompactSupport_atomicTest hsupp N y).mul_left).sub
        (hasCompactSupport_atomicTest hsupp N _)
    have hinterp := levyEnergy_le_interpolated hRk_cd hRk_cs hw hw1
    rw [hR_eq] at hinterp hRk_cd hRk_cs ⊢
    simp_rw [hR_pt] at hinterp ⊢
    have hh_diff : ∀ n : ℕ, Differentiable ℝ (h_atom n) := fun n =>
      (((contDiff_dyadicShellBump N k).sub contDiff_const).mul
        (hg.comp (contDiff_id.sub contDiff_const))).differentiable (by norm_num)
    have hval_atom : ∀ (n : ℕ) (u : ℝ),
        |h_atom n u| ≤
          (L_B * M₀ * w) * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
      intro n u
      by_cases huI : u ∈ Set.Icc (Real.log n) (Real.log n + w)
      · rw [Set.indicator_of_mem huI, mul_one]
        obtain ⟨hu_lo, hu_hi⟩ := Set.mem_Icc.mp huI
        have hv1 : |dyadicShellBump N k u - dyadicShellBump N k (Real.log n)| ≤ L_B * w := by
          have hl := hlipB (u - shellCenter N k) (Real.log n - shellCenter N k)
          have hd : |(u - shellCenter N k) - (Real.log n - shellCenter N k)| ≤ w := by
            rw [show (u - shellCenter N k) - (Real.log n - shellCenter N k) = u - Real.log n by ring,
              abs_of_nonneg (by linarith)]
            linarith
          exact hl.trans (mul_le_mul_of_nonneg_left hd hLB0)
        dsimp only [h_atom]
        rw [abs_mul]
        exact (mul_le_mul hv1 (hb0 _) (abs_nonneg _) (mul_nonneg hLB0 hw.le)).trans_eq (by ring)
      · rw [Set.indicator_of_notMem huI, mul_zero]
        have hvw : u - Real.log n ∉ Set.Icc 0 w := fun hmem =>
          huI (Set.mem_Icc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
        dsimp only [h_atom, g]
        rw [hsupp _ hvw, mul_zero, abs_zero]
    have hderiv_atom : ∀ (n : ℕ) (u : ℝ),
        |deriv (h_atom n) u| ≤
          K₀ * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
      intro n u
      by_cases huI : u ∈ Set.Icc (Real.log n) (Real.log n + w)
      · rw [Set.indicator_of_mem huI, mul_one]
        obtain ⟨hu_lo, hu_hi⟩ := Set.mem_Icc.mp huI
        have hd1 : HasDerivAt (fun v => dyadicShellBump N k v - dyadicShellBump N k (Real.log n))
            (deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k)) u := by
          have hsub1 : HasDerivAt (fun v : ℝ => v - shellCenter N k) 1 u :=
            (hasDerivAt_id u).sub_const (shellCenter N k)
          have hcomp1 := (hdiff_B.differentiableAt.hasDerivAt).comp u hsub1
          simpa only [Function.comp_def, id_eq, mul_one, dyadicShellBump] using
            hcomp1.sub_const (dyadicShellBump N k (Real.log n))
        have hd2 : HasDerivAt (fun v => g (v - Real.log n))
            (deriv tiltedUnitSpline ((u - Real.log n) / w) / w) u := by
          have hsub : HasDerivAt (fun v : ℝ => (v - Real.log n) / w) (1 / w) u :=
            ((hasDerivAt_id u).sub_const (Real.log n)).div_const w
          have hcomp := (hdiff_φ.differentiableAt.hasDerivAt).comp u hsub
          simpa only [Function.comp_def, id_eq, mul_one_div, g, atomDilate] using hcomp
        have hdmul := (hd1.mul hd2).deriv
        change deriv (h_atom n) u = _ at hdmul
        rw [hdmul]
        have hv1 : |dyadicShellBump N k u - dyadicShellBump N k (Real.log n)| ≤ L_B * w := by
          have hl := hlipB (u - shellCenter N k) (Real.log n - shellCenter N k)
          have hd : |(u - shellCenter N k) - (Real.log n - shellCenter N k)| ≤ w := by
            rw [show (u - shellCenter N k) - (Real.log n - shellCenter N k) = u - Real.log n by ring,
              abs_of_nonneg (by linarith)]
            linarith
          exact hl.trans (mul_le_mul_of_nonneg_left hd hLB0)
        have hd2_le : |deriv tiltedUnitSpline ((u - Real.log n) / w) / w| ≤ M₁ / w := by
          rw [abs_div, abs_of_pos hw]; exact div_le_div_of_nonneg_right (hb1 _) hw.le
        calc |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k) * g (u - Real.log n) +
              (dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) *
                (deriv tiltedUnitSpline ((u - Real.log n) / w) / w)|
            ≤ |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k)| * |g (u - Real.log n)| +
                |dyadicShellBump N k u - dyadicShellBump N k (Real.log n)| *
                  |deriv tiltedUnitSpline ((u - Real.log n) / w) / w| :=
              (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
          _ ≤ L_B * M₀ + (L_B * w) * (M₁ / w) :=
              add_le_add (mul_le_mul (hdB _) (hb0 _) (abs_nonneg _) hLB0)
                (mul_le_mul hv1 hd2_le (abs_nonneg _) (mul_nonneg hLB0 hw.le))
          _ = K₀ := by dsimp only [K₀]; field_simp [hw.ne']
      · rw [Set.indicator_of_notMem huI, mul_zero]
        have hev : h_atom n =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
          refine Filter.eventually_of_mem (isClosed_Icc.isOpen_compl.mem_nhds huI) fun v hv => ?_
          have hvw : v - Real.log n ∉ Set.Icc 0 w := fun hmem =>
            hv (Set.mem_Icc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
          dsimp only [h_atom, g]
          rw [hsupp _ hvw, mul_zero]
        rw [hev.deriv_eq, deriv_const, abs_zero]
    have hint_ind : ∀ n : ℕ,
        Integrable (fun u => y n ^ 2 *
          (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u) := fun n =>
      ((integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator
        measurableSet_Icc).const_mul (y n ^ 2)
    have hind_int : ∀ n : ℕ,
        (∫ u, y n ^ 2 *
          (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u) =
          w * y n ^ 2 := fun n => by
      rw [integral_const_mul, MeasureTheory.integral_indicator measurableSet_Icc, setIntegral_const,
        smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
      ring
    have hcs_ind : ∀ {A : ℝ} (f_n : ℕ → ℝ → ℝ), 0 ≤ A →
        (∀ (n : ℕ) (u : ℝ), |f_n n u| ≤
          A * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u) →
        ∀ u : ℝ, (∑ n ∈ S_k, y n * f_n n u) ^ 2 ≤
          A ^ 2 * ((Real.exp 1 + 1) * c) *
            ∑ n ∈ S_k, y n ^ 2 *
              (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
      intro A f_n hA0 hfn u
      let ind : ℕ → ℝ := fun n =>
        (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u
      have hind_sq : ∀ n, ind n ^ 2 = ind n := fun n => by
        dsimp only [ind]; by_cases hm : u ∈ Set.Icc (Real.log n) (Real.log n + w) <;> simp [hm]
      have hind0 : ∀ n, 0 ≤ ind n := fun n => by
        dsimp only [ind]; by_cases hm : u ∈ Set.Icc (Real.log n) (Real.log n + w) <;> simp [hm]
      have habs : |∑ n ∈ S_k, y n * f_n n u| ≤ A * ∑ n ∈ S_k, ind n * (|y n| * ind n) := by
        calc |∑ n ∈ S_k, y n * f_n n u|
            ≤ ∑ n ∈ S_k, |y n * f_n n u| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ S_k, |y n| * (A * ind n) :=
              sum_le_sum fun n _ => by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hfn n u) (abs_nonneg _)
          _ = A * ∑ n ∈ S_k, ind n * (|y n| * ind n) := by
              rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
              rw [show ind n * (|y n| * ind n) = |y n| * ind n ^ 2 by ring, hind_sq n]; ring
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs, mul_pow] at hsq
      have hcs := sum_mul_sq_le_sq_mul_sq S_k ind (fun n => |y n| * ind n)
      calc (∑ n ∈ S_k, y n * f_n n u) ^ 2
          ≤ A ^ 2 * ((∑ n ∈ S_k, ind n ^ 2) * ∑ n ∈ S_k, (|y n| * ind n) ^ 2) :=
            hsq.trans (mul_le_mul_of_nonneg_left hcs (sq_nonneg A))
        _ = A ^ 2 * (∑ n ∈ S_k, ind n) * ∑ n ∈ S_k, y n ^ 2 * ind n := by
            simp_rw [mul_pow, sq_abs, hind_sq]; ring
        _ ≤ A ^ 2 * ((Real.exp 1 + 1) * c) * ∑ n ∈ S_k, y n ^ 2 * ind n :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hoverlap S_k (filter_subset _ _) u) (sq_nonneg A))
              (sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hind0 n))
    have hL2_Rk : (∫ u, (∑ n ∈ S_k, y n * h_atom n u) ^ 2) ≤
        (L_B * M₀) ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 3 * ∑ n ∈ S_k, y n ^ 2 := by
      have hm := integral_mono (integrable_sq_of_continuous hRk_cd.continuous hRk_cs)
        ((integrable_finsetSum S_k fun n _ => hint_ind n).const_mul
          ((L_B * M₀ * w) ^ 2 * ((Real.exp 1 + 1) * c)))
        (hcs_ind h_atom (by positivity) hval_atom)
      rw [integral_const_mul, integral_finsetSum S_k fun n _ => hint_ind n] at hm
      simp_rw [hind_int, ← mul_sum] at hm
      exact hm.trans_eq (by ring)
    have hH1_Rk : (∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2) ≤
        K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w * ∑ n ∈ S_k, y n ^ 2 := by
      have hpt_d : ∀ u : ℝ, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2 ≤
          K₀ ^ 2 * ((Real.exp 1 + 1) * c) *
            ∑ n ∈ S_k, y n ^ 2 *
              (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
        intro u
        have hdsum : deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u =
            ∑ n ∈ S_k, y n * deriv (h_atom n) u := by
          have h0 : HasDerivAt (∑ n ∈ S_k, fun v => y n * h_atom n v)
              (∑ n ∈ S_k, y n * deriv (h_atom n) u) u :=
            HasDerivAt.sum fun n (_ : n ∈ S_k) => ((hh_diff n u).hasDerivAt).const_mul (y n)
          have hfn : (∑ n ∈ S_k, fun v => y n * h_atom n v) =
              fun v => ∑ n ∈ S_k, y n * h_atom n v := funext fun v => Finset.sum_apply v S_k _
          rw [hfn] at h0
          exact h0.deriv
        rw [hdsum]
        exact hcs_ind (fun n v => deriv (h_atom n) v) hK₀0 hderiv_atom u
      have hm := integral_mono
        (integrable_sq_of_continuous (hRk_cd.continuous_deriv (by norm_num)) hRk_cs.deriv)
        ((integrable_finsetSum S_k fun n _ => hint_ind n).const_mul
          (K₀ ^ 2 * ((Real.exp 1 + 1) * c))) hpt_d
      rw [integral_const_mul, integral_finsetSum S_k fun n _ => hint_ind n] at hm
      simp_rw [hind_int, ← mul_sum] at hm
      exact hm.trans_eq (by ring)
    have hS0 : 0 ≤ ∑ n ∈ S_k, y n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hw3_le : w ^ 3 ≤ w ^ 2 := by
      have : w ^ 3 = w ^ 2 * w := by ring
      rw [this]
      exact mul_le_of_le_one_right (sq_nonneg w) hw1
    refine ⟨?_, ?_⟩
    · have h1 : (L_B * M₀) ^ 2 ≤ C_shell := by
        dsimp only [C_shell]
        nlinarith [sq_nonneg K₀, sq_nonneg (L_B * M₀), hC_lip_nn]
      calc (∫ u, (∑ n ∈ S_k, y n * h_atom n u) ^ 2)
          ≤ (L_B * M₀) ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 3 * ∑ n ∈ S_k, y n ^ 2 := hL2_Rk
        _ ≤ (L_B * M₀) ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 2 * ∑ n ∈ S_k, y n ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hw3_le (by positivity)) hS0
        _ ≤ C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 * ∑ n ∈ S_k, y n ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h1 (by positivity)) (sq_nonneg w)) hS0
    · have hterm1 : w ^ 2 * (∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2) ≤
          K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 2 * ∑ n ∈ S_k, y n ^ 2 := by
        calc w ^ 2 * (∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2)
            ≤ w ^ 2 * (K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w * ∑ n ∈ S_k, y n ^ 2) :=
              mul_le_mul_of_nonneg_left hH1_Rk (sq_nonneg w)
          _ = K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 3 * ∑ n ∈ S_k, y n ^ 2 := by ring
          _ ≤ K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 2 * ∑ n ∈ S_k, y n ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hw3_le (by positivity)) hS0
      have hterm2 : ((2 + levyLipConstant) / w) * (∫ u, (∑ n ∈ S_k, y n * h_atom n u) ^ 2) ≤
          (2 + levyLipConstant) * (L_B * M₀) ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 2 *
            ∑ n ∈ S_k, y n ^ 2 := by
        calc ((2 + levyLipConstant) / w) * (∫ u, (∑ n ∈ S_k, y n * h_atom n u) ^ 2)
            ≤ ((2 + levyLipConstant) / w) *
                ((L_B * M₀) ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 3 * ∑ n ∈ S_k, y n ^ 2) :=
              mul_le_mul_of_nonneg_left hL2_Rk (by positivity)
          _ = (2 + levyLipConstant) * (L_B * M₀) ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 2 *
                ∑ n ∈ S_k, y n ^ 2 := by
              field_simp [hw.ne']
      have hsum12 : K₀ ^ 2 + (2 + levyLipConstant) * (L_B * M₀) ^ 2 ≤ C_shell := by
        dsimp only [C_shell]
        nlinarith [sq_nonneg (L_B * M₀)]
      have hstep := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsum12 (by positivity : 0 ≤ (Real.exp 1 + 1) * c))
          (sq_nonneg w)) hS0
      change levyEnergy (fun u => ∑ n ∈ S_k, y n * h_atom n u) ≤
        C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 * ∑ n ∈ S_k, y n ^ 2
      linarith only [hinterp, hterm1, hterm2, hstep,
        (by ring : K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 2 * (∑ n ∈ S_k, y n ^ 2) +
          (2 + levyLipConstant) * (L_B * M₀) ^ 2 * ((Real.exp 1 + 1) * c) * w ^ 2 *
            (∑ n ∈ S_k, y n ^ 2) =
          (K₀ ^ 2 + (2 + levyLipConstant) * (L_B * M₀) ^ 2) *
            ((Real.exp 1 + 1) * c) * w ^ 2 * (∑ n ∈ S_k, y n ^ 2))]
  have hswap : ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter
        (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3), y n ^ 2 ≤
      13 * ∑ n ∈ Icc 1 N, y n ^ 2 := by
    have heq : ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter
          (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3), y n ^ 2 =
        ∑ n ∈ Icc 1 N,
          ((s.filter fun k => |Real.log (n : ℝ) - shellCenter N k| ≤ 3).card : ℝ) * y n ^ 2 := by
      simp_rw [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun n _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    rw [heq, mul_sum]
    refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact (card_shellCenter_near_le s N (Real.log n) (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
      (by norm_num)
  have hid_rhs : C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 * (13 * ∑ n ∈ Icc 1 N, y n ^ 2) =
      C_comm_g * (c ^ 2 / N) * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        ∑ n ∈ Icc 1 N, y n ^ 2 := by
    dsimp only [C_comm_g, w]
    field_simp [hφ2.ne', hNR.ne']
  refine ⟨?_, ?_⟩
  · calc ∑ k ∈ s, _
        ≤ ∑ k ∈ s, C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 *
            ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
              y n ^ 2 := sum_le_sum fun k hk => (hshell k hk).1
      _ = C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 *
            ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter
              (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3), y n ^ 2 := by
          rw [← mul_sum]
      _ ≤ C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 * (13 * ∑ n ∈ Icc 1 N, y n ^ 2) :=
          mul_le_mul_of_nonneg_left hswap (by positivity)
      _ = _ := hid_rhs
  · calc ∑ k ∈ s, _
        ≤ ∑ k ∈ s, C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 *
            ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
              y n ^ 2 := sum_le_sum fun k hk => (hshell k hk).2
      _ = C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 *
            ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter
              (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3), y n ^ 2 := by
          rw [← mul_sum]
      _ ≤ C_shell * ((Real.exp 1 + 1) * c) * w ^ 2 * (13 * ∑ n ∈ Icc 1 N, y n ^ 2) :=
          mul_le_mul_of_nonneg_left hswap (by positivity)
      _ = _ := hid_rhs

/-- **Dyadic seventh-power archimedean Gårding reserve on the top collar.**
Retaining a pure `L²` shift `B_arch ∫ f_y²` eliminates the `O(c)` mass penalty of
`exists_top_archForm_dyadic_seventh_reserve`, leaving only an infinitesimal `O(c² / N)` discrete
commutator defect against `(dyadicTopMassConstant / c⁷) log N`. -/
theorem exists_top_archForm_dyadic_seventh_reserve_garding :
    ∃ B_arch C_err : ℝ, 0 ≤ B_arch ∧ 0 ≤ C_err ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → (linearDefectCutoff c : ℝ) ^ 2 ≤ N → ∀ x : ℕ → ℝ,
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
          (((dyadicTopMassConstant / c ^ 7) * Real.log N - C_err * (c ^ 2 / N)) *
            topCollarSeventhMass (N / linearDefectCutoff c) N x) ≤
          archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
              (atomDilate tiltedUnitSpline (c / N))) +
            B_arch * ∫ u, atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
              (atomDilate tiltedUnitSpline (c / N)) u ^ 2 := by
  obtain ⟨L_B, hLB0, -, hlipB⟩ := exists_baseShellBump_deriv_bound
  obtain ⟨C_comm_g, hCg0, hcomm_g⟩ := exists_sum_dyadicCommutator_L2_and_levyEnergy_le
  set K₀_low := factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|
  have hK₀_low0 : 0 ≤ K₀_low :=
    add_nonneg (add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg one_le_two))
      (by positivity)
  set B_arch := (9 * K₀_low + 648 * L_B ^ 2) / 18 + 2 * |gammaHardyPhaseRate 0|
  set C_err := (K₀_low + 1) * C_comm_g / 18
  refine ⟨B_arch, C_err, by positivity, by positivity, ?_⟩
  intro c N hc1 hL2N x
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  let Lc := linearDefectCutoff c
  let M := N / Lc
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLc_R : (3 : ℝ) ≤ Lc := by exact_mod_cast hL3
  have hNR : (9 : ℝ) ≤ N := (by norm_num : (9 : ℝ) ≤ 3 ^ 2).trans
    ((pow_le_pow_left₀ (by norm_num) hLc_R 2).trans hL2N)
  have hN_pos : (0 : ℝ) < N := by linarith
  have hcN : c ≤ (N : ℝ) := by nlinarith [h4c]
  have hMN : M ≤ N := Nat.div_le_self N Lc
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hN_pos
  let g := atomDilate tiltedUnitSpline w
  let G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  let y := atomicTailCoefficients M x
  have hy_eq : ∑ n ∈ Icc 1 N, y n ^ 2 = ∑ n ∈ Ioc M N, x n ^ 2 :=
    sum_atomicTailCoefficients_sq_eq_Ioc' hMN x
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  let s := range (dyadicShellCount c)
  -- Sum the shell Lévy energies with pure L² counterterms
  have hsum_F : G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
        Real.log N * topCollarSeventhMass M N x) -
      K₀_low * ∑ k ∈ s, ∫ u, atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g u ^ 2 ≤
      ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g) := by
    have hshell : ∀ k ∈ s,
        ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
          (Real.log N / 2) * G *
          (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) -
        K₀_low * ∫ u, atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g u ^ 2 ≤
        levyEnergy (atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g) :=
      fun k hk => dyadicShell_levyEnergy_garding_ge hc1 hL2N y hk
    refine le_trans ?_ (sum_le_sum hshell)
    rw [sum_sub_distrib, ← mul_sum]
    refine sub_le_sub_right ?_ _
    have hrestrict : ∀ k : ℕ,
        ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 =
          ∑ n ∈ Ioc M N, dyadicShellBump N k (Real.log n) ^ 2 * x n ^ 2 := fun k => by
      have hIoc : (Ioc M N : Finset ℕ) ⊆ Icc 1 N := fun n hn =>
        mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) (mem_Ioc.mp hn).1),
          (mem_Ioc.mp hn).2⟩
      rw [← sum_subset hIoc fun n hn hnot => by
        have hle : n ≤ M := by
          by_contra hgt; exact hnot (mem_Ioc.mpr ⟨not_le.mp hgt, (mem_Icc.mp hn).2⟩)
        have hy0 : y n = 0 := if_neg (Nat.not_lt.mpr hle)
        rw [hy0]; ring]
      exact sum_congr rfl fun n hn => by
        have hyx : y n = x n := if_pos (mem_Ioc.mp hn).1
        rw [hyx]
    simp_rw [hrestrict]
    have hswap : ∑ k ∈ s,
        ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
          (Real.log N / 2) * G *
          (∑ n ∈ Ioc M N, dyadicShellBump N k (Real.log n) ^ 2 * x n ^ 2) =
        G * ((1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) *
          ∑ n ∈ Ioc M N, (∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun n _ => ?_
      rw [sum_mul, mul_sum, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [hswap]
    refine mul_le_mul_of_nonneg_left ?_ hG.le
    have h1 : ∑ n ∈ Ioc M N, (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) * x n ^ 2 ≤
        ∑ n ∈ Ioc M N, (∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
          dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2 :=
      sum_le_sum fun n hn =>
        mul_le_mul_of_nonneg_right (dyadicShell_seventh_coverage_ge' hc1 hL2N hn) (sq_nonneg _)
    have hlog0 : 0 ≤ (1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) :=
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2052 : ℝ) ^ 8)
        growingMassConstant_pos.le) (div_nonneg (Real.log_natCast_nonneg N) zero_le_two)
    calc ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
          Real.log N * topCollarSeventhMass M N x
        = (1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) *
            ∑ n ∈ Ioc M N, (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) * x n ^ 2 := by
          unfold topCollarSeventhMass
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun n _ => ?_
          rw [show 2 * (8 : ℝ) ^ 7 * c ^ 7 = (8 ^ 7 * c ^ 7) * 2 by ring, ← div_div,
            div_eq_mul_one_div _ (8 ^ 7 * c ^ 7), div_eq_mul_one_div _ (8 ^ 7 * c ^ 7)]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hlog0
  -- Bound `∑ ∫ F_k²` by `18 ∫ f_y² + 2 ∑ ∫ R_k²`
  have hFk_L2_sum : (∑ k ∈ s, ∫ u, atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g u ^ 2) ≤
      18 * (∫ u, atomicTest N y g u ^ 2) +
        2 * ∑ k ∈ s, ∫ u, (dyadicShellBump N k u * atomicTest N y g u -
          atomicTest (dyadicShellHorizon N k)
            (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ^ 2 := by
    have hterm : ∀ k ∈ s,
        (∫ u, atomicTest (dyadicShellHorizon N k)
            (fun n => dyadicShellBump N k (Real.log n) * y n) g u ^ 2) ≤
          2 * (∫ u, (dyadicShellBump N k u * atomicTest N y g u) ^ 2) +
            2 * ∫ u, (dyadicShellBump N k u * atomicTest N y g u -
              atomicTest (dyadicShellHorizon N k)
                (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ^ 2 := by
      intro k _
      let a_k : ℝ → ℝ := fun u => dyadicShellBump N k u * atomicTest N y g u
      let F_k : ℝ → ℝ := atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g
      have hak : Continuous a_k := (contDiff_dyadicShellBump N k).continuous.mul hfy.continuous
      have hakc : HasCompactSupport a_k := hfyc.mul_left
      have hFk : Continuous F_k := (contDiff_atomicTest hg _ _).continuous
      have hFkc : HasCompactSupport F_k := hasCompactSupport_atomicTest hsupp _ _
      have hi_a : Integrable (fun u => a_k u ^ 2) := integrable_sq_of_continuous hak hakc
      have hi_r : Integrable (fun u => (a_k u - F_k u) ^ 2) :=
        integrable_sq_of_continuous (hak.sub hFk) (hakc.sub hFkc)
      have hi_F : Integrable (fun u => F_k u ^ 2) := integrable_sq_of_continuous hFk hFkc
      have hm := integral_mono hi_F ((hi_a.const_mul 2).add (hi_r.const_mul 2)) fun u => by
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (2 * a_k u - F_k u)]
      change (∫ x, F_k x ^ 2) ≤ ∫ x, (2 * a_k x ^ 2 + 2 * (a_k x - F_k x) ^ 2) at hm
      rwa [integral_add (hi_a.const_mul 2) (hi_r.const_mul 2),
        integral_const_mul, integral_const_mul] at hm
    have hsum_a : (∑ k ∈ s, ∫ u, (dyadicShellBump N k u * atomicTest N y g u) ^ 2) ≤
        9 * ∫ u, atomicTest N y g u ^ 2 := by
      have hi_k : ∀ k ∈ s, Integrable (fun u => (dyadicShellBump N k u * atomicTest N y g u) ^ 2) :=
        fun k _ => integrable_sq_of_continuous
          ((contDiff_dyadicShellBump N k).continuous.mul hfy.continuous) hfyc.mul_left
      rw [← integral_finsetSum s hi_k, ← integral_const_mul]
      refine integral_mono (integrable_finsetSum s hi_k)
        ((integrable_sq_of_continuous hfy.continuous hfyc).const_mul 9) fun u => ?_
      simp_rw [mul_pow, ← sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      calc ∑ k ∈ s, dyadicShellBump N k u ^ 2
          ≤ ∑ k ∈ s, (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) :=
            sum_le_sum fun k _ => by
              split_ifs with hle
              · nlinarith [dyadicShellBump_nonneg N k u, dyadicShellBump_le_one N k u]
              · rw [dyadicShellBump_eq_zero (le_of_not_ge hle), sq, zero_mul]
        _ ≤ 9 := by
            rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
            exact (card_shellCenter_near_le s N u (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
    have hsum_t := sum_le_sum hterm
    rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum_t
    linarith only [hsum_t, hsum_a]
  -- Triangle + IMS + sharpened commutator
  have htri_sum : (1 / 2 : ℝ) * ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g) -
      ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ≤
      ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun k _ => ?_
    let a_k : ℝ → ℝ := fun u => dyadicShellBump N k u * atomicTest N y g u
    let F_k : ℝ → ℝ := atomicTest (dyadicShellHorizon N k)
      (fun n => dyadicShellBump N k (Real.log n) * y n) g
    have hak : ContDiff ℝ 2 a_k := (contDiff_dyadicShellBump N k).mul hfy
    have hakc : HasCompactSupport a_k := hfyc.mul_left
    have hFk : ContDiff ℝ 2 F_k := contDiff_atomicTest hg _ _
    have hFkc : HasCompactSupport F_k := hasCompactSupport_atomicTest hsupp _ _
    have heq : F_k = fun u => a_k u - (a_k u - F_k u) := funext fun _ => by ring
    have hsub := levyEnergy_sub_le_two_mul hak hakc (hak.sub hFk) (hakc.sub hFkc)
    rw [← heq] at hsub
    linarith only [hsub]
  have hims := sum_levyEnergy_dyadicShellBump_mul_le hlipB s N hfy hfyc
  obtain ⟨hcomm_L2, hcomm_lev⟩ := hcomm_g hc1 hcN s y
  rw [hy_eq] at hcomm_L2 hcomm_lev
  have harch_eq := archForm_eq_levyEnergy hfy hfyc
  have hfy_nn : 0 ≤ ∫ u, atomicTest N y g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hγ_fy : -2 * |gammaHardyPhaseRate 0| * ∫ u, atomicTest N y g u ^ 2 ≤
      2 * gammaHardyPhaseRate 0 * ∫ u, atomicTest N y g u ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [neg_abs_le (gammaHardyPhaseRate 0)]) hfy_nn
  have hS_le_S7 := sum_sq_Ioc_le_topCollarSeventhMass M N x
  have h18 : 18 * levyEnergy (atomicTest N y g) +
      (9 * K₀_low + 648 * L_B ^ 2) * (∫ u, atomicTest N y g u ^ 2) ≥
      G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (4 * 8 ^ 7 * c ^ 7)) *
        Real.log N * topCollarSeventhMass M N x) -
      (K₀_low + 1) * C_comm_g * (c ^ 2 / N) * G * topCollarSeventhMass M N x := by
    have hFk_mul := mul_le_mul_of_nonneg_left hFk_L2_sum hK₀_low0
    have hcomm_L2_mul := mul_le_mul_of_nonneg_left hcomm_L2 hK₀_low0
    have herr_S7 : (K₀_low + 1) * C_comm_g * (c ^ 2 / N) * G * (∑ n ∈ Ioc M N, x n ^ 2) ≤
        (K₀_low + 1) * C_comm_g * (c ^ 2 / N) * G * topCollarSeventhMass M N x :=
      mul_le_mul_of_nonneg_left hS_le_S7 (by positivity)
    have hmain_id : (1 / 2 : ℝ) *
        (G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
          Real.log N * topCollarSeventhMass M N x)) =
        G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (4 * 8 ^ 7 * c ^ 7)) *
          Real.log N * topCollarSeventhMass M N x) := by
      rw [show (4 : ℝ) * 8 ^ 7 * c ^ 7 = 2 * (2 * 8 ^ 7 * c ^ 7) by ring]
      field_simp [hc0.ne']
    linarith only [htri_sum, hims, hsum_F, hFk_mul, hcomm_L2_mul, hcomm_lev, herr_S7, hmain_id]
  have hdiv18 : G * (((dyadicTopMassConstant / c ^ 7) * Real.log N - C_err * (c ^ 2 / N)) *
      topCollarSeventhMass M N x) ≤
      levyEnergy (atomicTest N y g) +
        ((9 * K₀_low + 648 * L_B ^ 2) / 18) * ∫ u, atomicTest N y g u ^ 2 := by
    have hdt : dyadicTopMassConstant / c ^ 7 =
        (1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7) := by
      unfold dyadicTopMassConstant; rw [div_div]
    have h72 : (1 / 2052 : ℝ) ^ 8 * growingMassConstant / (4 * 8 ^ 7 * c ^ 7) =
        18 * (dyadicTopMassConstant / c ^ 7) := by
      rw [hdt, show (72 : ℝ) * 8 ^ 7 * c ^ 7 = 18 * (4 * 8 ^ 7 * c ^ 7) by ring]
      field_simp [hc0.ne']
    rw [h72] at h18
    dsimp only [C_err]
    linarith only [h18,
      (by ring : G * (((dyadicTopMassConstant / c ^ 7) * Real.log N -
          ((K₀_low + 1) * C_comm_g / 18) * (c ^ 2 / N)) * topCollarSeventhMass M N x) =
        (G * ((18 * (dyadicTopMassConstant / c ^ 7)) * Real.log N * topCollarSeventhMass M N x) -
          (K₀_low + 1) * C_comm_g * (c ^ 2 / N) * G * topCollarSeventhMass M N x) / 18)]
  dsimp only [B_arch]
  linarith only [hdiv18, harch_eq, hγ_fy]

/-! ### 5. Collar atomic Gårding at every critical ratio -/

/-- **Scale-uniform collar atomic Gårding below any critical ratio `R_max > 0`.**
On the overlapping top collar `Ioc (N / linearDefectCutoff c) N`, uniformly across `1 ≤ c` with
`c⁸ ≤ R_max log N`, `weilQuad U_y + B_R ∫ U_y²` simultaneously dominates both a fixed positive
multiple of `topCollarSeventhMass` and a fixed positive multiple `a_R > 0` of `∫ U_y(u)² e^{−8u} du`. -/
theorem exists_collar_atomic_garding_below_ratio {R_max : ℝ} (hR : 0 < R_max) :
    ∃ B_R a_R κ_R : ℝ, 0 ≤ B_R ∧ 0 < a_R ∧ 0 < κ_R ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) → ∀ x : ℕ → ℝ,
          let y := atomicTailCoefficients (N / linearDefectCutoff c) x
          let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
          κ_R * topCollarSeventhMass (N / linearDefectCutoff c) N x +
              a_R * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
            weilQuad U_y + B_R * ∫ u, U_y u ^ 2 := by
  obtain ⟨B_arch, C_err, hB_arch0, hC_err0, harch_g⟩ :=
    exists_top_archForm_dyadic_seventh_reserve_garding
  set I₂ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  set C₈ := (256 * Real.exp 2 + 4 + 2 * Real.exp 1) * I₂
  have hC₈ : 0 < C₈ := by positivity
  set c₀ := I₂ * dyadicTopMassConstant / R_max
  have hc₀ : 0 < c₀ := by
    have := dyadicTopMassConstant_pos
    positivity
  set ε := c₀ / (12 * C₈)
  have hε : 0 < ε := by positivity
  obtain ⟨B_prime, hBp0, hprime⟩ := exists_abs_primeSum_le_exponential_mass_of_le_one hε
  obtain ⟨B_pole, hBpole0, hpole⟩ := exists_two_mul_sinhHalfMoment_sq_le_exponential_mass hε
  set B_R := B_arch + B_prime + B_pole
  set a_R := ε
  set κ_R := c₀ / 4
  refine ⟨B_R, a_R, κ_R, by positivity, hε, by positivity, ?_⟩
  have hL_lim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLN_zero : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev_L2N : ∀ᶠ N : ℕ in atTop,
      ((256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)) * Real.log (N : ℝ) ≤ N := by
    set A := (256 * Real.exp 2 + 4) ^ 2 * (R_max + 1)
    have hA : 0 < A := by positivity
    have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / A))
    filter_upwards [hev, eventually_ge_atTop 1] with N hlt hN1
    dsimp only [Function.comp_def] at hlt
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hm := (div_lt_iff₀ hN0).mp hlt
    have hdiv : 1 / A * (N : ℝ) = (N : ℝ) / A := by field_simp [hA.ne']
    exact ((le_div_iff₀ hA).mp (by linarith : Real.log (N : ℝ) ≤ (N : ℝ) / A)).trans_eq'
      (mul_comm _ _)
  have hev_err : ∀ᶠ N : ℕ in atTop,
      I₂ * C_err * ((R_max + 1) * Real.log (N : ℝ) / N) ≤ c₀ / 2 := by
    by_cases hCerr_pos : 0 < C_err
    · set A := I₂ * C_err * (R_max + 1)
      have hA : 0 < A := by positivity
      have hev := (hLN_zero.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (div_pos (div_pos hc₀ zero_lt_two) hA))
      filter_upwards [hev] with N hlt
      dsimp only [Function.comp_def] at hlt
      have hm := (lt_div_iff₀ hA).mp hlt
      linarith only [hm,
        (by ring : I₂ * C_err * ((R_max + 1) * Real.log (N : ℝ) / N) =
          (Real.log (N : ℝ) / N) * A)]
    · have h0 : C_err = 0 := le_antisymm (not_lt.mp hCerr_pos) hC_err0
      filter_upwards with N
      rw [h0]
      simp only [mul_zero, zero_mul]
      positivity
  filter_upwards [hev_L2N, hev_err, eventually_ge_atTop 3] with N hL2N_b herr_b hN3 c hc1 hc8 x
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  have hc0_pos : 0 < c := zero_lt_one.trans_le hc1
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc2_le : c ^ 2 ≤ R_max * Real.log (N : ℝ) :=
    (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 8)).trans hc8
  have hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N := by
    have h1 : (linearDefectCutoff c : ℝ) ^ 2 ≤ (256 * Real.exp 2 + 4) ^ 2 * c ^ 2 := by
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ linearDefectCutoff c) hLup 2
      exact hp.trans_eq (mul_pow _ _ 2)
    have h2 : (256 * Real.exp 2 + 4) ^ 2 * c ^ 2 ≤
        (256 * Real.exp 2 + 4) ^ 2 * (R_max + 1) * Real.log (N : ℝ) := by
      have hc2' : c ^ 2 ≤ (R_max + 1) * Real.log (N : ℝ) := by linarith
      exact (mul_le_mul_of_nonneg_left hc2' (by positivity)).trans_eq (by ring)
    linarith
  have hLN_nat : linearDefectCutoff c ≤ N := by
    have hLc1 : (1 : ℝ) ≤ linearDefectCutoff c := by
      have : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
      linarith
    have hle : (linearDefectCutoff c : ℝ) ≤ N :=
      (le_self_pow₀ hLc1 (by norm_num : 2 ≠ 0)).trans hL2N
    exact_mod_cast hle
  have hcN : c ≤ N := by
    have hle : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN_nat
    linarith
  let M := N / linearDefectCutoff c
  let y := atomicTailCoefficients M x
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0_pos hN_pos
  have hw1 : w ≤ 1 := (div_le_one hN_pos).mpr hcN
  let g := atomDilate tiltedUnitSpline w
  let f_y := atomicTest N y g
  let U_y := normalizedCentredAtomicTest tiltedUnitSpline y c N
  obtain ⟨hg, hgs, _⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  have hfy_cd : ContDiff ℝ 2 f_y := contDiff_atomicTest hg N y
  have hfy_cs : HasCompactSupport f_y := hasCompactSupport_atomicTest hgs N y
  have hcent_cd : ContDiff ℝ 2 (centredAtomicTest tiltedUnitSpline y c N) :=
    contDiff_centredAtomicTest contDiff_tiltedUnitSpline y c N
  have hcent_cs : HasCompactSupport (centredAtomicTest tiltedUnitSpline y c N) := by
    unfold centredAtomicTest
    exact hfy_cs.comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hUy_cd : ContDiff ℝ 2 U_y := contDiff_const.mul hcent_cd
  have hUy_cs : HasCompactSupport U_y := hcent_cs.mul_left
  have hUy_le1 : ∀ u, 1 < u → U_y u = 0 := by
    intro u hu1
    dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest, f_y]
    suffices h0 : atomicTest N y g (u + Real.log N) = 0 by rw [h0, mul_zero]
    unfold atomicTest
    refine sum_eq_zero fun n hn => ?_
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
    have hnot : u + Real.log N - Real.log n ∉ Set.Icc 0 w := fun hm => by linarith [hm.2, hw1]
    dsimp only [g]
    rw [hgs _ hnot, mul_zero]
  -- Scale archimedean Gårding reserve from `f_y` to `U_y`
  have hUy_arch_scale : archForm U_y + B_arch * (∫ u, U_y u ^ 2) =
      ((N : ℝ) / c ^ 2) * (archForm f_y + B_arch * ∫ u, f_y u ^ 2) := by
    have harch_cent : archForm (centredAtomicTest tiltedUnitSpline y c N) = archForm f_y := by
      have h1 := archForm_eq_levyEnergy hcent_cd hcent_cs
      have h2 := archForm_eq_levyEnergy hfy_cd hfy_cs
      have hL2_sh : (∫ u, centredAtomicTest tiltedUnitSpline y c N u ^ 2) = ∫ u, f_y u ^ 2 :=
        integral_add_right_eq_self (fun u => f_y u ^ 2) (Real.log N)
      have hlev_sh : levyEnergy (centredAtomicTest tiltedUnitSpline y c N) = levyEnergy f_y := by
        unfold levyEnergy centredAtomicTest
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        congr 1
        have hfn : (fun u => (f_y (u + Real.log N) - f_y (u + t + Real.log N)) ^ 2) =
            fun u => (fun v => (f_y v - f_y (v + t)) ^ 2) (u + Real.log N) :=
          funext fun u => by dsimp only; congr 2; ring
        rw [hfn]
        exact integral_add_right_eq_self (fun v => (f_y v - f_y (v + t)) ^ 2) (Real.log N)
      rw [h1, h2, hL2_sh, hlev_sh]
    have hL2_Uy : (∫ u, U_y u ^ 2) = ((N : ℝ) / c ^ 2) * ∫ u, f_y u ^ 2 := by
      dsimp only [U_y, normalizedCentredAtomicTest]
      simp_rw [mul_pow, div_pow, Real.sq_sqrt hN_pos.le]
      rw [integral_const_mul]
      exact congrArg (((N : ℝ) / c ^ 2) * ·)
        (integral_add_right_eq_self (fun u => f_y u ^ 2) (Real.log N))
    have harch_Uy_eq : archForm U_y = ((N : ℝ) / c ^ 2) * archForm f_y := by
      have hfn_Uy : U_y = fun u => (Real.sqrt N / c) * centredAtomicTest tiltedUnitSpline y c N u :=
        rfl
      rw [hfn_Uy, archForm_const_mul hcent_cd hcent_cs, div_pow, Real.sq_sqrt hN_pos.le,
        harch_cent]
    rw [harch_Uy_eq, hL2_Uy]
    ring
  have harch_Uy : (c₀ / 2) * topCollarSeventhMass M N x ≤
      archForm U_y + B_arch * ∫ u, U_y u ^ 2 := by
    have hg0 := mul_le_mul_of_nonneg_left (harch_g hc1 hL2N x)
      (div_nonneg hN_pos.le (sq_nonneg c))
    rw [← hUy_arch_scale] at hg0
    refine le_trans ?_ hg0
    have hid : ((N : ℝ) / c ^ 2) * (((c / N) * I₂) *
        (((dyadicTopMassConstant / c ^ 7) * Real.log N - C_err * (c ^ 2 / N)) *
          topCollarSeventhMass M N x)) =
        (I₂ * dyadicTopMassConstant * (Real.log N / c ^ 8) - I₂ * C_err * (c / N)) *
          topCollarSeventhMass M N x := by
      field_simp [hc0_pos.ne', hN_pos.ne']
    rw [hid]
    refine mul_le_mul_of_nonneg_right ?_ (topCollarSeventhMass_nonneg M N x)
    have hmain : c₀ ≤ I₂ * dyadicTopMassConstant * (Real.log N / c ^ 8) := by
      have hrat : 1 / R_max ≤ Real.log N / c ^ 8 :=
        (div_le_div_iff₀ hR (pow_pos hc0_pos 8)).mpr (by linarith)
      have hm := mul_le_mul_of_nonneg_left hrat
        (mul_nonneg hI₂.le dyadicTopMassConstant_pos.le)
      exact hm.trans_eq' (by dsimp only [c₀]; ring)
    have herr_c : I₂ * C_err * (c / N) ≤ c₀ / 2 := by
      have hc_le : c / N ≤ (R_max + 1) * Real.log (N : ℝ) / N := by
        refine div_le_div_of_nonneg_right ?_ hN_pos.le
        exact (le_self_pow₀ hc1 (by norm_num : 2 ≠ 0)).trans (by linarith)
      exact (mul_le_mul_of_nonneg_left hc_le (mul_nonneg hI₂.le hC_err0)).trans herr_b
    linarith
  -- Combine with W₈ collar bound, prime absorption, and sinh absorption
  have hW8_le : (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤ C₈ * topCollarSeventhMass M N x :=
    normalized_tail_exponential_mass_le contDiff_tiltedUnitSpline.continuous
      tiltedUnitSpline_eq_zero hc1 hLN_nat x
  have hpr_Uy := (neg_le_abs _).trans (hprime hUy_cd.continuous hUy_cs hUy_le1)
  have hpo_Uy := hpole hUy_cd.continuous hUy_cs hUy_le1
  have hweil_Uy : weilQuad U_y = archForm U_y - primeSum U_y +
      (2 * coshHalfMoment U_y ^ 2 - 2 * sinhHalfMoment U_y ^ 2) := by
    have h1 := weilQuad_eq hUy_cd hUy_cs
    have h2 := archForm_eq_levyEnergy hUy_cd hUy_cs
    linarith only [h1, h2]
  have hcosh0 : 0 ≤ 2 * coshHalfMoment U_y ^ 2 := by positivity
  have h3ε : 3 * ε * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
      (c₀ / 4) * topCollarSeventhMass M N x := by
    calc 3 * ε * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u)))
        ≤ 3 * ε * (C₈ * topCollarSeventhMass M N x) :=
          mul_le_mul_of_nonneg_left hW8_le (by positivity)
      _ = (c₀ / 4) * topCollarSeventhMass M N x := by
          dsimp only [ε]; field_simp [hC₈.ne']; ring
  change (c₀ / 4) * topCollarSeventhMass M N x +
      ε * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
    weilQuad U_y + (B_arch + B_prime + B_pole) * ∫ u, U_y u ^ 2
  change -primeSum U_y ≤
      ε * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + B_prime * ∫ u, U_y u ^ 2 at hpr_Uy
  change 2 * sinhHalfMoment U_y ^ 2 ≤
      ε * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) + B_pole * ∫ u, U_y u ^ 2 at hpo_Uy
  set S_M : ℝ := topCollarSeventhMass M N x
  set W_U : ℝ := ∫ u, U_y u ^ 2 * Real.exp (-(8 * u))
  set I_U : ℝ := ∫ u, U_y u ^ 2
  have hstep1 : (c₀ / 4) * S_M + ε * W_U ≤ (c₀ / 2) * S_M - 2 * (ε * W_U) := by
    have h4 : ε * W_U + 2 * (ε * W_U) ≤ (c₀ / 4) * S_M :=
      (le_of_eq (by ring : ε * W_U + 2 * (ε * W_U) = 3 * ε * W_U)).trans h3ε
    exact le_sub_iff_add_le.mpr
      ((le_of_eq (by ring : (c₀ / 4 * S_M + ε * W_U) + 2 * (ε * W_U) =
          c₀ / 4 * S_M + (ε * W_U + 2 * (ε * W_U)))).trans
        ((add_le_add_left h4 (c₀ / 4 * S_M)).trans_eq (by ring)))
  have hstep2 : (c₀ / 2) * S_M - 2 * (ε * W_U) ≤
      (archForm U_y + B_arch * I_U) - (primeSum U_y - B_prime * I_U) -
        (2 * sinhHalfMoment U_y ^ 2 - B_pole * I_U) := by
    have hp1 : -(ε * W_U) ≤ -primeSum U_y + B_prime * I_U :=
      neg_le_iff_add_nonneg.mpr (sub_nonneg.mpr hpr_Uy |>.trans_eq (by ring))
    have hp2 : -(ε * W_U) ≤ -(2 * sinhHalfMoment U_y ^ 2) + B_pole * I_U :=
      neg_le_iff_add_nonneg.mpr (sub_nonneg.mpr hpo_Uy |>.trans_eq (by ring))
    exact (le_of_eq (by ring : c₀ / 2 * S_M - 2 * (ε * W_U) =
        c₀ / 2 * S_M + -(ε * W_U) + -(ε * W_U))).trans
      ((add_le_add (add_le_add harch_Uy hp1) hp2).trans_eq (by ring))
  calc (c₀ / 4) * S_M + ε * W_U
      ≤ (archForm U_y + B_arch * I_U) - (primeSum U_y - B_prime * I_U) -
          (2 * sinhHalfMoment U_y ^ 2 - B_pole * I_U) := hstep1.trans hstep2
    _ ≤ (archForm U_y + B_arch * I_U) - (primeSum U_y - B_prime * I_U) -
          (2 * sinhHalfMoment U_y ^ 2 - B_pole * I_U) + 2 * coshHalfMoment U_y ^ 2 :=
        le_add_of_nonneg_right hcosh0
    _ = weilQuad U_y + (B_arch + B_prime + B_pole) * I_U := by
        rw [hweil_Uy]; ring

/-- **Collar atomic Gårding along any critical curve `c_N⁸ / log N → R > 0`.** -/
theorem exists_collar_atomic_garding_along_critical_curve
    {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    ∃ B_R a_R κ_R : ℝ, 0 ≤ B_R ∧ 0 < a_R ∧ 0 < κ_R ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
        let y := atomicTailCoefficients (N / linearDefectCutoff (c N)) x
        let U_y := normalizedCentredAtomicTest tiltedUnitSpline y (c N) N
        κ_R * topCollarSeventhMass (N / linearDefectCutoff (c N)) N x +
            a_R * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
          weilQuad U_y + B_R * ∫ u, U_y u ^ 2 := by
  obtain ⟨B_R, a_R, κ_R, hB0, ha, hκ, hev⟩ :=
    exists_collar_atomic_garding_below_ratio (by linarith : 0 < R + 1)
  refine ⟨B_R, a_R, κ_R, hB0, ha, hκ, ?_⟩
  have hlt_ev := htend.eventually (gt_mem_nhds (by linarith : R < R + 1))
  filter_upwards [hev, hc1, hlt_ev, eventually_ge_atTop 3] with N hg hcN hlt hN3 x
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact hg hcN ((div_lt_iff₀ hL0).mp hlt).le x

#print axioms not_unrestricted_atomic_garding_on_poleOrthogonal
#print axioms not_unrestricted_unitL2_atomic_garding_on_poleOrthogonal
#print axioms levyEnergy_le_interpolated
#print axioms exists_top_archForm_dyadic_seventh_reserve_garding
#print axioms exists_collar_atomic_garding_below_ratio
#print axioms exists_collar_atomic_garding_along_critical_curve

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

