import GaloisForLFunctions.HTGeometry.PeriodicTentMultiplicativeWindowLaw
import GaloisForLFunctions.HTGeometry.ChainGaussianFourierPacketHaarLaw

open Real intervalIntegral MeasureTheory Set ProbabilityTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- The same strong-extremality constant controls every Fejér order, radius,
and centre. -/
theorem exists_uniform_periodicProductFejerTent_multiplicativeWindowDiscrepancy
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : Fin d → ℝ) (u T : ℝ), 0 < T →
        ‖((1 / (T : ℂ)) *
            ∫ t in u..(u + T),
              ((periodicProductFejerTent N rho c (fun j => t * omega j) : ℝ) : ℂ))
            - (((rho / (2 * π)) ^ d : ℝ) : ℂ)‖ ≤
          (2 * C / T) * periodicFejerMultiplicativeCost N rho c eps := by
  classical
  set S := nonconstantPacketIndexSet N d with hS
  obtain ⟨C, hC, hpacket⟩ :=
    KleinbockMargulis.exists_global_indexedFourierPacketHaarDiscrepancy
      (n := d) (ι := {k // k ∈ S}) homega heps
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hpoint : ∀ t : ℝ,
      ((periodicProductFejerTent N rho c (fun j => t * omega j) : ℝ) : ℂ) =
        (((rho / (2 * π)) ^ d : ℝ) : ℂ)
          + ∑ i : {k // k ∈ S}, packetAmp N rho c i.1 *
            Complex.exp ((t : ℂ) *
              (KleinbockMargulis.dotProd (packetCharacter i.1) omega : ℂ) *
                Complex.I) := by
    intro t
    rw [periodicProductFejerTent_eq_const_add N hrho hrhopi]
    change (((rho / (2 * π)) ^ d : ℝ) : ℂ) +
        ∑ k ∈ nonconstantPacketIndexSet N d,
          packetMode N rho c (fun j => t * omega j) k = _
    rw [← hS]
    congr 1
    rw [Finset.sum_coe_sort S (fun k => packetAmp N rho c k *
      Complex.exp ((t : ℂ) *
        (KleinbockMargulis.dotProd (packetCharacter k) omega : ℂ) * Complex.I))]
    exact Finset.sum_congr rfl fun k _ => by
      rw [packetMode_linearPhase N rho c omega k t,
        dotProd_packetCharacter]
  have hmain := hpacket
    (((rho / (2 * π)) ^ d : ℝ) : ℂ)
    (fun i : {k // k ∈ S} => packetAmp N rho c i.1)
    (fun i : {k // k ∈ S} => packetCharacter i.1)
    (fun i => by
      apply packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet
      rw [← hS]
      exact i.2) u T hT
  rw [show periodicFejerMultiplicativeCost N rho c eps =
      KleinbockMargulis.indexedMultiplicativeFourierL1Cost
        (fun i : {k // k ∈ S} => packetAmp N rho c i.1)
        (fun i : {k // k ∈ S} => packetCharacter i.1) eps by rfl]
  have hInt :
      (∫ t in u..(u + T),
        ((periodicProductFejerTent N rho c (fun j => t * omega j) : ℝ) : ℂ)) =
      ∫ t in u..(u + T),
        ((((rho / (2 * π)) ^ d : ℝ) : ℂ)
          + ∑ i : {k // k ∈ S}, packetAmp N rho c i.1 *
            Complex.exp ((t : ℂ) *
              (KleinbockMargulis.dotProd (packetCharacter i.1) omega : ℂ) *
                Complex.I)) :=
    intervalIntegral.integral_congr fun t _ => hpoint t
  rw [hInt]
  exact hmain

/-- Uniform upper discrepancy for the nonsmoothed periodic product tent. -/
theorem exists_uniform_windowMean_periodicProductTent_le_multiplicative
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : Fin d → ℝ) (u T : ℝ), 0 < T →
        (1 / T) * ∫ t in u..(u + T),
            periodicProductTent rho c (fun j => t * omega j) ≤
          ((rho / (2 * π)) ^ d : ℝ)
            + (2 * C / T) * periodicFejerMultiplicativeCost N rho c eps
            + (d : ℝ) * ((1 / rho) *
                (2 * π / Real.sqrt ((N : ℝ) + 1))) := by
  obtain ⟨C, hC, hdisc⟩ :=
    exists_uniform_periodicProductFejerTent_multiplicativeWindowDiscrepancy
      homega heps N hrho hrhopi
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hcontP := continuous_periodicProductFejerTent N rho c omega
  have hcontf := continuous_periodicProductTent rho c omega
  have hd := hdisc c u T hT
  let Z : ℂ :=
    ((1 / (T : ℂ)) *
      ∫ t in u..(u + T),
        ((periodicProductFejerTent N rho c (fun j => t * omega j) : ℝ) : ℂ))
      - (((rho / (2 * π)) ^ d : ℝ) : ℂ)
  have hre : |Z.re| ≤ ‖Z‖ := Complex.abs_re_le_norm Z
  have hdZ : ‖Z‖ ≤
      (2 * C / T) * periodicFejerMultiplicativeCost N rho c eps := by
    simpa [Z] using hd
  have hupper := (abs_le.mp (hre.trans hdZ)).2
  dsimp [Z] at hupper
  rw [re_window_mean_ofReal hcontP hT u] at hupper
  set D : ℝ := (d : ℝ) * ((1 / rho) *
    (2 * π / Real.sqrt ((N : ℝ) + 1))) with hD
  have hdiff :
      |(1 / T) *
          (∫ t in u..(u + T),
            periodicProductFejerTent N rho c (fun j => t * omega j))
        - (1 / T) *
          (∫ t in u..(u + T),
            periodicProductTent rho c (fun j => t * omega j))| ≤ D := by
    have hsub :
        (1 / T) *
            (∫ t in u..(u + T),
              periodicProductFejerTent N rho c (fun j => t * omega j))
          - (1 / T) *
            (∫ t in u..(u + T),
              periodicProductTent rho c (fun j => t * omega j)) =
        (1 / T) * ∫ t in u..(u + T),
          (periodicProductFejerTent N rho c (fun j => t * omega j)
            - periodicProductTent rho c (fun j => t * omega j)) := by
      rw [intervalIntegral.integral_sub (hcontP.intervalIntegrable _ _)
        (hcontf.intervalIntegrable _ _)]
      ring
    rw [hsub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / T)]
    have hpi : u ≤ u + T := by linarith
    have hpoint : ∀ t ∈ Set.Icc u (u + T),
        |periodicProductFejerTent N rho c (fun j => t * omega j)
          - periodicProductTent rho c (fun j => t * omega j)| ≤ D := by
      intro t _
      exact abs_periodicProductFejerTent_sub_le N hrho c _
    have hint :
        |∫ t in u..(u + T),
          (periodicProductFejerTent N rho c (fun j => t * omega j)
            - periodicProductTent rho c (fun j => t * omega j))| ≤ T * D := by
      calc
        |∫ t in u..(u + T),
          (periodicProductFejerTent N rho c (fun j => t * omega j)
            - periodicProductTent rho c (fun j => t * omega j))| ≤
            ∫ t in u..(u + T),
              |periodicProductFejerTent N rho c (fun j => t * omega j)
                - periodicProductTent rho c (fun j => t * omega j)| :=
          intervalIntegral.abs_integral_le_integral_abs hpi
        _ ≤ ∫ _t in u..(u + T), D := by
          refine intervalIntegral.integral_mono_on hpi
            ((hcontP.sub hcontf).abs.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _) hpoint
        _ = T * D := by
          rw [intervalIntegral.integral_const, add_sub_cancel_left,
            smul_eq_mul, mul_comm]
    calc
      (1 / T) *
          |∫ t in u..(u + T),
            (periodicProductFejerTent N rho c (fun j => t * omega j)
              - periodicProductTent rho c (fun j => t * omega j))| ≤
        (1 / T) * (T * D) := mul_le_mul_of_nonneg_left hint (by positivity)
      _ = D := by field_simp
  have hlower := (abs_le.mp hdiff).1
  rw [hD]
  linarith

/-- Finite union of draw-adaptive periodic cubes. -/
def finiteCubeVisit {kappa : Type*} [Fintype kappa]
    (rho : ℝ) (c : kappa → Fin d → ℝ) (omega : Fin d → ℝ) : Set ℝ :=
  {t | ∃ a, t ∈ cubeVisit rho (c a) omega}

theorem measurableSet_finiteCubeVisit {kappa : Type*} [Fintype kappa]
    (rho : ℝ) (c : kappa → Fin d → ℝ) (omega : Fin d → ℝ) :
    MeasurableSet (finiteCubeVisit rho c omega) := by
  have hset : finiteCubeVisit rho c omega = ⋃ a, cubeVisit rho (c a) omega := by
    ext t
    simp [finiteCubeVisit]
  rw [hset]
  exact MeasurableSet.iUnion fun a => measurableSet_cubeVisit rho (c a) omega

theorem half_le_perTent_two_mul_of_turnDist_lt {rho x : ℝ}
    (hrho : 0 < rho) (hx : turnDist x < rho) :
    (1 / 2 : ℝ) ≤ perTent (2 * rho) x := by
  have hden : 0 < 2 * rho := by positivity
  have hdiv : turnDist x / (2 * rho) < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hden]
    linarith
  unfold perTent
  exact (show (1 / 2 : ℝ) ≤ 1 - turnDist x / (2 * rho) by linarith).trans
    (le_max_left _ _)

/-- A radius-rho cube indicator is majorized by 2^d times the radius-2rho
product tent. Summing gives a majorant for an arbitrary finite union. -/
theorem indicator_finiteCubeVisit_le_scaled_sum_tent
    {kappa : Type*} [Fintype kappa] {rho : ℝ} (hrho : 0 < rho)
    (c : kappa → Fin d → ℝ) (omega : Fin d → ℝ) (t : ℝ) :
    Set.indicator (finiteCubeVisit rho c omega) (fun _ => (1 : ℝ)) t ≤
      (2 : ℝ) ^ d * ∑ a, periodicProductTent (2 * rho) (c a)
        (fun j => t * omega j) := by
  classical
  by_cases ht : t ∈ finiteCubeVisit rho c omega
  · rw [Set.indicator_of_mem ht]
    obtain ⟨a, ha⟩ := ht
    have hprod : (1 / 2 : ℝ) ^ d ≤
        periodicProductTent (2 * rho) (c a) (fun j => t * omega j) := by
      rw [periodicProductTent]
      calc
        (1 / 2 : ℝ) ^ d = ∏ _j : Fin d, (1 / 2 : ℝ) := by simp
        _ ≤ ∏ j : Fin d, perTent (2 * rho) (t * omega j - c a j) := by
          exact Finset.prod_le_prod (fun _ _ => by positivity) fun j _ =>
            half_le_perTent_two_mul_of_turnDist_lt hrho (ha j)
    have hterm : periodicProductTent (2 * rho) (c a) (fun j => t * omega j) ≤
        ∑ b, periodicProductTent (2 * rho) (c b) (fun j => t * omega j) := by
      have hnonneg : ∀ b : kappa,
          0 ≤ periodicProductTent (2 * rho) (c b) (fun j => t * omega j) := by
        intro b
        rw [periodicProductTent]
        exact Finset.prod_nonneg fun j _ => perTent_nonneg _ _
      exact Finset.single_le_sum
        (fun b _ => hnonneg b) (Finset.mem_univ a)
    calc
      (1 : ℝ) = (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d := by
        rw [← mul_pow]
        norm_num
      _ ≤ (2 : ℝ) ^ d *
          periodicProductTent (2 * rho) (c a) (fun j => t * omega j) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ (2 : ℝ) ^ d * ∑ b,
          periodicProductTent (2 * rho) (c b) (fun j => t * omega j) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
  · rw [Set.indicator_of_notMem ht]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun b _ => by
      rw [periodicProductTent]
      exact Finset.prod_nonneg fun j _ => perTent_nonneg _ _

/-- Full finite-union moving-window upper law. For fixed resolution and
target count, one Diophantine constant controls every family of centres
selected after the frequency draw. -/
theorem exists_adaptiveFiniteCubeUnion_multiplicativeWindowUpper
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps : ℝ} (heps : 0 < eps) (N m : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : 2 * rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : Fin m → Fin d → ℝ) (u T : ℝ), 0 < T →
        (volume (finiteCubeVisit rho c omega ∩ Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (((2 * rho / (2 * π)) ^ d : ℝ) +
                  (d : ℝ) * ((1 / (2 * rho)) *
                    (2 * π / Real.sqrt ((N : ℝ) + 1))))
              + (2 * C / T) * ∑ a : Fin m,
                  periodicFejerMultiplicativeCost N (2 * rho) (c a) eps) := by
  have h2rho : 0 < 2 * rho := by positivity
  obtain ⟨C, hC, hsingle⟩ :=
    exists_uniform_windowMean_periodicProductTent_le_multiplicative
      homega heps N h2rho hrhopi
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hcont : ∀ a : Fin m, Continuous fun t : ℝ =>
      periodicProductTent (2 * rho) (c a) (fun j => t * omega j) :=
    fun a => continuous_periodicProductTent (2 * rho) (c a) omega
  have hsumInt :
      (1 / T) * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (c a) (fun j => t * omega j) ≤
        ((m : ℕ) : ℝ) *
            (((2 * rho / (2 * π)) ^ d : ℝ) +
              (d : ℝ) * ((1 / (2 * rho)) *
                (2 * π / Real.sqrt ((N : ℝ) + 1))))
          + (2 * C / T) * ∑ a : Fin m,
              periodicFejerMultiplicativeCost N (2 * rho) (c a) eps := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      calc
        ∑ a : Fin m, (1 / T) *
            ∫ t in u..(u + T),
              periodicProductTent (2 * rho) (c a) (fun j => t * omega j) ≤
          ∑ a : Fin m,
            (((2 * rho / (2 * π)) ^ d : ℝ)
              + (2 * C / T) * periodicFejerMultiplicativeCost N (2 * rho) (c a) eps
              + (d : ℝ) * ((1 / (2 * rho)) *
                (2 * π / Real.sqrt ((N : ℝ) + 1)))) := by
            exact Finset.sum_le_sum fun a _ =>
              hsingle (c a) u T hT
        _ = _ := by
          simp only [Finset.sum_add_distrib,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Finset.mul_sum]
          ring
    · intro a _
      exact (hcont a).intervalIntegrable u (u + T)
  have hle : u ≤ u + T := by linarith
  have hfin : volume (Set.Ioc u (u + T)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hIf : IntegrableOn
      (Set.indicator (finiteCubeVisit rho c omega) (fun _ => (1 : ℝ)))
      (Set.Ioc u (u + T)) :=
    (integrableOn_const (C := (1 : ℝ)) hfin (by simp)).indicator
      (measurableSet_finiteCubeVisit rho c omega)
  have hIg : IntegrableOn
      (fun t => (2 : ℝ) ^ d * ∑ a : Fin m,
        periodicProductTent (2 * rho) (c a) (fun j => t * omega j))
      (Set.Ioc u (u + T)) := by
    have hc : Continuous fun t : ℝ => ∑ a : Fin m,
        periodicProductTent (2 * rho) (c a) (fun j => t * omega j) :=
      continuous_finsetSum _ fun a _ => hcont a
    exact (continuous_const.mul hc).intervalIntegrable u (u + T) |>.1
  have hmono :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho c omega) (fun _ => (1 : ℝ)) t ≤
        ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ d * ∑ a : Fin m,
            periodicProductTent (2 * rho) (c a) (fun j => t * omega j) :=
    setIntegral_mono_on hIf hIg measurableSet_Ioc fun t _ =>
      indicator_finiteCubeVisit_le_scaled_sum_tent hrho c omega t
  have hind :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho c omega) (fun _ => (1 : ℝ)) t =
        (volume (finiteCubeVisit rho c omega ∩ Set.Ioc u (u + T))).toReal := by
    rw [setIntegral_indicator (measurableSet_finiteCubeVisit rho c omega),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [Set.inter_comm]
  have hright :
      ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ d * ∑ a : Fin m,
            periodicProductTent (2 * rho) (c a) (fun j => t * omega j) =
        (2 : ℝ) ^ d * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
            (fun j => t * omega j) := by
    rw [← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_const_mul]
  rw [hind, hright] at hmono
  have hTmul := mul_le_mul_of_nonneg_left hsumInt (le_of_lt hT)
  have hInt :
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (c a) (fun j => t * omega j)) ≤
        T * (((m : ℕ) : ℝ) *
              (((2 * rho / (2 * π)) ^ d : ℝ) +
                (d : ℝ) * ((1 / (2 * rho)) *
                  (2 * π / Real.sqrt ((N : ℝ) + 1))))
            + (2 * C / T) * ∑ a : Fin m,
                periodicFejerMultiplicativeCost N (2 * rho) (c a) eps) := by
    calc
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (c a) (fun j => t * omega j)) =
          T * ((1 / T) * ∫ t in u..(u + T),
            ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
              (fun j => t * omega j)) := by field_simp
      _ ≤ _ := hTmul
  have hscale : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
  exact hmono.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hInt hscale)

/-- Every finite target family chosen after the frequency packet is known
obeys the multiplicative moving-window union bound. -/
def HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
    (omega : Fin d → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ (N m : ℕ) (rho : ℝ),
    0 < rho → 2 * rho ≤ π →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : Fin m → Fin d → ℝ) (u T : ℝ), 0 < T →
        (volume (finiteCubeVisit rho c omega ∩ Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (((2 * rho / (2 * π)) ^ d : ℝ) +
                  (d : ℝ) * ((1 / (2 * rho)) *
                    (2 * π / Real.sqrt ((N : ℝ) + 1))))
              + (2 * C / T) * ∑ a : Fin m,
                  periodicFejerMultiplicativeCost N (2 * rho) (c a) eps)

theorem hasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper_of_not_vwma
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega) :
    HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper omega := by
  intro eps heps N m rho hrho hrhopi
  exact exists_adaptiveFiniteCubeUnion_multiplicativeWindowUpper
    homega heps N m hrho hrhopi

variable {K D n : ℕ} {P : Fin K → Matrix (Fin D) (Fin D) ℂ}

/-- Failure of the complete draw-adaptive finite-union law is null on every
escaping Hermitian simple-spectrum ensemble. -/
theorem volume_not_hasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper_sortedGapRatio_eq_zero
    [NeZero K]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock)
    (hac : anchor ≠ clock) :
    volume {x ∈ simpleEnsembleLocus hP |
      ¬ HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
        (fun k => anchoredGapRatioMap
          (sortedEnsembleSpectrum hP x) anchor clock ι k)} = 0 := by
  refine measure_mono_null ?_
    (volume_vwma_sortedGapRatio_eq_zero hP hS hι hanchor hclock hac)
  rintro x ⟨hx, hfail⟩
  refine ⟨hx, ?_⟩
  by_contra hvwma
  exact hfail
    (hasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper_of_not_vwma hvwma)

/-- **One-draw adaptive circuit-tube law.** Almost every standard Gaussian
nearest-neighbour time-independent Pauli Hamiltonian has simple spectrum and,
after that same draw is revealed, every finite phase-target family obeys the
explicit complete-union moving-window upper bound. -/
theorem chainGapRatio_hasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper_ae_stdGaussian
    (k : ℕ)
    {anchor clock : Fin (2 ^ (k + 3))}
    {ι : Fin n → Fin (2 ^ (k + 3))}
    (hι : Function.Injective ι) (hanchor : ∀ j, ι j ≠ anchor)
    (hclock : ∀ j, ι j ≠ clock) (hac : anchor ≠ clock) :
    ∀ᵐ x ∂(stdGaussian
      (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))),
      WithLp.ofLp x ∈ simpleEnsembleLocus
        (chainPauliFin_isHermitian (k + 3)) ∧
      HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
        (fun j => anchoredGapRatioMap
          (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3))
            (WithLp.ofLp x)) anchor clock ι j) := by
  classical
  let m := Fintype.card (ChainLabel (k + 3))
  let hP := chainPauliFin_isHermitian (k + 3)
  have hmp := PiLp.volume_preserving_ofLp (Fin m)
  have hnullSimple :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} = 0 := by
    have hsub :
        {θ : Fin m → ℝ | θ ∉ simpleEnsembleLocus hP} ⊆
          {θ | ¬ MaximallyProjectiveEnergy
            (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
      intro θ hθ hmax
      exact hθ hmax.injective
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {θ | θ ∉ simpleEnsembleLocus hP} = 0 :=
      measure_mono_null hsub (volume_notMaximallyProjective_chain_eq_zero k)
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∉ simpleEnsembleLocus hP} =
          WithLp.ofLp ⁻¹' {θ | θ ∉ simpleEnsembleLocus hP} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullLaw :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
          ¬ HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
            (fun j => anchoredGapRatioMap
              (sortedEnsembleSpectrum hP (WithLp.ofLp x))
              anchor clock ι j)} = 0 := by
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {θ ∈ simpleEnsembleLocus hP |
            ¬ HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP θ) anchor clock ι j)} = 0 :=
      volume_not_hasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper_sortedGapRatio_eq_zero
        hP (chainPauliFin_spectrumEscapesRealRelations k)
        hι hanchor hclock hac
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)} =
          WithLp.ofLp ⁻¹' {θ ∈ simpleEnsembleLocus hP |
            ¬ HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP θ) anchor clock ι j)} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullBad :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    measure_union_null hnullSimple hnullLaw
  have hgauss :
      stdGaussian (EuclideanSpace ℝ (Fin m))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveFiniteCubeUnionMultiplicativeWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    (stdGaussian_absolutelyContinuous_volume_finEuclidean m) hnullBad
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hgauss)
  intro x hx
  by_cases hs : WithLp.ofLp x ∈ simpleEnsembleLocus hP
  · exact Or.inr ⟨hs, fun hlaw => hx ⟨hs, hlaw⟩⟩
  · exact Or.inl hs

end

end GaloisForLFunctions.HTGeometry
