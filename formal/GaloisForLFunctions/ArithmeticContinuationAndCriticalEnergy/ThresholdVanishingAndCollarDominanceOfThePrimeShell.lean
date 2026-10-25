import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePrimeShellBetaFunction
import GaloisForLFunctions.RHTower.ChebyshevLagWindow
import GaloisForLFunctions.RHTower.CCM.CCMOddPrimeContinuousCancellation

/-!
# Threshold vanishing, collar dominance, and frozen-family collapse of the prime shell

At an aperture `c`, the restricted Weil prime-shell correlation
`σ_N(f) = Σ_{N < n ≤ ⌊e^{2c}⌋} Λ(n) n^{-1/2} Re(⟨τ_{log n} f, f⟩ + ⟨τ_{-log n} f, f⟩)`
governs the arithmetic jump `μ^{[N]}(c) − μ(c)` between the frozen-prime family and the literal
restricted Weil flow (`ThePrimeShellBetaFunction`).

This module establishes the three regime laws of the prime shell—threshold, macro-step, and
large-aperture asymptotic—and their consequences for the aperture renormalization flow:

* **Zero-birth threshold law (`inner_logTranslationCLM_eq_zero_of_two_mul_le`,
  `primeShellCorrelation_eq_zero_of_le_half_log_succ`, `frozenFamily_energy_eq_of_le_half_log_succ`).**
  Whenever `2c ≤ t`, the collar intervals `[−c, c − t]` and `[t − c, c]` sit inside the
  Lebesgue-null boundary singletons `{−c}` and `{c}`, so `⟨τ_t f, f⟩ = 0` and `⟨τ_{-t} f, f⟩ = 0`
  for every `f : suzukiApertureHilbert c`—including at the exact threshold `t = 2c` where a prime
  power `n = e^{2c}` first enters the floor cutoff `⌊e^{2c}⌋`. Consequently, for every `N ≥ 1`,
  `σ_N(f) = 0` and `(frozenFamily N).energy c = μ(c)` on the entire closed interval
  `c ≤ (1/2) log(N + 1)`.
* **Pure frozen-relaxation ladder (`primeThresholdLadder`,
  `apertureSpectralJump_primeThresholdLadder_eq_frozen`,
  `riemannHypothesis_iff_sum_frozen_relaxation_le`).**
  Along the strictly increasing unbounded threshold ladder `A_0 = 3/10`,
  `A_{j+1} = (1/2) log(j + 2)`, the visible cutoff satisfies `primeCutoff (A_j) = j + 1` for every
  `j : ℕ`, and at every step `A_j → A_{j+1}` the instantaneous arithmetic shell jump vanishes
  identically. Every step `μ(A_j) − μ(A_{j+1})` of the literal restricted Weil flow is therefore
  purely the nonnegative Rayleigh–Ritz domain relaxation of the fixed finite-prime operator
  `frozenFamily (j + 1)`.
* **Pythagorean collar-core decomposition and collar-defect dominance
  (`suzukiApertureHilbert_eq_collar_add_core`, `collar_norm_sq_add_eq_sub_core`,
  `abs_primeShellCorrelation_le_collar_defect`, `frozen_sub_literal_energy_collar_sandwich`).**
  Across any macro-step `a ≤ c` with `c ≤ 2a`, the aperture `[-c, c]` splits orthogonally in `L²(ℝ)`
  into the left collar `[-c, c - 2a]`, the interior core `(c - 2a, 2a - c)`, and the right collar
  `[2a - c, c]`. By unitarity of `τ_{log n}` and `2 ‖f_L‖ ‖f_R‖ ≤ ‖f_L‖² + ‖f_R‖² = ‖f‖² - ‖f_core‖²`,
  the shell correlation is bounded by the collar norm defect times the shell von Mangoldt weight,
  which is bounded in turn by `e^{-a} (ψ(e^{2c}) - ψ(e^{2a})) (‖f‖² - ‖f_core‖²)`.
* **First-rung zero-width reduction (`zetaZeroWidth_le_of_frozen_relaxation_and_collar_defect`).**
  Combining the two-step renormalization law with collar-defect dominance bounds `zetaZeroWidth` and
  `polarGroundEnergyRate` directly from frozen geometric relaxation plus core-concentration defect.
* **Exponential collapse of every frozen-prime family (`frozenFamily_Q_le_continuous_add_two_psi`,
  `eventually_frozenFamily_energy_le_neg_mul_exp`, `not_exists_subtrivial_exp_floor_frozenFamily`).**
  For every fixed `N : ℕ` and every `α < 1`, eventually `(frozenFamily N).energy c ≤ −α e^c` as
  `c → ∞`, because on the odd polar state `2 sinh(x/2) 𝟙_{[-c, c]}` the continuous odd Gamma–polar
  balance `~ −2 e^{2c}` overwhelms the `O_N(e^c)` contribution of the finitely many frozen primes
  `n ≤ N`. Thus no frozen-prime operator admits any exponential floor at rate `2σ < 1` (`σ < 1/2`):
  continuously unfreezing the prime shell is indispensable to cancel the odd polar mode.
-/

open Complex MeasureTheory Set Filter Finset
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilDeletion GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## 1. Null-collar annihilation and exact threshold vanishing -/

/-- Cutting off an `L²` function to a Lebesgue-null measurable set produces the zero vector. -/
theorem indicatorCutoff_eq_zero_of_volume_eq_zero {s : Set ℝ} (hs : MeasurableSet s)
    (h0 : volume s = 0) (f : SoninL2) :
    indicatorCutoff s hs f = 0 := by
  apply Lp.ext
  have hnot : ∀ᵐ x : ℝ ∂volume, x ∉ s := by
    simpa [ae_iff] using h0
  filter_upwards [indicatorCutoff_ae s hs f, Lp.coeFn_zero ℂ 2 volume, hnot] with x hcut hz hx
  rw [hcut, Set.indicator_of_notMem hx]
  exact hz.symm

/-- **Exact threshold vanishing of translation pairings.** For `2c ≤ t`, the left and right collars
sit inside the null singletons `{-c}` and `{c}`, so `⟨τ_t f, f⟩ = 0` for every
`f : suzukiApertureHilbert c`, including at the exact threshold `t = 2c`. -/
theorem inner_logTranslationCLM_eq_zero_of_two_mul_le (c : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert c) {t : ℝ} (ht : 2 * c.1 ≤ t) :
    inner ℂ (logTranslationCLM t f.1) f.1 = 0 := by
  have hLsub : Icc (-c.1) (c.1 - t) ⊆ ({-c.1} : Set ℝ) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [Set.mem_singleton_iff]
    linarith
  have hRsub : Icc (t - c.1) c.1 ⊆ ({c.1} : Set ℝ) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [Set.mem_singleton_iff]
    linarith
  rw [inner_logTranslation_eq_collar c f (measurableSet_singleton (-c.1))
    (measurableSet_singleton c.1) hLsub hRsub,
    indicatorCutoff_eq_zero_of_volume_eq_zero (measurableSet_singleton (-c.1))
      (MeasureTheory.measure_singleton (-c.1)) f.1,
    inner_zero_right]

/-- Both forward and backward translation pairings vanish for `2c ≤ t`. -/
theorem inner_symmetric_logTranslations_eq_zero_of_two_mul_le (c : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert c) {t : ℝ} (ht : 2 * c.1 ≤ t) :
    inner ℂ (logTranslationCLM t f.1) f.1 + inner ℂ (logTranslationCLM (-t) f.1) f.1 = 0 := by
  have hpos := inner_logTranslationCLM_eq_zero_of_two_mul_le c f ht
  have hneg : inner ℂ (logTranslationCLM (-t) f.1) f.1 = 0 := by
    rw [inner_logTranslationCLM (-t), neg_neg]
    exact inner_eq_zero_symm.mpr hpos
  rw [hpos, hneg, add_zero]

/-- **Zero-birth law for the prime shell.** For every `N ≥ 1` and every aperture
`c ≤ (1/2) log(N + 1)`, the prime-shell correlation `σ_N(f)` vanishes identically on
`suzukiApertureHilbert c`: even at the exact threshold `c = (1/2) log(N + 1)` where `N + 1` enters
`⌊e^{2c}⌋`, its translation lag `log(N + 1) = 2c` pairs only boundary singletons. -/
theorem primeShellCorrelation_eq_zero_of_le_half_log_succ {N : ℕ} (hN : 1 ≤ N)
    {c : SuzukiPositiveAperture} (hc : c.1 ≤ (1 / 2) * Real.log (N + 1))
    (f : suzukiApertureHilbert c) :
    primeShellCorrelation N c f = 0 := by
  rw [primeShellCorrelation_eq_primeSum hN c f]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hn_ge : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn.1)
  have hlog_ge : Real.log ((N : ℝ) + 1) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hN1_pos hn_ge
  have ht : 2 * c.1 ≤ Real.log (n : ℝ) := by linarith
  rw [inner_symmetric_logTranslations_eq_zero_of_two_mul_le c f ht, Complex.zero_re, mul_zero]

/-- On `c ≤ (1/2) log(N + 1)` (`N ≥ 1`), the frozen quadratic form agrees identically with the
literal restricted Weil quadratic form. -/
theorem frozenFamily_Q_eq_literal_of_le_half_log_succ {N : ℕ} (hN : 1 ≤ N)
    {c : SuzukiPositiveAperture} (hc : c.1 ≤ (1 / 2) * Real.log (N + 1))
    (u : CCMArchimedeanFormDomain c) :
    (frozenFamily N).Q c u = literalFamily.Q c u := by
  rw [frozenFamily_Q_eq, primeShellCorrelation_eq_zero_of_le_half_log_succ hN hc, add_zero]

/-- On the entire closed interval `c ≤ (1/2) log(N + 1)` (`N ≥ 1`), the frozen ground energy equals
the literal restricted Weil ground energy. -/
theorem frozenFamily_energy_eq_of_le_half_log_succ {N : ℕ} (hN : 1 ≤ N)
    {c : SuzukiPositiveAperture} (hc : c.1 ≤ (1 / 2) * Real.log (N + 1)) :
    (frozenFamily N).energy c = ccmRestrictedWeilGroundEnergy c :=
  energy_eq_of_Q_eq (frozenFamily N) literalFamily c
    (frozenFamily_Q_eq_literal_of_le_half_log_succ hN hc)

/-! ## 2. The half-logarithmic threshold ladder and pure frozen relaxation -/

/-- Algebraic proof that `3/10 < (1/2) log 2`, via `4/5 < e^{-1/5}` and `(4/5)^3 = 64/125 > 1/2`. -/
theorem three_tenths_lt_half_log_two : (3 / 10 : ℝ) < (1 / 2) * Real.log 2 := by
  have hexp1 : (4 / 5 : ℝ) < Real.exp (-1 / 5) := by
    have h := Real.add_one_lt_exp (x := (-1 / 5 : ℝ)) (by norm_num)
    linarith
  have hcube : (64 / 125 : ℝ) < Real.exp (-3 / 5) := by
    have hpow : ((4 / 5 : ℝ)) ^ 3 < (Real.exp (-1 / 5)) ^ 3 :=
      pow_lt_pow_left₀ hexp1 (by norm_num) (by norm_num)
    have hexp3 : (Real.exp (-1 / 5)) ^ 3 = Real.exp (-3 / 5) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    linarith
  have hexp_pos : 0 < Real.exp (3 / 5) := Real.exp_pos _
  have hprod : Real.exp (-3 / 5) * Real.exp (3 / 5) = 1 := by
    rw [← Real.exp_add, show (-3 / 5 : ℝ) + 3 / 5 = 0 by ring, Real.exp_zero]
  have hexp_lt_two : Real.exp (3 / 5) < 2 := by
    have hhalf : (1 / 2 : ℝ) < Real.exp (-3 / 5) := by linarith
    have hm := mul_lt_mul_of_pos_right hhalf hexp_pos
    rw [hprod] at hm
    linarith
  have hlog : (3 / 5 : ℝ) < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact hexp_lt_two
  linarith

/-- The canonical half-logarithmic prime-threshold ladder: `A_0 = 3/10` and
`A_{j+1} = (1/2) log(j + 2)`. -/
def primeThresholdLadder : ℕ → SuzukiPositiveAperture
  | 0 => ⟨3 / 10, by norm_num⟩
  | j + 1 => ⟨(1 / 2) * Real.log ((j : ℝ) + 2), by
      have hgt : (1 : ℝ) < (j : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) j]
      exact mul_pos (by norm_num) (Real.log_pos hgt)⟩

@[simp] theorem primeThresholdLadder_zero_val :
    (primeThresholdLadder 0).1 = 3 / 10 := rfl

@[simp] theorem primeThresholdLadder_succ_val (j : ℕ) :
    (primeThresholdLadder (j + 1)).1 = (1 / 2) * Real.log ((j : ℝ) + 2) := rfl

/-- Along `primeThresholdLadder`, the visible prime-power cutoff is `j + 1` at every stage `j`. -/
theorem primeCutoff_primeThresholdLadder (j : ℕ) :
    primeCutoff (primeThresholdLadder j) = j + 1 := by
  cases j with
  | zero =>
    unfold primeCutoff
    rw [primeThresholdLadder_zero_val]
    apply Nat.floor_eq_iff (Real.exp_nonneg _) |>.mpr
    refine ⟨?_, ?_⟩
    · simpa using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2 * (3 / 10))
    · have hlt := three_tenths_lt_half_log_two
      have h2 : 2 * (3 / 10 : ℝ) < Real.log 2 := by linarith
      calc Real.exp (2 * (3 / 10 : ℝ)) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr h2
        _ = ((1 : ℕ) + 1 : ℝ) := by rw [Real.exp_log (by norm_num)]; norm_num
  | succ k =>
    unfold primeCutoff
    rw [primeThresholdLadder_succ_val]
    have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hexp : Real.exp (2 * ((1 / 2) * Real.log ((k : ℝ) + 2))) = ((k + 2 : ℕ) : ℝ) := by
      rw [show 2 * ((1 / 2) * Real.log ((k : ℝ) + 2)) = Real.log ((k : ℝ) + 2) by ring,
        Real.exp_log hpos]
      push_cast
      ring
    rw [hexp, Nat.floor_natCast]

/-- The prime-threshold ladder is strictly increasing. -/
theorem strictMono_primeThresholdLadder :
    StrictMono fun j => (primeThresholdLadder j).1 := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  cases j with
  | zero =>
    simpa [primeThresholdLadder] using three_tenths_lt_half_log_two
  | succ k =>
    simp only [primeThresholdLadder_succ_val]
    have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hlt : (k : ℝ) + 2 < ((k + 1 : ℕ) : ℝ) + 2 := by
      push_cast
      linarith
    exact mul_lt_mul_of_pos_left (Real.log_lt_log hpos hlt) (by norm_num)

/-- Every step of `primeThresholdLadder` has gap at most `(1/2) log 2`. -/
theorem primeThresholdLadder_step_le (j : ℕ) :
    (primeThresholdLadder (j + 1)).1 ≤ (primeThresholdLadder j).1 + (1 / 2) * Real.log 2 := by
  cases j with
  | zero =>
    simp only [primeThresholdLadder_zero_val, primeThresholdLadder_succ_val]
    have : ((0 : ℕ) : ℝ) + 2 = 2 := by norm_num
    rw [this]
    linarith
  | succ k =>
    simp only [primeThresholdLadder_succ_val]
    have hkpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hle : ((k + 1 : ℕ) : ℝ) + 2 ≤ 2 * ((k : ℝ) + 2) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hlog : Real.log (((k + 1 : ℕ) : ℝ) + 2) ≤ Real.log 2 + Real.log ((k : ℝ) + 2) := by
      rw [← Real.log_mul (by norm_num) hkpos.ne']
      exact Real.log_le_log (by positivity) hle
    linarith

/-- The prime-threshold ladder diverges to `+∞`. -/
theorem tendsto_primeThresholdLadder_atTop :
    Tendsto (fun j => (primeThresholdLadder j).1) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (2 * max b 0))
  refine ⟨N + 1, fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [primeThresholdLadder_succ_val]
  have hkN : (N : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : N ≤ k + 2)
  have hexp_lt : Real.exp (2 * max b 0) < (k : ℝ) + 2 := hN.trans_le hkN
  have hlog : 2 * max b 0 < Real.log ((k : ℝ) + 2) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr hexp_lt
  linarith [le_max_left b 0]

/-- **Zero instantaneous arithmetic jump along `primeThresholdLadder`.** At every step
`A_j → A_{j+1}`, the frozen-prime family at cutoff `j + 1` agrees with the literal restricted Weil
energy at BOTH endpoints `A_j` and `A_{j+1}`, so the arithmetic jump is identically zero and the
literal spectral jump equals the pure frozen geometric relaxation. -/
theorem apertureSpectralJump_primeThresholdLadder_eq_frozen (j : ℕ) :
    (frozenFamily (j + 1)).energy (primeThresholdLadder j) =
        ccmRestrictedWeilGroundEnergy (primeThresholdLadder j) ∧
      (frozenFamily (j + 1)).energy (primeThresholdLadder (j + 1)) =
        ccmRestrictedWeilGroundEnergy (primeThresholdLadder (j + 1)) ∧
      apertureSpectralJump (primeThresholdLadder j) (primeThresholdLadder (j + 1)) =
        (frozenFamily (j + 1)).energy (primeThresholdLadder j) -
          (frozenFamily (j + 1)).energy (primeThresholdLadder (j + 1)) ∧
      ∀ z : ℂ,
        apertureSpectralJump (primeThresholdLadder j) (primeThresholdLadder (j + 1)) =
          (shiftedForm (frozenFamily (j + 1)) (primeThresholdLadder (j + 1))
            ((frozenFamily (j + 1)).energy (primeThresholdLadder (j + 1)))
            (apertureExt (strictMono_primeThresholdLadder (Nat.lt_succ_self j)).le
              ((frozenFamily (j + 1)).normalizedGround (primeThresholdLadder j)) -
              z • (frozenFamily (j + 1)).normalizedGround (primeThresholdLadder (j + 1)))
            (apertureExt (strictMono_primeThresholdLadder (Nat.lt_succ_self j)).le
              ((frozenFamily (j + 1)).normalizedGround (primeThresholdLadder j)) -
              z • (frozenFamily (j + 1)).normalizedGround (primeThresholdLadder (j + 1)))).re := by
  have h1 : (frozenFamily (j + 1)).energy (primeThresholdLadder j) =
      ccmRestrictedWeilGroundEnergy (primeThresholdLadder j) := by
    apply frozenFamily_energy_eq_of_floor_le
    exact (primeCutoff_primeThresholdLadder j).le
  have h2 : (frozenFamily (j + 1)).energy (primeThresholdLadder (j + 1)) =
      ccmRestrictedWeilGroundEnergy (primeThresholdLadder (j + 1)) := by
    apply frozenFamily_energy_eq_of_le_half_log_succ (by omega : 1 ≤ j + 1)
    rw [primeThresholdLadder_succ_val,
      show ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 by push_cast; ring]
  refine ⟨h1, h2, ?_, fun z => ?_⟩
  · unfold apertureSpectralJump
    rw [h1, h2]
  · unfold apertureSpectralJump
    rw [← h1, ← h2]
    exact energy_sub_energy_eq_shiftedForm (frozenFamily (j + 1))
      (strictMono_primeThresholdLadder (Nat.lt_succ_self j)).le z

/-- **Exact pure-frozen-relaxation characterization of `RiemannHypothesis`.** The Riemann Hypothesis
holds if and only if the cumulative fixed-operator geometric relaxations along
`primeThresholdLadder` never exceed `μ(3/10)`—with zero arithmetic shell remainder at every step. -/
theorem riemannHypothesis_iff_sum_frozen_relaxation_le :
    RiemannHypothesis ↔
      ∀ J : ℕ,
        ∑ j ∈ range J,
          ((frozenFamily (j + 1)).energy (primeThresholdLadder j) -
            (frozenFamily (j + 1)).energy (primeThresholdLadder (j + 1))) ≤
          ccmRestrictedWeilGroundEnergy (primeThresholdLadder 0) := by
  rw [riemannHypothesis_iff_sum_apertureSpectralJump_le tendsto_primeThresholdLadder_atTop]
  refine forall_congr' fun J => ?_
  rw [Finset.sum_congr rfl fun j _ => (apertureSpectralJump_primeThresholdLadder_eq_frozen j).2.2.1]

/-! ## 3. The Pythagorean collar-core decomposition -/

/-- The left collar interval `[−c, c − 2a]`. -/
def leftCollarSet (a c : SuzukiPositiveAperture) : Set ℝ :=
  Icc (-c.1) (c.1 - 2 * a.1)

/-- The open interior core interval `(c − 2a, 2a − c)` untouched by shell prime lags `> 2a`. -/
def interiorCoreSet (a c : SuzukiPositiveAperture) : Set ℝ :=
  Ioo (c.1 - 2 * a.1) (2 * a.1 - c.1)

/-- The right collar interval `[2a − c, c]`. -/
def rightCollarSet (a c : SuzukiPositiveAperture) : Set ℝ :=
  Icc (2 * a.1 - c.1) c.1

/-- Orthogonal projection onto the left collar `[−c, c − 2a]`. -/
def leftCollarCutoff (a c : SuzukiPositiveAperture) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (leftCollarSet a c) measurableSet_Icc

/-- Orthogonal projection onto the interior core `(c − 2a, 2a − c)`. -/
def interiorCoreCutoff (a c : SuzukiPositiveAperture) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (interiorCoreSet a c) measurableSet_Ioo

/-- Orthogonal projection onto the right collar `[2a − c, c]`. -/
def rightCollarCutoff (a c : SuzukiPositiveAperture) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (rightCollarSet a c) measurableSet_Icc

private theorem norm_add_sq_of_inner_eq_zero {g h : SoninL2} (hgh : inner ℂ g h = 0) :
    ‖g + h‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := by
  have h1 : (inner ℂ (g + h) (g + h)).re = ‖g + h‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
  have h2 : (inner ℂ g g).re = ‖g‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
  have h3 : (inner ℂ h h).re = ‖h‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
  have hhg : inner ℂ h g = 0 := inner_eq_zero_symm.mpr hgh
  rw [← h1, inner_add_left, inner_add_right, inner_add_right, hgh, hhg, add_zero, zero_add,
    Complex.add_re, h2, h3]

theorem inner_leftCollar_interiorCore_eq_zero (a c : SuzukiPositiveAperture) (f g : SoninL2) :
    inner ℂ (leftCollarCutoff a c f) (interiorCoreCutoff a c g) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc (∫ x : ℝ, inner ℂ (leftCollarCutoff a c f x) (interiorCoreCutoff a c g x))
      = ∫ _x : ℝ, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [indicatorCutoff_ae (leftCollarSet a c) measurableSet_Icc f,
          indicatorCutoff_ae (interiorCoreSet a c) measurableSet_Ioo g] with x hL hC
        change inner ℂ (indicatorCutoff (leftCollarSet a c) measurableSet_Icc f x)
          (indicatorCutoff (interiorCoreSet a c) measurableSet_Ioo g x) = 0
        rw [hL, hC]
        by_cases hxL : x ∈ leftCollarSet a c
        · have hxC : x ∉ interiorCoreSet a c := fun hm => by
            rw [leftCollarSet, Set.mem_Icc] at hxL
            rw [interiorCoreSet, Set.mem_Ioo] at hm
            linarith
          rw [Set.indicator_of_notMem hxC, inner_zero_right]
        · rw [Set.indicator_of_notMem hxL, inner_zero_left]
    _ = 0 := by simp

theorem inner_interiorCore_rightCollar_eq_zero (a c : SuzukiPositiveAperture) (f g : SoninL2) :
    inner ℂ (interiorCoreCutoff a c f) (rightCollarCutoff a c g) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc (∫ x : ℝ, inner ℂ (interiorCoreCutoff a c f x) (rightCollarCutoff a c g x))
      = ∫ _x : ℝ, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [indicatorCutoff_ae (interiorCoreSet a c) measurableSet_Ioo f,
          indicatorCutoff_ae (rightCollarSet a c) measurableSet_Icc g] with x hC hR
        change inner ℂ (indicatorCutoff (interiorCoreSet a c) measurableSet_Ioo f x)
          (indicatorCutoff (rightCollarSet a c) measurableSet_Icc g x) = 0
        rw [hC, hR]
        by_cases hxC : x ∈ interiorCoreSet a c
        · have hxR : x ∉ rightCollarSet a c := fun hm => by
            rw [interiorCoreSet, Set.mem_Ioo] at hxC
            rw [rightCollarSet, Set.mem_Icc] at hm
            linarith
          rw [Set.indicator_of_notMem hxR, inner_zero_right]
        · rw [Set.indicator_of_notMem hxC, inner_zero_left]
    _ = 0 := by simp

/-- For `c ≤ 2a`, the left and right collars intersect in at most `{0}`, so their `L²` projections
are orthogonal. -/
theorem inner_leftCollar_rightCollar_eq_zero {a c : SuzukiPositiveAperture}
    (hca : c.1 ≤ 2 * a.1) (f g : SoninL2) :
    inner ℂ (leftCollarCutoff a c f) (rightCollarCutoff a c g) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ c.1 - 2 * a.1 := by
    rw [ae_iff]
    simp
  calc (∫ x : ℝ, inner ℂ (leftCollarCutoff a c f x) (rightCollarCutoff a c g x))
      = ∫ _x : ℝ, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [indicatorCutoff_ae (leftCollarSet a c) measurableSet_Icc f,
          indicatorCutoff_ae (rightCollarSet a c) measurableSet_Icc g, hne] with x hL hR hxne
        change inner ℂ (indicatorCutoff (leftCollarSet a c) measurableSet_Icc f x)
          (indicatorCutoff (rightCollarSet a c) measurableSet_Icc g x) = 0
        rw [hL, hR]
        by_cases hxL : x ∈ leftCollarSet a c
        · have hxR : x ∉ rightCollarSet a c := fun hm => by
            rw [leftCollarSet, Set.mem_Icc] at hxL
            rw [rightCollarSet, Set.mem_Icc] at hm
            exact hxne (by linarith)
          rw [Set.indicator_of_notMem hxR, inner_zero_right]
        · rw [Set.indicator_of_notMem hxL, inner_zero_left]
    _ = 0 := by simp

/-- **Collar-core decomposition in `L²(ℝ)`.** For `a ≤ c ≤ 2a`, every vector
`f : suzukiApertureHilbert c` decomposes in `SoninL2` as the sum of its left-collar, interior-core,
and right-collar projections. -/
theorem suzukiApertureHilbert_eq_collar_add_core {a c : SuzukiPositiveAperture}
    (hac : a.1 ≤ c.1) (hca : c.1 ≤ 2 * a.1) (f : suzukiApertureHilbert c) :
    f.1 = leftCollarCutoff a c f.1 + interiorCoreCutoff a c f.1 + rightCollarCutoff a c f.1 := by
  apply Lp.ext
  have hfix : indicatorCutoff (centralInterval c.1) (measurableSet_centralInterval c.1) f.1 = f.1 :=
    indicatorCutoff_suzukiApertureHilbert c f
  have hfixAE : (f.1 : ℝ → ℂ) =ᵐ[volume] (centralInterval c.1).indicator (fun y => f.1 y) := by
    have h := indicatorCutoff_ae (centralInterval c.1) (measurableSet_centralInterval c.1) f.1
    rwa [hfix] at h
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ c.1 - 2 * a.1 := by
    rw [ae_iff]
    simp
  filter_upwards [hfixAE,
    indicatorCutoff_ae (leftCollarSet a c) measurableSet_Icc f.1,
    indicatorCutoff_ae (interiorCoreSet a c) measurableSet_Ioo f.1,
    indicatorCutoff_ae (rightCollarSet a c) measurableSet_Icc f.1,
    Lp.coeFn_add (leftCollarCutoff a c f.1 + interiorCoreCutoff a c f.1)
      (rightCollarCutoff a c f.1),
    Lp.coeFn_add (leftCollarCutoff a c f.1) (interiorCoreCutoff a c f.1),
    hne] with x hf hL hC hR hadd1 hadd2 hxne
  rw [hadd1, Pi.add_apply, hadd2, Pi.add_apply]
  change f.1 x = indicatorCutoff (leftCollarSet a c) measurableSet_Icc f.1 x +
    indicatorCutoff (interiorCoreSet a c) measurableSet_Ioo f.1 x +
    indicatorCutoff (rightCollarSet a c) measurableSet_Icc f.1 x
  rw [hf, hL, hC, hR]
  by_cases hxc : x ∈ centralInterval c.1
  · rw [Set.indicator_of_mem hxc]
    rw [centralInterval, Set.mem_Icc] at hxc
    by_cases hx1 : x ≤ c.1 - 2 * a.1
    · have hmL : x ∈ leftCollarSet a c := ⟨hxc.1, hx1⟩
      have hmC : x ∉ interiorCoreSet a c := fun hm => by
        rw [interiorCoreSet, Set.mem_Ioo] at hm; linarith
      have hmR : x ∉ rightCollarSet a c := fun hm => by
        rw [rightCollarSet, Set.mem_Icc] at hm; exact hxne (by linarith)
      rw [Set.indicator_of_mem hmL, Set.indicator_of_notMem hmC, Set.indicator_of_notMem hmR]
      ring
    · by_cases hx2 : 2 * a.1 - c.1 ≤ x
      · have hmL : x ∉ leftCollarSet a c := fun hm => hx1 hm.2
        have hmC : x ∉ interiorCoreSet a c := fun hm => by
          rw [interiorCoreSet, Set.mem_Ioo] at hm; linarith
        have hmR : x ∈ rightCollarSet a c := ⟨hx2, hxc.2⟩
        rw [Set.indicator_of_notMem hmL, Set.indicator_of_notMem hmC, Set.indicator_of_mem hmR]
        ring
      · have hmL : x ∉ leftCollarSet a c := fun hm => hx1 hm.2
        have hmC : x ∈ interiorCoreSet a c := ⟨lt_of_not_ge hx1, lt_of_not_ge hx2⟩
        have hmR : x ∉ rightCollarSet a c := fun hm => hx2 hm.1
        rw [Set.indicator_of_notMem hmL, Set.indicator_of_mem hmC, Set.indicator_of_notMem hmR]
        ring
  · have hmL : x ∉ leftCollarSet a c := fun hm => hxc ⟨hm.1, by linarith [hm.2, a.2]⟩
    have hmC : x ∉ interiorCoreSet a c := fun hm =>
      hxc ⟨by linarith [hm.1], by linarith [hm.2]⟩
    have hmR : x ∉ rightCollarSet a c := fun hm => hxc ⟨by linarith [hm.1, a.2], hm.2⟩
    rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hmL,
      Set.indicator_of_notMem hmC, Set.indicator_of_notMem hmR]
    ring

/-- **Pythagorean collar-core identity.** For `a ≤ c ≤ 2a` and `f : suzukiApertureHilbert c`, the
combined `L²` norm squared on the two collars equals `‖f‖² − ‖f_core‖²`. -/
theorem collar_norm_sq_add_eq_sub_core {a c : SuzukiPositiveAperture}
    (hac : a.1 ≤ c.1) (hca : c.1 ≤ 2 * a.1) (f : suzukiApertureHilbert c) :
    ‖leftCollarCutoff a c f.1‖ ^ 2 + ‖rightCollarCutoff a c f.1‖ ^ 2 =
      ‖f.1‖ ^ 2 - ‖interiorCoreCutoff a c f.1‖ ^ 2 := by
  have horthLC := inner_leftCollar_interiorCore_eq_zero a c f.1 f.1
  have horthLR := inner_leftCollar_rightCollar_eq_zero hca f.1 f.1
  have horthCR := inner_interiorCore_rightCollar_eq_zero a c f.1 f.1
  have horthLCR : inner ℂ (leftCollarCutoff a c f.1 + interiorCoreCutoff a c f.1)
      (rightCollarCutoff a c f.1) = 0 := by
    rw [inner_add_left, horthLR, horthCR, add_zero]
  have hsum : ‖f.1‖ ^ 2 =
      ‖leftCollarCutoff a c f.1‖ ^ 2 + ‖interiorCoreCutoff a c f.1‖ ^ 2 +
        ‖rightCollarCutoff a c f.1‖ ^ 2 := by
    calc ‖f.1‖ ^ 2
        = ‖(leftCollarCutoff a c f.1 + interiorCoreCutoff a c f.1) +
            rightCollarCutoff a c f.1‖ ^ 2 := by
          rw [← suzukiApertureHilbert_eq_collar_add_core hac hca f]
      _ = ‖leftCollarCutoff a c f.1 + interiorCoreCutoff a c f.1‖ ^ 2 +
            ‖rightCollarCutoff a c f.1‖ ^ 2 :=
          norm_add_sq_of_inner_eq_zero horthLCR
      _ = ‖leftCollarCutoff a c f.1‖ ^ 2 + ‖interiorCoreCutoff a c f.1‖ ^ 2 +
            ‖rightCollarCutoff a c f.1‖ ^ 2 := by
          rw [norm_add_sq_of_inner_eq_zero horthLC]
  linarith

theorem interiorCore_norm_sq_le {a c : SuzukiPositiveAperture}
    (hac : a.1 ≤ c.1) (hca : c.1 ≤ 2 * a.1) (f : suzukiApertureHilbert c) :
    ‖interiorCoreCutoff a c f.1‖ ^ 2 ≤ ‖f.1‖ ^ 2 := by
  have h := collar_norm_sq_add_eq_sub_core hac hca f
  linarith [sq_nonneg ‖leftCollarCutoff a c f.1‖, sq_nonneg ‖rightCollarCutoff a c f.1‖]

/-! ## 4. Collar-defect dominance of the prime shell and Chebyshev window bounds -/

/-- The scalar von Mangoldt shell weight `W(N, M) = Σ_{N < n ≤ M} Λ(n) / √n`. -/
def primeShellWeight (N M : ℕ) : ℝ :=
  ∑ n ∈ Ioc N M, (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n)

theorem primeShellWeight_nonneg (N M : ℕ) : 0 ≤ primeShellWeight N M :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- `logTranslationCLM t` is an `L²` isometry. -/
theorem norm_logTranslationCLM_apply (t : ℝ) (g : SoninL2) :
    ‖logTranslationCLM t g‖ = ‖g‖ :=
  (MellinL2.additiveTranslationUnitary t).norm_map g

/-- **Collar-defect dominance of `primeShellCorrelation`.** For `a ≤ c ≤ 2a`, the prime-shell
correlation is bounded in absolute value by the scalar shell weight times the collar norm defect
`‖f‖² − ‖f_core‖²`. -/
theorem abs_primeShellCorrelation_le_collar_defect {a c : SuzukiPositiveAperture}
    (hac : a.1 ≤ c.1) (hca : c.1 ≤ 2 * a.1) (f : suzukiApertureHilbert c) :
    |primeShellCorrelation (primeCutoff a) c f| ≤
      primeShellWeight (primeCutoff a) (Nat.floor (Real.exp (2 * c.1))) *
        (‖f.1‖ ^ 2 - ‖interiorCoreCutoff a c f.1‖ ^ 2) := by
  rw [primeShellCorrelation_eq_collar, primeShellWeight, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have hw0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  rw [abs_mul, abs_of_nonneg hw0]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  set fL := leftCollarCutoff a c f.1
  set fR := rightCollarCutoff a c f.1
  change |2 * (inner ℂ (logTranslationCLM (Real.log n) fR) fL).re| ≤ _
  have hre : |2 * (inner ℂ (logTranslationCLM (Real.log n) fR) fL).re| ≤
      2 * (‖fR‖ * ‖fL‖) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (Complex.abs_re_le_norm _).trans
      ((norm_inner_le_norm _ _).trans (by rw [norm_logTranslationCLM_apply]))
  have hamgm : 2 * (‖fR‖ * ‖fL‖) ≤ ‖fL‖ ^ 2 + ‖fR‖ ^ 2 := by
    nlinarith [sq_nonneg (‖fL‖ - ‖fR‖)]
  exact (hre.trans hamgm).trans_eq (collar_norm_sq_add_eq_sub_core hac hca f)

/-- **Chebyshev `ψ` upper bound on the shell weight.** Every `n > ⌊e^{2a}⌋` satisfies `√n > e^a`, so
`W(⌊e^{2a}⌋, ⌊e^{2c}⌋) ≤ e^{−a} (ψ(e^{2c}) − ψ(e^{2a}))`. -/
theorem primeShellWeight_le_exp_neg_mul_psi_sub {a c : SuzukiPositiveAperture}
    (hac : a.1 ≤ c.1) :
    primeShellWeight (primeCutoff a) (Nat.floor (Real.exp (2 * c.1))) ≤
      Real.exp (-a.1) * (Chebyshev.psi (Real.exp (2 * c.1)) -
        Chebyshev.psi (Real.exp (2 * a.1))) := by
  have hexp_le : Real.exp (2 * a.1) ≤ Real.exp (2 * c.1) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [RHTower.psi_sub_psi_eq_sum hexp_le, Finset.mul_sum, primeShellWeight, primeCutoff]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hexp_lt : Real.exp (2 * a.1) < (n : ℝ) := Nat.lt_of_floor_lt hn.1
  have hsqrt : Real.exp a.1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_sq (Real.exp_pos a.1).le, ← Real.exp_nat_mul]
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have hinv : 1 / Real.sqrt (n : ℝ) ≤ Real.exp (-a.1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos a.1) hsqrt
  calc (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n)
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (-a.1) :=
        mul_le_mul_of_nonneg_left hinv ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.exp (-a.1) * (ArithmeticFunction.vonMangoldt n : ℝ) := mul_comm _ _

/-- **Collar-defect sandwich on the arithmetic energy jump.** For `a ≤ c ≤ 2a`, the arithmetic jump
`μ^{[⌊e^{2a}⌋]}(c) − μ(c)` is bounded above by the literal ground state's collar defect times the
Chebyshev shell weight, and bounded below by the negative of the frozen ground state's collar defect
times the Chebyshev shell weight. -/
theorem frozen_sub_literal_energy_collar_sandwich {a c : SuzukiPositiveAperture}
    (hac : a.1 ≤ c.1) (hca : c.1 ≤ 2 * a.1) :
    (frozenFamily (primeCutoff a)).energy c - ccmRestrictedWeilGroundEnergy c ≤
        Real.exp (-a.1) *
          (Chebyshev.psi (Real.exp (2 * c.1)) - Chebyshev.psi (Real.exp (2 * a.1))) *
          (1 - ‖interiorCoreCutoff a c
            (ccmArchimedeanFormToAperture c (literalFamily.normalizedGround c)).1‖ ^ 2) ∧
      -(Real.exp (-a.1) *
          (Chebyshev.psi (Real.exp (2 * c.1)) - Chebyshev.psi (Real.exp (2 * a.1))) *
          (1 - ‖interiorCoreCutoff a c
            (ccmArchimedeanFormToAperture c
              ((frozenFamily (primeCutoff a)).normalizedGround c)).1‖ ^ 2)) ≤
        (frozenFamily (primeCutoff a)).energy c - ccmRestrictedWeilGroundEnergy c := by
  obtain ⟨hlow, hhigh⟩ := primeShell_sandwich (primeCutoff a) c
  have hw := primeShellWeight_le_exp_neg_mul_psi_sub hac
  constructor
  · set fLit := ccmArchimedeanFormToAperture c (literalFamily.normalizedGround c)
    have hnorm : ‖fLit.1‖ = 1 := literalFamily.norm_normalizedGround_embedding c
    have hdef : 0 ≤ 1 - ‖interiorCoreCutoff a c fLit.1‖ ^ 2 := by
      have := interiorCore_norm_sq_le hac hca fLit
      rw [hnorm, one_pow] at this
      linarith
    have habs := abs_primeShellCorrelation_le_collar_defect hac hca fLit
    rw [hnorm, one_pow] at habs
    exact hhigh.trans ((le_abs_self _).trans (habs.trans (mul_le_mul_of_nonneg_right hw hdef)))
  · set fFrz := ccmArchimedeanFormToAperture c
      ((frozenFamily (primeCutoff a)).normalizedGround c)
    have hnorm : ‖fFrz.1‖ = 1 :=
      (frozenFamily (primeCutoff a)).norm_normalizedGround_embedding c
    have hdef : 0 ≤ 1 - ‖interiorCoreCutoff a c fFrz.1‖ ^ 2 := by
      have := interiorCore_norm_sq_le hac hca fFrz
      rw [hnorm, one_pow] at this
      linarith
    have habs := abs_primeShellCorrelation_le_collar_defect hac hca fFrz
    rw [hnorm, one_pow] at habs
    have hneg : -(Real.exp (-a.1) *
        (Chebyshev.psi (Real.exp (2 * c.1)) - Chebyshev.psi (Real.exp (2 * a.1))) *
        (1 - ‖interiorCoreCutoff a c fFrz.1‖ ^ 2)) ≤ primeShellCorrelation (primeCutoff a) c fFrz := by
      linarith [neg_abs_le (primeShellCorrelation (primeCutoff a) c fFrz),
        habs.trans (mul_le_mul_of_nonneg_right hw hdef)]
    exact hneg.trans hlow

/-! ## 5. First-rung zero-width reduction from frozen relaxation and collar defect -/

/-- **Zero-width bound from frozen relaxation and collar-core concentration.** Along any monotone
unbounded sequence `A_j → ∞` with `A_{j+1} ≤ A_j + Δ` and `A_{j+1} ≤ 2 A_j`, if at each step the
sum of the fixed-operator frozen relaxation energy and the Chebyshev collar-defect shell bound is at
most `(1 − e^{2σ(A_{j+1} − A_j)}) μ(A_j) + δ_j` with bounded cumulative graded leakage, then
`CompensatedWidthFloor σ`, `zetaZeroWidth ≤ σ`, and `polarGroundEnergyRate ≤ σ` hold. -/
theorem zetaZeroWidth_le_of_frozen_relaxation_and_collar_defect
    {A : ℕ → SuzukiPositiveAperture} {δ : ℕ → ℝ} {σ C Δ : ℝ}
    (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hgap : ∀ j, (A (j + 1)).1 ≤ (A j).1 + Δ)
    (hmono : ∀ j, (A j).1 ≤ (A (j + 1)).1)
    (hdouble : ∀ j, (A (j + 1)).1 ≤ 2 * (A j).1)
    (hstep_bound : ∀ j,
      ((frozenFamily (primeCutoff (A j))).energy (A j) -
          (frozenFamily (primeCutoff (A j))).energy (A (j + 1))) +
        Real.exp (-(A j).1) *
          (Chebyshev.psi (Real.exp (2 * (A (j + 1)).1)) -
            Chebyshev.psi (Real.exp (2 * (A j).1))) *
          (1 - ‖interiorCoreCutoff (A j) (A (j + 1))
            (ccmArchimedeanFormToAperture (A (j + 1))
              (literalFamily.normalizedGround (A (j + 1)))).1‖ ^ 2) ≤
      (1 - Real.exp (2 * σ * ((A (j + 1)).1 - (A j).1))) *
          ccmRestrictedWeilGroundEnergy (A j) + δ j)
    (hsum : ∀ J : ℕ, ∑ j ∈ range J, Real.exp (-2 * σ * (A (j + 1)).1) * δ j ≤
      Real.exp (-2 * σ * (A 0).1) * ccmRestrictedWeilGroundEnergy (A 0) + C) :
    CompensatedWidthFloor σ ∧ zetaZeroWidth ≤ σ ∧ polarGroundEnergyRate ≤ σ := by
  refine zetaZeroWidth_le_of_graded_aperture_step hσ hC hΔ hAtop hgap (fun j => ?_) hsum
  have hrenorm := (apertureFlow_step_eq_geometric_add_arithmetic (hmono j)).1
  have harith := (frozen_sub_literal_energy_collar_sandwich (hmono j) (hdouble j)).1
  have hjump : ccmRestrictedWeilGroundEnergy (A j) - ccmRestrictedWeilGroundEnergy (A (j + 1)) ≤
      (1 - Real.exp (2 * σ * ((A (j + 1)).1 - (A j).1))) *
          ccmRestrictedWeilGroundEnergy (A j) + δ j := by
    linarith [hstep_bound j]
  have hE : Real.exp (-2 * σ * (A (j + 1)).1) * Real.exp (2 * σ * ((A (j + 1)).1 - (A j).1)) =
      Real.exp (-2 * σ * (A j).1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEpos := Real.exp_pos (-2 * σ * (A (j + 1)).1)
  have hmul := mul_le_mul_of_nonneg_left
    (show Real.exp (2 * σ * ((A (j + 1)).1 - (A j).1)) * ccmRestrictedWeilGroundEnergy (A j) -
        δ j ≤ ccmRestrictedWeilGroundEnergy (A (j + 1)) by linarith) hEpos.le
  rw [mul_sub, ← mul_assoc, hE] at hmul
  linarith

/-! ## 6. Exponential collapse of every frozen-prime family -/

private theorem abs_re_inner_visiblePrimeBlock_le (c : SuzukiPositiveAperture) (n : ℕ)
    (f : suzukiApertureHilbert c) :
    |(inner ℂ (ccmVisiblePrimeBlock c n f) f).re| ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * (2 * ‖f.1‖ ^ 2) := by
  by_cases hn : n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * c.1)))
  · rw [re_inner_visiblePrimeBlock_eq c n f hn]
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
    have hinv_le : 1 / Real.sqrt (n : ℝ) ≤ 1 := div_le_one_of_le₀ hsqrt_ge (Real.sqrt_nonneg _)
    have hpos : |(inner ℂ (logTranslationCLM (Real.log n) f.1) f.1).re| ≤ ‖f.1‖ ^ 2 := by
      calc |(inner ℂ (logTranslationCLM (Real.log n) f.1) f.1).re|
          ≤ ‖inner ℂ (logTranslationCLM (Real.log n) f.1) f.1‖ := Complex.abs_re_le_norm _
        _ ≤ ‖logTranslationCLM (Real.log n) f.1‖ * ‖f.1‖ := norm_inner_le_norm _ _
        _ = ‖f.1‖ ^ 2 := by rw [norm_logTranslationCLM_apply]; ring
    have hneg : |(inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re| ≤ ‖f.1‖ ^ 2 := by
      calc |(inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re|
          ≤ ‖inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1‖ := Complex.abs_re_le_norm _
        _ ≤ ‖logTranslationCLM (-Real.log n) f.1‖ * ‖f.1‖ := norm_inner_le_norm _ _
        _ = ‖f.1‖ ^ 2 := by rw [norm_logTranslationCLM_apply]; ring
    have hsum_re : |(inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
        inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re| ≤ 2 * ‖f.1‖ ^ 2 := by
      rw [Complex.add_re]
      linarith [abs_add_le (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1).re
        (inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re]
    have hw0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    rw [abs_mul, abs_of_nonneg hw0]
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          |(inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re|
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * (2 * ‖f.1‖ ^ 2) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hinv_le ArithmeticFunction.vonMangoldt_nonneg)
            hsum_re (abs_nonneg _)
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg zero_le_one)
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (2 * ‖f.1‖ ^ 2) := by ring
  · rw [ccmVisiblePrimeBlock_of_invisible c hn, zero_apply,
      inner_zero_left, Complex.zero_re, abs_zero]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- **Uniform Chebyshev bound between `frozenFamily N` and the prime-free continuous quadratic.**
For every cutoff `N : ℕ`, aperture `c`, and form vector `u`, the frozen quadratic form differs from
`ccmContinuousFormQuadratic c u` by at most `2 ψ(N) ‖J u‖²`. -/
theorem frozenFamily_Q_le_continuous_add_two_psi (N : ℕ) (c : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain c) :
    (frozenFamily N).Q c u ≤
      ccmContinuousFormQuadratic c u +
        2 * Chebyshev.psi (N : ℝ) * ‖ccmArchimedeanFormToAperture c u‖ ^ 2 := by
  set f := ccmArchimedeanFormToAperture c u
  set M := Nat.floor (Real.exp (2 * c.1))
  let g : ℕ → ℝ := fun n => (inner ℂ (ccmVisiblePrimeBlock c n f) f).re
  have hfin : (inner ℂ (ccmFinitePrimeOperator c f) f).re = ∑ n ∈ Finset.Ioc 0 M, g n := by
    rw [inner_ccmFinitePrimeOperator, Complex.re_sum]
    have hsub : Finset.Icc 2 M ⊆ Finset.Ioc 0 M := fun n hn => by
      rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ioc]; omega
    have h1 : ∑ n ∈ Finset.Icc 2 M,
        ((ArithmeticFunction.vonMangoldt n : ℝ) * inner ℂ (ccmPrimeTransportOperator c n f) f).re =
        ∑ n ∈ Finset.Icc 2 M, g n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      dsimp only [g]
      rw [ccmVisiblePrimeBlock, if_pos hn, smul_apply, inner_smul_left,
        Complex.conj_ofReal]
    rw [h1]
    refine Finset.sum_subset hsub fun n hn0 hn2 => ?_
    dsimp only [g]
    have hinv : n ∉ Finset.Icc 2 M := hn2
    rw [ccmVisiblePrimeBlock_of_invisible c hinv, zero_apply,
      inner_zero_left, Complex.zero_re]
  have hshell : primeShellCorrelation N c f = ∑ n ∈ Finset.Ioc (min N M) M, g n := by
    rw [primeShellCorrelation_eq_sum]
    have heq : Finset.Ioc N M = Finset.Ioc (min N M) M := by
      ext n; simp only [Finset.mem_Ioc]; omega
    rw [heq]
  have hunion : Finset.Ioc 0 M = Finset.Ioc 0 (min N M) ∪ Finset.Ioc (min N M) M := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ioc 0 (min N M)) (Finset.Ioc (min N M) M) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_Ioc] at h1 h2
    omega
  have hdiff : primeShellCorrelation N c f - (inner ℂ (ccmFinitePrimeOperator c f) f).re =
      -∑ n ∈ Finset.Ioc 0 (min N M), g n := by
    rw [hshell, hfin, hunion, Finset.sum_union hdisj]
    ring
  have hhead : |∑ n ∈ Finset.Ioc 0 (min N M), g n| ≤
      2 * Chebyshev.psi (N : ℝ) * ‖f‖ ^ 2 := by
    have hnorm_eq : ‖f.1‖ = ‖f‖ := rfl
    calc |∑ n ∈ Finset.Ioc 0 (min N M), g n|
        ≤ ∑ n ∈ Finset.Ioc 0 (min N M), |g n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc 0 (min N M),
            (ArithmeticFunction.vonMangoldt n : ℝ) * (2 * ‖f‖ ^ 2) := by
          refine Finset.sum_le_sum fun n _ => ?_
          simpa only [hnorm_eq] using abs_re_inner_visiblePrimeBlock_le c n f
      _ = (∑ n ∈ Finset.Ioc 0 (min N M), (ArithmeticFunction.vonMangoldt n : ℝ)) *
            (2 * ‖f‖ ^ 2) := (Finset.sum_mul _ _ _).symm
      _ ≤ Chebyshev.psi (N : ℝ) * (2 * ‖f‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
          intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [Finset.mem_Icc]
          exact ⟨Nat.zero_le n, hn.2.trans (Nat.min_le_left N M)⟩
      _ = 2 * Chebyshev.psi (N : ℝ) * ‖f‖ ^ 2 := by ring
  rw [frozenFamily_Q_eq, literalFamily_Q_eq, ccmContinuousFormQuadratic]
  linarith [neg_abs_le (∑ n ∈ Finset.Ioc 0 (min N M), g n), hdiff, hhead]

/-- **Exponential collapse of every frozen-prime family.** For every fixed cutoff `N : ℕ` and every
rate coefficient `α < 1`, eventually `(frozenFamily N).energy c ≤ −α e^c` as `c → ∞`: without the
unfreezing prime shell at `log n ≈ 2c`, the odd polar mode drives the Rayleigh quotient down at
exponential rate `−e^c`. -/
theorem eventually_frozenFamily_energy_le_neg_mul_exp (N : ℕ) {α : ℝ} (hα : α < 1) :
    ∀ᶠ c : SuzukiPositiveAperture in atTop,
      (frozenFamily N).energy c ≤ -α * Real.exp c.1 := by
  set β : ℝ := max α 0
  have hβ_nonneg : 0 ≤ β := le_max_right α 0
  have hβ_lt : β < 1 := max_lt hα zero_lt_one
  have h1sub_pos : 0 < 1 - β := sub_pos.mpr hβ_lt
  have hev_bal : ∀ᶠ c : SuzukiPositiveAperture in atTop,
      Real.exp (-(2 * c.1)) * ccmOddPoleGammaPolarBalance c < -(1 + β) :=
    tendsto_ccmOddPoleGammaPolarBalance_scaled_neg_two.eventually
      (Iio_mem_nhds (by linarith))
  set B : ℝ := max 3 (Real.log (4 * Chebyshev.psi (N : ℝ) / (1 - β) + 1))
  have hB_pos : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_left _ _)
  have hev_ge : ∀ᶠ c : SuzukiPositiveAperture in atTop, (⟨B, hB_pos⟩ : SuzukiPositiveAperture) ≤ c :=
    Filter.eventually_ge_atTop (⟨B, hB_pos⟩ : SuzukiPositiveAperture)
  filter_upwards [hev_bal, hev_ge] with c hbal hcB
  have hcB' : B ≤ c.1 := hcB
  have hc3 : 3 ≤ c.1 := (le_max_left 3 _).trans hcB'
  have hclog : Real.log (4 * Chebyshev.psi (N : ℝ) / (1 - β) + 1) ≤ c.1 :=
    (le_max_right 3 _).trans hcB'
  have hpsi_nonneg : 0 ≤ Chebyshev.psi (N : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hexp_psi : 4 * Chebyshev.psi (N : ℝ) / (1 - β) + 1 ≤ Real.exp c.1 := by
    have harg_pos : 0 < 4 * Chebyshev.psi (N : ℝ) / (1 - β) + 1 := by positivity
    rw [← Real.exp_log harg_pos]
    exact Real.exp_le_exp.mpr hclog
  have hpsi_le : 2 * Chebyshev.psi (N : ℝ) ≤ ((1 - β) / 2) * Real.exp c.1 := by
    have hm := mul_le_mul_of_nonneg_left hexp_psi h1sub_pos.le
    have hcancel : (1 - β) * (4 * Chebyshev.psi (N : ℝ) / (1 - β) + 1) =
        4 * Chebyshev.psi (N : ℝ) + (1 - β) := by
      field_simp [h1sub_pos.ne']
    linarith
  set u := ccmPolarParityFormVector c (-1)
  set D := ‖ccmArchimedeanFormToAperture c u‖ ^ 2
  have hD_eq : D = 2 * Real.exp c.1 - 2 * Real.exp (-c.1) - 4 * c.1 := by
    dsimp only [D, u]
    rw [norm_sq_ccmPolarParityFormVector_physical c (Or.inr rfl), Real.sinh_eq]
    ring
  have hD_le : D ≤ 2 * Real.exp c.1 := by
    rw [hD_eq]
    linarith [Real.exp_pos (-c.1), c.2]
  have hD_pos : 0 < D := by
    have hquad := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ c.1)
    have hexp_neg_le : Real.exp (-c.1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [hD_eq]
    nlinarith
  have hbal_le : ccmOddPoleGammaPolarBalance c ≤ -(1 + β) * Real.exp (2 * c.1) := by
    have hm := mul_lt_mul_of_pos_left hbal (Real.exp_pos (2 * c.1))
    have hexp_cancel : Real.exp (2 * c.1) *
        (Real.exp (-(2 * c.1)) * ccmOddPoleGammaPolarBalance c) =
        ccmOddPoleGammaPolarBalance c := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [hexp_cancel] at hm
    linarith
  have hbal_D : ccmOddPoleGammaPolarBalance c ≤ -((1 + β) / 2 * Real.exp c.1) * D := by
    have hm := mul_le_mul_of_nonneg_left hD_le
      (show 0 ≤ (1 + β) / 2 * Real.exp c.1 by positivity)
    have hexp2 : ((1 + β) / 2 * Real.exp c.1) * (2 * Real.exp c.1) =
        (1 + β) * Real.exp (2 * c.1) := by
      calc ((1 + β) / 2 * Real.exp c.1) * (2 * Real.exp c.1)
          = (1 + β) * (Real.exp c.1 * Real.exp c.1) := by ring
        _ = (1 + β) * Real.exp (2 * c.1) := by rw [← Real.exp_add]; congr 2; ring
    linarith
  have hray := (frozenFamily N).energy_mul_formNorm_sq_le c u
  have hQ := frozenFamily_Q_le_continuous_add_two_psi N c u
  rw [ccmContinuousFormQuadratic_oddPole c] at hQ
  have hmul_D : (frozenFamily N).energy c * D ≤
      (-((1 + β) / 2 * Real.exp c.1) + 2 * Chebyshev.psi (N : ℝ)) * D := by
    change (frozenFamily N).energy c * D ≤ (frozenFamily N).Q c u at hray
    change (frozenFamily N).Q c u ≤ ccmOddPoleGammaPolarBalance c + 2 * Chebyshev.psi (N : ℝ) * D at hQ
    nlinarith
  have henergy_le : (frozenFamily N).energy c ≤
      -((1 + β) / 2 * Real.exp c.1) + 2 * Chebyshev.psi (N : ℝ) :=
    le_of_mul_le_mul_right hmul_D hD_pos
  have hαβ : -β * Real.exp c.1 ≤ -α * Real.exp c.1 := by
    have : α ≤ β := le_max_left α 0
    nlinarith [Real.exp_pos c.1]
  linarith

/-- For every fixed cutoff `N : ℕ`, `(frozenFamily N).energy c → −∞` as `c → ∞`. -/
theorem tendsto_frozenFamily_energy_atBot (N : ℕ) :
    Tendsto (fun c : SuzukiPositiveAperture => (frozenFamily N).energy c) atTop atBot := by
  rw [Filter.tendsto_atTop_atBot]
  intro b
  have hev := eventually_frozenFamily_energy_le_neg_mul_exp N (α := 1 / 2) (by norm_num)
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.mp hev
  set B : ℝ := max c₀.1 (Real.log (2 * max (-b) 0 + 1))
  have hB_pos : 0 < B := lt_of_lt_of_le c₀.2 (le_max_left _ _)
  refine ⟨⟨B, hB_pos⟩, fun c hc => ?_⟩
  have hcc₀ : c₀ ≤ c := le_trans (le_max_left c₀.1 _) hc
  have hlog : Real.log (2 * max (-b) 0 + 1) ≤ c.1 := le_trans (le_max_right c₀.1 _) hc
  have hexp : 2 * max (-b) 0 + 1 ≤ Real.exp c.1 := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * max (-b) 0 + 1)]
    exact Real.exp_le_exp.mpr hlog
  linarith [hc₀ c hcc₀, le_max_left (-b) 0]

/-- **No subtrivial exponential floor for any frozen-prime family.** For every fixed `N : ℕ` and
every `σ < 1/2`, no lower bound `−C e^{2σ c} ≤ (frozenFamily N).energy c` can hold at all large
apertures `c`: freezing the prime shell destroys every zero-free strip beyond the trivial line
`σ = 1/2`. -/
theorem not_exists_subtrivial_exp_floor_frozenFamily (N : ℕ) {σ : ℝ} (hσ : σ < 1 / 2) :
    ¬ ∃ C A₀ : ℝ, ∀ c : SuzukiPositiveAperture, A₀ ≤ c.1 →
      -C * Real.exp (2 * σ * c.1) ≤ (frozenFamily N).energy c := by
  rintro ⟨C, A₀, hfloor⟩
  have hev := eventually_frozenFamily_energy_le_neg_mul_exp N (α := 1 / 2) (by norm_num)
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.mp hev
  have hgap : 0 < 1 - 2 * σ := by linarith
  set K : ℝ := 2 * max C 0 + 1
  have hK_pos : 0 < K := by positivity
  set B : ℝ := max (max c₀.1 (max A₀ 1)) (Real.log K / (1 - 2 * σ))
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one
    ((le_max_right A₀ 1).trans ((le_max_right c₀.1 _).trans (le_max_left _ _)))
  let c : SuzukiPositiveAperture := ⟨B, hB_pos⟩
  have hcc₀ : c₀ ≤ c := (le_max_left c₀.1 _).trans (le_max_left _ _)
  have hcA₀ : A₀ ≤ c.1 := (le_max_left A₀ 1).trans ((le_max_right c₀.1 _).trans (le_max_left _ _))
  have hlogK : Real.log K ≤ (1 - 2 * σ) * c.1 := by
    have hdiv : Real.log K / (1 - 2 * σ) ≤ c.1 := le_max_right _ _
    linarith [(div_le_iff₀ hgap).mp hdiv]
  have hexpK : K ≤ Real.exp ((1 - 2 * σ) * c.1) := by
    rw [← Real.exp_log hK_pos]
    exact Real.exp_le_exp.mpr hlogK
  have hmul : K * Real.exp (2 * σ * c.1) ≤ Real.exp c.1 := by
    calc K * Real.exp (2 * σ * c.1)
        ≤ Real.exp ((1 - 2 * σ) * c.1) * Real.exp (2 * σ * c.1) :=
          mul_le_mul_of_nonneg_right hexpK (Real.exp_pos _).le
      _ = Real.exp c.1 := by rw [← Real.exp_add]; congr 1; ring
  have h1 := hfloor c hcA₀
  have h2 := hc₀ c hcc₀
  have hCK : 2 * C < K := by
    dsimp only [K]
    linarith [le_max_left C 0]
  nlinarith [Real.exp_pos (2 * σ * c.1)]

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
