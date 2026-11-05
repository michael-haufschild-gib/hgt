import GaloisForLFunctions.RHTower.MollifiedMeanSquareGaussianPrimeFloor
import GaloisForLFunctions.RHTower.BarbanVehovMollifiedZetaTail
import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.RHTower.Sieve.MollifierShortRange
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular
import GaloisForLFunctions.RHTower.Sieve.VerticalPoleIntegral
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.RHTower.WeilFunctionalLineIntegral
import GaloisForLFunctions.RHTower.BurnolIntegrand
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ClusteringLogMeanAndMollifierEquivalence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Two-Sided `θ`-Trap for Critical-Line Mollification and Flow Credited Divergence

For polynomial-length Dirichlet mollifiers `Ψ(s) = ∑_{d ≤ y} b_d d^{-s}` on `Re s = 1/2` (and
`Re s = 1/2 + a / log T` with `a ≥ 0`), this module establishes a two-sided unconditional regime
dichotomy across `θ ∈ (0, ∞)` together with unconditional divergence of the credited Jensen budget
on the vertical flow `[T, 2T]`:

1. **Short/subcritical regime (`0 < θ < 1`, all `a ≥ 0` including `σ = 1/2`):**
   - *Prime-log floor:* Keeping `n = 1` and primes `p ∈ (y, M]` at `M = ⌊T^{θ'}⌋` (`θ' → 1⁻`) with
     sharp Mertens' second theorem (`abs_mertensS_sub_logLog_sub_const_le`) gives
     `∫_T^{2T} ‖ζΨ(1/2 + a/log T + it)‖² dt ≥ (1 + e^{-2a} log(1/θ) - ε) T`.
   - *`y`-rough `1/θ` blowup floor:* Splitting every `m ∈ [1, M]` into its `y`-smooth and `y`-rough
     parts gives `∑_{v ≤ M, P⁻(v) > y} 1/v ≥ c_rough · (log M) / max(1, log y)`, yielding an
     explicit `c_rough > 0` with
     `∫_T^{2T} ‖ζΨ(1/2 + a/log T + it)‖² dt ≥ (c_rough e^{-2a} / θ - ε) T`.

2. **Unconditional vertical-flow credited-Jensen divergence:**
   For every nonzero Dirichlet polynomial `Ψ(s) = ∑_{d ≤ y} b_d d^{-s}` (`1 ≤ y ≤ (log T)^{1/8}`,
   arbitrary complex coefficients and right-half zeros), Möbius inversion on `[1, y]` produces an
   index `e_* ≤ y` with `‖c_{e_*}‖ ≥ y⁻¹ max_d ‖b_d‖`, and `c_{e_* · v} = c_{e_*}` for all
   `y`-rough `v`, forcing
   `½ log(T⁻¹ ∫_T^{2T} ‖ζΨ(1/2+it)‖² dt) - T⁻¹ ∫_T^{2T} log‖Ψ(1/2+it)‖ dt → +∞`.

3. **Long/supercritical regime (`θ > 1` and `θ → ∞`):**
   Using the holomorphic divided difference `dslope F 0` of
   `F(w) = ζ(ρ₀ + w) Ψ(ρ₀ + w) exp(α w² + w log Y)` around an off-line zero
   `ρ₀ = 1/2 + δ₀ + iγ₀` (`δ₀ > 0`), compact Fubini evaluation of the error-function integral on
   `Re s = 2` produces a localized critical-line spike
   `∫_{γ₀-R}^{γ₀+R} ‖ζΨ(1/2+it)‖² dt ≥ (1/25) δ₀ e^{-2αδ₀²} Y^{2δ₀}`.
   Consequently:
   - Dyadic second-moment boundedness on `[T, 2T]` at prefix-cancellation length `X₁ ≥ T^{θ₁}`
     (`θ₁ > 1/2`) forces eventual quasi-RH (`|Re ρ - 1/2| < 1/(2θ₁) + ε` for all but finitely many
     nontrivial zeros).
   - Cofinal second-moment boundedness on `[1, T]` for prefix-exact mollifiers (`X ≤ T^θ`,
     `X₁ ≥ T^{θ/2}`) across arbitrarily large `θ > 0` implies `RiemannHypothesis`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ArithmeticFunction.Moebius BigOperators

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-! ## §1. Arithmetic splitting into `y`-smooth and `y`-rough parts -/

/-- The `y`-smooth factor `∏_{p ∣ m, p ≤ y} p^{v_p(m)}` of a natural number `m`. -/
def smoothPart (y m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (· ≤ y), p ^ (m.factorization p)

/-- The `y`-rough factor `∏_{p ∣ m, p > y} p^{v_p(m)}` of a natural number `m`. -/
def roughPart (y m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ y), p ^ (m.factorization p)

theorem smoothPart_mul_roughPart {m : ℕ} (y : ℕ) (hm : 1 ≤ m) :
    smoothPart y m * roughPart y m = m := by
  unfold smoothPart roughPart
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self (by omega)

theorem smoothPart_pos {m : ℕ} (y : ℕ) (hm : 1 ≤ m) : 1 ≤ smoothPart y m := by
  have h := smoothPart_mul_roughPart y hm
  rcases Nat.eq_zero_or_pos (smoothPart y m) with h0 | hp
  · rw [h0, zero_mul] at h; omega
  · omega

theorem roughPart_pos {m : ℕ} (y : ℕ) (hm : 1 ≤ m) : 1 ≤ roughPart y m := by
  have h := smoothPart_mul_roughPart y hm
  rcases Nat.eq_zero_or_pos (roughPart y m) with h0 | hp
  · rw [h0, mul_zero] at h; omega
  · omega

theorem smoothPart_le {m : ℕ} (y : ℕ) (hm : 1 ≤ m) : smoothPart y m ≤ m := by
  have h := smoothPart_mul_roughPart y hm
  calc smoothPart y m ≤ smoothPart y m * roughPart y m :=
        Nat.le_mul_of_pos_right _ (roughPart_pos y hm)
    _ = m := h

theorem roughPart_le {m : ℕ} (y : ℕ) (hm : 1 ≤ m) : roughPart y m ≤ m := by
  have h := smoothPart_mul_roughPart y hm
  calc roughPart y m ≤ smoothPart y m * roughPart y m :=
        Nat.le_mul_of_pos_left _ (smoothPart_pos y hm)
    _ = m := h

/-- Every prime divisor of `roughPart y m` strictly exceeds `y`. -/
theorem gt_of_prime_dvd_roughPart {y m q : ℕ} (hq : q.Prime) (hdvd : q ∣ roughPart y m) :
    y < q := by
  unfold roughPart at hdvd
  rw [hq.prime.dvd_finsetProd_iff] at hdvd
  obtain ⟨p, hp, hqp⟩ := hdvd
  have hp_mem := (Finset.mem_filter.mp hp).1
  have hp_gt : ¬ p ≤ y := (Finset.mem_filter.mp hp).2
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hqp' : q ∣ p := hq.dvd_of_dvd_pow hqp
  have heq : q = p := ((hp_prime.dvd_iff_eq hq.ne_one).mp hqp').symm
  omega

/-- Every integer `d ∈ [1, y]` is coprime to every `roughPart y m`. -/
theorem coprime_of_le_roughPart {y m d : ℕ} (hd1 : 1 ≤ d) (hdy : d ≤ y) :
    Nat.Coprime d (roughPart y m) := by
  refine Nat.coprime_of_dvd fun q hq hqd hqv => ?_
  have hqy := gt_of_prime_dvd_roughPart hq hqv
  have hqd_le : q ≤ d := Nat.le_of_dvd (by omega) hqd
  omega

/-- Multiplying any integer `e` by `roughPart y m` leaves `mollifiedZetaCoeff b y` unchanged. -/
theorem mollifiedZetaCoeff_mul_roughPart (b : ℕ → ℂ) (y e m : ℕ) :
    RHTower.mollifiedZetaCoeff b y (e * roughPart y m) = RHTower.mollifiedZetaCoeff b y e := by
  unfold RHTower.mollifiedZetaCoeff
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, and_congr_right_iff]
  rintro ⟨hd1, hdy⟩
  constructor
  · intro hdvd
    exact (coprime_of_le_roughPart hd1 hdy).dvd_of_dvd_mul_right hdvd
  · intro hdvd
    exact dvd_mul_of_dvd_left hdvd _

theorem mollifiedZetaCoeff_roughPart {b : ℕ → ℂ} {y : ℕ} (hy : 1 ≤ y) (hb1 : b 1 = 1) (m : ℕ) :
    RHTower.mollifiedZetaCoeff b y (roughPart y m) = 1 := by
  have h := mollifiedZetaCoeff_mul_roughPart b y 1 m
  rw [one_mul] at h
  rw [h]
  unfold RHTower.mollifiedZetaCoeff
  have h1 : (Finset.Icc 1 y).filter (· ∣ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Nat.dvd_one]
    omega
  rw [h1, Finset.sum_singleton, hb1]

theorem smoothPart_eq_prod_primesLE {y m : ℕ} (_hm : 1 ≤ m) :
    smoothPart y m = ∏ p ∈ Nat.primesLE y, p ^ (m.factorization p) := by
  unfold smoothPart
  refine Finset.prod_subset (fun p hp => ?_) (fun p hpP hpnot => ?_)
  · obtain ⟨hpm, hpy⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy, Nat.prime_of_mem_primeFactors hpm⟩
  · by_cases hpm : p ∈ m.primeFactors
    · exact absurd (Finset.mem_filter.mpr ⟨hpm, (Nat.mem_primesLE.mp hpP).1⟩) hpnot
    · have h0 : m.factorization p = 0 := by
        rw [← Nat.support_factorization] at hpm
        exact Finsupp.notMem_support_iff.mp hpm
      rw [h0, pow_zero]

theorem factorization_le_self (m p : ℕ) : m.factorization p ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · by_cases hp : p ∈ m.primeFactors
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      calc m.factorization p ≤ 2 ^ (m.factorization p) := Nat.lt_two_pow_self.le
        _ ≤ p ^ (m.factorization p) := Nat.pow_le_pow_left hp2 _
        _ ≤ m := Nat.ordProj_le p (by omega)
    · have h0 : m.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.notMem_support_iff.mp hp
      rw [h0]; omega

/-- Upper bound for the reciprocal sum over all `y`-smooth parts of `[1, M]` via `mertensS y`. -/
theorem sum_inv_image_smoothPart_le (y M : ℕ) :
    ∑ u ∈ (Finset.Icc 1 M).image (smoothPart y), (1 / (u : ℝ)) ≤
      Real.exp (1 + RHTower.Sieve.mertensS y) := by
  classical
  let P : Finset ℕ := Nat.primesLE y
  let Box : Finset (∀ _ : P, ℕ) := Fintype.piFinset fun _ : P => Finset.Icc 0 M
  let Φ : (∀ _ : P, ℕ) → ℕ := fun g => ∏ p : P, (p : ℕ) ^ g p
  have hsub : (Finset.Icc 1 M).image (smoothPart y) ⊆ Box.image Φ := by
    intro u hu
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    refine Finset.mem_image.mpr ⟨fun p => m.factorization (p : ℕ), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro p
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (factorization_le_self m p).trans hmM⟩
    · simp only [Φ]
      rw [smoothPart_eq_prod_primesLE hm1, ← Finset.prod_coe_sort P (fun p => p ^ m.factorization p)]
  have h1 : ∑ u ∈ (Finset.Icc 1 M).image (smoothPart y), (1 / (u : ℝ)) ≤
      ∑ u ∈ Box.image Φ, (1 / (u : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have h2 : ∑ u ∈ Box.image Φ, (1 / (u : ℝ)) ≤ ∑ g ∈ Box, (1 / (Φ g : ℝ)) :=
    Finset.sum_image_le_of_nonneg fun _ _ => by positivity
  have h3 : ∑ g ∈ Box, (1 / (Φ g : ℝ)) =
      ∏ p : P, ∑ e ∈ Finset.Icc 0 M, ((1 / ((p : ℕ) : ℝ)) ^ e) := by
    have hps := (Finset.prod_univ_sum (t := fun _ : P => Finset.Icc 0 M)
      (f := fun (p : P) (e : ℕ) => (1 / ((p : ℕ) : ℝ)) ^ e)).symm
    refine (Finset.sum_congr rfl fun g _ => ?_).trans hps
    simp only [Φ, Nat.cast_prod, Nat.cast_pow, one_div]
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [inv_pow]
  have hgeom : ∀ p : P, ∑ e ∈ Finset.Icc 0 M, ((1 / ((p : ℕ) : ℝ)) ^ e) ≤
      ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1) := by
    intro p
    have hp_prime := (Nat.mem_primesLE.mp p.2).2
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp_prime.two_le
    have hrange : Finset.Icc 0 M = Finset.range (M + 1) := by
      ext e; simp
    rw [hrange]
    set r : ℝ := 1 / ((p : ℕ) : ℝ)
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by simp only [r]; rw [div_lt_one (by linarith)]; linarith
    have hgs := geom_sum_mul_neg r (M + 1)
    have hpos : 0 < 1 - r := by linarith
    have hle1 : (∑ i ∈ Finset.range (M + 1), r ^ i) * (1 - r) ≤ 1 := by
      have : 0 ≤ r ^ (M + 1) := pow_nonneg hr0 _
      linarith
    have hdiv : ∑ i ∈ Finset.range (M + 1), r ^ i ≤ 1 / (1 - r) :=
      (le_div_iff₀ hpos).mpr hle1
    have heq : 1 / (1 - r) = ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1) := by
      simp only [r]; field_simp
    rwa [heq] at hdiv
  have h4 : (∏ p : P, ∑ e ∈ Finset.Icc 0 M, ((1 / ((p : ℕ) : ℝ)) ^ e)) ≤
      ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) := by
    calc (∏ p : P, ∑ e ∈ Finset.Icc 0 M, ((1 / ((p : ℕ) : ℝ)) ^ e))
        ≤ ∏ p : P, (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) :=
          Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun _ _ => by positivity)
            (fun p _ => hgeom p)
      _ = ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) :=
          Finset.prod_coe_sort P (fun p : ℕ => (p : ℝ) / ((p : ℝ) - 1))
  have h5 : ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (∑ p ∈ P, (1 / ((p : ℝ) - 1))) := by
    calc ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ p ∈ P, Real.exp (1 / ((p : ℝ) - 1)) := by
          refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
          · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
            have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            positivity
          · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
            have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
            have hstep := Real.add_one_le_exp (1 / ((p : ℝ) - 1))
            have heq : (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
              field_simp; ring
            linarith
      _ = Real.exp (∑ p ∈ P, (1 / ((p : ℝ) - 1))) := (Real.exp_sum _ _).symm
  have h6 : ∑ p ∈ P, (1 / ((p : ℝ) - 1)) ≤ 1 + RHTower.Sieve.mertensS y := by
    have hsplit : ∀ p ∈ P, 1 / ((p : ℝ) - 1) =
        1 / (p : ℝ) + (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := fun _ _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hmert : ∑ p ∈ P, 1 / (p : ℝ) = RHTower.Sieve.mertensS y := rfl
    rw [hmert, add_comm]
    gcongr
    have hsubP : P ⊆ Finset.Ico 2 (y + 1) := fun p hp => by
      obtain ⟨hpy, hpp⟩ := Nat.mem_primesLE.mp hp
      exact Finset.mem_Ico.mpr ⟨hpp.two_le, by omega⟩
    calc ∑ p ∈ P, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))
        ≤ ∑ k ∈ Finset.Ico 2 (y + 1), (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubP fun k hk _ => ?_
          have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
          exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) (by linarith))
      _ ≤ 1 := by
          rcases lt_or_ge y 2 with hy2 | hy2
          · have hempty : Finset.Ico 2 (y + 1) = ∅ := by
              ext k; simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
              rintro ⟨hk1, hk2⟩; omega
            rw [hempty, Finset.sum_empty]; norm_num
          · have hico := Finset.sum_Ico_sub (fun k : ℕ => -(1 / ((k : ℝ) - 1))) (by omega : 2 ≤ y + 1)
            have hrw : ∀ k ∈ Finset.Ico 2 (y + 1),
                (-(1 / (((k + 1 : ℕ) : ℝ) - 1))) - (-(1 / ((k : ℝ) - 1))) =
                  1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
              intro k _
              push_cast
              ring
            rw [← Finset.sum_congr rfl hrw, hico]
            push_cast
            have hypos : (0 : ℝ) ≤ 1 / (y : ℝ) := by positivity
            have hrhs : -(1 / (((y : ℝ) + 1) - 1)) - -(1 / ((2 : ℝ) - 1)) = 1 - 1 / (y : ℝ) := by
              ring
            rw [hrhs]
            linarith
  exact h1.trans (h2.trans (h3.le.trans (h4.trans (h5.trans (Real.exp_le_exp.mpr h6)))))

/-- Harmonic lower bound `log (M + 1) ≤ ∑_{m = 1}^M 1 / m`. -/
theorem log_add_one_le_sum_inv (M : ℕ) :
    Real.log ((M : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ)) := by
  induction M with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hstep : Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k : ℝ) + 1) ≤
        1 / ((k + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div (by positivity) hk1.ne']
      have hdiv : (((k + 1 : ℕ) : ℝ) + 1) / ((k : ℝ) + 1) = 1 + 1 / ((k + 1 : ℕ) : ℝ) := by
        push_cast; field_simp
      rw [hdiv]
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((k + 1 : ℕ) : ℝ))
      linarith
    linarith

/-- Lower bound for the reciprocal sum over `y`-rough parts in `[1, M]`. -/
theorem sum_inv_image_roughPart_ge (y M : ℕ) :
    Real.log ((M : ℝ) + 1) / Real.exp (1 + RHTower.Sieve.mertensS y) ≤
      ∑ v ∈ (Finset.Icc 1 M).image (roughPart y), (1 / (v : ℝ)) := by
  classical
  let U := (Finset.Icc 1 M).image (smoothPart y)
  let V := (Finset.Icc 1 M).image (roughPart y)
  have hprod : ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ)) ≤
      (∑ u ∈ U, (1 / (u : ℝ))) * (∑ v ∈ V, (1 / (v : ℝ))) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    let φ : ℕ → ℕ × ℕ := fun m => (smoothPart y m, roughPart y m)
    have hinj : Set.InjOn φ (Finset.Icc 1 M) := by
      intro m₁ hm₁ m₂ hm₂ heq
      have h1 := smoothPart_mul_roughPart y (Finset.mem_Icc.mp hm₁).1
      have h2 := smoothPart_mul_roughPart y (Finset.mem_Icc.mp hm₂).1
      have hfst : smoothPart y m₁ = smoothPart y m₂ := congrArg Prod.fst heq
      have hsnd : roughPart y m₁ = roughPart y m₂ := congrArg Prod.snd heq
      rw [← h1, ← h2, hfst, hsnd]
    have hsub : (Finset.Icc 1 M).image φ ⊆ U ×ˢ V := by
      intro p hp
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hm, Finset.mem_image_of_mem _ hm⟩
    have hval : ∀ m ∈ Finset.Icc 1 M,
        (1 / (m : ℝ)) = (1 / ((φ m).1 : ℝ)) * (1 / ((φ m).2 : ℝ)) := by
      intro m hm
      have h := smoothPart_mul_roughPart y (Finset.mem_Icc.mp hm).1
      simp only [φ]
      conv_lhs => rw [← h]
      push_cast
      ring
    calc ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ))
        = ∑ m ∈ Finset.Icc 1 M, (1 / ((φ m).1 : ℝ)) * (1 / ((φ m).2 : ℝ)) :=
          Finset.sum_congr rfl hval
      _ = ∑ p ∈ (Finset.Icc 1 M).image φ, (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) :=
          (Finset.sum_image (f := fun p : ℕ × ℕ => (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ))) hinj).symm
      _ ≤ ∑ p ∈ U ×ˢ V, (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hU_le := sum_inv_image_smoothPart_le y M
  have hV_nonneg : 0 ≤ ∑ v ∈ V, (1 / (v : ℝ)) := Finset.sum_nonneg fun _ _ => by positivity
  have hexp_pos : 0 < Real.exp (1 + RHTower.Sieve.mertensS y) := Real.exp_pos _
  rw [div_le_iff₀ hexp_pos]
  calc Real.log ((M : ℝ) + 1)
      ≤ ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ)) := log_add_one_le_sum_inv M
    _ ≤ (∑ u ∈ U, (1 / (u : ℝ))) * (∑ v ∈ V, (1 / (v : ℝ))) := hprod
    _ ≤ Real.exp (1 + RHTower.Sieve.mertensS y) * (∑ v ∈ V, (1 / (v : ℝ))) :=
        mul_le_mul_of_nonneg_right hU_le hV_nonneg
    _ = (∑ v ∈ V, (1 / (v : ℝ))) * Real.exp (1 + RHTower.Sieve.mertensS y) := mul_comm _ _

/-- Universal explicit constant `c_rough > 0` for the `y`-rough `1/θ` floor. -/
def roughMollifierConst : ℝ :=
  Real.exp (-(1 + |RHTower.Sieve.meisselMertensConst| +
    (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log 2))

theorem roughMollifierConst_pos : 0 < roughMollifierConst := by
  unfold roughMollifierConst
  exact Real.exp_pos _

theorem exp_one_add_mertensS_le_inv_roughMollifierConst {y : ℕ} {B : ℝ}
    (hy1 : 1 ≤ y) (hB1 : 1 ≤ B) (hlogy : Real.log (y : ℝ) ≤ B) :
    Real.exp (1 + RHTower.Sieve.mertensS y) ≤ B / roughMollifierConst := by
  unfold roughMollifierConst
  rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  have ⟨C₀, hC₀⟩ : ∃ x : ℝ, x = 1 + |RHTower.Sieve.meisselMertensConst| +
    (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log 2 := ⟨_, rfl⟩
  rw [← hC₀]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases eq_or_lt_of_le hy1 with rfl | hy2
  · have hm1 : RHTower.Sieve.mertensS 1 = 0 := by
      unfold RHTower.Sieve.mertensS
      have hempty : Nat.primesLE 1 = ∅ := by
        ext p; simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false]
        rintro ⟨hp1, hp⟩; exact absurd hp.two_le (by omega)
      rw [hempty, Finset.sum_empty]
    rw [hm1, add_zero]
    have hleC : Real.exp 1 ≤ Real.exp C₀ := by
      apply Real.exp_le_exp.mpr
      have := abs_nonneg RHTower.Sieve.meisselMertensConst
      have : 0 ≤ (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log 2 := by
        have := RHTower.Sieve.mertensFirstConst_nonneg; positivity
      linarith
    calc Real.exp 1 ≤ 1 * Real.exp C₀ := by rw [one_mul]; exact hleC
      _ ≤ B * Real.exp C₀ := mul_le_mul_of_nonneg_right hB1 (Real.exp_pos _).le
  · have hy2' : 2 ≤ y := by omega
    have hM := RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le hy2'
    have hlogy_ge : Real.log 2 ≤ Real.log (y : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy2')
    have hlogy_pos : 0 < Real.log (y : ℝ) := lt_of_lt_of_le hlog2 hlogy_ge
    have herr_le : (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log (y : ℝ) ≤
        (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log 2 :=
      div_le_div_of_nonneg_left (by have := RHTower.Sieve.mertensFirstConst_nonneg; linarith)
        hlog2 hlogy_ge
    have hMM : RHTower.Sieve.meisselMertensConst ≤ |RHTower.Sieve.meisselMertensConst| :=
      le_abs_self _
    have hm_ub : 1 + RHTower.Sieve.mertensS y ≤ Real.log (Real.log (y : ℝ)) + C₀ := by
      have h1 := (abs_le.mp hM).2
      unfold RHTower.Sieve.logLog at h1
      linarith
    calc Real.exp (1 + RHTower.Sieve.mertensS y)
        ≤ Real.exp (Real.log (Real.log (y : ℝ)) + C₀) := Real.exp_le_exp.mpr hm_ub
      _ = Real.log (y : ℝ) * Real.exp C₀ := by
          rw [Real.exp_add, Real.exp_log hlogy_pos]
      _ ≤ B * Real.exp C₀ := mul_le_mul_of_nonneg_right hlogy (Real.exp_pos _).le

/-! ## §1b. Critical-line & right-shifted prime-log and `y`-rough `1/θ` Gaussian floors -/

/-- General Gaussian floor assembly on `Re s = 1/2 + a / L` (`a ≥ 0`, including `a = 0`) for any
lower bound `D₀ ≥ 1` on the truncated mollified Dirichlet energy `D` at parameter `θ₁ ∈ (0, 1)`. -/
theorem gaussFloor_general_at_scale {a θ₁ L D₀ δ : ℝ}
    (ha : 0 ≤ a) (hθ₁0 : 0 < θ₁) (hθ₁1 : θ₁ < 1) (hD₀1 : 1 ≤ D₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hLa : 2 * a + 3 ≤ L) (hδL8 : 8 ≤ (1 - θ₁) / 4 * L)
    (hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L)
    (hsup : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤ δ / 6)
    {y : ℕ} (hy : 1 ≤ y) (hyle : (y : ℝ) ≤ Real.exp (θ₁ * L)) {b : ℕ → ℂ}
    (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L))) :
    (D₀ - δ) * Real.exp L ≤
      ∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hL0 : 0 < L := by linarith
  set M : ℕ := ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊
  have hMle : (M : ℝ) ≤ Real.exp ((θ₁ + (1 - θ₁) / 4) * L) := Nat.floor_le (by positivity)
  have hMgt : Real.exp ((θ₁ + (1 - θ₁) / 4) * L) - 1 < M := by
    have := Nat.lt_floor_add_one (Real.exp ((θ₁ + (1 - θ₁) / 4) * L)); linarith
  have hc0 : 0 < δ / D₀ := by positivity
  obtain ⟨hM2, _, _, hHM, h2R⟩ :=
    RHTower.gaussFloor_scale hθ₁0 hc0 hL0 hδL8 hδLc hyle hMle hMgt
  have hσ12 : 1 / 2 ≤ 1 / 2 + a / L := by
    have : 0 ≤ a / L := div_nonneg ha hL0.le; linarith
  have hσ1 : 1 / 2 + a / L < 1 := by
    have : a / L < 1 / 2 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  obtain ⟨hE1, hE2⟩ := RHTower.gaussFloor_error_bounds (σ := 1 / 2 + a / L) hθ₁0.le hθ₁1 hL0.le
    hy hyle (by omega : 1 ≤ M) hMle hsup hb (by linarith)
  set H : ℝ := Real.exp ((θ₁ + (1 - θ₁) / 2) * L)
  set R : ℝ := Real.exp ((θ₁ + 3 * (1 - θ₁) / 4) * L)
  have hR0 : 0 < R := Real.exp_pos _
  have hH0 : 0 < H := Real.exp_pos _
  have hT4 : 4 ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hδD_le1 : δ / D₀ ≤ 1 := (div_le_one (by linarith)).mpr (hδ1.trans hD₀1)
  have h2R_le : 32 * R ≤ Real.exp L :=
    h2R.trans (mul_le_of_le_one_left (Real.exp_pos _).le hδD_le1)
  have hRT : Real.exp L + R ≤ 2 * Real.exp L - R := by linarith
  have hZc := RHTower.continuous_normSq_zetaMollified_line (σ := 1 / 2 + a / L) (by linarith) b y
  set Z : ℝ → ℝ := fun t => ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
    RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hZ
  have hZ0 : ∀ t, 0 ≤ Z t := fun t => by simp only [hZ]; positivity
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 *
    (n : ℝ) ^ (-2 * (1 / 2 + a / L)) with hDdef
  have hwin : ∀ τ ∈ Icc (Real.exp L + R) (2 * Real.exp L - R),
      Real.sqrt (Real.pi * H ^ 2 / 2) * (D - 3 * (δ / 6)) ≤
        ∫ t in (Real.exp L)..(2 * Real.exp L), Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) := by
    intro τ hτ
    have hτ1 : Real.exp L ≤ τ - R := by linarith [hτ.1]
    have hτ2 : τ + R ≤ 2 * Real.exp L := by linarith [hτ.2]
    have h1 := RHTower.gaussFloor_window hσ12 hσ1 (by omega : 1 ≤ M) hb hT4 hH0 hHM hR0.le hτ1 hτ2
      (hD₀1.trans hD_ge) (by positivity) (by linarith) hE1 hE2
    refine h1.trans ?_
    have hcont : Continuous fun t => Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) :=
      hZc.mul (by fun_prop)
    exact intervalIntegral.integral_mono_interval hτ1 (by linarith) hτ2
      (Filter.Eventually.of_forall fun t => mul_nonneg (hZ0 t) (Real.exp_pos _).le)
      (hcont.intervalIntegrable _ _)
  have hfub := RHTower.integral_ge_of_gaussian_windows hZc hZ0 hH0 hRT hR0.le hwin
  have hTR2 : 0 ≤ Real.exp L - 2 * R := by linarith
  have hRD : 2 * R * D₀ ≤ (δ / 16) * Real.exp L := by
    have h1 : 32 * R * D₀ ≤ δ * Real.exp L := by
      have hm := mul_le_mul_of_nonneg_right h2R (by linarith : (0 : ℝ) ≤ D₀)
      have heq : δ / D₀ * Real.exp L * D₀ = δ * Real.exp L := by
        have hD₀_ne : D₀ ≠ 0 := by linarith
        field_simp
      linarith
    linarith
  have halg : (D₀ - δ) * Real.exp L ≤ (Real.exp L - 2 * R) * (D - 3 * (δ / 6)) := by
    have hDsub : D₀ - δ / 2 ≤ D - 3 * (δ / 6) := by linarith
    calc (D₀ - δ) * Real.exp L
        ≤ (Real.exp L - 2 * R) * (D₀ - δ / 2) := by
          have : 0 ≤ R * δ := by positivity
          have : 0 ≤ δ * Real.exp L := by positivity
          nlinarith
      _ ≤ (Real.exp L - 2 * R) * (D - 3 * (δ / 6)) :=
          mul_le_mul_of_nonneg_left hDsub hTR2
  exact halg.trans hfub

theorem sum_Ioc_prime_inv_eq_mertensS_sub' {N M : ℕ} (h : N ≤ M) :
    ∑ p ∈ (Finset.Ioc N M).filter Nat.Prime, (1 / (p : ℝ)) =
      RHTower.Sieve.mertensS M - RHTower.Sieve.mertensS N := by
  unfold RHTower.Sieve.mertensS
  rw [Nat.primesLE_eq_filter_range, Nat.primesLE_eq_filter_range, eq_sub_iff_add_eq,
    ← Finset.sum_union]
  · congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨h1, hp⟩) <;> exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩
      by_cases hpN : p ≤ N
      · exact Or.inr ⟨by omega, hp⟩
      · exact Or.inl ⟨⟨by omega, by omega⟩, hp⟩
  · rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp hp'
    omega

/-- **Unmollified prime-log floor on and right of the critical line (`0 < θ < 1`, all `a ≥ 0`).**
At `a = 0` (`Re s = 1/2`), every normalized mollifier of length `y ≤ T^θ` has mean square at least
`(1 + log(1/θ) - ε) T`, strictly exceeding `T` for every `θ ∈ (0, 1)`. -/
theorem eventually_integral_normSq_zetaMollified_ge_one_add_log_inv_theta
    {a θ ε : ℝ} (ha : 0 ≤ a) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ T ^ θ → ∀ b : ℕ → ℂ, b 1 = 1 →
      (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
      (1 + Real.exp (-(2 * a)) * Real.log (1 / θ) - ε) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have ⟨δ, hδ_def⟩ : ∃ x : ℝ, x = min (1 / 2) (ε / 2) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; exact lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := by rw [hδ_def]; exact (min_le_left _ _).trans (by norm_num)
  have hδ_le_ε : δ ≤ ε / 2 := by rw [hδ_def]; exact min_le_right _ _
  have ⟨η, hη_def⟩ : ∃ x : ℝ, x = min ((1 - θ) / 2) (1 - Real.exp (-(δ / 4))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη_def]
    refine lt_min (by linarith) ?_
    have : Real.exp (-(δ / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hη_le1 : η ≤ (1 - θ) / 2 := by rw [hη_def]; exact min_le_left _ _
  have hη_le2 : η ≤ 1 - Real.exp (-(δ / 4)) := by rw [hη_def]; exact min_le_right _ _
  have ⟨θ₁, hθ₁_def⟩ : ∃ x : ℝ, x = 1 - η := ⟨_, rfl⟩
  have hθθ₁ : θ < θ₁ := by linarith
  have hθ₁0 : 0 < θ₁ := lt_trans hθ0 hθθ₁
  have hθ₁1 : θ₁ < 1 := by linarith
  have ⟨θ', hθ'_def⟩ : ∃ x : ℝ, x = θ₁ + (1 - θ₁) / 4 := ⟨_, rfl⟩
  have hθ'1 : θ' < 1 := by linarith
  have hθ'ge : Real.exp (-(δ / 4)) ≤ θ' := by linarith
  have hθ'pos : 0 < θ' := lt_of_lt_of_le (Real.exp_pos _) hθ'ge
  have hlog_θ' : Real.log (1 / θ) - δ / 4 ≤ Real.log (θ' / θ) := by
    have h1 : Real.exp (-(δ / 4)) / θ ≤ θ' / θ := div_le_div_of_nonneg_right hθ'ge hθ0.le
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (Real.exp_pos _).ne' hθ0.ne', Real.log_exp] at h2
    rw [one_div, Real.log_inv]
    linarith
  have ⟨D₀, hD₀_def⟩ : ∃ x : ℝ, x = 1 + Real.exp (-(2 * a)) * max 0 (Real.log (1 / θ) - δ / 2) :=
    ⟨_, rfl⟩
  have hD₀1 : 1 ≤ D₀ := by
    have : 0 ≤ Real.exp (-(2 * a)) * max 0 (Real.log (1 / θ) - δ / 2) := by positivity
    linarith
  have ⟨Cm, hCm_def⟩ : ∃ x : ℝ, x = 2 * RHTower.Sieve.mertensFirstConst + 1 / 2 := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm_def]; have := RHTower.Sieve.mertensFirstConst_nonneg; linarith
  have ⟨yStar, hyStar_def⟩ : ∃ n : ℕ, n = max 2 ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊ := ⟨_, rfl⟩
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - θ₁) / 2) (ε := δ / 600) (by norm_num) (by linarith) (by positivity)
  have ⟨S_yStar, hSy_def⟩ : ∃ x : ℝ, x = RHTower.Sieve.mertensS yStar +
      |RHTower.Sieve.meisselMertensConst| + Cm / Real.log 2 + Real.log (1 / θ) + 2 := ⟨_, rfl⟩
  have ⟨L₁, hL₁_def⟩ : ∃ x : ℝ, x = max (max (2 * a + 3) (32 / (1 - θ₁)))
      (max (128 / ((δ / D₀) * (1 - θ₁)))
        (max ((2 * Real.log 2 + Real.exp S_yStar) / θ') (32 * (Cm + 1) / (δ * θ')))) := ⟨_, rfl⟩
  filter_upwards [Real.tendsto_log_atTop.eventually ((eventually_ge_atTop L₁).and hsup),
    eventually_gt_atTop 1] with T hTL hT1
  obtain ⟨hLL₁, hsupL⟩ := hTL
  have hT0 : 0 < T := lt_trans zero_lt_one hT1
  have ⟨L, hL_def⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
  rw [← hL_def] at hLL₁ hsupL ⊢
  have hL₁_val : max (max (2 * a + 3) (32 / (1 - θ₁)))
      (max (128 / ((δ / D₀) * (1 - θ₁)))
        (max ((2 * Real.log 2 + Real.exp S_yStar) / θ') (32 * (Cm + 1) / (δ * θ')))) ≤ L := by
    rwa [← hL₁_def]
  have hLa : 2 * a + 3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL₁_val
  have hL32 : 32 / (1 - θ₁) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL₁_val
  have hLc : 128 / ((δ / D₀) * (1 - θ₁)) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₁_val
  have hLyS : (2 * Real.log 2 + Real.exp S_yStar) / θ' ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hL₁_val
  have hLCm : 32 * (Cm + 1) / (δ * θ') ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hL₁_val
  have hL0 : 0 < L := by linarith
  have hδ₁0 : 0 < 1 - θ₁ := by linarith
  have hδL8 : 8 ≤ (1 - θ₁) / 4 * L := by
    have := (div_le_iff₀ hδ₁0).mp hL32; linarith
  have hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L := by
    have hcpos : 0 < δ / D₀ := by positivity
    have h1 := (div_le_iff₀ (mul_pos hcpos hδ₁0)).mp hLc
    rw [div_le_iff₀ hcpos]; nlinarith
  have hsup' : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤
      δ / 6 := by linarith
  intro y hy hyle b hb1 hb
  have hyle_θ : (y : ℝ) ≤ Real.exp (θ * L) := by
    rw [mul_comm, Real.exp_mul, hL_def, Real.exp_log hT0]; exact hyle
  have hyle_θ₁ : (y : ℝ) ≤ Real.exp (θ₁ * L) :=
    hyle_θ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθθ₁.le hL0.le))
  have ⟨M, hM_def⟩ : ∃ n : ℕ, n = ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊ := ⟨_, rfl⟩
  have hM_def' : M = ⌊Real.exp (θ' * L)⌋₊ := by rw [hM_def, hθ'_def]
  have hMle : (M : ℝ) ≤ Real.exp (θ' * L) := by rw [hM_def']; exact Nat.floor_le (by positivity)
  have hMgt : Real.exp (θ' * L) - 1 < M := by
    rw [hM_def']; have := Nat.lt_floor_add_one (Real.exp (θ' * L)); linarith
  have hMle1 : (M : ℝ) ≤ Real.exp ((θ₁ + (1 - θ₁) / 4) * L) := by rwa [← hθ'_def]
  have hMgt1 : Real.exp ((θ₁ + (1 - θ₁) / 4) * L) - 1 < M := by rwa [← hθ'_def]
  obtain ⟨hM2, hyM, hMge, _, _⟩ :=
    RHTower.gaussFloor_scale hθ₁0 (by positivity : 0 < δ / D₀) hL0 hδL8 hδLc hyle_θ₁ hMle1 hMgt1
  have hMge' : Real.exp (θ' * L) / 2 ≤ (M : ℝ) := by rwa [hθ'_def]
  have hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
    have ⟨fterm, hfterm_def⟩ : ∃ f : ℕ → ℝ, f = fun n =>
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := ⟨_, rfl⟩
    have hfterm_app : ∀ n, fterm n =
        ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
      intro n; rw [hfterm_def]
    simp_rw [← hfterm_app]
    have hfterm0 : ∀ n ∈ Finset.Icc 1 M, 0 ≤ fterm n := fun n _ => by
      rw [hfterm_app]; positivity
    have h1val : fterm 1 = 1 := by
      rw [hfterm_app, RHTower.mollifiedZetaCoeff_one hy, hb1, norm_one]; simp
    by_cases hpos_target : Real.log (1 / θ) - δ / 2 ≤ 0
    · have hD₀_eq : D₀ = 1 := by rw [hD₀_def, max_eq_left hpos_target, mul_zero, add_zero]
      rw [hD₀_eq, ← h1val]
      exact Finset.single_le_sum hfterm0 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    · have hpos_t : 0 < Real.log (1 / θ) - δ / 2 := lt_of_not_ge hpos_target
      have hD₀_eq : D₀ = 1 + Real.exp (-(2 * a)) * (Real.log (1 / θ) - δ / 2) := by
        rw [hD₀_def, max_eq_right hpos_t.le]
      have ⟨Pset, hPset_def⟩ : ∃ s : Finset ℕ, s = (Finset.Ioc y M).filter Nat.Prime := ⟨_, rfl⟩
      have hsub_union : insert 1 Pset ⊆ Finset.Icc 1 M := by
        intro n hn
        rcases Finset.mem_insert.mp hn with rfl | hp
        · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
        · rw [hPset_def] at hp
          obtain ⟨hny, hnM⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
          exact Finset.mem_Icc.mpr ⟨by omega, hnM⟩
      have h1not : 1 ∉ Pset := by
        rw [hPset_def]
        exact fun h => Nat.not_prime_one (Finset.mem_filter.mp h).2
      have hsum_ge : 1 + Real.exp (-(2 * a)) * (∑ p ∈ Pset, (1 / (p : ℝ))) ≤
          ∑ n ∈ Finset.Icc 1 M, fterm n := by
        have hp_le : ∀ p ∈ Pset, Real.exp (-(2 * a)) * (1 / (p : ℝ)) ≤ fterm p := by
          intro p hp
          rw [hfterm_app]
          rw [hPset_def] at hp
          obtain ⟨hpIoc, hpp⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpy, hpM⟩ := Finset.mem_Ioc.mp hpIoc
          rw [RHTower.mollifiedZetaCoeff_prime hy hpp hpy, hb1, norm_one, one_pow, one_mul]
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hp_le_expL : (p : ℝ) ≤ Real.exp L :=
            (by exact_mod_cast hpM : (p : ℝ) ≤ M).trans
              (hMle.trans (Real.exp_le_exp.mpr (by nlinarith)))
          have hlogp : Real.log (p : ℝ) ≤ L := by
            have := Real.log_le_log hp0 hp_le_expL; rwa [Real.log_exp] at this
          rw [Real.rpow_def_of_pos hp0, one_div, ← Real.rpow_neg_one,
            Real.rpow_def_of_pos hp0, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hq : Real.log (p : ℝ) / L ≤ 1 := (div_le_one hL0).mpr hlogp
          have hexp_eq : Real.log (p : ℝ) * (-2 * (1 / 2 + a / L)) =
              -(2 * a * (Real.log (p : ℝ) / L)) + Real.log (p : ℝ) * (-1) := by
            field_simp; ring
          nlinarith
        have hsum_le := Finset.sum_le_sum hp_le
        calc 1 + Real.exp (-(2 * a)) * (∑ p ∈ Pset, (1 / (p : ℝ)))
            = fterm 1 + ∑ p ∈ Pset, (Real.exp (-(2 * a)) * (1 / (p : ℝ))) := by
              rw [h1val, Finset.mul_sum]
          _ ≤ fterm 1 + ∑ p ∈ Pset, fterm p := by linarith only [hsum_le]
          _ = ∑ n ∈ insert 1 Pset, fterm n := (Finset.sum_insert h1not).symm
          _ ≤ ∑ n ∈ Finset.Icc 1 M, fterm n :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_union fun n hn _ => hfterm0 n hn
      have hlogM_ge : θ' * L - Real.log 2 ≤ Real.log (M : ℝ) := by
        have := Real.log_le_log (by positivity) hMge'
        rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
      have hθ'L_ge : 2 * Real.log 2 + Real.exp S_yStar ≤ θ' * L := by
        have := (div_le_iff₀ hθ'pos).mp hLyS; linarith
      have hlogM_half : θ' * L / 2 ≤ Real.log (M : ℝ) := by
        have hS0 : 1 ≤ Real.exp S_yStar := by
          have : 0 ≤ RHTower.Sieve.mertensS yStar :=
            Finset.sum_nonneg fun _ _ => by positivity
          have : 0 ≤ |RHTower.Sieve.meisselMertensConst| := abs_nonneg _
          have : 0 ≤ Cm / Real.log 2 := by
            have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
          have hlogθ : 0 < Real.log (1 / θ) := by
            rw [one_div, Real.log_inv]; exact neg_pos.mpr (Real.log_neg hθ0 hθ1)
          exact Real.one_le_exp (by linarith [hSy_def])
        linarith
      have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
      have hLCm_mul : 32 * (Cm + 1) ≤ δ * θ' * L := by
        have := (div_le_iff₀ (mul_pos hδ hθ'pos)).mp hLCm; linarith
      have hP_ge : Real.log (1 / θ) - δ / 2 ≤ ∑ p ∈ Pset, (1 / (p : ℝ)) := by
        rw [hPset_def, sum_Ioc_prime_inv_eq_mertensS_sub' hyM]
        have hM_mert := (abs_le.mp (RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le hM2)).1
        unfold RHTower.Sieve.logLog at hM_mert
        rw [← hCm_def] at hM_mert
        by_cases hyS : y ≤ yStar
        · have hmert_mono : RHTower.Sieve.mertensS y ≤ RHTower.Sieve.mertensS yStar := by
            unfold RHTower.Sieve.mertensS
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
            obtain ⟨hpy, hpp⟩ := Nat.mem_primesLE.mp hp
            exact Nat.mem_primesLE.mpr ⟨hpy.trans hyS, hpp⟩
          have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          have hlogM_exp : Real.exp S_yStar ≤ Real.log (M : ℝ) := by
            linarith only [hlogM_ge, hθ'L_ge]
          have hlogLogM : S_yStar ≤ Real.log (Real.log (M : ℝ)) := by
            have := Real.log_le_log (Real.exp_pos _) hlogM_exp
            rwa [Real.log_exp] at this
          have hlog2_le : Real.log 2 ≤ Real.log (M : ℝ) :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hM2)
          have herrM : Cm / Real.log (M : ℝ) ≤ Cm / Real.log 2 :=
            div_le_div_of_nonneg_left hCm0 hlog2_pos hlog2_le
          have hMM := neg_abs_le RHTower.Sieve.meisselMertensConst
          linarith only [hM_mert, hmert_mono, hlogLogM, herrM, hMM, hSy_def, hδ]
        · have hyS' : yStar < y := lt_of_not_ge hyS
          have hy2 : 2 ≤ y := by
            have : 2 ≤ yStar := by rw [hyStar_def]; exact le_max_left _ _
            omega
          have hy_mert := (abs_le.mp (RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le hy2)).2
          unfold RHTower.Sieve.logLog at hy_mert
          rw [← hCm_def] at hy_mert
          have hy_ceil : ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊ < y := by
            have : ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊ ≤ yStar := by
              rw [hyStar_def]; exact le_max_right _ _
            omega
          have hy_exp : Real.exp (16 * (Cm + 1) / δ) < (y : ℝ) :=
            lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hy_ceil)
          have hlogy_big : 16 * (Cm + 1) / δ ≤ Real.log (y : ℝ) := by
            have := Real.log_le_log (Real.exp_pos _) hy_exp.le
            rwa [Real.log_exp] at this
          have hlogy_pos : 0 < Real.log (y : ℝ) :=
            lt_of_lt_of_le (by positivity) hlogy_big
          have herry : Cm / Real.log (y : ℝ) ≤ δ / 16 := by
            rw [div_le_iff₀ hlogy_pos]
            have h1 := (div_le_iff₀ hδ).mp hlogy_big
            linarith only [h1]
          have herrM : Cm / Real.log (M : ℝ) ≤ δ / 16 := by
            rw [div_le_iff₀ hlogM_pos]
            have h1 : δ * (θ' * L / 2) ≤ δ * Real.log (M : ℝ) :=
              mul_le_mul_of_nonneg_left hlogM_half hδ.le
            linarith only [hLCm_mul, h1, hδ]
          have hlogy_le : Real.log (y : ℝ) ≤ θ * L := by
            have := Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) hyle_θ
            rwa [Real.log_exp] at this
          have hlogM_ge_mul : (1 - δ / 16) * (θ' * L) ≤ Real.log (M : ℝ) := by
            have hlog2_le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
            have hcm_ge0 : 0 ≤ Cm := hCm0
            nlinarith only [hlogM_ge, hlog2_le, hLCm_mul, hcm_ge0]
          have h1sub_pos : 0 < 1 - δ / 16 := by linarith only [hδ1]
          have hquot : (1 - δ / 16) * (θ' / θ) ≤ Real.log (M : ℝ) / Real.log (y : ℝ) := by
            calc (1 - δ / 16) * (θ' / θ)
                = ((1 - δ / 16) * (θ' * L)) / (θ * L) := by field_simp
              _ ≤ Real.log (M : ℝ) / Real.log (y : ℝ) :=
                  div_le_div₀ (by positivity) hlogM_ge_mul hlogy_pos hlogy_le
          have hlog_quot : Real.log (1 - δ / 16) + Real.log (θ' / θ) ≤
              Real.log (Real.log (M : ℝ)) - Real.log (Real.log (y : ℝ)) := by
            rw [← Real.log_mul h1sub_pos.ne' (by positivity),
              ← Real.log_div hlogM_pos.ne' hlogy_pos.ne']
            exact Real.log_le_log (by positivity) hquot
          have hlog_1sub : -(δ / 8) ≤ Real.log (1 - δ / 16) := by
            have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (1 - δ / 16)⁻¹)
            rw [Real.log_inv] at h
            have hinv : (1 - δ / 16)⁻¹ - 1 ≤ δ / 8 := by
              rw [sub_le_iff_le_add, inv_eq_one_div, div_le_iff₀ h1sub_pos]
              nlinarith only [hδ, hδ1]
            linarith only [h, hinv]
          linarith only [hM_mert, hy_mert, herry, herrM, hlog_quot, hlog_1sub, hlog_θ', hδ]
      rw [hD₀_eq]
      have hmul_P := mul_le_mul_of_nonneg_left hP_ge (Real.exp_pos (-(2 * a))).le
      linarith only [hmul_P, hsum_ge]
  rw [hM_def] at hD_ge
  have hmain := gaussFloor_general_at_scale ha hθ₁0 hθ₁1 hD₀1 hδ hδ1 hLa hδL8 hδLc hsup' hy
    hyle_θ₁ hb hD_ge
  rw [hL_def, Real.exp_log hT0, ← hL_def] at hmain
  refine le_trans ?_ hmain
  refine mul_le_mul_of_nonneg_right ?_ hT0.le
  have hmax : Real.log (1 / θ) - δ / 2 ≤ max 0 (Real.log (1 / θ) - δ / 2) := le_max_right _ _
  have hexp_le1 : Real.exp (-(2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ha])
  have h1 : Real.exp (-(2 * a)) * (Real.log (1 / θ) - δ / 2) ≤
      Real.exp (-(2 * a)) * max 0 (Real.log (1 / θ) - δ / 2) :=
    mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
  have h2 : Real.exp (-(2 * a)) * (δ / 2) ≤ δ / 2 := by
    have := mul_le_mul_of_nonneg_right hexp_le1 (by positivity : 0 ≤ δ / 2)
    linarith only [this]
  linarith only [h1, h2, hD₀_def, hδ_le_ε, hε]

/-- **`y`-rough `1/θ` divergence floor on and right of the critical line (`0 < θ < 1`, all `a ≥ 0`).**
At `a = 0` (`Re s = 1/2`), every normalized mollifier of length `y ≤ T^θ` has mean square at least
`(roughMollifierConst / θ - ε) T`, diverging at rate `1/θ` as `θ → 0⁺`. -/
theorem eventually_integral_normSq_zetaMollified_ge_roughConst_div_theta
    {a θ ε : ℝ} (ha : 0 ≤ a) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ T ^ θ → ∀ b : ℕ → ℂ, b 1 = 1 →
      (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
      (roughMollifierConst * Real.exp (-(2 * a)) / θ - ε) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have ⟨cr, hcr_def⟩ : ∃ x : ℝ, x = roughMollifierConst := ⟨_, rfl⟩
  rw [← hcr_def]
  have hcr0 : 0 < cr := by rw [hcr_def]; exact roughMollifierConst_pos
  have ⟨δ, hδ_def⟩ : ∃ x : ℝ, x = min (1 / 2) (ε / 2) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; exact lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := by rw [hδ_def]; exact (min_le_left _ _).trans (by norm_num)
  have hδ_le_ε : δ ≤ ε / 2 := by rw [hδ_def]; exact min_le_right _ _
  have ⟨η, hη_def⟩ : ∃ x : ℝ, x = min ((1 - θ) / 2) (δ * θ / (2 * cr + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη_def]; exact lt_min (by linarith) (by positivity)
  have hη_le1 : η ≤ (1 - θ) / 2 := by rw [hη_def]; exact min_le_left _ _
  have hη_le2 : η ≤ δ * θ / (2 * cr + 1) := by rw [hη_def]; exact min_le_right _ _
  have ⟨θ₁, hθ₁_def⟩ : ∃ x : ℝ, x = 1 - η := ⟨_, rfl⟩
  have hθθ₁ : θ < θ₁ := by linarith
  have hθ₁0 : 0 < θ₁ := lt_trans hθ0 hθθ₁
  have hθ₁1 : θ₁ < 1 := by linarith
  have ⟨θ', hθ'_def⟩ : ∃ x : ℝ, x = θ₁ + (1 - θ₁) / 4 := ⟨_, rfl⟩
  have hθ'1 : θ' < 1 := by linarith
  have hθ'pos : 0 < θ' := by linarith
  have ⟨D₀, hD₀_def⟩ : ∃ x : ℝ, x = max 1 (cr * Real.exp (-(2 * a)) * θ' / θ) := ⟨_, rfl⟩
  have hD₀1 : 1 ≤ D₀ := by rw [hD₀_def]; exact le_max_left _ _
  have hD₀_ge_main : cr * Real.exp (-(2 * a)) * θ' / θ ≤ D₀ := by
    rw [hD₀_def]; exact le_max_right _ _
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - θ₁) / 2) (ε := δ / 600) (by norm_num) (by linarith) (by positivity)
  have ⟨L₁, hL₁_def⟩ : ∃ x : ℝ, x = max (max (2 * a + 3) (1 / θ))
      (max (32 / (1 - θ₁)) (128 / ((δ / D₀) * (1 - θ₁)))) := ⟨_, rfl⟩
  filter_upwards [Real.tendsto_log_atTop.eventually ((eventually_ge_atTop L₁).and hsup),
    eventually_gt_atTop 1] with T hTL hT1
  obtain ⟨hLL₁, hsupL⟩ := hTL
  have hT0 : 0 < T := lt_trans zero_lt_one hT1
  have ⟨L, hL_def⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
  rw [← hL_def] at hLL₁ hsupL ⊢
  have hL₁_val : max (max (2 * a + 3) (1 / θ))
      (max (32 / (1 - θ₁)) (128 / ((δ / D₀) * (1 - θ₁)))) ≤ L := by rwa [← hL₁_def]
  have hLa : 2 * a + 3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL₁_val
  have hLθ : 1 / θ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL₁_val
  have hL32 : 32 / (1 - θ₁) ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₁_val
  have hLc : 128 / ((δ / D₀) * (1 - θ₁)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL₁_val
  have hL0 : 0 < L := by linarith
  have hδ₁0 : 0 < 1 - θ₁ := by linarith
  have hδL8 : 8 ≤ (1 - θ₁) / 4 * L := by
    have := (div_le_iff₀ hδ₁0).mp hL32; linarith
  have hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L := by
    have hcpos : 0 < δ / D₀ := by positivity
    have h1 := (div_le_iff₀ (mul_pos hcpos hδ₁0)).mp hLc
    rw [div_le_iff₀ hcpos]; nlinarith
  have hsup' : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤
      δ / 6 := by linarith
  intro y hy hyle b hb1 hb
  have hyle_θ : (y : ℝ) ≤ Real.exp (θ * L) := by
    rw [mul_comm, Real.exp_mul, hL_def, Real.exp_log hT0]; exact hyle
  have hyle_θ₁ : (y : ℝ) ≤ Real.exp (θ₁ * L) :=
    hyle_θ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθθ₁.le hL0.le))
  have ⟨M, hM_def⟩ : ∃ n : ℕ, n = ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊ := ⟨_, rfl⟩
  have hM_def' : M = ⌊Real.exp (θ' * L)⌋₊ := by rw [hM_def, hθ'_def]
  have hMle : (M : ℝ) ≤ Real.exp (θ' * L) := by rw [hM_def']; exact Nat.floor_le (by positivity)
  have hMgt : Real.exp (θ' * L) - 1 < M := by
    rw [hM_def']; have := Nat.lt_floor_add_one (Real.exp (θ' * L)); linarith
  have hMle1 : (M : ℝ) ≤ Real.exp ((θ₁ + (1 - θ₁) / 4) * L) := by rwa [← hθ'_def]
  have hMgt1 : Real.exp ((θ₁ + (1 - θ₁) / 4) * L) - 1 < M := by rwa [← hθ'_def]
  obtain ⟨hM2, _, _, _, _⟩ :=
    RHTower.gaussFloor_scale hθ₁0 (by positivity : 0 < δ / D₀) hL0 hδL8 hδLc hyle_θ₁ hMle1 hMgt1
  have hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
    have ⟨fterm, hfterm_def⟩ : ∃ f : ℕ → ℝ, f = fun n =>
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := ⟨_, rfl⟩
    have hfterm_app : ∀ n, fterm n =
        ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
      intro n; rw [hfterm_def]
    simp_rw [← hfterm_app]
    have hfterm0 : ∀ n ∈ Finset.Icc 1 M, 0 ≤ fterm n := fun n _ => by
      rw [hfterm_app]; positivity
    rw [hD₀_def]
    refine max_le ?_ ?_
    · have h1val : fterm 1 = 1 := by
        rw [hfterm_app, RHTower.mollifiedZetaCoeff_one hy, hb1, norm_one]; simp
      rw [← h1val]
      exact Finset.single_le_sum hfterm0 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    · have ⟨V, hV_def⟩ : ∃ s : Finset ℕ, s = (Finset.Icc 1 M).image (roughPart y) := ⟨_, rfl⟩
      have hVsub : V ⊆ Finset.Icc 1 M := by
        intro v hv
        rw [hV_def] at hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
        exact Finset.mem_Icc.mpr ⟨roughPart_pos y hm1, (roughPart_le y hm1).trans hmM⟩
      have hV_term : ∀ v ∈ V, Real.exp (-(2 * a)) * (1 / (v : ℝ)) ≤ fterm v := by
        intro v hv
        rw [hfterm_app]
        rw [hV_def] at hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
        rw [mollifiedZetaCoeff_roughPart hy hb1 m, norm_one, one_pow, one_mul]
        have hv1 : 1 ≤ roughPart y m := roughPart_pos y hm1
        have hv0 : (0 : ℝ) < roughPart y m := by exact_mod_cast hv1
        have hv_expL : (roughPart y m : ℝ) ≤ Real.exp L :=
          (by exact_mod_cast (roughPart_le y hm1).trans hmM : (roughPart y m : ℝ) ≤ M).trans
            (hMle.trans (Real.exp_le_exp.mpr (by nlinarith only [hθ'1, hL0])))
        have hlogv : Real.log (roughPart y m : ℝ) ≤ L := by
          have := Real.log_le_log hv0 hv_expL; rwa [Real.log_exp] at this
        rw [Real.rpow_def_of_pos hv0, one_div, ← Real.rpow_neg_one,
          Real.rpow_def_of_pos hv0, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hq : Real.log (roughPart y m : ℝ) / L ≤ 1 := (div_le_one hL0).mpr hlogv
        have hexp_eq : Real.log (roughPart y m : ℝ) * (-2 * (1 / 2 + a / L)) =
            -(2 * a * (Real.log (roughPart y m : ℝ) / L)) + Real.log (roughPart y m : ℝ) * (-1) := by
          field_simp; ring
        have h2a : -(2 * a) ≤ -(2 * a * (Real.log (roughPart y m : ℝ) / L)) := by
          nlinarith only [ha, hq]
        linarith only [hexp_eq, h2a]
      have hθL1 : 1 ≤ θ * L := by
        have := (div_le_iff₀ hθ0).mp hLθ; linarith
      have hlogy : Real.log (y : ℝ) ≤ θ * L := by
        have := Real.log_le_log (by exact_mod_cast hy) hyle_θ; rwa [Real.log_exp] at this
      have hmert_ub := exp_one_add_mertensS_le_inv_roughMollifierConst hy hθL1 hlogy
      rw [← hcr_def] at hmert_ub
      have hlogM1 : θ' * L ≤ Real.log ((M : ℝ) + 1) := by
        have h1 : Real.exp (θ' * L) ≤ (M : ℝ) + 1 := by linarith
        have := Real.log_le_log (Real.exp_pos _) h1
        rwa [Real.log_exp] at this
      have hlogM1_nn : 0 ≤ Real.log ((M : ℝ) + 1) := by
        have : 0 ≤ θ' * L := by positivity
        linarith
      have hrough_ge : cr * θ' / θ ≤ ∑ v ∈ V, (1 / (v : ℝ)) := by
        rw [hV_def]
        have hbase := sum_inv_image_roughPart_ge y M
        have hdiv : cr * θ' / θ ≤
            Real.log ((M : ℝ) + 1) / Real.exp (1 + RHTower.Sieve.mertensS y) := by
          have h1 : cr * θ' / θ = (θ' * L) / (θ * L / cr) := by field_simp
          rw [h1]
          exact div_le_div₀ hlogM1_nn hlogM1 (Real.exp_pos _) hmert_ub
        exact hdiv.trans hbase
      calc cr * Real.exp (-(2 * a)) * θ' / θ
          = Real.exp (-(2 * a)) * (cr * θ' / θ) := by ring
        _ ≤ Real.exp (-(2 * a)) * ∑ v ∈ V, (1 / (v : ℝ)) :=
            mul_le_mul_of_nonneg_left hrough_ge (Real.exp_pos _).le
        _ = ∑ v ∈ V, (Real.exp (-(2 * a)) * (1 / (v : ℝ))) := Finset.mul_sum _ _ _
        _ ≤ ∑ v ∈ V, fterm v := Finset.sum_le_sum hV_term
        _ ≤ ∑ n ∈ Finset.Icc 1 M, fterm n :=
            Finset.sum_le_sum_of_subset_of_nonneg hVsub fun n hn _ => hfterm0 n hn
  rw [hM_def] at hD_ge
  have hmain := gaussFloor_general_at_scale ha hθ₁0 hθ₁1 hD₀1 hδ hδ1 hLa hδL8 hδLc hsup' hy
    hyle_θ₁ hb hD_ge
  rw [hL_def, Real.exp_log hT0, ← hL_def] at hmain
  refine le_trans ?_ hmain
  refine mul_le_mul_of_nonneg_right ?_ hT0.le
  have hexp_le1 : Real.exp (-(2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hloss : cr * Real.exp (-(2 * a)) * (1 - θ') / θ ≤ δ / 2 := by
    have h1θ' : 1 - θ' = 3 * η / 4 := by linarith
    rw [h1θ']
    have hexp_34 : Real.exp (-(2 * a)) * (3 * η / 4) ≤ η := by
      have := mul_le_mul_of_nonneg_right hexp_le1 (by positivity : 0 ≤ 3 * η / 4)
      linarith
    have h1 : cr * Real.exp (-(2 * a)) * (3 * η / 4) ≤ cr * η := by
      have := mul_le_mul_of_nonneg_left hexp_34 hcr0.le
      linarith
    calc cr * Real.exp (-(2 * a)) * (3 * η / 4) / θ
        ≤ cr * η / θ := div_le_div_of_nonneg_right h1 hθ0.le
      _ ≤ cr * (δ * θ / (2 * cr + 1)) / θ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hη_le2 hcr0.le) hθ0.le
      _ = cr * δ / (2 * cr + 1) := by field_simp
      _ ≤ δ / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [hcr0, hδ]
  have hdecomp : cr * Real.exp (-(2 * a)) / θ - cr * Real.exp (-(2 * a)) * θ' / θ =
      cr * Real.exp (-(2 * a)) * (1 - θ') / θ := by ring
  linarith

/-! ## §2. Unconditional vertical-flow credited-Jensen divergence -/

/-- Homogeneous degree-zero credited Jensen budget on `[T, 2T]` at `Re s = 1/2`:
`½ log(T⁻¹ ∫_T^{2T} ‖ζΨ(1/2 + it)‖² dt) - T⁻¹ ∫_T^{2T} log‖Ψ(1/2 + it)‖ dt`. -/
def flowCreditedJensenBudget (b : ℕ → ℂ) (y : ℕ) (T : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 / T) * ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) -
    (1 / T) * ∫ t in T..(2 * T),
      Real.log ‖RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖

/-- Möbius inversion identity recovering `b_d` (`1 ≤ d ≤ y`) from `mollifiedZetaCoeff b y`. -/
theorem eq_sum_divisors_moebius_mollifiedZetaCoeff (b : ℕ → ℂ) {y d : ℕ}
    (hd1 : 1 ≤ d) (hdy : d ≤ y) :
    b d = ∑ e ∈ d.divisors, ((μ (d / e) : ℤ) : ℂ) * RHTower.mollifiedZetaCoeff b y e := by
  classical
  have hce : ∀ e ∈ d.divisors, RHTower.mollifiedZetaCoeff b y e = ∑ k ∈ e.divisors, b k := by
    intro e he
    unfold RHTower.mollifiedZetaCoeff
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    have hed : e ∣ d := (Nat.mem_divisors.mp he).1
    have he_pos : 0 < e := Nat.pos_of_dvd_of_pos hed (by omega)
    have he0 : e ≠ 0 := by omega
    have he_le : e ≤ d := Nat.le_of_dvd (by omega) hed
    constructor
    · rintro ⟨_, hk⟩; exact ⟨hk, he0⟩
    · rintro ⟨hk, _⟩
      have hk1 : 1 ≤ k := Nat.pos_of_dvd_of_pos hk he_pos
      have hke : k ≤ e := Nat.le_of_dvd he_pos hk
      exact ⟨⟨hk1, (hke.trans he_le).trans hdy⟩, hk⟩
  have hce_sum : ∀ e ∈ d.divisors,
      ((μ (d / e) : ℤ) : ℂ) * RHTower.mollifiedZetaCoeff b y e =
        ∑ k ∈ e.divisors, ((μ (d / e) : ℤ) : ℂ) * b k := fun e he => by
    rw [hce e he, Finset.mul_sum]
  rw [Finset.sum_congr rfl hce_sum]
  have hexpand : ∀ e ∈ d.divisors,
      (∑ k ∈ e.divisors, ((μ (d / e) : ℤ) : ℂ) * b k) =
        ∑ k ∈ Finset.Icc 1 d, if k ∣ e then ((μ (d / e) : ℤ) : ℂ) * b k else 0 := by
    intro e he
    have hed : e ≤ d := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp he).1
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (by omega)
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hk, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hk he0, (Nat.le_of_dvd he0 hk).trans hed⟩, hk⟩
    · rintro ⟨_, hk⟩; exact ⟨hk, by omega⟩
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  have hinner : ∀ k ∈ Finset.Icc 1 d,
      (∑ e ∈ d.divisors, if k ∣ e then ((μ (d / e) : ℤ) : ℂ) * b k else 0) =
        if k = d then b d else 0 := by
    intro k hk
    obtain ⟨hk1, hkd⟩ := Finset.mem_Icc.mp hk
    by_cases hkdvd : k ∣ d
    · obtain ⟨m, rfl⟩ := hkdvd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm; · simp at hd1
        · omega
      rw [← Finset.sum_filter]
      have hbij : (k * m).divisors.filter (fun e => k ∣ e) =
          m.divisors.image (fun r => k * r) := by
        ext e
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
        constructor
        · rintro ⟨⟨hekm, _⟩, ⟨r, rfl⟩⟩
          exact ⟨r, ⟨(mul_dvd_mul_iff_left (by omega : k ≠ 0)).mp hekm, by omega⟩, rfl⟩
        · rintro ⟨r, ⟨hrm, _⟩, rfl⟩
          exact ⟨⟨mul_dvd_mul_left k hrm, by omega⟩, ⟨r, rfl⟩⟩
      rw [hbij, Finset.sum_image (fun r₁ _ r₂ _ h => mul_left_cancel₀ (by omega) h)]
      have hdiv : ∀ r ∈ m.divisors, (k * m) / (k * r) = m / r := fun r _ =>
        Nat.mul_div_mul_left m r (by omega)
      have hsum_m : (∑ r ∈ m.divisors, ((μ ((k * m) / (k * r)) : ℤ) : ℂ) * b k) =
          (∑ r ∈ m.divisors, ((μ r : ℤ) : ℂ)) * b k := by
        rw [Finset.sum_mul]
        refine (Finset.sum_congr rfl fun r hr => by rw [hdiv r hr]).trans ?_
        have hm0 : m ≠ 0 := by omega
        exact Finset.sum_nbij' (fun r => m / r) (fun r => m / r)
          (fun r hr => Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hr).1, hm0⟩)
          (fun r hr => Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hr).1, hm0⟩)
          (fun r hr => Nat.div_div_self (Nat.mem_divisors.mp hr).1 hm0)
          (fun r hr => Nat.div_div_self (Nat.mem_divisors.mp hr).1 hm0)
          (fun _ _ => rfl)
      rw [hsum_m, RHTower.Sieve.sum_moebius_divisors_complex]
      by_cases hm_eq : m = 1
      · subst hm_eq; simp
      · have hne : k ≠ k * m := by
          intro h; apply hm_eq
          have := mul_left_cancel₀ (by omega : k ≠ 0) (by linarith : k * 1 = k * m)
          omega
        rw [if_neg hm_eq, if_neg hne, zero_mul]
    · have hzero : ∀ e ∈ d.divisors, (if k ∣ e then ((μ (d / e) : ℤ) : ℂ) * b k else 0) = 0 := by
        intro e he
        rw [if_neg]
        intro hke
        exact hkdvd (dvd_trans hke (Nat.mem_divisors.mp he).1)
      rw [Finset.sum_eq_zero hzero, if_neg]
      rintro rfl
      exact hkdvd dvd_rfl
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq', if_pos (Finset.mem_Icc.mpr ⟨hd1, le_rfl⟩)]

/-- Every nonzero coefficient vector `(b_1, ..., b_y)` produces an index `e ∈ [1, y]` with
`‖b d‖ ≤ y · ‖c_e‖` for all `d ∈ [1, y]`. -/
theorem exists_mollifiedZetaCoeff_ge_div {b : ℕ → ℂ} {y : ℕ} (hy : 1 ≤ y)
    (hne : ∃ d ∈ Finset.Icc 1 y, b d ≠ 0) :
    ∃ e ∈ Finset.Icc 1 y, 0 < ‖RHTower.mollifiedZetaCoeff b y e‖ ∧
      ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ (y : ℝ) * ‖RHTower.mollifiedZetaCoeff b y e‖ := by
  classical
  have hnonempty : (Finset.Icc 1 y).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hy⟩⟩
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 y)
    (fun n => ‖RHTower.mollifiedZetaCoeff b y n‖) hnonempty
  have hbd : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ (y : ℝ) * ‖RHTower.mollifiedZetaCoeff b y e‖ := by
    intro d hd
    obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
    rw [eq_sum_divisors_moebius_mollifiedZetaCoeff b hd1 hdy]
    have hdiv_sub : d.divisors ⊆ Finset.Icc 1 y := by
      intro k hk
      have hkd := (Nat.mem_divisors.mp hk).1
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hkd (by omega),
        (Nat.le_of_dvd (by omega) hkd).trans hdy⟩
    calc ‖∑ k ∈ d.divisors, ((μ (d / k) : ℤ) : ℂ) * RHTower.mollifiedZetaCoeff b y k‖
        ≤ ∑ k ∈ d.divisors, ‖((μ (d / k) : ℤ) : ℂ) * RHTower.mollifiedZetaCoeff b y k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k ∈ d.divisors, ‖RHTower.mollifiedZetaCoeff b y e‖ := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul]
          have h1 := RHTower.Sieve.norm_moebius_complex_le_one (d / k)
          have h2 := hmax k (hdiv_sub hk)
          exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans h2
      _ = (d.divisors.card : ℝ) * ‖RHTower.mollifiedZetaCoeff b y e‖ := by simp
      _ ≤ (y : ℝ) * ‖RHTower.mollifiedZetaCoeff b y e‖ := by
          have hcard : d.divisors.card ≤ y :=
            (Finset.card_le_card hdiv_sub).trans (by simp)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg _)
  obtain ⟨d₀, hd₀, hbd₀⟩ := hne
  have hpos : 0 < ‖RHTower.mollifiedZetaCoeff b y e‖ := by
    by_contra hle
    have hle' : ‖RHTower.mollifiedZetaCoeff b y e‖ ≤ 0 := not_lt.mp hle
    have h0 : ‖RHTower.mollifiedZetaCoeff b y e‖ = 0 := le_antisymm hle' (norm_nonneg _)
    have := hbd d₀ hd₀
    rw [h0, mul_zero, norm_le_zero_iff] at this
    exact hbd₀ this
  exact ⟨e, he, hpos, hbd⟩

/-- Every nonzero Dirichlet polynomial `∑_{d=1}^y b_d d^{-s}` evaluates to a nonzero complex number
at sufficiently large real arguments. -/
theorem exists_edPoly_ne_zero_of_exists_coeff_ne_zero {b : ℕ → ℂ} {y : ℕ}
    (hne : ∃ d ∈ Finset.Icc 1 y, b d ≠ 0) :
    ∃ z : ℂ, RHTower.edPoly b (Finset.Icc 1 y) z ≠ 0 := by
  classical
  let S := (Finset.Icc 1 y).filter (fun d => b d ≠ 0)
  obtain ⟨d_wit, hd_wit, hbd_wit⟩ := hne
  have hS_ne : S.Nonempty := ⟨d_wit, Finset.mem_filter.mpr ⟨hd_wit, hbd_wit⟩⟩
  let d₀ := S.min' hS_ne
  have hd₀_mem : d₀ ∈ S := Finset.min'_mem S hS_ne
  have hd₀_Icc : d₀ ∈ Finset.Icc 1 y := (Finset.mem_filter.mp hd₀_mem).1
  have hbd₀ : b d₀ ≠ 0 := (Finset.mem_filter.mp hd₀_mem).2
  have hd₀1 : 1 ≤ d₀ := (Finset.mem_Icc.mp hd₀_Icc).1
  have ⟨Bsum, hBsum_def⟩ : ∃ x : ℝ, x = ∑ d ∈ Finset.Icc 1 y, ‖b d‖ := ⟨_, rfl⟩
  have hBsum0 : 0 ≤ Bsum := by rw [hBsum_def]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ⟨K, hK_def⟩ : ∃ x : ℝ, x = 2 * Bsum / ‖b d₀‖ + 2 := ⟨_, rfl⟩
  have hK1 : 1 < K := by
    rw [hK_def]
    have : 0 ≤ 2 * Bsum / ‖b d₀‖ := div_nonneg (by positivity) (norm_nonneg _)
    linarith
  have hratio : 1 < ((d₀ : ℝ) + 1) / (d₀ : ℝ) := by
    have hd₀_pos : (0 : ℝ) < d₀ := by exact_mod_cast hd₀1
    rw [one_lt_div hd₀_pos]; linarith
  have ⟨σ, hσ_def⟩ : ∃ x : ℝ, x = Real.log K / Real.log (((d₀ : ℝ) + 1) / (d₀ : ℝ)) := ⟨_, rfl⟩
  refine ⟨(σ : ℂ), ?_⟩
  intro hzero
  have hmul : (((d₀ : ℝ) ^ σ : ℝ) : ℂ) * RHTower.edPoly b (Finset.Icc 1 y) (σ : ℂ) = 0 := by
    rw [hzero, mul_zero]
  unfold RHTower.edPoly at hmul
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hd₀_Icc] at hmul
  have hd₀_pos : (0 : ℝ) < d₀ := by exact_mod_cast hd₀1
  have hhead : (((d₀ : ℝ) ^ σ : ℝ) : ℂ) * (b d₀ * ((d₀ : ℝ) : ℂ) ^ (-(σ : ℂ))) = b d₀ := by
    rw [RHTower.ofReal_natCast_cpow_eq_exp hd₀1, Real.rpow_def_of_pos hd₀_pos,
      Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    have : ((Real.log (d₀ : ℝ) * σ : ℝ) : ℂ) + (Real.log (d₀ : ℝ) : ℂ) * -(σ : ℂ) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, mul_one]
  rw [hhead] at hmul
  have htail_norm : ‖∑ d ∈ (Finset.Icc 1 y).erase d₀,
      (((d₀ : ℝ) ^ σ : ℝ) : ℂ) * (b d * ((d : ℝ) : ℂ) ^ (-(σ : ℂ)))‖ ≤ Bsum / K := by
    calc ‖∑ d ∈ (Finset.Icc 1 y).erase d₀,
          (((d₀ : ℝ) ^ σ : ℝ) : ℂ) * (b d * ((d : ℝ) : ℂ) ^ (-(σ : ℂ)))‖
        ≤ ∑ d ∈ (Finset.Icc 1 y).erase d₀,
          ‖(((d₀ : ℝ) ^ σ : ℝ) : ℂ) * (b d * ((d : ℝ) : ℂ) ^ (-(σ : ℂ)))‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ (Finset.Icc 1 y).erase d₀, ‖b d‖ * (1 / K) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd_ne : d ≠ d₀ := (Finset.mem_erase.mp hd).1
          have hd_Icc : d ∈ Finset.Icc 1 y := (Finset.mem_erase.mp hd).2
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd_Icc).1
          by_cases hbd0 : b d = 0
          · simp [hbd0]
          · have hd_S : d ∈ S := Finset.mem_filter.mpr ⟨hd_Icc, hbd0⟩
            have hd₀_lt : d₀ < d := lt_of_le_of_ne (Finset.min'_le S d hd_S) hd_ne.symm
            have hd_ge : (d₀ : ℝ) + 1 ≤ d := by exact_mod_cast hd₀_lt
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.rpow_nonneg hd₀_pos.le _),
              RHTower.norm_ofReal_natCast_cpow hd1, Complex.neg_re, Complex.ofReal_re]
            have hrpow_eq : (d₀ : ℝ) ^ σ * (d : ℝ) ^ (-σ) = ((d : ℝ) / (d₀ : ℝ)) ^ (-σ) := by
              rw [Real.div_rpow (by positivity) hd₀_pos.le, Real.rpow_neg hd₀_pos.le,
                div_eq_mul_inv, inv_inv, mul_comm]
            have hσ0 : 0 < σ := by
              rw [hσ_def]; exact div_pos (Real.log_pos hK1) (Real.log_pos hratio)
            have hbase_le : ((d : ℝ) / (d₀ : ℝ)) ^ (-σ) ≤ 1 / K := by
              have h1 : (((d₀ : ℝ) + 1) / (d₀ : ℝ)) ^ (-σ) = 1 / K := by
                rw [Real.rpow_def_of_pos (by linarith), show Real.log (((d₀ : ℝ) + 1) / d₀) * (-σ) =
                  -Real.log K by rw [hσ_def]; have := (Real.log_pos hratio).ne'; field_simp,
                  Real.exp_neg, Real.exp_log (by linarith), one_div]
              rw [← h1]
              exact Real.rpow_le_rpow_of_nonpos (by linarith)
                (div_le_div_of_nonneg_right hd_ge hd₀_pos.le) (by linarith)
            calc (d₀ : ℝ) ^ σ * (‖b d‖ * (d : ℝ) ^ (-σ))
                = ‖b d‖ * ((d₀ : ℝ) ^ σ * (d : ℝ) ^ (-σ)) := by ring
              _ = ‖b d‖ * ((d : ℝ) / (d₀ : ℝ)) ^ (-σ) := by rw [hrpow_eq]
              _ ≤ ‖b d‖ * (1 / K) := mul_le_mul_of_nonneg_left hbase_le (norm_nonneg _)
      _ ≤ (∑ d ∈ Finset.Icc 1 y, ‖b d‖) * (1 / K) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun _ _ _ => norm_nonneg _) (by positivity)
      _ = Bsum / K := by rw [← hBsum_def]; ring
  have hbd₀_eq : b d₀ = -∑ d ∈ (Finset.Icc 1 y).erase d₀,
      (((d₀ : ℝ) ^ σ : ℝ) : ℂ) * (b d * ((d : ℝ) : ℂ) ^ (-(σ : ℂ))) :=
    eq_neg_of_add_eq_zero_left hmul
  have hnorm_eq : ‖b d₀‖ ≤ Bsum / K := by rw [hbd₀_eq, norm_neg]; exact htail_norm
  have hbd₀_pos : 0 < ‖b d₀‖ := norm_pos_iff.mpr hbd₀
  have hK_pos : 0 < K := by linarith
  have hcontra : ‖b d₀‖ * K ≤ Bsum := (le_div_iff₀ hK_pos).mp hnorm_eq
  have hK_mul : ‖b d₀‖ * K = 2 * Bsum + 2 * ‖b d₀‖ := by
    rw [hK_def]; field_simp
  linarith

theorem intervalIntegrable_log_norm_edPoly_criticalLine (b : ℕ → ℂ) (y : ℕ) (T₁ T₂ : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => Real.log ‖RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      volume T₁ T₂ := by
  have hs : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have han : AnalyticOnNhd ℂ (RHTower.edPoly b (Finset.Icc 1 y)) Set.univ :=
    RHTower.analyticOnNhd_edPoly b hs
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t _
  have hline : AnalyticAt ℝ (fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact AnalyticAt.comp (f := fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)
    (han _ (Set.mem_univ _)).restrictScalars hline |>.meromorphicAt

/-- Exact scale invariance `flowCreditedJensenBudget (λ • b) y T = flowCreditedJensenBudget b y T`
for every positive scalar `λ > 0` and every nonzero Dirichlet polynomial `b` whenever the mean
square on `[T, 2T]` is positive. -/
theorem flowCreditedJensenBudget_smul {b : ℕ → ℂ} {y : ℕ} {T lam : ℝ}
    (hT : 0 < T) (hlam : 0 < lam)
    (hne : ∃ d ∈ Finset.Icc 1 y, b d ≠ 0)
    (hmsq : 0 < ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) :
    flowCreditedJensenBudget (fun d => (lam : ℂ) * b d) y T = flowCreditedJensenBudget b y T := by
  unfold flowCreditedJensenBudget
  have hed : ∀ s : ℂ, RHTower.edPoly (fun d => (lam : ℂ) * b d) (Finset.Icc 1 y) s =
      (lam : ℂ) * RHTower.edPoly b (Finset.Icc 1 y) s := by
    intro s; unfold RHTower.edPoly; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  have hsq : (∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly (fun d => (lam : ℂ) * b d) (Finset.Icc 1 y)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      lam ^ 2 * ∫ t in T..(2 * T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hed, mul_left_comm _ (lam : ℂ) _, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hlam, mul_pow]
  have hs : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have han : AnalyticOnNhd ℂ (RHTower.edPoly b (Finset.Icc 1 y)) Set.univ :=
    RHTower.analyticOnNhd_edPoly b hs
  obtain ⟨z₀, hz₀⟩ := exists_edPoly_ne_zero_of_exists_coeff_ne_zero hne
  have hcod : (RHTower.edPoly b (Finset.Icc 1 y) ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    han.preimage_zero_mem_codiscreteWithin (x := z₀) hz₀ (Set.mem_univ z₀) isConnected_univ
  have hRect_fin : {z ∈ (uIcc (1 / 2 : ℝ) (1 / 2 : ℝ) ×ℂ uIcc T (2 * T)) |
      RHTower.edPoly b (Finset.Icc 1 y) z = 0}.Finite := by
    have hcodR := Filter.codiscreteWithin_mono
      (Set.subset_univ (uIcc (1 / 2 : ℝ) (1 / 2 : ℝ) ×ℂ uIcc T (2 * T))) hcod
    refine ((isCompact_uIcc.reProdIm isCompact_uIcc).finite_sdiff_of_mem_codiscreteWithin
      hcodR).subset fun z hz => ⟨hz.1, by simp [hz.2]⟩
  let Zt : Set ℝ := {t ∈ uIcc T (2 * T) |
    RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 0}
  have hpre : ((fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ⁻¹'
      {z ∈ (uIcc (1 / 2 : ℝ) (1 / 2 : ℝ) ×ℂ uIcc T (2 * T)) |
        RHTower.edPoly b (Finset.Icc 1 y) z = 0}).Finite :=
    hRect_fin.preimage fun t₁ _ t₂ _ h => by
      have := congrArg Complex.im h; simpa using this
  have hZt_fin : Zt.Finite :=
    hpre.subset fun t ht =>
      ⟨Complex.mem_reProdIm.mpr ⟨by simp, by simpa using ht.1⟩, ht.2⟩
  have hae : ∀ᵐ t ∂volume, t ∈ uIoc T (2 * T) →
      Real.log ‖RHTower.edPoly (fun d => (lam : ℂ) * b d) (Finset.Icc 1 y)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ =
        Real.log lam +
          Real.log ‖RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    have hmeas0 : volume Zt = 0 := hZt_fin.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hmeas0] with t htnot htI
    have hnz : RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
      fun h0 => htnot ⟨uIoc_subset_uIcc htI, h0⟩
    rw [hed, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam,
      Real.log_mul hlam.ne' (norm_ne_zero_iff.mpr hnz)]
  have hlog_int : (∫ t in T..(2 * T),
      Real.log ‖RHTower.edPoly (fun d => (lam : ℂ) * b d) (Finset.Icc 1 y)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) =
      T * Real.log lam + ∫ t in T..(2 * T),
        Real.log ‖RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    rw [intervalIntegral.integral_congr_ae hae,
      intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegrable_log_norm_edPoly_criticalLine b y T (2 * T)),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hsq, hlog_int]
  have ⟨Imsq, hImsq⟩ : ∃ x : ℝ, x = ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := ⟨_, rfl⟩
  have ⟨Ilog, hIlog⟩ : ∃ x : ℝ, x = ∫ t in T..(2 * T),
      Real.log ‖RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := ⟨_, rfl⟩
  rw [← hImsq, ← hIlog]
  rw [← hImsq] at hmsq
  have h1 : (1 / T) * (lam ^ 2 * Imsq) = lam ^ 2 * ((1 / T) * Imsq) := by ring
  rw [h1, Real.log_mul (pow_ne_zero 2 hlam.ne') (by positivity), Real.log_pow]
  push_cast
  have h2 : (1 / T) * (T * Real.log lam + Ilog) = Real.log lam + (1 / T) * Ilog := by
    field_simp [hT.ne']
  rw [h2]
  ring

/-- **Unconditional divergence of the vertical-flow credited Jensen budget.**
Uniformly over all `1 ≤ y ≤ (log T)^{1/8}` and all nonzero coefficient vectors
`(b_1, ..., b_y) ∈ ℂ^y \ {0}` (arbitrary complex coefficients, arbitrary right-half zeros),
`flowCreditedJensenBudget b y T → +∞` as `T → +∞`. -/
theorem eventually_flowCreditedJensenBudget_ge (A : ℝ) :
    ∀ᶠ T in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ (Real.log T) ^ (1 / 8 : ℝ) →
      ∀ b : ℕ → ℂ, (∃ d ∈ Finset.Icc 1 y, b d ≠ 0) →
        A ≤ flowCreditedJensenBudget b y T := by
  have ⟨cr, hcr_def⟩ : ∃ x : ℝ, x = roughMollifierConst := ⟨_, rfl⟩
  have hcr0 : 0 < cr := by rw [hcr_def]; exact roughMollifierConst_pos
  have ⟨E, hE_def⟩ : ∃ x : ℝ, x = Real.exp (2 * max 0 A + 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE_def]; exact Real.exp_pos _
  have hE_ge1 : 1 ≤ E := by
    rw [hE_def]; exact Real.one_le_exp (by have := le_max_left 0 A; linarith)
  have ⟨K, hK_def⟩ : ∃ x : ℝ, x = max 4 (max (4 * E / cr) (1024 * E)) := ⟨_, rfl⟩
  have hK4 : 4 ≤ K := by rw [hK_def]; exact le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hK_cr : 4 * E / cr ≤ K := by
    rw [hK_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK_1024 : 1024 * E ≤ K := by
    rw [hK_def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - (1 / 2 : ℝ)) / 2) (ε := (1 / 2 : ℝ) / 600) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [
    Real.tendsto_log_atTop.eventually ((eventually_ge_atTop (max 256 (K ^ 8))).and hsup),
    eventually_gt_atTop 1] with T hTL hT1
  obtain ⟨hLmax, hsupL⟩ := hTL
  have hT0 : 0 < T := lt_trans zero_lt_one hT1
  have ⟨L, hL_def⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
  rw [← hL_def] at hLmax hsupL
  have hL256 : 256 ≤ L := le_trans (le_max_left _ _) hLmax
  have hLK8 : K ^ 8 ≤ L := le_trans (le_max_right _ _) hLmax
  have hL0 : 0 < L := by linarith
  have ⟨u, hu_def⟩ : ∃ x : ℝ, x = L ^ (1 / 8 : ℝ) := ⟨_, rfl⟩
  have hu_pos : 0 < u := by rw [hu_def]; exact Real.rpow_pos_of_pos hL0 _
  have hu8 : u ^ 8 = L := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
  have hK_le_u : K ≤ u := by
    rw [hu_def]
    have h1 : (K ^ (8 : ℕ)) ^ (1 / 8 : ℝ) ≤ L ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hLK8 (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hK0.le,
      show ((8 : ℕ) : ℝ) * (1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one] at h1
  have hu4 : 4 ≤ u := le_trans hK4 hK_le_u
  have hu1 : 1 ≤ u := by linarith
  intro y hy hyle_u b hne
  rw [← hL_def, ← hu_def] at hyle_u
  classical
  have hIcc_ne : (Finset.Icc 1 y).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hy⟩⟩
  obtain ⟨d_max, hd_max, hmax_b⟩ :=
    Finset.exists_max_image (Finset.Icc 1 y) (fun d => ‖b d‖) hIcc_ne
  obtain ⟨d_nz, hd_nz, hbd_nz⟩ := hne
  have hΛpos : 0 < ‖b d_max‖ := lt_of_lt_of_le (norm_pos_iff.mpr hbd_nz) (hmax_b d_nz hd_nz)
  have ⟨lam, hlam_def⟩ : ∃ x : ℝ, x = 1 / ‖b d_max‖ := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam_def]; exact one_div_pos.mpr hΛpos
  let b' : ℕ → ℂ := fun d => (lam : ℂ) * b d
  have hb'_le1 : ∀ d ∈ Finset.Icc 1 y, ‖b' d‖ ≤ 1 := by
    intro d hd
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
    rw [hlam_def, one_div, inv_mul_le_iff₀ hΛpos, mul_one]
    exact hmax_b d hd
  have hb'_dmax : ‖b' d_max‖ = 1 := by
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
    rw [hlam_def]; field_simp
  have hb'_ne : ∃ d ∈ Finset.Icc 1 y, b' d ≠ 0 :=
    ⟨d_max, hd_max, fun h => by rw [h, norm_zero] at hb'_dmax; norm_num at hb'_dmax⟩
  obtain ⟨e, he, _, hce_bd⟩ := exists_mollifiedZetaCoeff_ge_div hy hb'_ne
  obtain ⟨he1, hey⟩ := Finset.mem_Icc.mp he
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hce_ge : 1 / (y : ℝ) ≤ ‖RHTower.mollifiedZetaCoeff b' y e‖ := by
    have h1 := hce_bd d_max hd_max
    rw [hb'_dmax] at h1
    rwa [div_le_iff₀ hy0, mul_comm]
  have hu_le_L8 : u ≤ L / 8 := by
    have hpow : (4 : ℝ) ^ 7 ≤ u ^ 7 := pow_le_pow_left₀ (by norm_num) hu4 7
    have hmul : 8 * u ≤ u ^ 7 * u := by
      have : (8 : ℝ) ≤ (4 : ℝ) ^ 7 := by norm_num
      have h8u7 : (8 : ℝ) ≤ u ^ 7 := this.trans hpow
      exact mul_le_mul_of_nonneg_right h8u7 hu_pos.le
    have : u ^ 7 * u = u ^ 8 := by ring
    linarith
  have hy_le_expL8 : (y : ℝ) ≤ Real.exp (L / 8) :=
    hyle_u.trans (hu_le_L8.trans ((by linarith : L / 8 ≤ L / 8 + 1).trans (Real.add_one_le_exp _)))
  have hyle_half : (y : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * L) :=
    hy_le_expL8.trans (Real.exp_le_exp.mpr (by linarith))
  have ⟨M, hM_def⟩ : ∃ n : ℕ, n = ⌊Real.exp (((1 / 2 : ℝ) + (1 - (1 / 2 : ℝ)) / 4) * L)⌋₊ :=
    ⟨_, rfl⟩
  have ⟨M₂, hM₂_def⟩ : ∃ n : ℕ, n = ⌊Real.exp (L / 2)⌋₊ := ⟨_, rfl⟩
  have hyM₂_le_M : y * M₂ ≤ M := by
    rw [hM_def]
    apply Nat.le_floor
    push_cast
    have hM₂_le : (M₂ : ℝ) ≤ Real.exp (L / 2) := by rw [hM₂_def]; exact Nat.floor_le (by positivity)
    calc (y : ℝ) * (M₂ : ℝ)
        ≤ Real.exp (L / 8) * Real.exp (L / 2) :=
          mul_le_mul hy_le_expL8 hM₂_le (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (((1 / 2 : ℝ) + (1 - (1 / 2 : ℝ)) / 4) * L) := by
          rw [← Real.exp_add]; congr 1; ring
  have ⟨D₀, hD₀_def⟩ : ∃ x : ℝ, x = 2 * (y : ℝ) ^ 2 * E := ⟨_, rfl⟩
  have hy2_ge1 : 1 ≤ (y : ℝ) ^ 2 := one_le_pow₀ hy1
  have hy2E_ge1 : 1 ≤ (y : ℝ) ^ 2 * E := one_le_mul_of_one_le_of_one_le hy2_ge1 hE_ge1
  have hD₀1 : 1 ≤ D₀ := by linarith
  have hD₀_le_u2 : D₀ ≤ 2 * E * u ^ 2 := by
    have hy2 : (y : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hyle_u 2
    have h := mul_le_mul_of_nonneg_left hy2 (by positivity : 0 ≤ 2 * E)
    linarith [hD₀_def, show 2 * E * (y : ℝ) ^ 2 = 2 * (y : ℝ) ^ 2 * E by ring]
  have hδLc : 32 / ((1 / 2 : ℝ) / D₀) ≤ (1 - (1 / 2 : ℝ)) / 4 * L := by
    have h1024 : 1024 * E ≤ u := hK_1024.trans hK_le_u
    have hu_le_u6 : u ≤ u ^ 6 := by
      have h1 : 1 ≤ u ^ 5 := one_le_pow₀ hu1
      have h2 := mul_le_mul_of_nonneg_left h1 hu_pos.le
      linarith [show u * 1 = u by ring, show u * u ^ 5 = u ^ 6 by ring]
    have h64 : 32 / ((1 / 2 : ℝ) / D₀) = 64 * D₀ := by field_simp; ring
    rw [h64, ← hu8]
    have hstep := mul_le_mul_of_nonneg_right (h1024.trans hu_le_u6) (sq_nonneg u)
    have hmul : (1024 * E) * u ^ 2 = 512 * (2 * E * u ^ 2) := by ring
    have hu62 : u ^ 6 * u ^ 2 = u ^ 8 := by ring
    linarith
  have hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b' y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + (0 : ℝ) / L)) := by
    let fterm : ℕ → ℝ := fun n =>
      ‖RHTower.mollifiedZetaCoeff b' y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + (0 : ℝ) / L))
    change D₀ ≤ ∑ n ∈ Finset.Icc 1 M, fterm n
    have hfterm0 : ∀ n ∈ Finset.Icc 1 M, 0 ≤ fterm n := fun n _ => by dsimp [fterm]; positivity
    let V₂ := (Finset.Icc 1 M₂).image (roughPart y)
    have hinj : Set.InjOn (fun v => e * v) V₂ := fun v₁ _ v₂ _ h =>
      mul_left_cancel₀ (by omega : e ≠ 0) h
    have hsub : V₂.image (fun v => e * v) ⊆ Finset.Icc 1 M := by
      intro n hn
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hm1, hmM₂⟩ := Finset.mem_Icc.mp hm
      have hv1 : 1 ≤ roughPart y m := roughPart_pos y hm1
      have hvM₂ : roughPart y m ≤ M₂ := (roughPart_le y hm1).trans hmM₂
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) (by omega),
        (Nat.mul_le_mul hey hvM₂).trans hyM₂_le_M⟩
    have hterm : ∀ v ∈ V₂, (1 / (y : ℝ) ^ 3) * (1 / (v : ℝ)) ≤ fterm (e * v) := by
      intro v hv
      dsimp [fterm]
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
      have hv1 : 1 ≤ roughPart y m := roughPart_pos y hm1
      have hv0 : (0 : ℝ) < roughPart y m := by exact_mod_cast hv1
      have he0 : (0 : ℝ) < e := by exact_mod_cast he1
      have he_le_y : (e : ℝ) ≤ y := by exact_mod_cast hey
      rw [mollifiedZetaCoeff_mul_roughPart b' y e m]
      have hexp1 : (-2 : ℝ) * (1 / 2 + (0 : ℝ) / L) = -1 := by ring
      rw [hexp1, Real.rpow_neg_one, Nat.cast_mul]
      have hce2 : (1 / (y : ℝ)) ^ 2 ≤ ‖RHTower.mollifiedZetaCoeff b' y e‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hce_ge 2
      have hev_inv : (1 / (y : ℝ)) * (1 / (roughPart y m : ℝ)) ≤
          ((e : ℝ) * (roughPart y m : ℝ))⁻¹ := by
        rw [mul_inv, ← one_div, ← one_div]
        exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le he0 he_le_y) (by positivity)
      calc (1 / (y : ℝ) ^ 3) * (1 / (roughPart y m : ℝ))
          = (1 / (y : ℝ)) ^ 2 * ((1 / (y : ℝ)) * (1 / (roughPart y m : ℝ))) := by ring
        _ ≤ ‖RHTower.mollifiedZetaCoeff b' y e‖ ^ 2 * ((e : ℝ) * (roughPart y m : ℝ))⁻¹ :=
            mul_le_mul hce2 hev_inv (by positivity) (sq_nonneg _)
    have hlogy_u : Real.log (y : ℝ) ≤ u := by
      have h1 : Real.log (y : ℝ) ≤ Real.log u := Real.log_le_log hy0 hyle_u
      have h2 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu_pos
      linarith
    have hmert := exp_one_add_mertensS_le_inv_roughMollifierConst hy hu1 hlogy_u
    rw [← hcr_def] at hmert
    have hlogM₂ : L / 2 ≤ Real.log ((M₂ : ℝ) + 1) := by
      have h1 : Real.exp (L / 2) ≤ (M₂ : ℝ) + 1 := by
        rw [hM₂_def]; have := Nat.lt_floor_add_one (Real.exp (L / 2)); linarith
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    have hlogM₂_nn : 0 ≤ Real.log ((M₂ : ℝ) + 1) := by linarith
    have hV₂_ge : (cr / 2) * u ^ 7 ≤ ∑ v ∈ V₂, (1 / (v : ℝ)) := by
      have hbase := sum_inv_image_roughPart_ge y M₂
      have hdiv : (cr / 2) * u ^ 7 ≤
          Real.log ((M₂ : ℝ) + 1) / Real.exp (1 + RHTower.Sieve.mertensS y) := by
        have h1 : (cr / 2) * u ^ 7 = (L / 2) / (u / cr) := by rw [← hu8]; field_simp
        rw [h1]
        exact div_le_div₀ hlogM₂_nn hlogM₂ (Real.exp_pos _) hmert
      exact hdiv.trans hbase
    have hy3_u3 : (y : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by positivity) hyle_u 3
    have hD₀_cr : D₀ ≤ (cr / 2) * u ^ 4 := by
      have h4E : 4 * E / cr ≤ u := hK_cr.trans hK_le_u
      have h4E' : 4 * E ≤ u * cr := (div_le_iff₀ hcr0).mp h4E
      have hu_u2 : u ≤ u ^ 2 := by
        have := mul_le_mul_of_nonneg_left hu1 hu_pos.le
        linarith [show u * 1 = u by ring, show u * u = u ^ 2 by ring]
      have h4E'' : 4 * E ≤ cr * u ^ 2 := by
        have := mul_le_mul_of_nonneg_left hu_u2 hcr0.le
        linarith
      have hstep : (4 * E) * u ^ 2 ≤ (cr * u ^ 2) * u ^ 2 :=
        mul_le_mul_of_nonneg_right h4E'' (sq_nonneg u)
      have h2Eu2 : 2 * E * u ^ 2 ≤ (cr / 2) * u ^ 4 := by
        linarith [show (4 * E) * u ^ 2 = 2 * (2 * E * u ^ 2) by ring,
          show (cr * u ^ 2) * u ^ 2 = 2 * ((cr / 2) * u ^ 4) by ring]
      exact hD₀_le_u2.trans h2Eu2
    calc D₀ ≤ (cr / 2) * u ^ 4 := hD₀_cr
      _ = (1 / u ^ 3) * ((cr / 2) * u ^ 7) := by field_simp
      _ ≤ (1 / (y : ℝ) ^ 3) * ((cr / 2) * u ^ 7) :=
          mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) hy3_u3)
            (by positivity)
      _ ≤ (1 / (y : ℝ) ^ 3) * ∑ v ∈ V₂, (1 / (v : ℝ)) :=
          mul_le_mul_of_nonneg_left hV₂_ge (by positivity)
      _ = ∑ v ∈ V₂, (1 / (y : ℝ) ^ 3) * (1 / (v : ℝ)) := Finset.mul_sum _ _ _
      _ ≤ ∑ v ∈ V₂, fterm (e * v) := Finset.sum_le_sum hterm
      _ = ∑ n ∈ V₂.image (fun v => e * v), fterm n := (Finset.sum_image hinj).symm
      _ ≤ ∑ n ∈ Finset.Icc 1 M, fterm n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hfterm0 n hn
  rw [hM_def] at hD_ge
  have hfloor := gaussFloor_general_at_scale (a := 0) (θ₁ := 1 / 2) (L := L) (D₀ := D₀)
    (δ := 1 / 2) le_rfl (by norm_num) (by norm_num) hD₀1 (by norm_num) (by norm_num)
    (by linarith) (by linarith) hδLc (by linarith) hy hyle_half hb'_le1 hD_ge
  rw [hL_def, Real.exp_log hT0, ← hL_def] at hfloor
  have hzero_div : ∀ t : ℝ, (((1 / 2 + (0 : ℝ) / L : ℝ) : ℂ) + (t : ℂ) * I) =
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := fun _ => by simp
  simp only [hzero_div] at hfloor
  have hD₀_sub_ge : (y : ℝ) ^ 2 * E ≤ D₀ - 1 / 2 := by linarith [hD₀_def]
  have hmsq_b'_ge : ((y : ℝ) ^ 2 * E) * T ≤ ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right hD₀_sub_ge hT0.le).trans hfloor
  have hmsq_b'_pos : 0 < ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) hmsq_b'_ge
  have hmsq_b_pos : 0 < ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    have heq : (∫ t in T..(2 * T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
        lam ^ 2 * ∫ t in T..(2 * T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have hed : RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
          (lam : ℂ) * RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
        unfold RHTower.edPoly; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by dsimp [b']; ring
      rw [hed, mul_left_comm _ (lam : ℂ) _, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hlam0, mul_pow]
    rw [heq] at hmsq_b'_pos
    exact pos_of_mul_pos_right hmsq_b'_pos (sq_nonneg lam)
  rw [← flowCreditedJensenBudget_smul hT0 hlam0 ⟨d_nz, hd_nz, hbd_nz⟩ hmsq_b_pos]
  have hlog_pt : ∀ t : ℝ,
      Real.log ‖RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        Real.log (y : ℝ) := by
    intro t
    have hnorm_y : ‖RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        (y : ℝ) := by
      unfold RHTower.edPoly
      calc ‖∑ d ∈ Finset.Icc 1 y, b' d * ((d : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖
          ≤ ∑ d ∈ Finset.Icc 1 y,
              ‖b' d * ((d : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ := norm_sum_le _ _
        _ ≤ ∑ _d ∈ Finset.Icc 1 y, (1 : ℝ) := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            rw [norm_mul, RHTower.norm_ofReal_natCast_cpow hd1]
            have hre : (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
            rw [hre]
            have hrpow : (d : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by norm_num)
            exact mul_le_one₀ (hb'_le1 d hd) (by positivity) hrpow
        _ = (y : ℝ) := by simp
    rcases eq_or_lt_of_le (norm_nonneg
      (RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))) with h0 | hpos
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hy1
    · exact Real.log_le_log hpos hnorm_y
  have hlog_int_le : (1 / T) * (∫ t in T..(2 * T),
      Real.log ‖RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
      Real.log (y : ℝ) := by
    have hint := intervalIntegral.integral_mono_on (by linarith : T ≤ 2 * T)
      (intervalIntegrable_log_norm_edPoly_criticalLine b' y T (2 * T)) intervalIntegrable_const
      (fun t _ => hlog_pt t)
    rw [intervalIntegral.integral_const, smul_eq_mul, show 2 * T - T = T by ring] at hint
    have hdiv := mul_le_mul_of_nonneg_left hint (one_div_nonneg.mpr hT0.le)
    calc (1 / T) * (∫ t in T..(2 * T),
          Real.log ‖RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        ≤ (1 / T) * (T * Real.log (y : ℝ)) := hdiv
      _ = Real.log (y : ℝ) := by field_simp [hT0.ne']
  have havg_ge : (y : ℝ) ^ 2 * E ≤ (1 / T) * ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hmsq_b'_ge (one_div_nonneg.mpr hT0.le)
    calc (y : ℝ) ^ 2 * E = (1 / T) * (((y : ℝ) ^ 2 * E) * T) := by field_simp [hT0.ne']
      _ ≤ _ := h
  have hhalf_log_ge : Real.log (y : ℝ) + max 0 A + 1 ≤
      (1 / 2 : ℝ) * Real.log ((1 / T) * ∫ t in T..(2 * T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
    have hlog := Real.log_le_log (by positivity) havg_ge
    have hlogE : Real.log E = 2 * max 0 A + 2 := by rw [hE_def, Real.log_exp]
    have hpow : Real.log ((y : ℝ) ^ 2) = 2 * Real.log (y : ℝ) := by
      rw [Real.log_pow]; push_cast; rfl
    rw [Real.log_mul (pow_ne_zero 2 hy0.ne') hE0.ne', hpow, hlogE] at hlog
    linarith
  unfold flowCreditedJensenBudget
  have hA_max : A ≤ max 0 A := le_max_right _ _
  linarith

/-- For every fixed nonzero Dirichlet polynomial `Ψ(s) = ∑_{d = 1}^y b_d d^{-s}`, the vertical-flow
credited Jensen budget `flowCreditedJensenBudget b y T` tends to `+∞` as `T → +∞`. -/
theorem tendsto_flowCreditedJensenBudget_atTop {b : ℕ → ℂ} {y : ℕ} (hy : 1 ≤ y)
    (hne : ∃ d ∈ Finset.Icc 1 y, b d ≠ 0) :
    Tendsto (flowCreditedJensenBudget b y) atTop atTop := by
  rw [tendsto_atTop]
  intro A
  have hy_ev : ∀ᶠ T in atTop, (y : ℝ) ≤ (Real.log T) ^ (1 / 8 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (y : ℝ))
  filter_upwards [eventually_flowCreditedJensenBudget_ge A, hy_ev] with T hA hyT
  exact hA y hy hyT b hne

/-! ## §3. Gaussian Cahen–Mellin single-zero critical-line spike (`θ > 1`, `θ → ∞`), Eventual Quasi-RH, and `RiemannHypothesis` -/

theorem convolution_one_cutIcc_eq_mollifiedZetaCoeff (b : ℕ → ℂ) (y : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    LSeries.convolution 1 (RHTower.cutIcc y b) n = RHTower.mollifiedZetaCoeff b y n := by
  simp only [LSeries.convolution_def]
  rw [Nat.sum_divisorsAntidiagonal' (fun x d => (1 : ℕ → ℂ) x * RHTower.cutIcc y b d)]
  simp only [Pi.one_apply, one_mul]
  unfold RHTower.mollifiedZetaCoeff RHTower.cutIcc
  rw [← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdn, hn0⟩, hd1, hdy⟩
    exact ⟨⟨hd1, hdy⟩, hdn⟩
  · rintro ⟨⟨hd1, hdy⟩, hdn⟩
    exact ⟨⟨hdn, by omega⟩, hd1, hdy⟩

/-- Dirichlet-series expansion of `ζ(s) Ψ(s)` in the half-plane `Re s > 1`. -/
theorem hasSum_mollifiedZeta_of_one_lt_re (b : ℕ → ℂ) (y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => LSeries.term (RHTower.mollifiedZetaCoeff b y) s n)
      (riemannZeta s * RHTower.edPoly b (Finset.Icc 1 y) s) := by
  have hsum1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hsumΨ : LSeriesSummable (RHTower.cutIcc y b) s :=
    RHTower.Sieve.LSeriesSummable_of_support (fun k hk => RHTower.cutIcc_support hk) s
  have hconv : LSeriesSummable (LSeries.convolution 1 (RHTower.cutIcc y b)) s :=
    hsum1.convolution hsumΨ
  have hterm : (fun n : ℕ => LSeries.term (RHTower.mollifiedZetaCoeff b y) s n) =
      (fun n : ℕ => LSeries.term (LSeries.convolution 1 (RHTower.cutIcc y b)) s n) := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [LSeries.term_of_ne_zero hn.ne',
        convolution_one_cutIcc_eq_mollifiedZetaCoeff b y hn]
  rw [hterm, ← LSeries_one_eq_riemannZeta hs, RHTower.edPoly_Icc_eq_LSeries y b s,
    ← LSeries_convolution' hsum1 hsumΨ]
  exact hconv.hasSum

theorem norm_mollifiedZetaCoeff_le_mul_nat {b : ℕ → ℂ} {y n : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ B) (hn : 1 ≤ n) :
    ‖RHTower.mollifiedZetaCoeff b y n‖ ≤ B * (n : ℝ) := by
  unfold RHTower.mollifiedZetaCoeff
  have hsub : (Finset.Icc 1 y).filter (fun d => d ∣ n) ⊆ Finset.Icc 1 n := by
    intro d hd
    obtain ⟨hd_Icc, hdn⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd_Icc).1, Nat.le_of_dvd (by omega) hdn⟩
  calc ‖∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), b d‖
      ≤ ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), ‖b d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), B :=
        Finset.sum_le_sum fun d hd => hb d (Finset.mem_filter.mp hd).1
    _ ≤ ∑ _d ∈ Finset.Icc 1 n, B :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hB
    _ = B * (n : ℝ) := by simp [mul_comm]

/-- Integrand `exp(α(u + iτ)² + x(u + iτ)) / (u + iτ)` of the Gaussian Cahen–Mellin kernel. -/
def cahenMellinGaussIntegrand (α u x τ : ℝ) : ℂ :=
  Complex.exp ((α : ℂ) * ((u : ℂ) + (τ : ℂ) * I) ^ 2 + (x : ℂ) * ((u : ℂ) + (τ : ℂ) * I)) /
    ((u : ℂ) + (τ : ℂ) * I)

/-- Gaussian Cahen–Mellin kernel `(2π)⁻¹ ∫_ℝ exp(α(u + iτ)² + x(u + iτ)) / (u + iτ) dτ`. -/
def cahenMellinGauss (α u x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, cahenMellinGaussIntegrand α u x τ

theorem norm_add_mul_I_ge_abs_left (u τ : ℝ) :
    |u| ≤ ‖(u : ℂ) + (τ : ℂ) * I‖ := by
  have h := Complex.abs_re_le_norm ((u : ℂ) + (τ : ℂ) * I)
  simpa using h

theorem norm_add_mul_I_ge_abs_right (u τ : ℝ) :
    |τ| ≤ ‖(u : ℂ) + (τ : ℂ) * I‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) + (τ : ℂ) * I)
  simpa using h

theorem norm_exp_quad_add_lin (α u x τ : ℝ) :
    ‖Complex.exp ((α : ℂ) * ((u : ℂ) + (τ : ℂ) * I) ^ 2 +
        (x : ℂ) * ((u : ℂ) + (τ : ℂ) * I))‖ =
      Real.exp (α * (u ^ 2 - τ ^ 2) + x * u) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]

theorem norm_cahenMellinGaussIntegrand_le {α u x τ : ℝ} (hu : u ≠ 0) :
    ‖cahenMellinGaussIntegrand α u x τ‖ ≤
      (Real.exp (α * u ^ 2 + x * u) / |u|) * Real.exp (-α * τ ^ 2) := by
  unfold cahenMellinGaussIntegrand
  rw [norm_div, norm_exp_quad_add_lin]
  have hu0 : 0 < |u| := abs_pos.mpr hu
  have hden : |u| ≤ ‖(u : ℂ) + (τ : ℂ) * I‖ := norm_add_mul_I_ge_abs_left u τ
  have hexp : Real.exp (α * (u ^ 2 - τ ^ 2) + x * u) =
      Real.exp (α * u ^ 2 + x * u) * Real.exp (-α * τ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc Real.exp (α * u ^ 2 + x * u) * Real.exp (-α * τ ^ 2) / ‖(u : ℂ) + (τ : ℂ) * I‖
      ≤ Real.exp (α * u ^ 2 + x * u) * Real.exp (-α * τ ^ 2) / |u| :=
        div_le_div_of_nonneg_left (by positivity) hu0 hden
    _ = (Real.exp (α * u ^ 2 + x * u) / |u|) * Real.exp (-α * τ ^ 2) := by ring

theorem continuous_cahenMellinGaussIntegrand {α u x : ℝ} (hu : u ≠ 0) :
    Continuous (cahenMellinGaussIntegrand α u x) := by
  unfold cahenMellinGaussIntegrand
  refine Continuous.div (by fun_prop) (by fun_prop) fun τ => ?_
  intro h0
  have := congrArg Complex.re h0
  simp at this
  exact hu this

theorem integrable_cahenMellinGaussIntegrand {α u x : ℝ} (hα : 0 < α) (hu : u ≠ 0) :
    Integrable (cahenMellinGaussIntegrand α u x) := by
  have hdom : Integrable (fun τ : ℝ =>
      (Real.exp (α * u ^ 2 + x * u) / |u|) * Real.exp (-α * τ ^ 2)) :=
    (integrable_exp_neg_mul_sq hα).const_mul _
  exact hdom.mono' (continuous_cahenMellinGaussIntegrand hu).aestronglyMeasurable
    (Eventually.of_forall fun τ => norm_cahenMellinGaussIntegrand_le hu)

theorem norm_cahenMellinGauss_le {α u x : ℝ} (hα : 0 < α) (hu : u ≠ 0) :
    ‖cahenMellinGauss α u x‖ ≤
      Real.exp (α * u ^ 2 + x * u) / (2 * |u| * Real.sqrt (Real.pi * α)) := by
  unfold cahenMellinGauss
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu0 : 0 < |u| := abs_pos.mpr hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hint : ‖∫ τ : ℝ, cahenMellinGaussIntegrand α u x τ‖ ≤
      (Real.exp (α * u ^ 2 + x * u) / |u|) * Real.sqrt (Real.pi / α) := by
    calc ‖∫ τ : ℝ, cahenMellinGaussIntegrand α u x τ‖
        ≤ ∫ τ : ℝ, ‖cahenMellinGaussIntegrand α u x τ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ τ : ℝ, (Real.exp (α * u ^ 2 + x * u) / |u|) * Real.exp (-α * τ ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            ((integrable_exp_neg_mul_sq hα).const_mul _)
            (Eventually.of_forall fun _ => norm_cahenMellinGaussIntegrand_le hu)
      _ = (Real.exp (α * u ^ 2 + x * u) / |u|) * Real.sqrt (Real.pi / α) := by
          rw [integral_const_mul, integral_gaussian]
  calc (1 / (2 * Real.pi)) * ‖∫ τ : ℝ, cahenMellinGaussIntegrand α u x τ‖
      ≤ (1 / (2 * Real.pi)) * ((Real.exp (α * u ^ 2 + x * u) / |u|) * Real.sqrt (Real.pi / α)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = Real.exp (α * u ^ 2 + x * u) / (2 * |u| * Real.sqrt (Real.pi * α)) := by
        rw [Real.sqrt_div hpi.le, Real.sqrt_mul hpi.le]
        have hsqrt_pi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
        have hsp_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr hpi).ne'
        have hsqa_ne : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
        field_simp
        nlinarith only [hsqrt_pi]

/-- Residue identity across `w = 0`: for `u > 0` and `v > 0`,
`cahenMellinGauss α u x - cahenMellinGauss α (-v) x = 1`. -/
theorem cahenMellinGauss_sub_neg_eq_one {α u v : ℝ} (hα : 0 < α) (hu : 0 < u) (hv : 0 < v)
    (x : ℝ) :
    cahenMellinGauss α u x - cahenMellinGauss α (-v) x = 1 := by
  have ⟨H, hH_def⟩ : ∃ f : ℂ → ℂ,
      f = fun w => Complex.exp ((α : ℂ) * w ^ 2 + (x : ℂ) * w) := ⟨_, rfl⟩
  have hH_diff : Differentiable ℂ H := by rw [hH_def]; fun_prop
  have ⟨M, hM_def⟩ : ∃ m : ℝ, m = max u v := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM_def]; exact lt_max_of_lt_left hu
  have ⟨C₀, hC₀_def⟩ : ∃ c : ℝ,
      c = Real.exp (α * M ^ 2 + |x| * M) * max 1 (1 / α) := ⟨_, rfl⟩
  have hC : ∀ σ t : ℝ, -v ≤ σ → σ ≤ u → ‖H ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₀ / (1 + t ^ 2) := by
    intro σ t hσ1 hσ2
    have habsσ : |σ| ≤ M := by
      rw [hM_def, abs_le]
      exact ⟨by linarith [le_max_right u v], by linarith [le_max_left u v]⟩
    have hσ_sq : σ ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs σ]
      exact pow_le_pow_left₀ (abs_nonneg σ) habsσ 2
    have hxσ : x * σ ≤ |x| * M :=
      (le_abs_self (x * σ)).trans
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left habsσ (abs_nonneg x))
    have hnormH : ‖H ((σ : ℂ) + (t : ℂ) * I)‖ =
        Real.exp (α * σ ^ 2 + x * σ) * Real.exp (-α * t ^ 2) := by
      rw [hH_def, norm_exp_quad_add_lin, ← Real.exp_add]
      congr 1; ring
    rw [hnormH]
    have hexp_σ : Real.exp (α * σ ^ 2 + x * σ) ≤ Real.exp (α * M ^ 2 + |x| * M) :=
      Real.exp_le_exp.mpr (by nlinarith only [hα, hσ_sq, hxσ])
    have hexp_t : Real.exp (-α * t ^ 2) ≤ max 1 (1 / α) / (1 + t ^ 2) := by
      have h1t : 0 < 1 + t ^ 2 := by positivity
      rw [le_div_iff₀ h1t]
      have h1a : 1 + α * t ^ 2 ≤ Real.exp (α * t ^ 2) :=
        by linarith [Real.add_one_le_exp (α * t ^ 2)]
      have hprod1 : Real.exp (-α * t ^ 2) * Real.exp (α * t ^ 2) = 1 := by
        rw [← Real.exp_add]; simp
      have hle1 : Real.exp (-α * t ^ 2) * (1 + α * t ^ 2) ≤ 1 := by
        calc Real.exp (-α * t ^ 2) * (1 + α * t ^ 2)
            ≤ Real.exp (-α * t ^ 2) * Real.exp (α * t ^ 2) :=
              mul_le_mul_of_nonneg_left h1a (Real.exp_pos _).le
          _ = 1 := hprod1
      have hm1 : 1 ≤ max 1 (1 / α) := le_max_left _ _
      have hm2 : 1 / α ≤ max 1 (1 / α) := le_max_right _ _
      have hm2' : 1 ≤ max 1 (1 / α) * α := (div_le_iff₀ hα).mp hm2
      have ht_bound : 1 + t ^ 2 ≤ max 1 (1 / α) * (1 + α * t ^ 2) := by
        have ht2_nn : 0 ≤ t ^ 2 := sq_nonneg t
        nlinarith only [hm1, hm2', ht2_nn]
      calc Real.exp (-α * t ^ 2) * (1 + t ^ 2)
          ≤ Real.exp (-α * t ^ 2) * (max 1 (1 / α) * (1 + α * t ^ 2)) :=
            mul_le_mul_of_nonneg_left ht_bound (Real.exp_pos _).le
        _ = max 1 (1 / α) * (Real.exp (-α * t ^ 2) * (1 + α * t ^ 2)) := by ring
        _ ≤ max 1 (1 / α) * 1 :=
            mul_le_mul_of_nonneg_left hle1 (by linarith)
        _ = max 1 (1 / α) := mul_one _
    rw [hC₀_def, mul_div_assoc]
    exact mul_le_mul hexp_σ hexp_t (Real.exp_pos _).le (Real.exp_pos _).le
  have hp1 : -v < (0 : ℂ).re := by simp [hv]
  have hp2 : (0 : ℂ).re < u := by simp [hu]
  have htwo := RHTower.WeilLineIntegral.two_line_simple_pole hH_diff hC hp1 hp2
  have hH0 : H 0 = 1 := by rw [hH_def]; simp
  rw [hH0, mul_one] at htwo
  have heq_int : ∀ w_re : ℝ,
      (∫ t : ℝ, H ((w_re : ℂ) + (t : ℂ) * I) / (((w_re : ℂ) + (t : ℂ) * I) - 0)) =
        ∫ t : ℝ, cahenMellinGaussIntegrand α w_re x t := by
    intro w_re
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [hH_def]
    dsimp only
    rw [sub_zero]
    rfl
  rw [heq_int u, heq_int (-v)] at htwo
  unfold cahenMellinGauss
  rw [← mul_sub, htwo]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem cahenMellinGauss_eq_of_pos {α u₁ u₂ : ℝ} (hα : 0 < α) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂)
    (x : ℝ) :
    cahenMellinGauss α u₁ x = cahenMellinGauss α u₂ x := by
  have h1 := cahenMellinGauss_sub_neg_eq_one hα hu₁ one_pos x
  have h2 := cahenMellinGauss_sub_neg_eq_one hα hu₂ one_pos x
  linear_combination h1 - h2

/-- Saddle-point Gaussian decay of `cahenMellinGauss α u x` for `x < 0`. -/
theorem norm_cahenMellinGauss_neg_le {α u x : ℝ} (hα : 0 < α) (hu : 0 < u) (hx : x < 0) :
    ‖cahenMellinGauss α u x‖ ≤
      (Real.sqrt α / (Real.sqrt Real.pi * (-x))) * Real.exp (-x ^ 2 / (4 * α)) := by
  have hv : 0 < -x / (2 * α) := div_pos (neg_pos.mpr hx) (by positivity)
  rw [cahenMellinGauss_eq_of_pos hα hu hv x]
  refine (norm_cahenMellinGauss_le (x := x) hα hv.ne').trans (le_of_eq ?_)
  rw [abs_of_pos hv]
  have h1 : α * (-x / (2 * α)) ^ 2 + x * (-x / (2 * α)) = -x ^ 2 / (4 * α) := by
    field_simp; ring
  have hden : 2 * (-x / (2 * α)) * Real.sqrt (Real.pi * α) =
      (Real.sqrt Real.pi * (-x)) / Real.sqrt α := by
    rw [Real.sqrt_mul Real.pi_pos.le]
    have hsqa : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
    have hsqa_ne : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
    field_simp
    rw [hsqa]; ring
  rw [h1, hden]
  field_simp; ring

/-- Saddle-point lower bound `(cahenMellinGauss α u x).re ≥ 3/4` whenever `x ≥ 2 √α`. -/
theorem re_cahenMellinGauss_ge_of_two_mul_sqrt_le {α u x : ℝ} (hα : 0 < α) (hu : 0 < u)
    (hx : 2 * Real.sqrt α ≤ x) :
    3 / 4 ≤ (cahenMellinGauss α u x).re := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hv : 0 < x / (2 * α) := div_pos hx0 (by positivity)
  have hres := cahenMellinGauss_sub_neg_eq_one hα hu hv x
  have heq : cahenMellinGauss α u x = 1 + cahenMellinGauss α (-(x / (2 * α))) x := by
    linear_combination hres
  have hnorm : ‖cahenMellinGauss α (-(x / (2 * α))) x‖ ≤ 1 / 4 := by
    have hle := norm_cahenMellinGauss_le (x := x) hα (neg_lt_zero.mpr hv).ne
    have habs : |-(x / (2 * α))| = x / (2 * α) := by rw [abs_neg, abs_of_pos hv]
    have hexp_arg : α * (-(x / (2 * α))) ^ 2 + x * (-(x / (2 * α))) = -x ^ 2 / (4 * α) := by
      field_simp; ring
    rw [habs, hexp_arg] at hle
    have hden_eq : 2 * (x / (2 * α)) * Real.sqrt (Real.pi * α) =
        (x / Real.sqrt α) * Real.sqrt Real.pi := by
      rw [Real.sqrt_mul Real.pi_pos.le]
      have hsqa : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
      have hsqa_ne : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
      field_simp
      rw [hsqa]; ring
    rw [hden_eq] at hle
    have hx_div : 2 ≤ x / Real.sqrt α := (le_div_iff₀ (Real.sqrt_pos.mpr hα)).mpr hx
    have hspi_ge1 : 1 ≤ Real.sqrt Real.pi := by
      rw [Real.le_sqrt zero_le_one Real.pi_pos.le]
      linarith [Real.pi_gt_three]
    have hden_ge2 : 2 ≤ (x / Real.sqrt α) * Real.sqrt Real.pi := by
      nlinarith only [hx_div, hspi_ge1]
    have hx2_ge : 4 * α ≤ x ^ 2 := by
      have h1 : (2 * Real.sqrt α) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
      rw [mul_pow, Real.sq_sqrt hα.le] at h1
      linarith
    have hexp_le : Real.exp (-x ^ 2 / (4 * α)) ≤ 1 / 2 := by
      have harg : -x ^ 2 / (4 * α) ≤ -1 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc Real.exp (-x ^ 2 / (4 * α))
          ≤ Real.exp (-1) := Real.exp_le_exp.mpr harg
        _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ zero_lt_two he1
    calc ‖cahenMellinGauss α (-(x / (2 * α))) x‖
        ≤ Real.exp (-x ^ 2 / (4 * α)) / ((x / Real.sqrt α) * Real.sqrt Real.pi) := hle
      _ ≤ (1 / 2) / 2 := div_le_div₀ (by norm_num) hexp_le zero_lt_two hden_ge2
      _ = 1 / 4 := by norm_num
  rw [heq, Complex.add_re, Complex.one_re]
  have hre_ge : -(1 / 4 : ℝ) ≤ (cahenMellinGauss α (-(x / (2 * α))) x).re := by
    have := neg_abs_le (cahenMellinGauss α (-(x / (2 * α))) x).re
    have h2 := (Complex.abs_re_le_norm (cahenMellinGauss α (-(x / (2 * α))) x)).trans hnorm
    linarith
  linarith

/-- Universal scale-free bound `‖cahenMellinGauss α u x‖ ≤ 2` across all `α > 0`, `u > 0`, `x ∈ ℝ`. -/
theorem norm_cahenMellinGauss_le_two {α u : ℝ} (hα : 0 < α) (hu : 0 < u) (x : ℝ) :
    ‖cahenMellinGauss α u x‖ ≤ 2 := by
  have hv : 0 < 1 / Real.sqrt α := by positivity
  have hden : 2 * (1 / Real.sqrt α) * Real.sqrt (Real.pi * α) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul Real.pi_pos.le]
    have hsqa_ne : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
    field_simp
  have he1_le : Real.exp 1 / (2 * Real.sqrt Real.pi) ≤ 1 := by
    have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    have h2spi : 3 ≤ 2 * Real.sqrt Real.pi := by
      have hsq : (3 : ℝ) ^ 2 ≤ (2 * Real.sqrt Real.pi) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
        linarith [Real.pi_gt_three]
      nlinarith [Real.sqrt_nonneg Real.pi]
    exact (div_le_one (by positivity)).mpr (he1.trans h2spi)
  rcases le_or_gt x 0 with hx | hx
  · rw [cahenMellinGauss_eq_of_pos hα hu hv x]
    have hle := norm_cahenMellinGauss_le (x := x) hα hv.ne'
    rw [abs_of_pos hv, hden] at hle
    have hexp_le : Real.exp (α * (1 / Real.sqrt α) ^ 2 + x * (1 / Real.sqrt α)) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      have h1 : α * (1 / Real.sqrt α) ^ 2 = 1 := by
        rw [one_div, inv_pow, Real.sq_sqrt hα.le, mul_inv_cancel₀ hα.ne']
      have h2 : x * (1 / Real.sqrt α) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx hv.le
      linarith
    exact hle.trans (((div_le_div_of_nonneg_right hexp_le (by positivity)).trans he1_le).trans
      (by norm_num))
  · have hres := cahenMellinGauss_sub_neg_eq_one hα hu hv x
    have heq : cahenMellinGauss α u x = 1 + cahenMellinGauss α (-(1 / Real.sqrt α)) x := by
      linear_combination hres
    rw [heq]
    have hle := norm_cahenMellinGauss_le (x := x) hα (neg_lt_zero.mpr hv).ne
    rw [abs_neg, abs_of_pos hv, hden] at hle
    have hexp_le : Real.exp (α * (-(1 / Real.sqrt α)) ^ 2 + x * (-(1 / Real.sqrt α))) ≤
        Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      have h1 : α * (-(1 / Real.sqrt α)) ^ 2 = 1 := by
        rw [neg_sq, one_div, inv_pow, Real.sq_sqrt hα.le, mul_inv_cancel₀ hα.ne']
      have h2 : x * (-(1 / Real.sqrt α)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hx.le (neg_nonpos.mpr hv.le)
      linarith
    have hneg_le1 : ‖cahenMellinGauss α (-(1 / Real.sqrt α)) x‖ ≤ 1 :=
      hle.trans ((div_le_div_of_nonneg_right hexp_le (by positivity)).trans he1_le)
    calc ‖(1 : ℂ) + cahenMellinGauss α (-(1 / Real.sqrt α)) x‖
        ≤ ‖(1 : ℂ)‖ + ‖cahenMellinGauss α (-(1 / Real.sqrt α)) x‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num

theorem rect_mem_nhds_zero {c d R : ℝ} (hc : c < 0) (hd : 0 < d) (hR : 0 < R) :
    Set.uIcc c d ×ℂ Set.uIcc (-R) R ∈ nhds (0 : ℂ) := by
  have hcd : c ≤ d := by linarith
  have hRR : (-R : ℝ) ≤ R := by linarith
  refine Filter.mem_of_superset (?_ : Set.Ioo c d ×ℂ Set.Ioo (-R) R ∈ nhds (0 : ℂ)) ?_
  · have hopen : IsOpen (Set.Ioo c d ×ℂ Set.Ioo (-R) R) :=
      (isOpen_Ioo.preimage Complex.continuous_re).inter
        (isOpen_Ioo.preimage Complex.continuous_im)
    refine hopen.mem_nhds ?_
    rw [Complex.mem_reProdIm]
    exact ⟨⟨by simp [hc], by simp [hd]⟩, ⟨by simp; linarith, by simp [hR]⟩⟩
  · intro z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le hRR]
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩

/-- Shifted Gaussian-mollified zeta numerator `ζ(ρ₀ + w) Ψ(ρ₀ + w) exp(α w² + w log Y)`. -/
def mollifiedZetaGauss (ρ₀ : ℂ) (b : ℕ → ℂ) (X : ℕ) (α Y : ℝ) (w : ℂ) : ℂ :=
  riemannZeta (ρ₀ + w) * RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + w) *
    Complex.exp ((α : ℂ) * w ^ 2 + (Real.log Y : ℂ) * w)

theorem differentiableOn_dslope_mollifiedZetaGauss_rect {ρ₀ : ℂ} (_hζ0 : riemannZeta ρ₀ = 0)
    (b : ℕ → ℂ) (X : ℕ) (α Y : ℝ) {c d R : ℝ} (hc : c < 0) (hd : 0 < d) (hR : 0 < R)
    (hγ : R + 1 ≤ ρ₀.im) :
    DifferentiableOn ℂ (dslope (mollifiedZetaGauss ρ₀ b X α Y) 0)
      (Set.uIcc c d ×ℂ Set.uIcc (-R) R) := by
  refine (Complex.differentiableOn_dslope (rect_mem_nhds_zero hc hd hR)).2 ?_
  intro w hw
  have hRR : (-R : ℝ) ≤ R := by linarith
  have hw_im : -R ≤ w.im := by
    have := (Complex.mem_reProdIm.mp hw).2
    rw [Set.uIcc_of_le hRR] at this
    exact this.1
  have hne1 : ρ₀ + w ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im] at this
    linarith
  have hsX : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  unfold mollifiedZetaGauss
  exact (((differentiableAt_riemannZeta hne1).comp w (differentiableAt_id.const_add ρ₀)).mul
    ((RHTower.differentiable_edPoly b hsX (ρ₀ + w)).comp w
      (differentiableAt_id.const_add ρ₀))).mul
    (by fun_prop) |>.differentiableWithinAt

theorem dslope_mollifiedZetaGauss_eq_div {ρ₀ : ℂ} (hζ0 : riemannZeta ρ₀ = 0)
    (b : ℕ → ℂ) (X : ℕ) (α Y : ℝ) {w : ℂ} (hw : w ≠ 0) :
    dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 w = mollifiedZetaGauss ρ₀ b X α Y w / w := by
  rw [dslope_of_ne _ hw, slope_def_field]
  have h0 : mollifiedZetaGauss ρ₀ b X α Y 0 = 0 := by simp [mollifiedZetaGauss, hζ0]
  rw [h0, sub_zero, sub_zero]

theorem sum_range_inv_sq_shift_le {a : ℕ} (ha : 1 ≤ a) (k : ℕ) :
    (∑ j ∈ Finset.range k, ((((a + 1 + j : ℕ) : ℝ)) ^ 2)⁻¹) ≤
      1 / (a : ℝ) - 1 / ((a + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hu0 : (0 : ℝ) < ((a + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + k)
    have hu1 : (0 : ℝ) < ((a + (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < a + (k + 1))
    have hcast : ((a + 1 + k : ℕ) : ℝ) = ((a + k : ℕ) : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((a + (k + 1) : ℕ) : ℝ) = ((a + k : ℕ) : ℝ) + 1 := by push_cast; ring
    have hstep : ((((a + 1 + k : ℕ) : ℝ)) ^ 2)⁻¹ ≤
        1 / ((a + k : ℕ) : ℝ) - 1 / ((a + (k + 1) : ℕ) : ℝ) := by
      rw [hcast, hcast2]
      have hden : 0 < ((a + k : ℕ) : ℝ) * (((a + k : ℕ) : ℝ) + 1) ^ 2 := by positivity
      have hdiff : 1 / ((a + k : ℕ) : ℝ) - 1 / (((a + k : ℕ) : ℝ) + 1) =
          1 / (((a + k : ℕ) : ℝ) * (((a + k : ℕ) : ℝ) + 1)) := by
        field_simp [hu0.ne', (by linarith : (((a + k : ℕ) : ℝ) + 1) ≠ 0)]; ring
      rw [hdiff, one_div]
      exact inv_anti₀ (by positivity) (by nlinarith only [hu0])
    linarith only [ih, hstep]

theorem sum_Ioo_inv_sq_le_div {X₁ : ℕ} (hX₁ : 1 ≤ X₁) (M : ℕ) :
    (∑ n ∈ Finset.Ioo X₁ M, ((n : ℝ) ^ 2)⁻¹) ≤ 1 / (X₁ : ℝ) := by
  have hX₁0 : (0 : ℝ) < X₁ := by exact_mod_cast hX₁
  rcases le_or_gt M (X₁ + 1) with hM | hM
  · have hemp : Finset.Ioo X₁ M = ∅ := by
      ext n; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
    rw [hemp, Finset.sum_empty]; positivity
  · have hbij : (∑ n ∈ Finset.Ioo X₁ M, ((n : ℝ) ^ 2)⁻¹) =
        ∑ j ∈ Finset.range (M - (X₁ + 1)), ((((X₁ + 1 + j : ℕ) : ℝ)) ^ 2)⁻¹ := by
      have hIoo : Finset.Ioo X₁ M = Finset.Ico (X₁ + 1) (X₁ + 1 + (M - (X₁ + 1))) := by
        ext n; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
      rw [hIoo]
      exact Finset.sum_Ico_eq_sum_range (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) (X₁ + 1) (M - (X₁ + 1))
    rw [hbij]
    have htele := sum_range_inv_sq_shift_le hX₁ (M - (X₁ + 1))
    have hnonneg : (0 : ℝ) ≤ 1 / ((X₁ + (M - (X₁ + 1)) : ℕ) : ℝ) := by positivity
    linarith only [htele, hnonneg]

theorem sum_Icc_inv_sq_le_two_nat (X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, ((d : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have hsub : Finset.Icc 1 X ⊆ insert 1 (Finset.Ioo 1 (X + 1)) := by
    intro d hd
    obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hd
    rcases eq_or_lt_of_le hd1 with rfl | hgt
    · exact Finset.mem_insert_self 1 _
    · exact Finset.mem_insert_of_mem (Finset.mem_Ioo.mpr ⟨hgt, by omega⟩)
  calc (∑ d ∈ Finset.Icc 1 X, ((d : ℝ) ^ 2)⁻¹)
      ≤ ∑ d ∈ insert 1 (Finset.Ioo 1 (X + 1)), ((d : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (((1 : ℕ) : ℝ) ^ 2)⁻¹ + ∑ d ∈ Finset.Ioo 1 (X + 1), ((d : ℝ) ^ 2)⁻¹ :=
        Finset.sum_insert (by simp)
    _ ≤ 1 + 1 / (1 : ℝ) := by
        have htail := sum_Ioo_inv_sq_le_div (le_refl 1) (X + 1)
        norm_num at htail ⊢
        exact htail
    _ = 2 := by norm_num

theorem norm_zeta_mul_edPoly_three_le {b : ℕ → ℂ} {X : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B) {s : ℂ} (hs : s.re = 3) :
    ‖riemannZeta s * RHTower.edPoly b (Finset.Icc 1 X) s‖ ≤ 4 * B := by
  rw [norm_mul]
  have hz : ‖riemannZeta s‖ ≤ 2 := by
    have h := RHTower.Sieve.norm_riemannZeta_le (s := s) (by linarith)
    rw [hs] at h; linarith
  have hM : ‖RHTower.edPoly b (Finset.Icc 1 X) s‖ ≤ 2 * B := by
    unfold RHTower.edPoly
    calc ‖∑ d ∈ Finset.Icc 1 X, b d * ((d : ℝ) : ℂ) ^ (-s)‖
        ≤ ∑ d ∈ Finset.Icc 1 X, ‖b d * ((d : ℝ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 X, B * ((d : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
          rw [norm_mul, RHTower.norm_ofReal_natCast_cpow hd1, Complex.neg_re, hs]
          have hrp : (d : ℝ) ^ (-(3 : ℝ)) ≤ ((d : ℝ) ^ 2)⁻¹ := by
            have h1 : (d : ℝ) ^ (-(3 : ℝ)) ≤ (d : ℝ) ^ (-(2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) (by norm_num)
            have h2 : (d : ℝ) ^ (-(2 : ℝ)) = ((d : ℝ) ^ 2)⁻¹ := by
              rw [Real.rpow_neg hd0.le]; norm_num
            rwa [h2] at h1
          exact mul_le_mul (hb d hd) hrp (by positivity) hB
      _ = B * ∑ d ∈ Finset.Icc 1 X, ((d : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two_nat X) hB
      _ = 2 * B := by ring
  calc ‖riemannZeta s‖ * ‖RHTower.edPoly b (Finset.Icc 1 X) s‖
      ≤ 2 * (2 * B) := mul_le_mul hz hM (norm_nonneg _) (by norm_num)
    _ = 4 * B := by ring

theorem tsum_inv_sq_gt_le {X₁ : ℕ} (hX₁ : 1 ≤ X₁) :
    (∑' n : ℕ, if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else (0 : ℝ)) ≤ 2 / (X₁ : ℝ) := by
  have hg0 : ∀ n : ℕ, 0 ≤ (if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else (0 : ℝ)) :=
    fun n => by split_ifs <;> positivity
  have hgsum : Summable (fun n : ℕ => if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else (0 : ℝ)) := by
    refine Summable.of_nonneg_of_le hg0 (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    split_ifs
    · rw [one_div]
    · positivity
  refine hgsum.tsum_le_of_sum_le fun S => ?_
  have ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ S, n < M :=
    ⟨S.sup id + 1, fun n hn => Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  calc ∑ n ∈ S, (if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else 0)
      ≤ ∑ n ∈ Finset.range M, (if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Finset.mem_range.mpr (hM n hn)) (fun n _ _ => hg0 n)
    _ = ∑ n ∈ Finset.Ioo X₁ M, ((n : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.sum_filter]
        have hset : (Finset.range M).filter (fun n => X₁ < n) = Finset.Ioo X₁ M := by
          ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]; tauto
        rw [hset]
    _ ≤ 1 / (X₁ : ℝ) := sum_Ioo_inv_sq_le_div hX₁ M
    _ ≤ 2 / (X₁ : ℝ) := by
        have hX₁0 : (0 : ℝ) < X₁ := by exact_mod_cast hX₁
        exact div_le_div_of_nonneg_right (by norm_num) hX₁0.le

theorem tsum_tail_mollifiedZeta_cahenMellin_le {ρ₀ : ℂ} (hre : 1 / 2 ≤ ρ₀.re)
    {b : ℕ → ℂ} {X X₁ : ℕ} (hX₁ : 1 ≤ X₁) {B α u Y : ℝ} (hB : 0 ≤ B)
    (hb : ∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B) (hα : 0 < α) (hu : 0 < u) (hY : 1 ≤ Y)
    (hYX₁ : Y < (X₁ : ℝ)) (hslope : 5 * α ≤ Real.log (X₁ : ℝ) - Real.log Y) :
    Summable (fun n : ℕ => if X₁ < n then
        ‖RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
          cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖
      else 0) ∧
    (∑' n : ℕ, if X₁ < n then
        ‖RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
          cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖
      else 0) ≤
      2 * B * (Real.sqrt α / (Real.log (X₁ : ℝ) - Real.log Y)) *
        (X₁ : ℝ) ^ (3 / 2 : ℝ) *
        Real.exp (-(Real.log (X₁ : ℝ) - Real.log Y) ^ 2 / (4 * α)) := by
  have ⟨A₀, hA₀_def⟩ : ∃ a : ℝ, a = Real.log (X₁ : ℝ) - Real.log Y := ⟨_, rfl⟩
  rw [← hA₀_def] at hslope ⊢
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hX₁0 : (0 : ℝ) < X₁ := by exact_mod_cast hX₁
  have hA₀_pos : 0 < A₀ := by
    rw [hA₀_def]; linarith [Real.log_lt_log hY0 hYX₁]
  have ⟨K_tail, hK_def⟩ : ∃ k : ℝ,
      k = B * (Real.sqrt α / A₀) * (X₁ : ℝ) ^ (5 / 2 : ℝ) *
        Real.exp (-A₀ ^ 2 / (4 * α)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K_tail := by rw [hK_def]; positivity
  have hpt : ∀ n : ℕ,
      (if X₁ < n then
        ‖RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
          cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖
      else 0) ≤ K_tail * (if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else 0) := by
    intro n
    split_ifs with hXn
    · have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hXn_real : (X₁ : ℝ) < (n : ℝ) := by exact_mod_cast hXn
      have htn_nn : 0 ≤ Real.log ((n : ℝ) / (X₁ : ℝ)) :=
        Real.log_nonneg ((one_le_div hX₁0).mpr hXn_real.le)
      have hx_neg : Real.log Y - Real.log (n : ℝ) < 0 := by
        linarith [Real.log_lt_log hY0 (hYX₁.trans hXn_real)]
      have hcm := norm_cahenMellinGauss_neg_le hα hu hx_neg
      have hneg_eq : -(Real.log Y - Real.log (n : ℝ)) = A₀ + Real.log ((n : ℝ) / (X₁ : ℝ)) := by
        rw [hA₀_def, Real.log_div hn0.ne' hX₁0.ne']; ring
      have hspi_ge1 : 1 ≤ Real.sqrt Real.pi := by
        rw [Real.le_sqrt zero_le_one Real.pi_pos.le]; linarith [Real.pi_gt_three]
      have hden_ge : A₀ ≤ Real.sqrt Real.pi * -(Real.log Y - Real.log (n : ℝ)) := by
        rw [hneg_eq]
        nlinarith only [hA₀_pos, htn_nn, hspi_ge1]
      have hpref : Real.sqrt α / (Real.sqrt Real.pi * -(Real.log Y - Real.log (n : ℝ))) ≤
          Real.sqrt α / A₀ :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg α) hA₀_pos hden_ge
      have hexp_le : Real.exp (-(Real.log Y - Real.log (n : ℝ)) ^ 2 / (4 * α)) ≤
          Real.exp (-A₀ ^ 2 / (4 * α)) * ((n : ℝ) / (X₁ : ℝ)) ^ (-(5 / 2 : ℝ)) := by
        have hsq_eq : (Real.log Y - Real.log (n : ℝ)) ^ 2 =
            (A₀ + Real.log ((n : ℝ) / (X₁ : ℝ))) ^ 2 := by
          rw [← neg_sq (Real.log Y - Real.log (n : ℝ)), hneg_eq]
        rw [hsq_eq, Real.rpow_def_of_pos (div_pos hn0 hX₁0), ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h4a : 0 < 4 * α := by positivity
        rw [div_le_iff₀ h4a]
        have hrhs : (-A₀ ^ 2 / (4 * α) + Real.log ((n : ℝ) / (X₁ : ℝ)) * -(5 / 2 : ℝ)) * (4 * α) =
            -A₀ ^ 2 - 10 * α * Real.log ((n : ℝ) / (X₁ : ℝ)) := by
          field_simp [hα.ne']; ring
        rw [hrhs]
        have hsq_t : 0 ≤ (Real.log ((n : ℝ) / (X₁ : ℝ))) ^ 2 := sq_nonneg _
        nlinarith only [hslope, htn_nn, hsq_t]
      have hcm' : ‖cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖ ≤
          (Real.sqrt α / A₀) * Real.exp (-A₀ ^ 2 / (4 * α)) *
            ((n : ℝ) / (X₁ : ℝ)) ^ (-(5 / 2 : ℝ)) := by
        calc ‖cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖
            ≤ (Real.sqrt α / (Real.sqrt Real.pi * -(Real.log Y - Real.log (n : ℝ)))) *
                Real.exp (-(Real.log Y - Real.log (n : ℝ)) ^ 2 / (4 * α)) := hcm
          _ ≤ (Real.sqrt α / A₀) *
                (Real.exp (-A₀ ^ 2 / (4 * α)) * ((n : ℝ) / (X₁ : ℝ)) ^ (-(5 / 2 : ℝ))) :=
              mul_le_mul hpref hexp_le (Real.exp_pos _).le (by positivity)
          _ = _ := by ring
      have hc_norm : ‖RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀)‖ ≤
          B * (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [norm_mul, RHTower.norm_ofReal_natCast_cpow hn1, Complex.neg_re]
        exact mul_le_mul (norm_mollifiedZetaCoeff_le_mul_nat hB hb hn1)
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith))
          (by positivity) (by positivity)
      have hrpow_id : (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((n : ℝ) / (X₁ : ℝ)) ^ (-(5 / 2 : ℝ)) =
          (X₁ : ℝ) ^ (5 / 2 : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        rw [Real.div_rpow hn0.le hX₁0.le, Real.rpow_neg hX₁0.le, div_inv_eq_mul]
        have hn_prod : (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(5 / 2 : ℝ)) =
            ((n : ℝ) ^ 2)⁻¹ := by
          have h1 : (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(5 / 2 : ℝ)) =
              (n : ℝ) ^ ((1 : ℝ) + -(1 / 2 : ℝ) + -(5 / 2 : ℝ)) := by
            rw [Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one]
          rw [h1, show (1 : ℝ) + -(1 / 2 : ℝ) + -(5 / 2 : ℝ) = -(2 : ℝ) by norm_num,
            Real.rpow_neg hn0.le]
          norm_num
        calc (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
              ((n : ℝ) ^ (-(5 / 2 : ℝ)) * (X₁ : ℝ) ^ (5 / 2 : ℝ))
            = (X₁ : ℝ) ^ (5 / 2 : ℝ) *
                ((n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by ring
          _ = (X₁ : ℝ) ^ (5 / 2 : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by rw [hn_prod]
      rw [norm_mul, hK_def]
      calc ‖RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀)‖ *
            ‖cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖
          ≤ (B * (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) *
              ((Real.sqrt α / A₀) * Real.exp (-A₀ ^ 2 / (4 * α)) *
                ((n : ℝ) / (X₁ : ℝ)) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul hc_norm hcm' (norm_nonneg _) (by positivity)
        _ = B * (Real.sqrt α / A₀) * Real.exp (-A₀ ^ 2 / (4 * α)) *
              ((n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) / (X₁ : ℝ)) ^ (-(5 / 2 : ℝ))) := by
            ring
        _ = B * (Real.sqrt α / A₀) * (X₁ : ℝ) ^ (5 / 2 : ℝ) *
              Real.exp (-A₀ ^ 2 / (4 * α)) * ((n : ℝ) ^ 2)⁻¹ := by
            rw [hrpow_id]; ring
    · simp
  have hmaj_sum : Summable (fun n : ℕ => K_tail * (if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else 0)) := by
    refine Summable.mul_left K_tail (Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => ?_) (Real.summable_one_div_nat_pow.mpr one_lt_two))
    split_ifs
    · rw [one_div]
    · positivity
  have hlhs_sum : Summable (fun n : ℕ => if X₁ < n then
      ‖RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
        cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖ else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpt hmaj_sum
  refine ⟨hlhs_sum, ?_⟩
  calc (∑' n : ℕ, if X₁ < n then
        ‖RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
          cahenMellinGauss α u (Real.log Y - Real.log (n : ℝ))‖ else 0)
      ≤ ∑' n : ℕ, K_tail * (if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else 0) :=
        hlhs_sum.tsum_le_tsum hpt hmaj_sum
    _ = K_tail * ∑' n : ℕ, (if X₁ < n then ((n : ℝ) ^ 2)⁻¹ else 0) := tsum_mul_left
    _ ≤ K_tail * (2 / (X₁ : ℝ)) := mul_le_mul_of_nonneg_left (tsum_inv_sq_gt_le hX₁) hK0
    _ = 2 * B * (Real.sqrt α / A₀) * (X₁ : ℝ) ^ (3 / 2 : ℝ) *
          Real.exp (-A₀ ^ 2 / (4 * α)) := by
        rw [hK_def]
        have hxpow : (X₁ : ℝ) ^ (5 / 2 : ℝ) * (2 / (X₁ : ℝ)) = 2 * (X₁ : ℝ) ^ (3 / 2 : ℝ) := by
          rw [show (5 / 2 : ℝ) = (3 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hX₁0, Real.rpow_one]
          field_simp
        calc B * (Real.sqrt α / A₀) * (X₁ : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-A₀ ^ 2 / (4 * α)) *
              (2 / (X₁ : ℝ))
            = B * (Real.sqrt α / A₀) * Real.exp (-A₀ ^ 2 / (4 * α)) *
                ((X₁ : ℝ) ^ (5 / 2 : ℝ) * (2 / (X₁ : ℝ))) := by ring
          _ = 2 * B * (Real.sqrt α / A₀) * (X₁ : ℝ) ^ (3 / 2 : ℝ) *
                Real.exp (-A₀ ^ 2 / (4 * α)) := by rw [hxpow]; ring

theorem continuous_riemannZeta_comp {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hne1 : ∀ t, φ t ≠ 1) : Continuous (fun t => riemannZeta (φ t)) :=
  continuous_iff_continuousAt.mpr fun t =>
    ContinuousAt.comp (g := riemannZeta) (f := φ)
      (differentiableAt_riemannZeta (hne1 t)).continuousAt hφ.continuousAt

/-- **Localized critical-line spike from a single off-line zero (`Re ρ₀ > 1/2`).**
Every off-line zero `ρ₀` of `ζ` in the upper half-plane (`ρ₀.im ≥ R + 1`) forces the localized
critical-line second moment of `ζ Ψ` on `[ρ₀.im - R, ρ₀.im + R]` to be at least
`(3/4) (ρ₀.re - 1/2) exp(-2 α (ρ₀.re - 1/2)²) Y^{2(ρ₀.re - 1/2)}` whenever the `2 ≤ n ≤ X₁`
coefficients, the `n > X₁` Gaussian tail, and the rectangle truncation tails are bounded. -/
theorem integral_normSq_zetaMollified_criticalLine_spike_of_zero
    {ρ₀ : ℂ} (hζ0 : riemannZeta ρ₀ = 0) (hre : 1 / 2 < ρ₀.re)
    {R α Y B : ℝ} (hR1 : 1 ≤ R) (hRγ : R + 1 ≤ ρ₀.im)
    (hα : 0 < α) (hY : 1 ≤ Y) (hYα : 2 * Real.sqrt α ≤ Real.log Y) (hB : 1 ≤ B)
    {X X₁ : ℕ} (hX : 1 ≤ X) (hX₁ : 1 ≤ X₁) (hYX₁ : Y < (X₁ : ℝ))
    (hslope : 5 * α ≤ Real.log (X₁ : ℝ) - Real.log Y)
    {b : ℕ → ℂ} (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B)
    (hshort : ∑ n ∈ Finset.Icc 2 X₁,
      ‖RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-ρ₀.re) ≤ 1 / 8)
    (htail : 2 * B * (Real.sqrt α / (Real.log (X₁ : ℝ) - Real.log Y)) *
      (X₁ : ℝ) ^ (3 / 2 : ℝ) *
      Real.exp (-(Real.log (X₁ : ℝ) - Real.log Y) ^ 2 / (4 * α)) ≤ 1 / 12)
    (hvtail : 4 * B * (1 / Real.sqrt α) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) ≤ 1 / 12)
    (hhoriz : 5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) ≤ 1 / 12) :
    (3 / 4 : ℝ) * (ρ₀.re - 1 / 2) * Real.exp (-2 * α * (ρ₀.re - 1 / 2) ^ 2) *
        Y ^ (2 * (ρ₀.re - 1 / 2)) ≤
      ∫ t in (ρ₀.im - R)..(ρ₀.im + R),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hre_lt1 : ρ₀.re < 1 := RHTower.riemannZeta_zero_re_lt_one hζ0
  have ⟨δ₀, hδ₀_def⟩ : ∃ d : ℝ, d = ρ₀.re - 1 / 2 := ⟨_, rfl⟩
  have hδ₀_pos : 0 < δ₀ := by linarith
  have hδ₀_lt : δ₀ < 1 / 2 := by linarith
  have ⟨u_R, hu_R_def⟩ : ∃ u : ℝ, u = 3 - ρ₀.re := ⟨_, rfl⟩
  have hu_R_gt2 : 2 < u_R := by linarith
  have hu_R_lt : u_R < 5 / 2 := by linarith
  have hu_R_pos : 0 < u_R := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hB0 : 0 ≤ B := by linarith
  -- Step 1: Divided-difference contour shift on `[-δ₀, u_R] × [-R, R]`.
  have hrect := RHTower.Sieve.integral_vertical_sub_eq_horizontal_rect R
    (differentiableOn_dslope_mollifiedZetaGauss_rect hζ0 b X α Y
      (by linarith : -δ₀ < 0) hu_R_pos hR0 hRγ)
  have hv_right_eq : (∫ τ : ℝ in (-R)..R,
      dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((u_R : ℂ) + (τ : ℂ) * I)) =
      ∫ τ : ℝ in (-R)..R,
        riemannZeta (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) *
          RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) *
          cahenMellinGaussIntegrand α u_R (Real.log Y) τ := by
    refine intervalIntegral.integral_congr fun τ _ => ?_
    have hw0 : ((u_R : ℂ) + (τ : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [dslope_mollifiedZetaGauss_eq_div hζ0 b X α Y hw0]
    simp only [mollifiedZetaGauss, cahenMellinGaussIntegrand, mul_div_assoc]
  have hv_left_eq : (∫ τ : ℝ in (-R)..R,
      dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 (((-δ₀ : ℝ) : ℂ) + (τ : ℂ) * I)) =
      ∫ τ : ℝ in (-R)..R,
        riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
          cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ := by
    refine intervalIntegral.integral_congr fun τ _ => ?_
    have hw0 : (((-δ₀ : ℝ) : ℂ) + (τ : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [dslope_mollifiedZetaGauss_eq_div hζ0 b X α Y hw0]
    have hpt_s : ρ₀ + (((-δ₀ : ℝ) : ℂ) + (τ : ℂ) * I) =
        ((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [hδ₀_def]; ring
      · simp
    simp only [mollifiedZetaGauss, cahenMellinGaussIntegrand, hpt_s, mul_div_assoc]
  -- Step 2: Bound the top and bottom horizontal edges at `±R`.
  have hhoriz_edge : ∀ sgn : ℝ, |sgn| = R →
      ‖∫ σ : ℝ in (-δ₀)..u_R,
        dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((σ : ℂ) + (sgn : ℂ) * I)‖ ≤
        (5 / 2) * (5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
          Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2)) := by
    intro sgn hsgn
    have hcd : -δ₀ ≤ u_R := by linarith
    have hwidth : |u_R - (-δ₀)| = 5 / 2 := by
      rw [abs_of_pos (by linarith), hu_R_def, hδ₀_def]; ring
    have hpt_bound : ∀ σ ∈ Set.uIoc (-δ₀) u_R,
        ‖dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((σ : ℂ) + (sgn : ℂ) * I)‖ ≤
          5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
            Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) := by
      intro σ hσ_mem
      have hσ_Icc := Set.uIoc_subset_uIcc hσ_mem
      rw [Set.uIcc_of_le hcd] at hσ_Icc
      obtain ⟨hσ_lo, hσ_hi⟩ := hσ_Icc
      have hw0 : ((σ : ℂ) + (sgn : ℂ) * I) ≠ 0 := by
        intro h
        have := congrArg Complex.im h; simp at this
        rw [this, abs_zero] at hsgn; linarith
      rw [dslope_mollifiedZetaGauss_eq_div hζ0 b X α Y hw0]
      unfold mollifiedZetaGauss
      rw [norm_div, norm_mul, norm_mul, norm_exp_quad_add_lin]
      have hw_norm_ge1 : 1 ≤ ‖(σ : ℂ) + (sgn : ℂ) * I‖ := by
        have := norm_add_mul_I_ge_abs_right σ sgn
        rw [hsgn] at this; linarith
      have hs_re : 1 / 2 ≤ (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)).re := by
        simp; linarith [hδ₀_def]
      have hs_re3 : (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)).re ≤ 3 := by
        simp; linarith [hu_R_def]
      have hs_im_ge1 : 1 ≤ (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)).im := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
        have := neg_abs_le sgn; rw [hsgn] at this; linarith
      have hs_sep1 : 1 ≤ ‖(ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)) - 1‖ := by
        have h1 := Complex.abs_im_le_norm ((ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)) - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at h1
        exact le_trans hs_im_ge1 ((le_abs_self _).trans h1)
      have hz_le : ‖riemannZeta (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I))‖ ≤
          5 * Real.sqrt (ρ₀.im + R + 6) := by
        have h1 := RHTower.norm_riemannZeta_le_sqrt_norm_add_two_half hs_re zero_lt_one hs_sep1
        rw [show (2 + 1 / (1 : ℝ) + 2 : ℝ) = 5 by norm_num] at h1
        refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
        have h2 := Complex.norm_le_abs_re_add_abs_im (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I))
        have hre_abs : |(ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)).re| ≤ 3 :=
          abs_le.mpr ⟨by linarith, hs_re3⟩
        have him_abs : |(ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)).im| ≤ ρ₀.im + R := by
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
          have := le_abs_self sgn; have := neg_abs_le sgn; rw [hsgn] at *
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      have hed_le : ‖RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I))‖ ≤
          B * (X : ℝ) := by
        unfold RHTower.edPoly
        calc ‖∑ d ∈ Finset.Icc 1 X, b d * ((d : ℝ) : ℂ) ^ (-(ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)))‖
            ≤ ∑ d ∈ Finset.Icc 1 X,
                ‖b d * ((d : ℝ) : ℂ) ^ (-(ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)))‖ := norm_sum_le _ _
          _ ≤ ∑ _d ∈ Finset.Icc 1 X, B := by
              refine Finset.sum_le_sum fun d hd => ?_
              have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
              rw [norm_mul, RHTower.norm_ofReal_natCast_cpow hd1, Complex.neg_re]
              have hrp : (d : ℝ) ^ (-(ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)).re) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by linarith)
              calc ‖b d‖ * (d : ℝ) ^ (-(ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I)).re)
                  ≤ B * 1 := mul_le_mul (hb d hd) hrp (by positivity) hB0
                _ = B := mul_one B
          _ = B * (X : ℝ) := by simp [mul_comm]
      have hexp_le : Real.exp (α * (σ ^ 2 - sgn ^ 2) + Real.log Y * σ) ≤
          Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hsgn_sq : sgn ^ 2 = R ^ 2 := by rw [← sq_abs sgn, hsgn]
        have hσ_abs : |σ| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hσ_sq : σ ^ 2 ≤ 25 / 4 := by
          have := pow_le_pow_left₀ (abs_nonneg σ) hσ_abs 2
          rw [sq_abs] at this; linarith
        have hlogY_σ : Real.log Y * σ ≤ (5 / 2) * Real.log Y := by
          nlinarith only [hlogY0, hσ_hi, hu_R_lt]
        rw [hsgn_sq]
        nlinarith only [hα, hσ_sq, hlogY_σ]
      calc ‖riemannZeta (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I))‖ *
            ‖RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I))‖ *
            Real.exp (α * (σ ^ 2 - sgn ^ 2) + Real.log Y * σ) /
            ‖(σ : ℂ) + (sgn : ℂ) * I‖
          ≤ ‖riemannZeta (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I))‖ *
              ‖RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + ((σ : ℂ) + (sgn : ℂ) * I))‖ *
              Real.exp (α * (σ ^ 2 - sgn ^ 2) + Real.log Y * σ) / 1 :=
            div_le_div_of_nonneg_left (by positivity) zero_lt_one hw_norm_ge1
        _ ≤ (5 * Real.sqrt (ρ₀.im + R + 6)) * (B * (X : ℝ)) *
              Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) := by
            rw [div_one]
            exact mul_le_mul (mul_le_mul hz_le hed_le (norm_nonneg _) (by positivity)) hexp_le
              (Real.exp_pos _).le (by positivity)
        _ = 5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
              Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) := by ring
    have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const hpt_bound
    rw [hwidth] at hint_le
    linarith
  have hhoriz_sum : (1 / (2 * Real.pi)) *
      ‖(∫ τ : ℝ in (-R)..R,
          riemannZeta (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) *
            RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) *
            cahenMellinGaussIntegrand α u_R (Real.log Y) τ) -
        (∫ τ : ℝ in (-R)..R,
          riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
            RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
            cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ)‖ ≤ 1 / 12 := by
    rw [← hv_right_eq, ← hv_left_eq]
    have hI_eq : ‖(∫ τ : ℝ in (-R)..R,
          dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((u_R : ℂ) + (τ : ℂ) * I)) -
        (∫ τ : ℝ in (-R)..R,
          dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 (((-δ₀ : ℝ) : ℂ) + (τ : ℂ) * I))‖ =
      ‖(∫ σ : ℝ in (-δ₀)..u_R,
          dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((σ : ℂ) + ((R : ℝ) : ℂ) * I)) -
        (∫ σ : ℝ in (-δ₀)..u_R,
          dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((σ : ℂ) + ((-R : ℝ) : ℂ) * I))‖ := by
      rw [← hrect, ← smul_sub, norm_smul, Complex.norm_I, one_mul]
    rw [hI_eq]
    have htop := hhoriz_edge R (abs_of_pos hR0)
    have hbot := hhoriz_edge (-R) (by rw [abs_neg, abs_of_pos hR0])
    have h5_2pi : (1 / (2 * Real.pi)) * (5 : ℝ) ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ (by positivity), mul_one]
      linarith [Real.pi_gt_three]
    calc (1 / (2 * Real.pi)) *
          ‖(∫ σ : ℝ in (-δ₀)..u_R,
              dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((σ : ℂ) + ((R : ℝ) : ℂ) * I)) -
            (∫ σ : ℝ in (-δ₀)..u_R,
              dslope (mollifiedZetaGauss ρ₀ b X α Y) 0 ((σ : ℂ) + ((-R : ℝ) : ℂ) * I))‖
        ≤ (1 / (2 * Real.pi)) *
            ((5 / 2 + 5 / 2) * (5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
              Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
          linarith
      _ = ((1 / (2 * Real.pi)) * 5) *
            (5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
              Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2)) := by ring
      _ ≤ 1 * (1 / 12) := mul_le_mul h5_2pi hhoriz (by positivity) zero_le_one
      _ = 1 / 12 := one_mul _
  -- Step 3: Extend the right-edge integral at `Re(ρ₀ + w) = 3` from `[-R, R]` to `ℝ`.
  have ⟨g_right, hg_right_def⟩ : ∃ f : ℝ → ℂ, f = fun (τ : ℝ) =>
      riemannZeta (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) *
        RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) *
        cahenMellinGaussIntegrand α u_R (Real.log Y) τ := ⟨_, rfl⟩
  have hg_right_re : ∀ τ : ℝ, (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)).re = 3 := by
    intro τ; simp [hu_R_def]
  have hg_right_norm : ∀ τ : ℝ, ‖g_right τ‖ ≤
      4 * B * (Real.exp (α * u_R ^ 2 + Real.log Y * u_R) / u_R) * Real.exp (-α * τ ^ 2) := by
    intro τ
    rw [hg_right_def, norm_mul]
    have h1 := norm_zeta_mul_edPoly_three_le hB0 hb (hg_right_re τ)
    have h2 := norm_cahenMellinGaussIntegrand_le (x := Real.log Y) (τ := τ) hu_R_pos.ne'
    rw [abs_of_pos hu_R_pos] at h2
    calc ‖riemannZeta (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) *
            RHTower.edPoly b (Finset.Icc 1 X) (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I))‖ *
          ‖cahenMellinGaussIntegrand α u_R (Real.log Y) τ‖
        ≤ (4 * B) * ((Real.exp (α * u_R ^ 2 + Real.log Y * u_R) / u_R) *
            Real.exp (-α * τ ^ 2)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hg_right_cont : Continuous g_right := by
    rw [hg_right_def]
    have hne1 : ∀ τ : ℝ, ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I) ≠ 1 := by
      intro τ h
      have := congrArg Complex.re h
      rw [hg_right_re τ] at this; norm_num at this
    have hsX : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
    refine Continuous.mul (Continuous.mul ?_ ?_)
      (continuous_cahenMellinGaussIntegrand hu_R_pos.ne')
    · exact continuous_riemannZeta_comp (by fun_prop) hne1
    · exact (RHTower.differentiable_edPoly b hsX).continuous.comp (by fun_prop)
  have hg_right_int : Integrable g_right :=
    ((integrable_exp_neg_mul_sq hα).const_mul _).mono' hg_right_cont.aestronglyMeasurable
      (Eventually.of_forall hg_right_norm)
  have hvtail_bound : (1 / (2 * Real.pi)) *
      ‖(∫ τ : ℝ, g_right τ) - (∫ τ : ℝ in (-R)..R, g_right τ)‖ ≤ 1 / 12 := by
    rw [intervalIntegral.integral_of_le (by linarith),
      ← integral_add_compl (measurableSet_Ioc (a := -R) (b := R)) hg_right_int,
      add_sub_cancel_left]
    have ⟨B_vt, hB_vt_def⟩ : ∃ f : ℝ → ℝ, f = fun (τ : ℝ) =>
        2 * B * Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) *
          Real.exp (-(α / 2) * τ ^ 2) := ⟨_, rfl⟩
    have hB_vt_int : Integrable B_vt := by
      rw [hB_vt_def]; exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _
    have hpt_vt : ∀ τ ∈ (Set.Ioc (-R) R)ᶜ, ‖g_right τ‖ ≤ B_vt τ := by
      intro τ hτ
      have hR2 : R ^ 2 ≤ τ ^ 2 := by
        simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hτ
        rcases hτ with h | h <;> nlinarith
      have hbase := hg_right_norm τ
      have hu_inv : 1 / u_R ≤ 1 / 2 := one_div_le_one_div_of_le zero_lt_two hu_R_gt2.le
      have hexp_vt : Real.exp (α * u_R ^ 2 + Real.log Y * u_R) * Real.exp (-α * τ ^ 2) ≤
          Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) *
            Real.exp (-(α / 2) * τ ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hu2 : u_R ^ 2 ≤ 25 / 4 := by nlinarith only [hu_R_pos, hu_R_lt]
        have hyu : Real.log Y * u_R ≤ (5 / 2) * Real.log Y := by
          nlinarith only [hlogY0, hu_R_lt]
        nlinarith only [hα, hu2, hyu, hR2]
      rw [hB_vt_def]
      calc ‖g_right τ‖
          ≤ 4 * B * (1 / u_R) *
              (Real.exp (α * u_R ^ 2 + Real.log Y * u_R) * Real.exp (-α * τ ^ 2)) := by
            linarith [show 4 * B * (Real.exp (α * u_R ^ 2 + Real.log Y * u_R) / u_R) *
                Real.exp (-α * τ ^ 2) =
              4 * B * (1 / u_R) *
                (Real.exp (α * u_R ^ 2 + Real.log Y * u_R) * Real.exp (-α * τ ^ 2)) by ring]
        _ ≤ 4 * B * (1 / 2) *
              (Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) *
                Real.exp (-(α / 2) * τ ^ 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hu_inv (by positivity)) hexp_vt
              (by positivity) (by positivity)
        _ = _ := by ring
    have hint_compl : ‖∫ τ in (Set.Ioc (-R) R)ᶜ, g_right τ‖ ≤ ∫ τ : ℝ, B_vt τ := by
      calc ‖∫ τ in (Set.Ioc (-R) R)ᶜ, g_right τ‖
          ≤ ∫ τ in (Set.Ioc (-R) R)ᶜ, ‖g_right τ‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ τ in (Set.Ioc (-R) R)ᶜ, B_vt τ :=
            setIntegral_mono_on hg_right_int.norm.integrableOn hB_vt_int.integrableOn
              measurableSet_Ioc.compl hpt_vt
        _ ≤ ∫ τ : ℝ, B_vt τ :=
            setIntegral_le_integral hB_vt_int
              (Eventually.of_forall fun τ => by rw [hB_vt_def]; positivity)
    have hint_eval : ∫ τ : ℝ, B_vt τ =
        2 * B * Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) *
          Real.sqrt (2 * Real.pi / α) := by
      rw [hB_vt_def, integral_const_mul, integral_gaussian]
      congr 2; field_simp [hα.ne']; ring
    rw [hint_eval] at hint_compl
    have hcoeff : (1 / (2 * Real.pi)) * Real.sqrt (2 * Real.pi / α) ≤ 2 * (1 / Real.sqrt α) := by
      rw [Real.sqrt_div (by positivity)]
      have hsp : Real.sqrt (2 * Real.pi) ≤ 4 * Real.pi := by
        have h1 : 2 * Real.pi ≤ (4 * Real.pi) ^ 2 := by
          have := Real.pi_gt_three; nlinarith
        exact (Real.sqrt_le_iff.mpr ⟨by positivity, h1⟩)
      have hdiv : Real.sqrt (2 * Real.pi) / (2 * Real.pi) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      calc (1 / (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) / Real.sqrt α)
          = (Real.sqrt (2 * Real.pi) / (2 * Real.pi)) * (1 / Real.sqrt α) := by ring
        _ ≤ 2 * (1 / Real.sqrt α) := mul_le_mul_of_nonneg_right hdiv (by positivity)
    calc (1 / (2 * Real.pi)) * ‖∫ τ in (Set.Ioc (-R) R)ᶜ, g_right τ‖
        ≤ (1 / (2 * Real.pi)) *
            (2 * B * Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) *
              Real.sqrt (2 * Real.pi / α)) :=
          mul_le_mul_of_nonneg_left hint_compl (by positivity)
      _ = 2 * B * Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) *
            ((1 / (2 * Real.pi)) * Real.sqrt (2 * Real.pi / α)) := by ring
      _ ≤ 2 * B * Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) *
            (2 * (1 / Real.sqrt α)) :=
          mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = 4 * B * (1 / Real.sqrt α) *
            Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) := by ring
      _ ≤ 1 / 12 := hvtail
  -- Step 4: Termwise Dirichlet-series expansion of `(2π)⁻¹ ∫_ℝ g_right τ dτ` on `Re(ρ₀ + w) = 3`.
  have hterm_id : ∀ (n : ℕ) (τ : ℝ), 1 ≤ n →
      LSeries.term (RHTower.mollifiedZetaCoeff b X) (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) n *
        cahenMellinGaussIntegrand α u_R (Real.log Y) τ =
      RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
        cahenMellinGaussIntegrand α u_R (Real.log Y - Real.log (n : ℝ)) τ := by
    intro n τ hn1
    have hn0 : n ≠ 0 := by omega
    rw [LSeries.term_of_ne_zero hn0, ← Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv,
      ← Complex.cpow_neg, neg_neg, show -(ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) =
        -ρ₀ + -((u_R : ℂ) + (τ : ℂ) * I) by ring]
    rw [RHTower.ofReal_natCast_cpow_eq_exp hn1, RHTower.ofReal_natCast_cpow_eq_exp hn1,
      Complex.exp_add]
    unfold cahenMellinGaussIntegrand
    rw [mul_assoc, mul_div_assoc', ← mul_div_assoc]
    congr 1
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hhasSum_line : HasSum
      (fun n : ℕ => if n = 0 then 0 else
        RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
          cahenMellinGauss α u_R (Real.log Y - Real.log (n : ℝ)))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, g_right τ) := by
    have ⟨F_term, hF_term_def⟩ : ∃ F : ℕ → ℝ → ℂ, F = fun (n : ℕ) (τ : ℝ) =>
        LSeries.term (RHTower.mollifiedZetaCoeff b X) (ρ₀ + ((u_R : ℂ) + (τ : ℂ) * I)) n *
          cahenMellinGaussIntegrand α u_R (Real.log Y) τ := ⟨_, rfl⟩
    have hF_int : ∀ n : ℕ, Integrable (F_term n) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h0 : F_term 0 = fun _ => 0 := by ext τ; simp [hF_term_def]
        rw [h0]; exact integrable_zero _ _ _
      · have heq_n : F_term n = fun τ =>
            (RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀)) *
              cahenMellinGaussIntegrand α u_R (Real.log Y - Real.log (n : ℝ)) τ := by
          ext τ; rw [hF_term_def, hterm_id n τ hn]
        rw [heq_n]
        exact (integrable_cahenMellinGaussIntegrand hα hu_R_pos.ne').const_mul _
    have hF_sum_norm : Summable (fun n : ℕ => ∫ τ : ℝ, ‖F_term n τ‖) := by
      have ⟨C_int, hC_int_def⟩ : ∃ c : ℝ, c =
          (Real.exp (α * u_R ^ 2 + Real.log Y * u_R) / u_R) * Real.sqrt (Real.pi / α) := ⟨_, rfl⟩
      have hC_int0 : 0 ≤ C_int := by rw [hC_int_def]; positivity
      refine Summable.of_nonneg_of_le
        (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
        ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (B * C_int))
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h0 : (fun τ => ‖F_term 0 τ‖) = fun _ => 0 := by ext τ; simp [hF_term_def]
        simp [h0]; positivity
      · have hn1 : 1 ≤ n := hn
        have hpt_n : ∀ τ : ℝ, ‖F_term n τ‖ ≤
            (B * (1 / (n : ℝ) ^ 2)) *
              ((Real.exp (α * u_R ^ 2 + Real.log Y * u_R) / u_R) * Real.exp (-α * τ ^ 2)) := by
          intro τ
          rw [hF_term_def, norm_mul, LSeries.norm_term_eq, if_neg hn.ne', hg_right_re τ]
          have hc := norm_mollifiedZetaCoeff_le_mul_nat hB0 hb hn1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          have hdiv_n : ‖RHTower.mollifiedZetaCoeff b X n‖ / (n : ℝ) ^ (3 : ℝ) ≤
              B * (1 / (n : ℝ) ^ 2) := by
            have hr3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) * (n : ℝ) ^ 2 := by
              rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]; ring
            rw [hr3, div_le_iff₀ (by positivity)]
            calc ‖RHTower.mollifiedZetaCoeff b X n‖ ≤ B * (n : ℝ) := hc
              _ = B * (1 / (n : ℝ) ^ 2) * ((n : ℝ) * (n : ℝ) ^ 2) := by field_simp; ring
          have hcm_n := norm_cahenMellinGaussIntegrand_le (α := α) (x := Real.log Y) (τ := τ)
            hu_R_pos.ne'
          rw [abs_of_pos hu_R_pos] at hcm_n
          exact mul_le_mul hdiv_n hcm_n (norm_nonneg _) (by positivity)
        calc ∫ τ : ℝ, ‖F_term n τ‖
            ≤ ∫ τ : ℝ, (B * (1 / (n : ℝ) ^ 2)) *
                ((Real.exp (α * u_R ^ 2 + Real.log Y * u_R) / u_R) * Real.exp (-α * τ ^ 2)) :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                (((integrable_exp_neg_mul_sq hα).const_mul _).const_mul _)
                (Eventually.of_forall hpt_n)
          _ = B * C_int * (1 / (n : ℝ) ^ 2) := by
              rw [integral_const_mul, integral_const_mul, integral_gaussian, hC_int_def]; ring
    have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm hF_int hF_sum_norm
    have hg_tsum : ∀ τ : ℝ, g_right τ = ∑' n : ℕ, F_term n τ := by
      intro τ
      have h1 := (hasSum_mollifiedZeta_of_one_lt_re b X
        (by rw [hg_right_re τ]; norm_num)).mul_right
        (cahenMellinGaussIntegrand α u_R (Real.log Y) τ)
      rw [hg_right_def, ← h1.tsum_eq]
      congr 1; ext n; rw [hF_term_def]
    rw [integral_congr_ae (Eventually.of_forall hg_tsum)]
    have hHS' := hHS.mul_left ((1 / (2 * Real.pi) : ℝ) : ℂ)
    refine hHS'.congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF_term_def]
    · rw [if_neg hn.ne']
      have heq_n : (∫ τ : ℝ, F_term n τ) =
          (RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀)) *
            ∫ τ : ℝ, cahenMellinGaussIntegrand α u_R (Real.log Y - Real.log (n : ℝ)) τ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
        rw [hF_term_def, hterm_id n τ hn]
      rw [heq_n]
      unfold cahenMellinGauss
      ring
  -- Step 5: Isolate `n = 1` (`≥ 3/4`) and bound `2 ≤ n ≤ X₁` (`≤ 1/4`) + `n > X₁` (`≤ 1/12`).
  have hline_re_ge : 5 / 12 ≤ (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, g_right τ).re := by
    have ⟨a_seq, ha_def⟩ : ∃ f : ℕ → ℂ, f = fun (n : ℕ) => if n = 0 then 0 else
        RHTower.mollifiedZetaCoeff b X n * ((n : ℝ) : ℂ) ^ (-ρ₀) *
          cahenMellinGauss α u_R (Real.log Y - Real.log (n : ℝ)) := ⟨_, rfl⟩
    rw [← ha_def] at hhasSum_line
    have ha_sum : Summable a_seq := hhasSum_line.summable
    have hsplit : (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, g_right τ) =
        ∑ n ∈ Finset.range (X₁ + 1), a_seq n + ∑' n : ℕ, a_seq (n + (X₁ + 1)) := by
      rw [← hhasSum_line.tsum_eq, ← ha_sum.sum_add_tsum_nat_add (X₁ + 1)]
    have ha0 : a_seq 0 = 0 := by simp [ha_def]
    have ha1 : a_seq 1 = cahenMellinGauss α u_R (Real.log Y) := by
      rw [ha_def, if_neg one_ne_zero, RHTower.mollifiedZetaCoeff_one hX, hb1]
      simp
    have hfin_split : ∑ n ∈ Finset.range (X₁ + 1), a_seq n =
        cahenMellinGauss α u_R (Real.log Y) + ∑ n ∈ Finset.Icc 2 X₁, a_seq n := by
      have hset : Finset.range (X₁ + 1) = insert 0 (insert 1 (Finset.Icc 2 X₁)) := by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ha0, zero_add, ha1]
    have hshort_norm : ‖∑ n ∈ Finset.Icc 2 X₁, a_seq n‖ ≤ 1 / 4 := by
      calc ‖∑ n ∈ Finset.Icc 2 X₁, a_seq n‖
          ≤ ∑ n ∈ Finset.Icc 2 X₁, ‖a_seq n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Icc 2 X₁,
              2 * (‖RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-ρ₀.re)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
            rw [ha_def, if_neg (by omega), norm_mul, norm_mul,
              RHTower.norm_ofReal_natCast_cpow (by omega), Complex.neg_re]
            have hcm2 := norm_cahenMellinGauss_le_two hα hu_R_pos (Real.log Y - Real.log (n : ℝ))
            have := mul_le_mul_of_nonneg_left hcm2
              (mul_nonneg (norm_nonneg (RHTower.mollifiedZetaCoeff b X n))
                (Real.rpow_nonneg (Nat.cast_nonneg n) (-ρ₀.re)))
            linarith
        _ = 2 * ∑ n ∈ Finset.Icc 2 X₁,
              ‖RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-ρ₀.re) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ 2 * (1 / 8) := mul_le_mul_of_nonneg_left hshort (by norm_num)
        _ = 1 / 4 := by norm_num
    have htail_norm : ‖∑' n : ℕ, a_seq (n + (X₁ + 1))‖ ≤ 1 / 12 := by
      obtain ⟨hg_sum, hg_le⟩ := tsum_tail_mollifiedZeta_cahenMellin_le hre.le hX₁ hB0 hb hα
        hu_R_pos hY hYX₁ hslope
      have ha_shift_eq : (fun n : ℕ => ‖a_seq (n + (X₁ + 1))‖) =
          (fun n : ℕ => (fun m : ℕ => if X₁ < m then
            ‖RHTower.mollifiedZetaCoeff b X m * ((m : ℝ) : ℂ) ^ (-ρ₀) *
              cahenMellinGauss α u_R (Real.log Y - Real.log (m : ℝ))‖ else 0) (n + (X₁ + 1))) := by
        ext n
        have hgt : X₁ < n + (X₁ + 1) := by omega
        have hne0 : n + (X₁ + 1) ≠ 0 := by omega
        simp only [ha_def, if_neg hne0, if_pos hgt]
      have ha_norm_sum : Summable (fun n : ℕ => ‖a_seq (n + (X₁ + 1))‖) := by
        rw [ha_shift_eq]
        exact (summable_nat_add_iff (X₁ + 1)).mpr hg_sum
      have htsum_eq : (∑' n : ℕ, ‖a_seq (n + (X₁ + 1))‖) =
          ∑' m : ℕ, (if X₁ < m then
            ‖RHTower.mollifiedZetaCoeff b X m * ((m : ℝ) : ℂ) ^ (-ρ₀) *
              cahenMellinGauss α u_R (Real.log Y - Real.log (m : ℝ))‖ else 0) := by
        have hsplit_g := hg_sum.sum_add_tsum_nat_add (X₁ + 1)
        have hzero_head : (∑ m ∈ Finset.range (X₁ + 1), if X₁ < m then
            ‖RHTower.mollifiedZetaCoeff b X m * ((m : ℝ) : ℂ) ^ (-ρ₀) *
              cahenMellinGauss α u_R (Real.log Y - Real.log (m : ℝ))‖ else 0) = 0 := by
          refine Finset.sum_eq_zero fun m hm => ?_
          rw [if_neg (by have := Finset.mem_range.mp hm; omega)]
        rw [hzero_head, zero_add] at hsplit_g
        rw [ha_shift_eq, hsplit_g]
      exact (norm_tsum_le_tsum_norm ha_norm_sum).trans (htsum_eq.le.trans (hg_le.trans htail))
    have hmain_re : 3 / 4 ≤ (cahenMellinGauss α u_R (Real.log Y)).re :=
      re_cahenMellinGauss_ge_of_two_mul_sqrt_le hα hu_R_pos hYα
    rw [hsplit, hfin_split, Complex.add_re, Complex.add_re]
    have h1 : -(1 / 4 : ℝ) ≤ (∑ n ∈ Finset.Icc 2 X₁, a_seq n).re := by
      have := neg_abs_le (∑ n ∈ Finset.Icc 2 X₁, a_seq n).re
      have h2 := (Complex.abs_re_le_norm (∑ n ∈ Finset.Icc 2 X₁, a_seq n)).trans hshort_norm
      linarith
    have h2 : -(1 / 12 : ℝ) ≤ (∑' n : ℕ, a_seq (n + (X₁ + 1))).re := by
      have := neg_abs_le (∑' n : ℕ, a_seq (n + (X₁ + 1))).re
      have h3 := (Complex.abs_re_le_norm (∑' n : ℕ, a_seq (n + (X₁ + 1)))).trans htail_norm
      linarith
    linarith
  -- Step 6: Combine Steps 2, 3, 5 on the critical-line edge and apply Cauchy–Schwarz.
  have hleft_norm_ge : 1 / 4 ≤
      (1 / (2 * Real.pi)) *
        ‖∫ τ : ℝ in (-R)..R,
          riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
            RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
            cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ‖ := by
    have ⟨I_full, hI_full⟩ : ∃ z : ℂ, z = ∫ τ : ℝ, g_right τ := ⟨_, rfl⟩
    have ⟨I_rR, hI_rR⟩ : ∃ z : ℂ, z = ∫ τ : ℝ in (-R)..R, g_right τ := ⟨_, rfl⟩
    have ⟨I_lR, hI_lR⟩ : ∃ z : ℂ, z = ∫ τ : ℝ in (-R)..R,
        riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
          cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ := ⟨_, rfl⟩
    have hfull_norm : 5 / 12 ≤ (1 / (2 * Real.pi)) * ‖I_full‖ := by
      rw [← hI_full] at hline_re_ge
      have hre_le := (le_abs_self (((1 / (2 * Real.pi) : ℝ) : ℂ) * I_full).re).trans
        (Complex.abs_re_le_norm (((1 / (2 * Real.pi) : ℝ) : ℂ) * I_full))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hre_le
      exact hline_re_ge.trans hre_le
    have hvtail' : (1 / (2 * Real.pi)) * ‖I_full - I_rR‖ ≤ 1 / 12 := by
      rwa [← hI_full, ← hI_rR] at hvtail_bound
    have hhoriz' : (1 / (2 * Real.pi)) * ‖I_rR - I_lR‖ ≤ 1 / 12 := by
      rw [← hg_right_def] at hhoriz_sum
      rwa [← hI_rR, ← hI_lR] at hhoriz_sum
    have htri : ‖I_full‖ ≤ ‖I_full - I_rR‖ + ‖I_rR - I_lR‖ + ‖I_lR‖ := by
      have h1 := norm_add_le (I_full - I_rR) (I_rR - I_lR)
      have h2 := norm_add_le (I_full - I_lR) I_lR
      have eq1 : (I_full - I_rR) + (I_rR - I_lR) = I_full - I_lR := by ring
      have eq2 : (I_full - I_lR) + I_lR = I_full := by ring
      rw [eq1] at h1; rw [eq2] at h2; linarith
    have htri' := mul_le_mul_of_nonneg_left htri (by positivity : 0 ≤ 1 / (2 * Real.pi))
    rw [← hI_lR]
    linarith
  have ⟨A_fn, hA_def⟩ : ∃ f : ℝ → ℝ, f = fun (τ : ℝ) =>
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 X)
          (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I)‖ := ⟨_, rfl⟩
  have ⟨B_fn, hB_def⟩ : ∃ f : ℝ → ℝ, f = fun (τ : ℝ) => 1 / Real.sqrt (δ₀ ^ 2 + τ ^ 2) := ⟨_, rfl⟩
  have hA_cont : Continuous A_fn := by
    rw [hA_def]
    have hne1 : ∀ τ : ℝ, (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) ≠ 1 := by
      intro τ h; have := congrArg Complex.re h; simp at this
    have hsX : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
    refine Continuous.norm (Continuous.mul ?_ ?_)
    · exact continuous_riemannZeta_comp (by fun_prop) hne1
    · exact (RHTower.differentiable_edPoly b hsX).continuous.comp (by fun_prop)
  have hB_cont : Continuous B_fn := by
    rw [hB_def]
    refine Continuous.div continuous_const (Continuous.sqrt (by fun_prop)) fun τ => ?_
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hcm_left_le : ∀ τ : ℝ,
      ‖cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ‖ ≤
        (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * B_fn τ := by
    intro τ
    unfold cahenMellinGaussIntegrand
    rw [norm_div, norm_exp_quad_add_lin, hB_def]
    have hnorm_den : ‖((-δ₀ : ℝ) : ℂ) + (τ : ℂ) * I‖ = Real.sqrt (δ₀ ^ 2 + τ ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
        zero_add]
      congr 1; ring
    rw [hnorm_den]
    have hexp_le : Real.exp (α * ((-δ₀) ^ 2 - τ ^ 2) + Real.log Y * (-δ₀)) ≤
        Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀) := by
      rw [Real.rpow_def_of_pos hY0, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ht2 : 0 ≤ α * τ ^ 2 := by positivity
      nlinarith only [ht2]
    calc Real.exp (α * ((-δ₀) ^ 2 - τ ^ 2) + Real.log Y * (-δ₀)) / Real.sqrt (δ₀ ^ 2 + τ ^ 2)
        = Real.exp (α * ((-δ₀) ^ 2 - τ ^ 2) + Real.log Y * (-δ₀)) *
            (1 / Real.sqrt (δ₀ ^ 2 + τ ^ 2)) := by ring
      _ ≤ (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * (1 / Real.sqrt (δ₀ ^ 2 + τ ^ 2)) :=
          mul_le_mul_of_nonneg_right hexp_le (by positivity)
  have ⟨J_int, hJ_def⟩ : ∃ j : ℝ, j = ∫ τ : ℝ in (-R)..R, A_fn τ * B_fn τ := ⟨_, rfl⟩
  have hJ_ge : (Real.pi / 2) * Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀ ≤ J_int := by
    have hint_norm : ‖∫ τ : ℝ in (-R)..R,
        riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
          cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ‖ ≤
        (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * J_int := by
      calc ‖∫ τ : ℝ in (-R)..R,
              riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
                RHTower.edPoly b (Finset.Icc 1 X)
                  (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
                cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ‖
          ≤ ∫ τ : ℝ in (-R)..R,
              ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
                RHTower.edPoly b (Finset.Icc 1 X)
                  (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + τ : ℝ) : ℂ) * I) *
                cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ τ : ℝ in (-R)..R, (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * (A_fn τ * B_fn τ) := by
            refine intervalIntegral.integral_mono_on (by linarith) ?_
              (((hA_cont.mul hB_cont).const_mul _).intervalIntegrable _ _) fun τ _ => ?_
            · refine Continuous.intervalIntegrable ?_ _ _
              exact Continuous.norm (by
                have hne1 : ∀ u : ℝ, (((1 / 2 : ℝ) : ℂ) + ((ρ₀.im + u : ℝ) : ℂ) * I) ≠ 1 := by
                  intro u h; have := congrArg Complex.re h; simp at this
                have hsX : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
                refine Continuous.mul (Continuous.mul ?_ ?_)
                  (continuous_cahenMellinGaussIntegrand (neg_lt_zero.mpr hδ₀_pos).ne)
                · exact continuous_riemannZeta_comp (by fun_prop) hne1
                · exact (RHTower.differentiable_edPoly b hsX).continuous.comp (by fun_prop))
            · rw [norm_mul, ← hA_def]
              have hA0 : 0 ≤ A_fn τ := by rw [hA_def]; exact norm_nonneg _
              calc A_fn τ * ‖cahenMellinGaussIntegrand α (-δ₀) (Real.log Y) τ‖
                  ≤ A_fn τ * ((Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * B_fn τ) :=
                    mul_le_mul_of_nonneg_left (hcm_left_le τ) hA0
                _ = (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * (A_fn τ * B_fn τ) := by ring
        _ = (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * J_int := by
            rw [intervalIntegral.integral_const_mul, hJ_def]
    have hcomb : 1 / 4 ≤
        (1 / (2 * Real.pi)) * ((Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * J_int) :=
      hleft_norm_ge.trans (mul_le_mul_of_nonneg_left hint_norm (by positivity))
    have hmul_pi : Real.pi / 2 ≤ (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * J_int := by
      have h := mul_le_mul_of_nonneg_left hcomb (by positivity : 0 ≤ 2 * Real.pi)
      have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
      have eq1 : (2 * Real.pi) * (1 / 4 : ℝ) = Real.pi / 2 := by ring
      have eq2 : (2 * Real.pi) * ((1 / (2 * Real.pi)) *
          ((Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * J_int)) =
          (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * J_int := by field_simp
      rw [eq1, eq2] at h; exact h
    have hprod_inv : (Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀) *
        (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) = 1 := by
      have h1 : Real.exp (-α * δ₀ ^ 2) * Real.exp (α * δ₀ ^ 2) = 1 := by
        rw [← Real.exp_add]; simp
      have h2 : Y ^ δ₀ * Y ^ (-δ₀) = 1 := by
        rw [← Real.rpow_add hY0]; simp
      calc (Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀) * (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀))
          = (Real.exp (-α * δ₀ ^ 2) * Real.exp (α * δ₀ ^ 2)) * (Y ^ δ₀ * Y ^ (-δ₀)) := by ring
        _ = 1 := by rw [h1, h2, mul_one]
    have h := mul_le_mul_of_nonneg_left hmul_pi
      (by positivity : 0 ≤ Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀)
    calc (Real.pi / 2) * Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀
        = (Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀) * (Real.pi / 2) := by ring
      _ ≤ (Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀) *
            ((Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀)) * J_int) := h
      _ = ((Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀) *
            (Real.exp (α * δ₀ ^ 2) * Y ^ (-δ₀))) * J_int := by ring
      _ = J_int := by rw [hprod_inv, one_mul]
  have hJ_pos : 0 < J_int :=
    lt_of_lt_of_le (by have := Real.pi_pos; positivity) hJ_ge
  have hIB_le : (∫ τ : ℝ in (-R)..R, B_fn τ ^ 2) ≤ Real.pi / δ₀ := by
    have hB2_eq : ∀ τ : ℝ, B_fn τ ^ 2 = (1 / δ₀) * (δ₀ / (δ₀ ^ 2 + τ ^ 2)) := by
      intro τ
      rw [hB_def, one_div, inv_pow, Real.sq_sqrt (by positivity)]
      field_simp [hδ₀_pos.ne']
    rw [intervalIntegral.integral_congr fun τ _ => hB2_eq τ,
      intervalIntegral.integral_const_mul, RHTower.Sieve.integral_re_pole_line hδ₀_pos.ne']
    have harc : Real.arctan (R / δ₀) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
    calc (1 / δ₀) * (2 * Real.arctan (R / δ₀))
        ≤ (1 / δ₀) * (2 * (Real.pi / 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = Real.pi / δ₀ := by ring
  have ⟨K_cs, hK_cs⟩ : ∃ k : ℝ, k = (Real.pi / δ₀) / J_int := ⟨_, rfl⟩
  have hK_cs_pos : 0 < K_cs := by rw [hK_cs]; have := Real.pi_pos; positivity
  have hcs_quad : J_int ≤
      (K_cs / 2) * (∫ τ : ℝ in (-R)..R, A_fn τ ^ 2) +
        (1 / (2 * K_cs)) * (∫ τ : ℝ in (-R)..R, B_fn τ ^ 2) := by
    rw [hJ_def, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hA_cont.pow 2).const_mul _ |>.intervalIntegrable _ _)
        ((hB_cont.pow 2).const_mul _ |>.intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((hA_cont.mul hB_cont).intervalIntegrable _ _)
      ((((hA_cont.pow 2).const_mul _).add ((hB_cont.pow 2).const_mul _)).intervalIntegrable _ _)
      fun τ _ => ?_
    have hsq0 : 0 ≤ (K_cs * A_fn τ - B_fn τ) ^ 2 := sq_nonneg _
    have hdivK := div_nonneg hsq0 (mul_pos zero_lt_two hK_cs_pos).le
    have hid : (K_cs * A_fn τ - B_fn τ) ^ 2 / (2 * K_cs) =
        (K_cs / 2) * A_fn τ ^ 2 + (1 / (2 * K_cs)) * B_fn τ ^ 2 - A_fn τ * B_fn τ := by
      field_simp [hK_cs_pos.ne']; ring
    linarith
  have hIA_ge : (δ₀ / Real.pi) * J_int ^ 2 ≤ ∫ τ : ℝ in (-R)..R, A_fn τ ^ 2 := by
    have h2 : (1 / (2 * K_cs)) * (∫ τ : ℝ in (-R)..R, B_fn τ ^ 2) ≤ J_int / 2 := by
      calc (1 / (2 * K_cs)) * (∫ τ : ℝ in (-R)..R, B_fn τ ^ 2)
          ≤ (1 / (2 * K_cs)) * (Real.pi / δ₀) :=
            mul_le_mul_of_nonneg_left hIB_le (by positivity)
        _ = J_int / 2 := by
            rw [hK_cs]
            have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
            field_simp [hδ₀_pos.ne', hJ_pos.ne']
    have hhalf : J_int / 2 ≤ (K_cs / 2) * ∫ τ : ℝ in (-R)..R, A_fn τ ^ 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 2 / K_cs)
    have eqL : (2 / K_cs) * (J_int / 2) = (δ₀ / Real.pi) * J_int ^ 2 := by
      rw [hK_cs]
      have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp [hδ₀_pos.ne', hJ_pos.ne']
    have eqR : (2 / K_cs) * ((K_cs / 2) * ∫ τ : ℝ in (-R)..R, A_fn τ ^ 2) =
        ∫ τ : ℝ in (-R)..R, A_fn τ ^ 2 := by field_simp [hK_cs_pos.ne']
    rw [eqL, eqR] at hmul
    exact hmul
  have hshift_int : (∫ τ : ℝ in (-R)..R, A_fn τ ^ 2) =
      ∫ t in (ρ₀.im - R)..(ρ₀.im + R),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_add_left
      (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ρ₀.im (a := -R) (b := R)
    rw [show ρ₀.im + -R = ρ₀.im - R by ring] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [hA_def]
  rw [← hshift_int, ← hδ₀_def]
  have hJ2_ge : ((Real.pi / 2) * Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀) ^ 2 ≤ J_int ^ 2 :=
    pow_le_pow_left₀ (by have := Real.pi_pos; positivity) hJ_ge 2
  have hpi_34 : 3 / 4 ≤ Real.pi / 4 := by linarith [Real.pi_gt_three]
  calc (3 / 4 : ℝ) * δ₀ * Real.exp (-2 * α * δ₀ ^ 2) * Y ^ (2 * δ₀)
      ≤ (Real.pi / 4) * δ₀ * Real.exp (-2 * α * δ₀ ^ 2) * Y ^ (2 * δ₀) := by
        have : 0 ≤ δ₀ * Real.exp (-2 * α * δ₀ ^ 2) * Y ^ (2 * δ₀) := by positivity
        nlinarith only [hpi_34, this]
    _ = (δ₀ / Real.pi) * ((Real.pi / 2) * Real.exp (-α * δ₀ ^ 2) * Y ^ δ₀) ^ 2 := by
        have hexp2 : (Real.exp (-α * δ₀ ^ 2)) ^ 2 = Real.exp (-2 * α * δ₀ ^ 2) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have hY2 : (Y ^ δ₀) ^ 2 = Y ^ (2 * δ₀) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; congr 1; push_cast; ring
        have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
        rw [mul_pow, mul_pow, hexp2, hY2]
        field_simp; ring
    _ ≤ (δ₀ / Real.pi) * J_int ^ 2 :=
        mul_le_mul_of_nonneg_left hJ2_ge (by have := Real.pi_pos; positivity)
    _ ≤ ∫ τ : ℝ in (-R)..R, A_fn τ ^ 2 := hIA_ge

theorem riemannZeta_one_sub_eq_zero_of_strip {s : ℂ} (hz : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) : riemannZeta (1 - s) = 0 := by
  have hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hc
    have he : s = ((-(2 * (m : ℝ)) : ℝ) : ℂ) := by push_cast; linear_combination 2 * hc
    rw [he, Complex.ofReal_re] at h0
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ) := by
    intro m hc
    have he : s = ((1 + 2 * (m : ℝ) : ℝ) : ℂ) := by push_cast; linear_combination -2 * hc
    rw [he, Complex.ofReal_re] at h1
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact (RHTower.riemannZeta_one_sub_eq_zero_iff_off_poles hs h1s).mpr hz

theorem exp_neg_le_inv_of_pos {z : ℝ} (hz : 0 < z) : Real.exp (-z) ≤ 1 / z := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hz (by linarith [Real.add_one_le_exp z])

theorem continuous_normSq_zetaMollified_criticalLine (b : ℕ → ℂ) (X : ℕ) :
    Continuous (fun t : ℝ =>
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  have hne1 : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h; have := congrArg Complex.re h; simp at this
  have hsX : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  refine (Continuous.norm (Continuous.mul ?_ ?_)).pow 2
  · exact continuous_riemannZeta_comp (by fun_prop) hne1
  · exact (RHTower.differentiable_edPoly b hsX).continuous.comp (by fun_prop)

theorem integral_subinterval_le_of_cont_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ t, 0 ≤ f t) {a c d b : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (∫ t in c..d, f t) ≤ ∫ t in a..b, f t := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) a c) (hf.intervalIntegrable (μ := volume) c b)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) c d) (hf.intervalIntegrable (μ := volume) d b)
  have h_ac : 0 ≤ ∫ t in a..c, f t := intervalIntegral.integral_nonneg hac fun t _ => h0 t
  have h_db : 0 ≤ ∫ t in d..b, f t := intervalIntegral.integral_nonneg hdb fun t _ => h0 t
  linarith

/-- Complex-valued Möbius mollifier coefficients `b_d = μ(d)`. -/
def moebiusMollifierCoeff (d : ℕ) : ℂ := ((ArithmeticFunction.moebius d : ℤ) : ℂ)

@[simp]
theorem moebiusMollifierCoeff_one : moebiusMollifierCoeff 1 = 1 := by
  simp [moebiusMollifierCoeff]

theorem norm_moebiusMollifierCoeff_le_one (d : ℕ) : ‖moebiusMollifierCoeff d‖ ≤ 1 :=
  RHTower.Sieve.norm_moebius_complex_le_one d

theorem mollifiedZetaCoeff_moebius_eq_zero {X n : ℕ} (hn : n ∈ Finset.Icc 2 X) :
    RHTower.mollifiedZetaCoeff moebiusMollifierCoeff X n = 0 := by
  obtain ⟨hn2, hnX⟩ := Finset.mem_Icc.mp hn
  unfold RHTower.mollifiedZetaCoeff moebiusMollifierCoeff
  have hfilter : (Finset.Icc 1 X).filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ X) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, hdX⟩, hdn⟩
      exact ⟨⟨hdn, by omega⟩, hdX⟩
    · rintro ⟨⟨hdn, _⟩, hdX⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
      exact ⟨⟨by omega, hdX⟩, hdn⟩
  have hreal := RHTower.Sieve.sum_moebius_filter_eq_zero (X := X) (k := n) (by omega) hnX
  have hcast : (∑ d ∈ n.divisors.filter (fun m => m ≤ X),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      ((∑ d ∈ n.divisors.filter (fun m => m ≤ X),
        (ArithmeticFunction.moebius d : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hfilter, hcast, hreal, Complex.ofReal_zero]

/-- **Eventual Quasi-RH from dyadic critical-line second-moment boundedness at `θ₁ > 1/2`.**
If eventually on `[T, 2T]` there exists a mollifier `Ψ` of length `X ≤ T^θ` whose product `ζ Ψ`
cancels Dirichlet coefficients `2 ≤ n ≤ X₁` with `X₁ ≥ T^{θ₁}` (`θ₁ > 1/2`) and satisfies
`∫_T^{2T} ‖ζΨ(1/2 + it)‖² dt ≤ C T`, then for every `ε > 0` only finitely many nontrivial zeros of
`ζ` satisfy `|Re ρ - 1/2| ≥ 1/(2θ₁) + ε`. -/
theorem finite_offLineZeros_beyond_of_dyadic_long_mollifier
    {θ₁ θ B C ε : ℝ} (hθ₁ : 1 / 2 < θ₁) (hθ : θ₁ ≤ θ) (hB : 1 ≤ B) (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ᶠ T in atTop, ∃ X X₁ : ℕ, 1 ≤ X ∧ (X : ℝ) ≤ T ^ θ ∧ T ^ θ₁ ≤ (X₁ : ℝ) ∧
      ∃ b : ℕ → ℂ, b 1 = 1 ∧ (∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B) ∧
        (∀ n ∈ Finset.Icc 2 X₁, RHTower.mollifiedZetaCoeff b X n = 0) ∧
        (∫ t in T..(2 * T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      1 / (2 * θ₁) + ε ≤ |ρ.re - 1 / 2|}.Finite := by
  have hθ₁_pos : 0 < θ₁ := by linarith
  have hθ_pos : 0 < θ := lt_of_lt_of_le hθ₁_pos hθ
  have ⟨δs, hδs_def⟩ : ∃ d : ℝ, d = 1 / (2 * θ₁) + ε := ⟨_, rfl⟩
  have hδs_pos : 0 < δs := by rw [hδs_def]; positivity
  have ⟨θ_Y, hθ_Y_def⟩ : ∃ t : ℝ, t = θ₁ / (1 + θ₁ * ε) := ⟨_, rfl⟩
  have hθ_Y_pos : 0 < θ_Y := by rw [hθ_Y_def]; positivity
  have hθ_Y_lt : θ_Y < θ₁ := by
    rw [hθ_Y_def, div_lt_iff₀ (by positivity)]
    have : 0 < θ₁ ^ 2 * ε := by positivity
    nlinarith
  have ⟨η_gap, hη_def⟩ : ∃ g : ℝ, g = 2 * δs * θ_Y - 1 := ⟨_, rfl⟩
  have hη_pos : 0 < η_gap := by
    rw [hη_def, hδs_def, hθ_Y_def]
    have hden : 0 < 1 + θ₁ * ε := by positivity
    have heq : 2 * (1 / (2 * θ₁) + ε) * (θ₁ / (1 + θ₁ * ε)) - 1 =
        (θ₁ * ε) / (1 + θ₁ * ε) := by field_simp [hθ₁_pos.ne']; ring
    rw [heq]; positivity
  obtain ⟨T_ev, hT_ev⟩ := Filter.eventually_atTop.mp hbound
  have ⟨c_R, hc_R_def⟩ : ∃ c : ℝ, c = 4 * θ + 8 * θ_Y + 30 := ⟨_, rfl⟩
  have hc_R_pos : 0 < c_R := by rw [hc_R_def]; positivity
  have ⟨L_min, hL_min_def⟩ : ∃ l : ℝ, l = max (max 100 (Real.log (max 2 T_ev) + 1))
      (max (max (12 / θ_Y) ((32 + 32 * θ₁) / (θ₁ - θ_Y) ^ 2))
        (max (48 * B + 240 * B + 1)
          (max (4 * c_R) ((4 * (C + 1) / (δs * Real.exp (-1 / 2)) + 1) / η_gap)))) := ⟨_, rfl⟩
  have ⟨T₀, hT₀_def⟩ : ∃ t : ℝ, t = (3 / 2) * Real.exp L_min + 1 := ⟨_, rfl⟩
  have hT₀_pos : 0 < T₀ := by rw [hT₀_def]; positivity
  suffices hbounded : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      δs ≤ |ρ.re - 1 / 2| → |ρ.im| ≤ T₀ by
    refine (RHTower.finite_riemannZeta_zeros_rectangle
      ((0 : ℂ) + ((-T₀ : ℝ) : ℂ) * I) ((1 : ℂ) + ((T₀ : ℝ) : ℂ) * I)).subset ?_
    rintro ρ ⟨hζ, h0, h1, hsep⟩
    refine ⟨?_, hζ⟩
    have him := abs_le.mp (hbounded ρ hζ h0 h1 (by rwa [hδs_def]))
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    simp only [Complex.add_re, Complex.zero_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, zero_add, Complex.one_re,
      Complex.add_im, Complex.zero_im, Complex.mul_im, mul_one, Complex.one_im]
    rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le (by linarith : -T₀ ≤ T₀)]
    exact ⟨⟨h0.le, h1.le⟩, him⟩
  have hupper_right : ∀ ρ₀ : ℂ, riemannZeta ρ₀ = 0 → 1 / 2 + δs ≤ ρ₀.re → ρ₀.im ≤ T₀ := by
    intro ρ₀ hζ0 hre_ge
    by_contra hgt_T₀
    push Not at hgt_T₀
    have hre_half : 1 / 2 < ρ₀.re := by linarith
    have hre_lt1 : ρ₀.re < 1 := RHTower.riemannZeta_zero_re_lt_one hζ0
    have ⟨T, hT_def⟩ : ∃ t : ℝ, t = (2 / 3) * ρ₀.im := ⟨_, rfl⟩
    have hT_gt_exp : Real.exp L_min < T := by linarith [hT₀_def, hT_def]
    have hT0 : 0 < T := lt_trans (Real.exp_pos _) hT_gt_exp
    have ⟨L, hL_def⟩ : ∃ l : ℝ, l = Real.log T := ⟨_, rfl⟩
    have hL_gt : L_min < L := by
      have := Real.log_lt_log (Real.exp_pos _) hT_gt_exp
      rwa [Real.log_exp, ← hL_def] at this
    have hL_max1 : max 100 (Real.log (max 2 T_ev) + 1) ≤ L := by
      have h1 : max 100 (Real.log (max 2 T_ev) + 1) ≤ L_min := by
        rw [hL_min_def]; exact le_max_left _ _
      linarith
    have hL100 : 100 ≤ L := le_trans (le_max_left _ _) hL_max1
    have hT_ge_ev : T_ev ≤ T := by
      have hlog_ev : Real.log (max 2 T_ev) < L :=
        lt_of_lt_of_le (by linarith [le_max_right 100 (Real.log (max 2 T_ev) + 1)]) hL_max1
      have hexp_ev := Real.exp_lt_exp.mpr hlog_ev
      rw [Real.exp_log (lt_of_lt_of_le zero_lt_two (le_max_left 2 T_ev)), hL_def,
        Real.exp_log hT0] at hexp_ev
      exact (le_max_right 2 T_ev).trans hexp_ev.le
    have hL_max2 : max (max (12 / θ_Y) ((32 + 32 * θ₁) / (θ₁ - θ_Y) ^ 2))
        (max (48 * B + 240 * B + 1)
          (max (4 * c_R) ((4 * (C + 1) / (δs * Real.exp (-1 / 2)) + 1) / η_gap))) ≤ L := by
      have h1 : _ ≤ L_min := by rw [hL_min_def]; exact le_max_right _ _
      linarith
    have hL_θY : 12 / θ_Y ≤ L :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL_max2
    have hL_gap : (32 + 32 * θ₁) / (θ₁ - θ_Y) ^ 2 ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL_max2
    have hL_B : 48 * B + 240 * B + 1 ≤ L :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL_max2
    have hL_cR : 4 * c_R ≤ L :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) hL_max2)
    have hL_C : (4 * (C + 1) / (δs * Real.exp (-1 / 2)) + 1) / η_gap ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) hL_max2)
    obtain ⟨X, X₁, hX1, hX_le, hX₁_ge, b, hb1, hb_le, hshort_zero, hmsq_le⟩ :=
      hT_ev T hT_ge_ev
    have ⟨X₁', hX₁'_def⟩ : ∃ m : ℕ, m = ⌊T ^ θ₁⌋₊ := ⟨_, rfl⟩
    have hX₁'_le_r : (X₁' : ℝ) ≤ T ^ θ₁ := by
      rw [hX₁'_def]; exact Nat.floor_le (Real.rpow_nonneg hT0.le θ₁)
    have hX₁'_le_X₁ : X₁' ≤ X₁ := by
      exact_mod_cast hX₁'_le_r.trans hX₁_ge
    have hTθ₁_eq : T ^ θ₁ = Real.exp (θ₁ * L) := by
      rw [hL_def, Real.rpow_def_of_pos hT0, mul_comm]
    have hθ₁L_ge : 50 ≤ θ₁ * L := by nlinarith only [hθ₁, hL100]
    have hTθ₁_ge : 50 ≤ T ^ θ₁ := by
      rw [hTθ₁_eq]; linarith [Real.add_one_le_exp (θ₁ * L)]
    have hX₁'_gt : T ^ θ₁ - 1 < (X₁' : ℝ) := by
      rw [hX₁'_def]; have := Nat.lt_floor_add_one (T ^ θ₁); linarith
    have hX₁'_ge1 : 1 ≤ X₁' := by
      have : (2 : ℝ) < X₁' := by linarith
      exact_mod_cast (by linarith : (1 : ℝ) ≤ X₁')
    have hX₁'_half : (1 / 2) * Real.exp (θ₁ * L) ≤ (X₁' : ℝ) := by
      have he50 : 2 ≤ Real.exp (θ₁ * L) := by linarith [Real.add_one_le_exp (θ₁ * L)]
      rw [hTθ₁_eq] at hX₁'_gt; linarith
    have ⟨Y, hY_def⟩ : ∃ y : ℝ, y = Real.exp (θ_Y * L) := ⟨_, rfl⟩
    have hθYL_ge12 : 12 ≤ θ_Y * L := by
      have := (div_le_iff₀ hθ_Y_pos).mp hL_θY; linarith
    have hY_ge1 : 1 ≤ Y := by rw [hY_def]; exact Real.one_le_exp (by linarith)
    have hlogY : Real.log Y = θ_Y * L := by rw [hY_def, Real.log_exp]
    have hYα : 2 * Real.sqrt 1 ≤ Real.log Y := by rw [Real.sqrt_one, hlogY]; linarith
    have hlog2_le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hgap_L : 32 + 32 * θ₁ ≤ (θ₁ - θ_Y) ^ 2 * L := by
      have hpos : 0 < (θ₁ - θ_Y) ^ 2 := sq_pos_of_pos (by linarith)
      have := (div_le_iff₀ hpos).mp hL_gap
      linarith
    have hgap_lin : 10 ≤ (θ₁ - θ_Y) * L := by
      by_contra hlt
      push Not at hlt
      have hpos : 0 < θ₁ - θ_Y := by linarith
      have hmul_pos : 0 < (θ₁ - θ_Y) * L := mul_pos hpos (by linarith)
      have hsq : ((θ₁ - θ_Y) * L) ^ 2 < 100 := by
        nlinarith only [hlt, hmul_pos]
      have h1 : (θ₁ - θ_Y) ^ 2 * L * L = ((θ₁ - θ_Y) * L) ^ 2 := by ring
      nlinarith only [hgap_L, hL100, hsq, h1, hθ₁]
    have hlogX₁'_sub : (1 / 2) * ((θ₁ - θ_Y) * L) ≤ Real.log (X₁' : ℝ) - Real.log Y := by
      have hX₁'0 : (0 : ℝ) < X₁' := by exact_mod_cast hX₁'_ge1
      have hlog_ge := Real.log_le_log (by positivity) hX₁'_half
      have hlog12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
      rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_pos _).ne',
        Real.log_exp, hlog12] at hlog_ge
      rw [hlogY]
      linarith
    have hslope : 5 * (1 : ℝ) ≤ Real.log (X₁' : ℝ) - Real.log Y := by linarith
    have hYX₁' : Y < (X₁' : ℝ) := by
      have hX₁'0 : (0 : ℝ) < X₁' := by exact_mod_cast hX₁'_ge1
      have hlt : Real.log Y < Real.log (X₁' : ℝ) := by linarith
      exact (Real.log_lt_log_iff (by positivity) hX₁'0).mp hlt
    have ⟨R, hR_def⟩ : ∃ r : ℝ, r = Real.sqrt (c_R * L) := ⟨_, rfl⟩
    have hcRL_ge : 400 ≤ c_R * L := by
      have hcR4 : 4 ≤ c_R := by rw [hc_R_def]; linarith
      nlinarith only [hcR4, hL100]
    have hR1 : 1 ≤ R := by
      rw [hR_def, Real.le_sqrt zero_le_one (by positivity)]; linarith
    have hR2_eq : R ^ 2 = c_R * L := by rw [hR_def, Real.sq_sqrt (by positivity)]
    have hR_le_T2 : R ≤ T / 2 := by
      have hR_le_L2 : R ≤ L / 2 := by
        rw [hR_def]
        have hsq : c_R * L ≤ (L / 2) ^ 2 := by nlinarith only [hL_cR, hL100]
        exact (Real.sqrt_le_iff.mpr ⟨by linarith, hsq⟩)
      have hL_le_T : L ≤ T := by
        rw [hL_def]; have := Real.log_le_sub_one_of_pos hT0; linarith
      linarith
    have hγ_eq : ρ₀.im = (3 / 2) * T := by linarith [hT_def]
    have hTL_ge100 : 100 ≤ T := by
      have := Real.add_one_le_exp L
      rw [hL_def, Real.exp_log hT0] at this; linarith
    have hRγ : R + 1 ≤ ρ₀.im := by linarith
    have hshort' : ∑ n ∈ Finset.Icc 2 X₁',
        ‖RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-ρ₀.re) ≤ 1 / 8 := by
      have h0 : ∑ n ∈ Finset.Icc 2 X₁',
          ‖RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-ρ₀.re) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        obtain ⟨hn2, hnX⟩ := Finset.mem_Icc.mp hn
        rw [hshort_zero n (Finset.mem_Icc.mpr ⟨hn2, hnX.trans hX₁'_le_X₁⟩), norm_zero, zero_mul]
      linarith
    have htail' : 2 * B * (Real.sqrt 1 / (Real.log (X₁' : ℝ) - Real.log Y)) *
        (X₁' : ℝ) ^ (3 / 2 : ℝ) *
        Real.exp (-(Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * 1)) ≤ 1 / 12 := by
      rw [Real.sqrt_one]
      have hdiv_le : 1 / (Real.log (X₁' : ℝ) - Real.log Y) ≤ 1 :=
        div_le_one_of_le₀ (by linarith) (by linarith)
      have hX₁'_rpow : (X₁' : ℝ) ^ (3 / 2 : ℝ) ≤ Real.exp ((3 / 2) * θ₁ * L) := by
        calc (X₁' : ℝ) ^ (3 / 2 : ℝ)
            ≤ (Real.exp (θ₁ * L)) ^ (3 / 2 : ℝ) := by
              rw [← hTθ₁_eq]; exact Real.rpow_le_rpow (Nat.cast_nonneg _) hX₁'_le_r (by norm_num)
          _ = Real.exp ((3 / 2) * θ₁ * L) := by
              rw [← Real.exp_mul]; congr 1; ring
      have hsq_ge : (1 / 4) * ((θ₁ - θ_Y) ^ 2 * L ^ 2) ≤
          (Real.log (X₁' : ℝ) - Real.log Y) ^ 2 := by
        have h1 := pow_le_pow_left₀ (by positivity) hlogX₁'_sub 2
        linarith [show ((1 / 2) * ((θ₁ - θ_Y) * L)) ^ 2 =
          (1 / 4) * ((θ₁ - θ_Y) ^ 2 * L ^ 2) by ring]
      have hexp_arg : (3 / 2) * θ₁ * L - (Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / 4 ≤ -L := by
        have hmulL := mul_le_mul_of_nonneg_right hgap_L (by linarith : 0 ≤ L)
        have h1 : (32 + 32 * θ₁) * L = (16 : ℝ) * ((2 + 2 * θ₁) * L) := by ring
        have h2 : (θ₁ - θ_Y) ^ 2 * L * L = (θ₁ - θ_Y) ^ 2 * L ^ 2 := by ring
        rw [h1, h2] at hmulL
        have hθ₁L_pos : 0 < θ₁ * L := by positivity
        linarith
      calc 2 * B * (1 / (Real.log (X₁' : ℝ) - Real.log Y)) *
            (X₁' : ℝ) ^ (3 / 2 : ℝ) *
            Real.exp (-(Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * 1))
          ≤ 2 * B * 1 * Real.exp ((3 / 2) * θ₁ * L) *
              Real.exp (-(Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / 4) := by
            rw [mul_one]
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            refine mul_le_mul ?_ hX₁'_rpow (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hdiv_le (by positivity)
        _ = 2 * B * Real.exp ((3 / 2) * θ₁ * L -
              (Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / 4) := by
            rw [mul_one, mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ 2 * B * Real.exp (-L) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by positivity)
        _ ≤ 2 * B * (1 / L) :=
            mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos (by linarith)) (by positivity)
        _ ≤ 1 / 12 := by
            rw [mul_one_div, div_le_iff₀ (by linarith)]
            linarith
    have hvtail' : 4 * B * (1 / Real.sqrt 1) *
        Real.exp ((25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2 / 2) ≤ 1 / 12 := by
      rw [Real.sqrt_one, div_one, mul_one]
      have hexp_arg : (25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2 / 2 ≤ -L := by
        rw [hlogY, hR2_eq, hc_R_def]
        have h1 : 0 < θ * L := by positivity
        have h2 : 0 < θ_Y * L := by positivity
        linarith
      calc 4 * B * Real.exp ((25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2 / 2)
          ≤ 4 * B * Real.exp (-L) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by positivity)
        _ ≤ 4 * B * (1 / L) :=
            mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos (by linarith)) (by positivity)
        _ ≤ 1 / 12 := by
            rw [mul_one_div, div_le_iff₀ (by linarith)]
            linarith
    have hhoriz' : 5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
        Real.exp ((25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2) ≤ 1 / 12 := by
      have hX_exp : (X : ℝ) ≤ Real.exp (θ * L) := by
        rw [hL_def, ← Real.rpow_def_of_pos hT0, mul_comm]; exact hX_le
      have hsqrt_le : Real.sqrt (ρ₀.im + R + 6) ≤ Real.exp L := by
        have hT_eq : Real.exp L = T := by rw [hL_def, Real.exp_log hT0]
        rw [hT_eq]
        refine Real.sqrt_le_iff.mpr ⟨hT0.le, ?_⟩
        nlinarith only [hγ_eq, hR_le_T2, hTL_ge100]
      have hexp_arg : θ * L + L + ((25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2) ≤ -L := by
        rw [hlogY, hR2_eq, hc_R_def]
        have h1 : 0 < θ * L := by positivity
        have h2 : 0 < θ_Y * L := by positivity
        linarith
      calc 5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + R + 6) *
            Real.exp ((25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2)
          ≤ 5 * B * Real.exp (θ * L) * Real.exp L *
              Real.exp ((25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact mul_le_mul (mul_le_mul_of_nonneg_left hX_exp (by positivity))
              hsqrt_le (Real.sqrt_nonneg _) (by positivity)
        _ = 5 * B * Real.exp (θ * L + L +
              ((25 / 4) * 1 + (5 / 2) * Real.log Y - 1 * R ^ 2)) := by
            rw [mul_assoc (5 * B), mul_assoc (5 * B), ← Real.exp_add, ← Real.exp_add]
            congr 2; ring
        _ ≤ 5 * B * Real.exp (-L) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by positivity)
        _ ≤ 5 * B * (1 / L) :=
            mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos (by linarith)) (by positivity)
        _ ≤ 1 / 12 := by
            rw [mul_one_div, div_le_iff₀ (by linarith)]
            linarith
    have hspike := integral_normSq_zetaMollified_criticalLine_spike_of_zero hζ0 hre_half
      hR1 hRγ zero_lt_one hY_ge1 hYα hB hX1 hX₁'_ge1 hYX₁' hslope hb1 hb_le
      hshort' htail' hvtail' hhoriz'
    have hint_sub : (∫ t in (ρ₀.im - R)..(ρ₀.im + R),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        ∫ t in T..(2 * T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      integral_subinterval_le_of_cont_nonneg (continuous_normSq_zetaMollified_criticalLine b X)
        (fun _ => sq_nonneg _) (by linarith) (by linarith [hR1]) (by linarith)
    have hcomb : (3 / 4 : ℝ) * (ρ₀.re - 1 / 2) *
        Real.exp (-2 * 1 * (ρ₀.re - 1 / 2) ^ 2) * Y ^ (2 * (ρ₀.re - 1 / 2)) ≤ C * T :=
      (hspike.trans hint_sub).trans hmsq_le
    have hδ0_lt : ρ₀.re - 1 / 2 < 1 / 2 := by linarith
    have hexp_ge : Real.exp (-1 / 2) ≤ Real.exp (-2 * 1 * (ρ₀.re - 1 / 2) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hsq : (ρ₀.re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith only [hre_half, hδ0_lt]
      linarith
    have hY_pow_ge : T * (η_gap * L) ≤ Y ^ (2 * (ρ₀.re - 1 / 2)) := by
      have h1 : Y ^ (2 * δs) ≤ Y ^ (2 * (ρ₀.re - 1 / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hY_ge1 (by linarith)
      have h2 : Y ^ (2 * δs) = T * Real.exp (η_gap * L) := by
        rw [hY_def, ← Real.exp_mul]
        have heq : θ_Y * L * (2 * δs) = L + η_gap * L := by rw [hη_def]; ring
        rw [heq, Real.exp_add, hL_def, Real.exp_log hT0]
      have h3 : η_gap * L ≤ Real.exp (η_gap * L) := by
        linarith [Real.add_one_le_exp (η_gap * L)]
      exact (mul_le_mul_of_nonneg_left h3 hT0.le).trans (h2 ▸ h1)
    have hηL_ge : 4 * (C + 1) / (δs * Real.exp (-1 / 2)) + 1 ≤ η_gap * L := by
      have := (div_le_iff₀ hη_pos).mp hL_C
      linarith
    have hprod_gt : C + 1 < (3 / 4 : ℝ) * δs * Real.exp (-1 / 2) * (η_gap * L) := by
      have hden_pos : 0 < δs * Real.exp (-1 / 2) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hηL_ge
        (by positivity : 0 ≤ (3 / 4 : ℝ) * (δs * Real.exp (-1 / 2)))
      have heq : (3 / 4 : ℝ) * (δs * Real.exp (-1 / 2)) *
          (4 * (C + 1) / (δs * Real.exp (-1 / 2)) + 1) =
          3 * (C + 1) + (3 / 4) * δs * Real.exp (-1 / 2) := by
        field_simp [hden_pos.ne']; ring
      linarith
    have hlow : (3 / 4 : ℝ) * δs * Real.exp (-1 / 2) * (T * (η_gap * L)) ≤
        (3 / 4 : ℝ) * (ρ₀.re - 1 / 2) *
          Real.exp (-2 * 1 * (ρ₀.re - 1 / 2) ^ 2) * Y ^ (2 * (ρ₀.re - 1 / 2)) := by
      refine mul_le_mul ?_ hY_pow_ge (by positivity) (by positivity)
      refine mul_le_mul ?_ hexp_ge (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hlow' : (C + 1) * T < (3 / 4 : ℝ) * δs * Real.exp (-1 / 2) * (T * (η_gap * L)) := by
      have := mul_lt_mul_of_pos_right hprod_gt hT0
      linarith
    linarith
  have hright : ∀ ρ₁ : ℂ, riemannZeta ρ₁ = 0 → 1 / 2 + δs ≤ ρ₁.re → |ρ₁.im| ≤ T₀ := by
    intro ρ₁ hζ1 hre1
    rcases le_or_gt 0 ρ₁.im with him0 | him0
    · rw [abs_of_nonneg him0]
      exact hupper_right ρ₁ hζ1 hre1
    · have hconj : riemannZeta (starRingEnd ℂ ρ₁) = 0 := by
        rw [riemannZeta_conj, hζ1, map_zero]
      have hre_c : 1 / 2 + δs ≤ (starRingEnd ℂ ρ₁).re := by simpa using hre1
      have him_c := hupper_right (starRingEnd ℂ ρ₁) hconj hre_c
      simp only [Complex.conj_im] at him_c
      rw [abs_of_neg him0]
      exact him_c
  intro ρ hζ h0 h1 hsep
  rcases le_or_gt (1 / 2) ρ.re with hre | hre
  · rw [abs_of_nonneg (by linarith)] at hsep
    exact hright ρ hζ (by linarith)
  · rw [abs_of_neg (by linarith)] at hsep
    have hζ_sym := riemannZeta_one_sub_eq_zero_of_strip hζ h0 h1
    have h1 : |(1 - ρ).im| ≤ T₀ :=
      hright (1 - ρ) hζ_sym (by rw [Complex.sub_re, Complex.one_re]; linarith)
    simpa [Complex.sub_im] using h1

/-- **Specialization of `finite_offLineZeros_beyond_of_dyadic_long_mollifier` to the truncated
Möbius mollifier `M_X(s) = ∑_{d ≤ X} μ(d) d^{-s}` at `X = ⌊T^θ⌋₊` (`θ > 1/2`).** -/
theorem finite_offLineZeros_beyond_of_dyadic_moebius_mollifier
    {θ C ε : ℝ} (hθ : 1 / 2 < θ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ᶠ T in atTop,
      (∫ t in T..(2 * T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      1 / (2 * θ) + ε ≤ |ρ.re - 1 / 2|}.Finite := by
  have hθ_pos : 0 < θ := by linarith
  have ⟨ε', hε'_def⟩ : ∃ e : ℝ, e = min (ε / 2) ((θ - 1 / 2) / (2 * θ)) := ⟨_, rfl⟩
  have hε'_pos : 0 < ε' := by rw [hε'_def]; exact lt_min (by linarith) (by positivity)
  have hε'_le : ε' ≤ ε / 2 := by rw [hε'_def]; exact min_le_left _ _
  have hθε'_le : θ * ε' ≤ (θ - 1 / 2) / 2 := by
    have h1 : ε' ≤ (θ - 1 / 2) / (2 * θ) := by rw [hε'_def]; exact min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hθ_pos.le
    have eq1 : θ * ((θ - 1 / 2) / (2 * θ)) = (θ - 1 / 2) / 2 := by
      field_simp [hθ_pos.ne']
    rwa [eq1] at h2
  have ⟨θ₁, hθ₁_def⟩ : ∃ t : ℝ, t = θ / (1 + θ * ε') := ⟨_, rfl⟩
  have hθ₁_gt : 1 / 2 < θ₁ := by
    rw [hθ₁_def, lt_div_iff₀ (by positivity)]
    linarith
  have hθ₁_lt : θ₁ < θ := by
    rw [hθ₁_def, div_lt_iff₀ (by positivity)]
    have : 0 < θ ^ 2 * ε' := by positivity
    nlinarith
  have hsep_eq : 1 / (2 * θ₁) + ε' / 2 ≤ 1 / (2 * θ) + ε := by
    have heq : 1 / (2 * θ₁) + ε' / 2 = 1 / (2 * θ) + ε' := by
      rw [hθ₁_def]; field_simp [hθ_pos.ne']; ring
    linarith
  have hev_floor : ∀ᶠ T : ℝ in atTop, 0 ≤ T ∧ 1 ≤ ⌊T ^ θ⌋₊ ∧ T ^ θ₁ ≤ (⌊T ^ θ⌋₊ : ℝ) := by
    have hgap_pos : 0 < θ - θ₁ := by linarith
    refine (Filter.eventually_ge_atTop (max 2 (Real.exp (2 / (θ - θ₁))))).mono fun T hT => ?_
    have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
    have hT0 : 0 < T := by linarith
    have hT_exp : Real.exp (2 / (θ - θ₁)) ≤ T := (le_max_right _ _).trans hT
    have hlog_ge : 2 / (θ - θ₁) ≤ Real.log T := by
      have := Real.log_le_log (Real.exp_pos _) hT_exp
      rwa [Real.log_exp] at this
    have hdiff_ge : 2 ≤ (θ - θ₁) * Real.log T := by
      have := (div_le_iff₀ hgap_pos).mp hlog_ge; linarith
    have hpow_diff : 2 ≤ T ^ (θ - θ₁) := by
      rw [Real.rpow_def_of_pos hT0]
      linarith [Real.add_one_le_exp (Real.log T * (θ - θ₁)),
        show Real.log T * (θ - θ₁) = (θ - θ₁) * Real.log T by ring]
    have hθ₁_pos : 0 < θ₁ := by linarith
    have hTθ₁_ge1 : 1 ≤ T ^ θ₁ := Real.one_le_rpow (by linarith) hθ₁_pos.le
    have hTθ_split : T ^ θ = T ^ θ₁ * T ^ (θ - θ₁) := by
      rw [← Real.rpow_add hT0]; congr 1; ring
    have hTθ_ge : T ^ θ₁ + 1 ≤ T ^ θ := by
      rw [hTθ_split]; nlinarith only [hpow_diff, hTθ₁_ge1]
    have hgt := Nat.lt_floor_add_one (T ^ θ)
    refine ⟨hT0.le, ?_, by linarith⟩
    exact_mod_cast (by linarith : (1 : ℝ) ≤ (⌊T ^ θ⌋₊ : ℝ))
  have hfin := finite_offLineZeros_beyond_of_dyadic_long_mollifier hθ₁_gt hθ₁_lt.le le_rfl hC
    (by positivity : 0 < ε' / 2) ((hbound.and hev_floor).mono fun T ⟨hbT, hT0, hX1, hX_ge⟩ =>
      ⟨⌊T ^ θ⌋₊, ⌊T ^ θ⌋₊, hX1, Nat.floor_le (Real.rpow_nonneg hT0 θ), hX_ge,
        moebiusMollifierCoeff, moebiusMollifierCoeff_one,
        fun d _ => norm_moebiusMollifierCoeff_le_one d,
        fun n hn => mollifiedZetaCoeff_moebius_eq_zero hn, hbT⟩)
  refine hfin.subset ?_
  rintro ρ ⟨hζ, h0, h1, hsep⟩
  exact ⟨hζ, h0, h1, hsep_eq.trans hsep⟩

/-- **Cofinal long-mollifier second-moment boundedness on `[1, T]` implies `RiemannHypothesis`.**
Even if the critical-line second moment `∫_1^T ‖ζ(1/2 + it) Ψ(1/2 + it)‖² dt` is bounded only by
`C_θ · T^K` (with `K ≥ 0` fixed and `C_θ` allowed to depend arbitrarily on `θ`) along an unbounded
sequence of heights `T` (`∃ᶠ T in atTop`) for arbitrarily large exponents `θ` (cancelling `2 ≤ n ≤ X₁`
with `X₁ ≥ T^{3θ/4}` and `X ≤ T^θ`), **every** nontrivial zero of `ζ` at **every** height lies on the
critical line `Re s = 1/2`. -/
theorem riemannHypothesis_of_cofinal_long_mollifier
    {B K : ℝ} (hB : 1 ≤ B) (hK : 0 ≤ K)
    (hcofinal : ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T in atTop, ∃ X X₁ : ℕ, 1 ≤ X ∧ (X : ℝ) ≤ T ^ θ ∧
        T ^ ((3 / 4) * θ) ≤ (X₁ : ℝ) ∧
        ∃ b : ℕ → ℂ, b 1 = 1 ∧ (∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B) ∧
          (∀ n ∈ Finset.Icc 2 X₁, RHTower.mollifiedZetaCoeff b X n = 0) ∧
          (∫ t in (1 : ℝ)..T,
            ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
            C * T ^ K) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs_half hs_lt1 hζs
  -- Conjugate if necessary so the putative off-line zero lies in the upper half-plane.
  obtain ⟨ρ₀, hζ0, hre_half, hre_lt1, him_nonneg⟩ :
      ∃ ρ₀ : ℂ, riemannZeta ρ₀ = 0 ∧ 1 / 2 < ρ₀.re ∧ ρ₀.re < 1 ∧ 0 ≤ ρ₀.im := by
    rcases le_or_gt 0 s.im with him | him
    · exact ⟨s, hζs, hs_half, hs_lt1, him⟩
    · refine ⟨starRingEnd ℂ s, ?_, by simpa using hs_half, by simpa using hs_lt1, ?_⟩
      · rw [riemannZeta_conj, hζs, map_zero]
      · simp only [Complex.conj_im]; linarith
  -- By `riemannZeta_ne_zero_of_im_sq_le`, `ρ₀.im² > 32 > (11/2)²`, so `ρ₀.im > 11/2`.
  have him_gt : 11 / 2 < ρ₀.im := by
    have hne1 : ρ₀ ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hre_lt1; norm_num at hre_lt1
    have hsq_gt : 32 < ρ₀.im ^ 2 := by
      by_contra hle; push Not at hle
      exact RHTower.riemannZeta_ne_zero_of_im_sq_le hne1 (by linarith) hle hζ0
    by_contra hle; push Not at hle
    have : ρ₀.im ^ 2 ≤ (11 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ him_nonneg hle 2
    linarith
  have ⟨δ₀, hδ₀_def⟩ : ∃ d : ℝ, d = ρ₀.re - 1 / 2 := ⟨_, rfl⟩
  have hδ₀_pos : 0 < δ₀ := by rw [hδ₀_def]; linarith
  have hδ₀_lt : δ₀ < 1 / 2 := by rw [hδ₀_def]; linarith
  have ⟨θ₀, hθ₀_def⟩ : ∃ t : ℝ, t = max 100 ((200 * (K + 1)) / δ₀) := ⟨_, rfl⟩
  have hθ₀_pos : 0 < θ₀ := by rw [hθ₀_def]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨θ, hθ_ge, C, hC0, hfreq⟩ := hcofinal θ₀ hθ₀_pos
  have hθ100 : 100 ≤ θ := le_trans (by rw [hθ₀_def]; exact le_max_left _ _) hθ_ge
  have hθ_K : (200 * (K + 1)) / δ₀ ≤ θ :=
    le_trans (by rw [hθ₀_def]; exact le_max_right _ _) hθ_ge
  have hspike_exp : K + 1 ≤ 2 * δ₀ * (9 / 200 - (17 / 200) * δ₀) * θ := by
    have hrate : 1 / 400 < 9 / 200 - (17 / 200) * δ₀ := by linarith
    have hprod1 : δ₀ / 200 ≤ 2 * δ₀ * (9 / 200 - (17 / 200) * δ₀) := by
      nlinarith only [hδ₀_pos, hrate]
    have hprod2 : K + 1 ≤ (δ₀ / 200) * θ := by
      have := (div_le_iff₀ hδ₀_pos).mp hθ_K; linarith
    exact hprod2.trans (mul_le_mul_of_nonneg_right hprod1 (by linarith))
  have ⟨M_γ, hM_γ_def⟩ : ∃ m : ℝ, m = 5 * B * Real.sqrt (ρ₀.im + 9 / 2 + 6) := ⟨_, rfl⟩
  have hM_γ_pos : 0 < M_γ := by
    rw [hM_γ_def]
    have hrad : 0 < ρ₀.im + 9 / 2 + 6 := by linarith
    have := Real.sqrt_pos.mpr hrad
    positivity
  have ⟨L_req, hL_req_def⟩ : ∃ l : ℝ, l = max 20000 (240 * B + 240 * M_γ + 1) := ⟨_, rfl⟩
  have ⟨T_min, hT_min_def⟩ : ∃ t : ℝ,
      t = max (max (ρ₀.im + 5) ((4 * (C + 1)) / (3 * δ₀) + 1)) (Real.exp L_req) := ⟨_, rfl⟩
  obtain ⟨T, hT_ge, X, X₁, hX1, hX_le, hX₁_ge, b, hb1, hb_le, hshort_zero, hmsq_le⟩ :=
    (Filter.frequently_atTop.mp hfreq) T_min
  have hT_im : ρ₀.im + 5 ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hT_min_def ▸ hT_ge)
  have hT_C : (4 * (C + 1)) / (3 * δ₀) + 1 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hT_min_def ▸ hT_ge)
  have hT_exp : Real.exp L_req ≤ T :=
    le_trans (le_max_right _ _) (hT_min_def ▸ hT_ge)
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT_exp
  have hT1 : 1 ≤ T := by linarith
  have hlogT_ge : L_req ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hT_exp
    rwa [Real.log_exp] at this
  have ⟨L₀, hL₀_def⟩ : ∃ l : ℝ, l = θ * Real.log T := ⟨_, rfl⟩
  have hL₀_ge_req : L_req ≤ L₀ := by
    have hL_req0 : 0 < L_req := by
      rw [hL_req_def]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    rw [hL₀_def]
    nlinarith only [hθ100, hlogT_ge, hL_req0]
  have hL₀_20000 : 20000 ≤ L₀ :=
    le_trans (by rw [hL_req_def]; exact le_max_left _ _) hL₀_ge_req
  have hL₀_BM : 240 * B + 240 * M_γ + 1 ≤ L₀ :=
    le_trans (by rw [hL_req_def]; exact le_max_right _ _) hL₀_ge_req
  have ⟨α, hα_def⟩ : ∃ a : ℝ, a = (17 / 200) * L₀ := ⟨_, rfl⟩
  have hα_ge1 : 1 ≤ α := by rw [hα_def]; linarith
  have hα_pos : 0 < α := by linarith
  have ⟨Y, hY_def⟩ : ∃ y : ℝ, y = Real.exp ((9 / 200) * L₀) := ⟨_, rfl⟩
  have hY_ge1 : 1 ≤ Y := by rw [hY_def]; exact Real.one_le_exp (by linarith)
  have hlogY : Real.log Y = (9 / 200) * L₀ := by rw [hY_def, Real.log_exp]
  have hYα : 2 * Real.sqrt α ≤ Real.log Y := by
    rw [hlogY]
    have hnonneg : 0 ≤ (9 / 200) * L₀ := by linarith
    have hsq : (2 * Real.sqrt α) ^ 2 ≤ ((9 / 200) * L₀) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hα_pos.le, hα_def]
      nlinarith only [hL₀_20000]
    exact ( abs_le_of_sq_le_sq' hsq hnonneg ).2
  have ⟨X₁', hX₁'_def⟩ : ∃ m : ℕ, m = ⌊T ^ ((3 / 4) * θ)⌋₊ := ⟨_, rfl⟩
  have hX₁'_le_r : (X₁' : ℝ) ≤ T ^ ((3 / 4) * θ) := by
    rw [hX₁'_def]; exact Nat.floor_le (Real.rpow_nonneg hT0.le _)
  have hX₁'_le_X₁ : X₁' ≤ X₁ := by exact_mod_cast hX₁'_le_r.trans hX₁_ge
  have hT34_eq : T ^ ((3 / 4) * θ) = Real.exp ((3 / 4) * L₀) := by
    rw [Real.rpow_def_of_pos hT0, hL₀_def]; congr 1; ring
  have hX₁'_gt : T ^ ((3 / 4) * θ) - 1 < (X₁' : ℝ) := by
    rw [hX₁'_def]; have := Nat.lt_floor_add_one (T ^ ((3 / 4) * θ)); linarith
  have hX₁'_half : (1 / 2) * Real.exp ((3 / 4) * L₀) ≤ (X₁' : ℝ) := by
    have he : 2 ≤ Real.exp ((3 / 4) * L₀) := by
      linarith [Real.add_one_le_exp ((3 / 4) * L₀)]
    rw [hT34_eq] at hX₁'_gt; linarith
  have hX₁'_ge1 : 1 ≤ X₁' := by
    have he : 4 ≤ Real.exp ((3 / 4) * L₀) := by
      linarith [Real.add_one_le_exp ((3 / 4) * L₀)]
    exact_mod_cast (by linarith : (1 : ℝ) ≤ X₁')
  have hlogX₁'_sub : (7 / 10) * L₀ ≤ Real.log (X₁' : ℝ) - Real.log Y := by
    have hX₁'0 : (0 : ℝ) < X₁' := by exact_mod_cast hX₁'_ge1
    have hlog_ge := Real.log_le_log (by positivity) hX₁'_half
    have hlog12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_pos _).ne',
      Real.log_exp, hlog12] at hlog_ge
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    rw [hlogY]; linarith
  have hslope : 5 * α ≤ Real.log (X₁' : ℝ) - Real.log Y := by rw [hα_def]; linarith
  have hYX₁' : Y < (X₁' : ℝ) := by
    have hX₁'0 : (0 : ℝ) < X₁' := by exact_mod_cast hX₁'_ge1
    exact (Real.log_lt_log_iff (by positivity) hX₁'0).mp (by linarith)
  have hshort' : ∑ n ∈ Finset.Icc 2 X₁',
      ‖RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-ρ₀.re) ≤ 1 / 8 := by
    have h0 : ∑ n ∈ Finset.Icc 2 X₁',
        ‖RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-ρ₀.re) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      obtain ⟨hn2, hnX⟩ := Finset.mem_Icc.mp hn
      rw [hshort_zero n (Finset.mem_Icc.mpr ⟨hn2, hnX.trans hX₁'_le_X₁⟩), norm_zero, zero_mul]
    linarith
  have htail' : 2 * B * (Real.sqrt α / (Real.log (X₁' : ℝ) - Real.log Y)) *
      (X₁' : ℝ) ^ (3 / 2 : ℝ) *
      Real.exp (-(Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * α)) ≤ 1 / 12 := by
    have hsqrt_le : Real.sqrt α ≤ α := by
      refine Real.sqrt_le_iff.mpr ⟨hα_pos.le, ?_⟩
      nlinarith only [hα_ge1]
    have hdiv_le : Real.sqrt α / (Real.log (X₁' : ℝ) - Real.log Y) ≤ 1 :=
      div_le_one_of_le₀ (hsqrt_le.trans (by linarith)) (by linarith)
    have hX₁'_rpow : (X₁' : ℝ) ^ (3 / 2 : ℝ) ≤ Real.exp ((9 / 8) * L₀) := by
      calc (X₁' : ℝ) ^ (3 / 2 : ℝ)
          ≤ (Real.exp ((3 / 4) * L₀)) ^ (3 / 2 : ℝ) := by
            rw [← hT34_eq]; exact Real.rpow_le_rpow (Nat.cast_nonneg _) hX₁'_le_r (by norm_num)
        _ = Real.exp ((9 / 8) * L₀) := by rw [← Real.exp_mul]; congr 1; ring
    have hsq_ge : ((7 / 10) * L₀) ^ 2 ≤ (Real.log (X₁' : ℝ) - Real.log Y) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlogX₁'_sub 2
    have hexp_arg : (9 / 8) * L₀ - (Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * α) ≤
        -(1 / 4) * L₀ := by
      have hdiv_ge : (49 / 34) * L₀ ≤ (Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * α) := by
        rw [le_div_iff₀ (by positivity), hα_def]
        nlinarith only [hsq_ge]
      linarith
    calc 2 * B * (Real.sqrt α / (Real.log (X₁' : ℝ) - Real.log Y)) *
          (X₁' : ℝ) ^ (3 / 2 : ℝ) *
          Real.exp (-(Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * α))
        ≤ 2 * B * 1 * Real.exp ((9 / 8) * L₀) *
            Real.exp (-(Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * α)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          refine mul_le_mul (mul_le_mul_of_nonneg_left hdiv_le (by positivity))
            hX₁'_rpow (by positivity) (by positivity)
      _ = 2 * B * Real.exp ((9 / 8) * L₀ -
            (Real.log (X₁' : ℝ) - Real.log Y) ^ 2 / (4 * α)) := by
          rw [mul_one, mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ 2 * B * Real.exp (-((1 / 4) * L₀)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          linarith
      _ ≤ 2 * B * (1 / ((1 / 4) * L₀)) :=
          mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos (by linarith)) (by positivity)
      _ ≤ 1 / 12 := by
          have eq1 : 2 * B * (1 / ((1 / 4) * L₀)) = 8 * B / L₀ := by ring
          rw [eq1, div_le_iff₀ (by linarith)]
          linarith
  have hvtail' : 4 * B * (1 / Real.sqrt α) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2 / 2) ≤ 1 / 12 := by
    have hinv_le : 1 / Real.sqrt α ≤ 1 :=
      div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (by linarith)) (Real.sqrt_nonneg _)
    have hexp_arg : (25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2 / 2 ≤
        -((1 / 5) * L₀) := by
      rw [hα_def, hlogY]; linarith
    calc 4 * B * (1 / Real.sqrt α) *
          Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2 / 2)
        ≤ 4 * B * 1 * Real.exp (-((1 / 5) * L₀)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv_le (by positivity))
            (Real.exp_le_exp.mpr hexp_arg) (Real.exp_pos _).le (by positivity)
      _ ≤ 4 * B * (1 / ((1 / 5) * L₀)) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos (by linarith)) (by positivity)
      _ ≤ 1 / 12 := by
          have eq1 : 4 * B * (1 / ((1 / 5) * L₀)) = 20 * B / L₀ := by ring
          rw [eq1, div_le_iff₀ (by linarith)]
          linarith
  have hhoriz' : 5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + 9 / 2 + 6) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2) ≤ 1 / 12 := by
    have hX_exp : (X : ℝ) ≤ Real.exp L₀ := by
      rw [hL₀_def, ← Real.rpow_def_of_pos hT0, mul_comm]; exact hX_le
    have hexp_arg : L₀ + ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2) ≤
        -((1 / 20) * L₀) := by
      rw [hα_def, hlogY]; linarith
    calc 5 * B * (X : ℝ) * Real.sqrt (ρ₀.im + 9 / 2 + 6) *
          Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2)
        = M_γ * ((X : ℝ) *
            Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2)) := by
          rw [hM_γ_def]; ring
      _ ≤ M_γ * (Real.exp L₀ *
            Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hX_exp (Real.exp_pos _).le) hM_γ_pos.le
      _ = M_γ * Real.exp (L₀ + ((25 / 4) * α + (5 / 2) * Real.log Y - α * (9 / 2 : ℝ) ^ 2)) := by
          rw [← Real.exp_add]
      _ ≤ M_γ * Real.exp (-((1 / 20) * L₀)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) hM_γ_pos.le
      _ ≤ M_γ * (1 / ((1 / 20) * L₀)) :=
          mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos (by linarith)) hM_γ_pos.le
      _ ≤ 1 / 12 := by
          have eq1 : M_γ * (1 / ((1 / 20) * L₀)) = 20 * M_γ / L₀ := by ring
          rw [eq1, div_le_iff₀ (by linarith)]
          linarith
  have hspike := integral_normSq_zetaMollified_criticalLine_spike_of_zero hζ0 hre_half
    (R := 9 / 2) (by norm_num) (by linarith) hα_pos hY_ge1 hYα hB hX1 hX₁'_ge1 hYX₁' hslope
    hb1 hb_le hshort' htail' hvtail' hhoriz'
  have hint_sub : (∫ t in (ρ₀.im - 9 / 2)..(ρ₀.im + 9 / 2),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      ∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    integral_subinterval_le_of_cont_nonneg (continuous_normSq_zetaMollified_criticalLine b X)
      (fun _ => sq_nonneg _) (by linarith) (by linarith) (by linarith)
  have hcomb : (3 / 4 : ℝ) * δ₀ * Real.exp (-2 * α * δ₀ ^ 2) * Y ^ (2 * δ₀) ≤ C * T ^ K := by
    rw [hδ₀_def]; exact (hspike.trans hint_sub).trans hmsq_le
  have hTK_pos : 0 < T ^ K := Real.rpow_pos_of_pos hT0 K
  have hfactor_ge : T * T ^ K ≤ Real.exp (-2 * α * δ₀ ^ 2) * Y ^ (2 * δ₀) := by
    have heq1 : Real.exp (-2 * α * δ₀ ^ 2) * Y ^ (2 * δ₀) =
        Real.exp ((2 * δ₀ * (9 / 200 - (17 / 200) * δ₀) * θ) * Real.log T) := by
      rw [hY_def, ← Real.exp_mul, ← Real.exp_add, hα_def, hL₀_def]
      congr 1; ring
    have heq2 : T * T ^ K = Real.exp ((K + 1) * Real.log T) := by
      rw [Real.rpow_def_of_pos hT0, show T = Real.exp (Real.log T) from (Real.exp_log hT0).symm,
        ← Real.exp_add]
      congr 1; ring
    rw [heq1, heq2]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hspike_exp (Real.log_nonneg hT1))
  have hlow1 : (3 / 4 : ℝ) * δ₀ * (T * T ^ K) ≤
      (3 / 4 : ℝ) * δ₀ * Real.exp (-2 * α * δ₀ ^ 2) * Y ^ (2 * δ₀) := by
    rw [mul_assoc ((3 / 4 : ℝ) * δ₀)]
    exact mul_le_mul_of_nonneg_left hfactor_ge (by positivity)
  have hT_gt_C : C + 1 < (3 / 4 : ℝ) * δ₀ * T := by
    have := mul_le_mul_of_nonneg_left hT_C (by positivity : 0 ≤ (3 / 4 : ℝ) * δ₀)
    have eq1 : (3 / 4 : ℝ) * δ₀ * ((4 * (C + 1)) / (3 * δ₀) + 1) =
        C + 1 + (3 / 4) * δ₀ := by field_simp [hδ₀_pos.ne']; ring
    linarith
  have hlow2 : (C + 1) * T ^ K < (3 / 4 : ℝ) * δ₀ * (T * T ^ K) := by
    have := mul_lt_mul_of_pos_right hT_gt_C hTK_pos
    linarith
  linarith

/-- **Specialization of `riemannHypothesis_of_cofinal_long_mollifier` to the truncated Möbius
mollifier `M_X(s) = ∑_{d ≤ X} μ(d) d^{-s}` at `X = ⌊T^θ⌋₊`.**
If for arbitrarily large `θ > 0` there exists `C_θ ≥ 0` such that along an unbounded sequence of
heights `T`, `∫_1^T ‖ζ(1/2 + it) M_{⌊T^θ⌋}(1/2 + it)‖² dt ≤ C_θ · T^K`, then `RiemannHypothesis`
holds. -/
theorem riemannHypothesis_of_cofinal_moebius_mollifier
    {K : ℝ} (hK : 0 ≤ K)
    (hcofinal : ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T ^ K) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_cofinal_long_mollifier (B := 1) le_rfl hK fun θ₀ hθ₀ => ?_
  obtain ⟨θ, hθ_max, C, hC0, hfreq⟩ := hcofinal (max θ₀ 4) (lt_max_of_lt_left hθ₀)
  have hθ_ge0 : θ₀ ≤ θ := (le_max_left _ _).trans hθ_max
  have hθ_ge4 : 4 ≤ θ := (le_max_right _ _).trans hθ_max
  refine ⟨θ, hθ_ge0, C, hC0, ?_⟩
  refine (hfreq.and_eventually (Filter.eventually_ge_atTop (2 : ℝ))).mono fun T ⟨hmsq, hT2⟩ => ?_
  have hT0 : 0 < T := by linarith
  have hT14 : 2 ≤ T ^ ((1 / 4) * θ) := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hT2 zero_le_one
      _ ≤ T ^ ((1 / 4) * θ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hT34 : 2 ≤ T ^ ((3 / 4) * θ) :=
    hT14.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  have hTθ_split : T ^ θ = T ^ ((3 / 4) * θ) * T ^ ((1 / 4) * θ) := by
    rw [← Real.rpow_add hT0]; congr 1; ring
  have hTθ_ge : T ^ ((3 / 4) * θ) + 1 ≤ T ^ θ := by
    rw [hTθ_split]; nlinarith only [hT14, hT34]
  have hgt := Nat.lt_floor_add_one (T ^ θ)
  have hX1 : 1 ≤ ⌊T ^ θ⌋₊ := by
    exact_mod_cast (by linarith : (1 : ℝ) ≤ (⌊T ^ θ⌋₊ : ℝ))
  exact ⟨⌊T ^ θ⌋₊, ⌊T ^ θ⌋₊, hX1, Nat.floor_le (Real.rpow_nonneg hT0.le θ), by linarith,
    moebiusMollifierCoeff, moebiusMollifierCoeff_one,
    fun d _ => norm_moebiusMollifierCoeff_le_one d,
    fun n hn => mollifiedZetaCoeff_moebius_eq_zero hn, hmsq⟩

#print axioms eventually_integral_normSq_zetaMollified_ge_one_add_log_inv_theta
#print axioms eventually_integral_normSq_zetaMollified_ge_roughConst_div_theta
#print axioms tendsto_flowCreditedJensenBudget_atTop
#print axioms integral_normSq_zetaMollified_criticalLine_spike_of_zero
#print axioms finite_offLineZeros_beyond_of_dyadic_long_mollifier
#print axioms finite_offLineZeros_beyond_of_dyadic_moebius_mollifier
#print axioms riemannHypothesis_of_cofinal_long_mollifier
#print axioms riemannHypothesis_of_cofinal_moebius_mollifier

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
