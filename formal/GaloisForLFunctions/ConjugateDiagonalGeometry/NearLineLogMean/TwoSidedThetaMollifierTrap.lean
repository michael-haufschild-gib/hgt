import GaloisForLFunctions.RHTower.MollifiedMeanSquareGaussianPrimeFloor
import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.RHTower.Sieve.MollifierShortRange
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
  exact Nat.factorization_prod_pow_eq_self (by omega)

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
  rw [hq.prime.dvd_finset_prod_iff] at hdvd
  obtain ⟨p, hp, hqp⟩ := hdvd
  have hp_mem := (Finset.mem_filter.mp hp).1
  have hp_gt : ¬ p ≤ y := (Finset.mem_filter.mp hp).2
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hqp' : q ∣ p := hq.dvd_of_dvd_pow hqp
  have heq : q = p := (hp_prime.dvd_iff_eq hq.ne_one).mp hqp'
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

theorem smoothPart_eq_prod_primesLE {y m : ℕ} (hm : 1 ≤ m) :
    smoothPart y m = ∏ p ∈ Nat.primesLE y, p ^ (m.factorization p) := by
  unfold smoothPart
  symm
  refine Finset.prod_subset (fun p hp => ?_) (fun p hpP hpnot => ?_)
  · obtain ⟨hpm, hpy⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.prime_of_mem_primeFactors hpm, hpy⟩
  · simp only [Finset.mem_filter] at hpnot
    push_neg at hpnot
    by_cases hpm : p ∈ m.primeFactors
    · have hpy := (Nat.mem_primesLE.mp hpP).2
      exact absurd hpy (not_le.mpr (lt_of_not_ge (hpnot hpm)))
    · rw [Nat.factorization_eq_zero_of_not_mem_primeFactors hpm, pow_zero]

theorem factorization_le_self (m p : ℕ) : m.factorization p ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · by_cases hp : p ∈ m.primeFactors
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      calc m.factorization p ≤ 2 ^ (m.factorization p) := Nat.lt_two_pow_self.le
        _ ≤ p ^ (m.factorization p) := Nat.pow_le_pow_left hp2 _
        _ ≤ m := Nat.ordProj_le (by omega)
    · rw [Nat.factorization_eq_zero_of_not_mem_primeFactors hp]; omega

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
    rw [Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [inv_pow]
  have hgeom : ∀ p : P, ∑ e ∈ Finset.Icc 0 M, ((1 / ((p : ℕ) : ℝ)) ^ e) ≤
      ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1) := by
    intro p
    have hp_prime := (Nat.mem_primesLE.mp p.2).1
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp_prime.two_le
    have hrange : Finset.Icc 0 M = Finset.range (M + 1) := by
      ext e; simp [Nat.lt_succ_iff]
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
      simp only [r]; field_simp; ring
    rwa [heq] at hdiv
  have h4 : (∏ p : P, ∑ e ∈ Finset.Icc 0 M, ((1 / ((p : ℕ) : ℝ)) ^ e)) ≤
      ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) := by
    calc (∏ p : P, ∑ e ∈ Finset.Icc 0 M, ((1 / ((p : ℕ) : ℝ)) ^ e))
        ≤ ∏ p : P, (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) :=
          Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun _ _ => by positivity)
            (fun p _ => hgeom p)
      _ = ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) := Finset.prod_coe_sort P _
  have h5 : ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (∑ p ∈ P, (1 / ((p : ℝ) - 1))) := by
    calc ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ p ∈ P, Real.exp (1 / ((p : ℝ) - 1)) := by
          refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
          · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).1.two_le
            positivity
          · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).1.two_le
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
      obtain ⟨hpp, hpy⟩ := Nat.mem_primesLE.mp hp
      exact Finset.mem_Ico.mpr ⟨hpp.two_le, by omega⟩
    calc ∑ p ∈ P, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))
        ≤ ∑ k ∈ Finset.Ico 2 (y + 1), (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubP fun k hk _ => ?_
          have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
          exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) (by linarith))
      _ ≤ 1 := by
          rcases lt_or_ge y 2 with hy2 | hy2
          · have hempty : Finset.Ico 2 (y + 1) = ∅ := by
              ext k; simp only [Finset.mem_Ico, Finset.notMem_empty]; omega
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
            have hypos : (0 : ℝ) ≤ 1 / ((y : ℝ) + 1 - 1) := by positivity
            norm_num at hypos ⊢
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
        push_cast; field_simp; ring
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
      rw [← h, Nat.cast_mul]
      ring
    calc ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ))
        = ∑ m ∈ Finset.Icc 1 M, (1 / ((φ m).1 : ℝ)) * (1 / ((φ m).2 : ℝ)) :=
          Finset.sum_congr rfl hval
      _ = ∑ p ∈ (Finset.Icc 1 M).image φ, (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) :=
          (Finset.sum_image hinj).symm
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
  set C₀ : ℝ := 1 + |RHTower.Sieve.meisselMertensConst| +
    (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases eq_or_lt_of_le hy1 with rfl | hy2
  · have hm1 : RHTower.Sieve.mertensS 1 = 0 := by
      unfold RHTower.Sieve.mertensS
      have hempty : Nat.primesLE 1 = ∅ := by
        ext p; simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false]
        rintro ⟨hp, hp1⟩; exact absurd hp.two_le (by omega)
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
  set δ : ℝ := min (1 / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  -- Choose `θ₁ ∈ (θ, 1)` close enough to `1` that `log(θ' / θ) ≥ log(1/θ) - δ / 2`.
  set η : ℝ := min ((1 - θ) / 2) (1 - Real.exp (-(δ / 4)))
  have hη0 : 0 < η := by
    refine lt_min (by linarith) ?_
    have : Real.exp (-(δ / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  set θ₁ : ℝ := 1 - η
  have hθθ₁ : θ < θ₁ := by
    have : η ≤ (1 - θ) / 2 := min_le_left _ _
    linarith
  have hθ₁0 : 0 < θ₁ := lt_trans hθ0 hθθ₁
  have hθ₁1 : θ₁ < 1 := by linarith
  set θ' : ℝ := θ₁ + (1 - θ₁) / 4
  have hθ'1 : θ' < 1 := by linarith
  have hθ'ge : Real.exp (-(δ / 4)) ≤ θ' := by
    have : η ≤ 1 - Real.exp (-(δ / 4)) := min_le_right _ _
    linarith
  have hθ'pos : 0 < θ' := lt_of_lt_of_le (Real.exp_pos _) hθ'ge
  have hlog_θ' : Real.log (1 / θ) - δ / 4 ≤ Real.log (θ' / θ) := by
    have h1 : Real.exp (-(δ / 4)) / θ ≤ θ' / θ := div_le_div_of_nonneg_right hθ'ge hθ0.le
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (Real.exp_pos _).ne' hθ0.ne', Real.log_exp, Real.log_one_div] at h2 ⊢
    linarith
  set D₀ : ℝ := 1 + Real.exp (-(2 * a)) * max 0 (Real.log (1 / θ) - δ / 2)
  have hD₀1 : 1 ≤ D₀ := by
    have : 0 ≤ Real.exp (-(2 * a)) * max 0 (Real.log (1 / θ) - δ / 2) := by positivity
    linarith
  set Cm : ℝ := 2 * RHTower.Sieve.mertensFirstConst + 1 / 2
  have hCm0 : 0 ≤ Cm := by unfold Cm; have := RHTower.Sieve.mertensFirstConst_nonneg; linarith
  set yStar : ℕ := max 2 ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - θ₁) / 2) (ε := δ / 600) (by norm_num) (by linarith) (by positivity)
  -- Threshold `L₁` ensuring both small-`y` and large-`y` Mertens regimes exceed `log(1/θ) - δ / 2`.
  set S_yStar : ℝ := RHTower.Sieve.mertensS yStar + |RHTower.Sieve.meisselMertensConst| +
    Cm / Real.log 2 + Real.log (1 / θ) + 2
  set L₁ : ℝ := max (max (2 * a + 3) (32 / (1 - θ₁)))
    (max (128 / ((δ / D₀) * (1 - θ₁)))
      (max ((2 * Real.log 2 + Real.exp S_yStar) / θ') (32 * (Cm + 1) / (δ * θ'))))
  filter_upwards [Real.tendsto_log_atTop.eventually ((eventually_ge_atTop L₁).and hsup),
    eventually_gt_atTop 1] with T hTL hT1
  obtain ⟨hLL₁, hsupL⟩ := hTL
  have hT0 : 0 < T := lt_trans zero_lt_one hT1
  set L : ℝ := Real.log T
  have hLa : 2 * a + 3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL₁
  have hL32 : 32 / (1 - θ₁) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL₁
  have hLc : 128 / ((δ / D₀) * (1 - θ₁)) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL₁
  have hLyS : (2 * Real.log 2 + Real.exp S_yStar) / θ' ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hLL₁
  have hLCm : 32 * (Cm + 1) / (δ * θ') ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hLL₁
  have hL0 : 0 < L := by linarith
  have hδ₁0 : 0 < 1 - θ₁ := by linarith
  have hδL8 : 8 ≤ (1 - θ₁) / 4 * L := by rw [div_le_iff₀ hδ₁0] at hL32; linarith
  have hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L := by
    have hcpos : 0 < δ / D₀ := by positivity
    rw [div_le_iff₀ (mul_pos hcpos hδ₁0)] at hLc
    rw [div_le_iff₀ hcpos]; nlinarith
  have hsup' : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤
      δ / 6 := by linarith
  intro y hy hyle b hb1 hb
  have hyle_θ : (y : ℝ) ≤ Real.exp (θ * L) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hT0]; exact hyle
  have hyle_θ₁ : (y : ℝ) ≤ Real.exp (θ₁ * L) :=
    hyle_θ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθθ₁.le hL0.le))
  set M : ℕ := ⌊Real.exp (θ' * L)⌋₊
  have hMle : (M : ℝ) ≤ Real.exp (θ' * L) := Nat.floor_le (by positivity)
  have hMgt : Real.exp (θ' * L) - 1 < M := by
    have := Nat.lt_floor_add_one (Real.exp (θ' * L)); linarith
  obtain ⟨hM2, hyM, hMge, _, _⟩ :=
    RHTower.gaussFloor_scale hθ₁0 (by positivity : 0 < δ / D₀) hL0 hδL8 hδLc hyle_θ₁ hMle hMgt
  -- Lower-bound `D` by `n = 1` plus the primes in `(y, M]`.
  have hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
    by_cases hpos_target : Real.log (1 / θ) - δ / 2 ≤ 0
    · have hD₀_eq : D₀ = 1 := by simp [D₀, max_eq_left hpos_target]
      rw [hD₀_eq]
      have h1mem : 1 ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      have h1val : ‖RHTower.mollifiedZetaCoeff b y 1‖ ^ 2 *
          (1 : ℝ) ^ (-2 * (1 / 2 + a / L)) = 1 := by
        rw [RHTower.mollifiedZetaCoeff_one hy, hb1, norm_one]; simp
      calc (1 : ℝ) = ‖RHTower.mollifiedZetaCoeff b y 1‖ ^ 2 *
            (1 : ℝ) ^ (-2 * (1 / 2 + a / L)) := h1val.symm
        _ ≤ ∑ n ∈ Finset.Icc 1 M,
            ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) :=
          Finset.single_le_sum (fun _ _ => by positivity) h1mem
    · push_neg at hpos_target
      have hD₀_eq : D₀ = 1 + Real.exp (-(2 * a)) * (Real.log (1 / θ) - δ / 2) := by
        simp [D₀, max_eq_right hpos_target.le]
      -- Split `{1}` and `(Ioc y M).filter Prime`.
      let Pset := (Finset.Ioc y M).filter Nat.Prime
      have hsub_union : insert 1 Pset ⊆ Finset.Icc 1 M := by
        intro n hn
        rcases Finset.mem_insert.mp hn with rfl | hp
        · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
        · obtain ⟨hny, hnM⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
          exact Finset.mem_Icc.mpr ⟨by omega, hnM⟩
      have h1not : 1 ∉ Pset := by
        intro h; exact Nat.not_prime_one (Finset.mem_filter.mp h).2
      have hsum_ge : 1 + Real.exp (-(2 * a)) * (∑ p ∈ Pset, (1 / (p : ℝ))) ≤
          ∑ n ∈ Finset.Icc 1 M,
            ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
        calc 1 + Real.exp (-(2 * a)) * (∑ p ∈ Pset, (1 / (p : ℝ)))
            = ‖RHTower.mollifiedZetaCoeff b y 1‖ ^ 2 * (1 : ℝ) ^ (-2 * (1 / 2 + a / L)) +
                ∑ p ∈ Pset, (Real.exp (-(2 * a)) * (1 / (p : ℝ))) := by
              rw [RHTower.mollifiedZetaCoeff_one hy, hb1, norm_one, Finset.mul_sum]; simp
          _ ≤ ‖RHTower.mollifiedZetaCoeff b y 1‖ ^ 2 * (1 : ℝ) ^ (-2 * (1 / 2 + a / L)) +
                ∑ p ∈ Pset, ‖RHTower.mollifiedZetaCoeff b y p‖ ^ 2 *
                  (p : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
              gcongr with p hp
              obtain ⟨hpIoc, hpp⟩ := Finset.mem_filter.mp hp
              obtain ⟨hpy, hpM⟩ := Finset.mem_Ioc.mp hpIoc
              rw [RHTower.mollifiedZetaCoeff_prime_gt hy hb1 hpp hpy, norm_one, one_pow, one_mul]
              have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
              have hp_le_expL : (p : ℝ) ≤ Real.exp L :=
                (by exact_mod_cast hpM : (p : ℝ) ≤ M).trans
                  (hMle.trans (Real.exp_le_exp.mpr (by nlinarith)))
              have hlogp : Real.log (p : ℝ) ≤ L := by
                have := Real.log_le_log hp0 hp_le_expL; rwa [Real.log_exp] at this
              rw [Real.rpow_def_of_pos hp0, one_div, ← Real.rpow_neg_one,
                Real.rpow_def_of_pos hp0, ← Real.exp_add]
              apply Real.exp_le_exp.mpr
              have hdiv : -(2 * a * (Real.log (p : ℝ) / L)) ≥ -(2 * a) := by
                have hq : Real.log (p : ℝ) / L ≤ 1 := (div_le_one hL0).mpr hlogp
                nlinarith
              have hexp_eq : Real.log (p : ℝ) * (-2 * (1 / 2 + a / L)) =
                  -(2 * a * (Real.log (p : ℝ) / L)) + Real.log (p : ℝ) * (-1) := by
                field_simp; ring
              linarith
          _ = ∑ n ∈ insert 1 Pset, ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 *
                (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := (Finset.sum_insert h1not).symm
          _ ≤ ∑ n ∈ Finset.Icc 1 M, ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 *
                (n : ℝ) ^ (-2 * (1 / 2 + a / L)) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_union fun _ _ _ => by positivity
      -- Lower-bound `∑_{p ∈ Pset} 1/p = mertensS M - mertensS y` in both `y ≤ yStar` and `y > yStar`.
      have hlogM_ge : θ' * L - Real.log 2 ≤ Real.log (M : ℝ) := by
        have := Real.log_le_log (by positivity) hMge
        rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
      have hθ'L_ge : 2 * Real.log 2 + Real.exp S_yStar ≤ θ' * L := by
        rwa [div_le_iff₀ hθ'pos] at hLyS
      have hlogM_half : θ' * L / 2 ≤ Real.log (M : ℝ) := by
        have hS0 : 1 ≤ Real.exp S_yStar := by
          have : 0 ≤ RHTower.Sieve.mertensS yStar :=
            Finset.sum_nonneg fun _ _ => by positivity
          have : 0 ≤ |RHTower.Sieve.meisselMertensConst| := abs_nonneg _
          have : 0 ≤ Cm / Real.log 2 := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
          have hlogθ : 0 < Real.log (1 / θ) := by
            rw [Real.log_one_div]; exact neg_pos.mpr (Real.log_neg hθ0 hθ1)
          exact Real.one_le_exp (by unfold S_yStar; linarith)
        linarith
      have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
      have hP_ge : Real.log (1 / θ) - δ / 2 ≤ ∑ p ∈ Pset, (1 / (p : ℝ)) := by
        rw [sum_Ioc_prime_inv_eq_mertensS_sub' hyM]
        have hM_mert := (abs_le.mp (RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le hM2)).1
        unfold RHTower.Sieve.logLog at hM_mert
        by_cases hyS : y ≤ yStar
        · have hmert_mono : RHTower.Sieve.mertensS y ≤ RHTower.Sieve.mertensS yStar := by
            unfold RHTower.Sieve.mertensS
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
            obtain ⟨hpp, hpy⟩ := Nat.mem_primesLE.mp hp
            exact Nat.mem_primesLE.mpr ⟨hpp, hpy.trans hyS⟩
          have hlogM_exp : Real.exp S_yStar ≤ Real.log (M : ℝ) := by linarith
          have hlogLogM : S_yStar ≤ Real.log (Real.log (M : ℝ)) := by
            have := Real.log_le_log (Real.exp_pos _) hlogM_exp
            rwa [Real.log_exp] at this
          have hlog2_le : Real.log 2 ≤ Real.log (M : ℝ) :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hM2)
          have herrM : Cm / Real.log (M : ℝ) ≤ Cm / Real.log 2 :=
            div_le_div_of_nonneg_left hCm0 (Real.log_pos (by norm_num)) hlog2_le
          have hMM := neg_abs_le RHTower.Sieve.meisselMertensConst
          unfold S_yStar at hlogLogM
          linarith
        · push_neg at hyS
          have hy2 : 2 ≤ y := le_trans (le_max_left _ _) hyS.le
          have hy_mert := (abs_le.mp (RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le hy2)).2
          unfold RHTower.Sieve.logLog at hy_mert
          have hy_ceil : ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊ < y :=
            lt_of_le_of_lt (le_max_right _ _) hyS
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
            nlinarith
          have herrM : Cm / Real.log (M : ℝ) ≤ δ / 16 := by
            rw [div_le_iff₀ hlogM_pos]
            have h1 : 32 * (Cm + 1) ≤ δ * θ' * L := by
              have := (div_le_iff₀ (mul_pos hδ hθ'pos)).mp hLCm; linarith
            nlinarith [hlogM_half]
          have hlogy_le : Real.log (y : ℝ) ≤ θ * L := by
            have := Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) hyle_θ
            rwa [Real.log_exp] at this
          have hlogM_ge_mul : (1 - δ / 16) * (θ' * L) ≤ Real.log (M : ℝ) := by
            have h1 : 32 * (Cm + 1) ≤ δ * θ' * L := by
              have := (div_le_iff₀ (mul_pos hδ hθ'pos)).mp hLCm; linarith
            have hlog2_le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
            nlinarith [hlogM_ge]
          have h1sub_pos : 0 < 1 - δ / 16 := by linarith
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
            have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / (1 - δ / 16))
            rw [Real.log_one_div] at h
            have hinv : 1 / (1 - δ / 16) - 1 ≤ δ / 8 := by
              rw [sub_le_iff_le_add, div_le_iff₀ h1sub_pos]
              nlinarith
            linarith
          linarith
      rw [hD₀_eq]
      exact (add_le_add_left (mul_le_mul_of_nonneg_left hP_ge (Real.exp_pos _).le) 1).trans hsum_ge
  have hmain := gaussFloor_general_at_scale ha hθ₁0 hθ₁1 hD₀1 hδ hδ1 hLa hδL8 hδLc hsup' hy
    hyle_θ₁ hb hD_ge
  rw [Real.exp_log hT0] at hmain
  refine le_trans ?_ hmain
  refine mul_le_mul_of_nonneg_right ?_ hT0.le
  have hmax : Real.log (1 / θ) - δ / 2 ≤ max 0 (Real.log (1 / θ) - δ / 2) := le_max_right _ _
  have hexp_le1 : Real.exp (-(2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1 : Real.exp (-(2 * a)) * (Real.log (1 / θ) - δ / 2) ≤
      Real.exp (-(2 * a)) * max 0 (Real.log (1 / θ) - δ / 2) :=
    mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
  have hδ_le_ε : δ ≤ ε / 2 := min_le_right _ _
  have : Real.exp (-(2 * a)) * (δ / 2) ≤ δ / 2 := by nlinarith [Real.exp_pos (-(2 * a))]
  dsimp only [D₀]
  linarith

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
  set cr : ℝ := roughMollifierConst
  have hcr0 : 0 < cr := roughMollifierConst_pos
  set δ : ℝ := min (1 / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  -- Choose `θ₁ ∈ (θ, 1)` close enough to `1` that `(cr e^{-2a} / θ) (1 - θ') ≤ δ / 2`.
  set η : ℝ := min ((1 - θ) / 2) (δ * θ / (2 * cr + 1))
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  set θ₁ : ℝ := 1 - η
  have hθθ₁ : θ < θ₁ := by have := min_le_left ((1 - θ) / 2) (δ * θ / (2 * cr + 1)); linarith
  have hθ₁0 : 0 < θ₁ := lt_trans hθ0 hθθ₁
  have hθ₁1 : θ₁ < 1 := by linarith
  set θ' : ℝ := θ₁ + (1 - θ₁) / 4
  have hθ'1 : θ' < 1 := by linarith
  set D₀ : ℝ := max 1 (cr * Real.exp (-(2 * a)) * θ' / θ)
  have hD₀1 : 1 ≤ D₀ := le_max_left _ _
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - θ₁) / 2) (ε := δ / 600) (by norm_num) (by linarith) (by positivity)
  set L₁ : ℝ := max (max (2 * a + 3) (1 / θ))
    (max (32 / (1 - θ₁)) (128 / ((δ / D₀) * (1 - θ₁))))
  filter_upwards [Real.tendsto_log_atTop.eventually ((eventually_ge_atTop L₁).and hsup),
    eventually_gt_atTop 1] with T hTL hT1
  obtain ⟨hLL₁, hsupL⟩ := hTL
  have hT0 : 0 < T := lt_trans zero_lt_one hT1
  set L : ℝ := Real.log T
  have hLa : 2 * a + 3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL₁
  have hLθ : 1 / θ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL₁
  have hL32 : 32 / (1 - θ₁) ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL₁
  have hLc : 128 / ((δ / D₀) * (1 - θ₁)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL₁
  have hL0 : 0 < L := by linarith
  have hδ₁0 : 0 < 1 - θ₁ := by linarith
  have hδL8 : 8 ≤ (1 - θ₁) / 4 * L := by rw [div_le_iff₀ hδ₁0] at hL32; linarith
  have hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L := by
    have hcpos : 0 < δ / D₀ := by positivity
    rw [div_le_iff₀ (mul_pos hcpos hδ₁0)] at hLc
    rw [div_le_iff₀ hcpos]; nlinarith
  have hsup' : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤
      δ / 6 := by linarith
  intro y hy hyle b hb1 hb
  have hyle_θ : (y : ℝ) ≤ Real.exp (θ * L) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hT0]; exact hyle
  have hyle_θ₁ : (y : ℝ) ≤ Real.exp (θ₁ * L) :=
    hyle_θ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθθ₁.le hL0.le))
  set M : ℕ := ⌊Real.exp (θ' * L)⌋₊
  have hMle : (M : ℝ) ≤ Real.exp (θ' * L) := Nat.floor_le (by positivity)
  have hMgt : Real.exp (θ' * L) - 1 < M := by
    have := Nat.lt_floor_add_one (Real.exp (θ' * L)); linarith
  obtain ⟨hM2, _, _, _, _⟩ :=
    RHTower.gaussFloor_scale hθ₁0 (by positivity : 0 < δ / D₀) hL0 hδL8 hδLc hyle_θ₁ hMle hMgt
  have hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
    refine max_le ?_ ?_
    · have h1mem : 1 ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      have h1val : ‖RHTower.mollifiedZetaCoeff b y 1‖ ^ 2 *
          (1 : ℝ) ^ (-2 * (1 / 2 + a / L)) = 1 := by
        rw [RHTower.mollifiedZetaCoeff_one hy, hb1, norm_one]; simp
      calc (1 : ℝ) = ‖RHTower.mollifiedZetaCoeff b y 1‖ ^ 2 *
            (1 : ℝ) ^ (-2 * (1 / 2 + a / L)) := h1val.symm
        _ ≤ _ := Finset.single_le_sum (fun _ _ => by positivity) h1mem
    · let V := (Finset.Icc 1 M).image (roughPart y)
      have hVsub : V ⊆ Finset.Icc 1 M := by
        intro v hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
        exact Finset.mem_Icc.mpr ⟨roughPart_pos y hm1, (roughPart_le y hm1).trans hmM⟩
      have hV_term : ∀ v ∈ V, Real.exp (-(2 * a)) * (1 / (v : ℝ)) ≤
          ‖RHTower.mollifiedZetaCoeff b y v‖ ^ 2 * (v : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
        intro v hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
        rw [mollifiedZetaCoeff_roughPart hy hb1 m, norm_one, one_pow, one_mul]
        have hv1 : 1 ≤ roughPart y m := roughPart_pos y hm1
        have hv0 : (0 : ℝ) < roughPart y m := by exact_mod_cast hv1
        have hv_expL : (roughPart y m : ℝ) ≤ Real.exp L :=
          (by exact_mod_cast (roughPart_le y hm1).trans hmM : (roughPart y m : ℝ) ≤ M).trans
            (hMle.trans (Real.exp_le_exp.mpr (by nlinarith)))
        have hlogv : Real.log (roughPart y m : ℝ) ≤ L := by
          have := Real.log_le_log hv0 hv_expL; rwa [Real.log_exp] at this
        rw [Real.rpow_def_of_pos hv0, one_div, ← Real.rpow_neg_one,
          Real.rpow_def_of_pos hv0, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hq : Real.log (roughPart y m : ℝ) / L ≤ 1 := (div_le_one hL0).mpr hlogv
        have hexp_eq : Real.log (roughPart y m : ℝ) * (-2 * (1 / 2 + a / L)) =
            -(2 * a * (Real.log (roughPart y m : ℝ) / L)) + Real.log (roughPart y m : ℝ) * (-1) := by
          field_simp; ring
        nlinarith
      have hθL1 : 1 ≤ θ * L := by rwa [div_le_iff₀ hθ0] at hLθ
      have hlogy : Real.log (y : ℝ) ≤ θ * L := by
        have := Real.log_le_log (by exact_mod_cast hy) hyle_θ; rwa [Real.log_exp] at this
      have hmert_ub := exp_one_add_mertensS_le_inv_roughMollifierConst hy hθL1 hlogy
      have hlogM1 : θ' * L ≤ Real.log ((M : ℝ) + 1) := by
        have h1 : Real.exp (θ' * L) ≤ (M : ℝ) + 1 := by linarith
        have := Real.log_le_log (Real.exp_pos _) h1
        rwa [Real.log_exp] at this
      have hrough_ge : cr * θ' / θ ≤ ∑ v ∈ V, (1 / (v : ℝ)) := by
        have hbase := sum_inv_image_roughPart_ge y M
        have hdiv : cr * θ' / θ ≤ Real.log ((M : ℝ) + 1) / Real.exp (1 + RHTower.Sieve.mertensS y) := by
          have h1 : cr * θ' / θ = (θ' * L) / (θ * L / cr) := by field_simp
          rw [h1]
          exact div_le_div₀ (by positivity) hlogM1 (Real.exp_pos _) hmert_ub
        exact hdiv.trans hbase
      calc cr * Real.exp (-(2 * a)) * θ' / θ
          = Real.exp (-(2 * a)) * (cr * θ' / θ) := by ring
        _ ≤ Real.exp (-(2 * a)) * ∑ v ∈ V, (1 / (v : ℝ)) :=
            mul_le_mul_of_nonneg_left hrough_ge (Real.exp_pos _).le
        _ = ∑ v ∈ V, (Real.exp (-(2 * a)) * (1 / (v : ℝ))) := Finset.mul_sum _ _ _
        _ ≤ ∑ v ∈ V, ‖RHTower.mollifiedZetaCoeff b y v‖ ^ 2 * (v : ℝ) ^ (-2 * (1 / 2 + a / L)) :=
            Finset.sum_le_sum hV_term
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hVsub fun _ _ _ => by positivity
  have hmain := gaussFloor_general_at_scale ha hθ₁0 hθ₁1 hD₀1 hδ hδ1 hLa hδL8 hδLc hsup' hy
    hyle_θ₁ hb hD_ge
  rw [Real.exp_log hT0] at hmain
  refine le_trans ?_ hmain
  refine mul_le_mul_of_nonneg_right ?_ hT0.le
  have hmax : cr * Real.exp (-(2 * a)) * θ' / θ ≤ D₀ := le_max_right _ _
  have hη_le : η ≤ δ * θ / (2 * cr + 1) := min_le_right _ _
  have hexp_le1 : Real.exp (-(2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hloss : cr * Real.exp (-(2 * a)) * (1 - θ') / θ ≤ δ / 2 := by
    have h1θ' : 1 - θ' = 3 * η / 4 := by dsimp [θ', θ₁]; ring
    rw [h1θ']
    have h1 : cr * Real.exp (-(2 * a)) * (3 * η / 4) ≤ cr * η := by
      nlinarith [Real.exp_pos (-(2 * a))]
    calc cr * Real.exp (-(2 * a)) * (3 * η / 4) / θ
        ≤ cr * η / θ := div_le_div_of_nonneg_right h1 hθ0.le
      _ ≤ cr * (δ * θ / (2 * cr + 1)) / θ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hη_le hcr0.le) hθ0.le
      _ = cr * δ / (2 * cr + 1) := by field_simp
      _ ≤ δ / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hδ_le_ε : δ ≤ ε / 2 := min_le_right _ _
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
    have he0 : e ≠ 0 := (Nat.mem_divisors.mp he).2
    have he_le : e ≤ d := Nat.le_of_dvd (by omega) hed
    constructor
    · rintro ⟨_, hk⟩; exact ⟨hk, he0⟩
    · rintro ⟨hk, _⟩
      have hk1 : 1 ≤ k := Nat.pos_of_dvd_of_pos hk (by omega)
      have hke : k ≤ e := Nat.le_of_dvd (by omega) hk
      exact ⟨⟨hk1, hke.trans hdy⟩, hk⟩
  rw [Finset.sum_congr rfl fun e he => by rw [hce e he, Finset.mul_sum]]
  have hexpand : ∀ e ∈ d.divisors,
      (∑ k ∈ e.divisors, ((μ (d / e) : ℤ) : ℂ) * b k) =
        ∑ k ∈ Finset.Icc 1 d, if k ∣ e then ((μ (d / e) : ℤ) : ℂ) * b k else 0 := by
    intro e he
    have hed : e ≤ d := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp he).1
    have he0 : 0 < e := Nat.pos_of_ne_zero (Nat.mem_divisors.mp he).2
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
        have hanti := Nat.sum_divisorsAntidiagonal'
          (f := fun x _ => ((μ x : ℤ) : ℂ) * b k) (n := m)
        exact hanti
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
    push_neg at hle
    have h0 : ‖RHTower.mollifiedZetaCoeff b y e‖ = 0 := le_antisymm hle (norm_nonneg _)
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
  set Bsum : ℝ := ∑ d ∈ Finset.Icc 1 y, ‖b d‖
  -- Choose `σ > 0` large enough that `((d₀ + 1) / d₀)^σ > 2 Bsum / ‖b d₀‖ + 1`.
  set K : ℝ := 2 * Bsum / ‖b d₀‖ + 2
  have hK1 : 1 < K := by
    have : 0 ≤ 2 * Bsum / ‖b d₀‖ := div_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (norm_nonneg _)
    linarith
  have hratio : 1 < ((d₀ : ℝ) + 1) / (d₀ : ℝ) := by
    have hd₀_pos : (0 : ℝ) < d₀ := by exact_mod_cast hd₀1
    rw [one_lt_div hd₀_pos]; linarith
  set σ : ℝ := Real.log K / Real.log (((d₀ : ℝ) + 1) / (d₀ : ℝ))
  have hσ0 : 0 < σ := div_pos (Real.log_pos hK1) (Real.log_pos hratio)
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
            have hbase_le : ((d : ℝ) / (d₀ : ℝ)) ^ (-σ) ≤ 1 / K := by
              have h1 : (((d₀ : ℝ) + 1) / (d₀ : ℝ)) ^ (-σ) = 1 / K := by
                rw [Real.rpow_def_of_pos (by linarith), show Real.log (((d₀ : ℝ) + 1) / d₀) * (-σ) =
                  -Real.log K by dsimp [σ]; have := (Real.log_pos hratio).ne'; field_simp,
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
      _ = Bsum / K := by ring
  have hbd₀_eq : b d₀ = -∑ d ∈ (Finset.Icc 1 y).erase d₀,
      (((d₀ : ℝ) ^ σ : ℝ) : ℂ) * (b d * ((d : ℝ) : ℂ) ^ (-(σ : ℂ))) :=
    eq_neg_of_add_eq_zero_left hmul
  have hnorm_eq : ‖b d₀‖ ≤ Bsum / K := by rw [hbd₀_eq, norm_neg]; exact htail_norm
  have hbd₀_pos : 0 < ‖b d₀‖ := norm_pos_iff.mpr hbd₀
  have hK_pos : 0 < K := by linarith
  have hcontra : ‖b d₀‖ * K ≤ Bsum := (le_div_iff₀ hK_pos).mp hnorm_eq
  have hK_def : ‖b d₀‖ * K = 2 * Bsum + 2 * ‖b d₀‖ := by
    dsimp [K]; field_simp; ring
  have hBsum0 : 0 ≤ Bsum := Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

theorem intervalIntegrable_log_norm_edPoly_criticalLine (b : ℕ → ℂ) (y : ℕ) (T₁ T₂ : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => Real.log ‖RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      volume T₁ T₂ := by
  have hs : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have han : AnalyticOnNhd ℂ (RHTower.edPoly b (Finset.Icc 1 y)) Set.univ :=
    RHTower.analyticOnNhd_edPoly b hs
  have hmer : MeromorphicOn
      (fun t : ℝ => RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
      (uIcc T₁ T₂) := by
    intro t _
    have hline : AnalyticAt ℂ (fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) t :=
      analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
    exact ((han _ (Set.mem_univ _)).comp hline).meromorphicAt
  exact hmer.intervalIntegrable_log_norm

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
    rw [hed, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    ring
  -- Finiteness of zeros of `Ψ` on `1/2 + i[T, 2T]` gives a.e. nonvanishing.
  have hs : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have han : AnalyticOnNhd ℂ (RHTower.edPoly b (Finset.Icc 1 y)) Set.univ :=
    RHTower.analyticOnNhd_edPoly b hs
  obtain ⟨z₀, hz₀⟩ := exists_edPoly_ne_zero_of_exists_coeff_ne_zero hne
  have hcod : (RHTower.edPoly b (Finset.Icc 1 y) ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    han.preimage_zero_mem_codiscreteWithin (x := z₀) hz₀ (Set.mem_univ z₀) isConnected_univ
  let Rect : Set ℂ := uIcc (1 / 2 : ℝ) (1 / 2 : ℝ) ×ℂ uIcc T (2 * T)
  have hRect_fin : {z ∈ Rect | RHTower.edPoly b (Finset.Icc 1 y) z = 0}.Finite := by
    have hcodR := Filter.codiscreteWithin_mono (Set.subset_univ Rect) hcod
    refine ((isCompact_uIcc.reProdIm isCompact_uIcc).finite_sdiff_of_mem_codiscreteWithin
      hcodR).subset fun z hz => ⟨hz.1, by simp [hz.2]⟩
  let Zt : Set ℝ := {t ∈ uIcc T (2 * T) |
    RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 0}
  have hZt_fin : Zt.Finite := by
    refine hRect_fin.preimage (fun t₁ _ t₂ _ h => ?_) |>.subset fun t ht => ?_
    · have := congrArg Complex.im h; simpa using this
    · exact ⟨Complex.mem_reProdIm.mpr ⟨by simp, by simpa using ht.1⟩, ht.2⟩
  have hae : ∀ᵐ t ∂volume, t ∈ uIoc T (2 * T) →
      Real.log ‖RHTower.edPoly (fun d => (lam : ℂ) * b d) (Finset.Icc 1 y)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ =
        Real.log lam +
          Real.log ‖RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    have hmeas0 : volume Zt = 0 := hZt_fin.measure_zero volume
    filter_upwards [ae_iff.mpr hmeas0] with t htnot htI
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
  have h1 : (1 / T) * (lam ^ 2 * ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      lam ^ 2 * ((1 / T) * ∫ t in T..(2 * T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) := by ring
  rw [h1, Real.log_mul (pow_ne_zero 2 hlam.ne') (by positivity), Real.log_pow]
  push_cast
  field_simp [hT.ne']
  ring

/-- **Unconditional divergence of the vertical-flow credited Jensen budget.**
Uniformly over all `1 ≤ y ≤ (log T)^{1/8}` and all nonzero coefficient vectors
`(b_1, ..., b_y) ∈ ℂ^y \ {0}` (arbitrary complex coefficients, arbitrary right-half zeros),
`flowCreditedJensenBudget b y T → +∞` as `T → +∞`. -/
theorem eventually_flowCreditedJensenBudget_ge (A : ℝ) :
    ∀ᶠ T in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ (Real.log T) ^ (1 / 8 : ℝ) →
      ∀ b : ℕ → ℂ, (∃ d ∈ Finset.Icc 1 y, b d ≠ 0) →
        A ≤ flowCreditedJensenBudget b y T := by
  set cr : ℝ := roughMollifierConst
  have hcr0 : 0 < cr := roughMollifierConst_pos
  set E : ℝ := Real.exp (2 * max 0 A + 2)
  have hE0 : 0 < E := Real.exp_pos _
  set K : ℝ := max 4 (max (4 * E / cr) (1024 * E))
  have hK4 : 4 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - (1 / 2 : ℝ)) / 2) (ε := (1 / 2 : ℝ) / 600) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [
    Real.tendsto_log_atTop.eventually ((eventually_ge_atTop (max 256 (K ^ 8))).and hsup),
    eventually_gt_atTop 1] with T hTL hT1
  obtain ⟨hLmax, hsupL⟩ := hTL
  have hL256 : 256 ≤ Real.log T := le_trans (le_max_left _ _) hLmax
  have hLK8 : K ^ 8 ≤ Real.log T := le_trans (le_max_right _ _) hLmax
  have hT0 : 0 < T := lt_trans zero_lt_one hT1
  set L : ℝ := Real.log T
  have hL0 : 0 < L := by linarith
  set u : ℝ := L ^ (1 / 8 : ℝ)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hL0 _
  have hu8 : u ^ 8 = L := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
  have hK_le_u : K ≤ u := by
    have h1 : (K ^ (8 : ℕ)) ^ (1 / 8 : ℝ) ≤ L ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hLK8 (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hK0.le,
      show ((8 : ℕ) : ℝ) * (1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one] at h1
  have hu4 : 4 ≤ u := le_trans hK4 hK_le_u
  have hu1 : 1 ≤ u := by linarith
  intro y hy hyle_u b hne
  classical
  have hIcc_ne : (Finset.Icc 1 y).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hy⟩⟩
  obtain ⟨d_max, hd_max, hmax_b⟩ :=
    Finset.exists_max_image (Finset.Icc 1 y) (fun d => ‖b d‖) hIcc_ne
  obtain ⟨d_nz, hd_nz, hbd_nz⟩ := hne
  have hΛpos : 0 < ‖b d_max‖ := lt_of_lt_of_le (norm_pos_iff.mpr hbd_nz) (hmax_b d_nz hd_nz)
  set lam : ℝ := 1 / ‖b d_max‖
  have hlam0 : 0 < lam := one_div_pos.mpr hΛpos
  let b' : ℕ → ℂ := fun d => (lam : ℂ) * b d
  have hb'_le1 : ∀ d ∈ Finset.Icc 1 y, ‖b' d‖ ≤ 1 := by
    intro d hd
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0, lam]
    rw [one_div, inv_mul_le_iff₀ hΛpos, mul_one]
    exact hmax_b d hd
  have hb'_dmax : ‖b' d_max‖ = 1 := by
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0, lam]
    field_simp
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
    have hpow : 4 ^ 7 ≤ u ^ 7 := pow_le_pow_left₀ (by norm_num) hu4 7
    have : 8 * u ≤ u ^ 7 * u := by nlinarith
    have : 8 * u ≤ L := by linarith [show u ^ 7 * u = u ^ 8 by ring, hu8]
    linarith
  have hy_le_expL8 : (y : ℝ) ≤ Real.exp (L / 8) :=
    hyle_u.trans (hu_le_L8.trans ((by linarith : L / 8 ≤ L / 8 + 1).trans (Real.add_one_le_exp _)))
  have hyle_half : (y : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * L) :=
    hy_le_expL8.trans (Real.exp_le_exp.mpr (by linarith))
  set M : ℕ := ⌊Real.exp (((1 / 2 : ℝ) + (1 - (1 / 2 : ℝ)) / 4) * L)⌋₊
  set M₂ : ℕ := ⌊Real.exp (L / 2)⌋₊
  have hyM₂_le_M : y * M₂ ≤ M := by
    apply Nat.le_floor
    push_cast
    calc (y : ℝ) * (M₂ : ℝ)
        ≤ Real.exp (L / 8) * Real.exp (L / 2) :=
          mul_le_mul hy_le_expL8 (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)
            (Real.exp_pos _).le
      _ = Real.exp (((1 / 2 : ℝ) + (1 - (1 / 2 : ℝ)) / 4) * L) := by
          rw [← Real.exp_add]; congr 1; ring
  set D₀ : ℝ := 2 * (y : ℝ) ^ 2 * E
  have hE_ge1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hD₀1 : 1 ≤ D₀ := by
    have : 1 ≤ (y : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hD₀_le_u2 : D₀ ≤ 2 * E * u ^ 2 := by
    have hy2 : (y : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hyle_u 2
    dsimp [D₀]; nlinarith
  have hδLc : 32 / ((1 / 2 : ℝ) / D₀) ≤ (1 - (1 / 2 : ℝ)) / 4 * L := by
    have h1024 : 1024 * E ≤ u :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK_le_u
    have hu_le_u6 : u ≤ u ^ 6 := by
      have : 1 ≤ u ^ 5 := one_le_pow₀ hu1
      nlinarith [show u * u ^ 5 = u ^ 6 by ring]
    have h64 : 32 / ((1 / 2 : ℝ) / D₀) = 64 * D₀ := by field_simp; ring
    rw [h64, ← hu8]
    have hmul : 512 * (2 * E * u ^ 2) = (1024 * E) * u ^ 2 := by ring
    have hu62 : u ^ 6 * u ^ 2 = u ^ 8 := by ring
    nlinarith [mul_le_mul_of_nonneg_right (h1024.trans hu_le_u6) (sq_nonneg u)]
  have hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b' y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + (0 : ℝ) / L)) := by
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
    have hterm : ∀ v ∈ V₂, (1 / (y : ℝ) ^ 3) * (1 / (v : ℝ)) ≤
        ‖RHTower.mollifiedZetaCoeff b' y (e * v)‖ ^ 2 *
          (((e * v : ℕ) : ℝ) ^ (-2 * (1 / 2 + (0 : ℝ) / L))) := by
      intro v hv
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
    have hlogM₂ : L / 2 ≤ Real.log ((M₂ : ℝ) + 1) := by
      have h1 : Real.exp (L / 2) ≤ (M₂ : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (Real.exp (L / 2)); linarith
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    have hV₂_ge : (cr / 2) * u ^ 7 ≤ ∑ v ∈ V₂, (1 / (v : ℝ)) := by
      have hbase := sum_inv_image_roughPart_ge y M₂
      have hdiv : (cr / 2) * u ^ 7 ≤
          Real.log ((M₂ : ℝ) + 1) / Real.exp (1 + RHTower.Sieve.mertensS y) := by
        have h1 : (cr / 2) * u ^ 7 = (L / 2) / (u / cr) := by rw [← hu8]; field_simp; ring
        rw [h1]
        exact div_le_div₀ (by positivity) hlogM₂ (Real.exp_pos _) hmert
      exact hdiv.trans hbase
    have hy3_u3 : (y : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by positivity) hyle_u 3
    have hD₀_cr : D₀ ≤ (cr / 2) * u ^ 4 := by
      have h4E : 4 * E / cr ≤ u :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK_le_u
      have h4E' : 4 * E ≤ cr * u := (div_le_iff₀ hcr0).mp h4E
      have hu_u2 : u ≤ u ^ 2 := by nlinarith
      have h4E'' : 4 * E ≤ cr * u ^ 2 := by nlinarith
      have : 2 * E * u ^ 2 ≤ (cr / 2) * u ^ 4 := by nlinarith [sq_nonneg u]
      exact hD₀_le_u2.trans this
    calc D₀ ≤ (cr / 2) * u ^ 4 := hD₀_cr
      _ = (1 / u ^ 3) * ((cr / 2) * u ^ 7) := by field_simp; ring
      _ ≤ (1 / (y : ℝ) ^ 3) * ((cr / 2) * u ^ 7) :=
          mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) hy3_u3)
            (by positivity)
      _ ≤ (1 / (y : ℝ) ^ 3) * ∑ v ∈ V₂, (1 / (v : ℝ)) :=
          mul_le_mul_of_nonneg_left hV₂_ge (by positivity)
      _ = ∑ v ∈ V₂, (1 / (y : ℝ) ^ 3) * (1 / (v : ℝ)) := Finset.mul_sum _ _ _
      _ ≤ ∑ v ∈ V₂, ‖RHTower.mollifiedZetaCoeff b' y (e * v)‖ ^ 2 *
            (((e * v : ℕ) : ℝ) ^ (-2 * (1 / 2 + (0 : ℝ) / L))) := Finset.sum_le_sum hterm
      _ = ∑ n ∈ V₂.image (fun v => e * v),
            ‖RHTower.mollifiedZetaCoeff b' y n‖ ^ 2 *
              ((n : ℝ) ^ (-2 * (1 / 2 + (0 : ℝ) / L))) := (Finset.sum_image hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hfloor := gaussFloor_general_at_scale (a := 0) (θ₁ := 1 / 2) (L := L) (D₀ := D₀)
    (δ := 1 / 2) le_rfl (by norm_num) (by norm_num) hD₀1 (by norm_num) (by norm_num)
    (by linarith) (by linarith) hδLc (by linarith) hy hyle_half hb'_le1 hD_ge
  rw [Real.exp_log hT0] at hfloor
  have hzero_div : ∀ t : ℝ, (((1 / 2 + (0 : ℝ) / L : ℝ) : ℂ) + (t : ℂ) * I) =
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := fun _ => by simp
  simp only [hzero_div] at hfloor
  have hD₀_sub_ge : (y : ℝ) ^ 2 * E ≤ D₀ - 1 / 2 := by
    have : 1 ≤ (y : ℝ) ^ 2 * E := mul_le_mul hy1 (by linarith) (by norm_num) (by positivity) |>
      fun h => by simpa using h
    dsimp [D₀]; linarith
  have hmsq_b'_ge : ((y : ℝ) ^ 2 * E) * T ≤ ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right hD₀_sub_ge hT0.le).trans hfloor
  have hmsq_b'_pos : 0 < ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) hmsq_b'_ge
  -- Rescale back to show the mean square for `b` is also strictly positive.
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
      rw [hed, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
      ring
    rw [heq] at hmsq_b'_pos
    exact pos_of_mul_pos_right hmsq_b'_pos (sq_nonneg lam)
  rw [← flowCreditedJensenBudget_smul hT0 hlam0 hne hmsq_b_pos]
  -- Upper-bound the mollifier log-integral for `b'` by `log y`.
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
    rw [Real.log_mul (pow_ne_zero 2 hy0.ne') hE0.ne', Real.log_pow,
      show Real.log E = 2 * max 0 A + 2 by dsimp [E]; rw [Real.log_exp]] at hlog
    push_cast at hlog
    linarith
  change A ≤ (1 / 2 : ℝ) * Real.log ((1 / T) * ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) -
    (1 / T) * ∫ t in T..(2 * T),
      Real.log ‖RHTower.edPoly b' (Finset.Icc 1 y) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
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

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
