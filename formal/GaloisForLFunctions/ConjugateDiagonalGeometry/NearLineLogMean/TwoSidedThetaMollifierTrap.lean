import GaloisForLFunctions.RHTower.MollifiedMeanSquareGaussianPrimeFloor
import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.RHTower.Sieve.MollifierShortRange
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ClusteringLogMeanAndMollifierEquivalence

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
   For every nonzero Dirichlet polynomial `Ψ(s) = ∑_{d ≤ y} b_d d^{-s}` (`1 ≤ y ≤ (log T)^{1/6}`,
   arbitrary complex coefficients and right-half zeros), Möbius inversion on `[1, y]` produces an
   index `e_* ≤ y` with `‖c_{e_*}‖ ≥ y⁻¹ max_d ‖b_d‖`, and `c_{e_* · v} = c_{e_*}` for all
   `y`-rough `v`, forcing
   `½ log(T⁻¹ ∫_T^{2T} ‖ζΨ(1/2+it)‖² dt) - T⁻¹ ∫_T^{2T} log‖Ψ(1/2+it)‖ dt → +∞`.

3. **Long/supercritical regime (`θ > 1` and `θ → ∞`):**
   Using the holomorphic divided difference `dslope F 0` of
   `F(w) = ζ(ρ₀ + w) Ψ(ρ₀ + w) exp(α w² + w log Y)` around an off-line zero
   `ρ₀ = 1/2 + δ₀ + iγ₀` (`δ₀ > 0`), compact Fubini evaluation of the error-function integral on
   `Re s = 2` produces a localized critical-line spike
   `∫_{γ₀-R}^{γ₀+R} ‖ζΨ(1/2+it)‖² dt ≥ (1/20) δ₀ e^{-2αδ₀²} Y^{2δ₀}`.
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

/-- Multiplying any integer `e` by `roughPart y m` leaves `mollifiedZetaCoeff b y` unchanged
whenever every divisor `d ≤ y` of `e * roughPart y m` must divide `e`. -/
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

/-- Rewrite `smoothPart y m` as a product over `Nat.primesLE y`. -/
theorem smoothPart_eq_prod_primesLE {y m : ℕ} (hm : 1 ≤ m) :
    smoothPart y m = ∏ p ∈ Nat.primesLE y, p ^ (m.factorization p) := by
  unfold smoothPart
  symm
  refine Finset.prod_subset (fun p hp => ?_) (fun p _ hpnot => ?_)
  · obtain ⟨hpm, hpy⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.prime_of_mem_primeFactors hpm, hpy⟩
  · simp only [Finset.mem_filter] at hpnot
    push_neg at hpnot
    by_cases hpm : p ∈ m.primeFactors
    · have hpy := (Nat.mem_primesLE.mp ‹p ∈ Nat.primesLE y›).2
      exact absurd hpy (not_le.mpr (lt_of_not_ge (hpnot hpm)))
    · rw [Nat.factorization_eq_zero_of_not_mem_primeFactors hpm, pow_zero]

theorem factorization_le_self (m p : ℕ) : m.factorization p ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · by_cases hp : p ∈ m.primeFactors
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      calc m.factorization p ≤ 2 ^ (m.factorization p) := (Nat.lt_two_pow_self).le
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
    have hprod := (Fintype.prod_bijective _ (Equiv.refl P).bijective _ _)
    have hps := Finset.prod_univ_sum (t := fun _ : P => Finset.Icc 0 M)
      (f := fun (p : P) (e : ℕ) => (1 / ((p : ℕ) : ℝ)) ^ e)
    rw [hps]
    refine Finset.sum_congr rfl fun g _ => ?_
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
          · have htel : ∀ k ∈ Finset.Ico 2 (y + 1),
                1 / ((k : ℝ) - 1) - 1 / (k : ℝ) =
                (-(1 / ((k + 1 : ℕ) : ℝ) + 1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) + 0) := by
              intro _ _; ring
            have hico := Finset.sum_Ico_sub (fun k : ℕ => -(1 / ((k : ℝ) - 1))) (by omega : 2 ≤ y + 1)
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
    have hmaps : ∀ m ∈ Finset.Icc 1 M, φ m ∈ U ×ˢ V := fun m hm =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hm, Finset.mem_image_of_mem _ hm⟩
    have hinj : Set.InjOn φ (Finset.Icc 1 M) := by
      intro m₁ hm₁ m₂ hm₂ heq
      have h1 := smoothPart_mul_roughPart y (Finset.mem_Icc.mp hm₁).1
      have h2 := smoothPart_mul_roughPart y (Finset.mem_Icc.mp hm₂).1
      have hfst : smoothPart y m₁ = smoothPart y m₂ := congrArg Prod.fst heq
      have hsnd : roughPart y m₁ = roughPart y m₂ := congrArg Prod.snd heq
      omega
    have hval : ∀ m ∈ Finset.Icc 1 M,
        (1 / (m : ℝ)) = (1 / ((φ m).1 : ℝ)) * (1 / ((φ m).2 : ℝ)) := by
      intro m hm
      have h := smoothPart_mul_roughPart y (Finset.mem_Icc.mp hm).1
      simp only [φ]
      rw [← h, Nat.cast_mul]
      ring
    rw [Finset.sum_congr rfl hval]
    exact Finset.sum_le_sum_of_ne_zero (fun m hm _ => hmaps m hm) (fun m₁ hm₁ _ m₂ hm₂ _ h =>
      hinj hm₁ hm₂ h) (fun _ _ _ => by positivity)
      -- Wait: check exact Finset injection lemma name below!
      sorry
  sorry
