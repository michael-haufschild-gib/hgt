import GaloisForLFunctions.HilbertianExplicitFormulas.TheSamePointQuantumOfAReflectionConfiguration
import GaloisForLFunctions.RHTower.XiHolomorphicTwoPrimePencilGrowthDichotomy
import GaloisForLFunctions.RHTower.GaussHodgeVerticalExtraction

/-!
# Holomorphic clocks carry no quantum

A clock reads each point of a configuration as a complex number; its pencil is
`P(n) = ∑ m_ρ c(ρ)^n`, and Parseval turns the Cesàro mean square of the pencil into a sum over clock
classes. Two kinds of clocks matter:

* the **holomorphic clock** `e^{λ(s - 1/2)}`, the only kind an explicit formula produces;
* the **ordinate clock** `e^{2itλ Im s}` (for real `t`), the product of a holomorphic clock at `s` and
  at its line reflection: a same-point (holomorphic × antiholomorphic) quantity.

The holomorphic clock has modulus `exp (Re λ · (Re s - 1/2) - Im λ · Im s)`. On a configuration with
line-reflection and conjugation symmetry every sign pattern of the two terms occurs, so its pencil
has bounded Cesàro mean square exactly when both terms vanish at every point
(`cesaroBounded_holomorphicClock_iff`). For a real frequency this is criticality, which by the
quantum law is `O < 2`: the holomorphic excess is finite exactly on critical configurations and
infinite otherwise, so it never carries the finite quantum `2`.

The ordinate clock is unimodular. Its Cesàro mean square converges to the sum over clock classes of
`m_ρ m_ρ'`, which is `∑ m² + O + A_t`, where `O` is the collision charge and `A_t ≥ 0` the aliasing
between distinct ordinates; `A_t = 0` at every non-resonant frequency
(`tendsto_cesaro_ordinateClock`). The quantum lives on the same-point side.
-/

open Complex Filter Topology Finset

namespace GaloisForLFunctions.HilbertianExplicitFormulas

noncomputable section

/-! ## Pencils with positive multiplicities -/

/-- Cesàro mean square of a finite pencil with natural multiplicities. -/
def cesaroMeanSquare {ι : Type*} (S : Finset ι) (m : ι → ℕ) (c : ι → ℂ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖∑ i ∈ S, (m i : ℂ) * c i ^ n‖ ^ 2

/-- The Cesàro mean square stays bounded. -/
def CesaroBounded {ι : Type*} (S : Finset ι) (m : ι → ℕ) (c : ι → ℂ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, cesaroMeanSquare S m c N ≤ C

/-- Unimodular (or contracting) clocks give a bounded Cesàro mean square. -/
theorem cesaroBounded_of_norm_le_one {ι : Type*} (S : Finset ι) (m : ι → ℕ) (c : ι → ℂ)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ 1) : CesaroBounded S m c := by
  refine ⟨(∑ i ∈ S, (m i : ℝ)) ^ 2, fun N => ?_⟩
  have hterm : ∀ n, ‖∑ i ∈ S, (m i : ℂ) * c i ^ n‖ ^ 2 ≤ (∑ i ∈ S, (m i : ℝ)) ^ 2 := by
    intro n
    have hle : ‖∑ i ∈ S, (m i : ℂ) * c i ^ n‖ ≤ ∑ i ∈ S, (m i : ℝ) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (hc i hi))
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaroMeanSquare]; positivity
  · rw [cesaroMeanSquare]
    calc (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖∑ i ∈ S, (m i : ℂ) * c i ^ n‖ ^ 2
        ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, (∑ i ∈ S, (m i : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hterm n) (by positivity)
      _ = (∑ i ∈ S, (m i : ℝ)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp

/-- A bounded Cesàro mean square forces `|P(n)|² ≤ C (n + 1)`. -/
theorem norm_sq_pencil_le_of_cesaroBounded {ι : Type*} {S : Finset ι} {m : ι → ℕ} {c : ι → ℂ}
    {C : ℝ} (hC : ∀ N : ℕ, cesaroMeanSquare S m c N ≤ C) (n : ℕ) :
    ‖∑ i ∈ S, (m i : ℂ) * c i ^ n‖ ^ 2 ≤ C * (n + 1) := by
  have h := hC (n + 1)
  rw [cesaroMeanSquare] at h
  have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hsum : ∑ k ∈ range (n + 1), ‖∑ i ∈ S, (m i : ℂ) * c i ^ k‖ ^ 2 ≤ C * (n + 1) := by
    rw [inv_mul_le_iff₀ hpos] at h
    push_cast at h
    linarith
  calc ‖∑ i ∈ S, (m i : ℂ) * c i ^ n‖ ^ 2
      ≤ ∑ k ∈ range (n + 1), ‖∑ i ∈ S, (m i : ℂ) * c i ^ k‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ‖∑ i ∈ S, (m i : ℂ) * c i ^ k‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.self_mem_range_succ n)
    _ ≤ C * (n + 1) := hsum

/-- **Dominant modes.** With positive multiplicities, one clock of modulus `> 1` makes the Cesàro mean
square unbounded: the top-modulus fibre has a positive aggregated multiplicity, so `P(n)/r^n` does not
tend to `0`, while a bounded mean square forces `|P(n)|² ≤ C (n+1)`. -/
theorem not_cesaroBounded_of_one_lt_norm {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (m : ι → ℕ) (c : ι → ℂ) (hm : ∀ i ∈ S, 0 < m i) {i₀ : ι} (hi₀ : i₀ ∈ S)
    (h1 : 1 < ‖c i₀‖) : ¬ CesaroBounded S m c := by
  rintro ⟨C, hC⟩
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S (fun i => ‖c i‖) ⟨i₀, hi₀⟩
  set r := ‖c j‖ with hr_def
  have hr1 : 1 < r := h1.trans_le (hjmax i₀ hi₀)
  have hr : 0 < r := zero_lt_one.trans hr1
  -- The normalized pencil does not decay.
  have hD : j ∈ S.filter fun i => ‖c i‖ = r := Finset.mem_filter.mpr ⟨hjS, rfl⟩
  have hfiber : ∃ u ∈ (S.filter fun i => ‖c i‖ = r).image (fun i => c i / (r : ℂ)),
      RHTower.finiteExponentialFiberCoefficient (S.filter fun i => ‖c i‖ = r)
        (fun i => (m i : ℂ)) (fun i => c i / (r : ℂ)) u ≠ 0 := by
    refine ⟨c j / (r : ℂ), Finset.mem_image_of_mem _ hD, ?_⟩
    rw [RHTower.finiteExponentialFiberCoefficient, ← Nat.cast_sum, Nat.cast_ne_zero]
    refine Nat.pos_iff_ne_zero.mp ((hm j hjS).trans_le ?_)
    exact Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨hD, rfl⟩)
  apply RHTower.not_tendsto_normalized_finitePencil_of_dominantFiber S (fun i => (m i : ℂ)) c hr
    (fun i hi => hjmax i hi) hfiber
  -- A bounded mean square makes it decay.
  set x : ℕ → ℂ := fun n => ∑ i ∈ S, (m i : ℂ) * (c i / (r : ℂ)) ^ n
  have hx : ∀ n, x n = (∑ i ∈ S, (m i : ℂ) * c i ^ n) / (r : ℂ) ^ n := by
    intro n
    simp only [x, div_pow, Finset.sum_div, mul_div_assoc]
  have hbound : ∀ n, ‖x n‖ ^ 2 ≤ C * ((n : ℝ) / (r ^ 2) ^ n + 1 / (r ^ 2) ^ n) := by
    intro n
    rw [hx, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_pow,
      ← pow_mul, mul_comm n 2, pow_mul]
    have hrn : 0 < (r ^ 2) ^ n := by positivity
    rw [div_le_iff₀ hrn]
    calc ‖∑ i ∈ S, (m i : ℂ) * c i ^ n‖ ^ 2 ≤ C * (n + 1) :=
          norm_sq_pencil_le_of_cesaroBounded hC n
      _ = C * ((n : ℝ) / (r ^ 2) ^ n + 1 / (r ^ 2) ^ n) * (r ^ 2) ^ n := by
          field_simp
  have hr2 : 1 < r ^ 2 := one_lt_pow₀ hr1 two_ne_zero
  have hlim : Tendsto (fun n : ℕ => C * ((n : ℝ) / (r ^ 2) ^ n + 1 / (r ^ 2) ^ n))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / (r ^ 2) ^ n) atTop (𝓝 0) := by
      simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 hr2
    have h2 : Tendsto (fun n : ℕ => 1 / (r ^ 2) ^ n) atTop (𝓝 0) := by
      have hrw : ∀ n : ℕ, 1 / (r ^ 2) ^ n = ((r ^ 2)⁻¹) ^ n := fun n => by
        rw [inv_pow, one_div]
      simp_rw [hrw]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hr2)
    simpa using (h1.add h2).const_mul C
  have hsq : Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) hbound hlim
  have hnorm : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-! ## Holomorphic clocks -/

/-- The holomorphic clock `e^{λ(s - 1/2)}`; at `λ = 2 log p` it is the prime clock `p^{2(s-1/2)}`. -/
def holomorphicClock (l : ℂ) (s : ℂ) : ℂ := Complex.exp (l * (s - 1 / 2))

theorem norm_holomorphicClock (l s : ℂ) :
    ‖holomorphicClock l s‖ = Real.exp (l.re * (s.re - 1 / 2) - l.im * s.im) := by
  rw [holomorphicClock, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

namespace ReflectionConfiguration

variable (Z : ReflectionConfiguration)

/-- **Clock classification.** The holomorphic pencil of a reflection configuration has bounded Cesàro
mean square exactly when `Re λ · (Re ρ - 1/2) = 0` and `Im λ · Im ρ = 0` at every point. -/
theorem cesaroBounded_holomorphicClock_iff (l : ℂ) :
    CesaroBounded Z.support Z.mult (holomorphicClock l) ↔
      ∀ ρ ∈ Z.support, l.re * (ρ.re - 1 / 2) = 0 ∧ l.im * ρ.im = 0 := by
  classical
  constructor
  · intro hB
    by_contra hne
    simp only [not_forall, not_and] at hne
    obtain ⟨ρ, hρ, hab⟩ := hne
    set a := l.re * (ρ.re - 1 / 2)
    set b := l.im * ρ.im
    -- The four points of the quartet have exponents `±a ± b`; one of them is positive.
    have hexp : ∃ σ ∈ Z.support, 0 < l.re * (σ.re - 1 / 2) - l.im * σ.im := by
      have hR : RHTower.lineReflect ρ ∈ Z.support := Z.reflect_mem ρ hρ
      have hC : (starRingEnd ℂ) ρ ∈ Z.support := Z.conj_mem ρ hρ
      have hRC : RHTower.lineReflect ((starRingEnd ℂ) ρ) ∈ Z.support :=
        Z.reflect_mem _ hC
      have eR : l.re * ((RHTower.lineReflect ρ).re - 1 / 2) -
          l.im * (RHTower.lineReflect ρ).im = -a - b := by
        simp only [a, b, RHTower.lineReflect_re, lineReflect_im]; ring
      have eC : l.re * (((starRingEnd ℂ) ρ).re - 1 / 2) -
          l.im * ((starRingEnd ℂ) ρ).im = a + b := by
        simp only [a, b, Complex.conj_re, Complex.conj_im]; ring
      have eRC : l.re * ((RHTower.lineReflect ((starRingEnd ℂ) ρ)).re - 1 / 2) -
          l.im * (RHTower.lineReflect ((starRingEnd ℂ) ρ)).im = -a + b := by
        simp only [a, b, RHTower.lineReflect_re, lineReflect_im, Complex.conj_re,
          Complex.conj_im]; ring
      by_cases h1 : 0 < a - b
      · exact ⟨ρ, hρ, h1⟩
      by_cases h2 : 0 < -a - b
      · exact ⟨_, hR, eR ▸ h2⟩
      by_cases h3 : 0 < a + b
      · exact ⟨_, hC, eC ▸ h3⟩
      by_cases h4 : 0 < -a + b
      · exact ⟨_, hRC, eRC ▸ h4⟩
      simp only [not_lt] at h1 h2 h3 h4
      have ha : a = 0 := by linarith
      have hb : b = 0 := by linarith
      exact absurd hb (hab ha)
    obtain ⟨σ, hσ, hpos⟩ := hexp
    refine not_cesaroBounded_of_one_lt_norm Z.support Z.mult (holomorphicClock l)
      Z.mult_pos hσ ?_ hB
    rw [norm_holomorphicClock]
    have := Real.exp_lt_exp.mpr hpos
    rwa [Real.exp_zero] at this
  · intro h
    apply cesaroBounded_of_norm_le_one
    intro ρ hρ
    rw [norm_holomorphicClock, (h ρ hρ).1, (h ρ hρ).2, sub_zero, Real.exp_zero]

/-- **Exchange law.** For a nonzero real frequency the holomorphic pencil is bounded exactly on
critical configurations, i.e. exactly below the quantum: its excess is `0` or `∞`, never finite and
positive. -/
theorem cesaroBounded_holomorphicClock_real_iff {t : ℝ} (ht : t ≠ 0) :
    CesaroBounded Z.support Z.mult (holomorphicClock t) ↔ Z.collisionCharge < 2 := by
  have hiff : Z.IsCritical ↔ Z.collisionCharge < 2 := (Z.isCritical_tfae).out 0 2
  rw [cesaroBounded_holomorphicClock_iff, ← hiff]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, and_true, IsCritical]
  refine forall₂_congr fun ρ _ => ?_
  rw [mul_eq_zero, or_iff_right ht, sub_eq_zero]

/-- A holomorphic clock with non-real frequency grows already on critical configurations as soon as
some point is off the real axis: conjugation supplies the mirrored ordinate. -/
theorem not_cesaroBounded_holomorphicClock_of_im_ne_zero {l : ℂ} (hl : l.im ≠ 0)
    {ρ : ℂ} (hρ : ρ ∈ Z.support) (him : ρ.im ≠ 0) :
    ¬ CesaroBounded Z.support Z.mult (holomorphicClock l) := by
  rw [cesaroBounded_holomorphicClock_iff]
  intro h
  exact mul_ne_zero hl him (h ρ hρ).2

/-! ## Ordinate clocks -/

/-- The ordinate clock `e^{2it Im s}`: the holomorphic clock at `s` times the holomorphic clock at the
line reflection of `s`. -/
def ordinateClock (t : ℝ) (s : ℂ) : ℂ := Complex.exp (2 * t * s.im * I)

theorem holomorphicClock_mul_lineReflect (t : ℝ) (s : ℂ) :
    holomorphicClock t s * holomorphicClock t (RHTower.lineReflect s) = ordinateClock t s := by
  rw [holomorphicClock, holomorphicClock, ← Complex.exp_add, ordinateClock]
  congr 1
  have hs : s = s.re + s.im * I := (Complex.re_add_im s).symm
  rw [RHTower.lineReflect]
  conv_lhs => rw [hs]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem norm_ordinateClock (t : ℝ) (s : ℂ) : ‖ordinateClock t s‖ = 1 := by
  rw [ordinateClock, Complex.norm_exp]
  simp

/-- Aliasing of the ordinate clock: weighted ordered pairs on distinct horizontal lines that the
clock cannot separate. -/
def aliasCharge (t : ℝ) : ℕ :=
  ∑ ρ ∈ Z.support, ∑ ρ' ∈ Z.support with
    ρ'.im ≠ ρ.im ∧ ordinateClock t ρ' = ordinateClock t ρ, Z.mult ρ * Z.mult ρ'

/-- A frequency is non-resonant when it separates all distinct ordinates. -/
def NonResonant (t : ℝ) : Prop :=
  ∀ ρ ∈ Z.support, ∀ ρ' ∈ Z.support, ρ'.im ≠ ρ.im → ordinateClock t ρ' ≠ ordinateClock t ρ

theorem aliasCharge_eq_zero_of_nonResonant {t : ℝ} (ht : Z.NonResonant t) :
    Z.aliasCharge t = 0 := by
  apply Finset.sum_eq_zero
  intro ρ hρ
  apply Finset.sum_eq_zero
  intro ρ' hρ'
  obtain ⟨hρ'S, hne, heq⟩ := Finset.mem_filter.mp hρ'
  exact absurd heq (ht ρ hρ ρ' hρ'S hne)

/-- The class-pair sum `∑_{ρ, ρ' : same clock} m_ρ m_ρ'` splits into the diagonal, the collision
charge and the aliasing. -/
theorem classPairSum_eq (t : ℝ) :
    ∑ ρ ∈ Z.support, ∑ ρ' ∈ Z.support with ordinateClock t ρ' = ordinateClock t ρ,
        Z.mult ρ * Z.mult ρ' =
      ∑ ρ ∈ Z.support, Z.mult ρ ^ 2 + Z.collisionCharge + Z.aliasCharge t := by
  classical
  rw [collisionCharge, aliasCharge, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [partnerMult, Finset.mul_sum]
  -- Split the class of `ρ` into `ρ` itself, its horizontal partners and its aliases.
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Z.support.filter fun ρ' => ordinateClock t ρ' = ordinateClock t ρ)
    (fun ρ' => ρ'.im = ρ.im) (fun ρ' => Z.mult ρ * Z.mult ρ')
  rw [← hsplit, Finset.filter_filter, Finset.filter_filter]
  have hsame : (Z.support.filter fun ρ' =>
      ordinateClock t ρ' = ordinateClock t ρ ∧ ρ'.im = ρ.im) =
      Z.support.filter fun ρ' => ρ'.im = ρ.im := by
    ext ρ'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, -, him⟩; exact ⟨h, him⟩
    · rintro ⟨h, him⟩; exact ⟨h, by rw [ordinateClock, ordinateClock, him], him⟩
  have halias : (Z.support.filter fun ρ' =>
      ordinateClock t ρ' = ordinateClock t ρ ∧ ¬ ρ'.im = ρ.im) =
      Z.support.filter fun ρ' => ρ'.im ≠ ρ.im ∧ ordinateClock t ρ' = ordinateClock t ρ := by
    ext ρ'
    simp only [Finset.mem_filter]
    tauto
  rw [hsame, halias]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (Z.support.filter fun ρ' => ρ'.im = ρ.im)
    (fun ρ' => ρ' = ρ), Finset.filter_filter, Finset.filter_filter]
  have hself : (Z.support.filter fun ρ' => ρ'.im = ρ.im ∧ ρ' = ρ) = {ρ} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, -, rfl⟩; rfl
    · rintro rfl; exact ⟨hρ, rfl, rfl⟩
  rw [hself, Finset.sum_singleton, sq]

/-- **Parseval for the ordinate clock.** The Cesàro mean square of the ordinate pencil converges to
`∑ m² + O + A_t`; at a non-resonant frequency its excess over the diagonal is exactly the collision
charge. -/
theorem tendsto_cesaro_ordinateClock (t : ℝ) :
    Tendsto (cesaroMeanSquare Z.support Z.mult (ordinateClock t)) atTop
      (𝓝 ((∑ ρ ∈ Z.support, Z.mult ρ ^ 2 + Z.collisionCharge + Z.aliasCharge t : ℕ) : ℝ)) := by
  classical
  let ι := { ρ // ρ ∈ Z.support }
  have h := RHTower.tendsto_tsum_pencil_cesaro_norm_sq (ι := ι)
    (fun ρ => (Z.mult ρ.1 : ℂ)) (fun ρ => ordinateClock t ρ.1)
    (Summable.of_finite) (fun ρ => norm_ordinateClock t ρ.1)
  have hpencil : ∀ n : ℕ, (∑' ρ : ι, (Z.mult ρ.1 : ℂ) * ordinateClock t ρ.1 ^ n) =
      ∑ ρ ∈ Z.support, (Z.mult ρ : ℂ) * ordinateClock t ρ ^ n := by
    intro n
    rw [tsum_fintype]
    exact Finset.sum_coe_sort Z.support (fun ρ => (Z.mult ρ : ℂ) * ordinateClock t ρ ^ n)
  have hlimit : ((∑' pq : ι × ι, if ordinateClock t pq.1.1 = ordinateClock t pq.2.1 then
      star ((Z.mult pq.1.1 : ℂ)) * (Z.mult pq.2.1 : ℂ) else 0).re) =
      ((∑ ρ ∈ Z.support, Z.mult ρ ^ 2 + Z.collisionCharge + Z.aliasCharge t : ℕ) : ℝ) := by
    rw [← Z.classPairSum_eq t, tsum_fintype, Fintype.sum_prod_type]
    have hinner : ∀ ρ : ι, (∑ ρ' : ι, if ordinateClock t ρ.1 = ordinateClock t ρ'.1 then
        star ((Z.mult ρ.1 : ℂ)) * (Z.mult ρ'.1 : ℂ) else 0) =
        (((∑ ρ' ∈ Z.support with ordinateClock t ρ' = ordinateClock t ρ.1,
          Z.mult ρ.1 * Z.mult ρ' : ℕ)) : ℂ) := by
      intro ρ
      rw [Finset.sum_filter, Nat.cast_sum]
      rw [← Finset.sum_coe_sort Z.support]
      apply Finset.sum_congr rfl
      intro ρ' _
      by_cases hc : ordinateClock t ρ'.1 = ordinateClock t ρ.1
      · rw [if_pos hc.symm, if_pos hc]; simp
      · rw [if_neg (Ne.symm hc), if_neg hc]; simp
    simp_rw [hinner]
    rw [← Nat.cast_sum, Complex.natCast_re]
    congr 1
    exact Finset.sum_coe_sort Z.support
      (fun ρ => ∑ ρ' ∈ Z.support with ordinateClock t ρ' = ordinateClock t ρ,
        Z.mult ρ * Z.mult ρ')
  rw [hlimit] at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  simp only [cesaroMeanSquare, hpencil]

/-- At a non-resonant frequency the ordinate excess converges to the collision charge itself. -/
theorem tendsto_cesaro_ordinateClock_sub_diag_of_nonResonant {t : ℝ} (ht : Z.NonResonant t) :
    Tendsto (fun N => cesaroMeanSquare Z.support Z.mult (ordinateClock t) N -
        ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) ^ 2) atTop (𝓝 (Z.collisionCharge : ℝ)) := by
  have h := (Z.tendsto_cesaro_ordinateClock t).sub_const (∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) ^ 2)
  rw [Z.aliasCharge_eq_zero_of_nonResonant ht] at h
  convert h using 2
  push_cast; ring

end ReflectionConfiguration

end

end GaloisForLFunctions.HilbertianExplicitFormulas
