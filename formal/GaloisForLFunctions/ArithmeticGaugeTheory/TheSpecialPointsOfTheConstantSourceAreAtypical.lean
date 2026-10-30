import GaloisForLFunctions.ArithmeticGaugeTheory.TheTypicalExponentIsOneHalf
import GaloisForLFunctions.ArithmeticGaugeTheory.TheDirichletPointsCancelThroughPeriodicity
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent

/-!
# The special points of the constant source are atypical

The constant source `a ≡ 1` read at a gauge point `x` has partial sums `Σ_{n ≤ N} χ_x(n)`. Its exponent
is `1/2` at Haar-almost every point. On the special locus, the Dirichlet gauge points and their vertical
shifts, it is `0` or `1`, never `1/2`.

* **Tail invariance** (`isTailInvariant_one`). Changing one prime coordinate inverts through the local
  factor `1 − χ(p) p^{−s}`: the partial sums prime to `p` are `B(N) − χ(p) B(N/p)`, and the new sums are a
  geometric series in them (`gaugePowerBound_one_of_agree_off`). So the exponent ignores finitely many
  primes.
* **The typical exponent** (`ae_gaugeExponent_one_eq_half`). The top-prime block and the zero–one law
  give exponent `1/2` almost surely.
* **The special locus** (`gaugeExponent_one_dirichletGauge_verticalShift`,
  `gaugeExponent_one_principal_verticalShift`). Along the vertical line through a nonprincipal Dirichlet
  point the exponent is `0`: periodicity cancels. Along the line through a principal one, which is a
  finite modification of the trivial point, it is `1`: the pole. So no special point is typical
  (`gaugeExponent_one_special_ne_typical`).
* **Typical modulo the pole** (`trivialPoint_atypical_one_and_rh_iff_typical_moebius`). For the
  constant source the trivial point carries the pole and has exponent `1`. For the Möbius source, its
  inverse, the pole becomes a zero and RH says the trivial point is typical.

The dichotomy `0` or `1` is the gauge form of additive structure at a special point: periodicity with a
nonprincipal character cancels, invariance under the successor is coherent. Neither mechanism produces
the typical value `1/2`, which is why typicality at the trivial point must come from the source, not
from the point.
-/

open MeasureTheory Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### One prime does not move the exponent -/

/-- A single term of the inversion is geometric in `p^{−θ}`. -/
theorem norm_div_pow_le {g : ℕ → ℂ} (hg0 : g 0 = 0) {p : ℕ} (hp : p.Prime) {C θ : ℝ}
    (hθ : 0 < θ) (hC : 0 ≤ C) (hS : ∀ M, ‖g M‖ ≤ C * ((M : ℝ) + 1) ^ θ) (N k : ℕ) :
    ‖g (N / p ^ k)‖ ≤ C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * ((p : ℝ) ^ (-θ)) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp0 k
  have hrhs : 0 ≤ C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * ((p : ℝ) ^ (-θ)) ^ k := by positivity
  rcases Nat.eq_zero_or_pos (N / p ^ k) with hM | hM
  · rw [hM, hg0, norm_zero]
    exact hrhs
  · set M := N / p ^ k with hMdef
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    -- `M + 1 ≤ 2M ≤ 2(N + 1)/p^k`.
    have hMle : (M : ℝ) ≤ ((N : ℝ) + 1) / (p : ℝ) ^ k := by
      have h1 : (M : ℝ) ≤ (N : ℝ) / ((p ^ k : ℕ) : ℝ) := Nat.cast_div_le
      have h2 : (N : ℝ) / ((p ^ k : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / (p : ℝ) ^ k := by
        push_cast
        exact div_le_div_of_nonneg_right (by linarith) hpk.le
      linarith
    have hpow : ((M : ℝ) + 1) ^ θ ≤ (2 * (((N : ℝ) + 1) / (p : ℝ) ^ k)) ^ θ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hθ.le
    have hsplit : (2 * (((N : ℝ) + 1) / (p : ℝ) ^ k)) ^ θ =
        2 ^ θ * ((N : ℝ) + 1) ^ θ * ((p : ℝ) ^ (-θ)) ^ k := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.div_rpow (by positivity) hpk.le,
        Real.rpow_neg hp0.le, inv_pow, ← Real.rpow_pow_comm hp0.le]
      field_simp
    calc ‖g M‖ ≤ C * ((M : ℝ) + 1) ^ θ := hS M
      _ ≤ C * (2 * (((N : ℝ) + 1) / (p : ℝ) ^ k)) ^ θ := mul_le_mul_of_nonneg_left hpow hC
      _ = C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * ((p : ℝ) ^ (-θ)) ^ k := by rw [hsplit]; ring

/-- The twisted sums prime to `p` see only the coordinates other than `p`. -/
theorem coprimeTwistSum_singleton_congr {p : ℕ} {x x' : GaugeTorus}
    (h : ∀ q, q.Prime → q ≠ p → twist x' q = twist x q) (N : ℕ) :
    coprimeTwistSum {p} x' N = coprimeTwistSum {p} x N := by
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨hnI, hnp⟩ := mem_filter.mp hn
  refine twist_eq_of_primes (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hnI).1) fun q hq hqn => ?_
  exact h q hq fun hqp => hnp p (mem_singleton_self p) (hqp ▸ hqn)

/-- Power bounds of the constant source, in terms of `B_∅`. -/
theorem gaugePowerBound_one_iff {y : GaugeTorus} {θ : ℝ} (hθ : 0 ≤ θ) :
    GaugePowerBound oneSource y θ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖coprimeTwistSum ∅ y N‖ ≤ C * ((N : ℝ) + 1) ^ θ := by
  simp only [GaugePowerBound, sum_range_oneSource]
  constructor
  · rintro ⟨C, hC, hb⟩
    refine ⟨C + 1, by positivity, fun N => ?_⟩
    have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ θ := Real.one_le_rpow (by linarith [N.cast_nonneg (α := ℝ)]) hθ
    have := norm_sub_le (1 + coprimeTwistSum ∅ y N) 1
    rw [add_sub_cancel_left, norm_one] at this
    nlinarith [hb N]
  · rintro ⟨C, hC, hb⟩
    refine ⟨C + 1, by positivity, fun N => ?_⟩
    have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ θ := Real.one_le_rpow (by linarith [N.cast_nonneg (α := ℝ)]) hθ
    calc ‖1 + coprimeTwistSum ∅ y N‖ ≤ 1 + ‖coprimeTwistSum ∅ y N‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_one]
      _ ≤ (C + 1) * ((N : ℝ) + 1) ^ θ := by nlinarith [hb N]

/-- **One prime.** A power bound of positive exponent for the constant source survives a change of
the gauge point at one prime. -/
theorem gaugePowerBound_one_of_agree_off {p : ℕ} (hp : p.Prime) {x x' : GaugeTorus}
    (h : ∀ q, q.Prime → q ≠ p → twist x' q = twist x q) {θ : ℝ} (hθ : 0 < θ)
    (hb : GaugePowerBound oneSource x θ) : GaugePowerBound oneSource x' θ := by
  have hP : ∀ r ∈ (∅ : Finset ℕ), r.Prime := fun r hr => absurd hr (notMem_empty r)
  have hpP : p ∉ (∅ : Finset ℕ) := notMem_empty p
  rw [gaugePowerBound_one_iff hθ.le] at hb ⊢
  obtain ⟨C, hC, hS⟩ := hb
  -- The sums prime to `p` at `x`: `B_{p}(N) = B(N) − χ_x(p) B(N/p)`.
  have hcop : ∀ M, ‖coprimeTwistSum {p} x M‖ ≤ 2 * C * ((M : ℝ) + 1) ^ θ := by
    intro M
    have hsplit := coprimeTwistSum_eq_split hP hp hpP x M
    rw [insert_empty] at hsplit
    have hMp : (((M / p : ℕ) : ℝ) + 1) ^ θ ≤ ((M : ℝ) + 1) ^ θ := by
      refine Real.rpow_le_rpow (by positivity) ?_ hθ.le
      have : ((M / p : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.div_le_self M p
      linarith
    calc ‖coprimeTwistSum {p} x M‖
        = ‖coprimeTwistSum ∅ x M - twist x p * coprimeTwistSum ∅ x (M / p)‖ := by
          rw [hsplit]; ring_nf
      _ ≤ ‖coprimeTwistSum ∅ x M‖ + ‖twist x p * coprimeTwistSum ∅ x (M / p)‖ := norm_sub_le _ _
      _ ≤ C * ((M : ℝ) + 1) ^ θ + C * ((M : ℝ) + 1) ^ θ := by
          rw [norm_mul, norm_twist, one_mul]
          exact add_le_add (hS M) ((hS _).trans (mul_le_mul_of_nonneg_left hMp hC))
      _ = 2 * C * ((M : ℝ) + 1) ^ θ := by ring
  -- At `x'` the full sums are a geometric series in the coprime sums, which agree.
  set r : ℝ := (p : ℝ) ^ (-θ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  set D := 2 * C * 2 ^ θ * (1 - r)⁻¹ with hD
  have hD0 : 0 ≤ D := by
    have : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith)
    positivity
  refine ⟨D, hD0, fun N => ?_⟩
  have hgeom : ∑ k ∈ range (N + 1), r ^ k ≤ (1 - r)⁻¹ := by
    rw [geom_sum_eq hr1.ne, div_le_iff_of_neg (by linarith : r - 1 < 0)]
    have hne : (1 : ℝ) - r ≠ 0 := by linarith
    have hm : (1 - r)⁻¹ * (r - 1) = -1 := by
      rw [show r - 1 = -(1 - r) by ring, mul_neg, inv_mul_cancel₀ hne]
    rw [hm]
    linarith [pow_nonneg hr0 (N + 1)]
  have hexp := coprimeTwistSum_eq_sum hP hp hpP x' N
  rw [insert_empty] at hexp
  have hK : 0 ≤ 2 * C * 2 ^ θ * ((N : ℝ) + 1) ^ θ := by positivity
  rw [hexp]
  calc ‖∑ k ∈ range (N + 1), twist x' p ^ k * coprimeTwistSum {p} x' (N / p ^ k)‖
      ≤ ∑ k ∈ range (N + 1), ‖twist x' p ^ k * coprimeTwistSum {p} x' (N / p ^ k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ range (N + 1), 2 * C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * r ^ k := by
        refine sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_pow, norm_twist, one_pow, one_mul, coprimeTwistSum_singleton_congr h]
        exact norm_div_pow_le (coprimeTwistSum_zero _ _) hp hθ (by positivity) hcop N k
    _ = 2 * C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * ∑ k ∈ range (N + 1), r ^ k := by rw [mul_sum]
    _ ≤ 2 * C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hK
    _ = D * ((N : ℝ) + 1) ^ θ := by rw [hD]; ring

/-- **The constant source is tail invariant.** -/
theorem isTailInvariant_one : IsTailInvariant oneSource := by
  refine isTailInvariant_of_one_prime fun p hp x x' h => ?_
  have hle : ∀ {y y' : GaugeTorus}, (∀ q, q.Prime → q ≠ p → twist y' q = twist y q) →
      gaugeExponent oneSource y' ≤ gaugeExponent oneSource y := by
    intro y y' hyy
    refine le_of_forall_gt fun θ hθ => ?_
    obtain ⟨θ', hθ'1, hθ'2⟩ := exists_between hθ
    have hθ'0 : 0 < θ' := lt_of_le_of_lt (gaugeExponent_nonneg norm_oneSource_le) hθ'1
    exact lt_of_le_of_lt (gaugeExponent_le hθ'0.le (gaugePowerBound_one_of_agree_off hp hyy
      hθ'0 (gaugePowerBound_of_gaugeExponent_lt norm_oneSource_le hθ'1))) hθ'2
  exact le_antisymm (hle h) (hle fun q hq hqp => (h q hq hqp).symm)

/-! ### Typical and special points -/

theorem norm_oneSource_prime (p : ℕ) (_hp : p.Prime) : ‖oneSource p‖ = 1 := by simp [oneSource]

theorem typicalExponent_one_eq_half : typicalExponent oneSource = 1 / 2 :=
  typicalExponent_eq_half norm_oneSource_le norm_oneSource_prime

/-- **Almost every point is typical for the constant source.** -/
theorem ae_gaugeExponent_one_eq_half : ∀ᵐ x ∂gaugeHaar, gaugeExponent oneSource x = 1 / 2 :=
  ae_gaugeExponent_eq_half norm_oneSource_le norm_oneSource_prime isTailInvariant_one

variable {q : ℕ} [NeZero q]

/-- **Cancellation along the line of a nonprincipal Dirichlet point.** -/
theorem gaugeExponent_one_dirichletGauge_verticalShift (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t : ℝ) : gaugeExponent oneSource (dirichletGauge χ + verticalShift t) = 0 := by
  rw [gaugeExponent_add_verticalShift norm_oneSource_le]
  exact gaugeExponent_one_dirichletGauge χ hχ

/-- **The pole along the line of a principal Dirichlet point.** A principal Dirichlet point is trivial
off the primes of `q`, hence a finite modification of the trivial point. -/
theorem gaugeExponent_one_principal_verticalShift (t : ℝ) :
    gaugeExponent oneSource (dirichletGauge (1 : DirichletCharacter ℂ q) + verticalShift t) = 1 := by
  rw [gaugeExponent_add_verticalShift norm_oneSource_le,
    isTailInvariant_one q.primeFactors 0 _ fun r hr hrq => ?_, gaugeExponent_one_trivial]
  have hcop : Nat.Coprime r q := (Nat.Prime.coprime_iff_not_dvd hr).mpr fun hdvd =>
    hrq (Nat.mem_primeFactors.mpr ⟨hr, hdvd, NeZero.ne q⟩)
  rw [twist_dirichletGauge _ hr.ne_zero hcop, twist_trivialPoint,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime r q).mpr hcop)]

/-- **No special point is typical** for the constant source. -/
theorem gaugeExponent_one_special_ne_typical (χ : DirichletCharacter ℂ q) (t : ℝ) :
    gaugeExponent oneSource (dirichletGauge χ + verticalShift t) ≠ typicalExponent oneSource := by
  rw [typicalExponent_one_eq_half]
  by_cases hχ : χ = 1
  · rw [hχ, gaugeExponent_one_principal_verticalShift]
    norm_num
  · rw [gaugeExponent_one_dirichletGauge_verticalShift χ hχ]
    norm_num

/-- **Typical modulo the pole.** The trivial point is atypical for the constant source, where it
carries the pole; for the Möbius source RH is the statement that it is typical. -/
theorem trivialPoint_atypical_one_and_rh_iff_typical_moebius :
    gaugeExponent oneSource 0 = 1 ∧ typicalExponent oneSource = 1 / 2 ∧
      (RiemannHypothesis ↔ gaugeExponent moebiusSource 0 ≤ typicalExponent moebiusSource) :=
  ⟨gaugeExponent_one_trivial, typicalExponent_one_eq_half,
    riemannHypothesis_iff_trivialPoint_typical⟩

end GaloisForLFunctions.ArithmeticGaugeTheory
