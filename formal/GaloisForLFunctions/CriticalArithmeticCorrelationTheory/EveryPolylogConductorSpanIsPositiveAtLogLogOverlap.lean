import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileIsPositiveAtLogLogOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileHasALogarithmicHighConductorGap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileHasSubexponentialConductorFloors

/-!
# Log-log overlap on every polylogarithmic conductor span

A small polylogarithmic block retains any prescribed exponential spectral floor.
Quadratic collar cancellation leaves a growing logarithmic gap above that block.
Orthogonal splitting absorbs the mixed residual at every fixed log-log overlap multiple.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

private theorem conductor_analysis_frame_lower {Q N : ℕ} (hQ : 2 ≤ Q)
    (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hx : x ∈ conductorSubspace Q N) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤
      ∑ m ∈ Icc 1 Q, ⟪normalizedRamanujanHorizonVector m N, x⟫ ^ 2 := by
  by_cases hx0 : x = 0
  · simp only [hx0, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      inner_zero_right, sum_const_zero, le_refl]
  have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  obtain ⟨a, -, hax⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := x)).mp hx
  have hcoef := (half_and_three_halves_riesz_of_log_le hQ hQN hlog a).1
  rw [← hax] at hcoef
  have hnorm : ‖x‖ ^ 2 = ∑ m ∈ Icc 1 Q,
      a m * ⟪normalizedRamanujanHorizonVector m N, x⟫ := by
    calc
      _ = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
      _ = ⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N, x⟫ :=
        congrArg (fun y => ⟪y, x⟫) hax
      _ = _ := by rw [sum_inner]; simp only [real_inner_smul_left]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 Q) a
    (fun m => ⟪normalizedRamanujanHorizonVector m N, x⟫)
  rw [← hnorm] at hcs
  have hmul := mul_le_mul_of_nonneg_right
    (show (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 2 * ‖x‖ ^ 2 by linarith only [hcoef])
    (sum_nonneg (s := Icc 1 Q) fun m _ => sq_nonneg ⟪normalizedRamanujanHorizonVector m N, x⟫)
  have hprod : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 *
      (2 * ∑ m ∈ Icc 1 Q, ⟪normalizedRamanujanHorizonVector m N, x⟫ ^ 2) := by
    calc
      _ = (‖x‖ ^ 2) ^ 2 := (sq _).symm
      _ ≤ _ := hcs.trans hmul
      _ = _ := by ring
  have hh := (mul_le_mul_iff_right₀ hxpos).mp hprod
  linarith only [hh]

private theorem conductor_span_coercive_of_relative_budget {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (E : ℕ → ℝ) {e : ℝ} (he : 0 < e) (hfloor : ∀ m ∈ Icc 1 Q, e ≤ E m)
    (hbudget : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2) ≤ 1 / 16) :
    ∀ x ∈ conductorSubspace Q N, e / 2 * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
  classical
  let I := ↥(Icc 1 Q)
  let V := conductorSubspace Q N
  let v : I → V := fun m => ⟨conductorBasisFamily Q N m, Submodule.subset_span ⟨m, rfl⟩⟩
  have hframe (x : V) : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ∑ m : I, ⟪v m, x⟫ ^ 2 := by
    change (1 / 2 : ℝ) * ‖(x : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 ≤
      ∑ m : ↥(Icc 1 Q), ⟪normalizedRamanujanHorizonVector m.1 N,
        (x : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2
    rw [sum_coe_sort (Icc 1 Q) (fun m : ℕ =>
      ⟪normalizedRamanujanHorizonVector m N, (x : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2)]
    exact conductor_analysis_frame_lower hQ hQN hlog x x.property
  have hsmall : (∑ m : I,
      ‖Matrix.toEuclideanLin A (v m : EuclideanSpace ℝ (PrimeHorizonIndex N)) -
        E m.1 • (v m : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 / E m.1 ^ 2) ≤
        (1 / 2 : ℝ) / 8 := by
    change (∑ m : ↥(Icc 1 Q),
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m.1 N) -
        E m.1 • normalizedRamanujanHorizonVector m.1 N‖ ^ 2 / E m.1 ^ 2) ≤ (1 / 2 : ℝ) / 8
    rw [sum_coe_sort (Icc 1 Q) (fun m : ℕ =>
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2)]
    convert hbudget using 1; norm_num
  have hbound := inner_ge_half_floor_on_subspace_of_relative_frame_budget
    (Matrix.toEuclideanLin A) (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    V v (fun m : I => E m.1) (by norm_num : (0 : ℝ) < 1 / 2) he hframe
    (fun m => hfloor m.1 m.property) hsmall
  intro x hx
  exact hbound ⟨x, hx⟩

private theorem conductor_span_coercive_of_raw_budget {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (E : ℕ → ℝ) {e : ℝ} (he : 0 < e) (hfloor : ∀ m ∈ Icc 1 Q, e ≤ E m)
    (hraw : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ e ^ 2 / 128) :
    ∀ x ∈ conductorSubspace Q N, e / 2 * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
  apply conductor_span_coercive_of_relative_budget hQ hQN hlog hA E he hfloor
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / e ^ 2 := by
      refine sum_le_sum fun m hm => ?_
      exact div_le_div₀ (sq_nonneg _) le_rfl (sq_pos_of_pos he)
        (pow_le_pow_left₀ he.le (hfloor m hm) 2)
    _ = (∑ m ∈ Icc 1 Q,
        ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N‖ ^ 2) / e ^ 2 := (sum_div _ _ _).symm
    _ ≤ 1 / 16 := (div_le_iff₀ (sq_pos_of_pos he)).mpr
      (by nlinarith only [hraw, sq_nonneg e])

private theorem residual_packet_norm_le {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N) {e : ℝ} (he : 0 < e)
    (r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hr : (∑ m ∈ Icc 1 Q, ‖r m‖ ^ 2) ≤ e ^ 2 / 128) (a : ℕ → ℝ) :
    ‖∑ m ∈ Icc 1 Q, a m • r m‖ ≤
      e / 8 * ‖∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N‖ := by
  let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  have hframe := (half_and_three_halves_riesz_of_log_le hQ hQN hlog a).1
  have hcoeff : (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    linarith only [hframe]
  have htri : ‖∑ m ∈ Icc 1 Q, a m • r m‖ ≤ ∑ m ∈ Icc 1 Q, |a m| * ‖r m‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 Q) (fun m => |a m|) (fun m => ‖r m‖)
  simp only [sq_abs] at hcs
  have hsq : ‖∑ m ∈ Icc 1 Q, a m • r m‖ ^ 2 ≤ (e / 8 * ‖u‖) ^ 2 := by
    calc
      _ ≤ (∑ m ∈ Icc 1 Q, |a m| * ‖r m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ m ∈ Icc 1 Q, a m ^ 2) * ∑ m ∈ Icc 1 Q, ‖r m‖ ^ 2 := hcs
      _ ≤ (2 * ‖u‖ ^ 2) * (e ^ 2 / 128) :=
        mul_le_mul hcoeff hr (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hright : 0 ≤ e / 8 * ‖u‖ := by positivity
  nlinarith only [hsq, hright, norm_nonneg (∑ m ∈ Icc 1 Q, a m • r m)]


/-- Orthogonality removes the prescribed conductor energies from the mixed pairing;
the remaining raw residual sum controls coupling to the entire orthogonal complement. -/
theorem low_packet_cross_le {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) (E : ℕ → ℝ)
    {e : ℝ} (he : 0 < e)
    (hres : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ e ^ 2 / 128)
    {p z : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hp : p ∈ conductorSubspace Q N) (hz : z ∈ (conductorSubspace Q N)ᗮ) :
    |⟪Matrix.toEuclideanLin A p, z⟫| ≤ e / 8 * ‖p‖ * ‖z‖ := by
  obtain ⟨a, -, hpa⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := p)).mp hp
  let r := fun m => Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
    E m • normalizedRamanujanHorizonVector m N
  let d := ∑ m ∈ Icc 1 Q, (a m * E m) • normalizedRamanujanHorizonVector m N
  let v := ∑ m ∈ Icc 1 Q, a m • r m
  have hAp : Matrix.toEuclideanLin A p = d + v := by
    rw [hpa]
    dsimp only [d, v, r]
    rw [map_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_sub, mul_smul]
    abel
  have hv : ‖v‖ ≤ e / 8 * ‖p‖ := by
    rw [hpa]
    exact residual_packet_norm_le hQ hQN hlog he r hres a
  have hd : d ∈ conductorSubspace Q N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N _
  rw [hAp, inner_add_left, Submodule.inner_right_of_mem_orthogonal hd hz, zero_add]
  exact (abs_real_inner_le_norm v z).trans
    (mul_le_mul_of_nonneg_right hv (norm_nonneg z))

private theorem tendsto_log_power_div_nat_power (a : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ a / (N : ℝ) ^ s) atTop (𝓝 0) := by
  simpa only [Function.comp_def] using
    ((isLittleO_log_rpow_rpow_atTop a hs).tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

private theorem raw_residual_rate_envelope {K B α L n c : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (_hα : 0 ≤ α) (hαt : α ≤ Real.log L)
    (hBα : 2 * B * α ≤ 1 / 4) (hL1 : 1 ≤ L) (ht1 : 1 ≤ Real.log L)
    {Q : ℕ} (hQ1 : 1 ≤ Q) (hQ : (Q : ℝ) ≤ L ^ (1 / 8 : ℝ))
    (hc : 1 ≤ c) (hct : c ≤ α * Real.log L) :
    K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 *
        (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 4 : ℝ) / L + c ^ 10 * (L / n) ^ 2) *
          Real.exp (2 * B * c) ≤
      4 * K * (L ^ (-1 / 4 : ℝ) * (Real.log L) ^ 12 + L ^ (25 : ℕ) / n ^ 2) := by
  let t := Real.log L
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 ≤ t := zero_le_one.trans ht1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hcT : c ≤ t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hαt ht
    nlinarith only [hct, hh]
  have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
  have hlogcT : 1 + Real.log c ≤ t ^ 2 :=
    (by linarith only [Real.log_le_sub_one_of_pos hc0] : 1 + Real.log c ≤ c).trans hcT
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hlogQ : Real.log (Q : ℝ) ≤ t := by
    have hh := Real.log_le_log hQ0 hQ
    rw [Real.log_rpow hL] at hh
    change Real.log (Q : ℝ) ≤ t
    change Real.log (Q : ℝ) ≤ (1 / 8 : ℝ) * t at hh
    linarith only [hh, ht]
  have hQsq : (Q : ℝ) ^ 2 ≤ L ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (L ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 2
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
        norm_num
  have hlogSq : (1 + Real.log (Q : ℝ)) ^ 2 ≤ 4 * t ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log (Q : ℝ))
      (show 1 + Real.log (Q : ℝ) ≤ 2 * t by linarith only [hlogQ, ht1]) 2
    nlinarith only [hh]
  have hexp : Real.exp (2 * B * c) ≤ L ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ Real.exp (2 * B * (α * t)) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hct (mul_nonneg zero_le_two hB))
      _ = L ^ (2 * B * α) := by
        rw [Real.rpow_def_of_pos hL]
        dsimp only [t]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hBα
  have hnear : c ^ 2 * (1 + Real.log c) ^ 3 ≤ t ^ 10 := by
    calc
      _ ≤ (t ^ 2) ^ 2 * (t ^ 2) ^ 3 := mul_le_mul
        (pow_le_pow_left₀ hc0.le hcT 2) (pow_le_pow_left₀ hlogc hlogcT 3)
        (by positivity) (sq_nonneg (t ^ 2))
      _ = _ := by ring
  have htail : c ^ 10 ≤ t ^ 20 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ hc0.le hcT 10
  have hrate := add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnear (Real.rpow_nonneg hL.le (1 / 4 : ℝ))) hL.le)
    (mul_le_mul_of_nonneg_right htail (sq_nonneg (L / n)))
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hQsq hK) hlogSq (sq_nonneg _) (by positivity))
    hrate (by positivity) (by positivity)
  have hfull := mul_le_mul hprod hexp (Real.exp_pos _).le (by positivity)
  have htL : t ≤ L := by dsimp only [t]; linarith only [Real.log_le_sub_one_of_pos hL]
  have htailPower : t ^ 22 * L ^ (5 / 2 : ℝ) ≤ L ^ (25 : ℕ) := by
    calc
      _ ≤ L ^ (22 : ℕ) * L ^ (3 : ℕ) := mul_le_mul
        (pow_le_pow_left₀ ht htL 22)
        (by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
        (Real.rpow_nonneg hL.le _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ K * L ^ (1 / 4 : ℝ) * (4 * t ^ 2) *
        (t ^ 10 * L ^ (1 / 4 : ℝ) / L + t ^ 20 * (L / n) ^ 2) * L ^ (1 / 4 : ℝ) := hfull
    _ = 4 * K * (L ^ (-1 / 4 : ℝ) * t ^ 12 + t ^ 22 * L ^ (5 / 2 : ℝ) / n ^ 2) := by
      have hpow₁ : L ^ (-1 / 4 : ℝ) =
          L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) / L := by
        rw [show (-1 / 4 : ℝ) = ((1 / 4 + 1 / 4) + 1 / 4) - 1 by norm_num,
          Real.rpow_sub hL, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_one]
      have hpow₂ : L ^ (5 / 2 : ℝ) = L ^ (1 / 4 : ℝ) * L ^ 2 * L ^ (1 / 4 : ℝ) := by
        rw [show (5 / 2 : ℝ) = (1 / 4 + 2) + 1 / 4 by norm_num,
          Real.rpow_add hL, Real.rpow_add hL, Real.rpow_two]
      rw [hpow₁, hpow₂, div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right htailPower (sq_nonneg n)))
      (mul_nonneg (by norm_num) hK)

/-- On the logarithmic conductor block of exponent `1/8`, the total raw residual is smaller
than any exponential floor whose decay fits inside the log-log overlap interval. -/
theorem eventually_raw_residual_below_exponential_floor {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) {B α a : ℝ} (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hBα : 2 * B * α ≤ 1 / 4) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ α * Real.log (Real.log (N : ℝ)) →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
      (∑ m ∈ Icc 1 Q,
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
        (a * Real.exp (-B * c)) ^ 2 / 128 := by
  obtain ⟨K, hK, hres⟩ := exists_completeWeil_quadratic_conductor_residual_variable_rate hφ hsupp hM
  have hfirst : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (-1 / 4 : ℝ) *
      Real.log (Real.log (N : ℝ)) ^ 12) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (_root_.RHTower.Sieve.tendsto_logRpow_mul_logLogPow
        (by norm_num : (-1 / 4 : ℝ) < 0) 12).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have htail : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (25 : ℕ) / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hp (x : ℝ) : x ^ (25 : ℝ) = x ^ (25 : ℕ) := Real.rpow_natCast x 25
    simpa only [hp, Real.rpow_two] using
      tendsto_log_power_div_nat_power (25 : ℝ) (by norm_num : (0 : ℝ) < 2)
  have hlim : Tendsto (fun N : ℕ => 4 * K *
      (Real.log (N : ℝ) ^ (-1 / 4 : ℝ) * Real.log (Real.log (N : ℝ)) ^ 12 +
        Real.log (N : ℝ) ^ (25 : ℕ) / (N : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hfirst.add htail).const_mul (4 * K)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  filter_upwards [hres (1 / 8 : ℝ) (by norm_num) 4 (by norm_num),
    hlim.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < a ^ 2 / 128)),
    hLlim.eventually_ge_atTop 1, htlim.eventually_ge_atTop 1, htlim.eventually_ge_atTop α]
    with N hresN hsmall hL1 ht1 hαt
  intro c hc hct hwidth Q hQ1 hQ
  let r := c ^ 2 * (1 + Real.log c) ^ 3 * Real.log (N : ℝ) ^ (1 / 4 : ℝ) / Real.log N +
    c ^ 10 * (Real.log (N : ℝ) / N) ^ 2
  have hr : 0 ≤ r := by
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
    have hlogN := Real.log_natCast_nonneg N
    dsimp only [r]
    positivity
  have hsum : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
      K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 * r := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, K * (m : ℝ) * (1 + Real.log Q) ^ 2 * r := by
        refine sum_le_sum fun m hm => ?_
        have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
        have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
        have hlog := Real.log_le_log hm0 hmQ
        have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log (m : ℝ))
          (show 1 + Real.log (m : ℝ) ≤ 1 + Real.log Q by linarith only [hlog]) 2
        have hh := hresN m (mem_Icc.mp hm).1 (hmQ.trans hQ) c hc hwidth
        norm_num only [Nat.cast_ofNat] at hh
        change _ ≤ K * ((m : ℝ) * (1 + Real.log m) ^ 2) * r at hh
        exact (hh.trans_eq (by ring)).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp (mul_nonneg hK.le hm0.le)) hr)
      _ ≤ ∑ _m ∈ Icc 1 Q, K * (Q : ℝ) * (1 + Real.log Q) ^ 2 * r := by
        refine sum_le_sum fun m hm => ?_
        have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmQ hK.le) (sq_nonneg _)) hr
      _ = _ := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
  have hscaled := (mul_le_mul_of_nonneg_right hsum (Real.exp_pos (2 * B * c)).le).trans
    (raw_residual_rate_envelope hK.le hB hα hαt hBα hL1 ht1 hQ1 hQ hc hct)
  have heq : (a * Real.exp (-B * c)) ^ 2 / 128 * Real.exp (2 * B * c) = a ^ 2 / 128 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = a ^ 2 / 128 * (Real.exp (2 * (-B * c)) * Real.exp (2 * B * c)) := by ring
      _ = _ := by rw [← Real.exp_add, show 2 * (-B * c) + 2 * B * c = 0 by ring,
        Real.exp_zero, mul_one]
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (2 * B * c))).mp
  rw [heq]
  exact hscaled.trans hsmall

private def highBandRate (c r q L n : ℝ) : ℝ :=
  c * (1 + Real.log c) * (1 + Real.log r) / L +
    c * (1 + Real.log r) / L + c ^ 2 / L +
    c ^ 2 * (1 + Real.log r) * (1 + Real.log c) / L +
    c ^ 2 * r * Real.sqrt (L / n) + c ^ 5 * L / n + c ^ 3 / Real.sqrt q +
    c ^ 3 * r ^ 4 / n + c ^ 2 * (1 + Real.log c) / L

private theorem tendsto_loglog_power_div_log_power {e : ℝ} (he : 0 < e) (k : ℕ) :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ k / Real.log (N : ℝ) ^ e)
      atTop (𝓝 0) := by
  have hh := (_root_.RHTower.Sieve.tendsto_logRpow_mul_logLogPow (neg_neg_of_pos he) k).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have heq (N : ℕ) : Real.log (N : ℝ) ^ (-e) * Real.log (Real.log (N : ℝ)) ^ k =
      Real.log (Real.log (N : ℝ)) ^ k / Real.log (N : ℝ) ^ e := by
    rw [Real.rpow_neg (Real.log_natCast_nonneg N)]
    ring
  simpa only [Function.comp_def, heq] using hh

private theorem tendsto_high_band_envelope (D : ℝ) :
    Tendsto (fun N : ℕ =>
      5 * (1 + D) * (Real.log (Real.log (N : ℝ)) ^ 7 / Real.log N) +
      2 * (Real.log (Real.log (N : ℝ)) ^ 6 / Real.log (N : ℝ) ^ (1 / 16 : ℝ)) +
      3 * (Real.log (N : ℝ) ^ (4 * D + 6) / Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 7 / Real.log N)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_loglog_power_div_log_power zero_lt_one 7
  have h₂ := tendsto_loglog_power_div_log_power (by norm_num : (0 : ℝ) < 1 / 16) 6
  have h₃ : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (4 * D + 6) / Real.sqrt (N : ℝ))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      tendsto_log_power_div_nat_power (4 * D + 6) (by norm_num : (0 : ℝ) < 1 / 2)
  simpa only [mul_zero, add_zero] using
    ((h₁.const_mul (5 * (1 + D))).add (h₂.const_mul 2)).add (h₃.const_mul 3)

private theorem high_band_rate_envelope {D L n c r q : ℝ}
    (hD : 0 ≤ D) (hL1 : 1 ≤ L) (ht1 : 1 ≤ Real.log L) (hn1 : 1 ≤ n)
    (hc1 : 1 ≤ c) (hcT : c ≤ (Real.log L) ^ 2) (hcL : c ≤ L)
    (hr1 : 1 ≤ r) (hr : r ≤ L ^ D)
    (hq : L ^ (1 / 8 : ℝ) / 2 ≤ q) :
    highBandRate c r q L n ≤
      5 * (1 + D) * ((Real.log L) ^ 7 / L) +
      2 * ((Real.log L) ^ 6 / L ^ (1 / 16 : ℝ)) +
      3 * (L ^ (4 * D + 6) / Real.sqrt n) := by
  let t := Real.log L
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 ≤ t := zero_le_one.trans ht1
  have hn : 0 < n := zero_lt_one.trans_le hn1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have hq0 : 0 < q := (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two).trans_le hq
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hlogc0 : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc1]
  have hlogr0 : 0 ≤ 1 + Real.log r := by linarith only [Real.log_nonneg hr1]
  have hlogcT : 1 + Real.log c ≤ t ^ 2 :=
    (by linarith only [Real.log_le_sub_one_of_pos hc] : 1 + Real.log c ≤ c).trans hcT
  have hlogr : Real.log r ≤ D * t := by
    have hh := Real.log_le_log hr0 hr
    rwa [Real.log_rpow hL] at hh
  have hlogrT : 1 + Real.log r ≤ (1 + D) * t := by linarith only [hlogr, ht1]
  have htpow (k : ℕ) (hk : k ≤ 7) : t ^ k ≤ t ^ 7 := pow_le_pow_right₀ ht1 hk
  let U := (1 + D) * (t ^ 7 / L)
  let V := L ^ (4 * D + 6) / Real.sqrt n
  have h1 : c * (1 + Real.log c) * (1 + Real.log r) / L ≤ U := by
    calc
      _ ≤ t ^ 2 * t ^ 2 * ((1 + D) * t) / L := by gcongr
      _ = (1 + D) * (t ^ 5 / L) := by ring
      _ ≤ U := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (htpow 5 (by norm_num)) hL.le) (by positivity)
  have h2 : c * (1 + Real.log r) / L ≤ U := by
    calc
      _ ≤ t ^ 2 * ((1 + D) * t) / L := by gcongr
      _ = (1 + D) * (t ^ 3 / L) := by ring
      _ ≤ U := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (htpow 3 (by norm_num)) hL.le) (by positivity)
  have h3 : c ^ 2 / L ≤ U := by
    calc
      _ ≤ t ^ 7 / L := div_le_div_of_nonneg_right
        ((pow_le_pow_left₀ hc.le hcT 2).trans
          (by simpa only [← pow_mul] using htpow 4 (by norm_num))) hL.le
      _ ≤ U := le_mul_of_one_le_left (by positivity) (by linarith only [hD])
  have h4 : c ^ 2 * (1 + Real.log r) * (1 + Real.log c) / L ≤ U := by
    calc
      _ ≤ (t ^ 2) ^ 2 * ((1 + D) * t) * t ^ 2 / L := by gcongr
      _ = U := by dsimp only [U]; ring
  have h9 : c ^ 2 * (1 + Real.log c) / L ≤ U := by
    calc
      _ ≤ (t ^ 2) ^ 2 * t ^ 2 / L := by gcongr
      _ = t ^ 6 / L := by ring
      _ ≤ t ^ 7 / L := div_le_div_of_nonneg_right (htpow 6 (by norm_num)) hL.le
      _ ≤ U := le_mul_of_one_le_left (by positivity) (by linarith only [hD])
  have hsqrtRatio : Real.sqrt (L / n) ≤ L / Real.sqrt n := by
    apply (le_div_iff₀ hsqrtn).mpr
    have hsq : (Real.sqrt (L / n) * Real.sqrt n) ^ 2 = L := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hL.le hn.le), Real.sq_sqrt hn.le,
        div_mul_cancel₀ _ hn.ne']
    have hll : L ≤ L ^ 2 := by nlinarith only [hL1]
    nlinarith only [hsq, hll, hL.le, mul_nonneg (Real.sqrt_nonneg (L / n)) (Real.sqrt_nonneg n)]
  have hsqrtn_le : Real.sqrt n ≤ n := by
    nlinarith only [Real.sq_sqrt hn.le, Real.sqrt_nonneg n, hn1]
  have h5 : c ^ 2 * r * Real.sqrt (L / n) ≤ V := by
    calc
      _ ≤ L ^ 2 * L ^ D * (L / Real.sqrt n) := by gcongr
      _ = L ^ (D + 3) / Real.sqrt n := by
        rw [Real.rpow_add hL]
        have hp : L ^ (3 : ℝ) = L ^ (3 : ℕ) := Real.rpow_natCast L 3
        rw [hp]
        ring
      _ ≤ V := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hD])) hsqrtn.le
  have h6 : c ^ 5 * L / n ≤ V := by
    calc
      _ ≤ L ^ 5 * L / Real.sqrt n := by gcongr
      _ = L ^ (6 : ℝ) / Real.sqrt n := by
        have hp : L ^ (6 : ℝ) = L ^ (6 : ℕ) := Real.rpow_natCast L 6
        rw [hp]
        ring
      _ ≤ V := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hD])) hsqrtn.le
  have h8 : c ^ 3 * r ^ 4 / n ≤ V := by
    calc
      _ ≤ L ^ 3 * (L ^ D) ^ 4 / Real.sqrt n := by gcongr
      _ = L ^ (4 * D + 3) / Real.sqrt n := by
        rw [Real.rpow_add hL]
        have hp : L ^ (3 : ℝ) = L ^ (3 : ℕ) := Real.rpow_natCast L 3
        have hp4 : (L ^ D) ^ 4 = L ^ (4 * D) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
          norm_num only [Nat.cast_ofNat]
          rw [mul_comm D]
        rw [hp, hp4]
        ring
      _ ≤ V := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) hsqrtn.le
  have hqroot : L ^ (1 / 16 : ℝ) / 2 ≤ Real.sqrt q := by
    have hsq : (L ^ (1 / 16 : ℝ) / 2) ^ 2 ≤ q := by
      rw [div_pow, ← Real.rpow_two, ← Real.rpow_mul hL.le]
      norm_num
      nlinarith only [hq, Real.rpow_nonneg hL.le (1 / 8 : ℝ)]
    nlinarith only [hsq, Real.sq_sqrt hq0.le, Real.sqrt_nonneg q,
      Real.rpow_nonneg hL.le (1 / 16 : ℝ)]
  have h7 : c ^ 3 / Real.sqrt q ≤ 2 * (t ^ 6 / L ^ (1 / 16 : ℝ)) := by
    calc
      _ ≤ (t ^ 2) ^ 3 / (L ^ (1 / 16 : ℝ) / 2) :=
        div_le_div₀ (pow_nonneg (sq_nonneg t) 3) (pow_le_pow_left₀ hc.le hcT 3)
          (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two) hqroot
      _ = _ := by ring
  dsimp only [highBandRate]
  calc
    _ ≤ 5 * U + 2 * (t ^ 6 / L ^ (1 / 16 : ℝ)) + 3 * V := by
      linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    _ = _ := by dsimp only [U, V, t]; ring

private theorem eventually_const_log_power_le_nat (C a : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * Real.log (N : ℝ) ^ a ≤ (N : ℝ) := by
  have hlim : Tendsto (fun N : ℕ => C * (Real.log (N : ℝ) ^ a / (N : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero] using
      (tendsto_log_power_div_nat_power a zero_lt_one).const_mul C
  filter_upwards [hlim.eventually (ge_mem_nhds zero_lt_one), eventually_ge_atTop 1]
    with N hsmall hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_one hN0).mp
  convert hsmall using 1; ring

private theorem eventually_high_band_loglog_horizon {D α C H : ℝ}
    (hD : 1 / 8 ≤ D) (_hα : 0 ≤ α) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      let Q := ⌊Real.log (N : ℝ) ^ (1 / 8 : ℝ)⌋₊
      let R := ⌊Real.log (N : ℝ) ^ D⌋₊
      2 ≤ Q ∧ Q ≤ R ∧ R ^ 6 ≤ N ∧ 36 * (1 + Real.log R) ≤ Real.log N ∧
      ∀ c : ℝ, 1 ≤ c → c ≤ α * Real.log (Real.log (N : ℝ)) →
        c ≤ Real.log N ∧ c / N ≤ 1 / 3 ∧
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
        C * highBandRate c R Q (Real.log N) N ≤ 1 ∧
        H + 1 + Real.log c ≤ (1 / 4 : ℝ) * Real.log Q := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  have hwidthLim : Tendsto (fun N : ℕ =>
      α * (Real.log (Real.log (N : ℝ)) / Real.log N)) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero] using
      (tendsto_loglog_power_div_log_power zero_lt_one 1).const_mul α
  have hgapLim : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
      Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop 1 zero_lt_one).tendsto_div_nhds_zero).comp htlim
  have hQlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim
  have hgram : Tendsto (fun N : ℕ =>
      36 * (1 + D * Real.log (Real.log (N : ℝ))) / Real.log N) atTop (𝓝 0) := by
    have hratio : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log N)
        atTop (𝓝 0) := by
      simpa only [pow_one, Real.rpow_one] using tendsto_loglog_power_div_log_power zero_lt_one 1
    have hinv := tendsto_inv_atTop_zero.comp hLlim
    have hh : Tendsto (fun N : ℕ => 36 * ((Real.log (N : ℝ))⁻¹ +
        D * (Real.log (Real.log (N : ℝ)) / Real.log N))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero, add_zero] using
        (hinv.add (hratio.const_mul D)).const_mul (36 : ℝ)
    apply hh.congr
    intro N
    ring
  let Cnear := 2 * Real.exp 2 + 1
  have hCnear : 0 < Cnear := by dsimp only [Cnear]; positivity
  have hsmall := (tendsto_high_band_envelope D).eventually
    (ge_mem_nhds (one_div_pos.mpr hC))
  filter_upwards [hLlim.eventually_ge_atTop 1, htlim.eventually_ge_atTop 1,
    hQlim.eventually_ge_atTop 2, hgram.eventually (ge_mem_nhds zero_lt_one),
    eventually_const_log_power_le_nat 1 (6 * D), eventually_const_log_power_le_nat 3 1,
    eventually_const_log_power_le_nat (4 * Cnear ^ 2) 2,
    eventually_const_log_power_le_nat (2 * Cnear) (2 * D + 1),
    eventually_const_log_power_le_nat (4 * (Real.exp 1 + 3) ^ 2) 2,
    hsmall, htlim.eventually_ge_atTop (64 * (H + 1 + Real.log 2 / 4)),
    htlim.eventually_ge_atTop α,
    hwidthLim.eventually (ge_mem_nhds zero_lt_one),
    hgapLim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 128)),
    eventually_ge_atTop 2]
    with N hL1 ht1 hQpow2 hgramN hR6N hwidthN hradN hsizeN hreswidthN hsmallN hgapN
      hαt hwidthSmall hgapSmall hN2
  let L := Real.log (N : ℝ)
  let t := Real.log L
  let Q := ⌊L ^ (1 / 8 : ℝ)⌋₊
  let R := ⌊L ^ D⌋₊
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 ≤ t := zero_le_one.trans ht1
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ2 : 2 ≤ Q := Nat.le_floor hQpow2
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ L ^ (1 / 8 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hRpow : (R : ℝ) ≤ L ^ D := Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hQR : Q ≤ R := Nat.le_floor
    (hQpow.trans (Real.rpow_le_rpow_of_exponent_le hL1 hD))
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hR6 : R ^ 6 ≤ N := by
    have hh : (R : ℝ) ^ 6 ≤ (N : ℝ) := by
      calc
        _ ≤ (L ^ D) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRpow 6
        _ = L ^ (6 * D) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
          norm_num only [Nat.cast_ofNat]
          rw [mul_comm D]
        _ ≤ _ := by simpa only [one_mul] using hR6N
    exact_mod_cast hh
  have hlogR : Real.log (R : ℝ) ≤ D * t := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hR1) hRpow
    rwa [Real.log_rpow hL] at hh
  have hgramR : 36 * (1 + Real.log R) ≤ L := by
    have hh := (div_le_one hL).mp hgramN
    linarith only [hh, hlogR]
  have hQlower : L ^ (1 / 8 : ℝ) / 2 ≤ (Q : ℝ) := by
    have hh := Nat.lt_floor_add_one (L ^ (1 / 8 : ℝ))
    change L ^ (1 / 8 : ℝ) < (Q : ℝ) + 1 at hh
    have hQcast : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    linarith only [hh, hQcast]
  have hlogQ : (1 / 8 : ℝ) * t - Real.log 2 ≤ Real.log (Q : ℝ) := by
    have hh := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two) hQlower
    rwa [Real.log_div (Real.rpow_pos_of_pos hL _).ne' (by norm_num), Real.log_rpow hL] at hh
  refine ⟨hQ2, hQR, hR6, hgramR, ?_⟩
  intro c hc1 hct
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hcT : c ≤ t ^ 2 := by
    change α ≤ t at hαt
    change c ≤ α * t at hct
    have hh := mul_le_mul_of_nonneg_right hαt ht
    nlinarith only [hct, hh]
  have hcL : c ≤ L := by
    have hh : α * t / L ≤ 1 := by
      simpa only [div_eq_mul_inv, mul_assoc] using hwidthSmall
    exact hct.trans ((div_le_one hL).mp hh)
  have hcN : c / N ≤ 1 / 3 := by
    apply (div_le_iff₀ hN).mpr
    have hh : 3 * L ≤ (N : ℝ) := by simpa only [Real.rpow_one] using hwidthN
    linarith only [hcL, hh]
  have hrad : linearNearRowRadius c + 1 ≤ Cnear * L := by
    dsimp only [linearNearRowRadius, Cnear]
    have hh := mul_le_mul_of_nonneg_right hcL (Real.exp_pos 2).le
    nlinarith only [hh, hL1]
  have hrad0 : 0 ≤ linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
  have hradBound : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrad0 hrad 2) (by norm_num : (0 : ℝ) ≤ 4)
    have hNrad : 4 * Cnear ^ 2 * L ^ 2 ≤ (N : ℝ) := by
      simpa only [Real.rpow_two] using hradN
    nlinarith only [hh, hNrad]
  have hRtwo : (R : ℝ) ^ 2 ≤ L ^ (2 * D) := by
    calc
      _ ≤ (L ^ D) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRpow 2
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hL.le, mul_comm D]
  have hRsum : ((R * R : ℕ) + 1 : ℝ) ≤ 2 * L ^ (2 * D) := by
    have hp : 1 ≤ L ^ (2 * D) := Real.one_le_rpow hL1 (by positivity)
    push_cast
    nlinarith only [hRtwo, hp]
  have hsize : ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
    calc
      _ ≤ (2 * L ^ (2 * D)) * (Cnear * L) := mul_le_mul hRsum hrad hrad0 (by positivity)
      _ = (2 * Cnear) * L ^ (2 * D + 1) := by rw [Real.rpow_add hL, Real.rpow_one]; ring
      _ ≤ _ := hsizeN
  have hresWidth : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hcL 2) (by positivity)).trans
      (by simpa only [Real.rpow_two] using hreswidthN)
  have hsmallRate : C * highBandRate c R Q L N ≤ 1 := by
    have hh := (high_band_rate_envelope hD0 hL1 ht1
      (by exact_mod_cast (show 1 ≤ N by omega)) hc1 hcT hcL hR1 hRpow hQlower).trans hsmallN
    have hm := mul_le_mul_of_nonneg_left hh hC.le
    simpa only [mul_one_div_cancel hC.ne'] using hm
  have hgap : H + 1 + Real.log c ≤ (1 / 4 : ℝ) * Real.log Q := by
    have hlogc : Real.log c ≤ 2 * Real.log t := by
      have hh := Real.log_le_log hc hcT
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hlogt : Real.log t ≤ t / 128 := by
      have hh := (div_le_iff₀ (zero_lt_one.trans_le ht1)).mp hgapSmall
      change Real.log t ≤ (1 / 128 : ℝ) * t at hh
      linarith only [hh]
    change 64 * (H + 1 + Real.log 2 / 4) ≤ t at hgapN
    linarith only [hlogc, hlogt, hlogQ, hgapN]
  exact ⟨hcL, hcN, hradBound, hsize, hresWidth, hsmallRate, hgap⟩

private theorem profile_energy_smul (φ : ℝ → ℝ) (c : ℝ) {N : ℕ} (s : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (s • u) = s ^ 2 * completeWeilEnergy φ c N u := by
  simp only [completeWeilEnergy, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem profile_energy_add (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (x + y) = completeWeilEnergy φ c N x +
      2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ +
        completeWeilEnergy φ c N y := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian φ c N)) y x
  simp only [completeWeilEnergy, map_add, inner_add_left, inner_add_right]
  rw [hsym, real_inner_comm y (Matrix.toEuclideanLin (completeWeilMatrix φ c N) x)]
  ring

/-- Every compact nonzero `C²` profile retains an exponential coercivity margin throughout
a universal log-log overlap interval on every fixed polylogarithmic conductor span.
Both universal constants and the profile prefactor are independent of the span exponent. -/
theorem exists_universal_loglog_overlap_all_polylog_coercivity :
    ∃ B α : ℝ, 0 < B ∧ 0 < α ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ a : ℝ, 0 < a ∧ ∀ A : ℝ, 0 < A →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ α * Real.log (Real.log (N : ℝ)) →
      ∀ x ∈ conductorSubspace ⌊Real.log (N : ℝ) ^ A⌋₊ N,
        a * Real.exp (-B * c) * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  obtain ⟨B, hB, hlowAll⟩ := exists_universal_loglog_overlap_coercivity
  let α := 1 / (128 * (B + 1))
  have hden : 0 < 128 * (B + 1) := by positivity
  have hα : 0 < α := div_pos zero_lt_one hden
  have hBα : 2 * B * α ≤ 1 / 4 := by
    dsimp only [α]
    rw [← mul_div_assoc, mul_one, div_le_iff₀ hden]
    linarith only [hB]
  have hBα1 : 2 * B * α < 1 := by linarith only [hBα]
  refine ⟨B, α, hB, hα, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨a₀, ha₀, hlow⟩ := hlowAll φ hφ hsupp hM
  let a := min a₀ 1
  have ha : 0 < a := lt_min ha₀ zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have haa₀ : a ≤ a₀ := min_le_left _ _
  obtain ⟨H, C, hH, hC, hhigh⟩ := exists_profile_completeWeilEnergy_ge_adjunction_and_log hφ hsupp hM
  refine ⟨a / 2, div_pos ha zero_lt_two, ?_⟩
  intro A hA
  let D := max A (1 / 8 : ℝ)
  have hD : 1 / 8 ≤ D := le_max_right _ _
  filter_upwards [hlow (1 / 8 : ℝ) (by norm_num) (by norm_num) α hα hBα1,
    eventually_raw_residual_below_exponential_floor hφ hsupp hM hB.le hα.le hBα ha,
    eventually_high_band_loglog_horizon (H := H) hD hα.le hC]
    with N hlowN hrawN hhorN
  let Q := ⌊Real.log (N : ℝ) ^ (1 / 8 : ℝ)⌋₊
  let R := ⌊Real.log (N : ℝ) ^ D⌋₊
  obtain ⟨hQ2, hQR, hR6, hlogR, hhor⟩ := hhorN
  have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hlogR, Real.log_natCast_nonneg R]
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hQQ : Q * Q ≤ N := (Nat.mul_le_mul hQR hQR).trans hRR
  have hlogQ : 18 * (1 + Real.log Q) ≤ Real.log N := by
    have hQRreal : (Q : ℝ) ≤ R := by exact_mod_cast hQR
    have hh := Real.log_le_log hQ0 hQRreal
    linarith only [hh, hlogR, Real.log_natCast_nonneg R]
  intro c hc hct x hx
  obtain ⟨hcL, hw, hrad, hsize, hresWidth, hsmall, hgap⟩ := hhor c hc hct
  let e := a * Real.exp (-B * c)
  have he : 0 < e := mul_pos ha (Real.exp_pos _)
  have he1 : e ≤ 1 := by
    have hexp : Real.exp (-B * c) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have hc0 := zero_le_one.trans hc; nlinarith only [mul_nonneg hB.le hc0])
    exact (mul_le_mul ha1 hexp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
  have hres := hrawN c hc hct hresWidth Q (by omega) hQpow
  have hlowEnergy : ∀ p ∈ conductorSubspace Q N,
      e * ‖p‖ ^ 2 ≤ completeWeilEnergy φ c N p := by
    intro p hp
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right haa₀ (Real.exp_pos _).le) (sq_nonneg ‖p‖)).trans
        (hlowN c hc hct p hp)
  have hhighEnergy : ∀ z ∈ conductorSubspace R N, z ∈ (conductorSubspace Q N)ᗮ →
      ‖z‖ ^ 2 ≤ completeWeilEnergy φ c N z := by
    intro z hzR hzQ
    by_cases hz0 : z = 0
    · simp only [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), completeWeilEnergy,
        map_zero, inner_zero_left, le_refl]
    have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let y := ‖z‖⁻¹ • z
    have hyR : y ∈ conductorSubspace R N := Submodule.smul_mem _ _ hzR
    have hyQ : y ∈ (conductorSubspace Q N)ᗮ := Submodule.smul_mem _ _ hzQ
    have hyNorm : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzNorm), inv_mul_cancel₀ hzNorm.ne']
    obtain ⟨b, -, hby⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := y)).mp hyR
    rw [hby] at hyQ hyNorm
    have hh := hhigh hQ2 hQR hR6 hlogR hc hcL hw hrad hsize hsmall b hyQ
      (by rw [hyNorm]; norm_num) hyNorm.le
    rw [← hby] at hh
    have hWy : 1 ≤ completeWeilEnergy φ c N y := by
      linarith only [hh, hgap, primeAdjunctionMass_nonneg R b]
    change 1 ≤ completeWeilEnergy φ c N (‖z‖⁻¹ • z) at hWy
    rw [profile_energy_smul] at hWy
    have hprod := mul_le_mul_of_nonneg_left hWy (sq_nonneg ‖z‖)
    have hscale : ‖z‖ ^ 2 * (‖z‖⁻¹ ^ 2 * completeWeilEnergy φ c N z) =
        completeWeilEnergy φ c N z := by field_simp
    rwa [mul_one, hscale] at hprod
  have hcut : ⌊Real.log (N : ℝ) ^ A⌋₊ ≤ R := Nat.le_floor
    ((Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) A)).trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)))
  have hxR := conductorSubspace_mono hcut N hx
  let p := (conductorSubspace Q N).starProjection x
  let z := x - p
  have hp : p ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hzQ : z ∈ (conductorSubspace Q N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace Q N).starProjection_inner_eq_zero x v hv
  have hzR : z ∈ conductorSubspace R N :=
    (conductorSubspace R N).sub_mem hxR (conductorSubspace_mono hQR N hp)
  have hpyth : ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖x‖ ^ 2 :=
    norm_starProjection_sq_add_sub_sq (conductorSubspace Q N) x
  have hpEnergy := hlowEnergy p hp
  have hzEnergy := hhighEnergy z hzR hzQ
  have hcross := low_packet_cross_le hQ2 hQQ hlogQ (completeWeilMatrix φ c N)
    (completedConductorEnergy φ c) he hres hp hzQ
  have hcrossCost : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫| ≤
      e / 8 * (‖p‖ ^ 2 + ‖z‖ ^ 2) := by
    have hh := mul_nonneg (show 0 ≤ e / 8 by positivity) (sq_nonneg (‖p‖ - ‖z‖))
    nlinarith only [hcross, hh]
  have hxSplit : x = p + z := by dsimp only [z]; abel
  have henergy := profile_energy_add φ c p z
  rw [← hxSplit] at henergy
  have hcrossLower := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫
  have hzReserve := mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖z‖)
  have hnonneg := mul_nonneg he.le (add_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖z‖))
  have hhalf : a / 2 * Real.exp (-B * c) = e / 2 := by dsimp only [e]; ring
  rw [hhalf, ← hpyth]
  nlinarith only [hpEnergy, hzEnergy, hcrossCost, henergy, hcrossLower, hzReserve, hnonneg]

/-- Every fixed log-log overlap multiple is allowed for every nonzero compact `C²`
profile. The exponential margin may depend on that multiple, but not on the span exponent. -/
theorem exists_loglog_overlap_all_polylog_coercivity {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) {α : ℝ} (hα : 0 < α) :
    ∃ B a : ℝ, 0 < B ∧ 0 < a ∧ ∀ A : ℝ, 0 < A →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ α * Real.log (Real.log (N : ℝ)) →
      ∀ x ∈ conductorSubspace ⌊Real.log (N : ℝ) ^ A⌋₊ N,
        a * Real.exp (-B * c) * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  let B := 1 / (16 * α)
  have hB : 0 < B := div_pos zero_lt_one (mul_pos (by norm_num) hα)
  have hBα : 2 * B * α ≤ 1 / 4 := by
    dsimp only [B]
    have heq : 2 * (1 / (16 * α)) * α = (1 / 8 : ℝ) := by field_simp; norm_num
    rw [heq]
    norm_num
  obtain ⟨a₀, ha₀, hfloorAll⟩ := exists_subexponential_completedConductor_floor hφ hsupp hM hB
  let a := min a₀ 1
  have ha : 0 < a := lt_min ha₀ zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have haa₀ : a ≤ a₀ := min_le_left _ _
  obtain ⟨H, C, hH, hC, hhigh⟩ := exists_profile_completeWeilEnergy_ge_adjunction_and_log hφ hsupp hM
  refine ⟨B, a / 4, hB, div_pos ha (by norm_num), ?_⟩
  intro A hA
  let D := max A (1 / 8 : ℝ)
  have hD : 1 / 8 ≤ D := le_max_right _ _
  filter_upwards [eventually_raw_residual_below_exponential_floor hφ hsupp hM hB.le hα.le hBα ha,
    eventually_high_band_loglog_horizon (H := H) hD hα.le hC]
    with N hrawN hhorN
  let Q := ⌊Real.log (N : ℝ) ^ (1 / 8 : ℝ)⌋₊
  let R := ⌊Real.log (N : ℝ) ^ D⌋₊
  obtain ⟨hQ2, hQR, hR6, hlogR, hhor⟩ := hhorN
  have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hlogR, Real.log_natCast_nonneg R]
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hQQ : Q * Q ≤ N := (Nat.mul_le_mul hQR hQR).trans hRR
  have hlogQ : 18 * (1 + Real.log Q) ≤ Real.log N := by
    have hQRreal : (Q : ℝ) ≤ R := by exact_mod_cast hQR
    have hh := Real.log_le_log hQ0 hQRreal
    linarith only [hh, hlogR, Real.log_natCast_nonneg R]
  intro c hc hct x hx
  obtain ⟨hcL, hw, hrad, hsize, hresWidth, hsmall, hgap⟩ := hhor c hc hct
  let e := a * Real.exp (-B * c)
  have he : 0 < e := mul_pos ha (Real.exp_pos _)
  have he1 : e ≤ 1 := by
    have hexp : Real.exp (-B * c) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have hc0 := zero_le_one.trans hc; nlinarith only [mul_nonneg hB.le hc0])
    exact (mul_le_mul ha1 hexp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
  have hres := hrawN c hc hct hresWidth Q (by omega) hQpow
  have hfloor : ∀ m ∈ Icc 1 Q, e ≤ completedConductorEnergy φ c m := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hcm : c / (m : ℝ) ≤ c := div_le_self (zero_le_one.trans hc) hm1
    calc
      e ≤ a₀ * Real.exp (-B * c) :=
        mul_le_mul_of_nonneg_right haa₀ (Real.exp_pos _).le
      _ ≤ a₀ * Real.exp (-B * (c / m)) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hcm (neg_nonpos.mpr hB.le))) ha₀.le
      _ ≤ _ := hfloorAll c (zero_lt_one.trans_le hc) m (mem_Icc.mp hm).1
  have hlowEnergy : ∀ p ∈ conductorSubspace Q N,
      e / 2 * ‖p‖ ^ 2 ≤ completeWeilEnergy φ c N p :=
    conductor_span_coercive_of_raw_budget hQ2 hQQ hlogQ (completeWeilMatrix_isHermitian φ c N)
      (completedConductorEnergy φ c) he hfloor hres
  have hhighEnergy : ∀ z ∈ conductorSubspace R N, z ∈ (conductorSubspace Q N)ᗮ →
      ‖z‖ ^ 2 ≤ completeWeilEnergy φ c N z := by
    intro z hzR hzQ
    by_cases hz0 : z = 0
    · simp only [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), completeWeilEnergy,
        map_zero, inner_zero_left, le_refl]
    have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let y := ‖z‖⁻¹ • z
    have hyR : y ∈ conductorSubspace R N := Submodule.smul_mem _ _ hzR
    have hyQ : y ∈ (conductorSubspace Q N)ᗮ := Submodule.smul_mem _ _ hzQ
    have hyNorm : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzNorm), inv_mul_cancel₀ hzNorm.ne']
    obtain ⟨b, -, hby⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := y)).mp hyR
    rw [hby] at hyQ hyNorm
    have hh := hhigh hQ2 hQR hR6 hlogR hc hcL hw hrad hsize hsmall b hyQ
      (by rw [hyNorm]; norm_num) hyNorm.le
    rw [← hby] at hh
    have hWy : 1 ≤ completeWeilEnergy φ c N y := by
      linarith only [hh, hgap, primeAdjunctionMass_nonneg R b]
    change 1 ≤ completeWeilEnergy φ c N (‖z‖⁻¹ • z) at hWy
    rw [profile_energy_smul] at hWy
    have hprod := mul_le_mul_of_nonneg_left hWy (sq_nonneg ‖z‖)
    have hscale : ‖z‖ ^ 2 * (‖z‖⁻¹ ^ 2 * completeWeilEnergy φ c N z) =
        completeWeilEnergy φ c N z := by field_simp
    rwa [mul_one, hscale] at hprod
  have hcut : ⌊Real.log (N : ℝ) ^ A⌋₊ ≤ R := Nat.le_floor
    ((Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) A)).trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)))
  have hxR := conductorSubspace_mono hcut N hx
  let p := (conductorSubspace Q N).starProjection x
  let z := x - p
  have hp : p ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hzQ : z ∈ (conductorSubspace Q N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace Q N).starProjection_inner_eq_zero x v hv
  have hzR : z ∈ conductorSubspace R N :=
    (conductorSubspace R N).sub_mem hxR (conductorSubspace_mono hQR N hp)
  have hpyth : ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖x‖ ^ 2 :=
    norm_starProjection_sq_add_sub_sq (conductorSubspace Q N) x
  have hpEnergy := hlowEnergy p hp
  have hzEnergy := hhighEnergy z hzR hzQ
  have hcross := low_packet_cross_le hQ2 hQQ hlogQ (completeWeilMatrix φ c N)
    (completedConductorEnergy φ c) he hres hp hzQ
  have hcrossCost : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫| ≤
      e / 8 * (‖p‖ ^ 2 + ‖z‖ ^ 2) := by
    have hh := mul_nonneg (show 0 ≤ e / 8 by positivity) (sq_nonneg (‖p‖ - ‖z‖))
    nlinarith only [hcross, hh]
  have hxSplit : x = p + z := by dsimp only [z]; abel
  have henergy := profile_energy_add φ c p z
  rw [← hxSplit] at henergy
  have hcrossLower := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫
  have hzReserve := mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖z‖)
  have hnonneg := mul_nonneg he.le (add_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖z‖))
  have hquarter : a / 4 * Real.exp (-B * c) = e / 4 := by dsimp only [e]; ring
  rw [hquarter, ← hpyth]
  nlinarith only [hpEnergy, hzEnergy, hcrossCost, henergy, hcrossLower, hzReserve, hnonneg]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
