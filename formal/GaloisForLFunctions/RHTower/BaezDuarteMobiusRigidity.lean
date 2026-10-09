import GaloisForLFunctions.RHTower.BaezDuarteDistance
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Báez-Duarte approximants are pointwise Möbius

In the tail coordinate `u = 1/t` the Báez-Duarte residual of a finite row,
`R(u) = 1/u − Σ_{k ≤ N} c_k ({u/k} − {u}/k)/u`, is a step function divided by `u`:
on every cell `[m, m+1)`,

  `u R(u) = S_m = 1 − Σ_{k ≤ N} c_k {m/k}`   (`bdRowResidualFun_eq_step`).

So `‖R‖ ≥ |S_m|/(m+1)` for every `m ≥ 1` (`norm_bdStepValue_le`), and exactly
`‖R‖² = Σ_{m ≥ 1} |S_m|²/(m(m+1))` (`hasSum_bdStepValue_sq`): the Báez-Duarte distance is the
minimum over rows of a weighted least-squares problem on the integers. The steps telescope to the Dirichlet
convolution `1 ⋆ ĉ`, with `ĉ_k = c_k` for `k ≤ N` and `0` beyond:
`S_{d} − S_{d−1} = −Σ c_k/k + Σ_{k ∣ d} ĉ_k`. Möbius inversion then gives, for every `n ≥ 2`
(`norm_bdRow_add_moebius_le`),

  `|ĉ_n + μ(n)| ≤ (Σ_{d ∣ n} (2d + 1)) · ‖R‖`.

No bound on the coefficients is assumed. Consequently every sequence of Báez-Duarte approximants
whose distance tends to `0` converges pointwise to `−μ` on `n ≥ 2`
(`tendsto_bdRow_neg_moebius`). The coefficient of `k = 1` multiplies the zero generator and is free.
Every node set carrying such approximants contains all squarefree `n ≥ 2`
(`mem_of_moebius_ne_zero_of_tendsto_bdRow`), and rows supported on the primes keep a residual at least
`1/28` (`bdRow_floor_primes`).
-/

open MeasureTheory Set Filter
open scoped Topology ArithmeticFunction.Moebius

noncomputable section
namespace RHTower

/-- The value of `u R(u)` on the cell `[m, m+1)`. -/
def bdStepValue (c : ℕ → ℂ) (N m : ℕ) : ℂ :=
  1 - ∑ k ∈ Finset.Ioc 0 N, c k * ((Int.fract ((m:ℝ) / k) : ℝ) : ℂ)

/-- The residual `1/u − Σ_{k ≤ N} c_k ρ_{1/k}(u)` in the tail coordinate. -/
def bdRowResidualFun (c : ℕ → ℂ) (N : ℕ) : ℝ → ℂ := fun u =>
  bdTargetFun u - ∑ k ∈ Finset.Ioc 0 N, c k * bdGenFun (1 / (k:ℝ)) u

/-- The residual vector in the Nyman–Beurling carrier. -/
def bdRowResidual (c : ℕ → ℂ) (N : ℕ) : BDCarrier :=
  bdTarget - ∑ k ∈ Finset.Ioc 0 N, c k • bdGen (1 / (k:ℝ))

/-- On a unit cell the dilated fractional part loses the fractional part of `u`. -/
theorem fract_div_sub_fract_div {k m : ℕ} (hk : 0 < k) {u : ℝ} (hm : (m:ℝ) ≤ u)
    (hm1 : u < m + 1) :
    Int.fract (u / k) - Int.fract u / k = Int.fract ((m:ℝ) / k) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  set f := u - m with hf
  have hf0 : 0 ≤ f := by linarith
  have hf1 : f < 1 := by linarith
  have hfu : Int.fract u = f := by
    rw [Int.fract_eq_iff]
    exact ⟨hf0, hf1, m, by rw [hf]; push_cast; ring⟩
  have hmod : ((m % k : ℕ) : ℝ) + 1 ≤ k := by
    have := Nat.mod_lt m hk
    exact_mod_cast this
  have hdecomp : (m:ℝ) = ((m % k : ℕ) : ℝ) + k * ((m / k : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div m k).symm
  have hfuk : Int.fract (u / k) = (((m % k : ℕ) : ℝ) + f) / k := by
    rw [Int.fract_eq_iff]
    refine ⟨by positivity, ?_, ((m / k : ℕ) : ℤ), ?_⟩
    · rw [div_lt_one hk']; linarith
    · have hnum : u - (((m % k : ℕ) : ℝ) + f) = k * ((m / k : ℕ) : ℝ) := by
        rw [hf]; linarith [hdecomp]
      rw [← sub_div, hnum, Int.cast_natCast]
      field_simp
  rw [hfuk, hfu, Int.fract_div_natCast_eq_div_natCast_mod]
  field_simp
  ring

/-- **Step form of the residual.** On the cell `[m, m+1)`, `R(u) = S_m / u`. -/
theorem bdRowResidualFun_eq_step (c : ℕ → ℂ) (N : ℕ) {m : ℕ} {u : ℝ} (hm : (m:ℝ) ≤ u)
    (hm1 : u < m + 1) :
    bdRowResidualFun c N u = bdStepValue c N m * ((u : ℂ))⁻¹ := by
  unfold bdRowResidualFun bdStepValue bdTargetFun
  have hgen : ∀ k ∈ Finset.Ioc 0 N, bdGenFun (1 / (k:ℝ)) u =
      ((Int.fract ((m:ℝ) / k) : ℝ) : ℂ) * ((u : ℂ))⁻¹ := by
    intro k hk
    have hk0 : 0 < k := (Finset.mem_Ioc.mp hk).1
    unfold bdGenFun
    rw [← fract_div_sub_fract_div hk0 hm hm1]
    congr 1
    rw [show (1 / (k:ℝ)) * u = u / k by ring]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k hk => by rw [hgen k hk], sub_mul, one_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem bdRowResidual_coeFn (c : ℕ → ℂ) (N : ℕ) :
    (bdRowResidual c N : ℝ → ℂ) =ᵐ[bdMeasure] bdRowResidualFun c N := by
  classical
  have hsum : ∀ (s : Finset ℕ),
      ((∑ k ∈ s, c k • bdGen (1 / (k:ℝ)) : BDCarrier) : ℝ → ℂ) =ᵐ[bdMeasure]
        fun u => ∑ k ∈ s, c k * bdGenFun (1 / (k:ℝ)) u := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 bdMeasure] with u hu
      simpa using hu
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • bdGen (1 / (i:ℝ))) (∑ k ∈ s, c k • bdGen (1 / (k:ℝ))),
        Lp.coeFn_smul (c i) (bdGen (1 / (i:ℝ))), (memLp_bdGenFun (1 / (i:ℝ))).coeFn_toLp, ih]
        with u h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h4, Finset.sum_insert hi, smul_eq_mul]
      unfold bdGen
      rw [h3]
  filter_upwards [Lp.coeFn_sub bdTarget (∑ k ∈ Finset.Ioc 0 N, c k • bdGen (1 / (k:ℝ))),
    memLp_bdTargetFun.coeFn_toLp, hsum (Finset.Ioc 0 N)] with u h1 h2 h3
  rw [bdRowResidual, h1, Pi.sub_apply, h3]
  unfold bdTarget
  rw [h2]
  rfl

/-- **Cell bound.** `|S_m| ≤ (m+1)‖R‖` for every `m ≥ 1`. -/
theorem norm_bdStepValue_le (c : ℕ → ℂ) (N : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ‖bdStepValue c N m‖ ≤ (m + 1) * ‖bdRowResidual c N‖ := by
  set v := bdRowResidual c N
  set S := bdStepValue c N m with hS
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hsq : ‖v‖ ^ 2 = ∫ u, ‖(v : ℝ → ℂ) u‖ ^ 2 ∂bdMeasure :=
    GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral v
  have hint : Integrable (fun u => ‖(v : ℝ → ℂ) u‖ ^ 2) bdMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hnonneg : 0 ≤ᵐ[bdMeasure] fun u => ‖(v : ℝ → ℂ) u‖ ^ 2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hsub : Ioo (m:ℝ) (m + 1) ⊆ Ioi 1 := fun u hu => lt_of_le_of_lt hm1 hu.1
  have hrestrict : (bdMeasure.restrict (Ioo (m:ℝ) (m + 1))) = volume.restrict (Ioo (m:ℝ) (m + 1)) := by
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub]
  have hle1 : (∫ u in Ioo (m:ℝ) (m + 1), ‖(v : ℝ → ℂ) u‖ ^ 2 ∂bdMeasure) ≤ ‖v‖ ^ 2 := by
    rw [hsq]; exact setIntegral_le_integral hint hnonneg
  have hae : ∀ᵐ u ∂(volume.restrict (Ioo (m:ℝ) (m + 1))),
      ‖(v : ℝ → ℂ) u‖ ^ 2 = ‖S‖ ^ 2 / u ^ 2 := by
    have h1 : ∀ᵐ u ∂(volume.restrict (Ioo (m:ℝ) (m + 1))),
        (v : ℝ → ℂ) u = bdRowResidualFun c N u := by
      rw [← hrestrict]
      exact ae_restrict_of_ae (bdRowResidual_coeFn c N)
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with u hu hmem
    have hu0 : 0 < u := by linarith [hmem.1]
    rw [hu, bdRowResidualFun_eq_step c N hmem.1.le hmem.2, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0, ← hS]
    field_simp
  have hlow : ‖S‖ ^ 2 / ((m:ℝ) + 1) ^ 2 ≤
      ∫ u in Ioo (m:ℝ) (m + 1), ‖(v : ℝ → ℂ) u‖ ^ 2 ∂bdMeasure := by
    rw [hrestrict, integral_congr_ae hae]
    have hconst : (∫ _u in Ioo (m:ℝ) (m + 1), ‖S‖ ^ 2 / ((m:ℝ) + 1) ^ 2) =
        ‖S‖ ^ 2 / ((m:ℝ) + 1) ^ 2 := by
      rw [setIntegral_const, Real.volume_real_Ioo]
      simp
    rw [← hconst]
    apply setIntegral_mono_on (integrableOn_const (hs := measure_Ioo_lt_top.ne)) _ measurableSet_Ioo
    · intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      exact pow_le_pow_left₀ hu0.le hu.2.le 2
    · refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Ioo_subset_Icc_self
      apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      intro u hu
      have : 0 < u := by linarith [hu.1]
      positivity
  have hfinal : ‖S‖ ^ 2 ≤ (((m:ℝ) + 1) * ‖v‖) ^ 2 := by
    have h := hlow.trans hle1
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith
  have hX : 0 ≤ ((m:ℝ) + 1) * ‖v‖ := by positivity
  nlinarith [norm_nonneg S]

theorem bdStepValue_zero (c : ℕ → ℂ) (N : ℕ) : bdStepValue c N 0 = 1 := by
  simp [bdStepValue]

/-- **Telescoping.** `S_{a+1} − S_a = −Σ_k c_k/k + Σ_{k ∣ a+1} c_k`. -/
theorem bdStepValue_succ_sub (c : ℕ → ℂ) (N a : ℕ) :
    bdStepValue c N (a + 1) - bdStepValue c N a =
      -(∑ k ∈ Finset.Ioc 0 N, c k / k) + ∑ k ∈ (Finset.Ioc 0 N).filter (· ∣ a + 1), c k := by
  unfold bdStepValue
  have hfr : ∀ k ∈ Finset.Ioc 0 N, ((Int.fract (((a + 1 : ℕ) : ℝ) / k) : ℝ) : ℂ) -
      ((Int.fract ((a : ℝ) / k) : ℝ) : ℂ) = 1 / k - if k ∣ a + 1 then 1 else 0 := by
    intro k hk
    have hk0 : 0 < k := (Finset.mem_Ioc.mp hk).1
    have hk' : (0:ℝ) < k := by exact_mod_cast hk0
    have hform : ∀ n : ℕ, Int.fract ((n:ℝ) / k) = (n:ℝ) / k - ((n / k : ℕ) : ℝ) := by
      intro n
      rw [Int.fract_div_natCast_eq_div_natCast_mod]
      have hd : (n:ℝ) = ((n % k : ℕ) : ℝ) + k * ((n / k : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mod_add_div n k).symm
      field_simp
      linarith
    rw [hform, hform, Nat.succ_div]
    split_ifs <;> push_cast <;> ring
  have hsplit : (∑ k ∈ Finset.Ioc 0 N, c k * ((Int.fract (((a + 1 : ℕ) : ℝ) / k) : ℝ) : ℂ)) -
      ∑ k ∈ Finset.Ioc 0 N, c k * ((Int.fract ((a : ℝ) / k) : ℝ) : ℂ) =
      ∑ k ∈ Finset.Ioc 0 N, c k * (1 / k - if k ∣ a + 1 then 1 else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k hk => by rw [← mul_sub, hfr k hk]
  have hrhs : (∑ k ∈ Finset.Ioc 0 N, c k * (1 / k - if k ∣ a + 1 then 1 else 0)) =
      (∑ k ∈ Finset.Ioc 0 N, c k / k) - ∑ k ∈ (Finset.Ioc 0 N).filter (· ∣ a + 1), c k := by
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  push_cast at hsplit ⊢
  linear_combination -hsplit - hrhs

/-- The divisor sum of the row over all divisors. -/
theorem sum_filter_dvd_eq_sum_divisors_complex (c : ℕ → ℂ) (N : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    (∑ k ∈ (Finset.Ioc 0 N).filter (· ∣ d), c k) =
      ∑ k ∈ d.divisors, if k ≤ N then c k else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, hkN⟩, hkd⟩
    exact ⟨⟨hkd, by omega⟩, hkN⟩
  · rintro ⟨⟨hkd, _⟩, hkN⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hkd (by omega), hkN⟩, hkd⟩

/-- **Möbius inversion of the steps.** For `n ≥ 2`, `Σ_{d ∣ n} μ(n/d)(S_d − S_{d−1}) = ĉ_n`. -/
theorem sum_moebius_bdStep_diff (c : ℕ → ℂ) (N : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (∑ d ∈ n.divisors, (μ (n / d) : ℂ) * (bdStepValue c N d - bdStepValue c N (d - 1))) =
      if n ≤ N then c n else 0 := by
  set ĉ : ℕ → ℂ := fun k => if k ≤ N then c k else 0
  set C₁ := ∑ k ∈ Finset.Ioc 0 N, c k / k
  have hstep : ∀ d ∈ n.divisors, bdStepValue c N d - bdStepValue c N (d - 1) =
      -C₁ + ∑ k ∈ d.divisors, ĉ k := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    obtain ⟨a, rfl⟩ : ∃ a, d = a + 1 := ⟨d - 1, by omega⟩
    rw [Nat.add_sub_cancel, bdStepValue_succ_sub, sum_filter_dvd_eq_sum_divisors_complex c N hd1]
  rw [Finset.sum_congr rfl fun d hd => by rw [hstep d hd]]
  simp only [mul_add, Finset.sum_add_distrib]
  have hmu0 : (∑ d ∈ n.divisors, (μ (n / d) : ℂ) * -C₁) = 0 := by
    rw [← Finset.sum_mul, Nat.sum_div_divisors n (fun e => (μ e : ℂ))]
    have h := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℂ))
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    push_cast at h
    rw [h, if_neg (by omega), zero_mul]
  rw [hmu0, zero_add]
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (f := ĉ)
    (g := fun d => ∑ k ∈ d.divisors, ĉ k)).mp (fun _ _ => rfl) n (by omega)
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℤ) • ∑ k ∈ b.divisors, ĉ k)] at hinv
  have hĉ : (if n ≤ N then c n else 0) = ĉ n := rfl
  rw [hĉ, ← hinv]
  apply Finset.sum_congr rfl
  intro d _
  rw [zsmul_eq_mul]

/-- **Báez-Duarte rigidity.** For every finite row and every `n ≥ 2`,
`|ĉ_n + μ(n)| ≤ (Σ_{d ∣ n}(2d+1)) ‖R‖`, with no bound on the coefficients. -/
theorem norm_bdRow_add_moebius_le (c : ℕ → ℂ) (N : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ‖(if n ≤ N then c n else 0) + (μ n : ℂ)‖ ≤
      (∑ d ∈ n.divisors, (2 * (d:ℝ) + 1)) * ‖bdRowResidual c N‖ := by
  set ε := ‖bdRowResidual c N‖
  set T : ℕ → ℂ := fun d =>
    bdStepValue c N d - bdStepValue c N (d - 1) + if d = 1 then 1 else 0
  have hid : (if n ≤ N then c n else 0) + (μ n : ℂ) =
      ∑ d ∈ n.divisors, (μ (n / d) : ℂ) * T d := by
    simp only [T, mul_add, Finset.sum_add_distrib]
    rw [sum_moebius_bdStep_diff c N hn]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp
    · intro d _ hd1; simp [hd1]
    · intro h; exact absurd (Nat.one_mem_divisors.mpr (by omega)) h
  have hT : ∀ d ∈ n.divisors, ‖T d‖ ≤ (2 * (d:ℝ) + 1) * ε := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    by_cases h1 : d = 1
    · subst h1
      have hS := norm_bdStepValue_le c N (m := 1) le_rfl
      have hT1 : T 1 = bdStepValue c N 1 := by simp [T, bdStepValue_zero]
      rw [hT1]
      have hS' : ‖bdStepValue c N 1‖ ≤ 2 * ε := by
        have h := hS
        push_cast at h
        have hε : ‖bdRowResidual c N‖ = ε := rfl
        rw [hε] at h
        linarith
      have : 0 ≤ ε := norm_nonneg _
      push_cast
      linarith
    · have hd2 : 2 ≤ d := by omega
      simp only [T, if_neg h1, add_zero]
      have hA := norm_bdStepValue_le c N (m := d) hd1
      have hB := norm_bdStepValue_le c N (m := d - 1) (by omega)
      have hcast : ((d - 1 : ℕ) : ℝ) = (d:ℝ) - 1 := by
        rw [Nat.cast_sub hd1]; simp
      rw [hcast] at hB
      calc ‖bdStepValue c N d - bdStepValue c N (d - 1)‖
          ≤ ‖bdStepValue c N d‖ + ‖bdStepValue c N (d - 1)‖ := norm_sub_le _ _
        _ ≤ ((d:ℝ) + 1) * ε + ((d:ℝ) - 1 + 1) * ε := add_le_add hA hB
        _ = (2 * (d:ℝ) + 1) * ε := by ring
  rw [hid, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul]
  have hmu : ‖(μ (n / d) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖(μ (n / d) : ℂ)‖ * ‖T d‖ ≤ 1 * ((2 * (d:ℝ) + 1) * ε) :=
        mul_le_mul hmu (hT d hd) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Approximants converge to `−μ`.** If rows have Báez-Duarte residuals tending to zero, then every
coefficient with index `n ≥ 2` tends to `−μ(n)`. -/
theorem tendsto_bdRow_neg_moebius (c : ℕ → ℕ → ℂ) (N : ℕ → ℕ)
    (hE : Tendsto (fun j => ‖bdRowResidual (c j) (N j)‖) atTop (𝓝 0)) {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun j => if n ≤ N j then c j n else 0) atTop (𝓝 (-(μ n : ℂ))) := by
  have hb : Tendsto (fun j => (∑ d ∈ n.divisors, (2 * (d:ℝ) + 1)) *
      ‖bdRowResidual (c j) (N j)‖) atTop (𝓝 0) := by
    simpa using hE.const_mul (∑ d ∈ n.divisors, (2 * (d:ℝ) + 1))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hb
  rw [sub_neg_eq_add]
  exact norm_bdRow_add_moebius_le (c j) (N j) hn

/-- **Node-set rigidity.** Rows supported on `S` with residuals tending to zero force every
`n ≥ 2` with `μ(n) ≠ 0` into `S`. -/
theorem mem_of_moebius_ne_zero_of_tendsto_bdRow (S : Set ℕ) (c : ℕ → ℕ → ℂ) (N : ℕ → ℕ)
    (hS : ∀ j, ∀ k ∈ Finset.Ioc 0 (N j), k ∉ S → c j k = 0)
    (hE : Tendsto (fun j => ‖bdRowResidual (c j) (N j)‖) atTop (𝓝 0))
    {n : ℕ} (hn : 2 ≤ n) (hμ : μ n ≠ 0) : n ∈ S := by
  by_contra hnS
  have hlim := tendsto_bdRow_neg_moebius c N hE hn
  have hzero : (fun j => if n ≤ N j then c j n else 0) = fun _ => (0:ℂ) := by
    funext j
    split_ifs with h
    · exact hS j n (Finset.mem_Ioc.mpr ⟨by omega, h⟩) hnS
    · rfl
  rw [hzero] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  apply hμ
  have h2 : (μ n : ℂ) = 0 := neg_eq_zero.mp this.symm
  exact_mod_cast h2

/-- Rows supported on the primes keep a Báez-Duarte residual of at least `1/28`
(the obstruction is `μ(6) = 1`). -/
theorem bdRow_floor_primes (c : ℕ → ℂ) (N : ℕ) (hc : ∀ k ∈ Finset.Ioc 0 N, ¬ k.Prime → c k = 0) :
    (1:ℝ) / 28 ≤ ‖bdRowResidual c N‖ := by
  have h := norm_bdRow_add_moebius_le c N (n := 6) (by norm_num)
  have hc6 : (if 6 ≤ N then c 6 else 0) = 0 := by
    split_ifs with h6
    · exact hc 6 (Finset.mem_Ioc.mpr ⟨by norm_num, h6⟩) (by decide)
    · rfl
  have hμ6 : (μ 6 : ℂ) = 1 := by
    have hcop : Nat.Coprime 2 3 := by norm_num
    rw [show (6:ℕ) = 2 * 3 by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  have hdiv : (∑ d ∈ (6:ℕ).divisors, (2 * (d:ℝ) + 1)) = 28 := by
    rw [show (6:ℕ).divisors = {1, 2, 3, 6} by decide]
    norm_num
  rw [hc6, hμ6, zero_add, norm_one, hdiv] at h
  linarith

/-- `∫_m^{m+1} u^{-2} du = 1/(m(m+1))`. -/
theorem integral_Ico_inv_sq {m : ℝ} (hm : 0 < m) :
    (∫ u in Ico m (m + 1), (u ^ 2)⁻¹) = 1 / (m * (m + 1)) := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hderiv : ∀ x ∈ Set.uIcc m (m + 1), HasDerivAt (fun u : ℝ => -u⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := (hasDerivAt_inv hx0).neg
    rw [neg_neg] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have : 0 < x := by linarith [hx.1]
    positivity

/-- **Exact discrete form of the Báez-Duarte distance.**
`‖R‖² = Σ_{m ≥ 1} |S_m|²/(m(m+1))` with `S_m = 1 − Σ_{k ≤ N} c_k{m/k}`. -/
theorem hasSum_bdStepValue_sq (c : ℕ → ℂ) (N : ℕ) :
    HasSum (fun n : ℕ => ‖bdStepValue c N (n + 1)‖ ^ 2 / (((n:ℝ) + 1) * ((n:ℝ) + 2)))
      (‖bdRowResidual c N‖ ^ 2) := by
  set v := bdRowResidual c N
  set cell : ℕ → Set ℝ := fun n => Ico ((n:ℝ) + 1) ((n:ℝ) + 2)
  have hcell_meas : ∀ n, MeasurableSet (cell n) := fun n => measurableSet_Ico
  have hdisj : Pairwise (Function.onFun Disjoint cell) := by
    intro i j hij
    simp only [Function.onFun, cell]
    rw [Set.disjoint_left]
    intro x hxi hxj
    have h1 : (i:ℝ) + 1 ≤ x := hxi.1
    have h2 : x < (i:ℝ) + 2 := hxi.2
    have h3 : (j:ℝ) + 1 ≤ x := hxj.1
    have h4 : x < (j:ℝ) + 2 := hxj.2
    have hlt1 : (i:ℝ) < (j:ℝ) + 1 := by linarith
    have hlt2 : (j:ℝ) < (i:ℝ) + 1 := by linarith
    have : i = j := by
      have a1 : i < j + 1 := by exact_mod_cast hlt1
      have a2 : j < i + 1 := by exact_mod_cast hlt2
      omega
    exact hij this
  have hunion : (⋃ n, cell n) = Ici (1:ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ici, cell, Set.mem_Ico]
    constructor
    · rintro ⟨n, h1, _⟩
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hx
      refine ⟨⌊x⌋₊ - 1, ?_, ?_⟩
      · have hf : (1:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
        rw [Nat.cast_sub hf]
        push_cast
        linarith [Nat.floor_le (show 0 ≤ x by linarith)]
      · have hf : (1:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
        rw [Nat.cast_sub hf]
        push_cast
        linarith [Nat.lt_floor_add_one x]
  have hint : Integrable (fun u => ‖(v : ℝ → ℂ) u‖ ^ 2) bdMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hIci : IntegrableOn (fun u => ‖(v : ℝ → ℂ) u‖ ^ 2) (Ici (1:ℝ)) volume := by
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioi_ae_eq_Ici]
    exact hint
  have hsum := hasSum_integral_iUnion (f := fun u => ‖(v : ℝ → ℂ) u‖ ^ 2) hcell_meas hdisj
    (by rwa [hunion])
  rw [hunion] at hsum
  have htotal : (∫ u in Ici (1:ℝ), ‖(v : ℝ → ℂ) u‖ ^ 2) = ‖v‖ ^ 2 := by
    rw [GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral v, integral_Ici_eq_integral_Ioi]
  rw [htotal] at hsum
  suffices h : ∀ n : ℕ, (∫ x in cell n, ‖(v : ℝ → ℂ) x‖ ^ 2) =
      ‖bdStepValue c N (n + 1)‖ ^ 2 / (((n:ℝ) + 1) * ((n:ℝ) + 2)) by
    simpa only [h] using hsum
  intro n
  have hm0 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hne1 : ∀ᵐ u ∂(volume.restrict (cell n)), u ≠ 1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  have hbd : ∀ᵐ u ∂volume, u ∈ Ioi (1:ℝ) → (v : ℝ → ℂ) u = bdRowResidualFun c N u :=
    (ae_restrict_iff' measurableSet_Ioi).mp (bdRowResidual_coeFn c N)
  have hae : ∀ᵐ u ∂(volume.restrict (cell n)),
      ‖(v : ℝ → ℂ) u‖ ^ 2 = ‖bdStepValue c N (n + 1)‖ ^ 2 * (u ^ 2)⁻¹ := by
    filter_upwards [hne1, ae_restrict_of_ae hbd, ae_restrict_mem (hcell_meas n)]
      with u hu1 hvu hmem
    simp only [cell, Set.mem_Ico] at hmem
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hgt : (1:ℝ) < u := lt_of_le_of_ne (by linarith [hmem.1]) (Ne.symm hu1)
    have hu0 : 0 < u := by linarith
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n:ℝ) + 1 := by push_cast; ring
    rw [hvu hgt, bdRowResidualFun_eq_step c N (m := n + 1) (by rw [hcast]; exact hmem.1)
      (by rw [hcast]; linarith [hmem.2]), norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu0]
    field_simp
  rw [integral_congr_ae hae, integral_const_mul]
  simp only [cell]
  rw [show (n:ℝ) + 2 = ((n:ℝ) + 1) + 1 by ring, integral_Ico_inv_sq hm0]
  field_simp

end RHTower
