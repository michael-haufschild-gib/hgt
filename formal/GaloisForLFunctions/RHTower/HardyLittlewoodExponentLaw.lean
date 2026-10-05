import GaloisForLFunctions.RHTower.HardyLittlewoodMellinCriterion
import GaloisForLFunctions.RHTower.RieszFunctionExponentLaw
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The Hardy--Littlewood exponent law

Let `Θ = sup {Re ρ : ζ(ρ) = 0}` and `H(x) = Σ_{k ≥ 1} (-x)^k/(k! ζ(2k+1))`.  Then `H` grows with
exponent exactly `(Θ - 1)/2`:

* if `|M(N)| ≤ C (N+1)^a` with `a + δ ≤ 1`, then `H(x) = O(x^{(a+δ-1)/2})`: Abel summation against
  `f(n) = n^{-1} e^{-x/n²}` (consecutive differences `≪ x^{-2θ} n^{4θ-2}`), where the partial sums
  of `μ(n) f(n)` converge to `H(x)` because `Σ μ(n)/n = 0` (the prime number theorem);
* unconditionally `|H(x)| ≤ ζ(1 + 2η) x^η` for every `η > 0`;
* conversely `H(x) = O(x^b)` forces `Θ ≤ 1 + 2b` by the Mellin continuation of `H`.

Hence `Θ = 1 + 2 inf {b : H(x) = O(x^b)}`; `Θ = ½` is the Hardy--Littlewood criterion: RH holds if
and only if `Σ_{k ≥ 1} (-x)^k/(k! ζ(2k+1)) = O(x^{-1/4+ε})` for every `ε > 0`.
-/

open Filter Finset
open scoped Topology

namespace RHTower

noncomputable section

/-! ## The prime number theorem input -/

/-- `Σ_{n ≤ N} μ(n)/n → 0` (the prime number theorem in Möbius form). -/
theorem tendsto_sum_range_succ_moebius_div :
    Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), (ArithmeticFunction.moebius n : ℝ) / n)
      atTop (𝓝 0) := by
  have h := (Asymptotics.isLittleO_one_iff ℝ).mp mu_pnt_alt
  have hN : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  refine (h.comp hN).congr fun N => ?_
  simp only [Function.comp_apply, Nat.floor_natCast]

/-- The unregularized partial sums `Σ_{n ≤ N} μ(n) n^{-1} e^{-x/n²}` converge to `H(x)`. -/
theorem tendsto_sum_moebius_mul_inv_exp {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), (ArithmeticFunction.moebius n : ℝ) *
      ((n : ℝ)⁻¹ * Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)))) atTop (𝓝 (hardyLittlewoodFunction x)) := by
  have h1 : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), hardyLittlewoodTerm x n) atTop
      (𝓝 (hardyLittlewoodFunction x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (summable_hardyLittlewoodTerm hx).hasSum.tendsto_sum_nat
  have h2 := h1.add tendsto_sum_range_succ_moebius_div
  rw [add_zero] at h2
  refine h2.congr fun N => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  unfold hardyLittlewoodTerm
  ring

/-! ## The consecutive weights -/

/-- Increment of `k(u) = u e^{-xu²}`: for `0 ≤ v ≤ u`,
`|k(u) - k(v)| ≤ (u - v)(1 + xv(u+v)) e^{-xv²}`. -/
theorem abs_mul_exp_neg_sq_sub_le {x u v : ℝ} (hx : 0 ≤ x) (hv : 0 ≤ v) (hvu : v ≤ u) :
    |u * Real.exp (-(x * u ^ 2)) - v * Real.exp (-(x * v ^ 2))| ≤
      (u - v) * ((1 + x * v * (u + v)) * Real.exp (-(x * v ^ 2))) := by
  set E1 := Real.exp (-(x * u ^ 2))
  set E2 := Real.exp (-(x * v ^ 2))
  have hE1 : 0 < E1 := Real.exp_pos _
  have hE2 : 0 < E2 := Real.exp_pos _
  have huv : 0 ≤ u - v := by linarith
  have hsq : v ^ 2 ≤ u ^ 2 := by nlinarith
  have h12 : E1 ≤ E2 := Real.exp_le_exp.mpr (by nlinarith)
  have hlow : E2 * (1 - x * (u ^ 2 - v ^ 2)) ≤ E1 := by
    have h := Real.add_one_le_exp (-(x * (u ^ 2 - v ^ 2)))
    have hsplit : E1 = E2 * Real.exp (-(x * (u ^ 2 - v ^ 2))) := by
      simp only [E1, E2]; rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    nlinarith
  have hfac : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
  rw [hfac] at hlow
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg huv hE1.le, mul_nonneg hv (mul_nonneg hx (mul_nonneg huv
      (by linarith : (0 : ℝ) ≤ u + v))), mul_nonneg (mul_nonneg huv (mul_nonneg (mul_nonneg hx hv)
      (by linarith : (0 : ℝ) ≤ u + v))) hE2.le]
  · nlinarith [mul_nonneg huv hE2.le, mul_nonneg (mul_nonneg huv (mul_nonneg (mul_nonneg hx hv)
      (by linarith : (0 : ℝ) ≤ u + v))) hE2.le]

/-- Consecutive Hardy--Littlewood weights `f(n) = n^{-1} e^{-x/n²}`: for `n ≥ 1`, `x > 0`,
`0 ≤ θ ≤ 1`: `|f(n) - f(n+1)| ≤ 3 · 128^θ x^{-2θ} n^{4θ-2}`. -/
theorem abs_inv_mul_exp_succ_sub_le {x θ : ℝ} (hx : 0 < x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    |(n : ℝ)⁻¹ * Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) -
        ((n + 1 : ℕ) : ℝ)⁻¹ * Real.exp (-(x * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹))| ≤
      3 * 128 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  push_cast
  set u : ℝ := (n : ℝ)⁻¹ with hu
  set v : ℝ := ((n : ℝ) + 1)⁻¹ with hv
  have hv0 : 0 < v := by positivity
  have hvu : v ≤ u := inv_anti₀ hn0 (by linarith)
  have hu2v : u ≤ 2 * v := by
    rw [hu, hv, ← div_eq_mul_inv, inv_le_iff_one_le_mul₀ hn0, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    linarith
  have hsqu : ((n : ℝ) ^ 2)⁻¹ = u ^ 2 := by rw [hu, inv_pow]
  have hsqv : (((n : ℝ) + 1) ^ 2)⁻¹ = v ^ 2 := by rw [hv, inv_pow]
  rw [hsqu, hsqv]
  have h1 := abs_mul_exp_neg_sq_sub_le hx.le hv0.le hvu
  set y : ℝ := x * v ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have h2 := one_add_mul_exp_neg_le_rpow hy0 hθ0 hθ1
  have hmid : (1 + x * v * (u + v)) * Real.exp (-y) ≤ 3 * ((1 + y) * Real.exp (-y)) := by
    have : x * v * (u + v) ≤ 3 * y := by rw [hy]; nlinarith [mul_pos hx hv0]
    have hE := Real.exp_pos (-y)
    nlinarith
  have hdiff : u - v ≤ 1 / (n : ℝ) ^ 2 := by
    rw [hu, hv, inv_sub_inv hn0.ne' (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have hv2pow : (v ^ 2) ^ (-(2 * θ)) = ((n : ℝ) + 1) ^ (4 * θ) := by
    rw [hv, inv_pow, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    ring_nf
  have hsucc : ((n : ℝ) + 1) ^ (4 * θ) ≤ 16 ^ θ * (n : ℝ) ^ (4 * θ) := by
    calc ((n : ℝ) + 1) ^ (4 * θ) ≤ (2 * (n : ℝ)) ^ (4 * θ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = 16 ^ θ * (n : ℝ) ^ (4 * θ) := by
          rw [Real.mul_rpow (by norm_num) hn0.le, Real.rpow_mul (by norm_num)]
          norm_num
  have hvpow : y ^ (-(2 * θ)) ≤ 16 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ) := by
    rw [hy, Real.mul_rpow hx.le (by positivity), hv2pow]
    have hxpos : 0 < x ^ (-(2 * θ)) := Real.rpow_pos_of_pos hx _
    nlinarith
  have hpow : (n : ℝ) ^ (4 * θ - 2) = (n : ℝ) ^ (4 * θ) / (n : ℝ) ^ 2 := by
    rw [show (4 * θ - 2) = 4 * θ - ((2 : ℕ) : ℝ) by norm_num, Real.rpow_sub_natCast hn0.ne']
  have h128 : (128 : ℝ) ^ θ = 8 ^ θ * 16 ^ θ := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have huv0 : 0 ≤ u - v := by linarith
  have h8 : 0 ≤ (8 : ℝ) ^ θ := Real.rpow_nonneg (by norm_num) _
  calc |u * Real.exp (-(x * u ^ 2)) - v * Real.exp (-(x * v ^ 2))|
      ≤ (u - v) * ((1 + x * v * (u + v)) * Real.exp (-(x * v ^ 2))) := h1
    _ ≤ (1 / (n : ℝ) ^ 2) * (3 * (8 ^ θ * (16 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ)))) := by
        refine mul_le_mul hdiff (hmid.trans ?_) (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hvpow h8))
          (by norm_num)
    _ = 3 * 128 ^ θ * x ^ (-(2 * θ)) * (n : ℝ) ^ (4 * θ - 2) := by
        rw [hpow, h128]; field_simp

/-! ## Mertens bounds transfer to `H` -/

/-- **Mertens bounds transfer to the Hardy--Littlewood function.**  If `|M(N)| ≤ C (N+1)^a` with
`a + δ ≤ 1`, `δ > 0`, then `|H(x)| ≤ K x^{(a+δ-1)/2}` for all `x > 0`.  Abel summation against
`f(n) = n^{-1} e^{-x/n²}`; the boundary term `M(N)/N` vanishes because `a < 1`, and the partial
sums of `μ(n) f(n)` tend to `H(x)` by the prime number theorem in the form `Σ μ(n)/n = 0`. -/
theorem abs_hardyLittlewoodFunction_le_of_mertens_bound {a δ C : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (haδ : a + δ ≤ 1) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x →
      |hardyLittlewoodFunction x| ≤ K * x ^ ((a + δ - 1) / 2) := by
  set θ : ℝ := (1 - a - δ) / 4 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have ha1 : a < 1 := by linarith
  set S : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-1 - δ)
  have hS0 : 0 ≤ S := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨2 ^ a * C * (3 * 128 ^ θ) * S, by positivity, fun x hx => ?_⟩
  set f : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) with hf
  set μr : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)
  have hA : ∀ n : ℕ, |deningerPartialSum μr n| = ‖mobiusMertensPartialSum n‖ := by
    intro n
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    simp [mobiusMertensPartialSum, mobiusComplexCoefficient, deningerPartialSum, μr]
  have hbd : Tendsto (fun N : ℕ => |deningerPartialSum μr N * f N|) atTop (𝓝 0) := by
    have hdec : Tendsto (fun N : ℕ => 2 * C * ((N : ℝ) + 1) ^ (a - 1)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := 1 - a) (by linarith)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have h' := h.const_mul (2 * C)
      rw [mul_zero] at h'
      refine h'.congr fun N => ?_
      simp only [Function.comp_apply, neg_sub]
      push_cast
      rfl
    refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hdec
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hfN : |f N| ≤ (N : ℝ)⁻¹ := by
      simp only [hf]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hN0), abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-(x * ((N : ℝ) ^ 2)⁻¹)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hx (inv_pos.mpr (pow_pos hN0 2))])
      calc (N : ℝ)⁻¹ * Real.exp (-(x * ((N : ℝ) ^ 2)⁻¹)) ≤ (N : ℝ)⁻¹ * 1 := by gcongr
        _ = (N : ℝ)⁻¹ := mul_one _
    have hinv : (N : ℝ)⁻¹ ≤ 2 * ((N : ℝ) + 1)⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hN0 (by positivity)]
      linarith
    have hpow : ((N : ℝ) + 1) ^ a * ((N : ℝ) + 1)⁻¹ = ((N : ℝ) + 1) ^ (a - 1) := by
      rw [Real.rpow_sub_one (by positivity), div_eq_mul_inv]
    rw [abs_mul, hA]
    calc ‖mobiusMertensPartialSum N‖ * |f N| ≤ C * ((N : ℝ) + 1) ^ a * (2 * ((N : ℝ) + 1)⁻¹) :=
          mul_le_mul (hM N) (hfN.trans hinv) (abs_nonneg _) (by positivity)
      _ = 2 * C * ((N : ℝ) + 1) ^ (a - 1) := by rw [← hpow]; ring
  have hlim := tendsto_sum_moebius_mul_inv_exp hx.le
  have h := abs_le_of_tendsto_of_mertens_bound (f := f) (D := 3 * 128 ^ θ * x ^ (-(2 * θ)))
    ha hδ hC (by positivity) hM hlim hbd (fun n hn => ?_)
  · calc |hardyLittlewoodFunction x| ≤ 2 ^ a * C * (3 * 128 ^ θ * x ^ (-(2 * θ))) * S := h
      _ = 2 ^ a * C * (3 * 128 ^ θ) * S * x ^ ((a + δ - 1) / 2) := by
          rw [show -(2 * θ) = (a + δ - 1) / 2 by rw [hθ]; ring]; ring
  · have hd := abs_inv_mul_exp_succ_sub_le hx hθ0 hθ1 hn
    rw [show 4 * θ - 2 = -1 - δ - a by rw [hθ]; ring] at hd
    exact hd

/-- An unconditional subpower bound: `|H(x)| ≤ ζ(1 + 2η) x^η` for every `0 < η ≤ 1`, `x ≥ 0`. -/
theorem abs_hardyLittlewoodFunction_le_rpow {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {x : ℝ}
    (hx : 0 ≤ x) :
    |hardyLittlewoodFunction x| ≤ (∑' n : ℕ, (n : ℝ) ^ (-1 - 2 * η)) * x ^ η := by
  have hsumS : Summable fun n : ℕ => (n : ℝ) ^ (-1 - 2 * η) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ n : ℕ, |hardyLittlewoodTerm x n| ≤ (n : ℝ) ^ (-1 - 2 * η) * x ^ η := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hardyLittlewoodTerm]
      exact mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg hx _)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hy : 0 ≤ x * ((n : ℝ) ^ 2)⁻¹ := by positivity
    obtain ⟨h1, h2⟩ := abs_exp_neg_sub_one_le_min hy
    have hmin : |Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) - 1| ≤ (x * ((n : ℝ) ^ 2)⁻¹) ^ η := by
      rcases le_or_gt (x * ((n : ℝ) ^ 2)⁻¹) 1 with hle | hgt
      · exact h1.trans (Real.self_le_rpow_of_le_one hy hle hη1)
      · exact h2.trans (Real.one_le_rpow hgt.le hη0.le)
    have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    unfold hardyLittlewoodTerm
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hn')]
    have hval : (n : ℝ)⁻¹ * (x * ((n : ℝ) ^ 2)⁻¹) ^ η = (n : ℝ) ^ (-1 - 2 * η) * x ^ η := by
      have e1 : ((n : ℝ) ^ 2)⁻¹ = (n : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hn'.le, Real.rpow_two]
      have e2 : (n : ℝ)⁻¹ = (n : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      rw [Real.mul_rpow hx (by positivity), e1, e2, ← Real.rpow_mul hn'.le]
      calc (n : ℝ) ^ (-1 : ℝ) * (x ^ η * (n : ℝ) ^ (-2 * η))
          = ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-2 * η)) * x ^ η := by ring
        _ = (n : ℝ) ^ (-1 - 2 * η) * x ^ η := by
            rw [← Real.rpow_add hn']; congr 2; ring
    calc |(ArithmeticFunction.moebius n : ℝ)| * ((n : ℝ)⁻¹ *
          |Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) - 1|)
        ≤ 1 * ((n : ℝ)⁻¹ * (x * ((n : ℝ) ^ 2)⁻¹) ^ η) := by gcongr
      _ = (n : ℝ) ^ (-1 - 2 * η) * x ^ η := by rw [one_mul, hval]
  unfold hardyLittlewoodFunction
  rw [← Real.norm_eq_abs, ← tsum_mul_right]
  refine (norm_tsum_le_tsum_norm (summable_hardyLittlewoodTerm hx).norm).trans ?_
  exact (summable_hardyLittlewoodTerm hx).norm.tsum_le_tsum (fun n => by
    rw [Real.norm_eq_abs]; exact hterm n) (hsumS.mul_right _)

/-! ## The Hardy--Littlewood exponent law -/

/-- **Upper half of the Hardy--Littlewood exponent law.**  `H(x) = O(x^b)` on `[1, ∞)` for every
`b > (Θ - 1)/2`. -/
theorem exists_hardyLittlewoodFunction_le_rpow_of_zetaZeroAbscissa_lt {b : ℝ}
    (hb : zetaZeroAbscissa < 1 + 2 * b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |hardyLittlewoodFunction x| ≤ C * x ^ b := by
  have hΘ := half_le_zetaZeroAbscissa
  rcases lt_or_ge 0 b with hb0 | hb0
  · set η : ℝ := min b 1 with hη
    have hη0 : 0 < η := lt_min hb0 one_pos
    have hη1 : η ≤ 1 := min_le_right _ _
    refine ⟨∑' n : ℕ, (n : ℝ) ^ (-1 - 2 * η),
      tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _, fun x hx => ?_⟩
    refine (abs_hardyLittlewoodFunction_le_rpow hη0 hη1 (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (min_le_left _ _))
      (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · set ε : ℝ := 1 + 2 * b - zetaZeroAbscissa with hε
    have hε0 : 0 < ε := by linarith
    obtain ⟨C, hC0, hC⟩ := mobiusMertens_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
    obtain ⟨K, hK0, hK⟩ := abs_hardyLittlewoodFunction_le_of_mertens_bound
      (a := zetaZeroAbscissa + ε / 2) (δ := ε / 2) (by linarith) (by positivity)
      (by rw [hε]; linarith) hC0 hC
    refine ⟨K, hK0, fun x hx => (hK x (by linarith)).trans_eq ?_⟩
    congr 2
    rw [hε]; ring

/-- **The Hardy--Littlewood exponent law.**  `Θ = 1 + 2 inf {b : H(x) = O(x^b) on [1, ∞)}`. -/
theorem zetaZeroAbscissa_eq_one_add_two_mul_sInf_hardyLittlewood_exponents :
    zetaZeroAbscissa = 1 + 2 * sInf {b : ℝ | ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |hardyLittlewoodFunction x| ≤ C * x ^ b} := by
  set S := {b : ℝ | ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |hardyLittlewoodFunction x| ≤ C * x ^ b}
    with hS
  have hlow : ∀ b ∈ S, (zetaZeroAbscissa - 1) / 2 ≤ b := fun b ⟨C, hC⟩ => by
    have := zetaZeroAbscissa_le_of_hardyLittlewoodFunction_le hC
    linarith
  have hmem : ∀ ε : ℝ, 0 < ε → (zetaZeroAbscissa - 1) / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, _, hC⟩ := exists_hardyLittlewoodFunction_le_rpow_of_zetaZeroAbscissa_lt
      (b := (zetaZeroAbscissa - 1) / 2 + ε) (by linarith)
    exact ⟨C, hC⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨_, hlow⟩
  have hinf : sInf S = (zetaZeroAbscissa - 1) / 2 := by
    refine le_antisymm ?_ (le_csInf hne hlow)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le hbdd (hmem ε hε)
  rw [hinf]
  ring

/-- **The Hardy--Littlewood criterion.**  RH holds if and only if `H(x) = O(x^{-1/4+ε})` for every
`ε > 0`. -/
theorem riemannHypothesis_iff_hardyLittlewoodFunction_le :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |hardyLittlewoodFunction x| ≤ C * x ^ (-(1 / 4) + ε) := by
  constructor
  · intro hRH ε hε
    have hΘ := zetaZeroAbscissa_eq_half_of_riemannHypothesis hRH
    obtain ⟨C, _, hC⟩ := exists_hardyLittlewoodFunction_le_rpow_of_zetaZeroAbscissa_lt
      (b := -(1 / 4) + ε) (by rw [hΘ]; linarith)
    exact ⟨C, hC⟩
  · intro h
    refine riemannHypothesis_of_zetaZeroAbscissa_eq_half
      (le_antisymm ?_ half_le_zetaZeroAbscissa)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC⟩ := h (ε / 2) (by positivity)
    have := zetaZeroAbscissa_le_of_hardyLittlewoodFunction_le hC
    linarith

/-- **The Hardy--Littlewood criterion in their form.**  RH holds if and only if
`Σ_{k ≥ 1} (-x)^k / (k! ζ(2k+1)) = O(x^{-1/4+ε})` for every `ε > 0`. -/
theorem riemannHypothesis_iff_hardyLittlewoodPowerSeries_le :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑' k : ℕ, (-1) ^ (k + 1) * (x : ℂ) ^ (k + 1) /
        (((k + 1).factorial : ℂ) * riemannZeta (2 * k + 3))‖ ≤ C * x ^ (-(1 / 4) + ε) := by
  have hnorm : ∀ x : ℝ, 1 ≤ x → ‖∑' k : ℕ, (-1) ^ (k + 1) * (x : ℂ) ^ (k + 1) /
      (((k + 1).factorial : ℂ) * riemannZeta (2 * k + 3))‖ = |hardyLittlewoodFunction x| :=
    fun x hx => by
      rw [← hardyLittlewoodFunction_eq_tsum (by linarith), Complex.norm_real, Real.norm_eq_abs]
  rw [riemannHypothesis_iff_hardyLittlewoodFunction_le]
  refine forall₂_congr fun ε _ => exists_congr fun C => forall₂_congr fun x hx => ?_
  rw [hnorm x hx]

end

end RHTower
