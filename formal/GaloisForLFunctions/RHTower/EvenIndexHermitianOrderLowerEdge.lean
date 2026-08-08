import GaloisForLFunctions.RHTower.MixedConvolutionSubpowerAbelBound
import GaloisForLFunctions.RHTower.EvenIndexHermitianAbelBound
import GaloisForLFunctions.RHTower.EvenIndexHermitianOrderUpperBound
import GaloisForLFunctions.HTGeometry.MellinPoleRadialGrowth

/-!
# The order lower edge of the even-index Hermitian channel

A subpower bound on the even-index Hermitian coefficients alone already forces a power bound on the
radial profile: if `Re R_k(2q) ≤ C (q+1)^α` then `‖A(e^{-x})‖ = O(x^{-(α+1)/(2k)})`
(`isBigO_zero_of_evenIndex_subpower`).  Feeding that into the Mellin holomorphy criterion, a
nonremovable pole `ρ` of the Dirichlet realisation in the right half-plane cannot lie beyond the
resulting decay exponent (`re_pole_le_of_evenIndex_subpower`).

Reading this contrapositively gives the order lower edge

`2 k Re ρ - 1 ≤ Ψ_k^even`,   `Ψ_k^even = limsup_q log(1 + max(Re R_k(2q), 0)) / log(q+1)`

(`le_evenIndexOrder_of_dirichletPole`): the even-index positive parts must grow at least at the
order dictated by the rightmost pole.
-/

open Complex Filter MeasureTheory Asymptotics
open scoped BigOperators Topology

namespace RHTower

/-! ### The radial bound from an even-index subpower estimate -/

/-- The Abel moment estimate in the form used by the even-index bound. -/
theorem tsum_natSucc_rpow_exp_neg_le {α y : ℝ} (hα : 0 ≤ α) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∑' N : ℕ, ((N : ℝ) + 1) ^ α * Real.exp (-((N : ℝ) * y))) ≤
      mixedSubpowerAbelConstant α * (1 / y) ^ (α + 1) := by
  obtain ⟨-, hmoment⟩ := summable_natSucc_rpow_exp_neg_and_tsum_le hα hy
  have hXge : (1 : ℝ) ≤ (1 / y) ^ (α + 1) := by
    apply Real.one_le_rpow
    · exact (one_le_div hy).2 hy1
    · linarith
  have hexp : Real.exp y ≤ Real.exp 1 := Real.exp_le_exp.mpr hy1
  have hgamma : 0 ≤ Real.Gamma (α + 1) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hfactor : 0 ≤ 2 ^ α * (1 / y) ^ (α + 1) * Real.Gamma (α + 1) := by positivity
  have hstep : 1 + Real.exp y * 2 ^ α * (1 / y) ^ (α + 1) * Real.Gamma (α + 1) ≤
      1 + Real.exp 1 * 2 ^ α * (1 / y) ^ (α + 1) * Real.Gamma (α + 1) := by
    nlinarith [hfactor, hexp]
  refine hmoment.trans (hstep.trans ?_)
  unfold mixedSubpowerAbelConstant
  have hpos : 0 ≤ Real.exp 1 * 2 ^ α * Real.Gamma (α + 1) := by positivity
  nlinarith [hXge, hpos]

/-- **Even-index radial bound.**  A subpower bound on the even-index Hermitian coefficients alone
already forces a power bound on the squared Hermitian modulus at radius `e^{-x}`. -/
theorem norm_pow_sq_le_of_evenIndex_subpower
    {a : ℕ → ℂ} {k : ℕ} {α C x : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hx : 0 < x) (hxOne : 2 * x ≤ 1)
    (ha : Summable fun N : ℕ => ‖a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N‖)
    (hupper : ∀ q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re ≤ C * ((q : ℝ) + 1) ^ α) :
    ‖(∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) ^ k‖ ^ 2 ≤
      2 * C * mixedSubpowerAbelConstant α * (1 / (2 * x)) ^ (α + 1) := by
  have h2x : (0 : ℝ) < 2 * x := by linarith
  have hbase := norm_pow_sq_le_two_mul_tsum_evenIndex_re a ha k
  have hrewrite : ∀ q : ℕ,
      (Real.exp (-x)) ^ (2 * q) = Real.exp (-((q : ℝ) * (2 * x))) := by
    intro q
    rw [exp_neg_pow]
    congr 1
    push_cast
    ring
  have hsumL : Summable
      (fun q : ℕ =>
        (mixedAdditiveConvolutionPower a k (2 * q)).re * (Real.exp (-x)) ^ (2 * q)) := by
    have h := summable_evenIndex_mixedAdditive a ha k
    have hmap := h.map Complex.reCLM.toLinearMap.toAddMonoidHom Complex.reCLM.continuous
    refine hmap.congr fun q => ?_
    show (mixedAdditiveConvolutionPower a k (2 * q) *
        ((Real.exp (-x) : ℝ) : ℂ) ^ (2 * q)).re = _
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hmomentSummable :
      Summable (fun q : ℕ => ((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x)))) :=
    (summable_natSucc_rpow_exp_neg_and_tsum_le hα h2x).1
  have hsumR : Summable
      (fun q : ℕ => C * (((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x))))) :=
    hmomentSummable.mul_left C
  have hcompare : (∑' q : ℕ,
        (mixedAdditiveConvolutionPower a k (2 * q)).re * (Real.exp (-x)) ^ (2 * q))
      ≤ ∑' q : ℕ, C * (((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x)))) := by
    refine hsumL.tsum_le_tsum (fun q => ?_) hsumR
    rw [hrewrite q]
    have hexp : (0 : ℝ) ≤ Real.exp (-((q : ℝ) * (2 * x))) := (Real.exp_pos _).le
    calc (mixedAdditiveConvolutionPower a k (2 * q)).re * Real.exp (-((q : ℝ) * (2 * x)))
        ≤ (C * ((q : ℝ) + 1) ^ α) * Real.exp (-((q : ℝ) * (2 * x))) :=
          mul_le_mul_of_nonneg_right (hupper q) hexp
      _ = C * (((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x)))) := by ring
  have hmoment := tsum_natSucc_rpow_exp_neg_le hα h2x hxOne
  have htsumR : (∑' q : ℕ, C * (((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x)))))
      = C * ∑' q : ℕ, ((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x))) := tsum_mul_left
  have hfinal := mul_le_mul_of_nonneg_left hmoment hC
  calc ‖(∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) ^ k‖ ^ 2
      ≤ 2 * ∑' q : ℕ,
          (mixedAdditiveConvolutionPower a k (2 * q)).re * (Real.exp (-x)) ^ (2 * q) := hbase
    _ ≤ 2 * ∑' q : ℕ, C * (((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x)))) := by linarith
    _ = 2 * (C * ∑' q : ℕ, ((q : ℝ) + 1) ^ α * Real.exp (-((q : ℝ) * (2 * x)))) := by
        rw [htsumR]
    _ ≤ 2 * (C * (mixedSubpowerAbelConstant α * (1 / (2 * x)) ^ (α + 1))) := by linarith
    _ = 2 * C * mixedSubpowerAbelConstant α * (1 / (2 * x)) ^ (α + 1) := by ring

/-- **Even-index radial bound on the series itself.**  Taking the `2k`-th root. -/
theorem norm_tsum_le_of_evenIndex_subpower
    {a : ℕ → ℂ} {k : ℕ} {α C x : ℝ} (hk : 0 < k) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hx : 0 < x) (hxOne : 2 * x ≤ 1)
    (ha : Summable fun N : ℕ => ‖a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N‖)
    (hupper : ∀ q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re ≤ C * ((q : ℝ) + 1) ^ α) :
    ‖∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N‖ ≤
      (2 * C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹) *
        (1 / (2 * x)) ^ ((α + 1) / (2 * (k : ℝ))) := by
  set z : ℂ := ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N with hzdef
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  have hxinv : (0 : ℝ) ≤ 1 / (2 * x) := by positivity
  set M : ℝ := 2 * C * mixedSubpowerAbelConstant α * (1 / (2 * x)) ^ (α + 1) with hMdef
  have hsq := norm_pow_sq_le_of_evenIndex_subpower hα hC hx hxOne ha hupper
  have hpow : ‖z‖ ^ (2 * k) ≤ M := by
    rw [← hzdef] at hsq
    rwa [norm_pow, ← pow_mul, mul_comm k 2] at hsq
  have hroot : ‖z‖ ≤ M ^ ((2 * (k : ℝ))⁻¹) := by
    have hcast : ‖z‖ ^ ((2 * (k : ℝ))) = ‖z‖ ^ (2 * k) := by
      rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hle : ‖z‖ ^ ((2 * (k : ℝ))) ≤ M := by rw [hcast]; exact hpow
    have hmono := Real.rpow_le_rpow (by positivity) hle (le_of_lt (inv_pos.mpr hkR))
    rwa [← Real.rpow_mul (norm_nonneg z), mul_inv_cancel₀ (ne_of_gt hkR),
      Real.rpow_one] at hmono
  refine hroot.trans (le_of_eq ?_)
  rw [hMdef, Real.mul_rpow (by positivity) (Real.rpow_nonneg hxinv _),
    ← Real.rpow_mul hxinv]
  congr 1

/-- **Even-index origin decay.**  A subpower bound on the even-index Hermitian coefficients makes
the exponential profile `O(x^{-(α+1)/(2k)})` at the origin. -/
theorem isBigO_zero_of_evenIndex_subpower
    {a : ℕ → ℂ} {k : ℕ} {α C : ℝ} (hk : 0 < k) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (habs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)
    (hupper : ∀ q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re ≤ C * ((q : ℝ) + 1) ^ α) :
    (fun x : ℝ => ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) =O[𝓝[>] (0 : ℝ)]
      fun x : ℝ => x ^ (-((α + 1) / (2 * (k : ℝ)))) := by
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  set β : ℝ := (α + 1) / (2 * (k : ℝ)) with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  have hconst : (0 : ℝ) ≤ 2 * C * mixedSubpowerAbelConstant α :=
    mul_nonneg (by linarith) hAbel
  rw [Asymptotics.isBigO_iff]
  refine ⟨(2 * C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹), ?_⟩
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hev] with x hx hxhalf
  have hx0 : (0 : ℝ) < x := hx
  have h2x1 : 2 * x ≤ 1 := by linarith
  have hr0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hbound := norm_tsum_le_of_evenIndex_subpower hk hα hC hx0 h2x1
    (habs (Real.exp (-x)) hr0 hr1) hupper
  refine hbound.trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  have hstep : (1 / (2 * x)) ^ β ≤ x ^ (-β) := by
    have h1 : (1 : ℝ) / (2 * x) ≤ 1 / x := by
      refine one_div_le_one_div_of_le hx0 ?_
      linarith
    have h2 : (1 / (2 * x)) ^ β ≤ (1 / x) ^ β := Real.rpow_le_rpow (by positivity) h1 hβ0
    have h3 : (1 / x) ^ β = x ^ (-β) := by
      rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
    rw [← h3]
    exact h2
  exact mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hconst _)

/-- **The pole cannot pass the even-index decay exponent.**  If the even-index Hermitian
coefficients obey a subpower bound of exponent `α`, then every nonremovable right half-plane pole of
the Dirichlet realisation has real part at most `(α + 1) / (2k)`. -/
theorem re_pole_le_of_evenIndex_subpower
    (a : ℕ → ℂ) (D : ℂ → ℂ) {k : ℕ} (hk : 0 < k) {ρ : ℂ} {a₀ α C : ℝ}
    (ha0 : 0 < a₀) (hρ : 0 < ρ.re) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (habs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)
    (hint : LocallyIntegrableOn (fun x => ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N)
      (Set.Ioi 0) volume)
    (htop : (fun x => ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) =O[atTop]
      fun t => Real.exp (-a₀ * t))
    (hMellin : ∀ᶠ s in 𝓝 ρ,
      mellin (fun x => ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) s = Complex.Gamma s * D s)
    (hpole : ¬ DifferentiableAt ℂ D ρ)
    (hupper : ∀ q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re ≤ C * ((q : ℝ) + 1) ^ α) :
    ρ.re ≤ (α + 1) / (2 * (k : ℝ)) := by
  by_contra hcon
  push Not at hcon
  exact GaloisForLFunctions.HTGeometry.not_isBigO_zero_of_mellin_eq_Gamma_mul
    ha0 hint htop hcon hρ hMellin hpole
    (isBigO_zero_of_evenIndex_subpower hk hα hC habs hupper)

/-! ### The logarithmic order exponent -/

/-- The even-index logarithmic order exponent `Ψ_k^even`. -/
noncomputable def evenIndexOrder (a : ℕ → ℂ) (k : ℕ) : ℝ :=
  Filter.limsup
    (fun q : ℕ => Real.log (1 + max (mixedAdditiveConvolutionPower a k (2 * q)).re 0)
      / Real.log ((q : ℝ) + 1)) Filter.atTop

/-- A polynomially dominated nonnegative sequence has bounded logarithmic order quotients. -/
theorem isBoundedUnder_log_one_add_div_log {f : ℕ → ℝ} {C : ℝ} {d : ℕ} (hC : 0 < C)
    (hf : ∀ N, 0 ≤ f N) (hbound : ∀ N, f N ≤ C * ((N : ℝ) + 1) ^ d) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ => Real.log (1 + f N) / Real.log ((N : ℝ) + 1)) := by
  refine ⟨(d : ℝ) + Real.log (1 + C) / Real.log 2, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have hlogge : Real.log 2 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpow1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
  have hle : 1 + f N ≤ (1 + C) * ((N : ℝ) + 1) ^ d := by nlinarith [hbound N, hpow1, hC]
  have hlogC : 0 < Real.log (1 + C) := Real.log_pos (by linarith)
  have key : Real.log (1 + f N) ≤ Real.log (1 + C) + (d : ℝ) * Real.log ((N : ℝ) + 1) := by
    calc Real.log (1 + f N) ≤ Real.log ((1 + C) * ((N : ℝ) + 1) ^ d) :=
          Real.log_le_log (by linarith [hf N]) hle
      _ = Real.log (1 + C) + (d : ℝ) * Real.log ((N : ℝ) + 1) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hfrac : Real.log (1 + C) / Real.log ((N : ℝ) + 1) ≤ Real.log (1 + C) / Real.log 2 :=
    div_le_div_of_nonneg_left hlogC.le hlog2 hlogge
  rw [div_le_iff₀ hlogpos]
  have hstep : Real.log (1 + C) ≤ (Real.log (1 + C) / Real.log 2) * Real.log ((N : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith [hlogge, hlogC]
  nlinarith [key, hstep]

/-- The order quotients of a unit-bounded sequence are bounded above. -/
theorem isBoundedUnder_evenIndexOrderSeq {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (j : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun q : ℕ => Real.log (1 + max (mixedAdditiveConvolutionPower a (j + 1) (2 * q)).re 0)
        / Real.log ((q : ℝ) + 1)) := by
  refine isBoundedUnder_log_one_add_div_log (C := 2 ^ (2 * j + 1)) (d := 2 * j + 1)
    (by positivity) (fun q => le_max_right _ _) (fun q => ?_)
  have hnorm := norm_mixedAdditiveConvolutionPower_le_pow ha j (2 * q)
  have hre : (mixedAdditiveConvolutionPower a (j + 1) (2 * q)).re ≤
      ((2 * q : ℕ) + 1 : ℝ) ^ (2 * j + 1) :=
    (Complex.re_le_norm _).trans (by exact_mod_cast hnorm)
  have hq : ((2 * q : ℕ) + 1 : ℝ) ≤ 2 * ((q : ℝ) + 1) := by push_cast; linarith
  have hpow : ((2 * q : ℕ) + 1 : ℝ) ^ (2 * j + 1) ≤ (2 * ((q : ℝ) + 1)) ^ (2 * j + 1) := by
    refine pow_le_pow_left₀ (by positivity) hq _
  have hmul : (2 * ((q : ℝ) + 1)) ^ (2 * j + 1)
      = 2 ^ (2 * j + 1) * ((q : ℝ) + 1) ^ (2 * j + 1) := by rw [mul_pow]
  refine max_le ?_ (by positivity)
  calc (mixedAdditiveConvolutionPower a (j + 1) (2 * q)).re
      ≤ ((2 * q : ℕ) + 1 : ℝ) ^ (2 * j + 1) := hre
    _ ≤ (2 * ((q : ℝ) + 1)) ^ (2 * j + 1) := hpow
    _ = 2 ^ (2 * j + 1) * ((q : ℝ) + 1) ^ (2 * j + 1) := hmul

/-- The logarithmic order exponent of a unit-bounded sequence is nonnegative. -/
theorem evenIndexOrder_nonneg {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (j : ℕ) :
    0 ≤ evenIndexOrder a (j + 1) := by
  refine Filter.le_limsup_of_frequently_le ?_ (isBoundedUnder_evenIndexOrderSeq ha j)
  refine Filter.Eventually.frequently ?_
  filter_upwards with q
  have hnum : 0 ≤ Real.log (1 + max (mixedAdditiveConvolutionPower a (j + 1) (2 * q)).re 0) :=
    Real.log_nonneg (by linarith [le_max_right (mixedAdditiveConvolutionPower a (j+1) (2*q)).re 0])
  have hden : 0 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
  positivity

/-- Absorbing finitely many exceptional indices into the constant of a subpower bound. -/
theorem exists_subpower_bound_of_eventually {a : ℕ → ℂ} {k : ℕ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hev : ∀ᶠ q in Filter.atTop,
      Real.log (1 + max (mixedAdditiveConvolutionPower a k (2 * q)).re 0)
        / Real.log ((q : ℝ) + 1) < lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re ≤ C * ((q : ℝ) + 1) ^ lam := by
  obtain ⟨Q₀, hQ₀⟩ := hev.exists_forall_of_atTop
  set Q : ℕ := max Q₀ 1 with hQdef
  set C : ℝ := 1 + ∑ q ∈ Finset.range Q,
    max (mixedAdditiveConvolutionPower a k (2 * q)).re 0 with hCdef
  have hsum0 : 0 ≤ ∑ q ∈ Finset.range Q, max (mixedAdditiveConvolutionPower a k (2 * q)).re 0 :=
    Finset.sum_nonneg fun q _ => le_max_right _ _
  have hC1 : 1 ≤ C := by rw [hCdef]; linarith
  refine ⟨C, by linarith, fun q => ?_⟩
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hpow1 : (1 : ℝ) ≤ ((q : ℝ) + 1) ^ lam := Real.one_le_rpow (by linarith) hlam
  have hmax : (mixedAdditiveConvolutionPower a k (2 * q)).re ≤
      max (mixedAdditiveConvolutionPower a k (2 * q)).re 0 := le_max_left _ _
  rcases lt_or_ge q Q with hq | hq
  · have hmem : max (mixedAdditiveConvolutionPower a k (2 * q)).re 0 ≤
        ∑ p ∈ Finset.range Q, max (mixedAdditiveConvolutionPower a k (2 * p)).re 0 :=
      Finset.single_le_sum (f := fun p : ℕ =>
        max (mixedAdditiveConvolutionPower a k (2 * p)).re 0)
        (fun p _ => le_max_right _ _) (Finset.mem_range.mpr hq)
    have hle : max (mixedAdditiveConvolutionPower a k (2 * q)).re 0 ≤ C := by
      rw [hCdef]; linarith
    nlinarith [hmax, hle, hpow1]
  · have hq1 : 1 ≤ q := le_trans (le_max_right Q₀ 1) hq
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hlog : 0 < Real.log ((q : ℝ) + 1) := Real.log_pos (by linarith)
    have hbound := hQ₀ q (le_trans (le_max_left Q₀ 1) hq)
    rw [div_lt_iff₀ hlog] at hbound
    have hlogle : Real.log (1 + max (mixedAdditiveConvolutionPower a k (2 * q)).re 0)
        ≤ Real.log (((q : ℝ) + 1) ^ lam) := by
      rw [Real.log_rpow (by linarith)]
      linarith
    have hposArg : (0 : ℝ) < 1 + max (mixedAdditiveConvolutionPower a k (2 * q)).re 0 := by
      have := le_max_right (mixedAdditiveConvolutionPower a k (2 * q)).re 0
      linarith
    have hle : 1 + max (mixedAdditiveConvolutionPower a k (2 * q)).re 0
        ≤ ((q : ℝ) + 1) ^ lam := by
      have hexp := Real.exp_le_exp.mpr hlogle
      rwa [Real.exp_log hposArg, Real.exp_log (by positivity)] at hexp
    nlinarith [hmax, hle, hpow1, hC1]

/-- **The order lower edge, abstract form `(8)`.**  If no subpower bound of exponent `α` on the
even-index Hermitian coefficients can push the decay exponent `(α+1)/(2k)` below a threshold `θ`,
then the even-index logarithmic order exponent is at least `2kθ - 1`. -/
theorem le_evenIndexOrder_of_subpower_threshold {a : ℕ → ℂ} {j : ℕ} {θ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hno : ∀ α C : ℝ, 0 ≤ α → 0 ≤ C →
      (∀ q : ℕ, (mixedAdditiveConvolutionPower a (j + 1) (2 * q)).re ≤ C * ((q : ℝ) + 1) ^ α) →
      θ ≤ (α + 1) / (2 * ((j : ℝ) + 1))) :
    2 * ((j : ℝ) + 1) * θ - 1 ≤ evenIndexOrder a (j + 1) := by
  by_contra hcon
  push Not at hcon
  set Psi : ℝ := evenIndexOrder a (j + 1) with hPsi
  have hPsi0 : 0 ≤ Psi := evenIndexOrder_nonneg ha j
  have htarget : 0 < 2 * ((j : ℝ) + 1) * θ - 1 := by linarith
  set lam : ℝ := (Psi + (2 * ((j : ℝ) + 1) * θ - 1)) / 2 with hlamdef
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; linarith
  have hlamPsi : Psi < lam := by rw [hlamdef]; linarith
  have hlamTarget : lam < 2 * ((j : ℝ) + 1) * θ - 1 := by rw [hlamdef]; linarith
  have hev := Filter.eventually_lt_of_limsup_lt hlamPsi (isBoundedUnder_evenIndexOrderSeq ha j)
  obtain ⟨C, hC0, hCbound⟩ := exists_subpower_bound_of_eventually (k := j + 1) hlam0 hev
  have hkey := hno lam C hlam0 hC0 hCbound
  have hkR : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hkR] at hkey
  nlinarith [hkey, hlamTarget]

/-- **The order lower edge `(8)`.**  For a unit-bounded coefficient sequence realised through the
Mellin identity by a Dirichlet function with a nonremovable pole `ρ` in the right half-plane, the
even-index logarithmic order exponent is at least `2k Re ρ - 1`. -/
theorem le_evenIndexOrder_of_dirichletPole
    (a : ℕ → ℂ) (D : ℂ → ℂ) {j : ℕ} {ρ : ℂ} {a₀ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (ha0 : 0 < a₀) (hρ : 0 < ρ.re)
    (habs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)
    (hint : LocallyIntegrableOn (fun x => ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N)
      (Set.Ioi 0) volume)
    (htop : (fun x => ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) =O[atTop]
      fun t => Real.exp (-a₀ * t))
    (hMellin : ∀ᶠ s in 𝓝 ρ,
      mellin (fun x => ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) s = Complex.Gamma s * D s)
    (hpole : ¬ DifferentiableAt ℂ D ρ) :
    2 * ((j : ℝ) + 1) * ρ.re - 1 ≤ evenIndexOrder a (j + 1) := by
  refine le_evenIndexOrder_of_subpower_threshold ha fun α C hα hC hbound => ?_
  have hkcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have hkey := re_pole_le_of_evenIndex_subpower a D (k := j + 1) (Nat.succ_pos j)
    ha0 hρ hα hC habs hint htop hMellin hpole hbound
  rwa [hkcast] at hkey

end RHTower
