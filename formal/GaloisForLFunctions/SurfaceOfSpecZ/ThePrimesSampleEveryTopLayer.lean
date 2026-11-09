import GaloisForLFunctions.SurfaceOfSpecZ.TheTensorPowerTrick

/-!
# The primes sample every top layer

`TheStepanovCountAtThePrimePowerDegrees` uses the zeros of `ζ` twice: as the exponents of the traces
and as the singularities of `ζ'/ζ`. For an arbitrary configuration only the first use is available,
and only the absence of zeros of `ζ` on `Re s = 1` is needed:

**Theorem** (`onLine_of_bddBelow_primePowers_of_max`). Let `Z` be a tempered configuration without
real zeros whose maximal real part is attained. If `2 Re S_Z(log n) ≥ −K` at every prime power `n`,
every zero of `Z` lies on the critical line.

**Proof.** Let `b = max Re ρ − ½ > 0` and `F(u) = 2 Re S_Z(u) e^{−bu} = Σ_z e_z e^{(z−b)u}`, bounded by
`E = Σ|e_z|`. Weight the prime powers by `Λ(n) n^{−σ}` and let `σ ↓ 1`:

* `Σ Λ(n) n^{−σ} → ∞` (`tendsto_vmSum_atTop`);
* `Σ Λ(n) F(log n) n^{−σ} = Σ_z e_z (−ζ'/ζ)(σ + b − z)` grows more slowly, since every `σ + b − z`
  tends to a point `≠ 1` of `Re ≥ 1`, where `ζ'/ζ` is finite (`tendsto_logDeriv_div_vmSum`): the
  top layer has no real exponent, its mean along the prime powers is `0`;
* `Σ Λ(n) F(log n)² n^{−σ}` has relative limit `Σ_{Re z = b} |e_z|² > 0`, from the pairs `(z, z̄)`.

At a prime power `F(log n) ≥ −|K| n^{−b}`, so `F² ≤ E(F + 2|K|n^{−b})`; the relative means give
`Σ |e_z|² ≤ 0`.

The attained maximum is what the arithmetic of `ζ` removes in `TheZeroFreeStripImprovesItself`; real
zeros are excluded because they mask (`ARealZeroMasksTheShallowerZeros`).
-/

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-! ### The weighted prime-power sums -/

/-- `Σ_{n ≥ 1} Λ(n) n^{−σ}`. -/
def vmSum (σ : ℝ) : ℝ := ∑' j : ℕ, Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)

theorem summable_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) := by
  have h := (summable_tsum_vonMangoldt (w := (σ : ℂ)) (by simpa using hσ)).1.norm
  refine h.congr fun j => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
    norm_natCast_add_one_cpow]
  simp

theorem ofReal_vmSum {σ : ℝ} (hσ : 1 < σ) :
    ((vmSum σ : ℝ) : ℂ) = -logDeriv riemannZeta σ := by
  obtain ⟨-, he⟩ := summable_tsum_vonMangoldt (w := (σ : ℂ)) (by simpa using hσ)
  rw [← he, vmSum, Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  rw [Complex.ofReal_mul, ofReal_add_one_rpow j (-σ)]
  push_cast; ring

theorem vmSum_nonneg (σ : ℝ) : 0 ≤ vmSum σ :=
  tsum_nonneg fun j => mul_nonneg vonMangoldt_nonneg (by positivity)

theorem vmSum_pos {σ : ℝ} (hσ : 1 < σ) : 0 < vmSum σ := by
  have h4 : Λ (1 + 1) * (((1 : ℕ) : ℝ) + 1) ^ (-σ) ≤ vmSum σ := by
    unfold vmSum
    exact (summable_vonMangoldt_rpow hσ).le_tsum 1
      (fun j _ => mul_nonneg vonMangoldt_nonneg (by positivity))
  have h5 : 0 < Λ (1 + 1) * ((1 : ℝ) + 1) ^ (-σ) := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, vonMangoldt_apply_prime Nat.prime_two]
    exact mul_pos (Real.log_pos (by norm_num)) (by positivity)
  push_cast at h4 h5
  linarith

theorem vmSum_antitone {σ σ' : ℝ} (hσ : 1 < σ) (hσσ' : σ ≤ σ') : vmSum σ' ≤ vmSum σ := by
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_vonMangoldt_rpow (by linarith))
    (summable_vonMangoldt_rpow hσ)
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hj1 (by linarith))
    vonMangoldt_nonneg

/-- `|ζ'/ζ(w)| ≤ Σ Λ(n) n^{−Re w}`. -/
theorem norm_logDeriv_le_vmSum {w : ℂ} (hw : 1 < w.re) : ‖logDeriv riemannZeta w‖ ≤ vmSum w.re := by
  obtain ⟨hs, he⟩ := summable_tsum_vonMangoldt hw
  calc ‖logDeriv riemannZeta w‖ = ‖∑' j : ℕ, (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w)‖ := by
        rw [he, norm_neg]
    _ ≤ ∑' j : ℕ, ‖(Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w)‖ := norm_tsum_le_tsum_norm hs.norm
    _ = vmSum w.re := by
        rw [vmSum]
        refine tsum_congr fun j => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
          norm_natCast_add_one_cpow]
        simp

/-- **`Σ Λ(n) n^{−σ} → ∞` as `σ ↓ 1`.** -/
theorem tendsto_vmSum_atTop : Tendsto vmSum (𝓝[>] 1) atTop := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun j => mul_nonneg vonMangoldt_nonneg (by positivity))).mp not_summable_vonMangoldt_div
  rw [tendsto_atTop]
  intro M
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp hdiv) (2 * |M| + 2) |>.exists_forall_of_atTop
  have hN' := hN N le_rfl
  -- for `σ` close to `1` each of the first `N` terms keeps half its size
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  set δ := Real.log 2 / (Real.log ((N : ℝ) + 1) + 1) with hδ
  have hδ0 : 0 < δ := div_pos (Real.log_pos (by norm_num)) (by linarith)
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with σ hσ
  obtain ⟨hσ1, hσ2⟩ := hσ
  have hfin : ∑ j ∈ Finset.range N, Λ (j + 1) * ((j : ℝ) + 1) ^ (-1 : ℝ) ≤
      2 * ∑ j ∈ Finset.range N, Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjN : (j : ℝ) + 1 ≤ N + 1 := by
      have : (j : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hj
      linarith
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hsplit : ((j : ℝ) + 1) ^ (-1 : ℝ) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (σ - 1) := by
      rw [← Real.rpow_add hj0]; ring_nf
    have hpow : ((j : ℝ) + 1) ^ (σ - 1) ≤ 2 := by
      rw [Real.rpow_def_of_pos hj0]
      calc Real.exp (Real.log ((j : ℝ) + 1) * (σ - 1)) ≤ Real.exp (Real.log 2) := by
            apply Real.exp_le_exp.mpr
            have h1 : Real.log ((j : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hj0 hjN
            have h2 : (σ - 1) * (Real.log ((N : ℝ) + 1) + 1) ≤ Real.log 2 := by
              have := (lt_div_iff₀ (by linarith : (0 : ℝ) < Real.log ((N : ℝ) + 1) + 1)).mp
                (show σ - 1 < δ by linarith)
              linarith
            have h3 : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])
            nlinarith
        _ = 2 := Real.exp_log (by norm_num)
    rw [hsplit]
    have hΛ := vonMangoldt_nonneg (n := j + 1)
    have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
    nlinarith [mul_nonneg hΛ hp]
  have hle : ∑ j ∈ Finset.range N, Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) ≤ vmSum σ :=
    Summable.sum_le_tsum (Finset.range N) (fun j _ => mul_nonneg vonMangoldt_nonneg (by positivity))
      (summable_vonMangoldt_rpow hσ1)
  linarith [le_abs_self M]

/-- **Relative mean zero off `s = 1`.** For `c₀ ≠ 0` with `Re c₀ ≥ 0`,
`ζ'/ζ(σ + c₀) / Σ Λ(n) n^{−σ} → 0` as `σ ↓ 1`. -/
theorem tendsto_logDeriv_div_vmSum {c₀ : ℂ} (hre : 0 ≤ c₀.re) (hne : c₀ ≠ 0) :
    Tendsto (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + c₀) / (vmSum σ : ℂ)) (𝓝[>] 1) (𝓝 0) := by
  have hw : (1 : ℂ) + c₀ ≠ 1 := by intro h; apply hne; linear_combination h
  have hz : riemannZeta (1 + c₀) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hcont := (differentiableAt_logDeriv_riemannZeta hw hz).continuousAt
  have hlim : Tendsto (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + c₀)) (𝓝[>] 1)
      (𝓝 (logDeriv riemannZeta (1 + c₀))) := by
    have h1 : Tendsto (fun σ : ℝ => (σ : ℂ) + c₀) (𝓝 1) (𝓝 (1 + c₀)) := by
      have := (Complex.continuous_ofReal.add continuous_const).tendsto (1 : ℝ) (f := fun σ : ℝ => (σ : ℂ) + c₀)
      simpa using this
    exact (hcont.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ σ : ℝ, ‖logDeriv riemannZeta ((σ : ℂ) + c₀) / (vmSum σ : ℂ)‖ =
      ‖logDeriv riemannZeta ((σ : ℂ) + c₀)‖ / vmSum σ := by
    intro σ
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vmSum_nonneg σ)]
  simp_rw [hnorm]
  exact (hlim.norm).div_atTop tendsto_vmSum_atTop

/-! ### The trace normalized by the top depth -/

/-- The trace normalized by a depth `b`, `F(u) = 2 Re S(u) e^{−bu}`. -/
def normTrace (Z : ZeroConfig) (b u : ℝ) : ℝ :=
  2 * (lagStructure Z (boxSpline 1 3) u).re * Real.exp (-(b * u))

/-- Every exponent has real part `≤ b`. -/
def TopDepth (Z : ZeroConfig) (b : ℝ) : Prop :=
  ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re ≤ b

/-- The weighted mean of `F` along the prime powers, `Σ Λ(n) F(log n) n^{−σ}`. -/
def normTraceMean (Z : ZeroConfig) (b σ : ℝ) : ℝ :=
  ∑' j : ℕ, Λ (j + 1) * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)

/-- The weighted mean of `F²` along the prime powers. -/
def normTraceSqMean (Z : ZeroConfig) (b σ : ℝ) : ℝ :=
  ∑' j : ℕ, Λ (j + 1) * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ)

/-- The weights of the diagonal `z + z' = 2b`. -/
def diagWeight (Z : ZeroConfig) (b : ℝ) (q : ℂ × ℂ) : ℂ :=
  if q.1 + q.2 = 2 * (b : ℂ) then
    evenCoeff Z (boxSpline 1 3) q.1 * evenCoeff Z (boxSpline 1 3) q.2 else 0

section TopLayer

variable {Z : ZeroConfig} {b : ℝ}

theorem summable_norm_evenCoeff_spline (hZ : TemperedConfig Z) :
    Summable fun z => ‖evenCoeff Z (boxSpline 1 3) z‖ := by
  have h0 := (two_re_lagStructure_eq Z hZ (contDiff_boxSpline (r := 1) one_pos 2)
    (boxSpline_support (r := 1) one_pos 3) 0).1.norm
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
  exact h0

theorem evenCoeff_conj (Z : ZeroConfig) (z : ℂ) :
    evenCoeff Z (boxSpline 1 3) (conj z) = conj (evenCoeff Z (boxSpline 1 3) z) := by
  simp only [evenCoeff, map_add, Complex.conj_conj]; ring

theorem ofReal_normTrace (hZ : TemperedConfig Z) (u : ℝ) :
    ((normTrace Z b u : ℝ) : ℂ) = ∑' z, evenCoeff Z (boxSpline 1 3) z * cexp ((z - b) * u) := by
  obtain ⟨-, he⟩ := two_re_lagStructure_eq Z hZ (contDiff_boxSpline (r := 1) one_pos 2)
    (boxSpline_support (r := 1) one_pos 3) u
  rw [normTrace, Complex.ofReal_mul, he, ← tsum_mul_right]
  refine tsum_congr fun z => ?_
  rw [mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem norm_evenCoeff_mul_cexp_le (h : TopDepth Z b) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖evenCoeff Z (boxSpline 1 3) z * cexp ((z - b) * u)‖ ≤ ‖evenCoeff Z (boxSpline 1 3) z‖ := by
  by_cases hz : evenCoeff Z (boxSpline 1 3) z = 0
  · simp [hz]
  rw [norm_mul, Complex.norm_exp]
  have h1 := h z hz
  have : ((z - b) * u).re ≤ 0 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero, mul_zero]
    nlinarith
  calc ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp ((z - b) * u).re
      ≤ ‖evenCoeff Z (boxSpline 1 3) z‖ * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr this) (norm_nonneg _)
    _ = _ := mul_one _

theorem abs_normTrace_le (hZ : TemperedConfig Z) (h : TopDepth Z b) {u : ℝ} (hu : 0 ≤ u) :
    |normTrace Z b u| ≤ ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ := by
  have hE := summable_norm_evenCoeff_spline hZ
  have hs : Summable fun z => evenCoeff Z (boxSpline 1 3) z * cexp ((z - b) * u) :=
    Summable.of_norm_bounded hE fun z => norm_evenCoeff_mul_cexp_le h z hu
  have hc := congrArg norm (ofReal_normTrace (b := b) hZ u)
  rw [Complex.norm_real, Real.norm_eq_abs] at hc
  rw [hc]
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (Summable.tsum_le_tsum (fun z => norm_evenCoeff_mul_cexp_le h z hu) hs.norm hE)

theorem log_add_one_nonneg (j : ℕ) : 0 ≤ Real.log ((j : ℝ) + 1) :=
  Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])

theorem summable_normTraceMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun j : ℕ => Λ (j + 1) * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) := by
  refine Summable.of_norm_bounded ((summable_vonMangoldt_rpow hσ).mul_left
    (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ (-σ))]
  have := abs_normTrace_le hZ h (log_add_one_nonneg j)
  have hΛ := vonMangoldt_nonneg (n := j + 1)
  have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
  nlinarith [mul_nonneg hΛ hp]

theorem summable_normTraceSqMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun j : ℕ => Λ (j + 1) * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ) := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖
  refine Summable.of_nonneg_of_le (fun j => by
      have := vonMangoldt_nonneg (n := j + 1); positivity) (fun j => ?_)
    ((summable_vonMangoldt_rpow hσ).mul_left (E ^ 2))
  have h1 := abs_normTrace_le hZ h (log_add_one_nonneg j)
  have hsq : normTrace Z b (Real.log (j + 1)) ^ 2 ≤ E ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hΛ := vonMangoldt_nonneg (n := j + 1)
  have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
  calc Λ (j + 1) * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ)
      = normTrace Z b (Real.log (j + 1)) ^ 2 * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := by ring
    _ ≤ E ^ 2 * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) :=
        mul_le_mul_of_nonneg_right hsq (mul_nonneg hΛ hp)

/-- **The mean of `F` through the zeros.** `Σ Λ(n) F(log n) n^{−σ} = Σ_z e_z (−ζ'/ζ)(σ + b − z)`. -/
theorem ofReal_normTraceMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) :
    ((normTraceMean Z b σ : ℝ) : ℂ) = ∑' z, evenCoeff Z (boxSpline 1 3) z *
      (-logDeriv riemannZeta ((σ : ℂ) + (b - z))) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  set f : ℕ → ℂ → ℂ := fun j z => (Λ (j + 1) : ℂ) * (e z * ((j : ℂ) + 1) ^ (-((σ : ℂ) + (b - z))))
    with hfdef
  have hfn : ∀ j z, ‖f j z‖ ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) * ‖e z‖ := by
    intro j z
    by_cases hz : e z = 0
    · simp [hfdef, hz]
    have h1 := h z hz
    simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg, norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-((σ : ℂ) + (b - z))).re ≤ ((j : ℝ) + 1) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp; linarith
    have hΛ0 := vonMangoldt_nonneg (n := j + 1)
    calc Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-((σ : ℂ) + (b - z))).re)
        ≤ Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) hΛ0
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × ℂ => Λ (p.1 + 1) * ((p.1 : ℝ) + 1) ^ (-σ) * ‖e p.2‖ :=
    (summable_vonMangoldt_rpow hσ).mul_of_nonneg hE
      (fun j => mul_nonneg vonMangoldt_nonneg (by positivity)) (fun _ => norm_nonneg _)
  have hFsum2 : Summable (Function.uncurry f) := Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  have hj : ∀ j : ℕ, ∑' z, f j z =
      ((Λ (j + 1) * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    intro j
    simp only [hfdef]
    rw [tsum_mul_left, Complex.ofReal_mul, Complex.ofReal_mul, ofReal_normTrace hZ,
      ofReal_add_one_rpow j (-σ), mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun z => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  have hz : ∀ z : ℂ, ∑' j, f j z = e z * (-logDeriv riemannZeta ((σ : ℂ) + (b - z))) := by
    intro z
    by_cases hz0 : e z = 0
    · simp [hfdef, hz0]
    have h1 := h z hz0
    have hres : 1 < ((σ : ℂ) + (b - z)).re := by simp; linarith
    obtain ⟨-, hsum⟩ := summable_tsum_vonMangoldt hres
    rw [← hsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hfdef]; ring
  rw [normTraceMean, Complex.ofReal_tsum, ← tsum_congr hj, hFsum2.tsum_comm.symm, tsum_congr hz]

/-- **The relative mean of `F` vanishes.** The top layer has no real exponent. -/
theorem tendsto_normTraceMean (hZ : TemperedConfig Z) (h : TopDepth Z b)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.im ≠ 0) :
    Tendsto (fun σ => normTraceMean Z b σ / vmSum σ) (𝓝[>] 1) (𝓝 0) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hc : Tendsto (fun σ : ℝ => ∑' z, e z * (-logDeriv riemannZeta ((σ : ℂ) + (b - z))) /
      (vmSum σ : ℂ)) (𝓝[>] 1) (𝓝 (∑' _z : ℂ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hz : e z = 0
      · simp [hz]
      have h1 := h z hz
      have h2 := hreal z hz
      have hne : (b : ℂ) - z ≠ 0 := by
        intro h0; apply h2; have := congrArg Complex.im h0; simp at this; linarith
      have := (tendsto_logDeriv_div_vmSum (c₀ := (b : ℂ) - z) (by simp; linarith) hne).const_mul
        (-e z)
      simpa [mul_div_assoc, neg_div, mul_neg, neg_mul] using this
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro z
      have hσ1 : 1 < σ := hσ
      by_cases hz : e z = 0
      · simp [hz]
      have h1 := h z hz
      have hres : 1 < ((σ : ℂ) + (b - z)).re := by simp; linarith
      have hV : 0 < vmSum σ := vmSum_pos hσ1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, norm_mul, norm_neg,
        div_le_iff₀ hV]
      have hb1 := norm_logDeriv_le_vmSum hres
      have hb2 : vmSum ((σ : ℂ) + (b - z)).re ≤ vmSum σ := vmSum_antitone hσ1 (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (hb1.trans hb2) (norm_nonneg _)
  rw [tsum_zero] at hc
  have hc' := (Complex.continuous_re.tendsto 0).comp hc
  refine (hc'.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hrat : ((normTraceMean Z b σ / vmSum σ : ℝ) : ℂ) =
      ∑' z, e z * (-logDeriv riemannZeta ((σ : ℂ) + (b - z))) / (vmSum σ : ℂ) := by
    rw [Complex.ofReal_div, ofReal_normTraceMean hZ h hσ, tsum_div_const]
  simp only [Function.comp_def]
  rw [← hrat, Complex.ofReal_re]

/-- **The mean of `F²` through the pairs of zeros.** -/
theorem ofReal_normTraceSqMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) :
    ((normTraceSqMean Z b σ : ℝ) : ℂ) = ∑' q : ℂ × ℂ, evenCoeff Z (boxSpline 1 3) q.1 *
      evenCoeff Z (boxSpline 1 3) q.2 * (-logDeriv riemannZeta ((σ : ℂ) + (2 * b - q.1 - q.2))) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hEE : Summable fun q : ℂ × ℂ => ‖e q.1‖ * ‖e q.2‖ :=
    Summable.mul_of_nonneg (f := fun z => ‖e z‖) (g := fun z => ‖e z‖) hE hE
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hFsum : ∀ u : ℝ, 0 ≤ u → Summable fun z => e z * cexp ((z - b) * u) := fun u hu =>
    Summable.of_norm_bounded hE fun z => norm_evenCoeff_mul_cexp_le h z hu
  have hF2 : ∀ u : ℝ, 0 ≤ u → ((normTrace Z b u ^ 2 : ℝ) : ℂ) =
      ∑' q : ℂ × ℂ, e q.1 * e q.2 * cexp ((q.1 + q.2 - 2 * b) * u) := by
    intro u hu
    rw [Complex.ofReal_pow, ofReal_normTrace hZ, sq,
      tsum_mul_tsum_of_summable_norm (hFsum u hu).norm (hFsum u hu).norm]
    refine tsum_congr fun q => ?_
    rw [show e q.1 * cexp ((q.1 - b) * u) * (e q.2 * cexp ((q.2 - b) * u)) =
      e q.1 * e q.2 * (cexp ((q.1 - b) * u) * cexp ((q.2 - b) * u)) by ring, ← Complex.exp_add]
    congr 2; ring
  set f : ℕ → ℂ × ℂ → ℂ := fun j q => (Λ (j + 1) : ℂ) *
    (e q.1 * e q.2 * ((j : ℂ) + 1) ^ (-((σ : ℂ) + (2 * b - q.1 - q.2)))) with hfdef
  have hfn : ∀ j q, ‖f j q‖ ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) * (‖e q.1‖ * ‖e q.2‖) := by
    intro j q
    by_cases hq : e q.1 * e q.2 = 0
    · simp only [hfdef, hq, zero_mul, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity)) (by positivity)
    have h1 := h q.1 (left_ne_zero_of_mul hq)
    have h2 := h q.2 (right_ne_zero_of_mul hq)
    simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg, norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-((σ : ℂ) + (2 * b - q.1 - q.2))).re ≤ ((j : ℝ) + 1) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp; linarith
    have hΛ0 := vonMangoldt_nonneg (n := j + 1)
    calc Λ (j + 1) * (‖e q.1‖ * ‖e q.2‖ * ((j : ℝ) + 1) ^ (-((σ : ℂ) + (2 * b - q.1 - q.2))).re)
        ≤ Λ (j + 1) * (‖e q.1‖ * ‖e q.2‖ * ((j : ℝ) + 1) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) hΛ0
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × (ℂ × ℂ) =>
      Λ (p.1 + 1) * ((p.1 : ℝ) + 1) ^ (-σ) * (‖e p.2.1‖ * ‖e p.2.2‖) :=
    (summable_vonMangoldt_rpow hσ).mul_of_nonneg hEE
      (fun j => mul_nonneg vonMangoldt_nonneg (by positivity)) (fun _ => by positivity)
  have hFsum2 : Summable (Function.uncurry f) :=
    Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  have hj : ∀ j : ℕ, ∑' q, f j q =
      ((Λ (j + 1) * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    intro j
    simp only [hfdef]
    rw [tsum_mul_left, Complex.ofReal_mul, Complex.ofReal_mul, hF2 _ (log_add_one_nonneg j),
      ofReal_add_one_rpow j (-σ), mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc (e q.1 * e q.2),
      ← Complex.exp_add]
    push_cast
    congr 2
    ring
  have hz : ∀ q : ℂ × ℂ, ∑' j, f j q =
      e q.1 * e q.2 * (-logDeriv riemannZeta ((σ : ℂ) + (2 * b - q.1 - q.2))) := by
    intro q
    by_cases hq : e q.1 * e q.2 = 0
    · simp [hfdef, hq]
    have h1 := h q.1 (left_ne_zero_of_mul hq)
    have h2 := h q.2 (right_ne_zero_of_mul hq)
    have hres : 1 < ((σ : ℂ) + (2 * b - q.1 - q.2)).re := by simp; linarith
    obtain ⟨-, hsum⟩ := summable_tsum_vonMangoldt hres
    rw [← hsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hfdef]; ring
  rw [normTraceSqMean, Complex.ofReal_tsum, ← tsum_congr hj, hFsum2.tsum_comm.symm, tsum_congr hz]

/-- **The relative mean of `F²` is the diagonal weight.** -/
theorem tendsto_normTraceSqMean (hZ : TemperedConfig Z) (h : TopDepth Z b) :
    Tendsto (fun σ => normTraceSqMean Z b σ / vmSum σ) (𝓝[>] 1)
      (𝓝 (∑' q, diagWeight Z b q).re) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hEE : Summable fun q : ℂ × ℂ => ‖e q.1‖ * ‖e q.2‖ :=
    Summable.mul_of_nonneg (f := fun z => ‖e z‖) (g := fun z => ‖e z‖) hE hE
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hc : Tendsto (fun σ : ℝ => ∑' q : ℂ × ℂ, e q.1 * e q.2 *
      (-logDeriv riemannZeta ((σ : ℂ) + (2 * b - q.1 - q.2))) / (vmSum σ : ℂ))
      (𝓝[>] 1) (𝓝 (∑' q, diagWeight Z b q)) := by
    refine tendsto_tsum_of_dominated_convergence hEE (fun q => ?_) ?_
    · by_cases hq : e q.1 * e q.2 = 0
      · simp [diagWeight, ← hedef, hq]
      by_cases hq2 : q.1 + q.2 = 2 * (b : ℂ)
      · have hconst : ∀ σ : ℝ, 1 < σ → e q.1 * e q.2 *
            (-logDeriv riemannZeta ((σ : ℂ) + (2 * b - q.1 - q.2))) / (vmSum σ : ℂ) =
              e q.1 * e q.2 := by
          intro σ hσ
          have h0 : (σ : ℂ) + (2 * b - q.1 - q.2) = σ := by rw [← hq2]; ring
          rw [h0, ← ofReal_vmSum hσ, mul_div_assoc,
            div_self (by exact_mod_cast (vmSum_pos hσ).ne'), mul_one]
        simp only [diagWeight, ← hedef, if_pos hq2]
        exact tendsto_const_nhds.congr' (by
          filter_upwards [self_mem_nhdsWithin] with σ hσ
          exact (hconst σ hσ).symm)
      · have h1 := h q.1 (left_ne_zero_of_mul hq)
        have h2 := h q.2 (right_ne_zero_of_mul hq)
        have hne : (2 * (b : ℂ) - q.1 - q.2) ≠ 0 := fun h0 => hq2 (by linear_combination -h0)
        have hre : 0 ≤ (2 * (b : ℂ) - q.1 - q.2).re := by simp; linarith
        have := (tendsto_logDeriv_div_vmSum hre hne).const_mul (-(e q.1 * e q.2))
        simp only [diagWeight, ← hedef, if_neg hq2]
        simpa [mul_div_assoc, neg_div, mul_neg, neg_mul] using this
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro q
      have hσ1 : 1 < σ := hσ
      by_cases hq : e q.1 * e q.2 = 0
      · simp [hq]; positivity
      have h1 := h q.1 (left_ne_zero_of_mul hq)
      have h2 := h q.2 (right_ne_zero_of_mul hq)
      have hres : 1 < ((σ : ℂ) + (2 * b - q.1 - q.2)).re := by simp; linarith
      have hV : 0 < vmSum σ := vmSum_pos hσ1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, norm_mul, norm_mul,
        norm_neg, div_le_iff₀ hV]
      have hb1 := norm_logDeriv_le_vmSum hres
      have hb2 : vmSum ((σ : ℂ) + (2 * b - q.1 - q.2)).re ≤ vmSum σ :=
        vmSum_antitone hσ1 (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (hb1.trans hb2) (by positivity)
  have hc' := (Complex.continuous_re.tendsto _).comp hc
  refine (hc'.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hrat : ((normTraceSqMean Z b σ / vmSum σ : ℝ) : ℂ) = ∑' q : ℂ × ℂ, e q.1 * e q.2 *
      (-logDeriv riemannZeta ((σ : ℂ) + (2 * b - q.1 - q.2))) / (vmSum σ : ℂ) := by
    rw [Complex.ofReal_div, ofReal_normTraceSqMean hZ h hσ, tsum_div_const]
  simp only [Function.comp_def]
  rw [← hrat, Complex.ofReal_re]

/-- **The diagonal weight is `Σ_{Re z = b} |e_z|² > 0`.** -/
theorem re_tsum_diagWeight_pos (hZ : TemperedConfig Z) (h : TopDepth Z b) {z₀ : ℂ}
    (hz₀ : evenCoeff Z (boxSpline 1 3) z₀ ≠ 0) (hz₀re : z₀.re = b) :
    0 < (∑' q, diagWeight Z b q).re := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hEE : Summable fun q : ℂ × ℂ => ‖e q.1‖ * ‖e q.2‖ :=
    Summable.mul_of_nonneg (f := fun z => ‖e z‖) (g := fun z => ‖e z‖) hE hE
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hgreal : ∀ q : ℂ × ℂ, diagWeight Z b q = (((diagWeight Z b q).re : ℝ) : ℂ) ∧
      0 ≤ (diagWeight Z b q).re := by
    intro q
    by_cases hq2 : q.1 + q.2 = 2 * (b : ℂ)
    · simp only [diagWeight, if_pos hq2]
      by_cases hq : e q.1 * e q.2 = 0
      · rw [← hedef, hq]; simp
      have h1 := h q.1 (left_ne_zero_of_mul hq)
      have h2 := h q.2 (right_ne_zero_of_mul hq)
      have hre := congrArg Complex.re hq2
      have him := congrArg Complex.im hq2
      simp at hre him
      have hq2c : q.2 = conj q.1 := Complex.ext (by simp; linarith) (by simp; linarith)
      rw [hq2c, evenCoeff_conj, Complex.mul_conj]
      exact ⟨by simp, by simp [Complex.normSq_nonneg]⟩
    · simp [diagWeight, hq2]
  have hrsum : Summable fun q => (diagWeight Z b q).re := by
    refine Summable.of_nonneg_of_le (fun q => (hgreal q).2) (fun q => ?_) hEE
    refine (Complex.re_le_norm _).trans ?_
    simp only [diagWeight]
    split_ifs
    · rw [norm_mul]
    · simp; positivity
  have htsum : (∑' q, diagWeight Z b q).re = ∑' q, (diagWeight Z b q).re := by
    rw [show (∑' q, diagWeight Z b q) = ∑' q, (((diagWeight Z b q).re : ℝ) : ℂ) from
      tsum_congr fun q => (hgreal q).1, ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [htsum]
  have hq₀ : (z₀, conj z₀).1 + (z₀, conj z₀).2 = 2 * (b : ℂ) := by
    apply Complex.ext <;> simp [hz₀re]; ring
  have hval : (diagWeight Z b (z₀, conj z₀)).re = ‖e z₀‖ ^ 2 := by
    simp only [diagWeight, if_pos hq₀, evenCoeff_conj, ← hedef, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    norm_cast
  have hle := hrsum.le_tsum (z₀, conj z₀) (fun q _ => (hgreal q).2)
  rw [hval] at hle
  have : 0 < ‖e z₀‖ ^ 2 := by
    have := norm_pos_iff.mpr hz₀; positivity
  linarith

/-- **At the prime powers, `F² ≤ E(F + 2|K| n^{−b})`.** Summed with the weights `Λ(n) n^{−σ}`. -/
theorem normTraceSqMean_le (hZ : TemperedConfig Z) (h : TopDepth Z b) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re)
    {σ : ℝ} (hσ : 1 < σ) (hb0 : 0 ≤ b) :
    normTraceSqMean Z b σ ≤ (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * normTraceMean Z b σ +
      2 * (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * |K| * vmSum (σ + b) := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  have hεsum := summable_vonMangoldt_rpow (show 1 < σ + b by linarith)
  have hS₁sum := summable_normTraceMean hZ h hσ
  have hrhs : Summable fun j : ℕ =>
      E * (Λ (j + 1) * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) +
        2 * E * |K| * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(σ + b))) :=
    (hS₁sum.mul_left E).add (hεsum.mul_left _)
  calc normTraceSqMean Z b σ
      ≤ ∑' j : ℕ, (E * (Λ (j + 1) * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) +
          2 * E * |K| * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(σ + b)))) := by
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_normTraceSqMean hZ h hσ) hrhs
        have hΛ := vonMangoldt_nonneg (n := j + 1)
        have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
        have hsplit : ((j : ℝ) + 1) ^ (-(σ + b)) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b) := by
          rw [← Real.rpow_add hj0]; ring_nf
        rw [hsplit]
        by_cases hΛ0 : Λ (j + 1) = 0
        · rw [hΛ0]; simp
        have hpp : IsPrimePow (j + 1) := vonMangoldt_ne_zero_iff.mp hΛ0
        have h1 := hK (j + 1) hpp
        push_cast at h1
        have hexp : Real.exp (-(b * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (-b) := by
          rw [Real.rpow_def_of_pos hj0]; ring_nf
        have hpb : 0 < ((j : ℝ) + 1) ^ (-b) := by positivity
        have hlow : -(|K| * ((j : ℝ) + 1) ^ (-b)) ≤ normTrace Z b (Real.log ((j : ℝ) + 1)) := by
          rw [normTrace, hexp]
          have h3 := mul_le_mul_of_nonneg_right h1 hpb.le
          have h4 : K * ((j : ℝ) + 1) ^ (-b) ≤ |K| * ((j : ℝ) + 1) ^ (-b) :=
            mul_le_mul_of_nonneg_right (le_abs_self K) hpb.le
          linarith
        have hFb := abs_normTrace_le hZ h (log_add_one_nonneg j)
        set f := normTrace Z b (Real.log ((j : ℝ) + 1))
        have habs : |f| ≤ f + 2 * (|K| * ((j : ℝ) + 1) ^ (-b)) := by
          rcases le_total 0 f with h0 | h0
          · rw [abs_of_nonneg h0]; nlinarith [abs_nonneg K]
          · rw [abs_of_nonpos h0]; linarith
        have hsq : f ^ 2 ≤ E * (f + 2 * (|K| * ((j : ℝ) + 1) ^ (-b))) := by
          calc f ^ 2 = |f| * |f| := by rw [← sq_abs, sq]
            _ ≤ E * |f| := mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left habs hE0
        have hw : 0 ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg hΛ hp.le
        have h5 := mul_le_mul_of_nonneg_right hsq hw
        calc Λ (j + 1) * f ^ 2 * ((j : ℝ) + 1) ^ (-σ) =
              f ^ 2 * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := by ring
          _ ≤ E * (f + 2 * (|K| * ((j : ℝ) + 1) ^ (-b))) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := h5
          _ = _ := by ring
    _ = E * normTraceMean Z b σ + 2 * E * |K| * vmSum (σ + b) := by
        rw [(hS₁sum.mul_left E).tsum_add (hεsum.mul_left _), tsum_mul_left, tsum_mul_left]
        rfl

end TopLayer

/-! ### The theorem -/

/-- **The prime powers sample every top layer.** For a tempered configuration without real zeros
whose maximal real part is attained, a lower bound on the spline traces at the prime powers puts
every zero on the critical line. -/
theorem onLine_of_bddBelow_primePowers_of_max (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  have hhalf : 1 / 2 ≤ ρ₀.re := by
    have h := hmax _ (Z.reflect_mem ρ₀ hρ₀)
    have hrefl : (Zeta23.reflect ρ₀).re = 1 - ρ₀.re := by simp [Zeta23.reflect]
    rw [hrefl] at h; linarith
  suffices hb : ρ₀.re = 1 / 2 by
    intro ρ hρ
    have h1 := hmax ρ hρ
    have h2 := hmax _ (Z.reflect_mem ρ hρ)
    have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
    rw [hrefl] at h2; linarith
  by_contra hne
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; exact sub_pos.mpr (lt_of_le_of_ne hhalf (Ne.symm hne))
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h
      simp at h1
      rw [hbdef]; linarith
    · have h1 := hmax _ h
      simp at h1
      rw [hbdef]; linarith
  have hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.im ≠ 0 := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h2 := hnoreal _ h; simp at h2; exact h2
    · have h2 := hnoreal _ h; simp at h2; exact h2
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hpos := re_tsum_diagWeight_pos hZ htop hz₀ (by simp [hbdef])
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  -- the relative means of the bound vanish
  have hlimε : Tendsto (fun σ => vmSum (σ + b) / vmSum σ) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
      ((tendsto_const_nhds (x := vmSum (1 + b))).div_atTop tendsto_vmSum_atTop) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact div_nonneg (vmSum_nonneg _) (vmSum_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < σ := hσ
      exact div_le_div_of_nonneg_right (vmSum_antitone (by linarith) (by linarith))
        (vmSum_nonneg _)
  have hrhs : Tendsto (fun σ => E * (normTraceMean Z b σ / vmSum σ) +
      2 * E * |K| * (vmSum (σ + b) / vmSum σ)) (𝓝[>] 1) (𝓝 0) := by
    simpa using ((tendsto_normTraceMean hZ htop hreal).const_mul E).add (hlimε.const_mul (2 * E * |K|))
  have hle : (∑' q, diagWeight Z b q).re ≤ 0 := by
    refine le_of_tendsto_of_tendsto (tendsto_normTraceSqMean hZ htop) hrhs ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < σ := hσ
    have hV := vmSum_pos hσ1
    have h := normTraceSqMean_le hZ htop hK hσ1 hb0.le
    rw [div_le_iff₀ hV]
    have : (E * (normTraceMean Z b σ / vmSum σ) + 2 * E * |K| * (vmSum (σ + b) / vmSum σ)) *
        vmSum σ = E * normTraceMean Z b σ + 2 * E * |K| * vmSum (σ + b) := by field_simp
    rw [this]; exact h
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
