import GaloisForLFunctions.RHTower.WeilAtomicBoundaryMeasure
import GaloisForLFunctions.RHTower.CompletionLogDerivZeroPairs
import GaloisForLFunctions.RHTower.CompletionOrderOneEnvelope

/-!
# Fake `ζᵏ` with the Riemann hypothesis give Weil producers

A **degree-`k` datum** (`ZetaPowerDatum k g E`) is a Dirichlet series `G(s) = Σ g(n) n^{−s}`,
absolutely convergent on `Re s > 1`, whose completion `E(s) = (s(s − 1)Γ_ℝ(s))^k G(s)` extends to
an entire function of finite order with `E(1 − s) = ±E(s)`: the functional equation of `ζᵏ`
(archimedean factor `Γ_ℝ(s)^k`, conductor `1`, the pole of `G` at `s = 1` of order at most `k`).

**Theorem** (`weilPositiveFull_of_zetaPowerDatum`).  If every zero of `E` lies on `Re s = ½` and
`lam` is real with `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1` and `−G'/G = k Σ_{n≥2} lam(n) n^{−s}` on
`Re s > 1`, i.e. `lam = (1/k)Λ_G`, then `lam` is full-cone Weil-positive.

**Proof.**
* Finite order upgrades to the order-one envelope (`CompletionGrowth.orderOneEnvelope_of_finiteOrder`).
* On `Re s > 1`, `k Φ_lam = E'/E`, and Hadamard's factorization writes `E'/E` as
  `½ Σ_ρ (1/(s − ρ) + 1/(s − (1 − ρ)))` over the zeros with multiplicity
  (`CompletionZeroPairs.hasSum_logDeriv_zeroPairs`).
* With every `ρ = ½ + iγ`, `Φ_lam` is a positive atomic Herglotz series, and the explicit formula
  gives `W_lam(f ⋆ f̃) = (1/2k) Σ_ρ (|f̂(γ)|² + |f̂(−γ)|²) ≥ 0` (`WeilAtomic.weilPositiveFull_of_atomic`).

The Weil measure of `lam` is then `(1/k) Σ_ρ δ_{γ_ρ}` over the zeros with multiplicity
(`boundaryMeasure_eq_zeroMeasure`; the zeros are symmetric under `ρ ↦ 1 − ρ`), so
`k μ_lam((a, b])` is the number of zeros with ordinate in `(a, b]` (`exists_natCast_eq_mul_boundaryMeasure`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section

namespace RHTower.WeilZetaPower

open WeilLineIntegral CompletionZeroPairs CompletionGrowth

/-- **A degree-`k` datum with the functional equation of `ζᵏ`.** -/
structure ZetaPowerDatum (k : ℕ) (g : ℕ → ℂ) (E : ℂ → ℂ) : Prop where
  summable : ∀ s : ℂ, 1 < s.re → LSeriesSummable g s
  entire : Differentiable ℂ E
  completion : ∀ s : ℂ, 1 < s.re → E s = (s * (s - 1) * Complex.Gammaℝ s) ^ k * LSeries g s
  functional_equation : (∀ s, E (1 - s) = E s) ∨ ∀ s, E (1 - s) = -E s
  finite_order : ∃ ρ C : ℝ, ∀ s, ‖E s‖ ≤ C * Real.exp (‖s‖ ^ ρ)

variable {k : ℕ} {g : ℕ → ℂ} {E : ℂ → ℂ}

theorem ZetaPowerDatum.exists_sign (hD : ZetaPowerDatum k g E) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ s, E (1 - s) = ε * E s := by
  rcases hD.functional_equation with h | h
  · exact ⟨1, by simp, fun s => by rw [h, one_mul]⟩
  · exact ⟨-1, by simp, fun s => by rw [h, neg_one_mul]⟩

theorem ZetaPowerDatum.orderOne (hD : ZetaPowerDatum k g E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨ε, hε, hsym⟩ := hD.exists_sign
  exact orderOneEnvelope_of_finiteOrder hD.entire hD.finite_order hε hsym
    (hD.summable 2 (by norm_num)) fun s hs => hD.completion s (by linarith)

theorem ZetaPowerDatum.abscissa_lt (hD : ZetaPowerDatum k g E) {s : ℂ} (hs : 1 < s.re) :
    LSeries.abscissaOfAbsConv g < s.re :=
  lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    fun y hy => hD.summable y (by simpa using hy)) (by exact_mod_cast hs)

/-- `E'/E = k Φ_lam` on `Re s > 1`. -/
theorem logDeriv_eq_mul_weilFunction (hD : ZetaPowerDatum k g E) {lam : ℕ → ℝ}
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s)
    {s : ℂ} (hs : 1 < s.re) (hEs : E s ≠ 0) :
    logDeriv E s = k * WeilHerglotz.weilFunction lam s := by
  set h : ℂ → ℂ := fun z => z * (z - 1) * Complex.Gammaℝ z with hh
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : E =ᶠ[𝓝 s] fun z => h z ^ k * LSeries g z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hD.completion z hz
  have hs0 : 0 < s.re := by linarith
  have hsne0 : s ≠ 0 := fun h0 => by rw [h0] at hs; norm_num at hs
  have hsne1 : s - 1 ≠ 0 := fun h0 => by
    rw [sub_eq_zero] at h0; rw [h0] at hs; norm_num at hs
  have hG0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have hGd : DifferentiableAt ℂ Complex.Gammaℝ s := Zeta23.WeilEF.differentiableAt_Gammaℝ hs0
  have hhd : DifferentiableAt ℂ h s := by
    simp only [hh]
    exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hGd)
  have hh0 : h s ≠ 0 := mul_ne_zero (mul_ne_zero hsne0 hsne1) hG0
  have hLd : DifferentiableAt ℂ (LSeries g) s := (LSeries_hasDerivAt (hD.abscissa_lt hs)).differentiableAt
  have hEeq : E s = h s ^ k * LSeries g s := hD.completion s hs
  have hL0 : LSeries g s ≠ 0 := by
    intro h0; apply hEs; rw [hEeq, h0, mul_zero]
  have hlogE : logDeriv E s = logDeriv (fun z => h z ^ k * LSeries g z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlogE, logDeriv_mul (f := fun z => h z ^ k) (g := LSeries g) s (pow_ne_zero k hh0) hL0
    (hhd.pow k) hLd, logDeriv_fun_pow hhd k]
  have hlogh : logDeriv h s = gPair 0 s + logDeriv Complex.Gammaℝ s := by
    have hpd : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s :=
      differentiableAt_id.mul (differentiableAt_id.sub_const 1)
    rw [show h = fun z => (fun z : ℂ => z * (z - 1)) z * Complex.Gammaℝ z from rfl,
      logDeriv_mul (f := fun z : ℂ => z * (z - 1)) (g := Complex.Gammaℝ) s
        (mul_ne_zero hsne0 hsne1) hG0 hpd hGd]
    congr 1
    rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hsne0 hsne1
      differentiableAt_id (differentiableAt_id.sub_const 1)]
    rw [logDeriv_apply, logDeriv_apply, deriv_id'', deriv_sub_const, deriv_id'']
    simp [gPair]
  have hlogL : logDeriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s := by
    rw [logDeriv_apply, hΛ s hs]
    field_simp
  rw [hlogh, hlogL, weilFunction_eq lam hs0]
  ring

/-- **The Weil function of `(1/k)Λ_G` is the atomic series over the zeros of `E`.** -/
theorem hasSum_weilFunction_zeros (hk : 0 < k) (hD : ZetaPowerDatum k g E)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun q : ZeroCopy (fun z => E (z + 2)) =>
        ((1 / (2 * k) : ℝ) : ℂ) *
          gPair (1 / 2 + ((zeroCopyPoint (fun z => E (z + 2)) q + 2).im : ℂ) * I) s)
      (WeilHerglotz.weilFunction lam s) := by
  obtain ⟨ε, hε, hsym⟩ := hD.exists_sign
  have hε0 : ε ≠ 0 := by rw [← norm_ne_zero_iff, hε]; exact one_ne_zero
  obtain ⟨C, hC0, hC⟩ := hD.orderOne
  have hE2 : E 2 ≠ 0 := fun h0 => by have := hRH 2 h0; norm_num at this
  have hEs : E s ≠ 0 := fun h0 => by have := hRH s h0; linarith
  have hsum := (hasSum_logDeriv_zeroPairs hD.entire hε0 hsym hC0 hC hE2 hEs).mul_left
    ((1 / k : ℝ) : ℂ)
  rw [logDeriv_eq_mul_weilFunction hD hΛ hs hEs] at hsum
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlhs : ((1 / k : ℝ) : ℂ) * (k * WeilHerglotz.weilFunction lam s) =
      WeilHerglotz.weilFunction lam s := by
    push_cast; field_simp
  rw [hlhs] at hsum
  have hfd : AnalyticOnNhd ℂ (fun z => E (z + 2)) univ :=
    (hD.entire.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  refine hsum.congr_fun fun q => ?_
  have hz : E (zeroCopyPoint (fun z => E (z + 2)) q + 2) = 0 := apply_zeroCopyPoint hfd q
  have hre := hRH _ hz
  have hρ : zeroCopyPoint (fun z => E (z + 2)) q + 2 =
      1 / 2 + ((zeroCopyPoint (fun z => E (z + 2)) q + 2).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [← hρ]
  push_cast
  field_simp

/-- **Converse: fake `ζᵏ` with the Riemann hypothesis give full-cone Weil producers.**  If `E` is
the completion of a degree-`k` datum, every zero of `E` lies on `Re s = ½`, and `lam = (1/k)Λ_G`,
then `lam` is full-cone Weil-positive. -/
theorem weilPositiveFull_of_zetaPowerDatum (hk : 0 < k) (hD : ZetaPowerDatum k g E)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s) :
    WeilPositiveFull lam := by
  have hfd : AnalyticOnNhd ℂ (fun z => E (z + 2)) univ :=
    (hD.entire.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  haveI := countable_zeroCopy hfd
  exact WeilAtomic.weilPositiveFull_of_atomic hsl (c := fun _ => 1 / (2 * k))
    (fun _ => by positivity) fun s hs => hasSum_weilFunction_zeros hk hD hRH hΛ hs

/-- **The Weil measure of `(1/k)Λ_G` is `(1/k) Σ_ρ δ_{γ_ρ}`** over the zeros `ρ = ½ + iγ_ρ` of `E`,
with multiplicity. -/
theorem boundaryMeasure_eq_zeroMeasure (hk : 0 < k) (hD : ZetaPowerDatum k g E)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s) :
    WeilSpectral.boundaryMeasure (weilPositiveFull_of_zetaPowerDatum hk hD hRH hsl hΛ) =
      Measure.sum fun q : ZeroCopy (fun z => E (z + 2)) =>
        ENNReal.ofReal (1 / k) • Measure.dirac (zeroCopyPoint (fun z => E (z + 2)) q + 2).im := by
  have hfd : AnalyticOnNhd ℂ (fun z => E (z + 2)) univ :=
    (hD.entire.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  haveI := countable_zeroCopy hfd
  set τ : ZeroCopy (fun z => E (z + 2)) → ℝ :=
    fun q => (zeroCopyPoint (fun z => E (z + 2)) q + 2).im with hτ
  rw [WeilAtomic.boundaryMeasure_eq_atomicMeasure _ (c := fun _ => 1 / (2 * k)) (τ := τ)
    (fun _ => by positivity) fun s hs => hasSum_weilFunction_zeros hk hD hRH hΛ hs]
  obtain ⟨ε, hε, hsym⟩ := hD.exists_sign
  have hε0 : ε ≠ 0 := by rw [← norm_ne_zero_iff, hε]; exact one_ne_zero
  obtain ⟨σ, hσ⟩ := exists_reflect_zeroCopy hD.entire hε0 hsym
  have hτσ : ∀ q, τ (σ q) = -τ q := fun q => by
    simp only [hτ]
    rw [hσ q]
    simp
  ext A hA
  rw [WeilAtomic.atomicMeasure, Measure.sum_apply _ hA, Measure.sum_apply _ hA]
  simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_add]
  have hrefl : ∑' q, A.indicator (1 : ℝ → ℝ≥0∞) (-τ q) = ∑' q, A.indicator 1 (τ q) := by
    rw [← σ.tsum_eq (fun q => A.indicator (1 : ℝ → ℝ≥0∞) (τ q))]
    simp only [hτσ]
  rw [hrefl, ← two_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- **`k μ_lam((a, b])` counts the zeros with ordinate in `(a, b]`**; in particular the masses of
`μ_lam` lie in `(1/k)ℤ_{>0}`. -/
theorem exists_natCast_eq_mul_boundaryMeasure (hk : 0 < k) (hD : ZetaPowerDatum k g E)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s)
    (a b : ℝ) : ∃ n : ℕ, (k : ℝ≥0∞) * WeilSpectral.boundaryMeasure
      (weilPositiveFull_of_zetaPowerDatum hk hD hRH hsl hΛ) (Ioc a b) = n := by
  have hfd : AnalyticOnNhd ℂ (fun z => E (z + 2)) univ :=
    (hD.entire.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  set τ : ZeroCopy (fun z => E (z + 2)) → ℝ :=
    fun q => (zeroCopyPoint (fun z => E (z + 2)) q + 2).im with hτ
  set S : Set (ZeroCopy (fun z => E (z + 2))) := {q | τ q ∈ Ioc a b} with hS
  have hSfin : S.Finite := by
    refine (locallyFinite_zeroCopyPoint hfd (3 + |a| + |b|)).subset fun q hq => ?_
    simp only [hS, mem_setOf_eq, mem_Ioc] at hq
    have hz : E (zeroCopyPoint (fun z => E (z + 2)) q + 2) = 0 := apply_zeroCopyPoint hfd q
    have hre := hRH _ hz
    have hre' : (zeroCopyPoint (fun z => E (z + 2)) q).re = -3 / 2 := by
      rw [Complex.add_re] at hre
      norm_num at hre
      linarith
    have hρ : zeroCopyPoint (fun z => E (z + 2)) q = ((-3 / 2 : ℝ) : ℂ) + (τ q : ℂ) * I := by
      apply Complex.ext
      · simp [hre']
      · simp [hτ]
    show ‖zeroCopyPoint (fun z => E (z + 2)) q‖ ≤ 3 + |a| + |b|
    rw [hρ]
    have hτb : |τ q| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    calc ‖((-3 / 2 : ℝ) : ℂ) + (τ q : ℂ) * I‖ ≤ ‖((-3 / 2 : ℝ) : ℂ)‖ + ‖(τ q : ℂ) * I‖ :=
          norm_add_le _ _
      _ = 3 / 2 + |τ q| := by simp
      _ ≤ 3 + |a| + |b| := by linarith
  refine ⟨hSfin.toFinset.card, ?_⟩
  rw [boundaryMeasure_eq_zeroMeasure hk hD hRH hsl hΛ, Measure.sum_apply _ measurableSet_Ioc]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc, smul_eq_mul]
  rw [ENNReal.tsum_mul_left]
  have hcount : ∑' q, (Ioc a b).indicator (1 : ℝ → ℝ≥0∞) (τ q) = hSfin.toFinset.card := by
    rw [tsum_eq_sum (s := hSfin.toFinset) fun q hq => by
      rw [Set.Finite.mem_toFinset] at hq
      exact Set.indicator_of_notMem (show τ q ∉ Ioc a b from hq) _]
    have hone : ∀ q ∈ hSfin.toFinset, (Ioc a b).indicator (1 : ℝ → ℝ≥0∞) (τ q) = 1 := by
      intro q hq
      rw [Set.Finite.mem_toFinset] at hq
      exact Set.indicator_of_mem (show τ q ∈ Ioc a b from hq) (1 : ℝ → ℝ≥0∞)
    rw [Finset.sum_congr rfl hone]
    simp
  rw [hcount, ← mul_assoc]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hk), ENNReal.ofReal_one, ENNReal.ofReal_natCast,
    ENNReal.mul_div_cancel hk0 (ENNReal.natCast_ne_top k), one_mul]

end RHTower.WeilZetaPower
