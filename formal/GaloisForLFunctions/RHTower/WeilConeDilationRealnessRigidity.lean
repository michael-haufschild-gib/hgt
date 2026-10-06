import GaloisForLFunctions.RHTower.WeilFiniteTypeResidues
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.WeilConeOneSidedDeviationRH

/-!
# Dilation rigidity of the Weil cone from realness at simple critical zeros

Let `a : ℕ → ℝ` be supported in `[1, N]`, `A(s) = Σ a(n) n^{−s}`, and let `v` be a regular sequence
(`RegularPart`).  Suppose `lam = Λ ⋆ a + v` is full-cone Weil-positive.

**Theorem** (`eq_delta_of_weilPositiveFull`).  Then `a(1) = 1` and `a(n) = 0` for every `n ≥ 2`.
So `lam = Λ + v` (`finiteTypeSeq_eq_vonMangoldt_add`).  For `v = 0` the system is `Λ` itself and
the Riemann hypothesis follows (`riemannHypothesis_of_weilPositiveFull_dilation`).

**Proof.**
* *Realness.*  At a simple critical zero `ρ = ½ + it` the Herglotz continuation of the Weil
  function has a boundary pole with residue `A(ρ)`, which must be real
  (`residue_real_of_critical_simple`).  So the entire function
  `D(z) = A(½ + iz) − A(½ − iz)` (`reflectionDefect`), which equals `2i · Im A(½ + it)` on the real
  axis, vanishes at every simple critical ordinate.
* *Counting.*  `D` has exponential type `log(N + 1)`.  By Jensen's formula a nonzero such function
  has at most linearly many real zeros up to height `T`, while the unconditional Zeta23 density
  gives at least `T log T/(72π)` simple critical ordinates.  Hence `D ≡ 0`.
* *Coefficients.*  `D ≡ 0` means `A(σ) = A(1 − σ)` for real `σ`, i.e.
  `Σ a(n)(n^{σ−1} − n^{−σ}) = 0`.  After division by `M^{σ−1}`, with `M` the largest `n ≥ 2` with
  `a(n) ≠ 0`, the left side tends to `a(M)` as `σ → ∞`.  So `a(n) = 0` for `n ≥ 2`, and the pole
  condition `A(1) = 1` gives `a(1) = 1`.

No discrete moment of `ζ′` over the zeros is used: the dilation part of a finite-type completion
is excluded by realness at the critical zeros alone, given a superlinear count of simple ones.
-/

noncomputable section

open Complex Filter Topology

namespace RHTower.WeilDilationRealness

open RHTower.WeilFiniteType

/-- The reflection defect `A(½ + iz) − A(½ − iz)` of the Dirichlet polynomial `A`. -/
def reflectionDefect (N : ℕ) (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  dirPoly N a (1 / 2 + z * I) - dirPoly N a (1 / 2 - z * I)

theorem differentiable_reflectionDefect (N : ℕ) (a : ℕ → ℝ) :
    Differentiable ℂ (reflectionDefect N a) := by
  unfold reflectionDefect
  exact ((differentiable_dirPoly N a).comp
      ((differentiable_const _).add (differentiable_id.mul_const I))).sub
    ((differentiable_dirPoly N a).comp
      ((differentiable_const _).sub (differentiable_id.mul_const I)))

theorem norm_dirPoly_le_exp (N : ℕ) (a : ℕ → ℝ) (s : ℂ) :
    ‖dirPoly N a s‖ ≤
      (∑ n ∈ Finset.Icc 1 N, |a n|) * Real.exp (Real.log (N + 1) * |s.re|) := by
  unfold dirPoly
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hnpos : 0 < n := hn1
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnpos, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlogle : Real.log n ≤ Real.log (N + 1) :=
    Real.log_le_log (by linarith) (by exact_mod_cast (by omega : n ≤ N + 1))
  have hre : (-s).re = -s.re := by simp
  rw [hre]
  calc Real.log n * -s.re ≤ Real.log n * |s.re| :=
        mul_le_mul_of_nonneg_left (by linarith [neg_abs_le s.re, le_abs_self s.re]) hlog0
    _ ≤ Real.log (N + 1) * |s.re| := mul_le_mul_of_nonneg_right hlogle (abs_nonneg _)


theorem norm_reflectionDefect_le (N : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    ‖reflectionDefect N a z‖ ≤
      (2 * (∑ n ∈ Finset.Icc 1 N, |a n|) * Real.exp (Real.log (N + 1)) + 1) *
        Real.exp (Real.log (N + 1) * ‖z‖) := by
  set S := ∑ n ∈ Finset.Icc 1 N, |a n| with hS
  set L := Real.log (N + 1) with hL
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hL0 : 0 ≤ L := Real.log_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have hz := abs_le.mp (abs_im_le_norm z)
  have hre : ∀ w : ℂ, w = 1 / 2 + z * I ∨ w = 1 / 2 - z * I → |w.re| ≤ 1 + ‖z‖ := by
    rintro w (rfl | rfl) <;>
    · simp only [add_re, sub_re, mul_re, I_re, I_im, mul_zero, mul_one, zero_sub]
      rw [abs_le]
      norm_num
      constructor <;> linarith
  have hbound : ∀ w : ℂ, w = 1 / 2 + z * I ∨ w = 1 / 2 - z * I →
      ‖dirPoly N a w‖ ≤ S * (Real.exp L * Real.exp (L * ‖z‖)) := by
    intro w hw
    refine (norm_dirPoly_le_exp N a w).trans (mul_le_mul_of_nonneg_left ?_ hS0)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hre w hw]
  unfold reflectionDefect
  refine (norm_sub_le _ _).trans ?_
  have h1 := hbound _ (Or.inl rfl)
  have h2 := hbound _ (Or.inr rfl)
  have hE : 0 ≤ Real.exp (L * ‖z‖) := (Real.exp_pos _).le
  nlinarith

/-- On the real axis the reflection defect is `2i · Im A(½ + it)`. -/
theorem reflectionDefect_ofReal (N : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    reflectionDefect N a t = ((2 * (dirPoly N a (linePt t)).im : ℝ) : ℂ) * I := by
  have hconj : (1 / 2 : ℂ) - (t : ℂ) * I = (starRingEnd ℂ) (linePt t) := by
    apply Complex.ext <;> simp [linePt]
  have hline : (1 / 2 : ℂ) + (t : ℂ) * I = linePt t := by simp [linePt]
  unfold reflectionDefect
  rw [hconj, dirPoly_conj, hline, Complex.sub_conj]


theorem supportedIn_zero (N : ℕ) : SupportedIn N (0 : ℕ → ℝ) := ⟨rfl, fun _ _ => rfl⟩

theorem dirPoly_zero (N : ℕ) (s : ℂ) : dirPoly N (0 : ℕ → ℝ) s = 0 := by
  simp [dirPoly]

/-- A simple zero of `ζ` has nonzero derivative. -/
theorem deriv_riemannZeta_ne_zero_of_order_one {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (horder : analyticOrderAt riemannZeta ρ = 1) : deriv riemannZeta ρ ≠ 0 := by
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    ((analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_natCast (n := 1)).mp (by simpa using horder)
  have hderivEq : deriv riemannZeta ρ = deriv (fun z => (z - ρ) * g z) ρ := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hfactor] with z hz
    simpa [smul_eq_mul] using hz
  have hhas : HasDerivAt (fun z => (z - ρ) * g z) (1 * g ρ + (ρ - ρ) * deriv g ρ) ρ :=
    ((hasDerivAt_id ρ).sub_const ρ).mul hg.differentiableAt.hasDerivAt
  rw [hderivEq, hhas.deriv]
  simpa using hg0

/-- **Realness at simple critical zeros.**  For a full-cone Weil-positive `Λ ⋆ a + v` with regular
`v`, the reflection defect vanishes at every simple critical ordinate. -/
theorem reflectionDefect_eq_zero_of_simpleCritical {N : ℕ} {a v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {t : ℝ} (hxi : xi (linePt t) = 0)
    (hsimple : (analyticOrderAt xi (linePt t)).toNat = 1) :
    reflectionDefect N a t = 0 := by
  have hre : (linePt t).re = 1 / 2 := by simp [linePt]
  have hstrip : 0 < (linePt t).re ∧ (linePt t).re < 1 := by rw [hre]; norm_num
  have hz : riemannZeta (linePt t) = 0 :=
    (xi_zero_iff_zeta_zero_of_mem_strip hstrip.1 hstrip.2).1 hxi
  have horder : analyticOrderAt riemannZeta (linePt t) = 1 := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip]
    cases h : analyticOrderAt xi (linePt t) with
    | top => rw [h] at hsimple; simp at hsimple
    | coe m =>
      rw [h] at hsimple
      simp only [ENat.toNat_coe] at hsimple
      rw [hsimple]; rfl
  have hρ1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hd := deriv_riemannZeta_ne_zero_of_order_one hρ1 horder
  have hres := (residue_real_of_critical_simple ha (supportedIn_zero N) rfl hv hW hre hz hd).1
  rw [dirPoly_zero, zero_div, sub_zero] at hres
  rw [reflectionDefect_ofReal, hres]
  simp

/-- **The reflection defect vanishes identically.**  A nonzero entire function of exponential type
vanishes at only linearly many simple critical ordinates up to height `T`, while Zeta23 supplies
`≫ T log T` of them. -/
theorem reflectionDefect_eq_zero {N : ℕ} {a v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) :
    reflectionDefect N a = 0 := by
  by_contra hne
  have hL0 : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have hC : 1 ≤ 2 * (∑ n ∈ Finset.Icc 1 N, |a n|) * Real.exp (Real.log (N + 1)) + 1 := by
    have : 0 ≤ ∑ n ∈ Finset.Icc 1 N, |a n| := Finset.sum_nonneg fun n _ => abs_nonneg _
    have := Real.exp_pos (Real.log (N + 1))
    nlinarith
  obtain ⟨K, -, hK⟩ := exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros
    (differentiable_reflectionDefect N a) hne hL0 hC (norm_reflectionDefect_le N a) ∅
    (fun t _ _ hxi hsimple => reflectionDefect_eq_zero_of_simpleCritical ha hv hW hxi hsimple)
  exact not_linear_bound_of_superlinear (c := 1 / (72 * Real.pi)) (by positivity)
    eventually_superlinear_xiSimpleCriticalZeroCount (K := K) (m := 0)
    (fun T hT => by simpa using hK T hT)

theorem tendsto_exp_affine_atTop {c d : ℝ} (hc : c < 0) :
    Tendsto (fun σ : ℝ => Real.exp (c * σ + d)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot_add_const_right
  exact tendsto_id.const_mul_atTop_of_neg hc

/-- Real reflection identity for a finite Dirichlet polynomial forces the coefficients beyond the
constant term to vanish. -/
theorem coeff_eq_zero_of_reflection {N : ℕ} {a : ℕ → ℝ}
    (h : ∀ σ : ℝ, ∑ n ∈ Finset.Icc 1 N, a n * ((n : ℝ) ^ (σ - 1) - (n : ℝ) ^ (-σ)) = 0) :
    ∀ n ∈ Finset.Icc 2 N, a n = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set P := (Finset.Icc 2 N).filter (fun n => a n ≠ 0) with hP
  have hPne : P.Nonempty := by
    obtain ⟨n, hn, han⟩ := hcon
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, han⟩⟩
  set M := P.max' hPne with hM
  have hMP : M ∈ P := P.max'_mem hPne
  obtain ⟨hMI, haM⟩ := Finset.mem_filter.mp hMP
  have hM2 : 2 ≤ M := (Finset.mem_Icc.mp hMI).1
  have hMN : M ≤ N := (Finset.mem_Icc.mp hMI).2
  have hbig : ∀ n ∈ Finset.Icc 1 N, M < n → a n = 0 := by
    intro n hn hMn
    by_contra han
    have hn2 : n ∈ P := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hn).2⟩, han⟩
    exact absurd (P.le_max' n hn2) (by omega)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set lM := Real.log M with hlM
  have hlMpos : 0 < lM := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  -- the rescaled identity
  let term : ℕ → ℝ → ℝ := fun n σ =>
    a n * (Real.exp ((Real.log n - lM) * σ + (lM - Real.log n)) -
      Real.exp (-(Real.log n + lM) * σ + lM))
  have hterm : ∀ σ : ℝ, ∑ n ∈ Finset.Icc 1 N, term n σ = 0 := by
    intro σ
    have hscale : ∀ n ∈ Finset.Icc 1 N, term n σ =
        (M : ℝ) ^ (1 - σ) * (a n * ((n : ℝ) ^ (σ - 1) - (n : ℝ) ^ (-σ))) := by
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      simp only [term]
      rw [Real.rpow_def_of_pos hMpos, Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos]
      have e1 : (Real.log n - lM) * σ + (lM - Real.log n) =
          lM * (1 - σ) + Real.log n * (σ - 1) := by ring
      have e2 : -(Real.log n + lM) * σ + lM = lM * (1 - σ) + Real.log n * -σ := by ring
      rw [e1, e2, Real.exp_add, Real.exp_add]
      ring
    rw [Finset.sum_congr rfl hscale, ← Finset.mul_sum, h σ, mul_zero]
  have hlim : Tendsto (fun σ => ∑ n ∈ Finset.Icc 1 N, term n σ) atTop
      (𝓝 (∑ n ∈ Finset.Icc 1 N, if n = M then a M else 0)) := by
    refine tendsto_finsetSum _ fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsecond : Tendsto (fun σ : ℝ => Real.exp (-(Real.log n + lM) * σ + lM)) atTop (𝓝 0) :=
      tendsto_exp_affine_atTop (by
        have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn1); linarith)
    rcases lt_trichotomy n M with hlt | heq | hgt
    · have hfirst : Tendsto (fun σ : ℝ => Real.exp ((Real.log n - lM) * σ + (lM - Real.log n)))
          atTop (𝓝 0) :=
        tendsto_exp_affine_atTop (by
          have := Real.log_lt_log hnpos (show (n : ℝ) < M by exact_mod_cast hlt); linarith)
      rw [if_neg hlt.ne]
      have h := (hfirst.sub hsecond).const_mul (a n)
      rw [sub_zero, mul_zero] at h
      exact h.congr fun σ => rfl
    · rw [if_pos heq]
      have hfirst : ∀ σ : ℝ, Real.exp ((Real.log n - lM) * σ + (lM - Real.log n)) = 1 := by
        intro σ; rw [heq, hlM]; simp
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hsecond |>.const_mul (a n)
      rw [sub_zero, mul_one, heq] at h
      exact h.congr fun σ => by simp only [term]; rw [hfirst σ, heq]
    · have h0 : term n = fun _ => 0 := by funext σ; simp [term, hbig n hn hgt]
      rw [if_neg hgt.ne', h0]
      exact tendsto_const_nhds
  have hsum : (∑ n ∈ Finset.Icc 1 N, if n = M then a M else 0) = a M := by
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_Icc.mpr ⟨by omega, hMN⟩)]
  rw [hsum] at hlim
  have hzero : Tendsto (fun σ => ∑ n ∈ Finset.Icc 1 N, term n σ) atTop (𝓝 0) := by
    simp only [hterm]; exact tendsto_const_nhds
  exact haM (tendsto_nhds_unique hlim hzero)

theorem dirPoly_ofReal (N : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    dirPoly N a (x : ℂ) = ((∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-x) : ℝ) : ℂ) := by
  unfold dirPoly
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Complex.ofReal_cpow hn0]
  push_cast
  rfl

/-- **Dilation rigidity of the Weil cone.**  If `Λ ⋆ a + v` is full-cone Weil-positive, with `a`
finitely supported and `v` regular, then `a = δ₁`. -/
theorem eq_delta_of_weilPositiveFull {N : ℕ} {a v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) :
    a 1 = 1 ∧ ∀ n, 2 ≤ n → a n = 0 := by
  have hdef := reflectionDefect_eq_zero ha hv hW
  have hrefl : ∀ σ : ℝ,
      ∑ n ∈ Finset.Icc 1 N, a n * ((n : ℝ) ^ (σ - 1) - (n : ℝ) ^ (-σ)) = 0 := by
    intro σ
    have h0 := congrFun hdef (((1 / 2 - σ : ℝ) : ℂ) * I)
    have e1 : (1 / 2 : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I * I = (σ : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    have e2 : (1 / 2 : ℂ) - ((1 / 2 - σ : ℝ) : ℂ) * I * I = ((1 - σ : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    simp only [reflectionDefect, e1, e2, Pi.zero_apply, dirPoly_ofReal, sub_eq_zero] at h0
    have h1 := Complex.ofReal_injective h0
    have e3 : ∀ n : ℕ, (n : ℝ) ^ (-(1 - σ)) = (n : ℝ) ^ (σ - 1) := fun n => by
      congr 1; ring
    simp only [e3] at h1
    simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self]
  have hcoef := coeff_eq_zero_of_reflection hrefl
  have hge2 : ∀ n, 2 ≤ n → a n = 0 := by
    intro n hn
    by_cases hnN : n ≤ N
    · exact hcoef n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
    · exact ha.2 n (by omega)
  refine ⟨?_, hge2⟩
  have hone := dirPoly_one_eq_one ha (supportedIn_zero N) rfl hv hW
  have hsingle : dirPoly N a 1 = (a 1 : ℂ) := by
    unfold dirPoly
    rw [Finset.sum_eq_single 1]
    · simp
    · intro n hn hn1
      rw [hge2 n (by have := (Finset.mem_Icc.mp hn).1; omega)]
      simp
    · intro h1
      rw [ha.2 1 (by simp at h1; omega)]
      simp
  rw [hsingle] at hone
  exact_mod_cast hone

/-- With `a = δ₁` the finite-type system is `Λ + v`. -/
theorem finiteTypeSeq_eq_vonMangoldt_add {a v : ℕ → ℝ} (h1 : a 1 = 1)
    (h2 : ∀ n, 2 ≤ n → a n = 0) (n : ℕ) :
    finiteTypeSeq a 0 v n = (ArithmeticFunction.vonMangoldt n : ℝ) + v n := by
  unfold finiteTypeSeq
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [Nat.sum_divisorsAntidiagonal (f := fun x y =>
      (ArithmeticFunction.vonMangoldt x : ℝ) * a y +
        (ArithmeticFunction.moebius x : ℝ) * (0 : ℕ → ℝ) y)]
  rw [Finset.sum_eq_single n]
  · rw [Nat.div_self hn, h1]; simp
  · intro d hd hdn
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hq : 2 ≤ n / d := by
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hle : d ≤ n := Nat.le_of_dvd hn hdvd
      have hlt : d < n := lt_of_le_of_ne hle hdn
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, Nat.mul_div_cancel_left _ hd0]
      by_contra hk2
      interval_cases k <;> simp_all
    rw [h2 _ hq]; simp
  · intro hn'; exact absurd (Nat.mem_divisors_self n hn.ne') hn'

/-- The zero sequence is a regular part. -/
theorem regularPart_zero : RegularPart (0 : ℕ → ℝ) (0 : ℂ → ℂ) where
  zero := rfl
  one := rfl
  summable := fun s _ => by
    have h : (fun n => (((0 : ℕ → ℝ) n : ℝ) : ℂ)) = 0 := by funext n; simp
    rw [h]; exact LSeriesSummable_zero
  series := fun s _ => by
    have h : (fun n => (((0 : ℕ → ℝ) n : ℝ) : ℂ)) = 0 := by funext n; simp
    rw [h, LSeries_zero]
  holo := ⟨1, one_pos, differentiableOn_const 0⟩
  growth := fun _ => ⟨0, 0, fun s _ _ => by simp⟩

/-- **A Weil-positive dilation system of `Λ` forces RH.**  If `Λ ⋆ a` is full-cone Weil-positive
for a finitely supported `a`, then `a = δ₁`, so `Λ` itself is Weil-positive and RH holds. -/
theorem riemannHypothesis_of_weilPositiveFull_dilation {N : ℕ} {a : ℕ → ℝ}
    (ha : SupportedIn N a) (hW : WeilPositiveFull (finiteTypeSeq a 0 0)) :
    RiemannHypothesis := by
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull ha regularPart_zero hW
  have hlam : finiteTypeSeq a 0 0 = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
    funext n; rw [finiteTypeSeq_eq_vonMangoldt_add h1 h2]; simp
  rw [hlam] at hW
  refine RHTower.WeilSpectral.riemannHypothesis_of_weilPositiveFull_of_summable_deviationPos hW
    fun σ _ => ?_
  simp [RHTower.WeilSpectral.deviationPos]

end RHTower.WeilDilationRealness
