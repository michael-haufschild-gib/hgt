import GaloisForLFunctions.RHTower.WeilFullConeDeviationResidue
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Finite-type Weil systems: the continued Weil function

Let `a, f : ℕ → ℝ` be supported in `[1, N]`, and let `v` be a *regular* sequence: `v(0) = v(1) = 0`,
`Σ |v(n)| n^{−σ} < ∞` for `σ > 1`, and the Dirichlet series of `v` continues to a function `E`
holomorphic on `Re s > ½ − η₀` with polynomial growth on vertical strips (`RegularPart`).  Put

`lam = Λ ⋆ a + μ ⋆ f + v`,  `A(s) = Σ a(n) n^{−s}`,  `F(s) = Σ f(n) n^{−s}`.

On `Re s > 1`, `Σ lam(n) n^{−s} = −A ζ'/ζ + F/ζ + E` (`LSeries_finiteTypeSeq`).

**Master identity** (`master_identity`).  If `f(1) = 0` and `lam` is full-cone Weil-positive, the
continuation `Φ` of the Weil function satisfies, with `Z₁(s) = (s − 1)ζ(s)` and
`G(s) = ½ψ(s/2) − ½ log π + 1/s`, for every `Re s > ½`:

`Z₁ · ((s − 1)(Φ − G + E) − 1) = A · ((s − 1) Z₁' − Z₁) − (s − 1)² F`.

Both sides are holomorphic on the convex set `Re s > ½` and agree on `Re s > 1`.  Off `s = 1` this is
`ζ · (Φ − G − 1/(s − 1) + E) = A ζ' − F` (`zeta_mul_eq`).  At `s = 1` it gives `A(1) = 1`
(`dirPoly_one_eq_one`).
-/

open Complex Filter Topology Set
open scoped LSeries.notation
open RHTower.WeilSpectral RHTower.WeilHerglotz

namespace RHTower.WeilFiniteType

noncomputable section

/-! ## Dirichlet polynomials -/

/-- `A(s) = Σ_{1 ≤ n ≤ N} a(n) n^{−s}`. -/
def dirPoly (N : ℕ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * (n : ℂ) ^ (-s)

theorem differentiable_dirPoly (N : ℕ) (a : ℕ → ℝ) : Differentiable ℂ (dirPoly N a) := by
  intro s
  unfold dirPoly
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hn0))

/-- `a` is supported in `[1, N]`. -/
def SupportedIn (N : ℕ) (a : ℕ → ℝ) : Prop := a 0 = 0 ∧ ∀ n, N < n → a n = 0

theorem LSeries_eq_dirPoly {N : ℕ} {a : ℕ → ℝ} (ha : SupportedIn N a) (s : ℂ) :
    LSeries (fun n => (a n : ℂ)) s = dirPoly N a s := by
  rw [LSeries, tsum_eq_sum (s := Finset.Icc 1 N)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [LSeries.term_of_ne_zero hn0, cpow_neg, div_eq_mul_inv]
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [LSeries.term]
    · have hN : N < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨hpos, not_lt.mp h⟩)
      simp [LSeries.term, ha.2 n hN]

theorem LSeriesSummable_of_supportedIn {N : ℕ} {a : ℕ → ℝ} (ha : SupportedIn N a) (s : ℂ) :
    LSeriesSummable (fun n => (a n : ℂ)) s := by
  refine summable_of_ne_finset_zero (s := Finset.Icc 1 N) fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [LSeries.term]
  · have hN : N < n := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨hpos, not_lt.mp h⟩)
    simp [LSeries.term, ha.2 n hN]

/-! ## The finite-type sequence -/

/-- `lam = Λ ⋆ a + μ ⋆ f + v`. -/
def finiteTypeSeq (a f v : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.vonMangoldt p.1 * a p.2 +
    (ArithmeticFunction.moebius p.1 : ℝ) * f p.2)) + v n

/-- **Regular part**: the Dirichlet series of `v` continues holomorphically across the critical line
with polynomial growth on vertical strips. -/
structure RegularPart (v : ℕ → ℝ) (E : ℂ → ℂ) : Prop where
  zero : v 0 = 0
  one : v 1 = 0
  summable : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (v n : ℂ)) s
  series : ∀ s : ℂ, 1 < s.re → E s = LSeries (fun n => (v n : ℂ)) s
  holo : ∃ η₀ : ℝ, 0 < η₀ ∧ DifferentiableOn ℂ E {s : ℂ | 1 / 2 - η₀ < s.re}
  growth : ∀ σ₁ : ℝ, ∃ C : ℝ, ∃ k : ℕ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ σ₁ →
    ‖E s‖ ≤ C * (1 + |s.im|) ^ k

theorem finiteTypeSeq_zero (a f : ℕ → ℝ) {v : ℕ → ℝ} (hv0 : v 0 = 0) :
    finiteTypeSeq a f v 0 = 0 := by
  simp [finiteTypeSeq, hv0]

theorem finiteTypeSeq_one (a : ℕ → ℝ) {f v : ℕ → ℝ} (hf1 : f 1 = 0) (hv1 : v 1 = 0) :
    finiteTypeSeq a f v 1 = 0 := by
  simp [finiteTypeSeq, hf1, hv1]

theorem lamC_finiteTypeSeq (a : ℕ → ℝ) {f v : ℕ → ℝ} (hf1 : f 1 = 0) (hv0 : v 0 = 0)
    (hv1 : v 1 = 0) : lamC (finiteTypeSeq a f v) = fun n => (finiteTypeSeq a f v n : ℂ) := by
  funext n
  unfold lamC
  split_ifs with h
  · rfl
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · simp [finiteTypeSeq_zero a f hv0]
    · simp [finiteTypeSeq_one a hf1 hv1]

theorem finiteTypeSeq_cast (a f v : ℕ → ℝ) :
    (fun n => (finiteTypeSeq a f v n : ℂ)) =
      ((fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ⍟ fun n => (a n : ℂ)) +
        ((fun n => (ArithmeticFunction.moebius n : ℂ)) ⍟ fun n => (f n : ℂ)) +
          fun n => (v n : ℂ) := by
  funext n
  simp only [Pi.add_apply, LSeries.convolution_def, finiteTypeSeq, ← Finset.sum_add_distrib]
  push_cast
  rfl

/-- **The Dirichlet series of a finite-type system**: `Σ lam(n) n^{−s} = −Aζ'/ζ + F/ζ + E`. -/
theorem LSeries_finiteTypeSeq {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hv : RegularPart v E) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (finiteTypeSeq a f v n : ℂ)) s =
      -(dirPoly N a s * deriv riemannZeta s / riemannZeta s) + dirPoly N f s / riemannZeta s +
        E s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hμ := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hA := LSeriesSummable_of_supportedIn ha s
  have hF := LSeriesSummable_of_supportedIn hf s
  rw [finiteTypeSeq_cast, LSeries_add ((hΛ.convolution hA).add (hμ.convolution hF))
    (hv.summable s hs), LSeries_add (hΛ.convolution hA) (hμ.convolution hF),
    LSeries_convolution' hΛ hA, LSeries_convolution' hμ hF,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_eq_dirPoly ha, LSeries_eq_dirPoly hf, ← hv.series s hs]
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hμζ : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 / riemannZeta s := by
    have h := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at h
    field_simp
    linear_combination h
  rw [hμζ]
  field_simp

/-! ## The master identity -/

/-- `G(s) = ½ψ(s/2) − ½ log π + 1/s` is holomorphic on `Re s > 0`. -/
theorem differentiableAt_zetaArchimedeanDatum {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaArchimedeanDatum s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hψ : DifferentiableAt ℂ (fun z : ℂ => Complex.digamma (z / 2)) s :=
    (differentiableAt_digamma_of_re_pos (by simpa using half_pos hs)).comp s
      ((differentiableAt_id.div_const 2))
  unfold zetaArchimedeanDatum
  exact ((hψ.div_const 2).sub (differentiableAt_const _)).add
    ((differentiableAt_const _).div differentiableAt_id hs0)

theorem deriv_zetaResidueUnit_eq {s : ℂ} (hs : s ≠ 1) :
    deriv zetaResidueUnit s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  rw [(zetaResidueUnit_eventuallyEq hs).deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv, one_mul]

/-- `(s − 1)² ζ'(s) = (s − 1) Z₁'(s) − Z₁(s)` for `s ≠ 1`. -/
theorem sq_mul_deriv_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    (s - 1) ^ 2 * deriv riemannZeta s =
      (s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s := by
  rw [deriv_zetaResidueUnit_eq hs, (zetaResidueUnit_eventuallyEq hs).eq_of_nhds]
  ring

/-- The left side of the master identity. -/
def masterLeft {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (E : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaResidueUnit s * ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s + E s) - 1)

/-- The right side of the master identity. -/
def masterRight (N : ℕ) (a f : ℕ → ℝ) (s : ℂ) : ℂ :=
  dirPoly N a s * ((s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s) -
    (s - 1) ^ 2 * dirPoly N f s

theorem analyticOnNhd_masterRight (N : ℕ) (a f : ℕ → ℝ) :
    AnalyticOnNhd ℂ (masterRight N a f) univ := by
  have hZ : AnalyticOnNhd ℂ zetaResidueUnit univ := fun s _ => analyticAt_zetaResidueUnit s
  have hZ' := hZ.deriv
  have hA : AnalyticOnNhd ℂ (dirPoly N a) univ :=
    (differentiable_dirPoly N a).differentiableOn.analyticOnNhd isOpen_univ
  have hF : AnalyticOnNhd ℂ (dirPoly N f) univ :=
    (differentiable_dirPoly N f).differentiableOn.analyticOnNhd isOpen_univ
  intro s _
  unfold masterRight
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
  exact ((hA s trivial).mul ((h1.mul (hZ' s trivial)).sub (hZ s trivial))).sub
    ((h1.pow 2).mul (hF s trivial))

theorem analyticOnNhd_masterLeft {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {E : ℂ → ℂ}
    (hE : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re}) :
    AnalyticOnNhd ℂ (masterLeft hW E) {s : ℂ | 1 / 2 < s.re} := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hU
  have hs' : 1 / 2 < s.re := hs
  have hΦ : DifferentiableAt ℂ (weilContinuation hW) s :=
    (differentiableOn_weilContinuation hW).differentiableAt (hU.mem_nhds hs)
  have hG := differentiableAt_zetaArchimedeanDatum (s := s) (by linarith)
  have hEs : DifferentiableAt ℂ E s := hE.differentiableAt (hU.mem_nhds hs)
  have hZ : DifferentiableAt ℂ zetaResidueUnit s := (analyticAt_zetaResidueUnit s).differentiableAt
  unfold masterLeft
  exact (hZ.mul (((differentiableAt_id.sub_const 1).mul ((hΦ.sub hG).add hEs)).sub
    (differentiableAt_const _))).differentiableWithinAt

/-- **The master identity** on `Re s > ½`. -/
theorem master_identity {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ} (hs : 1 / 2 < s.re) :
    masterLeft hW E s = masterRight N a f s := by
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  have hE : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re} :=
    hEd.mono fun z hz => by simp only [mem_setOf_eq] at hz ⊢; linarith
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hUdef
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ U := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  refine (analyticOnNhd_masterLeft hW hE).eqOn_of_preconnected_of_eventuallyEq
    (fun z _ => analyticOnNhd_masterRight N a f z trivial) hpre h2U ?_ hs
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  unfold masterLeft masterRight
  rw [weilContinuation_eq hW hz, weilFunction, lamC_finiteTypeSeq a hf1 hv.zero hv.one,
    LSeries_finiteTypeSeq ha hf hv hz, ← sq_mul_deriv_riemannZeta hz1,
    (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

/-- **Off `s = 1`**: `ζ · (Φ − G − 1/(s − 1) + E) = A ζ' − F`. -/
theorem zeta_mul_eq {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + E s) =
      dirPoly N a s * deriv riemannZeta s - dirPoly N f s := by
  have h := master_identity ha hf hf1 hv hW hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold masterLeft masterRight at h
  rw [← sq_mul_deriv_riemannZeta hs1, (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at h
  have h2 : (s - 1) ^ 2 * (riemannZeta s *
      (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + E s)) =
      (s - 1) ^ 2 * (dirPoly N a s * deriv riemannZeta s - dirPoly N f s) := by
    have e : (s - 1) ^ 2 * (riemannZeta s *
        (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + E s)) =
        (s - 1) * riemannZeta s *
          ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s + E s) - 1) := by
      field_simp; ring
    rw [e, h]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hs1') h2

/-- **Normalization at `s = 1`**: `A(1) = Σ a(n)/n = 1`. -/
theorem dirPoly_one_eq_one {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) : dirPoly N a 1 = 1 := by
  have h := master_identity ha hf hf1 hv hW (s := 1) (by norm_num)
  unfold masterLeft masterRight at h
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_sub, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_neg, mul_one] at h
  linear_combination h

end

end RHTower.WeilFiniteType
