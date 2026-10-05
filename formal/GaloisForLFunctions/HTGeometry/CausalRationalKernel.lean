import GaloisForLFunctions.HTGeometry.QuasiPolynomialDerivativeLaplace
import GaloisForLFunctions.HTGeometry.YoungConvolutionLp
import GaloisForLFunctions.HTGeometry.CausalGammaHalfLaplace

/-!
# Causal kernels of reciprocal polynomials and causal convolution

A complex polynomial `P` of positive degree factors as `P = c Π (X - μ_i)` over its roots.  The
iterated causal exponential convolution `g = c⁻¹ e^{μ_1·} ∗ ⋯ ∗ e^{μ_n·}` is a quasi-polynomial
with exponents among the roots and Laplace transform `1/P(q)` beyond every root.  When all roots
lie in `Re μ < 0` the kernel decays exponentially, so its causal extension lies in `L¹ ∩ L²` and,
by Young's inequality, convolution with it is bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`.

For continuous functions of exponential type the Laplace transform of the causal convolution
`∫₀ᵗ k(t-s) f(s) ds` is the product of the transforms (weighted Fubini).
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped Convolution

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace QuasiPolynomial

/-! ### The kernel of `Π (q - μ_i)⁻¹` -/

/-- The iterated causal exponential convolution `e^{μ_1·} ∗ ⋯ ∗ e^{μ_n·}`. -/
def rootKernel : List ℂ → QuasiPolynomial
  | [] => 0
  | [μ] => Finsupp.single μ 1
  | μ :: ν :: L => convExp μ (rootKernel (ν :: L))

theorem support_rootKernel : ∀ L : List ℂ, (rootKernel L).support ⊆ L.toFinset
  | [] => by simp [rootKernel]
  | [μ] => by
    intro x hx
    rw [rootKernel] at hx
    simp [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
  | μ :: ν :: L => by
    intro x hx
    rw [rootKernel] at hx
    rcases Finset.mem_insert.1 (support_convExp_subset μ _ hx) with h | h
    · simp [h]
    · have := support_rootKernel (ν :: L) h
      simp only [List.toFinset_cons, Finset.mem_insert] at this ⊢
      tauto

theorem laplace_rootKernel {q : ℂ} :
    ∀ L : List ℂ, L ≠ [] → (∀ μ ∈ L, μ.re < q.re) →
      (rootKernel L).laplace q = (L.map fun μ => (q - μ)⁻¹).prod
  | [], h, _ => absurd rfl h
  | [μ], _, hμ => by
    rw [rootKernel, laplace_single, laplaceTerm]
    simp
  | μ :: ν :: L, _, hμ => by
    have hrest : ∀ x ∈ ν :: L, x.re < q.re := fun x hx => hμ x (List.mem_cons_of_mem μ hx)
    rw [rootKernel, laplace_convExp μ _ (fun x hx => hrest x (by
        simpa using support_rootKernel (ν :: L) hx)) (hμ μ List.mem_cons_self),
      laplace_rootKernel (ν :: L) (List.cons_ne_nil _ _) hrest, div_eq_mul_inv, mul_comm]
    simp only [List.map_cons, List.prod_cons]

/-- The causal kernel of `1/P`. -/
def ratKernel (P : ℂ[X]) : QuasiPolynomial := (P.leadingCoeff)⁻¹ • rootKernel P.roots.toList

theorem support_ratKernel (P : ℂ[X]) : (ratKernel P).support ⊆ P.roots.toFinset := by
  intro x hx
  have h1 := Finsupp.support_smul hx
  have := support_rootKernel _ h1
  simpa using this

theorem eval_eq_prod_roots (P : ℂ[X]) (q : ℂ) :
    P.eval q = P.leadingCoeff * (P.roots.toList.map fun μ => q - μ).prod := by
  have h1 : (P.roots.toList.map fun μ => q - μ).prod = (P.roots.map fun μ => q - μ).prod := by
    conv_rhs => rw [← Multiset.coe_toList P.roots]
    rw [Multiset.map_coe, Multiset.prod_coe]
  rw [h1]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P)
    IsAlgClosed.card_roots_eq_natDegree]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  congr 1
  simp

theorem prod_map_inv (q : ℂ) :
    ∀ L : List ℂ, (L.map fun μ => (q - μ)⁻¹).prod = ((L.map fun μ => q - μ).prod)⁻¹
  | [] => by simp
  | μ :: L => by simp only [List.map_cons, List.prod_cons, prod_map_inv q L, mul_inv]

/-- **The Laplace transform of the kernel is `1/P`.** -/
theorem laplace_ratKernel {P : ℂ[X]} (hP : 0 < P.natDegree) {q : ℂ}
    (hq : ∀ μ ∈ P.roots, μ.re < q.re) : (ratKernel P).laplace q = (P.eval q)⁻¹ := by
  have hne : P.roots.toList ≠ [] := by
    intro h
    have := IsAlgClosed.card_roots_eq_natDegree (p := P)
    rw [← Multiset.coe_toList P.roots, h] at this
    simp at this
    omega
  have hP0 : P ≠ 0 := fun h => by simp [h] at hP
  rw [ratKernel, laplace_smul, laplace_rootKernel _ hne (fun μ hμ => hq μ (by simpa using hμ)),
    eval_eq_prod_roots, mul_inv, prod_map_inv]

/-! ### Decay and integrability of kernels with stable roots -/

theorem exists_decay {E : QuasiPolynomial} (hE : ∀ μ ∈ E.support, μ.re < 0) :
    ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ‖E.eval t‖ ≤ C * Real.exp (-δ * t) := by
  obtain ⟨A, hA0, hA⟩ := E.exists_re_lt_between (q := 0) (by simpa using hE)
  obtain ⟨C, hC0, hC⟩ := E.exists_norm_eval_le hA
  refine ⟨-A, by simpa using hA0, C, hC0, fun t ht => ?_⟩
  simpa using hC t ht

theorem integrableOn_eval_of_stable {E : QuasiPolynomial} (hE : ∀ μ ∈ E.support, μ.re < 0) :
    IntegrableOn E.eval (Ioi 0) := by
  obtain ⟨δ, hδ, C, hC0, hC⟩ := exists_decay hE
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hδ).const_mul C)
    (E.continuous_eval.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (hC t (le_of_lt ht)).trans (le_of_eq (by ring_nf))

end QuasiPolynomial

/-! ### Causal extensions -/

/-- The causal extension `1_{t > 0} f(t)`. -/
def causalExt (f : ℝ → ℂ) : ℝ → ℂ := (Ioi 0).indicator f

theorem causalExt_nonpos (f : ℝ → ℂ) {t : ℝ} (ht : t ≤ 0) : causalExt f t = 0 :=
  indicator_of_notMem (fun h => absurd (mem_Ioi.1 h) (not_lt.2 ht)) _

theorem integrable_causalExt {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (causalExt f) :=
  (integrable_indicator_iff measurableSet_Ioi).2 hf

theorem measurable_causalExt {f : ℝ → ℂ} (hf : Continuous f) : Measurable (causalExt f) :=
  hf.measurable.indicator measurableSet_Ioi

/-- **Convolution with a stable causal kernel is bounded on every `Lᵖ`**:
`‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p < ∞ · ‖f‖_p`. -/
theorem eLpNorm_lineConv_causal_le {E : QuasiPolynomial} (hE : ∀ μ ∈ E.support, μ.re < 0)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f) {p : ENNReal} (hp : 1 ≤ p) :
    eLpNorm (lineConv (causalExt E.eval) f) p volume ≤
      eLpNorm (causalExt E.eval) 1 volume * eLpNorm f p volume ∧
      eLpNorm (causalExt E.eval) 1 volume < ⊤ :=
  ⟨eLpNorm_lineConv_le (measurable_causalExt E.continuous_eval) hf hp,
    (memLp_one_iff_integrable.2
      (integrable_causalExt (QuasiPolynomial.integrableOn_eval_of_stable hE))).eLpNorm_lt_top⟩

/-- A stable kernel lies in `L¹ ∩ L²` of the half-line. -/
theorem memLp_two_causalExt {E : QuasiPolynomial} (hE : ∀ μ ∈ E.support, μ.re < 0) :
    MemLp (causalExt E.eval) 2 := by
  obtain ⟨δ, hδ, C, hC0, hC⟩ := QuasiPolynomial.exists_decay hE
  refine MemLp.of_le_mul (g := causalExt fun t => (Real.exp (-δ * t) : ℂ)) (c := C) ?_
    (measurable_causalExt E.continuous_eval).aestronglyMeasurable ?_
  · have hint : IntegrableOn (fun t : ℝ => Real.exp (-δ * t) ^ 2) (Ioi 0) := by
      have := exp_neg_integrableOn_Ioi 0 (by positivity : 0 < 2 * δ)
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      rw [← Real.exp_nat_mul]; ring_nf
    refine (memLp_two_iff_integrable_sq_norm ?_).2 ?_
    · exact (measurable_causalExt (by fun_prop)).aestronglyMeasurable
    · refine ((integrable_indicator_iff measurableSet_Ioi).2 hint).congr
        (Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp only [causalExt, indicator_of_mem ht, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le]
      · simp [causalExt, indicator_of_notMem ht]
  · refine Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [causalExt, indicator_of_mem ht, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hC t (le_of_lt ht)
    · simp [causalExt, indicator_of_notMem ht]

/-! ### Laplace transform of the causal convolution -/

/-- The causal convolution `∫₀ᵗ k(t-s) f(s) ds`. -/
def causalConv (k f : ℝ → ℂ) (t : ℝ) : ℂ := ∫ s in (0 : ℝ)..t, k (t - s) * f s

theorem continuous_causalConv {k f : ℝ → ℂ} (hk : Continuous k) (hf : Continuous f) :
    Continuous (causalConv k f) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t s => k (t - s) * f s) (by fun_prop) continuous_id

theorem integrableOn_weighted {f : ℝ → ℂ} (hf : Continuous f) {a c C : ℝ} (hac : a < c)
    (hb : ∀ t, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(c * t)) * f t) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < c - a)).const_mul C)
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(c * t)) * f t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_exp]
  have hre : (-((c : ℂ) * t)).re = -(c * t) := by simp
  rw [hre]
  calc Real.exp (-(c * t)) * ‖f t‖ ≤ Real.exp (-(c * t)) * (C * Real.exp (a * t)) :=
        mul_le_mul_of_nonneg_left (hb t (le_of_lt ht)) (Real.exp_pos _).le
    _ = C * Real.exp (-(c - a) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- **Convolution theorem**: for continuous `k, f` of exponential type `a` and real `σ > a`,
`𝓛(∫₀^· k(·-s) f(s) ds)(σ) = 𝓛k(σ) 𝓛f(σ)`. -/
theorem laplace_causalConv {k f : ℝ → ℂ} (hk : Continuous k) (hf : Continuous f) {a C C' : ℝ}
    (hkb : ∀ t, 0 ≤ t → ‖k t‖ ≤ C * Real.exp (a * t))
    (hfb : ∀ t, 0 ≤ t → ‖f t‖ ≤ C' * Real.exp (a * t)) {σ : ℝ} (hσ : a < σ) :
    IntegrableOn (fun t => causalConv k f t * Complex.exp (-(σ * t))) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), causalConv k f t * Complex.exp (-(σ * t)) =
      (∫ t in Ioi (0 : ℝ), k t * Complex.exp (-(σ * t))) *
        ∫ t in Ioi (0 : ℝ), f t * Complex.exp (-(σ * t)) := by
  set c : ℝ := (a + σ) / 2
  have hac : a < c := by simp only [c]; linarith
  have hcσ : 0 ≤ σ - c := by simp only [c]; linarith
  set kw : ℝ → ℂ := causalExt fun t => Complex.exp (-(c * t)) * k t
  set fw : ℝ → ℂ := causalExt fun t => Complex.exp (-(c * t)) * f t
  have hkw : Integrable kw := integrable_causalExt (integrableOn_weighted hk hac hkb)
  have hfw : Integrable fw := integrable_causalExt (integrableOn_weighted hf hac hfb)
  have hkc : ∀ t ≤ 0, kw t = 0 := fun t ht => causalExt_nonpos _ ht
  have hfc : ∀ t ≤ 0, fw t = 0 := fun t ht => causalExt_nonpos _ ht
  have hs : (0 : ℝ) ≤ ((σ - c : ℝ) : ℂ).re := by simpa using hcσ
  have key := causalComplexLaplace_convolution hs hkw hfw hkc hfc
  have hpw : ∀ g : ℝ → ℂ, causalComplexLaplaceWeight ((σ - c : ℝ) : ℂ)
      (causalExt fun t => Complex.exp (-(c * t)) * g t) =
        causalExt fun t => g t * Complex.exp (-(σ * t)) := fun g => by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [causalComplexLaplaceWeight, causalExt, indicator_of_mem ht]
      rw [show Complex.exp (-(((σ - c : ℝ) : ℂ) * t)) * (Complex.exp (-(c * t)) * g t) =
        g t * (Complex.exp (-(((σ - c : ℝ) : ℂ) * t)) * Complex.exp (-(c * t))) by ring,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp [causalComplexLaplaceWeight, causalExt, indicator_of_notMem ht]
  have hlap : ∀ g : ℝ → ℂ, causalComplexLaplace ((σ - c : ℝ) : ℂ)
      (causalExt fun t => Complex.exp (-(c * t)) * g t) =
        ∫ t in Ioi (0 : ℝ), g t * Complex.exp (-(σ * t)) := fun g => by
    rw [causalComplexLaplace, hpw, causalExt, integral_indicator measurableSet_Ioi]
  have hconv : (kw ⋆[ContinuousLinearMap.mul ℂ ℂ] fw) =
      causalExt fun t => Complex.exp (-(c * t)) * causalConv k f t := by
    funext t
    by_cases ht : 0 < t
    · rw [causalExt, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), convolution_def]
      simp only [ContinuousLinearMap.mul_apply']
      have hpt : ∀ u, kw u * fw (t - u) = (Ioo 0 t).indicator
          (fun u => Complex.exp (-(c * t)) * (k u * f (t - u))) u := fun u => by
        by_cases hu : u ∈ Ioo 0 t
        · rw [indicator_of_mem hu]
          have h1 : u ∈ Ioi (0 : ℝ) := hu.1
          have h2 : t - u ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith [hu.2]
          simp only [kw, fw, causalExt, indicator_of_mem h1, indicator_of_mem h2]
          rw [show Complex.exp (-(c * t)) = Complex.exp (-(c * u)) *
            Complex.exp (-(c * (t - u : ℝ))) by rw [← Complex.exp_add]; push_cast; ring_nf]
          ring
        · rw [indicator_of_notMem hu]
          simp only [mem_Ioo, not_and_or, not_lt] at hu
          rcases hu with hu | hu
          · simp [kw, causalExt_nonpos _ hu]
          · simp [fw, causalExt_nonpos _ (by linarith : t - u ≤ 0)]
      simp_rw [hpt]
      rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_const_mul, causalConv]
      congr 1
      have hsub := intervalIntegral.integral_comp_sub_left
        (fun s => k (t - s) * f s) t (a := 0) (b := t)
      simp only [sub_sub_cancel, sub_self, sub_zero] at hsub
      exact hsub
    · rw [causalExt_nonpos _ (not_lt.1 ht)]
      exact causal_convolution_nonpos hkc hfc (not_lt.1 ht)
  have hint := causalComplexLaplaceWeight_integrable hs
    (hkw.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hfw)
    (fun t ht => causal_convolution_nonpos hkc hfc ht)
  rw [hconv, hpw] at hint
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).1 hint, ?_⟩
  rw [hconv, hlap, hlap, hlap] at key
  exact key

end GaloisForLFunctions.HTGeometry
