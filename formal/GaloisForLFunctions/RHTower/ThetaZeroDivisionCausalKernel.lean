import GaloisForLFunctions.RHTower.ThetaTailIntegralCalculus
import GaloisForLFunctions.HTGeometry.QuasiPolynomialLaplaceCalculus

/-!
# The causal kernel of a zero-division source

For a list `L` of zeros `β` of `F = XiC` the one-sided division `T_β f(x) = β ∫₀^∞ sin(βt) f(x+t)`
has the kernel `β sin(βs)`, a quasi-polynomial with exponents `±iβ`.  Iterating by the shear
identity, a list division `T_L` (nonempty `L`) is `∫₀^∞ K_L(s) f(x+s) ds` with the quasi-polynomial
`K_L = K_{β₁} ⋆ ⋯ ⋆ K_{β_n}`, and the partial-fraction combination realizing `e(z²)/P_L(z)` is

`listComb L e (x) = c f(x) + ∫₀^∞ K(s) f(x+s) ds`

for every source with all exponential moments.  With `f = k` and real part taken this is the causal
representation `u(x) = c k(x) + ∫₀^∞ K(s) k(x+s) ds` on `x ≥ 0`.

* **Laplace identity.**  `c + ∫₀^∞ K(s) e^{-qs} ds = r(−q²) = e(−q²)/P_L(iq)` for `Re q` beyond
  every `|Im β|`: `K` is the causal inverse Laplace kernel of `r(−q²) − c`.
* **Poles.**  `r(−q²) = c + ℒK(q)` off the finite set `{±iβ}`; the poles of `r(−q²)` are exactly the
  exponents of `K`, the order being one more than the degree of the coefficient, and they are
  symmetric under `q ↦ −q`.
* **Reality.**  For conjugation-closed lists and real numerators `c` is real and `K` is real-valued.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry (QuasiPolynomial)

namespace RHTower

noncomputable section

/-! ## Integrability against quasi-polynomial kernels -/

theorem ExpMomentSource.integrableOn_mul_shift {f : ℝ → ℂ} (hf : ExpMomentSource f) {w : ℝ → ℂ}
    (hw : Continuous w) {C A : ℝ} (hwb : ∀ t, 0 ≤ t → ‖w t‖ ≤ C * Real.exp (A * t)) (x : ℝ) :
    IntegrableOn (fun t => w t * f (x + t)) (Ioi 0) := by
  have hI := (((hf.moment |A|).comp_add_left x).const_mul (|C| * Real.exp (|A| * |x|))).integrableOn
    (s := Ioi (0 : ℝ))
  refine hI.mono' ((hw.mul (hf.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [norm_mul]
  have h1 : Real.exp (A * t) ≤ Real.exp (|A| * |x|) * Real.exp (|A| * |x + t|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : |t| ≤ |x| + |x + t| := by
      calc |t| = |-x + (x + t)| := by ring_nf
        _ ≤ |-x| + |x + t| := abs_add_le _ _
        _ = |x| + |x + t| := by rw [abs_neg]
    calc A * t ≤ |A| * |t| := by
          rw [abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_right (le_abs_self A) ht0
      _ ≤ |A| * (|x| + |x + t|) := mul_le_mul_of_nonneg_left this (abs_nonneg A)
      _ = _ := by ring
  calc ‖w t‖ * ‖f (x + t)‖ ≤ |C| * (Real.exp (|A| * |x|) * Real.exp (|A| * |x + t|)) *
        ‖f (x + t)‖ := by
        refine mul_le_mul_of_nonneg_right ((hwb t ht0).trans ?_) (norm_nonneg _)
        exact mul_le_mul (le_abs_self C) h1 (Real.exp_pos _).le (abs_nonneg C)
    _ = |C| * Real.exp (|A| * |x|) * (Real.exp (|A| * |x + t|) * ‖f (x + t)‖) := by ring

theorem ExpMomentSource.integrableOn_mul_exp_shift {f : ℝ → ℂ} (hf : ExpMomentSource f) (a x : ℝ) :
    IntegrableOn (fun t => t * Real.exp (a * t) * ‖f (x + t)‖) (Ioi 0) := by
  have h := hf.integrableOn_mul_shift (w := fun t => ((t * Real.exp (a * t) : ℝ) : ℂ))
    (by fun_prop) (C := 1) (A := a + 1) (fun t ht => by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), one_mul,
        show (a + 1) * t = t + a * t by ring, Real.exp_add]
      exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le) x
  refine IntegrableOn.congr_fun h.norm (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ t * Real.exp (a * t))]

/-! ## The sine kernel and its convolutions -/

/-- The outward sine kernel `β sin(βs)` as a quasi-polynomial. -/
def sineKernel (β : ℂ) : QuasiPolynomial :=
  (β / (2 * I)) • (Finsupp.single (I * β) 1 - Finsupp.single (-(I * β)) 1)

theorem sineKernel_eval (β : ℂ) (s : ℝ) : (sineKernel β).eval s = β * Complex.sin (β * s) := by
  rw [sineKernel, QuasiPolynomial.eval_smul, QuasiPolynomial.eval_sub, QuasiPolynomial.eval_single,
    QuasiPolynomial.eval_single, Complex.sin]
  simp only [Polynomial.eval_one, one_mul]
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `β sin(β·) ⋆ E`, i.e. `∫₀^t β sin(β(t−u)) E(u) du`. -/
def sineConv (β : ℂ) (E : QuasiPolynomial) : QuasiPolynomial :=
  (β / (2 * I)) • (QuasiPolynomial.convExp (I * β) E - QuasiPolynomial.convExp (-(I * β)) E)

theorem sineConv_eval (β : ℂ) (E : QuasiPolynomial) (t : ℝ) :
    (sineConv β E).eval t = ∫ u in (0 : ℝ)..t, (sineKernel β).eval u * E.eval (t - u) := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
    (fun u : ℝ => (sineKernel β).eval u * E.eval (t - u)) t
  simp only [sub_zero, sub_self, sub_sub_cancel] at h
  rw [← h]
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hpt : ∀ u : ℝ, (sineKernel β).eval (t - u) * E.eval u = β / (2 * I) *
      (Complex.exp (I * β * (t - u)) * E.eval u - Complex.exp (-(I * β) * (t - u)) * E.eval u) :=
    fun u => by
      rw [sineKernel_eval, Complex.sin]
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring_nf
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (f := fun u : ℝ => Complex.exp (I * β * (t - u)) * E.eval u)
    (g := fun u : ℝ => Complex.exp (-(I * β) * (t - u)) * E.eval u)
    (((by fun_prop : Continuous fun u : ℝ => Complex.exp (I * β * (t - u))).mul
      E.continuous_eval).intervalIntegrable _ _)
    (((by fun_prop : Continuous fun u : ℝ => Complex.exp (-(I * β) * (t - u))).mul
      E.continuous_eval).intervalIntegrable _ _), sineConv, QuasiPolynomial.eval_smul,
    QuasiPolynomial.eval_sub, QuasiPolynomial.eval_convExp, QuasiPolynomial.eval_convExp]

theorem convExp_zero (μ : ℂ) : QuasiPolynomial.convExp μ 0 = 0 := by
  simp [QuasiPolynomial.convExp]

theorem sineConv_zero (β : ℂ) : sineConv β 0 = 0 := by
  simp [sineConv, convExp_zero]

/-! ## Kernels of list divisions -/

/-- The kernel `K_L` of the list division: `T_L f(x) = ∫₀^∞ K_L(s) f(x+s) ds` for nonempty `L`. -/
def divKernel : List ℂ → QuasiPolynomial
  | [] => 0
  | β :: L => (if L = [] then sineKernel β else 0) + sineConv β (divKernel L)

theorem divKernel_cons_of_ne_nil (β : ℂ) {L : List ℂ} (hL : L ≠ []) :
    divKernel (β :: L) = sineConv β (divKernel L) := by
  rw [divKernel, if_neg hL, zero_add]

theorem exists_bound_eval (E : QuasiPolynomial) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℝ, 0 ≤ s → ‖E.eval s‖ ≤ C * Real.exp (A * s) := by
  classical
  set A := ∑ μ ∈ E.support, |μ.re| + 1
  have hA : ∀ μ ∈ E.support, μ.re < A := fun μ hμ => by
    have := Finset.single_le_sum (f := fun μ : ℂ => |μ.re|) (fun _ _ => abs_nonneg _) hμ
    have := le_abs_self μ.re
    simp only [A]; linarith
  obtain ⟨C, hC0, hC⟩ := E.exists_norm_eval_le hA
  exact ⟨C, A, hC0, by positivity, hC⟩

/-- **Green formula for list divisions.**  For a source with all exponential moments,
`T_L f(x) = [L = []] f(x) + ∫₀^∞ K_L(s) f(x+s) ds`. -/
theorem halfListDivision_eq_kernel {f : ℝ → ℂ} (hf : ExpMomentSource f) (L : List ℂ) (x : ℝ) :
    halfListDivision L f x =
      (if L = [] then f x else 0) + ∫ s in Ioi (0 : ℝ), (divKernel L).eval s * f (x + s) := by
  induction L generalizing x with
  | nil => simp [halfListDivision, divKernel]
  | cons β L ih =>
    rw [if_neg (List.cons_ne_nil β L), zero_add]
    rcases L with _ | ⟨γ, L'⟩
    · have hK : divKernel [β] = sineKernel β := by
        simp [divKernel, sineConv_zero]
      rw [hK, halfListDivision]
      unfold outwardSine
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [sineKernel_eval]
      simp [halfListDivision, mul_assoc]
    · have ih' : ∀ y, halfListDivision (γ :: L') f y =
          ∫ s in Ioi (0 : ℝ), (divKernel (γ :: L')).eval s * f (y + s) := fun y => by
        rw [ih y, if_neg (List.cons_ne_nil γ L'), zero_add]
      obtain ⟨C₁, A₁, hC₁, hA₁, hb₁⟩ := exists_bound_eval (sineKernel β)
      obtain ⟨C₂, A₂, hC₂, hA₂, hb₂⟩ := exists_bound_eval (divKernel (γ :: L'))
      set A := max C₁ C₂ + max A₁ A₂ + 1
      have hAb : ∀ (E : QuasiPolynomial) (C a : ℝ), 0 ≤ C → 0 ≤ a → C ≤ max C₁ C₂ →
          a ≤ max A₁ A₂ → (∀ s : ℝ, 0 ≤ s → ‖E.eval s‖ ≤ C * Real.exp (a * s)) →
          ∀ s : ℝ, 0 ≤ s → ‖E.eval s‖ ≤ A * Real.exp (A * s) := fun E C a hC ha hCm ham hE s hs => by
        refine (hE s hs).trans ?_
        have hCA : C ≤ A := by simp only [A]; linarith [le_max_left A₁ A₂, hA₁]
        have haA : a * s ≤ A * s := mul_le_mul_of_nonneg_right (by
          simp only [A]; linarith [le_max_left C₁ C₂, hC₁]) hs
        exact mul_le_mul hCA (Real.exp_le_exp.2 haA) (Real.exp_pos _).le (by linarith)
      have hsh := integral_Ioi_shear (φ := (sineKernel β).eval) (ψ := (divKernel (γ :: L')).eval)
        (sineKernel β).continuous_eval (divKernel (γ :: L')).continuous_eval (A := A) (a := A)
        (hAb _ C₁ A₁ hC₁ hA₁ (le_max_left _ _) (le_max_left _ _) hb₁)
        (hAb _ C₂ A₂ hC₂ hA₂ (le_max_right _ _) (le_max_right _ _) hb₂)
        (hf.continuous.stronglyMeasurable) (x := x) (hf.integrableOn_mul_exp_shift A x)
      rw [halfListDivision]
      unfold outwardSine
      rw [← integral_const_mul]
      have hin : ∀ t : ℝ, β * (Complex.sin (β * t) * halfListDivision (γ :: L') f (x + t)) =
          (sineKernel β).eval t * ∫ s in Ioi (0 : ℝ), (divKernel (γ :: L')).eval s *
            f (x + t + s) := fun t => by
        rw [ih' (x + t), sineKernel_eval]; ring
      simp_rw [hin, hsh]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [divKernel_cons_of_ne_nil β (List.cons_ne_nil γ L'), sineConv_eval]

theorem ExpMomentSource.integrableOn_eval_mul_shift {f : ℝ → ℂ} (hf : ExpMomentSource f)
    (E : QuasiPolynomial) (x : ℝ) :
    IntegrableOn (fun s => E.eval s * f (x + s)) (Ioi 0) := by
  obtain ⟨C, A, -, -, hb⟩ := exists_bound_eval E
  exact hf.integrableOn_mul_shift E.continuous_eval hb x

/-! ## Kernels of partial-fraction combinations -/

/-- The constant part `c` of the combination `listComb L e`. -/
def combConst : List ℂ → Polynomial ℂ → ℂ
  | [], e => e.coeff 0
  | β :: L, e => -(β ^ 2) * combConst L (e /ₘ (Polynomial.X - Polynomial.C (β ^ 2)))

/-- The causal kernel `K` of the combination `listComb L e`. -/
def combKernel : List ℂ → Polynomial ℂ → QuasiPolynomial
  | [], _ => 0
  | β :: L, e => e.eval (β ^ 2) • divKernel (β :: L) -
      (β ^ 2) • combKernel L (e /ₘ (Polynomial.X - Polynomial.C (β ^ 2)))

/-- **Green formula for partial-fraction combinations.**
`listComb L e = c f + ∫₀^∞ K(s) f(· + s) ds`. -/
theorem listComb_eq_kernel {f : ℝ → ℂ} (hf : ExpMomentSource f) (L : List ℂ) (e : Polynomial ℂ)
    (x : ℝ) :
    listComb (fun L' => halfListDivision L' f) L e x =
      combConst L e * f x + ∫ s in Ioi (0 : ℝ), (combKernel L e).eval s * f (x + s) := by
  induction L generalizing e with
  | nil => simp [listComb_nil, combConst, combKernel, halfListDivision]
  | cons β L ih =>
    rw [listComb_cons]
    beta_reduce
    rw [halfListDivision_eq_kernel hf, if_neg (List.cons_ne_nil β L), zero_add, ih,
      combConst, combKernel]
    simp only [QuasiPolynomial.eval_sub, QuasiPolynomial.eval_smul, sub_mul, mul_assoc]
    rw [integral_sub ((hf.integrableOn_eval_mul_shift _ x).const_mul _)
      ((hf.integrableOn_eval_mul_shift _ x).const_mul _), integral_const_mul, integral_const_mul]
    ring

/-! ## Exponents and Laplace transforms of the kernels -/

/-- The candidate exponents `±iβ`, `β ∈ L`. -/
def kernelExponents (L : List ℂ) : Set ℂ := {μ | ∃ β ∈ L, μ = I * β ∨ μ = -(I * β)}

theorem support_sineKernel_subset (β : ℂ) :
    ((sineKernel β).support : Set ℂ) ⊆ {I * β, -(I * β)} := by
  intro μ hμ
  have h1 := Finsupp.support_smul (b := β / (2 * I))
    (g := Finsupp.single (I * β) (1 : Polynomial ℂ) - Finsupp.single (-(I * β)) 1) hμ
  rcases Finset.mem_union.1 (Finsupp.support_sub h1) with h | h
  · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]; simp
  · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]; simp

theorem support_sineConv_subset (β : ℂ) (E : QuasiPolynomial) :
    ((sineConv β E).support : Set ℂ) ⊆ {I * β, -(I * β)} ∪ E.support := by
  intro μ hμ
  have h1 := Finsupp.support_smul (b := β / (2 * I))
    (g := QuasiPolynomial.convExp (I * β) E - QuasiPolynomial.convExp (-(I * β)) E) hμ
  rcases Finset.mem_union.1 (Finsupp.support_sub h1) with h | h
  · rcases Finset.mem_insert.1 (QuasiPolynomial.support_convExp_subset _ E h) with h' | h'
    · left; rw [h']; simp
    · right; exact h'
  · rcases Finset.mem_insert.1 (QuasiPolynomial.support_convExp_subset _ E h) with h' | h'
    · left; rw [h']; simp
    · right; exact h'

theorem support_divKernel_subset (L : List ℂ) :
    ((divKernel L).support : Set ℂ) ⊆ kernelExponents L := by
  induction L with
  | nil => simp [divKernel]
  | cons β L ih =>
    intro μ hμ
    have hsub := Finsupp.support_add (g₁ := if L = [] then sineKernel β else 0)
      (g₂ := sineConv β (divKernel L)) hμ
    have hβ : ∀ ν ∈ ({I * β, -(I * β)} : Set ℂ), ν ∈ kernelExponents (β :: L) := by
      rintro ν (rfl | rfl)
      · exact ⟨β, List.mem_cons_self, Or.inl rfl⟩
      · exact ⟨β, List.mem_cons_self, Or.inr rfl⟩
    have hL : ∀ ν ∈ kernelExponents L, ν ∈ kernelExponents (β :: L) := by
      rintro ν ⟨γ, hγ, h⟩
      exact ⟨γ, List.mem_cons_of_mem _ hγ, h⟩
    rcases Finset.mem_union.1 hsub with h | h
    · split_ifs at h
      · exact hβ μ (support_sineKernel_subset β h)
      · simp at h
    · rcases support_sineConv_subset β _ h with h' | h'
      · exact hβ μ h'
      · exact hL μ (ih h')

theorem support_combKernel_subset (L : List ℂ) (e : Polynomial ℂ) :
    ((combKernel L e).support : Set ℂ) ⊆ kernelExponents L := by
  induction L generalizing e with
  | nil => simp [combKernel]
  | cons β L ih =>
    intro μ hμ
    have hsub := Finsupp.support_sub (f := e.eval (β ^ 2) • divKernel (β :: L))
      (g := (β ^ 2) • combKernel L (e /ₘ (Polynomial.X - Polynomial.C (β ^ 2)))) hμ
    rcases Finset.mem_union.1 hsub with h | h
    · exact support_divKernel_subset _ (Finsupp.support_smul h)
    · obtain ⟨γ, hγ, hγ'⟩ := ih _ (Finsupp.support_smul h)
      exact ⟨γ, List.mem_cons_of_mem _ hγ, hγ'⟩

/-- The exponents `±iβ` lie strictly left of `q` once `|Im β| < Re q`. -/
theorem re_lt_of_mem_kernelExponents {L : List ℂ} {q : ℂ} (hq : ∀ β ∈ L, |β.im| < q.re) {μ : ℂ}
    (hμ : μ ∈ kernelExponents L) : μ.re < q.re := by
  obtain ⟨β, hβ, rfl | rfl⟩ := hμ
  · have := hq β hβ
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
    linarith [neg_abs_le β.im]
  · have := hq β hβ
    simp only [neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg]
    linarith [le_abs_self β.im]

/-- **Laplace transform of the exponential convolution.** -/
theorem laplace_convExp (μ : ℂ) (E : QuasiPolynomial) {q : ℂ} (hμ : μ.re < q.re)
    (hE : ∀ ν ∈ E.support, ν.re < q.re) :
    (QuasiPolynomial.convExp μ E).laplace q = E.laplace q / (q - μ) := by
  classical
  have hC : ∀ ν ∈ (QuasiPolynomial.convExp μ E).support, ν.re < q.re := fun ν hν => by
    rcases Finset.mem_insert.1 (QuasiPolynomial.support_convExp_subset μ E hν) with h | h
    · rw [h]; exact hμ
    · exact hE ν h
  -- a common growth rate below `Re q`
  obtain ⟨b, hb, hbq⟩ : ∃ b, (∀ ν ∈ E.support, ν.re < b) ∧ b < q.re ∧ μ.re < b := by
    rcases E.support.eq_empty_or_nonempty with h | h
    · exact ⟨(μ.re + q.re) / 2, fun ν hν => by simp [h] at hν, by linarith, by linarith⟩
    · obtain ⟨ν₁, hν₁, hmax⟩ := Finset.exists_max_image E.support Complex.re h
      refine ⟨(max ν₁.re μ.re + q.re) / 2, fun ν hν => ?_, ?_, ?_⟩
      · have := hmax ν hν; have := hE ν₁ hν₁; have := le_max_left ν₁.re μ.re; linarith
      · have := hE ν₁ hν₁; rcases max_cases ν₁.re μ.re with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
      · have := le_max_right ν₁.re μ.re; have := hE ν₁ hν₁; linarith
  obtain ⟨C, hC0, hCb⟩ := E.exists_norm_eval_le hb
  set A := max C 1
  have hsh := integral_Ioi_shear (φ := E.eval) (ψ := fun s : ℝ => Complex.exp (μ * s))
    E.continuous_eval (by fun_prop) (A := A) (a := b)
    (fun u hu => (hCb u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
    (fun s hs => by
      rw [Complex.norm_exp, show (μ * (s : ℂ)).re = μ.re * s by simp [Complex.mul_re]]
      calc Real.exp (μ.re * s) ≤ Real.exp (b * s) := Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_right hbq.2.le hs)
        _ ≤ A * Real.exp (b * s) := le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _))
    (g := fun t : ℝ => Complex.exp (-(q * t))) (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-(q * t))).stronglyMeasurable (x := 0) (by
      have hz : 0 < (q - b).re := by simp; linarith [hbq.1]
      refine IntegrableOn.congr_fun (QuasiPolynomial.integrableOn_pow_mul_cexp 1 hz).norm (fun t ht => ?_)
        measurableSet_Ioi
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      simp only [pow_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, Complex.norm_exp,
        zero_add]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      simp [Complex.mul_re]; ring)
  simp only [zero_add] at hsh
  have hinner : ∀ u : ℝ, ∫ s in Ioi (0 : ℝ), Complex.exp (μ * s) *
      Complex.exp (-(q * ((u + s : ℝ) : ℂ))) =
      Complex.exp (-(q * u)) / (q - μ) := fun u => by
    have hz : 0 < (q - μ).re := by simp; linarith
    have h0 := QuasiPolynomial.integral_pow_mul_cexp 0 hz
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h0
    rw [div_eq_mul_one_div, ← h0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [hinner] at hsh
  rw [← (QuasiPolynomial.integral_eval_mul_cexp (QuasiPolynomial.convExp μ E) hC).2,
    ← (QuasiPolynomial.integral_eval_mul_cexp E hE).2]
  have hconv : ∀ t : ℝ, (∫ u in (0 : ℝ)..t, E.eval u * Complex.exp (μ * ((t - u : ℝ) : ℂ))) =
      (QuasiPolynomial.convExp μ E).eval t := fun t => by
    rw [QuasiPolynomial.eval_convExp]
    congr 1; funext u; push_cast; ring
  simp_rw [hconv] at hsh
  rw [← hsh, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

theorem laplaceTerm_one (μ q : ℂ) : QuasiPolynomial.laplaceTerm μ 1 q = 1 / (q - μ) := by
  simp [QuasiPolynomial.laplaceTerm]

theorem ne_I_mul_of_abs_im_lt {β q : ℂ} (hq : |β.im| < q.re) : q ≠ I * β ∧ q ≠ -(I * β) := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub] at this
    linarith [neg_abs_le β.im]
  · intro h
    have := congrArg Complex.re h
    simp only [neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg] at this
    linarith [le_abs_self β.im]

theorem sq_add_sq_ne_zero_of_abs_im_lt {β q : ℂ} (hq : |β.im| < q.re) : q ^ 2 + β ^ 2 ≠ 0 := by
  obtain ⟨h1, h2⟩ := ne_I_mul_of_abs_im_lt hq
  have : q ^ 2 + β ^ 2 = (q - I * β) * (q + I * β) := by ring_nf; rw [I_sq]; ring
  rw [this]
  exact mul_ne_zero (sub_ne_zero.2 h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))

theorem inv_sub_inv_I_mul {β q : ℂ} (hq : |β.im| < q.re) :
    1 / (q - I * β) - 1 / (q - -(I * β)) = 2 * I * β / (q ^ 2 + β ^ 2) := by
  obtain ⟨h1, h2⟩ := ne_I_mul_of_abs_im_lt hq
  have h1' : q - I * β ≠ 0 := sub_ne_zero.2 h1
  have h2' : q - -(I * β) ≠ 0 := sub_ne_zero.2 h2
  have hprod : (q - I * β) * (q - -(I * β)) = q ^ 2 + β ^ 2 := by ring_nf; rw [I_sq]; ring
  rw [div_sub_div _ _ h1' h2', hprod]
  congr 1; ring

theorem laplace_sineKernel (β : ℂ) {q : ℂ} (hq : |β.im| < q.re) :
    (sineKernel β).laplace q = β ^ 2 / (q ^ 2 + β ^ 2) := by
  obtain ⟨h1, h2⟩ := ne_I_mul_of_abs_im_lt hq
  have h1' : q - I * β ≠ 0 := sub_ne_zero.2 h1
  have h2' : q - -(I * β) ≠ 0 := sub_ne_zero.2 h2
  have hs := sq_add_sq_ne_zero_of_abs_im_lt hq
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  rw [sineKernel, QuasiPolynomial.laplace_smul, QuasiPolynomial.laplace_sub,
    QuasiPolynomial.laplace_single, QuasiPolynomial.laplace_single, laplaceTerm_one, laplaceTerm_one,
    inv_sub_inv_I_mul hq]
  field_simp

theorem laplace_sineConv (β : ℂ) (E : QuasiPolynomial) {q : ℂ} (hq : |β.im| < q.re)
    (hE : ∀ ν ∈ E.support, ν.re < q.re) :
    (sineConv β E).laplace q = β ^ 2 / (q ^ 2 + β ^ 2) * E.laplace q := by
  obtain ⟨h1, h2⟩ := ne_I_mul_of_abs_im_lt hq
  have h1' : q - I * β ≠ 0 := sub_ne_zero.2 h1
  have h2' : q - -(I * β) ≠ 0 := sub_ne_zero.2 h2
  have hs := sq_add_sq_ne_zero_of_abs_im_lt hq
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hre1 : (I * β).re < q.re := by
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]; linarith [neg_abs_le β.im]
  have hre2 : (-(I * β)).re < q.re := by
    simp only [neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg]
    linarith [le_abs_self β.im]
  rw [sineConv, QuasiPolynomial.laplace_smul, QuasiPolynomial.laplace_sub,
    laplace_convExp _ E hre1 hE, laplace_convExp _ E hre2 hE, div_eq_mul_one_div (E.laplace q),
    div_eq_mul_one_div (E.laplace q) (q - -(I * β)), ← mul_sub, inv_sub_inv_I_mul hq]
  field_simp

/-- **Laplace transform of a division kernel.**  `ℒK_L(q) = ∏_{β ∈ L} β²/(q² + β²)`. -/
theorem laplace_divKernel {L : List ℂ} (hL : L ≠ []) {q : ℂ} (hq : ∀ β ∈ L, |β.im| < q.re) :
    (divKernel L).laplace q = (L.map fun β => β ^ 2 / (q ^ 2 + β ^ 2)).prod := by
  induction L with
  | nil => exact absurd rfl hL
  | cons β L ih =>
    rcases L with _ | ⟨γ, L'⟩
    · have hK : divKernel [β] = sineKernel β := by simp [divKernel, sineConv_zero]
      rw [hK, laplace_sineKernel β (hq β List.mem_cons_self)]
      simp
    · rw [divKernel_cons_of_ne_nil β (List.cons_ne_nil γ L'),
        laplace_sineConv β _ (hq β List.mem_cons_self) (fun ν hν =>
          re_lt_of_mem_kernelExponents (fun b hb => hq b (List.mem_cons_of_mem _ hb))
            (support_divKernel_subset _ hν)),
        ih (List.cons_ne_nil γ L') (fun b hb => hq b (List.mem_cons_of_mem _ hb))]
      simp only [List.map_cons, List.prod_cons]

/-- The rate symbol `r(−q²) = e(−q²)/P_L(iq)`. -/
def rateSymbol (L : List ℂ) (e : Polynomial ℂ) (q : ℂ) : ℂ :=
  e.eval (-q ^ 2) / listDivisor L (I * q)

theorem listDivisor_I_mul (L : List ℂ) (q : ℂ) :
    listDivisor L (I * q) = (L.map fun β => 1 + q ^ 2 / β ^ 2).prod := by
  unfold listDivisor
  congr 1
  refine List.map_congr_left fun β _ => ?_
  rw [mul_pow, I_sq]; ring

theorem prod_div_sq_add_sq {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {q : ℂ}
    (hq : ∀ β ∈ L, |β.im| < q.re) :
    (L.map fun β => β ^ 2 / (q ^ 2 + β ^ 2)).prod * listDivisor L (I * q) = 1 := by
  induction L with
  | nil => simp [listDivisor_nil]
  | cons β L ih =>
    rw [List.map_cons, List.prod_cons, listDivisor_cons]
    have hih := ih (fun b hb => hL0 b (List.mem_cons_of_mem _ hb))
      (fun b hb => hq b (List.mem_cons_of_mem _ hb))
    have hβ := hL0 β List.mem_cons_self
    have hs := sq_add_sq_ne_zero_of_abs_im_lt (hq β List.mem_cons_self)
    have hk : β ^ 2 / (q ^ 2 + β ^ 2) * (1 - (I * q) ^ 2 / β ^ 2) = 1 := by
      rw [mul_pow, I_sq]; field_simp; ring
    calc β ^ 2 / (q ^ 2 + β ^ 2) * (List.map (fun β => β ^ 2 / (q ^ 2 + β ^ 2)) L).prod *
          ((1 - (I * q) ^ 2 / β ^ 2) * listDivisor L (I * q))
        = (β ^ 2 / (q ^ 2 + β ^ 2) * (1 - (I * q) ^ 2 / β ^ 2)) *
          ((List.map (fun β => β ^ 2 / (q ^ 2 + β ^ 2)) L).prod * listDivisor L (I * q)) := by ring
      _ = 1 := by rw [hk, hih, one_mul]

/-- **Laplace identity.**  `c + ℒK(q) = r(−q²)` for `Re q > max |Im β|`. -/
theorem combConst_add_laplace_combKernel {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0)
    {e : Polynomial ℂ} (he : e.natDegree ≤ L.length) {q : ℂ} (hq : ∀ β ∈ L, |β.im| < q.re) :
    combConst L e + (combKernel L e).laplace q = rateSymbol L e q := by
  induction L generalizing e with
  | nil =>
    have he0 : e = Polynomial.C (e.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by simpa using he)
    simp only [combConst, combKernel, QuasiPolynomial.laplace, Finsupp.sum_zero_index, add_zero,
      rateSymbol, listDivisor_nil, div_one]
    conv_rhs => rw [he0]
    simp
  | cons β L ih =>
    have hβ := hL0 β List.mem_cons_self
    have hqβ := hq β List.mem_cons_self
    have hL0' : ∀ b ∈ L, b ≠ 0 := fun b hb => hL0 b (List.mem_cons_of_mem _ hb)
    have hq' : ∀ b ∈ L, |b.im| < q.re := fun b hb => hq b (List.mem_cons_of_mem _ hb)
    set e' := e /ₘ (Polynomial.X - Polynomial.C (β ^ 2))
    have he' : e'.natDegree ≤ L.length := natDegree_divByMonic_X_sub_C_le (by simpa using he) _
    have hIH := ih hL0' he' hq'
    have hdiv := prod_div_sq_add_sq hL0 hq
    have hdivL := prod_div_sq_add_sq hL0' hq'
    have hPL : listDivisor L (I * q) ≠ 0 := fun h => by rw [h, mul_zero] at hdivL; exact zero_ne_one hdivL
    have hs := sq_add_sq_ne_zero_of_abs_im_lt hqβ
    have heval := congrArg (Polynomial.eval (-q ^ 2)) (eq_C_add_X_sub_C_mul_divByMonic e (β ^ 2))
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X] at heval
    rw [combConst, combKernel, QuasiPolynomial.laplace_sub, QuasiPolynomial.laplace_smul,
      QuasiPolynomial.laplace_smul, laplace_divKernel (List.cons_ne_nil β L) hq]
    unfold rateSymbol at hIH ⊢
    rw [listDivisor_cons] at hdiv ⊢
    set P := listDivisor L (I * q)
    set D := (List.map (fun β => β ^ 2 / (q ^ 2 + β ^ 2)) (β :: L)).prod
    have ha : 1 - (I * q) ^ 2 / β ^ 2 = (q ^ 2 + β ^ 2) / β ^ 2 := by
      rw [mul_pow, I_sq]; field_simp; ring
    rw [ha] at hdiv ⊢
    have ha0 : (q ^ 2 + β ^ 2) / β ^ 2 ≠ 0 := div_ne_zero hs (pow_ne_zero 2 hβ)
    have hD : D = 1 / ((q ^ 2 + β ^ 2) / β ^ 2 * P) :=
      eq_one_div_of_mul_eq_one_left hdiv
    have hsplit : combConst L e' = e'.eval (-q ^ 2) / P - (combKernel L e').laplace q := by
      rw [← hIH]; ring
    rw [hsplit, hD, heval]
    field_simp
    ring

/-! ## The real causal kernel -/

theorem tendsto_laplace_atTop (E : QuasiPolynomial) :
    Tendsto (fun σ : ℝ => E.laplace σ) atTop (𝓝 0) := by
  have hterm : ∀ (μ : ℂ) (k : ℕ), Tendsto (fun σ : ℝ => ((σ : ℂ) - μ)⁻¹ ^ (k + 1)) atTop (𝓝 0) := by
    intro μ k
    have hinv : Tendsto (fun σ : ℝ => ((σ : ℂ) - μ)⁻¹) atTop (𝓝 0) := by
      have hb : Tendsto (fun σ : ℝ => (σ - μ.re)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [eventually_gt_atTop (μ.re + 1)] with σ hσ
      have hpos : 0 < σ - μ.re := by linarith
      rw [norm_inv]
      refine inv_anti₀ hpos ?_
      calc σ - μ.re = ((σ : ℂ) - μ).re := by simp
        _ ≤ |((σ : ℂ) - μ).re| := le_abs_self _
        _ ≤ ‖(σ : ℂ) - μ‖ := Complex.abs_re_le_norm _
    have := hinv.pow (k + 1)
    rwa [zero_pow (Nat.succ_ne_zero k)] at this
  have hfun : (fun σ : ℝ => E.laplace σ) = fun σ : ℝ => ∑ μ ∈ E.support,
      ∑ j ∈ Finset.range ((E μ).natDegree + 1),
        (E μ).coeff j * (j.factorial : ℂ) * ((σ : ℂ) - μ)⁻¹ ^ (j + 1) := by
    funext σ
    rw [QuasiPolynomial.laplace_eq_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun j _ => ?_
    rw [inv_pow, div_eq_mul_inv]
  rw [hfun]
  have := tendsto_finsetSum E.support fun μ _ => tendsto_finsetSum
    (Finset.range ((E μ).natDegree + 1)) fun j _ =>
      (hterm μ j).const_mul ((E μ).coeff j * (j.factorial : ℂ))
  simpa using this

/-- The listed exponents are nonzero for a division list. -/
theorem ThetaDivisionList.ne_zero {L : List ℂ} (hL : ThetaDivisionList L) : ∀ β ∈ L, β ≠ 0 :=
  fun β hβ h => by have := hL.1 β hβ; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this

/-- `max |Im β|` over the list, a bound beyond which all transforms converge. -/
def listImBound (L : List ℂ) : ℝ := (L.map fun β => |β.im|).sum

theorem abs_im_le_listImBound {L : List ℂ} {β : ℂ} (hβ : β ∈ L) : |β.im| ≤ listImBound L := by
  unfold listImBound
  exact List.single_le_sum (fun x hx => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _) _ (List.mem_map_of_mem hβ)

/-- **Laplace transform of the kernel.**  `∫₀^∞ K(s) e^{-qs} ds = r(−q²) − c` for
`Re q > Σ |Im β|`. -/
theorem integral_combKernel_mul_cexp {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) {q : ℂ} (hq : listImBound L < q.re) :
    IntegrableOn (fun s : ℝ => (combKernel L e).eval s * Complex.exp (-(q * s))) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), (combKernel L e).eval s * Complex.exp (-(q * s)) =
        rateSymbol L e q - combConst L e := by
  have hq' : ∀ β ∈ L, |β.im| < q.re := fun β hβ => (abs_im_le_listImBound hβ).trans_lt hq
  have hsupp : ∀ ν ∈ (combKernel L e).support, ν.re < q.re := fun ν hν =>
    re_lt_of_mem_kernelExponents hq' (support_combKernel_subset L e hν)
  obtain ⟨hint, hval⟩ := QuasiPolynomial.integral_eval_mul_cexp _ hsupp
  refine ⟨hint, ?_⟩
  rw [hval, ← combConst_add_laplace_combKernel hL0 he hq']
  ring

/-- Conjugation-closed lists: `P_L(i q̄) = \overline{P_L(iq)}`. -/
theorem listDivisor_I_mul_conj {L : List ℂ} (hconj : (L.map (starRingEnd ℂ)).Perm L) (σ : ℝ) :
    starRingEnd ℂ (listDivisor L (I * σ)) = listDivisor L (I * σ) := by
  rw [listDivisor_I_mul, map_list_prod, List.map_map]
  conv_rhs => rw [← hconj.map (fun β => 1 + ((σ : ℂ)) ^ 2 / β ^ 2) |>.prod_eq]
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp [map_div₀, map_pow, Complex.conj_ofReal]

theorem rateSymbol_im {L : List ℂ} (hconj : (L.map (starRingEnd ℂ)).Perm L) (N : Polynomial ℝ)
    (σ : ℝ) : (rateSymbol L (N.map (algebraMap ℝ ℂ)) σ).im = 0 := by
  rw [← Complex.conj_eq_iff_im, rateSymbol, map_div₀, listDivisor_I_mul_conj hconj]
  congr 1
  rw [Polynomial.eval_map, show (-(σ : ℂ) ^ 2) = algebraMap ℝ ℂ (-σ ^ 2) by
    rw [Complex.coe_algebraMap]; push_cast; ring, Polynomial.eval₂_at_apply]
  exact Complex.conj_ofReal _

/-- **Reality of the causal kernel** for conjugation-closed division lists and real numerators. -/
theorem combKernel_real {L : List ℂ} (hL : ThetaDivisionList L)
    (hconj : (L.map (starRingEnd ℂ)).Perm L) {N : Polynomial ℝ} (hN : N.natDegree ≤ L.length) :
    (combConst L (N.map (algebraMap ℝ ℂ))).im = 0 ∧
      ∀ s : ℝ, ((combKernel L (N.map (algebraMap ℝ ℂ))).eval s).im = 0 := by
  have hdeg : (N.map (algebraMap ℝ ℂ)).natDegree ≤ L.length := (Polynomial.natDegree_map_le).trans hN
  set e := N.map (algebraMap ℝ ℂ)
  have hid : ∀ σ : ℝ, listImBound L < σ →
      combConst L e + (combKernel L e).laplace σ = rateSymbol L e σ := fun σ hσ =>
    combConst_add_laplace_combKernel hL.ne_zero hdeg fun β hβ =>
      (abs_im_le_listImBound hβ).trans_lt (by simpa using hσ)
  have hc : (combConst L e).im = 0 := by
    have hlim := ((Complex.continuous_im.tendsto 0).comp (tendsto_laplace_atTop (combKernel L e)))
    rw [Complex.zero_im] at hlim
    have hev : ∀ᶠ σ : ℝ in atTop, (combConst L e).im =
        -((combKernel L e).laplace σ).im := by
      filter_upwards [eventually_gt_atTop (listImBound L)] with σ hσ
      have h := congrArg Complex.im (hid σ hσ)
      rw [Complex.add_im, rateSymbol_im hconj N σ] at h
      linarith
    have := (tendsto_const_nhds (x := (combConst L e).im)).congr' hev
    have h2 := hlim.neg
    rw [neg_zero] at h2
    exact tendsto_nhds_unique this (h2.congr fun σ => rfl)
  refine ⟨hc, fun s => QuasiPolynomial.im_eval_eq_zero _ (A := listImBound L) (fun σ hσ => ?_) s⟩
  have h := congrArg Complex.im (hid σ hσ)
  rw [Complex.add_im, rateSymbol_im hconj N σ, hc, zero_add] at h
  exact h

/-- The real causal kernel `K` of the division source. -/
def causalRateKernel (L : List ℂ) (N : Polynomial ℝ) (s : ℝ) : ℝ :=
  ((combKernel L (N.map (algebraMap ℝ ℂ))).eval s).re

/-- The constant part `c` of the division source. -/
def causalRateConst (L : List ℂ) (N : Polynomial ℝ) : ℝ :=
  (combConst L (N.map (algebraMap ℝ ℂ))).re

/-- The real source `u = Re listComb` realizing `F(z) N(z²)/P_L(z)`. -/
def divisionSource (L : List ℂ) (N : Polynomial ℝ) (x : ℝ) : ℝ :=
  (listComb thetaListDivision L (N.map (algebraMap ℝ ℂ)) x).re

theorem continuous_causalRateKernel (L : List ℂ) (N : Polynomial ℝ) :
    Continuous (causalRateKernel L N) :=
  Complex.continuous_re.comp (QuasiPolynomial.continuous_eval _)

/-- **Causal representation (1).**  On `x ≥ 0`, `u(x) = c k(x) + ∫₀^∞ K(s) k(x+s) ds`. -/
theorem divisionSource_eq (L : List ℂ) (N : Polynomial ℝ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun s => causalRateKernel L N s * thetaCuspFullSource (x + s)) (Ioi 0) ∧
      divisionSource L N x = causalRateConst L N * thetaCuspFullSource x +
        ∫ s in Ioi (0 : ℝ), causalRateKernel L N s * thetaCuspFullSource (x + s) := by
  set e := N.map (algebraMap ℝ ℂ)
  have hint := expMomentSource_thetaSourceC.integrableOn_eval_mul_shift (combKernel L e) x
  have hre : ∀ s, causalRateKernel L N s * thetaCuspFullSource (x + s) =
      ((combKernel L e).eval s * thetaSourceC (x + s)).re := fun s => by
    simp [causalRateKernel, thetaSourceC, Complex.mul_re, e]
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.congr_fun hint.re (fun s _ => by
      simp only [RCLike.re_to_complex]; exact (hre s).symm) measurableSet_Ioi
  · have hre_int := integral_re hint
    simp only [RCLike.re_to_complex] at hre_int
    rw [divisionSource, listComb_congr (fun L' y hy => thetaListDivision_eq_halfListDivision L' y hy)
      _ _ hx, listComb_eq_kernel expMomentSource_thetaSourceC, Complex.add_re, ← hre_int]
    simp_rw [hre]
    simp [causalRateConst, thetaSourceC, Complex.mul_re, e]

/-! ## Poles of the rate symbol -/

theorem kernelExponents_finite (L : List ℂ) : (kernelExponents L).Finite := by
  refine (((L.map fun β => I * β) ++ L.map fun β => -(I * β)).toFinset.finite_toSet).subset ?_
  rintro μ ⟨β, hβ, rfl | rfl⟩
  · simp only [List.coe_toFinset, mem_setOf_eq, List.mem_append, List.mem_map]
    exact Or.inl ⟨β, hβ, rfl⟩
  · simp only [List.coe_toFinset, mem_setOf_eq, List.mem_append, List.mem_map]
    exact Or.inr ⟨β, hβ, rfl⟩

theorem neg_mem_kernelExponents {L : List ℂ} {μ : ℂ} (hμ : μ ∈ kernelExponents L) :
    -μ ∈ kernelExponents L := by
  obtain ⟨β, hβ, rfl | rfl⟩ := hμ
  · exact ⟨β, hβ, Or.inr rfl⟩
  · exact ⟨β, hβ, Or.inl (neg_neg _)⟩

theorem listDivisor_I_mul_ne_zero {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {q : ℂ}
    (hq : q ∉ kernelExponents L) : listDivisor L (I * q) ≠ 0 := by
  rw [listDivisor_I_mul]
  intro hprod
  obtain ⟨β, hβ, h⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 hprod)
  have hβ0 := hL0 β hβ
  have : (q - I * β) * (q + I * β) = 0 := by
    have h' : q ^ 2 + β ^ 2 = 0 := by
      have := congrArg (· * β ^ 2) h
      simp only [zero_mul] at this
      rw [add_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hβ0)] at this
      linear_combination this
    have hI : I ^ 2 = -1 := I_sq
    linear_combination h' - β ^ 2 * hI
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hq ⟨β, hβ, Or.inl (sub_eq_zero.1 h1)⟩
  · exact hq ⟨β, hβ, Or.inr (eq_neg_of_add_eq_zero_left h1)⟩

theorem analyticAt_listDivisor_I_mul (L : List ℂ) (q : ℂ) :
    AnalyticAt ℂ (fun q => listDivisor L (I * q)) q :=
  ((differentiable_listDivisor L).comp (differentiable_id.const_mul I)).analyticAt q

theorem meromorphicAt_rateSymbol (L : List ℂ) (e : Polynomial ℂ) (q : ℂ) :
    MeromorphicAt (rateSymbol L e) q := by
  have hnum : AnalyticAt ℂ (fun q : ℂ => e.eval (-q ^ 2)) q :=
    ((e.differentiable.comp (differentiable_id.pow 2).neg)).analyticAt q
  exact hnum.meromorphicAt.div (analyticAt_listDivisor_I_mul L q).meromorphicAt

/-- Off the candidate exponents, `r(−q²) = c + ℒK(q)` (identity theorem). -/
theorem rateSymbol_eq_add_laplace {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) {q : ℂ} (hq : q ∉ kernelExponents L) :
    rateSymbol L e q = combConst L e + (combKernel L e).laplace q := by
  set U : Set ℂ := (kernelExponents L)ᶜ
  have hU : IsPreconnected U :=
    ((kernelExponents_finite L).countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hf : AnalyticOnNhd ℂ (rateSymbol L e) U := fun q hq =>
    (((e.differentiable.comp (differentiable_id.pow 2).neg)).analyticAt q).div
      (analyticAt_listDivisor_I_mul L q) (listDivisor_I_mul_ne_zero hL0 hq)
  have hg : AnalyticOnNhd ℂ (fun q => combConst L e + (combKernel L e).laplace q) U := fun q hq =>
    analyticAt_const.add (QuasiPolynomial.analyticAt_laplace _ fun h =>
      hq (support_combKernel_subset L e h))
  set σ₀ : ℝ := listImBound L + 1
  have hσ₀U : (σ₀ : ℂ) ∈ U := fun hmem => by
    have := re_lt_of_mem_kernelExponents (q := (σ₀ : ℂ)) (fun β hβ => by
      simp only [Complex.ofReal_re, σ₀]; linarith [abs_im_le_listImBound hβ]) hmem
    simp at this
  have hev : rateSymbol L e =ᶠ[𝓝 (σ₀ : ℂ)] fun q => combConst L e + (combKernel L e).laplace q := by
    have hopen : IsOpen {q : ℂ | listImBound L < q.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show listImBound L < (σ₀ : ℂ).re by simp [σ₀])] with q hq'
    exact (combConst_add_laplace_combKernel hL0 he fun β hβ =>
      (abs_im_le_listImBound hβ).trans_lt hq').symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU hσ₀U hev hq

theorem rateSymbol_eventuallyEq {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) (μ : ℂ) :
    rateSymbol L e =ᶠ[𝓝[≠] μ] fun q => combConst L e + (combKernel L e).laplace q := by
  have hcl : IsClosed (kernelExponents L \ {μ}) := ((kernelExponents_finite L).sdiff).isClosed
  have hnot : μ ∉ kernelExponents L \ {μ} := fun h => h.2 rfl
  filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds hnot), self_mem_nhdsWithin]
    with q hq hqμ
  exact rateSymbol_eq_add_laplace hL0 he fun h => hq ⟨h, hqμ⟩

/-- **Poles of `r(−q²)` are the exponents of the kernel**, with order `deg + 1`. -/
theorem meromorphicOrderAt_rateSymbol {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) {μ : ℂ} (hμ : μ ∈ (combKernel L e).support) :
    meromorphicOrderAt (rateSymbol L e) μ =
      ((-((((combKernel L e) μ).natDegree : ℤ) + 1)) : ℤ) := by
  rw [meromorphicOrderAt_congr (rateSymbol_eventuallyEq hL0 he μ)]
  have hlap := QuasiPolynomial.meromorphicOrderAt_laplace _ hμ
  have hsum : (fun q => combConst L e + (combKernel L e).laplace q) =
      (combKernel L e).laplace + fun _ => combConst L e := by
    funext q; simp only [Pi.add_apply]; ring
  rw [hsum, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const _ _), hlap]
  rw [hlap]
  refine lt_of_lt_of_le ?_ (analyticAt_const.meromorphicOrderAt_nonneg)
  exact WithTop.coe_lt_coe.2 (by omega)

theorem meromorphicOrderAt_rateSymbol_nonneg {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0)
    {e : Polynomial ℂ} (he : e.natDegree ≤ L.length) {μ : ℂ} (hμ : μ ∉ (combKernel L e).support) :
    0 ≤ meromorphicOrderAt (rateSymbol L e) μ := by
  rw [meromorphicOrderAt_congr (rateSymbol_eventuallyEq hL0 he μ)]
  exact (analyticAt_const.add (QuasiPolynomial.analyticAt_laplace _ hμ)).meromorphicOrderAt_nonneg

theorem rateSymbol_neg (L : List ℂ) (e : Polynomial ℂ) (q : ℂ) :
    rateSymbol L e (-q) = rateSymbol L e q := by
  simp only [rateSymbol, listDivisor_I_mul, neg_sq]

/-- The exponents of the kernel are symmetric: `μ ↦ −μ`. -/
theorem neg_mem_support_combKernel {L : List ℂ} (hL0 : ∀ β ∈ L, β ≠ 0) {e : Polynomial ℂ}
    (he : e.natDegree ≤ L.length) {μ : ℂ} (hμ : μ ∈ (combKernel L e).support) :
    -μ ∈ (combKernel L e).support := by
  by_contra hneg
  have h0 := meromorphicOrderAt_rateSymbol_nonneg hL0 he hneg
  obtain ⟨g, hg, hfg⟩ := ((meromorphicAt_rateSymbol L e (-μ)).meromorphicOrderAt_nonneg_iff).1 h0
  have hpos : 0 ≤ meromorphicOrderAt (rateSymbol L e) μ := by
    refine ((meromorphicAt_rateSymbol L e μ).meromorphicOrderAt_nonneg_iff).2
      ⟨fun q => g (-q), hg.comp_of_eq (analyticAt_id.neg) (by simp), ?_⟩
    have htend : Tendsto (fun q : ℂ => -q) (𝓝[≠] μ) (𝓝[≠] (-μ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_neg.tendsto μ).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact fun h => hq (neg_inj.1 h)
    filter_upwards [htend.eventually hfg] with q hq
    rw [← rateSymbol_neg]; exact hq
  rw [meromorphicOrderAt_rateSymbol hL0 he hμ] at hpos
  have : ((-((((combKernel L e) μ).natDegree : ℤ) + 1)) : ℤ) < 0 := by omega
  exact absurd (WithTop.coe_le_coe.1 (by simpa using hpos)) (not_le.2 this)
end

end RHTower
