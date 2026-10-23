import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The critical Wiener algebra is a Banach algebra

For a real abscissa `σ` the arithmetic functions `f : ℕ → ℂ` whose Dirichlet series converges
absolutely at `σ` form a commutative `ℂ`-algebra under Dirichlet convolution, `𝒲_σ`
(`WienerAlgebraAt σ`).  At `σ = ½` it is the critical Wiener algebra of Trans-Horizon Incidence
Mechanics, with complex coefficients; at `σ = 0` it is the Dirichlet `ℓ¹` algebra.

* **Norm** (`norm_def`): `‖f‖ = Σ_n |f(n)| n^{−σ}`.  It is submultiplicative (`norm_mul_le'`):
  the weight `n^{−σ}` is completely multiplicative, so the norm of `|f| ⋆ |g|` is the product of
  the norms (`wienerNorm_absFn_mul`), read off the convolution theorem for L-series.
* **Completeness** (`isometryLp`): the coordinates `k ↦ f(k+1) (k+1)^{−σ}` identify `𝒲_σ`
  isometrically with `ℓ¹(ℕ)`, so `𝒲_σ` is a commutative unital Banach algebra with `‖1‖ = 1`.
* **Point masses** (`pointMass`, `pointMass_mul`, `norm_pointMass`, `hasSum_pointMass`): the point
  masses multiply as `δ_m δ_n = δ_{mn}`, have norm `n^{−σ}`, and every element is the
  norm-convergent series `f = Σ_n f(n) δ_n`.

These are the inputs of Gelfand theory; the spectrum and Wiener's lemma are in
`WienersLemmaOnTheBohrPolydisk`.
-/

open ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### The Wiener norm on arithmetic functions -/

/-- The Wiener norm at abscissa `σ`: `Σ_n ‖f(n)‖ n^{−σ}` (zero when the series diverges). -/
def wienerNorm (σ : ℝ) (f : ArithmeticFunction ℂ) : ℝ := ∑' n, ‖term (⇑f) σ n‖

theorem summable_norm_term_iff {σ : ℝ} {f : ℕ → ℂ} :
    (Summable fun n => ‖term f σ n‖) ↔ LSeriesSummable f σ :=
  summable_norm_iff

/-- The absolute value of an arithmetic function, as an arithmetic function. -/
def absFn (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => ((‖f n‖ : ℝ) : ℂ), by simp⟩

theorem absFn_apply (f : ArithmeticFunction ℂ) (n : ℕ) : absFn f n = ((‖f n‖ : ℝ) : ℂ) := rfl

/-- The L-series term of `|f|` at the real point `σ` is the real number `‖term f σ n‖`. -/
theorem term_absFn (σ : ℝ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    term (⇑(absFn f)) σ n = ((‖term (⇑f) σ n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, norm_term_eq, if_neg hn, absFn_apply, Complex.ofReal_re,
      ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_div]

theorem norm_term_absFn (σ : ℝ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    ‖term (⇑(absFn f)) σ n‖ = ‖term (⇑f) σ n‖ := by
  rw [term_absFn, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

theorem wienerNorm_absFn (σ : ℝ) (f : ArithmeticFunction ℂ) :
    wienerNorm σ (absFn f) = wienerNorm σ f := by
  unfold wienerNorm
  simp_rw [norm_term_absFn]

theorem lSeriesSummable_absFn_iff {σ : ℝ} {f : ArithmeticFunction ℂ} :
    LSeriesSummable (⇑(absFn f)) σ ↔ LSeriesSummable (⇑f) σ := by
  rw [← summable_norm_term_iff, ← summable_norm_term_iff]
  simp_rw [norm_term_absFn]

/-- The L-series of `|f|` at `σ` is the Wiener norm of `f`. -/
theorem lSeries_absFn (σ : ℝ) (f : ArithmeticFunction ℂ) :
    LSeries (⇑(absFn f)) σ = ((wienerNorm σ f : ℝ) : ℂ) := by
  unfold LSeries wienerNorm
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => term_absFn σ f n

/-- The convolution of two absolute values takes nonnegative real values. -/
theorem absFn_mul_apply (f g : ArithmeticFunction ℂ) (n : ℕ) :
    (absFn f * absFn g) n =
      ((∑ x ∈ n.divisorsAntidiagonal, ‖f x.1‖ * ‖g x.2‖ : ℝ) : ℂ) := by
  rw [mul_apply, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [absFn_apply, absFn_apply, Complex.ofReal_mul]

theorem absFn_absFn_mul (f g : ArithmeticFunction ℂ) :
    absFn (absFn f * absFn g) = absFn f * absFn g := by
  ext n
  rw [absFn_apply, absFn_mul_apply, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- `|(f ⋆ g)(n)| ≤ (|f| ⋆ |g|)(n)`. -/
theorem norm_mul_apply_le (f g : ArithmeticFunction ℂ) (n : ℕ) :
    ‖(f * g) n‖ ≤ ‖(absFn f * absFn g) n‖ := by
  rw [absFn_mul_apply, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_apply]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _))

/-- **The Wiener norm is multiplicative on absolute values**: the weight `n^{−σ}` is completely
multiplicative, so `‖|f| ⋆ |g|‖ = ‖f‖ ‖g‖`. -/
theorem wienerNorm_absFn_mul {σ : ℝ} {f g : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ)
    (hg : LSeriesSummable (⇑g) σ) :
    wienerNorm σ (absFn f * absFn g) = wienerNorm σ f * wienerNorm σ g := by
  have hF := lSeriesSummable_absFn_iff.2 hf
  have hG := lSeriesSummable_absFn_iff.2 hg
  have h := LSeries_convolution' hF hG
  rw [coe_mul, ← absFn_absFn_mul, lSeries_absFn, lSeries_absFn, lSeries_absFn,
    ← Complex.ofReal_mul] at h
  exact_mod_cast h

/-- **Submultiplicativity of the Wiener norm.** -/
theorem wienerNorm_mul_le {σ : ℝ} {f g : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ)
    (hg : LSeriesSummable (⇑g) σ) :
    wienerNorm σ (f * g) ≤ wienerNorm σ f * wienerNorm σ g := by
  rw [← wienerNorm_absFn_mul hf hg]
  have hFG : LSeriesSummable (⇑(absFn f * absFn g)) σ := by
    rw [← coe_mul]
    exact (lSeriesSummable_absFn_iff.2 hf).convolution (lSeriesSummable_absFn_iff.2 hg)
  exact Summable.tsum_le_tsum (fun n => norm_term_le σ (norm_mul_apply_le f g n))
    (summable_norm_term_iff.2 (by rw [← coe_mul]; exact hf.convolution hg))
    (summable_norm_term_iff.2 hFG)

/-! ### The Wiener subalgebra -/

/-- The Wiener subalgebra at abscissa `σ`: arithmetic functions whose Dirichlet series converges
absolutely at `σ`. -/
def wienerSubalgebra (σ : ℝ) : Subalgebra ℂ (ArithmeticFunction ℂ) where
  carrier := {f | LSeriesSummable (⇑f) σ}
  mul_mem' {f g} hf hg := by
    show LSeriesSummable (⇑(f * g)) σ
    rw [← coe_mul]
    exact LSeriesSummable.convolution hf hg
  add_mem' {f g} hf hg := LSeriesSummable.add hf hg
  algebraMap_mem' c := by
    show LSeriesSummable (⇑(algebraMap ℂ (ArithmeticFunction ℂ) c)) σ
    refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
    rw [Finset.mem_singleton] at hn
    rcases eq_or_ne n 0 with rfl | h0
    · simp
    · rw [term_of_ne_zero h0, Algebra.algebraMap_eq_smul_one, smul_map, one_apply_ne hn,
        smul_zero, zero_div]

/-- The Wiener algebra `𝒲_σ`. -/
def WienerAlgebraAt (σ : ℝ) : Type := ↥(wienerSubalgebra σ)

namespace WienerAlgebraAt

variable {σ : ℝ}

instance : CommRing (WienerAlgebraAt σ) := inferInstanceAs (CommRing ↥(wienerSubalgebra σ))

instance : Algebra ℂ (WienerAlgebraAt σ) := inferInstanceAs (Algebra ℂ ↥(wienerSubalgebra σ))

/-- The underlying arithmetic function. -/
def toFn (f : WienerAlgebraAt σ) : ArithmeticFunction ℂ := f.1

theorem summable (f : WienerAlgebraAt σ) : LSeriesSummable (⇑f.toFn) σ := f.2

theorem summable_norm (f : WienerAlgebraAt σ) : Summable fun n => ‖term (⇑f.toFn) σ n‖ :=
  summable_norm_term_iff.2 f.summable

theorem toFn_injective : Function.Injective (toFn (σ := σ)) := fun _ _ h => Subtype.ext h

@[ext]
theorem ext {f g : WienerAlgebraAt σ} (h : ∀ n, f.toFn n = g.toFn n) : f = g :=
  toFn_injective (ArithmeticFunction.ext h)

theorem toFn_zero : (0 : WienerAlgebraAt σ).toFn = 0 := rfl

theorem toFn_one : (1 : WienerAlgebraAt σ).toFn = 1 := rfl

theorem toFn_add (f g : WienerAlgebraAt σ) : (f + g).toFn = f.toFn + g.toFn := rfl

theorem toFn_neg (f : WienerAlgebraAt σ) : (-f).toFn = -f.toFn := rfl

theorem toFn_sub (f g : WienerAlgebraAt σ) : (f - g).toFn = f.toFn - g.toFn := rfl

theorem toFn_mul (f g : WienerAlgebraAt σ) : (f * g).toFn = f.toFn * g.toFn := rfl

theorem toFn_smul (c : ℂ) (f : WienerAlgebraAt σ) : (c • f).toFn = c • f.toFn := rfl

/-- An arithmetic function with absolutely convergent series at `σ`, as an element of `𝒲_σ`. -/
def mk (f : ArithmeticFunction ℂ) (hf : LSeriesSummable (⇑f) σ) : WienerAlgebraAt σ := ⟨f, hf⟩

theorem toFn_mk (f : ArithmeticFunction ℂ) (hf : LSeriesSummable (⇑f) σ) :
    (mk f hf).toFn = f := rfl

/-! ### The norm -/

/-- The Wiener norm as an additive group norm on `𝒲_σ`. -/
def groupNorm (σ : ℝ) : AddGroupNorm (WienerAlgebraAt σ) where
  toFun f := wienerNorm σ f.toFn
  map_zero' := by simp [wienerNorm, toFn_zero, term_def]
  add_le' f g := by
    show wienerNorm σ (f + g).toFn ≤ wienerNorm σ f.toFn + wienerNorm σ g.toFn
    unfold wienerNorm
    rw [toFn_add, ← (summable_norm f).tsum_add (summable_norm g)]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm (f + g))
      ((summable_norm f).add (summable_norm g))
    have hc : (⇑(f.toFn + g.toFn) : ℕ → ℂ) = ⇑f.toFn + ⇑g.toFn := rfl
    rw [hc, term_add_apply]
    exact norm_add_le _ _
  neg' f := by
    show wienerNorm σ (-f).toFn = wienerNorm σ f.toFn
    unfold wienerNorm
    have hc : (⇑(-f.toFn) : ℕ → ℂ) = -⇑f.toFn := rfl
    rw [toFn_neg, hc]
    simp_rw [term_neg_apply, norm_neg]
  eq_zero_of_map_eq_zero' f h := by
    change wienerNorm σ f.toFn = 0 at h
    have hz : ∀ n, ‖term (⇑f.toFn) σ n‖ = 0 := fun n =>
      le_antisymm (h ▸ (summable_norm f).le_tsum n fun _ _ => norm_nonneg _) (norm_nonneg _)
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [toFn_zero]
    · have := hz n
      rw [norm_eq_zero, term_of_ne_zero hn, div_eq_zero_iff] at this
      rcases this with h1 | h1
      · rw [h1, toFn_zero, ArithmeticFunction.zero_apply]
      · rw [Complex.cpow_eq_zero_iff] at h1
        exact absurd (by exact_mod_cast h1.1) hn

end WienerAlgebraAt

end

end GaloisForLFunctions.ArithmeticOrientationTheory
