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

instance : NormedAddCommGroup (WienerAlgebraAt σ) := (groupNorm σ).toNormedAddCommGroup

theorem norm_def (f : WienerAlgebraAt σ) : ‖f‖ = wienerNorm σ f.toFn := rfl

instance : NormedCommRing (WienerAlgebraAt σ) :=
  { (inferInstance : CommRing (WienerAlgebraAt σ)),
    (inferInstance : NormedAddCommGroup (WienerAlgebraAt σ)) with
    norm_mul_le := fun f g => by
      rw [norm_def, norm_def, norm_def, toFn_mul]
      exact wienerNorm_mul_le f.summable g.summable }

instance : NormedAlgebra ℂ (WienerAlgebraAt σ) :=
  { (inferInstance : Algebra ℂ (WienerAlgebraAt σ)) with
    norm_smul_le := fun c f => by
      rw [norm_def, norm_def, toFn_smul, wienerNorm, wienerNorm, ← tsum_mul_left]
      refine le_of_eq (tsum_congr fun n => ?_)
      have hc : (⇑(c • f.toFn) : ℕ → ℂ) = c • ⇑f.toFn := rfl
      rw [hc, term_smul_apply, norm_mul] }

/-- The term of the unit `δ₁` is `δ₁`. -/
theorem term_one (n : ℕ) : term (⇑(1 : ArithmeticFunction ℂ)) σ n = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, one_apply]
    split_ifs with h
    · subst h; simp
    · exact zero_div _

instance : NormOneClass (WienerAlgebraAt σ) where
  norm_one := by
    rw [norm_def, toFn_one, wienerNorm, tsum_eq_single 1]
    · rw [term_one, if_pos rfl, norm_one]
    · intro n hn
      rw [term_one, if_neg hn, norm_zero]

/-! ### Completeness through the weight isometry -/

/-- The weighted coordinates `k ↦ f(k+1) (k+1)^{−σ}` as an element of `ℓ¹`. -/
def toLp (f : WienerAlgebraAt σ) : lp (fun _ : ℕ => ℂ) 1 :=
  ⟨fun k => term (⇑f.toFn) σ (k + 1), by
    refine memℓp_gen ?_
    simp only [ENNReal.toReal_one, Real.rpow_one]
    exact (summable_nat_add_iff 1).2 (summable_norm f)⟩

theorem toLp_apply (f : WienerAlgebraAt σ) (k : ℕ) :
    (toLp f : ℕ → ℂ) k = term (⇑f.toFn) σ (k + 1) := rfl

theorem norm_lp_one (x : lp (fun _ : ℕ => ℂ) 1) : ‖x‖ = ∑' k, ‖(x : ℕ → ℂ) k‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

theorem norm_toLp (f : WienerAlgebraAt σ) : ‖toLp f‖ = ‖f‖ := by
  rw [norm_lp_one, norm_def, wienerNorm, (summable_norm f).tsum_eq_zero_add]
  simp [toLp_apply]

theorem toLp_sub (f g : WienerAlgebraAt σ) : toLp (f - g) = toLp f - toLp g := by
  refine lp.ext (funext fun k => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, toLp_apply, toLp_apply, toLp_apply, toFn_sub]
  have hc : (⇑(f.toFn - g.toFn) : ℕ → ℂ) = ⇑f.toFn - ⇑g.toFn := rfl
  rw [hc, term_sub_apply]

/-- The arithmetic function `n ↦ x(n−1) n^σ` of an `ℓ¹` sequence. -/
def ofLpFn (x : lp (fun _ : ℕ => ℂ) 1) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (x : ℕ → ℂ) (n - 1) * (n : ℂ) ^ (σ : ℂ), by simp⟩

theorem term_ofLpFn (x : lp (fun _ : ℕ => ℂ) 1) (k : ℕ) :
    term (⇑(ofLpFn (σ := σ) x)) σ (k + 1) = (x : ℕ → ℂ) k := by
  rw [term_of_ne_zero k.succ_ne_zero]
  show (if k + 1 = 0 then 0 else (x : ℕ → ℂ) (k + 1 - 1) * ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ)) /
    ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ) = _
  rw [if_neg k.succ_ne_zero, Nat.add_sub_cancel, mul_div_cancel_right₀]
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => k.succ_ne_zero (by exact_mod_cast h.1)

theorem summable_ofLpFn (x : lp (fun _ : ℕ => ℂ) 1) :
    LSeriesSummable (⇑(ofLpFn (σ := σ) x)) σ := by
  rw [← summable_norm_term_iff, ← summable_nat_add_iff 1]
  simp_rw [term_ofLpFn]
  have hmem := (memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp x)
  simpa [ENNReal.toReal_one, Real.rpow_one] using hmem

/-- The inverse of the weight isometry. -/
def ofLp (x : lp (fun _ : ℕ => ℂ) 1) : WienerAlgebraAt σ := mk (ofLpFn x) (summable_ofLpFn x)

theorem toLp_ofLp (x : lp (fun _ : ℕ => ℂ) 1) : toLp (ofLp (σ := σ) x) = x :=
  lp.ext (funext fun k => term_ofLpFn x k)

theorem ofLp_toLp (f : WienerAlgebraAt σ) : ofLp (toLp f) = f := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    show (if k + 1 = 0 then 0 else (toLp f : ℕ → ℂ) (k + 1 - 1) * ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ)) = _
    rw [if_neg k.succ_ne_zero, Nat.add_sub_cancel, toLp_apply, mul_comm]
    exact_mod_cast pow_mul_term_eq (⇑f.toFn) σ k

/-- **The weight isometry**: `𝒲_σ` and `ℓ¹(ℕ)` are isometric. -/
def isometryLp (σ : ℝ) : WienerAlgebraAt σ ≃ᵢ lp (fun _ : ℕ => ℂ) 1 where
  toFun := toLp
  invFun := ofLp
  left_inv := ofLp_toLp
  right_inv := toLp_ofLp
  isometry_toFun := by
    refine Isometry.of_dist_eq fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, ← toLp_sub, norm_toLp]

/-- **`𝒲_σ` is a Banach algebra.** -/
instance : CompleteSpace (WienerAlgebraAt σ) := by
  haveI : Fact ((1 : ENNReal) ≤ 1) := ⟨le_refl _⟩
  exact (isometryLp σ).completeSpace_iff.mpr inferInstance

/-! ### Point masses -/

/-- The point mass `δ_n` (zero for `n = 0`). -/
def pointMassFn (n : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun m => if m ≠ 0 ∧ m = n then 1 else 0, by simp⟩

theorem pointMassFn_apply (n m : ℕ) : pointMassFn n m = if m ≠ 0 ∧ m = n then 1 else 0 := rfl

theorem term_pointMassFn {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    term (⇑(pointMassFn n)) σ m = if m = n then 1 / (n : ℂ) ^ (σ : ℂ) else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hn.symm]
  · rw [term_of_ne_zero hm, pointMassFn_apply]
    by_cases h : m = n
    · subst h; simp [hm]
    · simp [h]

theorem summable_pointMassFn (n : ℕ) : LSeriesSummable (⇑(pointMassFn n)) σ := by
  rcases eq_or_ne n 0 with rfl | hn
  · refine summable_of_ne_finset_zero (s := ∅) fun m _ => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [term_of_ne_zero hm, pointMassFn_apply, if_neg (fun h => hm h.2), zero_div]
  · refine summable_of_ne_finset_zero (s := {n}) fun m hm => ?_
    rw [Finset.mem_singleton] at hm
    rw [term_pointMassFn hn, if_neg hm]

/-- The point mass `δ_n` in `𝒲_σ`. -/
def pointMass (n : ℕ) : WienerAlgebraAt σ := mk (pointMassFn n) (summable_pointMassFn n)

theorem toFn_pointMass (n : ℕ) : (pointMass (σ := σ) n).toFn = pointMassFn n := rfl

/-- `‖δ_n‖ = n^{−σ}`. -/
theorem norm_pointMass {n : ℕ} (hn : n ≠ 0) : ‖(pointMass n : WienerAlgebraAt σ)‖ = (n : ℝ) ^ (-σ) := by
  rw [norm_def, toFn_pointMass, wienerNorm, tsum_eq_single n]
  · rw [term_pointMassFn hn, if_pos rfl, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos
      (Nat.pos_of_ne_zero hn), Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), one_div]
  · intro m hm
    rw [term_pointMassFn hn, if_neg hm, norm_zero]

theorem pointMass_one : (pointMass 1 : WienerAlgebraAt σ) = 1 := by
  ext m
  rw [toFn_pointMass, pointMassFn_apply, toFn_one, one_apply]
  by_cases h : m = 1
  · simp [h]
  · simp [h]

/-- **Point masses multiply**: `δ_m δ_n = δ_{mn}`. -/
theorem pointMassFn_mul (m n : ℕ) : pointMassFn m * pointMassFn n = pointMassFn (m * n) := by
  ext k
  rw [mul_apply, pointMassFn_apply]
  by_cases hk : k ≠ 0 ∧ k = m * n
  · rw [if_pos hk, Finset.sum_eq_single (m, n)]
    · obtain ⟨hk0, rfl⟩ := hk
      have hm : m ≠ 0 := left_ne_zero_of_mul hk0
      have hn : n ≠ 0 := right_ne_zero_of_mul hk0
      simp [pointMassFn_apply, hm, hn]
    · rintro ⟨a, b⟩ _ hab
      simp only [pointMassFn_apply]
      split_ifs with h1 h2 <;> simp_all
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨hk.2.symm, hk.1⟩) h
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    simp only [pointMassFn_apply]
    split_ifs with h1 h2
    · exact absurd ⟨hx.2, by rw [← hx.1, h1.2, h2.2]⟩ hk
    all_goals simp

theorem pointMass_mul (m n : ℕ) :
    (pointMass m * pointMass n : WienerAlgebraAt σ) = pointMass (m * n) :=
  toFn_injective (pointMassFn_mul m n)

/-- The weight isometry sends a point mass of `ℓ¹` to a scaled point mass. -/
theorem ofLp_single (k : ℕ) (c : ℂ) :
    ofLp (σ := σ) (lp.single 1 k c) = (c * ((k + 1 : ℕ) : ℂ) ^ (σ : ℂ)) • pointMass (k + 1) := by
  ext n
  rw [toFn_smul, smul_map, toFn_pointMass, pointMassFn_apply, smul_eq_mul]
  show (if n = 0 then 0 else ((lp.single 1 k c : lp (fun _ : ℕ => ℂ) 1) : ℕ → ℂ) (n - 1) *
    (n : ℂ) ^ (σ : ℂ)) = _
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, lp.single_apply]
    by_cases h : n - 1 = k
    · have : n = k + 1 := by omega
      subst this
      simp
    · have : ¬ (n ≠ 0 ∧ n = k + 1) := fun h' => h (by omega)
      rw [Pi.single_apply, if_neg h, if_neg this]
      simp

/-- The inverse weight isometry as an additive map. -/
def ofLpHom : lp (fun _ : ℕ => ℂ) 1 →+ WienerAlgebraAt σ where
  toFun := ofLp
  map_zero' := by
    rw [← (isometryLp σ).symm_apply_apply 0]
    show ofLp 0 = ofLp (toLp 0)
    congr 1
    refine lp.ext (funext fun k => ?_)
    simp [toLp_apply, toFn_zero]
  map_add' x y := by
    apply (isometryLp σ).injective
    show toLp (ofLp (x + y)) = toLp (ofLp x + ofLp y)
    rw [toLp_ofLp]
    refine lp.ext (funext fun k => ?_)
    rw [lp.coeFn_add, Pi.add_apply, toLp_apply, toFn_add]
    have hc : (⇑((ofLp (σ := σ) x).toFn + (ofLp (σ := σ) y).toFn) : ℕ → ℂ) =
        ⇑(ofLp (σ := σ) x).toFn + ⇑(ofLp (σ := σ) y).toFn := rfl
    rw [hc, term_add_apply, ← toLp_apply, ← toLp_apply, toLp_ofLp, toLp_ofLp]

theorem continuous_ofLpHom : Continuous (ofLpHom (σ := σ)) := (isometryLp σ).symm.continuous

/-- **Every element is the norm-convergent series of its point masses**:
`f = Σ_n f(n) δ_n` in `𝒲_σ`. -/
theorem hasSum_pointMass (f : WienerAlgebraAt σ) :
    HasSum (fun n => f.toFn n • (pointMass n : WienerAlgebraAt σ)) f := by
  haveI : Fact ((1 : ENNReal) ≤ 1) := ⟨le_refl _⟩
  have h := (lp.hasSum_single (E := fun _ : ℕ => ℂ) ENNReal.one_ne_top (toLp f)).map
    (ofLpHom (σ := σ)) continuous_ofLpHom
  have h1 : (⇑(ofLpHom (σ := σ)) ∘ fun k => lp.single 1 k ((toLp f : ℕ → ℂ) k)) =
      fun k => f.toFn (k + 1) • (pointMass (k + 1) : WienerAlgebraAt σ) := by
    funext k
    show ofLp _ = _
    rw [ofLp_single, toLp_apply, mul_comm]
    congr 1
    exact_mod_cast pow_mul_term_eq (⇑f.toFn) σ k
  rw [h1] at h
  have h2 : ofLpHom (σ := σ) (toLp f) = f := ofLp_toLp f
  rw [h2] at h
  have h0 : f.toFn 0 • (pointMass 0 : WienerAlgebraAt σ) = 0 := by simp
  rw [← hasSum_nat_add_iff' 1]
  simpa [h0] using h

end WienerAlgebraAt

end

end GaloisForLFunctions.ArithmeticOrientationTheory
