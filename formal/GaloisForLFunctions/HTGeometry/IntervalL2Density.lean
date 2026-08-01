import GaloisForLFunctions.HTGeometry.CompactIntervalL2Pairing
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Density in `L²` of a compact interval

Towards a countable Hilbert basis of `L²[-a,a]`, which mathlib does not provide: it has no
separability instance for `Lp` at all, and no isometry identifying `L²` of an interval with `L²` of
the circle where the Fourier basis lives.

The first step is density of the bounded continuous functions.  The measure is the restriction of
Lebesgue measure to a compact interval, so it is finite and weakly regular, which is exactly what
mathlib's density theorem needs — no compactness of the ambient space is required.

The `L²` norm of a bounded continuous function is controlled by its supremum norm times the square
root of the total mass, so uniform approximation on the interval suffices to approximate in `L²`.
This is what will let Stone–Weierstrass supply a countable total family.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-- The measure of a compact symmetric interval is finite. -/
theorem intervalL2_measure_ne_top (a : ℝ) :
    (volume.restrict (Set.Icc (-a) a)) Set.univ ≠ ⊤ := by
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- **The bounded continuous functions are dense in `L²` of a compact interval.**  The restricted
Lebesgue measure is finite and weakly regular, which is all mathlib's density theorem requires. -/
theorem denseRange_boundedContinuousToIntervalL2 (a : ℝ) :
    DenseRange (BoundedContinuousFunction.toLp (E := ℂ) 2
      (volume.restrict (Set.Icc (-a) a)) ℂ) :=
  BoundedContinuousFunction.toLp_denseRange _ _ ℂ (by norm_num)

/-- Every element of `L²` of the interval is a limit of bounded continuous functions. -/
theorem exists_boundedContinuous_close (a : ℝ) (f : IntervalL2 a) {eps : ℝ} (heps : 0 < eps) :
    ∃ g : BoundedContinuousFunction ℝ ℂ,
      ‖BoundedContinuousFunction.toLp (E := ℂ) 2 (volume.restrict (Set.Icc (-a) a)) ℂ g - f‖
        < eps := by
  obtain ⟨y, hy, hclose⟩ :=
    Metric.mem_closure_iff.mp
      ((denseRange_boundedContinuousToIntervalL2 a).closure_eq ▸ Set.mem_univ f) eps heps
  obtain ⟨g, hg⟩ := hy
  refine ⟨g, ?_⟩
  rw [hg, ← dist_eq_norm, dist_comm]
  exact hclose

/-! ## Sup-norm control of the `L²` norm

On a finite measure the `L²` norm is dominated by the supremum norm times the square root of the
total mass.  So uniform approximation on the interval gives approximation in `L²`, which is how
Stone–Weierstrass will supply a countable total family. -/

/-- **Uniform closeness on the interval implies `L²` closeness.** -/
theorem norm_toIntervalL2_sub_le (a : ℝ) {w v : ℝ → ℂ} (hw : Continuous w) (hv : Continuous v)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ Set.Icc (-a) a, ‖w x - v x‖ ≤ C) :
    ‖toIntervalL2 a hw - toIntervalL2 a hv‖
      ≤ (measureUnivNNReal (volume.restrict (Set.Icc (-a) a)) : ℝ)
          ^ ((2 : ENNReal).toReal)⁻¹ * C := by
  refine Lp.norm_le_of_ae_bound hC ?_
  have hcoe : ((toIntervalL2 a hw - toIntervalL2 a hv : IntervalL2 a) : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Icc (-a) a)] fun x => w x - v x := by
    filter_upwards [Lp.coeFn_sub (toIntervalL2 a hw) (toIntervalL2 a hv),
      (memLp_two_of_continuous a hw).coeFn_toLp,
      (memLp_two_of_continuous a hv).coeFn_toLp] with x h1 h2 h3
    have hsub : ((toIntervalL2 a hw - toIntervalL2 a hv : IntervalL2 a) : ℝ → ℂ) x
        = (toIntervalL2 a hw : ℝ → ℂ) x - (toIntervalL2 a hv : ℝ → ℂ) x := by
      rw [h1]; rfl
    rw [hsub, show (toIntervalL2 a hw : ℝ → ℂ) x = w x from h2,
      show (toIntervalL2 a hv : ℝ → ℂ) x = v x from h3]
  filter_upwards [hcoe, ae_restrict_mem measurableSet_Icc] with x hx hmem
  rw [hx]
  exact h x hmem

/-! ## Polynomial approximation of complex functions on the interval

Weierstrass approximation is available for real-valued functions.  A complex-valued continuous
function is approximated by splitting into real and imaginary parts and approximating each, so no
complex Stone–Weierstrass is needed: the real monomials already span enough. -/

/-- **Uniform polynomial approximation of a complex continuous function on the interval.**  The
approximant is `p + i q` with `p`, `q` real polynomials. -/
theorem exists_complexPolynomial_near (a : ℝ) {w : ℝ → ℂ} (hw : Continuous w)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ p q : Polynomial ℝ, ∀ x ∈ Set.Icc (-a) a,
      ‖w x - (((Polynomial.eval x p : ℝ) : ℂ)
        + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))‖ < eps := by
  have hre : ContinuousOn (fun x => (w x).re) (Set.Icc (-a) a) :=
    (Complex.continuous_re.comp hw).continuousOn
  have him : ContinuousOn (fun x => (w x).im) (Set.Icc (-a) a) :=
    (Complex.continuous_im.comp hw).continuousOn
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (-a) a _ hre (eps / 2) (by linarith)
  obtain ⟨q, hq⟩ :=
    exists_polynomial_near_of_continuousOn (-a) a _ him (eps / 2) (by linarith)
  refine ⟨p, q, fun x hx => ?_⟩
  have hbound := Complex.norm_le_abs_re_add_abs_im
    (w x - (((Polynomial.eval x p : ℝ) : ℂ) + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ)))
  have hre' : (w x - (((Polynomial.eval x p : ℝ) : ℂ)
      + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))).re
      = (w x).re - Polynomial.eval x p := by simp
  have him' : (w x - (((Polynomial.eval x p : ℝ) : ℂ)
      + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))).im
      = (w x).im - Polynomial.eval x q := by simp
  rw [hre', him'] at hbound
  have h1 : |(w x).re - Polynomial.eval x p| < eps / 2 := by
    rw [abs_sub_comm]
    exact hp x hx
  have h2 : |(w x).im - Polynomial.eval x q| < eps / 2 := by
    rw [abs_sub_comm]
    exact hq x hx
  linarith

/-! ## The monomials as a total family

The polynomial approximants are complex combinations of real monomials, so the closed span of the
monomials in `L²` contains every polynomial function.  With the approximation results above this
makes the monomials a countable total family. -/

theorem continuous_ofReal_polynomial (p : Polynomial ℝ) :
    Continuous fun x : ℝ => ((Polynomial.eval x p : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp p.continuous

/-- The `n`-th monomial as an element of `L²` of the interval. -/
def monomialL2 (a : ℝ) (n : ℕ) : IntervalL2 a :=
  toIntervalL2 a (continuous_ofReal_polynomial (Polynomial.X ^ n))

/-- A real polynomial as an element of `L²` of the interval. -/
def polyToL2 (a : ℝ) (p : Polynomial ℝ) : IntervalL2 a :=
  toIntervalL2 a (continuous_ofReal_polynomial p)

/-- `toIntervalL2` depends only on the function, not on the continuity proof. -/
theorem toIntervalL2_congr (a : ℝ) {w v : ℝ → ℂ} (hw : Continuous w) (hv : Continuous v)
    (h : w = v) : toIntervalL2 a hw = toIntervalL2 a hv := by
  subst h
  rfl

theorem polyToL2_add (a : ℝ) (p q : Polynomial ℝ) :
    polyToL2 a (p + q) = polyToL2 a p + polyToL2 a q := by
  have hmem : ∀ r : Polynomial ℝ, MemLp (fun x : ℝ => ((Polynomial.eval x r : ℝ) : ℂ)) 2
      (volume.restrict (Set.Icc (-a) a)) :=
    fun r => memLp_two_of_continuous a (continuous_ofReal_polynomial r)
  unfold polyToL2 toIntervalL2
  rw [← MemLp.toLp_add (hmem p) (hmem q)]
  congr 1
  funext x
  simp

theorem polyToL2_smul (a : ℝ) (c : ℝ) (p : Polynomial ℝ) :
    polyToL2 a (Polynomial.C c * p) = (c : ℂ) • polyToL2 a p := by
  have hmem : MemLp (fun x : ℝ => ((Polynomial.eval x p : ℝ) : ℂ)) 2
      (volume.restrict (Set.Icc (-a) a)) :=
    memLp_two_of_continuous a (continuous_ofReal_polynomial p)
  unfold polyToL2 toIntervalL2
  rw [← MemLp.toLp_const_smul (c := (c : ℂ)) hmem]
  congr 1
  funext x
  simp

/-- **Every polynomial's `L²` element lies in the span of the monomials.** -/
theorem polyToL2_mem_span (a : ℝ) (p : Polynomial ℝ) :
    polyToL2 a p ∈ Submodule.span ℂ (Set.range (monomialL2 a)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [polyToL2_add]
      exact Submodule.add_mem _ hp hq
  | monomial n c =>
      have hmon : (Polynomial.monomial n c : Polynomial ℝ) = Polynomial.C c * Polynomial.X ^ n := by
        simp [Polynomial.C_mul_X_pow_eq_monomial]
      rw [hmon, polyToL2_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-! ## Density of the monomial span

Assembling the four steps: bounded continuous functions are dense, each is uniformly approximable by
a complex polynomial on the interval, uniform closeness gives `L²` closeness, and polynomials lie in
the span of the monomials. -/

/-- The two ways of sending a bounded continuous function into `L²` agree. -/
theorem bcfToLp_eq_toIntervalL2 (a : ℝ) (g : BoundedContinuousFunction ℝ ℂ) :
    BoundedContinuousFunction.toLp (E := ℂ) 2 (volume.restrict (Set.Icc (-a) a)) ℂ g
      = toIntervalL2 a g.continuous := by
  rw [Lp.ext_iff]
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (E := ℂ) 2
      (volume.restrict (Set.Icc (-a) a)) ℂ g,
    (memLp_two_of_continuous a g.continuous).coeFn_toLp] with x h1 h2
  rw [h1]
  exact (show (toIntervalL2 a g.continuous : ℝ → ℂ) x = g x from h2).symm

/-- The `L²` element of `p + i q` is the corresponding combination of the polynomial elements. -/
theorem toIntervalL2_complexPoly (a : ℝ) (p q : Polynomial ℝ)
    (hc : Continuous fun x : ℝ => ((Polynomial.eval x p : ℝ) : ℂ)
      + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ)) :
    toIntervalL2 a hc = polyToL2 a p + Complex.I • polyToL2 a q := by
  have hmemp : MemLp (fun x : ℝ => ((Polynomial.eval x p : ℝ) : ℂ)) 2
      (volume.restrict (Set.Icc (-a) a)) :=
    memLp_two_of_continuous a (continuous_ofReal_polynomial p)
  have hmemq : MemLp (fun x : ℝ => ((Polynomial.eval x q : ℝ) : ℂ)) 2
      (volume.restrict (Set.Icc (-a) a)) :=
    memLp_two_of_continuous a (continuous_ofReal_polynomial q)
  unfold polyToL2 toIntervalL2
  rw [← MemLp.toLp_const_smul (c := Complex.I) hmemq,
    ← MemLp.toLp_add hmemp (hmemq.const_smul Complex.I)]
  congr 1

/-- **The span of the monomials is dense in `L²` of the interval.**  The monomials are therefore a
countable total family, which is what a Hilbert basis is built from. -/
theorem dense_span_monomialL2 (a : ℝ) :
    Dense ((Submodule.span ℂ (Set.range (monomialL2 a)) : Submodule ℂ (IntervalL2 a)) :
      Set (IntervalL2 a)) := by
  rw [Metric.dense_iff]
  intro f eps heps
  set M : ℝ := (measureUnivNNReal (volume.restrict (Set.Icc (-a) a)) : ℝ)
      ^ ((2 : ENNReal).toReal)⁻¹ with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  obtain ⟨g, hg⟩ := exists_boundedContinuous_close a f (by linarith : (0:ℝ) < eps / 2)
  set delta : ℝ := (eps / 2) / (M + 1) with hdelta
  have hdpos : 0 < delta := by
    apply div_pos (by linarith)
    linarith
  obtain ⟨p, q, hpq⟩ := exists_complexPolynomial_near a g.continuous hdpos
  have hclose : ‖toIntervalL2 a g.continuous
      - toIntervalL2 a (by fun_prop :
        Continuous fun x : ℝ => ((Polynomial.eval x p : ℝ) : ℂ)
          + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))‖ ≤ M * delta := by
    refine norm_toIntervalL2_sub_le a _ _ hdpos.le ?_
    intro x hx
    exact (hpq x hx).le
  have hMd : M * delta < eps / 2 := by
    rw [hdelta]
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨polyToL2 a p + Complex.I • polyToL2 a q, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    calc ‖polyToL2 a p + Complex.I • polyToL2 a q - f‖
        = ‖(toIntervalL2 a (by fun_prop :
              Continuous fun x : ℝ => ((Polynomial.eval x p : ℝ) : ℂ)
                + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))
            - toIntervalL2 a g.continuous)
          + (toIntervalL2 a g.continuous - f)‖ := by
            rw [toIntervalL2_complexPoly a p q]
            congr 1
            abel
      _ ≤ ‖toIntervalL2 a (by fun_prop :
              Continuous fun x : ℝ => ((Polynomial.eval x p : ℝ) : ℂ)
                + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))
            - toIntervalL2 a g.continuous‖
          + ‖toIntervalL2 a g.continuous - f‖ := norm_add_le _ _
      _ < eps := by
            rw [norm_sub_rev]
            rw [bcfToLp_eq_toIntervalL2 a g] at hg
            linarith [hclose, hMd, hg]
  · exact Submodule.add_mem _ (polyToL2_mem_span a p)
      (Submodule.smul_mem _ _ (polyToL2_mem_span a q))

/-! ## Injectivity of the polynomial map

A complex polynomial that vanishes almost everywhere on a nondegenerate interval is zero: its root
set would otherwise be finite, hence null, forcing the interval to be null.  So the map sending a
polynomial to its `L²` element is injective, which is what makes the monomials linearly
independent. -/

theorem continuous_cpoly (P : Polynomial ℂ) :
    Continuous fun x : ℝ => Polynomial.eval (x : ℂ) P :=
  P.continuous.comp Complex.continuous_ofReal

/-- A complex polynomial as an element of `L²` of the interval, as a linear map. -/
def cpolyToL2 (a : ℝ) : Polynomial ℂ →ₗ[ℂ] IntervalL2 a where
  toFun P := (memLp_two_of_continuous a (continuous_cpoly P)).toLp _
  map_add' P Q := by
    rw [← MemLp.toLp_add]
    congr 1
    funext x
    simp
  map_smul' c P := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1
    funext x
    simp

/-- **The polynomial map into `L²` is injective on a nondegenerate interval.** -/
theorem cpolyToL2_injective (a : ℝ) (ha : 0 < a) :
    Function.Injective (cpolyToL2 a) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  by_contra hne
  have hzero : ((cpolyToL2 a P : IntervalL2 a) : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Icc (-a) a)] 0 := by
    rw [hP]
    exact Lp.coeFn_zero ℂ 2 _
  have hfun : (fun x : ℝ => Polynomial.eval (x : ℂ) P)
      =ᵐ[volume.restrict (Set.Icc (-a) a)] 0 :=
    ((memLp_two_of_continuous a (continuous_cpoly P)).coeFn_toLp).symm.trans hzero
  have hae := ae_iff.mp hfun
  have hsub : {x : ℝ | ¬ Polynomial.eval (x : ℂ) P = (0 : ℝ → ℂ) x}
      ⊇ {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)} := by
    intro x hx
    simpa [Polynomial.IsRoot] using hx
  have hroot : Set.Finite {z : ℂ | Polynomial.IsRoot P z} :=
    Polynomial.finite_setOf_isRoot hne
  have hrootReal : Set.Finite {x : ℝ | Polynomial.IsRoot P (x : ℂ)} := by
    refine Set.Finite.ofFinset (hroot.toFinset.preimage (fun x : ℝ => (x : ℂ))
      (Set.injOn_of_injective Complex.ofReal_injective)) ?_
    intro x
    simp [Set.Finite.mem_toFinset]
  have huniv : (volume.restrict (Set.Icc (-a) a)) Set.univ = 0 := by
    have h1 : (volume.restrict (Set.Icc (-a) a)) {x : ℝ | Polynomial.IsRoot P (x : ℂ)} = 0 :=
      hrootReal.measure_zero _
    have h2 : (volume.restrict (Set.Icc (-a) a))
        {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)} = 0 :=
      measure_mono_null hsub hae
    have hle := measure_union_le (μ := volume.restrict (Set.Icc (-a) a))
      {x : ℝ | Polynomial.IsRoot P (x : ℂ)} {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)}
    rw [h1, h2] at hle
    simp only [add_zero, nonpos_iff_eq_zero] at hle
    have hsetu : {x : ℝ | Polynomial.IsRoot P (x : ℂ)}
        ∪ {x : ℝ | ¬ Polynomial.IsRoot P (x : ℂ)} = Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      tauto
    rwa [hsetu] at hle
  rw [Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.ofReal_eq_zero] at huniv
  linarith

/-! ## Linear independence of the monomials

The monomials are a basis of `ℂ[X]`, and the polynomial map into `L²` is injective and linear, so
their `L²` images are linearly independent. -/

theorem cpolyToL2_X_pow (a : ℝ) (n : ℕ) :
    cpolyToL2 a (Polynomial.X ^ n) = monomialL2 a n := by
  unfold cpolyToL2 monomialL2 toIntervalL2
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  funext x
  simp

/-- **The monomials are linearly independent in `L²` of a nondegenerate interval.** -/
theorem linearIndependent_monomialL2 (a : ℝ) (ha : 0 < a) :
    LinearIndependent ℂ (monomialL2 a) := by
  have hX : LinearIndependent ℂ (fun n : ℕ => (Polynomial.X : Polynomial ℂ) ^ n) := by
    have hb := (Polynomial.basisMonomials ℂ).linearIndependent
    rw [Polynomial.coe_basisMonomials] at hb
    simpa [Polynomial.X_pow_eq_monomial] using hb
  have hmap := hX.map' (cpolyToL2 a)
    (LinearMap.ker_eq_bot.mpr (cpolyToL2_injective a ha))
  have hcomp : (⇑(cpolyToL2 a) ∘ fun n : ℕ => (Polynomial.X : Polynomial ℂ) ^ n)
      = monomialL2 a := by
    funext n
    exact cpolyToL2_X_pow a n
  rwa [hcomp] at hmap

/-! ## A countable Hilbert basis of `L²` of the interval

Gram–Schmidt turns the countable, linearly independent, total family of monomials into an
orthonormal one with the same span.  Orthonormality plus dense span is exactly `HilbertBasis.mk`.

mathlib has no separability instance for `Lp`, so this basis is not obtainable from the general
theory; it is built here from the monomials. -/

/-- **A countable Hilbert basis of `L²[-a,a]`**, obtained by Gram–Schmidt from the monomials. -/
def intervalL2Basis (a : ℝ) (ha : 0 < a) : HilbertBasis ℕ ℂ (IntervalL2 a) :=
  HilbertBasis.mk
    (InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℂ) (linearIndependent_monomialL2 a ha))
    (by
      have hspan : Submodule.span ℂ (Set.range (InnerProductSpace.gramSchmidtNormed ℂ (monomialL2 a)))
          = Submodule.span ℂ (Set.range (monomialL2 a)) :=
        by rw [InnerProductSpace.span_gramSchmidtNormed_range (monomialL2 a),
          InnerProductSpace.span_gramSchmidt ℂ (monomialL2 a)]
      have hdense := Submodule.dense_iff_topologicalClosure_eq_top.mp
        (dense_span_monomialL2 a)
      rw [hspan, hdense])

@[simp] theorem intervalL2Basis_apply (a : ℝ) (ha : 0 < a) (n : ℕ) :
    intervalL2Basis a ha n = InnerProductSpace.gramSchmidtNormed ℂ (monomialL2 a) n := by
  have h := HilbertBasis.coe_mk
    (InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℂ) (linearIndependent_monomialL2 a ha))
    (v := InnerProductSpace.gramSchmidtNormed ℂ (monomialL2 a))
    (by
      have hspan : Submodule.span ℂ (Set.range (InnerProductSpace.gramSchmidtNormed ℂ (monomialL2 a)))
          = Submodule.span ℂ (Set.range (monomialL2 a)) :=
        by rw [InnerProductSpace.span_gramSchmidtNormed_range (monomialL2 a),
          InnerProductSpace.span_gramSchmidt ℂ (monomialL2 a)]
      have hdense := Submodule.dense_iff_topologicalClosure_eq_top.mp
        (dense_span_monomialL2 a)
      rw [hspan, hdense])
  exact congrFun h n

end GaloisForLFunctions.HTGeometry
