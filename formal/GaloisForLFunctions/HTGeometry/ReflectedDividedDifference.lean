import Mathlib

/-!
# Reflected removable divided differences

The first divided difference absorbs the two signs in an anti-reflection: one from the
numerator and one from reflection of the affine denominator.  The identity remains exact on
the diagonal because `dslope` uses the derivative there.  Applied to a two-variable numerator,
this says that an anti-invariant numerator has a reflection-invariant removable diagonal
quotient.

This is source-independent bridge infrastructure.  It is an elementary law of divided
differences, not a new hypertranscendence theorem.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- **Reflected divided-difference law.**  Simultaneous negation of the argument and anchor,
together with negation of the reflected function, leaves the removable divided difference
unchanged.  No differentiability hypothesis is needed: at the diagonal the two chain-rule signs
cancel, while away from it the two quotient signs cancel algebraically. -/
theorem dslope_neg_comp_neg (T : ℂ → ℂ) (a z : ℂ) :
    dslope (fun w => -T (-w)) (-a) z = dslope T a (-z) := by
  by_cases hz : z = -a
  · subst z
    rw [dslope_same, neg_neg, dslope_same]
    have hcomp := iteratedDeriv_comp_neg 1 T (-a)
    have hneg := iteratedDeriv_neg 1 (fun w : ℂ => T (-w)) (-a)
    rw [iteratedDeriv_one, iteratedDeriv_one] at hcomp
    rw [iteratedDeriv_one, iteratedDeriv_one] at hneg
    have hfun : (fun w : ℂ => -T (-w)) = -(fun w : ℂ => T (-w)) := rfl
    rw [hfun, hneg, hcomp]
    ring_nf
  · have hnz : -z ≠ a := by
      intro h
      apply hz
      simpa using congrArg Neg.neg h
    rw [dslope_of_ne _ hz, dslope_of_ne _ hnz,
      slope_def_module, slope_def_module]
    simp only [neg_neg, smul_eq_mul]
    have hden : -z - a = -(z - -a) := by ring
    have hnum : -T (-z) - -T a = -(T (-z) - T a) := by ring
    rw [hden, hnum, inv_neg]
    ring

/-- **Vector-valued divided-slope/Taylor-jet law.**  Over every complete characteristic-zero
normed field, `k!` times the center value after `k` removable divided slopes of an analytic map
into any complete normed space is its `k`-th derivative.  Thus the full divided-difference chain
is the normalized analytic jet, not merely at the first step. -/
theorem factorial_nsmul_iterate_dslope_self_eq_iteratedDeriv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {f : 𝕜 → E} {a : 𝕜} (hf : AnalyticAt 𝕜 f a) (k : ℕ) :
    k.factorial • (Function.swap dslope a)^[k] f a =
      iteratedDeriv k f a := by
  obtain ⟨p, hp⟩ := hf
  have hcenter : (Function.swap dslope a)^[k] f a = p.coeff k := by
    rw [← (hp.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1,
      ← FormalMultilinearSeries.coeff,
      FormalMultilinearSeries.coeff_iterate_fslope, zero_add]
  rw [hcenter]
  obtain ⟨r, hr⟩ := hp
  have hfac := hr.factorial_smul (1 : 𝕜) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  change k.factorial • p.coeff k = iteratedDeriv k f a at hfac
  exact hfac

/-- Scalar division form of the vector-valued divided-slope/Taylor-jet law. -/
theorem iterate_dslope_self_eq_iteratedDeriv_div_factorial
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
    {f : 𝕜 → 𝕜} {a : 𝕜} (hf : AnalyticAt 𝕜 f a) (k : ℕ) :
    (Function.swap dslope a)^[k] f a =
      iteratedDeriv k f a / (k.factorial : 𝕜) := by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr k.factorial_ne_zero)]
  simpa only [nsmul_eq_mul, mul_comm] using
    factorial_nsmul_iterate_dslope_self_eq_iteratedDeriv hf k

/-- **Removable-slope jet-shift law.**  The `k`-th center jet of the removable slope of an
analytic vector-valued map is its `(k + 1)`-st jet, with the exact factor `k + 1`.  This is the
one-step form of the full divided-difference/Taylor-jet law. -/
theorem succ_smul_iteratedDeriv_dslope_self
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {f : 𝕜 → E} {a : 𝕜} (hf : AnalyticAt 𝕜 f a) (k : ℕ) :
    (k + 1 : 𝕜) • iteratedDeriv k (dslope f a) a =
      iteratedDeriv (k + 1) f a := by
  obtain ⟨p, hp⟩ := hf
  have hg : AnalyticAt 𝕜 (dslope f a) a :=
    hp.has_fpower_series_dslope_fslope.analyticAt
  have hk := factorial_nsmul_iterate_dslope_self_eq_iteratedDeriv hg k
  have hk1 :=
    factorial_nsmul_iterate_dslope_self_eq_iteratedDeriv hp.analyticAt (k + 1)
  rw [← hk, ← hk1]
  have hiter :
      (Function.swap dslope a)^[k] (dslope f a) a =
        (Function.swap dslope a)^[k + 1] f a := by
    rw [Function.iterate_succ_apply]
  rw [hiter]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, ← Nat.cast_smul_eq_nsmul 𝕜,
    smul_smul, Nat.factorial_succ, Nat.cast_mul]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Scalar division form of the removable-slope jet-shift law. -/
theorem iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
    {f : 𝕜 → 𝕜} {a : 𝕜} (hf : AnalyticAt 𝕜 f a) (k : ℕ) :
    iteratedDeriv k (dslope f a) a =
      iteratedDeriv (k + 1) f a / (k + 1 : 𝕜) := by
  have hk : (k + 1 : 𝕜) ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  apply (eq_div_iff hk).2
  simpa [smul_eq_mul, mul_comm] using
    succ_smul_iteratedDeriv_dslope_self hf k

/-- The removable diagonal quotient of a two-variable numerator. -/
def diagonalDslopeKernel (K : ℂ → ℂ → ℂ) (z v : ℂ) : ℂ :=
  dslope (K z) z v

/-- **Anti-reflection quotient law.**  A two-variable numerator that changes sign under
simultaneous centered reflection has a removable diagonal quotient that is exactly reflection
invariant, including at `v = z`. -/
theorem diagonalDslopeKernel_neg_neg_of_antiInvariant
    (K : ℂ → ℂ → ℂ)
    (hreflect : ∀ z v, K (-z) (-v) = -K z v) (z v : ℂ) :
    diagonalDslopeKernel K (-z) (-v) = diagonalDslopeKernel K z v := by
  have hfun : K (-z) = fun w => -K z (-w) := by
    funext w
    simpa using hreflect z (-w)
  rw [diagonalDslopeKernel, diagonalDslopeKernel, hfun]
  simpa using dslope_neg_comp_neg (K z) z (-v)

end

end HTGeometry
