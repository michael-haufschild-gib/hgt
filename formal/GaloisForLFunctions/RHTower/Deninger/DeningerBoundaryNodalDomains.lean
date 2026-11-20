import GaloisForLFunctions.RHTower.Deninger.DeningerCylinderModes
import GaloisForLFunctions.RHTower.Deninger.DeningerTwoPrimeKummerDenseNonclosedRange
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Boundary nodal domains of the two-prime Kummer cylinder

The boundary nodal count in arXiv:2611.24195 motivates examining the sign
domains of Kummer characters. The principal argument of the even power
defines a continuous root label away from the nodal set. Different labels
separate connected components of the full torus. Small two-prime frequencies
let the winding multiplicity grow while the conormal eigenvalue stays small.
-/

open Set Filter Topology UnitAddTorus

namespace RHTower

noncomputable section

private def nodalLabel (q : ℕ) (z : ℂ) : ℂ :=
  z / Complex.exp (((Complex.arg (z ^ q) / (q : ℝ) : ℝ) : ℂ) * Complex.I)

private theorem nodalLabel_continuousOn (q : ℕ) :
    ContinuousOn (nodalLabel q) {z | z ^ q ∈ Complex.slitPlane} := by
  intro z hz
  have hp : ContinuousAt (fun w : ℂ => w ^ q) z := by fun_prop
  have hz' : z ^ q ∈ Complex.slitPlane := hz
  have ha : ContinuousAt (fun w : ℂ => Complex.arg (w ^ q)) z :=
    (Complex.continuousAt_arg hz').comp hp
  have harg : ContinuousAt
      (fun w : ℂ => (((Complex.arg (w ^ q) / (q : ℝ) : ℝ) : ℂ) * Complex.I)) z :=
    (Complex.continuous_ofReal.continuousAt.comp (ha.div_const _)).mul_const _
  have he := Complex.continuous_exp.continuousAt.comp harg
  exact (continuousAt_id.div he (Complex.exp_ne_zero _)).continuousWithinAt

private theorem nodalLabel_pow {q : ℕ} (hq : q ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) :
    nodalLabel q z ^ q = 1 := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have harg : (q : ℂ) * (((Complex.arg (z ^ q) / (q : ℝ) : ℝ) : ℂ) * Complex.I) =
      (Complex.arg (z ^ q) : ℂ) * Complex.I := by
    push_cast
    field_simp [hq']
  have he := Complex.norm_mul_exp_arg_mul_I (z ^ q)
  rw [norm_pow, hz, one_pow, Complex.ofReal_one, one_mul] at he
  rw [nodalLabel, div_pow, ← Complex.exp_nat_mul, harg, he]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)))

private theorem nodalLabel_eq_of_pow_eq_one {q : ℕ} {z : ℂ} (hz : z ^ q = 1) :
    nodalLabel q z = z := by simp [nodalLabel, hz, Complex.arg_one]

/-- The square avoids the principal branch cut precisely off the nodal line. -/
private theorem square_mem_slitPlane_iff (z : ℂ) :
    z ^ 2 ∈ Complex.slitPlane ↔ z.re ≠ 0 := by
  rw [pow_two]
  change (0 < (z * z).re ∨ (z * z).im ≠ 0) ↔ z.re ≠ 0
  rw [Complex.mul_re, Complex.mul_im, mul_comm z.im z.re]
  constructor
  · rintro (h | h) hre
    · rw [hre, zero_mul, zero_sub] at h
      exact (not_lt_of_ge (neg_nonpos.mpr (mul_self_nonneg _))) h
    · exact h (by simp [hre])
  · intro h
    by_cases hi : z.re * z.im + z.re * z.im = 0
    · have him : z.re * z.im = 0 := by linarith only [hi]
      have hz : z.im = 0 := (mul_eq_zero.mp him).resolve_left h
      exact Or.inl (by simpa only [hz, mul_zero, sub_zero] using mul_self_pos.mpr h)
    · exact Or.inr hi

private theorem pow_mem_slitPlane_iff (k : ℕ) (z : ℂ) :
    z ^ (2 * k) ∈ Complex.slitPlane ↔ (z ^ k).re ≠ 0 := by
  rw [Nat.mul_comm 2 k, pow_mul, square_mem_slitPlane_iff]

/-- Connected subsets of the nonzero locus carry a single root label. -/
private theorem nodalLabel_eq_on_preconnected {X : Type*} [TopologicalSpace X]
    (u : C(X, ℂ)) (hu : ∀ x, ‖u x‖ = 1) (k : ℕ) (hk : k ≠ 0)
    {s : Set X} (hs : IsPreconnected s) (hn : s ⊆ {x | (u x ^ k).re ≠ 0})
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    nodalLabel (2 * k) (u x) = nodalLabel (2 * k) (u y) := by
  let q := 2 * k
  let f := nodalLabel q ∘ u
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))
  have hq : q ≠ 0 := mul_ne_zero two_ne_zero hk
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq
  haveI : NeZero q := ⟨hq⟩
  have hf : ContinuousOn f s :=
    (nodalLabel_continuousOn q).comp u.continuous.continuousOn
      (fun z hz => (pow_mem_slitPlane_iff k (u z)).mpr (hn hz))
  have hb : f '' s ⊆ range (fun i : Fin q => ζ ^ (i : ℕ)) := by
    rintro z ⟨v, _, rfl⟩
    obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one (nodalLabel_pow hq (hu v))
    exact ⟨⟨i, hi⟩, he⟩
  have hfin := (Set.finite_range (fun i : Fin q => ζ ^ (i : ℕ))).subset hb
  by_contra hne
  exact ((hs.image f hf).infinite_of_nontrivial
    ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hne⟩).not_finite hfin

private theorem mFourier_pointwise_norm {d : Type*} [Fintype d]
    (n : d → ℤ) (x : UnitAddTorus d) : ‖mFourier n x‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
    Finset.prod_const_one]

private theorem mFourier_nsmul_apply {d : Type*} [Fintype d] (k : ℕ)
    (n : d → ℤ) (x : UnitAddTorus d) : mFourier (k • n) x = mFourier n x ^ k := by
  induction k with
  | zero => simp [mFourier_zero]
  | succ k ih => rw [succ_nsmul, mFourier_add, ih, pow_succ]

/-- The nonzero locus of the real boundary trace of a cylinder mode. -/
def deningerBoundaryNonzero {d : Type*} [Fintype d] (n : d → ℤ) : Set (UnitAddTorus d) :=
  {x | (mFourier n x).re ≠ 0}

/-- A nonzero character raised to the `(k+1)`st power has at least `2(k+1)`
connected nodal domains on the full torus. Witnesses lie on a single flow line,
but equality of components is tested in the full nonzero locus. -/
theorem deningerBoundaryDistinctNodalDomains {d : Type*} [Fintype d]
    (lam : d → ℝ) (n : d → ℤ) (hfreq : deningerFrequency n lam ≠ 0) (k : ℕ) :
    ∃ x : Fin (2 * (k + 1)) → UnitAddTorus d,
      (∀ i, x i ∈ deningerBoundaryNonzero ((k + 1) • n)) ∧
      Function.Injective (fun i =>
        connectedComponentIn (deningerBoundaryNonzero ((k + 1) • n)) (x i)) := by
  let q := 2 * (k + 1)
  let μ := deningerFrequency n lam
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))
  have hq : q ≠ 0 := by omega
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq
  let x (i : Fin q) := deningerTorusFlow lam ((i : ℕ) / ((q : ℝ) * μ))
  have hx (i : Fin q) : mFourier n (x i) = ζ ^ (i : ℕ) := by
    rw [show x i = deningerTorusFlow lam ((i : ℕ) / ((q : ℝ) * μ)) from rfl,
      deningerMFourier_flow, show ζ = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)) from rfl,
      ← Complex.exp_nat_mul]
    congr 1
    change ((2 * Real.pi * μ * ((i : ℕ) / ((q : ℝ) * μ)) : ℝ) : ℂ) *
        Complex.I = _
    push_cast
    have hμC : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hfreq
    field_simp [hqC, hμC]
    ring
  have hroot (i : Fin q) : mFourier n (x i) ^ q = 1 := by
    rw [hx i, ← pow_mul, Nat.mul_comm (i : ℕ) q, pow_mul, hζ.pow_eq_one, one_pow]
  let s := deningerBoundaryNonzero ((k + 1) • n)
  have hs (i : Fin q) : x i ∈ s := by
    change (mFourier ((k + 1) • n) (x i)).re ≠ 0
    rw [mFourier_nsmul_apply]
    apply (pow_mem_slitPlane_iff (k + 1) (mFourier n (x i))).mp
    change mFourier n (x i) ^ q ∈ Complex.slitPlane
    rw [hroot i]
    exact Or.inl (by simp)
  refine ⟨x, hs, ?_⟩
  intro i j hij
  have hi : x i ∈ connectedComponentIn s (x i) := mem_connectedComponentIn (hs i)
  have hj : x j ∈ connectedComponentIn s (x i) := by
    rw [hij]
    exact mem_connectedComponentIn (hs j)
  have hsub : connectedComponentIn s (x i) ⊆ {y | (mFourier n y ^ (k + 1)).re ≠ 0} := by
    intro y hy
    simpa only [s, deningerBoundaryNonzero, Set.mem_setOf_eq, mFourier_nsmul_apply]
      using connectedComponentIn_subset s (x i) hy
  have hlabel :=
    nodalLabel_eq_on_preconnected (mFourier n) (mFourier_pointwise_norm n)
      (k + 1) (Nat.succ_ne_zero k) isPreconnected_connectedComponentIn hsub hi hj
  change nodalLabel q (mFourier n (x i)) = nodalLabel q (mFourier n (x j)) at hlabel
  rw [nodalLabel_eq_of_pow_eq_one (hroot i), nodalLabel_eq_of_pow_eq_one (hroot j),
    hx i, hx j] at hlabel
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt hlabel)

/-- The outward radial derivative of the real cylinder mode is the boundary
trace multiplied by the nonnegative conormal level. -/
theorem deningerCylinder_real_conormal {d : Type*} [Fintype d]
    (lam : d → ℝ) (n : d → ℤ) (x : UnitAddTorus d) :
    -(deriv (fun r => (deningerCylinderMode lam n r x).1.re) 0) =
      |deningerFrequency n lam| * (mFourier n x).re := by
  have h := (deningerModeProfile_hasDerivAt (deningerFrequency n lam) 0).const_mul
    (mFourier n x).re
  simp only [deningerCylinderMode_fst, deningerMode_fst, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [h.deriv, show deningerModeProfile (deningerFrequency n lam) 0 = 1 by
    simp [deningerModeProfile], one_mul]
  ring

/-- Two-prime Kronecker velocity in the real coordinates of the unit torus. -/
def deningerTwoPrimeVelocity : Fin 2 → ℝ := fun i => (deningerPrimeLogPeriodPair i).re

private theorem deningerTwoPrime_frequency_cast (n : Fin 2 → ℤ) :
    (deningerFrequency n deningerTwoPrimeVelocity : ℂ) =
      ∑ i, n i • deningerPrimeLogPeriodPair i := by
  rw [deningerFrequency, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hreal : ((deningerTwoPrimeVelocity i : ℝ) : ℂ) = deningerPrimeLogPeriodPair i := by
    refine Complex.ext rfl ?_
    exact (deningerPrimeLogPeriodGroup_im_eq_zero
      ⟨deningerPrimeLogPeriodPair i, Submodule.subset_span (Set.mem_range_self i)⟩).symm
  rw [Complex.ofReal_mul, Complex.ofReal_intCast, hreal, zsmul_eq_mul]

/-- The complexified torus frequencies are exactly the signed Kummer period group. -/
theorem deningerTwoPrime_frequency_range :
    range (fun n : Fin 2 → ℤ => (deningerFrequency n deningerTwoPrimeVelocity : ℂ)) =
      (deningerPrimeLogPeriodGroup : Set ℂ) := by
  ext p
  change (∃ n, (deningerFrequency n deningerTwoPrimeVelocity : ℂ) = p) ↔
    p ∈ deningerPrimeLogPeriodGroup
  simp_rw [deningerTwoPrime_frequency_cast]
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).symm

/-- The corpus's nondiscrete two-prime period group produces arbitrarily small
nonzero character frequencies on the actual unit torus. -/
theorem deningerTwoPrime_exists_small_frequency (ε : Ioi (0 : ℝ)) :
    ∃ n : Fin 2 → ℤ, 0 < |deningerFrequency n deningerTwoPrimeVelocity| ∧
      |deningerFrequency n deningerTwoPrimeVelocity| < (ε : ℝ) := by
  obtain ⟨p, hpL, hpne, hp0⟩ :=
    GaloisForLFunctions.exists_small_nonzero_of_not_discrete_intSubmodule
      deningerPrimeLogPeriodGroup deningerPrimeLogPeriodGroup_not_discrete
  have he : 0 < (ε : ℝ) := ε.2
  have hnorm := (Metric.tendsto_atTop.mp hp0 (ε : ℝ) he)
  obtain ⟨j, hj⟩ := hnorm
  obtain ⟨n, hn⟩ := deningerTwoPrime_frequency_range.symm.subset (hpL j)
  change (deningerFrequency n deningerTwoPrimeVelocity : ℂ) = p j at hn
  refine ⟨n, abs_pos.mpr (Complex.ofReal_ne_zero.mp (by rw [hn]; exact hpne j)), ?_⟩
  have hsmall := hj j le_rfl
  change dist (p j) 0 < (ε : ℝ) at hsmall
  rwa [dist_zero_right, ← hn, Complex.norm_real, Real.norm_eq_abs] at hsmall

private theorem deningerFrequency_nsmul {d : Type*} [Fintype d]
    (k : ℕ) (n : d → ℤ) (lam : d → ℝ) :
    deningerFrequency (k • n) lam = (k : ℝ) * deningerFrequency n lam := by
  rw [deningerFrequency, deningerFrequency, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc]

/-- Arbitrarily small strictly positive conormal levels support real boundary
modes with arbitrarily many distinct nodal domains. -/
theorem deningerTwoPrime_small_frequency_many_nodal_domains (ε : Ioi (0 : ℝ)) (k : ℕ) :
    ∃ n : Fin 2 → ℤ,
      0 < |deningerFrequency n deningerTwoPrimeVelocity| ∧
      |deningerFrequency n deningerTwoPrimeVelocity| < (ε : ℝ) ∧
      ∃ x : Fin (2 * (k + 1)) → UnitAddTorus (Fin 2),
        (∀ i, x i ∈ deningerBoundaryNonzero n) ∧
        Function.Injective (fun i => connectedComponentIn (deningerBoundaryNonzero n) (x i)) := by
  let d : ℝ := (k + 1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨n, hn, hsmall⟩ := deningerTwoPrime_exists_small_frequency
    ⟨(ε : ℝ) / d, div_pos ε.2 hd⟩
  refine ⟨(k + 1) • n, ?_, ?_, deningerBoundaryDistinctNodalDomains
    deningerTwoPrimeVelocity n (abs_pos.mp hn) k⟩
  · rw [deningerFrequency_nsmul, abs_mul, abs_of_pos hd]
    exact mul_pos hd hn
  · rw [deningerFrequency_nsmul, abs_mul, abs_of_pos hd, mul_comm]
    exact (lt_div_iff₀ hd).mp hsmall

#print axioms deningerBoundaryDistinctNodalDomains
#print axioms deningerCylinder_real_conormal
#print axioms deningerTwoPrime_small_frequency_many_nodal_domains

end

end RHTower
