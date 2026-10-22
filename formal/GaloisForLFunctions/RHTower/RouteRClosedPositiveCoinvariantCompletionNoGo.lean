import GaloisForLFunctions.RHTower.CCM.CCMRationalWeightedShiftReal
import GaloisForLFunctions.RHTower.ContinuousSesquilinearFormBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerSUnitEndpointPage
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Closed positive prime-coinvariant completions erase the Route R atom

This file closes the unbounded-positive completion loophole in Route R.  On the actual rational
CCM Morita Hilbert source, prime dilation has no fixed vector, hence its coinvariant boundary has
dense range.  If a dense invariant source domain is complete for a graph norm whose extra term is
a sesquilinear form, and every coinvariant boundary has zero form energy, ambient density upgrades
to graph-norm density.  The form is therefore identically zero.

Unlike the bounded Riesz-representation obstruction, no boundedness of the form is assumed in the
ambient Hilbert norm.  Closed Dirichlet/GNS/graph-form completions cannot retain a nonzero Route R
prime atom.  Any surviving producer must be signed or discontinuous before positive extraction.
-/

open Complex Filter Set
open scoped ComplexInnerProductSpace lp

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## Abstract closed graph-form collapse -/

/-- A closed positive graph-form completion of a linear boundary.  Completeness of `D` is
completeness for the displayed graph norm, not for the ambient Hilbert norm. -/
structure RouteRClosedPositiveCoinvariantCompletion
    (H D : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup D] [NormedSpace ℂ D] where
  embedding : D →L[ℂ] H
  embedding_injective : Function.Injective embedding
  boundary : D →ₗ[ℂ] D
  form : _root_.RHTower.ContinuousSesquilinearForm D
  hermitian : ∀ x y, form x y = star (form y x)
  nonnegative : ∀ x, 0 ≤ (form x x).re
  graph_norm_sq : ∀ x, ‖x‖ ^ 2 = ‖embedding x‖ ^ 2 + (form x x).re
  boundary_null : ∀ z, form (boundary z) (boundary z) = 0
  boundary_ambient_dense : DenseRange (fun z => embedding (boundary z))

namespace RouteRClosedPositiveCoinvariantCompletion

variable {H D : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]

/-- Ambient approximation by null boundaries becomes graph-norm approximation.  Closedness then
forces every diagonal value of the form to vanish. -/
theorem diagonal_eq_zero (C : RouteRClosedPositiveCoinvariantCompletion H D) (x : D) :
    C.form x x = 0 := by
  have hxclosure : C.embedding x ∈
      closure (Set.range fun z : D => C.embedding (C.boundary z)) :=
    C.boundary_ambient_dense (C.embedding x)
  rw [Metric.mem_closure_range_iff_nat] at hxclosure
  choose z hz using hxclosure
  let y : ℕ → D := fun n => C.boundary (z n)
  have hJy : Tendsto (fun n => C.embedding (y n)) atTop (nhds (C.embedding x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => le_of_lt (by simpa [y, dist_comm] using hz n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hyCauchy : CauchySeq y := by
    have hJCauchy : CauchySeq (fun n => C.embedding (y n)) := hJy.cauchySeq
    rw [Metric.cauchySeq_iff] at hJCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hJCauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hBdiff : C.form (y m - y n) (y m - y n) = 0 := by
      have hy_sub : y m - y n = C.boundary (z m - z n) := by
        simp [y]
      rw [hy_sub]
      exact C.boundary_null (z m - z n)
    have hsquare := C.graph_norm_sq (y m - y n)
    rw [hBdiff] at hsquare
    simp only [map_sub, Complex.zero_re, add_zero] at hsquare
    have hnorm : ‖y m - y n‖ =
        ‖C.embedding (y m) - C.embedding (y n)‖ := by
      nlinarith [norm_nonneg (y m - y n),
        norm_nonneg (C.embedding (y m) - C.embedding (y n))]
    simpa only [dist_eq_norm, hnorm] using hN m hm n hn
  obtain ⟨x', hx'⟩ := cauchySeq_tendsto_of_complete hyCauchy
  have hJx' : Tendsto (fun n => C.embedding (y n)) atTop
      (nhds (C.embedding x')) :=
    (C.embedding.continuous.tendsto x').comp hx'
  have hxeq : x' = x := by
    apply C.embedding_injective
    exact tendsto_nhds_unique hJx' hJy
  have hBlim : Tendsto (fun n => C.form (y n) (y n)) atTop
      (nhds (C.form x' x')) := by
    have hpair : Tendsto (fun n => (y n, y n)) atTop (nhds (x', x')) := by
      simpa only [nhds_prod_eq] using hx'.prodMk hx'
    simpa only [Function.comp_def] using
      (C.form.continuous.tendsto (x', x')).comp hpair
  have hBzero : Tendsto (fun _n : ℕ => (0 : ℂ)) atTop
      (nhds (C.form x' x')) := by
    simpa only [C.boundary_null, y] using hBlim
  rw [← hxeq]
  exact tendsto_nhds_unique hBzero
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℂ)) atTop (nhds 0))

/-- **Closed positive coinvariant collapse.**  The whole sesquilinear form vanishes, not only its
diagonal.  The last step is complex polarization. -/
theorem form_eq_zero (C : RouteRClosedPositiveCoinvariantCompletion H D) :
    ∀ u v : D, C.form u v = 0 := by
  intro u v
  let Q := C.form.toContinuousSesquilinearFormOn
  have hplus := C.diagonal_eq_zero (u + v)
  have hI := C.diagonal_eq_zero (u + Complex.I • v)
  have huu := C.diagonal_eq_zero u
  have hvv := C.diagonal_eq_zero v
  change Q (u + v) (u + v) = 0 at hplus
  change Q (u + Complex.I • v) (u + Complex.I • v) = 0 at hI
  change Q u u = 0 at huu
  change Q v v = 0 at hvv
  simp only [
    GaloisForLFunctions.HTGeometry.ContinuousSesquilinearFormOn.apply_add_left,
    GaloisForLFunctions.HTGeometry.ContinuousSesquilinearFormOn.apply_smul_left,
    GaloisForLFunctions.HTGeometry.ContinuousSesquilinearFormOn.apply_add_right,
    GaloisForLFunctions.HTGeometry.ContinuousSesquilinearFormOn.apply_smul_right] at hplus hI
  rw [huu, hvv] at hplus hI
  have hstarI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  rw [hstarI] at hI
  have hsum : Q u v + Q v u = 0 := by
    linear_combination hplus
  have hdiff : -Complex.I * Q u v + Complex.I * Q v u = 0 := by
    linear_combination hI
  have hvu : Q v u = -Q u v := by
    linear_combination hsum
  rw [hvu] at hdiff
  have hmul : (-2 * Complex.I) * Q u v = 0 := by
    linear_combination hdiff
  change Q u v = 0
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num [Complex.I_ne_zero])

end RouteRClosedPositiveCoinvariantCompletion

/-! ## Actual rational CCM prime dilation -/

/-- Prime dilation has no fixed vector on `ℓ²(ℚˣ)`.  A fixed vector is constant on an infinite
positive multiplicative orbit, contradicting square summability. -/
theorem ccmRationalMoritaHilbertLeftScale_fixed_eq_zero
    (k : CCMRationalUnit) (hkpos : 0 < (k : ℚ)) (hkone : (k : ℚ) ≠ 1)
    (f : CCMRationalMoritaHilbert)
    (hf : ccmRationalMoritaHilbertLeftScale k f = f) :
    f = 0 := by
  have hstep : ∀ q : CCMRationalUnit, f (k⁻¹ * q) = f q := by
    intro q
    have h := congrArg (fun g : CCMRationalMoritaHilbert => g q) hf
    simpa using h
  have horbit : ∀ (q : CCMRationalUnit) (n : ℕ),
      f ((k⁻¹) ^ n * q) = f q := by
    intro q n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          f ((k⁻¹) ^ (n + 1) * q) =
              f (k⁻¹ * ((k⁻¹) ^ n * q)) := by
                apply congrArg (fun r : CCMRationalUnit => f r)
                rw [pow_succ]
                ac_rfl
          _ = f ((k⁻¹) ^ n * q) := hstep _
          _ = f q := ih
  apply lp.ext
  funext q
  by_contra hq
  have horbitInjective : Function.Injective (fun n : ℕ => (k⁻¹) ^ n * q) := by
    intro m n hmn
    have hpowUnits : (k⁻¹) ^ m = (k⁻¹) ^ n := mul_right_cancel hmn
    have hpow : ((k : ℚ)⁻¹) ^ m = ((k : ℚ)⁻¹) ^ n := by
      simpa using congrArg (fun u : CCMRationalUnit => (u : ℚ)) hpowUnits
    exact pow_right_injective₀ (inv_pos.mpr hkpos) (inv_ne_one.mpr hkone) hpow
  have hs := ((lp.memℓp f).summable (by norm_num)).comp_injective horbitInjective
  change Summable (fun n : ℕ => ‖f ((k⁻¹) ^ n * q)‖ ^ (2 : ℝ)) at hs
  have hsconst : Summable (fun _n : ℕ => ‖f q‖ ^ (2 : ℝ)) := by
    simpa only [horbit] using hs
  exact Set.infinite_univ (Set.Finite.of_summable_const
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hq) _) hsconst)

/-- Actual prime-coinvariant boundary `U_k - 1` on the rational CCM Morita Hilbert source. -/
def ccmRationalMoritaHilbertCoinvariantBoundary (k : CCMRationalUnit) :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert :=
  (ccmRationalMoritaHilbertLeftScaleIsometry k :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) - 1

theorem ccmRationalMoritaHilbertCoinvariantBoundary_adjoint (k : CCMRationalUnit) :
    (ccmRationalMoritaHilbertCoinvariantBoundary k).adjoint =
      (ccmRationalMoritaHilbertLeftScaleIsometry k).symm - 1 := by
  let adj :
      (CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) ≃ₗᵢ⋆[ℂ]
        (CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :=
    ContinuousLinearMap.adjoint
  change adj ((ccmRationalMoritaHilbertLeftScaleIsometry k :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) - 1) = _
  rw [map_sub adj, LinearIsometryEquiv.adjoint_eq_symm,
    ContinuousLinearMap.adjoint_one]

/-- `U_k - 1` has dense range for every positive nontrivial rational dilation. -/
theorem ccmRationalMoritaHilbertCoinvariantBoundary_denseRange
    (k : CCMRationalUnit) (hkpos : 0 < (k : ℚ)) (hkone : (k : ℚ) ≠ 1) :
    DenseRange (ccmRationalMoritaHilbertCoinvariantBoundary k) := by
  let T := ccmRationalMoritaHilbertCoinvariantBoundary k
  have hAdjInjective : Function.Injective T.adjoint := by
    intro f g hfg
    have hkernel : T.adjoint (f - g) = 0 := by
      rw [map_sub, hfg, sub_self]
    rw [ccmRationalMoritaHilbertCoinvariantBoundary_adjoint] at hkernel
    have hfixed : ccmRationalMoritaHilbertLeftScale k⁻¹ (f - g) = f - g := by
      change (ccmRationalMoritaHilbertLeftScaleIsometry k).symm (f - g) = f - g
      exact sub_eq_zero.mp hkernel
    have hzero : f - g = 0 :=
      ccmRationalMoritaHilbertLeftScale_fixed_eq_zero k⁻¹
        (by simpa using inv_pos.mpr hkpos) (by simpa using inv_ne_one.mpr hkone)
        (f - g) hfixed
    exact sub_eq_zero.mp hzero
  have horth : T.rangeᗮ = ⊥ := by
    rw [T.orthogonal_range]
    exact LinearMap.ker_eq_bot.mpr hAdjInjective
  change Dense (T.range : Set CCMRationalMoritaHilbert)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  simpa using horth

/-- Every ordinary-prime coinvariant boundary has dense range on the actual rational source. -/
theorem ccmRationalMoritaHilbertPrimeCoinvariantBoundary_denseRange (p : Nat.Primes) :
    DenseRange (ccmRationalMoritaHilbertCoinvariantBoundary
      (_root_.RHTower.deningerPrimeUnit p)) := by
  apply ccmRationalMoritaHilbertCoinvariantBoundary_denseRange
  · rw [_root_.RHTower.deningerPrimeUnit_val]
    exact_mod_cast p.2.pos
  · rw [_root_.RHTower.deningerPrimeUnit_val]
    exact_mod_cast p.2.ne_one

/-! ## Coefficient-faithful dense source-domain comparison -/

/-- An honest closed positive completion on a dense source domain, with the domain boundary
intertwining the actual rational CCM prime-coinvariant boundary.  Density of the boundary image is
deliberately not a field: it is proved from the rational prime orbit below. -/
structure CCMRationalPrimeClosedPositiveCoinvariantCompletion
    (p : Nat.Primes) (D : Type*) [NormedAddCommGroup D] [NormedSpace ℂ D] where
  embedding : D →L[ℂ] CCMRationalMoritaHilbert
  embedding_injective : Function.Injective embedding
  embedding_dense : DenseRange embedding
  boundary : D →ₗ[ℂ] D
  boundary_intertwining : ∀ z,
    embedding (boundary z) =
      ccmRationalMoritaHilbertCoinvariantBoundary
        (_root_.RHTower.deningerPrimeUnit p) (embedding z)
  form : _root_.RHTower.ContinuousSesquilinearForm D
  hermitian : ∀ x y, form x y = star (form y x)
  nonnegative : ∀ x, 0 ≤ (form x x).re
  graph_norm_sq : ∀ x, ‖x‖ ^ 2 = ‖embedding x‖ ^ 2 + (form x x).re
  boundary_null : ∀ z, form (boundary z) (boundary z) = 0

namespace CCMRationalPrimeClosedPositiveCoinvariantCompletion

variable {p : Nat.Primes} {D : Type*}
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- Dense domain plus exact prime-boundary intertwining gives ambient density of domain
boundaries.  This is where the actual rational prime orbit enters the closed-form argument. -/
theorem boundary_ambient_dense
    (C : CCMRationalPrimeClosedPositiveCoinvariantCompletion p D) :
    DenseRange (fun z : D => C.embedding (C.boundary z)) := by
  let T := ccmRationalMoritaHilbertCoinvariantBoundary
    (_root_.RHTower.deningerPrimeUnit p)
  have hcomp : DenseRange (T ∘ C.embedding) :=
    DenseRange.comp (ccmRationalMoritaHilbertPrimeCoinvariantBoundary_denseRange p)
      C.embedding_dense T.continuous
  have hfun : (fun z : D => C.embedding (C.boundary z)) = T ∘ C.embedding := by
    funext z
    exact C.boundary_intertwining z
  rw [hfun]
  exact hcomp

variable [CompleteSpace D]

/-- Forget to the abstract graph-form completion after deriving boundary density. -/
def toClosedPositiveCoinvariantCompletion
    (C : CCMRationalPrimeClosedPositiveCoinvariantCompletion p D) :
    RouteRClosedPositiveCoinvariantCompletion CCMRationalMoritaHilbert D where
  embedding := C.embedding
  embedding_injective := C.embedding_injective
  boundary := C.boundary
  form := C.form
  hermitian := C.hermitian
  nonnegative := C.nonnegative
  graph_norm_sq := C.graph_norm_sq
  boundary_null := C.boundary_null
  boundary_ambient_dense := C.boundary_ambient_dense

/-- **Route R C29.**  Every coefficient-faithful closed positive completion descending through the
actual prime coinvariant has zero form. -/
theorem form_eq_zero
    (C : CCMRationalPrimeClosedPositiveCoinvariantCompletion p D) :
    ∀ u v : D, C.form u v = 0 :=
  C.toClosedPositiveCoinvariantCompletion.form_eq_zero

/-- No retained source atom can carry nonzero positive energy in such a completion. -/
theorem not_exists_retained_nonzero_atom
    (C : CCMRationalPrimeClosedPositiveCoinvariantCompletion p D) :
    ¬ ∃ x : D, C.form x x ≠ 0 := by
  rintro ⟨x, hx⟩
  exact hx (C.form_eq_zero x x)

end CCMRationalPrimeClosedPositiveCoinvariantCompletion

end
end GaloisForLFunctions.RHTower
