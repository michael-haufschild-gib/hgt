import GaloisForLFunctions.RHTower.DeningerSkewAdjointGraphCore
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Sequences

/-!
# Existence of the off-axis resolvent of a skew-adjoint operator

A densely defined skew-adjoint operator `A` on a complex Hilbert space has purely imaginary
spectrum: for `Re z ≠ 0` the shifted operator `A - z` is a bijection from the domain of `A` onto
the whole space.

The proof is the standard two-step argument, carried out here without any spectral theorem.  The
skew lower bound `|Re z| ‖x‖ ≤ ‖(A - z)x‖` makes `A - z` injective and, together with closedness
of `A`, makes its range closed.  If `y` is orthogonal to that range then `y` lies in the domain of
the adjoint with `A† y = z̄ y`, so skew-adjointness gives `(A + z̄)y = 0` and the same lower bound
forces `y = 0`.  A closed subspace with trivial orthogonal complement is everything.

* `deningerSkewAdjoint_skewSymmetric` : skew-adjoint implies skew-symmetric.
* `deningerShift_range_isClosed` : the range of `A - z` is closed.
* `deningerShift_bijective` : `A - z` is a bijection onto the whole space.
* `deningerSkewAdjointResolvent` : the resolvent, with `‖R_z y‖ ≤ |Re z|⁻¹ ‖y‖`.
-/

namespace RHTower

open Filter Topology

section SkewAdjointResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Skew-adjointness of a partially defined operator. -/
def DeningerSkewAdjointPMap (A : E →ₗ.[ℂ] E) : Prop := A.adjoint = -A

variable {A : E →ₗ.[ℂ] E}

/-- A skew-adjoint operator is skew-symmetric on its domain. -/
theorem deningerSkewAdjoint_skewSymmetric (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) : DeningerSkewSymmetric A.toFun := by
  intro x y
  have hf : ((-A : E →ₗ.[ℂ] E)).IsFormalAdjoint A := by
    rw [← hskew]
    exact LinearPMap.adjoint_isFormalAdjoint hdense
  have h := hf x y
  rw [LinearPMap.neg_apply, inner_neg_left] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The shifted generator `A - z`, defined on the domain of `A`. -/
noncomputable def deningerShift (A : E →ₗ.[ℂ] E) (z : ℂ) : A.domain →ₗ[ℂ] E :=
  A.toFun - z • A.domain.subtype

omit [CompleteSpace E] in
theorem deningerShift_apply (A : E →ₗ.[ℂ] E) (z : ℂ) (x : A.domain) :
    deningerShift A z x = A.toFun x - z • (x : E) := rfl

/-- The lower bound for the shifted generator, written for the shift map. -/
theorem deningerShift_lower_bound (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) (z : ℂ) (x : A.domain) :
    |z.re| * ‖(x : E)‖ ≤ ‖deningerShift A z x‖ :=
  deningerSkew_lower_bound (deningerSkewAdjoint_skewSymmetric hdense hskew) z x

/-- The shift map is injective off the imaginary axis. -/
theorem deningerShift_injective (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) {z : ℂ} (hz : z.re ≠ 0) :
    Function.Injective (deningerShift A z) := by
  intro a b hab
  have h := deningerShift_lower_bound hdense hskew z (a - b)
  have hval : deningerShift A z (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [hval, norm_zero] at h
  have habs : 0 < |z.re| := abs_pos.mpr hz
  have hzero : ‖((a - b : A.domain) : E)‖ = 0 := by nlinarith [norm_nonneg ((a - b : A.domain) : E)]
  have : ((a - b : A.domain) : E) = 0 := norm_eq_zero.mp hzero
  have hsub : (a : E) - (b : E) = 0 := this
  exact Subtype.ext (sub_eq_zero.mp hsub)

/-- **The range of the shifted generator is closed.** -/
theorem deningerShift_range_isClosed (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) (hclosed : A.IsClosed) {z : ℂ} (hz : z.re ≠ 0) :
    IsClosed ((LinearMap.range (deningerShift A z) : Submodule ℂ E) : Set E) := by
  have habs : 0 < |z.re| := abs_pos.mpr hz
  refine IsSeqClosed.isClosed ?_
  intro u p hu hup
  have hu' : ∀ n, ∃ w : A.domain, deningerShift A z w = u n := fun n => hu n
  choose x hx using hu'
  have hbound : ∀ a b : A.domain,
      |z.re| * ‖(a : E) - (b : E)‖ ≤ ‖deningerShift A z a - deningerShift A z b‖ := by
    intro a b
    have h := deningerShift_lower_bound hdense hskew z (a - b)
    have hcoe : ((a - b : A.domain) : E) = (a : E) - (b : E) := rfl
    have hval : deningerShift A z (a - b) = deningerShift A z a - deningerShift A z b := map_sub _ _ _
    rw [hcoe, hval] at h
    exact h
  have hxcau : CauchySeq (fun n => ((x n : A.domain) : E)) := by
    have hucau : CauchySeq u := hup.cauchySeq
    rw [Metric.cauchySeq_iff] at hucau ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hucau (|z.re| * ε) (by positivity)
    exact ⟨N, fun m hm n hn => by
      have h1 := hbound (x m) (x n)
      rw [hx m, hx n] at h1
      have h2 := hN m hm n hn
      rw [dist_eq_norm] at h2 ⊢
      nlinarith [h1, h2, habs]⟩
  obtain ⟨xlim, hxlim⟩ := cauchySeq_tendsto_of_complete hxcau
  have hAt : Tendsto (fun n => A.toFun (x n)) atTop (𝓝 (p + z • xlim)) := by
    have hrw : ∀ n, A.toFun (x n) = u n + z • ((x n : A.domain) : E) := by
      intro n
      rw [← hx n, deningerShift_apply]
      abel
    simp only [hrw]
    exact hup.add (hxlim.const_smul z)
  have hgraph : (xlim, p + z • xlim) ∈ A.graph := by
    refine hclosed.mem_of_tendsto (hxlim.prodMk_nhds hAt) ?_
    filter_upwards with n
    exact A.mem_graph (x n)
  rw [LinearPMap.mem_graph_iff'] at hgraph
  obtain ⟨y, hy⟩ := hgraph
  have hy1 : (y : E) = xlim := congrArg Prod.fst hy
  have hy2 : A.toFun y = p + z • xlim := congrArg Prod.snd hy
  refine ⟨y, ?_⟩
  rw [deningerShift_apply, hy2, hy1]
  abel

/-- **The range of the shifted generator is dense.**  This is where skew-adjointness, rather than
mere skew-symmetry, is used. -/
theorem deningerShift_range_orthogonal_eq_bot (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) {z : ℂ} (hz : z.re ≠ 0) :
    (LinearMap.range (deningerShift A z))ᗮ = ⊥ := by
  have habs : 0 < |z.re| := abs_pos.mpr hz
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have hall : ∀ x : A.domain,
      (inner ℂ (A.toFun x) y : ℂ) = (starRingEnd ℂ z) * (inner ℂ ((x : E)) y : ℂ) := by
    intro x
    have h0 := hy (deningerShift A z x) ⟨x, rfl⟩
    rw [deningerShift_apply, inner_sub_left, inner_smul_left, sub_eq_zero] at h0
    exact h0
  have hadj : ∀ x : A.domain,
      (inner ℂ ((starRingEnd ℂ z) • y) ((x : E)) : ℂ) = (inner ℂ y (A.toFun x) : ℂ) := by
    intro x
    have h1 := congrArg (starRingEnd ℂ) (hall x)
    rw [inner_conj_symm, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      inner_conj_symm] at h1
    rw [inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply]
    exact h1.symm
  have hmem : y ∈ A.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨(starRingEnd ℂ z) • y, hadj⟩
  have hval : A.adjoint ⟨y, hmem⟩ = (starRingEnd ℂ z) • y :=
    LinearPMap.adjoint_apply_eq hdense ⟨y, hmem⟩ hadj
  have hle : A.adjoint ≤ -A := le_of_eq hskew
  have hmemA : y ∈ A.domain := hle.1 hmem
  have hstep : A.adjoint ⟨y, hmem⟩ = (-A : E →ₗ.[ℂ] E) ⟨y, hmemA⟩ := hle.2 rfl
  rw [LinearPMap.neg_apply, hval] at hstep
  have hAy : A.toFun ⟨y, hmemA⟩ = -((starRingEnd ℂ z) • y) :=
    neg_eq_iff_eq_neg.mp hstep.symm
  have hlow := deningerShift_lower_bound hdense hskew (-(starRingEnd ℂ z)) ⟨y, hmemA⟩
  have hzero : deningerShift A (-(starRingEnd ℂ z)) ⟨y, hmemA⟩ = 0 := by
    rw [deningerShift_apply, hAy]
    module
  rw [hzero, norm_zero] at hlow
  have hre : (-(starRingEnd ℂ z)).re = -z.re := by simp
  rw [hre, abs_neg] at hlow
  have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp this

/-- **The shifted generator is a bijection onto the whole space.** -/
theorem deningerShift_bijective (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) (hclosed : A.IsClosed) {z : ℂ} (hz : z.re ≠ 0) :
    Function.Bijective (deningerShift A z) := by
  refine ⟨deningerShift_injective hdense hskew hz, ?_⟩
  haveI hc : IsClosed ((LinearMap.range (deningerShift A z) : Submodule ℂ E) : Set E) :=
    deningerShift_range_isClosed hdense hskew hclosed hz
  haveI : CompleteSpace (LinearMap.range (deningerShift A z)) := hc.completeSpace_coe
  have htop : LinearMap.range (deningerShift A z) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp
      (deningerShift_range_orthogonal_eq_bot hdense hskew hz)
  intro y
  have hmem : y ∈ LinearMap.range (deningerShift A z) := by
    rw [htop]
    exact Submodule.mem_top
  exact hmem

/-- The off-axis resolvent of a skew-adjoint operator. -/
noncomputable def deningerSkewAdjointResolvent (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) (hclosed : A.IsClosed) {z : ℂ} (hz : z.re ≠ 0)
    (y : E) : A.domain :=
  Classical.choose ((deningerShift_bijective hdense hskew hclosed hz).surjective y)

theorem deningerSkewAdjointResolvent_spec (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) (hclosed : A.IsClosed) {z : ℂ} (hz : z.re ≠ 0)
    (y : E) :
    deningerShift A z (deningerSkewAdjointResolvent hdense hskew hclosed hz y) = y :=
  Classical.choose_spec ((deningerShift_bijective hdense hskew hclosed hz).surjective y)

/-- **The resolvent estimate for a skew-adjoint generator.** -/
theorem deningerSkewAdjointResolvent_norm_le (hdense : Dense (A.domain : Set E))
    (hskew : DeningerSkewAdjointPMap A) (hclosed : A.IsClosed) {z : ℂ} (hz : z.re ≠ 0)
    (y : E) :
    ‖((deningerSkewAdjointResolvent hdense hskew hclosed hz y : A.domain) : E)‖
      ≤ |z.re|⁻¹ * ‖y‖ :=
  deningerSkew_resolvent_norm_le (deningerSkewAdjoint_skewSymmetric hdense hskew) hz
    (deningerSkewAdjointResolvent hdense hskew hclosed hz)
    (fun w => deningerSkewAdjointResolvent_spec hdense hskew hclosed hz w) y

end SkewAdjointResolvent

end RHTower
