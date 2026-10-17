import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

/-! # Closed dissipative graphs from dense Cayley resolvents -/

open Complex Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Complete
variable [CompleteSpace H]

theorem adjoint_fixed_of_contraction_fixed (C : H →L[ℂ] H) (hC : ‖C‖ ≤ 1)
    {f : H} (hf : C f = f) : C.adjoint f = f := by
  have hn : ‖C.adjoint f‖ ≤ ‖f‖ := by
    calc
      ‖C.adjoint f‖ ≤ ‖C.adjoint‖ * ‖f‖ := C.adjoint.le_opNorm f
      _ = ‖C‖ * ‖f‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  have hi : inner ℂ (C.adjoint f) f = inner ℂ f f := by
    rw [ContinuousLinearMap.adjoint_inner_left, hf]
  have hs := norm_sub_sq (𝕜 := ℂ) (C.adjoint f) f
  rw [hi, ← norm_sq_eq_re_inner] at hs
  have hsq := mul_self_le_mul_self (norm_nonneg (C.adjoint f)) hn
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (C.adjoint f-f)]

theorem injective_of_denseRange_cayley_contraction (R : H →L[ℂ] H)
    (hR : DenseRange R) (hC : ‖(1 : H →L[ℂ] H) - (2 : ℂ) • R‖ ≤ 1) :
    Function.Injective R := by
  have hk {f : H} (hf : R f = 0) : f = 0 := by
    let C : H →L[ℂ] H := 1 - (2 : ℂ) • R
    have hfix : C f = f := by simp [C, hf]
    have ha := adjoint_fixed_of_contraction_fixed C hC hfix
    have ho (g : H) : inner ℂ f (R g) = 0 := by
      have h := ContinuousLinearMap.adjoint_inner_left C g f
      rw [ha] at h
      change inner ℂ f g = inner ℂ f (g - (2 : ℂ) • R g) at h
      rw [inner_sub_right, inner_smul_right] at h
      have hz : (2 : ℂ) * inner ℂ f (R g) = 0 := by linear_combination h
      exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
    have hc : IsClosed {g : H | inner ℂ f g = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hzero : inner ℂ f f = 0 :=
      (closure_minimal (by rintro _ ⟨g, rfl⟩; exact ho g) hc) (hR f)
    exact inner_self_eq_zero.mp hzero
  intro f g h
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub, h, sub_self]

end Complete

/-- The graph encoded by one positive resolvent. -/
def cayleyResolventGraph (R : H →L[ℂ] H) : Submodule ℂ (H × H) where
  carrier := {p | R (p.1-p.2) = p.1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change R ((_+_)-(_+_)) = _+_
    rw [show (x.1+y.1)-(x.2+y.2) = (x.1-x.2)+(y.1-y.2) by abel,
      map_add, hx, hy]
  smul_mem' c p hp := by
    change R (c • p.1-c • p.2) = c • p.1
    rw [← smul_sub, map_smul, hp]

theorem isClosed_cayleyResolventGraph (R : H →L[ℂ] H) :
    IsClosed (cayleyResolventGraph R : Set (H × H)) :=
  isClosed_eq (R.continuous.comp (continuous_fst.sub continuous_snd)) continuous_fst

theorem cayleyResolventGraph_pair (R : H →L[ℂ] H) (w : H) :
    (R w, R w-w) ∈ cayleyResolventGraph R := by
  change R (R w-(R w-w)) = R w
  rw [sub_sub_cancel]

theorem cayleyResolventGraph_mem_iff (R : H →L[ℂ] H) (u v : H) :
    (u,v) ∈ cayleyResolventGraph R ↔ ∃ w, u = R w ∧ v = R w-w := by
  constructor
  · intro h
    change R (u-v) = u at h
    refine ⟨u-v, h.symm, ?_⟩
    rw [h, sub_sub_cancel]
  · rintro ⟨w, rfl, rfl⟩
    exact cayleyResolventGraph_pair R w

theorem cayleyResolventGraph_singleValued (R : H →L[ℂ] H)
    (hi : Function.Injective R) {u v w : H}
    (hv : (u,v) ∈ cayleyResolventGraph R) (hw : (u,w) ∈ cayleyResolventGraph R) :
    v = w := by
  change R (u-v) = u at hv
  change R (u-w) = u at hw
  exact sub_right_injective (hi (hv.trans hw.symm))

theorem cayleyResolventGraph_dissipative (R : H →L[ℂ] H)
    (hC : ‖(1 : H →L[ℂ] H) - (2 : ℂ) • R‖ ≤ 1)
    {u v : H} (huv : (u,v) ∈ cayleyResolventGraph R) :
    (inner ℂ u v).re ≤ 0 := by
  change R (u-v) = u at huv
  let C : H →L[ℂ] H := 1 - (2 : ℂ) • R
  have he : C (u-v) = -(u+v) := by
    change (u-v)-(2 : ℂ) • R (u-v) = -(u+v)
    rw [huv, two_smul]
    abel
  have hn : ‖u+v‖ ≤ ‖u-v‖ := by
    have h := (C.le_opNorm (u-v)).trans
      (mul_le_mul_of_nonneg_right hC (norm_nonneg (u-v)))
    simpa only [he, norm_neg, one_mul] using h
  have hsq := mul_self_le_mul_self (norm_nonneg (u+v)) hn
  have ha := norm_add_sq (𝕜 := ℂ) u v
  have hs := norm_sub_sq (𝕜 := ℂ) u v
  simp only [RCLike.re_eq_complex_re] at ha hs
  nlinarith

/-- Surjectivity of I-A makes any dissipative extension coincide with this graph. -/
theorem le_cayleyResolventGraph_of_dissipative_extension (R : H →L[ℂ] H)
    (S : Submodule ℂ (H × H)) (hGS : cayleyResolventGraph R ≤ S)
    (hS : ∀ p ∈ S, (inner ℂ p.1 p.2).re ≤ 0) : S ≤ cayleyResolventGraph R := by
  intro p hp
  let w := R (p.1-p.2)
  have hbase : (w,w-(p.1-p.2)) ∈ S := hGS (cayleyResolventGraph_pair R _)
  have hd := S.sub_mem hp hbase
  have he : p-(w,w-(p.1-p.2)) = (p.1-w,p.1-w) := by
    apply Prod.ext
    · rfl
    · change p.2-(w-(p.1-p.2)) = p.1-w
      abel
  rw [he] at hd
  have hs := hS _ hd
  change (inner ℂ (p.1-w) (p.1-w)).re ≤ 0 at hs
  rw [← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at hs
  have hz : p.1-w = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (p.1-w)]
  exact (sub_eq_zero.mp hz).symm

end GaloisForLFunctions.HTGeometry
