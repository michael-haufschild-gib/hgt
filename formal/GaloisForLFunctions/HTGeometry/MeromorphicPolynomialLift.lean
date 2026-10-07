import GaloisForLFunctions.HTGeometry.MeromorphicPlaneAlgebra
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Pole removal for polynomial lifts

A nonconstant polynomial multiplies the order of every pole by its degree.
Thus a polynomial lift of an entire function in the global meromorphic plane
has an entire representative, with the original field element preserved.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

private theorem order_sub_const_of_neg {f : ℂ → ℂ} {z : ℂ}
    (hn : meromorphicOrderAt f z < 0) (b : ℂ) :
    meromorphicOrderAt (fun w => f w - b) z = meromorphicOrderAt f z := by
  classical
  by_cases hb : b = 0
  · simp [hb]
  have hc : meromorphicOrderAt (fun _ : ℂ => -b) z = 0 := by
    rw [meromorphicOrderAt_const]
    simp [hb]
  have he := meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-b) z)
    (show meromorphicOrderAt f z < meromorphicOrderAt (fun _ : ℂ => -b) z by rwa [hc])
  convert he using 1
  congr 1

/-- At a pole, composition with a nonzero polynomial multiplies its order by the degree. -/
theorem meromorphicOrderAt_polynomial_of_neg {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hn : meromorphicOrderAt f z < 0)
    (P : Polynomial ℂ) (hP : P ≠ 0) :
    meromorphicOrderAt (fun w => P.eval (f w)) z =
      P.natDegree • meromorphicOrderAt f z := by
  classical
  have hprod (s : Multiset ℂ) :
      MeromorphicAt (fun w => (s.map (fun b => f w - b)).prod) z ∧
      meromorphicOrderAt (fun w => (s.map (fun b => f w - b)).prod) z =
        s.card • meromorphicOrderAt f z := by
    induction s using Multiset.induction_on with
    | empty => simp [meromorphicOrderAt_const]
    | @cons b s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      have hfb : MeromorphicAt (fun w => f w - b) z := hf.sub (MeromorphicAt.const b z)
      refine ⟨hfb.fun_mul ih.1, ?_⟩
      change meromorphicOrderAt ((fun w => f w - b) *
        (fun w => (s.map (fun c => f w - c)).prod)) z = _
      rw [meromorphicOrderAt_mul hfb ih.1,
        order_sub_const_of_neg hn, ih.2, succ_nsmul]
      exact add_comm _ _
  have hshape := (IsAlgClosed.splits P).eq_prod_roots
  have hfun : (fun w => P.eval (f w)) =
      (fun w => P.leadingCoeff * (P.roots.map (fun b => f w - b)).prod) := by
    funext w
    conv_lhs => rw [hshape]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X]
  have hc : meromorphicOrderAt (fun _ : ℂ => P.leadingCoeff) z = 0 := by
    rw [meromorphicOrderAt_const]
    simp [Polynomial.leadingCoeff_ne_zero.mpr hP]
  rw [hfun]
  change meromorphicOrderAt ((fun _ : ℂ => P.leadingCoeff) *
    (fun w => (P.roots.map (fun b => f w - b)).prod)) z = _
  rw [meromorphicOrderAt_mul (MeromorphicAt.const P.leadingCoeff z) (hprod P.roots).1,
    hc, zero_add, (hprod P.roots).2, (IsAlgClosed.splits P).natDegree_eq_card_roots]

/-- A meromorphic polynomial lift of an analytic germ has no pole. -/
theorem meromorphicOrderAt_nonneg_of_polynomial {f d : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hd : AnalyticAt ℂ d z)
    (P : Polynomial ℂ) (hPdeg : 0 < P.natDegree)
    (hrel : (fun w => P.eval (f w)) =ᶠ[𝓝[≠] z] d) :
    0 ≤ meromorphicOrderAt f z := by
  have hP : P ≠ 0 := by intro he; subst P; simp at hPdeg
  by_contra hn
  have hn' := lt_of_not_ge hn
  have ho := hd.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hrel, meromorphicOrderAt_polynomial_of_neg hf hn' P hP] at ho
  cases hx : meromorphicOrderAt f z with
  | top => simp [hx] at hn'
  | coe n =>
    rw [hx] at ho hn'
    have hn'' : n < 0 := WithTop.coe_lt_coe.mp hn'
    have hp : (0 : ℤ) < P.natDegree := by exact_mod_cast hPdeg
    change (↑(0 : ℤ) : WithTop ℤ) ≤ ↑((P.natDegree : ℤ) * n) at ho
    have ho' := WithTop.coe_le_coe.mp ho
    nlinarith

/-- Normal form fills every removable value of a meromorphic polynomial lift. -/
theorem entire_polynomial_lift_of_meromorphic {f d : ℂ → ℂ}
    (hf : ∀ z, MeromorphicAt f z) (hd : Differentiable ℂ d)
    (P : Polynomial ℂ) (hPdeg : 0 < P.natDegree)
    (hrel : ∀ z, (fun w => P.eval (f w)) =ᶠ[𝓝[≠] z] d) :
    ∃ (h : ℂ → ℂ) (_hh : Differentiable ℂ h),
      (∀ z, h =ᶠ[𝓝[≠] z] f) ∧ ∀ z, P.eval (h z) = d z := by
  let h := toMeromorphicNFOn f Set.univ
  have hfon : MeromorphicOn f Set.univ := fun z _ => hf z
  have hheq (z : ℂ) : h =ᶠ[𝓝[≠] z] f :=
    hfon.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han (z : ℂ) : AnalyticAt ℂ h z := by
    apply ((meromorphicNFOn_toMeromorphicNFOn f Set.univ)
      (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hfon (Set.mem_univ z)]
    exact meromorphicOrderAt_nonneg_of_polynomial (hf z) (hd.analyticAt z) P hPdeg (hrel z)
  refine ⟨h, fun z => (han z).differentiableAt, hheq, fun z => ?_⟩
  have he : (fun w => P.eval (h w)) =ᶠ[𝓝[≠] z] d := by
    filter_upwards [hheq z, hrel z] with w hw hr
    rwa [hw]
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (P.continuousAt.comp (han z).continuousAt) hd.continuous.continuousAt).mp he).eq_of_nhds

/-- A polynomial lift in the global meromorphic field has an entire representative. -/
theorem entire_polynomial_lift_of_plane {d : ℂ → ℂ} (hd : Differentiable ℂ d)
    (P : Polynomial ℂ) (hPdeg : 0 < P.natDegree) (x : MeromorphicPlane)
    (hrel : Polynomial.aeval x P = ofMeromorphic d (fun z => (hd.analyticAt z).meromorphicAt)) :
    ∃ (h : ℂ → ℂ) (hh : Differentiable ℂ h),
      ofMeromorphic h (fun z => (hh.analyticAt z).meromorphicAt) = x ∧
        ∀ z, P.eval (h z) = d z := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  have he := (ofMeromorphic_eq_iff (meromorphicAt_polyEval hf P)
    (fun z => (hd.analyticAt z).meromorphicAt)).mp
      ((aeval_ofMeromorphic P hf).symm.trans hrel)
  obtain ⟨h, hh, hheq, hval⟩ := entire_polynomial_lift_of_meromorphic hf hd P hPdeg he
  exact ⟨h, hh, (ofMeromorphic_eq_iff (fun z => (hh.analyticAt z).meromorphicAt) hf).mpr hheq, hval⟩

end GaloisForLFunctions.HTGeometry
