import GaloisForLFunctions.HTGeometry.MeromorphicPolynomialLift

/-!
# Reciprocal coordinates at finite poles of an outer rational map

If a meromorphic lift satisfies p(f)=d*q(f) with analytic d, a root b of q
where p(b) is nonzero cannot be a zero of f-b, even after filling removable
values. The reciprocal coordinate extends to an entire representative and
preserves its inverse in the global meromorphic field.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- An analytic quotient cannot meet a finite pole of its coprime outer map. -/
theorem meromorphicOrderAt_sub_const_nonpos_of_quotient {f d : ℂ → ℂ} {z b : ℂ}
    (hf : MeromorphicAt f z) (hd : AnalyticAt ℂ d z)
    (p q : Polynomial ℂ) (hp : p.eval b ≠ 0) (hq : q.eval b = 0)
    (hrel : (fun w => p.eval (f w)) =ᶠ[𝓝[≠] z] (fun w => d w * q.eval (f w))) :
    meromorphicOrderAt (fun w => f w - b) z ≤ 0 := by
  have hfb : MeromorphicAt (fun w => f w - b) z := hf.sub (MeromorphicAt.const b z)
  by_contra hn
  have hn' : 0 < meromorphicOrderAt (fun w => f w - b) z := lt_of_not_ge hn
  obtain ⟨g, hg, he⟩ := hfb.meromorphicOrderAt_nonneg_iff.mp (le_of_lt hn')
  have hgo : 0 < meromorphicOrderAt g z := by
    rwa [meromorphicOrderAt_congr he] at hn'
  have hg0 : g z = 0 := by
    by_contra hne
    have hzero := hg.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne
    rw [hzero] at hgo
    exact (lt_irrefl 0) hgo
  have he' : (fun w => p.eval (g w + b)) =ᶠ[𝓝[≠] z]
      (fun w => d w * q.eval (g w + b)) := by
    filter_upwards [he, hrel] with w hw hr
    have hw' : g w + b = f w := by rw [← hw]; ring
    simpa only [hw'] using hr
  have hg' : ContinuousAt (fun w => g w + b) z := hg.continuousAt.add continuousAt_const
  have hv := ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (p.continuousAt.comp hg') (hd.continuousAt.mul (q.continuousAt.comp hg'))).mp he').eq_of_nhds
  exact hp (by simpa [hg0, hq] using hv)

/-- The reciprocal coordinate at a finite outer pole has no poles of its own. -/
theorem meromorphicOrderAt_inv_sub_nonneg_of_quotient {f d : ℂ → ℂ} {z b : ℂ}
    (hf : MeromorphicAt f z) (hd : AnalyticAt ℂ d z)
    (p q : Polynomial ℂ) (hp : p.eval b ≠ 0) (hq : q.eval b = 0)
    (hrel : (fun w => p.eval (f w)) =ᶠ[𝓝[≠] z] (fun w => d w * q.eval (f w))) :
    0 ≤ meromorphicOrderAt (fun w => (f w - b)⁻¹) z := by
  have hn := meromorphicOrderAt_sub_const_nonpos_of_quotient hf hd p q hp hq hrel
  change 0 ≤ meromorphicOrderAt ((fun w => f w - b)⁻¹) z
  rw [meromorphicOrderAt_inv]
  cases ho : meromorphicOrderAt (fun w => f w - b) z with
  | top => simp [ho] at hn
  | coe n =>
    rw [ho] at hn
    have hn' : n ≤ 0 := WithTop.coe_le_coe.mp hn
    exact_mod_cast neg_nonneg.mpr hn'

/-- Filling removable values gives the entire coordinate reciprocal to an omitted pole. -/
theorem entire_reciprocal_lift_of_meromorphic {f d : ℂ → ℂ} {b : ℂ}
    (hf : ∀ z, MeromorphicAt f z) (hd : Differentiable ℂ d)
    (p q : Polynomial ℂ) (hp : p.eval b ≠ 0) (hq : q.eval b = 0)
    (hrel : ∀ z, (fun w => p.eval (f w)) =ᶠ[𝓝[≠] z]
      (fun w => d w * q.eval (f w))) :
    ∃ (h : ℂ → ℂ) (_hh : Differentiable ℂ h),
      ∀ z, h =ᶠ[𝓝[≠] z] (fun w => (f w - b)⁻¹) := by
  let k := fun w => (f w - b)⁻¹
  have hk : MeromorphicOn k Set.univ := fun z _ => ((hf z).sub (MeromorphicAt.const b z)).inv
  let h := toMeromorphicNFOn k Set.univ
  refine ⟨h, fun z => ?_, fun z => hk.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)⟩
  apply AnalyticAt.differentiableAt
  apply ((meromorphicNFOn_toMeromorphicNFOn k Set.univ)
    (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hk (Set.mem_univ z)]
  exact meromorphicOrderAt_inv_sub_nonneg_of_quotient (hf z) (hd.analyticAt z) p q hp hq (hrel z)

/-- The entire reciprocal coordinate represents the inverse in the meromorphic field. -/
theorem entire_reciprocal_lift_of_plane {d : ℂ → ℂ} (hd : Differentiable ℂ d)
    (p q : Polynomial ℂ) (b : ℂ) (hp : p.eval b ≠ 0) (hq : q.eval b = 0)
    (x : MeromorphicPlane)
    (hrel : Polynomial.aeval x p =
      ofMeromorphic d (fun z => (hd.analyticAt z).meromorphicAt) * Polynomial.aeval x q) :
    ∃ (h : ℂ → ℂ) (hh : Differentiable ℂ h),
      ofMeromorphic h (fun z => (hh.analyticAt z).meromorphicAt) =
        (x - algebraMap ℂ MeromorphicPlane b)⁻¹ := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [aeval_ofMeromorphic p hf, aeval_ofMeromorphic q hf, ofMeromorphic_mul] at hrel
  have he := (ofMeromorphic_eq_iff (meromorphicAt_polyEval hf p)
    (fun z => ((hd.analyticAt z).meromorphicAt).mul (meromorphicAt_polyEval hf q z))).mp hrel
  obtain ⟨h, hh, hhe⟩ := entire_reciprocal_lift_of_meromorphic hf hd p q hp hq he
  refine ⟨h, hh, ?_⟩
  apply (inv_eq_of_mul_eq_one_left ?_).symm
  rw [algebraMap_plane]
  change ofMeromorphic (fun w => h w * (f w - b))
    (fun z => ((hh.analyticAt z).meromorphicAt).mul ((hf z).sub (MeromorphicAt.const b z))) =
      ofMeromorphic (fun _ => 1) (fun z => MeromorphicAt.const 1 z)
  apply (ofMeromorphic_eq_iff _ _).mpr
  intro z
  have hn := meromorphicOrderAt_sub_const_nonpos_of_quotient (hf z)
    (hd.analyticAt z) p q hp hq (he z)
  have hnt : meromorphicOrderAt (fun w => f w - b) z ≠ ⊤ := by
    intro ht
    simp [ht] at hn
  have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    ((hf z).sub (MeromorphicAt.const b z))).mp hnt
  filter_upwards [hhe z, hne] with w hw hnw
  rw [hw]
  exact inv_mul_cancel₀ hnw

end GaloisForLFunctions.HTGeometry
