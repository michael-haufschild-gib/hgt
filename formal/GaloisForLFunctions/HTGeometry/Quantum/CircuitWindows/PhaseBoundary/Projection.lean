import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.LiftCertificate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SimpleRoot

/-! # Real projection preserves local polynomial certificates -/
open Polynomial Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A X : Type*} [CommRing A] [TopologicalSpace X]

/-- Every member has a neighborhood where one vanishing equation suffices
for membership. The equation may depend on the chosen member. -/
def LocallyCertified (ρ : X → A →+* ℝ) (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ a : A, ρ x a = 0 ∧ ∀ᶠ z in 𝓝 x, ρ z a = 0 → z ∈ S

/-- Append one real witness to the evaluation variables. -/
def appendEval (ρ : X → A →+* ℝ) (z : X × ℝ) : A[X] →+* ℝ :=
  eval₂RingHom (ρ z.1) z.2

theorem continuous_appendEval (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a)
    (p : A[X]) : Continuous fun z : X × ℝ => appendEval ρ z p := by
  change Continuous (fun z : X × ℝ => p.eval₂ (ρ z.1) z.2)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval₂_add]
    simpa only [Pi.add_def] using hp.add hq
  | monomial n a =>
    simpa only [eval₂_monomial,Pi.mul_def,Pi.pow_def,Function.comp_def] using ((hc a).comp continuous_fst).mul (continuous_snd.pow n)

private theorem real_root_of_crossing (p : ℝ[X]) {l r : ℝ} (hlr : l ≤ r)
    (h : p.eval l * p.eval r < 0) : ∃ z ∈ Icc l r, p.eval z = 0 := by
  rcases mul_neg_iff.mp h with h|h
  · exact intermediate_value_Icc' hlr p.continuousOn ⟨h.2.le,h.1.le⟩
  · exact intermediate_value_Icc hlr p.continuousOn ⟨h.1.le,h.2.le⟩

/-- The projected set retains a local certificate, even at a repeated root
or a point where the specialized polynomial vanishes identically. -/
theorem LocallyCertified.fst_image {ρ : X → A →+* ℝ}
    (hc : ∀ a, Continuous fun x => ρ x a) {S : Set (X × ℝ)}
    (hs : LocallyCertified (appendEval ρ) S) : LocallyCertified ρ (Prod.fst '' S) := by
  rintro _ ⟨⟨x,y⟩,hxy,rfl⟩
  obtain ⟨p,hp,hw⟩ := hs (x,y) hxy
  obtain ⟨U,hU,V,hV,hbox⟩ := mem_nhds_prod_iff.mp hw
  change p.eval₂ (ρ x) y = 0 at hp
  by_cases hz : p.map (specialize (ρ x)) = 0
  · have h0 : p.map (ρ x) = 0 := by
      change p.map ((valueField (ρ x)).subtype.comp (specialize (ρ x))) = 0
      rw [←Polynomial.map_map,hz,Polynomial.map_zero]
    refine ⟨coefficientSquares p,(coefficientSquares_zero_iff ..).2 h0,?_⟩
    filter_upwards [hU] with z hzU h
    refine ⟨(z,y),hbox ⟨hzU,mem_of_mem_nhds hV⟩ ?_,rfl⟩
    change p.eval₂ (ρ z) y = 0
    rw [eval₂_eq_eval_map,(coefficientSquares_zero_iff ..).1 h,eval_zero]
  · obtain ⟨g,d,P,hg,hd,hP,hder,hroot⟩ := simple_factor_certificate (ρ x) p y hp hz
    have hsimp : (P.map (ρ x)).derivative.eval y ≠ 0 := by
      rwa [Polynomial.derivative_map,eval_map]
    obtain ⟨l,r,hlr,hsub,hsign⟩ := sign_bracket (P.map (ρ x)) y (by rwa [eval_map]) hsimp hV
    have cont (t : ℝ) : Continuous fun z => P.eval₂ (ρ z) t :=
      (continuous_appendEval ρ hc P).comp (continuous_id.prodMk continuous_const)
    have ht : ∀ᶠ z in 𝓝 x, P.eval₂ (ρ z) l * P.eval₂ (ρ z) r < 0 := by
      apply ((cont l).mul (cont r)).continuousAt.eventually_lt continuousAt_const
      simpa only [eval_map,Pi.mul_apply] using hsign
    refine ⟨g,hg,?_⟩
    filter_upwards [hU,ht,(hc d).continuousAt.eventually_ne hd] with z hzU hsg hdz hg'
    obtain ⟨w,hw,he⟩ := real_root_of_crossing (P.map (ρ z)) hlr (by simpa only [eval_map] using hsg)
    exact ⟨(z,w),hbox ⟨hzU,hsub hw⟩ (hroot _ w hg' hdz (by rwa [eval_map] at he)),rfl⟩

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
