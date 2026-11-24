import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.DeterminantLimit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.PhysicalField

/-! # Extending a simple full-rank spectral chart by one physical spin -/
open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local notation "P" => (E × ℂ) × ℂ

/-- A single finite integer splitting works for every energy level, every old
word and both orders of the terminal reading. The appended field has its
physical coefficient, and the old terminal operator appears only on the new bond. -/
theorem extend_chart (H : E→M) (A : M) (k : I) (w : I→List E) (f : I→E × ℂ → ℂ)
    (hH : AnalyticAt ℂ H 0) (hi : Function.Injective (fun l => f l 0))
    (hf : ∀ l, AnalyticAt ℂ (f l) 0 ∧ ∀ᶠ p : E × ℂ in 𝓝 0,
      matrixCharpolyRelation (H p.1+p.2 • A,f l p)=0)
    (hd : ∀ m, (readings k w m f).det≠0) :
    ∃ (n : ℕ) (g : I⊕I → P→ℂ), Function.Injective (fun l => g l 0) ∧
      (∀ l, AnalyticAt ℂ (g l) 0 ∧ ∀ᶠ p : P in 𝓝 0,
        matrixCharpolyRelation (baseNext H A n p.1+p.2 • tip I,g l p)=0) ∧
      ∀ m, (readings (.inl k) (nextWords k w) m g).det≠0 := by
  have hr (l : I) : (H 0).charpoly.eval (f l 0)=0 := by
    simpa only [Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero,matrixCharpolyRelation,←Matrix.eval_charpoly]
      using (hf l).2.self_of_nhds
  have ht (b : Bool) (l : I) := tilted_branch b H A (f l) hH (hf l).1 (hf l).2
    (simple_packet (H 0) (fun l => f l 0) hi hr l)
  choose e ha hzero hπ hred using ht
  let F (n : ℕ) : I⊕I → P→ℂ :=
    Sum.elim (fun l => energy false (e false l) n) (fun l => energy true (e true l) n)
  have hscale : Tendsto (fun n => ((0:P),inverseHeight n)) atTop (𝓝 0) :=
    tendsto_const_nhds.prodMk_nhds inverseHeight_tendsto
  have hl (b : Bool) (l : I) : Tendsto (fun n => e b l (0,inverseHeight n)) atTop (𝓝 (f l 0)) := by
    rw [←hzero b l]
    exact (ha b l).continuousAt.tendsto.comp hscale
  have hsep : ∀ᶠ n in atTop, Function.Injective (fun l => F n l 0) := by
    have h := separated_sectors _ hi _ _ (hl false) (hl true)
    filter_upwards [h] with n hn
    have he : (fun l => F n l 0) = Sum.elim
        (fun l => height n+e false l (0,inverseHeight n)) (fun l => -height n+e true l (0,inverseHeight n)) := by
      funext l
      cases l <;> simp [F,energy,sign,splitting]
    rwa [he]
  have hm : ∀ᶠ n in atTop, ∀ j, (readings (.inl k) (nextWords k w) j (F n)).det≠0 :=
    Filter.eventually_all.mpr (enlarged_minor k w f e ha hπ hd)
  have hfinite := Filter.eventually_all.mpr (fun b =>
    Filter.eventually_all.mpr (fun l => finite_energy b H A (e b l) (ha b l) (hred b l)))
  obtain ⟨n,hin,hmn,hfn⟩ := (hsep.and (hm.and hfinite)).exists
  let u := inverseHeight n
  let cut (p : P) : P := (p.1,u*p.2)
  have hc₀ : cut 0=0 := by change ((0:E × ℂ),u*0)=0; rw [mul_zero]; rfl
  have hc : AnalyticAt ℂ cut 0 := analyticAt_fst.prod (analyticAt_const.mul analyticAt_snd)
  have hct : Tendsto cut (𝓝 0) (𝓝 0) := by simpa only [hc₀] using hc.continuousAt.tendsto
  refine ⟨n,fun l => F n l ∘ cut,by simpa only [Function.comp_apply,hc₀] using hin,?_,?_⟩
  · intro l
    have hs : AnalyticAt ℂ (F n l) 0 ∧ ∀ᶠ p : P in 𝓝 0,
        matrixCharpolyRelation (physical (H p.1.1) (p.1.2 • A) ((3/5)*height n)
          ((4/5+p.2)*height n),F n l p)=0 := by
      cases l with
      | inl i => exact hfn false i
      | inr i => exact hfn true i
    refine ⟨(show AnalyticAt ℂ (F n l) (cut 0) by simpa only [hc₀] using hs.1).comp hc,?_⟩
    filter_upwards [hct.eventually hs.2] with p hp
    simpa only [cut,u,physical_field,Function.comp_apply] using hp
  · intro j
    exact readings_scaled_ne (.inl k) (nextWords k w) j (F n) (one_div_ne_zero (height_ne_zero n)) (hmn j)

#print axioms extend_chart
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
