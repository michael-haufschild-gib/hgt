import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.OneSite

/-! # Full projective spectral rank at a tilted, uncoupled product Hamiltonian -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- A word occupies a contiguous suffix. Each occupied site contributes one
or two copies of its physical coordinate. -/
inductive Suffix : (n : ℕ) → List (Fin n) → Prop
  | empty (n : ℕ) : Suffix n []
  | append {n : ℕ} {v : List (Fin n)} (j : Bool) : Suffix n v → Suffix (n+1) (letters j v)

theorem Suffix.length_le {n : ℕ} {v : List (Fin n)} (h : Suffix n v) : v.length≤2*n := by
  induction h with
  | empty n => simp
  | append j _ ih => rw [letters_length]; cases j <;> simp only [order] <;> omega

private theorem nextLabels_suffix {n : ℕ} {I : Type*} [DecidableEq I]
    (k : I) (w : I→List (Fin n)) (hw : ∀ i, Suffix n (w i)) :
    ∀ i, Suffix (n+1) (nextLabels k w i) := by
  rintro (i|i) <;> by_cases h : i=k <;> simp only [nextLabels,Sum.elim_inl,Sum.elim_inr,h,if_true,if_false]
  · exact .empty _
  · exact .append _ (hw i)
  · exact .empty _
  · exact .append _ (hw i)

private theorem directed_chart (n : ℕ) :
    ∃ (B : Fin (n+1)→ℕ) (k : Config (n+1)) (w : Config (n+1)→List (Fin n))
      (f : Config (n+1) → Controls n × ℂ → ℂ),
      (∀ i, Suffix n (w i)) ∧ Function.Injective (fun l => f l 0) ∧
      (∀ l, AnalyticAt ℂ (f l) 0 ∧ ∀ᶠ p : Controls n × ℂ in 𝓝 0,
        matrixCharpolyRelation (background n B p.1+p.2 • lastPauli n 0,f l p)=0) ∧
      ∀ j, (readings k (fun i => (w i).map axis) j f).det≠0 := by
  induction n with
  | zero =>
    obtain ⟨B,k,f,hi,hf,hm⟩ := one_site_chart
    exact ⟨B,k,fun _ => [],f,fun _ => .empty _,hi,hf,hm⟩
  | succ n ih =>
    obtain ⟨B,k,w,f,hl,hi,hf,hd⟩ := ih
    obtain ⟨a,g,hin,hg,hm⟩ := extend_chart (background n B) (lastPauli n 0) k
      (fun i => (w i).map axis) f (background_analytic n B) hi hf hd
    let d := blockConfig (n+1)
    let v := nextLabels k w
    let B' : Fin ((n+1)+1)→ℕ := Fin.snoc (α:=fun _ => ℕ) B a
    let F (l : Config (n+1)⊕Config (n+1)) := g l ∘ splitEarlier n
    have h₀ : splitEarlier n 0=0 := map_zero _
    have hF : Function.Injective (fun l => F l 0) := by simpa only [F,Function.comp_apply,h₀] using hin
    refine ⟨B',d (.inl k),fun i => v (d.symm i),fun l => F (d.symm l),
      fun i => nextLabels_suffix k w hl (d.symm i),hF.comp d.symm.injective,?_,?_⟩
    · intro l
      let j := d.symm l
      have ha : AnalyticAt ℂ (g j) (splitEarlier n 0) := h₀.symm ▸ (hg j).1
      refine ⟨ha.comp ((splitEarlier n).analyticAt _),?_⟩
      have ht : Tendsto (splitEarlier n) (𝓝 0) (𝓝 0) := by
        simpa only [h₀] using ((splitEarlier n).continuous.continuousAt (x:=0)).tendsto
      filter_upwards [ht.eventually (hg j).2] with p hp
      have hphys := (relation_onRegister (n+1)
        (baseNext (background n B) (lastPauli n 0) a (splitControls n p.1)+p.2 • tip (Config (n+1)))
        (F j p)).trans hp
      simpa only [onRegister_add,onRegister_smul,onRegister_tip,background,B',Fin.snoc_last,Fin.snoc_castSucc] using hphys
    · intro j
      rw [readings_reindex d (.inl k) (fun i => (v i).map axis) j F]
      change (readings (.inl k) (fun i => ((nextLabels k w i).map axis)) j
        (fun l => g l ∘ splitEarlier n)).det≠0
      rw [readings_coordinates]
      simp only [split_nextLabels]
      exact hm j

/-- On N=n+1 spins, a single product background has full projective spectral rank
using only N physical controls. For each terminal order j, the all-ones row and
the remaining mixed energy rows form a nonsingular square matrix. The first-order
terminal basis has total order at most 2N−1 and the second-order basis at most 2N. -/
theorem product_full_projective_rank (n : ℕ) :
    ∃ (B : Fin (n+1)→ℕ) (k : Config (n+1)) (f : Config (n+1) → Controls (n+1)→ℂ),
      Function.Injective (fun l => f l 0) ∧
      (∀ l, AnalyticAt ℂ (f l) 0 ∧ ∀ᶠ p in 𝓝 0, matrixCharpolyRelation (chain B p,f l p)=0) ∧
      ∀ j : Bool, ∃ w : Config (n+1)→List (Fin (n+1)),
        (∀ i, ∃ v, Suffix n v ∧ w i=letters j v) ∧
        (∀ i, (w i).length≤2*n+order j) ∧
        (of fun i l => if i=k then (1:ℂ) else mixed (w i) (f l) 0).det≠0 := by
  obtain ⟨B,k,w,f,hl,hi,hf,hm⟩ := directed_chart n
  have h₀ : splitControls n 0=0 := map_zero _
  refine ⟨B,k,fun l => f l ∘ splitControls n,by simpa only [Function.comp_apply,h₀] using hi,?_,?_⟩
  · intro l
    have ha : AnalyticAt ℂ (f l) (splitControls n 0) := h₀.symm ▸ (hf l).1
    refine ⟨ha.comp ((splitControls n).analyticAt _),?_⟩
    have ht : Tendsto (splitControls n) (𝓝 0) (𝓝 0) := by
      simpa only [h₀] using ((splitControls n).continuous.continuousAt (x:=0)).tendsto
    exact ht.eventually (hf l).2
  · intro j
    refine ⟨fun i => letters j (w i),fun i => ⟨w i,hl i,rfl⟩,
      fun i => by rw [letters_length]; have h := (hl i).length_le; omega,?_⟩
    have he : (of fun i l => if i=k then (1:ℂ) else mixed (letters j (w i)) (f l ∘ splitControls n) 0) =
        readings k (fun i => (w i).map axis) j f := by
      ext i l
      simp only [of_apply,readings,Function.comp_def,mixed_letters]
    rw [he]
    exact hm j

#print axioms product_full_projective_rank
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
