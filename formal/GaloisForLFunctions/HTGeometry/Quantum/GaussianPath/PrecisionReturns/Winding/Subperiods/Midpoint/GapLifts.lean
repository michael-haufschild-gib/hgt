import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Arc

/-! # Phase lifts at the midpoint of two scalar visits -/

open Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
open EmptyVisitFlux
noncomputable section
variable {I : Type*}

/-- Real lifts in an interval starting at a common phase c. -/
def lifted (w : I → ℝ) (t r c : ℝ) (z : I → ℤ) : Prop :=
  ∀ i, t*w i-c-(z i:ℝ)∈Icc (0:ℝ) r

theorem arc_iff_lifted [Fintype I] [Nonempty I] {w : I → ℝ} {t r : ℝ} (hr : 0≤r) :
    flow w t∈enclosingUnitArc r ↔ ∃ c z, lifted w t r c z := by
  rw [anchored_iff hr]
  constructor
  · rintro ⟨b,z,h⟩
    refine ⟨t*w b,z,fun i => ?_⟩
    simpa only [mul_sub] using h i
  · rintro ⟨c,z,h⟩
    let E (i : I) := t*w i-c-(z i:ℝ)
    obtain ⟨b,_,hb⟩ := Finset.univ.exists_min_image E Finset.univ_nonempty
    refine ⟨b,fun i => z i-z b,fun i => ?_⟩
    have he : t*(w i-w b)-((z i-z b:ℤ):ℝ)=E i-E b := by
      simp only [E,Int.cast_sub,mul_sub]
      ring
    rw [he]
    exact ⟨sub_nonneg.mpr (hb i (Finset.mem_univ _)),(sub_le_self (E i) (h b).1).trans (h i).2⟩

/-- With the bulk phase removed, midpoint lifts consist of a half-integer
and the mean of the endpoint residuals. -/
private theorem midpoint_lift {w : I → ℝ} {u v r c b : ℝ} {p q : I → ℤ}
    (hu : lifted w u r c p) (hv : lifted w v r b q) (i : I) :
    (u+v)/2*w i-(c+b)/2-((p i+q i:ℤ):ℝ)/2∈Icc (0:ℝ) r := by
  rw [Int.cast_add]
  constructor <;> linarith only [(hu i).1,(hv i).1,(hu i).2,(hv i).2]

/-- The eigenphases lie in two arcs, a half turn apart, each with the
original width. If they also fit in an arc shorter than half a turn minus
that width, the two clusters use the same parity and one original arc suffices. -/
theorem midpoint_arc_alternative [Fintype I] [Nonempty I] {w : I → ℝ} {u v r : ℝ} (hr : 0≤r)
    (hu : flow w u∈enclosingUnitArc r) (hv : flow w v∈enclosingUnitArc r) :
    let t := (u+v)/2
    flow w t∈enclosingUnitArc (1/2+r) ∧
      ∀ s : ℝ, 0 ≤ s → s+r < 1/2 → flow w t ∈ enclosingUnitArc s → flow w t ∈ enclosingUnitArc r := by
  classical
  intro t
  obtain ⟨c,p,hp⟩ := (arc_iff_lifted hr).mp hu
  obtain ⟨b,q,hq⟩ := (arc_iff_lifted hr).mp hv
  let h := (c+b)/2
  let n (i : I) := p i+q i
  let E (i : I) := t*w i-h-(n i:ℝ)/2
  have hE (i : I) : E i∈Icc (0:ℝ) r := midpoint_lift hp hq i
  constructor
  · apply (arc_iff_lifted (by linarith only [hr] : (0:ℝ)≤1/2+r)).mpr
    refine ⟨h,fun i => n i/2,fun i => ?_⟩
    have hk : (n i:ℝ)=((n i%2:ℤ):ℝ)+2*((n i/2:ℤ):ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (n i) 2).symm
    have hl : (0:ℝ)≤((n i%2:ℤ):ℝ) := by exact_mod_cast Int.emod_nonneg (n i) (by decide : (2:ℤ)≠0)
    have hh : ((n i%2:ℤ):ℝ)≤1 := by exact_mod_cast (show n i%2≤1 by omega)
    change t*w i-h-((n i/2:ℤ):ℝ)∈Icc (0:ℝ) (1/2+r)
    obtain ⟨he₀,he₁⟩ := hE i
    dsimp only [E] at he₀ he₁
    exact ⟨by linarith only [hk,hl,he₀],by linarith only [hk,hh,he₁]⟩
  · intro s hs hsmall hsfit
    obtain ⟨γ,y,hy⟩ := (arc_iff_lifted hs).mp hsfit
    let i₀ : I := Classical.arbitrary I
    let F (i : I) := t*w i-γ-(y i:ℝ)
    have hdiff (i : I) : n i-n i₀=2*(y i-y i₀) := by
      let k := n i-n i₀-2*(y i-y i₀)
      have heq : (k:ℝ)=2*(F i-F i₀)-2*(E i-E i₀) := by
        dsimp only [k,F,E]
        push_cast
        ring
      have hbound : (-1:ℝ)<(k:ℝ) ∧ (k:ℝ)<1 := by
        rw [heq]
        have fi : F i∈Icc (0:ℝ) s := hy i
        have f₀ : F i₀∈Icc (0:ℝ) s := hy i₀
        constructor <;> linarith only [fi.1,fi.2,f₀.1,f₀.2,(hE i).1,(hE i).2,(hE i₀).1,(hE i₀).2,hsmall]
      have hk : (-1:ℤ)<k ∧ k<1 := by exact_mod_cast hbound
      exact sub_eq_zero.mp (show k=0 by omega)
    apply (arc_iff_lifted hr).mpr
    refine ⟨h+(n i₀:ℝ)/2,fun i => y i-y i₀,fun i => ?_⟩
    have he : (n i:ℝ)-(n i₀:ℝ)=2*((y i:ℝ)-(y i₀:ℝ)) := by exact_mod_cast hdiff i
    have hlift : t*w i-(h+(n i₀:ℝ)/2)-((y i-y i₀:ℤ):ℝ)=E i := by
      rw [Int.cast_sub]
      dsimp only [E]
      linarith only [he]
    rw [hlift]
    exact hE i

#print axioms midpoint_arc_alternative
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
