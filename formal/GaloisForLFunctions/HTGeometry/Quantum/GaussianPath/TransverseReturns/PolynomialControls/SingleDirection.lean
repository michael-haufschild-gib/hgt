import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PolynomialControls.PinnedCoordinates

/-! # A pinned spectral pencil at independent clock and pulse resolutions -/
open Real Finset
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section

/-- A direction constant on the synchronized pair pays only a coarse
bin on the third energy level. All remaining levels use fine bins. -/
theorem two_scale_pencil {I : Type*} [Fintype I] [DecidableEq I] (E F : I → ℝ)
    (a b c : I) (hab : a≠b) (hca : c≠a) (hcb : c≠b) {τ : ℝ} (z : ℤ)
    (hturn : τ*(E b-E a)/(2*π)=z) (hpin : F b=F a) (hmove : F c≠F a)
    {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    ∃ q : ℕ, 0<q ∧ q≤m*n^(Fintype.card I-3) ∧
      ∃ β : ℝ, |β|≤(2*π/|F c-F a|)/(m:ℝ) ∧
        ∀ j, latticeClose (((q:ℝ)*τ*(E j-E a)-β*(F j-F a))/(2*π)) (1/(n:ℝ)) := by
  classical
  let S : Finset I := {c}
  let k : S := ⟨c,mem_singleton_self _⟩
  let X (i : I) := τ*(E i-E a)/(2*π)
  let g (i : I) := (F i-F a)/(F c-F a)
  have he := sub_ne_zero.mpr hmove
  have hδ (j l : S) : g l=if j=l then 1 else 0 := by
    have hl : l.val=c := mem_singleton.mp l.property
    rw [if_pos (Subsingleton.elim j l)]
    simp only [g,hl,div_self he]
  obtain ⟨q,hq,hN,d,hd,hw⟩ := pinned_coordinates S a b hab
    (fun h => hca (mem_singleton.mp h).symm) (fun h => hcb (mem_singleton.mp h).symm)
    X 0 z (by simp [X]) hturn (fun _ i => g i)
    (fun _ => by simp [g]) (fun _ => by simp [g,hpin]) hδ hm hn
  let β := 2*π*d k/(F c-F a)
  refine ⟨q,hq,by simpa only [S,card_singleton,pow_one,Nat.sub_sub] using hN,β,?_,?_⟩
  · have hβ : |β|=(2*π/|F c-F a|)*|d k| := by
      dsimp only [β]
      rw [abs_div,abs_mul,abs_of_pos two_pi_pos]
      ring
    calc
      _ = _ := hβ
      _ ≤ (2*π/|F c-F a|)*(1/(m:ℝ)) :=
        mul_le_mul_of_nonneg_left (hd k).le (div_nonneg two_pi_pos.le (abs_nonneg _))
      _ = _ := by ring
  · intro i
    have h := hw i
    rw [Fintype.sum_unique,show (default:S)=k from Subsingleton.elim ..] at h
    convert h using 2
    dsimp only [β,X,g]
    field_simp
    <;> ring

#print axioms two_scale_pencil
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
