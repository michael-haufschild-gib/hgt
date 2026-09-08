import GaloisForLFunctions.RHTower.PartialSubsetEnergyOrder
import GaloisForLFunctions.RHTower.ThreePlaneSourceMargin

/-!
# Bounded receiving displacement under finite directional supply

A uniformly available inward direction keeps a quadratic displacement
inside a fixed ball. The bound depends on the source size and directional
margin, not the number of selected elements.
-/
noncomputable section
open Finset
namespace RHTower

private lemma plane_step (z w : ℝ × ℝ) (B c : ℝ) (hB : 0<B) (hc : 0<c)
    (hw : ‖w‖≤B) (hdot : z.1*w.1+z.2*w.2≤-c*‖z‖) :
    max (2*(B^2/c+B)^2) ((z.1+w.1)^2+(z.2+w.2)^2) ≤
      max (2*(B^2/c+B)^2) (z.1^2+z.2^2) := by
  have hw0 : |w.1|≤B := (show |w.1|≤‖w‖ by simpa using norm_fst_le w).trans hw
  have hw1 : |w.2|≤B := (show |w.2|≤‖w‖ by simpa using norm_snd_le w).trans hw
  have hws0 := mul_le_mul hw0 hw0 (abs_nonneg w.1) hB.le
  have hws1 := mul_le_mul hw1 hw1 (abs_nonneg w.2) hB.le
  have hA : 0≤B^2/c := div_nonneg (sq_nonneg B) hc.le
  by_cases hz : B^2≤c*‖z‖
  · have he : (z.1+w.1)^2+(z.2+w.2)^2≤z.1^2+z.2^2 := by
      nlinarith only [hdot,hz,hws0,hws1,sq_abs w.1,sq_abs w.2]
    exact max_le_max le_rfl he
  · have hn : ‖z‖≤B^2/c := (le_div_iff₀ hc).mpr (by linarith only [hz])
    have hz0 : |z.1|≤B^2/c := (show |z.1|≤‖z‖ by simpa using norm_fst_le z).trans hn
    have hz1 : |z.2|≤B^2/c := (show |z.2|≤‖z‖ by simpa using norm_snd_le z).trans hn
    have hsum0 := (abs_add_le z.1 w.1).trans (add_le_add hz0 hw0)
    have hsum1 := (abs_add_le z.2 w.2).trans (add_le_add hz1 hw1)
    have h0 := mul_le_mul hsum0 hsum0 (abs_nonneg _) (add_nonneg hA hB.le)
    have h1 := mul_le_mul hsum1 hsum1 (abs_nonneg _) (add_nonneg hA hB.le)
    have he : (z.1+w.1)^2+(z.2+w.2)^2≤2*(B^2/c+B)^2 := by
      nlinarith only [h0,h1,sq_abs (z.1+w.1),sq_abs (z.2+w.2)]
    exact (max_le_iff.mpr ⟨le_rfl,he⟩).trans (le_max_left _ _)

/-- Uniform directional supply produces a finite distinct batch with bounded total displacement, including a prescribed initial vector. -/
theorem exists_bounded_plane_displacement_batch {α : Type*} [DecidableEq α]
    (v : α → ℝ × ℝ) (U : Finset α) (n : ℕ) (z0 : ℝ × ℝ) (B c : ℝ)
    (hB : 0<B) (hc : 0<c) (hz0 : ‖z0‖≤B) (hv : ∀ p∈U,‖v p‖≤B)
    (hdir : ∀ L⊆U,L.card<n → ∀ z : ℝ × ℝ,
      ∃ p∈U,p∉L ∧ z.1*(v p).1+z.2*(v p).2≤-c*‖z‖) :
    ∃ l : List α,l.Nodup ∧ l.length=n ∧ l.toFinset⊆U ∧
      (z0.1+∑ p∈l.toFinset,(v p).1)^2+(z0.2+∑ p∈l.toFinset,(v p).2)^2≤2*(B^2/c+B)^2 := by
  let d := fun L : Finset α => (z0.1+∑ p∈L,(v p).1,z0.2+∑ p∈L,(v p).2)
  let F := fun L : Finset α => max (2*(B^2/c+B)^2) ((d L).1^2+(d L).2^2)
  have hstart : F ∅=2*(B^2/c+B)^2 := by
    have h0 : |z0.1|≤B := (show |z0.1|≤‖z0‖ by simpa using norm_fst_le z0).trans hz0
    have h1 : |z0.2|≤B := (show |z0.2|≤‖z0‖ by simpa using norm_snd_le z0).trans hz0
    have hs0 := mul_le_mul h0 h0 (abs_nonneg _) hB.le
    have hs1 := mul_le_mul h1 h1 (abs_nonneg _) hB.le
    have hA := div_nonneg (sq_nonneg B) hc.le
    have he : z0.1^2+z0.2^2≤2*(B^2/c+B)^2 := by
      nlinarith only [hs0,hs1,sq_abs z0.1,sq_abs z0.2,hA,hB,sq_nonneg (B^2/c)]
    simpa only [F,d,sum_empty,add_zero] using max_eq_left he
  obtain ⟨l,hnd,hlen,hsub,hbound⟩ := exists_partialSubsetEnergyOrder F U n (by
    intro L hLU hLn
    obtain ⟨p,hp,hpL,hpdir⟩ := hdir L hLU hLn (d L)
    refine ⟨p,hp,hpL,?_⟩
    have he : d (insert p L)=((d L).1+(v p).1,(d L).2+(v p).2) := by
      dsimp only [d]
      rw [sum_insert hpL,sum_insert hpL]
      apply Prod.ext <;> dsimp <;> ring
    have h := plane_step (d L) (v p) B c hB hc (hv p hp) hpdir
    simpa only [F,he] using h)
  have he := hbound l.length
  rw [List.take_length,hstart] at he
  refine ⟨l,hnd,hlen,hsub,?_⟩
  exact (le_max_right _ _).trans he
end RHTower
