import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Linear return cost under fresh planar inward supply

A fixed inward margin decreases Euclidean radius by a fixed amount outside
a fixed ball. Distinct source choices therefore return any displacement
with a number of helpers linear in its initial radius. A bounded prescribed
packet requires only a fixed number of helpers, including every prefix.
-/

noncomputable section
open Finset
namespace HTGeometry

/-- Euclidean radius of a planar displacement represented in the product norm. -/
def planeDisplacementRadius (z : ℝ × ℝ) : ℝ := Real.sqrt (z.1^(2 : ℕ)+z.2^(2 : ℕ))

private lemma radius_nonneg (z : ℝ × ℝ) : 0 ≤ planeDisplacementRadius z := Real.sqrt_nonneg _
private lemma radius_sq (z : ℝ × ℝ) : (planeDisplacementRadius z)^(2 : ℕ)=z.1^(2 : ℕ)+z.2^(2 : ℕ) :=
  Real.sq_sqrt (by positivity)

private lemma radius_coord (z : ℝ × ℝ) : |z.1| ≤ planeDisplacementRadius z ∧
    |z.2| ≤ planeDisplacementRadius z := by
  have hr := radius_nonneg z
  have hs := radius_sq z
  constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2,sq_abs z.1,sq_abs z.2,
    abs_nonneg z.1,abs_nonneg z.2]

private lemma radius_le_two_norm (z : ℝ × ℝ) : planeDisplacementRadius z ≤ 2*‖z‖ := by
  have hz0 : |z.1| ≤ ‖z‖ := by simpa using norm_fst_le z
  have hz1 : |z.2| ≤ ‖z‖ := by simpa using norm_snd_le z
  have h0 := mul_le_mul hz0 hz0 (abs_nonneg _) (norm_nonneg _)
  have h1 := mul_le_mul hz1 hz1 (abs_nonneg _) (norm_nonneg _)
  nlinarith [radius_sq z,radius_nonneg z,norm_nonneg z,sq_abs z.1,sq_abs z.2]

/-- A bounded prescribed packet increases Euclidean displacement radius by at most twice its product-norm bound. -/
theorem planeDisplacementRadius_add_le {z w : ℝ × ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hw : ‖w‖ ≤ B) :
    planeDisplacementRadius (z+w) ≤ planeDisplacementRadius z+2*B := by
  have hw0 : |w.1| ≤ B := (show |w.1| ≤ ‖w‖ by simpa using norm_fst_le w).trans hw
  have hw1 : |w.2| ≤ B := (show |w.2| ≤ ‖w‖ by simpa using norm_snd_le w).trans hw
  have h0 := mul_le_mul hw0 hw0 (abs_nonneg _) hB
  have h1 := mul_le_mul hw1 hw1 (abs_nonneg _) hB
  have hz := radius_coord z
  have hd0 : z.1*w.1 ≤ planeDisplacementRadius z*B := by
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul hz.1 hw0 (abs_nonneg _) (radius_nonneg z))
  have hd1 : z.2*w.2 ≤ planeDisplacementRadius z*B := by
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul hz.2 hw1 (abs_nonneg _) (radius_nonneg z))
  have hs := radius_sq (z+w)
  simp only [Prod.fst_add,Prod.snd_add] at hs
  nlinarith [radius_sq z,radius_nonneg (z+w),radius_nonneg z,sq_abs w.1,sq_abs w.2]

/-- Inward source selection decreases radius by a fixed amount outside a fixed ball. -/
theorem planeDisplacementRadius_inward_step {z w : ℝ × ℝ} {B c : ℝ}
    (hB : 0<B) (hc : 0<c) (hw : ‖w‖ ≤ B)
    (hdot : z.1*w.1+z.2*w.2 ≤ -c*‖z‖) :
    planeDisplacementRadius (z+w) ≤
      max (4*B^(2 : ℕ)/c+2*B+c) (planeDisplacementRadius z-c/4) := by
  have hBc : 0 ≤ 4*B^(2 : ℕ)/c := by positivity
  by_cases hz : planeDisplacementRadius z ≤ 4*B^(2 : ℕ)/c+c
  · exact (planeDisplacementRadius_add_le hB.le hw).trans
      ((by linarith : planeDisplacementRadius z+2*B ≤ 4*B^(2 : ℕ)/c+2*B+c).trans (le_max_left _ _))
  have hzlarge : 4*B^(2 : ℕ)/c+c < planeDisplacementRadius z := lt_of_not_ge hz
  have hrpos : 0 ≤ planeDisplacementRadius z-c/4 := by nlinarith
  have hw0 : |w.1| ≤ B := (show |w.1| ≤ ‖w‖ by simpa using norm_fst_le w).trans hw
  have hw1 : |w.2| ≤ B := (show |w.2| ≤ ‖w‖ by simpa using norm_snd_le w).trans hw
  have h0 := mul_le_mul hw0 hw0 (abs_nonneg _) hB.le
  have h1 := mul_le_mul hw1 hw1 (abs_nonneg _) hB.le
  have hrad := mul_le_mul_of_nonneg_left (radius_le_two_norm z) hc.le
  have hlarge := mul_lt_mul_of_pos_left hzlarge hc
  have hcancel : c*(4*B^(2 : ℕ)/c+c)=4*B^(2 : ℕ)+c^(2 : ℕ) := by field_simp
  rw [hcancel] at hlarge
  have hs := radius_sq (z+w)
  simp only [Prod.fst_add,Prod.snd_add] at hs
  have hbound : planeDisplacementRadius (z+w) ≤ planeDisplacementRadius z-c/4 := by
    nlinarith [radius_sq z,radius_nonneg (z+w),radius_nonneg z,sq_abs w.1,sq_abs w.2]
  exact hbound.trans (le_max_right _ _)

private lemma max_radius_decay {R r x δ : ℝ} (hδ : 0 ≤ δ) (hr : r ≤ max R x) :
    max R (r-δ) ≤ max R (x-δ) := by
  apply max_le (le_max_left _ _)
  by_cases hx : R ≤ x
  · rw [max_eq_right hx] at hr
    exact (sub_le_sub_right hr δ).trans (le_max_right _ _)
  · rw [max_eq_left (le_of_not_ge hx)] at hr
    exact (show r-δ ≤ R by linarith).trans (le_max_left _ _)

/-- Fresh inward choices return any initial displacement to a fixed ball with a
helper count linear in its initial radius, while controlling every prefix. -/
theorem exists_planeDisplacement_return_batch {ι : Type*} [DecidableEq ι]
    (v : ι → ℝ × ℝ) (U : Finset ι) (n : ℕ) (z0 : ℝ × ℝ) (B c : ℝ)
    (hB : 0<B) (hc : 0<c) (hv : ∀ p ∈ U,‖v p‖ ≤ B)
    (hdir : ∀ L ⊆ U,L.card<n → ∀ z : ℝ × ℝ,
      ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖) :
    ∃ l : List ι,l.Nodup ∧ l.length=n ∧ l.toFinset ⊆ U ∧ ∀ k ≤ n,
      planeDisplacementRadius (z0+∑ p ∈ (l.take k).toFinset,v p) ≤
        max (4*B^(2 : ℕ)/c+2*B+c) (planeDisplacementRadius z0-(k:ℝ)*c/4) := by
  induction n with
  | zero =>
    refine ⟨[],by simp,by simp,by simp,?_⟩
    intro k hk
    have hk0 : k=0 := by omega
    simp only [hk0,List.take_zero,List.toFinset_nil,sum_empty,add_zero,Nat.cast_zero,zero_mul,zero_div,sub_zero]
    exact le_max_right _ _
  | succ n ih =>
    obtain ⟨l,hnd,hlen,hsub,hbound⟩ := ih (fun L hL hLn z => hdir L hL (by omega) z)
    let z := z0+∑ p ∈ l.toFinset,v p
    obtain ⟨p,hp,hpn,hpd⟩ := hdir l.toFinset hsub
      (by rw [List.toFinset_card_of_nodup hnd,hlen]; omega) z
    have hpnot : p ∉ l := by simpa using hpn
    have hnd' : (l++[p]).Nodup := by
      rw [List.nodup_append_comm]
      simpa using List.nodup_cons.mpr ⟨hpnot,hnd⟩
    refine ⟨l++[p],hnd',by simp [hlen],?_,?_⟩
    · simpa using insert_subset hp hsub
    · intro k hk
      by_cases hkn : k ≤ n
      · rw [List.take_append_of_le_length (by omega)]
        exact hbound k hkn
      · have hk1 : k=n+1 := by omega
        have hklong : (l++[p]).length ≤ k := by simp only [List.length_append,List.length_singleton]; omega
        rw [List.take_of_length_le hklong]
        have hz : planeDisplacementRadius z ≤
            max (4*B^(2 : ℕ)/c+2*B+c) (planeDisplacementRadius z0-(n:ℝ)*c/4) := by
          simpa only [z,← hlen,List.take_length] using hbound n le_rfl
        have hs := planeDisplacementRadius_inward_step hB hc (hv p hp) hpd
        have hb := hs.trans (max_radius_decay (by positivity : 0 ≤ c/4) hz)
        have he : z0+∑ q ∈ (l++[p]).toFinset,v q=z+v p := by
          simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,insert_empty_eq,union_singleton]
          rw [sum_insert hpn]
          dsimp [z]
          abel
        rw [he,hk1]
        rw [show planeDisplacementRadius z0-((n+1:ℕ):ℝ)*c/4 =
          planeDisplacementRadius z0-(n:ℝ)*c/4-c/4 by push_cast; ring]
        exact hb

/-- A fixed number of fresh inward helpers restores the ball after one arbitrary bounded packet. -/
theorem exists_planeDisplacement_restoring_batch {ι : Type*} [DecidableEq ι]
    (v : ι → ℝ × ℝ) (U : Finset ι) (K : ℕ) (z0 w : ℝ × ℝ) (B c : ℝ)
    (hB : 0<B) (hc : 0<c) (hK : 2*B ≤ (K:ℝ)*c/4)
    (hz : planeDisplacementRadius z0 ≤ 4*B^(2 : ℕ)/c+2*B+c) (hw : ‖w‖ ≤ B)
    (hv : ∀ p ∈ U,‖v p‖ ≤ B)
    (hdir : ∀ L ⊆ U,L.card<K → ∀ z : ℝ × ℝ,
      ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖) :
    ∃ l : List ι,l.Nodup ∧ l.length=K ∧ l.toFinset ⊆ U ∧
      (∀ k ≤ K,planeDisplacementRadius (z0+w+((l.take k).map v).sum) ≤ 4*B^(2 : ℕ)/c+4*B+c) ∧
      planeDisplacementRadius (z0+w+(l.map v).sum) ≤ 4*B^(2 : ℕ)/c+2*B+c := by
  obtain ⟨l,hnd,hlen,hsub,hbound⟩ := exists_planeDisplacement_return_batch v U K (z0+w) B c hB hc hv hdir
  have hstart : planeDisplacementRadius (z0+w) ≤ 4*B^(2 : ℕ)/c+4*B+c := by
    have hh := planeDisplacementRadius_add_le (z:=z0) hB.le hw
    linarith
  refine ⟨l,hnd,hlen,hsub,?_,?_⟩
  · intro k hk
    have hb := hbound k hk
    rw [List.sum_toFinset _ (show (l.take k).Nodup from hnd.take)] at hb
    apply hb.trans
    apply max_le
    · linarith
    · have hn : 0 ≤ (k:ℝ)*c/4 := by positivity
      linarith
  · have hb := hbound K le_rfl
    rw [← hlen,List.take_length,List.sum_toFinset _ hnd,hlen] at hb
    exact hb.trans (max_le le_rfl (by linarith))

end HTGeometry
