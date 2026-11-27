import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BufferedOwners
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PacketCount

/-! # Circuit counts for one cut in each full buffer -/

open Real MeasureTheory ProbabilityTheory Finset Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n N : ℕ}

private theorem count_divisor {j c b k g : ℕ} (hc : c=b)
    (h : j*2^(c-k)≤3^g*4^(c-g)) :
    (j:ℝ)≤((3^g*4^(b-g):ℕ):ℝ)/(2:ℝ)^(b-k) := by
  subst b
  apply (le_div_iff₀ (pow_pos two_pos _)).mpr
  exact_mod_cast h

def bufferedMask (hN : 0<N) (p : fullBuffers n N→Fin N) (j : packetIndices n N→Bool) :=
  cutLabels (bufferedOwner (n:=n) hN p) ∪ selectedLabels (sites (bufferedOwner (n:=n) hN p)) j

def bufferedFit (hN : 0<N) (s : ℕ) (e t F E w R : ℝ)
    (p : fullBuffers n N→Fin N) :=
  affordableDraw n s e t ∩ cutBounds (cutLabels (bufferedOwner (n:=n) hN p)) F E w R

/-- Bound the number of successful dilations before integrating over the selected partition. -/
theorem buffered_count (hN : 0<N) (p : fullBuffers n N→Fin N)
    (r s g : ℕ) {t a w R : ℝ} (ht : 0≤t) (ha : 0≤a) (hw : 0≤w) (hR : 0≤R)
    (e F E : ℝ) {m C : ℝ} (hm : 0 ≤ m) (hC : 0<C) :
    open Classical in
    let b := (n+1)/(3*N)+1
    let L := 2*(3*N)
    let δ := t^2*a*((84:ℝ)*(9*((n+1)/(3*N)):ℕ)*w*R)
    π≤2*(t*a)*m → 2*(e+δ)+(t*a)*C*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1 →
    b*m+g*(sqrt L*C)+sqrt L/C*E<F/(1+a) → ∀ z : PathLabel n→ℝ,
    ((Finset.univ.filter fun j => expand (bufferedMask (n:=n) hN p j) (1+a) z∈
      bufferedFit (n:=n) hN s e t F E w R p).card:ℝ) ≤
      ((3^g*4^(b-g):ℕ):ℝ)/(2:ℝ)^(b-2*s/(r+1)) := by
  classical
  intro b L δ hcross htest hfield z
  let T := cutLabels (bufferedOwner (n:=n) hN p)
  have hprice : t^2*a*(84*(T.card:ℝ)*w*R)≤δ := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) ha)
    apply mul_le_mul_of_nonneg_right _ hR
    apply mul_le_mul_of_nonneg_right _ hw
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cutLabel_count (n:=n) hN p)) (by norm_num)
  have hp := weak_partition_count (bufferedOwner (n:=n) hN p) L r s g (bufferedOwner_size (n:=n) hN p)
    ht ha hw hR e F E hm hC hcross (lt_of_le_of_lt
      (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (le_refl e) hprice) zero_le_two) le_rfl) htest)
  have hcard : Fintype.card (packetIndices n N)=b := Fintype.card_fin _
  have hn := hp (by rwa [hcard]) z
  apply count_divisor hcard
  refine le_trans ?_ hn
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro j hj
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,bufferedMask,bufferedFit] using hj

#print axioms buffered_count
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
