import GaloisForLFunctions.HTGeometry.InwardPlanePrescribedStream
import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedWindowRepair

/-!
# Linear helper cost for actual prescribed prime streams

Literal bounded-quotient packets admit a fixed inward margin after arbitrary
finite depletion within the signed-window capacity. Interleaving a fixed
number of helpers per prescribed prime keeps every two-coordinate signed
prefix displacement on the square-root scale. One final square-root-sized
reserve batch pays the complete successor-envelope error and lowers that
envelope by the cutoff. The construction preserves prescribed relative order.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
open HTGeometry

private lemma physical_displacement_bound (M : ℕ) (P L : Finset ℕ) {R : ℝ}
    (hM : 0<M) (hR : 0 ≤ R)
    (hz : planeDisplacementRadius (∑ p ∈ L,mobiusDivisorTwoPlanePacket M p P) ≤ R) :
    |∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
      |∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}| ≤ 2*R*Real.sqrt M := by
  let z : ℝ × ℝ := ∑ p ∈ L,mobiusDivisorTwoPlanePacket M p P
  have hr : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  have hsq : z.1^(2 : ℕ)+z.2^(2 : ℕ) ≤ R^(2 : ℕ) := by
    have hs : (planeDisplacementRadius z)^(2 : ℕ) ≤ R^(2 : ℕ) :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hR).mpr hz
    dsimp only [planeDisplacementRadius] at hs
    rw [Real.sq_sqrt (by positivity)] at hs
    exact hs
  have habs : |z.1|+|z.2| ≤ 2*R := by
    nlinarith [sq_abs z.1,sq_abs z.2,sq_nonneg (|z.1|-|z.2|),abs_nonneg z.1,abs_nonneg z.2]
  have hx : (∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)=Real.sqrt M*z.1 := by
    dsimp only [z]
    rw [Prod.fst_sum]
    simp only [mobiusDivisorTwoPlanePacket]
    rw [← sum_div]
    field_simp
  have hy : (∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})=Real.sqrt M*z.2 := by
    dsimp only [z]
    rw [Prod.snd_sum]
    simp only [mobiusDivisorTwoPlanePacket]
    rw [← sum_div]
    field_simp
  rw [hx,hy,abs_mul,abs_mul,abs_of_pos hr]
  nlinarith only [mul_le_mul_of_nonneg_left habs hr.le]

set_option maxHeartbeats 800000 in
/-- A complete prescribed bounded-quotient stream uses only a fixed number of helpers
per prescribed prime and one final square-root reserve payment. Every prefix has a
uniform quadratic successor envelope, and the final envelope strictly decreases. -/
theorem exists_mobiusDivisor_prescribed_stream_repair :
    ∃ b K : ℕ, ∃ H : ℝ,15 ≤ b ∧ 0 < H ∧ ∀ C : ℝ,0<C → ∃ A C' : ℝ,0<A ∧ 0<C' ∧
      ∀ N : ℕ,1 ≤ N →
        let M := 14*(b+1)*N
        ∀ P : Finset ℕ,mobiusDivisorCoupledTwoCore ⊆ P → 2 ∉ P →
          (∀ p ∈ mobiusDivisorCoupledTwoPool b N,p ∉ P) →
          mobiusDivisorSuccessorEnvelope M P ≤ C*(M:ℝ)^(2 : ℕ) →
          ∀ t : List ℕ,t.Nodup →
            (∀ p ∈ t,p.Prime ∧ p<M ∧ p ∉ P ∧ 15 ≤ p ∧ M/p ≤ 14) →
            (K+1)*t.length+⌈A*Real.sqrt M⌉₊ ≤ mobiusDivisorCoupledTwoCapacity b N-1 →
            ∃ l : List ℕ,l.Nodup ∧ t.Sublist l ∧
              l.length=(K+1)*t.length+⌈A*Real.sqrt M⌉₊ ∧
              l.toFinset ⊆ t.toFinset ∪ mobiusDivisorCoupledTwoPool b N ∧
              (∀ k : ℕ,
                |∑ p ∈ (l.take k).toFinset, Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
                |∑ p ∈ (l.take k).toFinset, Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}| ≤ H*Real.sqrt M) ∧
              (∀ k : ℕ,mobiusDivisorSuccessorEnvelope M (P ∪ (l.take k).toFinset) ≤ C'*(M:ℝ)^(2 : ℕ)) ∧
              mobiusDivisorSuccessorEnvelope M (P ∪ l.toFinset)+(M:ℝ) ≤ mobiusDivisorSuccessorEnvelope M P := by
  obtain ⟨b,c,d,hb,hc,hd,hgeometry⟩ := exists_mobiusDivisorTwoPlaneWindowGeometry
  obtain ⟨K,hK⟩ := exists_nat_ge (72/c)
  have hKpay : 18 ≤ (K:ℝ)*c/4 := by
    have hh := (div_le_iff₀ hc).mp hK
    nlinarith
  let R : ℝ := 4*9^(2 : ℕ)/c+2*9+c
  let H : ℝ := 2*(R+18)
  have hR : 0<R := by dsimp [R]; positivity
  have hH : 0<H := by dsimp [H]; positivity
  refine ⟨b,K,H,hb,hH,?_⟩
  intro C hC
  let A : ℝ := (2*Real.sqrt C*H+H^(2 : ℕ)+1)/d
  let C' : ℝ := C+2*Real.sqrt C*H+H^(2 : ℕ)
  have hA : 0<A := by dsimp [A]; positivity
  have hC' : 0<C' := by dsimp [C']; positivity
  refine ⟨A,C',hA,hC',?_⟩
  intro N hN
  let M := 14*(b+1)*N
  have hM : 2<M := by dsimp [M]; nlinarith
  have hMr : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<M by omega))
  dsimp only
  intro P hP h2 hfresh hE t htnd ht hcap
  obtain ⟨hv,hreserve,hdir⟩ := hgeometry N hN P hP h2 hfresh
  let v : ℕ → ℝ × ℝ := fun p => mobiusDivisorTwoPlanePacket M p P
  let W := mobiusDivisorCoupledTwoPool b N
  let U := W \ t.toFinset
  let n : ℕ := ⌈A*Real.sqrt M⌉₊
  have hdirU : ∀ L ⊆ U,L.card<K*t.length → ∀ z : ℝ × ℝ,
      ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖ := by
    intro L hL hLc z
    have hcard : (L ∪ t.toFinset).card< mobiusDivisorCoupledTwoCapacity b N-1 := by
      have hh := card_union_le L t.toFinset
      rw [List.toFinset_card_of_nodup htnd] at hh
      nlinarith
    obtain ⟨p,hp,hpn,hpd⟩ := hdir 0 (L ∪ t.toFinset) hcard z
    have hnot : p ∉ L ∧ p ∉ t.toFinset := by simpa only [mem_union,not_or] using hpn
    exact ⟨p,mem_sdiff.mpr ⟨(mem_erase.mp hp).2,hnot.2⟩,hnot.1,hpd⟩
  obtain ⟨s,hsnd,hts,hslen,hssub,hsprefix,hsend⟩ := exists_planeDisplacement_prescribed_stream
    v U t K 0 9 c (by norm_num) hc (by norm_num; exact hKpay) (by simp [planeDisplacementRadius]; positivity)
    htnd (fun p hp => norm_mobiusDivisorTwoPlanePacket_le_nine P hM (ht p hp).1
      (ht p hp).2.2.1 (by have := (ht p hp).2.2.2.1; omega) (ht p hp).2.2.2.2)
    (fun p hp hn => (mem_sdiff.mp hp).2 (List.mem_toFinset.mpr hn))
    (fun p hp => hv p (mem_sdiff.mp hp).1) hdirU
  simp only [zero_add] at hsprefix hsend
  change planeDisplacementRadius (s.map v).sum ≤ R at hsend
  have hsprefix' : ∀ k,planeDisplacementRadius ((s.take k).map v).sum ≤ R+18 := by
    intro k
    have hh := hsprefix k
    dsimp [R]
    linarith
  let U' := W \ s.toFinset
  have hdirU' : ∀ L ⊆ U',L.card<n → ∀ z : ℝ × ℝ,
      ∃ p ∈ U',p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖ := by
    intro L hL hLc z
    have hcard : (L ∪ s.toFinset).card< mobiusDivisorCoupledTwoCapacity b N-1 := by
      have hh := card_union_le L s.toFinset
      rw [List.toFinset_card_of_nodup hsnd,hslen] at hh
      change (K+1)*t.length+n ≤ mobiusDivisorCoupledTwoCapacity b N-1 at hcap
      omega
    obtain ⟨p,hp,hpn,hpd⟩ := hdir 0 (L ∪ s.toFinset) hcard z
    have hnot : p ∉ L ∧ p ∉ s.toFinset := by simpa only [mem_union,not_or] using hpn
    exact ⟨p,mem_sdiff.mpr ⟨(mem_erase.mp hp).2,hnot.2⟩,hnot.1,hpd⟩
  obtain ⟨r,hrnd,hrlen,hrsub,hrbound⟩ := exists_planeDisplacement_return_batch
    v U' n (s.map v).sum 9 c (by norm_num) hc
    (fun p hp => hv p (mem_sdiff.mp hp).1) hdirU'
  have hrprefix : ∀ k ≤ n,planeDisplacementRadius ((s.map v).sum+((r.take k).map v).sum) ≤ R := by
    intro k hk
    have hh := hrbound k hk
    rw [List.sum_toFinset _ (show (r.take k).Nodup from hrnd.take)] at hh
    have hn : 0 ≤ (k:ℝ)*c/4 := by positivity
    exact hh.trans (max_le le_rfl (by linarith))
  have hdis : List.Disjoint s r := by
    intro p hps hpr
    exact (mem_sdiff.mp (hrsub (List.mem_toFinset.mpr hpr))).2 (List.mem_toFinset.mpr hps)
  let l := s++r
  have hlnd : l.Nodup := List.nodup_append'.mpr ⟨hsnd,hrnd,hdis⟩
  have hllen : l.length=(K+1)*t.length+n := by simp [l,hslen,hrlen]
  have hlsub : l.toFinset ⊆ t.toFinset ∪ W := by
    intro p hp
    simp only [l,List.toFinset_append,mem_union] at hp
    rcases hp with hs|hr
    · rcases mem_union.mp (hssub hs) with ht|hu
      · exact mem_union_left _ ht
      · exact mem_union_right _ (mem_sdiff.mp hu).1
    · exact mem_union_right _ (mem_sdiff.mp (hrsub hr)).1
  have hlradius : ∀ k,planeDisplacementRadius (∑ p ∈ (l.take k).toFinset,v p) ≤ R+18 := by
    intro k
    rw [List.sum_toFinset _ (show (l.take k).Nodup from hlnd.take)]
    dsimp [l]
    by_cases hk : k ≤ s.length
    · rw [List.take_append_of_le_length hk]
      exact hsprefix' k
    · rw [List.take_append,List.take_of_length_le (le_of_not_ge hk)]
      simp only [List.map_append,List.sum_append]
      by_cases hkr : k-s.length ≤ n
      · exact (hrprefix _ hkr).trans (by linarith)
      · have hrl : r.length ≤ k-s.length := by omega
        rw [List.take_of_length_le hrl]
        have hh := hrprefix n le_rfl
        rw [← hrlen,List.take_length] at hh
        exact hh.trans (by linarith)
  have pdata : ∀ p ∈ l.toFinset,p.Prime ∧ p<M ∧ p ∉ P ∧ 15 ≤ p ∧ M/p ≤ 14 := by
    intro p hp
    rcases mem_union.mp (hlsub hp) with hpt|hpw
    · exact ht p (List.mem_toFinset.mp hpt)
    · obtain ⟨j,hj,_,hpp,hpm,hp15,hpq,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN hpw
      have hj14 : j ≤ 14 := by simp only [mem_insert,mem_singleton] at hj; rcases hj with rfl|rfl|rfl <;> omega
      exact ⟨hpp,hpm,hfresh p hpw,hp15,by dsimp [M]; omega⟩
  have hbase : ∀ L ⊆ l.toFinset,
      mobiusDivisorSuccessorEnvelope M (P ∪ L)+
        min (∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)))
          (∑ p ∈ L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) ≤
      mobiusDivisorSuccessorEnvelope M P+
        2*Real.sqrt (mobiusDivisorSuccessorEnvelope M P)*
          (|∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
           |∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}|)+
          (|∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
           |∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}|)^(2 : ℕ) := by
    intro L hL
    apply mobiusDivisorSuccessorEnvelope_two_block_reserve_error M P L hM
    · intro p hp
      have hh := pdata p (hL hp)
      exact ⟨hh.1,hh.2.1,hh.2.2.1,by have := hh.2.2.2.1; omega⟩
    · intro p hp
      exact (mobiusDivisorCoupledTwoCore_covers (by have := (pdata p (hL hp)).2.2.2.2; omega)).trans hP
    · intro p hp q hq _
      have := (pdata p (hL hp)).2.2.2.2
      have := (pdata q (hL hq)).2.2.2.1
      omega
  have hD : ∀ k,
      |∑ p ∈ (l.take k).toFinset,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
      |∑ p ∈ (l.take k).toFinset,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}| ≤ H*Real.sqrt M := by
    intro k
    exact physical_displacement_bound M P _ (by omega) (by linarith) (hlradius k)
  refine ⟨l,hlnd,hts.trans (List.sublist_append_left s r),hllen,hlsub,hD,?_,?_⟩
  · intro k
    let L := (l.take k).toFinset
    have hL : L ⊆ l.toFinset := by
      intro p hp
      exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp))
    have he := hbase L hL
    have hmin : 0 ≤ min
        (∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)))
        (∑ p ∈ L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) := by positivity
    let D := |∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
      |∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}|
    have hD0 : 0 ≤ D := by dsimp [D]; positivity
    have hsE : Real.sqrt (mobiusDivisorSuccessorEnvelope M P) ≤ Real.sqrt C*(M:ℝ) := by
      calc
        _ ≤ Real.sqrt (C*(M:ℝ)^(2 : ℕ)) := Real.sqrt_le_sqrt hE
        _ = _ := by rw [Real.sqrt_mul hC.le,Real.sqrt_sq (Nat.cast_nonneg M)]
    have hrootM : Real.sqrt M ≤ (M:ℝ) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨Nat.cast_nonneg M,?_⟩
      have hm1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      nlinarith
    have hDM : D ≤ H*(M:ℝ) := (hD k).trans (mul_le_mul_of_nonneg_left hrootM hH.le)
    have hlin := mul_le_mul (mul_le_mul_of_nonneg_left hsE (by norm_num : (0:ℝ) ≤ 2)) hDM hD0 (by positivity)
    have hquad := (sq_le_sq₀ hD0 (by positivity : 0 ≤ H*(M:ℝ))).mpr hDM
    change mobiusDivisorSuccessorEnvelope M (P ∪ L)+_ ≤ mobiusDivisorSuccessorEnvelope M P+
      2*Real.sqrt (mobiusDivisorSuccessorEnvelope M P)*D+D^(2 : ℕ) at he
    dsimp [C']
    nlinarith only [he,hmin,hE,hlin,hquad]
  · have he := hbase l.toFinset Subset.rfl
    have hrall : r.toFinset ⊆ l.toFinset := by simp only [l,List.toFinset_append]; exact subset_union_right
    have hres0 := sum_le_sum (fun p hp => (hreserve p (mem_sdiff.mp (hrsub hp)).1).1)
    have hres1 := sum_le_sum (fun p hp => (hreserve p (mem_sdiff.mp (hrsub hp)).1).2)
    have hrcard : r.toFinset.card=n := (List.toFinset_card_of_nodup hrnd).trans hrlen
    simp only [sum_const,nsmul_eq_mul,hrcard] at hres0 hres1
    have hRsum := hres0.trans (sum_le_sum_of_subset_of_nonneg hrall (fun p _ _ => by positivity))
    have hTsum := hres1.trans (sum_le_sum_of_subset_of_nonneg hrall (fun p _ _ => by positivity))
    have hmin := le_min hRsum hTsum
    have hDf := hD l.length
    rw [List.take_length] at hDf
    have hpay := mobiusDivisor_two_plane_repair_error_budget
      (mobiusDivisorSuccessorEnvelope M P) C H d M n
      (|∑ p ∈ l.toFinset,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
       |∑ p ∈ l.toFinset,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}|)
      hC hH hd (by exact_mod_cast (show 1 ≤ M by omega)) hE (by positivity) hDf (Nat.le_ceil _)
    nlinarith only [he,hmin,hpay]

/-- Eventually any prescribed bounded-quotient stream occupying at most a fixed
fraction of source capacity admits a prefix-controlled repair. -/
theorem eventually_mobiusDivisor_prescribed_stream_repair :
    ∃ b K : ℕ, ∃ H : ℝ, 15 ≤ b ∧ 0 < H ∧ ∀ C : ℝ, 0 < C → ∃ A C' : ℝ, 0 < A ∧ 0 < C' ∧
      ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        ∀ P : Finset ℕ, mobiusDivisorCoupledTwoCore ⊆ P → 2 ∉ P →
          (∀ p ∈ mobiusDivisorCoupledTwoPool b N, p ∉ P) →
          mobiusDivisorSuccessorEnvelope M P ≤ C*(M:ℝ)^(2 : ℕ) →
          ∀ t : List ℕ, t.Nodup →
            (∀ p ∈ t, p.Prime ∧ p < M ∧ p ∉ P ∧ 15 ≤ p ∧ M/p ≤ 14) →
            2*(K+1)*t.length ≤ mobiusDivisorCoupledTwoCapacity b N-1 →
            ∃ l : List ℕ, l.Nodup ∧ t.Sublist l ∧
              l.length = (K+1)*t.length+⌈A*Real.sqrt M⌉₊ ∧
              l.toFinset ⊆ t.toFinset ∪ mobiusDivisorCoupledTwoPool b N ∧
              (∀ k : ℕ,
                |∑ p ∈ (l.take k).toFinset, Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
                |∑ p ∈ (l.take k).toFinset, Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}| ≤ H*Real.sqrt M) ∧
              (∀ k : ℕ, mobiusDivisorSuccessorEnvelope M (P ∪ (l.take k).toFinset) ≤ C'*(M:ℝ)^(2 : ℕ)) ∧
              mobiusDivisorSuccessorEnvelope M (P ∪ l.toFinset)+(M:ℝ) ≤ mobiusDivisorSuccessorEnvelope M P := by
  obtain ⟨b,K,H,hb,hH,hrepair⟩ := exists_mobiusDivisor_prescribed_stream_repair
  refine ⟨b,K,H,hb,hH,?_⟩
  intro C hC
  obtain ⟨A,C',hA,hC',hrepair⟩ := hrepair C hC
  refine ⟨A,C',hA,hC',?_⟩
  filter_upwards [eventually_mobiusDivisorCoupledTwoCapacity_sub_one_ge_sqrt
      b (by omega) (2*A+2) (by positivity), eventually_ge_atTop (1:ℕ)] with N hcap hN
  dsimp only
  intro P hP h2 hfresh hE t htnd ht htcap
  apply hrepair N hN P hP h2 hfresh hE t htnd ht
  let M := 14*(b+1)*N
  let n : ℕ := ⌈A*Real.sqrt M⌉₊
  have hm : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by dsimp [M]; nlinarith)
  have hs : (1:ℝ) ≤ Real.sqrt M := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
    exact_mod_cast hm
  have hn : (n:ℝ) < A*Real.sqrt M+1 := Nat.ceil_lt_add_one (by positivity)
  have hncap : 2*n ≤ mobiusDivisorCoupledTwoCapacity b N-1 := by
    have hh : (2:ℝ)*(n:ℝ) ≤ (mobiusDivisorCoupledTwoCapacity b N-1:ℕ) := by
      change (2*A+2)*Real.sqrt M ≤ ((mobiusDivisorCoupledTwoCapacity b N-1:ℕ):ℝ) at hcap
      nlinarith only [hn,hcap,hs]
    exact_mod_cast hh
  change (K+1)*t.length+n ≤ mobiusDivisorCoupledTwoCapacity b N-1
  nlinarith only [htcap,hncap]

end RHTower
