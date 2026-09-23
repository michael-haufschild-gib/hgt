import GaloisForLFunctions.HTGeometry.InwardPlaneDisplacementReturn
import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedWindowRepair

/-!
# Neutralizing the literal head and prime-two receiving coordinates

Actual unused prime windows steer the current two-coordinate field into a
fixed square-root-scale ball. The complete raw-energy identity releases both
initial receiving squares and the removed packet reserve. Every selected
prefix has only a linear allowance above the prepared energy.

The fixed-core theorem supplies its own initial admission bound and all
preparation states. Other prime fibres remain unprocessed.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
open HTGeometry

private lemma receiving_radius_sq (a b s : ℝ) (hs : s ≠ 0) (x y : ℝ) :
    s^(2 : ℕ) * (planeDisplacementRadius (-a/s+x,-b/s+y))^(2 : ℕ) =
      (a-s*x)^(2 : ℕ)+(b-s*y)^(2 : ℕ) := by
  rw [planeDisplacementRadius, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- Actual source primes neutralize both receiving coordinates. Every prefix
has only a linear energy allowance; the endpoint releases both original
receiving squares and an additional cutoff-sized reserve. -/
theorem eventually_exists_mobiusDivisorReceivingPairNeutralization :
    ∃ b : ℕ, ∃ R : ℝ, 15 ≤ b ∧ 0 < R ∧
      ∀ C : ℝ, 0 < C → ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        ∀ P : Finset ℕ, mobiusDivisorCoupledTwoCore ⊆ P → 2 ∉ P →
          (∀ p ∈ mobiusDivisorCoupledTwoPool b N, p ∉ P) →
          (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)+
            (mobiusDivisorSelectionFibre M P {2})^(2 : ℕ) ≤ C*(M:ℝ)^(2 : ℕ) →
          ∃ l : List ℕ, l.Nodup ∧ l.length = ⌈A*Real.sqrt M⌉₊ ∧
            l.toFinset ⊆ mobiusDivisorCoupledTwoPool b N ∧
            (∀ k : ℕ, mobiusDivisorSelectionEnergy M (P ∪ (l.take k).toFinset) ≤
              mobiusDivisorSelectionEnergy M P+R^(2 : ℕ)*M) ∧
            (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) ∅)^(2 : ℕ)+
              (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) {2})^(2 : ℕ) ≤ R^(2 : ℕ)*M ∧
            mobiusDivisorSelectionEnergy M (P ∪ l.toFinset)+
              (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)+
              (mobiusDivisorSelectionFibre M P {2})^(2 : ℕ)+M ≤
                mobiusDivisorSelectionEnergy M P := by
  obtain ⟨b,c,d,hb,hc,hd,hgeometry⟩ := exists_mobiusDivisorTwoPlaneWindowGeometry
  let R : ℝ := 4*9^(2 : ℕ)/c+2*9+c
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨b,R,hb,hR,?_⟩
  intro C hC
  let A : ℝ := 4*Real.sqrt C/c+(R^(2 : ℕ)+1)/d+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_mobiusDivisorCoupledTwoCapacity_sub_one_ge_sqrt
    b (by omega) (A+2) (by positivity), eventually_ge_atTop (1:ℕ)] with N hcap hN
  let M := 14*(b+1)*N
  have hM : 2 < M := by dsimp [M]; nlinarith
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  let s : ℝ := Real.sqrt M
  have hs : 0 < s := Real.sqrt_pos.mpr hMr
  have hssq : s^(2 : ℕ) = M := Real.sq_sqrt hMr.le
  have hs1 : 1 ≤ s := by
    change 1 ≤ Real.sqrt (M:ℝ)
    rw [Real.le_sqrt (by norm_num) hMr.le]
    simpa using hm1
  let n : ℕ := ⌈A*s⌉₊
  have hn : A*s ≤ (n:ℝ) := Nat.le_ceil _
  have hncap : n ≤ mobiusDivisorCoupledTwoCapacity b N-1 := by
    have hceil : (n:ℝ) < A*s+1 := Nat.ceil_lt_add_one (by positivity)
    change (A+2)*s ≤ ((mobiusDivisorCoupledTwoCapacity b N-1:ℕ):ℝ) at hcap
    exact_mod_cast (show (n:ℝ) ≤ ((mobiusDivisorCoupledTwoCapacity b N-1:ℕ):ℝ) by linarith)
  dsimp only
  intro P hP h2 hfresh hE
  obtain ⟨hv,hreserve,hdir⟩ := hgeometry N hN P hP h2 hfresh
  let v := fun p => mobiusDivisorTwoPlanePacket M p P
  let a := mobiusDivisorSelectionFibre M P ∅
  let e := mobiusDivisorSelectionFibre M P {2}
  let z0 : ℝ × ℝ := (-a/s,-e/s)
  let z := fun L : Finset ℕ => z0+∑ p ∈ L,v p
  have hdir' : ∀ L ⊆ mobiusDivisorCoupledTwoPool b N, L.card < n → ∀ w : ℝ × ℝ,
      ∃ p ∈ mobiusDivisorCoupledTwoPool b N, p ∉ L ∧
        w.1*(v p).1+w.2*(v p).2 ≤ -c*‖w‖ := by
    intro L _ hLn w
    obtain ⟨p,hp,hpn,hpd⟩ := hdir 0 L (by omega) w
    exact ⟨p,(mem_erase.mp hp).2,hpn,hpd⟩
  obtain ⟨l,hlnd,hlen,hlsub,hradius⟩ := exists_planeDisplacement_return_batch
    v (mobiusDivisorCoupledTwoPool b N) n z0 9 c (by norm_num) hc hv hdir'
  have pdata : ∀ p ∈ l.toFinset, p.Prime ∧ p < M ∧ p ∉ P ∧ 15 ≤ p ∧ M/p ≤ 14 := by
    intro p hp
    obtain ⟨K,hK,_,hpp,hpM,hp15,hpq,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN (hlsub hp)
    have hk : K ≤ 14 := by
      simp only [mem_insert,mem_singleton] at hK
      rcases hK with rfl|rfl|rfl <;> omega
    exact ⟨hpp,hpM,hfresh p (hlsub hp),hp15,by dsimp [M]; omega⟩
  have coord (L : Finset ℕ) :
      s*(∑ p ∈ L,v p).1 = ∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅ ∧
      s*(∑ p ∈ L,v p).2 = ∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2} := by
    constructor
    · rw [Prod.fst_sum]
      simp only [v,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      change s*(_/s)=_
      field_simp
    · rw [Prod.snd_sum]
      simp only [v,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      change s*(_/s)=_
      field_simp
  have physical (L : Finset ℕ) (hL : L ⊆ l.toFinset) :
      (mobiusDivisorSelectionFibre M (P ∪ L) ∅)^(2 : ℕ)+
        (mobiusDivisorSelectionFibre M (P ∪ L) {2})^(2 : ℕ) =
          (M:ℝ)*(planeDisplacementRadius (z L))^(2 : ℕ) := by
    have hchild : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → M/p+1 ≤ q := by
      intro p hp q hq _
      have := (pdata p (hL hp)).2.2.2.2
      have := (pdata q (hL hq)).2.2.2.1
      omega
    have ha := mobiusDivisorSelectionFibre_union_two_child_inactive M P L ∅
      (fun p hp => ⟨(pdata p (hL hp)).1,(pdata p (hL hp)).2.2.1,by simp⟩) hchild
    have he := mobiusDivisorSelectionFibre_union_two_child_inactive M P L {2}
      (fun p hp => ⟨(pdata p (hL hp)).1,(pdata p (hL hp)).2.2.1,
        by have := (pdata p (hL hp)).2.2.2.1; simp only [mem_singleton]; omega⟩) hchild
    rw [ha,he,← (coord L).1,← (coord L).2]
    symm
    rw [← hssq]
    exact receiving_radius_sq a e s hs.ne' _ _
  have initial : (M:ℝ)*(planeDisplacementRadius z0)^(2 : ℕ) = a^(2 : ℕ)+e^(2 : ℕ) := by
    have hh := physical ∅ (empty_subset _)
    simpa only [union_empty,z,sum_empty,add_zero] using hh.symm
  have hr0 : planeDisplacementRadius z0 ≤ Real.sqrt C*s := by
    have hz0 : 0 ≤ planeDisplacementRadius z0 := Real.sqrt_nonneg _
    have hCroot := Real.sq_sqrt hC.le
    have hrE : (planeDisplacementRadius z0)^(2 : ℕ) ≤ C*(M:ℝ) := by
      change a^(2 : ℕ)+e^(2 : ℕ) ≤ C*(M:ℝ)^(2 : ℕ) at hE
      nlinarith only [hE,initial,hMr]
    have hprod : (Real.sqrt C*s)^(2 : ℕ) = C*(M:ℝ) := by rw [mul_pow,hCroot,hssq]
    nlinarith only [hrE,hprod,hz0,mul_nonneg (Real.sqrt_nonneg C) hs.le]
  have hdecay : planeDisplacementRadius z0-(n:ℝ)*c/4 ≤ 0 := by
    have hAroot : 4*Real.sqrt C/c ≤ A := by
      have hh : 0 ≤ (R^(2 : ℕ)+1)/d := by positivity
      dsimp [A]
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hAroot hs.le
    have hcn := mul_le_mul_of_nonneg_right (hh.trans hn) hc.le
    have heq : (4*Real.sqrt C/c*s)*c = 4*(Real.sqrt C*s) := by field_simp
    rw [heq] at hcn
    linarith
  have hpay : R^(2 : ℕ)+1 ≤ d*(n:ℝ) := by
    have hAr : (R^(2 : ℕ)+1)/d ≤ A := by
      have hh : 0 ≤ 4*Real.sqrt C/c := by positivity
      dsimp [A]
      linarith only [hh]
    have hAn : A ≤ (n:ℝ) := (le_mul_of_one_le_right hA.le hs1).trans hn
    exact (div_le_iff₀ hd).mp (hAr.trans hAn) |>.trans_eq (mul_comm _ _)
  have endpoint : (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) ∅)^(2 : ℕ)+
      (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) {2})^(2 : ℕ) ≤ R^(2 : ℕ)*M := by
    have hr := hradius n le_rfl
    rw [← hlen,List.take_length,hlen] at hr
    have hrr : planeDisplacementRadius (z l.toFinset) ≤ R :=
      hr.trans (max_le le_rfl (hdecay.trans hR.le))
    rw [physical _ Subset.rfl]
    have hh : (planeDisplacementRadius (z l.toFinset))^(2 : ℕ) ≤ R^(2 : ℕ) :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hrr
    exact (mul_le_mul_of_nonneg_left hh hMr.le).trans_eq (mul_comm _ _)
  have energy (L : Finset ℕ) (hL : L ⊆ l.toFinset) :
      mobiusDivisorSelectionEnergy M (P ∪ L)+a^(2 : ℕ)+e^(2 : ℕ)+
        (∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
          (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ))) =
      mobiusDivisorSelectionEnergy M P+(M:ℝ)*(planeDisplacementRadius (z L))^(2 : ℕ) := by
    have he := mobiusDivisorSelectionEnergy_union_two_child_inactive M P L hM
      (fun p hp => ⟨(pdata p (hL hp)).1,(pdata p (hL hp)).2.1,
        (pdata p (hL hp)).2.2.1,by have := (pdata p (hL hp)).2.2.2.1; omega⟩)
      (fun p hp => (mobiusDivisorCoupledTwoCore_covers
        (by have := (pdata p (hL hp)).2.2.2.2; omega)).trans hP)
      (fun p hp q hq _ => by
        have := (pdata p (hL hp)).2.2.2.2
        have := (pdata q (hL hq)).2.2.2.1
        omega)
    have hr := receiving_radius_sq a e s hs.ne' (∑ p ∈ L,v p).1 (∑ p ∈ L,v p).2
    rw [hssq,(coord L).1,(coord L).2] at hr
    change (M:ℝ)*(planeDisplacementRadius (z L))^(2 : ℕ)=_ at hr
    change _ = mobiusDivisorSelectionEnergy M P-2*a*_-2*e*_+_+_-_ at he
    linarith only [he,hr]
  refine ⟨l,hlnd,hlen,hlsub,?_,endpoint,?_⟩
  · intro k
    let L := (l.take k).toFinset
    have hL : L ⊆ l.toFinset := by
      intro p hp
      exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp))
    have hr : planeDisplacementRadius (z L) ≤ max R (planeDisplacementRadius z0) := by
      by_cases hk : k ≤ n
      · exact (hradius k hk).trans
          (max_le_max_left _ (sub_le_self _ (by positivity)))
      · have ht : l.take k=l := List.take_of_length_le (by omega)
        have hh := hradius n le_rfl
        rw [← hlen,List.take_length,hlen] at hh
        dsimp [L]
        rw [ht]
        exact hh.trans (max_le_max_left _ (sub_le_self _ (by positivity)))
    have he := energy L hL
    have hres : 0 ≤ ∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
        (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) := by positivity
    change mobiusDivisorSelectionEnergy M (P ∪ L) ≤ mobiusDivisorSelectionEnergy M P+R^(2 : ℕ)*M
    rcases le_total R (planeDisplacementRadius z0) with hle|hle
    · rw [max_eq_right hle] at hr
      have hh := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr hr) hMr.le
      change (M:ℝ)*(planeDisplacementRadius (z L))^(2 : ℕ) ≤
        (M:ℝ)*(planeDisplacementRadius z0)^(2 : ℕ) at hh
      nlinarith only [he,hh,initial,hres,sq_nonneg R,hMr]
    · rw [max_eq_left hle] at hr
      have hh := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hr) hMr.le
      change (M:ℝ)*(planeDisplacementRadius (z L))^(2 : ℕ) ≤ (M:ℝ)*R^(2 : ℕ) at hh
      nlinarith only [he,hh,hres,sq_nonneg a,sq_nonneg e]
  · have he := energy l.toFinset Subset.rfl
    have hres := sum_le_sum (fun p hp => (hreserve p (hlsub hp)).1)
    simp only [sum_const,nsmul_eq_mul,List.toFinset_card_of_nodup hlnd,hlen] at hres
    have hp := mul_le_mul_of_nonneg_right hpay hMr.le
    rw [physical _ Subset.rfl] at endpoint
    change _+a^(2 : ℕ)+e^(2 : ℕ)+M ≤ _
    nlinarith only [he,hres,hp,endpoint]

/-- With the literal fixed core, the receiving-pair construction has no
admission premise. Preparation and every selected prefix have one uniform
quadratic ceiling, and the actual terminal receiving pair has linear energy. -/
theorem eventually_exists_mobiusDivisorInitialReceivingPairNeutralization :
    ∃ b : ℕ, ∃ R A C : ℝ, 15 ≤ b ∧ 0 < R ∧ 0 < A ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        (∀ T ⊆ P, mobiusDivisorSelectionEnergy M T ≤ C*(M:ℝ)^(2 : ℕ)) ∧
        ∃ l : List ℕ, l.Nodup ∧ l.length = ⌈A*Real.sqrt M⌉₊ ∧
          l.toFinset ⊆ mobiusDivisorCoupledTwoPool b N ∧
          (∀ k : ℕ, mobiusDivisorSelectionEnergy M (P ∪ (l.take k).toFinset) ≤ C*(M:ℝ)^(2 : ℕ)) ∧
          (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) ∅)^(2 : ℕ)+
            (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) {2})^(2 : ℕ) ≤ R^(2 : ℕ)*M ∧
          mobiusDivisorSelectionEnergy M (P ∪ l.toFinset)+
            (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)+
            (mobiusDivisorSelectionFibre M P {2})^(2 : ℕ)+M ≤
              mobiusDivisorSelectionEnergy M P := by
  obtain ⟨b,R,hb,hR,hreturn⟩ := eventually_exists_mobiusDivisorReceivingPairNeutralization
  let P := mobiusDivisorCoupledTwoCore
  let D : ℝ := 2^P.card*722
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨A,hA,hreturn⟩ := hreturn D hD
  refine ⟨b,R,A,D+R^(2 : ℕ),hb,hR,hA,by positivity,?_⟩
  filter_upwards [hreturn,eventually_ge_atTop (1:ℕ)] with N hreturn hN
  let M := 14*(b+1)*N
  have hM : 15 ≤ M := by dsimp [M]; nlinarith
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hp : ∀ p ∈ P, p.Prime ∧ p < M := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp (mem_erase.mp hp).2
    exact ⟨hprime,(mem_range.mp hp).trans_le hM⟩
  have hprep : ∀ T ⊆ P, mobiusDivisorSelectionEnergy M T ≤ D*(M:ℝ)^(2 : ℕ) := by
    intro T hT
    have he := mobiusDivisorSelectionEnergy_le_pow_card M T (fun p hpT => hp p (hT hpT))
    rw [mobiusDivisorSelectionEnergy_empty] at he
    have hdiag := sum_mobiusDivisorDilationChannel_sq_le_quadratic M
    have hpow : (2:ℝ)^T.card ≤ 2^P.card := by gcongr; norm_num
    calc
      _ ≤ 2^T.card*(722*(M:ℝ)^(2 : ℕ)) := he.trans (mul_le_mul_of_nonneg_left hdiag (by positivity))
      _ ≤ 2^P.card*(722*(M:ℝ)^(2 : ℕ)) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by dsimp [D]; ring
  have hpair : (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)+
      (mobiusDivisorSelectionFibre M P {2})^(2 : ℕ) ≤ D*(M:ℝ)^(2 : ℕ) := by
    have hh := sum_mobiusDivisorSelectionFibre_sq_le_energy M P {∅,{2}}
    have hh' : (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)+
        (mobiusDivisorSelectionFibre M P {2})^(2 : ℕ) ≤ mobiusDivisorSelectionEnergy M P := by
      simpa using hh
    exact hh'.trans (hprep P Subset.rfl)
  obtain ⟨l,hnd,hlen,hsub,hprefix,hpair',hend⟩ := hreturn P Subset.rfl
    (by simp [P,mobiusDivisorCoupledTwoCore]) (by
      intro p hpW hpP
      obtain ⟨K,hK,_,_,_,hp15,_,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN hpW
      have hpLt := mem_range.mp (mem_filter.mp (mem_erase.mp hpP).2).1
      omega) hpair
  refine ⟨?_,l,hnd,hlen,hsub,?_,hpair',hend⟩
  · intro T hT
    have hh := hprep T hT
    change mobiusDivisorSelectionEnergy M T ≤ (D+R^(2 : ℕ))*(M:ℝ)^(2 : ℕ)
    nlinarith only [hh,sq_nonneg R,sq_nonneg (M:ℝ)]
  · intro k
    have hh := hprefix k
    have he := hprep P Subset.rfl
    change mobiusDivisorSelectionEnergy M (P ∪ (l.take k).toFinset) ≤ (D+R^(2 : ℕ))*(M:ℝ)^(2 : ℕ)
    change mobiusDivisorSelectionEnergy M (P ∪ (l.take k).toFinset) ≤
      mobiusDivisorSelectionEnergy M P+R^(2 : ℕ)*M at hh
    have hsq : (M:ℝ) ≤ (M:ℝ)^(2 : ℕ) := by nlinarith
    nlinarith only [hh,he,mul_le_mul_of_nonneg_left hsq (sq_nonneg R)]

end RHTower
