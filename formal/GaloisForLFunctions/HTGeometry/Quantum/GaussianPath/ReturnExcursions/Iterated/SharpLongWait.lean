import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.SubcriticalWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.LongWait
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.ForwardWait

/-! # First chronological wait above the inverse scalar-arc scale -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
open SharpOccupation
noncomputable section

/-- Padding an observation to the minimum record length costs only an additive
term. Both the density and the additive term keep the rare-event factor. -/
private theorem pad_record (B : Set ℝ) {L r : ℝ} (hL : 0<L) (hr : 0≤r)
    (h : ∀ a T : ℝ, L≤T → volume.real (B∩Icc a (a+T))/T≤r)
    (a T : ℝ) (hT : 0≤T) : volume.real (B∩Icc a (a+T))≤r*(T+L) := by
  let u := max T L
  have hLu : L≤u := le_max_right ..
  have hTu : T≤u := le_max_left ..
  have hsub : B∩Icc a (a+T) ⊆ B∩Icc a (a+u) :=
    inter_subset_inter_right _ (Icc_subset_Icc_right (add_le_add_right hTu a))
  have hfinite : volume (B∩Icc a (a+u))≠⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  exact (measureReal_mono hsub hfinite).trans (((div_le_iff₀ (hL.trans_le hLu)).mp
    (h a u hLu)).trans (mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right hL.le) (le_add_of_nonneg_left hT)) hr))

/-- After every recorded low visit, a genuine post-crossing wait exceeds the
inverse arc scale for any larger arc parameter. Two finite-record estimates
bound the first such crossing date, uniformly over the starting index. -/
theorem gaussian_first_sharp_long_wait :
    ∃ c₁ c₂ : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ S : ℕ → ℕ, subcriticalBudget S →
      ∀ z b : ℝ, physicalArc (1/10)<z → z<b → b<1 → ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let G₁ := (2:ℝ)^(D^c₁)
      let G₂ := (2:ℝ)^(D^c₂)
      ∀ s≤S N, let v := lowDate H P s
        let σ := highDate H P s
        ∀ m : ℕ, ∃ j : ℕ, 1/b^D<v (m+j+1)-σ (m+j) ∧
          (∀ i<j, v (m+i+1)-σ (m+i)≤1/b^D) ∧
          σ (m+j)-v m≤2*(1/(2:ℝ)^(7*D/16))*G₁+8*(z/b)^D*G₂ := by
  obtain ⟨c₁,hwin⟩ := gaussian_full_budget_robust_windows
  obtain ⟨c₂,hquant⟩ := FiniteRecords.gaussian_finite_wait_quantile_full
  obtain ⟨_,hcycle⟩ := gaussian_cycle_windows
  refine ⟨c₁,c₂,?_⟩
  filter_upwards [hwin,hquant,hcycle] with ω hw hq hc
  intro S hS z b hxz hzb hb
  have he : (1/10:ℝ)∈Ioo (0:ℝ) (Real.sqrt 2) :=
    ⟨by norm_num,(Real.lt_sqrt (by norm_num)).mpr (by norm_num)⟩
  have hz := (physicalArc_spec he.1 he.2).1.1.trans hxz
  have hbp := hz.trans hzb
  have hratio := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hz.le hbp.le)
    ((div_lt_one hbp).mpr hzb)
  have hdim : Tendsto (fun k : ℕ => (2:ℕ)^(k+3)) atTop atTop :=
    tendsto_atTop_mono (fun k => (show k≤k+3 by omega).trans (Nat.lt_two_pow_self (n:=k+3)).le) tendsto_id
  filter_upwards [hw,hq S hS _ ⟨he.1,by norm_num⟩ z b hxz hzb hb,hc,
    (tendsto_add_atTop_nat 3).eventually (eventually_half_budget hS),
    (hratio.comp hdim).eventually_lt_const (by norm_num : (0:ℝ)<1/8)] with k hk hqk hck hcap hsmall
  intro N D H P G₁ G₂ s hs v σ m
  let A := robustWindowHits H P 1
  let B := windowHits H s (1/10) (1/b^D)
  let E := (2:ℝ)^(7*D/16)
  let p := 1/E
  let r := 2*(z/b)^D
  have hD : 8≤D := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 3≤k+3)
  have hE : (4:ℝ)≤E := by
    calc
      (4:ℝ) = 2^2 := by norm_num
      _ ≤ E := pow_le_pow_right₀ (by norm_num) (by omega : 2≤7*D/16)
  have hEp : 0<E := lt_of_lt_of_le (by norm_num) hE
  have hp : p≤1/4 := one_div_le_one_div_of_le (by norm_num) hE
  have hr : 0≤r := by dsimp only [r]; positivity
  change (z/b)^D<1/8 at hsmall
  have hsum : p+r≤1/2 := by dsimp only [r]; linarith only [hp,hsmall]
  obtain ⟨hd,_⟩ := hck s (hs.trans hcap)
  have pay (a T : ℝ) (hT : 0≤T) :
      2*volume.real ((A∪B)∩Icc a (a+T))≤T+2*p*G₁+4*r*G₂ := by
    have hA := hk.2 0 (7*D/16) (by change 16*(0+7*D/16)≤7*D; omega) a T hT
    simp only [pow_zero] at hA
    change E*volume.real (A∩Icc a (a+T))≤T+G₁ at hA
    have ha : volume.real (A∩Icc a (a+T))≤p*(T+G₁) := by
      rw [show p*(T+G₁)=(T+G₁)/E by dsimp only [p]; ring]
      exact (le_div_iff₀ hEp).mpr ((mul_comm ..).le.trans hA)
    have hb' := pad_record B (L:=2*G₂) (by dsimp only [G₂]; positivity) hr (hqk s hs) a T hT
    rw [union_inter_distrib_right]
    linarith only [measureReal_union_le (μ:=volume) (A∩Icc a (a+T)) (B∩Icc a (a+T)),
      ha,hb',mul_le_mul_of_nonneg_right hsum hT]
  have hpre (i : ℕ) : Icc (v i) (σ i)⊆A∪B := by
    intro t ht
    have hl : orbitCircuitDistance H P t≤9/80 := by
      rcases ht.2.lt_or_eq with hlt|rfl
      · exact le_of_not_ge (fun hh => hlt.not_ge ((hd i).2.2.1.2 ⟨ht.1,hh⟩))
      · exact (hd i).2.1.le
    exact Or.inl ⟨t,⟨le_rfl,by linarith⟩,hl.trans (by norm_num)⟩
  have hpost (i : ℕ) (h : v (i+1)-σ i≤1/b^D) : Icc (σ i) (v (i+1))⊆A∪B := by
    intro t ht
    exact Or.inr ⟨v (i+1),⟨ht.2,by linarith only [ht.1,h]⟩,low_visit H P s (i+1)⟩
  obtain ⟨j,hj,hbefore,hbound⟩ := first_long v σ (A∪B) (E:=2) (by norm_num)
    (fun i => (hd i).1.le) (fun i => by have h := hd i; linarith only [h.1,h.2.2.2.2.1])
    hpre hpost (fun a T hT => by simpa only [add_assoc] using pay a T hT) m
  refine ⟨j,hj,hbefore,?_⟩
  norm_num only [show (2:ℝ)-1=1 by norm_num,one_mul] at hbound
  change σ (m+j)-v m≤2*p*G₁+8*(z/b)^D*G₂
  dsimp only [r] at hbound
  linarith only [hbound]

#print axioms gaussian_first_sharp_long_wait
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
