import GaloisForLFunctions.ArithmeticIndexDescent.PrimeWindowUnitCoordinates
import GaloisForLFunctions.ArithmeticIndexDescent.GrowingPacketPrimePoleCancellation

/-!
# Prime–pole cancellation uniform over every Haar detail row

A growing finite square has the classical prime number theorem rate. Its
complement has a summable Hilbert tail, without any cutoff on detail indices.
Together these bounds control all unit Haar sections against a growing unit
coarse section in their original cell masses.
-/

noncomputable section
open Finset Filter Topology
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open GaloisForLFunctions.BiarithmeticGaugeGeometry
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
namespace GaloisForLFunctions.ArithmeticIndexDescent

private lemma prime_window_tail_exp_bound {C r t x : ℝ} {A M : ℕ}
    (hC : 0<C) (hr : 0≤r) (ht : 0≤t)
    (hM : (M:ℝ)+1≤2*Real.exp (r*t))
    (hA : Real.exp (8*r*t)≤(A:ℝ)+1)
    (hx : x^2≤C*((M:ℝ)+1)^3/((A:ℝ)+1)) :
    |x| ≤(8*C+1)*Real.exp (-2*r*t) := by
  have hp := pow_le_pow_left₀ (show 0≤(M:ℝ)+1 by positivity) hM 3
  have he : (2*Real.exp (r*t))^3 =
      8*Real.exp (-5*r*t)*Real.exp (8*r*t) := by
    calc
      _ = 8*(Real.exp (r*t)*Real.exp (r*t)*Real.exp (r*t)) := by ring
      _ = 8*Real.exp (3*r*t) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      _ = 8*(Real.exp (-5*r*t)*Real.exp (8*r*t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := by ring
  have hsq : x^2≤8*C*Real.exp (-5*r*t) := by
    apply hx.trans
    rw [div_le_iff₀ (show (0:ℝ)<(A:ℝ)+1 by positivity)]
    calc
      _ ≤ C*(2*Real.exp (r*t))^3 := mul_le_mul_of_nonneg_left hp hC.le
      _ = (8*C*Real.exp (-5*r*t))*Real.exp (8*r*t) := by rw [he];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)
  apply (sq_le_sq₀ (abs_nonneg x) (show 0≤(8*C+1)*Real.exp (-2*r*t) by positivity)).mp
  rw [sq_abs]
  calc
    _ ≤ 8*C*Real.exp (-5*r*t) := hsq
    _ ≤ (8*C+1)^2*Real.exp (-4*r*t) := by
      apply mul_le_mul
      · nlinarith only [hC,sq_nonneg (8*C)]
      · apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg hr ht]
      · exact (Real.exp_pos _).le
      · exact sq_nonneg _
    _ = _ := by
      have he : Real.exp (-2*r*t)^2=Real.exp (-4*r*t) := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      rw [mul_pow,he]

private lemma prime_window_head_exp_bound {C r t x : ℝ} {A M : ℕ}
    (hC : 0<C) (hr : 0≤r) (ht : 0≤t)
    (hM : (M:ℝ)+1≤2*Real.exp (r*t))
    (hA : (A:ℝ)+1≤2*Real.exp (8*r*t))
    (hx : |x| ≤C*(7*((A:ℝ)+1)*((M:ℝ)+1))*Real.exp (-24*r*t)) :
    |x| ≤28*C*Real.exp (-2*r*t) := by
  have hp : 7*((A:ℝ)+1)*((M:ℝ)+1) ≤
      28*(Real.exp (8*r*t)*Real.exp (r*t)) := by
    calc
      _ ≤ 7*(2*Real.exp (8*r*t))*(2*Real.exp (r*t)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hM
          (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hx
    _ ≤ C*(28*(Real.exp (8*r*t)*Real.exp (r*t)))*Real.exp (-24*r*t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (Real.exp_pos _).le
    _ = 28*C*Real.exp (-15*r*t) := by
      rw [show C*(28*(Real.exp (8*r*t)*Real.exp (r*t)))*Real.exp (-24*r*t) =
        28*C*((Real.exp (8*r*t)*Real.exp (r*t))*Real.exp (-24*r*t)) by ring,
        ← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      nlinarith only [mul_nonneg hr ht])) (by positivity)

/-- The literal prime–pole remainder tends uniformly to zero on all unit Haar
sections and a growing coarse range, with no detail-index restriction. -/
theorem exists_fullPrimeWindowRemainder_all_detail_growing_coarse_rate :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop,
      ∀ M : ℕ, (M:ℝ)≤Real.exp ((1/184320000:ℝ)*Real.sqrt (Real.log Y)) →
      ∀ (X : ℕ) (d q : ℕ → ℝ),
      (∑ a ∈ Icc 1 X,haarMass a*d a^2)≤1 →
      (∑ b ∈ Icc 1 M,logCellWidth b*q b^2)≤1 →
      |∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc 1 X,d a*fullPrimeWindowRemainder Y a b)| ≤
        C*Real.exp (-(1/92160000:ℝ)*Real.sqrt (Real.log Y)) := by
  obtain ⟨Cp,hCp,hpacket⟩ := exists_fullPrimeWindowRemainder_growing_packet_rate
  obtain ⟨Ct,hCt,htail⟩ := exists_fullPrimeWindowRemainder_hilbert_tail_bound
  refine ⟨28*Cp+8*Ct+1,by positivity,?_⟩
  filter_upwards [hpacket,eventually_ge_atTop 1] with Y hpacketY hY
  intro M hM X d q hd hq
  let r : ℝ := 1/184320000
  let t : ℝ := Real.sqrt (Real.log Y)
  let A : ℕ := ⌊Real.exp (8*r*t)⌋₊
  let H : ℝ := ∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc 1 (min X A),
    d a*fullPrimeWindowRemainder Y a b)
  let T : ℝ := ∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc (A+1) X,
    d a*fullPrimeWindowRemainder Y a b)
  have hr : 0≤r := by norm_num [r]
  have ht : 0≤t := Real.sqrt_nonneg _
  have he1 : 1≤Real.exp (r*t) := Real.one_le_exp_iff.mpr (mul_nonneg hr ht)
  have he8 : 1≤Real.exp (8*r*t) := Real.one_le_exp_iff.mpr (by positivity)
  have hA : (A:ℝ)≤Real.exp (8*r*t) := Nat.floor_le (Real.exp_pos _).le
  have hAl : Real.exp (8*r*t)≤(A:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hAu : (A:ℝ)+1≤2*Real.exp (8*r*t) := by linarith only [hA,he8]
  have hMu : (M:ℝ)+1≤2*Real.exp (r*t) := by
    change (M:ℝ)≤Real.exp (r*t) at hM
    linarith only [hM,he1]
  -- The natural coarse range fits inside the floor cutoff.
  have hMr : (M:ℝ)≤Real.exp (r*t) := hM
  have hMA : M≤A := Nat.le_floor (hMr.trans (Real.exp_le_exp.mpr (by
    nlinarith only [mul_nonneg hr ht])))
  let S := (Icc 1 (min X A)).product (Icc 1 M)
  have hS : ∀ p∈S,1≤p.1 ∧ p.1≤A ∧ 1≤p.2 ∧ p.2≤A := by
    intro p hp
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    exact ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans (min_le_right _ _),
      (mem_Icc.mp hb).1,(mem_Icc.mp hb).2.trans hMA⟩
  have hc : ∀ p∈S,|d p.1*q p.2| ≤7*((A:ℝ)+1)*((M:ℝ)+1) := by
    intro p hp
    exact abs_unit_prime_packet_coefficient_le d q hd hq
      (mem_product.mp hp).1 (mem_product.mp hp).2
  have hclassic : (1/23040000:ℝ)*t=8*r*t := by dsimp only [r];ring
  have hdecay : -(1/7680000:ℝ)*t= -24*r*t := by dsimp only [r];ring
  have hhead := hpacketY A (by
    change (A:ℝ)≤Real.exp ((1/23040000:ℝ)*t)
    rw [hclassic]
    exact hA) S hS (7*((A:ℝ)+1)*((M:ℝ)+1)) (fun p => d p.1*q p.2) hc
  have heqH : (∑ p∈S,(d p.1*q p.2)*fullPrimeWindowRemainder Y p.1 p.2)=H := by
    dsimp only [S,H]
    have hp := Finset.sum_product (Icc 1 (min X A)) (Icc 1 M)
      (fun p : ℕ × ℕ => (d p.1*q p.2)*fullPrimeWindowRemainder Y p.1 p.2)
    calc
      _ = ∑ a∈Icc 1 (min X A),∑ b∈Icc 1 M,
          (d a*q b)*fullPrimeWindowRemainder Y a b := hp
      _ = ∑ b∈Icc 1 M,∑ a∈Icc 1 (min X A),
          (d a*q b)*fullPrimeWindowRemainder Y a b := Finset.sum_comm
      _ = _ := ?_
    apply sum_congr rfl
    intro b hb
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    ring
  rw [heqH,abs_of_nonneg (by positivity : 0≤7*((A:ℝ)+1)*((M:ℝ)+1))] at hhead
  change |H| ≤Cp*(7*((A:ℝ)+1)*((M:ℝ)+1))*Real.exp (-(1/7680000:ℝ)*t) at hhead
  rw [hdecay] at hhead
  have hh := prime_window_head_exp_bound hCp hr ht hMu hAu hhead
  -- All remaining detail rows are controlled without an outer cutoff.
  have hT : T^2≤Ct*((M:ℝ)+1)^3/((A:ℝ)+1) := htail Y A X M hY d q hd hq
  have htb := prime_window_tail_exp_bound hCt hr ht hMu hAl hT
  have hsplit : (∑ b∈Icc 1 M,q b*(∑ a∈Icc 1 X,d a*fullPrimeWindowRemainder Y a b))=H+T := by
    calc
      _ = ∑ b∈Icc 1 M,q b*((∑ a∈Icc 1 (min X A),d a*fullPrimeWindowRemainder Y a b)+
          (∑ a∈Icc (A+1) X,d a*fullPrimeWindowRemainder Y a b)) := by
        apply sum_congr rfl
        intro b hb
        rw [sum_Icc_split_at (fun a => d a*fullPrimeWindowRemainder Y a b) X A]
      _ = _ := by simp_rw [mul_add];rw [sum_add_distrib]
  rw [hsplit]
  calc
    _ ≤ |H| +|T| := abs_add_le _ _
    _ ≤ 28*Cp*Real.exp (-2*r*t)+(8*Ct+1)*Real.exp (-2*r*t) := add_le_add hh htb
    _ = _ := by
      have he : -2*r*t= -(1/92160000:ℝ)*Real.sqrt (Real.log Y) := by dsimp only [r,t];ring
      rw [he]
      ring

/-- The same all-detail bound holds for the actual all-prime source at any
common horizon containing both the detail packet and the translated coarse packet. -/
theorem exists_allPrimesMixedSource_all_detail_growing_coarse_rate :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop,
      ∀ M : ℕ, (M:ℝ)≤Real.exp ((1/184320000:ℝ)*Real.sqrt (Real.log Y)) →
      ∀ X N : ℕ, X≤N → Y*(M+1)≤N+1 →
      ∀ d q : ℕ → ℝ,
      (∑ a∈Icc 1 X,haarMass a*d a^2)≤1 →
      (∑ b∈Icc 1 M,logCellWidth b*q b^2)≤1 →
      |∑ b∈Icc 1 M,q b*(∑ a∈Icc 1 X,d a*
        (((∑' p : Nat.Primes,primeEulerMixedSource p (detailUnit a) (coarseWindow Y b) N)-
          fullPrimeWindowMixedPole Y a b)/Real.sqrt Y))| ≤
        C*Real.exp (-(1/92160000:ℝ)*Real.sqrt (Real.log Y)) := by
  obtain ⟨C,hC,hbound⟩ := exists_fullPrimeWindowRemainder_all_detail_growing_coarse_rate
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with Y hboundY hY
  intro M hM X N hXN hMN d q hd hq
  have he : (∑ b∈Icc 1 M,q b*(∑ a∈Icc 1 X,d a*
      (((∑' p : Nat.Primes,primeEulerMixedSource p (detailUnit a) (coarseWindow Y b) N)-
        fullPrimeWindowMixedPole Y a b)/Real.sqrt Y))) =
      ∑ b∈Icc 1 M,q b*(∑ a∈Icc 1 X,d a*fullPrimeWindowRemainder Y a b) := by
    apply sum_congr rfl
    intro b hb
    congr 1
    apply sum_congr rfl
    intro a ha
    have hbN : Y*(b+1)≤N+1 :=
      (Nat.mul_le_mul_left Y (Nat.add_le_add_right (mem_Icc.mp hb).2 1)).trans hMN
    rw [fullPrimeWindowRemainder,
      ← fullPrimeWindowCoupling_eq_tsum_euler (X := N) hY (mem_Icc.mp ha).1
        (mem_Icc.mp hb).1 ((mem_Icc.mp ha).2.trans hXN) hbN,
      ← fullPrimeWindowCoupling_eq_tsum_euler (X := a+(b+1)*Y) hY (mem_Icc.mp ha).1
        (mem_Icc.mp hb).1 (by omega) (by nlinarith only [Nat.zero_le a])]
  rw [he]
  exact hboundY M hM X d q hd hq

private lemma prime_window_opposite_pole_rate {Y M : ℕ}
    (hY : 1≤Y) (hL : 1≤Real.log (Y:ℝ))
    (hM : (M:ℝ)≤Real.exp ((1/184320000:ℝ)*Real.sqrt (Real.log Y))) :
    ((M:ℝ)+1)^2/(Y:ℝ) ≤
      4*Real.exp (-(1/92160000:ℝ)*Real.sqrt (Real.log Y)) := by
  let r : ℝ := 1/184320000
  let t : ℝ := Real.sqrt (Real.log Y)
  have ht : 0≤t := Real.sqrt_nonneg _
  have hY0 : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have ht1 : 1≤t := by
    rw [Real.le_sqrt zero_le_one (zero_le_one.trans hL)]
    simpa only [one_pow] using hL
  have ht2 : t^2=Real.log (Y:ℝ) := Real.sq_sqrt (zero_le_one.trans hL)
  have htL : t≤Real.log (Y:ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_right ht1 ht,ht2]
  have he1 : 1≤Real.exp (r*t) := Real.one_le_exp_iff.mpr (by positivity)
  have hMp : (M:ℝ)+1≤2*Real.exp (r*t) := by
    change (M:ℝ)≤Real.exp (r*t) at hM
    linarith only [hM,he1]
  have hrec : Real.exp (-Real.log (Y:ℝ))≤Real.exp (-t) :=
    Real.exp_le_exp.mpr (neg_le_neg htL)
  calc
    _ = ((M:ℝ)+1)^2*Real.exp (-Real.log (Y:ℝ)) := by
      rw [Real.exp_neg,Real.exp_log hY0]
      ring
    _ ≤ (2*Real.exp (r*t))^2*Real.exp (-t) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hMp 2) hrec
        (Real.exp_pos _).le (sq_nonneg _)
    _ = 4*Real.exp ((2*r-1)*t) := by
      rw [show (2*Real.exp (r*t))^2*Real.exp (-t) =
        4*((Real.exp (r*t)*Real.exp (r*t))*Real.exp (-t)) by ring,
        ← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ 4*Real.exp (-2*r*t) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hr : 4*r≤1 := by norm_num [r]
      nlinarith only [mul_le_mul_of_nonneg_right hr ht]
    _ = _ := by
      congr 2
      dsimp only [r,t]
      ring

/-- One separable pole channel approximates every normalized mixed prime
packet, uniformly over all detail horizons and the growing coarse range. -/
theorem exists_fullPrimeWindowCoupling_all_detail_rank_one_rate :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop,
      ∀ M : ℕ, (M:ℝ)≤Real.exp ((1/184320000:ℝ)*Real.sqrt (Real.log Y)) →
      ∀ (X : ℕ) (d q : ℕ → ℝ),
      (∑ a ∈ Icc 1 X,haarMass a*d a^2)≤1 →
      (∑ b ∈ Icc 1 M,logCellWidth b*q b^2)≤1 →
      |∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc 1 X,d a*
        (fullPrimeWindowCoupling (haarProfile a) Y b/Real.sqrt Y-
          (4*(Real.sqrt ((2:ℝ)*b+2)-Real.sqrt ((2:ℝ)*b)))*
            (∫ u,haarProfile a u*Real.exp (-u/2))))| ≤
        C*Real.exp (-(1/92160000:ℝ)*Real.sqrt (Real.log Y)) := by
  obtain ⟨C,hC,hbound⟩ := exists_fullPrimeWindowRemainder_all_detail_growing_coarse_rate
  have hlog : Tendsto (fun Y : ℕ => Real.log (Y:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C+16,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1,hlog.eventually_ge_atTop 1]
    with Y hboundY hY hL
  intro M hM X d q hd hq
  let P := ∑ a ∈ Icc 1 X,d a*(∫ u,haarProfile a u*Real.exp (u/2))
  let Q := ∑ b ∈ Icc 1 M,q b*(∫ u,coarseProfile b u*Real.exp (-u/2))
  have hP : |P|≤1 := abs_haar_exp_pos_sum_le_of_unit_mass d hd
  have hQ : |Q|≤2*((M:ℝ)+1)^2 := abs_coarse_exp_neg_sum_le_of_unit_mass q hq
  have hY0 : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hentry (a b : ℕ) (ha : 1≤a) (hb : 1≤b) :
      fullPrimeWindowCoupling (haarProfile a) Y b/Real.sqrt Y-
        (4*(Real.sqrt ((2:ℝ)*b+2)-Real.sqrt ((2:ℝ)*b)))*
          (∫ u,haarProfile a u*Real.exp (-u/2)) =
      fullPrimeWindowRemainder Y a b+
        (2*(∫ u,haarProfile a u*Real.exp (u/2))*
          (∫ u,coarseProfile b u*Real.exp (-u/2)))/(Y:ℝ) := by
    rw [fullPrimeWindowRemainder,
      ← fullPrimeWindowCoupling_eq_tsum_euler (X := a+(b+1)*Y)
        hY ha hb (by omega) (by nlinarith only [Nat.zero_le a]),
      sub_div,fullPrimeWindowMixedPole_div_sqrt hY hb]
    ring
  have hsep : (∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc 1 X,d a*
      ((2*(∫ u,haarProfile a u*Real.exp (u/2))*
        (∫ u,coarseProfile b u*Real.exp (-u/2)))/(Y:ℝ)))) =
      ((2/(Y:ℝ))*P)*Q := by
    calc
      _ = ∑ b ∈ Icc 1 M,((2/(Y:ℝ))*P)*
          (q b*(∫ u,coarseProfile b u*Real.exp (-u/2))) := by
        apply sum_congr rfl
        intro b hb
        rw [mul_sum]
        calc
          _ = ∑ a ∈ Icc 1 X,
              ((2/(Y:ℝ))*(q b*(∫ u,coarseProfile b u*Real.exp (-u/2))))*
                (d a*(∫ u,haarProfile a u*Real.exp (u/2))) := by
            apply sum_congr rfl
            intro a ha
            ring
          _ = ((2/(Y:ℝ))*(q b*(∫ u,coarseProfile b u*Real.exp (-u/2))))*P :=
            (mul_sum _ _ _).symm
          _ = _ := by ring
      _ = _ := (mul_sum _ _ _).symm
  have hsmall : |((2/(Y:ℝ))*P)*Q| ≤
      16*Real.exp (-(1/92160000:ℝ)*Real.sqrt (Real.log Y)) := by
    calc
      _ = (2/(Y:ℝ))*|P| * |Q| := by
        rw [abs_mul,abs_mul,abs_of_pos (div_pos (by norm_num) hY0)]
      _ ≤ (2/(Y:ℝ))*1*(2*((M:ℝ)+1)^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP (by positivity)) hQ
          (abs_nonneg _) (by positivity)
      _ = 4*(((M:ℝ)+1)^2/(Y:ℝ)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (prime_window_opposite_pole_rate hY hL hM) (show (0:ℝ)≤4 by norm_num)).trans_eq (by ring)
  have he : (∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc 1 X,d a*
      (fullPrimeWindowCoupling (haarProfile a) Y b/Real.sqrt Y-
        (4*(Real.sqrt ((2:ℝ)*b+2)-Real.sqrt ((2:ℝ)*b)))*
          (∫ u,haarProfile a u*Real.exp (-u/2))))) =
      (∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc 1 X,d a*fullPrimeWindowRemainder Y a b))+
        ((2/(Y:ℝ))*P)*Q := by
    calc
      _ = ∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc 1 X,d a*
          (fullPrimeWindowRemainder Y a b+
            (2*(∫ u,haarProfile a u*Real.exp (u/2))*
              (∫ u,coarseProfile b u*Real.exp (-u/2)))/(Y:ℝ))) := by
        apply sum_congr rfl
        intro b hb
        congr 1
        apply sum_congr rfl
        intro a ha
        rw [hentry a b (mem_Icc.mp ha).1 (mem_Icc.mp hb).1]
      _ = _ := by
        simp_rw [mul_add]
        simp_rw [sum_add_distrib]
        simp_rw [mul_add]
        rw [sum_add_distrib,hsep]
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add (hboundY M hM X d q hd hq) hsmall).trans_eq (by ring))

#print axioms exists_fullPrimeWindowCoupling_all_detail_rank_one_rate
#print axioms exists_fullPrimeWindowRemainder_all_detail_growing_coarse_rate
#print axioms exists_allPrimesMixedSource_all_detail_growing_coarse_rate
end GaloisForLFunctions.ArithmeticIndexDescent
