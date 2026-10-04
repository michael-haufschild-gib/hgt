import GaloisForLFunctions.RHTower.ChiPhysicalCubicPackets
import GaloisForLFunctions.RHTower.ChiPrimePacketFourthMoment

/-!
# Prime packets with unbounded noncontracting physical cubic

The source PNT constructs dense coherent prime packets. Even after both
repeated-prime contraction families are removed, their literal grade-one
physical cubic has positive mass growing faster than height. Coefficient energy
is exactly one and every coefficient tends to zero. Thus energy and individual
flatness cannot control this joint cubic. This does not assert a value or bound
for the full-window Gaussian coefficient family required by BAG.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- Actual cubic with the two repeated-prime contraction families removed. -/
def coherentPrimePacketCubicOffDiagonal (S : Finset ℕ) (t : ℝ) : ℂ :=
  physicalCubicPacket S (fun p q r => if p ≠ r ∧ q ≠ r then 1 else 0) t

/-- Off-diagonal tensor with the same unit-energy coefficient normalization in all three slots. -/
def normalizedPrimePacketCubicOffDiagonal (S : Finset ℕ) (t : ℝ) : ℂ :=
  (((Real.sqrt (S.card:ℝ))⁻¹ ^ 3 : ℝ):ℂ)*coherentPrimePacketCubicOffDiagonal S t

/-- This is the literal adjacent cubic minus its exact repeated-prime contractions. -/
theorem coherentPrimePacketCubicOffDiagonal_eq (S : Finset ℕ) (t : ℝ) :
    coherentPrimePacketCubicOffDiagonal S t =
      coherentPrimePacketPoly S t^2*(starRingEnd ℂ) (coherentPrimePacketPoly S t) -
        ((2*(S.card:ℝ)-1:ℝ):ℂ)*coherentPrimePacketPoly S t := by
  let e : ℕ → ℕ → ℕ → ℂ := fun p q r =>
    Complex.exp ((((Real.log p+Real.log q-Real.log r)*t:ℝ):ℂ)*I)
  have hpq (p q : ℕ) : e p q p = bourgainOscillation (t*Real.log q) := by
    dsimp [e,bourgainOscillation]
    congr 1
    push_cast
    ring
  have hqq (p q : ℕ) : e p q q = bourgainOscillation (t*Real.log p) := by
    dsimp [e,bourgainOscillation]
    congr 1
    push_cast
    ring
  have hphase (p q r : ℕ) : e p q r =
      bourgainOscillation (t*Real.log p)*bourgainOscillation (t*Real.log q)*
        (starRingEnd ℂ) (bourgainOscillation (t*Real.log r)) := by
    dsimp [e,bourgainOscillation]
    rw [← Complex.exp_conj]
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he (p q r : ℕ) : ((if p≠r ∧ q≠r then 1 else 0 : ℝ):ℂ)*e p q r =
      e p q r-(if r=p then e p q r else 0)-(if r=q then e p q r else 0)+
        (if q=p then (if r=p then e p q r else 0) else 0) := by
    by_cases hp : p=r
    · subst p
      by_cases hq : q=r
      · subst q; simp
      · simp [hq,Ne.symm hq]
    · by_cases hq : q=r
      · subst q; simp [hp,Ne.symm hp]
      · simp [hp,hq,Ne.symm hp,Ne.symm hq]
  have hfull : (∑ p ∈ S,∑ q ∈ S,∑ r ∈ S,e p q r) =
      coherentPrimePacketPoly S t^2*(starRingEnd ℂ) (coherentPrimePacketPoly S t) := by
    simp only [hphase,coherentPrimePacketPoly,pow_two,map_sum,← Finset.mul_sum,← Finset.sum_mul]
  unfold coherentPrimePacketCubicOffDiagonal physicalCubicPacket
  change (∑ p ∈ S,∑ q ∈ S,∑ r ∈ S,((if p≠r ∧ q≠r then 1 else 0 : ℝ):ℂ)*e p q r) = _
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [hfull]
  have hleft : (∑ p ∈ S,∑ q ∈ S,∑ r ∈ S,if r=p then e p q r else 0) =
      (S.card:ℂ)*coherentPrimePacketPoly S t := by
    calc
      _ = ∑ _p ∈ S, coherentPrimePacketPoly S t := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Finset.sum_ite_eq',if_pos hp,hpq,coherentPrimePacketPoly]
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hright : (∑ p ∈ S,∑ q ∈ S,∑ r ∈ S,if r=q then e p q r else 0) =
      (S.card:ℂ)*coherentPrimePacketPoly S t := by
    calc
      _ = ∑ p ∈ S,(S.card:ℂ)*bourgainOscillation (t*Real.log p) := by
        apply Finset.sum_congr rfl
        intro p _
        calc
          _ = ∑ _q ∈ S,bourgainOscillation (t*Real.log p) := by
            apply Finset.sum_congr rfl
            intro q hq
            simp only [Finset.sum_ite_eq',if_pos hq,hqq]
          _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ = _ := by simp only [← Finset.mul_sum,coherentPrimePacketPoly]
  have hover : (∑ p ∈ S,∑ q ∈ S,∑ r ∈ S,if q=p then (if r=p then e p q r else 0) else 0) =
      coherentPrimePacketPoly S t := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [Finset.sum_ite_eq',hp,hpq]
  rw [hleft,hright,hover]
  push_cast
  ring

private theorem cubic_offDiagonal_mass (S : Finset ℕ) :
    (∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, if p ≠ r ∧ q ≠ r then (1:ℝ) else 0) =
      (S.card:ℝ)*((S.card:ℝ)-1)^2 := by
  have hf (p q r : ℕ) : (if p ≠ r ∧ q ≠ r then (1:ℝ) else 0) =
      (1-(if p=r then (1:ℝ) else 0))*(1-(if q=r then (1:ℝ) else 0)) := by
    by_cases hp : p=r <;> by_cases hq : q=r <;> simp [hp,hq]
  calc
    _ = ∑ p ∈ S, ∑ r ∈ S, ∑ q ∈ S, if p ≠ r ∧ q ≠ r then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = ∑ r ∈ S, ∑ p ∈ S, ∑ q ∈ S, if p ≠ r ∧ q ≠ r then (1:ℝ) else 0 := Finset.sum_comm
    _ = ∑ r ∈ S, ((S.card:ℝ)-1)^2 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [hf, ← Finset.mul_sum]
      simp [Finset.sum_sub_distrib, hr, ← Finset.sum_mul, pow_two]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Removing both contraction families still leaves a positive cubic-order coherent mass. -/
theorem exists_coherentPrimePacketCubicOffDiagonal_positive :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H → H ≤ N/32 →
      2*Real.pi*H^2/N ≤ 1/4 → ∀ S : Finset ℕ, 2 ≤ S.card →
      (∀ p ∈ S, (p:ℝ) ∈ Icc N (N+H)) →
      (Real.pi*Real.sqrt N/16)*(S.card:ℝ)^3 ≤
        (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
          (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
            zetaChi (linePt t)*coherentPrimePacketCubicOffDiagonal S t).re := by
  obtain ⟨N₀,hN₀,hb⟩ := exists_physicalCubicPacket_positive
  refine ⟨N₀,hN₀,?_⟩
  intro N H hN hH hHN heps S hcard hS
  have hm : (2:ℝ) ≤ S.card := by exact_mod_cast hcard
  have hm0 : (0:ℝ) ≤ S.card := by positivity
  have hsq : (S.card:ℝ)^2/4 ≤ ((S.card:ℝ)-1)^2 := by nlinarith only [hm]
  have hmass := mul_le_mul_of_nonneg_left hsq hm0
  have hl := hb N H hN hH hHN heps S hS (fun p q r => if p≠r ∧ q≠r then 1 else 0)
    (by intros; split_ifs <;> norm_num)
  rw [cubic_offDiagonal_mass] at hl
  apply le_trans _ hl
  have hh := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ Real.pi*Real.sqrt N/4)
  nlinarith only [hh]

private theorem normalized_cubic_integral (N : ℝ) (S : Finset ℕ) :
    (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
      (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
        zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re =
      (Real.sqrt (S.card:ℝ))⁻¹ ^ 3 *
        (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
          (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
            zetaChi (linePt t)*coherentPrimePacketCubicOffDiagonal S t).re := by
  have he (t:ℝ) : (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
      zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t =
      (((Real.sqrt (S.card:ℝ))⁻¹ ^ 3 : ℝ):ℂ)*
        ((bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
          zetaChi (linePt t)*coherentPrimePacketCubicOffDiagonal S t) := by
    unfold normalizedPrimePacketCubicOffDiagonal
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, Complex.re_ofReal_mul]

/-- Constructed flat, unit-energy prime packets have an unbounded noncontracting
signed physical cubic per unit height. No prime-location or moment premise is assumed. -/
theorem eventually_exists_flat_prime_packet_cubic_offDiagonal_large :
    ∀ᶠ m : ℕ in atTop, ∃ (N : ℕ) (S : Finset ℕ),
      64*m^8 ≤ N ∧ N ≤ 128*m^8 ∧ m^3 ≤ S.card ∧
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N+m^4) ∧
      (∑ _p ∈ S, ‖(Real.sqrt (S.card:ℝ):ℂ)⁻¹‖^2) = 1 ∧
      ‖(Real.sqrt (S.card:ℝ):ℂ)⁻¹‖ ≤ 1/(m:ℝ) ∧
      physicalCubicPacketScale N*(Real.sqrt m/256) ≤
        (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
          (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
            zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re := by
  obtain ⟨N₀,hN₀,hb⟩ := exists_coherentPrimePacketCubicOffDiagonal_positive
  have ht : Tendsto (fun m:ℕ => 64*(m:ℝ)^8) atTop atTop :=
    (tendsto_const_mul_pow_atTop (by norm_num : (8:ℕ) ≠ 0)
      (by norm_num : (0:ℝ)<64)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_dense_prime_packet, ht.eventually_ge_atTop N₀,
    eventually_ge_atTop (2:ℕ)] with m hm hmlarge hm2
  obtain ⟨N,S,hNlo,hNhi,hcard,hS⟩ := hm
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hNloR : (64:ℝ)*(m:ℝ)^8 ≤ N := by exact_mod_cast hNlo
  have hNhiR : (N:ℝ) ≤ 128*(m:ℝ)^8 := by exact_mod_cast hNhi
  have hcardR : (m:ℝ)^3 ≤ S.card := by exact_mod_cast hcard
  have hM : (0:ℝ)<S.card := lt_of_lt_of_le (by positivity) hcardR
  have hNpos : (0:ℝ)<N := hN₀.trans_le (hmlarge.trans hNloR)
  have hH1 : (1:ℝ) ≤ (m:ℝ)^4 := one_le_pow₀ (by linarith only [hmR])
  have hHsq : ((m:ℝ)^4)^2 = (m:ℝ)^8 := by ring
  have hplateau : (m:ℝ)^4 ≤ (N:ℝ)/32 := by nlinarith only [hNloR,hHsq,hH1]
  have hcohere : 2*Real.pi*((m:ℝ)^4)^2/(N:ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ hNpos).mpr
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg ((m:ℝ)^4))
    nlinarith only [hNloR,hHsq,hpi]
  have hSreal : ∀ p ∈ S, (p:ℝ) ∈ Icc (N:ℝ) (N+(m:ℝ)^4) := by
    intro p hp
    exact ⟨by exact_mod_cast (hS p hp).2.1, by exact_mod_cast (hS p hp).2.2⟩
  have hM2 : 2 ≤ S.card := by
    have hh : (2:ℝ) ≤ S.card := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hmR 3
      norm_num at hh
      linarith only [hh,hcardR]
    exact_mod_cast hh
  have hl := hb N ((m:ℝ)^4) (hmlarge.trans hNloR) (by positivity) hplateau hcohere S hM2 hSreal
  have hs : 0 < Real.sqrt (S.card:ℝ) := Real.sqrt_pos.mpr hM
  have hs2 := Real.sq_sqrt hM.le
  have hn : ‖(Real.sqrt (S.card:ℝ):ℂ)⁻¹‖ = (Real.sqrt (S.card:ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have henergy : (∑ _p ∈ S, ‖(Real.sqrt (S.card:ℝ):ℂ)⁻¹‖^2) = 1 := by
    simp only [hn,Finset.sum_const,nsmul_eq_mul,inv_pow,hs2]
    exact mul_inv_cancel₀ hM.ne'
  have hflat : ‖(Real.sqrt (S.card:ℝ):ℂ)⁻¹‖ ≤ 1/(m:ℝ) := by
    have hmSq : (m:ℝ)^2 ≤ (m:ℝ)^3 := by
      nlinarith only [mul_nonneg (sq_nonneg (m:ℝ)) (show 0 ≤ (m:ℝ)-1 by linarith only [hmR])]
    have hms : (m:ℝ) ≤ Real.sqrt (S.card:ℝ) := Real.le_sqrt_of_sq_le (hmSq.trans hcardR)
    rw [hn,← one_div]
    exact one_div_le_one_div_of_le hm0 hms
  have hnormmass : (Real.pi*Real.sqrt N/16)*(S.card:ℝ)*Real.sqrt (S.card:ℝ) ≤
      (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
        (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
          zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re := by
    rw [normalized_cubic_integral]
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (Real.sqrt (S.card:ℝ))⁻¹^3)
    have he : (Real.pi*Real.sqrt N/16)*(S.card:ℝ)*Real.sqrt (S.card:ℝ) =
        (Real.sqrt (S.card:ℝ))⁻¹^3*((Real.pi*Real.sqrt N/16)*(S.card:ℝ)^3) := by
      rw [← hs2]
      simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
      field_simp
    rw [he]
    exact hh
  have hsqrtN : Real.sqrt N ≤ 12*(m:ℝ)^4 := by
    nlinarith only [hNhiR,hHsq,Real.sq_sqrt hNpos.le,Real.sqrt_nonneg (N:ℝ),hH1]
  have hsqrtM : (m:ℝ)*Real.sqrt m ≤ Real.sqrt (S.card:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    calc
      _ = (m:ℝ)^3 := by rw [mul_pow,Real.sq_sqrt hm0.le]; ring
      _ ≤ _ := hcardR
  have hcore : Real.sqrt N*Real.sqrt m ≤ 12*(S.card:ℝ)*Real.sqrt (S.card:ℝ) := by
    calc
      _ ≤ (12*(m:ℝ)^4)*Real.sqrt m := mul_le_mul_of_nonneg_right hsqrtN (Real.sqrt_nonneg _)
      _ = 12*((m:ℝ)^3*((m:ℝ)*Real.sqrt m)) := by ring
      _ ≤ _ := by
        have hh := mul_le_mul hcardR hsqrtM (by positivity) hM.le
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 12)
  have hscale : physicalCubicPacketScale N*(Real.sqrt m/256) ≤
      (Real.pi*Real.sqrt N/16)*(S.card:ℝ)*Real.sqrt (S.card:ℝ) := by
    calc
      _ = (Real.pi*Real.sqrt N/192)*(Real.sqrt N*Real.sqrt m) := by
        unfold physicalCubicPacketScale
        ring_nf
        rw [Real.sq_sqrt hNpos.le]
        ring
      _ ≤ (Real.pi*Real.sqrt N/192)*(12*(S.card:ℝ)*Real.sqrt (S.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = _ := by ring
  exact ⟨N,S,hNlo,hNhi,hcard,hS,henergy,hflat,hscale.trans hnormmass⟩

/-- No eventual constant bounds the actual noncontracting cubic using only prime
support, unit coefficient energy and individual coefficient flatness. -/
theorem no_uniform_flat_prime_packet_cubic_offDiagonal_bound :
    ¬ ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∀ (N : ℕ) (S : Finset ℕ),
      64*m^8 ≤ N → N ≤ 128*m^8 → m^3 ≤ S.card →
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N+m^4) →
      (∑ _p ∈ S, ‖(Real.sqrt (S.card:ℝ):ℂ)⁻¹‖^2) = 1 →
      ‖(Real.sqrt (S.card:ℝ):ℂ)⁻¹‖ ≤ 1/(m:ℝ) →
      (∫ t in physicalCubicPacketScale N..2*physicalCubicPacketScale N,
        (bagPhysicalHeightWindow (t/physicalCubicPacketScale N):ℂ)*
          zetaChi (linePt t)*normalizedPrimePacketCubicOffDiagonal S t).re ≤ C*physicalCubicPacketScale N := by
  rintro ⟨C,hC⟩
  have ht : Tendsto (fun m:ℕ => Real.sqrt (m:ℝ)/256) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num)
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨m,hm,hmC,hm1,hmlarge⟩ := (eventually_exists_flat_prime_packet_cubic_offDiagonal_large.and
    (hC.and ((eventually_ge_atTop (1:ℕ)).and (ht.eventually_gt_atTop C)))).exists
  obtain ⟨N,S,hNlo,hNhi,hcard,hS,henergy,hflat,hlower⟩ := hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
  have hNloR : (64:ℝ)*(m:ℝ)^8 ≤ N := by exact_mod_cast hNlo
  have hNpos : (0:ℝ)<N := lt_of_lt_of_le (by positivity) hNloR
  have hT : 0 < physicalCubicPacketScale N := by unfold physicalCubicPacketScale; positivity
  have hu := hmC N S hNlo hNhi hcard hS henergy hflat
  nlinarith only [hlower,hu,mul_pos hT (sub_pos.mpr hmlarge)]

end RHTower
