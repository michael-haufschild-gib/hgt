import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.SincSamplingOfShortPeriods
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfScaleOfTheRate

/-!
# A log-free square-root floor for integer alphabets

Shift the positive sinc-square sampler to 4K. Each centered sawtooth still
has mean zero. On the positive integers the sampler is bounded by 68K
times the pronic excess weight. Its negative tail has mass at most 1/4,
which can be absorbed using the exact global peak of the multiplicity.
The resulting peak bound and the zero uncertainty law give a square-root
rate floor for every producer.
-/

open Finset Filter Topology GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.TransThresholdPairCorrelation
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

/-- The floor multiplicity on all integer translates of its common period. -/
def periodicFloorHeight (c : ℕ →₀ ℤ) (z : ℤ) : ℝ :=
  stepWeight c (z : ZMod (IsProducer.period c)).val

theorem periodicFloorHeight_natCast {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (n : ℕ) :
    periodicFloorHeight c n = stepWeight c n := by
  simp only [periodicFloorHeight,Int.cast_natCast,ZMod.val_natCast]
  apply congrArg (fun u : ℤ => (u : ℝ))
  exact (stepWeight_periodic hP.zero hP.balanced IsProducer.dvd_period
    (n / IsProducer.period c) (n % IsProducer.period c)).symm.trans
      (congrArg (stepWeight c) (by rw [Nat.mul_comm, Nat.div_add_mod]))

private theorem residue_class_mean (k : ℕ) [NeZero k] :
    ∑ j : ZMod k, residue k j.val = 0 := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    change ∑ i : Fin (k+1), residue (k+1) i.val = 0
    rw [Fin.sum_univ_eq_sum_range]
    exact (isMeanZero_residue (Nat.succ_pos k)).mean

/-- Exact whole-line reconstruction of the peak from one shifted positive sampler. -/
theorem sinc_mean_periodicFloorHeight {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : 0 < K) (hal : AlphabetLE c K) (s : ℤ) :
    HasSum (fun z : ℤ => gridSincWeight K (z-s)*periodicFloorHeight c z) ((peak c : ℝ)/2) := by
  let L := IsProducer.period c
  letI : NeZero L := ⟨hP.period_pos.ne'⟩
  have hW : HasSum (fun z : ℤ => gridSincWeight K (z-s)) 1 :=
    (Equiv.subRight s).hasSum_iff.mpr ((summable_gridSincWeight hK).hasSum_iff.mpr (tsum_gridSincWeight hK))
  have hc (k : ℕ) (hk : k ∈ c.support) :
      HasSum (fun z : ℤ => gridSincWeight K (z-s) *
        ((-(c k : ℝ)/k)*residue k (z : ZMod L).val)) 0 := by
    have hk0 : k ≠ 0 := fun he => Finsupp.mem_support_iff.mp hk (he ▸ hP.zero)
    letI : NeZero k := ⟨hk0⟩
    have h := hasSum_gridSinc_periodic_mean (hal k hk) (fun j : ZMod k => residue k j.val) s
    rw [residue_class_mean,zero_div] at h
    have h' := h.mul_left (-(c k : ℝ)/k)
    rw [mul_zero] at h'
    apply h'.congr_fun
    intro z
    have hcast : (((z : ZMod L).val : ℕ) : ZMod k) = (z : ZMod k) := by
      have H := congrArg (ZMod.castHom (IsProducer.dvd_period k hk) (ZMod k))
        (ZMod.natCast_zmod_val (z : ZMod L))
      simpa only [map_natCast,map_intCast] using H
    have hres : (z : ZMod L).val % k = (z : ZMod k).val := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
    simp only [residue,hres,Nat.mod_eq_of_lt (ZMod.val_lt _)]
    ring
  have hs := (hW.mul_right ((peak c : ℝ)/2)).add (hasSum_sum (s := c.support) hc)
  simp only [one_mul,sum_const_zero,add_zero] at hs
  apply hs.congr_fun
  intro z
  rw [periodicFloorHeight,stepWeight_eq_mean_add hP.zero hP.balanced,mul_add,mul_sum]

private def weight (K : ℕ) (z : ℤ) := gridSincWeight K (z-4*K)

private theorem positive_cost {K : ℕ} (hK : 0 < K) (n : ℕ) :
    weight K ((n:ℤ)+1) * (((n:ℝ)+1)*((n:ℝ)+2)) ≤ 68*K := by
  let z := (n:ℤ)+1-4*K
  have h₁ := gridSincWeight_mul_sq_le hK z
  have h₂ := (le_div_iff₀ (by exact_mod_cast hK : (0:ℝ) < K)).mp (gridSincWeight_le_peak hK z)
  have h₃ := mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg (α := ℝ) K)
  let x : ℝ := (n:ℝ)+1
  have hx : 1 ≤ x := by dsimp [x]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hz : (z : ℝ) = x-4*K := by dsimp [z,x]; push_cast; ring
  have he : x*(x+1) ≤ 4*(z:ℝ)^2+64*(K:ℝ)^2 := by
    rw [hz]
    nlinarith only [sq_nonneg (x-8*K),mul_nonneg (by linarith : 0 ≤ x) (sub_nonneg.mpr hx)]
  have hb := mul_le_mul_of_nonneg_left he (gridSincWeight_nonneg K z)
  change gridSincWeight K z*(x*((n:ℝ)+2)) ≤ 68*K
  rw [show (n:ℝ)+2=x+1 by dsimp [x]; ring]
  linarith only [hb,h₁,h₃]

/-- A telescoping upper bound for one tail of the translated sampler. -/
def tailCap (K n : ℕ) : ℝ := (K:ℝ)/(((n:ℝ)+4*K)*((n:ℝ)+4*K+1))

private theorem negative_cost {K : ℕ} (hK : 0 < K) (n : ℕ) :
    weight K (-((n:ℤ)+1)) ≤ tailCap K n := by
  let z := -((n:ℤ)+1)-4*K
  have h := gridSincWeight_mul_sq_le hK z
  have he : (z:ℝ) = -((n:ℝ)+4*K+1) := by dsimp [z]; push_cast; ring
  rw [tailCap,le_div_iff₀ (by positivity)]
  change gridSincWeight K z * _ ≤ K
  apply le_trans (mul_le_mul_of_nonneg_left _ (gridSincWeight_nonneg K z)) h
  rw [he]
  nlinarith only [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) K]

theorem hasSum_tailCap {K : ℕ} (hK : 0 < K) : HasSum (tailCap K) (1/4) := by
  let u (n : ℕ) := 1/((n:ℝ)+4*K)
  have hstep (n : ℕ) : tailCap K n = (K:ℝ)*(u n-u (n+1)) := by
    dsimp [tailCap,u]
    push_cast
    field_simp
    ring
  have ht : Tendsto u atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => show 0 ≤ tailCap K n by unfold tailCap; positivity) _).mpr
  simp_rw [hstep, ←mul_sum, sum_range_sub']
  have he : (K:ℝ)*(u 0 - 0) = 1/4 := by dsimp [u]; push_cast; field_simp; ring
  exact he ▸ ((tendsto_const_nhds (x := u 0)).sub ht).const_mul (K:ℝ)

private def majorant (c : ℕ →₀ ℤ) (m B K : ℕ) : ℤ → ℝ
  | .ofNat 0 => 0
  | .ofNat (n+1) => 68*K*IsProducer.excessTerm m B c n
  | .negSucc n => (peak c : ℝ)*tailCap K n

/-- The peak is bounded by the window height plus the excess times the alphabet width. -/
theorem peak_le_sinc_excess {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : 0 < K) (hal : AlphabetLE c K) :
    (peak c : ℝ) ≤ 4*m + 272*K*excess c m B := by
  have hmean := sinc_mean_periodicFloorHeight hP hK hal (4*K)
  have hW : HasSum (weight K) 1 :=
    (Equiv.subRight (4*(K:ℤ))).hasSum_iff.mpr ((summable_gridSincWeight hK).hasSum_iff.mpr (tsum_gridSincWeight hK))
  have hpos : HasSum (fun n : ℕ => majorant c m B K (n+1)) (68*K*excess c m B) :=
    hP.hasSum_excess.mul_left _
  have hneg : HasSum (fun n : ℕ => majorant c m B K (-(n+1))) ((peak c : ℝ)*(1/4)) :=
    (hasSum_tailCap hK).mul_left _
  have hpeak : 0 ≤ (peak c : ℝ) := by exact_mod_cast (hP.nonneg 0).trans (hP.stepWeight_le_peak _)
  have hs := (hW.mul_right (m:ℝ)).add (hpos.of_add_one_of_neg_add_one hneg)
  have hle (z : ℤ) : weight K z * periodicFloorHeight c z ≤ weight K z * m + majorant c m B K z := by
    have hW0 : 0 ≤ weight K z := gridSincWeight_nonneg _ _
    cases z with
    | ofNat n =>
      cases n with
      | zero => simp [periodicFloorHeight,majorant,stepWeight_zero]; positivity
      | succ n =>
        change weight K ((n:ℤ)+1)*periodicFloorHeight c ((n+1:ℕ) : ℤ) ≤ _ + 68*K*IsProducer.excessTerm m B c n
        rw [periodicFloorHeight_natCast hP]
        let D : ℝ := ((n:ℝ)+1)*((n:ℝ)+2)
        have hD : D ≠ 0 := by dsimp [D]; positivity
        have he : (stepWeight c (n+1) : ℝ) ≤ m + D*IsProducer.excessTerm m B c n := by
          unfold IsProducer.excessTerm
          change _ ≤ m+D*((_ - _)/D)
          rw [mul_div_cancel₀ _ hD]
          split_ifs <;> linarith only [Nat.cast_nonneg (α := ℝ) m]
        have hcost := mul_le_mul_of_nonneg_right (positive_cost hK n) (hP.excessTerm_nonneg n)
        have hg := mul_le_mul_of_nonneg_left he hW0
        dsimp only [D] at hg
        change weight K (.ofNat (n+1))*(((n:ℝ)+1)*(n+2))*IsProducer.excessTerm m B c n ≤ _ at hcost
        change weight K (.ofNat (n+1))*(stepWeight c (n+1):ℝ) ≤
          weight K (.ofNat (n+1))*m + 68*K*IsProducer.excessTerm m B c n
        linarith only [hg,hcost]
    | negSucc n =>
      have hg : periodicFloorHeight c (.negSucc n) ≤ (peak c : ℝ) := by
        unfold periodicFloorHeight
        exact_mod_cast hP.stepWeight_le_peak _
      have h₁ := mul_le_mul_of_nonneg_left hg hW0
      have h₂ := mul_le_mul_of_nonneg_right (negative_cost hK n) hpeak
      change weight K (.negSucc n)*(peak c:ℝ) ≤ tailCap K n*(peak c:ℝ) at h₂
      change _ ≤ _ + (peak c : ℝ)*tailCap K n
      linarith only [h₁,h₂,mul_nonneg hW0 (Nat.cast_nonneg (α := ℝ) m)]
  have h := hasSum_le hle hmean hs
  change (peak c : ℝ)/2 ≤ 1*m+(68*K*excess c m B+0+(peak c : ℝ)*(1/4)) at h
  linarith only [h]

/-- The normalized rate of every admissible integer floor row on [1,K] is
at least a fixed positive constant divided by the square root of K. -/
theorem exists_log_free_half_floor :
    ∃ η : ℝ, 0 < η ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ), 1 ≤ K → IsProducer c m B → AlphabetLE c K →
      η/Real.sqrt K ≤ rate c m B := by
  obtain ⟨δ,hδ,hδ1,hlaw⟩ := exists_uncertainty_constant
  refine ⟨δ/276,by positivity,fun K c m B hK hP hAB => ?_⟩
  let ε := rate c m B
  let x := IsProducer.peakRatio c m
  have hm := hP.m_pos
  have hε : 0 < ε := hP.rate_pos
  have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hS : 1 ≤ Real.sqrt (K:ℝ) := Real.one_le_sqrt.mpr hKR
  have hSp : 0 < Real.sqrt (K:ℝ) := by linarith
  have hS2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) K)
  rw [div_le_iff₀ hSp]
  by_contra! hn
  change ε * Real.sqrt K < δ/276 at hn
  have hεS := le_mul_of_one_le_right hε.le hS
  have hsmall : ε ≤ 1 := by linarith only [hn,hδ1,hεS]
  have hx : x ≤ 4+272*K*ε := by
    change (peak c : ℝ)/m ≤ _
    rw [div_le_iff₀ hm]
    have h := peak_le_sinc_excess hP hK hAB
    have ht := mul_le_mul_of_nonneg_left hP.excess_le (by positivity : 0 ≤ 272*(K:ℝ))
    linarith only [h,ht]
  have hlow : δ ≤ ε*x := hlaw c m B hP hsmall
  have hprod := mul_le_mul_of_nonneg_left hx hε.le
  have hy : ε*Real.sqrt K ≤ 1 := by linarith only [hn,hδ1]
  have hy2 := mul_le_mul_of_nonneg_left hy (mul_nonneg hε.le hSp.le)
  rw [mul_one] at hy2
  have he : (ε*Real.sqrt K)*(ε*Real.sqrt K) = K*ε^2 := by
    calc _ = (Real.sqrt K)^2*ε^2 := by ring
         _ = _ := by rw [hS2]
  rw [he] at hy2
  linarith only [hlow,hprod,hεS,hy2,hn]

#print axioms sinc_mean_periodicFloorHeight
#print axioms peak_le_sinc_excess
#print axioms exists_log_free_half_floor

end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
