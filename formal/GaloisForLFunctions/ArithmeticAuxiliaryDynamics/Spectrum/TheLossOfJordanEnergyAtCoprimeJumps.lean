import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.JordanEnergyOfAnIntegerFloorRow

import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.TheSquareRootFloorOfEveryIntegerAlphabet
import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# The loss of Jordan energy at odd jumps of an integer floor row

The level-one Haar differences (Arushi–Goswami–Das–Santra, Definition 2.8)
pair each odd sample with its predecessor. The jump and the room on either
side of the pair exactly decompose its loss below the binary ceiling. The
coprime jumps alone force a spectral loss at Euler-totient density.
-/
noncomputable section
open Finset Filter Topology GaloisForLFunctions.ArithmeticKreinLangerTheory
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

/-- Unused variance at a height between zero and the top P. -/
private def slack (P u : ℝ) := u*(P-u)

private theorem slack_pair (P a b : ℝ) :
    slack P a+slack P b=slack P |b-a|+2*min a b*(P-max a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,max_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
    dsimp only [slack]; ring
  · rw [min_eq_right h,max_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    dsimp only [slack]; ring

private theorem slack_jump_le {P a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ P) (hb' : b ≤ P) :
    slack P |b-a| ≤ slack P a+slack P b := by
  rw [slack_pair]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) (le_min ha hb))
    (sub_nonneg.mpr (max_le ha' hb')))

variable {c : ℕ →₀ ℤ} {m B K : ℕ}

private theorem sum_adjacent_le {S : Finset ℕ} {T : ℕ} {d : ℕ → ℝ}
    (hS : S⊆range T) (hodd : ∀ r∈S, ¬2∣r) (hd : ∀ r, 0 ≤ d r) :
    (∑ r∈S, (d r+d (r-1))) ≤ ∑ r∈range T, d r := by
  classical
  let V := S.image (fun r => r-1)
  have hdis : Disjoint S V := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hr'
    have h₁ := hodd k hk
    have h₂ := hodd (k-1) hr
    omega
  have hv : V⊆range T := by
    intro r hr
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hr
    exact mem_range.mpr ((Nat.sub_le _ _).trans_lt (mem_range.mp (hS hk)))
  have hinj : ∀ a∈S, ∀ b∈S, a-1=b-1 → a=b := by
    intro a ha b hb he
    have h₁ := hodd a ha
    have h₂ := hodd b hb
    omega
  rw [sum_add_distrib,←sum_image hinj,←sum_union hdis]
  exact sum_le_sum_of_subset_of_nonneg (union_subset hS hv) fun r _ _ => hd r

/-- Every selection of disjoint odd Haar pairs consumes the quadratic
defect of the same row. Keeping all odd sites gives the strongest such bound. -/
theorem odd_jump_energy_budget (hP : IsProducer c m B) (hK : AlphabetLE c K)
    (S : Finset ℕ) (hS : S⊆range K.factorial) (hodd : ∀ r∈S, ¬2∣r) :
    12*(∑ r∈S, |(increment c r:ℝ)| * ((peak c:ℝ)- |(increment c r:ℝ)|)) ≤
      (K.factorial:ℝ)*(3*(peak c:ℝ)^2-jordanEnergy K c) := by
  let P : ℝ := peak c
  let H := fun r => (stepWeight c r:ℝ)
  have hn (r : ℕ) : 0 ≤ H r := by
    dsimp only [H]
    exact_mod_cast hP.nonneg r
  have hp (r : ℕ) : H r ≤ P := by
    dsimp only [H,P]
    exact_mod_cast hP.stepWeight_le_peak r
  have hdiff (r : ℕ) (hr : r∈S) : H r-H (r-1)=(increment c r:ℝ) := by
    have hi := stepWeight_succ c (r-1)
    have hr' := hodd r hr
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hi
    dsimp only [H]
    exact_mod_cast (show stepWeight c r-stepWeight c (r-1)=increment c r by omega)
  have hpoint (r : ℕ) (hr : r∈S) :
      slack P |(increment c r:ℝ)| ≤ slack P (H r)+slack P (H (r-1)) := by
    rw [←hdiff r hr,add_comm]
    exact slack_jump_le (hn _) (hn _) (hp _) (hp _)
  have he := (sum_le_sum hpoint).trans (sum_adjacent_le hS hodd (d:=fun r => slack P (H r))
    (fun r => mul_nonneg (hn _) (sub_nonneg.mpr (hp _))))
  have hz : (K.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 12)).trans_eq ?_
  rw [jordan_defect hP hK, ←mul_assoc,
    show (K.factorial:ℝ) * (12 / K.factorial) = 12 by
      rw [mul_comm, div_mul_cancel₀ _ hz]]
  rfl

private theorem card_coprime_periods (D q : ℕ) :
    ((range (q*D)).filter D.Coprime).card = q*D.totient := by
  let f (r : ℕ) : ℕ := if D.Coprime r then 1 else 0
  have hcard (T : ℕ) : ((range T).filter D.Coprime).card = ∑ r ∈ range T, f r := by
    simp [f]
  have hbase : ∑ r ∈ range D, f r = D.totient := (hcard D).symm
  rw [hcard]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.succ_mul, sum_range_add, ih]
    congr 1
    refine (sum_congr rfl fun r _ => ?_).trans hbase
    simp only [f, Nat.add_comm (q*D) r, Nat.coprime_add_mul_right_right]

/-- Any even divisor of the period which meets every active letter above one
gives a loss at its own unit density. This retains the larger density of
sparse alphabets even when the maximum letter is large. -/
theorem jordan_loss_from_a_covering_modulus (hP : IsProducer c m B) (hK : AlphabetLE c K)
    {D : ℕ} (hD : D ∣ K.factorial) (heven : 2 ∣ D)
    (hcover : ∀ k ∈ c.support, k ≠ 1 → ¬D.Coprime k) :
    12*(D.totient:ℝ)*(c 1:ℝ)*((peak c:ℝ)-c 1) ≤
      (D:ℝ)*(3*(peak c:ℝ)^2-jordanEnergy K c) := by
  let T := K.factorial
  let S := (range T).filter D.Coprime
  have hodd (r : ℕ) (hr : r∈S) : ¬2∣r := fun hd => by
    have he := Nat.eq_one_of_dvd_coprimes (mem_filter.mp hr).2 heven hd
    omega
  have hrough (r : ℕ) (hr : r∈S) : IsRough c r := fun k hk hk₁ hd =>
    hcover k hk hk₁ (Nat.Coprime.of_dvd_right hd (mem_filter.mp hr).2)
  have h := odd_jump_energy_budget hP hK S (filter_subset _ _) hodd
  have hc : 0 ≤ (c 1:ℝ) := by
    have hz := hP.nonneg 1
    rw [stepWeight_one hP.zero] at hz
    exact_mod_cast hz
  have hsum : (∑ r∈S, |(increment c r:ℝ)| * ((peak c:ℝ)- |(increment c r:ℝ)|)) =
      (S.card:ℝ)*((c 1:ℝ)*((peak c:ℝ)-c 1)) := by
    calc _ = ∑ _r∈S, (c 1:ℝ)*((peak c:ℝ)-c 1) := sum_congr rfl fun r hr => by
           rw [increment_of_isRough (hrough r hr),abs_of_nonneg hc]
         _ = _ := by rw [sum_const,nsmul_eq_mul]
  rw [hsum] at h
  obtain ⟨q,hq⟩ := hD
  have hT : T=q*D := hq.trans (Nat.mul_comm _ _)
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.mul_zero] at hq
    exact Nat.factorial_ne_zero K hq
  change 12*((S.card:ℝ)*_) ≤ (T:ℝ)*_ at h
  have hSc : S.card = q*D.totient := by
    change ((range T).filter D.Coprime).card = _
    rw [hT, card_coprime_periods]
  rw [hSc,hT] at h
  push_cast at h
  apply (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hqpos : 0 < (q:ℝ))).mp
  linarith only [h]

/-- Each unit residue reports the first letter. The resulting
totient-density price is independent of the distribution of the remaining letters. -/
theorem coprime_jump_energy_budget (hP : IsProducer c m B) (hK : AlphabetLE c K) (h₂ : 2 ≤ K) :
    12*(K.factorial.totient:ℝ)*(c 1:ℝ)*((peak c:ℝ)-c 1) ≤
      (K.factorial:ℝ)*(3*(peak c:ℝ)^2-jordanEnergy K c) := by
  apply jordan_loss_from_a_covering_modulus hP hK dvd_rfl (Nat.dvd_factorial (by decide) h₂)
  intro k hk hk₁ he
  have hp : 0 < k := Nat.pos_of_ne_zero fun hz => Finsupp.mem_support_iff.mp hk (hz ▸ hP.zero)
  exact hk₁ (Nat.eq_one_of_dvd_coprimes he (Nat.dvd_factorial hp (hK k hk)) dvd_rfl)

/-- For any family with rate tending to zero, the Jordan loss per coprime
jump is eventually at least half of the first-letter times the peak. -/
theorem small_rate_forces_relative_jordan_loss :
    ∃ η : ℝ, 0 < η ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ),
      IsProducer c m B → AlphabetLE c K → 2 ≤ K → rate c m B ≤ η →
      6*(K.factorial.totient:ℝ)*(m:ℝ)*(peak c:ℝ) ≤
        (K.factorial:ℝ)*(3*(peak c:ℝ)^2-jordanEnergy K c) := by
  obtain ⟨a,ha,hfirst⟩ := first_height_rate_floor
  refine ⟨a/2,by positivity,fun K c m B hp hk h₂ hr => ?_⟩
  have hs := hfirst c m B hp
  rw [stepWeight_one hp.zero] at hs
  have hn : 0 ≤ (peak c:ℝ) := by exact_mod_cast (hp.nonneg 1).trans (hp.stepWeight_le_peak 1)
  have hm : (m:ℝ) ≤ c 1 := by
    have hw := hp.window 1 (mem_Ico.mpr ⟨le_rfl,hp.two_le_B⟩)
    rw [stepWeight_one hp.zero] at hw
    exact_mod_cast hw
  have hprice : (c 1:ℝ) ≤ (peak c:ℝ)/2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    calc a*(c 1:ℝ) ≤ rate c m B*(peak c:ℝ) := hs
         _ ≤ (a/2)*(peak c:ℝ) := mul_le_mul_of_nonneg_right hr hn
         _ = a*((peak c:ℝ)/2) := by ring
  have hprod := mul_le_mul hm (by linarith only [hprice] : (peak c:ℝ)/2 ≤ (peak c:ℝ)-c 1)
    (div_nonneg hn (by norm_num)) (hm.trans' (Nat.cast_nonneg _))
  have h := mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ 12*K.factorial.totient by positivity)
  exact (by linarith only [h] : 6*(K.factorial.totient:ℝ)*(m:ℝ)*(peak c:ℝ) ≤
    12*(K.factorial.totient:ℝ)*(c 1:ℝ)*((peak c:ℝ)-c 1)).trans (coprime_jump_energy_budget hp hk h₂)

/-- The relative gap below the Jordan ceiling. -/
def relativeJordanLoss (K : ℕ) (c : ℕ →₀ ℤ) := 3-jordanEnergy K c/(peak c:ℝ)^2

private theorem totient_factorial_product (K : ℕ) :
    (K.factorial.totient:ℝ)=(K.factorial:ℝ)*RHTower.mertensPrimeProduct K := by
  have h := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors K.factorial)
  push_cast at h
  rw [h]
  congr 1
  rw [RHTower.mertensPrimeProduct,←prod_filter]
  congr 1
  ext p
  simp only [Nat.mem_primeFactors,mem_filter,mem_Icc,Nat.zero_le,true_and]
  exact ⟨fun e => ⟨e.1.dvd_factorial.mp e.2.1,e.1⟩,fun e => ⟨e.2,e.2.dvd_factorial.mpr e.1,Nat.factorial_ne_zero K⟩⟩

/-- In the small-rate regime the distance to the binary ceiling is
bounded below by the Mertens product divided by the width-rate budget. -/
theorem jordan_loss_rate_tradeoff :
    ∃ η : ℝ, 0 < η ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ),
      IsProducer c m B → AlphabetLE c K → 2 ≤ K → rate c m B ≤ η →
      6*RHTower.mertensPrimeProduct K ≤ (4+272*K*rate c m B)*relativeJordanLoss K c := by
  obtain ⟨η,hη,hgap⟩ := small_rate_forces_relative_jordan_loss
  refine ⟨η,hη,fun K c m B hP hK h₂ hr => ?_⟩
  let P : ℝ := peak c
  let d := relativeJordanLoss K c
  have hp : 0 < P := by
    have hh := (hP.window 1 (mem_Ico.mpr ⟨le_rfl,hP.two_le_B⟩)).trans (hP.stepWeight_le_peak 1)
    exact hP.m_pos.trans_le (by dsimp only [P]; exact_mod_cast hh)
  have hT : 0 < (K.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos K)
  have heq : 3*P^2-jordanEnergy K c=d*P^2 := by
    change 3*P^2-jordanEnergy K c = (3-jordanEnergy K c/P^2)*P^2
    rw [sub_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hp.ne')]
  have hd : 0 ≤ d := by
    apply nonneg_of_mul_nonneg_left (b:=P^2) _ (sq_pos_of_pos hp)
    rw [←heq]
    exact sub_nonneg.mpr (jordan_ceiling hP hK)
  have hb := hgap K c m B hP hK h₂ hr
  rw [totient_factorial_product,←show 3*P^2-jordanEnergy K c=3*(peak c:ℝ)^2-jordanEnergy K c from rfl,heq] at hb
  have h₁ : 6*RHTower.mertensPrimeProduct K*m ≤ d*P := by
    apply (mul_le_mul_iff_left₀ (mul_pos hT hp)).mp
    linarith only [hb]
  have hpeak := peak_le_sinc_excess hP (by omega) hK
  have hcost := mul_le_mul_of_nonneg_left hP.excess_le (show (0:ℝ) ≤ 272*K by positivity)
  have h₂' : P ≤ (4+272*K*rate c m B)*m := by linarith only [hpeak,hcost]
  have h := h₁.trans (mul_le_mul_of_nonneg_left h₂' hd)
  apply (mul_le_mul_iff_left₀ hP.m_pos).mp
  linarith only [h]

/-- An alphabet row at the square-root rate must lose a definite multiple
of 1/(√K log K) from its normalized Jordan ceiling. -/
theorem square_root_rate_forces_spectral_loss {A : ℝ} (hA : 0 < A) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ K : ℕ in Filter.atTop, ∀ (c : ℕ →₀ ℤ) (m B : ℕ),
      IsProducer c m B → AlphabetLE c K → rate c m B ≤ A/Real.sqrt K →
      c₀ ≤ Real.sqrt K*Real.log K*relativeJordanLoss K c := by
  obtain ⟨η,hη,h⟩ := jordan_loss_rate_tradeoff
  let e := Real.exp (-Real.eulerMascheroniConstant)
  have he : 0 < e := Real.exp_pos _
  let D := 4+272*A
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨3*e/D,by positivity,?_⟩
  have hs := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Filter.Tendsto (fun K : ℕ => A/Real.sqrt K) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hs
  have heuler : ∀ᶠ K : ℕ in atTop, e/2 < RHTower.mertensPrimeProduct K*Real.log K :=
    RHTower.tendsto_mertensPrimeProduct_mul_log (Ioi_mem_nhds (show e/2 < e by linarith))
  filter_upwards [Filter.eventually_ge_atTop 2,hsmall.eventually_lt_const hη,heuler]
    with K hK hr heK c m B hp hal hrate
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hlog := Real.log_nonneg hK1
  have hsK := Real.one_le_sqrt.mpr hK1
  have hsK' : 0 < Real.sqrt K := zero_lt_one.trans_le hsK
  have hsK2 := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) K)
  let d := relativeJordanLoss K c
  have h₁ := h K c m B hp hal hK (hrate.trans hr.le)
  have hd : 0 ≤ d := by
    have hw : 0 < 4+272*(K:ℝ)*rate c m B := by positivity [hp.rate_pos]
    exact nonneg_of_mul_nonneg_right ((by positivity [RHTower.mertensPrimeProduct_pos K] :
      0 ≤ 6*RHTower.mertensPrimeProduct K).trans h₁) hw
  have hmul := (le_div_iff₀ hsK').mp hrate
  have hsq := mul_le_mul_of_nonneg_right hmul hsK'.le
  rw [mul_assoc,←sq,hsK2] at hsq
  have hw : 4+272*K*rate c m B ≤ D*Real.sqrt K := by
    dsimp only [D]
    linarith only [hsq,hsK]
  have ht := mul_le_mul_of_nonneg_right (h₁.trans (mul_le_mul_of_nonneg_right hw hd)) hlog
  apply (div_le_iff₀ hD).mpr
  linarith only [ht,heK]

#print axioms jordan_loss_rate_tradeoff
#print axioms square_root_rate_forces_spectral_loss

#print axioms odd_jump_energy_budget
#print axioms jordan_loss_from_a_covering_modulus
#print axioms coprime_jump_energy_budget
#print axioms small_rate_forces_relative_jordan_loss
end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
