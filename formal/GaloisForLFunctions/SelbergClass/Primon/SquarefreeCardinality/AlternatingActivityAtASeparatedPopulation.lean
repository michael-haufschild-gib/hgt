import GaloisForLFunctions.SelbergClass.Primon.SquarefreeCardinality.TheTemperatureGapBetweenPopulationLayers
import GaloisForLFunctions.HTGeometry.SignAlternationHyperbolicity

/-!
# Detecting separate populations by alternating activity

An alternating sum with increasing terms up to j and decreasing terms
after j has the sign of term j if its two neighbors together are smaller.
The squarefree partition has this separation at an explicit negative
activity for each population whose ground-state energy is sufficiently large.
-/

open Finset Polynomial RHTower
namespace GaloisForLFunctions.SelbergClass.Primon

noncomputable section

private theorem sign_sq (i : ℕ) : (-1:ℝ)^i*(-1)^i=1 := by rw [←mul_pow]; norm_num

private theorem increasing_prefix (b : ℕ → ℝ) (hn : ∀ i, 0 ≤ b i) (n : ℕ)
    (h : ∀ i < n, b i ≤ b (i+1)) :
    0 ≤ (-1:ℝ)^n*∑ i ∈ range (n+1), (-1:ℝ)^i*b i ∧
    (-1:ℝ)^n*(∑ i ∈ range (n+1), (-1:ℝ)^i*b i) ≤ b n := by
  induction n with
  | zero => simpa using hn 0
  | succ n ih =>
    have hh := ih (fun i hi => h i (by omega))
    have he : (-1:ℝ)^(n+1)*(∑ i ∈ range (n+1+1), (-1:ℝ)^i*b i) =
        b (n+1)-(-1:ℝ)^n*(∑ i ∈ range (n+1), (-1:ℝ)^i*b i) := by
      rw [sum_range_succ,mul_add,←mul_assoc _ _ (b _),sign_sq,one_mul,pow_succ]
      ring
    rw [he]
    exact ⟨sub_nonneg.mpr (hh.2.trans (h n (by omega))), sub_le_self _ hh.1⟩

private theorem decreasing_prefix (b : ℕ → ℝ) (n : ℕ) (hn : ∀ i, 0 ≤ b i)
    (h : ∀ i, i+1 < n → b (i+1) ≤ b i) :
    0 ≤ ∑ i ∈ range n, (-1:ℝ)^i*b i ∧ (∑ i ∈ range n, (-1:ℝ)^i*b i) ≤ b 0 := by
  induction n generalizing b with
  | zero => simpa using hn 0
  | succ n ih =>
    have he : (∑ i ∈ range (n+1), (-1:ℝ)^i*b i) =
        b 0-∑ i ∈ range n, (-1:ℝ)^i*b (i+1) := by
      rw [sum_range_succ']
      simp only [pow_succ,mul_neg_one,neg_mul,sum_neg_distrib,pow_zero,one_mul]
      ring
    rw [he]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hn]
    · have hh := ih (fun i => b (i+1)) (fun i => hn _) (fun i hi => h (i+1) (by omega))
      exact ⟨sub_nonneg.mpr (hh.2.trans (h 0 (by omega))),sub_le_self _ hh.1⟩

/-- A strict peak in a positive coefficient row forces its alternating sign
if every step toward the peak contracts by less than one half in reverse. -/
theorem dominant_population_sign (b : ℕ → ℝ) (hn : ∀ i, 0 ≤ b i) {j d : ℕ} (hj : j ≤ d)
    (hb : 0 < b j) {q : ℝ} (hq : 0 ≤ q) (hq' : 2*q < 1)
    (hl : ∀ i < j, b i ≤ q*b (i+1)) (hr : ∀ i, j ≤ i → i < d → b (i+1) ≤ q*b i) :
    0 < (-1:ℝ)^j * ∑ i ∈ range (d+1), (-1:ℝ)^i*b i := by
  let L := ∑ i ∈ range j, (-1:ℝ)^i*b i
  let R := ∑ i ∈ range (d-j), (-1:ℝ)^i*b (j+1+i)
  have hq₁ : q ≤ 1 := by linarith only [hq,hq']
  have hL : |L| ≤ q*b j := by
    cases j with
    | zero => simpa [L] using mul_nonneg hq (hn 0)
    | succ n =>
      have hh := increasing_prefix b hn n (fun i hi =>
        (hl i (by omega)).trans (mul_le_of_le_one_left (hn _) hq₁))
      have he : |(-1:ℝ)^n*L|=|L| := by simp [abs_mul]
      rw [←he,abs_of_nonneg hh.1]
      exact hh.2.trans (hl n (by omega))
  have hR : R ≤ q*b j := by
    by_cases h : j=d
    · simpa [R,h] using mul_nonneg hq (hn d)
    · have hh := decreasing_prefix (fun i => b (j+1+i)) (d-j) (fun i => hn _)
        (fun i hi => (hr (j+1+i) (by omega) (by omega)).trans
          (mul_le_of_le_one_left (hn _) hq₁))
      exact hh.2.trans (hr j le_rfl (lt_of_le_of_ne hj h))
  have he : (∑ i ∈ range (d+1), (-1:ℝ)^i*b i) =
      L+(-1:ℝ)^j*b j+(-1:ℝ)^(j+1)*R := by
    rw [show d+1=(j+1)+(d-j) by omega,sum_range_add,sum_range_succ]
    simp only [L,R,pow_add,mul_sum,mul_assoc]
  rw [he,mul_add,mul_add,←mul_assoc _ _ (b j),sign_sq,one_mul,pow_succ]
  have hlow : -|L| ≤ (-1:ℝ)^j*L := by
    simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using
      (neg_abs_le ((-1:ℝ)^j*L))
  have hx : (-1:ℝ)^j*(((-1:ℝ)^j*(-1))*R) = -R := by
    calc _ = -(((-1:ℝ)^j*(-1)^j)*R) := by ring
         _ = _ := by rw [sign_sq,one_mul]
  rw [hx]
  linarith only [hlow,hL,hR,mul_lt_mul_of_pos_right hq' hb]

private theorem ground_mono {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ P.card) : leastPopulationEnergy P i ≤ leastPopulationEnergy P j := by
  induction j,hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans ((by omega : leastPopulationEnergy P j ≤ 2*leastPopulationEnergy P j).trans
      (leastPopulationEnergy_double hp (by omega)))

/-- Half the preceding ground energy; population zero uses half the vacuum energy. -/
def populationHalfGap (P : Finset ℕ) (j : ℕ) : ℝ := leastPopulationEnergy P (j-1)/2

/-- Logarithmic activity at which the j-particle term dominates its two neighbors. -/
def populationSlope (P : Finset ℕ) (j : ℕ) : ℝ := leastPopulationEnergy P j-populationHalfGap P j

private theorem slope_bounds {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {j : ℕ} (hj : j ≤ P.card) :
    (∀ i < j, (leastPopulationEnergy P (i+1):ℝ)-leastPopulationEnergy P i ≤
        populationSlope P j-populationHalfGap P j) ∧
    (∀ i, j ≤ i → i < P.card → populationSlope P j+populationHalfGap P j ≤
        (leastPopulationEnergy P (i+1):ℝ)-leastPopulationEnergy P i) := by
  constructor
  · intro i hi
    have he : populationSlope P j-populationHalfGap P j =
        (leastPopulationEnergy P j:ℝ)-leastPopulationEnergy P (j-1) := by
      unfold populationSlope populationHalfGap
      ring
    rw [he]
    by_cases h : i+1=j
    · simp [←h]
    · have hj₀ : 0 < j := by omega
      have h₁ := ground_mono hp (show i+1 ≤ j-1 by omega) (show j-1 ≤ P.card by omega)
      have h₂ := leastPopulationEnergy_double hp (j:=j-1) (by omega)
      rw [show j-1+1=j by omega] at h₂
      exact_mod_cast (show (leastPopulationEnergy P (i+1):ℤ)-leastPopulationEnergy P i ≤
        (leastPopulationEnergy P j:ℤ)-leastPopulationEnergy P (j-1) by omega)
  · intro i hi h
    rw [populationSlope,sub_add_cancel]
    have h₁ := ground_mono hp hi h.le
    have h₂ := leastPopulationEnergy_double hp h
    exact_mod_cast (show (leastPopulationEnergy P j:ℤ) ≤ (leastPopulationEnergy P (i+1):ℤ)-leastPopulationEnergy P i by omega)

/-- Every population whose energy gap dominates thermal uncertainty gives a
certified sign at a negative real activity. -/
theorem squarefree_negative_activity_sign {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p)
    {j : ℕ} (hj : j ≤ P.card) {β : ℝ} (hb : 0 < β)
    (hgap : 2*Real.exp (-β*populationHalfGap P j) < 1-Real.exp (-β)) :
    0 < (-1:ℝ)^j*(squarefreeCardinalityPolynomial P β).eval (-Real.exp (β*populationSlope P j)) := by
  let F := squarefreeCardinalityPolynomial P β
  let E (i : ℕ) : ℝ := leastPopulationEnergy P i
  let s := populationSlope P j
  let D := populationHalfGap P j
  let u := 1-Real.exp (-β)
  let q := Real.exp (-β*D)/u
  let b (i : ℕ) := F.coeff i*Real.exp (β*s*(i:ℝ))
  have hu : 0 < u := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb))
  have hq : 0 ≤ q := div_nonneg (Real.exp_pos _).le hu.le
  have hq' : 2*q < 1 := by change 2*(_/u)<1; rw [←mul_div_assoc,div_lt_one hu]; exact hgap
  have hn (i : ℕ) : 0 ≤ b i := by
    dsimp only [b,F]
    rw [squarefreeCardinality_coeff]
    exact mul_nonneg (sum_nonneg fun _ _ => (Real.exp_pos _).le) (Real.exp_pos _).le
  have hbox (i : ℕ) (hi : i ≤ P.card) :
      Real.exp (β*(s*i-E i)) ≤ b i ∧ u*b i ≤ Real.exp (β*(s*i-E i)) := by
    obtain ⟨hlo,hhi⟩ := normalized_population_enclosure hp hi hb
    change _ ≤ u⁻¹ at hhi
    have hhi' := mul_le_mul_of_nonneg_left hhi hu.le
    rw [mul_inv_cancel₀ hu.ne'] at hhi'
    have hem : Real.exp (β*(s*i-E i))*Real.exp (β*E i) = Real.exp (β*s*i) := by
      rw [←Real.exp_add]; congr 1; ring
    constructor
    · have h := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (β*(s*i-E i))).le
      calc _ ≤ Real.exp (β*(s*i-E i))*(Real.exp (β*E i)*F.coeff i) := by simpa using h
           _ = _ := by rw [←mul_assoc,hem]; dsimp only [b]; ring
    · have h := mul_le_mul_of_nonneg_left hhi' (Real.exp_pos (β*(s*i-E i))).le
      calc _ = Real.exp (β*(s*i-E i))*(u*(Real.exp (β*E i)*F.coeff i)) := by
                 dsimp only [b]; rw [←hem]; ring
           _ ≤ _ := by simpa only [mul_one] using h
  have hstep {i k : ℕ} (hi : i ≤ P.card) (hk : k ≤ P.card)
      (hprice : s*i-E i ≤ s*k-E k-D) : b i ≤ q*b k := by
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hprice hb.le)
    rw [show β*(s*k-E k-D) = -β*D+β*(s*k-E k) by ring,Real.exp_add] at h
    have hc := ((hbox i hi).2.trans h).trans (mul_le_mul_of_nonneg_left (hbox k hk).1 (Real.exp_pos _).le)
    dsimp only [q]
    rw [div_mul_eq_mul_div,le_div_iff₀ hu,mul_comm (b i)]
    exact hc
  obtain ⟨hleft,hright⟩ := slope_bounds hp hj
  have hpos := (Real.exp_pos _).trans_le (hbox j hj).1
  have hdom := dominant_population_sign b hn hj hpos hq hq' (fun i hi => hstep (by omega) (by omega) (by
    have he := hleft i hi
    change E (i+1)-E i ≤ s-D at he
    push_cast
    linarith only [he])) (fun i hi h => hstep (by omega) (by omega) (by
    have he := hright i hi h
    change s+D ≤ E (i+1)-E i at he
    push_cast
    linarith only [he]))
  have hdeg : F.natDegree ≤ P.card := natDegree_sum_le_of_forall_le _ _ fun S hS =>
    (natDegree_C_mul_le ..).trans ((natDegree_X_pow_le _).trans (card_le_card (mem_powerset.mp hS)))
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  convert hdom using 2
  apply sum_congr rfl
  intro i _
  change F.coeff i*(-Real.exp (β*s))^i = (-1:ℝ)^i*(F.coeff i*Real.exp (β*s*i))
  have he : (Real.exp (β*s))^i = Real.exp (β*s*i) := by
    rw [←Real.exp_nat_mul]; congr 1; ring
  rw [←neg_one_mul (Real.exp _),mul_pow,he]
  ring


end

end GaloisForLFunctions.SelbergClass.Primon
