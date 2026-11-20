import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTernaryBoundaryDataOfThePrimeMidpoint
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Power-weighted stability of the integer prime midpoint inverse

At each ternary layer the normalized boundary data acquire the factor
((2/3)^s+(4/3)^s)/2. Power-shaped errors realize the full geometric
sum of forcing errors. Uniform stability holds exactly between the two
resonances s = 0 and s = 1.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Gain of one ternary layer when the price unit is n^s. -/
def ternaryPowerGain (s : ℝ) := ((2/3:ℝ)^s+(4/3:ℝ)^s)/2

theorem ternary_gain_balance (s : ℝ) :
    2*(3:ℝ)^s*ternaryPowerGain s=(2:ℝ)^s+(4:ℝ)^s := by
  unfold ternaryPowerGain
  rw [Real.div_rpow (by norm_num) (by norm_num),Real.div_rpow (by norm_num) (by norm_num)]
  field_simp [(Real.rpow_pos_of_pos (by norm_num : 0<(3:ℝ)) s).ne']

theorem ternary_gain_pos (s : ℝ) : 0<ternaryPowerGain s := by unfold ternaryPowerGain; positivity

/-- Both endpoint gains are one. Strict concavity gives contraction in
the open unit interval. Negative exponents expand by the geometric mean. -/
theorem ternary_gain_phase (s : ℝ) :
    (ternaryPowerGain s<1 ↔ s ∈ Set.Ioo (0:ℝ) 1) ∧
    (ternaryPowerGain s=1 ↔ s=0 ∨ s=1) := by
  have h₀ : ternaryPowerGain 0=1 := by norm_num [ternaryPowerGain]
  have h₁ : ternaryPowerGain 1=1 := by norm_num [ternaryPowerGain]
  have middle (hp : 0<s) (hl : s<1) : ternaryPowerGain s<1 := by
    have h := (Real.strictConcaveOn_rpow hp hl).2
      (show (2/3:ℝ) ∈ Set.Ici 0 by norm_num) (show (4/3:ℝ) ∈ Set.Ici 0 by norm_num)
      (by norm_num : (2/3:ℝ)≠4/3) (by norm_num : 0<(1/2:ℝ)) (by norm_num : 0<(1/2:ℝ)) (by norm_num)
    simp only [smul_eq_mul,show (1/2:ℝ)*(2/3)+(1/2)*(4/3)=1 by norm_num,Real.one_rpow] at h
    unfold ternaryPowerGain
    linarith only [h]
  have large (hl : 1<s) : 1<ternaryPowerGain s := by
    have h := (strictConvexOn_rpow hl).2
      (show (2/3:ℝ) ∈ Set.Ici 0 by norm_num) (show (4/3:ℝ) ∈ Set.Ici 0 by norm_num)
      (by norm_num : (2/3:ℝ)≠4/3) (by norm_num : 0<(1/2:ℝ)) (by norm_num : 0<(1/2:ℝ)) (by norm_num)
    simp only [smul_eq_mul,show (1/2:ℝ)*(2/3)+(1/2)*(4/3)=1 by norm_num,Real.one_rpow] at h
    unfold ternaryPowerGain
    linarith only [h]
  have neg (hl : s<0) : 1<ternaryPowerGain s := by
    let a := (2/3:ℝ)^s
    let b := (4/3:ℝ)^s
    have hh : 1<a*b := by
      dsimp only [a,b]
      rw [←Real.mul_rpow (by norm_num) (by norm_num)]
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) hl
    change 1<(a+b)/2
    by_contra! hn
    have hsum : 0≤a+b := by dsimp only [a,b]; positivity
    have hsq := mul_nonneg (show 0≤2-(a+b) by linarith only [hn]) (show 0≤2+(a+b) by linarith only [hsum])
    nlinarith only [hh,hsq,sq_nonneg (a-b)]
  rcases lt_trichotomy s 0 with hn | rfl | hp
  · simp [Set.mem_Ioo,hn.not_gt,(neg hn).not_gt,(neg hn).ne',hn.ne,show s≠1 by linarith only [hn]]
  · simp [h₀]
  rcases lt_trichotomy s 1 with hl | rfl | hl
  · simp [Set.mem_Ioo,hp,hl,middle hp hl,(middle hp hl).ne,hp.ne',hl.ne]
  · simp [h₁]
  · simp [Set.mem_Ioo,hl.not_gt,(large hl).not_gt,(large hl).ne',hp.ne',hl.ne']

/-- Exact response to power-shaped boundary and forcing errors, normalized
by the price scale at the point of evaluation. -/
def layerPowerResponse (s C A : ℝ) (b : ℕ) :=
  C*(ternaryPowerGain s)^b+A/(2*(3:ℝ)^s)*∑ j ∈ range b, (ternaryPowerGain s)^j

private theorem response_succ (s C A : ℝ) (b : ℕ) :
    layerPowerResponse s C A (b+1)=
      ternaryPowerGain s*layerPowerResponse s C A b+A/(2*(3:ℝ)^s) := by
  simp only [layerPowerResponse,sum_range_succ' (f:=fun j => ternaryPowerGain s^j),
    pow_succ,pow_zero,←sum_mul]
  ring

private theorem scale_power (s : ℝ) (a b : ℕ) :
    ((a*b:ℕ):ℝ)^s=(a:ℝ)^s*(b:ℝ)^s := by rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- Exact signed row, including the resonant endpoint powers. The data
are evaluated on all integers, including those already divisible by 3. -/
theorem ternary_power_response (s C A : ℝ) (b m : ℕ) :
    ternaryMidpointRow (fun j => C*(j:ℝ)^s) (fun j => A*(j:ℝ)^s) b m =
      ((3^b*m:ℕ):ℝ)^s*layerPowerResponse s C A b := by
  induction b generalizing m with
  | zero => simp [ternaryMidpointRow,layerPowerResponse,mul_comm]
  | succ b ih =>
    rw [ternaryMidpointRow_succ_apply,ih,ih,response_succ,pow_succ]
    rw [show 3^b*(2*m)=2*(3^b*m) by ac_rfl,show 3^b*(4*m)=4*(3^b*m) by ac_rfl,
      show 3^b*3*m=3*(3^b*m) by ac_rfl,scale_power s 2,scale_power s 4,scale_power s 3]
    norm_num only [Nat.cast_ofNat]
    let X := ((3^b*m:ℕ):ℝ)^s
    let R := layerPowerResponse s C A b
    change ((2:ℝ)^s*X*R+(4:ℝ)^s*X*R+A*X)/2 =
      (3:ℝ)^s*X*(ternaryPowerGain s*R+A/(2*(3:ℝ)^s))
    have he := congrArg (fun z : ℝ => z*X*R) (ternary_gain_balance s)
    have hpaid : (3:ℝ)^s*(A/(2*(3:ℝ)^s))=A/2 := by field_simp [(Real.rpow_pos_of_pos (by norm_num : 0<(3:ℝ)) s).ne']
    linarith only [he,congrArg (X*·) hpaid]

/-- Arbitrary signed inputs obey the power response attained by the
positive power data. Thus the gain is a sharp bound, even with full
freedom of signs between distinct indices and ternary layers. -/
theorem sharp_power_midpoint_inverse (s C A : ℝ) (n : ℕ) :
    (∀ seed data : ℕ → ℝ, (∀ j, |seed j|≤C*(j:ℝ)^s) → (∀ j, |data j|≤A*(j:ℝ)^s) →
      |integerMidpointInverse seed data n|≤(n:ℝ)^s*layerPowerResponse s C A (n.factorization 3)) ∧
    integerMidpointInverse (fun j => C*(j:ℝ)^s) (fun j => A*(j:ℝ)^s) n =
      (n:ℝ)^s*layerPowerResponse s C A (n.factorization 3) := by
  constructor
  · intro seed data hs hd
    have hb (b m : ℕ) : |ternaryMidpointRow seed data b m| ≤
        ternaryMidpointRow (fun j => C*(j:ℝ)^s) (fun j => A*(j:ℝ)^s) b m := by
      induction b generalizing m with
      | zero => exact hs m
      | succ b ih =>
        simp only [ternaryMidpointRow,abs_div,abs_of_pos (by norm_num : 0<(2:ℝ))]
        exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (ih _) (ih _))) (hd _))) (by norm_num)
    simpa only [integerMidpointInverse,ternary_power_response,Nat.ordProj_mul_ordCompl_eq_self] using
      hb (n.factorization 3) (ordCompl[3] n)
  · rw [integerMidpointInverse,ternary_power_response,Nat.ordProj_mul_ordCompl_eq_self]

/-- With zero boundary data and unit power forcing the normalized response
stays bounded through all layers precisely for exponents strictly between
zero and one. The sharp limiting constant is the reciprocal Mellin gap. -/
theorem stable_ternary_power_forcing (s : ℝ) :
    (∃ B : ℝ, ∀ b, layerPowerResponse s 0 1 b≤B) ↔ s ∈ Set.Ioo (0:ℝ) 1 := by
  rw [←(ternary_gain_phase s).1]
  let d := 1/(2*(3:ℝ)^s)
  have hd : 0<d := by dsimp only [d]; positivity
  have he (b : ℕ) : layerPowerResponse s 0 1 b=d*∑ j ∈ range b,ternaryPowerGain s^j := by
    simp [layerPowerResponse,d]
  constructor
  · rintro ⟨B,hB⟩
    by_contra! hg
    obtain ⟨n,hn⟩ := exists_nat_gt (B/d)
    have hsum : (n:ℝ) ≤ ∑ j ∈ range n, ternaryPowerGain s^j := by
      simpa only [sum_const,card_range,nsmul_eq_mul,mul_one] using
        (sum_le_sum (s:=range n) (fun j _ => one_le_pow₀ hg (n:=j)))
    have hb := hB n
    rw [he] at hb
    linarith only [(div_lt_iff₀ hd).mp hn,mul_le_mul_of_nonneg_left hsum hd.le,hb]
  · intro hg
    have h := hasSum_geometric_of_lt_one (ternary_gain_pos s).le hg
    refine ⟨d*(1-ternaryPowerGain s)⁻¹,fun b => ?_⟩
    rw [he]
    exact mul_le_mul_of_nonneg_left (sum_le_hasSum (range b) (fun i _ => pow_nonneg (ternary_gain_pos s).le i) h) hd.le

theorem stable_ternary_response_limit {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    Tendsto (layerPowerResponse s 0 1) atTop (𝓝 (1/(2*(3:ℝ)^s-(2:ℝ)^s-(4:ℝ)^s))) := by
  have hg := (ternary_gain_phase s).1.mpr hs
  have ht := ((hasSum_geometric_of_lt_one (ternary_gain_pos s).le hg).tendsto_sum_nat).const_mul
    (1/(2*(3:ℝ)^s))
  have he : 2*(3:ℝ)^s-(2:ℝ)^s-(4:ℝ)^s=2*(3:ℝ)^s*(1-ternaryPowerGain s) := by
    linarith only [ternary_gain_balance s]
  have hf : layerPowerResponse s 0 1=fun b => (1/(2*(3:ℝ)^s))*∑ j ∈ range b, ternaryPowerGain s^j := by
    funext b
    simp only [layerPowerResponse,zero_mul,zero_add]
  rw [hf]
  simpa only [he,one_div,mul_inv_rev,mul_comm] using ht

#print axioms ternary_gain_phase
#print axioms sharp_power_midpoint_inverse
#print axioms stable_ternary_power_forcing
#print axioms stable_ternary_response_limit

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
