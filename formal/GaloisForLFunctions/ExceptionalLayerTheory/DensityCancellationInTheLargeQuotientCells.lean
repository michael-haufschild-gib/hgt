import GaloisForLFunctions.ExceptionalLayerTheory.CenteringTheFactorialPrimeWeight
import GaloisForLFunctions.ExceptionalLayerTheory.TruncatedHarmonicDensityOfDivisorFloors

/-!
# Cancellation of the density in the large quotient cells

The factorial divisor coefficients annihilate the bulk and half-endpoint terms
of the truncated harmonic count. The remaining reciprocal divisor errors have
harmonic cost, allowing the interval discrepancy to grow with the horizon.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def floorForm (R : ℕ) (f : ℕ → ℝ) : ℝ :=
  -stencil R f + momentRatio R*parityFunctional R f -
    ((2/63)*primeWeightMean R)*parityFunctional (128*R^2+1) f

private theorem form_sub (R : ℕ) (f g : ℕ → ℝ) :
    floorForm R (fun k => f k-g k) = floorForm R f-floorForm R g := by
  simp only [floorForm,stencil_sub,parityFunctional]; ring

private theorem weighted_form (R X : ℕ) (S : Finset ℕ) (a : ℕ → ℝ) :
    ∑ m ∈ S, a m*centeredPrimeWeight R (X/m) =
      (∑ m ∈ S, a m)+floorForm R (fun k => ∑ m ∈ S, a m*((X/m/k : ℕ) : ℝ)) := by
  have hw (j : ℕ) : centeredPrimeWeight R j = 1+floorForm R (fun k => ((j/k : ℕ) : ℝ)) := by
    simp only [centeredPrimeWeight,primeWeight,parityCorrection_floors,factorialPrefix,floorForm,parityFunctional]
    ring
  simp only [hw,floorForm,mul_add,mul_one,mul_sub,mul_neg,sum_add_distrib,sum_sub_distrib,
    sum_neg_distrib,mul_left_comm (a _) (momentRatio R),mul_left_comm (a _) ((2/63)*primeWeightMean R),
    ← mul_sum,stencil_weighted_sum,commute_functional]

private def logTest (x c : ℝ) (k : ℕ) : ℝ := (x/k)*(c-Real.log k)

private theorem parity_log {a : ℕ} (ha : 1 ≤ a) (x c : ℝ) :
    parityFunctional a (logTest x c) = 0 := by
  have half (b : ℕ) (hb : 1 ≤ b) :
      -logTest x c b+2*logTest x c (2*b) = -(x/b)*Real.log 2 := by
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
    simp only [logTest,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hb0]
    field_simp [hb0]; ring
  rw [parityFunctional,half _ ha,half _ (by omega)]
  push_cast
  field_simp [show (a : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt ha]; ring

private theorem form_main {R X Z : ℕ} (hR : 1 ≤ R) (hX : 1 ≤ X) (hZ : 1 ≤ Z) :
    floorForm R (floorDensity X Z) = Z-X := by
  let c := Real.log ((X : ℝ)/Z)+Real.eulerMascheroniConstant-1
  have he (k : ℕ) : floorDensity X Z k = logTest X c k - (-(Z : ℝ)/2) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [floorDensity,logTest]; ring
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hz0 : (Z : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hZ
    have hx0 : (X : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hX
    simp only [floorDensity,c,logTest,Real.log_div hx0 hz0,Real.log_div hx0 (mul_ne_zero hk0 hz0),
      Real.log_mul hk0 hz0]
    ring
  have hs (u : ℝ) : stencil R (fun _ => u/2) = u*stencil R (fun _ => 1/2) := by
    simpa only [sum_singleton,mul_one_div] using (stencil_weighted_sum R ({0} : Finset ℕ)
      (fun _ => u) (fun _ _ => 1/2)).symm
  rw [funext he,form_sub]
  unfold floorForm
  rw [show stencil R (logTest X c) = X from stencil_log_quotient hR X c,
    parity_log hR,parity_log (show 1 ≤ 128*R^2+1 by omega),hs (-(Z : ℝ))]
  simp only [parityFunctional,primeWeightMean]
  ring

private theorem form_two_errors :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℕ}, 1 ≤ R → ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → ∀ f : ℕ → ℝ,
      (∀ d ∈ Icc 1 (128*(128*R^2+1)), |f d| ≤ u*d+v/d) →
      |floorForm R f| ≤ C*((R : ℝ)^3*u+(1+Real.log R)*v) := by
  obtain ⟨C,hC,hst⟩ := stencil_two_errors
  obtain ⟨K,hK,hM⟩ := mass_uniform
  let F := 3*(1+K)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨C+195*16512*F,by linarith only [hC,hF],?_⟩
  intro R hR u v hu hv f hf
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hr0 : (0 : ℝ) < R := zero_lt_one.trans_le hr
  have hr₂ : 1 ≤ (R : ℝ)^2 := one_le_pow₀ hr
  have hR₂ : R ≤ R^2 := by simpa only [sq,Nat.mul_one] using Nat.mul_le_mul_left R hR
  let A := 128*R^2+1
  have hA : R ≤ A := by dsimp [A]; omega
  have hmax : (128*A : ℕ) ≤ 16512*(R : ℝ)^2 := by dsimp [A]; push_cast; linarith only [hr₂]
  let M := u*(16512*(R : ℝ)^2)+v/R
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have large {a : ℕ} (ha : R ≤ a) (ha' : a ≤ A) : |parityFunctional a f| ≤ 195*M := by
    apply parityFunctional_bound
    intro d hd
    obtain ⟨hl,hh⟩ := mem_Icc.mp hd
    have hd' : d ≤ 128*A := by omega
    apply (hf d (mem_Icc.mpr ⟨hR.trans (ha.trans hl),hd'⟩)).trans
    exact add_le_add (mul_le_mul_of_nonneg_left ((by exact_mod_cast hd' : (d : ℝ) ≤ (128*A : ℕ)).trans hmax) hu)
      (div_le_div_of_nonneg_left hv hr0 (by exact_mod_cast ha.trans hl))
  have hs := hst hR hu hv f (fun d hd => hf d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,
    by have := (mem_Icc.mp hd).2; change d ≤ 128*A; omega⟩))
  have hcoeff : |momentRatio R|+|(2/63)*primeWeightMean R| ≤ F*R := by
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/63)]
    dsimp [F]
    linarith only [ratio_bound hR,mean_bound hR,hM R hR,hr,mul_nonneg hK hr0.le]
  have h₂ := mul_le_mul_of_nonneg_left (large le_rfl hA) (abs_nonneg (momentRatio R))
  have h₃ := mul_le_mul_of_nonneg_left (large hA le_rfl) (abs_nonneg ((2/63)*primeWeightMean R))
  have hc := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ 195*M by positivity)
  have hscale : F*R*(195*M) = 195*F*(16512*((R : ℝ)^3*u)+v) := by dsimp [M]; field_simp
  rw [hscale] at hc
  have hr₃ : (R : ℝ)^2 ≤ (R : ℝ)^3 := by rw [pow_succ _ 2]; exact le_mul_of_one_le_right (sq_nonneg _) hr
  have hp := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr₃ hu) (zero_le_one.trans hC)
  have hl := mul_nonneg (Real.log_natCast_nonneg R) hv
  unfold floorForm
  apply (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [abs_neg,abs_mul,abs_mul]
  change _+_+|(2/63)*primeWeightMean R| * |parityFunctional A f| ≤ _
  linarith only [hs,h₂,h₃,hc,hp,mul_nonneg hF hl,mul_nonneg hF hv]

/-- Uniform evaluation of the entire truncated density. The three bulk
terms cancel: the divisor harmonic moment, log slope and endpoint term. -/
theorem abs_truncated_density :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y R : ℕ, 1 ≤ X → Y ≤ X → 1 ≤ R → ∀ (a : ℕ → ℝ) (B : ℝ), 0 ≤ B →
      (∀ L U : ℕ, L ≤ U → |(∑ m ∈ Ioc L U, a m)-((U : ℝ)-L)| ≤ B) →
      let Z := Y+1
      |∑ m ∈ Ioc Y X, a m*centeredPrimeWeight R (X/m)| ≤
        B+1+C*((R : ℝ)^3*(4*(Z : ℝ)^2/X)+(1+Real.log R)*((B+2)*X/Z)) := by
  obtain ⟨C,hC,h⟩ := form_two_errors
  refine ⟨C,hC,fun X Y R hX hY hR a B hB ha => ?_⟩
  intro Z
  let floors (d : ℕ) := ∑ m ∈ Ioc Y X, a m*((X/m/d : ℕ) : ℝ)
  let u := 4*(Z : ℝ)^2/X
  let v := (B+2)*(X : ℝ)/Z
  have he := h hR (u := u) (v := v) (by dsimp [u]; positivity) (by dsimp [v]; positivity)
    (fun d => floors d-floorDensity X Z d) (fun d hd => by
      apply (truncated_floor_density hX (mem_Icc.mp hd).1 a hB ha).trans_eq
      dsimp [u,v]; simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  rw [form_sub,form_main hR hX (show 1 ≤ Z by dsimp [Z]; omega)] at he
  rw [weighted_form]
  have hconst := abs_le.mp (ha Y X hY)
  have hf := abs_le.mp he
  change |(∑ m ∈ Ioc Y X, a m)+floorForm R floors| ≤ B+1+C*((R : ℝ)^3*u+(1+Real.log R)*v)
  have hz : (Z : ℝ) = (Y : ℝ)+1 := by simp [Z]
  rw [abs_le]
  constructor <;> linarith only [hconst.1,hconst.2,hf.1,hf.2,hz]

/-- Pairing on the large-prime interval, extended through X where the
centered weight already vanishes. -/
def highPair (X : ℕ) (a : ℕ → ℝ) : ℝ :=
  let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
  let Y := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
  ∑ m ∈ Ioc Y X, a m*centeredPrimeWeight R (X/m)

/-- Discrepancies up to a fixed multiple of X to the power 1/200000
are absorbed at square-root precision at each horizon. -/
theorem high_density_bound (D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X → ∀ a : ℕ → ℝ,
      (∀ L U : ℕ, L ≤ U → |(∑ m ∈ Ioc L U, a m)-((U : ℝ)-L)| ≤ D*(X : ℝ)^(1/200000 : ℝ)) →
      |highPair X a| ≤ K*Real.sqrt X := by
  obtain ⟨C,hC,h⟩ := abs_truncated_density
  refine ⟨D+1+C*(16+200001*(D+2)),by positivity,?_⟩
  intro X hX a ha
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  let P := fun t : ℝ => (X : ℝ)^t
  let R := ⌊P (1/100000)⌋₊
  let Y := ⌊P (50001/100000)⌋₊
  let Z := ((Y+1 : ℕ) : ℝ)
  let B := D*P (1/200000)
  have pos (t : ℝ) : 0 < P t := Real.rpow_pos_of_pos hx0 _
  have mono {s t : ℝ} (hst : s ≤ t) : P s ≤ P t := Real.rpow_le_rpow_of_exponent_le hx hst
  have add (s t : ℝ) : P s*P t = P (s+t) := (Real.rpow_add hx0 _ _).symm
  have one : P 1 = X := Real.rpow_one _
  have half : P (1/2) = Real.sqrt X := (Real.sqrt_eq_rpow _).symm
  have lo (t : ℝ) (ht : 0 ≤ t) : 1 ≤ P t := Real.one_le_rpow hx ht
  have hr := (Nat.one_le_floor_iff _).mpr (lo (1/100000) (by norm_num))
  have hR : (R : ℝ) ≤ P (1/100000) := Nat.floor_le (pos _).le
  have hY : Y ≤ X := Nat.floor_le_of_le ((mono (by norm_num : (50001/100000 : ℝ) ≤ 1)).trans_eq one)
  have zlo : P (50001/100000) ≤ Z := by simpa only [Z,Y,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (P (50001/100000))).le
  have zhi : Z ≤ 2*P (50001/100000) := by
    have hy : (Y : ℝ) ≤ P (50001/100000) := Nat.floor_le (pos _).le
    simp only [Z,Nat.cast_add,Nat.cast_one]
    linarith only [hy,lo (50001/100000) (by norm_num)]
  have root : 1 ≤ Real.sqrt X := (lo (1/2) (by norm_num)).trans_eq half
  have small : P (1/200000) ≤ Real.sqrt X := (mono (by norm_num : (1/200000 : ℝ) ≤ 1/2)).trans_eq half
  have hb : B+1 ≤ (D+1)*Real.sqrt X := by
    dsimp [B]; linarith only [mul_le_mul_of_nonneg_left small hD,root]
  have hbulk : (R : ℝ)^3*(4*Z^2/X) ≤ 16*Real.sqrt X := by
    have hr3 := pow_le_pow_left₀ (Nat.cast_nonneg R) hR 3
    have hz2 := pow_le_pow_left₀ (show 0 ≤ Z by dsimp [Z]; positivity) zhi 2
    have hh := mul_le_mul hr3 hz2 (sq_nonneg Z) (pow_nonneg (pos _).le 3)
    have hpow : P (1/100000)^3 * (2*P (50001/100000))^2 = 4*P (100005/100000) := by
      rw [mul_pow,show P (1/100000)^3 = P (3/100000) by
        dsimp [P]; rw [← Real.rpow_natCast _ 3,← Real.rpow_mul hx0.le]; norm_num,
        show P (50001/100000)^2 = P (100002/100000) by
          dsimp [P]; rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hx0.le]; norm_num]
      rw [mul_left_comm,add]; norm_num
    rw [hpow] at hh
    have hxpow : P (1/2)*X = P (3/2) := by rw [←one,add]; norm_num
    rw [←half,show (R : ℝ)^3*(4*Z^2/X) = 4*((R : ℝ)^3*Z^2)/X by ring,div_le_iff₀ hx0]
    linarith only [hh,mono (by norm_num : (100005/100000 : ℝ) ≤ 3/2),hxpow]
  have hlog : 1+Real.log R ≤ 200001*P (1/200000) := by
    have hRX := hR.trans ((mono (by norm_num : (1/100000 : ℝ) ≤ 1)).trans_eq one)
    have h₁ := Real.log_le_log (by exact_mod_cast hr : (0 : ℝ) < R) hRX
    have h₂ := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1/200000)
    change Real.log X ≤ P (1/200000)/(1/200000 : ℝ) at h₂
    linarith only [h₁,h₂,lo (1/200000) (by norm_num)]
  have hv : (B+2)*X/Z ≤ (D+2)*P (99999/200000) := by
    have h₁ : B+2 ≤ (D+2)*P (1/200000) := by
      dsimp [B]; linarith only [lo (1/200000) (by norm_num)]
    rw [div_le_iff₀ ((pos _).trans_le zlo)]
    apply (mul_le_mul_of_nonneg_right h₁ hx0.le).trans
    apply le_trans _ (mul_le_mul_of_nonneg_left zlo (mul_nonneg (by linarith) (pos _).le))
    rw [mul_assoc,mul_assoc,←one,add,add]; norm_num
  have htail := mul_le_mul hlog hv (show 0 ≤ (B+2)*X/Z by dsimp [B,Z,P]; positivity)
    (show 0 ≤ 200001*P (1/200000) from mul_nonneg (by norm_num) (pos _).le)
  have he : 200001*P (1/200000)*((D+2)*P (99999/200000)) = 200001*(D+2)*Real.sqrt X := by
    rw [show 200001*P (1/200000)*((D+2)*P (99999/200000)) =
      200001*(D+2)*(P (1/200000)*P (99999/200000)) by ring,add,←half]; norm_num
  rw [he] at htail
  have hmain := h X Y R hX hY hr a B (mul_nonneg hD (pos _).le) ha
  apply hmain.trans
  change B+1+C*(_+_) ≤ _
  linarith only [hb,mul_le_mul_of_nonneg_left (add_le_add hbulk htail) hC]

#print axioms high_density_bound

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
