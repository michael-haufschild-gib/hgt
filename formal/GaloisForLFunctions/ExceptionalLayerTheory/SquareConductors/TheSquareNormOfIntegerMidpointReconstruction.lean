import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheExactIntegerSamplesOfTheMidpointInverse
import GaloisForLFunctions.HTGeometry.CentralBinomialWallisAsymptotic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Euclidean error amplification by integer midpoint reconstruction

At depth b the boundary and forcing terms occupy (b+2 choose 2) distinct
measurement coordinates. The squared norm of reconstruction is
(1+b/2)·C(2b,b)/4^b. Thus independent squared errors amplify in norm
on the scale of the fourth root of the ternary depth.
-/

noncomputable section
open Finset Filter GaloisForLFunctions.HTGeometry
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- A boundary column or a pair consisting of a forcing layer and column. -/
abbrev MidpointReadIndex := ℕ ⊕ (Σ _ : ℕ, ℕ)

def midpointReadIndices (b : ℕ) : Finset MidpointReadIndex :=
  (range (b+1)).disjSum ((range b).sigma fun c => range (b-1-c+1))

/-- The two tags distinguish seed and observation at the same integer. -/
def midpointMeasurement (b m : ℕ) : MidpointReadIndex → ℕ ⊕ ℕ
  | .inl j => .inl (2^(b+j)*m)
  | .inr ⟨c,j⟩ => .inr ((3^c*2^(b-1-c+j))*m)

private def measurementColumn (b m : ℕ) : ℕ ⊕ ℕ → MidpointReadIndex
  | .inl z => .inl ((z/m).factorization 2-b)
  | .inr z =>
    let c := (z/m).factorization 3
    .inr ⟨c,(z/m).factorization 2-(b-1-c)⟩

/-- The 3-adic order identifies the layer and the 2-adic order the column
after removing the common base m. -/
private theorem measurement_left_inverse (b : ℕ) {m : ℕ} (hm : 0 < m) :
    Function.LeftInverse (measurementColumn b m) (midpointMeasurement b m) := by
  have h₃ (c r : ℕ) : (3^c*2^r).factorization 3=c := by
    rw [Nat.factorization_mul (by positivity) (by positivity),Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_three,Nat.prime_two.factorization_pow]
    simp
  have h₂ (c r : ℕ) : (3^c*2^r).factorization 2=r := by
    rw [Nat.factorization_mul (by positivity) (by positivity),Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,Nat.prime_three.factorization_pow]
    simp
  rintro (j | ⟨c,j⟩)
  · simp only [midpointMeasurement,measurementColumn,Nat.mul_div_cancel _ hm,
      Nat.factorization_pow_self Nat.prime_two,Nat.add_sub_cancel_left]
  · simp only [midpointMeasurement,measurementColumn,Nat.mul_div_cancel _ hm,h₃,h₂,Nat.add_sub_cancel_left]

/-- Exact number of different tagged integer measurements. -/
theorem count_midpoint_measurements (b : ℕ) {m : ℕ} (hm : 0 < m) :
    ((midpointReadIndices b).image (midpointMeasurement b m)).card=(b+2).choose 2 := by
  rw [card_image_of_injective _ (measurement_left_inverse b hm).injective,midpointReadIndices,
    card_disjSum,card_sigma,card_range]
  simp only [card_range]
  rw [sum_range_reflect (fun i => i+1) b]
  have h (n : ℕ) : ∑ j ∈ range n, (j+1)=(n+1).choose 2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih,Nat.choose_succ_succ (n+1) 1,Nat.choose_one_right,Nat.add_comm]
  rw [h,Nat.choose_succ_succ (b+1) 1,Nat.choose_one_right]

private def rowWeight (r j : ℕ) : ℝ := (1/2:ℝ)^r*(r.choose j:ℝ)

def midpointReadWeight (b : ℕ) : MidpointReadIndex → ℝ
  | .inl j => rowWeight b j
  | .inr ⟨c,j⟩ => rowWeight (b-1-c) j/2

private theorem reconstruction_pairing (seed data : ℕ → ℝ) (b m : ℕ) :
    ternaryMidpointRow seed data b m=
      ∑ i ∈ midpointReadIndices b, midpointReadWeight b i*Sum.elim seed data (midpointMeasurement b m i) := by
  rw [ternary_binomial_green,midpointReadIndices,sum_disjSum,sum_sigma]
  congr 1
  · simp only [dyadicMidpointAverage,mul_sum,midpointReadWeight,rowWeight,midpointMeasurement,Sum.elim_inl,mul_assoc]
  · rw [Finset.sum_div]
    apply sum_congr rfl
    intro c _
    simp only [dyadicMidpointAverage,mul_sum,Finset.sum_div,midpointReadWeight,rowWeight,midpointMeasurement,
      Sum.elim_inr,Nat.mul_assoc]
    exact sum_congr rfl fun j _ => by ring

private theorem row_weight_energy (n : ℕ) :
    ∑ j ∈ range (n+1), (rowWeight n j)^2=normalizedCentralBinom n := by
  have hv : ∑ j ∈ range (n+1), (n.choose j:ℝ)^2=(Nat.centralBinom n:ℝ) := by
    exact_mod_cast Nat.sum_range_choose_sq n
  have hpow : ((1/2:ℝ)^n)^2=(1/(4:ℝ))^n := by
    rw [←pow_mul,mul_comm n 2,pow_mul]
    norm_num
  simp only [rowWeight,mul_pow]
  rw [←mul_sum,hv,hpow,normalizedCentralBinom,one_div,inv_pow,div_eq_mul_inv,mul_comm]

private theorem central_step (n : ℕ) :
    2*((n:ℝ)+1)*normalizedCentralBinom (n+1)=(2*(n:ℝ)+1)*normalizedCentralBinom n := by
  have h : ((n:ℝ)+1)*(Nat.centralBinom (n+1):ℝ)=2*(2*(n:ℝ)+1)*(Nat.centralBinom n:ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have he := congrArg (fun y : ℝ => y*((1/2:ℝ)/(4:ℝ)^n)) h
  dsimp only at he
  simp only [normalizedCentralBinom,pow_succ,div_eq_mul_inv,mul_inv_rev]
  linarith only [he]

private theorem sum_normalized_central (b : ℕ) :
    ∑ j ∈ range b, normalizedCentralBinom j=2*(b:ℝ)*normalizedCentralBinom b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ,ih,Nat.cast_succ,central_step]
    ring

/-- Boundary and forcing coordinates contribute, respectively, a single
central binomial mass and one quarter of the sum of all previous masses. -/
theorem midpoint_weight_energy (b : ℕ) :
    ∑ i ∈ midpointReadIndices b, (midpointReadWeight b i)^2=(1+(b:ℝ)/2)*normalizedCentralBinom b := by
  rw [midpointReadIndices,sum_disjSum,sum_sigma]
  simp only [midpointReadWeight,div_pow,←Finset.sum_div,row_weight_energy]
  rw [sum_range_reflect normalizedCentralBinom,sum_normalized_central]
  ring

def midpointMeasurementEnergy (seed data : ℕ → ℝ) (b m : ℕ) : ℝ :=
  ∑ i ∈ midpointReadIndices b, (Sum.elim seed data (midpointMeasurement b m i))^2

/-- Least squared gain on actual integer measurements. Weights themselves
can be prescribed as data because each measured coordinate has a unique
column. This realizes equality in Cauchy-Schwarz. -/
theorem sharp_midpoint_energy_gain (b : ℕ) {m : ℕ} (hm : 0 < m) :
    IsLeast {C : ℝ | ∀ seed data : ℕ → ℝ,
      (ternaryMidpointRow seed data b m)^2 ≤ C*midpointMeasurementEnergy seed data b m}
      ((1+(b:ℝ)/2)*normalizedCentralBinom b) := by
  let W := (1+(b:ℝ)/2)*normalizedCentralBinom b
  have hw : 0<W := mul_pos (by positivity) (div_pos (Nat.cast_pos.mpr (Nat.centralBinom_pos b)) (by positivity))
  constructor
  · intro seed data
    rw [reconstruction_pairing,←midpoint_weight_energy]
    exact sum_mul_sq_le_sq_mul_sq _ _ _
  · intro C hC
    let f := fun z => midpointReadWeight b (measurementColumn b m z)
    let seed := fun n => f (.inl n)
    let data := fun n => f (.inr n)
    have read (i : MidpointReadIndex) :
        Sum.elim seed data (midpointMeasurement b m i)=midpointReadWeight b i := by
      have hs : Sum.elim seed data=f := funext fun z => by cases z <;> rfl
      rw [hs]
      exact congrArg (midpointReadWeight b) (measurement_left_inverse b hm i)
    have hv := hC seed data
    simp only [reconstruction_pairing,midpointMeasurementEnergy,read,←sq,midpoint_weight_energy] at hv
    exact (le_of_mul_le_mul_right (by simpa only [sq] using hv : W*W≤C*W) hw)

/-- The norm divided by the fourth root of depth tends to the exact
Wallis constant. -/
theorem midpoint_euclidean_gain_asymptotic :
    Tendsto (fun b : ℕ => Real.sqrt (∑ i ∈ midpointReadIndices b, (midpointReadWeight b i)^2)/
      Real.sqrt (Real.sqrt b)) atTop (𝓝 (Real.sqrt (1/(2*Real.sqrt Real.pi)))) := by
  have hinv : Tendsto (fun b : ℕ => (1:ℝ)/b) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hl := tendsto_sqrtNat_mul_normalizedCentralBinom.mul (hinv.add_const (1/2:ℝ))
  have hs : Tendsto (fun b : ℕ => ((1+(b:ℝ)/2)*normalizedCentralBinom b)/Real.sqrt b)
      atTop (𝓝 (1/(2*Real.sqrt Real.pi))) := by
    rw [←show (1/Real.sqrt Real.pi)*(0+(1/2:ℝ))=1/(2*Real.sqrt Real.pi) by
      simp only [div_eq_mul_inv,mul_inv_rev]; ring]
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with b hb
    have hb' : 0<(b:ℝ) := Nat.cast_pos.mpr hb
    have hroot := Real.sqrt_pos.mpr hb'
    change (Real.sqrt b*normalizedCentralBinom b)*(1/(b:ℝ)+1/2)=_
    apply (eq_div_iff hroot.ne').mpr
    calc _ = (Real.sqrt b)^2*(1/(b:ℝ)+1/2)*normalizedCentralBinom b := by ring
         _ = _ := by rw [Real.sq_sqrt hb'.le]; field_simp [hb'.ne'] <;> ring
  have hn (b : ℕ) : 0≤(1+(b:ℝ)/2)*normalizedCentralBinom b :=
    mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg _) (by positivity))
  simpa only [Function.comp_apply,midpoint_weight_energy,Real.sqrt_div (hn _)] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hs

#print axioms count_midpoint_measurements
#print axioms sharp_midpoint_energy_gain
#print axioms midpoint_euclidean_gain_asymptotic

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
