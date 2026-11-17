import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.SignedConductorDivisors
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompletePrimeSourceTransfer

/-!
# Smooth prime contacts from integral graph divisors

On a mesh starting at N, the lower graph has real multiplicity
`√i log(1+1/i) fᵢ` and the upper graph has multiplicity `gⱼ/√j`.
At dilation m these numbers are multiplied by m and rounded to integers.
For N = ⌊√m⌋ both the rounding error and the logarithmic quadrature error
vanish after division by m². This gives the full signed prime pairing as a
single limit of differences of logarithms of effective vertical orders.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open LogCells BiarithmeticGaugeGeometry

private def lowerWeight (c : ℕ → ℝ) (i : ℕ) : ℝ := Real.sqrt i * logCellWidth i * c i
private def upperWeight (d : ℕ → ℝ) (j : ℕ) : ℝ := d j / Real.sqrt j

/-- Signed logarithmic degree of the two oriented integral restriction orders. -/
def sampledGraphHeight (m B : ℕ) (R : ℝ) (f g : ℝ → ℝ) : ℝ :=
  let N := m.sqrt
  2 * signedDivisorHeight N (N*B) B
    (fun i => ⌊(m : ℝ) * lowerWeight (logSamples f R N) i⌋)
    (fun j => ⌊(m : ℝ) * upperWeight (logSamples g R N) j⌋)

private theorem spine_weights {A : ℕ} (hA : 0 < A) (X B : ℕ) (c d : ℕ → ℝ) :
    primeCellSpine c d A X B =
      2 * ∑ i ∈ Icc A X, ∑ t ∈ Icc 1 B, lowerWeight c i * upperWeight d (i*t) * Λ t := by
  unfold primeCellSpine cellSpine
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => sum_congr rfl fun t ht => ?_
  have hi' : (0 : ℝ) < i := Nat.cast_pos.mpr (hA.trans_le (mem_Icc.mp hi).1)
  rw [lowerWeight, upperWeight, Nat.cast_mul, Real.sqrt_mul hi'.le]
  field_simp [Real.sqrt_ne_zero'.mpr hi', Real.sqrt_ne_zero'.mpr
    (Nat.cast_pos.mpr (mem_Icc.mp ht).1)]

private theorem lowerWeight_le {i : ℕ} (hi : 0 < i) (c : ℕ → ℝ) :
    |lowerWeight c i| ≤ |c i| := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hs : 1 ≤ Real.sqrt i := Real.one_le_sqrt.mpr hi'
  have hsi : Real.sqrt i ≤ (i : ℝ) := by
    nlinarith only [Real.sq_sqrt (Nat.cast_nonneg i), mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg i)]
  have hfactor : Real.sqrt i * logCellWidth i ≤ 1 := calc
    _ ≤ Real.sqrt i * (1 / (i : ℝ)) :=
      mul_le_mul_of_nonneg_left (logCellWidth_le_inv hi) (Real.sqrt_nonneg _)
    _ ≤ 1 := by rw [mul_one_div, div_le_one (Nat.cast_pos.mpr hi)]; exact hsi
  rw [lowerWeight, abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (logCellWidth_pos hi).le)]
  exact mul_le_of_le_one_left (abs_nonneg _) hfactor

private theorem upperWeight_le {j : ℕ} (hj : 0 < j) (d : ℕ → ℝ) : |upperWeight d j| ≤ |d j| := by
  rw [upperWeight, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_self (abs_nonneg _)
  exact Real.one_le_sqrt.mpr (by exact_mod_cast hj)

/-- Rounding each of two multiplicities loses at most a linear term. -/
private theorem round_product_le (x y s C : ℝ) (hs : 1 ≤ s) (hx : |x| ≤ C) (hy : |y| ≤ C) :
    |(⌊s*x⌋ : ℝ) * (⌊s*y⌋ : ℝ) - s^2 * (x*y)| ≤ s * (2*C+1) := by
  let e := (⌊s*x⌋ : ℝ) - s*x
  let d := (⌊s*y⌋ : ℝ) - s*y
  have err (z : ℝ) : |(⌊z⌋ : ℝ)-z| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [Int.floor_le z, Int.lt_floor_add_one z]
  have he : |e| ≤ 1 := err _
  have hd : |d| ≤ 1 := err _
  have hC := (abs_nonneg x).trans hx
  have hs0 : 0 ≤ s := by linarith
  calc _ = |s*x*d + s*y*e + e*d| := by congr 1; dsimp [e,d]; ring
       _ ≤ (|s*x*d| + |s*y*e|) + |e*d| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
       _ ≤ (s*C + s*C) + 1 := by
         simp only [abs_mul, abs_of_nonneg hs0]
         apply add_le_add _ (mul_le_one₀ he (abs_nonneg _) hd)
         apply add_le_add
         · exact (mul_le_of_le_one_right (mul_nonneg hs0 (abs_nonneg x)) hd).trans
             (mul_le_mul_of_nonneg_left hx hs0)
         · exact (mul_le_of_le_one_right (mul_nonneg hs0 (abs_nonneg y)) he).trans
             (mul_le_mul_of_nonneg_left hy hs0)
       _ ≤ s*(2*C+1) := by linarith only [hs]

private theorem mesh_tendsto : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop.mpr fun b => (eventually_ge_atTop (b*b)).mono fun _ h => Nat.le_sqrt.mpr h

private theorem mesh_div_tendsto :
    Tendsto (fun m : ℕ => (m.sqrt : ℝ) / m) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
    (tendsto_one_div_atTop_nhds_zero_nat.comp mesh_tendsto)
  filter_upwards [eventually_ge_atTop 1] with m hm
  have h : 0 < m.sqrt := Nat.sqrt_pos.mpr hm
  simp only [Function.comp_apply]
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr h), one_mul]
  exact_mod_cast Nat.sqrt_le m

private theorem rounded_height_bound {m B : ℕ} (hm : 0 < m) (R C : ℝ) (f g : ℝ → ℝ)
    (hf : ∀ x, |f x| ≤ C) (hg : ∀ x, |g x| ≤ C) :
    |sampledGraphHeight m B R f g / (m : ℝ)^2 -
      primeCellSpine (logSamples f R m.sqrt) (logSamples g R m.sqrt) m.sqrt (m.sqrt*B) B| ≤
        (m.sqrt : ℝ) / m * (2 * B * (2*C+1) * ∑ t ∈ Icc 1 B, Λ t) := by
  let N := m.sqrt
  let S := Icc N (N*B)
  let T := Icc 1 B
  let x := lowerWeight (logSamples f R N)
  let y := upperWeight (logSamples g R N)
  have hN : 0 < N := Nat.sqrt_pos.mpr hm
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hC := (abs_nonneg (f 0)).trans (hf 0)
  let D := (m : ℝ) * (2*C+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrow (i : ℕ) (hi : i ∈ S) :
      ∀ t ∈ T, |(⌊(m:ℝ)*x i⌋ : ℝ) * (⌊(m:ℝ)*y (i*t)⌋ : ℝ) -
        (m:ℝ)^2*(x i*y (i*t))| ≤ D := by
    have hi' := hN.trans_le (mem_Icc.mp hi).1
    intro t ht
    exact round_product_le _ _ _ _ (by exact_mod_cast hm)
      ((lowerWeight_le hi' _).trans (hf _))
      ((upperWeight_le (Nat.mul_pos hi' (mem_Icc.mp ht).1) _).trans (hg _))
  rw [sampledGraphHeight, signedDivisorHeight_eq hN, spine_weights hN]
  change |2*(∑ i ∈ S, ∑ t ∈ T, (⌊(m:ℝ)*x i⌋ : ℝ)*(⌊(m:ℝ)*y (i*t)⌋ : ℝ)*Λ t)/(m:ℝ)^2 -
    2*(∑ i ∈ S, ∑ t ∈ T, x i*y (i*t)*Λ t)| ≤ _
  rw [div_sub' (pow_ne_zero 2 hm'.ne'), abs_div, abs_of_nonneg (sq_nonneg (m:ℝ)),
    div_le_iff₀ (sq_pos_of_pos hm')]
  rw [show ∀ z : ℝ, (m:ℝ)^2*(2*z) = 2*((m:ℝ)^2*z) by intro; ring, ← mul_sub, abs_mul]
  have hrows : |(∑ i ∈ S, ∑ t ∈ T, (⌊(m:ℝ)*x i⌋ : ℝ)*(⌊(m:ℝ)*y (i*t)⌋ : ℝ)*Λ t) -
      (m:ℝ)^2*(∑ i ∈ S, ∑ t ∈ T, x i*y (i*t)*Λ t)| ≤ S.card * (D * ∑ t ∈ T, Λ t) := by
    simp only [mul_sum, ← sum_sub_distrib]
    calc _ ≤ ∑ i ∈ S, ∑ t ∈ T, |(⌊(m:ℝ)*x i⌋ : ℝ)*(⌊(m:ℝ)*y (i*t)⌋ : ℝ)*Λ t -
             (m:ℝ)^2*(x i*y (i*t)*Λ t)| :=
              (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
         _ ≤ ∑ _i ∈ S, ∑ t ∈ T, D*Λ t := by
           refine sum_le_sum fun i hi => sum_le_sum fun t ht => ?_
           rw [← mul_assoc ((m:ℝ)^2), ← sub_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
           exact mul_le_mul_of_nonneg_right (hrow i hi t ht) ArithmeticFunction.vonMangoldt_nonneg
         _ = _ := by simp [← mul_sum]
  have hcard : (S.card : ℝ) ≤ (N:ℝ)*B := by
    have hh : S.card ≤ N*B := by dsimp [S]; rw [Nat.card_Icc]; omega
    exact_mod_cast hh
  have hsum : 0 ≤ ∑ t ∈ T, Λ t := sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc _ ≤ 2*(S.card * (D * ∑ t ∈ T, Λ t)) := by gcongr
       _ ≤ 2*((N:ℝ)*B * (D * ∑ t ∈ T, Λ t)) := by gcongr
       _ = _ := by dsimp [D,N,T]; field_simp; ring

/-- A single growing integral divisor family recovers the full signed prime
pairing. Both mesh and graph multiplicities vary along the same sequence. -/
theorem exists_tendsto_sampledGraphHeight {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun m : ℕ => sampledGraphHeight m B R f g / (m:ℝ)^2)
        atTop (𝓝 (smoothPrimePair f g)) := by
  obtain ⟨R,hR,B,hB,hs⟩ := exists_tendsto_primeSpine hf hg hfc hgc
  obtain ⟨Cf,hCf⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨Cg,hCg⟩ := hgc.exists_bound_of_continuous hg.continuous
  let C := max Cf Cg
  have h1 (u : ℝ) : |f u| ≤ C := (Real.norm_eq_abs (f u)) ▸ (hCf u).trans (le_max_left _ _)
  have h2 (u : ℝ) : |g u| ≤ C := (Real.norm_eq_abs (g u)) ▸ (hCg u).trans (le_max_right _ _)
  let P := fun n => primeCellSpine (logSamples f R n) (logSamples g R n) n (n*B) B
  let H := fun m : ℕ => sampledGraphHeight m B R f g / (m:ℝ)^2
  have he : Tendsto (fun m => H m - P m.sqrt) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      ((eventually_ge_atTop 1).mono fun m hm => rounded_height_bound hm R C f g h1 h2)
    simpa only [zero_mul] using mesh_div_tendsto.mul_const (2 * (B:ℝ) * (2*C+1) * ∑ t ∈ Icc 1 B, Λ t)
  refine ⟨R,hR,B,hB,?_⟩
  simpa only [Function.comp_def, sub_add_cancel, zero_add, H,P] using he.add (hs.comp mesh_tendsto)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
