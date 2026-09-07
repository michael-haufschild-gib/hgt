import GaloisForLFunctions.RHTower.EulerDeletionFluxWeightReplacement

/-!
# Uniform bound for the complete reduced-denominator flux head

The complementary divisor rectangle has coordinates `d = r*a > N` and
`e = r*b ≤ N`, with coprime `a,b`. Restricting only the reduced denominator
`b ≤ B` leaves both the numerator and time series infinite. The complete
kernel is bounded by `e/(4*d²)`. Summing the numerator tail first costs
`b/(2*N)` for each common factor `r`; the admissible common factors then
cost at most `1/2` for each reduced denominator. The resulting head is
bounded by `B/2` uniformly in the physical cutoff, with actual Möbius
coefficients and coprimality masks retained.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower.DeletionFlux

/-- Complete time kernel of two literal modular divisor channels. -/
def completeKernel (d e : ℕ) : ℝ :=
  ∑' j : ℕ, HTGeometry.centeredModularPrimitive e (d*(j+1)) /
    ((d*(j+1) : ℕ) : ℝ)^2

private theorem reciprocal_bound {q : ℕ} (hq : 0 < q) {C : ℝ}
    (hC : 0 ≤ C) (f : ℕ → ℝ)
    (h : ∀ j, |f j| ≤ C / (((q : ℝ)+j)*((q : ℝ)+j+1))) :
    Summable f ∧ |∑' j, f j| ≤ C/q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb (T : ℕ) : ∑ j ∈ range T, |f j| ≤ C/q := by
    calc _ ≤ ∑ j ∈ range T, C / (((q : ℝ)+j)*((q : ℝ)+j+1)) :=
           sum_le_sum (fun j _ => h j)
         _ = C/q - C/((q : ℝ)+T) := by
           calc _ = ∑ j ∈ range T, (C/((q : ℝ)+j)-C/((q : ℝ)+(j+1 : ℕ))) := by
                  apply sum_congr rfl
                  intro j hj
                  push_cast
                  field_simp
                  ring
                _ = _ := by
                  simpa using sum_range_sub' (fun j : ℕ => C/((q : ℝ)+j)) T
         _ ≤ _ := sub_le_self _ (by positivity)
  have ha : Summable (fun j => |f j|) := summable_of_sum_range_le (fun _ => abs_nonneg _) hb
  refine ⟨summable_abs_iff.mp ha, ?_⟩
  have hlim : (∑' j, |f j|) ≤ C/q :=
    le_of_tendsto ha.hasSum.tendsto_sum_nat (Eventually.of_forall hb)
  have hn := norm_tsum_le_tsum_norm (show Summable (fun j => ‖f j‖) by
    simpa only [Real.norm_eq_abs] using ha)
  simpa only [Real.norm_eq_abs] using hn.trans hlim

private theorem primitive_abs (e k : ℕ) :
    |HTGeometry.centeredModularPrimitive e k| ≤ (e : ℝ)/8 := by
  have h := HTGeometry.centeredModularPrimitive_bounds e k
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem kernel_series {d : ℕ} (hd : 0 < d) (e : ℕ) :
    Summable (fun j : ℕ => HTGeometry.centeredModularPrimitive e (d*(j+1)) /
      ((d*(j+1) : ℕ) : ℝ)^2) ∧
    |completeKernel d e| ≤ (e : ℝ)/(4*(d : ℝ)^2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := reciprocal_bound (q := 1) (by omega)
    (C := (e : ℝ)/(4*(d : ℝ)^2)) (by positivity)
    (fun j : ℕ => HTGeometry.centeredModularPrimitive e (d*(j+1)) /
      ((d*(j+1) : ℕ) : ℝ)^2) (fun j => ?_)
  · simpa [completeKernel] using h
  rw [abs_div, abs_of_nonneg (sq_nonneg (((d*(j+1) : ℕ) : ℝ)))]
  calc _ ≤ ((e : ℝ)/8) / ((d*(j+1) : ℕ) : ℝ)^2 := by
             exact div_le_div_of_nonneg_right (primitive_abs e _) (sq_nonneg _)
       _ ≤ _ := by
         push_cast
         field_simp
         nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) e)
           (mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (show 0 ≤ (j : ℝ)+1 by positivity))]

/-- One reduced-denominator channel, with its complete numerator tail and actual Möbius signs. -/
def reducedTerm (N b r j : ℕ) : ℝ :=
  let a : ℕ := N/r+j+1
  if a.Coprime b then
    ((ArithmeticFunction.moebius (r*a) : ℤ) : ℝ) *
    ((ArithmeticFunction.moebius (r*b) : ℤ) : ℝ) * completeKernel (r*a) (r*b)
  else 0

/-- The complete complementary flux restricted by reduced denominator. -/
def reducedHead (N B : ℕ) : ℝ :=
  -(∑ b ∈ Icc 1 (min B N), ∑ r ∈ Icc 1 (N/b), ∑' j, reducedTerm N b r j)

private theorem mu_abs (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

private theorem term_bound {N b r : ℕ} (hr : 0 < r) (j : ℕ) :
    |reducedTerm N b r j| ≤ (b : ℝ)/(4*r*((N/r+j+1 : ℕ) : ℝ)^2) := by
  let a : ℕ := N/r+j+1
  have ha : 0 < a := Nat.zero_lt_succ _
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hk := (kernel_series (Nat.mul_pos hr ha) (r*b)).2
  unfold reducedTerm
  dsimp only
  split_ifs with h
  · calc _ ≤ 1*1*|completeKernel (r*a) (r*b)| := by
               rw [abs_mul, abs_mul]
               gcongr <;> apply mu_abs
           _ ≤ ((r*b : ℕ) : ℝ)/(4*((r*a : ℕ) : ℝ)^2) := by simpa using hk
           _ = _ := by
             change ((r*b : ℕ) : ℝ)/(4*((r*a : ℕ) : ℝ)^2) = (b : ℝ)/(4*r*(a : ℝ)^2)
             push_cast
             field_simp
  · simp only [abs_zero]
    positivity

private theorem reduced_series {N b r : ℕ} (hr : 0 < r) (hrN : r ≤ N) :
    Summable (reducedTerm N b r) ∧
    |∑' j, reducedTerm N b r j| ≤ (b : ℝ)/(2*N) := by
  have hq : 0 < N/r := Nat.div_pos hrN hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (0 : ℝ) < (N/r : ℕ) := by exact_mod_cast hq
  have hN : 0 < N := lt_of_lt_of_le hr hrN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := reciprocal_bound hq (C := (b : ℝ)/(4*r)) (by positivity)
    (reducedTerm N b r) (fun j => ?_)
  · refine ⟨hs.1, hs.2.trans ?_⟩
    have hn : N ≤ 2*r*(N/r) := by
      have hm := Nat.mod_lt N hr
      have he := Nat.mod_add_div N r
      nlinarith
    have hnR : (N : ℝ) ≤ 2*r*(N/r : ℕ) := by exact_mod_cast hn
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  calc _ ≤ (b : ℝ)/(4*r*((N/r+j+1 : ℕ) : ℝ)^2) := term_bound hr j
       _ ≤ _ := by
         push_cast
         rw [div_div]
         apply div_le_div_of_nonneg_left (by positivity) (by positivity)
         nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- The full reduced-denominator head has a bound independent of the physical cutoff. -/
theorem reducedHead_bound (N B : ℕ) : |reducedHead N B| ≤ (B : ℝ)/2 := by
  by_cases hN : N = 0
  · subst N
    simp [reducedHead]
    positivity
  have hNR : (0 : ℝ) < N := by positivity
  unfold reducedHead
  rw [abs_neg]
  calc _ ≤ ∑ b ∈ Icc 1 (min B N), |∑ r ∈ Icc 1 (N/b), ∑' j, reducedTerm N b r j| :=
           abs_sum_le_sum_abs _ _
       _ ≤ ∑ b ∈ Icc 1 (min B N), (1/2 : ℝ) := by
         apply sum_le_sum
         intro b hb
         have hb0 : 0 < b := (mem_Icc.mp hb).1
         have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
         calc _ ≤ ∑ r ∈ Icc 1 (N/b), |∑' j, reducedTerm N b r j| := abs_sum_le_sum_abs _ _
              _ ≤ ∑ r ∈ Icc 1 (N/b), (b : ℝ)/(2*N) := by
                apply sum_le_sum
                intro r hr
                have hr0 : 0 < r := (mem_Icc.mp hr).1
                have hrN : r ≤ N := (mem_Icc.mp hr).2.trans (Nat.div_le_self _ _)
                exact (reduced_series hr0 hrN).2
              _ = (N/b : ℕ)*(b : ℝ)/(2*N) := by simp; ring
              _ ≤ 1/2 := by
                have hmul : (N/b : ℕ)*(b : ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N b
                rw [div_le_iff₀ (by positivity)]
                nlinarith
       _ ≤ _ := by
         simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
         have h : ((min B N : ℕ) : ℝ) ≤ B := by exact_mod_cast min_le_left B N
         linarith

end RHTower.DeletionFlux
