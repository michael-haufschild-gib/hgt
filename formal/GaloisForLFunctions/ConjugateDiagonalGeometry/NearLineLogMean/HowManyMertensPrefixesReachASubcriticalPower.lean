import GaloisForLFunctions.RHTower.MobiusMertensMeanSquareExponentLaw

/-!
# How many Mertens prefixes exceed a subcritical power

Split the mean square into the prefixes exceeding the test and their
complement. Littlewood bounds the contribution of each exceptional
index. Since the second moment already has the zero abscissa as its
critical power, any smaller price exponent must be exceeded at sets
of cutoffs whose counting exponent reaches one.
-/

noncomputable section
open Finset Filter
open _root_.RHTower
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Indices through N where the absolute Mertens prefix exceeds a
fixed multiple of the indicated power. -/
def mertensExcursions (b C : ℝ) (N : ℕ) : Finset ℕ :=
  (range (N+1)).filter fun k => C*((k:ℝ)+1)^b < |shiftedMertensReal k|

private theorem square_le_power {m C x b : ℝ} (hx : 0 ≤ x) (h : |m| ≤ C*x^b) :
    m^2 ≤ C^2*x^(2*b) := by
  have hs := pow_le_pow_left₀ (abs_nonneg m) h 2
  rw [sq_abs,mul_pow,←Real.rpow_natCast (x^b) 2,←Real.rpow_mul hx] at hs
  simpa only [Nat.cast_ofNat,mul_comm b (2:ℝ)] using hs

/-- A bound for the number of exceptional indices at a fixed cutoff
controls the entire second moment at that cutoff. -/
theorem mertens_second_moment_from_excursion_count {b a : ℝ}
    (hb : 0 ≤ b) (ha : zetaZeroAbscissa < a) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      (∑ k ∈ range (N+1), shiftedMertensReal k^2) ≤ C^2*((N:ℝ)+1)^(1+2*b) +
        B*(mertensExcursions b C N).card*((N:ℝ)+1)^(2*a) := by
  classical
  obtain ⟨A,hA,h⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroAbscissa) (sub_pos.mpr ha)
  rw [show zetaZeroAbscissa+(a-zetaZeroAbscissa)=a by ring] at h
  refine ⟨A^2,sq_nonneg _,fun N => ?_⟩
  let S := range (N+1)
  let E := mertensExcursions b C N
  have hsub : E ⊆ S := filter_subset _ _
  have cmp (k : ℕ) (hk : k ∈ S) : (k:ℝ)+1 ≤ (N:ℝ)+1 :=
    add_le_add (Nat.cast_le.mpr (Nat.lt_succ_iff.mp (mem_range.mp hk))) le_rfl
  have cap (k : ℕ) (hk : k ∈ E) : shiftedMertensReal k^2 ≤ A^2*((N:ℝ)+1)^(2*a) := by
    have hh := h k
    rw [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal] at hh
    exact square_le_power (by positivity) (hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (cmp k (hsub hk)) (by linarith only [half_le_zetaZeroAbscissa,ha])) hA))
  have floor (k : ℕ) (hk : k ∈ S \ E) : shiftedMertensReal k^2 ≤ C^2*((N:ℝ)+1)^(2*b) := by
    obtain ⟨hk,hn⟩ := mem_sdiff.mp hk
    have hh : |shiftedMertensReal k| ≤ C*((k:ℝ)+1)^b :=
      le_of_not_gt fun hu => hn (mem_filter.mpr ⟨hk,hu⟩)
    exact square_le_power (by positivity) (hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (cmp k hk) hb) hC))
  have he := sum_le_sum cap
  have hf := sum_le_sum floor
  simp only [sum_const,nsmul_eq_mul] at he hf
  have hc : ((S \ E).card:ℝ) ≤ (N:ℝ)+1 := by
    have h' := card_le_card (sdiff_subset : S \ E ⊆ S)
    simpa only [S,card_range,Nat.cast_add,Nat.cast_one] using
      (Nat.cast_le (α:=ℝ)).mpr h'
  have hs := (hf.trans (mul_le_mul_of_nonneg_right hc (by positivity)))
  change (∑ k ∈ S, _) ≤ _
  rw [←sum_sdiff hsub]
  rw [Real.rpow_add (by positivity : 0<(N:ℝ)+1),Real.rpow_one]
  linarith only [hs,he]

/-- At every power below the zero edge and every fixed price constant,
the exceptional count beats every power exponent below one cofinally.
This includes exponents below one half even if RH holds. -/
theorem frequently_many_mertens_excursions {b d : ℝ} (hb : 0 ≤ b) (hbz : b < zetaZeroAbscissa)
    (hd : d < 1) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ᶠ N : ℕ in atTop, K*((N:ℝ)+1)^d < ((mertensExcursions b C N).card:ℝ) := by
  let a := zetaZeroAbscissa+(1-d)/4
  have ha : zetaZeroAbscissa < a := lt_add_of_pos_right _ (by linarith only [hd])
  let c := max (1+2*b) (d+2*a)
  have hc1 : 1 ≤ c := (by linarith only [hb] : 1 ≤ 1+2*b).trans (le_max_left _ _)
  have hc : c < 1+2*zetaZeroAbscissa := max_lt (by linarith only [hbz]) (by dsimp only [a]; linarith only [hd])
  intro hno
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hno.mono fun _ h => le_of_not_gt h)
  obtain ⟨B,hB,hbound⟩ := mertens_second_moment_from_excursion_count hb ha C hC
  let H := ∑ k ∈ range (L+1), shiftedMertensReal k^2
  have hH : 0 ≤ H := sum_nonneg fun _ _ => sq_nonneg _
  have strip := zetaZeroAbscissa_le_of_sum_sq_shiftedMertens_le (C:=H+C^2+B*K) hc1 (fun N => by
    have hn : 1 ≤ (N:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) N]
    have nr := zero_lt_one.trans_le hn
    have pp := Real.rpow_nonneg nr.le c
    by_cases hNL : N < L
    · have hsmall : (∑ k ∈ range (N+1),shiftedMertensReal k^2) ≤ H :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun k _ _ => sq_nonneg _
      exact hsmall.trans ((by linarith only [sq_nonneg C,mul_nonneg hB hK] : H ≤ H+C^2+B*K).trans
        (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hn (by linarith only [hc1]))))
    · have he := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hL N (le_of_not_gt hNL)) hB) (Real.rpow_nonneg nr.le (2*a))
      have hscale : B*(K*((N:ℝ)+1)^d)*((N:ℝ)+1)^(2*a) = B*K*((N:ℝ)+1)^(d+2*a) := by
        rw [Real.rpow_add nr]; ring
      rw [hscale] at he
      have hs := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _ : 1+2*b ≤ c)) (sq_nonneg C)
      have ht := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (le_max_right _ _ : d+2*a ≤ c)) (mul_nonneg hB hK)
      linarith only [hbound N,he,hs,ht,mul_nonneg hH pp])
  linarith only [strip,hc]

#print axioms mertens_second_moment_from_excursion_count
#print axioms frequently_many_mertens_excursions
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
