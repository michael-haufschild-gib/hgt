import GaloisForLFunctions.RHTower.EulerDeletionMobiusPrimitiveEnergy
import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Complete Möbius Gram diagonal and constructive cross interference

The actual modular source norm is its full signed Gram form. The diagonal
has a first-power logarithmic ceiling. Any off-line zero would therefore force
superlogarithmic positive escape in the aggregate off-diagonal source term.
-/
noncomputable section
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionMobiusGram

/-- Literal signed Gram entry; both Möbius signs are retained. -/
def entry (m n : ℕ) : ℝ :=
  ((moebius m : ℤ) : ℝ) * ((moebius n : ℤ) : ℝ) * bdGram (1 / (m : ℝ)) (1 / (n : ℝ))

/-- Full diagonal of the raw modular Möbius Gram. -/
def diagonal (N : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 N, entry m m

/-- Complete signed off-diagonal sum over ordered pairs, with no discarded cross terms. -/
def cross (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, entry m n

/-- Exact arithmetic decomposition of the entire existing carrier norm. -/
theorem modular_norm_sq_eq_diagonal_add_cross (N : ℕ) :
    ‖bdMobiusModularApproximantVec N‖^2 = diagonal N + cross N := by
  rw [bdMobiusModularApproximantVec_eq_generatorCombination, bdMobiusGeneratorCombination,
    ← bdGram_quadraticForm_eq_norm_sq]
  simp only [neg_mul_neg]
  rw [diagonal, cross, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  exact (Finset.sum_erase_add (Finset.Icc 1 N) (entry m) hm).symm.trans (add_comm _ _)

/-- The signed coefficient cannot change the nonnegative diagonal. -/
theorem diagonal_nonneg (N : ℕ) : 0 ≤ diagonal N := by
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (mul_self_nonneg _) (bdGram_self_nonneg _)

/-- A head/telescoping-tail split removes the logarithmic loss from the individual diagonal. -/
theorem gram_self_le_two_div {m : ℕ} (hm : 1 ≤ m) :
    bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) ≤ 2 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  let g (n : ℕ) : ℝ := (((n+1)%m : ℕ) : ℝ) * (((n+1)%m : ℕ) : ℝ) /
    ((m : ℝ)*(m : ℝ)*((n : ℝ)+1)*((n : ℝ)+2))
  have hnonneg (n : ℕ) : 0 ≤ g n := by unfold g; positivity
  have hhead (n : ℕ) : g n ≤ 1 / (m : ℝ)^2 := by
    have hr : (0 : ℝ) ≤ (((n+1)%m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hx : (((n+1)%m : ℕ) : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast Nat.mod_le (n+1) m
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold g
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (((n+1)%m : ℕ) : ℝ)*(((n+1)%m : ℕ) : ℝ) ≤ ((n : ℝ)+1)*((n : ℝ)+2) := by
      have h := mul_le_mul hx hx hr (show 0 ≤ (n : ℝ)+1 by positivity)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (m : ℝ))]
  have htail (n : ℕ) : g n ≤ 1 / ((n : ℝ)+1) - 1 / ((n : ℝ)+2) := by
    have hr : (0 : ℝ) ≤ (((n+1)%m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hx : (((n+1)%m : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.mod_lt (n+1) hm).le
    have heq : 1 / ((n : ℝ)+1) - 1 / ((n : ℝ)+2) =
        1 / (((n : ℝ)+1)*((n : ℝ)+2)) := by field_simp; ring
    rw [heq]
    unfold g
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (((n+1)%m : ℕ) : ℝ)*(((n+1)%m : ℕ) : ℝ) ≤ (m : ℝ)*(m : ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq
      (show 0 ≤ ((n : ℝ)+1)*((n : ℝ)+2) by positivity)]
  have hfinite (L : ℕ) : ∑ n ∈ Finset.range L, g n ≤ 2 / (m : ℝ) := by
    have hfirst : ∑ n ∈ Finset.range m, g n ≤ 1 / (m : ℝ) := by
      calc _ ≤ ∑ n ∈ Finset.range m, 1 / (m : ℝ)^2 := Finset.sum_le_sum (fun n _ => hhead n)
           _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    have hlast : ∑ n ∈ Finset.range L, g (m+n) ≤ 1 / ((m : ℝ)+1) := by
      calc _ ≤ ∑ n ∈ Finset.range L,
               (1 / ((m : ℝ)+n+1) - 1 / ((m : ℝ)+(n+1 : ℕ)+1)) := by
             apply Finset.sum_le_sum
             intro n hn
             have he : (m : ℝ)+(n+1 : ℕ)+1 = ((m+n : ℕ) : ℝ)+2 := by push_cast; ring
             rw [he]
             simpa only [Nat.cast_add] using htail (m+n)
           _ = 1 / ((m : ℝ)+1) - 1 / ((m : ℝ)+L+1) := by
             simpa only [Nat.cast_zero, add_zero] using
               Finset.sum_range_sub' (fun n : ℕ => (1 : ℝ) / ((m : ℝ)+n+1)) L
           _ ≤ _ := sub_le_self _ (by positivity)
    calc ∑ n ∈ Finset.range L, g n ≤ ∑ n ∈ Finset.range (m+L), g n :=
           Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun n _ _ => hnonneg n)
         _ = (∑ n ∈ Finset.range m, g n) + ∑ n ∈ Finset.range L, g (m+n) := Finset.sum_range_add _ _ _
         _ ≤ 1 / (m : ℝ) + 1 / ((m : ℝ)+1) := add_le_add hfirst hlast
         _ ≤ 2 / (m : ℝ) := by
           have hrec : 1 / ((m : ℝ)+1) ≤ 1 / (m : ℝ) := by
             apply (div_le_div_iff₀ (by positivity) hm0).mpr
             linarith
           calc _ ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add le_rfl hrec
                _ = _ := by ring
  exact le_of_tendsto (hasSum_bdGram_discrete hm hm).tendsto_sum_nat (Eventually.of_forall hfinite)

/-- The complete literal Möbius diagonal has at most twice the harmonic mass. -/
theorem diagonal_le_two_mul_harmonic (N : ℕ) : diagonal N ≤ 2 * (harmonic N : ℝ) := by
  have hterm (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : entry m m ≤ 2 * (m : ℝ)⁻¹ := by
    have hmu := Sieve.abs_moebius_real_le_one m
    have hmu2 : ((moebius m : ℤ) : ℝ) * ((moebius m : ℤ) : ℝ) ≤ 1 := by
      have hlow := (abs_le.mp hmu).1
      have hupp := (abs_le.mp hmu).2
      nlinarith
    calc entry m m ≤ bdGram (1 / (m : ℝ)) (1 / (m : ℝ)) :=
           (mul_le_mul_of_nonneg_right hmu2 (bdGram_self_nonneg _)).trans_eq (one_mul _)
         _ ≤ 2 / (m : ℝ) := gram_self_le_two_div (Finset.mem_Icc.mp hm).1
         _ = _ := div_eq_mul_inv _ _
  calc diagonal N ≤ ∑ m ∈ Finset.Icc 1 N, 2 * (m : ℝ)⁻¹ := Finset.sum_le_sum hterm
       _ = _ := by
         rw [← Finset.mul_sum]
         simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Unconditional logarithmic ceiling for the complete arithmetic diagonal, at every cutoff. -/
theorem diagonal_le_two_mul_one_add_log (N : ℕ) :
    diagonal N ≤ 2 * (1 + Real.log (N : ℝ)) :=
  (diagonal_le_two_mul_harmonic N).trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by norm_num))

private theorem log_tendsto : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Every sufficiently late diagonal fits one fixed first-power logarithmic budget. -/
theorem diagonal_eventually_le_four_log :
    ∀ᶠ N : ℕ in atTop, diagonal N ≤ 4 * Real.log (N : ℝ) := by
  filter_upwards [log_tendsto.eventually_ge_atTop 1] with N hlog
  have hd := diagonal_le_two_mul_one_add_log N
  linarith

/-- At every hypothetical off-line zero, the complete raw source norm escapes every log power. -/
theorem modular_norm_sq_div_log_pow_tendsto (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : rho.1.re ≠ 1/2) (q : ℕ) :
    Tendsto (fun N : ℕ => ‖bdMobiusModularApproximantVec N‖^2 / Real.log (N : ℝ)^q) atTop atTop := by
  obtain ⟨C,hC,hbound⟩ := DeletionMobiusPrimitive.exists_current_bound_by_primitiveEnergy rho
  have hcurrent := (DeletionMobiusLogGrowth.abs_sourceCurrent_div_log_pow_tendsto rho hs q).atTop_div_const
    (show 0 < 2*C by positivity)
  apply tendsto_atTop_mono' atTop _ hcurrent
  filter_upwards [log_tendsto.eventually_ge_atTop 1] with N hlog
  have hpow : 0 < Real.log (N : ℝ)^q := pow_pos (by linarith) q
  have hb := (hbound N).trans (mul_le_mul_of_nonneg_left
    (DeletionMobiusPrimitive.primitiveEnergy_le_two_modular_norm_sq N) hC.le)
  apply (div_le_iff₀ (show 0 < 2*C by positivity)).mpr
  apply (div_le_iff₀ hpow).mpr
  calc |(DeletionMobiusCurrent.sourceCurrent N rho.1).re| ≤ C*(2*‖bdMobiusModularApproximantVec N‖^2) := hb
       _ = _ := by field_simp

/-- Every hypothetical off-line zero forces aggregate constructive arithmetic interference
beyond every logarithmic power; the whole controlled diagonal has already been removed. -/
theorem cross_div_log_pow_tendsto (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : rho.1.re ≠ 1/2) (q : ℕ) :
    Tendsto (fun N : ℕ => cross N / Real.log (N : ℝ)^q) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [(modular_norm_sq_div_log_pow_tendsto rho hs (q+1)).eventually_ge_atTop (max B 0+4),
    diagonal_eventually_le_four_log, log_tendsto.eventually_ge_atTop 1] with N hnorm hd hlog
  have hpow : 0 < Real.log (N : ℝ)^q := pow_pos (by linarith) q
  have hpone : 1 ≤ Real.log (N : ℝ)^q := one_le_pow₀ hlog
  have hn := (le_div_iff₀ (pow_pos (by linarith : 0 < Real.log (N : ℝ)) (q+1))).mp hnorm
  rw [pow_succ, modular_norm_sq_eq_diagonal_add_cross] at hn
  have hB : B * Real.log (N : ℝ)^q ≤
      (max B 0 * Real.log (N : ℝ)^q) * Real.log (N : ℝ) := by
    calc _ ≤ max B 0 * Real.log (N : ℝ)^q := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
         _ ≤ _ := by
           simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog
             (mul_nonneg (le_max_right B 0) hpow.le)
  have hfour : 4 * Real.log (N : ℝ) ≤
      4 * Real.log (N : ℝ)^q * Real.log (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hpone (show 0 ≤ Real.log (N : ℝ) by linarith)]
  apply (le_div_iff₀ hpow).mpr
  nlinarith

/-- A sufficient arithmetic cancellation criterion: the complete signed cross sum need only
have cofinal polynomial-log upper returns. This theorem does not prove that source ceiling. -/
theorem riemannHypothesis_of_cofinally_log_bounded_cross
    (hsource : ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      cross N ≤ B * Real.log (N : ℝ)^q) : RiemannHypothesis := by
  intro s hz ht hs1
  let rho : RiemannGaussian.NontrivialZetaZero := ⟨s,hz,ht,hs1⟩
  by_contra hs
  obtain ⟨q,B,hB⟩ := hsource
  have he := (cross_div_log_pow_tendsto rho hs q).eventually_gt_atTop B
  obtain ⟨K,hK⟩ := eventually_atTop.mp (he.and (log_tendsto.eventually_ge_atTop 1))
  obtain ⟨N,hKN,hN⟩ := hB K
  have h := hK N hKN
  exact (not_le.mpr h.1) ((div_le_iff₀ (pow_pos (by linarith : 0 < Real.log (N : ℝ)) q)).mpr hN)

end RHTower.DeletionMobiusGram
end
