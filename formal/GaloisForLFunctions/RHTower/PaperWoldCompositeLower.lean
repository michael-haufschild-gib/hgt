import GaloisForLFunctions.RHTower.PaperWoldFullKernel

/-! # The composite part of the literal Wold kernel

Even composite indices carry the exact negative logarithmic cell. Their sizes
give an arithmetic lower bound without any prime-distribution assumption.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

/-- The unwindowed directed kernel at an arbitrary real exponent. -/
def paperWoldDirectedKernel (t : ℝ) (q : ℕ × ℕ) : ℂ :=
  if q.1 < q.2 then
    (((q.1 : ℝ) + 1) ^ (2 * t) * xiHeatCassiniWoldNatIncrement q.1 *
      xiHeatCassiniWoldNatIncrement q.2 : ℝ) else 0

theorem paperWoldDirectedKernel_strictHalf (p : PaperWoldStrictHalf) :
    paperWoldDirectedKernel p.t = paperWoldFullKernel p := rfl

theorem paperWold_even_composite_increment (k : ℕ) :
    xiHeatCassiniWoldNatIncrement (2 * k + 2) =
      -(Real.log (2 * (k : ℝ) + 4) - Real.log (2 * (k : ℝ) + 3)) := by
  have hp : ¬ (2 * k + 2 + 2).Prime :=
    Nat.not_prime_of_dvd_of_ne
      (show 2 ∣ 2 * k + 2 + 2 from ⟨k + 2, by omega⟩) (by norm_num) (by omega)
  rw [xiHeatCassiniWoldNatIncrement_eq, xiHeatCassiniWoldNatWeight, dif_neg hp]
  push_cast
  ring_nf

theorem paperWold_even_composite_increment_lower (k : ℕ) :
    1 / (2 * (k : ℝ) + 4) ≤ -xiHeatCassiniWoldNatIncrement (2 * k + 2) := by
  rw [paperWold_even_composite_increment, neg_neg]
  have hx : 0 < 2 * (k : ℝ) + 3 := by positivity
  have hy : 0 < 2 * (k : ℝ) + 4 := by positivity
  have h := Real.log_le_sub_one_of_pos (x := (2 * (k : ℝ) + 3) / (2 * (k : ℝ) + 4))
    (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  have he : (2 * (k : ℝ) + 3) / (2 * (k : ℝ) + 4) - 1 =
      -(1 / (2 * (k : ℝ) + 4)) := by field_simp; ring
  linarith

theorem paperWold_even_composite_increment_neg (k : ℕ) :
    xiHeatCassiniWoldNatIncrement (2 * k + 2) < 0 := by
  have := paperWold_even_composite_increment_lower k
  have : 0 < 1 / (2 * (k : ℝ) + 4) := by positivity
  linarith

private theorem directed_composite_lower (t : ℝ) (ht : 1 / 2 ≤ t)
    (m k : ℕ) (hk : k ≤ m) :
    1 / (4 * (m : ℝ) + 12) ≤
      ‖paperWoldDirectedKernel t (2 * k + 2, 2 * m + 4)‖ := by
  have hki : 2 * k + 2 < 2 * m + 4 := by omega
  have ha := paperWold_even_composite_increment_lower k
  have hb := paperWold_even_composite_increment_lower (m + 1)
  have hka := paperWold_even_composite_increment_neg k
  have hmb := paperWold_even_composite_increment_neg (m + 1)
  have hj : 2 * (m + 1) + 2 = 2 * m + 4 := by omega
  rw [hj] at hb hmb
  push_cast at hb
  have hn : (1 : ℝ) ≤ (2 * k + 2 : ℕ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (2 * k + 2)]
  have hw : (2 * (k : ℝ) + 3) ≤ ((2 * k + 2 : ℕ) + 1 : ℝ) ^ (2 * t) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn (show (1 : ℝ) ≤ 2 * t by linarith)
    rw [Real.rpow_one] at h
    convert h using 1
    push_cast
    ring
  have hx : 0 < 2 * (k : ℝ) + 4 := by positivity
  have hy : 0 < 2 * (m : ℝ) + 6 := by positivity
  have hhalf : (1 : ℝ) / 2 ≤ (2 * (k : ℝ) + 3) / (2 * (k : ℝ) + 4) := by
    apply (le_div_iff₀ hx).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hfirst : (1 : ℝ) / 2 ≤
      ((2 * k + 2 : ℕ) + 1 : ℝ) ^ (2 * t) * (-xiHeatCassiniWoldNatIncrement (2 * k + 2)) := by
    calc
      _ ≤ (2 * (k : ℝ) + 3) * (1 / (2 * (k : ℝ) + 4)) := by simpa [div_eq_mul_inv] using hhalf
      _ ≤ _ := mul_le_mul hw ha (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hprod := mul_le_mul hfirst hb (by positivity : 0 ≤ 1 / (2 * ((m : ℝ) + 1) + 4))
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (neg_nonneg.mpr hka.le))
  rw [paperWoldDirectedKernel, if_pos hki, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _) hka.le) hmb.le)]
  dsimp only [Prod.fst, Prod.snd]
  calc
    1 / (4 * (m : ℝ) + 12) = (1 / 2 : ℝ) * (1 / (2 * ((m : ℝ) + 1) + 4)) := by
      field_simp
      ring
    _ ≤ _ := hprod
    _ = _ := by ring

/-- A whole triangular family of actual entries survives at and above the half power. -/
theorem paperWoldDirectedKernel_composite_lower
    (t : {t : ℝ // 1 / 2 ≤ t}) (m : ℕ) (k : Fin (m + 1)) :
    1 / (4 * (m : ℝ) + 12) ≤
      ‖paperWoldDirectedKernel t (2 * k.val + 2, 2 * m + 4)‖ :=
  directed_composite_lower t t.property m k.val (by omega)

/-- Each composite column contains a harmonic amount of squared energy. -/
theorem paperWoldDirectedKernel_composite_column_lower
    (t : {t : ℝ // 1 / 2 ≤ t}) (m : ℕ) :
    1 / (144 * ((m : ℝ) + 1)) ≤
      ∑ k ∈ Finset.range (m + 1),
        ‖paperWoldDirectedKernel t (2 * k + 2, 2 * m + 4)‖ ^ 2 := by
  have hsum : (m + 1 : ℝ) * (1 / (4 * (m : ℝ) + 12)) ^ 2 ≤
      ∑ k ∈ Finset.range (m + 1),
        ‖paperWoldDirectedKernel t (2 * k + 2, 2 * m + 4)‖ ^ 2 := by
    calc
      _ = ∑ _k ∈ Finset.range (m + 1), (1 / (4 * (m : ℝ) + 12)) ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk =>
        (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr
          (directed_composite_lower t t.property m k (by have := Finset.mem_range.mp hk; omega))
  apply le_trans _ hsum
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hd : 0 < 4 * (m : ℝ) + 12 := by positivity
  rw [one_div_pow, mul_one_div]
  apply (div_le_div_iff₀ (by positivity : 0 < 144 * ((m : ℝ) + 1))
    (sq_pos_of_pos hd)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

end
end RHTower
