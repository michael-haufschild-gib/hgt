import GaloisForLFunctions.RHTower.PaperWoldCompositeGrowth
import GaloisForLFunctions.HTGeometry.LpInjectionCompression

/-! # Phase-invariant column energy at the three-quarter boundary

Even composite rows alone force a nonvanishing column norm. Entrywise phases
cannot remove this obstruction, because each coordinate norm is unchanged.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

abbrev PaperWoldUnitPhase := ℕ × ℕ → {z : ℂ // ‖z‖ = 1}

def PaperWoldPhaseRealization (t : ℝ) (u : PaperWoldUnitPhase) :=
  {T : PaperWoldHistory →L[ℂ] PaperWoldHistory //
    HasLpMatrix T (fun n j => (u (n, j) : ℂ) * paperWoldDirectedKernel t (n, j))}

theorem paperWoldPhaseRealization_single_norm (t : ℝ) (u : PaperWoldUnitPhase)
    (T : PaperWoldPhaseRealization t u) (n j : ℕ) :
    ‖T.val (lp.single 2 j 1) n‖ = ‖paperWoldDirectedKernel t (n, j)‖ := by
  have h := T.property n j
  change T.val (lp.single 2 j 1) n = _ at h
  rw [h, norm_mul, (u (n, j)).property, one_mul]

private theorem even_window_energy_le (x : PaperWoldHistory) (N : ℕ) :
    ∑ n ∈ Finset.Ico N (2 * N), ‖x (2 * n + 2)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let f : ℕ → ℕ := fun n => 2 * n + 2
  have hf : Function.Injective f := by intro n m h; dsimp [f] at h; omega
  let R := lpCoordinatePullback (E := ℂ) f hf
  have hs := lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (R x) (Finset.Ico N (2 * N))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  have hb : ‖R x‖ ≤ ‖x‖ := lpCoordinatePullbackLinear_norm_le f hf x
  exact hs.trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

theorem paperWoldPhase_column_energy_lower (t : {t : ℝ // 3 / 4 ≤ t})
    (u : PaperWoldUnitPhase) (T : PaperWoldPhaseRealization t u) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (4 * t.val - 3) / 2304 ≤ ‖T.val (lp.single 2 (4 * N + 2) 1)‖ ^ 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he (n : ℕ) (hn : n ∈ Finset.Ico N (2 * N)) :
      (N : ℝ) ^ (2 * t.val) / (48 * (N : ℝ) ^ 2) ≤
        ‖T.val (lp.single 2 (4 * N + 2) 1) (2 * n + 2)‖ := by
    rw [paperWoldPhaseRealization_single_norm]
    have h := paperWoldCompositeEntry_rectangle_lower ⟨t.val, by linarith [t.property]⟩ N hN n hn
      (2 * N) (by simp only [Finset.mem_Ico]; omega)
    rw [← paperWoldCompositeEntry_norm_eq_re] at h
    simpa only [paperWoldCompositeEntry, show 2 * (2 * N) + 2 = 4 * N + 2 by omega] using h
  have hs : (N : ℝ) * ((N : ℝ) ^ (2 * t.val) / (48 * (N : ℝ) ^ 2)) ^ 2 ≤
      ∑ n ∈ Finset.Ico N (2 * N), ‖T.val (lp.single 2 (4 * N + 2) 1) (2 * n + 2)‖ ^ 2 := by
    calc
      _ = ∑ _n ∈ Finset.Ico N (2 * N), ((N : ℝ) ^ (2 * t.val) / (48 * (N : ℝ) ^ 2)) ^ 2 := by
        simp only [Finset.sum_const, Nat.card_Ico, show 2 * N - N = N by omega, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun n hn =>
        (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (he n hn)
  have hid : (N : ℝ) * ((N : ℝ) ^ (2 * t.val) / (48 * (N : ℝ) ^ 2)) ^ 2 =
      (N : ℝ) ^ (4 * t.val - 3) / 2304 := by
    rw [div_pow, ← Real.rpow_mul_natCast hNp.le]
    simp only [Nat.cast_ofNat]
    rw [show 2 * t.val * (2 : ℝ) = 4 * t.val by ring,
      Real.rpow_sub hNp, show (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 3 from Real.rpow_natCast _ 3]
    field_simp [hNp.ne']
    ring
  rw [hid] at hs
  exact hs.trans (even_window_energy_le _ N)

theorem paperWoldPhase_column_energy_floor (t : {t : ℝ // 3 / 4 ≤ t})
    (u : PaperWoldUnitPhase) (T : PaperWoldPhaseRealization t u) (N : ℕ) (hN : 1 ≤ N) :
    (1 / 2304 : ℝ) ≤ ‖T.val (lp.single 2 (4 * N + 2) 1)‖ ^ 2 := by
  apply le_trans _ (paperWoldPhase_column_energy_lower t u T N hN)
  exact div_le_div_of_nonneg_right
    (Real.one_le_rpow (by exact_mod_cast hN) (by linarith [t.property])) (by norm_num)

end
end RHTower
