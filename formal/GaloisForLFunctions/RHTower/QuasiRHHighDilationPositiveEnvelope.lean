import GaloisForLFunctions.RHTower.QuasiRHPowerMeshMeanSquareAbscissa
import GaloisForLFunctions.RHTower.MobiusDivisorPositiveNormalizationCost

/-!
# Sharp positive-envelope cost after the dilation cutoff

Deleting the sublinear head leaves a positive fraction of the actual quadratic diagonal.
On `M=j^m`, `D=j^(m-1)`, the absolute tail mass still has order `M*sqrt M`.
Its cumulative normalized square therefore has order `J^(m+1)`, two powers above
the signed covariance targets for the sixth and fourth power meshes.
-/

noncomputable section
open Finset Real
open scoped BigOperators

namespace RHTower

/-- Absolute mass of the literal high-dilation coefficients, retaining their actual support. -/
def mobiusDivisorDilationTailAbsoluteMass (M D : ℕ) : ℝ :=
  ∑ d ∈ Icc (D + 1) (M - 1), |mobiusDivisorDilationChannel M d|

private theorem channel_abs_le_sqrt (M d : ℕ) :
    |mobiusDivisorDilationChannel M d| ≤ Real.sqrt M :=
  (abs_mobiusDivisorDilationChannel_le_three_fifths_sqrt M d).trans
    (by nlinarith [Real.sqrt_nonneg (M : ℝ)])

/-- Deleting `D` channels removes at most `D*M` from the actual quadratic diagonal. -/
theorem mobiusDivisorDiagonal_le_head_cost_add_tail {M D : ℕ} (hD : D < M) :
    mobiusDivisorSelectionEnergy M ∅ ≤ (D : ℝ) * M +
      ∑ d ∈ Icc (D + 1) (M - 1), (mobiusDivisorDilationChannel M d) ^ 2 := by
  have hM : 1 ≤ M := by omega
  have hterminal : (∑ d ∈ Icc 1 M, (mobiusDivisorDilationChannel M d) ^ 2) =
      ∑ d ∈ Icc 1 (M - 1), (mobiusDivisorDilationChannel M d) ^ 2 := by
    symm
    apply sum_subset (Icc_subset_Icc_right (Nat.sub_le M 1))
    intro d hd hnot
    have hdM : d = M := by
      have := mem_Icc.mp hd
      simp only [mem_Icc] at hnot
      omega
    subst d
    rw [mobiusDivisorDilationChannel_eq_zero_of_lt (by omega : M - 1 < M)]
    norm_num
  have hsplit : Icc 1 (M - 1) = Icc 1 D ∪ Icc (D + 1) (M - 1) := by
    ext d
    simp only [mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc 1 D) (Icc (D + 1) (M - 1)) := by
    rw [disjoint_left]
    intro d hd1 hd2
    have := mem_Icc.mp hd1
    have := mem_Icc.mp hd2
    omega
  have hterm (d : ℕ) : (mobiusDivisorDilationChannel M d) ^ 2 ≤ (M : ℝ) := by
    have h := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr (channel_abs_le_sqrt M d)
    simpa only [sq_abs, Real.sq_sqrt (Nat.cast_nonneg M)] using h
  have hhead : ∑ d ∈ Icc 1 D, (mobiusDivisorDilationChannel M d) ^ 2 ≤ (D : ℝ) * M := by
    calc
      _ ≤ ∑ _d ∈ Icc 1 D, (M : ℝ) := sum_le_sum fun d _ => hterm d
      _ = _ := by simp
  rw [mobiusDivisorSelectionEnergy_empty, hterminal, hsplit, sum_union hdisj]
  linarith only [hhead]

/-- A uniform positive fraction of the normalized diagonal survives on every power mesh. -/
theorem exists_powerMesh_dilationTailDiagonal_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ J₀ : ℕ, 2 ≤ J₀ ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ j : ℕ, J₀ ≤ j → c ≤ mobiusDivisorDilationTailDiagonal (j ^ m) (j ^ (m - 1)) := by
  obtain ⟨c, hc, N, _hN, hQ⟩ := exists_mobiusDivisorDiagonal_quadratic_lower
  refine ⟨c / 2, by positivity, max N (max 2 ⌈2 / c⌉₊), by omega, fun m hm j hj => ?_⟩
  have hjN : N ≤ j := (le_max_left _ _).trans hj
  have hj2 : 2 ≤ j := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hj
  have hjceil : ⌈2 / c⌉₊ ≤ j := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hj
  have hratio : 2 / c ≤ (j : ℝ) :=
    (Nat.le_ceil (2 / c)).trans (by exact_mod_cast hjceil)
  have h2 : 2 ≤ (j : ℝ) * c := (div_le_iff₀ hc).mp hratio
  let M := j ^ m
  let D := j ^ (m - 1)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hprodN : M = j * D := by
    dsimp [M, D]
    rw [← pow_succ', Nat.sub_add_cancel hm]
  have hprod : (M : ℝ) = (j : ℝ) * D := by exact_mod_cast hprodN
  have htwice : 2 * D ≤ M := by rw [hprodN]; gcongr
  have hDM : D < M := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNM : N ≤ M := hjN.trans (le_self_pow (by omega : 1 ≤ j) (by omega : m ≠ 0))
  have hDsmall : 2 * (D : ℝ) ≤ c * M := by
    calc
      _ ≤ ((j : ℝ) * c) * D := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg D)
      _ = _ := by rw [hprod]; ring
  have hcost : (D : ℝ) * M ≤ (c / 2) * (M : ℝ) ^ 2 := by
    calc
      _ ≤ (c / 2 * M) * M := mul_le_mul_of_nonneg_right (by linarith) hM0.le
      _ = _ := by ring
  have hfull := hQ M hNM
  have hsplit := mobiusDivisorDiagonal_le_head_cost_add_tail hDM
  change c / 2 ≤ (∑ d ∈ Icc (D + 1) (M - 1), (mobiusDivisorDilationChannel M d) ^ 2) / (M : ℝ) ^ 2
  apply (le_div_iff₀ (sq_pos_of_pos hM0)).mpr
  linarith

/-- The uniform channel ceiling bounds the tail absolute mass at its natural scale. -/
theorem mobiusDivisorDilationTailAbsoluteMass_le (M D : ℕ) :
    mobiusDivisorDilationTailAbsoluteMass M D ≤ (3 / 5 : ℝ) * M * Real.sqrt M := by
  apply le_trans _ (mobiusDivisorAbsoluteMass_le M)
  unfold mobiusDivisorDilationTailAbsoluteMass mobiusDivisorAbsoluteMass
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have := mem_Icc.mp hd
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intros; exact abs_nonneg _

/-- The actual diagonal cannot exceed square-root scale times its absolute tail mass. -/
theorem mobiusDivisorDilationTail_sq_sum_le_sqrt_mul_absoluteMass (M D : ℕ) :
    (∑ d ∈ Icc (D + 1) (M - 1), (mobiusDivisorDilationChannel M d) ^ 2) ≤
      Real.sqrt M * mobiusDivisorDilationTailAbsoluteMass M D := by
  unfold mobiusDivisorDilationTailAbsoluteMass
  rw [mul_sum]
  apply sum_le_sum
  intro d _
  have h := mul_le_mul_of_nonneg_right (channel_abs_le_sqrt M d)
    (abs_nonneg (mobiusDivisorDilationChannel M d))
  simpa only [← pow_two, sq_abs] using h

/-- Deleting the sublinear head preserves the full absolute source-mass scale. -/
theorem exists_powerMesh_dilationTailAbsoluteMass_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ J₀ : ℕ, 2 ≤ J₀ ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ j : ℕ, J₀ ≤ j →
        c * ((j ^ m : ℕ) : ℝ) * Real.sqrt (j ^ m : ℕ) ≤
          mobiusDivisorDilationTailAbsoluteMass (j ^ m) (j ^ (m - 1)) := by
  obtain ⟨c, hc, J₀, hJ₀, hdiag⟩ := exists_powerMesh_dilationTailDiagonal_lower
  refine ⟨c, hc, J₀, hJ₀, fun m hm j hj => ?_⟩
  have hj2 : 2 ≤ j := hJ₀.trans hj
  let M := j ^ m
  let D := j ^ (m - 1)
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hQ : c * (M : ℝ) ^ 2 ≤ ∑ d ∈ Icc (D + 1) (M - 1),
      (mobiusDivisorDilationChannel M d) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hM)).mp (hdiag m hm j hj)
  have h := hQ.trans (mobiusDivisorDilationTail_sq_sum_le_sqrt_mul_absoluteMass M D)
  have heq : c * (M : ℝ) ^ 2 = Real.sqrt M * (c * M * Real.sqrt M) := by
    calc
      _ = c * M * (Real.sqrt M) ^ 2 := by rw [Real.sq_sqrt hM.le]; ring
      _ = _ := by ring
  rw [heq] at h
  exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hM)).mp h

/-- Cumulative square of the absolute high-dilation envelope on an exact power mesh. -/
def mobiusDivisorDilationPositiveMeshEnergy (m J : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 J,
    (mobiusDivisorDilationTailAbsoluteMass (j ^ m) (j ^ (m - 1)) / ((j ^ m : ℕ) : ℝ)) ^ 2

private theorem normalized_tail_absoluteMass_sq_le {M : ℕ} (hM : 0 < M) (D : ℕ) :
    (mobiusDivisorDilationTailAbsoluteMass M D / M) ^ 2 ≤ (9 / 25 : ℝ) * M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hU : 0 ≤ mobiusDivisorDilationTailAbsoluteMass M D := sum_nonneg fun _ _ => abs_nonneg _
  have hnorm : mobiusDivisorDilationTailAbsoluteMass M D / M ≤ (3 / 5 : ℝ) * Real.sqrt M := by
    apply (div_le_iff₀ hMR).mpr
    have h := mobiusDivisorDilationTailAbsoluteMass_le M D
    nlinarith
  have h := (sq_le_sq₀ (div_nonneg hU hMR.le) (by positivity)).mpr hnorm
  simpa only [mul_pow, Real.sq_sqrt hMR.le, show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] using h

private theorem normalized_tail_absoluteMass_sq_lower {M D : ℕ} {c : ℝ}
    (hM : 0 < M) (hc : 0 ≤ c)
    (hU : c * M * Real.sqrt M ≤ mobiusDivisorDilationTailAbsoluteMass M D) :
    c ^ 2 * M ≤ (mobiusDivisorDilationTailAbsoluteMass M D / M) ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnonneg : 0 ≤ mobiusDivisorDilationTailAbsoluteMass M D := sum_nonneg fun _ _ => abs_nonneg _
  have hnorm : c * Real.sqrt M ≤ mobiusDivisorDilationTailAbsoluteMass M D / M := by
    apply (le_div_iff₀ hMR).mpr
    nlinarith
  have h := (sq_le_sq₀ (by positivity) (div_nonneg hnonneg hMR.le)).mpr hnorm
  simpa only [mul_pow, Real.sq_sqrt hMR.le] using h

/-- The positive envelope has the expected upper exponent without an arithmetic premise. -/
theorem mobiusDivisorDilationPositiveMeshEnergy_le (m J : ℕ) :
    mobiusDivisorDilationPositiveMeshEnergy m J ≤ (9 / 25 : ℝ) * (J : ℝ) ^ (m + 1) := by
  by_cases hJ : 2 ≤ J
  · have hterm : ∀ j ∈ Icc 2 J,
        (mobiusDivisorDilationTailAbsoluteMass (j ^ m) (j ^ (m - 1)) / ((j ^ m : ℕ) : ℝ)) ^ 2 ≤
          (9 / 25 : ℝ) * (J : ℝ) ^ m := by
      intro j hj
      have hj' := mem_Icc.mp hj
      have hj2 : 2 ≤ j := hj'.1
      calc
        _ ≤ (9 / 25 : ℝ) * ((j ^ m : ℕ) : ℝ) :=
          normalized_tail_absoluteMass_sq_le (by positivity : 0 < j ^ m) (j ^ (m - 1))
        _ = (9 / 25 : ℝ) * (j : ℝ) ^ m := by rw [Nat.cast_pow]
        _ ≤ (9 / 25 : ℝ) * (J : ℝ) ^ m := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg j)
            (show (j : ℝ) ≤ J by exact_mod_cast hj'.2) m) (by norm_num)
    unfold mobiusDivisorDilationPositiveMeshEnergy
    calc
      _ ≤ ∑ _j ∈ Icc 2 J, (9 / 25 : ℝ) * (J : ℝ) ^ m := sum_le_sum hterm
      _ = ((Icc 2 J).card : ℝ) * ((9 / 25 : ℝ) * (J : ℝ) ^ m) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (J : ℝ) * ((9 / 25 : ℝ) * (J : ℝ) ^ m) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show (Icc 2 J).card ≤ J by rw [Nat.card_Icc]; omega)
      _ = _ := by rw [pow_succ]; ring
  · have hempty : Icc 2 J = ∅ := Icc_eq_empty_of_lt (by omega)
    simp only [mobiusDivisorDilationPositiveMeshEnergy, hempty, sum_empty]
    positivity

/-- The exact positive-envelope scale is `J^(m+1)` on every positive power mesh. -/
theorem exists_mobiusDivisorDilationPositiveMeshEnergy_two_sided {m : ℕ} (hm : 1 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ J₁ : ℕ, 2 ≤ J₁ ∧ ∀ J : ℕ, J₁ ≤ J →
      c * (J : ℝ) ^ (m + 1) ≤ mobiusDivisorDilationPositiveMeshEnergy m J ∧
      mobiusDivisorDilationPositiveMeshEnergy m J ≤ (9 / 25 : ℝ) * (J : ℝ) ^ (m + 1) := by
  obtain ⟨c, hc, J₀, hJ₀, hmass⟩ := exists_powerMesh_dilationTailAbsoluteMass_lower
  refine ⟨c ^ 2 / (2 : ℝ) ^ (m + 1), by positivity, 2 * J₀, by omega, fun J hJ =>
    ⟨?_, mobiusDivisorDilationPositiveMeshEnergy_le m J⟩⟩
  let L := Icc (J / 2 + 1) J
  have hsubset : L ⊆ Icc 2 J := by
    intro j hj
    have := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : (J : ℝ) / 2 ≤ (L.card : ℝ) := by
    have hnat : J ≤ 2 * L.card := by dsimp [L]; rw [Nat.card_Icc]; omega
    have hcast : (J : ℝ) ≤ 2 * L.card := by exact_mod_cast hnat
    linarith
  have hterm : ∀ j ∈ L, c ^ 2 * ((J : ℝ) / 2) ^ m ≤
      (mobiusDivisorDilationTailAbsoluteMass (j ^ m) (j ^ (m - 1)) / ((j ^ m : ℕ) : ℝ)) ^ 2 := by
    intro j hj
    have hj' := mem_Icc.mp hj
    have hj0 : J₀ ≤ j := by omega
    have hj2 : 2 ≤ j := hJ₀.trans hj0
    have hhalf : (J : ℝ) / 2 ≤ j := by
      have hnat : J ≤ 2 * j := by omega
      have hcast : (J : ℝ) ≤ 2 * j := by exact_mod_cast hnat
      linarith
    have h := normalized_tail_absoluteMass_sq_lower (by positivity : 0 < j ^ m) hc.le
      (hmass m hm j hj0)
    calc
      _ ≤ c ^ 2 * (j : ℝ) ^ m := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hhalf m) (sq_nonneg c)
      _ ≤ _ := by simpa only [Nat.cast_pow] using h
  calc
    (c ^ 2 / (2 : ℝ) ^ (m + 1)) * (J : ℝ) ^ (m + 1) =
        c ^ 2 * ((J : ℝ) / 2) ^ (m + 1) := by rw [div_pow]; ring
    _ = ((J : ℝ) / 2) * (c ^ 2 * ((J : ℝ) / 2) ^ m) := by rw [pow_succ]; ring
    _ ≤ (L.card : ℝ) * (c ^ 2 * ((J : ℝ) / 2) ^ m) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ _j ∈ L, c ^ 2 * ((J : ℝ) / 2) ^ m := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ L,
        (mobiusDivisorDilationTailAbsoluteMass (j ^ m) (j ^ (m - 1)) / ((j ^ m : ℕ) : ℝ)) ^ 2 :=
      sum_le_sum hterm
    _ ≤ mobiusDivisorDilationPositiveMeshEnergy m J :=
      sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)

/-- Even the larger exponent `m` is impossible for the positive envelope. -/
theorem not_mobiusDivisorDilationPositiveMeshEnergy_le_pow {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ J : ℕ, N₀ ≤ J →
      mobiusDivisorDilationPositiveMeshEnergy m J ≤ C * (J : ℝ) ^ m := by
  rintro ⟨C, N₀, hC⟩
  obtain ⟨c, hc, J₀, hJ₀, hbound⟩ := exists_mobiusDivisorDilationPositiveMeshEnergy_two_sided hm
  let J := max (max J₀ N₀) ⌈(C + 1) / c⌉₊
  have hJ0 : J₀ ≤ J := (le_max_left _ _).trans (le_max_left _ _)
  have hJN : N₀ ≤ J := (le_max_right _ _).trans (le_max_left _ _)
  have hJ2 : 2 ≤ J := hJ₀.trans hJ0
  have hratio : (C + 1) / c ≤ (J : ℝ) :=
    (Nat.le_ceil ((C + 1) / c)).trans (by exact_mod_cast (le_max_right (max J₀ N₀) ⌈(C + 1) / c⌉₊))
  have hlarge : C < c * J := by have := (div_le_iff₀ hc).mp hratio; nlinarith
  have h := ((hbound J hJ0).1).trans (hC J hJN)
  rw [pow_succ] at h
  have hprod := mul_pos (sub_pos.mpr hlarge) (show (0 : ℝ) < (J : ℝ) ^ m by positivity)
  nlinarith only [h, hprod]

/-- Every compatible positive probability weighting pays at least absolute mass squared. -/
theorem mobiusDivisorDilationTailAbsoluteMass_sq_le_weightedEnergy
    (M D : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ Icc (D + 1) (M - 1), 0 ≤ w d)
    (hsum : ∑ d ∈ Icc (D + 1) (M - 1), w d = 1)
    (hsupport : ∀ d ∈ Icc (D + 1) (M - 1), w d = 0 → mobiusDivisorDilationChannel M d = 0) :
    (mobiusDivisorDilationTailAbsoluteMass M D) ^ 2 ≤
      ∑ d ∈ Icc (D + 1) (M - 1), (mobiusDivisorDilationChannel M d) ^ 2 / w d := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc (D + 1) (M - 1))
    (r := fun d => |mobiusDivisorDilationChannel M d|)
    (f := fun d => (mobiusDivisorDilationChannel M d) ^ 2 / w d) (g := w)
    (fun d hd => div_nonneg (sq_nonneg _) (hw d hd)) hw ?_
  · simpa only [hsum, mul_one, mobiusDivisorDilationTailAbsoluteMass] using h
  · intro d hd
    by_cases hz : w d = 0
    · simp [hz, hsupport d hd hz]
    · rw [div_mul_cancel₀ _ hz, sq_abs]

/-- Absolute-amplitude weights attain the optimal positive normalization cost. -/
theorem mobiusDivisorDilationTailAbsoluteMass_optimal_weights (M D : ℕ)
    (hU : 0 < mobiusDivisorDilationTailAbsoluteMass M D) :
    let w := fun d => |mobiusDivisorDilationChannel M d| / mobiusDivisorDilationTailAbsoluteMass M D
    (∀ d ∈ Icc (D + 1) (M - 1), 0 ≤ w d) ∧
      (∑ d ∈ Icc (D + 1) (M - 1), w d = 1) ∧
      (∀ d ∈ Icc (D + 1) (M - 1), w d = 0 → mobiusDivisorDilationChannel M d = 0) ∧
      (∑ d ∈ Icc (D + 1) (M - 1), (mobiusDivisorDilationChannel M d) ^ 2 / w d) =
        (mobiusDivisorDilationTailAbsoluteMass M D) ^ 2 := by
  dsimp only
  refine ⟨fun _ _ => div_nonneg (abs_nonneg _) hU.le, ?_, ?_, ?_⟩
  · rw [← sum_div]
    exact div_self hU.ne'
  · intro d hd hz
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hU.ne')
  · have he (d : ℕ) : (mobiusDivisorDilationChannel M d) ^ 2 /
        (|mobiusDivisorDilationChannel M d| / mobiusDivisorDilationTailAbsoluteMass M D) =
          |mobiusDivisorDilationChannel M d| * mobiusDivisorDilationTailAbsoluteMass M D := by
      by_cases hz : mobiusDivisorDilationChannel M d = 0
      · simp [hz]
      · have hn := abs_ne_zero.mpr hz
        rw [← sq_abs (mobiusDivisorDilationChannel M d)]
        field_simp
    simp_rw [he]
    rw [← sum_mul]
    change mobiusDivisorDilationTailAbsoluteMass M D * mobiusDivisorDilationTailAbsoluteMass M D = _
    ring

end RHTower
