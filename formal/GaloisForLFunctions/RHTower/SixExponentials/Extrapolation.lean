import GaloisForLFunctions.RHTower.SixExponentials.Auxiliary
import GaloisForLFunctions.RHTower.BakerProof.MultipointSchwarz
import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryArithmetic

/-!
# Six exponentials: the Schwarz step and the Liouville step

If the auxiliary function vanishes at the `M³` sample points of level `M`, the multipoint
Schwarz lemma on the disc of radius `4(M+1)Y` bounds it at every point of modulus at most
`(M+1)Y` by `(2/3)^{M³} · L² B exp(4 L X Y (M+1))`.  If it does not vanish at a sample point of
level `M`, the Liouville inequality for the nonzero algebraic integer `c^{6LM} F(s_m)` gives the
lower bound `1 ≤ H^{6LM} ‖F(s_m)‖ (L² H^{6LM} B)^{d−1}`.
-/

open Complex Finset NumberField

namespace GaloisForLFunctions.RHTower.SixExponentials

namespace AlgData

variable (A : AlgData)

/-- The sample points of level `M` as a finite set. -/
noncomputable def samples (M : ℕ) : Finset ℂ :=
  Finset.univ.image (fun m : Fin 3 → Fin M => A.toData.pt m)

theorem card_samples (M : ℕ) : (A.samples M).card = M ^ 3 := by
  unfold samples
  rw [Finset.card_image_of_injective _ (A.toData.pt_injective M), Finset.card_univ]
  simp

theorem norm_le_of_mem_samples {M : ℕ} {c : ℂ} (hc : c ∈ A.samples M) : ‖c‖ ≤ M * A.toData.Y := by
  unfold samples at hc
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hc
  exact A.toData.norm_pt_le m

/-- **Schwarz step.**  Vanishing on the level-`M` samples gives a small bound on the disc of
radius `(M+1)Y`. -/
theorem norm_F_le_of_vanishing {L M : ℕ} (ξ : Fin L × Fin L → 𝓞 A.K) {B : ℝ}
    (hB : ∀ l, house (algebraMap (𝓞 A.K) A.K (ξ l)) ≤ B) (hB0 : 0 ≤ B)
    (hvan : ∀ m : Fin 3 → Fin M, A.F ξ (A.toData.pt m) = 0)
    {z : ℂ} (hz : ‖z‖ ≤ (M + 1) * A.toData.Y) :
    ‖A.F ξ z‖ ≤ (2 / 3 : ℝ) ^ (M ^ 3)
      * ((L * L) * (B * Real.exp (L * A.toData.X * (4 * (M + 1) * A.toData.Y)))) := by
  have hY := A.toData.Y_pos
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  set R : ℝ := 4 * (M + 1) * A.toData.Y with hR
  have hRpos : 0 < R := by positivity
  set Mb : ℝ := (L * L) * (B * Real.exp (L * A.toData.X * R)) with hMb
  set Db : ℝ := (3 * (M + 1) * A.toData.Y) ^ (M ^ 3) with hDb
  have hDpos : 0 < Db := by positivity
  have horder : ∀ c ∈ A.samples M, ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt (A.F ξ) c := by
    intro c hc
    unfold samples at hc
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hc
    have h0 : analyticOrderAt (A.F ξ) (A.toData.pt m) ≠ 0 := by
      rw [Ne, (A.analyticAt_F ξ _).analyticOrderAt_eq_zero]
      push Not
      exact hvan m
    rw [Nat.cast_one]
    exact ENat.one_le_iff_ne_zero.mpr h0
  have hbf : ∀ w ∈ Metric.sphere (0 : ℂ) R, ‖A.F ξ w‖ ≤ Mb := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    have := A.norm_F_le ξ hB w
    rw [hw] at this
    exact this
  have hbfac : ∀ w ∈ Metric.sphere (0 : ℂ) R, Db ≤ ‖∏ c ∈ A.samples M, (w - c) ^ 1‖ := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    rw [norm_prod]
    have hcard := A.card_samples M
    calc Db = ∏ _c ∈ A.samples M, (3 * (M + 1) * A.toData.Y) := by
          rw [Finset.prod_const, hcard]
      _ ≤ ∏ c ∈ A.samples M, ‖(w - c) ^ 1‖ := by
          apply Finset.prod_le_prod
          · intro c _; positivity
          · intro c hc
            rw [pow_one]
            have h1 := A.norm_le_of_mem_samples hc
            have h2 : ‖w‖ - ‖c‖ ≤ ‖w - c‖ := norm_sub_norm_le _ _
            have h3 : (M : ℝ) * A.toData.Y ≤ (M + 1) * A.toData.Y := by nlinarith
            rw [hw, hR] at h2
            linarith
  have hzball : z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, hR]
    nlinarith
  have hmain := BakerProof.multipoint_schwarz_bound (A.F ξ) (A.analyticAt_F ξ) (A.samples M) 1
    horder hRpos hDpos hbf hbfac hzball
  have hprodz : ‖∏ c ∈ A.samples M, (z - c) ^ 1‖ ≤ (2 * (M + 1) * A.toData.Y) ^ (M ^ 3) := by
    rw [norm_prod]
    have hcard := A.card_samples M
    calc ∏ c ∈ A.samples M, ‖(z - c) ^ 1‖ ≤ ∏ _c ∈ A.samples M, (2 * (M + 1) * A.toData.Y) := by
          apply Finset.prod_le_prod
          · intro c _; positivity
          · intro c hc
            rw [pow_one]
            have h1 := A.norm_le_of_mem_samples hc
            have h2 : ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le _ _
            have h3 : (M : ℝ) * A.toData.Y ≤ (M + 1) * A.toData.Y := by nlinarith
            linarith
      _ = (2 * (M + 1) * A.toData.Y) ^ (M ^ 3) := by rw [Finset.prod_const, hcard]
  have hratio : (2 * (M + 1) * A.toData.Y) ^ (M ^ 3) / Db = (2 / 3 : ℝ) ^ (M ^ 3) := by
    rw [hDb, ← div_pow]
    congr 1
    field_simp
  have hMb0 : 0 ≤ Mb := by
    rw [hMb]
    positivity
  calc ‖A.F ξ z‖ ≤ ‖∏ c ∈ A.samples M, (z - c) ^ 1‖ * (Mb / Db) := hmain
    _ ≤ (2 * (M + 1) * A.toData.Y) ^ (M ^ 3) * (Mb / Db) :=
        mul_le_mul_of_nonneg_right hprodz (div_nonneg hMb0 hDpos.le)
    _ = ((2 * (M + 1) * A.toData.Y) ^ (M ^ 3) / Db) * Mb := by ring
    _ = (2 / 3 : ℝ) ^ (M ^ 3) * Mb := by rw [hratio]

/-- **Liouville step.**  A nonzero value at a sample point of level `M` is bounded below. -/
theorem one_le_of_F_ne_zero {L M : ℕ} (ξ : Fin L × Fin L → 𝓞 A.K) {B : ℝ}
    (hB : ∀ l, house (algebraMap (𝓞 A.K) A.K (ξ l)) ≤ B) (hB0 : 0 ≤ B) (m : Fin 3 → Fin M)
    (hne : A.F ξ (A.toData.pt m) ≠ 0) :
    1 ≤ A.Hb ^ (6 * L * M) * ‖A.F ξ (A.toData.pt m)‖
      * ((L * L) * (A.Hb ^ (6 * L * M) * B)) ^ (Module.finrank ℚ A.K - 1) := by
  have hH0 : 0 ≤ A.Hb := le_trans zero_le_one A.one_le_Hb
  have hσ := A.σ_sval L M ξ m
  set Xv := A.sval L M ξ m with hXv
  have hX0 : Xv ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hσ
    have hc : (A.scale : ℂ) ^ (6 * L * M) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast A.scale_ne_zero)
    rcases mul_eq_zero.mp hσ.symm with h1 | h1
    · exact hc h1
    · exact hne h1
  have hliou : ¬ (‖A.σ (algebraMap (𝓞 A.K) A.K Xv)‖
      * house (algebraMap (𝓞 A.K) A.K Xv) ^ (Module.finrank ℚ A.K - 1) < 1) := by
    intro hsmall
    exact hX0 (BakerProof.algebraicInteger_eq_zero_of_distinguished_mul_house_pow_lt_one
      A.σ Xv hsmall)
  push Not at hliou
  have hnormσ : ‖A.σ (algebraMap (𝓞 A.K) A.K Xv)‖
      ≤ A.Hb ^ (6 * L * M) * ‖A.F ξ (A.toData.pt m)‖ := by
    rw [hσ, norm_mul, norm_pow, Complex.norm_intCast]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) A.abs_scale_le_Hb _
  have hhouse : house (algebraMap (𝓞 A.K) A.K Xv) ^ (Module.finrank ℚ A.K - 1)
      ≤ ((L * L) * (A.Hb ^ (6 * L * M) * B)) ^ (Module.finrank ℚ A.K - 1) :=
    pow_le_pow_left₀ (house_nonneg _) (A.house_sval_le L M ξ hB m) _
  calc (1 : ℝ) ≤ ‖A.σ (algebraMap (𝓞 A.K) A.K Xv)‖
        * house (algebraMap (𝓞 A.K) A.K Xv) ^ (Module.finrank ℚ A.K - 1) := hliou
    _ ≤ (A.Hb ^ (6 * L * M) * ‖A.F ξ (A.toData.pt m)‖)
        * ((L * L) * (A.Hb ^ (6 * L * M) * B)) ^ (Module.finrank ℚ A.K - 1) :=
        mul_le_mul hnormσ hhouse (pow_nonneg (house_nonneg _) _)
          (mul_nonneg (pow_nonneg hH0 _) (norm_nonneg _))

end AlgData

end GaloisForLFunctions.RHTower.SixExponentials
