import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitExcursion
import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw

/-! # Extending single-target occupation estimates to circuit windows at fixed error -/
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Cover a circuit visit by a gate-net target and a time grid point, then
sum the single-target occupation bound over both finite sets. -/
theorem circuit_window_occupation_at_error {n d : ℕ}
    (H : selfAdjoint (Reg n))
    (ε : ℝ) (hε : ε ≤ 1/8) {S : ℝ} (hh : ∀ (W : Reg n) (offset A T : ℝ), 0 ≤ T →
      (2:ℝ)^d * volume.real
        ({t | ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution H.val (t+offset) - c • W‖ ≤ 2/5}
          ∩ Icc A (A+T)) ≤ T+S) :
    ∀ (s : ℕ) (W mesh : ℝ), 0 < mesh → ‖(H : Reg n)‖*mesh ≤ 1/40 →
      ∀ A T : ℝ, 0 ≤ T →
      (2:ℝ)^d * volume.real ({u | ∃ t ∈ Icc u (u+W), HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t)} ∩ Icc A (A+T)) ≤
        (plateauGridCount W mesh : ℝ) * ((atMostQuarterCircuitNet n s).card : ℝ) * (T+S) := by
  classical
  intro s W mesh hm hs A T hT
  let N := plateauGridCount W mesh
  let net := atMostQuarterCircuitNet n s
  let I := Fin N × {U // U ∈ net}
  let τ (j : Fin N) := (j.val : ℝ)*mesh
  let f (i : I) : Set ℝ := {u | ∃ c : ℂ, ‖c‖ = 1 ∧
    ‖unitaryEvolution (H : Reg n) (u+τ i.1) - c • (i.2.val : Reg n)‖ ≤ 2/5} ∩ Icc A (A+T)
  have hsub : {u | ∃ t ∈ Icc u (u+W), HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t)} ∩ Icc A (A+T) ⊆ ⋃ i, f i := by
    rintro u ⟨⟨t,ht,c,hc,C,hC,he⟩,hu⟩
    obtain ⟨j,hj⟩ := exists_plateauGrid_near hm u ht
    obtain ⟨V,hV,hCV⟩ := atMostQuarterCircuitNet_cover C hC
    refine Set.mem_iUnion.mpr ⟨(j,⟨V,hV⟩),⟨⟨c,hc,?_⟩,hu⟩⟩
    have hnear : ‖unitaryEvolution (H : Reg n) t - unitaryEvolution H (u+τ j)‖ ≤ 1/40 :=
      (norm_unitaryEvolution_time_sub_le H.2 _ _).trans
        ((mul_le_mul_of_nonneg_left hj (norm_nonneg _)).trans hs)
    have hnet : ‖c • (C.eval : Reg n) - c • (V : Reg n)‖ ≤ 1/4 := by
      rw [← smul_sub, norm_smul, hc, one_mul]
      simpa only [dist_eq_norm] using hCV
    have ha := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (H : Reg n) (u+τ j))
      (unitaryEvolution (H : Reg n) t) (c • (V : Reg n))
    have hb := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (H : Reg n) t)
      (c • (C.eval : Reg n)) (c • (V : Reg n))
    rw [norm_sub_rev] at hnear
    change ‖unitaryEvolution (H : Reg n) (u+τ j) - c • (V : Reg n)‖ ≤ 2/5
    linarith only [ha,hb,hnear,hnet,he,hε]
  have hf : (⋃ i, f i) ⊆ Icc A (A+T) := Set.iUnion_subset fun _ => inter_subset_right
  have hvol := measureReal_mono (μ := volume) hsub
    (measure_ne_top_of_subset hf measure_Icc_lt_top.ne)
  have hb (i : I) : (2:ℝ)^d * volume.real (f i) ≤ T+S := hh _ _ A T hT
  calc
    _ ≤ (2:ℝ)^d * ∑ i : I, volume.real (f i) :=
      mul_le_mul_of_nonneg_left (hvol.trans (measureReal_iUnion_fintype_le f)) (by positivity)
    _ = ∑ i : I, (2:ℝ)^d * volume.real (f i) := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : I, (T+S) := Finset.sum_le_sum fun i _ => hb i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,I,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul,Nat.cast_mul,N,net]

end
end GaloisForLFunctions.HTGeometry
