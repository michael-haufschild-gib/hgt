import GaloisForLFunctions.HTGeometry.FiniteDetuningTensorMajorantWindowLaw

/-! # Finite-window filling of a projective phase cube

The positive tensor Fejér kernel has a positive constant Fourier coefficient.
When one coordinate misses the target, the uniform Fejér error bounds the
entire product. The finite detuning floor bounds the translated averaging time.
-/
open Set Real MeasureTheory intervalIntegral
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem tensor_mean_lower {d N : ℕ} {ρ δ T : ℝ} (hρ : 0 < ρ) (hπ : ρ ≤ π)
    (hδ : 0 < δ) (hT : 0 < T) (c ω : Fin d → ℝ) (u : ℝ)
    (hm : ∀ k ∈ nonconstantPacketIndexSet N d, δ ≤ |packetFreq ω k|) :
    let μ := (ρ/(2*π) + periodicTentFejerError N ρ)^d
    μ - ((nonconstantPacketIndexSet N d).card:ℝ)*μ*(2/(T*δ)) ≤
      (1/T)*∫ t in u..(u+T), periodicProductFejerMajorant N ρ c (fun j => t*ω j) := by
  classical
  intro μ
  let S := nonconstantPacketIndexSet N d
  let e := periodicTentFejerError N ρ
  have he : 0 < e := periodicTentFejerError_pos N hρ
  have hbase : 0 ≤ ρ/(2*π)+e := add_nonneg (div_nonneg hρ.le (by positivity)) he.le
  have hμ : 0 ≤ μ := pow_nonneg hbase _
  have hA (k : {k // k ∈ S}) : ‖majorantPacketAmp N ρ e c k.val‖ ≤ μ := by
    apply (norm_majorantPacketAmp_le N hρ hπ he.le c k.val).trans
    apply pow_le_pow_left₀ (mul_nonneg (by positivity) hbase)
    apply mul_le_of_le_one_left hbase
    exact inv_le_one_of_one_le₀ (by have hn : (0:ℝ) ≤ N := Nat.cast_nonneg _; linarith only [hn])
  have h := norm_window_mean_sub_const_le (ι := {k // k ∈ S}) (μ:ℂ)
    (fun k => majorantPacketAmp N ρ e c k.val) (fun k => packetFreq ω k.val)
    hδ (fun k => hm _ k.property) hμ hA hT u
  let F (t : ℝ) := periodicProductFejerMajorant N ρ c (fun j => t*ω j)
  have hpoint (t : ℝ) : (F t:ℂ) = (μ:ℂ) + ∑ k : {k // k ∈ S},
      majorantPacketAmp N ρ e c k.val * Complex.exp ((t:ℂ)*(packetFreq ω k.val:ℂ)*Complex.I) := by
    rw [show F t = periodicProductFejerMajorant N ρ c (fun j => t*ω j) from rfl,
      periodicProductFejerMajorant_eq_const_add N hρ hπ]
    congr 1
    rw [Finset.sum_coe_sort S (fun k => majorantPacketAmp N ρ e c k * Complex.exp ((t:ℂ)*(packetFreq ω k:ℂ)*Complex.I))]
    exact Finset.sum_congr rfl fun k _ => majorantPacketMode_linearPhase N ρ e c ω k t
  have hi := intervalIntegral.integral_congr (μ := volume) (a := u) (b := u+T)
    (fun t _ => hpoint t)
  rw [← hi] at h
  let Z := (1/(T:ℂ))*(∫ t in u..(u+T), (F t:ℂ))-(μ:ℂ)
  have ht : |Z.re| ≤ (S.card:ℝ)*μ*(2/(T*δ)) :=
    (Complex.abs_re_le_norm Z).trans (by simpa only [Fintype.card_coe] using h)
  have hl := (abs_le.mp ht).1
  have hr : Z.re = (1/T)*(∫ t in u..(u+T), F t)-μ := by
    dsimp only [Z,Complex.sub_re,Complex.ofReal_re]
    rw [re_window_mean_ofReal (continuous_periodicProductFejerMajorant N ρ c ω) hT u]
  rw [hr] at hl
  linarith only [hl]

private theorem tensor_outside_cube {d N : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (c θ : Fin d → ℝ)
    (hmiss : ∃ j, ρ ≤ turnDist (θ j-c j)) (hsmall : periodicTentFejerError N ρ ≤ 1/2) :
    periodicProductFejerMajorant N ρ c θ ≤ 2*periodicTentFejerError N ρ*2^d := by
  classical
  obtain ⟨i,hi⟩ := hmiss
  let e := periodicTentFejerError N ρ
  let F (j : Fin d) := fejerConv N (perTent ρ) (θ j-c j)+e
  have he := periodicTentFejerError_pos N hρ
  have hpos j : 0 ≤ F j := (perTent_nonneg _ _).trans (perTent_le_fejerConv_add_error N hρ _)
  have hu (j) : F j ≤ perTent ρ (θ j-c j) + 2*e := by
    have ha := (abs_le.mp (abs_fejerConv_perTent_sub_le N hρ (θ j-c j))).2
    change _ ≤ e at ha
    dsimp only [F]; linarith only [ha]
  have htwo j : F j ≤ 2 := by
    have h1 := perTent_le_one hρ (θ j-c j)
    change e ≤ 1/2 at hsmall
    linarith only [hu j,h1,hsmall]
  have hz : perTent ρ (θ i-c i) = 0 := by
    rw [perTent,max_eq_right]
    linarith only [(one_le_div hρ).mpr hi]
  have hrest : ∏ j ∈ Finset.univ.erase i, F j ≤ (2:ℝ)^d := by
    refine (Finset.prod_le_prod (fun j _ => hpos j) (fun j _ => htwo j)).trans ?_
    rw [Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin d)
  change ∏ j, F j ≤ _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),mul_comm]
  apply mul_le_mul _ hrest (Finset.prod_nonneg fun j _ => hpos j) (by positivity)
  simpa only [hz,zero_add] using hu i

/-- Any translated interval of this length hits every phase target to radius
ρ when all retained nonconstant phase frequencies are at least δ in modulus. -/
theorem finite_detuning_phase_cube_hit {d N : ℕ} {ρ δ : ℝ} (hρ : 0 < ρ) (hπ : ρ ≤ π)
    (hδ : 0 < δ) (ω : Fin d → ℝ) (hm : ∀ k ∈ nonconstantPacketIndexSet N d, δ ≤ |packetFreq ω k|)
    (he : periodicTentFejerError N ρ ≤ 1/2)
    (hsmall : 2*periodicTentFejerError N ρ*(2:ℝ)^d < (ρ/(2*π))^d/2)
    (u : ℝ) (c : Fin d → ℝ) :
    ∃ t ∈ Icc u (u+8*(((nonconstantPacketIndexSet N d).card:ℝ)+1)/δ),
      ∀ j, turnDist (t*ω j-c j) < ρ := by
  let b : ℝ := (nonconstantPacketIndexSet N d).card
  let T := 8*(b+1)/δ
  let base := ρ/(2*π)
  let e := periodicTentFejerError N ρ
  let μ := (base+e)^d
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hT : 0 < T := div_pos (mul_pos (by norm_num) (by linarith only [hb])) hδ
  have hepos : 0 < e := periodicTentFejerError_pos N hρ
  have hbase : 0 < base := div_pos hρ (by positivity)
  have hμ : 0 < μ := pow_pos (add_pos hbase hepos) _
  have hB : base^d ≤ μ := pow_le_pow_left₀ hbase.le (le_add_of_nonneg_right hepos.le) _
  have hcost : b*μ*(2/(T*δ)) ≤ μ/4 := by
    have ht : T*δ = 8*(b+1) := div_mul_cancel₀ _ hδ.ne'
    rw [ht,← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 8*(b+1) by positivity)).mpr
    linarith only [hμ]
  have hav := tensor_mean_lower hρ hπ hδ hT c ω u hm
  change μ-b*μ*(2/(T*δ)) ≤ _ at hav
  by_contra! hmiss
  have bound (t) (ht : t ∈ Icc u (u+T)) :
      periodicProductFejerMajorant N ρ c (fun j => t*ω j) ≤ 2*e*2^d :=
    tensor_outside_cube hρ c _ (hmiss t ht) he
  have hint := intervalIntegral.integral_mono_on (μ := volume) (show u ≤ u+T by linarith only [hT])
    ((continuous_periodicProductFejerMajorant N ρ c ω).intervalIntegrable _ _) intervalIntegrable_const bound
  rw [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left] at hint
  have hupper := mul_le_mul_of_nonneg_left hint (show 0 ≤ 1/T by positivity)
  have ht : (1/T)*(T*(2*e*2^d)) = 2*e*2^d := by field_simp
  rw [ht] at hupper
  change 2*e*2^d < base^d/2 at hsmall
  linarith only [hav,hcost,hupper,hsmall,hB,hμ]

/-- Fourier cutoff at which one missed coordinate makes the tensor Fejér
kernel smaller than half its constant coefficient. -/
def phaseCubeFourierCutoff (d : ℕ) (ρ : ℝ) : ℕ :=
  ⌈(2*π/(ρ*((ρ/(4*π))^d/16)))^2⌉₊

private theorem phaseCubeFourierCutoff_spec (d : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hπ : ρ ≤ π) :
    let M := phaseCubeFourierCutoff d ρ
    periodicTentFejerError M ρ ≤ 1/2 ∧
      2*periodicTentFejerError M ρ*(2:ℝ)^d < (ρ/(2*π))^d/2 := by
  intro M
  let b := ρ/(4*π)
  let a := b^d/16
  let L := 2*π/(ρ*a)
  have hb : 0 < b := div_pos hρ (by positivity)
  have hb1 : b ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hπ,Real.pi_pos])
  have ha : 0 < a := div_pos (pow_pos hb d) (by norm_num)
  have ha1 : a ≤ 1/16 := div_le_div_of_nonneg_right (pow_le_one₀ hb.le hb1) (by norm_num)
  have hL : 0 < L := div_pos (by positivity) (mul_pos hρ ha)
  have hM : L^2 ≤ (M:ℝ) := Nat.le_ceil _
  have hrt : L ≤ Real.sqrt ((M:ℝ)+1) := (Real.le_sqrt hL.le (by positivity)).mpr (by linarith only [hM])
  have hmul : 2*π ≤ Real.sqrt ((M:ℝ)+1)*(ρ*a) := (div_le_iff₀ (mul_pos hρ ha)).mp hrt
  have he : periodicTentFejerError M ρ ≤ a := by
    rw [periodicTentFejerError]
    have hs : 0 < Real.sqrt ((M:ℝ)+1) := by positivity
    rw [show 1/ρ*(2*π/Real.sqrt ((M:ℝ)+1)) = 2*π/(Real.sqrt ((M:ℝ)+1)*ρ) by ring]
    apply (div_le_iff₀ (mul_pos hs hρ)).mpr
    linarith only [hmul]
  refine ⟨he.trans (by linarith only [ha1]),?_⟩
  have h2 : b*2 = ρ/(2*π) := by dsimp [b]; ring
  rw [← h2,mul_pow]
  have hprice : 2*a*(2:ℝ)^d < b^d*2^d/2 := by
    dsimp only [a]
    have hpos : 0 < b^d*(2:ℝ)^d := mul_pos (pow_pos hb _) (by positivity)
    linarith only [hpos]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity)).trans_lt hprice

/-- An explicit horizon for every target and time origin from a lower bound
on the finite, fully specified set of retained frequencies. -/
theorem phaseCube_hit_at_calibrated_cutoff {d : ℕ} {ρ δ : ℝ} (hρ : 0 < ρ) (hπ : ρ ≤ π)
    (hδ : 0 < δ) (ω : Fin d → ℝ)
    (hm : ∀ k ∈ nonconstantPacketIndexSet (phaseCubeFourierCutoff d ρ) d, δ ≤ |packetFreq ω k|)
    (u : ℝ) (c : Fin d → ℝ) :
    ∃ t ∈ Icc u (u+8*(((nonconstantPacketIndexSet (phaseCubeFourierCutoff d ρ) d).card:ℝ)+1)/δ),
      ∀ j, turnDist (t*ω j-c j) < ρ := by
  obtain ⟨he,hsmall⟩ := phaseCubeFourierCutoff_spec d hρ hπ
  exact finite_detuning_phase_cube_hit hρ hπ hδ ω hm he hsmall u c

#print axioms phaseCube_hit_at_calibrated_cutoff

#print axioms finite_detuning_phase_cube_hit
end
end GaloisForLFunctions.HTGeometry
