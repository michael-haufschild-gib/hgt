import GaloisForLFunctions.BiScaleUncertainty.CappedBlockSupport

/-!
# Whole-coset spheres with paired low-node constraints

Two shared caps encode all opposite-sign low-block constraints. High coordinates
retain their budget inside each whole block. Maximizing the exact capped-block
supports on a quarter circle therefore retains every node and every whole-block
sphere.
-/

set_option autoImplicit false
open Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι : Type*}

/-- The two sign caps lie on the nonnegative unit circle. -/
def pairedCap (t : ℝ) (σ : Bool) : ℝ := if σ then Real.sqrt (1 - t ^ 2) else t

theorem pairedCap_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (σ : Bool) :
    pairedCap t σ ∈ Icc (0 : ℝ) 1 := by
  cases σ
  · exact ht
  · exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩⟩

theorem pairedCap_sq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pairedCap t false ^ 2 + pairedCap t true ^ 2 = 1 := by
  simp only [pairedCap, Bool.false_eq_true, ↓reduceIte]
  rw [Real.sq_sqrt (by nlinarith [ht.1, ht.2] : 0 ≤ 1 - t ^ 2)]
  ring

/-- Exact angular support after compressing each low/high subblock to its norm. -/
def cappedCosetSupport (M : Finset ι) (L H : Bool → ι → ℝ) : ℝ :=
  sSup ((fun t : ℝ => ∑ σ : Bool, ∑ m ∈ M,
    cappedBlockSupport (L σ m) (H σ m) (pairedCap t σ)) '' Icc 0 1)

theorem continuous_cappedCosetSupport (M : Finset ι) :
    Continuous (fun p : (Bool → ι → ℝ) × (Bool → ι → ℝ) => cappedCosetSupport M p.1 p.2) := by
  apply isCompact_Icc.continuous_sSup
  change Continuous (fun p : ((Bool → ι → ℝ) × (Bool → ι → ℝ)) × ℝ =>
    ∑ σ : Bool, ∑ m ∈ M, cappedBlockSupport (p.1.1 σ m) (p.1.2 σ m) (pairedCap p.2 σ))
  apply continuous_finsetSum
  intro σ _
  apply continuous_finsetSum
  intro m _
  exact continuous_cappedBlockSupport.comp
    (show Continuous (fun p : ((Bool → ι → ℝ) × (Bool → ι → ℝ)) × ℝ =>
      (p.1.1 σ m, p.1.2 σ m, pairedCap p.2 σ)) from by
      cases σ <;> dsimp [pairedCap] <;> fun_prop)

theorem cappedCosetSupport_attained (M : Finset ι) (L H : Bool → ι → ℝ) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      cappedCosetSupport M L H =
        ∑ σ : Bool, ∑ m ∈ M, cappedBlockSupport (L σ m) (H σ m) (pairedCap t σ) ∧
      ∀ v ∈ Icc (0 : ℝ) 1,
        (∑ σ : Bool, ∑ m ∈ M, cappedBlockSupport (L σ m) (H σ m) (pairedCap v σ)) ≤
          cappedCosetSupport M L H := by
  have hc : Continuous (fun t : ℝ => ∑ σ : Bool, ∑ m ∈ M,
      cappedBlockSupport (L σ m) (H σ m) (pairedCap t σ)) := by
    apply continuous_finsetSum
    intro σ _
    apply continuous_finsetSum
    intro m _
    exact continuous_cappedBlockSupport.comp
      (show Continuous (fun t : ℝ => (L σ m, H σ m, pairedCap t σ)) from by
        cases σ <;> dsimp [pairedCap] <;> fun_prop)
  obtain ⟨t, ht, he, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_sSup_image_eq_and_ge
      ⟨0, by simp⟩ hc.continuousOn
  exact ⟨t, ht, he, fun v hv => (hmax v hv).trans_eq he.symm⟩

theorem cappedCosetSupport_nonneg (M : Finset ι) (L H : Bool → ι → ℝ)
    (hH : ∀ σ m, 0 ≤ H σ m) : 0 ≤ cappedCosetSupport M L H := by
  obtain ⟨t, _, he, _⟩ := cappedCosetSupport_attained M L H
  rw [he]
  exact Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun m _ => cappedBlockSupport_nonneg (hH σ m)

/-- No loss of whole-block information: imposing paired caps reduces support. -/
theorem cappedCosetSupport_le_independent (M : Finset ι) (L H : Bool → ι → ℝ) :
    cappedCosetSupport M L H ≤ ∑ σ : Bool, ∑ m ∈ M, Real.sqrt ((L σ m) ^ 2 + (H σ m) ^ 2) := by
  obtain ⟨t, ht, he, _⟩ := cappedCosetSupport_attained M L H
  rw [he]
  exact Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun m _ =>
    cappedBlockSupport_le_norm _ _ (pairedCap_mem ht σ)

/-- All opposite-sign constraints reduce exactly to two caps. -/
theorem cappedCosetSupport_bound (M : Finset ι) (hM : M.Nonempty)
    (L H x z : Bool → ι → ℝ) (hH : ∀ σ m, 0 ≤ H σ m)
    (hx : ∀ σ, ∀ m ∈ M, 0 ≤ x σ m)
    (hwhole : ∀ σ, ∀ m ∈ M, (x σ m) ^ 2 + (z σ m) ^ 2 ≤ 1)
    (hpair : ∀ p ∈ M, ∀ q ∈ M, (x false p) ^ 2 + (x true q) ^ 2 ≤ 1) :
    (∑ σ : Bool, ∑ m ∈ M, (L σ m * x σ m + H σ m * z σ m)) ≤
      cappedCosetSupport M L H := by
  obtain ⟨p, hp, hep⟩ := Finset.exists_mem_eq_sup' hM (x false)
  let t := x false p
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    refine ⟨hx false p hp, ?_⟩
    have hw := hwhole false p hp
    dsimp [t]
    nlinarith [sq_nonneg (z false p)]
  have hcap (σ : Bool) (m : ι) (hm : m ∈ M) : x σ m ≤ pairedCap t σ := by
    cases σ
    · change x false m ≤ x false p
      rw [← hep]
      exact Finset.le_sup' (x false) hm
    · apply Real.le_sqrt_of_sq_le
      have h := hpair p hp m hm
      dsimp [t]
      linarith
  obtain ⟨_, _, _, hmax⟩ := cappedCosetSupport_attained M L H
  apply le_trans ?_ (hmax t ht)
  exact Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun m hm =>
    cappedBlockSupport_bound (hH σ m) (pairedCap_mem ht σ) (hx σ m hm)
      (hcap σ m hm) (hwhole σ m hm)

/-- Exact finite-amplitude attainment, including vanishing low/high weights. -/
theorem cappedCosetSupport_disk_attained (M : Finset ι) (L H : Bool → ι → ℝ) :
    ∃ x z : Bool → ι → ℝ,
      (∀ σ m, 0 ≤ x σ m ∧ 0 ≤ z σ m ∧ (x σ m) ^ 2 + (z σ m) ^ 2 = 1) ∧
      (∀ p q, (x false p) ^ 2 + (x true q) ^ 2 ≤ 1) ∧
      (∑ σ : Bool, ∑ m ∈ M, (L σ m * x σ m + H σ m * z σ m)) =
        cappedCosetSupport M L H := by
  obtain ⟨t, ht, he, _⟩ := cappedCosetSupport_attained M L H
  have hex (σ : Bool) (m : ι) :=
    cappedBlockSupport_disk_attained (L σ m) (H σ m) (pairedCap_mem ht σ)
  choose x z hx hxt hz hsq hval using hex
  refine ⟨x, z, fun σ m => ⟨hx σ m, hz σ m, hsq σ m⟩, ?_, ?_⟩
  · intro p q
    have hf := pairedCap_mem ht false
    have hg := pairedCap_mem ht true
    have hs := pairedCap_sq ht
    have hfp := hxt false p
    have hgq := hxt true q
    nlinarith [hx false p, hx true q]
  · simp_rw [hval]
    exact he.symm

/-- Restoring the shared origin combines its weight with the exact angular
support in Euclidean norm. -/
theorem capped_spheres_weighted_sum_le (M : Finset ι) (hM : M.Nonempty)
    (L H x z : Bool → ι → ℝ) (hH : ∀ σ m, 0 ≤ H σ m)
    (hx : ∀ σ, ∀ m ∈ M, 0 ≤ x σ m)
    (W u₀ R : ℝ) (hR : 0 ≤ R)
    (hwhole : ∀ σ, ∀ m ∈ M, u₀ ^ 2 + (x σ m) ^ 2 + (z σ m) ^ 2 ≤ R ^ 2)
    (hpair : ∀ p ∈ M, ∀ q ∈ M, u₀ ^ 2 + (x false p) ^ 2 + (x true q) ^ 2 ≤ R ^ 2) :
    W * u₀ + (∑ σ : Bool, ∑ m ∈ M, (L σ m * x σ m + H σ m * z σ m)) ≤
      Real.sqrt (W ^ 2 + cappedCosetSupport M L H ^ 2) * R := by
  obtain ⟨m, hm⟩ := hM
  have hres : 0 ≤ R ^ 2 - u₀ ^ 2 := by
    have h := hwhole false m hm
    nlinarith [sq_nonneg (x false m), sq_nonneg (z false m)]
  let r := Real.sqrt (R ^ 2 - u₀ ^ 2)
  have hr : r ^ 2 = R ^ 2 - u₀ ^ 2 := Real.sq_sqrt hres
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hsum : (∑ σ : Bool, ∑ m ∈ M, (L σ m * x σ m + H σ m * z σ m)) ≤
      cappedCosetSupport M L H * r := by
    by_cases hz : r = 0
    · have hzero (σ : Bool) (m : ι) (hm : m ∈ M) : x σ m = 0 ∧ z σ m = 0 := by
        have h := hwhole σ m hm
        rw [hz] at hr
        constructor <;> nlinarith [sq_nonneg (x σ m), sq_nonneg (z σ m)]
      rw [hz, mul_zero]
      apply Finset.sum_nonpos
      intro σ _
      apply Finset.sum_nonpos
      intro m hm
      simp [(hzero σ m hm).1, (hzero σ m hm).2]
    · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
      have hb := cappedCosetSupport_bound M ⟨m, hm⟩ L H
        (fun σ m => x σ m / r) (fun σ m => z σ m / r) hH
        (fun σ m hm => div_nonneg (hx σ m hm) hr0)
        (by
          intro σ m hm
          rw [div_pow, div_pow, ← add_div]
          apply (div_le_one (sq_pos_of_pos hrp)).2
          have h := hwhole σ m hm
          linarith)
        (by
          intro p hp q hq
          rw [div_pow, div_pow, ← add_div]
          apply (div_le_one (sq_pos_of_pos hrp)).2
          have h := hpair p hp q hq
          linarith)
      simp_rw [← mul_div_assoc, ← add_div, ← Finset.sum_div] at hb
      exact (div_le_iff₀ hrp).1 hb
  have hfinal := sphere_weighted_sum_le_sqrt_mul ({()} : Finset Unit) W
    (fun _ => cappedCosetSupport M L H) (fun _ => r) u₀ R hR
    (by simp only [Finset.sum_singleton]; linarith)
  simp only [Finset.sum_singleton] at hfinal
  linarith

/-- The common-origin support is attained in the finite amplitude model. -/
theorem capped_spheres_support_attained (M : Finset ι) (L H : Bool → ι → ℝ)
    (hH : ∀ σ m, 0 ≤ H σ m) {W R : ℝ} (hW : 0 < W) (hR : 0 ≤ R) :
    ∃ (u₀ : ℝ) (x z : Bool → ι → ℝ),
      (∀ σ m, 0 ≤ x σ m ∧ 0 ≤ z σ m ∧
        u₀ ^ 2 + (x σ m) ^ 2 + (z σ m) ^ 2 ≤ R ^ 2) ∧
      (∀ p q, u₀ ^ 2 + (x false p) ^ 2 + (x true q) ^ 2 ≤ R ^ 2) ∧
      W * u₀ + (∑ σ : Bool, ∑ m ∈ M, (L σ m * x σ m + H σ m * z σ m)) =
        Real.sqrt (W ^ 2 + cappedCosetSupport M L H ^ 2) * R := by
  obtain ⟨x, z, hwhole, hpair, hval⟩ := cappedCosetSupport_disk_attained M L H
  let Z := cappedCosetSupport M L H
  let D := Real.sqrt (W ^ 2 + Z ^ 2)
  have hZ : 0 ≤ Z := cappedCosetSupport_nonneg M L H hH
  have hD : 0 < D := Real.sqrt_pos.2 (by positivity)
  have hDsq : D ^ 2 = W ^ 2 + Z ^ 2 := Real.sq_sqrt (by positivity)
  let a := R * W / D
  let b := R * Z / D
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hR hZ) hD.le
  have hab : a ^ 2 + b ^ 2 = R ^ 2 := by
    dsimp [a, b]
    calc
      _ = R ^ 2 * (W ^ 2 + Z ^ 2) / D ^ 2 := by ring
      _ = R ^ 2 := by rw [← hDsq]; field_simp
  refine ⟨a, (fun σ m => b * x σ m), (fun σ m => b * z σ m), ?_, ?_, ?_⟩
  · intro σ m
    refine ⟨mul_nonneg hb (hwhole σ m).1, mul_nonneg hb (hwhole σ m).2.1, ?_⟩
    have hs := (hwhole σ m).2.2
    have he : (b * x σ m) ^ 2 + (b * z σ m) ^ 2 = b ^ 2 := by
      calc
        _ = b ^ 2 * ((x σ m) ^ 2 + (z σ m) ^ 2) := by ring
        _ = b ^ 2 := by rw [hs, mul_one]
    linarith
  · intro p q
    have h := mul_le_mul_of_nonneg_left (hpair p q) (sq_nonneg b)
    nlinarith
  · have hsum : (∑ σ : Bool, ∑ m ∈ M,
        (L σ m * (b * x σ m) + H σ m * (b * z σ m))) = b * Z := by
      calc
        _ = b * (∑ σ : Bool, ∑ m ∈ M, (L σ m * x σ m + H σ m * z σ m)) := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          apply Finset.sum_congr rfl
          intro m _
          ring
        _ = b * Z := by rw [hval]
    rw [hsum]
    change W * a + b * Z = D * R
    dsimp [a, b]
    calc
      _ = R * (W ^ 2 + Z ^ 2) / D := by ring
      _ = D * R := by rw [← hDsq]; field_simp

variable {κ : Type*}

/-- Exact block-vector support: parallel low/high weight subvectors lift the
amplitude maximizer, even when a subblock has zero weight. This is finite-vector
attainment, without a claim of realization by an autocorrelation. -/
theorem capped_block_vectors_support_attained (M : Finset ι)
    (s t : ι → Finset κ) (a b : Bool → ι → κ → ℝ) {W R : ℝ}
    (hW : 0 < W) (hR : 0 ≤ R) :
    ∃ (u₀ : ℝ) (u v : Bool → ι → κ → ℝ),
      (∀ σ m, u₀ ^ 2 + (∑ j ∈ s m, u σ m j ^ 2) +
        (∑ j ∈ t m, v σ m j ^ 2) ≤ R ^ 2) ∧
      (∀ p q, u₀ ^ 2 + (∑ j ∈ s p, u false p j ^ 2) +
        (∑ j ∈ s q, u true q j ^ 2) ≤ R ^ 2) ∧
      W * u₀ + (∑ σ : Bool, ∑ m ∈ M,
        ((∑ j ∈ s m, a σ m j * u σ m j) +
         (∑ j ∈ t m, b σ m j * v σ m j))) =
        Real.sqrt (W ^ 2 + (cappedCosetSupport M
          (fun σ m => collarBlockSize (s m) (a σ m))
          (fun σ m => collarBlockSize (t m) (b σ m))) ^ 2) * R := by
  obtain ⟨u₀, x, z, hwhole, hpair, hval⟩ := capped_spheres_support_attained M
    (fun σ m => collarBlockSize (s m) (a σ m))
    (fun σ m => collarBlockSize (t m) (b σ m))
    (fun _ _ => Real.sqrt_nonneg _) hW hR
  let u (σ : Bool) (m : ι) (j : κ) := x σ m * collarBlockDirection (s m) (a σ m) j
  let v (σ : Bool) (m : ι) (j : κ) := z σ m * collarBlockDirection (t m) (b σ m) j
  have hu (σ : Bool) (m : ι) : (∑ j ∈ s m, u σ m j ^ 2) ≤ (x σ m) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (collarBlockDirection_sq_sum_le (s m) (a σ m))
      (sq_nonneg (x σ m))
    simpa only [u, mul_pow, ← Finset.mul_sum, mul_one] using h
  have hv (σ : Bool) (m : ι) : (∑ j ∈ t m, v σ m j ^ 2) ≤ (z σ m) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (collarBlockDirection_sq_sum_le (t m) (b σ m))
      (sq_nonneg (z σ m))
    simpa only [v, mul_pow, ← Finset.mul_sum, mul_one] using h
  refine ⟨u₀, u, v, ?_, ?_, ?_⟩
  · intro σ m
    linarith [(hwhole σ m).2.2, hu σ m, hv σ m]
  · intro p q
    linarith [hpair p q, hu false p, hu true q]
  · have hpairing (σ : Bool) (m : ι) :
        (∑ j ∈ s m, a σ m j * u σ m j) + (∑ j ∈ t m, b σ m j * v σ m j) =
          collarBlockSize (s m) (a σ m) * x σ m + collarBlockSize (t m) (b σ m) * z σ m := by
      have hau : (∑ j ∈ s m, a σ m j * u σ m j) =
          x σ m * collarBlockSize (s m) (a σ m) := by
        calc
          _ = x σ m * ∑ j ∈ s m, a σ m j * collarBlockDirection (s m) (a σ m) j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            dsimp [u]
            ring
          _ = _ := by rw [collarBlockDirection_pairing]
      have hbv : (∑ j ∈ t m, b σ m j * v σ m j) =
          z σ m * collarBlockSize (t m) (b σ m) := by
        calc
          _ = z σ m * ∑ j ∈ t m, b σ m j * collarBlockDirection (t m) (b σ m) j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            dsimp [v]
            ring
          _ = _ := by rw [collarBlockDirection_pairing]
      rw [hau, hbv]
      ring
    simp_rw [hpairing]
    exact hval

end
end GaloisForLFunctions.BiScaleUncertainty
