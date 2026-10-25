import GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorDiagonalsAreHorizonEnergyRatios
import GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorKernelFamiliesAreSingletonOrContinuum
import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverEnergyEscapesToTheHorizon

/-!
# Record-minimum renormalization forces strictly positive cofactor diagonals

At every subcritical damping `0 < ε < 1/2`, the actual receiver energy obeys
`E_ε(N) ≤ D (1 + N^{1-2ε})`. Dividing by `N^{1-2ε + 1/(m+1)}` produces a strictly
positive sequence tending to zero, which therefore attains cofinal record minima
`g_m(N_m) = min_{1 ≤ j ≤ N_m} g_m(j)`.

Passing to an actual common cofactor limit `L` along `T_m = N_m - 1` bounds every
contracted energy ratio `E_ε(⌊N_m/p⌋) / E_ε(N_m)` below by `(⌊N_m/p⌋ / N_m)^{1-2ε + o(1)}`,
forcing the simultaneous diagonal lower bound

`p^{2ε - 2} ≤ L.kernel p p`   for every `p ∈ ℕ+`.

In particular, every cofactor row vector `L.vector p` is nonzero, neither the
augmentation kernel `1_{j=k=1}` nor any kernel with a vanishing diagonal entry can
be the unique actual cofactor limit, and the occurrence of any zero-cofactor limit
forces continuum many distinct actual cofactor kernels.
-/

noncomputable section
set_option autoImplicit false

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The rank-one augmentation cofactor kernel supported solely at `(1, 1)`. -/
def augmentationCofactorKernel (j k : ℕ+) : ℝ :=
  if j = 1 ∧ k = 1 then 1 else 0

@[simp]
theorem augmentationCofactorKernel_one_one :
    augmentationCofactorKernel 1 1 = 1 := by
  simp [augmentationCofactorKernel]

theorem augmentationCofactorKernel_diag_eq_zero {p : ℕ+} (hp : p ≠ 1) :
    augmentationCofactorKernel p p = 0 := by
  simp [augmentationCofactorKernel, hp]

/-- Any positive sequence tending to zero attains cofinal record minima above every threshold. -/
theorem exists_record_min_gt {g : ℕ → ℝ}
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < g n)
    (htend : Tendsto g atTop (𝓝 0))
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ N : ℕ, B < N ∧ ∀ j : ℕ, 1 ≤ j → j ≤ N → g N ≤ g j := by
  classical
  let S : Finset ℕ := Finset.Icc 1 B
  have hSne : S.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hB⟩⟩
  let μ : ℝ := (S.image g).min' (hSne.image g)
  have hμ_mem : μ ∈ S.image g := Finset.min'_mem (S.image g) (hSne.image g)
  obtain ⟨j₀, hj₀S, hj₀eq⟩ := Finset.mem_image.mp hμ_mem
  have hμ_pos : 0 < μ := by
    rw [← hj₀eq]
    exact hpos j₀ (Finset.mem_Icc.mp hj₀S).1
  have hμ_le : ∀ j : ℕ, 1 ≤ j → j ≤ B → μ ≤ g j := fun j hj1 hjB =>
    Finset.min'_le (S.image g) (g j) (Finset.mem_image_of_mem g (Finset.mem_Icc.mpr ⟨hj1, hjB⟩))
  have hex : ∃ M : ℕ, B < M ∧ g M < μ := by
    have hev := (eventually_gt_atTop B).and (htend.eventually (gt_mem_nhds hμ_pos))
    exact hev.exists
  let N : ℕ := Nat.find hex
  have hN : B < N ∧ g N < μ := Nat.find_spec hex
  refine ⟨N, hN.1, fun j hj1 hjN => ?_⟩
  rcases eq_or_lt_of_le hjN with rfl | hjlt
  · exact le_rfl
  · rcases le_or_gt j B with hjB | hjB
    · exact hN.2.le.trans (hμ_le j hj1 hjB)
    · have hnot : ¬ (B < j ∧ g j < μ) := Nat.find_min hex hjlt
      have hge : μ ≤ g j := not_lt.mp fun hlt => hnot ⟨hjB, hlt⟩
      exact hN.2.le.trans hge

private def recordExponent (ε : SubcriticalDamping) (m : ℕ) : ℝ :=
  1 - 2 * (ε : ℝ) + 1 / ((m : ℝ) + 1)

private def scaledReceiverEnergy (ε : SubcriticalDamping) (m N : ℕ) : ℝ :=
  dampedMobiusEnergy ε N / (N : ℝ) ^ recordExponent ε m

private theorem scaledReceiverEnergy_pos (ε : SubcriticalDamping) (m : ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    0 < scaledReceiverEnergy ε m N := by
  unfold scaledReceiverEnergy
  have hE : 0 < dampedMobiusEnergy ε N := by
    rw [← Nat.sub_add_cancel hN]
    exact receiverEnergy_succ_pos ε (N - 1)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact div_pos hE (Real.rpow_pos_of_pos hNpos _)

private theorem tendsto_scaledReceiverEnergy_zero (ε : SubcriticalDamping) (m : ℕ) :
    Tendsto (scaledReceiverEnergy ε m) atTop (𝓝 0) := by
  obtain ⟨D, hD0, hD⟩ := exists_dampedMobiusEnergy_le ε.property.1 ε.property.2
  have hα : 0 < 1 - 2 * (ε : ℝ) := by linarith [ε.property.2]
  have hδ : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have hmaj : Tendsto (fun N : ℕ => (2 * D) * (N : ℝ) ^ (-(1 / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul (2 * D)
  refine squeeze_zero' (eventually_ge_atTop 1 |>.mono fun N hN =>
      (scaledReceiverEnergy_pos ε m hN).le) ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have h1le : 1 ≤ (N : ℝ) ^ (1 - 2 * (ε : ℝ)) := Real.one_le_rpow hN1 hα.le
  have hEn : dampedMobiusEnergy ε N ≤ 2 * D * (N : ℝ) ^ (1 - 2 * (ε : ℝ)) := by
    calc dampedMobiusEnergy ε N
        ≤ D * (1 + (N : ℝ) ^ (1 - 2 * (ε : ℝ))) := hD N
      _ ≤ D * ((N : ℝ) ^ (1 - 2 * (ε : ℝ)) + (N : ℝ) ^ (1 - 2 * (ε : ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add_left h1le _) hD0
      _ = 2 * D * (N : ℝ) ^ (1 - 2 * (ε : ℝ)) := by ring
  unfold scaledReceiverEnergy recordExponent
  rw [Real.rpow_add hNpos, ← div_div,
    div_le_iff₀ (Real.rpow_pos_of_pos hNpos (1 / ((m : ℝ) + 1)))]
  have hpow_pos : 0 < (N : ℝ) ^ (1 - 2 * (ε : ℝ)) := Real.rpow_pos_of_pos hNpos _
  calc dampedMobiusEnergy ε N / (N : ℝ) ^ (1 - 2 * (ε : ℝ))
      ≤ (2 * D * (N : ℝ) ^ (1 - 2 * (ε : ℝ))) / (N : ℝ) ^ (1 - 2 * (ε : ℝ)) :=
        div_le_div_of_nonneg_right hEn hpow_pos.le
    _ = 2 * D := mul_div_cancel_right₀ (2 * D) hpow_pos.ne'
    _ = 2 * D * (N : ℝ) ^ (-(1 / ((m : ℝ) + 1))) * (N : ℝ) ^ (1 / ((m : ℝ) + 1)) := by
        rw [mul_assoc, ← Real.rpow_add hNpos, neg_add_cancel, Real.rpow_zero, mul_one]

private def nextRecordHorizon (ε : SubcriticalDamping) (m B : ℕ) : ℕ :=
  (exists_record_min_gt (fun _ h => scaledReceiverEnergy_pos ε m h)
    (tendsto_scaledReceiverEnergy_zero ε m) (max B 1) (le_max_right B 1)).choose

private theorem nextRecordHorizon_spec (ε : SubcriticalDamping) (m B : ℕ) :
    max B 1 < nextRecordHorizon ε m B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ nextRecordHorizon ε m B →
        scaledReceiverEnergy ε m (nextRecordHorizon ε m B) ≤ scaledReceiverEnergy ε m j :=
  (exists_record_min_gt (fun _ h => scaledReceiverEnergy_pos ε m h)
    (tendsto_scaledReceiverEnergy_zero ε m) (max B 1) (le_max_right B 1)).choose_spec

private def recordHorizonSeq (ε : SubcriticalDamping) : ℕ → ℕ
  | 0 => nextRecordHorizon ε 0 1
  | m + 1 => nextRecordHorizon ε (m + 1) (recordHorizonSeq ε m)

private theorem one_lt_recordHorizonSeq (ε : SubcriticalDamping) (m : ℕ) :
    1 < recordHorizonSeq ε m := by
  cases m with
  | zero =>
    have h := (nextRecordHorizon_spec ε 0 1).1
    exact lt_of_le_of_lt (le_max_right 1 1) h
  | succ m =>
    have h := (nextRecordHorizon_spec ε (m + 1) (recordHorizonSeq ε m)).1
    exact lt_of_le_of_lt (le_max_right _ 1) h

private theorem strictMono_recordHorizonSeq (ε : SubcriticalDamping) :
    StrictMono (recordHorizonSeq ε) :=
  strictMono_nat_of_lt_succ fun m =>
    lt_of_le_of_lt (le_max_left _ 1) (nextRecordHorizon_spec ε (m + 1) (recordHorizonSeq ε m)).1

private theorem recordHorizonSeq_min (ε : SubcriticalDamping) (m : ℕ)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ recordHorizonSeq ε m) :
    scaledReceiverEnergy ε m (recordHorizonSeq ε m) ≤ scaledReceiverEnergy ε m j := by
  cases m with
  | zero => exact (nextRecordHorizon_spec ε 0 1).2 j hj1 hj
  | succ m => exact (nextRecordHorizon_spec ε (m + 1) (recordHorizonSeq ε m)).2 j hj1 hj

private theorem tendsto_nat_div_ratio {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) (p : ℕ+) :
    Tendsto (fun r : ℕ => ((M r / (p : ℕ) : ℕ) : ℝ) / (M r : ℝ)) atTop (𝓝 ((p : ℝ)⁻¹)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hlow : Tendsto (fun r : ℕ => (p : ℝ)⁻¹ - 1 / (M r : ℝ)) atTop (𝓝 ((p : ℝ)⁻¹)) := by
    have h0 : Tendsto (fun r : ℕ => 1 / (M r : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hM)
    simpa only [sub_zero] using tendsto_const_nhds.sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hM.eventually_ge_atTop 1] with r hr
    have hMr_pos : (0 : ℝ) < (M r : ℝ) := by exact_mod_cast hr
    have hmod_lt : ((M r % (p : ℕ) : ℕ) : ℝ) < (p : ℝ) := by
      exact_mod_cast Nat.mod_lt (M r) p.property
    have hdiv_mod : (p : ℝ) * ((M r / (p : ℕ) : ℕ) : ℝ) + ((M r % (p : ℕ) : ℕ) : ℝ) = (M r : ℝ) := by
      exact_mod_cast Nat.div_add_mod (M r) (p : ℕ)
    have hineq : (M r : ℝ) - (p : ℝ) ≤ (p : ℝ) * ((M r / (p : ℕ) : ℕ) : ℝ) := by
      linarith
    rw [inv_eq_one_div, div_sub_div _ _ hp_pos.ne' hMr_pos.ne', mul_one, one_mul,
      div_le_div_iff₀ (mul_pos hp_pos hMr_pos) hMr_pos]
    nlinarith
  · filter_upwards [hM.eventually_ge_atTop 1] with r hr
    have hMr_pos : (0 : ℝ) < (M r : ℝ) := by exact_mod_cast hr
    have hmul_le : (p : ℝ) * ((M r / (p : ℕ) : ℕ) : ℝ) ≤ (M r : ℝ) := by
      exact_mod_cast Nat.mul_div_le (M r) (p : ℕ)
    rw [inv_eq_one_div, div_le_div_iff₀ hMr_pos hp_pos]
    linarith

/-- At every subcritical damping `0 < ε < 1/2`, record-minimum renormalization produces
an actual common cofactor limit `L` satisfying the sharp simultaneous diagonal lower bound
`p^{2ε - 2} ≤ L.kernel p p` for every `p ∈ ℕ+`. -/
theorem exists_actualCofactorLimit_kernel_diag_ge_rpow (ε : SubcriticalDamping) :
    ∃ L : ActualCofactorLimit ε, ∀ p : ℕ+, (p : ℝ) ^ (2 * (ε : ℝ) - 2) ≤ L.kernel p p := by
  let T : ℕ → ℕ := fun m => recordHorizonSeq ε m - 1
  have hT_succ : ∀ m : ℕ, T m + 1 = recordHorizonSeq ε m := fun m =>
    Nat.sub_add_cancel (one_lt_recordHorizonSeq ε m).le
  have hT_mono : StrictMono T := fun a b hab => by
    have hlt := strictMono_recordHorizonSeq ε hab
    have ha := hT_succ a
    have hb := hT_succ b
    omega
  obtain ⟨ns, hns, L, hLsub⟩ := exists_actualCofactorLimit_along ε T hT_mono
  refine ⟨L, fun p => ?_⟩
  let M : ℕ → ℕ := fun r => recordHorizonSeq ε (ns r)
  have hM_eq : ∀ r : ℕ, L.subsequence r + 1 = M r := fun r => by
    rw [hLsub, Function.comp_apply, hT_succ]
  have hM_mono : StrictMono M := (strictMono_recordHorizonSeq ε).comp hns
  have hM_top : Tendsto M atTop atTop := hM_mono.tendsto_atTop
  have hrat_lim := L.contracted_energy_ratio_tendsto p
  have hbase_lim : Tendsto (fun r : ℕ => ((M r / (p : ℕ) : ℕ) : ℝ) / (M r : ℝ)) atTop
      (𝓝 ((p : ℝ)⁻¹)) := tendsto_nat_div_ratio hM_top p
  have hexp_lim : Tendsto (fun r : ℕ => recordExponent ε (ns r)) atTop
      (𝓝 (1 - 2 * (ε : ℝ))) := by
    unfold recordExponent
    have h0 : Tendsto (fun r : ℕ => 1 / ((ns r : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop
    simpa only [add_zero] using tendsto_const_nhds.add h0
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hlow_lim : Tendsto
      (fun r : ℕ => (((M r / (p : ℕ) : ℕ) : ℝ) / (M r : ℝ)) ^ recordExponent ε (ns r))
      atTop (𝓝 (((p : ℝ)⁻¹) ^ (1 - 2 * (ε : ℝ)))) :=
    hbase_lim.rpow hexp_lim (Or.inl (inv_ne_zero hp_pos.ne'))
  have hev_le : ∀ᶠ r : ℕ in atTop,
      (((M r / (p : ℕ) : ℕ) : ℝ) / (M r : ℝ)) ^ recordExponent ε (ns r) ≤
        dampedMobiusEnergy ε ((L.subsequence r + 1) / p) /
          dampedMobiusEnergy ε (L.subsequence r + 1) := by
    filter_upwards [hM_top.eventually_ge_atTop (p : ℕ)] with r hr
    rw [hM_eq r]
    have hq1 : 1 ≤ M r / (p : ℕ) := Nat.div_pos hr p.property
    have hq_le : M r / (p : ℕ) ≤ M r := Nat.div_le_self (M r) (p : ℕ)
    have hmin := recordHorizonSeq_min ε (ns r) hq1 hq_le
    unfold scaledReceiverEnergy at hmin
    have hMr_pos : (0 : ℝ) < (M r : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le p.property hr)
    have hqr_pos : (0 : ℝ) < ((M r / (p : ℕ) : ℕ) : ℝ) := by exact_mod_cast hq1
    have hE_pos : 0 < dampedMobiusEnergy ε (M r) := by
      rw [← hM_eq r]
      exact receiverEnergy_succ_pos ε (L.subsequence r)
    have hMr_pow : 0 < (M r : ℝ) ^ recordExponent ε (ns r) := Real.rpow_pos_of_pos hMr_pos _
    have hqr_pow : 0 < ((M r / (p : ℕ) : ℕ) : ℝ) ^ recordExponent ε (ns r) :=
      Real.rpow_pos_of_pos hqr_pos _
    rw [Real.div_rpow hqr_pos.le hMr_pos.le, div_le_div_iff₀ hMr_pow hE_pos]
    rw [div_le_div_iff₀ hMr_pow hqr_pow] at hmin
    linarith
  have hscaled : ((p : ℝ)⁻¹) ^ (1 - 2 * (ε : ℝ)) ≤ (p : ℝ) * L.kernel p p :=
    le_of_tendsto_of_tendsto hlow_lim hrat_lim hev_le
  have hrpow_eq : ((p : ℝ)⁻¹) ^ (1 - 2 * (ε : ℝ)) = (p : ℝ) ^ (2 * (ε : ℝ) - 1) := by
    rw [Real.inv_rpow hp_pos.le, ← Real.rpow_neg hp_pos.le]
    congr 1
    ring
  rw [hrpow_eq] at hscaled
  have hmul : (p : ℝ) * (p : ℝ) ^ (2 * (ε : ℝ) - 2) = (p : ℝ) ^ (2 * (ε : ℝ) - 1) := by
    rw [show (2 * (ε : ℝ) - 1) = 1 + (2 * (ε : ℝ) - 2) by ring, Real.rpow_add hp_pos,
      Real.rpow_one]
  rw [← hmul] at hscaled
  exact le_of_mul_le_mul_left hscaled hp_pos

/-- Every subcritical damping admits an actual cofactor limit whose diagonal entries are
all strictly positive and whose Hilbert row vectors are all nonzero. -/
theorem exists_actualCofactorLimit_forall_diag_pos (ε : SubcriticalDamping) :
    ∃ L : ActualCofactorLimit ε,
      (∀ p : ℕ+, 0 < L.kernel p p) ∧ (∀ p : ℕ+, L.vector p ≠ 0) := by
  obtain ⟨L, hL⟩ := exists_actualCofactorLimit_kernel_diag_ge_rpow ε
  refine ⟨L, fun p => ?_, fun p hzero => ?_⟩
  · exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) (hL p)
  · have hpos : 0 < L.kernel p p :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) (hL p)
    have hnorm := L.norm_vector_sq p
    rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hnorm
    linarith

/-- No kernel with a vanishing diagonal entry can be the unique actual cofactor kernel
at any subcritical damping. -/
theorem actualCofactorKernelSet_ne_singleton_of_diag_zero (ε : SubcriticalDamping)
    {K : ℕ+ → ℕ+ → ℝ} {p : ℕ+} (hp : K p p = 0) :
    actualCofactorKernelSet ε ≠ {K} := by
  obtain ⟨L, hpos, _⟩ := exists_actualCofactorLimit_forall_diag_pos ε
  intro hsing
  have hmem : L.kernel ∈ actualCofactorKernelSet ε := ⟨L, rfl⟩
  rw [hsing, Set.mem_singleton_iff] at hmem
  have h0 : L.kernel p p = 0 := by rw [hmem, hp]
  linarith [hpos p]

/-- The augmentation kernel `1_{j=k=1}` is never the singleton actual cofactor kernel. -/
theorem actualCofactorKernelSet_ne_singleton_augmentation (ε : SubcriticalDamping) :
    actualCofactorKernelSet ε ≠ {augmentationCofactorKernel} :=
  actualCofactorKernelSet_ne_singleton_of_diag_zero ε
    (p := 2) (augmentationCofactorKernel_diag_eq_zero (by decide))

/-- If any actual cofactor limit has a vanishing diagonal entry (in particular, if any
subsequence produces a zero cofactor row), the set of actual cofactor kernels has
continuum cardinality and the receiver escapes at `ε`. -/
theorem cardinal_actualCofactorKernelSet_eq_continuum_of_exists_diag_zero
    {ε : SubcriticalDamping} (M : ActualCofactorLimit ε) {p : ℕ+} (hp : M.kernel p p = 0) :
    Cardinal.mk (actualCofactorKernelSet ε) = Cardinal.continuum ∧
      ¬ Admits dampedMobiusEnergy ε := by
  obtain ⟨L, hpos, _⟩ := exists_actualCofactorLimit_forall_diag_pos ε
  have hne : L.kernel ≠ M.kernel := by
    intro heq
    have h0 : L.kernel p p = 0 := by rw [heq, hp]
    linarith [hpos p]
  exact ⟨L.cardinal_actualKernelSet_eq_continuum_of_ne M hne, L.not_admits_of_kernel_ne M hne⟩

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.exists_actualCofactorLimit_kernel_diag_ge_rpow
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.exists_actualCofactorLimit_forall_diag_pos
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.actualCofactorKernelSet_ne_singleton_of_diag_zero
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.actualCofactorKernelSet_ne_singleton_augmentation
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.cardinal_actualCofactorKernelSet_eq_continuum_of_exists_diag_zero

