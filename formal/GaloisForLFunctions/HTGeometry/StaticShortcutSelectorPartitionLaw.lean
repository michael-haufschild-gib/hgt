import GaloisForLFunctions.HTGeometry.StaticShortcutRecurrenceEnergyLaw

/-!
# Static shortcut selector-partition law

Adaptive shortcuts must preserve the selected target label until after temporal recurrence is
measured. This module partitions a history by its actual observer channel and proves the exact
channel-resolved observer--spectral inequality. A constant selector recovers scalar recurrence;
an injective selector retains only diagonal norm. The final capstone inserts the static two-memory
collision decomposition and identifies each channel energy with a stationary recurrence kernel.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J C F : Type*} [Fintype J] [Fintype C] [DecidableEq C]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Weight retained by observer channel `c`. -/
def selectorMaskedWeight (chosen : J → C) (w : J → ℝ) (c : C) (j : J) : ℝ :=
  if chosen j = c then w j else 0

/-- Total temporal load assigned to one observer channel. -/
def selectorChannelWeight (chosen : J → C) (w : J → ℝ) (c : C) : ℝ :=
  ∑ j, selectorMaskedWeight chosen w c j

/-- Dynamical memory accumulated inside one observer channel. -/
def selectorChannelMemory
    (r : J → F) (chosen : J → C) (w : J → ℝ) (c : C) : F :=
  weightedMemorySum r (selectorMaskedWeight chosen w c)

/-- Quadratic load of the occupied observer-channel partition. -/
def selectorLoadEnergy (chosen : J → C) (w : J → ℝ) : ℝ :=
  ∑ c, selectorChannelWeight chosen w c ^ (2 : ℕ)

/-- Recurrence energy after preserving the selected observer-channel label. -/
def selectorRecurrenceEnergy (r : J → F) (chosen : J → C) (w : J → ℝ) : ℝ :=
  ∑ c, weightedRecurrenceEnergy r (selectorMaskedWeight chosen w c)

omit [Fintype J] [Fintype C] in
theorem selectorMaskedWeight_nonneg
    (chosen : J → C) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (c : C) (j : J) :
    0 ≤ selectorMaskedWeight chosen w c j := by
  by_cases h : chosen j = c
  · simpa [selectorMaskedWeight, h] using hw j
  · simp [selectorMaskedWeight, h]

omit [Fintype C] in
theorem selectorChannelWeight_nonneg
    (chosen : J → C) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (c : C) :
    0 ≤ selectorChannelWeight chosen w c := by
  exact Finset.sum_nonneg fun j _ => selectorMaskedWeight_nonneg chosen w hw c j

/-- **Selector-partition observer--spectral law.** Each selected target receives its own positive
margin and its own recurrence channel; no averaging over unselected targets occurs. -/
theorem selectorMargins_sq_load_le_recurrenceEnergy
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    (margin : C → ℝ)
    (hmargin : ∀ c, 0 ≤ margin c)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, margin (chosen j) ≤ inner ℝ (r j) (q (chosen j))) :
    (∑ c, margin c ^ (2 : ℕ) * selectorChannelWeight chosen w c ^ (2 : ℕ)) ≤
      ∑ c, ‖q c‖ ^ (2 : ℕ) *
        weightedRecurrenceEnergy r (selectorMaskedWeight chosen w c) := by
  apply Finset.sum_le_sum
  intro c hc
  have hload : 0 ≤ selectorChannelWeight chosen w c :=
    selectorChannelWeight_nonneg chosen w hw c
  have hlin :
      margin c * selectorChannelWeight chosen w c ≤
        weightedAlignment r (q c) (selectorMaskedWeight chosen w c) := by
    simp only [selectorChannelWeight, weightedAlignment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjc : chosen j = c
    · have hselected := halign j
      rw [hjc] at hselected
      simpa [selectorMaskedWeight, hjc, mul_comm] using
        mul_le_mul_of_nonneg_left hselected (hw j)
    · simp [selectorMaskedWeight, hjc]
  have hleft : 0 ≤ margin c * selectorChannelWeight chosen w c :=
    mul_nonneg (hmargin c) hload
  have halignment :
      0 ≤ weightedAlignment r (q c) (selectorMaskedWeight chosen w c) :=
    le_trans hleft hlin
  have hsq :
      (margin c * selectorChannelWeight chosen w c) ^ (2 : ℕ) ≤
        weightedAlignment r (q c) (selectorMaskedWeight chosen w c) ^ (2 : ℕ) := by
    nlinarith
  calc
    margin c ^ (2 : ℕ) * selectorChannelWeight chosen w c ^ (2 : ℕ) =
        (margin c * selectorChannelWeight chosen w c) ^ (2 : ℕ) := by ring
    _ ≤ weightedAlignment r (q c) (selectorMaskedWeight chosen w c) ^ (2 : ℕ) := hsq
    _ ≤ ‖q c‖ ^ (2 : ℕ) *
        weightedRecurrenceEnergy r (selectorMaskedWeight chosen w c) :=
      weightedAlignment_sq_le_recurrenceEnergy r (q c)
        (selectorMaskedWeight chosen w c)

/-- Uniform-margin, uniform-target-norm form of the selector-partition law. -/
theorem selectorThreshold_sq_load_le_recurrenceEnergy
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B : ℝ}
    (heta : 0 ≤ eta)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ (2 : ℕ) ≤ B) :
    eta ^ (2 : ℕ) * selectorLoadEnergy chosen w ≤
      B * selectorRecurrenceEnergy r chosen w := by
  have hmain := selectorMargins_sq_load_le_recurrenceEnergy
    r q chosen w (fun _ => eta) (fun _ => heta) hw halign
  calc
    eta ^ (2 : ℕ) * selectorLoadEnergy chosen w =
        ∑ c, eta ^ (2 : ℕ) * selectorChannelWeight chosen w c ^ (2 : ℕ) := by
      simp [selectorLoadEnergy, Finset.mul_sum]
    _ ≤ ∑ c, ‖q c‖ ^ (2 : ℕ) *
        weightedRecurrenceEnergy r (selectorMaskedWeight chosen w c) := hmain
    _ ≤ ∑ c, B * weightedRecurrenceEnergy r
        (selectorMaskedWeight chosen w c) := by
      apply Finset.sum_le_sum
      intro c hc
      apply mul_le_mul_of_nonneg_right (hq c)
      rw [weightedRecurrenceEnergy_eq_norm_sq]
      positivity
    _ = B * selectorRecurrenceEnergy r chosen w := by
      simp [selectorRecurrenceEnergy, Finset.mul_sum]

/-- Exact same-channel pair expansion of selector recurrence energy. -/
theorem selectorRecurrenceEnergy_eq_pairSum
    (r : J → F) (chosen : J → C) (w : J → ℝ) :
    selectorRecurrenceEnergy r chosen w =
      ∑ i, ∑ j,
        if chosen i = chosen j then
          w i * w j * inner ℝ (r i) (r j)
        else 0 := by
  classical
  simp only [selectorRecurrenceEnergy, weightedRecurrenceEnergy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : chosen i = chosen j
  · rw [if_pos hij]
    simp [selectorMaskedWeight, hij]
  · rw [if_neg hij]
    simp [selectorMaskedWeight, hij]

/-- A static unitary orbit turns the selector energy into a same-channel stationary kernel. -/
theorem selectorRecurrenceEnergy_flow_eq_kernel
    (U : UnitaryFlow ℝ F) (z : F) (time : J → ℝ)
    (chosen : J → C) (w : J → ℝ) :
    selectorRecurrenceEnergy (fun j => U.op (time j) z) chosen w =
      ∑ i, ∑ j,
        if chosen i = chosen j then
          w i * w j * inner ℝ z (U.op (time j - time i) z)
        else 0 := by
  rw [selectorRecurrenceEnergy_eq_pairSum]
  simp only [inner_unitaryFlow_eq_recurrenceKernel]

/-- A constant selector recovers the complete scalar recurrence energy exactly. -/
theorem selectorRecurrenceEnergy_const
    (r : J → F) (c₀ : C) (w : J → ℝ) :
    selectorRecurrenceEnergy r (fun _ => c₀) w = weightedRecurrenceEnergy r w := by
  rw [selectorRecurrenceEnergy_eq_pairSum]
  simp [weightedRecurrenceEnergy]

/-- An injective selector removes every off-diagonal pair exactly. -/
theorem selectorRecurrenceEnergy_injective
    (r : J → F) (chosen : J → C) (w : J → ℝ)
    (hinjective : Function.Injective chosen) :
    selectorRecurrenceEnergy r chosen w =
      ∑ j, w j ^ (2 : ℕ) * ‖r j‖ ^ (2 : ℕ) := by
  rw [selectorRecurrenceEnergy_eq_pairSum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j, if chosen i = chosen j then
        w i * w j * inner ℝ (r i) (r j) else 0) =
        w i * w i * inner ℝ (r i) (r i) := by
      have hsingle :
          (∑ j, if chosen i = chosen j then
              w i * w j * inner ℝ (r i) (r j) else 0) =
            (if chosen i = chosen i then
              w i * w i * inner ℝ (r i) (r i) else 0) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hneq : chosen i ≠ chosen j := fun h => hji (hinjective h.symm)
          simp [hneq]
        · simp
      simpa using hsingle
    _ = w i ^ (2 : ℕ) * ‖r i‖ ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq]
      ring

/-- For a static unitary orbit, a fresh channel at every sample pays only diagonal norm. -/
theorem selectorRecurrenceEnergy_flow_injective
    (U : UnitaryFlow ℝ F) (z : F) (time : J → ℝ)
    (chosen : J → C) (w : J → ℝ)
    (hinjective : Function.Injective chosen) :
    selectorRecurrenceEnergy (fun j => U.op (time j) z) chosen w =
      ‖z‖ ^ (2 : ℕ) * ∑ j, w j ^ (2 : ℕ) := by
  rw [selectorRecurrenceEnergy_injective _ _ _ hinjective]
  simp only [LinearIsometryEquiv.norm_map]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- **Fresh-channel saturation.** If each sample selects itself as its target channel and its
preparation memory is the sampled memory, then the channel-resolved observer--spectral inequality
is an equality for arbitrary weights and vectors. No orthogonality, phase separation, or spectral
assumption can remove this diagonal cost. -/
theorem selectorIdentity_selfTarget_saturation (r : C → F) (w : C → ℝ) :
    (∑ c, (‖r c‖ ^ (2 : ℕ)) ^ (2 : ℕ) *
        selectorChannelWeight (fun j : C => j) w c ^ (2 : ℕ)) =
      ∑ c, ‖r c‖ ^ (2 : ℕ) *
        weightedRecurrenceEnergy r
          (selectorMaskedWeight (fun j : C => j) w c) := by
  apply Finset.sum_congr rfl
  intro c hc
  rw [weightedRecurrenceEnergy_eq_norm_sq]
  have hweight : selectorChannelWeight (fun j : C => j) w c = w c := by
    simp [selectorChannelWeight, selectorMaskedWeight]
  have hmemory :
      weightedMemorySum r
          (selectorMaskedWeight (fun j : C => j) w c) = w c • r c := by
    simp [weightedMemorySum, selectorMaskedWeight]
  rw [hweight, hmemory, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

variable [CompleteSpace F]

/-- **Target-specific two-memory selector capstone.** Adaptive shortcut targets are partitioned
before temporal Cauchy--Schwarz. The resulting obligation retains each occupied target channel and
is exactly a same-channel stationary recurrence kernel. -/
theorem adaptive_selected_shortcuts_force_channel_recurrence
    (PiOp P : F →L[ℝ] F) (U : UnitaryFlow ℝ F) (x : F)
    (target : C → F) (chosen : J → C) (time : J → ℝ) (w : J → ℝ)
    (margin : C → ℝ)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ t z, P (U.op t z) = P z)
    (hUP : ∀ t z, U.op t (P z) = P z)
    (hPiy : ∀ c, PiOp (target c) = PiOp x)
    (hmargin : ∀ c, 0 ≤ margin c)
    (hw : ∀ j, 0 ≤ w j)
    (hcollision : ∀ j,
      inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (target (chosen j))) +
          margin (chosen j) ≤
        inner ℝ (U.op (time j) x) (target (chosen j))) :
    (∑ c, margin c ^ (2 : ℕ) * selectorChannelWeight chosen w c ^ (2 : ℕ)) ≤
      ∑ c, ‖preparationMemory PiOp x (target c)‖ ^ (2 : ℕ) *
        (∑ i, ∑ j,
          selectorMaskedWeight chosen w c i *
            selectorMaskedWeight chosen w c j *
              inner ℝ (x - P x) (U.op (time j - time i) (x - P x))) := by
  have halign : ∀ j,
      margin (chosen j) ≤
        inner ℝ (dynamicMemory P (U.op (time j)) x)
          (preparationMemory PiOp x (target (chosen j))) := by
    intro j
    have h := twoMemory_dynamicAlignment_ge_of_collision_ge
      PiOp P (U.op (time j)) x (target (chosen j))
      hPisa hPiid hPiP (hPU (time j)) (hPiy (chosen j))
      (threshold :=
        inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x (target (chosen j))) +
          margin (chosen j))
      (hcollision j)
    linarith
  have hmain := selectorMargins_sq_load_le_recurrenceEnergy
    (r := fun j => dynamicMemory P (U.op (time j)) x)
    (q := fun c => preparationMemory PiOp x (target c))
    chosen w margin hmargin hw halign
  have hdynamic :
      (fun j => dynamicMemory P (U.op (time j)) x) =
        fun j => U.op (time j) (x - P x) := by
    funext j
    simp only [dynamicMemory, map_sub, hUP]
  rw [hdynamic] at hmain
  simpa only [weightedRecurrenceEnergy_flow_eq_kernel] using hmain

end

end GaloisForLFunctions.HTGeometry
