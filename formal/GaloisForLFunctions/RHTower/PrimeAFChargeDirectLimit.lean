import GaloisForLFunctions.RHTower.PrimeQuasiLocalCharge
import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier
import Mathlib.Algebra.Colimit.Module

/-!
# AF finite-prime charge direct limits

The integer winding group at each finite prime stage is `ℤ`. Adjoining the local factor at stage
`i + 1` multiplies winding by its dimension. This file constructs that directed system literally,
computes its algebraic direct limit inside `ℚ`, proves every limit class has a finite ancestor, and
proves uniform norm-regular convergence cannot create winding at infinity.

For qubit local factors the normalized-charge subgroup is exactly the dyadic rationals. General
positive local dimensions give the subgroup of `ℚ` whose denominators divide a finite product of
the successive dimensions.
-/

namespace PrimeQuasiLocalCharge

noncomputable section

/-- Product of local dimensions adjoined after stage `i` through stage `j`. -/
def chargeTransitionFactor (localDim : ℕ → ℕ) (i j : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (j - i), localDim (i + k + 1)

@[simp] theorem chargeTransitionFactor_self (localDim : ℕ → ℕ) (i : ℕ) :
    chargeTransitionFactor localDim i i = 1 := by
  simp [chargeTransitionFactor]

@[simp] theorem chargeTransitionFactor_succ (localDim : ℕ → ℕ) (i : ℕ) :
    chargeTransitionFactor localDim i (i + 1) = localDim (i + 1) := by
  simp [chargeTransitionFactor]

theorem chargeTransitionFactor_mul {localDim : ℕ → ℕ} {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    chargeTransitionFactor localDim i j * chargeTransitionFactor localDim j k =
      chargeTransitionFactor localDim i k := by
  have hji : i + (j - i) = j := Nat.add_sub_of_le hij
  have hki : k - i = (j - i) + (k - j) := by omega
  rw [chargeTransitionFactor, chargeTransitionFactor, chargeTransitionFactor, hki,
    Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  congr 1
  omega

/-- Transition on the finite-stage integer winding group. -/
def chargeTransition (localDim : ℕ → ℕ) (i j : ℕ) (_ : i ≤ j) : ℤ →ₗ[ℤ] ℤ where
  toFun q := (chargeTransitionFactor localDim i j : ℤ) * q
  map_add' x y := by ring
  map_smul' r x := by
    change (chargeTransitionFactor localDim i j : ℤ) * (r * x) =
      r * ((chargeTransitionFactor localDim i j : ℤ) * x)
    ring

@[simp] theorem chargeTransition_apply (localDim : ℕ → ℕ) (i j : ℕ) (h : i ≤ j) (q : ℤ) :
    chargeTransition localDim i j h q = (chargeTransitionFactor localDim i j : ℤ) * q := rfl

instance chargeDirectedSystem (localDim : ℕ → ℕ) :
    DirectedSystem (fun _ : ℕ => ℤ) (fun i j h => chargeTransition localDim i j h) where
  map_self := by
    intro i x
    simp [chargeTransition]
  map_map := by
    intro i j k hij hjk x
    simp only [chargeTransition_apply]
    calc
      (chargeTransitionFactor localDim j i : ℤ) *
          ((chargeTransitionFactor localDim k j : ℤ) * x) =
        ((chargeTransitionFactor localDim k j : ℤ) *
          (chargeTransitionFactor localDim j i : ℤ)) * x := by ring
      _ = (chargeTransitionFactor localDim k i : ℤ) * x := by
        rw [← Nat.cast_mul, chargeTransitionFactor_mul hij hjk]

/-- Algebraic direct limit of finite-stage winding groups under tensor amplification. -/
abbrev AFChargeLimit (localDim : ℕ → ℕ) :=
  Module.DirectLimit (fun _ : ℕ => ℤ) (chargeTransition localDim)

/-- Canonical finite-stage charge class in the AF limit. -/
def finiteStageCharge (localDim : ℕ → ℕ) (i : ℕ) : ℤ →ₗ[ℤ] AFChargeLimit localDim :=
  Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => ℤ) (chargeTransition localDim) i

/-- A finite-stage charge and its amplification represent the same limit class. -/
theorem finiteStageCharge_transition (localDim : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) (z : ℤ) :
    finiteStageCharge localDim j ((chargeTransitionFactor localDim i j : ℤ) * z) =
      finiteStageCharge localDim i z := by
  exact Module.DirectLimit.of_f (hij := hij)

/-- One-prime inclusion acts on integer winding by the new local dimension. -/
theorem finiteStageCharge_succ (localDim : ℕ → ℕ) (i : ℕ) (z : ℤ) :
    finiteStageCharge localDim (i + 1) ((localDim (i + 1) : ℤ) * z) =
      finiteStageCharge localDim i z := by
  simpa using finiteStageCharge_transition localDim (Nat.le_succ i) z

/-- Every AF charge-limit class is represented at a finite stage. -/
theorem chargeLimit_has_finiteAncestor (localDim : ℕ → ℕ) (q : AFChargeLimit localDim) :
    ∃ i z, finiteStageCharge localDim i z = q := by
  exact Module.DirectLimit.exists_of q

theorem finiteStageCharge_zero (localDim : ℕ → ℕ) (i : ℕ) :
    finiteStageCharge localDim i 0 = 0 := by simp [finiteStageCharge]

theorem chargeTransitionFactor_pos {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i j : ℕ) :
    0 < chargeTransitionFactor localDim i j := by
  exact Finset.prod_pos fun k _ => hd (i + k + 1)

/-- Positive local dimensions make every finite-stage map into the charge limit injective. -/
theorem finiteStageCharge_injective {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ) :
    Function.Injective (finiteStageCharge localDim i) := by
  intro x y hxy
  have hzero : finiteStageCharge localDim i (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hzero
  rw [chargeTransition_apply] at hj
  rcases mul_eq_zero.mp hj with hfactor | hsub
  · have hpos := chargeTransitionFactor_pos hd i j
    exact False.elim ((Int.ofNat_ne_zero.mpr hpos.ne') hfactor)
  · exact sub_eq_zero.mp hsub

/-- A limit class which has only zero finite-stage representatives is zero. -/
theorem chargeLimit_eq_zero_of_all_ancestors_zero (localDim : ℕ → ℕ)
    {q : AFChargeLimit localDim}
    (hzero : ∀ i z, finiteStageCharge localDim i z = q → z = 0) : q = 0 := by
  obtain ⟨i, z, hz⟩ := chargeLimit_has_finiteAncestor localDim q
  rw [hzero i z hz] at hz
  simpa using hz.symm

/-- Every nonzero AF charge-limit class has a nonzero finite-stage ancestor. -/
theorem nonzero_chargeLimit_has_nonzero_finiteAncestor (localDim : ℕ → ℕ)
    {q : AFChargeLimit localDim} (hq : q ≠ 0) :
    ∃ i z, z ≠ 0 ∧ finiteStageCharge localDim i z = q := by
  obtain ⟨i, z, hz⟩ := chargeLimit_has_finiteAncestor localDim q
  refine ⟨i, z, ?_, hz⟩
  intro hz0
  subst z
  exact hq (by simpa using hz.symm)

/-- Product of all local dimensions adjoined through stage `i`. -/
def chargeDenominator (localDim : ℕ → ℕ) (i : ℕ) : ℕ :=
  chargeTransitionFactor localDim 0 i

theorem chargeDenominator_mul_factor {localDim : ℕ → ℕ} {i j : ℕ} (hij : i ≤ j) :
    chargeDenominator localDim i * chargeTransitionFactor localDim i j =
      chargeDenominator localDim j := by
  exact chargeTransitionFactor_mul (Nat.zero_le i) hij

/-- Stage `i` embeds in `ℚ` by dividing its integer charge by dimensions already adjoined. -/
def stageChargeRational (localDim : ℕ → ℕ) (i : ℕ) : ℤ →ₗ[ℤ] ℚ where
  toFun z := (z : ℚ) / (chargeDenominator localDim i : ℚ)
  map_add' x y := by push_cast; ring
  map_smul' r x := by
    change ((r * x : ℤ) : ℚ) / (chargeDenominator localDim i : ℚ) =
      (r : ℚ) * ((x : ℚ) / (chargeDenominator localDim i : ℚ))
    push_cast
    ring

theorem stageChargeRational_compatible {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) {i j : ℕ} (hij : i ≤ j) (z : ℤ) :
    stageChargeRational localDim j (chargeTransition localDim i j hij z) =
      stageChargeRational localDim i z := by
  have hdi : 0 < chargeDenominator localDim i := chargeTransitionFactor_pos hd 0 i
  have hf : 0 < chargeTransitionFactor localDim i j := chargeTransitionFactor_pos hd i j
  have hdj : chargeDenominator localDim j =
      chargeDenominator localDim i * chargeTransitionFactor localDim i j :=
    (chargeDenominator_mul_factor hij).symm
  change (((chargeTransitionFactor localDim i j : ℤ) * z : ℤ) : ℚ) /
      (chargeDenominator localDim j : ℚ) =
    (z : ℚ) / (chargeDenominator localDim i : ℚ)
  push_cast
  rw [hdj]
  push_cast
  field_simp [hdi.ne', hf.ne']

/-- Canonical faithful realization of the AF charge limit inside `ℚ`. -/
def afChargeToRational {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    AFChargeLimit localDim →ₗ[ℤ] ℚ :=
  Module.DirectLimit.lift ℤ ℕ (fun _ : ℕ => ℤ) (chargeTransition localDim)
    (stageChargeRational localDim) fun _ _ hij z =>
      stageChargeRational_compatible hd hij z

@[simp] theorem afChargeToRational_finiteStage {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ) (z : ℤ) :
    afChargeToRational hd (finiteStageCharge localDim i z) =
      (z : ℚ) / (chargeDenominator localDim i : ℚ) := by
  unfold afChargeToRational finiteStageCharge
  exact Module.DirectLimit.lift_of (stageChargeRational localDim)
    (fun _ _ hij z => stageChargeRational_compatible hd hij z) z

/-- Positive local dimensions identify the direct limit with its normalized-charge subgroup of
`ℚ`; in particular no nonzero charge is collapsed by normalization. -/
theorem afChargeToRational_injective {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) : Function.Injective (afChargeToRational hd) := by
  apply Module.DirectLimit.lift_injective
  intro i x y hxy
  have hden : (chargeDenominator localDim i : ℚ) ≠ 0 := by
    exact_mod_cast (chargeTransitionFactor_pos hd 0 i).ne'
  change (x : ℚ) / (chargeDenominator localDim i : ℚ) =
    (y : ℚ) / (chargeDenominator localDim i : ℚ) at hxy
  field_simp [hden] at hxy
  exact_mod_cast hxy

/-- The AF charge limit is linearly equivalent to its normalized-charge subgroup of `ℚ`. -/
def afChargeLimitEquivRationalRange {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) :
    AFChargeLimit localDim ≃ₗ[ℤ] LinearMap.range (afChargeToRational hd) :=
  LinearEquiv.ofInjective (afChargeToRational hd) (afChargeToRational_injective hd)

theorem mem_afChargeToRational_range_iff {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (q : ℚ) :
    q ∈ LinearMap.range (afChargeToRational hd) ↔
      ∃ (i : ℕ) (z : ℤ), q = (z : ℚ) / (chargeDenominator localDim i : ℚ) := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, z, hz⟩ := chargeLimit_has_finiteAncestor localDim x
    refine ⟨i, z, ?_⟩
    rw [← hz, afChargeToRational_finiteStage]
  · rintro ⟨i, z, rfl⟩
    exact ⟨finiteStageCharge localDim i z, afChargeToRational_finiteStage hd i z⟩

@[simp] theorem chargeDenominator_qubit (i : ℕ) :
    chargeDenominator (fun _ => 2) i = 2 ^ i := by
  simp [chargeDenominator, chargeTransitionFactor]

/-- For qubit primes, normalized AF charge values are exactly dyadic rationals `z / 2^i`. -/
theorem mem_qubit_afChargeToRational_range_iff (q : ℚ) :
    q ∈ LinearMap.range (afChargeToRational (localDim := fun _ => 2) (by intro; norm_num)) ↔
      ∃ (i : ℕ) (z : ℤ), q = (z : ℚ) / (2 ^ i : ℕ) := by
  rw [mem_afChargeToRational_range_iff]
  simp only [chargeDenominator_qubit]

/-- Uniform convergence on one period to a nonvanishing loop preserves zero winding. This is the
norm-regular part of AF no-nucleation, stated directly for the determinant loops that carry the
integer charge. -/
theorem windingNumber_eq_zero_of_uniform_limit
    {gamma : ℝ → ℂ} {delta : ℕ → ℝ → ℂ}
    (hgammaCont : Continuous gamma) (hgammaNonzero : ∀ t, gamma t ≠ 0)
    (hgammaPer : Function.Periodic gamma (2 * Real.pi))
    (hdeltaCont : ∀ n, Continuous (delta n))
    (hdeltaPer : ∀ n, Function.Periodic (delta n) (2 * Real.pi))
    (hdeltaZero : ∀ n, RHTower.windingNumber (delta n) 0 (2 * Real.pi) = 0)
    (hconv : ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖delta n t - gamma t‖ < ε) :
    RHTower.windingNumber gamma 0 (2 * Real.pi) = 0 := by
  have hKne : (Set.Icc (0 : ℝ) (2 * Real.pi)).Nonempty :=
    Set.nonempty_Icc.mpr (le_of_lt Real.two_pi_pos)
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn hKne
    (hgammaCont.norm.continuousOn)
  have hmpos : 0 < ‖gamma t0‖ := norm_pos_iff.mpr (hgammaNonzero t0)
  have hlowPeriod : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖gamma t0‖ ≤ ‖gamma t‖ :=
    isMinOn_iff.mp hmin
  have hlow : ∀ t : ℝ, ‖gamma t0‖ ≤ ‖gamma t‖ := by
    intro t
    obtain ⟨y, hy, hval⟩ := hgammaPer.exists_mem_Ico₀ Real.two_pi_pos t
    rw [hval]
    exact hlowPeriod y (Set.Ico_subset_Icc_self hy)
  have hev := hconv ‖gamma t0‖ hmpos
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hclosePeriod := hN N le_rfl
  have hdiffPer : Function.Periodic (fun t => delta N t - gamma t) (2 * Real.pi) := by
    intro t
    show delta N (t + 2 * Real.pi) - gamma (t + 2 * Real.pi) = delta N t - gamma t
    rw [hdeltaPer N t, hgammaPer t]
  have hclose : ∀ t : ℝ, ‖delta N t - gamma t‖ < ‖gamma t0‖ := by
    intro t
    obtain ⟨y, hy, hval⟩ := hdiffPer.exists_mem_Ico₀ Real.two_pi_pos t
    rw [hval]
    exact hclosePeriod y (Set.Ico_subset_Icc_self hy)
  have hgammaLoop : gamma 0 = gamma (2 * Real.pi) := by
    simpa using (hgammaPer 0).symm
  have hdeltaLoop : delta N 0 = delta N (2 * Real.pi) := by
    simpa using (hdeltaPer N 0).symm
  have heq := RHTower.windingNumber_eq_of_close hgammaCont (hdeltaCont N)
    hgammaLoop hdeltaLoop hlow hclose
  rw [hdeltaZero N] at heq
  exact heq.symm

/-- Positive finite-ancestor form: if the norm-regular limit has nonzero winding, some finite
approximant already has nonzero winding. -/
theorem nonzero_winding_uniform_limit_has_finiteAncestor
    {gamma : ℝ → ℂ} {delta : ℕ → ℝ → ℂ}
    (hgammaCont : Continuous gamma) (hgammaNonzero : ∀ t, gamma t ≠ 0)
    (hgammaPer : Function.Periodic gamma (2 * Real.pi))
    (hdeltaCont : ∀ n, Continuous (delta n))
    (hdeltaPer : ∀ n, Function.Periodic (delta n) (2 * Real.pi))
    (hconv : ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖delta n t - gamma t‖ < ε)
    (hcharge : RHTower.windingNumber gamma 0 (2 * Real.pi) ≠ 0) :
    ∃ n, RHTower.windingNumber (delta n) 0 (2 * Real.pi) ≠ 0 := by
  by_contra h
  push Not at h
  exact hcharge (windingNumber_eq_zero_of_uniform_limit hgammaCont hgammaNonzero hgammaPer
    hdeltaCont hdeltaPer h hconv)

end

end PrimeQuasiLocalCharge
