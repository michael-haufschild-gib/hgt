import GaloisForLFunctions.RHTower.PrimeShiftMarcinkiewiczTrichotomy
import GaloisForLFunctions.RHTower.SingularCoronaResidueIncidenceTrilemma
import GaloisForLFunctions.RHTower.Deninger.DeningerSeminormInducedCompleted
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.GraphPushoutSplitting
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Algebra.Exact.Basic

/-!
# Logarithmic Marcinkiewicz prime-tail Banach quotient

Constructs genuine completed `M_log`, closed finite-support part `M₀`, and Banach quotient
`Q_log`. Proves exact tail-closure criterion, unit and critical-character quotient norm one,
right/line/left and reflection classifications, arbitrary Hahn--Banach readers, instantiated
unit-pullback and bounded-reader-pushout splittings, and canonical residue-graph boundary.
-/

open Complex Filter Topology
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Complex logarithmic Marcinkiewicz cutoff quotient. -/
def complexMarcinkiewiczQuotient (b : ℕ → ℂ) (X : ℕ) : ℝ :=
  marcinkiewiczLogQuotient (absField b) X

/-- Complex fields with uniformly bounded logarithmic Marcinkiewicz cutoffs. -/
def marcinkiewiczLogPreSubmodule : Submodule ℂ (ℕ → ℂ) where
  carrier := {b | MemMarcinkiewiczLogLayer (absField b)}
  zero_mem' := by
    refine ⟨0, fun X hX => ?_⟩
    simp [marcinkiewiczLogQuotient, primeLogMass_weightedEulerCoefficientSpaces, absField]
  add_mem' := by
    intro b c hb hc
    obtain ⟨B, hB⟩ := hb
    obtain ⟨C, hC⟩ := hc
    refine ⟨B + C, fun X hX => ?_⟩
    exact (marcinkiewiczLogQuotient_absField_add_le b c hX).trans
      (add_le_add (hB X hX) (hC X hX))
  smul_mem' := by
    intro a b hb
    obtain ⟨B, hB⟩ := hb
    refine ⟨‖a‖ * B, fun X hX => ?_⟩
    rw [marcinkiewiczLogQuotient_absField_smul]
    exact mul_le_mul_of_nonneg_left (hB X hX) (norm_nonneg a)

/-- Algebraic carrier before Hausdorff quotient and completion. -/
abbrev MarcinkiewiczLogPre : Type := marcinkiewiczLogPreSubmodule

/-- Cutoff family whose supremum is the logarithmic Marcinkiewicz seminorm. -/
def marcinkiewiczCutoffRange (b : MarcinkiewiczLogPre) : Set ℝ :=
  Set.range fun X : {X : ℕ // 2 ≤ X} => complexMarcinkiewiczQuotient b X

theorem marcinkiewiczCutoffRange_nonempty (b : MarcinkiewiczLogPre) :
    (marcinkiewiczCutoffRange b).Nonempty := Set.range_nonempty _

theorem marcinkiewiczCutoffRange_bddAbove (b : MarcinkiewiczLogPre) :
    BddAbove (marcinkiewiczCutoffRange b) := by
  obtain ⟨C, hC⟩ := b.property
  refine ⟨C, ?_⟩
  rintro y ⟨X, rfl⟩
  exact hC X X.property

/-- Exact finite logarithmic Marcinkiewicz supremum on the bounded carrier. -/
def marcinkiewiczPreNorm (b : MarcinkiewiczLogPre) : ℝ :=
  sSup (marcinkiewiczCutoffRange b)

theorem complexMarcinkiewiczQuotient_le_preNorm
    (b : MarcinkiewiczLogPre) {X : ℕ} (hX : 2 ≤ X) :
    complexMarcinkiewiczQuotient b X ≤ marcinkiewiczPreNorm b := by
  exact le_csSup (marcinkiewiczCutoffRange_bddAbove b)
    ⟨⟨X, hX⟩, rfl⟩

theorem marcinkiewiczPreNorm_le (b : MarcinkiewiczLogPre) {C : ℝ}
    (hC : ∀ X : ℕ, 2 ≤ X → complexMarcinkiewiczQuotient b X ≤ C) :
    marcinkiewiczPreNorm b ≤ C := by
  apply csSup_le (marcinkiewiczCutoffRange_nonempty b)
  rintro y ⟨X, rfl⟩
  exact hC X X.property

theorem complexMarcinkiewiczQuotient_nonneg (b : ℕ → ℂ) {X : ℕ} (hX : 2 ≤ X) :
    0 ≤ complexMarcinkiewiczQuotient b X := by
  exact div_nonneg (primeLogMass_nonneg_weightedEulerCoefficientSpaces (absField b) X) (log_cutoff_pos hX).le

theorem marcinkiewiczPreNorm_nonneg (b : MarcinkiewiczLogPre) :
    0 ≤ marcinkiewiczPreNorm b := by
  exact (complexMarcinkiewiczQuotient_nonneg b (show 2 ≤ 2 by omega)).trans
    (complexMarcinkiewiczQuotient_le_preNorm b (show 2 ≤ 2 by omega))

@[simp] theorem marcinkiewiczPreNorm_zero :
    marcinkiewiczPreNorm (0 : MarcinkiewiczLogPre) = 0 := by
  apply le_antisymm
  · apply marcinkiewiczPreNorm_le
    intro X hX
    simp [complexMarcinkiewiczQuotient, marcinkiewiczLogQuotient, primeLogMass_weightedEulerCoefficientSpaces, absField]
  · exact marcinkiewiczPreNorm_nonneg 0

theorem marcinkiewiczPreNorm_add_le (b c : MarcinkiewiczLogPre) :
    marcinkiewiczPreNorm (b + c) ≤ marcinkiewiczPreNorm b + marcinkiewiczPreNorm c := by
  apply marcinkiewiczPreNorm_le
  intro X hX
  exact (marcinkiewiczLogQuotient_absField_add_le b c hX).trans
    (add_le_add (complexMarcinkiewiczQuotient_le_preNorm b hX)
      (complexMarcinkiewiczQuotient_le_preNorm c hX))

theorem marcinkiewiczPreNorm_smul (a : ℂ) (b : MarcinkiewiczLogPre) :
    marcinkiewiczPreNorm (a • b) = ‖a‖ * marcinkiewiczPreNorm b := by
  have upper : ∀ (c : ℂ) (x : MarcinkiewiczLogPre),
      marcinkiewiczPreNorm (c • x) ≤ ‖c‖ * marcinkiewiczPreNorm x := by
    intro c x
    apply marcinkiewiczPreNorm_le
    intro X hX
    change marcinkiewiczLogQuotient (absField (c • (x : ℕ → ℂ))) X ≤ _
    rw [marcinkiewiczLogQuotient_absField_smul]
    exact mul_le_mul_of_nonneg_left
      (complexMarcinkiewiczQuotient_le_preNorm x hX) (norm_nonneg c)
  apply le_antisymm (upper a b)
  · by_cases ha : a = 0
    · subst a
      simp
    · have hinv := upper a⁻¹ (a • b)
      have hsimp : a⁻¹ • (a • b) = b := by simp [ha]
      rw [hsimp, norm_inv] at hinv
      calc
        ‖a‖ * marcinkiewiczPreNorm b ≤
            ‖a‖ * (‖a‖⁻¹ * marcinkiewiczPreNorm (a • b)) :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg a)
        _ = marcinkiewiczPreNorm (a • b) := by
          rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul]

/-- Logarithmic Marcinkiewicz seminorm on the bounded field carrier. -/
def marcinkiewiczLogSeminorm : Seminorm ℂ MarcinkiewiczLogPre :=
  Seminorm.of marcinkiewiczPreNorm marcinkiewiczPreNorm_add_le marcinkiewiczPreNorm_smul

/-- Banach completion of the logarithmic Marcinkiewicz prime-field seminorm. -/
abbrev MarcinkiewiczLog : Type :=
  DeningerSeminormCompletion marcinkiewiczLogSeminorm

/-- Canonical prime-field map into the Banach completion. -/
noncomputable def marcinkiewiczLogMk : MarcinkiewiczLogPre →ₗ[ℂ] MarcinkiewiczLog :=
  deningerSeminormMkC marcinkiewiczLogSeminorm

@[simp] theorem marcinkiewiczLogMk_norm (b : MarcinkiewiczLogPre) :
    ‖marcinkiewiczLogMk b‖ = marcinkiewiczPreNorm b :=
  deningerSeminormMkC_norm _ b

/-- Finite-support fields inside the bounded algebraic carrier. -/
def marcinkiewiczFiniteSupportPre : Submodule ℂ MarcinkiewiczLogPre where
  carrier := {b | (Function.support (b : ℕ → ℂ)).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro b c hb hc
    change (Function.support (fun n => (b : ℕ → ℂ) n + (c : ℕ → ℂ) n)).Finite
    exact (hb.union hc).subset
      (Function.support_add (b : ℕ → ℂ) (c : ℕ → ℂ))
  smul_mem' := by
    intro a b hb
    change (Function.support (fun n => a * (b : ℕ → ℂ) n)).Finite
    exact hb.subset (Function.support_const_smul_subset a (b : ℕ → ℂ))

/-- Closed `M₀`: closure of finite-support fields in completed `M_log`. -/
def MarcinkiewiczZero : Submodule ℂ MarcinkiewiczLog :=
  (marcinkiewiczFiniteSupportPre.map marcinkiewiczLogMk).topologicalClosure

theorem isClosed_marcinkiewiczZero : IsClosed (MarcinkiewiczZero : Set MarcinkiewiczLog) :=
  Submodule.isClosed_topologicalClosure _

/-- Finite-unit-invariant quotient `Q_log = M_log / M₀`. -/
abbrev MarcinkiewiczLogQuotient : Type := MarcinkiewiczLog ⧸ MarcinkiewiczZero

/-- Quotient map from `M_log` to `Q_log`. -/
noncomputable def marcinkiewiczLogQuotientMk :
    MarcinkiewiczLog →ₗ[ℂ] MarcinkiewiczLogQuotient :=
  MarcinkiewiczZero.mkQ

example : CompleteSpace MarcinkiewiczLog := inferInstance
example : CompleteSpace MarcinkiewiczLogQuotient := inferInstance

/-- Every finitely-supported complex field is a vanishing Marcinkiewicz tail. -/
theorem memVanishingTailLayer_absField_of_finiteSupport {b : ℕ → ℂ}
    (hb : (Function.support b).Finite) :
    MemVanishingTailLayer (absField b) := by
  obtain ⟨P, hP⟩ := hb.bddAbove
  intro ε hε
  refine ⟨P, fun X hX => ?_⟩
  have htail : primeCoefficientTail (absField b) P = 0 := by
    funext n
    by_cases hPn : P < n
    · have hbn : b n = 0 := by
        by_contra hn
        exact (not_le_of_gt hPn) (hP (by simpa [Function.mem_support] using hn))
      simp [primeCoefficientTail, hPn, absField, hbn]
    · simp [primeCoefficientTail, hPn]
  rw [htail]
  simp [marcinkiewiczLogQuotient, primeLogMass_weightedEulerCoefficientSpaces, hε.le]

/-- Truncation tails contract every finite cutoff. -/
theorem complexMarcinkiewiczQuotient_tail_le (b : ℕ → ℂ) (P : ℕ)
    {X : ℕ} (hX : 2 ≤ X) :
    complexMarcinkiewiczQuotient (primeFieldTail b P) X ≤
      complexMarcinkiewiczQuotient b X := by
  rw [complexMarcinkiewiczQuotient, absField_primeFieldTail]
  unfold marcinkiewiczLogQuotient
  apply div_le_div_of_nonneg_right _ (log_cutoff_pos hX).le
  have hsplit := primeLogMass_head_add_tail (absField b) P X
  have hhead := primeLogMass_nonneg_weightedEulerCoefficientSpaces (primeCoefficientHead (absField b) P) X
  linarith

/-- Truncation tail as an element of the bounded carrier. -/
def marcinkiewiczTailPre (b : MarcinkiewiczLogPre) (P : ℕ) : MarcinkiewiczLogPre := by
  refine ⟨primeFieldTail b P, ?_⟩
  obtain ⟨C, hC⟩ := b.property
  exact ⟨C, fun X hX => (complexMarcinkiewiczQuotient_tail_le b P hX).trans (hC X hX)⟩

/-- Finite head as an element of the bounded carrier. -/
def marcinkiewiczHeadPre (b : MarcinkiewiczLogPre) (P : ℕ) : MarcinkiewiczLogPre := by
  refine ⟨primeFieldHead b P, ?_⟩
  exact memMarcinkiewiczLogLayer_of_memVanishingTailLayer
    (memVanishingTailLayer_absField_of_finiteSupport (finite_support_primeFieldHead b P))

@[simp] theorem marcinkiewiczTailPre_coe (b : MarcinkiewiczLogPre) (P : ℕ) :
    (marcinkiewiczTailPre b P : ℕ → ℂ) = primeFieldTail b P := rfl

@[simp] theorem marcinkiewiczHeadPre_coe (b : MarcinkiewiczLogPre) (P : ℕ) :
    (marcinkiewiczHeadPre b P : ℕ → ℂ) = primeFieldHead b P := rfl

theorem marcinkiewiczPre_sub_head (b : MarcinkiewiczLogPre) (P : ℕ) :
    b - marcinkiewiczHeadPre b P = marcinkiewiczTailPre b P := by
  apply Subtype.ext
  exact sub_primeFieldHead b P

theorem marcinkiewiczPreNorm_tail_le (b : MarcinkiewiczLogPre) (P : ℕ) :
    marcinkiewiczPreNorm (marcinkiewiczTailPre b P) ≤ marcinkiewiczPreNorm b := by
  apply marcinkiewiczPreNorm_le
  intro X hX
  exact (complexMarcinkiewiczQuotient_tail_le b P hX).trans
    (complexMarcinkiewiczQuotient_le_preNorm b hX)

theorem marcinkiewiczHeadPre_mem_finiteSupport (b : MarcinkiewiczLogPre) (P : ℕ) :
    marcinkiewiczHeadPre b P ∈ marcinkiewiczFiniteSupportPre :=
  finite_support_primeFieldHead b P

theorem primeFieldTail_sub (b c : ℕ → ℂ) (P : ℕ) :
    primeFieldTail (b - c) P = primeFieldTail b P - primeFieldTail c P := by
  funext n
  by_cases hPn : P < n <;> simp [primeFieldTail, hPn]

theorem primeFieldTail_eq_zero_of_support_le {b : ℕ → ℂ} {P : ℕ}
    (hP : ∀ n ∈ Function.support b, n ≤ P) : primeFieldTail b P = 0 := by
  funext n
  by_cases hPn : P < n
  · have hbn : b n = 0 := by
      by_contra hn
      exact (not_le_of_gt hPn) (hP n (by simpa [Function.mem_support] using hn))
    simp [primeFieldTail, hPn, hbn]
  · simp [primeFieldTail, hPn]

/-- Exact closure criterion: an algebraic bounded field lands in completed `M₀` iff its
truncation tails vanish uniformly in the logarithmic Marcinkiewicz seminorm. -/
theorem marcinkiewiczLogMk_mem_zero_iff (b : MarcinkiewiczLogPre) :
    marcinkiewiczLogMk b ∈ MarcinkiewiczZero ↔
      MemVanishingTailLayer (absField b) := by
  constructor
  · intro hb0
    intro ε hε
    change marcinkiewiczLogMk b ∈
      (marcinkiewiczFiniteSupportPre.map marcinkiewiczLogMk).topologicalClosure at hb0
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hb0
    have hbcl := hb0
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hbcl ε hε
    obtain ⟨f, hf, rfl⟩ := hy
    obtain ⟨P, hP⟩ := hf.bddAbove
    refine ⟨P, fun X hX => ?_⟩
    have htailf : primeFieldTail (f : ℕ → ℂ) P = 0 :=
      primeFieldTail_eq_zero_of_support_le hP
    have htailEq : marcinkiewiczTailPre b P = marcinkiewiczTailPre (b - f) P := by
      apply Subtype.ext
      change primeFieldTail (b : ℕ → ℂ) P =
        primeFieldTail ((b : ℕ → ℂ) - (f : ℕ → ℂ)) P
      rw [primeFieldTail_sub, htailf, sub_zero]
    have hnormSub : marcinkiewiczPreNorm (b - f) < ε := by
      simpa [dist_eq_norm, ← map_sub, marcinkiewiczLogMk_norm] using hdist
    rw [← absField_primeFieldTail]
    change complexMarcinkiewiczQuotient (marcinkiewiczTailPre b P) X ≤ ε
    rw [htailEq]
    exact (complexMarcinkiewiczQuotient_le_preNorm _ hX).trans
      ((marcinkiewiczPreNorm_tail_le (b - f) P).trans hnormSub.le)
  · intro htail
    change marcinkiewiczLogMk b ∈
      (marcinkiewiczFiniteSupportPre.map marcinkiewiczLogMk).topologicalClosure
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    show marcinkiewiczLogMk b ∈
      closure (marcinkiewiczFiniteSupportPre.map marcinkiewiczLogMk : Set MarcinkiewiczLog)
    ·
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨P, hP⟩ := htail (ε / 2) (half_pos hε)
      refine ⟨marcinkiewiczLogMk (marcinkiewiczHeadPre b P), ?_, ?_⟩
      · exact ⟨marcinkiewiczHeadPre b P,
          marcinkiewiczHeadPre_mem_finiteSupport b P, rfl⟩
      · rw [dist_eq_norm, ← map_sub, marcinkiewiczLogMk_norm,
          marcinkiewiczPre_sub_head]
        have hle : marcinkiewiczPreNorm (marcinkiewiczTailPre b P) ≤ ε / 2 := by
          apply marcinkiewiczPreNorm_le
          intro X hX
          rw [complexMarcinkiewiczQuotient, marcinkiewiczTailPre_coe,
            absField_primeFieldTail]
          exact hP X hX
        linarith

/-- Every finite-support embedded field vanishes in `Q_log`. -/
theorem marcinkiewiczLogQuotientMk_mk_eq_zero_of_finiteSupport
    (b : MarcinkiewiczLogPre) (hb : b ∈ marcinkiewiczFiniteSupportPre) :
    marcinkiewiczLogQuotientMk (marcinkiewiczLogMk b) = 0 := by
  change MarcinkiewiczZero.mkQ (marcinkiewiczLogMk b) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (marcinkiewiczLogMk_mem_zero_iff b).2
    (memVanishingTailLayer_absField_of_finiteSupport hb)

/-- Real finite-support fields are vanishing Marcinkiewicz tails. -/
theorem memVanishingTailLayer_of_finiteSupport {b : ℕ → ℝ}
    (hb : (Function.support b).Finite) : MemVanishingTailLayer b := by
  obtain ⟨P, hP⟩ := hb.bddAbove
  intro ε hε
  refine ⟨P, fun X hX => ?_⟩
  have htail : primeCoefficientTail b P = 0 := by
    funext n
    by_cases hPn : P < n
    · have hbn : b n = 0 := by
        by_contra hn
        exact (not_le_of_gt hPn) (hP (by simpa [Function.mem_support] using hn))
      simp [primeCoefficientTail, hPn, hbn]
    · simp [primeCoefficientTail, hPn]
  rw [htail]
  simp [marcinkiewiczLogQuotient, primeLogMass_weightedEulerCoefficientSpaces, hε.le]

/-- Actual complex Euler unit as a bounded algebraic Marcinkiewicz field. -/
def marcinkiewiczUnitPre : MarcinkiewiczLogPre := by
  refine ⟨fun _ => 1, ?_⟩
  change MemMarcinkiewiczLogLayer (absField fun _ : ℕ => (1 : ℂ))
  have hEq : absField (fun _ : ℕ => (1 : ℂ)) = fun _ => (1 : ℝ) := by
    funext n
    simp [absField]
  rw [hEq]
  exact unitField_memMarcinkiewiczLogLayer

/-- Actual Euler unit in completed `M_log`. -/
noncomputable def marcinkiewiczUnit : MarcinkiewiczLog :=
  marcinkiewiczLogMk marcinkiewiczUnitPre

/-- Surviving Euler unit class in `Q_log`. -/
noncomputable def marcinkiewiczUnitClass : MarcinkiewiczLogQuotient :=
  marcinkiewiczLogQuotientMk marcinkiewiczUnit

/-- Every finite modification of the unit remains at Marcinkiewicz distance at least one. -/
theorem one_le_marcinkiewiczPreNorm_unit_sub_finite
    (f : MarcinkiewiczLogPre) (hf : f ∈ marcinkiewiczFiniteSupportPre) :
    1 ≤ marcinkiewiczPreNorm (marcinkiewiczUnitPre - f) := by
  let x : ℕ → ℝ := absField ((marcinkiewiczUnitPre - f : MarcinkiewiczLogPre) : ℕ → ℂ)
  have hsupp : (Function.support (fun n => x n - 1)).Finite := by
    refine hf.subset ?_
    intro n hn
    contrapose! hn
    have hfn : (f : ℕ → ℂ) n = 0 := Function.notMem_support.mp hn
    simp [x, absField, marcinkiewiczUnitPre, hfn]
  have hnull : MemVanishingTailLayer (fun n => x n - 1) :=
    memVanishingTailLayer_of_finiteSupport hsupp
  have hbound : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient x X ≤
      marcinkiewiczPreNorm (marcinkiewiczUnitPre - f) := by
    intro X hX
    exact complexMarcinkiewiczQuotient_le_preNorm _ hX
  have h := abs_le_of_marcinkiewiczLogQuotient_le (x := x) (c := 1)
    (C := marcinkiewiczPreNorm (marcinkiewiczUnitPre - f)) hnull hbound
  simpa using h

/-- Every point of closed `M₀` stays at distance at least one from actual Euler unit. -/
theorem one_le_dist_marcinkiewiczUnit_marcinkiewiczZero
    (m : MarcinkiewiczLog) (hm : m ∈ MarcinkiewiczZero) :
    1 ≤ dist marcinkiewiczUnit m := by
  apply le_of_forall_pos_le_add
  intro ε hε
  change m ∈ (marcinkiewiczFiniteSupportPre.map marcinkiewiczLogMk).topologicalClosure at hm
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hm
  obtain ⟨y, hy, hmy⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨f, hf, rfl⟩ := hy
  have hlower : 1 ≤ dist marcinkiewiczUnit (marcinkiewiczLogMk f) := by
    rw [dist_eq_norm, marcinkiewiczUnit, ← map_sub, marcinkiewiczLogMk_norm]
    exact one_le_marcinkiewiczPreNorm_unit_sub_finite f hf
  have htri := dist_triangle marcinkiewiczUnit m (marcinkiewiczLogMk f)
  linarith

/-- Unit truncation tails have asymptotic seminorm at most one. -/
theorem marcinkiewiczUnit_tail_preNorm_le_one_add { ε : ℝ } (hε : 0 < ε) :
    ∃ P : ℕ, marcinkiewiczPreNorm (marcinkiewiczTailPre marcinkiewiczUnitPre P) ≤ 1 + ε := by
  obtain ⟨P, hP2, hPlog⟩ := exists_nat_two_le_log_ge (mertensPrimeConstant / ε)
  refine ⟨P, ?_⟩
  apply marcinkiewiczPreNorm_le
  intro X hX
  by_cases hXP : X ≤ P
  · rw [complexMarcinkiewiczQuotient, marcinkiewiczTailPre_coe,
      absField_primeFieldTail]
    have hmass0 : primeLogMass_weightedEulerCoefficientSpaces
        (primeCoefficientTail (absField (marcinkiewiczUnitPre : ℕ → ℂ)) P) X = 0 := by
      unfold primeLogMass_weightedEulerCoefficientSpaces
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      have hnP : ¬P < n := not_lt_of_ge (hn.1.2.trans hXP)
      simp [primeCoefficientTail, hnP]
    rw [marcinkiewiczLogQuotient, hmass0, zero_div]
    linarith
  · have hPX : P ≤ X := Nat.le_of_lt (lt_of_not_ge hXP)
    have hlogP : Real.log P ≤ Real.log X :=
      Real.log_le_log (by positivity) (by exact_mod_cast hPX)
    have hCeps : mertensPrimeConstant ≤ ε * Real.log P := by
      rw [div_le_iff₀ hε] at hPlog
      nlinarith
    have hmassTail : primeLogMass_weightedEulerCoefficientSpaces
        (primeCoefficientTail (fun _ => (1 : ℝ)) P) X ≤
        primeLogMass_weightedEulerCoefficientSpaces (fun _ => (1 : ℝ)) X := by
      have hsplit := primeLogMass_head_add_tail (fun _ => (1 : ℝ)) P X
      have hhead := primeLogMass_nonneg_weightedEulerCoefficientSpaces
        (primeCoefficientHead (fun _ => (1 : ℝ)) P) X
      linarith
    have hmassUnit := primeLogMass_unit_le X (by omega)
    have hmass : primeLogMass_weightedEulerCoefficientSpaces
        (primeCoefficientTail (fun _ => (1 : ℝ)) P) X ≤
        (1 + ε) * Real.log X := by
      have hC : mertensPrimeConstant ≤ ε * Real.log X :=
        hCeps.trans (mul_le_mul_of_nonneg_left hlogP hε.le)
      nlinarith
    have habs : absField (marcinkiewiczUnitPre : ℕ → ℂ) = fun _ => (1 : ℝ) := by
      funext n
      simp [absField, marcinkiewiczUnitPre]
    rw [complexMarcinkiewiczQuotient, marcinkiewiczTailPre_coe,
      absField_primeFieldTail, habs, marcinkiewiczLogQuotient]
    rwa [div_le_iff₀ (log_cutoff_pos hX)]

/-- **Exact unit quotient norm**: the actual Euler tail survives with norm one. -/
theorem norm_marcinkiewiczUnitClass : ‖marcinkiewiczUnitClass‖ = 1 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨P, hP⟩ := marcinkiewiczUnit_tail_preNorm_le_one_add hε
    have hhead0 : marcinkiewiczLogQuotientMk
        (marcinkiewiczLogMk (marcinkiewiczHeadPre marcinkiewiczUnitPre P)) = 0 :=
      marcinkiewiczLogQuotientMk_mk_eq_zero_of_finiteSupport _
        (marcinkiewiczHeadPre_mem_finiteSupport _ _)
    have hclass : marcinkiewiczUnitClass = marcinkiewiczLogQuotientMk
        (marcinkiewiczLogMk (marcinkiewiczTailPre marcinkiewiczUnitPre P)) := by
      rw [marcinkiewiczUnitClass, marcinkiewiczUnit, ← marcinkiewiczPre_sub_head]
      simp only [map_sub, hhead0, sub_zero]
    rw [hclass]
    exact (Submodule.Quotient.norm_mk_le MarcinkiewiczZero
      (marcinkiewiczLogMk (marcinkiewiczTailPre marcinkiewiczUnitPre P))).trans
        ((marcinkiewiczLogMk_norm _).trans_le hP)
  · rw [marcinkiewiczUnitClass, marcinkiewiczLogQuotientMk, Submodule.mkQ_apply]
    have hnorm : ‖(Submodule.Quotient.mk marcinkiewiczUnit :
        MarcinkiewiczLogQuotient)‖ =
        Metric.infDist marcinkiewiczUnit (MarcinkiewiczZero : Set MarcinkiewiczLog) :=
      QuotientAddGroup.norm_mk marcinkiewiczUnit
    rw [hnorm]
    rw [Metric.le_infDist ⟨0, MarcinkiewiczZero.zero_mem⟩]
    intro m hm
    exact one_le_dist_marcinkiewiczUnit_marcinkiewiczZero m hm

theorem marcinkiewiczUnitClass_ne_zero : marcinkiewiczUnitClass ≠ 0 := by
  intro h
  have := congrArg norm h
  simpa [norm_marcinkiewiczUnitClass] using this

/-- Hahn--Banach supplies a bounded reader assigning any prescribed scalar to Euler unit class. -/
theorem exists_marcinkiewiczUnit_reader (c : ℂ) :
    ∃ Λ : MarcinkiewiczLogQuotient →L[ℂ] ℂ, Λ marcinkiewiczUnitClass = c := by
  obtain ⟨g, hg, hgu⟩ := exists_dual_vector ℂ marcinkiewiczUnitClass
    (by rw [norm_marcinkiewiczUnitClass]; norm_num)
  refine ⟨c • g, ?_⟩
  rw [smul_apply, hgu, norm_marcinkiewiczUnitClass]
  simp

/-- A unit-modulus prime field differs from one by finite support after any finite modification,
in the precise real tail topology used by the Mertens conormal. -/
theorem one_le_marcinkiewiczPreNorm_sub_finite_of_abs_primes
    (b f : MarcinkiewiczLogPre)
    (hb : ∀ p : ℕ, p.Prime → absField (b : ℕ → ℂ) p = 1)
    (hf : f ∈ marcinkiewiczFiniteSupportPre) :
    1 ≤ marcinkiewiczPreNorm (b - f) := by
  let x : ℕ → ℝ := absField ((b - f : MarcinkiewiczLogPre) : ℕ → ℂ)
  let g : ℕ → ℝ := fun n => if n.Prime then x n - 1 else 0
  have hsupport : Function.support g ⊆ Function.support (f : ℕ → ℂ) := by
    intro n hn
    by_contra hnf
    have hfn : (f : ℕ → ℂ) n = 0 := Function.notMem_support.mp hnf
    by_cases hnp : n.Prime
    · have hbn := hb n hnp
      have hx : x n = 1 := by
        change ‖(b : ℕ → ℂ) n - (f : ℕ → ℂ) n‖ = 1
        rw [hfn, sub_zero]
        exact hbn
      exact hn (by simp [g, hnp, hx])
    · exact hn (by simp [g, hnp])
  have hgfinite : (Function.support g).Finite := hf.subset hsupport
  have hgnull : MemVanishingTailLayer g :=
    memVanishingTailLayer_of_finiteSupport hgfinite
  have hnull : MemVanishingTailLayer (fun n => x n - 1) :=
    memVanishingTailLayer_congr_primes
      (fun p hp => by simp [g, hp]) hgnull
  have hbound : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient x X ≤
      marcinkiewiczPreNorm (b - f) := by
    intro X hX
    exact complexMarcinkiewiczQuotient_le_preNorm _ hX
  have h := abs_le_of_marcinkiewiczLogQuotient_le (x := x) (c := 1)
    (C := marcinkiewiczPreNorm (b - f)) hnull hbound
  simpa using h

theorem one_le_dist_marcinkiewiczLogMk_marcinkiewiczZero_of_abs_primes
    (b : MarcinkiewiczLogPre)
    (hb : ∀ p : ℕ, p.Prime → absField (b : ℕ → ℂ) p = 1)
    (m : MarcinkiewiczLog) (hm : m ∈ MarcinkiewiczZero) :
    1 ≤ dist (marcinkiewiczLogMk b) m := by
  apply le_of_forall_pos_le_add
  intro ε hε
  change m ∈ (marcinkiewiczFiniteSupportPre.map marcinkiewiczLogMk).topologicalClosure at hm
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hm
  obtain ⟨y, hy, hmy⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨f, hf, rfl⟩ := hy
  have hlower : 1 ≤ dist (marcinkiewiczLogMk b) (marcinkiewiczLogMk f) := by
    rw [dist_eq_norm, ← map_sub, marcinkiewiczLogMk_norm]
    exact one_le_marcinkiewiczPreNorm_sub_finite_of_abs_primes b f hb hf
  have htri := dist_triangle (marcinkiewiczLogMk b) m (marcinkiewiczLogMk f)
  linarith

theorem complexMarcinkiewiczQuotient_tail_eq_unit_of_abs_primes
    (b : MarcinkiewiczLogPre)
    (hb : ∀ p : ℕ, p.Prime → absField (b : ℕ → ℂ) p = 1)
    (P X : ℕ) :
    complexMarcinkiewiczQuotient (marcinkiewiczTailPre b P) X =
      complexMarcinkiewiczQuotient (marcinkiewiczTailPre marcinkiewiczUnitPre P) X := by
  unfold complexMarcinkiewiczQuotient marcinkiewiczLogQuotient
  congr 1
  rw [marcinkiewiczTailPre_coe, marcinkiewiczTailPre_coe,
    absField_primeFieldTail, absField_primeFieldTail]
  apply primeLogMass_congr_primes
  intro p hp
  by_cases hPp : P < p
  · have hbp : ‖(b : ℕ → ℂ) p‖ = 1 := by
      simpa [absField] using hb p hp
    simp [primeCoefficientTail, hPp, hbp, absField, marcinkiewiczUnitPre]
  · simp [primeCoefficientTail, hPp]

theorem marcinkiewiczPreNorm_tail_le_unit_of_abs_primes
    (b : MarcinkiewiczLogPre)
    (hb : ∀ p : ℕ, p.Prime → absField (b : ℕ → ℂ) p = 1)
    (P : ℕ) :
    marcinkiewiczPreNorm (marcinkiewiczTailPre b P) ≤
      marcinkiewiczPreNorm (marcinkiewiczTailPre marcinkiewiczUnitPre P) := by
  apply marcinkiewiczPreNorm_le
  intro X hX
  rw [complexMarcinkiewiczQuotient_tail_eq_unit_of_abs_primes b hb]
  exact complexMarcinkiewiczQuotient_le_preNorm _ hX

/-- Every bounded prime field of unit modulus has quotient norm exactly one. -/
theorem norm_marcinkiewiczLogQuotientMk_mk_eq_one_of_abs_primes
    (b : MarcinkiewiczLogPre)
    (hb : ∀ p : ℕ, p.Prime → absField (b : ℕ → ℂ) p = 1) :
    ‖marcinkiewiczLogQuotientMk (marcinkiewiczLogMk b)‖ = 1 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨P, hP⟩ := marcinkiewiczUnit_tail_preNorm_le_one_add hε
    have hhead0 : marcinkiewiczLogQuotientMk
        (marcinkiewiczLogMk (marcinkiewiczHeadPre b P)) = 0 :=
      marcinkiewiczLogQuotientMk_mk_eq_zero_of_finiteSupport _
        (marcinkiewiczHeadPre_mem_finiteSupport _ _)
    have hclass : marcinkiewiczLogQuotientMk (marcinkiewiczLogMk b) =
        marcinkiewiczLogQuotientMk (marcinkiewiczLogMk (marcinkiewiczTailPre b P)) := by
      rw [← marcinkiewiczPre_sub_head]
      simp only [map_sub, hhead0, sub_zero]
    rw [hclass]
    exact (Submodule.Quotient.norm_mk_le MarcinkiewiczZero
      (marcinkiewiczLogMk (marcinkiewiczTailPre b P))).trans
        ((marcinkiewiczLogMk_norm _).trans_le
          ((marcinkiewiczPreNorm_tail_le_unit_of_abs_primes b hb P).trans hP))
  · rw [marcinkiewiczLogQuotientMk, Submodule.mkQ_apply]
    have hnorm : ‖(Submodule.Quotient.mk (marcinkiewiczLogMk b) :
        MarcinkiewiczLogQuotient)‖ =
        Metric.infDist (marcinkiewiczLogMk b) (MarcinkiewiczZero : Set MarcinkiewiczLog) :=
      QuotientAddGroup.norm_mk (marcinkiewiczLogMk b)
    rw [hnorm, Metric.le_infDist ⟨0, MarcinkiewiczZero.zero_mem⟩]
    intro m hm
    exact one_le_dist_marcinkiewiczLogMk_marcinkiewiczZero_of_abs_primes b hb m hm

/-- Prime-shift character in algebraic `M_log` whenever it lies on or right of critical line. -/
def marcinkiewiczPrimeShiftPre (z : ℂ) (hz : 1 / 2 ≤ z.re) : MarcinkiewiczLogPre :=
  ⟨primeShiftCharacter z,
    (memMarcinkiewiczLogLayer_primeShiftCharacter_iff_half_le_re z).2 hz⟩

/-- Quotient class of a bounded normalized prime-shift character. -/
noncomputable def marcinkiewiczPrimeShiftClass (z : ℂ) (hz : 1 / 2 ≤ z.re) :
    MarcinkiewiczLogQuotient :=
  marcinkiewiczLogQuotientMk (marcinkiewiczLogMk (marcinkiewiczPrimeShiftPre z hz))

/-- Critical-line characters have exact essential Marcinkiewicz norm one. -/
theorem norm_marcinkiewiczPrimeShiftClass_of_re_eq_half
    (z : ℂ) (hz : z.re = 1 / 2) :
    ‖marcinkiewiczPrimeShiftClass z hz.ge‖ = 1 := by
  apply norm_marcinkiewiczLogQuotientMk_mk_eq_one_of_abs_primes
  intro p hp
  exact absField_primeShiftCharacter_eq_one_on_primes z hz hp

/-- Strict-right characters vanish in completed `M₀` and hence in `Q_log`. -/
theorem marcinkiewiczPrimeShiftClass_eq_zero_of_half_lt_re
    (z : ℂ) (hz : 1 / 2 < z.re) :
    marcinkiewiczPrimeShiftClass z hz.le = 0 := by
  rw [marcinkiewiczPrimeShiftClass, marcinkiewiczLogQuotientMk]
  change MarcinkiewiczZero.mkQ (marcinkiewiczLogMk (marcinkiewiczPrimeShiftPre z hz.le)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (marcinkiewiczLogMk_mem_zero_iff _).2
    (memVanishingTailLayer_absField_primeShiftCharacter_of_half_lt_re hz)

/-- Exact right/line quotient classification on the bounded half-plane. -/
theorem marcinkiewiczPrimeShiftClass_eq_zero_iff
    (z : ℂ) (hz : 1 / 2 ≤ z.re) :
    marcinkiewiczPrimeShiftClass z hz = 0 ↔ 1 / 2 < z.re := by
  constructor
  · intro hzero
    rcases hz.eq_or_lt with hline | hright
    · have hnorm := norm_marcinkiewiczPrimeShiftClass_of_re_eq_half z hline.symm
      have := congrArg norm hzero
      rw [hnorm] at this
      simp at this
    · exact hright
  · exact marcinkiewiczPrimeShiftClass_eq_zero_of_half_lt_re z

/-- Simultaneous boundedness of a character and its functional-equation reflection is already
equivalent to the critical line. -/
theorem primeShiftCharacter_and_reflection_mem_iff_re_eq_half (z : ℂ) :
    MemMarcinkiewiczLogLayer (absField (primeShiftCharacter z)) ∧
      MemMarcinkiewiczLogLayer
        (absField (primeShiftCharacter (1 - starRingEnd ℂ z))) ↔
      z.re = 1 / 2 := by
  rw [memMarcinkiewiczLogLayer_primeShiftCharacter_iff_half_le_re,
    memMarcinkiewiczLogLayer_primeShiftCharacter_iff_half_le_re]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  constructor <;> intro h
  · linarith
  · constructor <;> linarith

/-! ## Instantiated pullback, pushout, graph, and exactness boundaries -/

open HTGeometry.ConstraintRelativity

/-- Pullback of `M_log → Q_log` along the actual Euler unit line. -/
abbrev MarcinkiewiczUnitPullback : Type :=
  quotientUnitPullback MarcinkiewiczZero marcinkiewiczUnit

/-- Distinguished bounded splitting of the actual Euler unit pullback. -/
noncomputable def marcinkiewiczUnitPullbackSection :
    ℂ →L[ℂ] MarcinkiewiczUnitPullback :=
  quotientUnitPullbackSection MarcinkiewiczZero marcinkiewiczUnit

/-- The actual Euler lift splits its scalar-line pullback exactly. -/
theorem marcinkiewiczUnitPullbackProjection_section :
    (quotientUnitPullbackProjection MarcinkiewiczZero marcinkiewiczUnit).comp
      marcinkiewiczUnitPullbackSection = ContinuousLinearMap.id ℂ ℂ :=
  quotientUnitPullbackProjection_section MarcinkiewiczZero marcinkiewiczUnit

/-- Every bounded reader on `M₀` has a Hahn--Banach-split scalar graph pushout. -/
theorem isClosed_marcinkiewiczGraphPushoutRelation
    (ℓ : MarcinkiewiczZero →L[ℂ] ℂ) :
    IsClosed (graphPushoutRelation MarcinkiewiczZero ℓ :
      Set (MarcinkiewiczLog × ℂ)) := by
  letI : IsClosed (MarcinkiewiczZero : Set MarcinkiewiczLog) :=
    isClosed_marcinkiewiczZero
  let L := graphPushoutExtension MarcinkiewiczZero ℓ
  have hL : ∀ n : MarcinkiewiczZero, L n = ℓ n :=
    graphPushoutExtension_restrict MarcinkiewiczZero ℓ
  have heq : graphPushoutRelation MarcinkiewiczZero ℓ =
      LinearMap.ker (graphPushoutForwardPre MarcinkiewiczZero L :
        MarcinkiewiczLog × ℂ →ₗ[ℂ] MarcinkiewiczLogQuotient × ℂ) := by
    apply le_antisymm
    · exact graphPushoutRelation_le_forwardKer MarcinkiewiczZero ℓ L hL
    · rintro ⟨x, c⟩ hx
      rw [LinearMap.mem_ker] at hx
      change (Submodule.Quotient.mk x, c + L x) = 0 at hx
      rw [Prod.mk_eq_zero] at hx
      have hxN : x ∈ MarcinkiewiczZero :=
        (Submodule.Quotient.mk_eq_zero MarcinkiewiczZero).mp hx.1
      refine ⟨⟨x, hxN⟩, ?_⟩
      change (x, -ℓ ⟨x, hxN⟩) = (x, c)
      congr 1
      rw [← hL]
      exact (eq_neg_of_add_eq_zero_left hx.2).symm
  rw [heq]
  exact (graphPushoutForwardPre MarcinkiewiczZero L).isClosed_ker

/-- The graph relation for every bounded reader is closed, so its quotient carries the genuine
normed Hausdorff topology required by the Banach pushout. -/
noncomputable instance instIsClosedMarcinkiewiczGraphPushoutRelation
    (ℓ : MarcinkiewiczZero →L[ℂ] ℂ) :
    IsClosed (graphPushoutRelation MarcinkiewiczZero ℓ :
      Set (MarcinkiewiczLog × ℂ)) :=
  isClosed_marcinkiewiczGraphPushoutRelation ℓ

noncomputable def marcinkiewiczGraphPushoutEquiv
    (ℓ : MarcinkiewiczZero →L[ℂ] ℂ) :
    graphPushout MarcinkiewiczZero ℓ ≃L[ℂ] MarcinkiewiczLogQuotient × ℂ :=
  graphPushoutHahnBanachEquiv MarcinkiewiczZero ℓ

/-- Every bounded-reader graph pushout is a complete normed space. -/
theorem completeSpace_marcinkiewiczGraphPushout
    (ℓ : MarcinkiewiczZero →L[ℂ] ℂ) :
    CompleteSpace (graphPushout MarcinkiewiczZero ℓ) :=
  inferInstance

/-- Complete ordinary Banach--Yoneda splitting package for unit pullback and every bounded
vanishing-tail reader pushout. -/
theorem marcinkiewicz_bounded_yoneda_splitting :
    (∃ s : ℂ →L[ℂ] MarcinkiewiczUnitPullback,
      (quotientUnitPullbackProjection MarcinkiewiczZero marcinkiewiczUnit).comp s =
        ContinuousLinearMap.id ℂ ℂ) ∧
    (∀ ℓ : MarcinkiewiczZero →L[ℂ] ℂ,
      CompleteSpace (graphPushout MarcinkiewiczZero ℓ)) ∧
    (∀ ℓ : MarcinkiewiczZero →L[ℂ] ℂ,
      Nonempty (graphPushout MarcinkiewiczZero ℓ ≃L[ℂ]
        MarcinkiewiczLogQuotient × ℂ)) := by
  exact ⟨⟨marcinkiewiczUnitPullbackSection,
      marcinkiewiczUnitPullbackProjection_section⟩,
    fun ℓ => completeSpace_marcinkiewiczGraphPushout ℓ,
    fun ℓ => ⟨marcinkiewiczGraphPushoutEquiv ℓ⟩⟩

/-- Exactness alone annihilates every class having an actual lift. This is the formal content of
the vanishing connecting map on lifted unit and phase `K`-classes in any exact realization. -/
theorem connectingMap_eq_zero_on_actual_lift
    {R A B C : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (q : A →ₗ[R] B) (δ : B →ₗ[R] C) (hexact : Function.Exact q δ) (a : A) :
    δ (q a) = 0 :=
  hexact.apply_apply_eq_zero a

/-- Canonical residue graph has no unconditional nontrivial closed-operator branch: under RH it
is zero and closable; off RH it is nonclosable. -/
theorem canonicalPrimeShiftResidue_graph_status :
    (IsClosableMarcinkiewicz residueDomain residueFunctional ↔ RiemannHypothesis) ∧
    (RiemannHypothesis →
      ∀ (y : ℕ → ℂ) (hy : y ∈ residueDomain), residueFunctional ⟨y, hy⟩ = 0) ∧
    (¬ RiemannHypothesis →
      ¬ IsClosableMarcinkiewicz residueDomain residueFunctional) := by
  refine ⟨riemannHypothesis_iff_residueFunctional_isClosable.symm, ?_, ?_⟩
  · exact riemannHypothesis_iff_residueFunctional_eq_zero.mp
  · intro hnot hclos
    exact hnot (riemannHypothesis_iff_residueFunctional_isClosable.mpr hclos)

end RHTower
