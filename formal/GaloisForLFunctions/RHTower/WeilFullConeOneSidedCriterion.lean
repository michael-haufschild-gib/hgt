import GaloisForLFunctions.HTGeometry.FinsuppOneSidedFeasibility
import GaloisForLFunctions.RHTower.WeilFullConeSummableExcessRigidity
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.LowHeightWeilTests

/-!
# One-sided Weil criteria

For a Weil test `f` (`C²`, compactly supported) write `k_f = f ⋆ f̃` for its autocorrelation and
`ℓ_n(f) = Re(k_f(log n) + k_f(−log n))/√n` for its normalized value at `±log n`. The full Weil
functional is `W_U(k_f) = A(k_f) − Σ_{n≥2} U(n) ℓ_n(f)`, where `A` collects the pole and
archimedean terms.

- The **nonpositive cone** consists of the nonnegative combinations `Σ c_f k_f` with
  `Σ c_f ℓ_n(f) ≤ 0` for every `n ≥ 2`. On this cone the prime sum of `W_Λ` is nonnegative.
- The **nonnegative cone** is defined with `≥ 0`.

**Theorems.**
- `riemannHypothesis_iff_positiveOnNonposCone`: RH holds iff `W_Λ ≥ 0` on the nonpositive cone.
- `riemannHypothesis_iff_positiveOnNonnegCone`: RH holds iff `W_Λ ≥ 0` on the nonnegative cone.
- `riemannHypothesis_of_positiveOnNonposCone` (robust form). For any `U` whose excess over `Λ` is
  summable against `n^{−½}`, `W_U ≥ 0` on the nonpositive cone already implies RH.
- `riemannHypothesis_of_positiveOnNonnegCone` (robust form). The same holds for any `L` with
  summable deficit, using the nonnegative cone.

**Proof.** Positivity on the nonpositive cone is exactly the hypothesis of the M. Riesz extension
theorem (`HTGeometry.exists_le_of_nonneg_on_nonpos_cone`). It produces a full-cone Weil-positive
`lam ≤ U`. Such a `lam` has summable excess over `Λ`, so `lam = Λ` by summable-excess rigidity.
Density of the cone uses the tests `h ± h(· − log j)` with `h` a bump of width `< 1/(j+1)`: their
`ℓ`-vectors are `±` multiples of `e_j`. The nonnegative cone is the mirror, using summable-deficit
rigidity.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff
open Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-- Weil tests: `C²` functions with compact support. -/
def WeilTestFn : Type := {f : ℝ → ℂ // ContDiff ℝ 2 f ∧ HasCompactSupport f}

/-- The integers `n ≥ 2`. -/
abbrev LogIndex : Type := {n : ℕ // 2 ≤ n}

/-- The normalized symmetric value of the autocorrelation of `f` at `±log n`. -/
def logValue (f : ℝ → ℂ) (n : ℕ) : ℝ :=
  (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re / Real.sqrt n

theorem exists_weilTest_log_eq_zero (f : WeilTestFn) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0 := by
  obtain ⟨A, hA⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  have hf : ∀ u, f.1 u ≠ 0 → |u| ≤ A := fun u hu => by
    have := hA (subset_tsupport _ hu)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have hk := weilTest_support_abs_le hf hf
  refine ⟨⌈Real.exp (A + A)⌉₊, fun n hn => ?_⟩
  have hn' : Real.exp (A + A) < n := Nat.lt_of_ceil_lt hn
  have hpos : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
  have hlog : A + A < Real.log n := (Real.lt_log_iff_exp_lt hpos).mpr hn'
  constructor
  · by_contra h
    linarith [hk _ h, le_abs_self (Real.log n)]
  · by_contra h
    have := hk _ h
    rw [abs_neg] at this
    linarith [le_abs_self (Real.log n)]

theorem finite_support_logValue (f : WeilTestFn) :
    (Function.support fun j : LogIndex => logValue f.1 j).Finite := by
  obtain ⟨N, hN⟩ := exists_weilTest_log_eq_zero f
  refine ((Set.finite_Iic N).preimage Subtype.val_injective.injOn).subset fun j hj => ?_
  simp only [Set.mem_preimage, Set.mem_Iic]
  by_contra h
  rw [not_le] at h
  apply hj
  simp [logValue, (hN j h).1, (hN j h).2]

/-- The `ℓ`-vector of a Weil test, finitely supported on `n ≥ 2`. -/
def logVector (f : WeilTestFn) : LogIndex →₀ ℝ :=
  Finsupp.ofSupportFinite (fun j => logValue f.1 j) (finite_support_logValue f)

theorem logVector_apply (f : WeilTestFn) (j : LogIndex) : logVector f j = logValue f.1 j := by
  simp [logVector, Finsupp.ofSupportFinite_coe]

/-- The pole and archimedean part of the Weil functional (real part). -/
def weilArchRe (k : ℝ → ℂ) : ℝ :=
  (paperFT k (I / 2) + paperFT k (-I / 2) +
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)).re

/-- **The Weil functional splits** into its pole and archimedean part minus the pairing of the
weights with the `ℓ`-vector. -/
theorem re_weilFullFunctional_eq (lam : ℕ → ℝ) (f : WeilTestFn) :
    (weilFullFunctional lam (EF.weilTest f.1 f.1)).re =
      weilArchRe (EF.weilTest f.1 f.1) -
        linearCombination ℝ (fun j : LogIndex => lam j) (logVector f) := by
  classical
  obtain ⟨N, hN⟩ := exists_weilTest_log_eq_zero f
  set k := EF.weilTest f.1 f.1 with hk
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))) =
      ∑ n ∈ Finset.range (N + 1), ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
    refine tsum_eq_sum fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [(hN n (by omega)).1, (hN n (by omega)).2, add_zero, mul_zero]
  have hlc : linearCombination ℝ (fun j : LogIndex => lam j) (logVector f) =
      ∑ j ∈ (Finset.range (N + 1)).subtype (fun n => 2 ≤ n), logValue f.1 j * lam j := by
    rw [linearCombination_apply]
    refine (Finsupp.sum_of_support_subset (logVector f) (fun j hj => ?_) (fun j a => a • lam j)
      fun _ _ => zero_smul _ _).trans
      (Finset.sum_congr rfl fun j _ => by rw [logVector_apply, smul_eq_mul])
    rw [Finsupp.mem_support_iff, logVector_apply] at hj
    rw [Finset.mem_subtype, Finset.mem_range]
    by_contra h
    apply hj
    have h0 := hN j (by omega)
    rw [logValue, ← hk, h0.1, h0.2, add_zero, Complex.zero_re, zero_div]
  have hW : weilFullFunctional lam k =
      (paperFT k (I / 2) + paperFT k (-I / 2) +
        (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)) -
      ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
    unfold weilFullFunctional; ring
  have hterm : ∀ n ∈ Finset.range (N + 1),
      (((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))).re =
      if 2 ≤ n then logValue f.1 n * lam n else 0 := by
    intro n _
    rw [Complex.re_ofReal_mul]
    split_ifs
    · rw [logValue, ← hk]; ring
    · simp
  rw [hlc, Finset.sum_subtype_eq_sum_filter (fun n => logValue f.1 n * lam n), Finset.sum_filter,
    hW, Complex.sub_re, hsum, Complex.re_sum, Finset.sum_congr rfl hterm, weilArchRe]

/-! ## Tests reaching one coordinate -/

/-- A bump of radius `1/(4(j+1))`. -/
def narrowBump (j : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (8 * ((j : ℝ) + 1)), 1 / (4 * ((j : ℝ) + 1)), by positivity, by
    apply one_div_lt_one_div_of_lt (by positivity); nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]⟩

/-- The complex bump `h_j`. -/
def narrowBumpC (j : ℕ) (u : ℝ) : ℂ := ((narrowBump j u : ℝ) : ℂ)

theorem contDiff_narrowBumpC (j : ℕ) : ContDiff ℝ ∞ (narrowBumpC j) :=
  ofRealCLM.contDiff.comp (narrowBump j).contDiff

theorem narrowBumpC_eq_zero (j : ℕ) {u : ℝ} (hu : 1 / (4 * ((j : ℝ) + 1)) < |u|) :
    narrowBumpC j u = 0 := by
  have h : (narrowBump j).rOut ≤ dist u 0 := by rw [Real.dist_eq, sub_zero]; exact hu.le
  simp only [narrowBumpC, (narrowBump j).zero_of_le_dist h, Complex.ofReal_zero]

theorem hasCompactSupport_narrowBumpC (j : ℕ) : HasCompactSupport (narrowBumpC j) :=
  (narrowBump j).hasCompactSupport.comp_left Complex.ofReal_zero

/-- The pair test `h_j(u) + σ h_j(u − log j)`. -/
def pairTest (j : ℕ) (σ : ℝ) (u : ℝ) : ℂ := narrowBumpC j u + (σ : ℂ) * narrowBumpC j (u - Real.log j)

theorem pairTest_eq_sum (j : ℕ) (σ : ℝ) :
    pairTest j σ = fun u => ∑ m ∈ Finset.range 2,
      (if m = 0 then (1 : ℂ) else (σ : ℂ)) * narrowBumpC j (u - if m = 0 then 0 else Real.log j) := by
  funext u
  simp [pairTest, Finset.sum_range_succ]

theorem contDiff_pairTest (j : ℕ) (σ : ℝ) : ContDiff ℝ 2 (pairTest j σ) :=
  ((contDiff_narrowBumpC j).of_le (by norm_cast)).add
    (contDiff_const.mul (((contDiff_narrowBumpC j).of_le (by norm_cast)).comp
      (contDiff_id.sub contDiff_const)))

theorem hasCompactSupport_pairTest (j : ℕ) (σ : ℝ) : HasCompactSupport (pairTest j σ) :=
  (hasCompactSupport_narrowBumpC j).add
    ((((hasCompactSupport_narrowBumpC j).comp_homeomorph (Homeomorph.subRight (Real.log j)))).mul_left)

/-- The autocorrelation of a pair test. -/
theorem weilTest_pairTest (j : ℕ) (σ : ℝ) (y : ℝ) :
    EF.weilTest (pairTest j σ) (pairTest j σ) y =
      (1 + σ ^ 2 : ℝ) * EF.weilTest (narrowBumpC j) (narrowBumpC j) y +
        (σ : ℂ) * (EF.weilTest (narrowBumpC j) (narrowBumpC j) (y + Real.log j) +
          EF.weilTest (narrowBumpC j) (narrowBumpC j) (y - Real.log j)) := by
  rw [pairTest_eq_sum, weilTest_sum_translates (contDiff_narrowBumpC j).continuous
    (hasCompactSupport_narrowBumpC j)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, Complex.conj_ofReal, map_one, mul_one, one_mul, sub_zero, add_zero]
  rw [show y - Real.log j + Real.log j = y by ring]
  push_cast
  ring

theorem weilTest_narrowBumpC_eq_zero (j : ℕ) {Y : ℝ} (hY : 1 / (2 * ((j : ℝ) + 1)) < |Y|) :
    EF.weilTest (narrowBumpC j) (narrowBumpC j) Y = 0 :=
  weilTest_self_eq_zero (fun u hu => narrowBumpC_eq_zero j hu)
    (by rw [show 2 * (1 / (4 * ((j : ℝ) + 1))) = 1 / (2 * ((j : ℝ) + 1)) by field_simp; ring]
        exact hY)

theorem integral_narrowBump_sq_pos (j : ℕ) : 0 < ∫ t, (narrowBump j t) ^ 2 := by
  have hc : Continuous fun t => (narrowBump j t) ^ 2 := (narrowBump j).continuous.pow 2
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((narrowBump j).hasCompactSupport.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
    (fun t => sq_nonneg _) (x := 0) ?_
  rw [(narrowBump j).one_of_mem_closedBall (Metric.mem_closedBall_self (narrowBump j).rIn_pos.le)]
  norm_num

theorem weilTest_narrowBumpC_zero (j : ℕ) :
    EF.weilTest (narrowBumpC j) (narrowBumpC j) 0 = ((∫ t, (narrowBump j t) ^ 2 : ℝ) : ℂ) :=
  weilTest_self_zero_ofReal (g := fun t => narrowBump j t)

/-- The `ℓ`-values of a pair test: `2σ∫h_j²/√j` at `n = j` and `0` at every other `n ≥ 2`. -/
theorem logValue_pairTest {j : ℕ} (hj : 2 ≤ j) (σ : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    logValue (pairTest j σ) m =
      if m = j then 2 * σ * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j else 0 := by
  have hH := fun Y => weilTest_narrowBumpC_eq_zero j (Y := Y)
  have hlog2 : ∀ n : ℕ, 2 ≤ n → Real.log 2 ≤ Real.log n := fun n hn =>
    Real.log_le_log two_pos (by exact_mod_cast hn)
  have hsmall : 1 / (2 * ((j : ℝ) + 1)) < Real.log 2 := by
    refine lt_of_le_of_lt ?_ WeilExcess.seventeen_div_twentyfive_lt_log_two
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hm2 := hlog2 m hm
  have hj2 := hlog2 j hj
  have hpos : 0 < 1 / (2 * ((j : ℝ) + 1)) := by positivity
  have e1 := hH (Real.log m) (by rw [abs_of_pos (by linarith)]; linarith)
  have e2 := hH (-Real.log m) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have e3 := hH (Real.log m + Real.log j) (by rw [abs_of_pos (by linarith)]; linarith)
  have e4 := hH (-Real.log m - Real.log j) (by
    rw [show -Real.log m - Real.log j = -(Real.log m + Real.log j) by ring, abs_neg,
      abs_of_pos (by linarith)]; linarith)
  rw [logValue, weilTest_pairTest, weilTest_pairTest, e1, e2, e3,
    show -Real.log m + Real.log j = -(Real.log m - Real.log j) by ring, e4]
  split_ifs with hmj
  · subst hmj
    rw [sub_self, neg_zero, weilTest_narrowBumpC_zero]
    simp only [mul_zero, zero_add, add_zero]
    rw [show ((σ : ℂ) * ((∫ t, (narrowBump m t) ^ 2 : ℝ) : ℂ) +
        (σ : ℂ) * ((∫ t, (narrowBump m t) ^ 2 : ℝ) : ℂ)) =
        ((2 * σ * ∫ t, (narrowBump m t) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  · have hgap := WeilExcess.inv_succ_le_abs_log_sub (by omega) (by omega) hmj
    have hlt : 1 / (2 * ((j : ℝ) + 1)) < 1 / ((j : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    rw [hH (Real.log m - Real.log j) (by linarith), hH (-(Real.log m - Real.log j))
      (by rw [abs_neg]; linarith)]
    simp

/-- The pair test as a Weil test. -/
def pairTestFn (j : ℕ) (σ : ℝ) : WeilTestFn :=
  ⟨pairTest j σ, contDiff_pairTest j σ, hasCompactSupport_pairTest j σ⟩

theorem logVector_pairTestFn (j : LogIndex) (σ : ℝ) :
    logVector (pairTestFn j σ) =
      Finsupp.single j (2 * σ * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (pairTest j σ) m = _
  rw [logValue_pairTest j.2 σ m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

theorem pairTest_weight_pos (j : LogIndex) :
    0 < 2 * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j := by
  have hj : (0 : ℝ) < (j : ℕ) := by exact_mod_cast (lt_of_lt_of_le two_pos j.2)
  exact div_pos (mul_pos two_pos (integral_narrowBump_sq_pos j)) (Real.sqrt_pos.mpr hj)

/-! ## The one-sided cones -/

/-- Weil positivity of `U` on the nonnegative combinations of tests whose `ℓ`-values are
nonpositive at every `n ≥ 2`. -/
def PositiveOnNonposCone (U : ℕ → ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) ≤ 0) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1 f.1)).re

/-- Weil positivity of `L` on the nonnegative combinations of tests whose `ℓ`-values are
nonnegative at every `n ≥ 2`. -/
def PositiveOnNonnegCone (L : ℕ → ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1 n) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional L (EF.weilTest f.1 f.1)).re

theorem linearCombination_logVector_apply (c : WeilTestFn →₀ ℝ) (j : LogIndex) :
    linearCombination ℝ logVector c j = c.sum fun f t => t * logValue f.1 j := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVector_apply]

theorem sum_re_weilFullFunctional (U : ℕ → ℝ) (c : WeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1 f.1)).re) =
      linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) c -
        linearCombination ℝ (fun j : LogIndex => U j) (linearCombination ℝ logVector c) := by
  simp_rw [re_weilFullFunctional_eq]
  have e1 : linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) c =
      c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1) := by
    rw [linearCombination_apply]; simp only [smul_eq_mul]
  have e2 : linearCombination ℝ (fun j : LogIndex => U j) (linearCombination ℝ logVector c) =
      c.sum fun f t => t * linearCombination ℝ (fun j : LogIndex => U j) (logVector f) := by
    rw [linearCombination_apply ℝ (v := logVector), map_finsuppSum]
    exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
  rw [e1, e2, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun f _ => by ring

theorem weilPositiveFull_of_le_arch {lam : LogIndex → ℝ}
    (h : ∀ f : WeilTestFn,
      linearCombination ℝ lam (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1)) :
    WeilPositiveFull fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0 := by
  intro f hf hc
  rw [re_weilFullFunctional_eq _ ⟨f, hf, hc⟩]
  have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
      lam := funext fun j => by simp [j.2]
  rw [e]
  linarith [h ⟨f, hf, hc⟩]

/-- **Positivity on the nonpositive cone produces a Weil-positive minorant of `U`.** -/
theorem exists_weilPositiveFull_le_of_positiveOnNonposCone {U : ℕ → ℝ}
    (h : PositiveOnNonposCone U) :
    ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ (∀ n, 2 ≤ n → lam n ≤ U n) ∧ ∀ n, n < 2 → lam n = 0 := by
  obtain ⟨lam, hlamU, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_le_of_nonneg_on_nonpos_cone
    logVector (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) (fun j : LogIndex => U j)
    (fun j => ⟨pairTestFn j (-1), _, pairTest_weight_pos j, by
      rw [logVector_pairTestFn]; congr 1; ring⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        rw [← linearCombination_logVector_apply c ⟨n, hn⟩]; exact hcT ⟨n, hn⟩
      rw [sum_re_weilFullFunctional] at h1
      linarith)
  refine ⟨_, weilPositiveFull_of_le_arch hlamT, fun n hn => ?_, fun n hn => ?_⟩
  · simp only [dif_pos hn]; exact hlamU ⟨n, hn⟩
  · simp only [dif_neg (by omega : ¬ 2 ≤ n)]

/-- **Positivity on the nonnegative cone produces a Weil-positive majorant of `L`.** -/
theorem exists_weilPositiveFull_ge_of_positiveOnNonnegCone {L : ℕ → ℝ}
    (h : PositiveOnNonnegCone L) :
    ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ (∀ n, 2 ≤ n → L n ≤ lam n) ∧ ∀ n, n < 2 → lam n = 0 := by
  obtain ⟨lam, hlamL, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
    logVector (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) (fun j : LogIndex => L j)
    (fun j => ⟨pairTestFn j 1, _, pairTest_weight_pos j, by
      rw [logVector_pairTestFn]; congr 1; ring⟩)
    (fun c hc hcT => by
      have h1 := h c hc fun n hn => by
        rw [← linearCombination_logVector_apply c ⟨n, hn⟩]; exact hcT ⟨n, hn⟩
      rw [sum_re_weilFullFunctional] at h1
      linarith)
  refine ⟨_, weilPositiveFull_of_le_arch hlamT, fun n hn => ?_, fun n hn => ?_⟩
  · simp only [dif_pos hn]; exact hlamL ⟨n, hn⟩
  · simp only [dif_neg (by omega : ¬ 2 ≤ n)]

theorem vonMangoldt_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) :
    (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
  interval_cases n <;> simp

/-! ## The criteria -/

/-- **Robust one-sided Weil criterion (nonpositive cone).** If `U` has summable excess over `Λ`
against `n^{−½}` and `W_U` is nonnegative on the nonpositive cone, then RH holds. -/
theorem riemannHypothesis_of_positiveOnNonposCone {U : ℕ → ℝ}
    (hU : Summable fun n => max (U n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n)
    (h : PositiveOnNonposCone U) : RiemannHypothesis := by
  obtain ⟨lam, hW, hle, h01⟩ := exists_weilPositiveFull_le_of_positiveOnNonposCone h
  have hexc : Summable fun n =>
      max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n := by
    refine Summable.of_nonneg_of_le (fun n => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
      (fun n => ?_) hU
    by_cases hn : 2 ≤ n
    · exact div_le_div_of_nonneg_right (max_le_max (by linarith [hle n hn]) le_rfl)
        (Real.sqrt_nonneg _)
    · rw [h01 n (by omega), vonMangoldt_eq_zero_of_lt_two (by omega), sub_zero, max_self,
        zero_div]
      exact div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have heq := WeilExcess.eq_vonMangoldt_of_weilPositiveFull_of_summable_excess hW hexc
  refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hc => ?_
  have := hW f hf hc
  rwa [weilFullFunctional_congr heq] at this

/-- **Robust one-sided Weil criterion (nonnegative cone).** If `L` has summable deficit below `Λ`
against `n^{−½}` and `W_L` is nonnegative on the nonnegative cone, then RH holds. -/
theorem riemannHypothesis_of_positiveOnNonnegCone {L : ℕ → ℝ}
    (hL : Summable fun n => max ((ArithmeticFunction.vonMangoldt n : ℝ) - L n) 0 / Real.sqrt n)
    (h : PositiveOnNonnegCone L) : RiemannHypothesis := by
  obtain ⟨lam, hW, hge, h01⟩ := exists_weilPositiveFull_ge_of_positiveOnNonnegCone h
  have hdef : Summable fun n =>
      max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n := by
    refine Summable.of_nonneg_of_le (fun n => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
      (fun n => ?_) hL
    by_cases hn : 2 ≤ n
    · exact div_le_div_of_nonneg_right (max_le_max (by linarith [hge n hn]) le_rfl)
        (Real.sqrt_nonneg _)
    · rw [h01 n (by omega), vonMangoldt_eq_zero_of_lt_two (by omega), sub_zero, max_self,
        zero_div]
      exact div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have heq := eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit hW hdef
  refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hc => ?_
  have := hW f hf hc
  rwa [weilFullFunctional_congr heq] at this

theorem summable_self_excess :
    Summable fun n => max ((ArithmeticFunction.vonMangoldt n : ℝ) -
      (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n := by
  simp only [sub_self, max_self, zero_div]
  exact summable_zero

theorem sum_nonneg_of_weilPositiveFull {U : ℕ → ℝ} (hW : WeilPositiveFull U)
    (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) :
    0 ≤ c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1 f.1)).re :=
  Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (hW f.1 f.2.1 f.2.2)

/-- **One-sided Weil criterion.** RH holds iff `W_Λ` is nonnegative on the cone of tests that are
nonpositive at every `±log n`. On this cone the prime sum of `W_Λ` is a nonnegative term. -/
theorem riemannHypothesis_iff_positiveOnNonposCone :
    RiemannHypothesis ↔
      PositiveOnNonposCone fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ⟨fun hRH c hc _ => sum_nonneg_of_weilPositiveFull
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) c hc,
    riemannHypothesis_of_positiveOnNonposCone summable_self_excess⟩

/-- **One-sided Weil criterion.** RH holds iff `W_Λ` is nonnegative on the cone of tests that are
nonnegative at every `±log n`. -/
theorem riemannHypothesis_iff_positiveOnNonnegCone :
    RiemannHypothesis ↔
      PositiveOnNonnegCone fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ⟨fun hRH c hc _ => sum_nonneg_of_weilPositiveFull
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) c hc,
    riemannHypothesis_of_positiveOnNonnegCone summable_self_excess⟩

/-! ## Nonemptiness of the Weil cone is prime-blind -/

/-- **Prime-blind positivity**: the pole and archimedean part of the Weil functional is
nonnegative on every nonnegative combination of tests whose symmetric values vanish at every
`±log n`, `n ≥ 2`. No prime enters. -/
def PrimeBlindPositive : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) →
    0 ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)

theorem linearCombination_logVector_eq_zero {c : WeilTestFn →₀ ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) :
    linearCombination ℝ logVector c = 0 := by
  ext j
  rw [linearCombination_logVector_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact h j j.2

theorem sum_weilArchRe_eq (c : WeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) =
      linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) c := by
  rw [linearCombination_apply]; simp only [smul_eq_mul]

/-- **The Weil cone is nonempty iff prime-blind positivity holds.** Some real sequence `lam` is
full-cone Weil-positive exactly when the pole and archimedean part is nonnegative on the
combinations that vanish at every `±log n`. -/
theorem exists_weilPositiveFull_iff_primeBlindPositive :
    (∃ lam : ℕ → ℝ, WeilPositiveFull lam) ↔ PrimeBlindPositive := by
  constructor
  · rintro ⟨lam, hW⟩ c hc hnull
    have h1 := sum_nonneg_of_weilPositiveFull hW c hc
    rw [sum_re_weilFullFunctional, linearCombination_logVector_eq_zero hnull, map_zero,
      sub_zero] at h1
    rw [sum_weilArchRe_eq]
    exact h1
  · intro h
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      logVector (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1))
      (fun j => ⟨pairTestFn j (-1), _, pairTest_weight_pos j, by
        rw [logVector_pairTestFn]; congr 1; ring⟩)
      (fun j => ⟨pairTestFn j 1, _, pairTest_weight_pos j, by
        rw [logVector_pairTestFn]; congr 1; ring⟩)
      (fun c hc hnull => by
        rw [← sum_weilArchRe_eq]
        refine h c hc fun n hn => ?_
        rw [← linearCombination_logVector_apply c ⟨n, hn⟩, hnull]
        rfl)
    exact ⟨_, weilPositiveFull_of_le_arch hlam⟩

/-- **RH implies prime-blind positivity.** -/
theorem primeBlindPositive_of_riemannHypothesis (hRH : RiemannHypothesis) : PrimeBlindPositive :=
  exists_weilPositiveFull_iff_primeBlindPositive.mp
    ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH⟩

end

end RHTower.WeilOneSided
