import GaloisForLFunctions.HTGeometry.EulerShellHeatOrbit
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.KummerPhaseExcess

/-!
# Ramification power formation of the exponent shells

For `m ≥ 1` let `A_m = {n ≥ 2 : max_p v_p(n) = m}` (`EulerShell m`).  For `r ≥ 2` the power map
`P_r : A_m → A_{rm}`, `k ↦ k^r`, is injective, and its image is exactly the set of `r`-th powers in
`A_{rm}` (an `r`-th power has all exponents divisible by `r`, and its root lies in `A_m`).  With the
excess `X_{m,r} = A_{rm} ∖ P_r(A_m)` this gives the canonical splitting

`A_{rm} ≃ A_m ⊔ X_{m,r}`,  `S_{rm}(σ) = S_m(rσ) + C_{m,r}(σ)`,

where `S_m(σ) = Σ_{n ∈ A_m} n^{-σ}` and `C_{m,r}(σ) = Σ_{N ∈ X_{m,r}} N^{-σ}`; the excess is
nonempty
(`2^{rm}·3`).  On the line, the atomic measures `μ_{m,σ} = Σ_{n ∈ A_m} n^{-σ} δ_{log n}` and
`η_{m,r,σ} = Σ_{N ∈ X_{m,r}} N^{-σ} δ_{log N}` satisfy the formation identity

`μ_{rm,σ} = (x ↦ r x)_* μ_{m,rσ} + η_{m,r,σ}`,

with mutually singular summands, and after normalization
`P_{rm,σ} = α P^{in} + β Q` with `α = S_m(rσ)/S_{rm}(σ)`, `β = C_{m,r}(σ)/S_{rm}(σ)`,
`0 < α, β < 1`, `α + β = 1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationExcess

open _root_.RHTower _root_.HTGeometry.ConstraintFrameRelativity

/-! ### The power map and the excess -/

variable {m r : ℕ}

theorem two_le_pow_of_two_le {k : ℕ} (hk : 2 ≤ k) (hr : r ≠ 0) : 2 ≤ k ^ r :=
  hk.trans (Nat.le_self_pow hr k)

/-- The power map `P_r : A_m → A_{rm}`, `k ↦ k^r`. -/
def shellPow (hr : r ≠ 0) (k : EulerShell m) : EulerShell (r * m) :=
  ⟨(k : ℕ) ^ r, two_le_pow_of_two_le k.2.1 hr, by rw [shellIndicator_pow hr]; exact k.2.2⟩

@[simp] theorem shellPow_val (hr : r ≠ 0) (k : EulerShell m) :
    (shellPow hr k : ℕ) = (k : ℕ) ^ r := rfl

/-- Iterated power formation: `P_s ∘ P_r = P_{sr}` on values. -/
theorem shellPow_shellPow_val {s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) (k : EulerShell m) :
    (shellPow hs (shellPow hr k) : ℕ) = (k : ℕ) ^ (s * r) := by
  rw [shellPow_val, shellPow_val, ← pow_mul, mul_comm]

theorem shellPow_injective (hr : r ≠ 0) : Function.Injective (shellPow (m := m) hr) :=
  fun _ _ h => Subtype.ext (Nat.pow_left_injective hr (congrArg Subtype.val h))

/-- The excess `X_{m,r} = A_{rm} ∖ P_r(A_m)`: the non-`r`-th-powers of `A_{rm}`. -/
abbrev ExcessShell (m r : ℕ) : Type := {N : EulerShell (r * m) // ¬ IsRPow r (N : ℕ)}

/-- The `r`-th powers of `A_{rm}` are exactly the image of `P_r`. -/
theorem exists_shellPow_eq (hr : r ≠ 0) {N : EulerShell (r * m)} (hN : IsRPow r (N : ℕ)) :
    ∃ k : EulerShell m, shellPow hr k = N := by
  obtain ⟨k, hk⟩ := hN
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · rw [zero_pow hr] at hk; have := N.2.1; omega
    · rw [one_pow] at hk; have := N.2.1; omega
  refine ⟨⟨k, hk2, ?_⟩, Subtype.ext hk⟩
  rw [← shellIndicator_pow hr, hk]
  exact N.2.2

/-- The power image of `A_m` in `A_{rm}`, as a type equivalent to `A_m`. -/
def powImageEquiv (hr : r ≠ 0) : EulerShell m ≃ {N : EulerShell (r * m) // IsRPow r (N : ℕ)} :=
  Equiv.ofBijective (fun k => ⟨shellPow hr k, ⟨k, rfl⟩⟩)
    ⟨fun a b h => shellPow_injective hr (congrArg Subtype.val h), fun N => by
      obtain ⟨k, hk⟩ := exists_shellPow_eq hr N.2
      exact ⟨k, Subtype.ext hk⟩⟩

open scoped Classical in
/-- **The canonical splitting `A_{rm} ≃ A_m ⊔ X_{m,r}`.** -/
def shellSplit (hr : r ≠ 0) : EulerShell (r * m) ≃ EulerShell m ⊕ ExcessShell m r :=
  (Equiv.sumCompl fun N : EulerShell (r * m) => IsRPow r (N : ℕ)).symm.trans
    (Equiv.sumCongr (powImageEquiv hr).symm (Equiv.refl _))

theorem shellSplit_symm_inl (hr : r ≠ 0) (k : EulerShell m) :
    (shellSplit hr).symm (Sum.inl k) = shellPow hr k := rfl

theorem shellSplit_symm_inr (hr : r ≠ 0) (N : ExcessShell m r) :
    (shellSplit hr).symm (Sum.inr N) = N.1 := rfl

/-- The excess witness `2^{rm}·3`. -/
def excessWitness (hm : m ≠ 0) (hr : 2 ≤ r) : ExcessShell m r :=
  ⟨⟨2 ^ (r * m) * 3, by
    have : 1 ≤ 2 ^ (r * m) := Nat.one_le_two_pow
    omega, shellIndicator_two_pow_mul_three (by positivity)⟩, by
    have h := excessStream_witness hm hr
    unfold excessStream at h
    split_ifs at h with hp
    · exact absurd h (by norm_num)
    · exact hp⟩

/-! ### Dirichlet masses -/

/-- The excess Dirichlet mass `C_{m,r}(σ) = Σ_{N ∈ X_{m,r}} N^{-σ}`. -/
def excessSum (m r : ℕ) (σ : ℝ) : ℝ := ∑' N : ExcessShell m r, ((N : ℕ) : ℝ) ^ (-σ)

theorem summable_excess (m r : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun N : ExcessShell m r => ((N : ℕ) : ℝ) ^ (-σ) :=
  (summable_shell (r * m) hσ).comp_injective Subtype.val_injective

theorem excessSum_pos (hm : m ≠ 0) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) : 0 < excessSum m r σ :=
  (summable_excess m r hσ).tsum_pos (fun _ => by positivity) (excessWitness hm hr)
    (Real.rpow_pos_of_pos (by
      have : 2 ≤ ((excessWitness hm hr : EulerShell (r * m)) : ℕ) := (excessWitness hm hr).1.2.1
      exact_mod_cast (show 0 < ((excessWitness hm hr : EulerShell (r * m)) : ℕ) by omega)) _)

theorem rpow_shellPow (hr : r ≠ 0) (k : EulerShell m) (σ : ℝ) :
    ((shellPow hr k : ℕ) : ℝ) ^ (-σ) = ((k : ℕ) : ℝ) ^ (-(r * σ)) := by
  rw [shellPow_val, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  ring_nf

/-- **`S_{rm}(σ) = S_m(rσ) + C_{m,r}(σ)`.** -/
theorem eulerShellSum_split (hr : r ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    eulerShellSum (r * m) σ = eulerShellSum m (r * σ) + excessSum m r σ := by
  have hrσ : 1 < (r : ℝ) * σ := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
    nlinarith
  rw [eulerShellSum, ← (shellSplit hr).symm.tsum_eq]
  rw [Summable.tsum_sum]
  · simp only [shellSplit_symm_inl, shellSplit_symm_inr, rpow_shellPow hr]
    rfl
  · exact ((summable_shell m hrσ).congr fun k => (rpow_shellPow hr k σ).symm)
  · exact summable_excess m r hσ

/-- The survival fraction `α_{m,r}(σ) = S_m(rσ)/S_{rm}(σ)`. -/
def survival (m r : ℕ) (σ : ℝ) : ℝ := eulerShellSum m (r * σ) / eulerShellSum (r * m) σ

/-- The excess fraction `β_{m,r}(σ) = C_{m,r}(σ)/S_{rm}(σ)`. -/
def excessFraction (m r : ℕ) (σ : ℝ) : ℝ := excessSum m r σ / eulerShellSum (r * m) σ

section Fractions

variable (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ)
include hm hr hσ

omit hm in
theorem one_lt_mul_of_two_le : 1 < (r : ℝ) * σ := by
  have : (2 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

theorem survival_add_excessFraction : survival m r σ + excessFraction m r σ = 1 := by
  have hS := eulerShellSum_pos (m := r * m) (by nlinarith) hσ
  rw [survival, excessFraction, ← add_div, ← eulerShellSum_split (by omega) hσ, div_self hS.ne']

theorem survival_pos : 0 < survival m r σ :=
  div_pos (eulerShellSum_pos hm (one_lt_mul_of_two_le hr hσ))
    (eulerShellSum_pos (by nlinarith) hσ)

theorem excessFraction_pos : 0 < excessFraction m r σ :=
  div_pos (excessSum_pos (by omega) hr hσ) (eulerShellSum_pos (by nlinarith) hσ)

theorem survival_lt_one : survival m r σ < 1 := by
  have h1 := survival_add_excessFraction hm hr hσ
  have h2 := excessFraction_pos hm hr hσ
  linarith

theorem excessFraction_lt_one : excessFraction m r σ < 1 := by
  have h1 := survival_add_excessFraction hm hr hσ
  have h2 := survival_pos hm hr hσ
  linarith

end Fractions

/-! ### The positive measure formation -/

/-- The atomic measure `Σ_i w_i δ_{x_i}` on the line. -/
def atomic {ι : Type*} (w : ι → ℝ) (x : ι → ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (w i) • Measure.dirac (x i)

theorem atomic_apply {ι : Type*} (w : ι → ℝ) (x : ι → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    atomic w x s = ∑' i, ENNReal.ofReal (w i) * s.indicator 1 (x i) := by
  rw [atomic, Measure.sum_apply _ hs]
  refine tsum_congr fun i => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

/-- The shell measure `μ_{m,σ} = Σ_{n ∈ A_m} n^{-σ} δ_{log n}`. -/
def shellMeasure (m : ℕ) (σ : ℝ) : Measure ℝ :=
  atomic (fun n : EulerShell m => ((n : ℕ) : ℝ) ^ (-σ)) fun n => Real.log (n : ℕ)

/-- The excess measure `η_{m,r,σ} = Σ_{N ∈ X_{m,r}} N^{-σ} δ_{log N}`. -/
def excessMeasure (m r : ℕ) (σ : ℝ) : Measure ℝ :=
  atomic (fun N : ExcessShell m r => ((N : ℕ) : ℝ) ^ (-σ)) fun N => Real.log (N : ℕ)

/-- The dilation `d_r(x) = r x`. -/
def dilate (r : ℕ) (x : ℝ) : ℝ := r * x

theorem measurable_dilate (r : ℕ) : Measurable (dilate r) := measurable_const.mul measurable_id

theorem atomic_map {ι : Type*} (w : ι → ℝ) (x : ι → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (atomic w x).map f = atomic w (f ∘ x) := by
  rw [atomic, Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul, Measure.map_dirac]
  rfl

theorem atomic_sum {ι κ : Type*} (w : ι ⊕ κ → ℝ) (x : ι ⊕ κ → ℝ) :
    atomic w x = atomic (w ∘ Sum.inl) (x ∘ Sum.inl) + atomic (w ∘ Sum.inr) (x ∘ Sum.inr) := by
  ext s hs
  rw [Measure.add_apply, atomic_apply _ _ hs, atomic_apply _ _ hs, atomic_apply _ _ hs,
    ENNReal.summable.tsum_sum ENNReal.summable]
  rfl

theorem atomic_comp_equiv {ι κ : Type*} (e : κ ≃ ι) (w : ι → ℝ) (x : ι → ℝ) :
    atomic (w ∘ e) (x ∘ e) = atomic w x :=
  Measure.sum_comp_equiv e fun i => ENNReal.ofReal (w i) • Measure.dirac (x i)

/-- **Theorem 2.1 (unnormalized formation identity)**:
`μ_{rm,σ} = (d_r)_* μ_{m,rσ} + η_{m,r,σ}`. -/
theorem shellMeasure_formation (hr : r ≠ 0) (σ : ℝ) :
    shellMeasure (r * m) σ = (shellMeasure m (r * σ)).map (dilate r) + excessMeasure m r σ := by
  rw [shellMeasure, ← atomic_comp_equiv (shellSplit hr).symm, atomic_sum, shellMeasure,
    atomic_map _ _ (measurable_dilate r), excessMeasure]
  congr 1
  congr 1
  · funext k
    exact rpow_shellPow hr k σ
  · funext k
    simp only [Function.comp_apply, shellSplit_symm_inl, shellPow_val, dilate, Nat.cast_pow,
      Real.log_pow]

theorem atomic_univ {ι : Type*} (w : ι → ℝ) (x : ι → ℝ) :
    atomic w x univ = ∑' i, ENNReal.ofReal (w i) := by
  rw [atomic_apply _ _ MeasurableSet.univ]
  simp

theorem atomic_univ_of_summable {ι : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (x : ι → ℝ) : atomic w x univ = ENNReal.ofReal (∑' i, w i) := by
  rw [atomic_univ, ENNReal.ofReal_tsum_of_nonneg hw hs]

theorem shellMeasure_univ (m : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    shellMeasure m σ univ = ENNReal.ofReal (eulerShellSum m σ) :=
  atomic_univ_of_summable (fun _ => by positivity) (summable_shell m hσ) _

theorem excessMeasure_univ (m r : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    excessMeasure m r σ univ = ENNReal.ofReal (excessSum m r σ) :=
  atomic_univ_of_summable (fun _ => by positivity) (summable_excess m r hσ) _

instance (m : ℕ) {σ : ℝ} [Fact (1 < σ)] : IsFiniteMeasure (shellMeasure m σ) :=
  ⟨by rw [shellMeasure_univ m Fact.out]; exact ENNReal.ofReal_lt_top⟩

instance (m r : ℕ) {σ : ℝ} [Fact (1 < σ)] : IsFiniteMeasure (excessMeasure m r σ) :=
  ⟨by rw [excessMeasure_univ m r Fact.out]; exact ENNReal.ofReal_lt_top⟩

/-- The inherited support `{r log k : k ∈ A_m} = {log N : N ∈ P_r(A_m)}`. -/
def inheritedSupport (m r : ℕ) : Set ℝ := range fun k : EulerShell m => (r : ℝ) * Real.log (k : ℕ)

theorem measurableSet_inheritedSupport (m r : ℕ) : MeasurableSet (inheritedSupport m r) :=
  (countable_range _).measurableSet

/-- **The two summands of the formation identity are mutually singular**: the inherited part lives
on the logarithms of `r`-th powers, the excess never charges them. -/
theorem formation_mutuallySingular (σ : ℝ) :
    (shellMeasure m (r * σ)).map (dilate r) (inheritedSupport m r)ᶜ = 0 ∧
      excessMeasure m r σ (inheritedSupport m r) = 0 := by
  constructor
  · rw [shellMeasure, atomic_map _ _ (measurable_dilate r),
      atomic_apply _ _ (measurableSet_inheritedSupport m r).compl]
    refine ENNReal.tsum_eq_zero.2 fun k => ?_
    rw [indicator_of_notMem (by rw [mem_compl_iff, not_not]; exact ⟨k, rfl⟩), mul_zero]
  · rw [excessMeasure, atomic_apply _ _ (measurableSet_inheritedSupport m r)]
    refine ENNReal.tsum_eq_zero.2 fun N => ?_
    rw [indicator_of_notMem, mul_zero]
    rintro ⟨k, hk⟩
    apply N.2
    have hpos : (0 : ℝ) < ((k : ℕ) : ℝ) ^ r := by
      have : (0 : ℝ) < (k : ℕ) := by exact_mod_cast (show 0 < (k : ℕ) by have := k.2.1; omega)
      positivity
    have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < ((N : EulerShell (r * m)) : ℕ) by have := N.1.2.1; omega)
    refine ⟨k, ?_⟩
    have h1 : Real.log (((k : ℕ) : ℝ) ^ r) = Real.log ((N : ℕ) : ℝ) := by
      rw [Real.log_pow]; exact hk
    have h2 := Real.log_injOn_pos (mem_Ioi.2 hpos) (mem_Ioi.2 hNpos) h1
    exact_mod_cast h2

/-! ### Normalization and the mixture -/

/-- The normalized shell law `P_{m,σ} = μ_{m,σ}/S_m(σ)`. -/
def shellLaw (m : ℕ) (σ : ℝ) : Measure ℝ := ENNReal.ofReal (eulerShellSum m σ)⁻¹ • shellMeasure m σ

/-- The inherited conditional law `I_{m,r,σ} = (d_r)_* P_{m,rσ}`. -/
def inheritedLaw (m r : ℕ) (σ : ℝ) : Measure ℝ := (shellLaw m (r * σ)).map (dilate r)

/-- The excess conditional law `Q_{m,r,σ} = η_{m,r,σ}/C_{m,r}(σ)`. -/
def excessLaw (m r : ℕ) (σ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (excessSum m r σ)⁻¹ • excessMeasure m r σ

theorem isProbabilityMeasure_shellLaw (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (shellLaw m σ) := by
  constructor
  rw [shellLaw, Measure.smul_apply, shellMeasure_univ m hσ, smul_eq_mul,
    ← ENNReal.ofReal_mul (inv_nonneg.2 (eulerShellSum_pos hm hσ).le),
    inv_mul_cancel₀ (eulerShellSum_pos hm hσ).ne', ENNReal.ofReal_one]

theorem isProbabilityMeasure_excessLaw (hm : m ≠ 0) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (excessLaw m r σ) := by
  constructor
  rw [excessLaw, Measure.smul_apply, excessMeasure_univ m r hσ, smul_eq_mul,
    ← ENNReal.ofReal_mul (inv_nonneg.2 (excessSum_pos hm hr hσ).le),
    inv_mul_cancel₀ (excessSum_pos hm hr hσ).ne', ENNReal.ofReal_one]

theorem isProbabilityMeasure_inheritedLaw (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (inheritedLaw m r σ) := by
  haveI := isProbabilityMeasure_shellLaw hm (one_lt_mul_of_two_le hr hσ)
  exact Measure.isProbabilityMeasure_map (measurable_dilate r).aemeasurable

/-- **Corollary 2.2 (canonical mixture formation)**:
`P_{rm,σ} = α_{m,r}(σ) I_{m,r,σ} + β_{m,r}(σ) Q_{m,r,σ}`. -/
theorem shellLaw_mixture (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    shellLaw (r * m) σ = ENNReal.ofReal (survival m r σ) • inheritedLaw m r σ +
      ENNReal.ofReal (excessFraction m r σ) • excessLaw m r σ := by
  have hS := eulerShellSum_pos (m := r * m) (by nlinarith) hσ
  have hSm := eulerShellSum_pos hm (one_lt_mul_of_two_le hr hσ)
  have hC := excessSum_pos (m := m) (by omega) hr hσ
  have e1 : eulerShellSum m (r * σ) / eulerShellSum (r * m) σ * (eulerShellSum m (r * σ))⁻¹ =
      (eulerShellSum (r * m) σ)⁻¹ := by field_simp
  have e2 : excessSum m r σ / eulerShellSum (r * m) σ * (excessSum m r σ)⁻¹ =
      (eulerShellSum (r * m) σ)⁻¹ := by field_simp
  rw [shellLaw, shellMeasure_formation (by omega), smul_add, inheritedLaw, shellLaw,
    Measure.map_smul, excessLaw, smul_smul, smul_smul, survival, excessFraction,
    ← ENNReal.ofReal_mul (div_nonneg hSm.le hS.le), ← ENNReal.ofReal_mul (div_nonneg hC.le hS.le),
    e1, e2]

end GaloisForLFunctions.HTGeometry.FormationExcess
