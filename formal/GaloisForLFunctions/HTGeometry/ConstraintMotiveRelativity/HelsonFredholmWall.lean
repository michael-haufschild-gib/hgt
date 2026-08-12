import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.SimpleEigenvalueAffineBranch
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.HelsonDivisorResponse

/-!
# The Helson trace-class realization and its Fredholm crossing response

A divisor-summable coefficient stream `a` is realized as the trace-class Helson operator
`K_a(j,k) = a_{jk}` on `ℓ²`, assembled as an absolutely trace-norm convergent sum of the divisor
blocks.  The realization is coefficient faithful, is self-adjoint for real streams, and its
quadratic form at a vector `u` is the divisor convolution `W_u`.

At a simple nonzero eigenvalue the eigenvalue branch of `K_{a+th}` is differentiable with
derivative `∑ h_n W_u(n)`, so the Fredholm wall `τ ∈ spec K_a` carries the exact crossing covector
`h ↦ -∑ h_n W_u(n)`, which is continuous and nonzero.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open RHTower
open scoped InnerProductSpace

/-- The Helson chart `ℓ²(ℕ)`. -/
abbrev HelsonSpace : Type := lp (fun _ : ℕ => ℂ) 2

/-- The coordinate vector of the Helson chart. -/
noncomputable def helsonBasis (j : ℕ) : HelsonSpace := lp.single 2 j (1 : ℂ)

@[simp] theorem norm_helsonBasis (j : ℕ) : ‖helsonBasis j‖ = 1 := by
  rw [helsonBasis, lp.norm_single (by norm_num), norm_one]

@[simp] theorem inner_helsonBasis_left (j : ℕ) (f : HelsonSpace) :
    inner ℂ (helsonBasis j) f = (f : ℕ → ℂ) j := by
  rw [helsonBasis, lp.inner_single_left]
  simp [RCLike.inner_apply]

@[simp] theorem inner_helsonBasis_right (j : ℕ) (f : HelsonSpace) :
    inner ℂ f (helsonBasis j) = (starRingEnd ℂ) ((f : ℕ → ℂ) j) := by
  rw [helsonBasis, lp.inner_single_right]
  simp [RCLike.inner_apply]

@[simp] theorem helsonBasis_coe (j k : ℕ) :
    ((helsonBasis j : HelsonSpace) : ℕ → ℂ) k = if k = j then 1 else 0 := by
  rw [helsonBasis, lp.single_apply, Pi.single_apply]

section Realization

/-- **`(HFR.5)`.**  The divisor block of the Helson realization. -/
noncomputable def helsonBlockOp (a : ℕ → ℂ) (n : ℕ) : SchattenOneOperator HelsonSpace :=
  ∑ p ∈ n.divisorsAntidiagonal, a n • rankOneSchattenOne (helsonBasis p.1) (helsonBasis p.2)

theorem norm_helsonBlockOp_le (a : ℕ → ℂ) (n : ℕ) :
    ‖helsonBlockOp a n‖ ≤ (divisorWeight n : ℝ) * ‖a n‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ n.divisorsAntidiagonal,
      ‖a n • rankOneSchattenOne (helsonBasis p.1) (helsonBasis p.2)‖ = ‖a n‖ := by
    intro p _
    rw [norm_smul, norm_rankOneSchattenOne, norm_helsonBasis, norm_helsonBasis]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, divisorWeight]

theorem summable_norm_helsonBlockOp {a : ℕ → ℂ} (ha : HelsonSummable a) :
    Summable fun n : ℕ => ‖helsonBlockOp a n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_helsonBlockOp_le a) ha

theorem summable_helsonBlockOp {a : ℕ → ℂ} (ha : HelsonSummable a) :
    Summable (helsonBlockOp a) :=
  Summable.of_norm (summable_norm_helsonBlockOp ha)

/-- **`(HFR.2)`, `(HFR.5)`.**  The Helson operator of a divisor-summable stream, assembled as an
absolutely trace-norm convergent sum of rank ones. -/
noncomputable def helsonOperator (a : ℕ → ℂ) : SchattenOneOperator HelsonSpace :=
  ∑' n : ℕ, helsonBlockOp a n

/-- The divisor block as a bounded operator on the chart. -/
noncomputable def helsonBlockCLM (a : ℕ → ℂ) (n : ℕ) : HelsonSpace →L[ℂ] HelsonSpace :=
  (helsonBlockOp a n).val

/-- The Helson operator as a bounded operator on the chart. -/
noncomputable def helsonCLM (a : ℕ → ℂ) : HelsonSpace →L[ℂ] HelsonSpace :=
  (helsonOperator a).val

/-- **Theorem 2.1 (1), `(HFR.3)`.**  The Helson realization is trace class with trace norm at most
the divisor-weighted coefficient mass. -/
theorem norm_helsonOperator_le {a : ℕ → ℂ} (ha : HelsonSummable a) :
    ‖helsonOperator a‖ ≤ ∑' n : ℕ, (divisorWeight n : ℝ) * ‖a n‖ := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_helsonBlockOp ha)) ?_
  exact (summable_norm_helsonBlockOp ha).tsum_le_tsum (norm_helsonBlockOp_le a) ha

/-- The Helson operator is a compact operator on the chart. -/
theorem isCompactOperator_helsonOperator (a : ℕ → ℂ) :
    IsCompactOperator (helsonCLM a) :=
  (helsonOperator a).isCompactOperator

theorem coe_helsonOperator {a : ℕ → ℂ} (ha : HelsonSummable a) :
    ((helsonOperator a : SchattenOneOperator HelsonSpace) : HelsonSpace →L[ℂ] HelsonSpace)
      = ∑' n : ℕ, ((helsonBlockOp a n : SchattenOneOperator HelsonSpace) :
          HelsonSpace →L[ℂ] HelsonSpace) := by
  have h := ContinuousLinearMap.map_tsum
    (schattenOneCoeCLM (H := HelsonSpace)) (summable_helsonBlockOp ha)
  simpa [helsonOperator] using h

/-- The quadratic form of a divisor block. -/
theorem inner_helsonBlockOp_apply (a : ℕ → ℂ) (n : ℕ) (x y : HelsonSpace) :
    inner ℂ x (helsonBlockCLM a n y)
      = a n * ∑ p ∈ n.divisorsAntidiagonal,
        (starRingEnd ℂ) ((x : ℕ → ℂ) p.1) * (y : ℕ → ℂ) p.2 := by
  classical
  have hcoe : helsonBlockCLM a n
      = ∑ p ∈ n.divisorsAntidiagonal,
        a n • (InnerProductSpace.rankOne ℂ (helsonBasis p.1) (helsonBasis p.2)) := by
    have h := map_sum (schattenOneCoeCLM (H := HelsonSpace))
      (fun p : ℕ × ℕ => a n • rankOneSchattenOne (helsonBasis p.1) (helsonBasis p.2))
      n.divisorsAntidiagonal
    simp only [schattenOneCoeCLM_apply, SchattenOneOperator.coe_smul,
      rankOneSchattenOne_coe] at h
    simpa [helsonBlockCLM, helsonBlockOp] using h
  rw [hcoe]
  rw [sum_apply, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_apply, inner_smul_right, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_helsonBasis_left, inner_helsonBasis_right]
  ring

end Realization

section Entries

/-- Evaluation of a Schatten-one operator at a pair of chart vectors. -/
noncomputable def entryCLM (x y : HelsonSpace) : SchattenOneOperator HelsonSpace →L[ℂ] ℂ :=
  (innerSL ℂ x) ∘L ((ContinuousLinearMap.apply ℂ HelsonSpace y) ∘L schattenOneCoeCLM)

@[simp] theorem entryCLM_apply (x y : HelsonSpace) (T : SchattenOneOperator HelsonSpace) :
    entryCLM x y T = inner ℂ x ((T : HelsonSpace →L[ℂ] HelsonSpace) y) := rfl

/-- The quadratic form of the Helson operator, atom by atom. -/
theorem inner_helsonOperator_apply {a : ℕ → ℂ} (ha : HelsonSummable a) (x y : HelsonSpace) :
    inner ℂ x (helsonCLM a y)
      = ∑' n : ℕ, a n * ∑ p ∈ n.divisorsAntidiagonal,
        (starRingEnd ℂ) ((x : ℕ → ℂ) p.1) * (y : ℕ → ℂ) p.2 := by
  have h := ContinuousLinearMap.map_tsum (entryCLM x y) (summable_helsonBlockOp ha)
  rw [entryCLM_apply] at h
  rw [show helsonCLM a = (∑' z : ℕ, helsonBlockOp a z).val from rfl, h]
  refine tsum_congr fun n => ?_
  rw [entryCLM_apply]
  exact inner_helsonBlockOp_apply a n x y

/-- **Theorem 2.1 (2), `(HFR.4)`.**  The realization is coefficient faithful: the matrix entry at
`(j,k)` is the coefficient at `jk`. -/
theorem inner_helsonOperator_basis {a : ℕ → ℂ} (ha : HelsonSummable a) {j k : ℕ}
    (hj : j ≠ 0) (hk : k ≠ 0) :
    inner ℂ (helsonBasis j) (helsonCLM a (helsonBasis k)) = a (j * k) := by
  classical
  rw [inner_helsonOperator_apply ha]
  have hfib : ∀ n : ℕ, (∑ p ∈ n.divisorsAntidiagonal,
      (starRingEnd ℂ) (((helsonBasis j : HelsonSpace) : ℕ → ℂ) p.1)
        * (((helsonBasis k : HelsonSpace) : ℕ → ℂ) p.2))
      = if (j, k) ∈ n.divisorsAntidiagonal then 1 else 0 := by
    intro n
    by_cases hmem : (j, k) ∈ n.divisorsAntidiagonal
    · rw [if_pos hmem, Finset.sum_eq_single (j, k)]
      · simp
      · intro p _ hp
        rcases Prod.ext_iff.not.mp hp with hne
        by_cases h1 : p.1 = j
        · have h2 : p.2 ≠ k := fun h2 => hne ⟨h1, h2⟩
          simp [helsonBasis_coe, h2]
        · simp [helsonBasis_coe, h1]
      · intro hcon; exact absurd hmem hcon
    · rw [if_neg hmem]
      refine Finset.sum_eq_zero fun p hp => ?_
      by_cases h1 : p.1 = j
      · by_cases h2 : p.2 = k
        · exact absurd (by rw [← h1, ← h2]; exact hp) hmem
        · simp [helsonBasis_coe, h2]
      · simp [helsonBasis_coe, h1]
  rw [tsum_congr fun n => by rw [hfib n]]
  rw [tsum_eq_single (j * k)]
  · have hmem : (j, k) ∈ (j * k).divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.mul_ne_zero hj hk⟩
    rw [if_pos hmem, mul_one]
  · intro n hn
    rw [if_neg, mul_zero]
    intro hmem
    exact hn (Nat.mem_divisorsAntidiagonal.mp hmem).1.symm

end Entries

section SelfAdjoint

theorem sum_divisorsAntidiagonal_swap {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → ℕ → M) :
    ∑ p ∈ n.divisorsAntidiagonal, g p.1 p.2 = ∑ p ∈ n.divisorsAntidiagonal, g p.2 p.1 := by
  rw [Nat.sum_divisorsAntidiagonal g, Nat.sum_divisorsAntidiagonal' (fun j k => g k j)]

theorem isSelfAdjoint_helsonBlockOp {a : ℕ → ℂ} (hreal : ∀ n, (starRingEnd ℂ) (a n) = a n)
    (n : ℕ) :
    IsSelfAdjoint (helsonBlockCLM a n) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm]
  rw [inner_helsonBlockOp_apply a n y x, inner_helsonBlockOp_apply a n x y, map_mul, hreal,
    map_sum]
  congr 1
  rw [sum_divisorsAntidiagonal_swap n (fun j k =>
    (starRingEnd ℂ) ((starRingEnd ℂ) ((y : ℕ → ℂ) j) * (x : ℕ → ℂ) k))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- **Theorem 2.1 (3).**  A real coefficient stream gives a self-adjoint Helson operator. -/
theorem isSelfAdjoint_helsonOperator {a : ℕ → ℂ} (ha : HelsonSummable a)
    (hreal : ∀ n, (starRingEnd ℂ) (a n) = a n) :
    IsSelfAdjoint (helsonCLM a) := by
  classical
  have hclosed : IsClosed {T : HelsonSpace →L[ℂ] HelsonSpace | IsSelfAdjoint T} := by
    have : {T : HelsonSpace →L[ℂ] HelsonSpace | IsSelfAdjoint T}
        = {T | ContinuousLinearMap.adjoint T = T} := rfl
    rw [this]
    exact isClosed_eq (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := HelsonSpace)
      (F := HelsonSpace)).continuous continuous_id
  have hsum : HasSum (fun n : ℕ => helsonBlockCLM a n) (helsonCLM a) := by
    have h := (summable_helsonBlockOp ha).hasSum.map
      (schattenOneCoeCLM (H := HelsonSpace)).toLinearMap.toAddMonoidHom
      (schattenOneCoeCLM (H := HelsonSpace)).continuous
    simpa [helsonCLM, helsonBlockCLM, helsonOperator, Function.comp_def] using h
  refine hclosed.mem_of_tendsto hsum ?_
  filter_upwards with s
  show star (∑ n ∈ s, helsonBlockCLM a n) = ∑ n ∈ s, helsonBlockCLM a n
  rw [star_sum]
  exact Finset.sum_congr rfl fun n _ => isSelfAdjoint_helsonBlockOp hreal n

end SelfAdjoint

section Response

/-- **`(HFR.7)`.**  The Helson quadratic form is the divisor-convolution pairing. -/
theorem inner_helsonCLM_self {h : ℕ → ℂ} (hh : HelsonSummable h) (u : HelsonSpace) :
    inner ℂ u (helsonCLM h u) = ∑' n : ℕ, h n * divisorConv ((u : HelsonSpace) : ℕ → ℂ) n := by
  rw [inner_helsonOperator_apply hh]
  exact tsum_congr fun n => by rw [divisorConv]

theorem helsonBlockOp_add (a b : ℕ → ℂ) (n : ℕ) :
    helsonBlockOp (fun m => a m + b m) n = helsonBlockOp a n + helsonBlockOp b n := by
  rw [helsonBlockOp, helsonBlockOp, helsonBlockOp, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [add_smul]

theorem helsonBlockOp_smul (c : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    helsonBlockOp (fun m => c * a m) n = c • helsonBlockOp a n := by
  rw [helsonBlockOp, helsonBlockOp, Finset.smul_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [smul_smul]

theorem helsonSummable_smul (c : ℂ) {a : ℕ → ℂ} (ha : HelsonSummable a) :
    HelsonSummable (fun m => c * a m) := by
  have h := ha.mul_left ‖c‖
  refine h.congr fun n => ?_
  rw [norm_mul]
  ring

theorem helsonOperator_add {a b : ℕ → ℂ} (ha : HelsonSummable a) (hb : HelsonSummable b) :
    helsonOperator (fun m => a m + b m) = helsonOperator a + helsonOperator b := by
  rw [helsonOperator, helsonOperator, helsonOperator,
    ← (summable_helsonBlockOp ha).tsum_add (summable_helsonBlockOp hb)]
  exact tsum_congr fun n => helsonBlockOp_add a b n

theorem helsonOperator_smul (c : ℂ) {a : ℕ → ℂ} (ha : HelsonSummable a) :
    helsonOperator (fun m => c * a m) = c • helsonOperator a := by
  rw [helsonOperator, helsonOperator, ← (summable_helsonBlockOp ha).tsum_const_smul c]
  exact tsum_congr fun n => helsonBlockOp_smul c a n

theorem helsonCLM_affine {a h : ℕ → ℂ} (ha : HelsonSummable a) (hh : HelsonSummable h) (t : ℝ) :
    helsonCLM (fun n => a n + (t : ℂ) * h n) = helsonCLM a + (t : ℂ) • helsonCLM h := by
  rw [helsonCLM, helsonCLM, helsonCLM,
    helsonOperator_add ha (helsonSummable_smul (t : ℂ) hh), helsonOperator_smul (t : ℂ) hh]
  rfl

/-- **Theorem 3.2, `(HFR.7)`.**  At a simple nonzero eigenvalue of `K_a` the eigenvalue branch of
`K_{a+th}` is differentiable with derivative the divisor-convolution response `∑ h_n W_u(n)`. -/
theorem helson_eigenBranch {a h : ℕ → ℂ} (ha : HelsonSummable a) (hh : HelsonSummable h)
    {μ : ℂ} {u : HelsonSpace} (hp : IsSimpleEigenpair (helsonCLM a) μ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ lam : ℝ → ℂ, ∃ v : ℝ → HelsonSpace,
      lam 0 = μ ∧ v 0 = u ∧
      (∀ t : ℝ, |t| < δ → helsonCLM (fun n => a n + (t : ℂ) * h n) (v t) = lam t • v t) ∧
      (∀ t : ℝ, |t| < δ → v t ≠ 0) ∧
      HasDerivAt lam (∑' n : ℕ, h n * divisorConv ((u : HelsonSpace) : ℕ → ℂ) n) 0 := by
  obtain ⟨δ, hδ, lam, v, h0, hv0, heq, hne, hd⟩ := exists_eigenBranch hp (helsonCLM h)
  refine ⟨δ, hδ, lam, v, h0, hv0, fun t ht => ?_, hne, ?_⟩
  · rw [helsonCLM_affine ha hh t]
    exact heq t ht
  · rwa [inner_helsonCLM_self hh u] at hd

end Response

section Wall

/-- The zeroth chart coordinate is annihilated by every Helson operator. -/
theorem inner_helsonBasis_zero_helsonCLM {a : ℕ → ℂ} (ha : HelsonSummable a) (y : HelsonSpace) :
    inner ℂ (helsonBasis 0) (helsonCLM a y) = 0 := by
  rw [inner_helsonOperator_apply ha]
  have hz : ∀ n : ℕ, a n * ∑ p ∈ n.divisorsAntidiagonal,
      (starRingEnd ℂ) (((helsonBasis 0 : HelsonSpace) : ℕ → ℂ) p.1)
        * (((y : HelsonSpace) : ℕ → ℂ) p.2) = 0 := by
    intro n
    have hterm : ∀ p ∈ n.divisorsAntidiagonal,
        (starRingEnd ℂ) (((helsonBasis 0 : HelsonSpace) : ℕ → ℂ) p.1)
          * (((y : HelsonSpace) : ℕ → ℂ) p.2) = 0 := by
      intro p hp
      have hp1 : p.1 ≠ 0 := by
        intro h0
        have h2 := (Nat.mem_divisorsAntidiagonal.mp hp).2
        rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, h0, zero_mul] at h2
        exact h2 rfl
      simp [helsonBasis_coe, hp1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, mul_zero]
  rw [tsum_congr hz, tsum_zero]

theorem eigenvector_coord_zero {a : ℕ → ℂ} (ha : HelsonSummable a) {μ : ℂ} (hμ : μ ≠ 0)
    {u : HelsonSpace} (heq : helsonCLM a u = μ • u) : (u : ℕ → ℂ) 0 = 0 := by
  have h := inner_helsonBasis_zero_helsonCLM ha u
  rw [heq, inner_smul_right, inner_helsonBasis_left] at h
  exact (mul_eq_zero.mp h).resolve_left hμ

/-- **Theorem 4.1 (2).**  The wall condition: `τ` is a spectral point of `K_a` exactly when it is an
eigenvalue.  This is the Fredholm alternative for the compact operator `K_a`. -/
theorem helson_wall_iff {a : ℕ → ℂ} {τ : ℂ} (hτ : τ ≠ 0) :
    (∃ u : HelsonSpace, u ≠ 0 ∧ helsonCLM a u = τ • u) ↔ τ ∈ spectrum ℂ (helsonCLM a) := by
  have hcpt : IsCompactOperator (helsonCLM a) := (helsonOperator a).isCompactOperator
  rw [← IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt hτ]
  constructor
  · rintro ⟨u, hu, heq⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := u) ⟨?_, hu⟩
    rw [Module.End.mem_eigenspace_iff]
    exact heq
  · intro hev
    obtain ⟨u, hmem, hu⟩ := hev.exists_hasEigenvector
    exact ⟨u, hu, Module.End.mem_eigenspace_iff.mp hmem⟩

/-- **Theorem 4.1 (1).**  `τ - K_a` is Fredholm of index zero: injectivity on the chart already
forces invertibility. -/
theorem helson_index_zero {a : ℕ → ℂ} {τ : ℂ} (hτ : τ ≠ 0)
    (hinj : ∀ u : HelsonSpace, helsonCLM a u = τ • u → u = 0) :
    τ ∈ resolventSet ℂ (helsonCLM a) := by
  have hcpt : IsCompactOperator (helsonCLM a) := (helsonOperator a).isCompactOperator
  refine (hcpt.hasEigenvalue_or_mem_resolventSet hτ).resolve_left ?_
  intro hev
  obtain ⟨u, hmem, hu⟩ := hev.exists_hasEigenvector
  exact hu (hinj u (Module.End.mem_eigenspace_iff.mp hmem))

/-- **`(HFR.9)`, `(HFR.9a)`.**  The crossing covector of a simple Fredholm wall. -/
noncomputable def crossingForm (u : HelsonSpace) (h : ℕ → ℂ) : ℂ :=
  - ∑' n : ℕ, h n * divisorConv ((u : HelsonSpace) : ℕ → ℂ) n

theorem crossingForm_eq_neg_inner {h : ℕ → ℂ} (hh : HelsonSummable h) (u : HelsonSpace) :
    crossingForm u h = - inner ℂ u (helsonCLM h u) := by
  rw [crossingForm, inner_helsonCLM_self hh u]

/-- **Theorem 4.1 (3).**  The wall gap `Ω(t) = τ - μ(t)` has derivative the crossing form. -/
theorem hasDerivAt_wallGap {a h : ℕ → ℂ} (ha : HelsonSummable a) (hh : HelsonSummable h)
    {μ : ℂ} {u : HelsonSpace} (hp : IsSimpleEigenpair (helsonCLM a) μ u) (τ : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ lam : ℝ → ℂ, ∃ v : ℝ → HelsonSpace,
      lam 0 = μ ∧ v 0 = u ∧
      (∀ t : ℝ, |t| < δ → helsonCLM (fun n => a n + (t : ℂ) * h n) (v t) = lam t • v t) ∧
      (∀ t : ℝ, |t| < δ → v t ≠ 0) ∧
      HasDerivAt (fun t => τ - lam t) (crossingForm u h) 0 := by
  obtain ⟨δ, hδ, lam, v, h0, hv0, heq, hne, hd⟩ := helson_eigenBranch ha hh hp
  exact ⟨δ, hδ, lam, v, h0, hv0, heq, hne, by simpa [crossingForm] using hd.const_sub τ⟩

theorem norm_crossing_term_le {h : ℕ → ℂ} (u : HelsonSpace) (hu : ‖u‖ = 1) (n : ℕ) :
    ‖h n * divisorConv ((u : HelsonSpace) : ℕ → ℂ) n‖ ≤ (divisorWeight n : ℝ) * ‖h n‖ := by
  rw [norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : divisorConv ((u : HelsonSpace) : ℕ → ℂ) 0 = 0 := by
      rw [divisorConv]
      simp
    rw [h0, norm_zero, mul_zero]
    positivity
  · have h1 : ‖divisorConv ((u : HelsonSpace) : ℕ → ℂ) n‖ ≤ 1 := by
      have h := norm_divisorConv_le u n
      rw [hu] at h
      simpa using h
    have h2 : (1 : ℝ) ≤ (divisorWeight n : ℝ) := by
      have h3 : 1 ≤ divisorWeight n := by
        rw [divisorWeight]
        exact Finset.card_pos.mpr ⟨(1, n), Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn.ne'⟩⟩
      exact_mod_cast h3
    nlinarith [norm_nonneg (h n), norm_nonneg (divisorConv ((u : HelsonSpace) : ℕ → ℂ) n)]

theorem summable_norm_crossing {h : ℕ → ℂ} (hh : HelsonSummable h) (u : HelsonSpace)
    (hu : ‖u‖ = 1) :
    Summable fun n : ℕ => ‖h n * divisorConv ((u : HelsonSpace) : ℕ → ℂ) n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_crossing_term_le u hu) hh

/-- **Theorem 4.1 (4), `(HFR.9a)`.**  The crossing covector is continuous on `ℓ¹_d`. -/
theorem norm_crossingForm_le {h : ℕ → ℂ} (hh : HelsonSummable h) (u : HelsonSpace)
    (hu : ‖u‖ = 1) : ‖crossingForm u h‖ ≤ ∑' n : ℕ, (divisorWeight n : ℝ) * ‖h n‖ := by
  rw [crossingForm, norm_neg]
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_crossing hh u hu)) ?_
  exact (summable_norm_crossing hh u hu).tsum_le_tsum (norm_crossing_term_le u hu) hh

/-- **Theorem 4.1 (4).**  The crossing covector is nonzero: the atom at the square of the least
active index detects it. -/
theorem exists_crossingForm_ne_zero {a : ℕ → ℂ} (ha : HelsonSummable a) {μ : ℂ} (hμ : μ ≠ 0)
    {u : HelsonSpace} (hu : u ≠ 0) (heq : helsonCLM a u = μ • u) :
    ∃ h : ℕ → ℂ, HelsonSummable h ∧ crossingForm u h ≠ 0 := by
  classical
  have hu0 : (u : ℕ → ℂ) 0 = 0 := eigenvector_coord_zero ha hμ heq
  have hex : ∃ m : ℕ, 0 < m ∧ (u : ℕ → ℂ) m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu
    refine lp.ext (funext fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hu0
    · simpa using hcon n hn
  set m := Nat.find hex with hm
  obtain ⟨hmpos, hmne⟩ := Nat.find_spec hex
  have hlt : ∀ j, 0 < j → j < m → (u : ℕ → ℂ) j = 0 := by
    intro j hj hjm
    by_contra hne
    exact absurd ⟨hj, hne⟩ (Nat.find_min hex hjm)
  refine ⟨fun n => if n = m * m then 1 else 0, ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {m * m}) fun n hn => ?_
    have : n ≠ m * m := by simpa using hn
    simp [this]
  · rw [crossingForm, neg_ne_zero, tsum_eq_single (m * m)]
    · rw [if_pos rfl, one_mul, divisorConv_least_sq hmpos hmne hlt]
      exact mul_ne_zero (by simpa using hmne) hmne
    · intro n hn
      simp [hn]

end Wall

section Countermodels

/-- **§6, countermodel 2.**  A threshold can be fitted: every eigenvalue manufactures a wall. -/
theorem eigenvalue_mem_spectrum {a : ℕ → ℂ} {τ : ℂ} {u : HelsonSpace} (hu : u ≠ 0)
    (heq : helsonCLM a u = τ • u) : τ ∈ spectrum ℂ (helsonCLM a) := by
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨U, hU⟩ := hunit
  have hker : ((algebraMap ℂ (HelsonSpace →L[ℂ] HelsonSpace)) τ - helsonCLM a) u = 0 := by
    simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self, heq, sub_self]
  apply hu
  have hinj : Function.Injective ((algebraMap ℂ (HelsonSpace →L[ℂ] HelsonSpace)) τ
      - helsonCLM a) := by
    rw [← hU]
    intro x y hxy
    have := congrArg (fun z => ((U⁻¹ : (HelsonSpace →L[ℂ] HelsonSpace)ˣ) :
      HelsonSpace →L[ℂ] HelsonSpace) z) hxy
    simpa [← mul_apply_eq_comp] using this
  have := hinj (by simpa using hker : _ = ((algebraMap ℂ (HelsonSpace →L[ℂ] HelsonSpace)) τ
    - helsonCLM a) 0)
  exact this

/-- **§6, countermodel 4.**  Strong summability is a real restriction: the constant stream has
coefficient-faithful entries but is not divisor summable. -/
theorem not_helsonSummable_one : ¬ HelsonSummable (fun _ : ℕ => (1 : ℂ)) := by
  intro hs
  have ht := hs.tendsto_atTop_zero
  have h1 : ∀ n : ℕ, 0 < n → (1 : ℝ) ≤ (divisorWeight n : ℝ) * ‖(1 : ℂ)‖ := by
    intro n hn
    rw [norm_one, mul_one]
    have h2 : 1 ≤ divisorWeight n := by
      rw [divisorWeight]
      exact Finset.card_pos.mpr ⟨(1, n), Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn.ne'⟩⟩
    exact_mod_cast h2
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN1, hN2⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  linarith [h1 N hN2, hN1]

/-- **§6, countermodel 3.**  Distinct simple eigenlines give distinct response covectors. -/
theorem divisorConv_ne_of_ne :
    divisorConv ((helsonBasis 1 : HelsonSpace) : ℕ → ℂ)
      ≠ divisorConv ((helsonBasis 2 : HelsonSpace) : ℕ → ℂ) := by
  intro hcon
  have h := congrFun hcon 1
  rw [divisorConv, divisorConv] at h
  simp [Nat.divisorsAntidiagonal_one, helsonBasis_coe] at h

end Countermodels

section Projective

variable {σ : ℝ}

/-- **Corollary 5.1, `(HFR.12)`.**  The wall gap responds to a source intervention through the
normalized exchange tangent. -/
theorem projective_wall_response (c h : ℕ → ℂ) (u : HelsonSpace) :
    crossingForm u (mellinExchangeSeed σ c h)
      = - ∑' n : ℕ, mellinExchangeSeed σ c h n
          * divisorConv ((u : HelsonSpace) : ℕ → ℂ) n := rfl

/-- **Corollary 5.1.**  The radial direction is in the kernel of the exchange tangent, hence of the
projective response. -/
theorem mellinExchangeSeed_self (c : ℕ → ℂ) (hZ : mellinMass σ c ≠ 0) (n : ℕ) :
    mellinExchangeSeed σ c c n = 0 := by
  rw [mellinExchangeSeed]
  field_simp
  ring

end Projective

end HTGeometry.ConstraintMotiveRelativity
