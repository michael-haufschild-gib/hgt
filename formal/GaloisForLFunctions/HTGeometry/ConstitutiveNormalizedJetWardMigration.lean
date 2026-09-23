import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationInformationProperness
import GaloisForLFunctions.HTGeometry.MarkedVariationDynamics
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection

/-!
# Normalized jet splitting, Markov coinvariants, and Ward-anomaly migration

This module formalizes the finite algebraic and finite-probability mechanisms of ULF-SRSM-9.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## All-order common-recovery splitting -/

/-- Finite jets through order `N`. -/
abbrev FiniteJet (N : ℕ) (E : Type*) := Fin (N + 1) → E

/-- The jet index `n-k`, retained in the same finite jet. -/
def jetSubIndex {N : ℕ} (n : Fin (N + 1)) (k : ℕ) : Fin (N + 1) :=
  ⟨n.1 - k, lt_of_le_of_lt (Nat.sub_le n.1 k) n.2⟩

@[simp] theorem jetSubIndex_zero {N : ℕ} (n : Fin (N + 1)) :
    jetSubIndex n 0 = n := by
  apply Fin.ext
  simp [jetSubIndex]

section JetSplitting

variable {K E V : Type*} [Field K]
variable [AddCommGroup E] [Module K E] [AddCommGroup V] [Module K V]

/-- Leibniz formation of a coefficient jet by normalized shape operators. -/
def normalizedFormedJet (N : ℕ) (M : ℕ → E →ₗ[K] V)
    (c : FiniteJet N E) : FiniteJet N V :=
  fun n => ∑ k ∈ Finset.range (n.1 + 1),
    (Nat.choose n.1 k : K) • M k (c (jetSubIndex n k))

/-- The normalized jet formation as a linear map. -/
def normalizedJetFormation (N : ℕ) (M : ℕ → E →ₗ[K] V) :
    FiniteJet N E →ₗ[K] FiniteJet N V where
  toFun := normalizedFormedJet N M
  map_add' c d := by
    ext n
    simp only [normalizedFormedJet, Pi.add_apply, LinearMap.map_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' a c := by
    ext n
    simp only [normalizedFormedJet, Pi.smul_apply, LinearMap.map_smul, RingHom.id_apply,
      smul_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [smul_smul, mul_comm]

/-- Common recovery applied levelwise to a finite jet. -/
def levelwiseJetRecovery (N : ℕ) (R : V →ₗ[K] E) :
    FiniteJet N V →ₗ[K] FiniteJet N E where
  toFun v := fun n => R (v n)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- All coefficient derivatives are recovered exactly from the normalized formed jet. -/
theorem levelwiseJetRecovery_normalizedJetFormation
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    (levelwiseJetRecovery N R).comp (normalizedJetFormation N M) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  funext n
  change R (∑ k ∈ Finset.range (n.1 + 1),
    (Nat.choose n.1 k : K) • M k (c (jetSubIndex n k))) = c n
  rw [map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single 0]
  · simp [hM0]
  · intro k hk hkn0
    simp [hMk k (Nat.pos_of_ne_zero hkn0)]
  · simp

/-- A normalized finite jet formation is injective. -/
theorem normalizedJetFormation_injective
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    Function.Injective (normalizedJetFormation N M) := by
  apply Function.LeftInverse.injective
  intro c
  have h := LinearMap.congr_fun
    (levelwiseJetRecovery_normalizedJetFormation N R M hM0 hMk) c
  simpa using h

/-- Projection onto the formed-jet range. -/
def normalizedJetProjection (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V) :
    FiniteJet N V →ₗ[K] FiniteJet N V :=
  (normalizedJetFormation N M).comp (levelwiseJetRecovery N R)

theorem normalizedJetProjection_idempotent
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    IsIdempotentElem (normalizedJetProjection N R M) := by
  apply LinearMap.ext
  intro v
  change normalizedJetFormation N M
      (levelwiseJetRecovery N R
        (normalizedJetFormation N M (levelwiseJetRecovery N R v))) =
    normalizedJetFormation N M (levelwiseJetRecovery N R v)
  have h := LinearMap.congr_fun
    (levelwiseJetRecovery_normalizedJetFormation N R M hM0 hMk)
    (levelwiseJetRecovery N R v)
  have hrecover : levelwiseJetRecovery N R
      (normalizedJetFormation N M (levelwiseJetRecovery N R v)) =
        levelwiseJetRecovery N R v := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  rw [hrecover]

theorem normalizedJetProjection_range
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    LinearMap.range (normalizedJetProjection N R M) =
      LinearMap.range (normalizedJetFormation N M) := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact ⟨levelwiseJetRecovery N R w, rfl⟩
  · rintro v ⟨c, rfl⟩
    refine ⟨normalizedJetFormation N M c, ?_⟩
    change normalizedJetFormation N M
      (levelwiseJetRecovery N R (normalizedJetFormation N M c)) =
        normalizedJetFormation N M c
    have h := LinearMap.congr_fun
      (levelwiseJetRecovery_normalizedJetFormation N R M hM0 hMk) c
    have hrecover : levelwiseJetRecovery N R (normalizedJetFormation N M c) = c := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    rw [hrecover]

theorem normalizedJetProjection_ker
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    LinearMap.ker (normalizedJetProjection N R M) =
      LinearMap.ker (levelwiseJetRecovery N R) := by
  ext v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hv
    have hrecover := LinearMap.congr_fun
      (levelwiseJetRecovery_normalizedJetFormation N R M hM0 hMk)
      (levelwiseJetRecovery N R v)
    have hrecover' : levelwiseJetRecovery N R
        (normalizedJetFormation N M (levelwiseJetRecovery N R v)) =
          levelwiseJetRecovery N R v := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hrecover
    calc
      levelwiseJetRecovery N R v =
          levelwiseJetRecovery N R
            (normalizedJetFormation N M (levelwiseJetRecovery N R v)) := hrecover'.symm
      _ = 0 := by
        change levelwiseJetRecovery N R (normalizedJetProjection N R M v) = 0
        rw [hv]
        simp
  · intro hv
    change normalizedJetFormation N M (levelwiseJetRecovery N R v) = 0
    rw [hv]
    simp

/-- Component form of all-order recovery: the order-`n` coefficient is recovered exactly. -/
theorem commonRecovery_normalizedFormedJet_component
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0)
    (c : FiniteJet N E) (n : Fin (N + 1)) :
    R (normalizedFormedJet N M c n) = c n := by
  have hrecover := LinearMap.congr_fun
    (levelwiseJetRecovery_normalizedJetFormation N R M hM0 hMk) c
  change (fun n => R (normalizedFormedJet N M c n)) = c at hrecover
  exact congrFun hrecover n

/-- Exact direct-sum splitting into formed jets and the vertical recovery kernel. -/
theorem normalizedJetFormation_isCompl_ker_recovery
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    IsCompl (LinearMap.range (normalizedJetFormation N M))
      (LinearMap.ker (levelwiseJetRecovery N R)) := by
  have hP := normalizedJetProjection_idempotent N R M hM0 hMk
  rw [← normalizedJetProjection_range N R M hM0 hMk,
    ← normalizedJetProjection_ker N R M hM0 hMk]
  exact LinearMap.IsIdempotentElem.isCompl hP

/-- Every jet splits into its recovered formed part and a vertical recovery-kernel part. -/
theorem normalizedJet_decomposition
    (N : ℕ) (R : V →ₗ[K] E) (M : ℕ → E →ₗ[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0)
    (v : FiniteJet N V) :
    v = normalizedJetFormation N M (levelwiseJetRecovery N R v) +
      (v - normalizedJetFormation N M (levelwiseJetRecovery N R v)) ∧
    v - normalizedJetFormation N M (levelwiseJetRecovery N R v) ∈
      LinearMap.ker (levelwiseJetRecovery N R) := by
  constructor
  · abel
  · simp only [LinearMap.mem_ker, map_sub]
    have h := LinearMap.congr_fun
      (levelwiseJetRecovery_normalizedJetFormation N R M hM0 hMk)
      (levelwiseJetRecovery N R v)
    have hrecover : levelwiseJetRecovery N R
        (normalizedJetFormation N M (levelwiseJetRecovery N R v)) =
          levelwiseJetRecovery N R v := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    rw [hrecover, sub_self]

/-! ### Exact finite-jet norm control and topological range closure -/

/-- Totalized inclusion of a natural index into a finite jet. On the relevant range this is the
ordinary inclusion; totalization keeps triangular sum reindexing proof-independent. -/
def rangeJetIndex (N n : ℕ) : Fin (N + 1) :=
  ⟨n % (N + 1), Nat.mod_lt _ (Nat.zero_lt_succ N)⟩

@[simp] theorem rangeJetIndex_val_of_lt {N n : ℕ} (hn : n < N + 1) :
    (rangeJetIndex N n).1 = n := by
  simp [rangeJetIndex, Nat.mod_eq_of_lt hn]

theorem sum_fin_eq_sum_range_rangeJetIndex {A : Type*} [AddCommMonoid A]
    (N : ℕ) (f : Fin (N + 1) → A) :
    (∑ i, f i) = ∑ n ∈ Finset.range (N + 1), f (rangeJetIndex N n) := by
  calc
    (∑ i, f i) = ∑ i : Fin (N + 1), f (rangeJetIndex N i.1) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg f
      apply Fin.ext
      exact (rangeJetIndex_val_of_lt i.2).symm
    _ = ∑ n ∈ Finset.range (N + 1), f (rangeJetIndex N n) :=
      Fin.sum_univ_eq_sum_range (fun n => f (rangeJetIndex N n)) (N + 1)

/-- Triangular convolution reindexing `(n,k) ↦ (n-k,k)` through jet order `N`. -/
theorem finiteJet_triangle_reindex (F : ℕ → ℕ → ℝ) : ∀ N : ℕ,
    (∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1), F (n - k) k) =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N - j + 1), F j k := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hinner :
          (∑ j ∈ Finset.range (N + 1),
              ∑ k ∈ Finset.range (N.succ - j + 1), F j k) =
            (∑ j ∈ Finset.range (N + 1),
              ∑ k ∈ Finset.range (N - j + 1), F j k) +
              ∑ j ∈ Finset.range (N + 1), F j (N + 1 - j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [Nat.succ_sub hjle]
        rw [Finset.sum_range_succ]
      have hrow :
          (∑ k ∈ Finset.range (N + 1 + 1), F (N + 1 - k) k) =
            ∑ j ∈ Finset.range (N + 1 + 1), F j (N + 1 - j) := by
        rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => F b a) (N + 1)]
        have hswap := @Finset.Nat.sum_antidiagonal_swap ℝ _ (N + 1)
          (fun p => F p.1 p.2)
        calc
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (N + 1), F ij.2 ij.1) =
              ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (N + 1), F ij.1 ij.2 := by
            simpa [Prod.swap] using hswap
          _ = ∑ j ∈ Finset.range (N + 1 + 1), F j (N + 1 - j) := by
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
      calc
        (∑ j ∈ Finset.range (N + 1),
            ∑ k ∈ Finset.range (N - j + 1), F j k) +
            ∑ k ∈ Finset.range (N + 1 + 1), F (N + 1 - k) k =
          (∑ j ∈ Finset.range (N + 1),
            ∑ k ∈ Finset.range (N - j + 1), F j k) +
            ((∑ j ∈ Finset.range (N + 1), F j (N + 1 - j)) +
              F (N + 1) 0) := by
          rw [hrow]
          simpa using congrArg
            (fun z => (∑ j ∈ Finset.range (N + 1),
              ∑ k ∈ Finset.range (N - j + 1), F j k) + z)
            (Finset.sum_range_succ (fun j => F j (N + 1 - j)) (N + 1))
        _ = ((∑ j ∈ Finset.range (N + 1),
            ∑ k ∈ Finset.range (N - j + 1), F j k) +
              ∑ j ∈ Finset.range (N + 1), F j (N + 1 - j)) +
                F (N + 1) 0 := by ring
        _ = (∑ j ∈ Finset.range (N + 1),
              ∑ k ∈ Finset.range (N.succ - j + 1), F j k) +
                F (N + 1) 0 := by rw [hinner]
        _ = (∑ j ∈ Finset.range (N + 1),
              ∑ k ∈ Finset.range (N.succ - j + 1), F j k) +
            ∑ k ∈ Finset.range (N.succ - N.succ + 1), F N.succ k := by simp
        _ = ∑ j ∈ Finset.range (N.succ + 1),
              ∑ k ∈ Finset.range (N.succ - j + 1), F j k := by
          exact (Finset.sum_range_succ
            (fun j => ∑ k ∈ Finset.range (N.succ - j + 1), F j k) (N + 1)).symm

/-- Finite-jet `ℓ¹` norm used in the normalized splitting estimate. -/
def finiteJetL1Norm {N : ℕ} {E : Type*} [Norm E] (c : FiniteJet N E) : ℝ :=
  ∑ n, ‖c n‖

/-- Column weight in the exact triangular operator bound. -/
def normalizedJetColumnWeight {E V : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup V] {K : Type*} [NontriviallyNormedField K]
    [NormedSpace K E] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) (j : Fin (N + 1)) : ℝ :=
  ∑ k ∈ Finset.range (N - j.1 + 1), (Nat.choose (j.1 + k) k : ℝ) * ‖M k‖

/-- Exact finite-order constant
`C_N = max_{0 ≤ j ≤ N} ∑_{k=0}^{N-j} choose(j+k,k) ‖M_k‖`. -/
def normalizedJetBound {E V : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup V] {K : Type*} [NontriviallyNormedField K]
    [NormedSpace K E] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (normalizedJetColumnWeight N M)

theorem normalizedJetColumnWeight_le_bound {E V : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup V]
    {K : Type*} [NontriviallyNormedField K] [NormedSpace K E] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) (j : Fin (N + 1)) :
    normalizedJetColumnWeight N M j ≤ normalizedJetBound N M := by
  exact Finset.le_sup' (normalizedJetColumnWeight N M) (Finset.mem_univ j)

/-- The finite maximum defining `normalizedJetBound` is attained. -/
theorem exists_normalizedJetColumnWeight_eq_bound {E V : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup V]
    {K : Type*} [NontriviallyNormedField K] [NormedSpace K E] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) :
    ∃ j : Fin (N + 1), normalizedJetColumnWeight N M j = normalizedJetBound N M := by
  have h := (Finset.le_sup'_iff (s := Finset.univ) (H := Finset.univ_nonempty)
    (f := normalizedJetColumnWeight N M)).mp (le_refl (normalizedJetBound N M))
  rcases h with ⟨j, hj, hle⟩
  exact ⟨j, le_antisymm (normalizedJetColumnWeight_le_bound N M j) hle⟩

/-- One row of normalized jet formation obeys its exact triangular norm majorant. -/
theorem normalizedFormedJet_row_bound
    {K E V : Type*} [RCLike K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) (c : FiniteJet N E) (n : Fin (N + 1)) :
    ‖normalizedFormedJet N (fun k => (M k).toLinearMap) c n‖ ≤
      ∑ k ∈ Finset.range (n.1 + 1),
        (Nat.choose n.1 k : ℝ) * ‖M k‖ * ‖c (jetSubIndex n k)‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_smul, RCLike.norm_natCast]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.le_opNorm (M k) (c (jetSubIndex n k)))
    (Nat.cast_nonneg _)

/-- Exact `C_N` upper estimate for normalized finite-jet formation. -/
theorem normalizedFormedJet_l1_upper_bound
    {K E V : Type*} [RCLike K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) (c : FiniteJet N E) :
    finiteJetL1Norm (normalizedFormedJet N (fun k => (M k).toLinearMap) c) ≤
      normalizedJetBound N M * finiteJetL1Norm c := by
  rw [finiteJetL1Norm, finiteJetL1Norm]
  calc
    (∑ n, ‖normalizedFormedJet N (fun k => (M k).toLinearMap) c n‖) ≤
        ∑ n : Fin (N + 1), ∑ k ∈ Finset.range (n.1 + 1),
          (Nat.choose n.1 k : ℝ) * ‖M k‖ * ‖c (jetSubIndex n k)‖ :=
      Finset.sum_le_sum fun n _ => normalizedFormedJet_row_bound N M c n
    _ = ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * ‖M k‖ * ‖c (rangeJetIndex N (n - k))‖ := by
      rw [sum_fin_eq_sum_range_rangeJetIndex]
      apply Finset.sum_congr rfl
      intro n hn
      have hidx : rangeJetIndex N n =
          (⟨n, Finset.mem_range.mp hn⟩ : Fin (N + 1)) := by
        apply Fin.ext
        exact rangeJetIndex_val_of_lt (Finset.mem_range.mp hn)
      rw [hidx]
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      apply congrArg c
      apply Fin.ext
      change n - k = (rangeJetIndex N (n - k)).1
      rw [rangeJetIndex_val_of_lt]
      exact lt_of_le_of_lt (Nat.sub_le n k) (Finset.mem_range.mp hn)
    _ = ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1),
          (Nat.choose ((n - k) + k) k : ℝ) * ‖M k‖ *
            ‖c (rangeJetIndex N (n - k))‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.sub_add_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N - j + 1),
          (Nat.choose (j + k) k : ℝ) * ‖M k‖ * ‖c (rangeJetIndex N j)‖ := by
      exact finiteJet_triangle_reindex
        (fun j k => (Nat.choose (j + k) k : ℝ) * ‖M k‖ * ‖c (rangeJetIndex N j)‖) N
    _ = ∑ j : Fin (N + 1), normalizedJetColumnWeight N M j * ‖c j‖ := by
      rw [sum_fin_eq_sum_range_rangeJetIndex]
      apply Finset.sum_congr rfl
      intro j hj
      rw [normalizedJetColumnWeight, Finset.sum_mul]
      rw [rangeJetIndex_val_of_lt (Finset.mem_range.mp hj)]
    _ ≤ ∑ j : Fin (N + 1), normalizedJetBound N M * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (normalizedJetColumnWeight_le_bound N M j) (norm_nonneg _)
    _ = normalizedJetBound N M * ∑ j : Fin (N + 1), ‖c j‖ := by
      rw [Finset.mul_sum]

/-- Continuous normalized jet formation between finite product normed spaces. -/
def normalizedJetFormationCLM
    {K E V : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) : FiniteJet N E →L[K] FiniteJet N V :=
  ContinuousLinearMap.pi fun n =>
    ∑ k ∈ Finset.range (n.1 + 1),
      (Nat.choose n.1 k : K) •
        (M k).comp (ContinuousLinearMap.proj (R := K)
          (φ := fun _ : Fin (N + 1) => E) (jetSubIndex n k))

@[simp] theorem normalizedJetFormationCLM_apply
    {K E V : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (M : ℕ → E →L[K] V) (c : FiniteJet N E) :
    normalizedJetFormationCLM N M c =
      normalizedFormedJet N (fun k => (M k).toLinearMap) c := by
  ext n
  simp [normalizedJetFormationCLM, normalizedFormedJet]

/-- Continuous levelwise common recovery. -/
def levelwiseJetRecoveryCLM
    {K E V : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (R : V →L[K] E) : FiniteJet N V →L[K] FiniteJet N E :=
  ContinuousLinearMap.pi fun n =>
    R.comp (ContinuousLinearMap.proj (R := K)
      (φ := fun _ : Fin (N + 1) => V) n)

@[simp] theorem levelwiseJetRecoveryCLM_apply
    {K E V : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (R : V →L[K] E) (v : FiniteJet N V) :
    levelwiseJetRecoveryCLM N R v = fun n => R (v n) := by
  rfl

/-- Contractive common recovery is contractive in the finite-jet `ℓ¹` norm. -/
theorem finiteJetL1Norm_levelwiseRecovery_le
    {K E V : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (R : V →L[K] E) (hR : ‖R‖ ≤ 1) (v : FiniteJet N V) :
    finiteJetL1Norm (fun n => R (v n)) ≤ finiteJetL1Norm v := by
  rw [finiteJetL1Norm, finiteJetL1Norm]
  apply Finset.sum_le_sum
  intro n hn
  calc
    ‖R (v n)‖ ≤ ‖R‖ * ‖v n‖ := ContinuousLinearMap.le_opNorm R (v n)
    _ ≤ 1 * ‖v n‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = ‖v n‖ := one_mul _

/-- Exact common recovery gives the lower `ℓ¹` bound, hence inverse norm at most one on range. -/
theorem normalizedJetFormation_l1_lower_bound
    {K E V : Type*} [RCLike K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (R : V →L[K] E) (M : ℕ → E →L[K] V)
    (hR : ‖R‖ ≤ 1)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0)
    (c : FiniteJet N E) :
    finiteJetL1Norm c ≤
      finiteJetL1Norm (normalizedFormedJet N (fun k => (M k).toLinearMap) c) := by
  have hrecover := LinearMap.congr_fun
    (levelwiseJetRecovery_normalizedJetFormation N R.toLinearMap
      (fun k => (M k).toLinearMap) hM0 hMk) c
  have hpoint : ∀ n,
      R (normalizedFormedJet N (fun k => (M k).toLinearMap) c n) = c n := by
    intro n
    exact congrFun (by simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hrecover) n
  calc
    finiteJetL1Norm c = finiteJetL1Norm (fun n =>
        R (normalizedFormedJet N (fun k => (M k).toLinearMap) c n)) := by
      apply congrArg finiteJetL1Norm
      funext n
      exact (hpoint n).symm
    _ ≤ finiteJetL1Norm (normalizedFormedJet N
        (fun k => (M k).toLinearMap) c) :=
      finiteJetL1Norm_levelwiseRecovery_le N R hR _

/-- Complete two-sided finite-order stability estimate. -/
theorem normalizedJetFormation_l1_bounds
    {K E V : Type*} [RCLike K]
    [SeminormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (R : V →L[K] E) (M : ℕ → E →L[K] V)
    (hR : ‖R‖ ≤ 1)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0)
    (c : FiniteJet N E) :
    finiteJetL1Norm c ≤
        finiteJetL1Norm (normalizedFormedJet N (fun k => (M k).toLinearMap) c) ∧
      finiteJetL1Norm (normalizedFormedJet N (fun k => (M k).toLinearMap) c) ≤
        normalizedJetBound N M * finiteJetL1Norm c := by
  exact ⟨normalizedJetFormation_l1_lower_bound N R M hR hM0 hMk c,
    normalizedFormedJet_l1_upper_bound N M c⟩

/-- Common recovery is a continuous left inverse of normalized jet formation. -/
theorem normalizedJetFormationCLM_hasLeftInverse
    {K E V : Type*} [RCLike K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (R : V →L[K] E) (M : ℕ → E →L[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    (normalizedJetFormationCLM N M).HasLeftInverse := by
  refine ⟨levelwiseJetRecoveryCLM N R, ?_⟩
  intro c
  have hrecover := LinearMap.congr_fun
    (levelwiseJetRecovery_normalizedJetFormation N R.toLinearMap
      (fun k => (M k).toLinearMap) hM0 hMk) c
  rw [normalizedJetFormationCLM_apply, levelwiseJetRecoveryCLM_apply]
  change (fun n => R (normalizedFormedJet N (fun k => (M k).toLinearMap) c n)) = c
    at hrecover
  exact hrecover

/-- The normalized finite-jet range is closed, with no completeness assumption on source or
target: continuous common recovery supplies a continuous left inverse. -/
theorem isClosed_range_normalizedFormedJet
    {K E V : Type*} [RCLike K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup V] [NormedSpace K V]
    (N : ℕ) (R : V →L[K] E) (M : ℕ → E →L[K] V)
    (hM0 : ∀ e, R (M 0 e) = e)
    (hMk : ∀ k, 0 < k → ∀ e, R (M k e) = 0) :
    IsClosed (Set.range
      (normalizedFormedJet N (fun k => (M k).toLinearMap))) := by
  have hli := normalizedJetFormationCLM_hasLeftInverse N R M hM0 hMk
  have heq : Set.range
      (normalizedFormedJet N (fun k => (M k).toLinearMap)) =
      Set.range (normalizedJetFormationCLM N M) := by
    ext v
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, normalizedJetFormationCLM_apply N M c⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, (normalizedJetFormationCLM_apply N M c).symm⟩
  rw [heq]
  exact hli.isClosed_range

end JetSplitting

/-! ## Markov coinvariants and universal mass reporters -/

section Coinvariants

variable {K V Y : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]

/-- Response radical generated by a family of linear refinements. -/
def linearResponseRadical (S : Set (V →ₗ[K] V)) : Submodule K V :=
  ⨆ T : S, LinearMap.range (T.1 - LinearMap.id)

/-- Invariant linear reporters are exactly those annihilating the response radical. -/
theorem invariant_reporter_iff_responseRadical_le_ker
    (S : Set (V →ₗ[K] V)) (tau : V →ₗ[K] Y) :
    (∀ T ∈ S, tau.comp T = tau) ↔
      linearResponseRadical S ≤ LinearMap.ker tau := by
  constructor
  · intro hinv
    apply iSup_le
    intro T
    rintro w ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    have h := LinearMap.congr_fun (hinv T.1 T.2) v
    have h' : tau (T.1 v) = tau v := by
      simpa only [LinearMap.comp_apply] using h
    rw [h', sub_self]
  · intro hrad T hT
    apply LinearMap.ext
    intro v
    have hgen : (T - (LinearMap.id : V →ₗ[K] V)) v ∈ linearResponseRadical S := by
      apply (le_iSup (fun U : S => LinearMap.range (U.1 - LinearMap.id)) ⟨T, hT⟩)
      exact ⟨v, rfl⟩
    have hzero := hrad hgen
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      sub_eq_zero] at hzero
    exact hzero

variable {E : Type*} [AddCommGroup E] [Module K E]

/-- Every linear refinement preserving a common recovery map. -/
def allRecoveryPreservingRefinements (R : V →ₗ[K] E) : Set (V →ₗ[K] V) :=
  {T | R.comp T = R}

/-- For a split common recovery, the universal refinement radical is exactly its vertical
kernel. This includes channelwise mass recovery as a special case. -/
theorem linearResponseRadical_allRecoveryPreserving_eq_ker
    (R : V →ₗ[K] E) (S : E →ₗ[K] V) (hRS : R.comp S = LinearMap.id) :
    linearResponseRadical (allRecoveryPreservingRefinements R) = LinearMap.ker R := by
  apply le_antisymm
  · apply iSup_le
    intro T
    rintro w ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    have h := LinearMap.congr_fun T.2 v
    have h' : R (T.1 v) = R v := by
      simpa only [LinearMap.comp_apply] using h
    rw [h', sub_self]
  · intro v hv
    let P : V →ₗ[K] V := S.comp R
    have hP : P ∈ allRecoveryPreservingRefinements R := by
      apply LinearMap.ext
      intro w
      change R (S (R w)) = R w
      have h := LinearMap.congr_fun hRS (R w)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    have hneg : -v ∈ linearResponseRadical (allRecoveryPreservingRefinements R) := by
      apply (le_iSup
        (fun T : allRecoveryPreservingRefinements R =>
          LinearMap.range (T.1 - LinearMap.id)) ⟨P, hP⟩)
      refine ⟨v, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply]
      change S (R v) - v = -v
      rw [show R v = 0 from hv]
      simp
    exact neg_mem_iff.mp hneg

/-- Universal common-recovery-invariant reporters are exactly maps through the recovered
horizontal quotient. -/
theorem invariant_under_allRecoveryPreserving_iff_factors
    (R : V →ₗ[K] E) (S : E →ₗ[K] V) (hRS : R.comp S = LinearMap.id)
    (tau : V →ₗ[K] Y) :
    (∀ T ∈ allRecoveryPreservingRefinements R, tau.comp T = tau) ↔
      ∃ sigma : E →ₗ[K] Y, tau = sigma.comp R := by
  constructor
  · intro hinv
    refine ⟨tau.comp S, ?_⟩
    apply LinearMap.ext
    intro v
    let P : V →ₗ[K] V := S.comp R
    have hP : P ∈ allRecoveryPreservingRefinements R := by
      apply LinearMap.ext
      intro w
      change R (S (R w)) = R w
      have h := LinearMap.congr_fun hRS (R w)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    have h := LinearMap.congr_fun (hinv P hP) v
    simpa only [LinearMap.comp_apply, P] using h.symm
  · rintro ⟨sigma, rfl⟩ T hT
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun hT v
    simpa only [LinearMap.comp_apply] using congrArg sigma h

/-- The full common-recovery coinvariant quotient is canonically the recovered space. -/
noncomputable def allRecoveryCoinvariantEquiv
    (R : V →ₗ[K] E) (S : E →ₗ[K] V) (hRS : R.comp S = LinearMap.id) :
    (V ⧸ linearResponseRadical (allRecoveryPreservingRefinements R)) ≃ₗ[K] E :=
  (Submodule.quotEquivOfEq _ _
      (linearResponseRadical_allRecoveryPreserving_eq_ker R S hRS)).trans
    (R.quotKerEquivOfSurjective fun e => by
      refine ⟨S e, ?_⟩
      have h := LinearMap.congr_fun hRS e
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Total mass on a finite source. -/
def finiteMass : (X → K) →ₗ[K] K where
  toFun v := ∑ x, v x
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' a v := by
    change (∑ x, a * v x) = a * ∑ x, v x
    rw [Finset.mul_sum]

/-- Coordinate mass carrier at `y`. -/
def finiteMassCarrier (y : X) : X → K :=
  fun x => if x = y then 1 else 0

@[simp] theorem finiteMass_finiteMassCarrier (y : X) :
    finiteMass (X := X) (K := K) (finiteMassCarrier (K := K) y) = 1 := by
  classical
  change (∑ x, if x = y then (1 : K) else 0) = 1
  calc
    (∑ x, if x = y then (1 : K) else 0) = if y = y then 1 else 0 := by
      apply Finset.sum_eq_single y
      · intro b _ hby
        simp [hby]
      · simp
    _ = 1 := by simp

/-- Reset every vector to its total mass concentrated at `y`. -/
def finiteMassReset (y : X) : (X → K) →ₗ[K] (X → K) where
  toFun v := finiteMass (X := X) (K := K) v • finiteMassCarrier y
  map_add' v w := by
    ext x
    by_cases hxy : x = y
    · subst x
      simp [finiteMass, finiteMassCarrier, Finset.sum_add_distrib]
    · simp [finiteMassCarrier, hxy]
  map_smul' a v := by
    ext x
    by_cases hxy : x = y
    · subst x
      simp [finiteMass, finiteMassCarrier, Finset.mul_sum]
    · simp [finiteMassCarrier, hxy]

@[simp] theorem finiteMassReset_apply (y : X) (v : X → K) :
    finiteMassReset (K := K) y v =
      finiteMass (X := X) (K := K) v • finiteMassCarrier y := rfl

theorem finiteMassReset_preserves_mass (y : X) :
    (finiteMass (X := X) (K := K)).comp (finiteMassReset (K := K) y) =
      finiteMass (X := X) (K := K) := by
  apply LinearMap.ext
  intro v
  change finiteMass (X := X) (K := K)
      (finiteMass (X := X) (K := K) v • finiteMassCarrier y) =
    finiteMass (X := X) (K := K) v
  rw [map_smul, finiteMass_finiteMassCarrier, smul_eq_mul, mul_one]

/-- Family of every mass-preserving linear refinement. -/
def allMassPreservingRefinements : Set ((X → K) →ₗ[K] (X → K)) :=
  {T | finiteMass.comp T = finiteMass}

variable [Nonempty X]

/-- Universal refinement radical is exactly the zero-mass hyperplane. -/
theorem linearResponseRadical_allMassPreserving_eq_ker_finiteMass :
    linearResponseRadical (allMassPreservingRefinements (X := X) (K := K)) =
      LinearMap.ker finiteMass := by
  apply le_antisymm
  · apply iSup_le
    intro T
    rintro w ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    have h := LinearMap.congr_fun T.2 v
    have h' : finiteMass (T.1 v) = finiteMass v := by
      simpa only [LinearMap.comp_apply] using h
    rw [h', sub_self]
  · intro v hv
    let y : X := Classical.choice inferInstance
    have hy : finiteMassReset (K := K) y ∈
        allMassPreservingRefinements (X := X) (K := K) :=
      finiteMassReset_preserves_mass y
    have hneg : -v ∈ linearResponseRadical
        (allMassPreservingRefinements (X := X) (K := K)) := by
      apply (le_iSup
        (fun T : allMassPreservingRefinements (X := X) (K := K) =>
          LinearMap.range (T.1 - LinearMap.id))
        ⟨finiteMassReset (K := K) y, hy⟩)
      refine ⟨v, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply]
      change finiteMass v • finiteMassCarrier y - v = -v
      rw [show finiteMass v = 0 from hv]
      simp
    exact neg_mem_iff.mp hneg

theorem finiteMass_surjective :
    Function.Surjective (finiteMass (X := X) (K := K)) := by
  intro a
  let y : X := Classical.choice inferInstance
  refine ⟨a • finiteMassCarrier (K := K) y, ?_⟩
  rw [map_smul, finiteMass_finiteMassCarrier, smul_eq_mul, mul_one]

/-- The universal Markov coinvariant quotient is canonically the one-dimensional mass line. -/
noncomputable def allMassCoinvariantEquiv :
    ((X → K) ⧸ linearResponseRadical
      (allMassPreservingRefinements (X := X) (K := K))) ≃ₗ[K] K :=
  (Submodule.quotEquivOfEq _ _
      linearResponseRadical_allMassPreserving_eq_ker_finiteMass).trans
    ((finiteMass (X := X) (K := K)).quotKerEquivOfSurjective finiteMass_surjective)

@[simp] theorem allMassCoinvariantEquiv_mk (v : X → K) :
    allMassCoinvariantEquiv
      (Submodule.Quotient.mk v :
        (X → K) ⧸ linearResponseRadical
          (allMassPreservingRefinements (X := X) (K := K))) = finiteMass v := by
  simp [allMassCoinvariantEquiv]

/-- A reporter invariant under every finite Markov refinement is mass and nothing else. -/
theorem invariant_under_allMassPreserving_iff_factors_finiteMass
    (tau : (X → K) →ₗ[K] Y) :
    (∀ T ∈ allMassPreservingRefinements (X := X) (K := K), tau.comp T = tau) ↔
      ∃ y₀ : Y, ∀ v, tau v = finiteMass v • y₀ := by
  constructor
  · intro hinv
    let y : X := Classical.choice inferInstance
    refine ⟨tau (finiteMassCarrier (K := K) y), ?_⟩
    intro v
    have hreset := LinearMap.congr_fun
      (hinv (finiteMassReset (K := K) y) (finiteMassReset_preserves_mass y)) v
    have hreset' : tau (finiteMassReset (K := K) y v) = tau v := by
      simpa only [LinearMap.comp_apply] using hreset
    calc
      tau v = tau (finiteMassReset (K := K) y v) := hreset'.symm
      _ = finiteMass v • tau (finiteMassCarrier (K := K) y) := by simp
  · rintro ⟨y₀, hy₀⟩ T hT
    apply LinearMap.ext
    intro v
    change tau (T v) = tau v
    rw [hy₀, hy₀]
    have hmass := LinearMap.congr_fun hT v
    have hmass' : finiteMass (T v) = finiteMass v := by
      simpa only [LinearMap.comp_apply] using hmass
    rw [hmass']

/-- Universal refinement-invariant reporters annihilate every normalized positive-order shape. -/
theorem invariant_reporter_annihilates_zeroMass
    (tau : (X → K) →ₗ[K] Y)
    (hinv : ∀ T ∈ allMassPreservingRefinements (X := X) (K := K), tau.comp T = tau)
    {v : X → K} (hv : finiteMass v = 0) : tau v = 0 := by
  obtain ⟨y₀, hy₀⟩ :=
    (invariant_under_allMassPreserving_iff_factors_finiteMass tau).mp hinv
  rw [hy₀, hv, zero_smul]

end Coinvariants

/-! ## Finite Bartlett--Ward balance and observation migration -/

section WardMigration

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Pointwise two-jet of a strictly positive finite probability family. -/
structure PositiveProbabilityTwoJet (X : Type*) [Fintype X] where
  p : X → ℝ
  dp : X → ℝ
  ddp : X → ℝ
  p_pos : ∀ x, 0 < p x
  sum_p : ∑ x, p x = 1
  sum_dp : ∑ x, dp x = 0
  sum_ddp : ∑ x, ddp x = 0

/-- Score of a finite positive probability two-jet. -/
def finiteScore (j : PositiveProbabilityTwoJet X) (x : X) : ℝ :=
  j.dp x / j.p x

/-- Score connection, i.e. the derivative of the score. -/
def finiteScoreConnection (j : PositiveProbabilityTwoJet X) (x : X) : ℝ :=
  j.ddp x / j.p x - (finiteScore j x) ^ (2 : ℕ)

/-- Expectation under the base probability of a finite two-jet. -/
def finiteJetExpectation (j : PositiveProbabilityTwoJet X) (f : X → ℝ) : ℝ :=
  ∑ x, j.p x * f x

/-- Fisher mass of a finite probability two-jet. -/
def finiteFisherMass (j : PositiveProbabilityTwoJet X) : ℝ :=
  finiteJetExpectation j (fun x => (finiteScore j x) ^ (2 : ℕ))

/-- Mean Ward connection. -/
def finiteMeanScoreConnection (j : PositiveProbabilityTwoJet X) : ℝ :=
  finiteJetExpectation j (finiteScoreConnection j)

/-- Pointwise inverse-response Riccati identity. -/
theorem finiteScoreConnection_add_sq (j : PositiveProbabilityTwoJet X) (x : X) :
    finiteScoreConnection j x + (finiteScore j x) ^ (2 : ℕ) = j.ddp x / j.p x := by
  unfold finiteScoreConnection
  ring

/-- The score is centered. -/
theorem finiteJetExpectation_score_eq_zero (j : PositiveProbabilityTwoJet X) :
    finiteJetExpectation j (finiteScore j) = 0 := by
  calc
    finiteJetExpectation j (finiteScore j) = ∑ x, j.dp x := by
      apply Finset.sum_congr rfl
      intro x _
      unfold finiteScore
      field_simp [ne_of_gt (j.p_pos x)]
    _ = 0 := j.sum_dp

/-- The total inverse-response Ward current vanishes. -/
theorem finiteJetExpectation_connection_add_score_sq_eq_zero
    (j : PositiveProbabilityTwoJet X) :
    finiteJetExpectation j
      (fun x => finiteScoreConnection j x + (finiteScore j x) ^ (2 : ℕ)) = 0 := by
  calc
    finiteJetExpectation j
        (fun x => finiteScoreConnection j x + (finiteScore j x) ^ (2 : ℕ)) =
        ∑ x, j.ddp x := by
      apply Finset.sum_congr rfl
      intro x _
      change j.p x * (finiteScoreConnection j x + (finiteScore j x) ^ (2 : ℕ)) = j.ddp x
      rw [finiteScoreConnection_add_sq]
      field_simp [ne_of_gt (j.p_pos x)]
    _ = 0 := j.sum_ddp

/-- Bartlett--Ward neutrality: Fisher mass is the negative mean score connection. -/
theorem finiteFisherMass_eq_neg_meanScoreConnection (j : PositiveProbabilityTwoJet X) :
    finiteFisherMass j = -finiteMeanScoreConnection j := by
  have h := finiteJetExpectation_connection_add_score_sq_eq_zero j
  have hsplit : finiteMeanScoreConnection j + finiteFisherMass j = 0 := by
    calc
      finiteMeanScoreConnection j + finiteFisherMass j =
          finiteJetExpectation j
            (fun x => finiteScoreConnection j x + (finiteScore j x) ^ (2 : ℕ)) := by
        unfold finiteMeanScoreConnection finiteFisherMass finiteJetExpectation
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := h
  linarith

theorem finiteFisherMass_nonneg (j : PositiveProbabilityTwoJet X) :
    0 ≤ finiteFisherMass j := by
  unfold finiteFisherMass finiteJetExpectation
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (j.p_pos x).le (sq_nonneg _)

/-- Observed probability coordinate. -/
def observedJetP (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) (y : Y) : ℝ :=
  ∑ x, K.weight y x * j.p x

/-- First observed derivative. -/
def observedJetDP (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) (y : Y) : ℝ :=
  ∑ x, K.weight y x * j.dp x

/-- Second observed derivative. -/
def observedJetDDP (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) (y : Y) : ℝ :=
  ∑ x, K.weight y x * j.ddp x

theorem sum_observedJetP (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :
    ∑ y, observedJetP K j y = 1 := by
  rw [show (∑ y, observedJetP K j y) =
      ∑ x, ∑ y, K.weight y x * j.p x by
    unfold observedJetP
    rw [Finset.sum_comm]]
  calc
    (∑ x, ∑ y, K.weight y x * j.p x) =
        ∑ x, (∑ y, K.weight y x) * j.p x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ x, j.p x := by simp [K.column_sum]
    _ = 1 := j.sum_p

theorem sum_observedJetDP (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :
    ∑ y, observedJetDP K j y = 0 := by
  rw [show (∑ y, observedJetDP K j y) =
      ∑ x, ∑ y, K.weight y x * j.dp x by
    unfold observedJetDP
    rw [Finset.sum_comm]]
  calc
    (∑ x, ∑ y, K.weight y x * j.dp x) =
        ∑ x, (∑ y, K.weight y x) * j.dp x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ x, j.dp x := by simp [K.column_sum]
    _ = 0 := j.sum_dp

theorem sum_observedJetDDP (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :
    ∑ y, observedJetDDP K j y = 0 := by
  rw [show (∑ y, observedJetDDP K j y) =
      ∑ x, ∑ y, K.weight y x * j.ddp x by
    unfold observedJetDDP
    rw [Finset.sum_comm]]
  calc
    (∑ x, ∑ y, K.weight y x * j.ddp x) =
        ∑ x, (∑ y, K.weight y x) * j.ddp x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ x, j.ddp x := by simp [K.column_sum]
    _ = 0 := j.sum_ddp

theorem observedJetP_nonneg
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) (y : Y) :
    0 ≤ observedJetP K j y := by
  unfold observedJetP
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (K.nonneg y x) (j.p_pos x).le

/-- An output of zero observed mass receives zero kernel weight from every positive source atom. -/
theorem kernelWeight_eq_zero_of_observedJetP_eq_zero
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    {y : Y} (hy : observedJetP K j y = 0) (x : X) :
    K.weight y x = 0 := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun x _ => mul_nonneg (K.nonneg y x) (j.p_pos x).le)).mp hy x (Finset.mem_univ x)
  exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt (j.p_pos x))

theorem observedJetDP_eq_zero_of_observedJetP_eq_zero
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    {y : Y} (hy : observedJetP K j y = 0) : observedJetDP K j y = 0 := by
  unfold observedJetDP
  apply Finset.sum_eq_zero
  intro x hx
  rw [kernelWeight_eq_zero_of_observedJetP_eq_zero K j hy x, zero_mul]

theorem observedJetDDP_eq_zero_of_observedJetP_eq_zero
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    {y : Y} (hy : observedJetP K j y = 0) : observedJetDDP K j y = 0 := by
  unfold observedJetDDP
  apply Finset.sum_eq_zero
  intro x hx
  rw [kernelWeight_eq_zero_of_observedJetP_eq_zero K j hy x, zero_mul]

/-- Active observed support: output coordinates carrying nonzero observed mass. -/
abbrev ActiveObservedOutput
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :=
  {y : Y // observedJetP K j y ≠ 0}

/-- Summing a function supported on the active observed outputs may be done over the active
subtype without changing its value. -/
theorem sum_activeObservedOutput_eq
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (f : Y → ℝ) (hf : ∀ y, observedJetP K j y = 0 → f y = 0) :
    (∑ y : ActiveObservedOutput K j, f y.1) = ∑ y : Y, f y := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun y : Y => observedJetP K j y ≠ 0) f
  have hcomplement :
      (∑ y : {y : Y // ¬ observedJetP K j y ≠ 0}, f y.1) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    exact hf y.1 (not_ne_iff.mp y.2)
  rw [hcomplement, add_zero] at hsplit
  exact hsplit

/-- Restriction of an observation kernel to its active output support. -/
def activeObservedKernel
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :
    FiniteMarkovKernel X (ActiveObservedOutput K j) where
  weight y x := K.weight y.1 x
  nonneg y x := K.nonneg y.1 x
  column_sum x := by
    calc
      (∑ y : ActiveObservedOutput K j, K.weight y.1 x) =
          ∑ y : Y, K.weight y x := by
        exact sum_activeObservedOutput_eq K j (fun y => K.weight y x)
          (fun y hy => kernelWeight_eq_zero_of_observedJetP_eq_zero K j hy x)
      _ = 1 := K.column_sum x

@[simp] theorem activeObservedKernel_weight
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (x : X) (y : ActiveObservedOutput K j) :
    (activeObservedKernel K j).weight y x = K.weight y.1 x := rfl

@[simp] theorem observedJetP_activeObservedKernel
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (y : ActiveObservedOutput K j) :
    observedJetP (activeObservedKernel K j) j y = observedJetP K j y.1 := by
  rfl

theorem activeObservedJetP_pos
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (y : ActiveObservedOutput K j) :
    0 < observedJetP (activeObservedKernel K j) j y := by
  change 0 < observedJetP K j y.1
  exact lt_of_le_of_ne (observedJetP_nonneg K j y.1) (Ne.symm y.2)

/-- Observed two-jet after deleting zero-probability output rows. -/
def observedProbabilityTwoJet
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) : PositiveProbabilityTwoJet Y where
  p := observedJetP K j
  dp := observedJetDP K j
  ddp := observedJetDDP K j
  p_pos := hactive
  sum_p := sum_observedJetP K j
  sum_dp := sum_observedJetDP K j
  sum_ddp := sum_observedJetDDP K j

/-- Observed probability two-jet on the literal active output support; no positivity premise is
needed from the caller. -/
def observedActiveProbabilityTwoJet
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :
    PositiveProbabilityTwoJet (ActiveObservedOutput K j) :=
  observedProbabilityTwoJet (activeObservedKernel K j) j (activeObservedJetP_pos K j)

/-- The observed score is the conditional mean of the source score. -/
theorem observed_score_conditional_identity
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) (y : Y) :
    observedJetP K j y * finiteScore (observedProbabilityTwoJet K j hactive) y =
      ∑ x, K.weight y x * j.p x * finiteScore j x := by
  have hq : observedJetP K j y ≠ 0 := ne_of_gt (hactive y)
  calc
    observedJetP K j y * finiteScore (observedProbabilityTwoJet K j hactive) y =
        observedJetDP K j y := by
      unfold finiteScore observedProbabilityTwoJet
      field_simp
    _ = ∑ x, K.weight y x * j.p x * finiteScore j x := by
      unfold observedJetDP finiteScore
      apply Finset.sum_congr rfl
      intro x _
      field_simp [ne_of_gt (j.p_pos x)]

/-- Joint conditional-score defect. -/
def jointScoreDefect
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) : ℝ :=
  ∑ x, ∑ y, j.p x * K.weight y x *
    (finiteScore j x - finiteScore (observedProbabilityTwoJet K j hactive) y) ^ (2 : ℕ)

theorem jointScoreDefect_nonneg
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) :
    0 ≤ jointScoreDefect K j hactive := by
  unfold jointScoreDefect
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg (j.p_pos x).le (K.nonneg y x)) (sq_nonneg _)

/-- Orthogonal score decomposition under a finite Markov observation. -/
theorem finiteFisherMass_sub_observed_eq_jointScoreDefect
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) :
    finiteFisherMass j - finiteFisherMass (observedProbabilityTwoJet K j hactive) =
      jointScoreDefect K j hactive := by
  let q := observedProbabilityTwoJet K j hactive
  have hsource :
      (∑ x, ∑ y, j.p x * K.weight y x * (finiteScore j x) ^ (2 : ℕ)) =
        finiteFisherMass j := by
    unfold finiteFisherMass finiteJetExpectation
    apply Finset.sum_congr rfl
    intro x _
    calc
      (∑ y, j.p x * K.weight y x * (finiteScore j x) ^ (2 : ℕ)) =
          j.p x * (finiteScore j x) ^ (2 : ℕ) * ∑ y, K.weight y x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = j.p x * (finiteScore j x) ^ (2 : ℕ) := by rw [K.column_sum]; ring
  have hcross :
      (∑ x, ∑ y, j.p x * K.weight y x * finiteScore j x * finiteScore q y) =
        finiteFisherMass q := by
    rw [Finset.sum_comm]
    unfold finiteFisherMass finiteJetExpectation
    apply Finset.sum_congr rfl
    intro y _
    calc
      (∑ x, j.p x * K.weight y x * finiteScore j x * finiteScore q y) =
          finiteScore q y *
            (∑ x, K.weight y x * j.p x * finiteScore j x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = finiteScore q y * (observedJetP K j y * finiteScore q y) := by
        rw [observed_score_conditional_identity]
      _ = q.p y * (finiteScore q y) ^ (2 : ℕ) := by
        change finiteScore q y * (q.p y * finiteScore q y) =
          q.p y * (finiteScore q y) ^ (2 : ℕ)
        ring
  have hobserved :
      (∑ x, ∑ y, j.p x * K.weight y x * (finiteScore q y) ^ (2 : ℕ)) =
        finiteFisherMass q := by
    rw [Finset.sum_comm]
    unfold finiteFisherMass finiteJetExpectation
    apply Finset.sum_congr rfl
    intro y _
    calc
      (∑ x, j.p x * K.weight y x * (finiteScore q y) ^ (2 : ℕ)) =
          (finiteScore q y) ^ (2 : ℕ) * ∑ x, K.weight y x * j.p x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = q.p y * (finiteScore q y) ^ (2 : ℕ) := by
        change (finiteScore q y) ^ (2 : ℕ) * q.p y = q.p y * (finiteScore q y) ^ (2 : ℕ)
        ring
  unfold jointScoreDefect
  change finiteFisherMass j - finiteFisherMass q =
    ∑ x, ∑ y, j.p x * K.weight y x *
      (finiteScore j x - finiteScore q y) ^ (2 : ℕ)
  calc
    finiteFisherMass j - finiteFisherMass q =
        (∑ x, ∑ y, j.p x * K.weight y x * (finiteScore j x) ^ (2 : ℕ)) -
          2 * (∑ x, ∑ y,
            j.p x * K.weight y x * finiteScore j x * finiteScore q y) +
          (∑ x, ∑ y, j.p x * K.weight y x * (finiteScore q y) ^ (2 : ℕ)) := by
      rw [hsource, hcross, hobserved]
      ring
    _ = ∑ x, ∑ y,
          (j.p x * K.weight y x * (finiteScore j x) ^ (2 : ℕ) -
            2 * (j.p x * K.weight y x * finiteScore j x * finiteScore q y) +
            j.p x * K.weight y x * (finiteScore q y) ^ (2 : ℕ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = ∑ x, ∑ y, j.p x * K.weight y x *
          (finiteScore j x - finiteScore q y) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

/-- Fisher loss is exactly migration of the mean Ward anomaly. -/
theorem finiteFisherLoss_eq_meanConnection_migration
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) :
    finiteFisherMass j - finiteFisherMass (observedProbabilityTwoJet K j hactive) =
      finiteMeanScoreConnection (observedProbabilityTwoJet K j hactive) -
        finiteMeanScoreConnection j := by
  rw [finiteFisherMass_eq_neg_meanScoreConnection,
    finiteFisherMass_eq_neg_meanScoreConnection]
  ring

/-- Complete Fisher/Ward observation law, including nonnegativity. -/
theorem finiteFisherWardMigration
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) :
    finiteFisherMass j - finiteFisherMass (observedProbabilityTwoJet K j hactive) =
        jointScoreDefect K j hactive ∧
      finiteFisherMass j - finiteFisherMass (observedProbabilityTwoJet K j hactive) =
        finiteMeanScoreConnection (observedProbabilityTwoJet K j hactive) -
          finiteMeanScoreConnection j ∧
      0 ≤ finiteFisherMass j -
        finiteFisherMass (observedProbabilityTwoJet K j hactive) := by
  refine ⟨finiteFisherMass_sub_observed_eq_jointScoreDefect K j hactive,
    finiteFisherLoss_eq_meanConnection_migration K j hactive, ?_⟩
  rw [finiteFisherMass_sub_observed_eq_jointScoreDefect K j hactive]
  exact jointScoreDefect_nonneg K j hactive

/-- Equality occurs exactly when source score is constant on every active observation fibre. -/
theorem finiteFisherLoss_eq_zero_iff_score_observed
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (hactive : ∀ y, 0 < observedJetP K j y) :
    finiteFisherMass j - finiteFisherMass (observedProbabilityTwoJet K j hactive) = 0 ↔
      ∀ x y, 0 < K.weight y x →
        finiteScore j x = finiteScore (observedProbabilityTwoJet K j hactive) y := by
  rw [finiteFisherMass_sub_observed_eq_jointScoreDefect K j hactive]
  unfold jointScoreDefect
  constructor
  · intro hzero x y hKxy
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (fun x _ => by
        apply Finset.sum_nonneg
        intro y _
        exact mul_nonneg (mul_nonneg (j.p_pos x).le (K.nonneg y x)) (sq_nonneg _))).mp
          hzero x (Finset.mem_univ x)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (fun y _ =>
        mul_nonneg (mul_nonneg (j.p_pos x).le (K.nonneg y x)) (sq_nonneg _))).mp
          hall y (Finset.mem_univ y)
    have hpK : 0 < j.p x * K.weight y x := mul_pos (j.p_pos x) hKxy
    have hsquare :
        (finiteScore j x - finiteScore (observedProbabilityTwoJet K j hactive) y) ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hpK)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro hscore
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    by_cases hKxy : K.weight y x = 0
    · simp [hKxy]
    · have hKpos : 0 < K.weight y x := lt_of_le_of_ne (K.nonneg y x) (Ne.symm hKxy)
      simp [hscore x y hKpos]

/-! ### Premise-free active-support observation law -/

/-- Conditional-score defect after canonically deleting zero-mass output rows. -/
def activeJointScoreDefect
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) : ℝ :=
  jointScoreDefect (activeObservedKernel K j) j (activeObservedJetP_pos K j)

/-- On the active support, the observed score is the conditional source-score mean, with no
caller-supplied positivity hypothesis. -/
theorem observedActive_score_conditional_identity
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X)
    (y : ActiveObservedOutput K j) :
    observedJetP K j y.1 * finiteScore (observedActiveProbabilityTwoJet K j) y =
      ∑ x, K.weight y.1 x * j.p x * finiteScore j x := by
  simpa [observedActiveProbabilityTwoJet] using
    observed_score_conditional_identity (activeObservedKernel K j) j
      (activeObservedJetP_pos K j) y

/-- Exact Fisher loss/conditional variance/Ward-connection migration on the canonical active
output support. This is the unconditional form of the observation theorem. -/
theorem finiteFisherWardMigration_active
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :
    finiteFisherMass j - finiteFisherMass (observedActiveProbabilityTwoJet K j) =
        activeJointScoreDefect K j ∧
      finiteFisherMass j - finiteFisherMass (observedActiveProbabilityTwoJet K j) =
        finiteMeanScoreConnection (observedActiveProbabilityTwoJet K j) -
          finiteMeanScoreConnection j ∧
      0 ≤ finiteFisherMass j - finiteFisherMass (observedActiveProbabilityTwoJet K j) := by
  simpa [observedActiveProbabilityTwoJet, activeJointScoreDefect] using
    finiteFisherWardMigration (activeObservedKernel K j) j (activeObservedJetP_pos K j)

/-- Equality in active-support Fisher monotonicity occurs exactly when source score is constant
on every positive kernel fibre. -/
theorem finiteFisherLoss_active_eq_zero_iff_score_observed
    (K : FiniteMarkovKernel X Y) (j : PositiveProbabilityTwoJet X) :
    finiteFisherMass j - finiteFisherMass (observedActiveProbabilityTwoJet K j) = 0 ↔
      ∀ (x : X) (y : ActiveObservedOutput K j), 0 < K.weight y.1 x →
        finiteScore j x = finiteScore (observedActiveProbabilityTwoJet K j) y := by
  simpa [observedActiveProbabilityTwoJet, activeObservedKernel] using
    finiteFisherLoss_eq_zero_iff_score_observed
      (activeObservedKernel K j) j (activeObservedJetP_pos K j)

/-! ### Sharp affine Bernoulli countermodel -/

/-- Two-point affine probability jet at the neutral parameter. -/
def affineBernoulliTwoJet : PositiveProbabilityTwoJet Bool where
  p := fun _ => 1 / 2
  dp := fun b => if b then 1 / 2 else -(1 / 2)
  ddp := fun _ => 0
  p_pos := by
    intro b
    positivity
  sum_p := by
    simp
  sum_dp := by
    simp
  sum_ddp := by
    simp

@[simp] theorem affineBernoulliTwoJet_score_true :
    finiteScore affineBernoulliTwoJet true = 1 := by
  simp [finiteScore, affineBernoulliTwoJet]

@[simp] theorem affineBernoulliTwoJet_score_false :
    finiteScore affineBernoulliTwoJet false = -1 := by
  simp [finiteScore, affineBernoulliTwoJet]

@[simp] theorem affineBernoulliTwoJet_connection (b : Bool) :
    finiteScoreConnection affineBernoulliTwoJet b = -1 := by
  cases b <;> simp [finiteScoreConnection, finiteScore, affineBernoulliTwoJet]

/-- Exact countermodel: affine source, positive Fisher mass one, mean connection minus one. -/
theorem affineBernoulliTwoJet_bartlett_countermodel :
    finiteFisherMass affineBernoulliTwoJet = 1 ∧
      finiteMeanScoreConnection affineBernoulliTwoJet = -1 ∧
      finiteJetExpectation affineBernoulliTwoJet
        (fun b => finiteScoreConnection affineBernoulliTwoJet b +
          (finiteScore affineBernoulliTwoJet b) ^ (2 : ℕ)) = 0 := by
  constructor
  · rw [finiteFisherMass, finiteJetExpectation, Fintype.sum_bool]
    change (1 / 2) * (finiteScore affineBernoulliTwoJet true) ^ (2 : ℕ) +
      (1 / 2) * (finiteScore affineBernoulliTwoJet false) ^ (2 : ℕ) = 1
    rw [affineBernoulliTwoJet_score_true, affineBernoulliTwoJet_score_false]
    ring
  constructor
  · rw [finiteMeanScoreConnection, finiteJetExpectation, Fintype.sum_bool]
    change (1 / 2) * finiteScoreConnection affineBernoulliTwoJet true +
      (1 / 2) * finiteScoreConnection affineBernoulliTwoJet false = -1
    rw [affineBernoulliTwoJet_connection, affineBernoulliTwoJet_connection]
    ring
  · exact finiteJetExpectation_connection_add_score_sq_eq_zero affineBernoulliTwoJet

end WardMigration

end


end GaloisForLFunctions.HTGeometry
