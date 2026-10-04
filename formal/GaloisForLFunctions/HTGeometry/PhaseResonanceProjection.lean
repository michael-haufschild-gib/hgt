import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Phase resonance projection and small-divisor properness

Let `U eⱼ = zⱼ eⱼ` be a diagonal unitary on `ℓ²(J)`, `|zⱼ| = 1`.  On Hilbert–Schmidt operators,
written as square-summable kernels `X ∈ ℓ²(J × J)`, conjugation `α(X) = U* X U` and the
transgression `δ_U = 1 - α` are diagonal multipliers on the matrix units:
`α(E_jk) = z̄ⱼ z_k E_jk`, `δ_U(E_jk) = (1 - z̄ⱼ z_k) E_jk` (`matrixOf_adjoint_comp_comp`).

* **Resonance projection.**  `Π_U` keeps the resonant entries `zⱼ = z_k`.  Then
  `ker δ_U = ran Π_U`, `ran Π_U ⟂ ran δ_U`, `closure (ran δ_U) = ker Π_U`, and under a positive
  small-divisor gap `ran δ_U = ker Π_U` with the canonical splitting `X = Π_U X + δ_U G_U X`;
  the oscillatory inverse has norm exactly `g(U)⁻¹`.
* **Cesàro formation.**  `N⁻¹ ∑_{n<N} αⁿ(X) → Π_U X`.
* **Global properness.**  `ran δ_U` is closed exactly when the distinct phases are uniformly
  separated, which for unit phases happens exactly when only finitely many distinct phases
  occur; with infinitely many phases the finite-aperture inverse norms are unbounded.
* **Reflection.**  `z ↦ z̄` preserves the resonance partition and every multiplier modulus.
-/

open Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {J : Type*}

/-- The Hilbert–Schmidt kernel space `ℓ²(J × J)`. -/
abbrev KernelSpace (J : Type*) : Type _ := lp (fun _ : J × J => ℂ) 2

/-! ### Phase multipliers -/

section Multipliers

/-- The phase ratio `z̄ⱼ z_k` of the matrix unit `E_jk`. -/
def phaseRatio (z : J → ℂ) (p : J × J) : ℂ := conj (z p.1) * z p.2

/-- The resonance indicator `1_{zⱼ = z_k}`. -/
def resonanceInd (z : J → ℂ) (p : J × J) : ℂ := if z p.1 = z p.2 then 1 else 0

variable {z : J → ℂ}

theorem norm_phaseRatio (hz : ∀ j, ‖z j‖ = 1) (p : J × J) : ‖phaseRatio z p‖ = 1 := by
  rw [phaseRatio, norm_mul, Complex.norm_conj, hz, hz, one_mul]

theorem conj_mul_self_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) : conj a * a = 1 := by
  rw [Complex.conj_mul', ha]
  norm_num

/-- `|1 - z̄ⱼ z_k| = |zⱼ - z_k|` for unit phases. -/
theorem norm_one_sub_phaseRatio (hz : ∀ j, ‖z j‖ = 1) (p : J × J) :
    ‖1 - phaseRatio z p‖ = ‖z p.1 - z p.2‖ := by
  have h : 1 - phaseRatio z p = conj (z p.1) * (z p.1 - z p.2) := by
    rw [phaseRatio, mul_sub, conj_mul_self_of_norm_eq_one (hz p.1)]
  rw [h, norm_mul, Complex.norm_conj, hz, one_mul]

theorem phaseRatio_eq_one_iff (hz : ∀ j, ‖z j‖ = 1) (p : J × J) :
    phaseRatio z p = 1 ↔ z p.1 = z p.2 := by
  rw [← sub_eq_zero (a := z p.1), ← norm_eq_zero, ← norm_one_sub_phaseRatio hz, norm_eq_zero,
    sub_eq_zero, eq_comm]

theorem one_sub_phaseRatio_eq_zero_iff (hz : ∀ j, ‖z j‖ = 1) (p : J × J) :
    1 - phaseRatio z p = 0 ↔ z p.1 = z p.2 := by
  rw [sub_eq_zero, eq_comm, phaseRatio_eq_one_iff hz]

theorem norm_one_sub_phaseRatio_le (hz : ∀ j, ‖z j‖ = 1) (p : J × J) :
    ‖1 - phaseRatio z p‖ ≤ 2 := by
  calc ‖1 - phaseRatio z p‖ ≤ ‖(1 : ℂ)‖ + ‖phaseRatio z p‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_phaseRatio hz, norm_one]; norm_num

theorem norm_resonanceInd_le (p : J × J) : ‖resonanceInd z p‖ ≤ 1 := by
  unfold resonanceInd
  split_ifs <;> simp

/-- The resolvent multiplier: `(1 - z̄ⱼ z_k)⁻¹` off resonance, `0` on resonance. -/
def phaseResolventMult (z : J → ℂ) (p : J × J) : ℂ :=
  if z p.1 = z p.2 then 0 else (1 - phaseRatio z p)⁻¹

/-- **Uniform phase separation**: the nonzero transgression multipliers stay at least `c` away
from `0`. -/
def PhaseSeparated (z : J → ℂ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ p : J × J, z p.1 ≠ z p.2 → c ≤ ‖1 - phaseRatio z p‖

/-- The small-divisor gap `g(U) = inf_{zⱼ ≠ z_k} |1 - z̄ⱼ z_k|`. -/
def transgressionGap (z : J → ℂ) : ℝ :=
  sInf {r | ∃ p : J × J, z p.1 ≠ z p.2 ∧ ‖1 - phaseRatio z p‖ = r}

theorem transgressionGap_le {p : J × J} (hp : z p.1 ≠ z p.2) :
    transgressionGap z ≤ ‖1 - phaseRatio z p‖ :=
  csInf_le ⟨0, by rintro _ ⟨q, -, rfl⟩; exact norm_nonneg _⟩ ⟨p, hp, rfl⟩

theorem norm_phaseResolventMult_le {c : ℝ} (hc : PhaseSeparated z c)
    (p : J × J) : ‖phaseResolventMult z p‖ ≤ c⁻¹ := by
  unfold phaseResolventMult
  split_ifs with h
  · rw [norm_zero]
    exact inv_nonneg.mpr hc.1.le
  · rw [norm_inv]
    exact inv_anti₀ hc.1 (hc.2 p h)

end Multipliers

/-! ### The operators on the Hilbert–Schmidt kernel space -/

section Operators

variable {z : J → ℂ}

/-- Conjugation `α(X) = U* X U` on the kernel space: multiplication by `z̄ⱼ z_k`. -/
def phaseConj (hz : ∀ j, ‖z j‖ = 1) :
    lp (fun _ : J × J => ℂ) 2 →L[ℂ] lp (fun _ : J × J => ℂ) 2 :=
  lpDiagonalCLM (phaseRatio z) zero_le_one fun p => (norm_phaseRatio hz p).le

/-- The transgression `δ_U = 1 - α`: multiplication by `1 - z̄ⱼ z_k`. -/
def phaseTransgression (hz : ∀ j, ‖z j‖ = 1) :
    lp (fun _ : J × J => ℂ) 2 →L[ℂ] lp (fun _ : J × J => ℂ) 2 :=
  lpDiagonalCLM (fun p => 1 - phaseRatio z p) zero_le_two (norm_one_sub_phaseRatio_le hz)

/-- The resonance projection `Π_U = ∑_λ P_λ · P_λ`: keeps the entries with `zⱼ = z_k`. -/
def resonanceProj (z : J → ℂ) : lp (fun _ : J × J => ℂ) 2 →L[ℂ] lp (fun _ : J × J => ℂ) 2 :=
  lpDiagonalCLM (resonanceInd z) zero_le_one norm_resonanceInd_le

/-- The oscillatory inverse `G_U` under a separation constant `c`. -/
def phaseResolvent {c : ℝ} (hc : PhaseSeparated z c) :
    lp (fun _ : J × J => ℂ) 2 →L[ℂ] lp (fun _ : J × J => ℂ) 2 :=
  lpDiagonalCLM (phaseResolventMult z) (inv_nonneg.mpr hc.1.le) (norm_phaseResolventMult_le hc)

@[simp] theorem phaseConj_apply (hz : ∀ j, ‖z j‖ = 1) (x : lp (fun _ : J × J => ℂ) 2)
    (p : J × J) : phaseConj hz x p = phaseRatio z p * x p := rfl

@[simp] theorem phaseTransgression_apply (hz : ∀ j, ‖z j‖ = 1) (x : lp (fun _ : J × J => ℂ) 2)
    (p : J × J) : phaseTransgression hz x p = (1 - phaseRatio z p) * x p := rfl

@[simp] theorem resonanceProj_apply (x : lp (fun _ : J × J => ℂ) 2) (p : J × J) :
    resonanceProj z x p = resonanceInd z p * x p := rfl

@[simp] theorem phaseResolvent_apply {c : ℝ} (hc : PhaseSeparated z c)
    (x : lp (fun _ : J × J => ℂ) 2) (p : J × J) :
    phaseResolvent hc x p = phaseResolventMult z p * x p := rfl

theorem phaseTransgression_eq (hz : ∀ j, ‖z j‖ = 1) :
    phaseTransgression hz = 1 - phaseConj hz := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun p => ?_)
  simp [sub_mul]

/-- The kernel of the transgression on a single coordinate. -/
theorem resonanceInd_mul_one_sub (hz : ∀ j, ‖z j‖ = 1) (p : J × J) :
    resonanceInd z p * (1 - phaseRatio z p) = 0 := by
  unfold resonanceInd
  split_ifs with h
  · rw [(one_sub_phaseRatio_eq_zero_iff hz p).mpr h, mul_zero]
  · rw [zero_mul]

theorem resonanceProj_comp_phaseTransgression (hz : ∀ j, ‖z j‖ = 1) :
    resonanceProj z ∘L phaseTransgression hz = 0 := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun p => ?_)
  simp only [ContinuousLinearMap.comp_apply, resonanceProj_apply, phaseTransgression_apply,
    ← mul_assoc, resonanceInd_mul_one_sub hz, zero_mul, zero_apply,
    lp.coeFn_zero, Pi.zero_apply]

theorem resonanceProj_idem : resonanceProj z ∘L resonanceProj z = resonanceProj z := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun p => ?_)
  simp only [ContinuousLinearMap.comp_apply, resonanceProj_apply, ← mul_assoc]
  unfold resonanceInd
  split_ifs <;> simp

/-- Membership in the kernel of `Π_U`: vanishing on resonant entries. -/
theorem mem_ker_resonanceProj_iff (x : lp (fun _ : J × J => ℂ) 2) :
    x ∈ LinearMap.ker (resonanceProj z : KernelSpace J →ₗ[ℂ] KernelSpace J) ↔
      ∀ p : J × J, z p.1 = z p.2 → x p = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h p hp
    have := congrArg (fun y : lp (fun _ : J × J => ℂ) 2 => y p) h
    simpa [resonanceInd, hp] using this
  · intro h
    refine lp.ext (funext fun p => ?_)
    show resonanceInd z p * x p = 0
    unfold resonanceInd
    split_ifs with hp
    · rw [h p hp, mul_zero]
    · rw [zero_mul]

/-- Membership in the kernel of `δ_U`: vanishing on oscillatory entries. -/
theorem mem_ker_phaseTransgression_iff (hz : ∀ j, ‖z j‖ = 1) (x : lp (fun _ : J × J => ℂ) 2) :
    x ∈ LinearMap.ker (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J) ↔
      ∀ p : J × J, z p.1 ≠ z p.2 → x p = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h p hp
    have := congrArg (fun y : lp (fun _ : J × J => ℂ) 2 => y p) h
    simp only [lp.coeFn_zero, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left fun h0 =>
      hp ((one_sub_phaseRatio_eq_zero_iff hz p).mp h0)
  · intro h
    refine lp.ext (funext fun p => ?_)
    show (1 - phaseRatio z p) * x p = 0
    by_cases hp : z p.1 = z p.2
    · rw [(one_sub_phaseRatio_eq_zero_iff hz p).mpr hp, zero_mul]
    · rw [h p hp, mul_zero]

/-- **Theorem 4.1.**  The fixed space of the transgression is the range of the resonance
projection: `ker δ_U = ran Π_U`. -/
theorem ker_phaseTransgression_eq_range (hz : ∀ j, ‖z j‖ = 1) :
    LinearMap.ker (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J) =
      LinearMap.range (resonanceProj z : KernelSpace J →ₗ[ℂ] KernelSpace J) := by
  ext x
  rw [mem_ker_phaseTransgression_iff hz]
  constructor
  · intro h
    refine ⟨x, lp.ext (funext fun p => ?_)⟩
    show resonanceInd z p * x p = x p
    unfold resonanceInd
    split_ifs with hp
    · rw [one_mul]
    · rw [h p hp, mul_zero]
  · rintro ⟨y, rfl⟩ p hp
    show resonanceInd z p * y p = 0
    simp [resonanceInd, hp]

/-- **Theorem 4.1.**  The resonant and oscillatory ranges are orthogonal for the
Hilbert–Schmidt inner product. -/
theorem inner_resonanceProj_phaseTransgression (hz : ∀ j, ‖z j‖ = 1)
    (x y : lp (fun _ : J × J => ℂ) 2) :
    ⟪resonanceProj z x, phaseTransgression hz y⟫_ℂ = 0 := by
  rw [lp.inner_eq_tsum]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  rw [resonanceProj_apply, phaseTransgression_apply, RCLike.inner_apply]
  unfold resonanceInd
  split_ifs with hp
  · rw [(one_sub_phaseRatio_eq_zero_iff hz p).mpr hp]
    simp
  · simp

/-- `ker Π_U` is the orthogonal complement of `ran Π_U`. -/
theorem ker_resonanceProj_eq_orthogonal :
    LinearMap.ker (resonanceProj z : KernelSpace J →ₗ[ℂ] KernelSpace J) =
      (LinearMap.range (resonanceProj z : KernelSpace J →ₗ[ℂ] KernelSpace J))ᗮ := by
  classical
  ext x
  rw [mem_ker_resonanceProj_iff, Submodule.mem_orthogonal]
  constructor
  · rintro h _ ⟨y, rfl⟩
    rw [lp.inner_eq_tsum]
    refine (tsum_congr fun p => ?_).trans tsum_zero
    show ⟪resonanceInd z p * (y : J × J → ℂ) p, (x : J × J → ℂ) p⟫_ℂ = 0
    unfold resonanceInd
    split_ifs with hp
    · simp [h p hp]
    · simp
  · intro h p hp
    have h1 := h (resonanceProj z (lp.single 2 p 1)) ⟨_, rfl⟩
    rw [lp.inner_eq_tsum, tsum_eq_single p] at h1
    · simpa [resonanceInd, hp] using h1
    · intro q hq
      simp [lp.single_apply, hq]

/-- **Theorem 4.1, `(CTR.7)`.**  Under phase separation every kernel splits canonically into its
resonant survivor and an exact oscillatory coboundary: `X = Π_U X + δ_U G_U X`. -/
theorem resonance_add_transgression_resolvent (hz : ∀ j, ‖z j‖ = 1) {c : ℝ}
    (hc : PhaseSeparated z c) (x : lp (fun _ : J × J => ℂ) 2) :
    resonanceProj z x + phaseTransgression hz (phaseResolvent hc x) = x := by
  refine lp.ext (funext fun p => ?_)
  show resonanceInd z p * x p + (1 - phaseRatio z p) * (phaseResolventMult z p * x p) = x p
  unfold resonanceInd phaseResolventMult
  split_ifs with hp
  · simp
  · rw [zero_mul, zero_add, ← mul_assoc, mul_inv_cancel₀
      (fun h0 => hp ((one_sub_phaseRatio_eq_zero_iff hz p).mp h0)), one_mul]

/-- **Theorem 4.1.**  Under phase separation `ran δ_U = ker Π_U`. -/
theorem range_phaseTransgression_eq_ker (hz : ∀ j, ‖z j‖ = 1) {c : ℝ}
    (hc : PhaseSeparated z c) :
    LinearMap.range (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J) =
      LinearMap.ker (resonanceProj z : KernelSpace J →ₗ[ℂ] KernelSpace J) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun T : _ →L[ℂ] _ => T y) (resonanceProj_comp_phaseTransgression hz)
  · refine ⟨phaseResolvent hc x, ?_⟩
    have h := resonance_add_transgression_resolvent hz hc x
    have hx' : resonanceProj z x = 0 := hx
    rw [hx', zero_add] at h
    exact h

/-- **Theorem 4.1, `(CTR.6)`.**  `End(E) = ran Π_U ⊕ ran δ_U`, an orthogonal direct sum. -/
theorem range_phaseTransgression_eq_orthogonal (hz : ∀ j, ‖z j‖ = 1) {c : ℝ}
    (hc : PhaseSeparated z c) :
    LinearMap.range (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J) =
      (LinearMap.range (resonanceProj z : KernelSpace J →ₗ[ℂ] KernelSpace J))ᗮ := by
  rw [range_phaseTransgression_eq_ker hz hc, ker_resonanceProj_eq_orthogonal]

/-- **`(CTR.9)`.**  With at least one oscillatory entry and a positive gap, the oscillatory
inverse has norm exactly `g(U)⁻¹`. -/
theorem norm_phaseResolvent (hz : ∀ j, ‖z j‖ = 1) {c : ℝ} (hc : PhaseSeparated z c)
    (hne : ∃ p : J × J, z p.1 ≠ z p.2) (hg : 0 < transgressionGap z) :
    ‖phaseResolvent hc‖ = (transgressionGap z)⁻¹ := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  have hgsep : PhaseSeparated z (transgressionGap z) :=
    ⟨hg, fun p hp => transgressionGap_le hp⟩
  have hval : ∀ p : J × J, z p.1 ≠ z p.2 →
      ‖(1 - phaseRatio z p)⁻¹‖ ≤ ‖phaseResolvent hc‖ := by
    intro p hp
    have h := (phaseResolvent hc).le_opNorm (lp.single 2 p 1)
    rw [lp.norm_single (by norm_num), norm_one, mul_one] at h
    refine le_trans ?_ h
    have := lp.norm_apply_le_norm (E := fun _ : J × J => ℂ) (p := 2) (by norm_num)
      (phaseResolvent hc (lp.single 2 p 1)) p
    refine le_trans (le_of_eq ?_) this
    simp [phaseResolventMult, hp]
  have hpos : 0 < ‖phaseResolvent hc‖ := by
    refine lt_of_lt_of_le ?_ (hval p₀ hp₀)
    rw [norm_inv]
    exact inv_pos.mpr (norm_pos_iff.mpr fun h0 =>
      hp₀ ((one_sub_phaseRatio_eq_zero_iff hz p₀).mp h0))
  refine le_antisymm ?_ ?_
  · -- the multiplier bound with the optimal constant `g`
    have h := norm_lpDiagonalCLM_le (phaseResolventMult z) (inv_nonneg.mpr hg.le)
      (norm_phaseResolventMult_le hgsep)
    exact h
  · rw [inv_le_comm₀ hg hpos]
    refine le_csInf ⟨_, p₀, hp₀, rfl⟩ ?_
    rintro _ ⟨p, hp, rfl⟩
    have h := hval p hp
    rw [norm_inv] at h
    have hp' : 0 < ‖1 - phaseRatio z p‖ :=
      norm_pos_iff.mpr fun h0 => hp ((one_sub_phaseRatio_eq_zero_iff hz p).mp h0)
    rwa [inv_le_comm₀ hp' hpos] at h

end Operators

/-! ### Closure of the transgression range and properness -/

section Properness

variable {z : J → ℂ}

/-- **Theorem 6.1 (1).**  `closure (ran δ_U) = ker Π_U`. -/
theorem closure_range_phaseTransgression (hz : ∀ j, ‖z j‖ = 1) :
    (LinearMap.range
      (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J)).topologicalClosure =
      LinearMap.ker (resonanceProj z : KernelSpace J →ₗ[ℂ] KernelSpace J) := by
  classical
  refine le_antisymm ?_ ?_
  · refine Submodule.topologicalClosure_minimal _ ?_ (resonanceProj z).isClosed_ker
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun T : _ →L[ℂ] _ => T y) (resonanceProj_comp_phaseTransgression hz)
  · rw [← Submodule.orthogonal_orthogonal_eq_closure]
    intro x hx
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hy0 : ∀ p : J × J, z p.1 ≠ z p.2 → y p = 0 := by
      intro p hp
      have h := (Submodule.mem_orthogonal _ _).mp hy (phaseTransgression hz (lp.single 2 p 1))
        ⟨_, rfl⟩
      rw [lp.inner_eq_tsum, tsum_eq_single p] at h
      · simp only [phaseTransgression_apply, lp.single_apply, Pi.single_eq_same, mul_one,
          RCLike.inner_apply] at h
        rcases mul_eq_zero.mp h with h1 | h1
        · exact h1
        · exact absurd ((map_eq_zero _).mp h1) fun h0 =>
            hp ((one_sub_phaseRatio_eq_zero_iff hz p).mp h0)
      · intro q hq
        simp [lp.single_apply, hq]
    have hx0 := (mem_ker_resonanceProj_iff x).mp hx
    rw [lp.inner_eq_tsum]
    refine (tsum_congr fun p => ?_).trans tsum_zero
    rw [RCLike.inner_apply]
    by_cases hp : z p.1 = z p.2
    · simp [hx0 p hp]
    · simp [hy0 p hp]

theorem mem_ker_phaseTransgression_orthogonal (hz : ∀ j, ‖z j‖ = 1)
    {x : lp (fun _ : J × J => ℂ) 2}
    (hx : x ∈ (LinearMap.ker (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J))ᗮ)
    (p : J × J)
    (hp : z p.1 = z p.2) : x p = 0 := by
  classical
  have hsingle : (lp.single 2 p 1 : lp (fun _ : J × J => ℂ) 2) ∈
      LinearMap.ker (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J) := by
    rw [mem_ker_phaseTransgression_iff hz]
    intro q hq
    simp only [lp.single_apply, Pi.single_apply]
    rw [if_neg]
    rintro rfl
    exact hq hp
  have h := (Submodule.mem_orthogonal _ _).mp hx _ hsingle
  rw [lp.inner_eq_tsum, tsum_eq_single p] at h
  · simpa using h
  · intro q hq
    simp [lp.single_apply, hq]

/-- **Theorem 6.1 (2), `(CTR.17)`.**  The transgression has closed range exactly when the
distinct phases are uniformly separated. -/
theorem isClosed_range_phaseTransgression_iff (hz : ∀ j, ‖z j‖ = 1) :
    IsClosed (Set.range (phaseTransgression hz)) ↔ ∃ c, PhaseSeparated z c := by
  classical
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
  constructor
  · rintro ⟨c, hc, hbound⟩
    refine ⟨c, hc, fun p hp => ?_⟩
    have hmem : (lp.single 2 p 1 : lp (fun _ : J × J => ℂ) 2) ∈
        (LinearMap.ker (phaseTransgression hz : KernelSpace J →ₗ[ℂ] KernelSpace J))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [lp.inner_eq_tsum, tsum_eq_single p]
      · simp [(mem_ker_phaseTransgression_iff hz u).mp hu p hp]
      · intro q hq
        simp [lp.single_apply, hq]
    have h := hbound _ hmem
    rw [lp.norm_single (by norm_num), norm_one, mul_one] at h
    refine h.trans (le_of_eq ?_)
    have : phaseTransgression hz (lp.single 2 p 1) = lp.single 2 p (1 - phaseRatio z p) := by
      refine lp.ext (funext fun q => ?_)
      simp only [phaseTransgression_apply, lp.single_apply, Pi.single_apply]
      split_ifs with hq
      · subst hq
        rw [mul_one]
      · rw [mul_zero]
    rw [this, lp.norm_single (by norm_num)]
  · rintro ⟨c, hc, hsep⟩
    refine ⟨c, hc, fun x hx => ?_⟩
    have hx0 := mem_ker_phaseTransgression_orthogonal hz hx
    have h1 := HilbertSchmidt.lp_norm_sq_eq x
    have h2 := HilbertSchmidt.lp_norm_sq_eq (phaseTransgression hz x)
    have hsq : (c * ‖x‖) ^ 2 ≤ ‖phaseTransgression hz x‖ ^ 2 := by
      rw [mul_pow, h1, h2, ← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun p => ?_)
        ((HilbertSchmidt.summable_coe_sq x).mul_left _)
        (HilbertSchmidt.summable_coe_sq _)
      rw [phaseTransgression_apply, norm_mul, mul_pow]
      by_cases hp : z p.1 = z p.2
      · rw [hx0 p hp]
        simp
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le (hsep p hp) 2)
          (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq

/-- Two distinct points of an infinite subset of the unit circle can be found arbitrarily
close together. -/
theorem exists_ne_norm_sub_lt_of_infinite {S : Set ℂ} (hS : S.Infinite)
    (hS1 : ∀ w ∈ S, ‖w‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ‖a - b‖ < ε := by
  have hsub : S ⊆ Metric.sphere (0 : ℂ) 1 := fun w hw => by
    rw [mem_sphere_zero_iff_norm]
    exact hS1 w hw
  obtain ⟨w, -, hacc⟩ := hS.exists_accPt_of_subset_isCompact (isCompact_sphere 0 1) hsub
  rw [accPt_iff_nhds] at hacc
  obtain ⟨a, ⟨haB, haS⟩, haw⟩ :=
    hacc (Metric.ball w (ε / 2)) (Metric.ball_mem_nhds w (by positivity))
  have hda : 0 < dist a w := dist_pos.mpr haw
  obtain ⟨b, ⟨hbB, hbS⟩, hbw⟩ := hacc (Metric.ball w (dist a w)) (Metric.ball_mem_nhds w hda)
  refine ⟨a, haS, b, hbS, ?_, ?_⟩
  · rintro rfl
    rw [Metric.mem_ball] at hbB
    exact lt_irrefl _ hbB
  · rw [Metric.mem_ball] at haB hbB
    calc ‖a - b‖ = dist a b := (dist_eq_norm a b).symm
      _ ≤ dist a w + dist b w := dist_triangle_right a b w
      _ < ε / 2 + ε / 2 := add_lt_add haB (hbB.trans haB)
      _ = ε := add_halves ε

/-- **Theorem 6.1 (3).**  Unit phases are uniformly separated exactly when only finitely many
distinct phases occur. -/
theorem exists_phaseSeparated_iff_finite (hz : ∀ j, ‖z j‖ = 1) :
    (∃ c, PhaseSeparated z c) ↔ (Set.range z).Finite := by
  constructor
  · rintro ⟨c, hc, hsep⟩
    by_contra hinf
    obtain ⟨a, ⟨j, rfl⟩, b, ⟨k, rfl⟩, hab, hlt⟩ :=
      exists_ne_norm_sub_lt_of_infinite hinf (by rintro _ ⟨j, rfl⟩; exact hz j) hc
    have h := hsep (j, k) hab
    rw [norm_one_sub_phaseRatio hz] at h
    exact absurd hlt (not_lt.mpr h)
  · intro hfin
    classical
    set T : Finset ℝ := ((hfin.toFinset ×ˢ hfin.toFinset).filter fun q => q.1 ≠ q.2).image
      fun q => ‖q.1 - q.2‖
    by_cases hT : T.Nonempty
    · refine ⟨T.min' hT, ?_, fun p hp => ?_⟩
      · obtain ⟨r, hr, hreq⟩ := Finset.mem_image.mp (T.min'_mem hT)
        rw [← hreq]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hr).2)
      · rw [norm_one_sub_phaseRatio hz]
        refine T.min'_le _ (Finset.mem_image.mpr ⟨(z p.1, z p.2), ?_, rfl⟩)
        simp [Finset.mem_filter, hp]
    · refine ⟨1, one_pos, fun p hp => absurd ?_ hT⟩
      exact ⟨_, Finset.mem_image.mpr ⟨(z p.1, z p.2), by simp [Finset.mem_filter, hp], rfl⟩⟩

/-- **Theorem 6.1 (2)–(3).**  The transgression has closed range exactly when only finitely many
distinct phases occur. -/
theorem isClosed_range_phaseTransgression_iff_finite (hz : ∀ j, ‖z j‖ = 1) :
    IsClosed (Set.range (phaseTransgression hz)) ↔ (Set.range z).Finite := by
  rw [isClosed_range_phaseTransgression_iff, exists_phaseSeparated_iff_finite hz]

/-- A finite phase packet is uniformly separated. -/
theorem exists_phaseSeparated_of_finite [Finite J] (hz : ∀ j, ‖z j‖ = 1) :
    ∃ c, PhaseSeparated z c :=
  (exists_phaseSeparated_iff_finite hz).mpr (Set.finite_range z)

/-- **Theorem 6.1 (4).**  With infinitely many distinct phases, every finite aperture is
exactly invertible on its oscillatory sector, but the aperture gaps are not bounded below: for
every `M` some two-point aperture has inverse norm `g⁻¹ > M`. -/
theorem exists_aperture_transgressionGap_inv_gt (hz : ∀ j, ‖z j‖ = 1) (hinf : (Set.range z).Infinite)
    (M : ℝ) :
    ∃ F : Finset J, (∃ p : F × F, z p.1 ≠ z p.2) ∧ 0 < transgressionGap (fun j : F => z j) ∧
      M < (transgressionGap (fun j : F => z j))⁻¹ := by
  classical
  obtain ⟨a, ⟨j, rfl⟩, b, ⟨k, rfl⟩, hab, hlt⟩ :=
    exists_ne_norm_sub_lt_of_infinite hinf (by rintro _ ⟨j, rfl⟩; exact hz j)
      (by positivity : (0 : ℝ) < 1 / (|M| + 1))
  set F : Finset J := {j, k}
  have hjF : j ∈ F := by simp [F]
  have hkF : k ∈ F := by simp [F]
  have hzF : ∀ i : F, ‖z i‖ = 1 := fun i => hz i
  obtain ⟨c, hc⟩ := exists_phaseSeparated_of_finite (J := F) hzF
  have hpair : z (⟨j, hjF⟩ : F) ≠ z (⟨k, hkF⟩ : F) := hab
  have hgpos : 0 < transgressionGap (fun i : F => z i) :=
    lt_of_lt_of_le hc.1 (le_csInf ⟨_, (⟨j, hjF⟩, ⟨k, hkF⟩), hpair, rfl⟩
      (by rintro _ ⟨p, hp, rfl⟩; exact hc.2 p hp))
  have hgle : transgressionGap (fun i : F => z i) < 1 / (|M| + 1) := by
    refine lt_of_le_of_lt (transgressionGap_le (p := (⟨j, hjF⟩, ⟨k, hkF⟩)) hpair) ?_
    rw [norm_one_sub_phaseRatio hzF]
    exact hlt
  refine ⟨F, ⟨(⟨j, hjF⟩, ⟨k, hkF⟩), hpair⟩, hgpos, ?_⟩
  have h1 : M < |M| + 1 := by linarith [le_abs_self M]
  calc M < |M| + 1 := h1
    _ < (transgressionGap (fun i : F => z i))⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hgpos, ← one_div]
      exact hgle

end Properness

/-! ### Cesàro formation -/

section Cesaro

variable {z : J → ℂ}

theorem phaseConj_pow_apply (hz : ∀ j, ‖z j‖ = 1) (n : ℕ) (x : KernelSpace J) (p : J × J) :
    ((phaseConj hz ^ n) x : J × J → ℂ) p = phaseRatio z p ^ n * x p := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih,
        phaseConj_apply, pow_succ]
      ring

/-- The Cesàro coefficient `N⁻¹ ∑_{n<N} rⁿ`. -/
def cesaroCoeff (r : ℂ) (N : ℕ) : ℂ := (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, r ^ n

/-- The Cesàro formation `M_N = N⁻¹ ∑_{n<N} αⁿ`. -/
def phaseCesaro (hz : ∀ j, ‖z j‖ = 1) (N : ℕ) : KernelSpace J →L[ℂ] KernelSpace J :=
  (N : ℂ)⁻¹ • ∑ n ∈ Finset.range N, phaseConj hz ^ n

theorem phaseCesaro_apply (hz : ∀ j, ‖z j‖ = 1) (N : ℕ) (x : KernelSpace J) (p : J × J) :
    (phaseCesaro hz N x : J × J → ℂ) p = cesaroCoeff (phaseRatio z p) N * x p := by
  rw [phaseCesaro, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    sum_apply, lp.coeFn_sum, Finset.sum_apply, cesaroCoeff, smul_eq_mul, mul_assoc,
    Finset.sum_mul]
  simp_rw [phaseConj_pow_apply hz]

theorem norm_cesaroCoeff_le {r : ℂ} (hr : ‖r‖ = 1) (N : ℕ) : ‖cesaroCoeff r N‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaroCoeff]
  rw [cesaroCoeff, norm_mul, norm_inv, Complex.norm_natCast]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [inv_mul_le_iff₀ hNpos, mul_one]
  calc ‖∑ n ∈ Finset.range N, r ^ n‖ ≤ ∑ n ∈ Finset.range N, ‖r ^ n‖ := norm_sum_le _ _
    _ = N := by simp [hr]

theorem tendsto_cesaroCoeff {r : ℂ} (hr : ‖r‖ = 1) :
    Tendsto (cesaroCoeff r) atTop (𝓝 (if r = 1 then 1 else 0)) := by
  split_ifs with h1
  · subst h1
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun N hN => ?_⟩)
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp [cesaroCoeff, hN0]
  · have h2 : 0 < ‖1 - r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h1))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ N : ℕ, ‖cesaroCoeff r N‖ ≤ 2 / ‖1 - r‖ * (N : ℝ)⁻¹ := by
      intro N
      rw [cesaroCoeff, norm_mul, norm_inv, Complex.norm_natCast, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Nat.cast_nonneg N))
      rw [geom_sum_eq h1, norm_div, ← norm_neg (r - 1), neg_sub]
      refine div_le_div_of_nonneg_right ?_ h2.le
      calc ‖r ^ N - 1‖ ≤ ‖r ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hr, one_pow, norm_one]; norm_num
    refine squeeze_zero (fun N => norm_nonneg _) hbound ?_
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 / ‖1 - r‖)

theorem tendsto_cesaroCoeff_phaseRatio (hz : ∀ j, ‖z j‖ = 1) (p : J × J) :
    Tendsto (cesaroCoeff (phaseRatio z p)) atTop (𝓝 (resonanceInd z p)) := by
  have h := tendsto_cesaroCoeff (norm_phaseRatio hz p)
  simp only [phaseRatio_eq_one_iff hz] at h
  exact h

/-- **Corollary 4.2, `(CTR.10)`.**  The Cesàro formation converges to the resonance projection:
`N⁻¹ ∑_{n<N} αⁿ(X) → Π_U X` in the Hilbert–Schmidt norm. -/
theorem tendsto_phaseCesaro (hz : ∀ j, ‖z j‖ = 1) (x : KernelSpace J) :
    Tendsto (fun N => phaseCesaro hz N x) atTop (𝓝 (resonanceProj z x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun N => ‖phaseCesaro hz N x - resonanceProj z x‖ ^ 2) atTop (𝓝 0) := by
    have hcoord : ∀ N p, ((phaseCesaro hz N x - resonanceProj z x : KernelSpace J) :
        J × J → ℂ) p = (cesaroCoeff (phaseRatio z p) N - resonanceInd z p) * x p := by
      intro N p
      rw [lp.coeFn_sub, Pi.sub_apply, phaseCesaro_apply, resonanceProj_apply, sub_mul]
    simp_rw [HilbertSchmidt.lp_norm_sq_eq, hcoord]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun N p => ‖(cesaroCoeff (phaseRatio z p) N - resonanceInd z p) * x p‖ ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun p => 4 * ‖(x : J × J → ℂ) p‖ ^ 2)
      ((HilbertSchmidt.summable_coe_sq x).mul_left 4) (fun p => ?_) ?_
    · simpa using h
    · have hc := tendsto_cesaroCoeff_phaseRatio hz p
      have : Tendsto (fun N => ‖(cesaroCoeff (phaseRatio z p) N - resonanceInd z p) * x p‖ ^ 2)
          atTop (𝓝 (‖(resonanceInd z p - resonanceInd z p) * x p‖ ^ 2)) :=
        (((hc.sub_const _).mul_const _).norm).pow 2
      simpa using this
    · refine Eventually.of_forall fun N p => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hle : ‖cesaroCoeff (phaseRatio z p) N - resonanceInd z p‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by
          linarith [norm_cesaroCoeff_le (norm_phaseRatio hz p) N,
            norm_resonanceInd_le (z := z) p])
      have : ‖cesaroCoeff (phaseRatio z p) N - resonanceInd z p‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (cesaroCoeff (phaseRatio z p) N - resonanceInd z p)]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero] at this
  refine this.congr fun N => ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (norm_nonneg _)

end Cesaro

/-! ### Conjugation by a diagonal unitary -/

section Bridge

variable {z : J → ℂ}

/-- The diagonal unitary `U eⱼ = zⱼ eⱼ` on `ℓ²(J)`. -/
def phaseUnitary (hz : ∀ j, ‖z j‖ = 1) : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2 :=
  lpDiagonalCLM z zero_le_one fun j => (hz j).le

theorem adjoint_phaseUnitary (hz : ∀ j, ‖z j‖ = 1) :
    ContinuousLinearMap.adjoint (phaseUnitary hz) =
      lpDiagonalCLM (fun j => conj (z j)) zero_le_one fun j => by
        rw [Complex.norm_conj, hz] := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  rw [lpDiagonalCLM_inner (fun j => conj (z j)) zero_le_one _ zero_le_one
    (fun j => by rw [Complex.norm_conj, Complex.norm_conj, hz])]
  congr 1
  refine lp.ext (funext fun j => ?_)
  simp [phaseUnitary]

/-- **`(CTR.4)` on operators.**  Conjugation `α(T) = U* T U` multiplies the matrix of `T` by the
phase ratios: `α(T)_{jk} = z̄ⱼ z_k T_{jk}`. -/
theorem matrixOf_adjoint_comp_comp [DecidableEq J] (hz : ∀ j, ‖z j‖ = 1)
    (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2) (p : J × J) :
    HilbertSchmidt.matrixOf (ContinuousLinearMap.adjoint (phaseUnitary hz) ∘L T ∘L
      phaseUnitary hz) p = phaseRatio z p * HilbertSchmidt.matrixOf T p := by
  simp only [HilbertSchmidt.matrixOf, ContinuousLinearMap.comp_apply, adjoint_phaseUnitary]
  rw [show phaseUnitary hz (lp.single 2 p.2 (1 : ℂ)) = z p.2 • lp.single 2 p.2 (1 : ℂ) by
    rw [phaseUnitary, lpDiagonalCLM_single, ← lp.single_smul, smul_eq_mul, mul_one], map_smul,
    lpDiagonalCLM_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, phaseRatio]
  ring

end Bridge

/-! ### Functional-equation reflection -/

section Reflection

variable {z : J → ℂ}

theorem phaseRatio_conj (p : J × J) :
    phaseRatio (fun j => conj (z j)) p = conj (phaseRatio z p) := by
  simp [phaseRatio, mul_comm]

/-- Reflection `z ↦ z̄` preserves the resonance partition. -/
theorem resonanceInd_conj : resonanceInd (fun j => conj (z j)) = resonanceInd z := by
  funext p
  simp only [resonanceInd, (RingHom.injective (starRingEnd ℂ)).eq_iff]

theorem resonanceProj_conj : resonanceProj (fun j => conj (z j)) = resonanceProj z := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun p => ?_)
  rw [resonanceProj_apply, resonanceProj_apply, resonanceInd_conj]

/-- Reflection preserves every transgression multiplier modulus. -/
theorem norm_one_sub_phaseRatio_conj (p : J × J) :
    ‖1 - phaseRatio (fun j => conj (z j)) p‖ = ‖1 - phaseRatio z p‖ := by
  rw [phaseRatio_conj, show (1 : ℂ) - conj (phaseRatio z p) = conj (1 - phaseRatio z p) by
    simp, Complex.norm_conj]

theorem phaseSeparated_conj_iff {c : ℝ} :
    PhaseSeparated (fun j => conj (z j)) c ↔ PhaseSeparated z c := by
  simp only [PhaseSeparated, norm_one_sub_phaseRatio_conj,
    (RingHom.injective (starRingEnd ℂ)).ne_iff]

/-- Reflection preserves the small-divisor gap. -/
theorem transgressionGap_conj : transgressionGap (fun j => conj (z j)) = transgressionGap z := by
  simp only [transgressionGap, norm_one_sub_phaseRatio_conj,
    (RingHom.injective (starRingEnd ℂ)).ne_iff]

/-- Reflection preserves closed-range status of the transgression. -/
theorem isClosed_range_phaseTransgression_conj_iff (hz : ∀ j, ‖z j‖ = 1) :
    IsClosed (Set.range (phaseTransgression (z := fun j => conj (z j))
        fun j => by rw [Complex.norm_conj, hz])) ↔
      IsClosed (Set.range (phaseTransgression hz)) := by
  rw [isClosed_range_phaseTransgression_iff, isClosed_range_phaseTransgression_iff]
  simp only [phaseSeparated_conj_iff]

end Reflection

end GaloisForLFunctions.HTGeometry
