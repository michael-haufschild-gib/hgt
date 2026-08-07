import Mathlib

/-!
# Replica observer-Jacobian compensation law

Raw reporter-Jacobian pseudodeterminants are not invariant under observer
duplication.  Repeating every output coordinate `k` times multiplies a
rank-`v` Gram determinant by `k^v`, although the underlying capture event is
unchanged.  Dividing by that deterministic factor makes every lower tail
exactly invariant.

The same compensation appears in fidelity replicas: raising every
nonnegative target fidelity and its capture threshold to one common positive
power preserves the complete target union exactly.  These finite identities
show that replica multiplicity alone cannot supply a circuit-union
anti-concentration exponent.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Gram matrix of a real observer Jacobian, with observer outputs as rows and
visible parameter directions as columns. -/
def observerJacobianGram {ι : Type*} [Fintype ι] {v : ℕ}
    (J : ι → Fin v → ℝ) : Matrix (Fin v) (Fin v) ℝ :=
  fun i j => ∑ a, J a i * J a j

/-- Uniformly repeat every observer row `k` times. -/
def replicateObserverJacobian {N v : ℕ} (k : ℕ)
    (J : Fin N → Fin v → ℝ) : Fin k × Fin N → Fin v → ℝ :=
  fun a i => J a.2 i

/-- Uniform observer duplication multiplies the Jacobian Gram by the
replication count. -/
theorem observerJacobianGram_replicate {N v : ℕ} (k : ℕ)
    (J : Fin N → Fin v → ℝ) :
    observerJacobianGram (replicateObserverJacobian k J) =
      (k : ℝ) • observerJacobianGram J := by
  ext i j
  simp only [observerJacobianGram, replicateObserverJacobian,
    Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [Fintype.card_fin]

/-- A rank-`v` raw Gram determinant acquires the entirely artificial factor
`k^v` under `k` identical observer copies. -/
theorem det_observerJacobianGram_replicate {N v : ℕ} (k : ℕ)
    (J : Fin N → Fin v → ℝ) :
    (observerJacobianGram (replicateObserverJacobian k J)).det =
      (k : ℝ) ^ v * (observerJacobianGram J).det := by
  rw [observerJacobianGram_replicate, Matrix.det_smul]
  simp

/-- The determinant normalized by uniform output multiplicity is exactly the
one-copy determinant. -/
theorem normalized_det_observerJacobianGram_replicate {N v : ℕ}
    (k : ℕ) (hk : 0 < k) (J : Fin N → Fin v → ℝ) :
    (observerJacobianGram (replicateObserverJacobian k J)).det /
        (k : ℝ) ^ v =
      (observerJacobianGram J).det := by
  rw [det_observerJacobianGram_replicate]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- Exact normalized lower-tail equivalence, pointwise in the realized
Jacobian. -/
theorem det_observerJacobianGram_replicate_le_scaled_iff {N v : ℕ}
    (k : ℕ) (hk : 0 < k) (J : Fin N → Fin v → ℝ) (τ : ℝ) :
    (observerJacobianGram (replicateObserverJacobian k J)).det ≤
        (k : ℝ) ^ v * τ ↔
      (observerJacobianGram J).det ≤ τ := by
  rw [det_observerJacobianGram_replicate]
  exact mul_le_mul_iff_of_pos_left (by positivity : 0 < (k : ℝ) ^ v)

/-- Under every measure, uniform reporter replication leaves the normalized
Jacobian lower-tail probability unchanged.  No measurability assumption is
needed because the two events are literally the same set. -/
theorem measure_det_observerJacobianGram_replicate_le_scaled
    {X : Type*} [MeasurableSpace X] {N v : ℕ}
    (μ : Measure X) (k : ℕ) (hk : 0 < k)
    (J : X → Fin N → Fin v → ℝ) (τ : ℝ) :
    μ {x |
        (observerJacobianGram (replicateObserverJacobian k (J x))).det ≤
          (k : ℝ) ^ v * τ} =
      μ {x | (observerJacobianGram (J x)).det ≤ τ} := by
  congr 1
  ext x
  exact det_observerJacobianGram_replicate_le_scaled_iff k hk (J x) τ

/-- Raising a nonnegative capture value and threshold to one common positive
replica order neither creates nor removes capture. -/
theorem pow_capture_iff {r : ℕ} (hr : r ≠ 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ r ≤ b ^ r ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb hr

/-- The power compensation holds before an arbitrary target selector. -/
theorem exists_pow_capture_iff
    {X C : Type*} {r : ℕ} (hr : r ≠ 0)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (fidelity : X → C → ℝ)
    (hfidelity : ∀ x c, 0 ≤ fidelity x c) (x : X) :
    (∃ c, threshold ^ r ≤ fidelity x c ^ r) ↔
      ∃ c, threshold ≤ fidelity x c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (pow_capture_iff hr hthreshold (hfidelity x c)).mp hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (pow_capture_iff hr hthreshold (hfidelity x c)).mpr hc⟩

/-- **Complete-union replica compensation.**  For every target class, finite
or infinite, the matched replica-fidelity tube is exactly the original tube.
This requires no selector measurability and no union bound. -/
theorem completeTargetUnion_pow_capture_set_eq
    {X C : Type*} {r : ℕ} (hr : r ≠ 0)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (fidelity : X → C → ℝ)
    (hfidelity : ∀ x c, 0 ≤ fidelity x c) :
    {x | ∃ c, threshold ^ r ≤ fidelity x c ^ r} =
      {x | ∃ c, threshold ≤ fidelity x c} := by
  ext x
  exact exists_pow_capture_iff hr threshold hthreshold fidelity hfidelity x

/-- The probability of the complete matched replica tube is therefore
identical under every law on the source parameters. -/
theorem measure_completeTargetUnion_pow_capture
    {X C : Type*} [MeasurableSpace X] {r : ℕ} (hr : r ≠ 0)
    (μ : Measure X) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (fidelity : X → C → ℝ)
    (hfidelity : ∀ x c, 0 ≤ fidelity x c) :
    μ {x | ∃ c, threshold ^ r ≤ fidelity x c ^ r} =
      μ {x | ∃ c, threshold ≤ fidelity x c} := by
  rw [completeTargetUnion_pow_capture_set_eq hr threshold hthreshold
    fidelity hfidelity]

/-- **Replica observer-Jacobian compensation capstone.**  Uniform output
replication simultaneously (i) multiplies the raw rank-`v` Gram determinant by
`k^v`, (ii) leaves its correctly normalized lower tail unchanged under every
measure, and (iii) leaves every matched complete target tube unchanged. -/
theorem replicaObserverJacobian_compensationLaw
    {X C : Type*} [MeasurableSpace X] {N v : ℕ}
    (μ : Measure X) (k : ℕ) (hk : 0 < k)
    (J : X → Fin N → Fin v → ℝ) (τ threshold : ℝ)
    (hthreshold : 0 ≤ threshold)
    (fidelity : X → C → ℝ)
    (hfidelity : ∀ x c, 0 ≤ fidelity x c) :
    (∀ x,
      (observerJacobianGram
        (replicateObserverJacobian k (J x))).det =
          (k : ℝ) ^ v * (observerJacobianGram (J x)).det) ∧
    μ {x |
        (observerJacobianGram
          (replicateObserverJacobian k (J x))).det ≤
            (k : ℝ) ^ v * τ} =
      μ {x | (observerJacobianGram (J x)).det ≤ τ} ∧
    μ {x | ∃ c, threshold ^ k ≤ fidelity x c ^ k} =
      μ {x | ∃ c, threshold ≤ fidelity x c} := by
  refine ⟨fun x => det_observerJacobianGram_replicate k (J x),
    measure_det_observerJacobianGram_replicate_le_scaled μ k hk J τ, ?_⟩
  exact measure_completeTargetUnion_pow_capture hk.ne' μ threshold hthreshold
    fidelity hfidelity

end

end GaloisForLFunctions.HTGeometry
