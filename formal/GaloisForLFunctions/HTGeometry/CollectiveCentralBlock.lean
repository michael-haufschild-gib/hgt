import GaloisForLFunctions.HTGeometry.TwirlSeparationHouseholder
import GaloisForLFunctions.HTGeometry.ReplicaMomentPurity

/-!
# The collective commutant: block structure and constancy of the replica quadratic form

An operator commuting with every replica power of a unitary is block diagonal for the content
classes: a diagonal unitary whose only nontrivial entry is a primitive root of unity of order
`r + 1` separates two coordinates whose contents differ in that letter, because the two diagonal
eigenvalues are distinct powers of the root below its order.

The replica quadratic form of such an operator is constant on unit vectors.  Every unit vector is a
diagonal phase times a non-negative unit vector, and a Householder reflection carries a basis vector
to the latter, so the whole unit sphere is one unitary orbit; conjugating by a collective unitary
leaves the quadratic form unchanged.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Central

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The collective commutant.**  Operators commuting with every replica power of a unitary. -/
def IsCollectiveCentral (r : ℕ) (Z : Matrix (Fin r → α) (Fin r → α) ℂ) : Prop :=
  ∀ U : Matrix α α ℂ, Uᴴ * U = 1 →
    replicaTensorPowerMatrix r U * Z = Z * replicaTensorPowerMatrix r U

theorem isCollectiveCentral_symReplicaProjection (r : ℕ) :
    IsCollectiveCentral r (symReplicaProjection (α := α) r) :=
  fun U _ => (symReplicaProjection_commute r U).symm

theorem replicaTensorPower_diagonal (r : ℕ) (d : α → ℂ) (z w : Fin r → α) :
    replicaTensorPowerMatrix r (Matrix.diagonal d) z w
      = if z = w then ∏ i, d (z i) else 0 := by
  rw [replicaTensorPowerMatrix]
  simp only [Matrix.of_apply, Matrix.diagonal_apply]
  by_cases h : z = w
  · subst h
    rw [if_pos rfl]
    exact Finset.prod_congr rfl fun i _ => if_pos rfl
  · rw [if_neg h]
    have hne : ∃ i, z i ≠ w i := by
      by_contra hc
      refine h (funext fun i => ?_)
      by_contra hi
      exact hc ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem prod_ite_eq_pow_card (r : ℕ) (omega : ℂ) (b : α) (z : Fin r → α) :
    (∏ i, if z i = b then omega else 1)
      = omega ^ (Fintype.card {i : Fin r // z i = b}) := by
  classical
  rw [Finset.prod_ite (fun _ : Fin r => omega) (fun _ : Fin r => (1 : ℂ)),
    Finset.prod_const, Finset.prod_const_one, mul_one, Fintype.card_subtype]

/-- **Block structure.**  A collectively central operator vanishes off the content classes. -/
theorem eq_zero_of_isCollectiveCentral (r : ℕ) {Z : Matrix (Fin r → α) (Fin r → α) ℂ}
    (hZ : IsCollectiveCentral r Z) {x y : Fin r → α}
    (hxy : symTupleIndex r x ≠ symTupleIndex r y) : Z x y = 0 := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : α, Fintype.card {i : Fin r // x i = b}
      ≠ Fintype.card {i : Fin r // y i = b} := by
    by_contra hc
    refine hxy ((symTupleIndex_eq_iff_card r x y).mpr fun a => ?_)
    by_contra hne
    exact hc ⟨a, hne⟩
  set omega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((r + 1 : ℕ) : ℂ)) with homega
  have hprim : IsPrimitiveRoot omega (r + 1) :=
    Complex.isPrimitiveRoot_exp (r + 1) (Nat.succ_ne_zero r)
  have hnorm : ‖omega‖ = 1 := by
    have h1 : ‖omega‖ ^ (r + 1) = 1 := by
      rw [← norm_pow, hprim.pow_eq_one, norm_one]
    have h2 : (0 : ℝ) ≤ ‖omega‖ := norm_nonneg _
    rcases lt_trichotomy ‖omega‖ 1 with h | h | h
    · exact absurd h1 (ne_of_lt (pow_lt_one₀ h2 h (Nat.succ_ne_zero r)))
    · exact h
    · exact absurd h1 (ne_of_gt (one_lt_pow₀ h (Nat.succ_ne_zero r)))
  set d : α → ℂ := fun a => if a = b then omega else 1 with hd
  have hdnorm : ∀ a, ‖d a‖ = 1 := by
    intro a
    have hda : d a = if a = b then omega else 1 := rfl
    rw [hda]
    by_cases ha : a = b
    · rw [if_pos ha, hnorm]
    · rw [if_neg ha, norm_one]
  set U : Matrix α α ℂ := Matrix.diagonal d with hU
  have hUunit : Uᴴ * U = 1 := by
    rw [hU, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => star d i * d i) = fun _ : α => (1 : ℂ) from ?_]
    · exact Matrix.diagonal_one
    · funext a
      have hn := hdnorm a
      simp only [Pi.star_apply, RCLike.star_def]
      rw [Complex.conj_mul', hn]
      norm_num
  have hcomm := hZ U hUunit
  have hentry := congrFun (congrFun hcomm x) y
  rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
  have hleft : (∑ z : Fin r → α, replicaTensorPowerMatrix r U x z * Z z y)
      = omega ^ (Fintype.card {i : Fin r // x i = b}) * Z x y := by
    have hterm : ∀ z : Fin r → α, replicaTensorPowerMatrix r U x z * Z z y
        = if x = z then omega ^ (Fintype.card {i : Fin r // x i = b}) * Z z y else 0 := by
      intro z
      rw [hU, replicaTensorPower_diagonal]
      by_cases h : x = z
      · subst h
        rw [if_pos rfl, if_pos rfl, hd]
        congr 2
        exact prod_ite_eq_pow_card r omega b x
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl fun z _ => hterm z,
      Finset.sum_ite_eq Finset.univ x
        (fun z => omega ^ (Fintype.card {i : Fin r // x i = b}) * Z z y)]
    simp
  have hright : (∑ z : Fin r → α, Z x z * replicaTensorPowerMatrix r U z y)
      = Z x y * omega ^ (Fintype.card {i : Fin r // y i = b}) := by
    have hterm : ∀ z : Fin r → α, Z x z * replicaTensorPowerMatrix r U z y
        = if z = y then Z x z * omega ^ (Fintype.card {i : Fin r // y i = b}) else 0 := by
      intro z
      rw [hU, replicaTensorPower_diagonal]
      by_cases h : z = y
      · subst h
        rw [if_pos rfl, if_pos rfl, hd]
        congr 2
        exact prod_ite_eq_pow_card r omega b z
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun z _ => hterm z,
      Finset.sum_ite_eq' Finset.univ y
        (fun z => Z x z * omega ^ (Fintype.card {i : Fin r // y i = b}))]
    simp
  rw [hleft, hright] at hentry
  have hltx : Fintype.card {i : Fin r // x i = b} < r + 1 := by
    have := Fintype.card_subtype_le (fun i : Fin r => x i = b)
    simpa using Nat.lt_succ_of_le this
  have hlty : Fintype.card {i : Fin r // y i = b} < r + 1 := by
    have := Fintype.card_subtype_le (fun i : Fin r => y i = b)
    simpa using Nat.lt_succ_of_le this
  have hne : omega ^ (Fintype.card {i : Fin r // x i = b})
      ≠ omega ^ (Fintype.card {i : Fin r // y i = b}) := by
    intro h
    exact hb (hprim.pow_inj hltx hlty h)
  have hfactor : (omega ^ (Fintype.card {i : Fin r // x i = b})
      - omega ^ (Fintype.card {i : Fin r // y i = b})) * Z x y = 0 := by
    rw [sub_mul, hentry]
    ring
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h


theorem replicaTensorPower_conjTranspose_mul (r : ℕ) {A : Matrix α α ℂ} (hA : Aᴴ * A = 1) :
    (replicaTensorPowerMatrix r A)ᴴ * replicaTensorPowerMatrix r A = 1 := by
  rw [replicaTensorPowerMatrix_conjTranspose, ← replicaTensorPowerMatrix_mul, hA,
    replicaTensorPowerMatrix_one]

theorem mulVec_mul_apply {W : Type*} [Fintype W] (A B : Matrix W W ℂ) (v : W → ℂ) (x : W) :
    ((A * B).mulVec v) x = (A.mulVec (B.mulVec v)) x := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring

/-- The replica projector of a one-copy vector. -/
def replicaProjector (r : ℕ) (psi : α → ℂ) : Matrix (Fin r → α) (Fin r → α) ℂ :=
  Matrix.of fun x y => finitePureTensorPower r psi x *
    (starRingEnd ℂ) (finitePureTensorPower r psi y)

theorem replicaProjector_apply (r : ℕ) (psi : α → ℂ) (x y : Fin r → α) :
    replicaProjector r psi x y = finitePureTensorPower r psi x *
      (starRingEnd ℂ) (finitePureTensorPower r psi y) := rfl

/-- A one-copy unitary transports the replica projector by conjugation. -/
theorem replicaProjector_mulVec (r : ℕ) (A : Matrix α α ℂ) (psi : α → ℂ) :
    replicaProjector r (A.mulVec psi)
      = replicaTensorPowerMatrix r A * replicaProjector r psi *
          (replicaTensorPowerMatrix r A)ᴴ := by
  have hpure : ∀ z : Fin r → α, finitePureTensorPower r (A.mulVec psi) z
      = ∑ w : Fin r → α, replicaTensorPowerMatrix r A z w * finitePureTensorPower r psi w := by
    intro z
    have h := congrFun (replicaTensorPowerMatrix_mulVec r A psi) z
    rw [Matrix.mulVec, dotProduct] at h
    exact h.symm
  funext x y
  have hinner : ∀ w : Fin r → α,
      (replicaTensorPowerMatrix r A * replicaProjector r psi) x w *
        (replicaTensorPowerMatrix r A)ᴴ w y
      = (∑ z : Fin r → α, replicaTensorPowerMatrix r A x z * finitePureTensorPower r psi z) *
          ((starRingEnd ℂ) (replicaTensorPowerMatrix r A y w *
            finitePureTensorPower r psi w)) := by
    intro w
    rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.sum_mul,
      RCLike.star_def, map_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [replicaProjector_apply]
    ring
  rw [replicaProjector_apply, hpure x, hpure y, map_sum, Matrix.mul_apply,
    Finset.sum_congr rfl fun w _ => hinner w, ← Finset.mul_sum]

/-- **The replica trace pairing is a unitary invariant.** -/
theorem trace_mul_replicaProjector_mulVec (r : ℕ) {Z : Matrix (Fin r → α) (Fin r → α) ℂ}
    (hZ : IsCollectiveCentral r Z) {A : Matrix α α ℂ} (hA : Aᴴ * A = 1) (psi : α → ℂ) :
    (Z * replicaProjector r (A.mulVec psi)).trace = (Z * replicaProjector r psi).trace := by
  rw [replicaProjector_mulVec]
  have hkey : Z * (replicaTensorPowerMatrix r A * replicaProjector r psi *
      (replicaTensorPowerMatrix r A)ᴴ)
      = (replicaTensorPowerMatrix r A) * (Z * replicaProjector r psi) *
          (replicaTensorPowerMatrix r A)ᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hZ A hA]
    simp [Matrix.mul_assoc]
  rw [hkey, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    replicaTensorPower_conjTranspose_mul r hA, Matrix.one_mul]

theorem exists_unitary_mulVec_basis_of_unit (psi : α → ℂ)
    (hunit : finiteComplexInner psi psi = 1) (a0 : α) :
    ∃ A : Matrix α α ℂ, Aᴴ * A = 1 ∧
      A.mulVec (fun a => if a = a0 then (1 : ℂ) else 0) = psi := by
  classical
  set t : α → ℝ := fun a => ‖psi a‖ with ht
  have htsum : ∑ a, t a ^ (2 : ℕ) = 1 := by
    have hcx : ((∑ a, t a ^ (2 : ℕ) : ℝ) : ℂ) = 1 := by
      rw [← hunit, finiteComplexInner]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ht]
      simpa using (Complex.conj_mul' (psi a)).symm
    exact_mod_cast hcx
  obtain ⟨A, hAunit, hAe⟩ := exists_unitary_mulVec_basis t htsum a0
  set d : α → ℂ := fun a => if psi a = 0 then 1 else psi a / (‖psi a‖ : ℂ) with hd
  have hdnorm : ∀ a, ‖d a‖ = 1 := by
    intro a
    have hda : d a = if psi a = 0 then 1 else psi a / ((‖psi a‖ : ℝ) : ℂ) := rfl
    rw [hda]
    by_cases ha : psi a = 0
    · rw [if_pos ha, norm_one]
    · rw [if_neg ha, norm_div, Complex.norm_real, norm_norm,
        div_self (by simpa using ha)]
  have hDunit : (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => star d i * d i) = fun _ : α => (1 : ℂ) from ?_]
    · exact Matrix.diagonal_one
    · funext a
      have hn := hdnorm a
      simp only [Pi.star_apply, RCLike.star_def]
      rw [Complex.conj_mul', hn]
      norm_num
  have hDt : (Matrix.diagonal d).mulVec (fun a => (t a : ℂ)) = psi := by
    funext a
    rw [Matrix.mulVec_diagonal]
    have hda : d a = if psi a = 0 then 1 else psi a / ((‖psi a‖ : ℝ) : ℂ) := rfl
    have hta : t a = ‖psi a‖ := rfl
    rw [hda, hta]
    by_cases ha : psi a = 0
    · rw [if_pos ha, ha]
      simp
    · rw [if_neg ha]
      have hne : ((‖psi a‖ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
        exact ha
      field_simp
  refine ⟨Matrix.diagonal d * A, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d)ᴴ,
      hDunit, Matrix.one_mul, hAunit]
  · funext a
    rw [mulVec_mul_apply, hAe, hDt]

/-- **Constancy.**  The replica trace pairing of a collectively central operator is the same at
every unit vector. -/
theorem trace_mul_replicaProjector_eq_of_unit (r : ℕ) {Z : Matrix (Fin r → α) (Fin r → α) ℂ}
    (hZ : IsCollectiveCentral r Z) (psi : α → ℂ) (hunit : finiteComplexInner psi psi = 1)
    (a0 : α) :
    (Z * replicaProjector r psi).trace
      = (Z * replicaProjector r (fun a => if a = a0 then (1 : ℂ) else 0)).trace := by
  obtain ⟨A, hAunit, hAe⟩ := exists_unitary_mulVec_basis_of_unit psi hunit a0
  rw [← hAe, trace_mul_replicaProjector_mulVec r hZ hAunit]

end Central

end

end GaloisForLFunctions.HTGeometry
