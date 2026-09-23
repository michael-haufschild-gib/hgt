import GaloisForLFunctions.HTGeometry.StabilizerCollisionPerBasis

/-!
# The exact two-design collision law of stabilizer states

Averaging the collision of a stabilizer state against an arbitrary family of unit states over all
ordered Lagrangian bases and all sign patterns gives exactly `2/(D+1)`: the sign average leaves the
Pauli diagonals over the span of the basis, every nonzero label lies in one span out of `D+1`, and
Parseval totals the squared Pauli diagonals at a unit state.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

theorem finiteComplexInner_self {α : Type*} [Fintype α] (ψ : α → ℂ) :
    finiteComplexInner ψ ψ = ((∑ x, ‖ψ x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [finiteComplexInner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := Complex.mul_conj (ψ x)
  rw [Complex.sq_norm, ← h]
  ring

theorem card_finiteQubitConfiguration :
    Fintype.card (FiniteQubitConfiguration (Fin n)) = 2 ^ n := by
  simp [FiniteQubitConfiguration]

/-- The stabilizer projector of an arbitrary family, zero off the commuting locus. -/
def stabProjectorOf (b : Fin n → PauliSymp n) (ε : Fin n → ZMod 2) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  if hb : ∀ i j, symForm (b i) (b j) = 0 then stabProjector b hb ε else 0

theorem stabProjectorOf_eq {b : Fin n → PauliSymp n} (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ε : Fin n → ZMod 2) : stabProjectorOf b ε = stabProjector b hb ε := dif_pos hb

section Assembly

variable (e : FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ)

/-- The squared Pauli diagonal in one member of the family. -/
def pauliDiagSq (e : FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ)
    (v : PauliSymp n) (j : FiniteQubitConfiguration (Fin n)) : ℂ :=
  (matDiag (pauliMat v) (e j)) ^ (2 : ℕ)

theorem pauliDiagSq_zero (hunit : ∀ j, (∑ x, ‖e j x‖ ^ (2 : ℕ)) = 1)
    (j : FiniteQubitConfiguration (Fin n)) : pauliDiagSq e 0 j = 1 := by
  rw [pauliDiagSq, pauliMat_zero, matDiag_one, finiteComplexInner_self, hunit j]
  norm_num

theorem sum_pauliDiagSq (hunit : ∀ j, (∑ x, ‖e j x‖ ^ (2 : ℕ)) = 1)
    (j : FiniteQubitConfiguration (Fin n)) :
    (∑ v : PauliSymp n, pauliDiagSq e v j) = (2 : ℂ) ^ n :=
  sum_matDiag_pauliMat_sq (e j) (hunit j)

/-- **The sign-averaged collision of one ordered Lagrangian basis.** -/
theorem sum_sign_collision_of_mem_lagrBases {b : Fin n → PauliSymp n} (hbmem : b ∈ lagrBases n) :
    (∑ ε : Fin n → ZMod 2, ∑ j, (matDiag (stabProjectorOf b ε) (e j)) ^ (2 : ℕ)) =
      ((2 : ℂ) ^ n)⁻¹ * ∑ j, ∑ v ∈ spanOf b, pauliDiagSq e v j := by
  classical
  have hbasis := mem_lagrBases.mp hbmem
  have hb := hbasis.1
  have hj : ∀ j, (∑ ε : Fin n → ZMod 2, (matDiag (stabProjectorOf b ε) (e j)) ^ (2 : ℕ)) =
      ((2 : ℂ) ^ n)⁻¹ * ∑ v ∈ spanOf b, pauliDiagSq e v j := by
    intro j
    have hrepl : (∑ ε : Fin n → ZMod 2, (matDiag (stabProjectorOf b ε) (e j)) ^ (2 : ℕ)) =
        ∑ ε : Fin n → ZMod 2, (matDiag (stabProjector b hb ε) (e j)) ^ (2 : ℕ) :=
      Finset.sum_congr rfl fun ε _ => by rw [stabProjectorOf_eq hb]
    rw [hrepl, sum_sign_matDiag_sq hb (e j)]
    congr 1
    exact sum_labSum_eq_sum_span hbasis fun v => pauliDiagSq e v j
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]

/-- **The label incidence identity at one family member.** -/
theorem sum_lagrBases_span_collision (hunit : ∀ j, (∑ x, ‖e j x‖ ^ (2 : ℕ)) = 1)
    (j : FiniteQubitConfiguration (Fin n)) :
    ((2 : ℂ) ^ n + 1) * (∑ b ∈ lagrBases n, ∑ v ∈ spanOf b, pauliDiagSq e v j) =
      ((lagrBases n).card : ℂ) * 2 ^ (n + 1) := by
  classical
  set c : PauliSymp n → ℕ := fun v => ((lagrBases n).filter fun b => v ∈ spanOf b).card with hc
  have hdouble : (∑ b ∈ lagrBases n, ∑ v ∈ spanOf b, pauliDiagSq e v j) =
      ∑ v : PauliSymp n, (c v : ℂ) * pauliDiagSq e v j := by
    have hind : ∀ b : Fin n → PauliSymp n, (∑ v ∈ spanOf b, pauliDiagSq e v j) =
        ∑ v : PauliSymp n, (if v ∈ spanOf b then pauliDiagSq e v j else 0) := by
      intro b
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl fun b _ => hind b, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc]
  have hc0 : c 0 = (lagrBases n).card := by
    have hfil : ((lagrBases n).filter fun b => (0 : PauliSymp n) ∈ spanOf b) = lagrBases n :=
      Finset.filter_true_of_mem fun b _ => zero_mem_spanOf b
    show ((lagrBases n).filter fun b => (0 : PauliSymp n) ∈ spanOf b).card = _
    rw [hfil]
  have hzeroset : (Finset.univ.filter fun v : PauliSymp n => ¬ (v ≠ 0)) = {0} := by
    ext v
    simp
  have hsplit : (∑ v : PauliSymp n, (c v : ℂ) * pauliDiagSq e v j) =
      (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0, (c v : ℂ) * pauliDiagSq e v j) +
        ((lagrBases n).card : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : PauliSymp n => v ≠ 0)]
    congr 1
    rw [hzeroset, Finset.sum_singleton, hc0, pauliDiagSq_zero e hunit j, mul_one]
  have hnzsum : (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0, pauliDiagSq e v j) =
      (2 : ℂ) ^ n - 1 := by
    have htotal : (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0, pauliDiagSq e v j) +
        (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => ¬ (v ≠ 0), pauliDiagSq e v j) =
        (2 : ℂ) ^ n := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact sum_pauliDiagSq e hunit j
    rw [hzeroset, Finset.sum_singleton, pauliDiagSq_zero e hunit j] at htotal
    linear_combination htotal
  have hscale : ((2 : ℂ) ^ n + 1) *
      (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0, (c v : ℂ) * pauliDiagSq e v j) =
      ((lagrBases n).card : ℂ) * ((2 : ℂ) ^ n - 1) := by
    rw [Finset.mul_sum]
    have hterm : ∀ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0,
        ((2 : ℂ) ^ n + 1) * ((c v : ℂ) * pauliDiagSq e v j) =
          ((lagrBases n).card : ℂ) * pauliDiagSq e v j := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have h := card_filter_mem_spanOf_mul_succ hv.2
      have hcast : (c v : ℂ) * ((2 : ℂ) ^ n + 1) = ((lagrBases n).card : ℂ) := by
        rw [hc]
        exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) h
      calc ((2 : ℂ) ^ n + 1) * ((c v : ℂ) * pauliDiagSq e v j)
          = ((c v : ℂ) * ((2 : ℂ) ^ n + 1)) * pauliDiagSq e v j := by ring
        _ = ((lagrBases n).card : ℂ) * pauliDiagSq e v j := by rw [hcast]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hnzsum]
  rw [hdouble, hsplit, mul_add, hscale]
  ring

/-- **The exact two-design collision law.**  Summed over ordered Lagrangian bases, sign patterns
and family members, the collision of a stabilizer state totals `2/(D+1)` per state. -/
theorem sum_lagrBases_sign_collision (hunit : ∀ j, (∑ x, ‖e j x‖ ^ (2 : ℕ)) = 1) :
    ((2 : ℂ) ^ n + 1) * (∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2,
        ∑ j, (matDiag (stabProjectorOf b ε) (e j)) ^ (2 : ℕ)) =
      ((lagrBases n).card : ℂ) * 2 ^ (n + 1) := by
  classical
  have hpow : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  rw [Finset.sum_congr rfl fun b hb => sum_sign_collision_of_mem_lagrBases e hb, ← Finset.mul_sum]
  have hswap : (∑ b ∈ lagrBases n, ∑ j, ∑ v ∈ spanOf b, pauliDiagSq e v j) =
      ∑ j, ∑ b ∈ lagrBases n, ∑ v ∈ spanOf b, pauliDiagSq e v j := Finset.sum_comm
  rw [hswap]
  calc ((2 : ℂ) ^ n + 1) *
        (((2 : ℂ) ^ n)⁻¹ * ∑ j, ∑ b ∈ lagrBases n, ∑ v ∈ spanOf b, pauliDiagSq e v j)
      = ((2 : ℂ) ^ n)⁻¹ *
          (((2 : ℂ) ^ n + 1) * ∑ j, ∑ b ∈ lagrBases n, ∑ v ∈ spanOf b, pauliDiagSq e v j) := by
        ring
    _ = ((2 : ℂ) ^ n)⁻¹ * ∑ j, ((2 : ℂ) ^ n + 1) *
          (∑ b ∈ lagrBases n, ∑ v ∈ spanOf b, pauliDiagSq e v j) := by
        rw [Finset.mul_sum]
    _ = ((2 : ℂ) ^ n)⁻¹ *
          ∑ _j : FiniteQubitConfiguration (Fin n), ((lagrBases n).card : ℂ) * 2 ^ (n + 1) := by
        rw [Finset.sum_congr rfl fun j _ => sum_lagrBases_span_collision e hunit j]
    _ = ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n * (((lagrBases n).card : ℂ) * 2 ^ (n + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, card_finiteQubitConfiguration, nsmul_eq_mul]
        push_cast
        ring
    _ = ((lagrBases n).card : ℂ) * 2 ^ (n + 1) := by
        field_simp

end Assembly

end GaloisForLFunctions.HTGeometry
