import GaloisForLFunctions.HTGeometry.TwoReplicaLocalSingletSynchronization

/-!
# The single edge commutator on the local identity/swap basis

One fixed-orientation weight-two collective commutator annihilates both endpoint-matched swap words
and sends each mismatched word to a product of replica differences.  The computation is the swap
relations `F σ_a ⊗ I = I ⊗ σ_a F` applied once at each endpoint; no spectral input is used.

These are the four values a resolved edge-incidence argument reads off: the kernel is exactly the
matched sector, and the two mismatched outputs are visibly nonzero difference operators.
-/

open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The replica difference `σ_a ⊗ I - I ⊗ σ_a` at one site. -/
def twoReplicaLocalDiff (a : Fin 3) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  twoReplicaPauliLeft a - twoReplicaPauliRight a

theorem twoReplicaLocalDiff_mul_swap (a : Fin 3) :
    twoReplicaLocalDiff a * twoReplicaSwap =
      -(twoReplicaSwap * twoReplicaLocalDiff a) := by
  rw [twoReplicaLocalDiff, Matrix.sub_mul, Matrix.mul_sub,
    ← twoReplicaSwap_mul_right a, ← twoReplicaSwap_mul_left a]
  module

/-- The matched word `I ⊗ I` is annihilated. -/
theorem twoReplicaEdgeCommutator_one_one (a b : Fin 3) :
    twoReplicaEdgeCommutator a b
        ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ
          (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) = 0 := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = 0
  rw [Matrix.one_kronecker_one, Matrix.mul_one, Matrix.one_mul, sub_self]

/-- The matched word `F ⊗ F` is annihilated. -/
theorem twoReplicaEdgeCommutator_swap_swap (a b : Fin 3) :
    twoReplicaEdgeCommutator a b (twoReplicaSwap ⊗ₖ twoReplicaSwap) = 0 := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = 0
  rw [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add]
  simp only [twoReplicaKronecker_mul]
  rw [← twoReplicaSwap_mul_right a, ← twoReplicaSwap_mul_right b,
    ← twoReplicaSwap_mul_left a, ← twoReplicaSwap_mul_left b]
  module

/-- The mismatched word `I ⊗ F` goes to a product of replica differences. -/
theorem twoReplicaEdgeCommutator_one_swap (a b : Fin 3) :
    twoReplicaEdgeCommutator a b
        ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ twoReplicaSwap) =
      -(twoReplicaLocalDiff a ⊗ₖ (twoReplicaSwap * twoReplicaLocalDiff b)) := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = _
  rw [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add]
  simp only [twoReplicaKronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [← twoReplicaSwap_mul_right b, ← twoReplicaSwap_mul_left b,
    twoReplicaLocalDiff, twoReplicaLocalDiff, Matrix.mul_sub]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.neg_apply]
  ring

/-- The mismatched word `F ⊗ I` goes to a product of replica differences. -/
theorem twoReplicaEdgeCommutator_swap_one (a b : Fin 3) :
    twoReplicaEdgeCommutator a b
        (twoReplicaSwap ⊗ₖ (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) =
      -((twoReplicaSwap * twoReplicaLocalDiff a) ⊗ₖ twoReplicaLocalDiff b) := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = _
  rw [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add]
  simp only [twoReplicaKronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [← twoReplicaSwap_mul_right a, ← twoReplicaSwap_mul_left a,
    twoReplicaLocalDiff, twoReplicaLocalDiff, Matrix.mul_sub]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.neg_apply]
  ring

/-! ## Hilbert--Schmidt sizes of the mismatched outputs -/

/-- The replica difference squares to twice the identity minus twice the correlation term. -/
theorem twoReplicaLocalDiff_sq (a : Fin 3) :
    twoReplicaLocalDiff a * twoReplicaLocalDiff a =
      (2 : ℂ) • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) -
        (2 : ℂ) • twoReplicaPauliPair a := by
  rw [twoReplicaLocalDiff, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    twoReplicaPauliLeft_mul_self, twoReplicaPauliRight_mul_self,
    twoReplicaPauliLeft_mul_right, twoReplicaPauliRight_mul_left]
  module

/-- **The replica difference has Hilbert--Schmidt square eight.** -/
theorem trace_twoReplicaLocalDiff_sq (a : Fin 3) :
    Matrix.trace (twoReplicaLocalDiff a * twoReplicaLocalDiff a) = 8 := by
  have hpair : Matrix.trace (twoReplicaPauliPair a) = 0 := by
    rw [twoReplicaPauliPair, Matrix.trace_kronecker]
    fin_cases a <;>
      simp [finiteQubitPauli, Matrix.trace]
  rw [twoReplicaLocalDiff_sq, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one, hpair]
  norm_num

/-- Swapping past the correlation term of one axis costs nothing in trace. -/
theorem trace_twoReplicaPauliPair_mul_swap (a : Fin 3) :
    Matrix.trace (twoReplicaPauliPair a * twoReplicaSwap) = 2 := by
  rw [← twoReplicaPauliLeft_mul_right a, Matrix.mul_assoc,
    ← twoReplicaSwap_mul_left a, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, twoReplicaPauliLeft_mul_self, Matrix.one_mul,
    trace_twoReplicaSwap]

/-- **The replica difference is Hilbert--Schmidt orthogonal to its swap translate.** -/
theorem trace_twoReplicaLocalDiff_mul_swap_mul_diff (a : Fin 3) :
    Matrix.trace
      (twoReplicaLocalDiff a * (twoReplicaSwap * twoReplicaLocalDiff a)) = 0 := by
  rw [← Matrix.mul_assoc, twoReplicaLocalDiff_mul_swap, Matrix.neg_mul,
    Matrix.trace_neg, Matrix.mul_assoc, twoReplicaLocalDiff_sq,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    trace_twoReplicaSwap, Matrix.trace_mul_comm,
    trace_twoReplicaPauliPair_mul_swap]
  norm_num

/-! ## The mismatched outputs leave the local singlet algebra -/

theorem trace_twoReplicaLocalDiff (a : Fin 3) :
    Matrix.trace (twoReplicaLocalDiff a) = 0 := by
  have hleft : Matrix.trace (twoReplicaPauliLeft a) = 0 := by
    rw [twoReplicaPauliLeft, Matrix.trace_kronecker]
    fin_cases a <;> simp [finiteQubitPauli, Matrix.trace]
  have hright : Matrix.trace (twoReplicaPauliRight a) = 0 := by
    rw [twoReplicaPauliRight, Matrix.trace_kronecker]
    fin_cases a <;> simp [finiteQubitPauli, Matrix.trace]
  rw [twoReplicaLocalDiff, Matrix.trace_sub, hleft, hright, sub_zero]

/-- The swap translate of a replica difference is also traceless, because conjugating by the swap
exchanges the two replica Paulis and so negates the difference. -/
theorem trace_swap_mul_twoReplicaLocalDiff (a : Fin 3) :
    Matrix.trace (twoReplicaSwap * twoReplicaLocalDiff a) = 0 := by
  have hself : Matrix.trace (twoReplicaSwap * twoReplicaLocalDiff a) =
      -Matrix.trace (twoReplicaSwap * twoReplicaLocalDiff a) := by
    conv_lhs => rw [← Matrix.trace_mul_comm, twoReplicaLocalDiff_mul_swap]
    rw [Matrix.trace_neg]
  linear_combination hself / 2

/-- **The mismatched outputs are orthogonal to the local singlet algebra.** -/
theorem trace_twoReplicaLocalSwapRaw_mul_diff (x : Bool) (a : Fin 3) :
    Matrix.trace (twoReplicaLocalSwapRaw x * twoReplicaLocalDiff a) = 0 := by
  cases x with
  | false => rw [twoReplicaLocalSwapRaw, Matrix.one_mul, trace_twoReplicaLocalDiff]
  | true => rw [twoReplicaLocalSwapRaw, trace_swap_mul_twoReplicaLocalDiff]

theorem trace_twoReplicaLocalSwapRaw_mul_swap_mul_diff (x : Bool) (a : Fin 3) :
    Matrix.trace
      (twoReplicaLocalSwapRaw x * (twoReplicaSwap * twoReplicaLocalDiff a)) = 0 := by
  cases x with
  | false =>
      rw [twoReplicaLocalSwapRaw, Matrix.one_mul, trace_swap_mul_twoReplicaLocalDiff]
  | true =>
      rw [twoReplicaLocalSwapRaw, ← Matrix.mul_assoc, twoReplicaSwap_sq,
        Matrix.one_mul, trace_twoReplicaLocalDiff]

end

end GaloisForLFunctions.HTGeometry
