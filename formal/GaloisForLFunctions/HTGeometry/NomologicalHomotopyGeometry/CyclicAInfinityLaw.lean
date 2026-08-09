import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.TensorCoalgebra
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Cyclic A-infinity law geometry and the dual-number event

The first section isolates the universal odd-square-zero operator algebra behind a cyclic
`A∞` codifferential.  It proves the Maurer--Cartan equation, the two-periodic deformation
differential, the gauge anchor, and the tangent quotient without assuming those conclusions.

The second section constructs the sourced two-dimensional Frobenius family
`ε *ₜ ε = t·1` over `ℝ`.  Associativity, fixed-pairing cyclicity, its normalized Hochschild
cocycle, and non-coboundary result are all checked symbolically.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw

open Function

universe u v

/-! ## Universal Q-geometry of an odd codifferential -/

namespace QGeometry

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C]

abbrev End := Module.End k C

/-- Composition square of a law operator. -/
def square (Q : End (k := k) (C := C)) : End (k := k) (C := C) :=
  Q.comp Q

/-- Supercommutator of two odd operators. -/
def oddBracket (D E : End (k := k) (C := C)) : End (k := k) (C := C) :=
  D.comp E + E.comp D

/-- Half the odd self-supercommutator is exactly the composition square. -/
theorem half_oddBracket_self [CharZero k] (Q : End (k := k) (C := C)) :
    (2 : k)⁻¹ • oddBracket Q Q = square Q := by
  ext x
  simp [oddBracket, square, ← two_smul k]

/-- Maurer--Cartan form of the square-zero field equation. -/
theorem square_zero_iff_half_bracket_zero [CharZero k]
    (Q : End (k := k) (C := C)) :
    square Q = 0 ↔ (2 : k)⁻¹ • oddBracket Q Q = 0 := by
  rw [half_oddBracket_self]

/-- Commutator with `Q` on even coordinate changes. -/
def dEven (Q : End (k := k) (C := C)) :
    End (k := k) (C := C) →ₗ[k] End (k := k) (C := C) where
  toFun ξ := Q.comp ξ - ξ.comp Q
  map_add' ξ η := by ext; simp; abel
  map_smul' a ξ := by ext; simp [smul_sub]

/-- Anticommutator with `Q` on odd tangent/obstruction cochains. -/
def dOdd (Q : End (k := k) (C := C)) :
    End (k := k) (C := C) →ₗ[k] End (k := k) (C := C) where
  toFun η := Q.comp η + η.comp Q
  map_add' η θ := by ext; simp; abel
  map_smul' a η := by ext; simp

@[simp]
theorem dEven_apply (Q ξ : End (k := k) (C := C)) :
    dEven Q ξ = Q.comp ξ - ξ.comp Q :=
  rfl

@[simp]
theorem dOdd_apply (Q η : End (k := k) (C := C)) :
    dOdd Q η = Q.comp η + η.comp Q :=
  rfl

theorem square_eq_zero_apply (Q : End (k := k) (C := C)) (hQ : square Q = 0)
    (x : C) : Q (Q x) = 0 := by
  have h := LinearMap.congr_fun hQ x
  simpa [square] using h

/-- The deformation differential squares to zero from even to even when `Q²=0`. -/
theorem dOdd_comp_dEven (Q : End (k := k) (C := C)) (hQ : square Q = 0) :
    (dOdd Q).comp (dEven Q) = 0 := by
  ext ξ x
  simp [dOdd, dEven, LinearMap.comp_apply, square_eq_zero_apply Q hQ]

/-- The deformation differential squares to zero from odd to odd when `Q²=0`. -/
theorem dEven_comp_dOdd (Q : End (k := k) (C := C)) (hQ : square Q = 0) :
    (dEven Q).comp (dOdd Q) = 0 := by
  ext η x
  simp [dOdd, dEven, LinearMap.comp_apply, square_eq_zero_apply Q hQ]

/-- Odd infinitesimal solutions of the linearized Maurer--Cartan equation. -/
def tangentCycles (Q : End (k := k) (C := C)) : Submodule k (End (k := k) (C := C)) :=
  LinearMap.ker (dOdd Q)

/-- Even infinitesimal automorphisms. -/
def automorphismCycles (Q : End (k := k) (C := C)) : Submodule k (End (k := k) (C := C)) :=
  LinearMap.ker (dEven Q)

/-- Infinitesimal coordinate anchor `ξ ↦ [Q,ξ]`. -/
def anchor (Q : End (k := k) (C := C)) :
    End (k := k) (C := C) →ₗ[k] End (k := k) (C := C) :=
  dEven Q

/-- Every gauge-anchor direction is tangent to square-zero law space. -/
theorem anchor_mem_tangentCycles (Q : End (k := k) (C := C)) (hQ : square Q = 0)
    (ξ : End (k := k) (C := C)) : anchor Q ξ ∈ tangentCycles Q := by
  change dOdd Q (dEven Q ξ) = 0
  have h := LinearMap.congr_fun (dOdd_comp_dEven Q hQ) ξ
  simpa [LinearMap.comp_apply] using h

/-- Anchor with codomain restricted to the tangent cycle space. -/
def anchorToTangent (Q : End (k := k) (C := C)) (hQ : square Q = 0) :
    End (k := k) (C := C) →ₗ[k] tangentCycles Q :=
  (anchor Q).codRestrict (tangentCycles Q) (anchor_mem_tangentCycles Q hQ)

/-- Primary tangent deformation space: linearized solutions modulo infinitesimal coordinates. -/
abbrev TangentCohomology (Q : End (k := k) (C := C)) (hQ : square Q = 0) :=
  tangentCycles Q ⧸ LinearMap.range (anchorToTangent Q hQ)

/-- Odd differential with codomain restricted to even cycles. -/
def obstructionBoundary (Q : End (k := k) (C := C)) (hQ : square Q = 0) :
    End (k := k) (C := C) →ₗ[k] automorphismCycles Q :=
  (dOdd Q).codRestrict (automorphismCycles Q) fun η ↦ by
    change dEven Q (dOdd Q η) = 0
    have h := LinearMap.congr_fun (dEven_comp_dOdd Q hQ) η
    simpa [LinearMap.comp_apply] using h

/-- Even deformation cohomology.  In the full integer grading its degree-zero and degree-two
pieces are respectively infinitesimal automorphisms and primary obstructions. -/
abbrev EvenCohomology (Q : End (k := k) (C := C)) (hQ : square Q = 0) :=
  automorphismCycles Q ⧸ LinearMap.range (obstructionBoundary Q hQ)

/-- A source-anchored cyclic law chart.  `cyclic` is the fixed linear sector selected by the
pairing; closure records that the commutator deformation stays inside that sector. -/
structure CyclicLawChart where
  Q : End (k := k) (C := C)
  cyclic : Submodule k (End (k := k) (C := C))
  q_cyclic : Q ∈ cyclic
  square_zero : square Q = 0
  anchor_closed : ∀ ξ ∈ cyclic, dEven Q ξ ∈ cyclic
  obstruction_closed : ∀ η ∈ cyclic, dOdd Q η ∈ cyclic

/-- A cyclic law chart supplies an unconditional square-zero deformation complex and anchor. -/
theorem CyclicLawChart.deformation_package [CharZero k]
    (A : CyclicLawChart (k := k) (C := C)) :
    (2 : k)⁻¹ • oddBracket A.Q A.Q = 0 ∧
      (dOdd A.Q).comp (dEven A.Q) = 0 ∧
      (dEven A.Q).comp (dOdd A.Q) = 0 ∧
      (∀ ξ, ξ ∈ A.cyclic → anchor A.Q ξ ∈ tangentCycles A.Q) := by
  refine ⟨(square_zero_iff_half_bracket_zero A.Q).mp A.square_zero,
    dOdd_comp_dEven A.Q A.square_zero, dEven_comp_dOdd A.Q A.square_zero, ?_⟩
  intro ξ _
  exact anchor_mem_tangentCycles A.Q A.square_zero ξ

end QGeometry

/-! ## Reduced tensor-coalgebra realization -/

namespace TensorModel

open scoped TensorProduct
open TensorCoalgebra

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]

abbrev Carrier := TensorCoalgebra.Reduced k V
abbrev End := Module.End k (Carrier (k := k) (V := V))

/-- Koszul tensor action of an odd map: `D ⊗ 1 + P ⊗ D`, where `P` is parity on the first
tensor factor. -/
noncomputable def oddTensorAction (P D : End (k := k) (V := V)) :
    Module.End k (Carrier (k := k) (V := V) ⊗[k] Carrier (k := k) (V := V)) :=
  TensorProduct.map D LinearMap.id + TensorProduct.map P D

/-- Ordinary tensor action of an even map. -/
noncomputable def evenTensorAction (D : End (k := k) (V := V)) :
    Module.End k (Carrier (k := k) (V := V) ⊗[k] Carrier (k := k) (V := V)) :=
  TensorProduct.map D LinearMap.id + TensorProduct.map LinearMap.id D

/-- Exact odd coderivation law on reduced deconcatenation. -/
def IsOddCoderivation (P D : End (k := k) (V := V)) : Prop :=
  (TensorCoalgebra.comul k V).comp D =
    (oddTensorAction P D).comp (TensorCoalgebra.comul k V)

/-- Exact even coderivation law on reduced deconcatenation. -/
def IsEvenCoderivation (D : End (k := k) (V := V)) : Prop :=
  (TensorCoalgebra.comul k V).comp D =
    (evenTensorAction D).comp (TensorCoalgebra.comul k V)

/-- Exact degree-one condition relative to the parity involution. -/
def IsOdd (P D : End (k := k) (V := V)) : Prop :=
  P.comp D = -(D.comp P)

/-- Exact degree-zero condition relative to parity. -/
def IsEven (P D : End (k := k) (V := V)) : Prop :=
  P.comp D = D.comp P

/-- An even coordinate coderivation brackets with an odd law coderivation to an odd coderivation. -/
theorem odd_even_commutator_coderivation (P Q D : End (k := k) (V := V))
    (hDp : IsEven P D) (hQ : IsOddCoderivation P Q) (hD : IsEvenCoderivation D) :
    IsOddCoderivation P (Q.comp D - D.comp Q) := by
  apply LinearMap.ext
  intro x
  change TensorCoalgebra.comul k V (Q (D x) - D (Q x)) = _
  rw [map_sub]
  have hQDx := LinearMap.congr_fun hQ (D x)
  have hDQx := LinearMap.congr_fun hD (Q x)
  change TensorCoalgebra.comul k V (Q (D x)) = _ at hQDx
  change TensorCoalgebra.comul k V (D (Q x)) = _ at hDQx
  rw [hQDx, hDQx]
  have hDx := LinearMap.congr_fun hD x
  have hQx := LinearMap.congr_fun hQ x
  change TensorCoalgebra.comul k V (D x) = _ at hDx
  change TensorCoalgebra.comul k V (Q x) = _ at hQx
  simp only [LinearMap.comp_apply] at hDx hQx ⊢
  rw [hDx, hQx]
  simp only [oddTensorAction, evenTensorAction, LinearMap.add_apply, map_add]
  generalize TensorCoalgebra.comul k V x = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      simp only [map_add]
      convert congrArg₂ (fun a b => a + b) hz hw using 1 <;> abel
  | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.sub_apply]
      have hDpa := LinearMap.congr_fun hDp a
      simp only [LinearMap.comp_apply] at hDpa
      rw [hDpa]
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel

/-- The supercommutator of two odd coderivations is an even coderivation. -/
theorem odd_odd_supercommutator_coderivation (P Q E : End (k := k) (V := V))
    (hP : P.comp P = LinearMap.id) (hQp : IsOdd P Q) (hEp : IsOdd P E)
    (hQ : IsOddCoderivation P Q) (hE : IsOddCoderivation P E) :
    IsEvenCoderivation (Q.comp E + E.comp Q) := by
  apply LinearMap.ext
  intro x
  change TensorCoalgebra.comul k V (Q (E x) + E (Q x)) = _
  rw [map_add]
  have hQEx := LinearMap.congr_fun hQ (E x)
  have hEQx := LinearMap.congr_fun hE (Q x)
  change TensorCoalgebra.comul k V (Q (E x)) = _ at hQEx
  change TensorCoalgebra.comul k V (E (Q x)) = _ at hEQx
  rw [hQEx, hEQx]
  have hEx := LinearMap.congr_fun hE x
  have hQx := LinearMap.congr_fun hQ x
  change TensorCoalgebra.comul k V (E x) = _ at hEx
  change TensorCoalgebra.comul k V (Q x) = _ at hQx
  simp only [LinearMap.comp_apply] at hEx hQx ⊢
  rw [hEx, hQx]
  simp only [oddTensorAction, evenTensorAction, LinearMap.add_apply, map_add]
  generalize TensorCoalgebra.comul k V x = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      simp only [map_add]
      convert congrArg₂ (fun a b => a + b) hz hw using 1 <;> abel
  | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.add_apply]
      have hEpa := LinearMap.congr_fun hEp a
      have hQpa := LinearMap.congr_fun hQp a
      have hPPa := LinearMap.congr_fun hP a
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] at hEpa hQpa hPPa
      rw [hEpa, hQpa, hPPa]
      simp only [TensorProduct.neg_tmul, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel

/-- Ordinary commutators preserve even coderivations. -/
theorem even_even_commutator_coderivation (D E : End (k := k) (V := V))
    (hD : IsEvenCoderivation D) (hE : IsEvenCoderivation E) :
    IsEvenCoderivation (D.comp E - E.comp D) := by
  apply LinearMap.ext
  intro x
  change TensorCoalgebra.comul k V (D (E x) - E (D x)) = _
  rw [map_sub]
  have hDEx := LinearMap.congr_fun hD (E x)
  have hEDx := LinearMap.congr_fun hE (D x)
  change TensorCoalgebra.comul k V (D (E x)) = _ at hDEx
  change TensorCoalgebra.comul k V (E (D x)) = _ at hEDx
  rw [hDEx, hEDx]
  have hEx := LinearMap.congr_fun hE x
  have hDx := LinearMap.congr_fun hD x
  change TensorCoalgebra.comul k V (E x) = _ at hEx
  change TensorCoalgebra.comul k V (D x) = _ at hDx
  simp only [LinearMap.comp_apply] at hEx hDx ⊢
  rw [hEx, hDx]
  simp only [evenTensorAction, LinearMap.add_apply, map_add]
  generalize TensorCoalgebra.comul k V x = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      simp only [map_add]
      convert congrArg₂ (fun a b => a + b) hz hw using 1 <;> abel
  | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.sub_apply, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel

theorem odd_even_commutator_isOdd (P Q D : End (k := k) (V := V))
    (hQ : IsOdd P Q) (hD : IsEven P D) :
    IsOdd P (Q.comp D - D.comp Q) := by
  apply LinearMap.ext
  intro x
  have hQDx := LinearMap.congr_fun hQ (D x)
  have hDx := LinearMap.congr_fun hD x
  have hDQx := LinearMap.congr_fun hD (Q x)
  have hQx := LinearMap.congr_fun hQ x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hQDx hDx hDQx hQx ⊢
  simp only [LinearMap.sub_apply, map_sub, LinearMap.comp_apply]
  rw [hQDx, hDx, hDQx, hQx]
  simp only [map_neg]
  abel

theorem odd_odd_supercommutator_isEven (P Q E : End (k := k) (V := V))
    (hQ : IsOdd P Q) (hE : IsOdd P E) :
    IsEven P (Q.comp E + E.comp Q) := by
  apply LinearMap.ext
  intro x
  have hQEx := LinearMap.congr_fun hQ (E x)
  have hEQx := LinearMap.congr_fun hE (Q x)
  have hEx := LinearMap.congr_fun hE x
  have hQx := LinearMap.congr_fun hQ x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hQEx hEQx hEx hQx ⊢
  simp only [LinearMap.add_apply, map_add, LinearMap.comp_apply]
  rw [hQEx, hEQx, hEx, hQx]
  simp only [map_neg]
  abel

theorem even_even_commutator_isEven (P D E : End (k := k) (V := V))
    (hD : IsEven P D) (hE : IsEven P E) :
    IsEven P (D.comp E - E.comp D) := by
  apply LinearMap.ext
  intro x
  have hDEx := LinearMap.congr_fun hD (E x)
  have hEDx := LinearMap.congr_fun hE (D x)
  have hDx := LinearMap.congr_fun hD x
  have hEx := LinearMap.congr_fun hE x
  simp only [LinearMap.comp_apply] at hDEx hEDx hDx hEx ⊢
  simp only [LinearMap.sub_apply, map_sub, LinearMap.comp_apply]
  rw [hDEx, hEDx, hDx, hEx]

/-- Infinitesimal preservation of a fixed bilinear form by an even endomorphism. -/
def IsCyclicEven (B : Carrier (k := k) (V := V) →ₗ[k]
    Carrier (k := k) (V := V) →ₗ[k] k) (D : End (k := k) (V := V)) : Prop :=
  ∀ x y, B (D x) y + B x (D y) = 0

/-- Infinitesimal graded preservation of a fixed bilinear form by an odd endomorphism. -/
def IsCyclicOdd (B : Carrier (k := k) (V := V) →ₗ[k]
    Carrier (k := k) (V := V) →ₗ[k] k)
    (P D : End (k := k) (V := V)) : Prop :=
  ∀ x y, B (D x) y + B (P x) (D y) = 0

/-- Cyclic odd coderivations are closed under the gauge commutator with cyclic even
coderivations. -/
theorem cyclic_odd_even_commutator (B : Carrier (k := k) (V := V) →ₗ[k]
    Carrier (k := k) (V := V) →ₗ[k] k)
    (P Q D : End (k := k) (V := V))
    (hDP : IsEven P D) (hQ : IsCyclicOdd B P Q) (hD : IsCyclicEven B D) :
    IsCyclicOdd B P (Q.comp D - D.comp Q) := by
  intro x y
  have hQDy := hQ x (D y)
  have hQDx := hQ (D x) y
  have hDPx := LinearMap.congr_fun hDP x
  simp only [LinearMap.comp_apply] at hDPx
  have hDPair := hD (P x) (Q y)
  have hDQ := hD (Q x) y
  simp only [LinearMap.sub_apply, map_sub, LinearMap.comp_apply]
  rw [hDPx] at hQDx
  linear_combination hQDx - hDPair - hDQ + hQDy

/-- Cyclic odd coderivations are closed under odd supercommutator. -/
theorem cyclic_odd_odd_supercommutator (B : Carrier (k := k) (V := V) →ₗ[k]
    Carrier (k := k) (V := V) →ₗ[k] k)
    (P Q E : End (k := k) (V := V))
    (hP : P.comp P = LinearMap.id) (hQP : IsOdd P Q) (hEP : IsOdd P E)
    (hQ : IsCyclicOdd B P Q) (hE : IsCyclicOdd B P E) :
    IsCyclicEven B (Q.comp E + E.comp Q) := by
  intro x y
  have hQEx := hQ (E x) y
  have hEQx := hE (Q x) y
  have hEPx := LinearMap.congr_fun hEP x
  have hQPx := LinearMap.congr_fun hQP x
  have hPPx := LinearMap.congr_fun hP x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] at hEPx hQPx hPPx
  have hEPQ := hE (P x) (Q y)
  have hQPE := hQ (P x) (E y)
  simp only [LinearMap.add_apply, map_add, LinearMap.comp_apply]
  rw [hEPx] at hQEx
  rw [hQPx] at hEQx
  rw [hPPx] at hEPQ hQPE
  simp only [map_neg, LinearMap.neg_apply] at hQEx hEQx hEPQ hQPE
  linear_combination hQEx + hEQx + hEPQ + hQPE

/-- Cyclic even coderivations are closed under ordinary commutator. -/
theorem cyclic_even_even_commutator (B : Carrier (k := k) (V := V) →ₗ[k]
    Carrier (k := k) (V := V) →ₗ[k] k)
    (D E : End (k := k) (V := V))
    (hD : IsCyclicEven B D) (hE : IsCyclicEven B E) :
    IsCyclicEven B (D.comp E - E.comp D) := by
  intro x y
  have hDE := hD (E x) y
  have hED := hE (D x) y
  have hDxy := hD x (E y)
  have hExy := hE x (D y)
  simp only [LinearMap.sub_apply, map_sub, LinearMap.comp_apply]
  linear_combination hDE - hED + hDxy - hExy

/-- Taylor corestriction of an endomorphism at positive tensor length `n`. -/
def taylorCorestriction (D : End (k := k) (V := V))
    (n : TensorCoalgebra.PositiveNat) :
    TensorPower k n.1 V →ₗ[k] V :=
  (TensorCoalgebra.cogenerator k V).comp
    (D.comp (TensorCoalgebra.ofTensor k V n))

@[simp]
theorem taylorCorestriction_zero (n : TensorCoalgebra.PositiveNat) :
    taylorCorestriction (0 : End (k := k) (V := V)) n = 0 := by
  ext x
  simp [taylorCorestriction]

theorem taylorCorestriction_add (D E : End (k := k) (V := V))
    (n : TensorCoalgebra.PositiveNat) :
    taylorCorestriction (D + E) n =
      taylorCorestriction D n + taylorCorestriction E n := by
  ext x
  simp [taylorCorestriction]

theorem taylorCorestriction_smul (a : k) (D : End (k := k) (V := V))
    (n : TensorCoalgebra.PositiveNat) :
    taylorCorestriction (a • D) n = a • taylorCorestriction D n := by
  ext x
  simp [taylorCorestriction]

/-- Tensors supported in lengths at most `N`. -/
def lengthLE (N : ℕ) : Submodule k (Carrier (k := k) (V := V)) :=
  Submodule.span k {x | ∃ (n : TensorCoalgebra.PositiveNat) (y : TensorPower k n.1 V),
    n.1 ≤ N ∧ TensorCoalgebra.ofTensor k V n y = x}

theorem ofTensor_mem_lengthLE (n : TensorCoalgebra.PositiveNat) (x : TensorPower k n.1 V) :
    TensorCoalgebra.ofTensor k V n x ∈ lengthLE (k := k) (V := V) n.1 := by
  apply Submodule.subset_span
  exact ⟨n, x, le_rfl, rfl⟩

theorem lengthLE_mono : Monotone (lengthLE (k := k) (V := V)) := by
  intro M N hMN
  apply Submodule.span_mono
  rintro x ⟨n, y, hn, rfl⟩
  exact ⟨n, y, hn.trans hMN, rfl⟩

theorem lengthLE_zero : lengthLE (k := k) (V := V) 0 = ⊥ := by
  apply le_antisymm
  · rw [lengthLE, Submodule.span_le]
    rintro x ⟨n, y, hn, rfl⟩
    omega
  · exact bot_le

/-- Maximum output length for an operation whose Taylor arity is at least `p`. -/
def outputBound (p N : ℕ) : ℕ := if p ≤ N then N - p + 1 else 0

theorem outputBound_comp (p q N : ℕ) (hp : 0 < p) (hq : 0 < q) :
    outputBound p (outputBound q N) = outputBound (p + q - 1) N := by
  simp only [outputBound]
  split <;> split <;> split <;> omega

theorem outputBound_mono (p : ℕ) : Monotone (outputBound p) := by
  intro M N hMN
  simp only [outputBound]
  split <;> split <;> omega

/-- Actual arity filtration.  A map in `F^p` vanishes below length `p` and lowers every finite
tensor-length truncation by at least `p-1`.  This support formulation remains meaningful on the
tensor-length completion. -/
def arityFiltration (p : ℕ) : Submodule k (End (k := k) (V := V)) where
  carrier := {D | ∀ N x, x ∈ lengthLE (k := k) (V := V) N →
    D x ∈ lengthLE (k := k) (V := V) (outputBound p N)}
  zero_mem' := by intro N x hx; simp
  add_mem' hD hE := by
    intro N x hx
    exact Submodule.add_mem _ (hD N x hx) (hE N x hx)
  smul_mem' a D hD := by
    intro N x hx
    exact Submodule.smul_mem _ a (hD N x hx)

/-- The arity filtration is descending. -/
theorem arityFiltration_antitone : Antitone (arityFiltration (k := k) (V := V)) := by
  intro p q hpq D hD N x hx
  apply (lengthLE_mono (k := k) (V := V)) ?_
  · exact hD N x hx
  · simp only [outputBound]
    split <;> split <;> omega

/-- Arity support implies vanishing of every lower Taylor corestriction. -/
theorem taylorCorestriction_eq_zero_of_mem_arityFiltration (p : ℕ)
    {D : End (k := k) (V := V)} (hD : D ∈ arityFiltration (k := k) (V := V) p)
    (n : TensorCoalgebra.PositiveNat) (hn : n.1 < p) :
    taylorCorestriction D n = 0 := by
  apply LinearMap.ext
  intro x
  have h := hD n.1 (TensorCoalgebra.ofTensor k V n x)
    (ofTensor_mem_lengthLE (k := k) (V := V) n x)
  have hz : D (TensorCoalgebra.ofTensor k V n x) = 0 := by
    rw [outputBound, if_neg (not_le.mpr hn), lengthLE_zero] at h
    exact h
  simp [taylorCorestriction, hz]

/-- Composition adds arities and subtracts the shared insertion slot. -/
theorem comp_mem_arityFiltration (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    {D E : End (k := k) (V := V)}
    (hD : D ∈ arityFiltration (k := k) (V := V) p)
    (hE : E ∈ arityFiltration (k := k) (V := V) q) :
    D.comp E ∈ arityFiltration (k := k) (V := V) (p + q - 1) := by
  intro N x hx
  change D (E x) ∈ _
  have h := hD (outputBound q N) (E x) (hE N x hx)
  rwa [outputBound_comp p q N hp hq] at h

/-- Exact filtered commutator estimate `[F^p,F^q] ⊆ F^(p+q-1)`. -/
theorem commutator_mem_arityFiltration (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    {D E : End (k := k) (V := V)}
    (hD : D ∈ arityFiltration (k := k) (V := V) p)
    (hE : E ∈ arityFiltration (k := k) (V := V) q) :
    D.comp E - E.comp D ∈ arityFiltration (k := k) (V := V) (p + q - 1) := by
  intro N x hx
  change D (E x) - E (D x) ∈ _
  have hDE := comp_mem_arityFiltration p q hp hq hD hE
  have hED := comp_mem_arityFiltration q p hq hp hE hD
  exact Submodule.sub_mem _ (hDE N x hx)
    (by simpa [Nat.add_comm] using hED N x hx)

/-- Exact filtered odd-supercommutator estimate. -/
theorem oddBracket_mem_arityFiltration (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    {D E : End (k := k) (V := V)}
    (hD : D ∈ arityFiltration (k := k) (V := V) p)
    (hE : E ∈ arityFiltration (k := k) (V := V) q) :
    D.comp E + E.comp D ∈ arityFiltration (k := k) (V := V) (p + q - 1) := by
  intro N x hx
  change D (E x) + E (D x) ∈ _
  have hDE := comp_mem_arityFiltration p q hp hq hD hE
  have hED := comp_mem_arityFiltration q p hq hp hE hD
  exact Submodule.add_mem _ (hDE N x hx)
    (by simpa [Nat.add_comm] using hED N x hx)

/-- Taylor coefficients below `p` vanish. -/
def TaylorSupportedFrom (p : ℕ) (m : TensorCoalgebra.TaylorFamily k V) : Prop :=
  ∀ n, n.1 < p → m n = 0

theorem insertTaylor_zero_local (n r i : ℕ) (hr : r ≤ n) (hi : i ≤ n - r) :
    TensorCoalgebra.insertTaylor k V n r i hr hi
      (0 : TensorPower k r V →ₗ[k] V) = 0 := by
  ext x
  simp [TensorCoalgebra.insertTaylor]

theorem homogeneousTaylorExtension_mem (p : ℕ) (m : TensorCoalgebra.TaylorFamily k V)
    (hm : TaylorSupportedFrom p m) (n : TensorCoalgebra.PositiveNat)
    (x : TensorPower k n.1 V) :
    TensorCoalgebra.homogeneousTaylorExtension k V m n x ∈
      lengthLE (k := k) (V := V) (outputBound p n.1) := by
  rw [TensorCoalgebra.homogeneousTaylorExtension]
  simp only [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.sum_mem
  intro i _
  by_cases hr : p ≤ r.1 + 1
  · change TensorCoalgebra.ofTensor k V (TensorCoalgebra.insertionWeight n r)
      (TensorCoalgebra.insertTaylor k V n.1 (r.1 + 1) i.1 (by omega) (by omega)
        (m (TensorCoalgebra.selectedArity n r)) x) ∈ _
    apply (lengthLE_mono (k := k) (V := V)) ?_
      (ofTensor_mem_lengthLE (k := k) (V := V) (TensorCoalgebra.insertionWeight n r) _)
    simp only [outputBound]
    split <;> omega
  · have hs : (TensorCoalgebra.selectedArity n r).1 < p := by
      change r.1 + 1 < p
      omega
    have hz := hm (TensorCoalgebra.selectedArity n r) hs
    change TensorCoalgebra.ofTensor k V (TensorCoalgebra.insertionWeight n r)
      (TensorCoalgebra.insertTaylor k V n.1 (r.1 + 1) i.1 (by omega) (by omega)
        (m (TensorCoalgebra.selectedArity n r)) x) ∈ _
    rw [hz, insertTaylor_zero_local]
    simp

/-- The insertion extension of a Taylor family supported from arity `p` belongs to `F^p`. -/
theorem extendTaylor_mem_arityFiltration (p : ℕ) (m : TensorCoalgebra.TaylorFamily k V)
    (hm : TaylorSupportedFrom p m) :
    TensorCoalgebra.extendTaylor k V m ∈ arityFiltration (k := k) (V := V) p := by
  intro N x hx
  change TensorCoalgebra.extendTaylor k V m x ∈ _
  refine Submodule.span_induction (p := fun x _ ↦
      TensorCoalgebra.extendTaylor k V m x ∈
        lengthLE (k := k) (V := V) (outputBound p N)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨n, y, hn, rfl⟩
    rw [TensorCoalgebra.extendTaylor_ofTensor]
    exact (lengthLE_mono (k := k) (V := V))
      ((outputBound_mono p) hn) (homogeneousTaylorExtension_mem p m hm n y)
  · simp
  · intro a b ha hb hma hmb
    simpa using Submodule.add_mem _ hma hmb
  · intro a x hx hmx
    simpa using Submodule.smul_mem _ a hmx

/-! ### Exact tensor-length completion and pronilpotence -/

/-- Taylor coefficients through tensor length `N`. -/
abbrev TaylorJet (N : ℕ) :=
  ∀ n : {n : TensorCoalgebra.PositiveNat // n.1 ≤ N},
    TensorPower k n.1.1 V →ₗ[k] V

/-- Restriction between finite Taylor jets. -/
def restrictTaylorJet {M N : ℕ} (hMN : M ≤ N)
    (j : TaylorJet (k := k) (V := V) N) : TaylorJet (k := k) (V := V) M :=
  fun n ↦ j ⟨n.1, n.2.trans hMN⟩

/-- Algebraic inverse limit of every finite tensor-length Taylor jet. -/
structure TaylorJetTower where
  jet : ∀ N, TaylorJet (k := k) (V := V) N
  compatible : ∀ {M N} (hMN : M ≤ N)
    (n : {n : TensorCoalgebra.PositiveNat // n.1 ≤ M}),
    restrictTaylorJet hMN (jet N) n = jet M n

def TaylorJetTower.ofTaylor (m : TensorCoalgebra.TaylorFamily k V) :
    TaylorJetTower (k := k) (V := V) where
  jet _ n := m n.1
  compatible _ _ := rfl

def TaylorJetTower.toTaylor (J : TaylorJetTower (k := k) (V := V)) :
    TensorCoalgebra.TaylorFamily k V :=
  fun n ↦ J.jet n.1 ⟨n, le_rfl⟩

theorem TaylorJetTower.toTaylor_ofTaylor (m : TensorCoalgebra.TaylorFamily k V) :
    (TaylorJetTower.ofTaylor m).toTaylor = m := by
  rfl

theorem TaylorJetTower.ofTaylor_toTaylor (J : TaylorJetTower (k := k) (V := V)) :
    TaylorJetTower.ofTaylor J.toTaylor = J := by
  cases J with
  | mk jet compatible =>
      simp only [TaylorJetTower.toTaylor, TaylorJetTower.ofTaylor]
      congr
      funext N n
      exact (compatible n.2 ⟨n.1, le_rfl⟩).symm

/-- The full Taylor family is exactly the inverse limit of its finite jets.  This is the algebraic
completeness statement for the tensor-arity topology. -/
def taylorCompletionEquiv :
    TensorCoalgebra.TaylorFamily k V ≃ TaylorJetTower (k := k) (V := V) where
  toFun := TaylorJetTower.ofTaylor
  invFun := TaylorJetTower.toTaylor
  left_inv := TaylorJetTower.toTaylor_ofTaylor
  right_inv := TaylorJetTower.ofTaylor_toTaylor

/-- The Taylor arity filtration is separated. -/
theorem taylorFiltration_separated (m : TensorCoalgebra.TaylorFamily k V)
    (hm : ∀ p, TaylorSupportedFrom p m) : m = 0 := by
  funext n
  exact hm (n.1 + 1) n (by omega)

/-- Left-nested ordinary commutator. -/
def iteratedCommutator (D : End (k := k) (V := V)) :
    List (End (k := k) (V := V)) → End (k := k) (V := V)
  | [] => D
  | E :: L => iteratedCommutator (D.comp E - E.comp D) L

theorem iteratedCommutator_mem (p : ℕ) (hp : 0 < p)
    (D : End (k := k) (V := V)) (L : List (End (k := k) (V := V)))
    (hD : D ∈ arityFiltration (k := k) (V := V) p)
    (hL : ∀ E ∈ L, E ∈ arityFiltration (k := k) (V := V) 2) :
    iteratedCommutator D L ∈
      arityFiltration (k := k) (V := V) (p + L.length) := by
  induction L generalizing D p with
  | nil => simpa [iteratedCommutator] using hD
  | cons E L ih =>
      have hE : E ∈ arityFiltration (k := k) (V := V) 2 := hL E (by simp)
      have hBracket := commutator_mem_arityFiltration p 2 hp (by omega) hD hE
      have hTail : ∀ F ∈ L, F ∈ arityFiltration (k := k) (V := V) 2 := by
        intro F hF
        exact hL F (by simp [hF])
      have h := ih (p := p + 1) (by omega) (D := D.comp E - E.comp D) hBracket hTail
      rw [iteratedCommutator]
      have heq : p + 1 + L.length = p + (L.length + 1) := by omega
      change iteratedCommutator (D.comp E - E.comp D) L ∈
        arityFiltration (k := k) (V := V) (p + (L.length + 1))
      rw [← heq]
      exact h

/-- `F^(N+1)` acts trivially on the length-`N` Taylor jet. -/
theorem arityFiltration_succ_annihilates_lengthLE (N : ℕ)
    {D : End (k := k) (V := V)}
    (hD : D ∈ arityFiltration (k := k) (V := V) (N + 1))
    {x : Carrier (k := k) (V := V)} (hx : x ∈ lengthLE (k := k) (V := V) N) :
    D x = 0 := by
  have h := hD N x hx
  rw [outputBound, if_neg (by omega), lengthLE_zero] at h
  exact h

/-- Every length-`N+1` quotient of the positive-arity ideal is nilpotent: an `(N+1)`-fold
commutator of arity-at-least-two operators vanishes on that jet. -/
theorem finiteTaylorJet_pronilpotent (N : ℕ)
    (D : End (k := k) (V := V)) (L : List (End (k := k) (V := V)))
    (hD : D ∈ arityFiltration (k := k) (V := V) 2)
    (hL : ∀ E ∈ L, E ∈ arityFiltration (k := k) (V := V) 2)
    (hlen : L.length = N) {x : Carrier (k := k) (V := V)}
    (hx : x ∈ lengthLE (k := k) (V := V) (N + 1)) :
    iteratedCommutator D L x = 0 := by
  have h := iteratedCommutator_mem 2 (by omega) D L hD hL
  rw [hlen] at h
  have h' : iteratedCommutator D L ∈
      arityFiltration (k := k) (V := V) ((N + 1) + 1) := by
    have heq : 2 + N = (N + 1) + 1 := by omega
    rw [← heq]
    exact h
  exact arityFiltration_succ_annihilates_lengthLE (N + 1) h' hx

/-- All tensor-length components of `Q²` vanish.  This is the direct-sum form of the Stasheff
identities before projecting further to cogenerators. -/
def TensorLengthIdentities (Q : End (k := k) (V := V)) : Prop :=
  ∀ (n : TensorCoalgebra.PositiveNat) (x : TensorPower k n.1 V)
    (m : TensorCoalgebra.PositiveNat),
    DirectSum.component k TensorCoalgebra.PositiveNat
      (fun r : TensorCoalgebra.PositiveNat ↦ TensorPower k r.1 V) m
      (Q (Q (TensorCoalgebra.ofTensor k V n x))) = 0

/-- Square-zero is equivalent to the complete family of tensor-length Stasheff components. -/
theorem square_zero_iff_tensorLengthIdentities (Q : End (k := k) (V := V)) :
    QGeometry.square Q = 0 ↔ TensorLengthIdentities Q := by
  constructor
  · intro hQ n x m
    have h := LinearMap.congr_fun hQ (TensorCoalgebra.ofTensor k V n x)
    simpa [QGeometry.square] using congrArg
      (DirectSum.component k TensorCoalgebra.PositiveNat
        (fun r : TensorCoalgebra.PositiveNat ↦ TensorPower k r.1 V) m) h
  · intro h
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    apply DirectSum.ext_component k
    intro m
    simpa [QGeometry.square, TensorCoalgebra.ofTensor] using h n x m

/-- A source-anchored cyclic `A∞` tensor chart with its fixed form on the completed tensor
coordinates.  Cyclic closure is proved below rather than stored as a field. -/
structure CyclicTensorLaw where
  parity : End (k := k) (V := V)
  parity_involutive : parity.comp parity = LinearMap.id
  pairing : V →ₗ[k] V →ₗ[k] k
  pairing_nondegenerate : ∀ x, (∀ y, pairing x y = 0) → x = 0
  carrierPairing : Carrier (k := k) (V := V) →ₗ[k] Carrier (k := k) (V := V) →ₗ[k] k
  carrierPairing_nondegenerate : ∀ x, (∀ y, carrierPairing x y = 0) → x = 0
  carrierPairing_on_cogenerators : ∀ x y : TensorPower k 1 V,
    carrierPairing
        (TensorCoalgebra.ofTensor k V TensorCoalgebra.oneWeight x)
        (TensorCoalgebra.ofTensor k V TensorCoalgebra.oneWeight y) =
      pairing (TensorCoalgebra.tensorPowerOneEquiv k V x)
        (TensorCoalgebra.tensorPowerOneEquiv k V y)
  Q : End (k := k) (V := V)
  q_odd : IsOdd parity Q
  q_coderivation : IsOddCoderivation parity Q
  q_cyclic : IsCyclicOdd carrierPairing parity Q
  square_zero : QGeometry.square Q = 0

/-- The gauge anchor of a cyclic even coderivation is again an odd cyclic coderivation. -/
theorem CyclicTensorLaw.anchor_closed (A : CyclicTensorLaw (k := k) (V := V))
    (ξ : End (k := k) (V := V)) (hξp : IsEven A.parity ξ)
    (hξD : IsEvenCoderivation ξ) (hξc : IsCyclicEven A.carrierPairing ξ) :
    IsOdd A.parity (QGeometry.dEven A.Q ξ) ∧
      IsOddCoderivation A.parity (QGeometry.dEven A.Q ξ) ∧
      IsCyclicOdd A.carrierPairing A.parity (QGeometry.dEven A.Q ξ) := by
  exact ⟨odd_even_commutator_isOdd A.parity A.Q ξ A.q_odd hξp,
    odd_even_commutator_coderivation A.parity A.Q ξ hξp A.q_coderivation hξD,
    cyclic_odd_even_commutator A.carrierPairing A.parity A.Q ξ hξp A.q_cyclic hξc⟩

/-- The odd deformation differential closes into even cyclic coderivations. -/
theorem CyclicTensorLaw.obstruction_closed (A : CyclicTensorLaw (k := k) (V := V))
    (η : End (k := k) (V := V)) (hηp : IsOdd A.parity η)
    (hηD : IsOddCoderivation A.parity η)
    (hηc : IsCyclicOdd A.carrierPairing A.parity η) :
    IsEven A.parity (QGeometry.dOdd A.Q η) ∧
      IsEvenCoderivation (QGeometry.dOdd A.Q η) ∧
      IsCyclicEven A.carrierPairing (QGeometry.dOdd A.Q η) := by
  exact ⟨odd_odd_supercommutator_isEven A.parity A.Q η A.q_odd hηp,
    odd_odd_supercommutator_coderivation A.parity A.Q η A.parity_involutive
      A.q_odd hηp A.q_coderivation hηD,
    cyclic_odd_odd_supercommutator A.carrierPairing A.parity A.Q η
      A.parity_involutive A.q_odd hηp A.q_cyclic hηc⟩

/-- A tensor law satisfies the complete tensor-length identities and carries the intrinsic cyclic
deformation package. -/
theorem CyclicTensorLaw.field_equation [CharZero k]
    (A : CyclicTensorLaw (k := k) (V := V)) :
    TensorLengthIdentities A.Q ∧
      (2 : k)⁻¹ • QGeometry.oddBracket A.Q A.Q = 0 ∧
      (QGeometry.dOdd A.Q).comp (QGeometry.dEven A.Q) = 0 := by
  exact ⟨(square_zero_iff_tensorLengthIdentities A.Q).mp A.square_zero,
    (QGeometry.square_zero_iff_half_bracket_zero A.Q).mp A.square_zero,
    QGeometry.dOdd_comp_dEven A.Q A.square_zero⟩

end TensorModel

/-! ## Explicit sourced law: the dual-number event -/

namespace DualNumberEvent

/-- Coordinate model `a·1 + b·ε`. -/
abbrev Dual := ℝ × ℝ

/-- Unit basis vector. -/
def one : Dual := (1, 0)

/-- Nilpotent/event basis vector. -/
def eps : Dual := (0, 1)

/-- Product family `ε *ₜ ε = t·1`. -/
def product (t : ℝ) (x y : Dual) : Dual :=
  (x.1 * y.1 + t * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Frobenius trace, extracting the `ε` coefficient. -/
def trace (x : Dual) : ℝ := x.2

/-- Fixed Frobenius pairing from the undeformed dual-number product. -/
def pairing (x y : Dual) : ℝ := trace (product 0 x y)

/-- Infinitesimal event cochain: only `(ε,ε)` is sent to `1`. -/
def phi (x y : Dual) : Dual := (x.2 * y.2, 0)

@[simp] theorem product_one_left (t : ℝ) (x : Dual) : product t one x = x := by
  ext <;> simp [product, one]

@[simp] theorem product_one_right (t : ℝ) (x : Dual) : product t x one = x := by
  ext <;> simp [product, one]

theorem product_comm (t : ℝ) (x y : Dual) : product t x y = product t y x := by
  ext <;> dsimp [product] <;> ring

theorem product_assoc (t : ℝ) (x y z : Dual) :
    product t (product t x y) z = product t x (product t y z) := by
  ext <;> dsimp [product] <;> ring

/-- The pairing matrix in the basis `(1,ε)` is `[[0,1],[1,0]]`. -/
theorem pairing_basis_matrix :
    pairing one one = 0 ∧ pairing one eps = 1 ∧
      pairing eps one = 1 ∧ pairing eps eps = 0 := by
  norm_num [pairing, trace, product, one, eps]

/-- Fixed pairing is nondegenerate. -/
theorem pairing_nondegenerate :
    ∀ x : Dual, (∀ y : Dual, pairing x y = 0) → x = 0 := by
  intro x h
  have h1 := h one
  have he := h eps
  ext <;> simp [pairing, trace, product, one, eps] at h1 he ⊢ <;> assumption

/-- Every deformed product is cyclic for the same fixed pairing. -/
theorem pairing_cyclic (t : ℝ) (x y z : Dual) :
    pairing (product t x y) z = pairing x (product t y z) := by
  dsimp [pairing, trace, product]
  ring

/-- Exact first-order expansion of the law family. -/
theorem product_eq_base_add_event (t : ℝ) (x y : Dual) :
    product t x y = product 0 x y + t • phi x y := by
  ext <;> dsimp [product, phi] <;> ring

@[simp] theorem phi_eps_eps : phi eps eps = one := by
  norm_num [phi, eps, one]

@[simp] theorem phi_one_left (x : Dual) : phi one x = 0 := by
  ext <;> simp [phi, one]

@[simp] theorem phi_one_right (x : Dual) : phi x one = 0 := by
  ext <;> simp [phi, one]

/-- Hochschild differential of a binary cochain, for the undeformed product. -/
def deltaTwo (ψ : Dual → Dual → Dual) (x y z : Dual) : Dual :=
  product 0 x (ψ y z) - ψ (product 0 x y) z +
    ψ x (product 0 y z) - product 0 (ψ x y) z

/-- The event derivative is a normalized Hochschild two-cocycle. -/
theorem phi_cocycle (x y z : Dual) : deltaTwo phi x y z = 0 := by
  ext <;> dsimp [deltaTwo, phi, product] <;> ring

/-- Hochschild coboundary of an infinitesimal linear coordinate change. -/
def deltaOne (ξ : Dual →ₗ[ℝ] Dual) (x y : Dual) : Dual :=
  product 0 x (ξ y) - ξ (product 0 x y) + product 0 (ξ x) y

/-- Any one-cochain coboundary has zero `1`-coordinate on `(ε,ε)`. -/
theorem deltaOne_eps_eps_fst (ξ : Dual →ₗ[ℝ] Dual) :
    (deltaOne ξ eps eps).1 = 0 := by
  simp [deltaOne, product, eps]
  rw [show ((0, 0) : Dual) = 0 by rfl, map_zero]
  rfl

/-- The event cocycle is not a coboundary, even before restricting to normalized coordinate
changes; hence its normalized deformation class is nonzero. -/
theorem phi_not_coboundary :
    ¬ ∃ ξ : Dual →ₗ[ℝ] Dual, ξ one = 0 ∧ ∀ x y, deltaOne ξ x y = phi x y := by
  rintro ⟨ξ, _, hξ⟩
  have h := congrArg Prod.fst (hξ eps eps)
  rw [deltaOne_eps_eps_fst] at h
  norm_num [phi_eps_eps, one] at h

/-- Complete concrete event package. -/
theorem dualNumber_event_realization :
    (∀ t x y z, product t (product t x y) z = product t x (product t y z)) ∧
      (∀ t x y z, pairing (product t x y) z = pairing x (product t y z)) ∧
      (∀ x y z, deltaTwo phi x y z = 0) ∧
      ¬ ∃ ξ : Dual →ₗ[ℝ] Dual, ξ one = 0 ∧ ∀ x y, deltaOne ξ x y = phi x y :=
  ⟨product_assoc, pairing_cyclic, phi_cocycle, phi_not_coboundary⟩

end DualNumberEvent

end HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw
