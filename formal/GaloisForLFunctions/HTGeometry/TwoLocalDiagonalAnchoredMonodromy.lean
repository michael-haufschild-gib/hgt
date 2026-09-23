import GaloisForLFunctions.HTGeometry.TwoLocalFullStarSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A label-controlled diagonal anchor for two-local spectral monodromy

The earlier isolated-edge loop realizes an exact transposition, but an
arbitrary path to a common base can conjugate that transposition by an
unknown permutation.  This file removes that ambiguity.

We introduce a variable transverse coupling `u` and the closed loop

`w(s) = (i/4)(1-exp(2πis))`, `u(s) = (1/4)(1+exp(2πis))`.

Its selected radicand is `(1/4)exp(2πis)`, so one selected sheet changes
sign.  Every nonselected radicand stays in the open right half-plane, and
distinct Boolean environments remain spectrally disjoint.  The loop is
based at `(w,u)=(0,1/2)`.

The explicit connector

`w(t)=t/2`, `u(t)=sqrt(1-t^(2 : ℕ))/2`

keeps the selected radicand equal to `1/4`, ends at the diagonal point
`(1/2,0)`, and transports every signed root to its named computational
label.  Thus subsequent transport inside a diagonal simple-spectrum locus
cannot introduce an unknown relabeling.
-/

open scoped BigOperators

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-! ## Variable-transverse isolated-edge family -/

/-- Quadratic radicand with independent longitudinal and transverse
couplings. -/
def twoLocalVariableBranchRadicand {m : ℕ}
    (z₀ z : Fin m → Bool) (w u : ℂ) : ℂ :=
  ((starIsingBinaryCode z₀ z : ℂ) + w) ^ (2 : ℕ) + u ^ (2 : ℕ)

/-- The corresponding two-level Hamiltonian block. -/
def twoLocalVariableEdgeHamiltonianBlock {m : ℕ}
    (z₀ z : Fin m → Bool) (w u : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((starIsingBinaryCode z₀ z : ℂ) + w), u;
      u, -((starIsingBinaryCode z₀ z : ℂ) + w)]

/-- The corresponding `λI-H` block. -/
def twoLocalVariableEdgeCharacteristicMatrix {m : ℕ}
    (z₀ z : Fin m → Bool) (w u lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![lam - ((starIsingBinaryCode z₀ z : ℂ) + w), -u;
      -u, lam + ((starIsingBinaryCode z₀ z : ℂ) + w)]

theorem det_twoLocalVariableEdgeCharacteristicMatrix {m : ℕ}
    (z₀ z : Fin m → Bool) (w u lam : ℂ) :
    (twoLocalVariableEdgeCharacteristicMatrix z₀ z w u lam).det =
      lam ^ (2 : ℕ) - twoLocalVariableBranchRadicand z₀ z w u := by
  simp [twoLocalVariableEdgeCharacteristicMatrix,
    Matrix.det_fin_two, twoLocalVariableBranchRadicand]
  ring

def twoLocalVariableBlockHamiltonianMatrix {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    Matrix (Fin 2 × (Fin m → Bool))
      (Fin 2 × (Fin m → Bool)) ℂ :=
  Matrix.blockDiagonal fun z =>
    twoLocalVariableEdgeHamiltonianBlock z₀ z w u

theorem twoLocalVariableBlockCharacteristicMatrix_eq {m : ℕ}
    (z₀ : Fin m → Bool) (w u lam : ℂ) :
    Matrix.scalar (Fin 2 × (Fin m → Bool)) lam -
        twoLocalVariableBlockHamiltonianMatrix z₀ w u =
      Matrix.blockDiagonal fun z =>
        twoLocalVariableEdgeCharacteristicMatrix z₀ z w u lam := by
  ext ⟨i, z⟩ ⟨j, y⟩
  by_cases hzy : z = y
  · subst y
    fin_cases i <;> fin_cases j <;>
      simp [twoLocalVariableBlockHamiltonianMatrix,
        twoLocalVariableEdgeHamiltonianBlock,
        twoLocalVariableEdgeCharacteristicMatrix,
        Matrix.blockDiagonal_apply, Matrix.scalar_apply,
        ]
    ring
  · have hp : (i, z) ≠ (j, y) := by
      intro h
      exact hzy (congrArg Prod.snd h)
    simp [twoLocalVariableBlockHamiltonianMatrix,
      twoLocalVariableEdgeCharacteristicMatrix,
      Matrix.blockDiagonal_apply, Matrix.scalar_apply,
      hzy, hp]

theorem twoLocalVariableBlockHamiltonian_charpoly_eval_eq_prod {m : ℕ}
    (z₀ : Fin m → Bool) (w u lam : ℂ) :
    (twoLocalVariableBlockHamiltonianMatrix z₀ w u).charpoly.eval lam =
      ∏ z : Fin m → Bool,
        (twoLocalVariableEdgeCharacteristicMatrix
          z₀ z w u lam).det := by
  rw [Matrix.eval_charpoly,
    twoLocalVariableBlockCharacteristicMatrix_eq,
    Matrix.det_blockDiagonal]

/-- Full variable-transverse Hamiltonian in the Boolean computational
basis. -/
def twoLocalVariableStarHamiltonianMatrix {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    Matrix (Bool × (Fin m → Bool))
      (Bool × (Fin m → Bool)) ℂ :=
  fun x y =>
    if x.2 = y.2 then
      if x.1 = y.1 then
        if x.1 then
          -((starIsingBinaryCode z₀ x.2 : ℂ) + w)
        else
          (starIsingBinaryCode z₀ x.2 : ℂ) + w
      else u
    else 0

theorem twoLocalVariableBlock_reindex_eq_star {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    Matrix.reindex (twoLocalFullIndexEquiv m)
        (twoLocalFullIndexEquiv m)
        (twoLocalVariableBlockHamiltonianMatrix z₀ w u) =
      twoLocalVariableStarHamiltonianMatrix z₀ w u := by
  ext ⟨b, z⟩ ⟨d, y⟩
  cases b <;> cases d <;> by_cases hzy : z = y <;>
    simp [Matrix.reindex_apply, twoLocalFullIndexEquiv,
      finTwoEquiv, twoLocalVariableBlockHamiltonianMatrix,
      twoLocalVariableEdgeHamiltonianBlock,
      twoLocalVariableStarHamiltonianMatrix,
      Matrix.blockDiagonal_apply, hzy]

theorem twoLocalVariableStarHamiltonian_charpoly_eval_eq_prod {m : ℕ}
    (z₀ : Fin m → Bool) (w u lam : ℂ) :
    (twoLocalVariableStarHamiltonianMatrix z₀ w u).charpoly.eval lam =
      ∏ z : Fin m → Bool,
        (twoLocalVariableEdgeCharacteristicMatrix
          z₀ z w u lam).det := by
  rw [← twoLocalVariableBlock_reindex_eq_star,
    Matrix.charpoly_reindex,
    twoLocalVariableBlockHamiltonian_charpoly_eval_eq_prod]

theorem twoLocalVariableStar_eq_distinguishedStar {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    ∃ (constant longitudinal : ℂ)
        (onsite interaction : Fin m → ℂ),
      twoLocalVariableStarHamiltonianMatrix z₀ w u =
        distinguishedStarTwoLocalHamiltonian
          constant longitudinal u onsite interaction := by
  rcases twoLocalStarHamiltonian_is_complex_twoLocal z₀ w with
    ⟨constant, longitudinal, _transverse, onsite, interaction, h⟩
  refine ⟨constant, longitudinal, onsite, interaction, ?_⟩
  ext x y
  have hxy := congrFun (congrFun h x) y
  by_cases henv : x.2 = y.2
  · by_cases hbit : x.1 = y.1
    · have hfull : x = y := Prod.ext hbit henv
      subst y
      calc
        twoLocalVariableStarHamiltonianMatrix z₀ w u x x =
            twoLocalStarHamiltonianMatrix z₀ w x x := by
          rcases x with ⟨b, z⟩
          cases b <;>
            simp [twoLocalVariableStarHamiltonianMatrix,
              twoLocalStarHamiltonianMatrix]
        _ = distinguishedStarTwoLocalHamiltonian
            constant longitudinal u onsite interaction x x := by
          simpa [distinguishedStarTwoLocalHamiltonian] using hxy
    · have hne : x ≠ y := fun hxy' => hbit (congrArg Prod.fst hxy')
      simp [twoLocalVariableStarHamiltonianMatrix,
        distinguishedStarTwoLocalHamiltonian, henv, hbit, hne]
  · have hne : x ≠ y := fun hxy' => henv (congrArg Prod.snd hxy')
    simp [twoLocalVariableStarHamiltonianMatrix,
      distinguishedStarTwoLocalHamiltonian, henv, hne]

theorem twoLocalVariableStar_is_complex_twoLocal {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    IsComplexDistinguishedStarTwoLocalHamiltonian
      (twoLocalVariableStarHamiltonianMatrix z₀ w u) := by
  rcases twoLocalVariableStar_eq_distinguishedStar z₀ w u with
    ⟨constant, longitudinal, onsite, interaction, h⟩
  exact ⟨constant, longitudinal, u, onsite, interaction, h⟩

/-! ## A closed loop based at a controllable point -/

/-- Longitudinal part of the diagonal-anchored loop. -/
noncomputable def twoLocalAnchoredLongitudinal (s : I) : ℂ :=
  (Complex.I / 4) * (1 - twoLocalMonodromyPhase s)

/-- Transverse part of the diagonal-anchored loop. -/
noncomputable def twoLocalAnchoredTransverse (s : I) : ℂ :=
  (1 + twoLocalMonodromyPhase s) / 4

theorem continuous_twoLocalAnchoredLongitudinal :
    Continuous twoLocalAnchoredLongitudinal := by
  unfold twoLocalAnchoredLongitudinal
  exact continuous_const.mul
    (continuous_const.sub continuous_twoLocalMonodromyPhase)

theorem continuous_twoLocalAnchoredTransverse :
    Continuous twoLocalAnchoredTransverse := by
  unfold twoLocalAnchoredTransverse
  exact (continuous_const.add
    continuous_twoLocalMonodromyPhase).div_const _

@[simp] theorem twoLocalAnchoredLongitudinal_zero :
    twoLocalAnchoredLongitudinal 0 = 0 := by
  simp [twoLocalAnchoredLongitudinal]

@[simp] theorem twoLocalAnchoredLongitudinal_one :
    twoLocalAnchoredLongitudinal 1 = 0 := by
  simp [twoLocalAnchoredLongitudinal]

@[simp] theorem twoLocalAnchoredTransverse_zero :
    twoLocalAnchoredTransverse 0 = 1 / 2 := by
  simp [twoLocalAnchoredTransverse]
  ring

@[simp] theorem twoLocalAnchoredTransverse_one :
    twoLocalAnchoredTransverse 1 = 1 / 2 := by
  simp [twoLocalAnchoredTransverse]
  ring

theorem abs_twoLocalAnchoredLongitudinal_re_le_quarter (s : I) :
    |(twoLocalAnchoredLongitudinal s).re| ≤ 1 / 4 := by
  have him :=
    Complex.abs_im_le_norm (twoLocalMonodromyPhase s)
  rw [twoLocalMonodromyPhase_norm] at him
  norm_num [twoLocalAnchoredLongitudinal,
    Complex.mul_re, Complex.div_re] at him ⊢
  linarith

theorem twoLocalAnchored_selectedRadicand_eq_phase {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    twoLocalVariableBranchRadicand z₀ z₀
        (twoLocalAnchoredLongitudinal s)
        (twoLocalAnchoredTransverse s) =
      (1 / 4 : ℂ) * twoLocalMonodromyPhase s := by
  simp only [twoLocalVariableBranchRadicand,
    starIsingBinaryCode_self, Nat.cast_zero, zero_add,
    twoLocalAnchoredLongitudinal, twoLocalAnchoredTransverse]
  field_simp
  rw [Complex.I_sq]
  ring

theorem twoLocalAnchoredNonselectedRadicand_re_pos {m : ℕ}
    (z₀ z : Fin m → Bool) (hz : z ≠ z₀) (s : I) :
    0 <
      (twoLocalVariableBranchRadicand z₀ z
        (twoLocalAnchoredLongitudinal s)
        (twoLocalAnchoredTransverse s)).re := by
  let c : ℕ := starIsingBinaryCode z₀ z
  let w : ℂ := twoLocalAnchoredLongitudinal s
  have hcpos : 0 < c := Nat.pos_of_ne_zero (by
    intro hc
    exact hz ((starIsingBinaryCode_eq_zero_iff z₀ z).mp hc))
  have hcOne : (1 : ℝ) ≤ c := by exact_mod_cast hcpos
  have hwAbs : |w.re| ≤ (1 / 4 : ℝ) :=
    abs_twoLocalAnchoredLongitudinal_re_le_quarter s
  have hwLower : -(1 / 4 : ℝ) ≤ w.re := (abs_le.mp hwAbs).1
  have hphaseAbs :
      |(twoLocalMonodromyPhase s).re| ≤ 1 := by
    simpa [twoLocalMonodromyPhase_norm s] using
      Complex.abs_re_le_norm (twoLocalMonodromyPhase s)
  have hphaseLower :
      -(1 : ℝ) ≤ (twoLocalMonodromyPhase s).re :=
    (abs_le.mp hphaseAbs).1
  have hdecomposition :
      twoLocalVariableBranchRadicand z₀ z w
          (twoLocalAnchoredTransverse s) =
        (c : ℂ) ^ (2 : ℕ) + 2 * (c : ℂ) * w +
          (1 / 4 : ℂ) * twoLocalMonodromyPhase s := by
    have hselected :=
      twoLocalAnchored_selectedRadicand_eq_phase z₀ s
    rw [twoLocalVariableBranchRadicand,
      starIsingBinaryCode_self, Nat.cast_zero, zero_add] at hselected
    change
      ((c : ℂ) + w) ^ (2 : ℕ) +
          (twoLocalAnchoredTransverse s) ^ (2 : ℕ) =
        (c : ℂ) ^ (2 : ℕ) + 2 * (c : ℂ) * w +
          (1 / 4 : ℂ) * twoLocalMonodromyPhase s
    rw [← hselected]
    ring
  have hre := congrArg Complex.re hdecomposition
  norm_num [pow_two, Complex.mul_re] at hre
  have hcNonneg : (0 : ℝ) ≤ c := by positivity
  have hcsq : (c : ℝ) ≤ (c : ℝ) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcOne) hcNonneg]
  rw [hre]
  nlinarith

theorem twoLocalAnchoredRadicand_injective {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun z : Fin m → Bool =>
      twoLocalVariableBranchRadicand z₀ z
        (twoLocalAnchoredLongitudinal s)
        (twoLocalAnchoredTransverse s) := by
  intro z y heq
  have hsquare :
      ((starIsingBinaryCode z₀ z : ℂ) +
          twoLocalAnchoredLongitudinal s) ^ (2 : ℕ) =
        ((starIsingBinaryCode z₀ y : ℂ) +
          twoLocalAnchoredLongitudinal s) ^ (2 : ℕ) := by
    simp only [twoLocalVariableBranchRadicand] at heq
    linear_combination heq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hopposite
  · apply starIsingBinaryCode_injective z₀
    have hcast :
        (starIsingBinaryCode z₀ z : ℂ) =
          (starIsingBinaryCode z₀ y : ℂ) := by
      linear_combination hsame
    exact_mod_cast hcast
  · by_contra hzy
    have hcodeNe :
        starIsingBinaryCode z₀ z ≠
          starIsingBinaryCode z₀ y :=
      fun h => hzy (starIsingBinaryCode_injective z₀ h)
    have hsumPos :
        0 <
          starIsingBinaryCode z₀ z +
            starIsingBinaryCode z₀ y := by
      omega
    have hsumOne :
        (1 : ℝ) ≤
          starIsingBinaryCode z₀ z +
            starIsingBinaryCode z₀ y := by
      exact_mod_cast hsumPos
    have hwAbs :=
      abs_twoLocalAnchoredLongitudinal_re_le_quarter s
    have hwLower :
        -(1 / 4 : ℝ) ≤
          (twoLocalAnchoredLongitudinal s).re :=
      (abs_le.mp hwAbs).1
    have hre := congrArg Complex.re hopposite
    norm_num [Complex.add_re] at hre
    linarith

theorem twoLocalAnchoredRadicand_ne_zero {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    twoLocalVariableBranchRadicand z₀ z
      (twoLocalAnchoredLongitudinal s)
      (twoLocalAnchoredTransverse s) ≠ 0 := by
  by_cases hz : z = z₀
  · subst z
    rw [twoLocalAnchored_selectedRadicand_eq_phase]
    exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  · intro hzero
    have hre := congrArg Complex.re hzero
    have hpos :=
      twoLocalAnchoredNonselectedRadicand_re_pos z₀ z hz s
    simp at hre
    linarith

noncomputable def twoLocalAnchoredNonselectedRoot {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) : ℂ :=
  Complex.sqrt
    (twoLocalVariableBranchRadicand z₀ z
      (twoLocalAnchoredLongitudinal s)
      (twoLocalAnchoredTransverse s))

theorem continuous_twoLocalAnchoredNonselectedRoot {m : ℕ}
    (z₀ z : Fin m → Bool) (hz : z ≠ z₀) :
    Continuous (twoLocalAnchoredNonselectedRoot z₀ z) := by
  unfold twoLocalAnchoredNonselectedRoot
  apply Complex.continuousOn_sqrt.comp_continuous
  · unfold twoLocalVariableBranchRadicand
    exact
      ((continuous_const.add
        continuous_twoLocalAnchoredLongitudinal).pow 2).add
          (continuous_twoLocalAnchoredTransverse.pow 2)
  · intro s
    exact Complex.mem_slitPlane_iff.mpr
      (Or.inl
        (twoLocalAnchoredNonselectedRadicand_re_pos z₀ z hz s))

noncomputable def twoLocalAnchoredBaseRoot {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) : ℂ :=
  if z = z₀ then
    twoLocalSelectedEigenvalueLift s
  else
    twoLocalAnchoredNonselectedRoot z₀ z s

theorem continuous_twoLocalAnchoredBaseRoot {m : ℕ}
    (z₀ z : Fin m → Bool) :
    Continuous (twoLocalAnchoredBaseRoot z₀ z) := by
  classical
  change Continuous fun s =>
    if z = z₀ then
      twoLocalSelectedEigenvalueLift s
    else
      twoLocalAnchoredNonselectedRoot z₀ z s
  by_cases hz : z = z₀
  · simpa only [if_pos hz] using
      continuous_twoLocalSelectedEigenvalueLift
  · simpa only [if_neg hz] using
      continuous_twoLocalAnchoredNonselectedRoot z₀ z hz

theorem twoLocalAnchoredBaseRoot_sq {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    (twoLocalAnchoredBaseRoot z₀ z s) ^ (2 : ℕ) =
      twoLocalVariableBranchRadicand z₀ z
        (twoLocalAnchoredLongitudinal s)
        (twoLocalAnchoredTransverse s) := by
  classical
  by_cases hz : z = z₀
  · subst z
    rw [twoLocalAnchoredBaseRoot, if_pos rfl,
      twoLocalAnchored_selectedRadicand_eq_phase]
    unfold twoLocalSelectedEigenvalueLift
    rw [mul_pow]
    norm_num [twoLocalMonodromyPhase, pow_two,
      ← Complex.exp_add]
    congr 1
    ring
  · rw [twoLocalAnchoredBaseRoot, if_neg hz]
    simp [twoLocalAnchoredNonselectedRoot, Complex.sqrt]

theorem twoLocalAnchoredBaseRoot_ne_zero {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    twoLocalAnchoredBaseRoot z₀ z s ≠ 0 := by
  intro hzero
  have hsquare := twoLocalAnchoredBaseRoot_sq z₀ z s
  rw [hzero, zero_pow (by norm_num)] at hsquare
  exact
    (twoLocalAnchoredRadicand_ne_zero z₀ z s) hsquare.symm

noncomputable def twoLocalAnchoredGlobalRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) : ℂ :=
  if x.1 then
    -twoLocalAnchoredBaseRoot z₀ x.2 s
  else
    twoLocalAnchoredBaseRoot z₀ x.2 s

theorem continuous_twoLocalAnchoredGlobalRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    Continuous (twoLocalAnchoredGlobalRoot z₀ x) := by
  rcases x with ⟨b, z⟩
  cases b
  · change Continuous (twoLocalAnchoredBaseRoot z₀ z)
    exact continuous_twoLocalAnchoredBaseRoot z₀ z
  · change Continuous fun s => -twoLocalAnchoredBaseRoot z₀ z s
    exact (continuous_twoLocalAnchoredBaseRoot z₀ z).neg

theorem twoLocalAnchoredGlobalRoot_sq {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) :
    (twoLocalAnchoredGlobalRoot z₀ x s) ^ (2 : ℕ) =
      twoLocalVariableBranchRadicand z₀ x.2
        (twoLocalAnchoredLongitudinal s)
        (twoLocalAnchoredTransverse s) := by
  cases x.1 <;>
    simp [twoLocalAnchoredGlobalRoot,
      twoLocalAnchoredBaseRoot_sq]

theorem twoLocalAnchoredGlobalRoot_fullMatrix_root {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) :
    (twoLocalVariableStarHamiltonianMatrix z₀
      (twoLocalAnchoredLongitudinal s)
      (twoLocalAnchoredTransverse s)).charpoly.eval
        (twoLocalAnchoredGlobalRoot z₀ x s) = 0 := by
  rw [twoLocalVariableStarHamiltonian_charpoly_eval_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ x.2)
  rw [det_twoLocalVariableEdgeCharacteristicMatrix,
    twoLocalAnchoredGlobalRoot_sq]
  ring

theorem twoLocalAnchoredGlobalRoot_injective {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun x : Bool × (Fin m → Bool) =>
      twoLocalAnchoredGlobalRoot z₀ x s := by
  rintro ⟨b, z⟩ ⟨d, y⟩ heq
  have hsq := congrArg (fun q : ℂ => q ^ (2 : ℕ)) heq
  rw [twoLocalAnchoredGlobalRoot_sq,
    twoLocalAnchoredGlobalRoot_sq] at hsq
  have hzy : z = y :=
    twoLocalAnchoredRadicand_injective z₀ s hsq
  subst y
  have hrootNe :=
    twoLocalAnchoredBaseRoot_ne_zero z₀ z s
  cases b <;> cases d
  · rfl
  · exfalso
    simp [twoLocalAnchoredGlobalRoot] at heq
    apply hrootNe
    linear_combination (1 / 2 : ℂ) * heq
  · exfalso
    simp [twoLocalAnchoredGlobalRoot] at heq
    apply hrootNe
    linear_combination (-1 / 2 : ℂ) * heq
  · rfl

theorem twoLocalAnchoredGlobalRoot_endpoint {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    twoLocalAnchoredGlobalRoot z₀ x 1 =
      twoLocalAnchoredGlobalRoot z₀
        (twoLocalSelectedEdgeSwap z₀ x) 0 := by
  rcases x with ⟨b, z⟩
  by_cases hz : z = z₀
  · subst z
    cases b <;>
      simp [twoLocalAnchoredGlobalRoot,
        twoLocalAnchoredBaseRoot,
        twoLocalSelectedEdgeSwap,
        twoLocalSelectedEigenvalueLift_endpoint_swap]
  · cases b <;>
      simp [twoLocalAnchoredGlobalRoot,
        twoLocalAnchoredBaseRoot,
        twoLocalAnchoredNonselectedRoot,
        twoLocalSelectedEdgeSwap, hz]

/-! ## Explicit label-preserving connector to a diagonal Hamiltonian -/

noncomputable def twoLocalDiagonalConnectorLongitudinal (s : I) : ℂ :=
  ((s : ℝ) : ℂ) / 2

noncomputable def twoLocalDiagonalConnectorTransverse (s : I) : ℂ :=
  ((Real.sqrt (1 - (s : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) / 2

theorem continuous_twoLocalDiagonalConnectorLongitudinal :
    Continuous twoLocalDiagonalConnectorLongitudinal := by
  unfold twoLocalDiagonalConnectorLongitudinal
  fun_prop

theorem continuous_twoLocalDiagonalConnectorTransverse :
    Continuous twoLocalDiagonalConnectorTransverse := by
  unfold twoLocalDiagonalConnectorTransverse
  fun_prop

@[simp] theorem twoLocalDiagonalConnectorLongitudinal_zero :
    twoLocalDiagonalConnectorLongitudinal 0 = 0 := by
  simp [twoLocalDiagonalConnectorLongitudinal]

@[simp] theorem twoLocalDiagonalConnectorLongitudinal_one :
    twoLocalDiagonalConnectorLongitudinal 1 = 1 / 2 := by
  simp [twoLocalDiagonalConnectorLongitudinal]

@[simp] theorem twoLocalDiagonalConnectorTransverse_zero :
    twoLocalDiagonalConnectorTransverse 0 = 1 / 2 := by
  norm_num [twoLocalDiagonalConnectorTransverse]

@[simp] theorem twoLocalDiagonalConnectorTransverse_one :
    twoLocalDiagonalConnectorTransverse 1 = 0 := by
  norm_num [twoLocalDiagonalConnectorTransverse]

theorem twoLocalDiagonalConnectorRadicand_eq {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    twoLocalVariableBranchRadicand z₀ z
        (twoLocalDiagonalConnectorLongitudinal s)
        (twoLocalDiagonalConnectorTransverse s) =
      (starIsingBinaryCode z₀ z : ℂ) ^ (2 : ℕ) +
        (starIsingBinaryCode z₀ z : ℂ) * (s : ℝ) +
        1 / 4 := by
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hnonneg : 0 ≤ 1 - (s : ℝ) ^ (2 : ℕ) := by nlinarith
  have hsqrt := Real.sq_sqrt hnonneg
  simp only [pow_two] at hsqrt
  unfold twoLocalVariableBranchRadicand
  unfold twoLocalDiagonalConnectorLongitudinal
    twoLocalDiagonalConnectorTransverse
  apply Complex.ext
  · norm_num [pow_two, Complex.mul_re]
    nlinarith [hsqrt]
  · norm_num [pow_two, Complex.mul_im]

theorem twoLocalDiagonalConnectorRadicand_re_pos {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    0 <
      (twoLocalVariableBranchRadicand z₀ z
        (twoLocalDiagonalConnectorLongitudinal s)
        (twoLocalDiagonalConnectorTransverse s)).re := by
  rw [twoLocalDiagonalConnectorRadicand_eq]
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hc0 : (0 : ℝ) ≤ starIsingBinaryCode z₀ z := by positivity
  norm_num [pow_two, Complex.mul_re]
  positivity

noncomputable def twoLocalDiagonalConnectorBaseRoot {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) : ℂ :=
  Complex.sqrt
    (twoLocalVariableBranchRadicand z₀ z
      (twoLocalDiagonalConnectorLongitudinal s)
      (twoLocalDiagonalConnectorTransverse s))

theorem continuous_twoLocalDiagonalConnectorBaseRoot {m : ℕ}
    (z₀ z : Fin m → Bool) :
    Continuous (twoLocalDiagonalConnectorBaseRoot z₀ z) := by
  unfold twoLocalDiagonalConnectorBaseRoot
  apply Complex.continuousOn_sqrt.comp_continuous
  · unfold twoLocalVariableBranchRadicand
    exact
      ((continuous_const.add
        continuous_twoLocalDiagonalConnectorLongitudinal).pow 2).add
          (continuous_twoLocalDiagonalConnectorTransverse.pow 2)
  · intro s
    exact Complex.mem_slitPlane_iff.mpr
      (Or.inl
        (twoLocalDiagonalConnectorRadicand_re_pos z₀ z s))

theorem twoLocalDiagonalConnectorBaseRoot_sq {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    (twoLocalDiagonalConnectorBaseRoot z₀ z s) ^ (2 : ℕ) =
      twoLocalVariableBranchRadicand z₀ z
        (twoLocalDiagonalConnectorLongitudinal s)
        (twoLocalDiagonalConnectorTransverse s) := by
  simp [twoLocalDiagonalConnectorBaseRoot, Complex.sqrt]

theorem twoLocalDiagonalConnectorBaseRoot_ne_zero {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    twoLocalDiagonalConnectorBaseRoot z₀ z s ≠ 0 := by
  intro hzero
  have hsquare :=
    twoLocalDiagonalConnectorBaseRoot_sq z₀ z s
  rw [hzero, zero_pow (by norm_num)] at hsquare
  have hpos :=
    twoLocalDiagonalConnectorRadicand_re_pos z₀ z s
  have hre := congrArg Complex.re hsquare.symm
  simp at hre
  linarith

noncomputable def twoLocalDiagonalConnectorGlobalRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) : ℂ :=
  if x.1 then
    -twoLocalDiagonalConnectorBaseRoot z₀ x.2 s
  else
    twoLocalDiagonalConnectorBaseRoot z₀ x.2 s

theorem continuous_twoLocalDiagonalConnectorGlobalRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    Continuous (twoLocalDiagonalConnectorGlobalRoot z₀ x) := by
  rcases x with ⟨b, z⟩
  cases b
  · change Continuous (twoLocalDiagonalConnectorBaseRoot z₀ z)
    exact continuous_twoLocalDiagonalConnectorBaseRoot z₀ z
  · change Continuous fun s =>
      -twoLocalDiagonalConnectorBaseRoot z₀ z s
    exact (continuous_twoLocalDiagonalConnectorBaseRoot z₀ z).neg

theorem twoLocalDiagonalConnectorGlobalRoot_sq {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) :
    (twoLocalDiagonalConnectorGlobalRoot z₀ x s) ^ (2 : ℕ) =
      twoLocalVariableBranchRadicand z₀ x.2
        (twoLocalDiagonalConnectorLongitudinal s)
        (twoLocalDiagonalConnectorTransverse s) := by
  cases x.1 <;>
    simp [twoLocalDiagonalConnectorGlobalRoot,
      twoLocalDiagonalConnectorBaseRoot_sq]

theorem twoLocalDiagonalConnectorGlobalRoot_fullMatrix_root {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) :
    (twoLocalVariableStarHamiltonianMatrix z₀
      (twoLocalDiagonalConnectorLongitudinal s)
      (twoLocalDiagonalConnectorTransverse s)).charpoly.eval
        (twoLocalDiagonalConnectorGlobalRoot z₀ x s) = 0 := by
  rw [twoLocalVariableStarHamiltonian_charpoly_eval_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ x.2)
  rw [det_twoLocalVariableEdgeCharacteristicMatrix,
    twoLocalDiagonalConnectorGlobalRoot_sq]
  ring

theorem twoLocalDiagonalConnectorRadicand_injective {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun z : Fin m → Bool =>
      twoLocalVariableBranchRadicand z₀ z
        (twoLocalDiagonalConnectorLongitudinal s)
        (twoLocalDiagonalConnectorTransverse s) := by
  intro z y heq
  change
    twoLocalVariableBranchRadicand z₀ z
        (twoLocalDiagonalConnectorLongitudinal s)
        (twoLocalDiagonalConnectorTransverse s) =
      twoLocalVariableBranchRadicand z₀ y
        (twoLocalDiagonalConnectorLongitudinal s)
        (twoLocalDiagonalConnectorTransverse s) at heq
  rw [twoLocalDiagonalConnectorRadicand_eq,
    twoLocalDiagonalConnectorRadicand_eq] at heq
  let c : ℕ := starIsingBinaryCode z₀ z
  let d : ℕ := starIsingBinaryCode z₀ y
  have hre := congrArg Complex.re heq
  norm_num [pow_two, Complex.mul_re] at hre
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hcd : c = d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hltR : (c : ℝ) < d := by exact_mod_cast hlt
      nlinarith
    · have hgtR : (d : ℝ) < c := by exact_mod_cast hgt
      nlinarith
  exact starIsingBinaryCode_injective z₀ hcd

theorem twoLocalDiagonalConnectorGlobalRoot_injective {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun x : Bool × (Fin m → Bool) =>
      twoLocalDiagonalConnectorGlobalRoot z₀ x s := by
  rintro ⟨b, z⟩ ⟨d, y⟩ heq
  have hsq := congrArg (fun q : ℂ => q ^ (2 : ℕ)) heq
  rw [twoLocalDiagonalConnectorGlobalRoot_sq,
    twoLocalDiagonalConnectorGlobalRoot_sq] at hsq
  have hzy :=
    twoLocalDiagonalConnectorRadicand_injective z₀ s hsq
  change z = y at hzy
  subst y
  have hrootNe :=
    twoLocalDiagonalConnectorBaseRoot_ne_zero z₀ z s
  cases b <;> cases d
  · rfl
  · exfalso
    simp [twoLocalDiagonalConnectorGlobalRoot] at heq
    apply hrootNe
    linear_combination (1 / 2 : ℂ) * heq
  · exfalso
    simp [twoLocalDiagonalConnectorGlobalRoot] at heq
    apply hrootNe
    linear_combination (-1 / 2 : ℂ) * heq
  · rfl

theorem twoLocalAnchoredRoot_eq_connectorRoot_at_zero {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    twoLocalAnchoredGlobalRoot z₀ x 0 =
      twoLocalDiagonalConnectorGlobalRoot z₀ x 0 := by
  rcases x with ⟨b, z⟩
  by_cases hz : z = z₀
  · subst z
    have hsqrtQuarter :
        Complex.sqrt (1 / 4 : ℂ) = 1 / 2 := by
      rw [Complex.sqrt_eq_real_add_ite]
      norm_num
    have hrad :
        twoLocalVariableBranchRadicand z₀ z₀
            (twoLocalDiagonalConnectorLongitudinal 0)
            (twoLocalDiagonalConnectorTransverse 0) =
          (1 / 4 : ℂ) := by
      rw [twoLocalDiagonalConnectorRadicand_eq]
      simp
    have hconnector :
        twoLocalDiagonalConnectorBaseRoot z₀ z₀ 0 =
          1 / 2 := by
      rw [twoLocalDiagonalConnectorBaseRoot, hrad,
        hsqrtQuarter]
    cases b
    · simp only [twoLocalAnchoredGlobalRoot,
        twoLocalDiagonalConnectorGlobalRoot, Bool.false_eq_true,
        ↓reduceIte]
      rw [twoLocalAnchoredBaseRoot, if_pos rfl, hconnector]
      simp [twoLocalSelectedEigenvalueLift]
    · simp only [twoLocalAnchoredGlobalRoot,
        twoLocalDiagonalConnectorGlobalRoot, ↓reduceIte]
      rw [twoLocalAnchoredBaseRoot, if_pos rfl, hconnector]
      simp [twoLocalSelectedEigenvalueLift]
  · cases b <;>
      simp [twoLocalAnchoredGlobalRoot,
        twoLocalAnchoredBaseRoot,
        twoLocalAnchoredNonselectedRoot,
        twoLocalDiagonalConnectorGlobalRoot,
        twoLocalDiagonalConnectorBaseRoot, hz]

/-- Named diagonal energy reached by the controlled connector. -/
noncomputable def twoLocalAnchoredDiagonalEnergy {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) : ℂ :=
  if x.1 then
    -((starIsingBinaryCode z₀ x.2 : ℂ) + 1 / 2)
  else
    (starIsingBinaryCode z₀ x.2 : ℂ) + 1 / 2

theorem twoLocalDiagonalConnectorRoot_at_one {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    twoLocalDiagonalConnectorGlobalRoot z₀ x 1 =
      twoLocalAnchoredDiagonalEnergy z₀ x := by
  rcases x with ⟨b, z⟩
  let a : ℝ := (starIsingBinaryCode z₀ z : ℝ) + 1 / 2
  have hcNonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hsqrt :
      Complex.sqrt ((a : ℂ) ^ (2 : ℕ)) = (a : ℂ) := by
    rw [Complex.sqrt_eq_real_add_ite]
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcNonneg, pow_two,
      Complex.mul_re, Complex.mul_im]
    rw [← pow_two, Real.sqrt_sq hcNonneg]
  have hrad :
      twoLocalVariableBranchRadicand z₀ z
          (twoLocalDiagonalConnectorLongitudinal 1)
          (twoLocalDiagonalConnectorTransverse 1) =
        (a : ℂ) ^ (2 : ℕ) := by
    rw [twoLocalDiagonalConnectorRadicand_eq]
    simp [a]
    ring
  have hbase :
      twoLocalDiagonalConnectorBaseRoot z₀ z 1 = (a : ℂ) := by
    rw [twoLocalDiagonalConnectorBaseRoot, hrad, hsqrt]
  cases b
  · change twoLocalDiagonalConnectorBaseRoot z₀ z 1 =
      (starIsingBinaryCode z₀ z : ℂ) + 1 / 2
    rw [hbase]
    simp [a]
  · change -twoLocalDiagonalConnectorBaseRoot z₀ z 1 =
      -((starIsingBinaryCode z₀ z : ℂ) + 1 / 2)
    rw [hbase]
    simp [a]

theorem twoLocalVariableStar_diagonalAnchor {m : ℕ}
    (z₀ : Fin m → Bool) :
    twoLocalVariableStarHamiltonianMatrix z₀ (1 / 2) 0 =
      Matrix.diagonal (twoLocalAnchoredDiagonalEnergy z₀) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    rcases x with ⟨b, z⟩
    cases b <;>
      simp [twoLocalVariableStarHamiltonianMatrix,
        twoLocalAnchoredDiagonalEnergy,
        ]
  · by_cases henv : x.2 = y.2
    · have hbit : x.1 ≠ y.1 := by
        intro hb
        exact hxy (Prod.ext hb henv)
      simp [twoLocalVariableStarHamiltonianMatrix,
        hxy, henv, hbit]
    · simp [twoLocalVariableStarHamiltonianMatrix,
        hxy, henv]

/-- Controlled local certificate: a closed simple-spectrum two-local loop
performs exactly the selected edge swap, and a simple-spectrum connector
then transports every sheet to its named diagonal computational label. -/
theorem twoLocal_exact_edgeSwap_with_diagonal_label_anchor {m : ℕ}
    (z₀ : Fin m → Bool) :
    (∀ s,
      Function.Injective fun x =>
        twoLocalAnchoredGlobalRoot z₀ x s) ∧
    (∀ x,
      twoLocalAnchoredGlobalRoot z₀ x 1 =
        twoLocalAnchoredGlobalRoot z₀
          (twoLocalSelectedEdgeSwap z₀ x) 0) ∧
    (∀ s,
      Function.Injective fun x =>
        twoLocalDiagonalConnectorGlobalRoot z₀ x s) ∧
    (∀ x,
      twoLocalAnchoredGlobalRoot z₀ x 0 =
        twoLocalDiagonalConnectorGlobalRoot z₀ x 0) ∧
    ∀ x,
      twoLocalDiagonalConnectorGlobalRoot z₀ x 1 =
        twoLocalAnchoredDiagonalEnergy z₀ x := by
  exact
    ⟨twoLocalAnchoredGlobalRoot_injective z₀,
      twoLocalAnchoredGlobalRoot_endpoint z₀,
      twoLocalDiagonalConnectorGlobalRoot_injective z₀,
      twoLocalAnchoredRoot_eq_connectorRoot_at_zero z₀,
      twoLocalDiagonalConnectorRoot_at_one z₀⟩

end GaloisForLFunctions.HTGeometry
