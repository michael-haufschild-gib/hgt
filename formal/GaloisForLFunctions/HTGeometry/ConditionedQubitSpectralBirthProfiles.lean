import Mathlib

/-!
# Two exact temporal birth layers in a conditioned qubit spectrum

A qutrit label selects one of three affine qubit blocks.  Two balanced
relations among their exact level splittings are born at different powers
of the same coupling: the first at order one and the second at order two.
The proof uses an exact rationalization of the square root, not a numerical
or asymptotic computation.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive spectral radius of the qubit block with longitudinal
coefficient `c` and transverse coefficient `h`. -/
def conditionedQubitRadius (c h g : ℝ) : ℝ :=
  Real.sqrt ((1 + c * g) ^ 2 + (h * g) ^ 2)

/-- Exact level splitting of one conditioned qubit block. -/
def conditionedQubitSplitting (c h g : ℝ) : ℝ :=
  2 * conditionedQubitRadius c h g

/-- Quadratic remainder after the constant and longitudinal-linear parts
of a conditioned qubit radius are removed. -/
def conditionedQubitRemainder (c h g : ℝ) : ℝ :=
  (conditionedQubitRadius c h g - (1 + c * g)) / g ^ 2

/-- First spectral character: difference of the `(1,1)` and `(0,1)`
conditioned-qubit splittings. -/
def conditionedQubitLayerOneDetuning (g : ℝ) : ℝ :=
  conditionedQubitSplitting 1 1 g -
    conditionedQubitSplitting 0 1 g

/-- Second spectral character: the balanced second difference of the
`(0,1)`, `(1,1)`, and `(2,2)` conditioned-qubit splittings. -/
def conditionedQubitLayerTwoDetuning (g : ℝ) : ℝ :=
  conditionedQubitSplitting 0 1 g -
    2 * conditionedQubitSplitting 1 1 g +
      conditionedQubitSplitting 2 2 g

/-- Every conditioned-qubit radius tends to its uncoupled value one along
positive couplings. -/
theorem conditionedQubitRadius_tendsto_one (c h : ℝ) :
    Tendsto (conditionedQubitRadius c h) (𝓝[>] 0) (𝓝 1) := by
  change
    Tendsto
      (fun g : ℝ =>
        Real.sqrt ((1 + c * g) ^ 2 + (h * g) ^ 2))
      (𝓝[>] 0) (𝓝 1)
  have hi :
      Tendsto
        (fun g : ℝ => (1 + c * g) ^ 2 + (h * g) ^ 2)
        (𝓝[>] 0) (𝓝 1) := by
    have hc :
        ContinuousAt
          (fun g : ℝ => (1 + c * g) ^ 2 + (h * g) ^ 2) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  simpa [Function.comp_def] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hi

/-- Exact square-root rationalization on the physical positive-coupling
ray. -/
theorem conditionedQubitRadius_sub_affine_eq
    {c h g : ℝ} (hc : 0 ≤ c) (hg : 0 < g) :
    conditionedQubitRadius c h g - (1 + c * g) =
      h ^ 2 * g ^ 2 /
        (conditionedQubitRadius c h g + (1 + c * g)) := by
  have hlin : 0 < 1 + c * g := by positivity
  have hins : 0 ≤ (1 + c * g) ^ 2 + (h * g) ^ 2 := by positivity
  have hsqrt :
      (conditionedQubitRadius c h g) ^ 2 =
        (1 + c * g) ^ 2 + (h * g) ^ 2 := by
    simpa [conditionedQubitRadius] using Real.sq_sqrt hins
  have hden :
      conditionedQubitRadius c h g + (1 + c * g) ≠ 0 :=
    ne_of_gt
      (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hlin)
  apply (eq_div_iff hden).2
  nlinarith [sq_nonneg (h * g)]

/-- The exact normalized quadratic remainder tends to `h² / 2`. -/
theorem conditionedQubitRemainder_tendsto
    {c h : ℝ} (hc : 0 ≤ c) :
    Tendsto
      (conditionedQubitRemainder c h)
      (𝓝[>] 0) (𝓝 (h ^ 2 / 2)) := by
  have hlin :
      Tendsto (fun g : ℝ => 1 + c * g) (𝓝[>] 0) (𝓝 1) := by
    have hc' : ContinuousAt (fun g : ℝ => 1 + c * g) 0 := by
      fun_prop
    simpa using hc'.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hden :
      Tendsto
        (fun g =>
          conditionedQubitRadius c h g + (1 + c * g))
        (𝓝[>] 0) (𝓝 2) := by
    convert (conditionedQubitRadius_tendsto_one c h).add hlin using 1
    norm_num
  have hquot :
      Tendsto
        (fun g =>
          h ^ 2 /
            (conditionedQubitRadius c h g + (1 + c * g)))
        (𝓝[>] 0) (𝓝 (h ^ 2 / 2)) :=
    tendsto_const_nhds.div hden (by norm_num)
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  change 0 < g at hg
  have hg0 : g ≠ 0 := ne_of_gt hg
  rw [conditionedQubitRemainder,
    conditionedQubitRadius_sub_affine_eq hc hg]
  field_simp

/-- The first conditioned-qubit spectral relation has exact positive
birth coefficient two at order one. -/
theorem conditionedQubitLayerOne_profile :
    Tendsto
      (fun g => conditionedQubitLayerOneDetuning g / g)
      (𝓝[>] 0) (𝓝 2) := by
  have hg :
      Tendsto (fun g : ℝ => g) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have h11 :=
    conditionedQubitRemainder_tendsto
      (c := 1) (h := 1) (by norm_num)
  have h01 :=
    conditionedQubitRemainder_tendsto
      (c := 0) (h := 1) (by norm_num)
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) :=
    tendsto_const_nhds
  have hcalc :
      Tendsto
        (fun g =>
          2 * (1 + g *
            (conditionedQubitRemainder 1 1 g -
              conditionedQubitRemainder 0 1 g)))
        (𝓝[>] 0) (𝓝 2) := by
    convert (hone.add (hg.mul (h11.sub h01))).const_mul 2 using 1
    norm_num
  apply hcalc.congr'
  filter_upwards [self_mem_nhdsWithin] with g hgpos
  change 0 < g at hgpos
  have hg0 : g ≠ 0 := ne_of_gt hgpos
  unfold conditionedQubitLayerOneDetuning conditionedQubitSplitting
    conditionedQubitRemainder
  field_simp
  ring

/-- The second conditioned-qubit spectral relation has exact positive
birth coefficient three at order two. -/
theorem conditionedQubitLayerTwo_profile :
    Tendsto
      (fun g => conditionedQubitLayerTwoDetuning g / g ^ 2)
      (𝓝[>] 0) (𝓝 3) := by
  have h01 :=
    conditionedQubitRemainder_tendsto
      (c := 0) (h := 1) (by norm_num)
  have h11 :=
    conditionedQubitRemainder_tendsto
      (c := 1) (h := 1) (by norm_num)
  have h22 :=
    conditionedQubitRemainder_tendsto
      (c := 2) (h := 2) (by norm_num)
  have hcalc :
      Tendsto
        (fun g =>
          2 * (conditionedQubitRemainder 0 1 g -
            2 * conditionedQubitRemainder 1 1 g +
              conditionedQubitRemainder 2 2 g))
        (𝓝[>] 0) (𝓝 3) := by
    convert ((h01.sub (h11.const_mul 2)).add h22).const_mul 2 using 1
    norm_num
  apply hcalc.congr'
  filter_upwards [self_mem_nhdsWithin] with g hgpos
  change 0 < g at hgpos
  have hg0 : g ≠ 0 := ne_of_gt hgpos
  unfold conditionedQubitLayerTwoDetuning conditionedQubitSplitting
    conditionedQubitRemainder
  field_simp
  ring

/-! ## Exact Hermitian Hamiltonian realization -/

/-- Real symmetric qubit block embedded in the complex spectral field. -/
def realQubitBlock (b a q : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(b + a : ℂ), (q : ℂ); (q : ℂ), (b - a : ℂ)]

/-- Algebraic positive-branch eigenvector of a real qubit block. -/
def realQubitPlusVector (a q R : ℝ) : Fin 2 → ℂ :=
  ![(R + a : ℂ), (q : ℂ)]

/-- Algebraic negative-branch eigenvector of a real qubit block. -/
def realQubitMinusVector (a q R : ℝ) : Fin 2 → ℂ :=
  ![(-q : ℂ), (R + a : ℂ)]

/-- Positive branch eigen-equation for a real qubit block. -/
theorem realQubitBlock_mulVec_plus
    {b a q R : ℝ} (hR : R ^ 2 = a ^ 2 + q ^ 2) :
    (realQubitBlock b a q).mulVec (realQubitPlusVector a q R) =
      ((b + R : ℝ) : ℂ) • realQubitPlusVector a q R := by
  funext i
  fin_cases i <;>
    simp [realQubitBlock, realQubitPlusVector, Matrix.mulVec]
  · exact_mod_cast (by nlinarith [hR] :
      (b + a) * (R + a) + q * q = (b + R) * (R + a))
  · ring

/-- Negative branch eigen-equation for a real qubit block. -/
theorem realQubitBlock_mulVec_minus
    {b a q R : ℝ} (hR : R ^ 2 = a ^ 2 + q ^ 2) :
    (realQubitBlock b a q).mulVec (realQubitMinusVector a q R) =
      ((b - R : ℝ) : ℂ) • realQubitMinusVector a q R := by
  funext i
  fin_cases i <;>
    simp [realQubitBlock, realQubitMinusVector, Matrix.mulVec]
  · ring
  · exact_mod_cast (by nlinarith [hR] :
      -(q * q) + (b - a) * (R + a) = (b - R) * (R + a))

/-- Direct sum of qubit blocks indexed by a finite sector type. -/
def qubitSectorMatrix
    {S : Type*} [DecidableEq S]
    (B : S → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (S × Fin 2) (S × Fin 2) ℂ :=
  fun x y => if x.1 = y.1 then B x.1 x.2 y.2 else 0

/-- Embed a qubit vector into one direct-sum sector. -/
def qubitSectorEmbed
    {S : Type*} [DecidableEq S]
    (s : S) (v : Fin 2 → ℂ) : S × Fin 2 → ℂ :=
  fun x => if x.1 = s then v x.2 else 0

/-- A block eigenvector remains an eigenvector after sector embedding. -/
theorem qubitSectorMatrix_mulVec_qubitSectorEmbed
    {S : Type*} [Fintype S] [DecidableEq S]
    (B : S → Matrix (Fin 2) (Fin 2) ℂ)
    (s : S) (v : Fin 2 → ℂ) (lam : ℂ)
    (hv : (B s).mulVec v = lam • v) :
    (qubitSectorMatrix B).mulVec (qubitSectorEmbed s v) =
      lam • qubitSectorEmbed s v := by
  funext x
  rcases x with ⟨t, i⟩
  by_cases hts : t = s
  · subst t
    have hi := congrFun hv i
    simpa [qubitSectorMatrix, qubitSectorEmbed, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type] using hi
  · simp [qubitSectorMatrix, qubitSectorEmbed, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, hts]

/-- Sector embedding preserves nonzeroness. -/
theorem qubitSectorEmbed_ne_zero
    {S : Type*} [DecidableEq S]
    (s : S) (v : Fin 2 → ℂ) {i : Fin 2} (hi : v i ≠ 0) :
    qubitSectorEmbed s v ≠ 0 := by
  intro hv
  have hvi := congrFun hv (s, i)
  simp [qubitSectorEmbed] at hvi
  exact hi hvi

/-- Longitudinal coefficients of the three conditioned qubit sectors. -/
def conditionedQubitLongitudinalCoefficient : Fin 3 → ℝ :=
  ![0, 1, 2]

/-- Transverse coefficients of the three conditioned qubit sectors. -/
def conditionedQubitTransverseCoefficient : Fin 3 → ℝ :=
  ![1, 1, 2]

/-- Separated energy offsets; they do not affect the splitting
characters. -/
def conditionedQubitOffset : Fin 3 → ℝ :=
  ![0, 4, 9]

/-- Qubit block selected by sector `s`. -/
def conditionedQubitBlock
    (s : Fin 3) (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  realQubitBlock
    (conditionedQubitOffset s)
    (1 + conditionedQubitLongitudinalCoefficient s * g)
    (conditionedQubitTransverseCoefficient s * g)

/-- The concrete qutrit-conditioned qubit Hamiltonian. -/
def conditionedQubitHamiltonian (g : ℝ) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  qubitSectorMatrix (fun s => conditionedQubitBlock s g)

/-- Positive energy branch in sector `s`. -/
def conditionedQubitEnergyPlus (s : Fin 3) (g : ℝ) : ℝ :=
  conditionedQubitOffset s +
    conditionedQubitRadius
      (conditionedQubitLongitudinalCoefficient s)
      (conditionedQubitTransverseCoefficient s) g

/-- Negative energy branch in sector `s`. -/
def conditionedQubitEnergyMinus (s : Fin 3) (g : ℝ) : ℝ :=
  conditionedQubitOffset s -
    conditionedQubitRadius
      (conditionedQubitLongitudinalCoefficient s)
      (conditionedQubitTransverseCoefficient s) g

/-- Embedded positive-branch eigenvector. -/
def conditionedQubitEigenvectorPlus
    (s : Fin 3) (g : ℝ) : Fin 3 × Fin 2 → ℂ :=
  qubitSectorEmbed s
    (realQubitPlusVector
      (1 + conditionedQubitLongitudinalCoefficient s * g)
      (conditionedQubitTransverseCoefficient s * g)
      (conditionedQubitRadius
        (conditionedQubitLongitudinalCoefficient s)
        (conditionedQubitTransverseCoefficient s) g))

/-- Embedded negative-branch eigenvector. -/
def conditionedQubitEigenvectorMinus
    (s : Fin 3) (g : ℝ) : Fin 3 × Fin 2 → ℂ :=
  qubitSectorEmbed s
    (realQubitMinusVector
      (1 + conditionedQubitLongitudinalCoefficient s * g)
      (conditionedQubitTransverseCoefficient s * g)
      (conditionedQubitRadius
        (conditionedQubitLongitudinalCoefficient s)
        (conditionedQubitTransverseCoefficient s) g))

/-- Exact radius equation for every conditioned-qubit sector. -/
theorem conditionedQubitRadius_sq
    (s : Fin 3) (g : ℝ) :
    conditionedQubitRadius
        (conditionedQubitLongitudinalCoefficient s)
        (conditionedQubitTransverseCoefficient s) g ^ 2 =
      (1 + conditionedQubitLongitudinalCoefficient s * g) ^ 2 +
        (conditionedQubitTransverseCoefficient s * g) ^ 2 := by
  apply Real.sq_sqrt
  positivity

/-- Every conditioned qubit block is Hermitian. -/
theorem conditionedQubitBlock_isHermitian
    (s : Fin 3) (g : ℝ) :
    (conditionedQubitBlock s g).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conditionedQubitBlock, realQubitBlock]

/-- A direct sum of Hermitian qubit blocks is Hermitian. -/
theorem qubitSectorMatrix_isHermitian
    {S : Type*} [Fintype S] [DecidableEq S]
    {B : S → Matrix (Fin 2) (Fin 2) ℂ}
    (hB : ∀ s, (B s).IsHermitian) :
    (qubitSectorMatrix B).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨s, i⟩ ⟨t, j⟩
  by_cases hst : s = t
  · subst t
    simpa [qubitSectorMatrix] using
      (Matrix.IsHermitian.ext_iff.mp (hB s) i j)
  · simp [qubitSectorMatrix, hst, Ne.symm hst]

/-- The complete six-level conditioned-qubit Hamiltonian is Hermitian. -/
theorem conditionedQubitHamiltonian_isHermitian (g : ℝ) :
    (conditionedQubitHamiltonian g).IsHermitian :=
  qubitSectorMatrix_isHermitian fun s =>
    conditionedQubitBlock_isHermitian s g

/-- The complete Hamiltonian is exactly affine in its single physical
coupling. -/
theorem conditionedQubitHamiltonian_affine (g : ℝ) :
    conditionedQubitHamiltonian g =
      conditionedQubitHamiltonian 0 +
        (g : ℂ) •
          (conditionedQubitHamiltonian 1 -
            conditionedQubitHamiltonian 0) := by
  ext x y
  rcases x with ⟨s, i⟩
  rcases y with ⟨t, j⟩
  by_cases hst : s = t
  · subst t
    fin_cases s <;> fin_cases i <;> fin_cases j <;>
      simp [conditionedQubitHamiltonian, qubitSectorMatrix,
        conditionedQubitBlock, realQubitBlock,
        conditionedQubitLongitudinalCoefficient,
        conditionedQubitTransverseCoefficient, conditionedQubitOffset]
    all_goals ring
  · simp [conditionedQubitHamiltonian, qubitSectorMatrix, hst]

/-- Every displayed positive branch satisfies the exact Hamiltonian
eigen-equation. -/
theorem conditionedQubitHamiltonian_mulVec_eigenvectorPlus
    (s : Fin 3) (g : ℝ) :
    (conditionedQubitHamiltonian g).mulVec
        (conditionedQubitEigenvectorPlus s g) =
      ((conditionedQubitEnergyPlus s g : ℝ) : ℂ) •
        conditionedQubitEigenvectorPlus s g := by
  apply qubitSectorMatrix_mulVec_qubitSectorEmbed
  exact realQubitBlock_mulVec_plus (conditionedQubitRadius_sq s g)

/-- Every displayed negative branch satisfies the exact Hamiltonian
eigen-equation. -/
theorem conditionedQubitHamiltonian_mulVec_eigenvectorMinus
    (s : Fin 3) (g : ℝ) :
    (conditionedQubitHamiltonian g).mulVec
        (conditionedQubitEigenvectorMinus s g) =
      ((conditionedQubitEnergyMinus s g : ℝ) : ℂ) •
        conditionedQubitEigenvectorMinus s g := by
  apply qubitSectorMatrix_mulVec_qubitSectorEmbed
  exact realQubitBlock_mulVec_minus (conditionedQubitRadius_sq s g)

/-- Every longitudinal coefficient is nonnegative. -/
theorem conditionedQubitLongitudinalCoefficient_nonneg (s : Fin 3) :
    0 ≤ conditionedQubitLongitudinalCoefficient s := by
  fin_cases s <;>
    norm_num [conditionedQubitLongitudinalCoefficient]

/-- The nonzero component shared by both algebraic eigenvectors is
strictly positive on the physical positive-coupling ray. -/
theorem conditionedQubitRadius_add_longitudinal_pos
    (s : Fin 3) {g : ℝ} (hg : 0 < g) :
    0 <
      conditionedQubitRadius
          (conditionedQubitLongitudinalCoefficient s)
          (conditionedQubitTransverseCoefficient s) g +
        (1 + conditionedQubitLongitudinalCoefficient s * g) := by
  have ha :
      0 < 1 + conditionedQubitLongitudinalCoefficient s * g := by
    have hc := conditionedQubitLongitudinalCoefficient_nonneg s
    positivity
  exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ha

/-- The positive-branch eigenvector is nonzero for every positive
coupling. -/
theorem conditionedQubitEigenvectorPlus_ne_zero
    (s : Fin 3) {g : ℝ} (hg : 0 < g) :
    conditionedQubitEigenvectorPlus s g ≠ 0 := by
  apply qubitSectorEmbed_ne_zero (i := 0)
  have hreal :=
    ne_of_gt (conditionedQubitRadius_add_longitudinal_pos s hg)
  have hcomplex :
      ((conditionedQubitRadius
          (conditionedQubitLongitudinalCoefficient s)
          (conditionedQubitTransverseCoefficient s) g +
        (1 + conditionedQubitLongitudinalCoefficient s * g) : ℝ) : ℂ) ≠
        0 := by
    exact_mod_cast hreal
  simpa [realQubitPlusVector] using hcomplex

/-- The negative-branch eigenvector is nonzero for every positive
coupling. -/
theorem conditionedQubitEigenvectorMinus_ne_zero
    (s : Fin 3) {g : ℝ} (hg : 0 < g) :
    conditionedQubitEigenvectorMinus s g ≠ 0 := by
  apply qubitSectorEmbed_ne_zero (i := 1)
  have hreal :=
    ne_of_gt (conditionedQubitRadius_add_longitudinal_pos s hg)
  have hcomplex :
      ((conditionedQubitRadius
          (conditionedQubitLongitudinalCoefficient s)
          (conditionedQubitTransverseCoefficient s) g +
        (1 + conditionedQubitLongitudinalCoefficient s * g) : ℝ) : ℂ) ≠
        0 := by
    exact_mod_cast hreal
  simpa [realQubitMinusVector] using hcomplex

/-- Sector splitting is exactly the abstract conditioned-qubit splitting
used in the birth-profile theorem. -/
theorem conditionedQubitEnergyPlus_sub_energyMinus
    (s : Fin 3) (g : ℝ) :
    conditionedQubitEnergyPlus s g -
        conditionedQubitEnergyMinus s g =
      conditionedQubitSplitting
        (conditionedQubitLongitudinalCoefficient s)
        (conditionedQubitTransverseCoefficient s) g := by
  simp [conditionedQubitEnergyPlus, conditionedQubitEnergyMinus,
    conditionedQubitSplitting]
  ring

/-- The first abstract detuning is an exact projective relation among
actual Hamiltonian eigenvalue branches. -/
theorem conditionedQubitLayerOne_energyCharacter_eq
    (g : ℝ) :
    (conditionedQubitEnergyPlus 1 g -
        conditionedQubitEnergyMinus 1 g) -
      (conditionedQubitEnergyPlus 0 g -
        conditionedQubitEnergyMinus 0 g) =
      conditionedQubitLayerOneDetuning g := by
  rw [conditionedQubitEnergyPlus_sub_energyMinus,
    conditionedQubitEnergyPlus_sub_energyMinus]
  rfl

/-- The second abstract detuning is an exact projective relation among
actual Hamiltonian eigenvalue branches. -/
theorem conditionedQubitLayerTwo_energyCharacter_eq
    (g : ℝ) :
    (conditionedQubitEnergyPlus 0 g -
        conditionedQubitEnergyMinus 0 g) -
      2 * (conditionedQubitEnergyPlus 1 g -
        conditionedQubitEnergyMinus 1 g) +
      (conditionedQubitEnergyPlus 2 g -
        conditionedQubitEnergyMinus 2 g) =
      conditionedQubitLayerTwoDetuning g := by
  rw [conditionedQubitEnergyPlus_sub_energyMinus,
    conditionedQubitEnergyPlus_sub_energyMinus,
    conditionedQubitEnergyPlus_sub_energyMinus]
  rfl

end

end GaloisForLFunctions.HTGeometry
