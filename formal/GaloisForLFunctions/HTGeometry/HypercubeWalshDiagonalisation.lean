import GaloisForLFunctions.HTGeometry.TwoLocalGenericFamily
import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Walsh transform diagonalises the transverse part of a hypercube Hamiltonian

The transverse flips `T_i` of the Boolean hypercube commute and are simultaneously diagonalised by
the Walsh–Hadamard matrix, with eigenvalues `(-1)^{x_i}`.  In the Walsh frame a transverse-field
Hamiltonian `D + ∑_i u_i T_i` is therefore *diagonal plus the rotated diagonal part*, and the
all-zero product state becomes the flat superposition.  That is exactly the configuration in which
`NearDiagonalOverlapFlatness.spectralCollision_le_of_near_diagonal` bounds the spectral collision by
`(2^{-n/2} + 2‖D‖/γ)²`, with `γ` the separation of the transverse energies `∑_i ± u_i`.

## Main results

* `cubeSign`, `walshMatrix` — the Walsh characters of the hypercube and their matrix.
* `sum_cubeSign_mul` — Walsh orthogonality.
* `walshMatrix_mul_self` — the Walsh matrix is an involution.
* `transverseOnly` — the transverse part, split off from `transverseFamilyHam`.
* `transverseFamilyHam_eq_diagonal_add` — the split.
* `conj_walsh_transverseOnly` — **the Walsh frame diagonalises the transverse part.**
-/

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

namespace Walsh

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

variable {n : ℕ}

/-- The sign of one Boolean coordinate: `+1` at `false`, `-1` at `true`. -/
def boolSign (b : Bool) : ℂ := if b then -1 else 1

@[simp] theorem boolSign_false : boolSign false = 1 := rfl
@[simp] theorem boolSign_true : boolSign true = -1 := rfl

theorem boolSign_ne_zero (b : Bool) : boolSign b ≠ 0 := by
  cases b <;> simp [boolSign]

/-- The Walsh character `(-1)^{x·y}` of the Boolean hypercube. -/
def cubeSign (x y : Fin n → Bool) : ℂ := ∏ i, boolSign (x i && y i)

theorem cubeSign_comm (x y : Fin n → Bool) : cubeSign x y = cubeSign y x := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Bool.and_comm]

@[simp] theorem cubeSign_zero_left (y : Fin n → Bool) :
    cubeSign (fun _ => false) y = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  simp [boolSign]

theorem star_cubeSign (x y : Fin n → Bool) : star (cubeSign x y) = cubeSign x y := by
  rw [cubeSign, star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases h : (x i && y i) <;> simp [boolSign]

theorem norm_cubeSign (x y : Fin n → Bool) : ‖cubeSign x y‖ = 1 := by
  rw [cubeSign, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  cases h : (x i && y i) <;> simp [boolSign]

/-- **Walsh orthogonality on the hypercube.** -/
theorem sum_cubeSign_mul (x y : Fin n → Bool) :
    ∑ z : Fin n → Bool, cubeSign x z * cubeSign y z
      = if x = y then ((2 : ℂ) ^ n) else 0 := by
  classical
  have hfac : ∀ z : Fin n → Bool, cubeSign x z * cubeSign y z
      = ∏ i, (boolSign (x i && z i) * boolSign (y i && z i)) := by
    intro z
    rw [cubeSign, cubeSign, ← Finset.prod_mul_distrib]
  have hswap : ∑ z : Fin n → Bool, ∏ i, (boolSign (x i && z i) * boolSign (y i && z i))
      = ∏ i, ∑ b : Bool, (boolSign (x i && b) * boolSign (y i && b)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hcoord : ∀ i : Fin n, ∑ b : Bool, (boolSign (x i && b) * boolSign (y i && b))
      = if x i = y i then (2 : ℂ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hx : x i <;> cases hy : y i <;> norm_num [boolSign]
  rw [Finset.sum_congr rfl (fun z _ => hfac z), hswap,
    Finset.prod_congr rfl (fun i _ => hcoord i)]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Finset.prod_congr rfl (fun i _ => if_pos rfl), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      exact hxy (funext fun i => not_not.mp (fun h => hc ⟨i, h⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The normalisation `2^{-n/2}` of the Walsh matrix. -/
def cubeNorm (n : ℕ) : ℝ := (Real.sqrt ((2 : ℝ) ^ n))⁻¹

theorem cubeNorm_pos (n : ℕ) : 0 < cubeNorm n := by
  rw [cubeNorm]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem cubeNorm_sq (n : ℕ) : cubeNorm n * cubeNorm n = ((2 : ℝ) ^ n)⁻¹ := by
  rw [cubeNorm, ← mul_inv, Real.mul_self_sqrt (by positivity)]

/-- The Walsh–Hadamard matrix of the Boolean hypercube. -/
def walshMatrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.of fun x y => ((cubeNorm n : ℝ) : ℂ) * cubeSign x y

theorem walshMatrix_apply (n : ℕ) (x y : Fin n → Bool) :
    walshMatrix n x y = ((cubeNorm n : ℝ) : ℂ) * cubeSign x y := rfl

theorem walshMatrix_conjTranspose (n : ℕ) : (walshMatrix n)ᴴ = walshMatrix n := by
  ext x y
  rw [Matrix.conjTranspose_apply, walshMatrix_apply, walshMatrix_apply, star_mul',
    star_cubeSign, Complex.star_def, Complex.conj_ofReal, cubeSign_comm, mul_comm]

theorem walshMatrix_mul_self (n : ℕ) : walshMatrix n * walshMatrix n = 1 := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  have hterm : ∀ z : Fin n → Bool, walshMatrix n x z * walshMatrix n z y
      = (((cubeNorm n * cubeNorm n : ℝ)) : ℂ) * (cubeSign x z * cubeSign y z) := by
    intro z
    rw [walshMatrix_apply, walshMatrix_apply, cubeSign_comm z y]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.mul_sum, sum_cubeSign_mul,
    cubeNorm_sq, Matrix.one_apply]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
    push_cast
    field_simp
  · rw [if_neg hxy, if_neg hxy, mul_zero]

theorem walshMatrix_conjTranspose_mul (n : ℕ) : (walshMatrix n)ᴴ * walshMatrix n = 1 := by
  rw [walshMatrix_conjTranspose, walshMatrix_mul_self]

theorem walshMatrix_mul_conjTranspose (n : ℕ) : walshMatrix n * (walshMatrix n)ᴴ = 1 := by
  rw [walshMatrix_conjTranspose, walshMatrix_mul_self]

/-! ### The Walsh frame diagonalises the transverse part -/

theorem norm_walshMatrix (n : ℕ) : ‖walshMatrix n‖ = 1 := by
  have hone : ‖(1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ = 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact norm_one
  have hsq : ‖walshMatrix n‖ * ‖walshMatrix n‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, walshMatrix_conjTranspose_mul, hone]
  nlinarith [norm_nonneg (walshMatrix n), hsq]

/-- The purely transverse part of the hypercube family. -/
def transverseOnly (u : Fin n → ℂ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.of fun x y => ∑ i, if y = boolToggle x i then u i else 0

/-- **The transverse family splits as diagonal plus transverse.** -/
theorem transverseFamilyHam_eq_diagonal_add (d : (Fin n → Bool) → ℂ) (u : Fin n → ℂ) :
    transverseFamilyHam d u = Matrix.diagonal d + transverseOnly u := by
  classical
  ext x y
  rw [transverseFamilyHam, Matrix.add_apply, transverseOnly, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Matrix.diagonal_apply_eq]
    have hzero : ∀ i : Fin n, (if x = boolToggle x i then u i else 0) = 0 := by
      intro i
      rw [if_neg (boolToggle_ne x i)]
    rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const_zero, add_zero]
  · rw [if_neg hxy, Matrix.diagonal_apply_ne _ hxy, zero_add]

/-- The transverse energies `∑_i ± u_i`. -/
def transverseEnergy (u : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, (if x i then -u i else u i)

theorem boolSign_toggle_and (a b : Bool) :
    boolSign ((!a) && b) = boolSign b * boolSign (a && b) := by
  cases a <;> cases b <;> simp [boolSign]

theorem cubeSign_boolToggle (x y : Fin n → Bool) (i : Fin n) :
    cubeSign (boolToggle x i) y = boolSign (y i) * cubeSign x y := by
  classical
  have hsplit : ∀ v : Fin n → Bool,
      cubeSign v y = boolSign (v i && y i) * ∏ j ∈ Finset.univ.erase i, boolSign (v j && y j) := by
    intro v
    rw [cubeSign, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∀ j ∈ Finset.univ.erase i,
      boolSign ((boolToggle x i) j && y j) = boolSign (x j && y j) := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [show (boolToggle x i) j = x j from by simp [boolToggle, Function.update_of_ne hji]]
  have hi : (boolToggle x i) i = !x i := by simp [boolToggle]
  rw [hsplit (boolToggle x i), hsplit x, hi,
    Finset.prod_congr rfl hrest, boolSign_toggle_and]
  ring

/-- **The Walsh matrix diagonalises the transverse part.** -/
theorem transverseOnly_mul_walsh (u : Fin n → ℝ) :
    transverseOnly (fun i => ((u i : ℝ) : ℂ)) * walshMatrix n
      = walshMatrix n * Matrix.diagonal (fun x => ((transverseEnergy u x : ℝ) : ℂ)) := by
  classical
  ext y x
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hLHS : ∑ z, transverseOnly (fun i => ((u i : ℝ) : ℂ)) y z * walshMatrix n z x
      = ∑ i, ((u i : ℝ) : ℂ) * walshMatrix n (boolToggle y i) x := by
    have hexp : ∀ z : Fin n → Bool,
        transverseOnly (fun i => ((u i : ℝ) : ℂ)) y z * walshMatrix n z x
          = ∑ i, (if z = boolToggle y i then ((u i : ℝ) : ℂ) * walshMatrix n z x else 0) := by
      intro z
      rw [transverseOnly, Matrix.of_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : z = boolToggle y i
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl (fun z _ => hexp z), Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq' Finset.univ (boolToggle y i)
      (fun z => ((u i : ℝ) : ℂ) * walshMatrix n z x), if_pos (Finset.mem_univ _)]
  have hRHS : ∑ z, walshMatrix n y z * Matrix.diagonal
      (fun w => ((transverseEnergy u w : ℝ) : ℂ)) z x
      = walshMatrix n y x * ((transverseEnergy u x : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ x) hb
  rw [hLHS, hRHS]
  have hterm : ∀ i : Fin n, ((u i : ℝ) : ℂ) * walshMatrix n (boolToggle y i) x
      = walshMatrix n y x * (((if x i then -u i else u i : ℝ)) : ℂ) := by
    intro i
    rw [walshMatrix_apply, walshMatrix_apply, cubeSign_boolToggle]
    cases hxi : x i <;> simp [boolSign] <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, transverseEnergy,
    Complex.ofReal_sum]

/-! ### Lacunary separation of the transverse energies -/

section Lacunary

variable {w : ℕ → ℝ}

theorem sum_lacunary_le_half (hpos : ∀ i, 0 < w i) (hgrow : ∀ i, 3 * w i ≤ w (i + 1)) :
    ∀ k, ∑ i ∈ Finset.range k, w i ≤ w k / 2 := by
  intro k
  induction k with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      linarith [hpos 0]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith [hgrow k]

theorem lacunary_mono (hpos : ∀ i, 0 < w i) (hgrow : ∀ i, 3 * w i ≤ w (i + 1))
    {a b : ℕ} (hab : a ≤ b) : w a ≤ w b := by
  induction b with
  | zero =>
      have hz : a = 0 := Nat.le_zero.mp hab
      rw [hz]
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · linarith [ih (Nat.lt_succ_iff.mp h), hgrow b, hpos b]
      · have hz : a = b + 1 := le_antisymm hab h
        rw [hz]

/-- **A lacunary signed sum cannot be small.** -/
theorem abs_signed_lacunary_sum_ge (hpos : ∀ i, 0 < w i) (hgrow : ∀ i, 3 * w i ≤ w (i + 1))
    (c : ℕ → ℝ) (hcbound : ∀ i, |c i| ≤ 2) {k : ℕ} (hck : 2 ≤ |c k|) :
    w k ≤ |∑ i ∈ Finset.range (k + 1), c i * w i| := by
  have htail : |∑ i ∈ Finset.range k, c i * w i| ≤ w k := by
    calc |∑ i ∈ Finset.range k, c i * w i|
        ≤ ∑ i ∈ Finset.range k, |c i * w i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range k, 2 * w i := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_pos (hpos i)]
          exact mul_le_mul_of_nonneg_right (hcbound i) (le_of_lt (hpos i))
      _ = 2 * ∑ i ∈ Finset.range k, w i := by rw [Finset.mul_sum]
      _ ≤ w k := by linarith [sum_lacunary_le_half hpos hgrow k]
  have hhead : 2 * w k ≤ |c k * w k| := by
    rw [abs_mul, abs_of_pos (hpos k)]
    exact mul_le_mul_of_nonneg_right hck (le_of_lt (hpos k))
  rw [Finset.sum_range_succ, add_comm]
  have hsplit := abs_sub_abs_le_abs_sub (c k * w k) (-(∑ i ∈ Finset.range k, c i * w i))
  rw [sub_neg_eq_add, abs_neg] at hsplit
  linarith [hsplit, hhead, htail]

end Lacunary

/-- The transverse-energy difference as a signed sum over `ℕ`. -/
theorem transverseEnergy_sub_eq_sum_range {n : ℕ} (w : ℕ → ℝ) (x y : Fin n → Bool) :
    transverseEnergy (fun i : Fin n => w i.val) x
        - transverseEnergy (fun i : Fin n => w i.val) y
      = ∑ i ∈ Finset.range n,
          ((if (∃ h : i < n, x ⟨i, h⟩) then (-1 : ℝ) else 1)
            - (if (∃ h : i < n, y ⟨i, h⟩) then (-1 : ℝ) else 1)) * w i := by
  classical
  rw [transverseEnergy, transverseEnergy, ← Finset.sum_sub_distrib]
  rw [← Fin.sum_univ_eq_sum_range
    (f := fun i : ℕ => ((if (∃ h : i < n, x ⟨i, h⟩) then (-1 : ℝ) else 1)
      - (if (∃ h : i < n, y ⟨i, h⟩) then (-1 : ℝ) else 1)) * w i) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : (∃ h : (i : ℕ) < n, x ⟨(i : ℕ), h⟩) ↔ x i = true := by
    constructor
    · rintro ⟨h, hx⟩
      simpa using hx
    · intro hx
      exact ⟨i.isLt, by simpa using hx⟩
  have hy : (∃ h : (i : ℕ) < n, y ⟨(i : ℕ), h⟩) ↔ y i = true := by
    constructor
    · rintro ⟨h, hy⟩
      simpa using hy
    · intro hy
      exact ⟨i.isLt, by simpa using hy⟩
  by_cases hxb : x i <;> by_cases hyb : y i <;>
    simp [hx, hy, hxb, hyb] <;> ring

/-- **The transverse energies of a lacunary field are separated.** -/
theorem transverseEnergy_separated {n : ℕ} {w : ℕ → ℝ} (hpos : ∀ i, 0 < w i)
    (hgrow : ∀ i, 3 * w i ≤ w (i + 1)) (x y : Fin n → Bool) (hxy : x ≠ y) :
    w 0 ≤ |transverseEnergy (fun i : Fin n => w i.val) x
      - transverseEnergy (fun i : Fin n => w i.val) y| := by
  classical
  set c : ℕ → ℝ := fun i =>
    (if (∃ h : i < n, x ⟨i, h⟩) then (-1 : ℝ) else 1)
      - (if (∃ h : i < n, y ⟨i, h⟩) then (-1 : ℝ) else 1) with hc
  have hxiff : ∀ (i : ℕ) (h : i < n), (∃ h' : i < n, x ⟨i, h'⟩) ↔ x ⟨i, h⟩ = true := by
    intro i h
    constructor
    · rintro ⟨h', hx'⟩
      simpa using hx'
    · intro hx'
      exact ⟨h, by simpa using hx'⟩
  have hyiff : ∀ (i : ℕ) (h : i < n), (∃ h' : i < n, y ⟨i, h'⟩) ↔ y ⟨i, h⟩ = true := by
    intro i h
    constructor
    · rintro ⟨h', hy'⟩
      simpa using hy'
    · intro hy'
      exact ⟨h, by simpa using hy'⟩
  have hcbound : ∀ i, |c i| ≤ 2 := by
    intro i
    rw [hc]
    by_cases h1 : (∃ h : i < n, x ⟨i, h⟩) <;> by_cases h2 : (∃ h : i < n, y ⟨i, h⟩) <;>
      simp [h1, h2] <;> norm_num
  set S : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ y i) with hS
  have hSne : S.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    refine hxy (funext fun i => ?_)
    by_contra hne
    have hmem : i ∈ S := by
      rw [hS]
      simp [hne]
    rw [hcon] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  set k0 : Fin n := S.max' hSne with hk0
  have hk0mem : k0 ∈ S := S.max'_mem hSne
  have hdiff : x k0 ≠ y k0 := by
    have hm := hk0mem
    rw [hS] at hm
    simpa using hm
  have hck : 2 ≤ |c (k0 : ℕ)| := by
    have hx' : (∃ h' : (k0 : ℕ) < n, x ⟨(k0 : ℕ), h'⟩) ↔ x k0 = true :=
      hxiff (k0 : ℕ) k0.isLt
    have hy' : (∃ h' : (k0 : ℕ) < n, y ⟨(k0 : ℕ), h'⟩) ↔ y k0 = true :=
      hyiff (k0 : ℕ) k0.isLt
    have hval : c (k0 : ℕ)
        = (if x k0 = true then (-1 : ℝ) else 1) - (if y k0 = true then (-1 : ℝ) else 1) := by
      show (if (∃ h : (k0 : ℕ) < n, x ⟨(k0 : ℕ), h⟩) then (-1 : ℝ) else 1)
          - (if (∃ h : (k0 : ℕ) < n, y ⟨(k0 : ℕ), h⟩) then (-1 : ℝ) else 1)
        = (if x k0 = true then (-1 : ℝ) else 1) - (if y k0 = true then (-1 : ℝ) else 1)
      simp only [hx', hy']
    rw [hval]
    by_cases hxb : x k0 <;> by_cases hyb : y k0
    · exact absurd (by rw [hxb, hyb]) hdiff
    · norm_num [hxb, hyb]
    · norm_num [hxb, hyb]
    · exact absurd (by simp [hxb, hyb]) hdiff
  have hzero : ∀ i ∈ Finset.range n, i ∉ Finset.range ((k0 : ℕ) + 1) →
      c i * w i = 0 := by
    intro i hi hnot
    rw [Finset.mem_range] at hi
    rw [Finset.mem_range] at hnot
    have hlt : (k0 : ℕ) < i := by omega
    have heq : x ⟨i, hi⟩ = y ⟨i, hi⟩ := by
      by_contra hne
      have hmem : (⟨i, hi⟩ : Fin n) ∈ S := by
        rw [hS]
        simp [hne]
      have hle := S.le_max' _ hmem
      rw [← hk0] at hle
      have hle' : i ≤ (k0 : ℕ) := hle
      omega
    have hczero : c i = 0 := by
      show (if (∃ h : i < n, x ⟨i, h⟩) then (-1 : ℝ) else 1)
          - (if (∃ h : i < n, y ⟨i, h⟩) then (-1 : ℝ) else 1) = 0
      simp only [hxiff i hi, hyiff i hi, heq]
      ring
    rw [hczero, zero_mul]
  have hk0lt : (k0 : ℕ) < n := k0.isLt
  have hsub : Finset.range ((k0 : ℕ) + 1) ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  have hsumeq : ∑ i ∈ Finset.range ((k0 : ℕ) + 1), c i * w i
      = ∑ i ∈ Finset.range n, c i * w i :=
    Finset.sum_subset hsub hzero
  have hkey := abs_signed_lacunary_sum_ge hpos hgrow c hcbound hck
  rw [hsumeq] at hkey
  rw [transverseEnergy_sub_eq_sum_range w x y]
  exact le_trans (lacunary_mono hpos hgrow (Nat.zero_le _)) hkey

end

end Walsh

end GaloisForLFunctions.HTGeometry
