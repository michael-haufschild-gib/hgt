import GaloisForLFunctions.HTGeometry.SteinbergGroupPresentation
import Mathlib.Data.Matrix.Basis

/-!
# Elementary matrices, the elementary group, and `K_2` of a ring

Milnor's definition of `K_2` is the kernel of the map from the Steinberg group to the elementary
group.  This file builds that map: the elementary matrix `1 + a·E_ij` is a unit, and the three
Steinberg relations hold for elementary matrices — additivity of the entry is
`transvection_mul_transvection_same`, and the two commutator relations come from the products of
the single-entry matrices, which vanish or shift according to whether the indices match.

* `elemUnit` : **the elementary matrix as a unit.**
* `transvection_comm`, `transvection_chain` : **the two commutator relations for elementary
  matrices.**
* `steinbergToGL` : **the map from the Steinberg group to the invertible matrices.**
* `elementaryGroup`, `KTwo` : **the elementary group and `K_2`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The elementary matrix as a unit.** -/
def elemUnit {i j : n} (hij : i ≠ j) (a : R) : (Matrix n n R)ˣ where
  val := Matrix.transvection i j a
  inv := Matrix.transvection i j (-a)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same i j hij a (-a), add_neg_cancel,
      Matrix.transvection_zero]
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same i j hij (-a) a, neg_add_cancel,
      Matrix.transvection_zero]

@[simp]
theorem elemUnit_val {i j : n} (hij : i ≠ j) (a : R) :
    (elemUnit hij a : Matrix n n R) = Matrix.transvection i j a := rfl

theorem elemUnit_mul {i j : n} (hij : i ≠ j) (a b : R) :
    elemUnit hij a * elemUnit hij b = elemUnit hij (a + b) := by
  refine Units.ext ?_
  show Matrix.transvection i j a * Matrix.transvection i j b = Matrix.transvection i j (a + b)
  exact Matrix.transvection_mul_transvection_same i j hij a b

/-- **Elementary matrices at disjoint positions commute.** -/
theorem transvection_comm {i j k l : n} (hjk : j ≠ k) (hil : i ≠ l) (a b : R) :
    Matrix.transvection i j a * Matrix.transvection k l b
      = Matrix.transvection k l b * Matrix.transvection i j a := by
  have h1 : (Matrix.single i j a : Matrix n n R) * Matrix.single k l b = 0 := by simp [hjk]
  have h2 : (Matrix.single k l b : Matrix n n R) * Matrix.single i j a = 0 := by
    simp [Ne.symm hil]
  simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    h1, h2]
  abel

/-- **The chained commutator of elementary matrices.** -/
theorem transvection_chain {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    Matrix.transvection i j a * Matrix.transvection j k b * Matrix.transvection i j (-a)
        * Matrix.transvection j k (-b)
      = Matrix.transvection i k (a * b) := by
  have hAB : (Matrix.single i j a : Matrix n n R) * Matrix.single j k b
      = Matrix.single i k (a * b) := by simp
  have hAA : (Matrix.single i j a : Matrix n n R) * Matrix.single i j (-a) = 0 := by
    simp [Ne.symm hij]
  have hBA : (Matrix.single j k b : Matrix n n R) * Matrix.single i j (-a) = 0 := by
    simp [Ne.symm hik]
  have hCA : (Matrix.single i k (a * b) : Matrix n n R) * Matrix.single i j (-a) = 0 := by
    simp [Ne.symm hik]
  have hBB : (Matrix.single j k b : Matrix n n R) * Matrix.single j k (-b) = 0 := by
    simp [Ne.symm hjk]
  have hCB : (Matrix.single i k (a * b) : Matrix n n R) * Matrix.single j k (-b) = 0 := by
    simp [Ne.symm hjk]
  have hAsum : (Matrix.single i j a : Matrix n n R) + Matrix.single i j (-a) = 0 := by
    rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
  have hBsum : (Matrix.single j k b : Matrix n n R) + Matrix.single j k (-b) = 0 := by
    rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
  have step1 : Matrix.transvection i j a * Matrix.transvection j k b
      = 1 + Matrix.single i j a + Matrix.single j k b + Matrix.single i k (a * b) := by
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hAB]
    abel
  have step2 : (1 + Matrix.single i j a + Matrix.single j k b + Matrix.single i k (a * b))
        * Matrix.transvection i j (-a)
      = 1 + Matrix.single j k b + Matrix.single i k (a * b) := by
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hAA, hBA, hCA, add_zero]
    rw [show (1 : Matrix n n R) + Matrix.single i j a + Matrix.single j k b
        + Matrix.single i k (a * b) + Matrix.single i j (-a)
      = 1 + (Matrix.single i j a + Matrix.single i j (-a)) + Matrix.single j k b
        + Matrix.single i k (a * b) from by abel, hAsum, add_zero]
  have step3 : (1 + Matrix.single j k b + Matrix.single i k (a * b))
        * Matrix.transvection j k (-b)
      = Matrix.transvection i k (a * b) := by
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hBB, hCB, add_zero]
    rw [show (1 : Matrix n n R) + Matrix.single j k b + Matrix.single i k (a * b)
        + Matrix.single j k (-b)
      = 1 + (Matrix.single j k b + Matrix.single j k (-b)) + Matrix.single i k (a * b)
        from by abel, hBsum, add_zero]
  rw [step1, step2, step3]


theorem elemUnit_zero {i j : n} (hij : i ≠ j) : elemUnit hij (0 : R) = 1 := by
  refine Units.ext ?_
  show Matrix.transvection i j (0 : R) = 1
  exact Matrix.transvection_zero i j

theorem elemUnit_inv {i j : n} (hij : i ≠ j) (a : R) :
    (elemUnit hij a)⁻¹ = elemUnit hij (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [elemUnit_mul, add_neg_cancel, elemUnit_zero]

theorem elemUnit_commute {i j k l : n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
    (a b : R) : elemUnit hij a * elemUnit hkl b = elemUnit hkl b * elemUnit hij a := by
  refine Units.ext ?_
  exact transvection_comm hjk hil a b

theorem elemUnit_chain {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    elemUnit hij a * elemUnit hjk b * (elemUnit hij a)⁻¹ * (elemUnit hjk b)⁻¹
      = elemUnit hik (a * b) := by
  rw [elemUnit_inv, elemUnit_inv]
  refine Units.ext ?_
  exact transvection_chain hij hjk hik a b


/-- **The map from the Steinberg group to the invertible matrices**, sending a generator to the
corresponding elementary matrix.  It exists because the elementary matrices satisfy Steinberg's
three relations. -/
noncomputable def steinbergToGL : SteinbergGroup R n →* (Matrix n n R)ˣ :=
  PresentedGroup.toGroup (f := fun g : SteinbergGen R n => elemUnit g.hij g.a) (by
    rintro r ((hr | hr) | hr)
    · obtain ⟨i, j, hij, a, b, rfl⟩ := hr
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [elemUnit_mul, mul_inv_cancel]
    · obtain ⟨i, j, k, l, hij, hkl, a, b, hjk, hil, rfl⟩ := hr
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [elemUnit_commute hij hkl hjk hil]
      simp [mul_assoc]
    · obtain ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩ := hr
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [elemUnit_chain hij hjk hik, mul_inv_cancel])

@[simp]
theorem steinbergToGL_x {i j : n} (hij : i ≠ j) (a : R) :
    steinbergToGL (steinbergX hij a) = elemUnit hij a :=
  PresentedGroup.toGroup.of _


variable (R n)

/-- **The elementary group**: the image of the Steinberg group in the invertible matrices. -/
noncomputable def elementaryGroup : Subgroup (Matrix n n R)ˣ :=
  (steinbergToGL (R := R) (n := n)).range

/-- **`K_2` of a ring**: the kernel of the map from the Steinberg group to the invertible
matrices. -/
noncomputable def KTwo : Subgroup (SteinbergGroup R n) :=
  (steinbergToGL (R := R) (n := n)).ker

variable {R n}

theorem mem_KTwo_iff (x : SteinbergGroup R n) :
    x ∈ KTwo R n ↔ steinbergToGL x = 1 := Iff.rfl

theorem elemUnit_mem_elementaryGroup {i j : n} (hij : i ≠ j) (a : R) :
    elemUnit hij a ∈ elementaryGroup R n :=
  ⟨steinbergX hij a, steinbergToGL_x hij a⟩

/-- **`K_2` is a normal subgroup of the Steinberg group.** -/
instance : (KTwo R n).Normal := (steinbergToGL (R := R) (n := n)).normal_ker


/-! ## The Weyl element -/

/-- The Weyl matrix attached to a unit at an off-diagonal position. -/
def weylMatrix (i j : n) (u : Rˣ) : Matrix n n R :=
  1 + Matrix.single i j (u : R) + Matrix.single j i (-((u⁻¹ : Rˣ) : R))
    + Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)

/-- **The Weyl element of the Steinberg group maps to the Weyl matrix.** -/
theorem transvection_weyl {i j : n} (hij : i ≠ j) (u : Rˣ) :
    Matrix.transvection i j (u : R) * Matrix.transvection j i (-((u⁻¹ : Rˣ) : R))
        * Matrix.transvection i j (u : R)
      = weylMatrix i j u := by
  have hAA : (Matrix.single i j (u : R) : Matrix n n R) * Matrix.single i j (u : R) = 0 := by
    simp [Ne.symm hij]
  have hAB : (Matrix.single i j (u : R) : Matrix n n R)
      * Matrix.single j i (-((u⁻¹ : Rˣ) : R)) = Matrix.single i i (-1 : R) := by
    rw [Matrix.single_mul_single_same]
    congr 1
    rw [mul_neg, Units.mul_inv]
  have hBA : (Matrix.single j i (-((u⁻¹ : Rˣ) : R)) : Matrix n n R)
      * Matrix.single i j (u : R) = Matrix.single j j (-1 : R) := by
    rw [Matrix.single_mul_single_same]
    congr 1
    rw [neg_mul, Units.inv_mul]
  have hCA : (Matrix.single i i (-1 : R) : Matrix n n R)
      * Matrix.single i j (u : R) = Matrix.single i j (-(u : R)) := by
    rw [Matrix.single_mul_single_same]
    congr 1
    ring
  have step1 : Matrix.transvection i j (u : R) * Matrix.transvection j i (-((u⁻¹ : Rˣ) : R))
      = 1 + Matrix.single i j (u : R) + Matrix.single j i (-((u⁻¹ : Rˣ) : R))
        + Matrix.single i i (-1 : R) := by
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hAB]
    abel
  rw [step1]
  simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hAA, hBA, hCA, add_zero]
  rw [weylMatrix]
  rw [show (Matrix.single i j (-(u : R)) : Matrix n n R) = -Matrix.single i j (u : R) from by
    rw [← Matrix.single_neg]]
  abel

/-- The diagonal matrix with `u` at `i`, `u⁻¹` at `j`, and ones elsewhere. -/
def diagMatrix (i j : n) (u : Rˣ) : Matrix n n R :=
  1 + Matrix.single i i ((u : R) - 1) + Matrix.single j j (((u⁻¹ : Rˣ) : R) - 1)

theorem weylMatrix_neg_one (i j : n) :
    weylMatrix i j (-1 : Rˣ)
      = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R)
        + Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by
  rw [weylMatrix]
  norm_num


omit [Fintype n] in
theorem single_eq_smul (i j : n) (c : R) :
    (Matrix.single i j c : Matrix n n R) = c • Matrix.single i j (1 : R) := by
  ext p q
  by_cases h1 : i = p <;> by_cases h2 : j = q <;> simp [Matrix.single_apply, h1, h2]

/-- **The Weyl matrix times the Weyl matrix at `-1` is the diagonal matrix.**  In the two-index
block this is `[[0,u],[-u⁻¹,0]]·[[0,-1],[1,0]] = [[u,0],[0,u⁻¹]]`. -/
theorem weylMatrix_mul_neg_one {i j : n} (hij : i ≠ j) (u : Rˣ) :
    weylMatrix i j u * weylMatrix i j (-1 : Rˣ) = diagMatrix i j u := by
  have hji : j ≠ i := Ne.symm hij
  set X : Matrix n n R := Matrix.single i j 1 with hXdef
  set Y : Matrix n n R := Matrix.single j i 1 with hYdef
  set Z : Matrix n n R := Matrix.single i i 1 with hZdef
  set W : Matrix n n R := Matrix.single j j 1 with hWdef
  have hXX : X * X = 0 := by rw [hXdef]; simp [hji]
  have hXY : X * Y = Z := by rw [hXdef, hYdef, hZdef]; simp
  have hXZ : X * Z = 0 := by rw [hXdef, hZdef]; simp [hji]
  have hXW : X * W = X := by rw [hXdef, hWdef]; simp
  have hYX : Y * X = W := by rw [hXdef, hYdef, hWdef]; simp
  have hYY : Y * Y = 0 := by rw [hYdef]; simp [hij]
  have hYZ : Y * Z = Y := by rw [hYdef, hZdef]; simp
  have hYW : Y * W = 0 := by rw [hYdef, hWdef]; simp [hij]
  have hZX : Z * X = X := by rw [hXdef, hZdef]; simp
  have hZY : Z * Y = 0 := by rw [hYdef, hZdef]; simp [hij]
  have hZZ : Z * Z = Z := by rw [hZdef]; simp
  have hZW : Z * W = 0 := by rw [hZdef, hWdef]; simp [hij]
  have hWX : W * X = 0 := by rw [hXdef, hWdef]; simp [hji]
  have hWY : W * Y = Y := by rw [hYdef, hWdef]; simp
  have hWZ : W * Z = 0 := by rw [hZdef, hWdef]; simp [hji]
  have hWW : W * W = W := by rw [hWdef]; simp
  rw [weylMatrix, weylMatrix, diagMatrix]
  rw [single_eq_smul i j (u : R), single_eq_smul j i (-((u⁻¹ : Rˣ) : R)),
    single_eq_smul i i (-1 : R), single_eq_smul j j (-1 : R),
    single_eq_smul i j ((-1 : Rˣ) : R), single_eq_smul j i (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)),
    single_eq_smul i i ((u : R) - 1), single_eq_smul j j (((u⁻¹ : Rˣ) : R) - 1)]
  rw [← hXdef, ← hYdef, ← hZdef, ← hWdef]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hXX, hXY, hXZ, hXW, hYX, hYY, hYZ, hYW,
    hZX, hZY, hZZ, hZW, hWX, hWY, hWZ, hWW, smul_zero]
  have hu : (u : R) * (((u⁻¹ : Rˣ)) : R) = 1 := u.mul_inv
  have hinv : (((-1 : Rˣ)⁻¹ : Rˣ) : R) = -1 := by norm_num
  rw [hinv]
  module


omit [Fintype n] in
theorem diagMatrix_one (i j : n) : diagMatrix i j (1 : Rˣ) = (1 : Matrix n n R) := by
  rw [diagMatrix]
  norm_num

/-- **The diagonal matrices multiply.** -/
theorem diagMatrix_mul {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    diagMatrix i j u * diagMatrix i j v = diagMatrix i j (u * v) := by
  have hji : j ≠ i := Ne.symm hij
  set Z : Matrix n n R := Matrix.single i i 1 with hZdef
  set W : Matrix n n R := Matrix.single j j 1 with hWdef
  have hZZ : Z * Z = Z := by rw [hZdef]; simp
  have hZW : Z * W = 0 := by rw [hZdef, hWdef]; simp [hij]
  have hWZ : W * Z = 0 := by rw [hZdef, hWdef]; simp [hji]
  have hWW : W * W = W := by rw [hWdef]; simp
  rw [diagMatrix, diagMatrix, diagMatrix]
  rw [single_eq_smul i i ((u : R) - 1), single_eq_smul j j (((u⁻¹ : Rˣ) : R) - 1),
    single_eq_smul i i ((v : R) - 1), single_eq_smul j j (((v⁻¹ : Rˣ) : R) - 1),
    single_eq_smul i i (((u * v : Rˣ) : R) - 1),
    single_eq_smul j j ((((u * v : Rˣ)⁻¹ : Rˣ) : R) - 1)]
  rw [← hZdef, ← hWdef]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hZZ, hZW, hWZ, hWW, smul_zero]
  have hprod : ((u * v : Rˣ) : R) = (u : R) * (v : R) := rfl
  have hinvprod : (((u * v : Rˣ)⁻¹ : Rˣ) : R) = ((u⁻¹ : Rˣ) : R) * ((v⁻¹ : Rˣ) : R) := by
    rw [mul_inv]
    exact rfl
  rw [hprod, hinvprod]
  module


/-- The diagonal matrix as a unit. -/
def diagUnit {i j : n} (hij : i ≠ j) (u : Rˣ) : (Matrix n n R)ˣ where
  val := diagMatrix i j u
  inv := diagMatrix i j u⁻¹
  val_inv := by rw [diagMatrix_mul hij, mul_inv_cancel, diagMatrix_one]
  inv_val := by rw [diagMatrix_mul hij, inv_mul_cancel, diagMatrix_one]

theorem diagUnit_mul {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    diagUnit hij u * diagUnit hij v = diagUnit hij (u * v) :=
  Units.ext (diagMatrix_mul hij u v)

/-- The Weyl element of the Steinberg group. -/
def steinbergWeyl {i j : n} (hij : i ≠ j) (u : Rˣ) : SteinbergGroup R n :=
  steinbergX hij (u : R) * steinbergX (Ne.symm hij) (-((u⁻¹ : Rˣ) : R)) * steinbergX hij (u : R)

/-- The torus element of the Steinberg group. -/
def steinbergTorus {i j : n} (hij : i ≠ j) (u : Rˣ) : SteinbergGroup R n :=
  steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ)

/-- **The Steinberg symbol.** -/
def steinbergSymbol {i j : n} (hij : i ≠ j) (u v : Rˣ) : SteinbergGroup R n :=
  steinbergTorus hij (u * v) * (steinbergTorus hij u)⁻¹ * (steinbergTorus hij v)⁻¹

theorem steinbergToGL_weyl {i j : n} (hij : i ≠ j) (u : Rˣ) :
    ((steinbergToGL (steinbergWeyl hij u) : (Matrix n n R)ˣ) : Matrix n n R)
      = weylMatrix i j u := by
  rw [steinbergWeyl, map_mul, map_mul, steinbergToGL_x, steinbergToGL_x,
    Units.val_mul, Units.val_mul, elemUnit_val, elemUnit_val]
  exact transvection_weyl hij u

theorem steinbergToGL_torus {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergToGL (steinbergTorus hij u) = diagUnit hij u := by
  refine Units.ext ?_
  rw [steinbergTorus, map_mul, Units.val_mul, steinbergToGL_weyl, steinbergToGL_weyl]
  exact weylMatrix_mul_neg_one hij u

/-- **The Steinberg symbol lies in `K_2`.** -/
theorem steinbergSymbol_mem_KTwo {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    steinbergSymbol hij u v ∈ KTwo R n := by
  rw [mem_KTwo_iff, steinbergSymbol, map_mul, map_mul, map_inv, map_inv,
    steinbergToGL_torus, steinbergToGL_torus, steinbergToGL_torus, ← diagUnit_mul hij]
  have hcomm : diagUnit hij u * diagUnit hij v = diagUnit hij v * diagUnit hij u := by
    rw [diagUnit_mul, diagUnit_mul, mul_comm]
  rw [hcomm]
  simp [mul_assoc]


/-! ## The abelian column subgroups -/

/-- **Two elementary matrices with the same second index multiply by adding their entries.** -/
theorem transvection_col_mul {k l j : n} (hlj : l ≠ j) (a b : R) :
    Matrix.transvection k j a * Matrix.transvection l j b
      = 1 + Matrix.single k j a + Matrix.single l j b := by
  have h0 : (Matrix.single k j a : Matrix n n R) * Matrix.single l j b = 0 := by
    simp [Ne.symm hlj]
  simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, h0]
  abel

/-- **Elementary matrices with a common second index commute.** -/
theorem transvection_col_comm {k l j : n} (hkj : k ≠ j) (hlj : l ≠ j) (a b : R) :
    Matrix.transvection k j a * Matrix.transvection l j b
      = Matrix.transvection l j b * Matrix.transvection k j a := by
  rw [transvection_col_mul hlj, transvection_col_mul hkj]
  abel


omit [Fintype n] in
theorem single_col_apply {j : n} (b : n → R) (p k : n) :
    (Matrix.single k j (b k) : Matrix n n R) p j = if k = p then b k else 0 := by
  by_cases h : k = p <;> simp [Matrix.single_apply, h]

/-- **The `(p, j)` entry of a column sum is the `p`-th coefficient.** -/
theorem sum_single_col_apply {j : n} (b : n → R) (p : n) :
    (∑ k, Matrix.single k j (b k) : Matrix n n R) p j = b p := by
  classical
  rw [Matrix.sum_apply]
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => single_col_apply b p k)]
  rw [Finset.sum_ite_eq' Finset.univ p (fun k => b k), if_pos (Finset.mem_univ p)]

/-- **A column sum vanishes only if all its coefficients do.**  This is the injectivity that turns
"same image in the matrices" into "equal" for the abelian column subgroups. -/
theorem sum_single_col_eq_zero_iff {j : n} (b : n → R) :
    (∑ k, Matrix.single k j (b k) : Matrix n n R) = 0 ↔ ∀ k, b k = 0 := by
  constructor
  · intro h k
    rw [← sum_single_col_apply b k, h]
    simp
  · intro h
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [h k, Matrix.single_zero]


end GaloisForLFunctions.HTGeometry
