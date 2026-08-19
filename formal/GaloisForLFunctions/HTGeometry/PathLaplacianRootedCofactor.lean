import Mathlib

/-!
# Rooted cofactors of the weighted path Laplacian

The difference operator of the path with `n + 1` vertices is the incidence matrix
`(d f) j = f (j + 1) - f j`, and its weighted Hodge Laplacian is `L = a · dᵀ d`.  Deleting the row
and column of one root leaves `a · D_rᵀ D_r`, where `D_r` is the incidence matrix with the root
column removed.  Explicit partial-sum potentials invert `D_r` over `ℤ`, so its determinant is a
unit and

`det (L with root r deleted) = a ^ n`

for every root and every weight.  Summing over the `n + 1` roots gives the marked deformation
`(n + 1) · a ^ n`.  The same partial sums identify the kernel of the differential with the
constants and give the Dirichlet energy identity; a diagonal gauge conjugates every twisted
differential `(d_u f) j = f (j + 1) - u j · f j` to the untwisted one, so unimodular transports
leave every rooted cofactor unchanged.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

section Differential

variable (R : Type*) [CommRing R]

/-- The difference operator of the path with `n + 1` vertices, as an incidence matrix. -/
def pathDifferential (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) R :=
  fun j k => if k = j.castSucc then -1 else if k = j.succ then 1 else 0

/-- Partial sums of an edge function up to a vertex. -/
def pathPartialSum {n : ℕ} (g : Fin n → R) (v : ℕ) : R :=
  ∑ j : Fin n, if (j : ℕ) < v then g j else 0

theorem pathPartialSum_succ {n : ℕ} (g : Fin n → R) (j₀ : Fin n) :
    pathPartialSum R g ((j₀ : ℕ) + 1) = pathPartialSum R g (j₀ : ℕ) + g j₀ := by
  classical
  have hdiff : pathPartialSum R g ((j₀ : ℕ) + 1) - pathPartialSum R g (j₀ : ℕ)
      = ∑ j : Fin n, if j = j₀ then g j else 0 := by
    rw [pathPartialSum, pathPartialSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj
      simp
    · have hne : (j : ℕ) ≠ (j₀ : ℕ) := fun h => hj (Fin.ext h)
      rcases lt_or_gt_of_ne hne with h | h
      · have h1 : (j : ℕ) < (j₀ : ℕ) + 1 := Nat.lt_succ_of_lt h
        simp [h1, h, hj]
      · have h1 : ¬ ((j : ℕ) < (j₀ : ℕ) + 1) := by omega
        have h2 : ¬ ((j : ℕ) < (j₀ : ℕ)) := by omega
        simp [h1, h2, hj]
  rw [Finset.sum_ite_eq' Finset.univ j₀ g] at hdiff
  simp only [Finset.mem_univ, if_true] at hdiff
  linear_combination hdiff

/-- The potential of an edge function, normalized to vanish at the root. -/
def pathPotential {n : ℕ} (r : Fin (n + 1)) (g : Fin n → R) (v : Fin (n + 1)) : R :=
  pathPartialSum R g (v : ℕ) - pathPartialSum R g (r : ℕ)

@[simp]
theorem pathPotential_root {n : ℕ} (r : Fin (n + 1)) (g : Fin n → R) :
    pathPotential R r g r = 0 := by
  simp [pathPotential]

theorem pathDifferential_mulVec {n : ℕ} (f : Fin (n + 1) → R) (j : Fin n) :
    (pathDifferential R n *ᵥ f) j = f j.succ - f j.castSucc := by
  classical
  have hne : (j.castSucc : Fin (n + 1)) ≠ j.succ := (Fin.castSucc_lt_succ (i := j)).ne
  have hterm : ∀ k : Fin (n + 1),
      pathDifferential R n j k * f k
        = (if k = j.castSucc then -f k else 0) + (if k = j.succ then f k else 0) := by
    intro k
    by_cases h1 : k = j.castSucc
    · subst h1
      simp [pathDifferential, hne]
    · by_cases h2 : k = j.succ
      · subst h2
        simp [pathDifferential, h1]
      · simp [pathDifferential, h1, h2]
  have hsum : (pathDifferential R n *ᵥ f) j = ∑ k : Fin (n + 1), pathDifferential R n j k * f k :=
    rfl
  rw [hsum]
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j.castSucc (fun k => -f k),
    Finset.sum_ite_eq' Finset.univ j.succ (fun k => f k)]
  simp
  ring

theorem pathDifferential_mulVec_pathPotential {n : ℕ} (r : Fin (n + 1)) (g : Fin n → R) :
    pathDifferential R n *ᵥ pathPotential R r g = g := by
  funext j
  rw [pathDifferential_mulVec]
  have h1 : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := by simp
  have h2 : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := by simp
  rw [pathPotential, pathPotential, h1, h2, pathPartialSum_succ]
  ring

/-- The kernel of the path differential is exactly the line of constants. -/
theorem pathDifferential_mulVec_eq_zero_iff {n : ℕ} (f : Fin (n + 1) → R) :
    pathDifferential R n *ᵥ f = 0 ↔ ∀ v w : Fin (n + 1), f v = f w := by
  constructor
  · intro h
    have hstep : ∀ j : Fin n, f j.succ = f j.castSucc := by
      intro j
      have hj := congrFun h j
      rw [pathDifferential_mulVec] at hj
      have hz : f j.succ - f j.castSucc = 0 := by simpa using hj
      linear_combination hz
    have hval : ∀ m : ℕ, ∀ hm : m < n + 1, f ⟨m, hm⟩ = f ⟨0, Nat.succ_pos n⟩ := by
      intro m
      induction m with
      | zero => intro hm; rfl
      | succ k ih =>
        intro hm
        have hk : k < n := Nat.succ_lt_succ_iff.mp hm
        have hs := hstep ⟨k, hk⟩
        have hsucc : (⟨k, hk⟩ : Fin n).succ = ⟨k + 1, hm⟩ := rfl
        have hcast : (⟨k, hk⟩ : Fin n).castSucc = ⟨k, Nat.lt_succ_of_lt hk⟩ := rfl
        rw [hsucc, hcast] at hs
        rw [hs]
        exact ih _
    intro v w
    rw [show v = ⟨(v : ℕ), v.isLt⟩ from rfl, show w = ⟨(w : ℕ), w.isLt⟩ from rfl,
      hval _ v.isLt, hval _ w.isLt]
  · intro h
    funext j
    rw [pathDifferential_mulVec, h j.succ j.castSucc]
    simp

/-- The incidence matrix with the root column deleted. -/
def reducedPathDifferential (n : ℕ) (r : Fin (n + 1)) : Matrix (Fin n) (Fin n) R :=
  (pathDifferential R n).submatrix id r.succAbove

/-- The integrator: the root-normalized potential, as a matrix. -/
def reducedPathIntegrator (n : ℕ) (r : Fin (n + 1)) : Matrix (Fin n) (Fin n) R :=
  fun k j => (if (j : ℕ) < ((r.succAbove k : Fin (n + 1)) : ℕ) then 1 else 0)
    - (if (j : ℕ) < (r : ℕ) then 1 else 0)

theorem reducedPathIntegrator_mulVec {n : ℕ} (r : Fin (n + 1)) (g : Fin n → R) :
    reducedPathIntegrator R n r *ᵥ g = fun k => pathPotential R r g (r.succAbove k) := by
  funext k
  have hsum : (reducedPathIntegrator R n r *ᵥ g) k
      = ∑ j : Fin n, reducedPathIntegrator R n r k j * g j := rfl
  rw [hsum, pathPotential, pathPartialSum, pathPartialSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [reducedPathIntegrator]
  by_cases h1 : (j : ℕ) < ((r.succAbove k : Fin (n + 1)) : ℕ) <;>
    by_cases h2 : (j : ℕ) < (r : ℕ) <;> simp [h1, h2]

theorem reducedPathDifferential_mulVec {n : ℕ} (r : Fin (n + 1)) (g : Fin n → R) :
    reducedPathDifferential R n r *ᵥ (fun k => pathPotential R r g (r.succAbove k)) = g := by
  funext j
  have hsum : (reducedPathDifferential R n r *ᵥ fun k => pathPotential R r g (r.succAbove k)) j
      = ∑ k : Fin n, pathDifferential R n j (r.succAbove k)
          * pathPotential R r g (r.succAbove k) := rfl
  have hfull := Fin.sum_univ_succAbove
    (fun v : Fin (n + 1) => pathDifferential R n j v * pathPotential R r g v) r
  have htotal : (∑ v : Fin (n + 1), pathDifferential R n j v * pathPotential R r g v) = g j := by
    have := congrFun (pathDifferential_mulVec_pathPotential R r g) j
    simpa [Matrix.mulVec, dotProduct] using this
  rw [hsum]
  rw [htotal, pathPotential_root] at hfull
  simpa using hfull.symm

theorem reducedPathDifferential_mul_integrator {n : ℕ} (r : Fin (n + 1)) :
    reducedPathDifferential R n r * reducedPathIntegrator R n r = 1 := by
  classical
  have key : ∀ g : Fin n → R,
      (reducedPathDifferential R n r * reducedPathIntegrator R n r) *ᵥ g = g := by
    intro g
    rw [← Matrix.mulVec_mulVec, reducedPathIntegrator_mulVec, reducedPathDifferential_mulVec]
  ext i j
  have h := congrFun (key (Pi.single j 1)) i
  rw [Matrix.mulVec_single] at h
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h

theorem det_reducedPathDifferential_int_sq {n : ℕ} (r : Fin (n + 1)) :
    ((reducedPathDifferential ℤ n r).det) ^ 2 = 1 := by
  have hmul : (reducedPathDifferential ℤ n r).det * (reducedPathIntegrator ℤ n r).det = 1 := by
    rw [← Matrix.det_mul, reducedPathDifferential_mul_integrator, Matrix.det_one]
  have hunit : IsUnit ((reducedPathDifferential ℤ n r).det) :=
    IsUnit.of_mul_eq_one _ hmul
  rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num

theorem reducedPathDifferential_map {n : ℕ} (r : Fin (n + 1)) :
    (reducedPathDifferential ℤ n r).map (Int.cast : ℤ → R) = reducedPathDifferential R n r := by
  ext k j
  by_cases h1 : (r.succAbove j : Fin (n + 1)) = k.castSucc <;>
    by_cases h2 : (r.succAbove j : Fin (n + 1)) = k.succ <;>
      simp [reducedPathDifferential, pathDifferential, h1, h2]

theorem det_reducedPathDifferential_sq {n : ℕ} (r : Fin (n + 1)) :
    ((reducedPathDifferential R n r).det) ^ 2 = 1 := by
  have hmap := reducedPathDifferential_map R (n := n) r
  have hdet : (reducedPathDifferential R n r).det
      = ((reducedPathDifferential ℤ n r).det : ℤ) := by
    rw [← hmap]
    exact (RingHom.map_det (Int.castRingHom R) (reducedPathDifferential ℤ n r)).symm
  rw [hdet, ← Int.cast_pow, det_reducedPathDifferential_int_sq]
  norm_num

end Differential

section Laplacian

variable (R : Type*) [CommRing R]

/-- The weighted Hodge Laplacian `a · dᵀ d` of the path with `n + 1` vertices. -/
def pathLaplacian (a : R) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  a • ((pathDifferential R n)ᵀ * pathDifferential R n)

/-- The rooted Laplacian: the row and the column of the root are deleted. -/
def rootedPathLaplacian (a : R) (n : ℕ) (r : Fin (n + 1)) : Matrix (Fin n) (Fin n) R :=
  (pathLaplacian R a n).submatrix r.succAbove r.succAbove

theorem rootedPathLaplacian_eq (a : R) (n : ℕ) (r : Fin (n + 1)) :
    rootedPathLaplacian R a n r
      = a • ((reducedPathDifferential R n r)ᵀ * reducedPathDifferential R n r) := by
  ext k k'
  simp [rootedPathLaplacian, pathLaplacian, reducedPathDifferential, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.mul_sum]

/-- **Rooted Hodge-cofactor law.**  Every rooted cofactor of the weighted path Laplacian is the
product of the conductances of the `n` path edges. -/
theorem det_rootedPathLaplacian (a : R) (n : ℕ) (r : Fin (n + 1)) :
    (rootedPathLaplacian R a n r).det = a ^ n := by
  rw [rootedPathLaplacian_eq, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose,
    Fintype.card_fin]
  have hsq := det_reducedPathDifferential_sq R (n := n) r
  have hprod : (reducedPathDifferential R n r).det * (reducedPathDifferential R n r).det = 1 := by
    rw [← sq]
    exact hsq
  rw [hprod, mul_one]

/-- **Marked support deformation.**  Summing the rooted cofactors over the `n + 1` roots gives the
positive prime-support deformation. -/
theorem sum_det_rootedPathLaplacian (a : R) (n : ℕ) :
    (∑ r : Fin (n + 1), (rootedPathLaplacian R a n r).det) = ((n : R) + 1) * a ^ n := by
  simp [det_rootedPathLaplacian, Finset.card_univ, add_mul]

end Laplacian

section Energy

/-- **Dirichlet energy identity.**  The Hodge quadratic form of the path Laplacian is the weighted
sum of the squared edge increments. -/
theorem star_dotProduct_pathLaplacian_mulVec (a : ℂ) (n : ℕ) (f : Fin (n + 1) → ℂ) :
    star f ⬝ᵥ (pathLaplacian ℂ a n *ᵥ f)
      = a * ∑ j : Fin n, ((‖f j.succ - f j.castSucc‖ ^ 2 : ℝ) : ℂ) := by
  have hstar : ∀ j : Fin n,
      (pathDifferential ℂ n *ᵥ (star f)) j = star ((pathDifferential ℂ n *ᵥ f) j) := by
    intro j
    rw [pathDifferential_mulVec, pathDifferential_mulVec]
    simp [Pi.star_apply]
  have hexp : star f ⬝ᵥ (pathLaplacian ℂ a n *ᵥ f)
      = a * ∑ j : Fin n, (pathDifferential ℂ n *ᵥ star f) j * (pathDifferential ℂ n *ᵥ f) j := by
    rw [pathLaplacian, smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec]
    congr 1
    rw [dotProduct_mulVec, Matrix.vecMul_transpose]
    rfl
  rw [hexp]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hstar j, pathDifferential_mulVec, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- The Hodge form is nonnegative for nonnegative conductance, and its radical is exactly the line
of constants. -/
theorem pathLaplacian_form_eq_zero_iff (a : ℂ) (ha : a ≠ 0) (n : ℕ) (f : Fin (n + 1) → ℂ) :
    star f ⬝ᵥ (pathLaplacian ℂ a n *ᵥ f) = 0 ↔ ∀ v w : Fin (n + 1), f v = f w := by
  rw [star_dotProduct_pathLaplacian_mulVec, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h ha
    · rw [← pathDifferential_mulVec_eq_zero_iff]
      have hsum : ∑ j : Fin n, ((‖f j.succ - f j.castSucc‖ ^ 2 : ℝ)) = 0 := by
        exact_mod_cast congrArg Complex.re h
      have hzero : ∀ j : Fin n, ‖f j.succ - f j.castSucc‖ ^ 2 = 0 := by
        intro j
        refine (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by positivity).1 hsum j
          (Finset.mem_univ j)
      funext j
      rw [pathDifferential_mulVec]
      have := hzero j
      have hnorm : ‖f j.succ - f j.castSucc‖ = 0 := by
        nlinarith [norm_nonneg (f j.succ - f j.castSucc)]
      simpa using norm_eq_zero.mp hnorm
  · intro h
    right
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h j.succ j.castSucc]
    simp

end Energy

section Twisted

variable (R : Type*) [CommRing R]

/-- The twisted difference operator `(d_u f) j = f (j + 1) - u j · f j`. -/
def twistedPathDifferential (n : ℕ) (u : Fin n → R) : Matrix (Fin n) (Fin (n + 1)) R :=
  fun j k => if k = j.castSucc then -(u j) else if k = j.succ then 1 else 0

/-- The vertex gauge determined by the edge transports: `g 0 = 1` and `g (j + 1) = u j · g j`. -/
def pathGauge {n : ℕ} (u : Fin n → R) (v : Fin (n + 1)) : R :=
  ∏ j : Fin n, if (j : ℕ) < (v : ℕ) then u j else 1

theorem pathGauge_succ {n : ℕ} (u : Fin n → R) (j₀ : Fin n) :
    pathGauge R u j₀.succ = u j₀ * pathGauge R u j₀.castSucc := by
  classical
  have hcast : ((j₀.castSucc : Fin (n + 1)) : ℕ) = (j₀ : ℕ) := by simp
  have hsucc : ((j₀.succ : Fin (n + 1)) : ℕ) = (j₀ : ℕ) + 1 := by simp
  rw [pathGauge, pathGauge, hcast, hsucc]
  have hpoint : u j₀ = ∏ j : Fin n, (if j = j₀ then u j else 1) := by simp
  rw [hpoint, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = j₀
  · subst hj
    simp
  · have hne : (j : ℕ) ≠ (j₀ : ℕ) := fun h => hj (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : (j : ℕ) < (j₀ : ℕ) + 1 := Nat.lt_succ_of_lt h
      simp [h1, h, hj]
    · have h1 : ¬ ((j : ℕ) < (j₀ : ℕ) + 1) := by omega
      have h2 : ¬ ((j : ℕ) < (j₀ : ℕ)) := by omega
      simp [h1, h2, hj]

/-- **Gauge conjugation.**  The diagonal vertex gauge intertwines the twisted differential with the
untwisted one; on a tree the transports carry no invariant information. -/
theorem twistedPathDifferential_mul_diagonal {n : ℕ} (u : Fin n → R) :
    twistedPathDifferential R n u * Matrix.diagonal (pathGauge R u)
      = Matrix.diagonal (fun j : Fin n => pathGauge R u j.succ) * pathDifferential R n := by
  ext j k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h1 : k = j.castSucc
  · subst h1
    rw [pathGauge_succ]
    simp [twistedPathDifferential, pathDifferential]
  · by_cases h2 : k = j.succ
    · subst h2
      simp [twistedPathDifferential, pathDifferential, h1]
    · simp [twistedPathDifferential, pathDifferential, h1, h2]

/-- The twisted incidence matrix with the root column deleted. -/
def reducedTwistedPathDifferential (n : ℕ) (r : Fin (n + 1)) (u : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  (twistedPathDifferential R n u).submatrix id r.succAbove

theorem reducedTwistedPathDifferential_mul_diagonal {n : ℕ} (r : Fin (n + 1)) (u : Fin n → R) :
    reducedTwistedPathDifferential R n r u * Matrix.diagonal (fun k => pathGauge R u (r.succAbove k))
      = Matrix.diagonal (fun j : Fin n => pathGauge R u j.succ) * reducedPathDifferential R n r := by
  ext j k
  have h := congrFun (congrFun (twistedPathDifferential_mul_diagonal R u) j) (r.succAbove k)
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact h

/-- **Phase blindness of the rooted cofactor.**  For every family of transports the twisted rooted
determinant differs from the untwisted one only by the gauge factors; those cancel exactly when
the transports are unimodular. -/
theorem det_reducedTwistedPathDifferential {n : ℕ} (r : Fin (n + 1)) (u : Fin n → R) :
    (reducedTwistedPathDifferential R n r u).det * ∏ k : Fin n, pathGauge R u (r.succAbove k)
      = (∏ j : Fin n, pathGauge R u j.succ) * (reducedPathDifferential R n r).det := by
  have h := congrArg Matrix.det (reducedTwistedPathDifferential_mul_diagonal R r u)
  rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h

end Twisted

section TwistedComplex

/-- The twisted Hodge Laplacian of the path. -/
def twistedPathLaplacian (a : ℂ) (n : ℕ) (u : Fin n → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  a • ((twistedPathDifferential ℂ n u)ᴴ * twistedPathDifferential ℂ n u)

/-- The rooted twisted Laplacian. -/
def rootedTwistedPathLaplacian (a : ℂ) (n : ℕ) (r : Fin (n + 1)) (u : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (twistedPathLaplacian a n u).submatrix r.succAbove r.succAbove

theorem rootedTwistedPathLaplacian_eq (a : ℂ) (n : ℕ) (r : Fin (n + 1)) (u : Fin n → ℂ) :
    rootedTwistedPathLaplacian a n r u
      = a • ((reducedTwistedPathDifferential ℂ n r u)ᴴ * reducedTwistedPathDifferential ℂ n r u) := by
  ext k k'
  simp [rootedTwistedPathLaplacian, twistedPathLaplacian, reducedTwistedPathDifferential,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]

theorem norm_pathGauge_eq_one {n : ℕ} {u : Fin n → ℂ} (hu : ∀ j, ‖u j‖ = 1)
    (v : Fin (n + 1)) : ‖pathGauge ℂ u v‖ = 1 := by
  rw [pathGauge, norm_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  by_cases h : (j : ℕ) < (v : ℕ) <;> simp [h, hu j]

/-- **Unimodular transports leave every rooted Hodge cofactor unchanged.**  The chamber metric of a
flag path is phase blind. -/
theorem det_rootedTwistedPathLaplacian_of_unimodular (a : ℂ) {n : ℕ} (r : Fin (n + 1))
    {u : Fin n → ℂ} (hu : ∀ j, ‖u j‖ = 1) :
    (rootedTwistedPathLaplacian a n r u).det = a ^ n := by
  have hgauge := det_reducedTwistedPathDifferential ℂ r u
  have hprod1 : ‖∏ k : Fin n, pathGauge ℂ u (r.succAbove k)‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun k _ => norm_pathGauge_eq_one hu _
  have hprod2 : ‖∏ j : Fin n, pathGauge ℂ u j.succ‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun j _ => norm_pathGauge_eq_one hu _
  have hdet : ‖(reducedTwistedPathDifferential ℂ n r u).det‖
      = ‖(reducedPathDifferential ℂ n r).det‖ := by
    have := congrArg norm hgauge
    rw [norm_mul, norm_mul, hprod1, hprod2, mul_one, one_mul] at this
    exact this
  have hbase : ‖(reducedPathDifferential ℂ n r).det‖ = 1 := by
    have hsq := det_reducedPathDifferential_sq ℂ (n := n) r
    have : ‖(reducedPathDifferential ℂ n r).det‖ ^ 2 = 1 := by
      rw [← norm_pow, hsq, norm_one]
    nlinarith [norm_nonneg ((reducedPathDifferential ℂ n r).det), this]
  rw [rootedTwistedPathLaplacian_eq, Matrix.det_smul, Matrix.det_mul, Matrix.det_conjTranspose,
    Fintype.card_fin]
  have hmul : star (reducedTwistedPathDifferential ℂ n r u).det
      * (reducedTwistedPathDifferential ℂ n r u).det = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hdet,
      hbase]
    norm_num
  rw [hmul, mul_one]

end TwistedComplex

end GaloisForLFunctions.HTGeometry
