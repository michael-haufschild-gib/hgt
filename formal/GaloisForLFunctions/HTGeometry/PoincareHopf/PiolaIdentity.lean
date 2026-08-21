import GaloisForLFunctions.HTGeometry.PoincareHopf.CofactorPermutation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The Piola identity

For a `C²` map `u : ℝⁿ → ℝⁿ` the rows of the cofactor matrix of its Jacobian are divergence free:
`∑ j, ∂_j (cof (Du))_{i j} = 0`.

The proof differentiates the permutation sum defining the cofactor.  Each term is indexed by a
permutation `σ` with `σ j = i` together with the coordinate `l ≠ j` that the derivative hits; the
map `(σ, l) ↦ (σ ∘ swap (σ⁻¹ i) l, σ⁻¹ i)` is a fixed-point-free involution of that index set which
reverses the sign of the permutation and leaves the term otherwise unchanged, because second
derivatives are symmetric.  Hence the sum vanishes.

This is the analytic engine of degree theory: combined with the row contraction of the cofactor
matrix it writes `(div W) ∘ u · det (Du)` as an honest divergence, which is what makes the
mollified determinant integral independent of the mollifier and invariant under homotopies.
-/

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

open Matrix Finset Equiv

variable {n : ℕ}

section Analytic

variable {u : (Fin n → ℝ) → (Fin n → ℝ)}

/-- The Jacobian matrix of `u` at `x`: `jac u x a b = ∂ u_a / ∂ x_b`. -/
noncomputable def jac (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => fderiv ℝ u x (Pi.single b 1) a

/-- The second derivative entry `∂²u_a / ∂x_c ∂x_b`. -/
noncomputable def hess (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (c b a : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ u) x (Pi.single c 1) (Pi.single b 1) a

/-- The differential of the Jacobian entry `x ↦ jac u x a b`. -/
noncomputable def jacEntryCLM (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (a b : Fin n) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single b (1 : ℝ)))).comp
    (fderiv ℝ (fderiv ℝ u) x)

theorem jacEntryCLM_apply_single (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (a b c : Fin n) :
    jacEntryCLM u x a b (Pi.single c 1) = hess u x c b a := rfl

theorem hasFDerivAt_jacEntry (hu : ContDiff ℝ 2 u) (x : Fin n → ℝ) (a b : Fin n) :
    HasFDerivAt (fun y => jac u y a b) (jacEntryCLM u x a b) x := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x :=
    (h1.differentiable (by simp) x).hasFDerivAt
  exact (ContinuousLinearMap.hasFDerivAt
    (f := (ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single b (1 : ℝ))))).comp x h2

theorem hess_symm (hu : ContDiff ℝ 2 u) (x : Fin n → ℝ) (c b a : Fin n) :
    hess u x c b a = hess u x b c a := by
  have hev : ∀ᶠ y in nhds x, HasFDerivAt u (fderiv ℝ u y) y :=
    Filter.Eventually.of_forall fun y => (hu.differentiable (by norm_num) y).hasFDerivAt
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x :=
    (h1.differentiable (by simp) x).hasFDerivAt
  have := second_derivative_symmetric_of_eventually hev h2 (Pi.single c 1) (Pi.single b 1)
  exact congrFun this a


/-- The differential of the cofactor entry `x ↦ cofSum (jac u x) i j`. -/
noncomputable def cofD (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (i j : Fin n) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i),
    ((Equiv.Perm.sign σ : ℤ) : ℝ) •
      (∑ l ∈ univ.erase j,
        (∏ k ∈ (univ.erase j).erase l, jac u x (σ k) k) • jacEntryCLM u x (σ l) l)

theorem hasFDerivAt_cofSum (hu : ContDiff ℝ 2 u) (x : Fin n → ℝ) (i j : Fin n) :
    HasFDerivAt (fun y => cofSum (jac u y) i j) (cofD u x i j) x := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      HasFDerivAt (fun y => ∏ k ∈ univ.erase j, jac u y (σ k) k)
        (∑ l ∈ univ.erase j,
          (∏ k ∈ (univ.erase j).erase l, jac u x (σ k) k) • jacEntryCLM u x (σ l) l) x :=
    fun σ => HasFDerivAt.finsetProd (fun l _ => hasFDerivAt_jacEntry hu x (σ l) l)
  have hterm : ∀ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i),
      HasFDerivAt (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k ∈ univ.erase j, jac u y (σ k) k)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) •
          (∑ l ∈ univ.erase j,
            (∏ k ∈ (univ.erase j).erase l, jac u x (σ k) k) • jacEntryCLM u x (σ l) l)) x :=
    fun σ _ => (hprod σ).const_mul _
  have hfun : (fun y => cofSum (jac u y) i j)
      = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i),
          (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k ∈ univ.erase j, jac u y (σ k) k) := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hfun, cofD]
  exact HasFDerivAt.sum hterm

theorem cofD_apply_single (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (i j : Fin n) :
    cofD u x i j (Pi.single j 1)
      = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ l ∈ univ.erase j,
              (∏ k ∈ (univ.erase j).erase l, jac u x (σ k) k) * hess u x j l (σ l) := by
  simp [cofD, jacEntryCLM_apply_single]

/-- The summand of the Piola sum, indexed by a permutation and a second coordinate. -/
noncomputable def piolaTerm (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (i : Fin n)
    (p : Equiv.Perm (Fin n) × Fin n) : ℝ :=
  ((Equiv.Perm.sign p.1 : ℤ) : ℝ) *
    ((∏ k ∈ (univ.erase (p.1⁻¹ i)).erase p.2, jac u x (p.1 k) k) *
      hess u x (p.1⁻¹ i) p.2 (p.1 p.2))

theorem sum_cofD_eq_piolaSum (u : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (i : Fin n) :
    ∑ j, cofD u x i j (Pi.single j 1)
      = ∑ p ∈ univ.filter (fun p : Equiv.Perm (Fin n) × Fin n => p.2 ≠ p.1⁻¹ i),
          piolaTerm u x i p := by
  classical
  set G : Equiv.Perm (Fin n) → Fin n → ℝ := fun σ j =>
    ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∑ l ∈ univ.erase j,
        (∏ k ∈ (univ.erase j).erase l, jac u x (σ k) k) * hess u x j l (σ l) with hG
  have step1 : ∑ j, cofD u x i j (Pi.single j 1)
      = ∑ j, ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i), G σ j :=
    Finset.sum_congr rfl fun j _ => cofD_apply_single u x i j
  have step2 : ∑ j, ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i), G σ j
      = ∑ σ : Equiv.Perm (Fin n), G σ (σ⁻¹ i) := by
    have h1 : ∀ j : Fin n,
        (univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i))
          = univ.filter (fun σ : Equiv.Perm (Fin n) => j = σ⁻¹ i) := by
      intro j
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    calc ∑ j, ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i), G σ j
        = ∑ j, ∑ σ : Equiv.Perm (Fin n), if j = σ⁻¹ i then G σ j else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h1 j, Finset.sum_filter]
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ j, if j = σ⁻¹ i then G σ j else 0 := Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (Fin n), G σ (σ⁻¹ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp
  have step3 : ∑ σ : Equiv.Perm (Fin n), G σ (σ⁻¹ i)
      = ∑ p ∈ univ.filter (fun p : Equiv.Perm (Fin n) × Fin n => p.2 ≠ p.1⁻¹ i),
          piolaTerm u x i p := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hG]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_filter, Finset.filter_ne']
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [piolaTerm]
  rw [step1, step2, step3]

/-- **Piola identity.**  For a `C²` map `u`, the rows of the cofactor matrix of the Jacobian of
`u` are divergence free. -/
theorem piola (hu : ContDiff ℝ 2 u) (x : Fin n → ℝ) (i : Fin n) :
    ∑ j, cofD u x i j (Pi.single j 1) = 0 := by
  classical
  rw [sum_cofD_eq_piolaSum]
  set S : Finset (Equiv.Perm (Fin n) × Fin n) :=
    univ.filter (fun p : Equiv.Perm (Fin n) × Fin n => p.2 ≠ p.1⁻¹ i) with hS
  have hmemS : ∀ p : Equiv.Perm (Fin n) × Fin n, p ∈ S ↔ p.2 ≠ p.1⁻¹ i := by
    intro p; simp [hS]
  refine Finset.sum_involution
    (fun p _ => (p.1 * Equiv.swap (p.1⁻¹ i) p.2, p.1⁻¹ i)) ?_ ?_ ?_ ?_
  · rintro ⟨σ, l⟩ hp
    have hne : l ≠ σ⁻¹ i := (hmemS _).mp hp
    have hswapl : (σ * Equiv.swap (σ⁻¹ i) l) l = i := by simp
    have hswapj : (σ * Equiv.swap (σ⁻¹ i) l) (σ⁻¹ i) = σ l := by simp
    have hinv2 : (σ * Equiv.swap (σ⁻¹ i) l)⁻¹ i = l := by rw [← hswapl]; simp
    have hsign : ((Equiv.Perm.sign (σ * Equiv.swap (σ⁻¹ i) l) : ℤ) : ℝ)
        = -((Equiv.Perm.sign σ : ℤ) : ℝ) := by
      rw [map_mul, Equiv.Perm.sign_swap (Ne.symm hne)]
      push_cast
      ring
    have hprodeq : (∏ k ∈ (univ.erase l).erase (σ⁻¹ i),
          jac u x ((σ * Equiv.swap (σ⁻¹ i) l) k) k)
        = ∏ k ∈ (univ.erase (σ⁻¹ i)).erase l, jac u x (σ k) k := by
      rw [Finset.erase_right_comm]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hkl : k ≠ l := (Finset.mem_erase.mp hk).1
      have hkj : k ≠ σ⁻¹ i := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1
      have hsw : Equiv.swap (σ⁻¹ i) l k = k := Equiv.swap_apply_of_ne_of_ne hkj hkl
      rw [Equiv.Perm.mul_apply, hsw]
    simp only [piolaTerm, hinv2, hswapj, hsign, hprodeq]
    rw [hess_symm hu x (σ⁻¹ i) l (σ l)]
    ring
  · rintro ⟨σ, l⟩ hp _
    have hne : l ≠ σ⁻¹ i := (hmemS _).mp hp
    intro hcon
    exact hne (congrArg Prod.snd hcon).symm
  · rintro ⟨σ, l⟩ hp
    have hne : l ≠ σ⁻¹ i := (hmemS _).mp hp
    have hswapl : (σ * Equiv.swap (σ⁻¹ i) l) l = i := by simp
    have hinv2 : (σ * Equiv.swap (σ⁻¹ i) l)⁻¹ i = l := by rw [← hswapl]; simp
    rw [hmemS]
    simp only [hinv2]
    exact fun h => hne h.symm
  · rintro ⟨σ, l⟩ hp
    have hne : l ≠ σ⁻¹ i := (hmemS _).mp hp
    have hswapl : (σ * Equiv.swap (σ⁻¹ i) l) l = i := by simp
    have hinv2 : (σ * Equiv.swap (σ⁻¹ i) l)⁻¹ i = l := by rw [← hswapl]; simp
    have h1 : (σ * Equiv.swap (σ⁻¹ i) l) * Equiv.swap l (σ⁻¹ i) = σ := by
      rw [Equiv.swap_comm l (σ⁻¹ i), mul_assoc, Equiv.swap_mul_self, mul_one]
    simp only [hinv2, h1]

end Analytic

end GaloisForLFunctions.HTGeometry.PoincareHopf
