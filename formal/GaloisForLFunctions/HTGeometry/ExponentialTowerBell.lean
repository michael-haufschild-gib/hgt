import GaloisForLFunctions.HTGeometry.ExponentialTowerLowAlgebra

/-!
# Bell iterates for a logarithmically linear element

If `δH = A·H` then every jet of `H` is `H` times a polynomial in the jets of `A`, defined by the Bell
recursion.  For the tower this applies to each monomial with `A` the partial sum below it, so the jets
of a monomial are the monomial times objects of strictly lower index.

This is the decomposition the height induction runs on: the newest variable enters the jets of the
newest partial sum only through the newest monomial, linearly.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The Bell iterates of `A`: `B_0 = 1`, `B_{i+1} = δB_i + A·B_i`. -/
noncomputable def towerBell (A : MvPolynomial ℕ ℂ) : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | (i + 1) => towerDerivation (towerBell A i) + A * towerBell A i

@[simp] theorem towerBell_zero (A : MvPolynomial ℕ ℂ) : towerBell A 0 = 1 := rfl

theorem towerBell_succ (A : MvPolynomial ℕ ℂ) (i : ℕ) :
    towerBell A (i + 1) = towerDerivation (towerBell A i) + A * towerBell A i := rfl

/-- **The jets of a logarithmically linear element.** -/
theorem iterate_towerDerivation_of_logLinear {H A : MvPolynomial ℕ ℂ}
    (hH : towerDerivation H = A * H) (i : ℕ) :
    ((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) H = H * towerBell A i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz, hH, towerBell_succ]
      simp only [smul_eq_mul]
      ring

theorem towerBell_mem_lowAlg {m : ℕ} {A : MvPolynomial ℕ ℂ} (hA : A ∈ lowAlg m) (i : ℕ) :
    towerBell A i ∈ lowAlg m := by
  induction i with
  | zero => simp [towerBell]
  | succ i ih =>
      rw [towerBell_succ]
      exact Subalgebra.add_mem _ (towerDerivation_mem_lowAlg ih) (Subalgebra.mul_mem _ hA ih)

/-! ## The tower decomposition -/

/-- **The jets of a monomial.**  Every jet of `Π_{m+1}` is `Π_{m+1}` times a Bell iterate of the
partial sum below it. -/
theorem iterate_towerMonomial (m i : ℕ) :
    ((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (towerMonomial (m + 1))
      = towerMonomial (m + 1) * towerBell (towerSum m) i := by
  refine iterate_towerDerivation_of_logLinear ?_ i
  rw [towerDerivation_towerMonomial]
  ring

/-- **The jets of a partial sum split off the newest monomial.** -/
theorem iterate_towerSum_succ (m i : ℕ) :
    ((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (towerSum (m + 1))
      = ((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (towerSum m)
        + towerMonomial (m + 1) * towerBell (towerSum m) i := by
  rw [towerSum_succ, ← iterate_towerMonomial m i]
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

/-- The newest variable enters a jet of the newest partial sum only through the newest monomial. -/
theorem pderiv_iterate_towerSum_succ_low {m i j : ℕ} (hj : j ≤ m) :
    (MvPolynomial.pderiv j)
        (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (towerSum (m + 1)))
      = (MvPolynomial.pderiv j)
          (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (towerSum m))
        + MvPolynomial.X (m + 1) *
          (MvPolynomial.pderiv j) (towerMonomial m * towerBell (towerSum m) i) := by
  rw [iterate_towerSum_succ, map_add]
  congr 1
  rw [towerMonomial_succ]
  have hcomm : towerMonomial m * MvPolynomial.X (m + 1) * towerBell (towerSum m) i
      = MvPolynomial.X (m + 1) * (towerMonomial m * towerBell (towerSum m) i) := by ring
  rw [hcomm, Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (by omega : (m + 1) ≠ j)]
  simp

/-- The newest variable's own partial derivative sees only the newest monomial's cofactor. -/
theorem pderiv_iterate_towerSum_succ_top (m i : ℕ) :
    (MvPolynomial.pderiv (m + 1))
        (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (towerSum (m + 1)))
      = towerMonomial m * towerBell (towerSum m) i := by
  rw [iterate_towerSum_succ, map_add]
  have h1 : (MvPolynomial.pderiv (m + 1))
      (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (towerSum m)) = 0 :=
    pderiv_eq_zero_of_mem_lowAlg (by omega)
      (iterate_towerDerivation_mem_lowAlg (towerSum_mem_lowAlg (le_refl m)) i)
  have h2 : (MvPolynomial.pderiv (m + 1)) (towerBell (towerSum m) i) = 0 :=
    pderiv_eq_zero_of_mem_lowAlg (by omega)
      (towerBell_mem_lowAlg (towerSum_mem_lowAlg (le_refl m)) i)
  have h3 : (MvPolynomial.pderiv (m + 1)) (towerMonomial m) = 0 :=
    pderiv_eq_zero_of_mem_lowAlg (by omega) (towerMonomial_mem_lowAlg (le_refl m))
  rw [h1, zero_add, towerMonomial_succ]
  have hcomm : towerMonomial m * MvPolynomial.X (m + 1) * towerBell (towerSum m) i
      = MvPolynomial.X (m + 1) * (towerMonomial m * towerBell (towerSum m) i) := by ring
  rw [hcomm, Derivation.leibniz, MvPolynomial.pderiv_X_self, Derivation.leibniz, h2, h3]
  simp


/-! ## Partial derivatives and the top substitution -/

theorem pderiv_mem_lowAlg {m k : ℕ} {P : MvPolynomial ℕ ℂ} (h : P ∈ lowAlg m) :
    (MvPolynomial.pderiv k) P ∈ lowAlg m := by
  induction h using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨j, _, rfl⟩ := hx
      by_cases hkj : k = j
      · rw [hkj, MvPolynomial.pderiv_X_self]
        exact Subalgebra.one_mem _
      · rw [MvPolynomial.pderiv_X_of_ne (by omega : j ≠ k)]
        exact Subalgebra.zero_mem _
  | algebraMap c =>
      have hc : (algebraMap ℂ (MvPolynomial ℕ ℂ)) c = MvPolynomial.C c := rfl
      rw [hc, MvPolynomial.pderiv_C]
      exact Subalgebra.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
      simp only [Derivation.leibniz, smul_eq_mul]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx ihy) (Subalgebra.mul_mem _ hy ihx)

/-- Substituting a fresh polynomial variable for the model's `(m+1)`-st variable. -/
noncomputable def topSub (m : ℕ) : MvPolynomial ℕ ℂ →ₐ[ℂ] Polynomial (MvPolynomial ℕ ℂ) :=
  MvPolynomial.aeval fun k =>
    if k = m + 1 then Polynomial.X else Polynomial.C (MvPolynomial.X k)

@[simp] theorem topSub_X_top (m : ℕ) :
    topSub m (MvPolynomial.X (m + 1)) = Polynomial.X := by
  simp [topSub]

theorem topSub_X_of_ne {m k : ℕ} (h : k ≠ m + 1) :
    topSub m (MvPolynomial.X k) = Polynomial.C (MvPolynomial.X k) := by
  simp [topSub, h]

/-- **Low objects are constants for the top substitution.** -/
theorem topSub_eq_C {m : ℕ} {P : MvPolynomial ℕ ℂ} (h : P ∈ lowAlg m) :
    topSub m P = Polynomial.C P := by
  induction h using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      have hj' : j ≤ m := hj
      exact topSub_X_of_ne (by omega)
  | algebraMap c =>
      have hc : (algebraMap ℂ (MvPolynomial ℕ ℂ)) c = MvPolynomial.C c := rfl
      rw [hc]
      simp [topSub]
  | add x y hx hy ihx ihy =>
      rw [map_add, ihx, ihy, map_add]
  | mul x y hx hy ihx ihy =>
      rw [map_mul, ihx, ihy, map_mul]

end GaloisForLFunctions.HTGeometry
