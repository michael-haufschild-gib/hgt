import GaloisForLFunctions.HTGeometry.PoincareTermAppellHumbertDecay
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit
import GaloisForLFunctions.HTGeometry.QuasiAbelianFiniteVanishingDamping

/-!
# Abe positivity as a positive-definite Gram matrix, and the Gaussian lattice majorant

The damping estimate asks for a bound by `polynomialGaussianLatticeWeight`, a product of Gaussians
in the *lattice coordinates*.  What the difference form supplies is a Gaussian in the form value
`D(γ,γ)`.  The bridge is coercivity: on the complement lattice the form is a real quadratic form
whose Gram matrix is `Re D(v_i, v_j)`, and positive definiteness of that matrix — which is exactly
Abe positivity in coordinates — makes the form dominate a positive multiple of `∑ z_i²`.

* `abeGram`, `hermitian_sum_left`, `hermitian_sum_right`, `re_hermitian_latticeSum`;
* `exists_gaussian_of_posDef` — **the Gaussian in the form value dominates a Gaussian in the lattice
  coordinates**;
* `norm_multiIndexJetEvalCLM_le_gaussianLatticeWeight` — **the damping majorant**.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Bilinear

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : V → V → ℂ}

theorem hermitian_sum_left (hH : IsHermitianForm H) {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (u : ι → V) (y : V) : H (∑ i ∈ s, f i • u i) y = ∑ i ∈ s, f i * H (u i) y := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h := hH.add_left 0 0 y
      rw [add_zero] at h
      linear_combination -h
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hH.add_left, hH.smul_left, ih]

theorem hermitian_sum_right (hH : IsHermitianForm H) {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (u : ι → V) (x : V) : H x (∑ j ∈ s, f j • u j) = ∑ j ∈ s, star (f j) * H x (u j) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h := hH.add_right x 0 0
      rw [add_zero] at h
      linear_combination -h
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hH.add_right, hH.smul_right, ih]

end Bilinear

section Gram

variable {d c : ℕ}

/-- The real Gram matrix of a Hermitian form on a complement basis. -/
def abeGram (D : (Fin d → ℂ) → (Fin d → ℂ) → ℂ) (v : Fin c → (Fin d → ℂ)) :
    Matrix (Fin c) (Fin c) ℝ :=
  Matrix.of fun i j => (D (v i) (v j)).re

/-- **The form on a lattice point is the real quadratic form of the Gram matrix.** -/
theorem re_hermitian_latticeSum {D : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} (hD : IsHermitianForm D)
    (v : Fin c → (Fin d → ℂ)) (z : Fin c → ℤ) :
    (D (∑ i, ((z i : ℂ)) • v i) (∑ i, ((z i : ℂ)) • v i)).re
      = (fun i => (z i : ℝ)) ⬝ᵥ (abeGram D v) *ᵥ (fun i => (z i : ℝ)) := by
  rw [hermitian_sum_left hD]
  have hterm : ∀ i : Fin c, ((z i : ℂ)) * D (v i) (∑ j, ((z j : ℂ)) • v j)
      = ∑ j, (((z i : ℝ) * (z j : ℝ) : ℝ) : ℂ) * D (v i) (v j) := by
    intro i
    rw [hermitian_sum_right hD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hstar : star ((z j : ℂ)) = ((z j : ℂ)) := by
      rw [Complex.star_def]
      simp
    rw [hstar, ← mul_assoc]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Complex.re_sum]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul, abeGram]
  simp only [Matrix.of_apply]
  ring

/-- **Abe positivity gives a Gaussian in the lattice coordinates.** -/
theorem exists_gaussian_of_posDef {D : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} (hD : IsHermitianForm D)
    (v : Fin c → (Fin d → ℂ)) (hpos : (abeGram D v).PosDef) {t : ℝ} (ht : 0 < t) :
    ∃ sigma : ℝ, 0 < sigma ∧ ∀ z : Fin c → ℤ,
      Real.exp (-t * (D (∑ i, ((z i : ℂ)) • v i) (∑ i, ((z i : ℂ)) • v i)).re)
        ≤ Real.exp (-sigma * ∑ i, ((z i : ℝ)) ^ 2) := by
  obtain ⟨μ, hμ, hcoer⟩ := posDef_coercive hpos
  refine ⟨t * μ, by positivity, fun z => ?_⟩
  refine Real.exp_le_exp.mpr ?_
  have hq := hcoer (fun i => (z i : ℝ))
  rw [← re_hermitian_latticeSum hD v z] at hq
  have hdot : (fun i => (z i : ℝ)) ⬝ᵥ (fun i => (z i : ℝ)) = ∑ i, ((z i : ℝ)) ^ 2 := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [hdot] at hq
  nlinarith [hq, ht.le]

end Gram

section Majorant

open GaloisForLFunctions

variable {d c : ℕ} {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χu χl : (Fin d → ℂ) → ℂ}

/-- **The damping majorant from Abe positivity.**  A positive-definite Gram matrix of the difference
form on the complement basis converts the Gaussian in the form value into the Gaussian lattice
weight the damping datum asks for. -/
theorem norm_multiIndexJetEvalCLM_le_gaussianLatticeWeight
    (hHu : IsHermitianForm Hu) (hHl : IsHermitianForm Hl)
    (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hpos : ∀ w : Fin d → ℂ, 0 ≤ (Hu w w - Hl w w).re)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : ∀ γ γ' : Fin d → ℂ, χu (γ + γ')
      = χu γ * χu γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hu γ γ').im : ℝ))))
    (seed : MultivariateEntire d) {M : ℝ}
    (hseednorm : ∀ y : Fin d → ℂ, ‖seed.1 y‖ ≤ M * Real.exp (Real.pi / 2 * (Hl y y).re))
    (pt : Fin d → ℂ) (a : Fin d →₀ ℕ) {ρ L : ℝ} (hρ : 0 < ρ)
    (v : Fin c → (Fin d → ℂ))
    (hgram : (abeGram (fun x y => Hu x y - Hl x y) v).PosDef) :
    ∃ sigma : ℝ, 0 < sigma ∧ ∀ (z : Fin c → ℤ) (γ : Γ),
      (γ : Fin d → ℂ) = ∑ i, ((z i : ℂ)) • v i →
      (∀ y : Fin d → ℂ,
        ‖y - pt‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ →
          (Hu y y - Hl y y).re ≤ C₀ ^ 2) →
      (∀ y : Fin d → ℂ,
        ‖y - pt‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ → (Hl y y).re ≤ L) →
      ‖multiIndexJetEvalCLM pt a
          (poincareTermEntire (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) seed γ)‖
        ≤ (M * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2)
              / ρ ^ (Fintype.card (MultiIndexSlot a)))
            * polynomialGaussianLatticeWeight (Fin c) (fun _ => 0) (fun _ => sigma) z := by
  have hD : IsHermitianForm fun x y => Hu x y - Hl x y := hHu.sub hHl
  obtain ⟨sigma, hsigma, hgauss⟩ :=
    exists_gaussian_of_posDef hD v hgram (t := Real.pi / 4) (by positivity)
  refine ⟨sigma, hsigma, fun z γ hγ hzsup hLsup => ?_⟩
  have hM : 0 ≤ M := by
    have h := hseednorm pt
    have h0 : (0 : ℝ) ≤ ‖seed.1 pt‖ := norm_nonneg _
    nlinarith [Real.exp_pos (Real.pi / 2 * (Hl pt pt).re), h, h0]
  have hbase := norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le hHu hHl hχu hpos hC₀
    hsemiu seed hseednorm pt a hρ hzsup hLsup γ
  have hK : 0 ≤ M * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2)
      / ρ ^ (Fintype.card (MultiIndexSlot a)) := by positivity
  have hexp : Real.exp (-(Real.pi / 4) * (Hu γ.1 γ.1 - Hl γ.1 γ.1).re)
      ≤ polynomialGaussianLatticeWeight (Fin c) (fun _ => 0) (fun _ => sigma) z := by
    rw [polynomialGaussianLatticeWeight_zero_exponent]
    have h := hgauss z
    rw [← hγ] at h
    exact h
  exact le_trans hbase (mul_le_mul_of_nonneg_left hexp hK)

end Majorant

end

end GaloisForLFunctions.HTGeometry
