import GaloisForLFunctions.RHTower.Deninger.DeningerGaussianEndpointCore
import GaloisForLFunctions.RHTower.Deninger.DeningerJetInterpolation

/-!
# Finite-jet universality of the endpoint-corrected Gaussian core

Every exponential polynomial of the source core is a polynomial in `e^{-δ s}`, so its jets are the
Euler jets of that polynomial at the exponential images of the nodes.  Choosing the shift so that
the exponential is injective on the nodes together with `0` and `1`, Hermite interpolation for the
Euler operator produces a polynomial with the prescribed jets and with zeros at the two endpoint
images.  Reading its coefficients as Gaussian widths `μ_j = e^{jδ}` gives an endpoint-corrected
Gaussian combination realizing the prescribed jets.

* `deningerExpPoly_eq_eval` : an exponential polynomial is a polynomial in `e^{-δ s}`.
* `deningerGaussianJet_universality` : the universality theorem.
-/

namespace RHTower

open Polynomial Complex

section Universality

/-- **An exponential polynomial with geometric widths is a polynomial in the exponential.** -/
theorem deningerExpPoly_eq_eval (δ : ℝ) (P : ℂ[X]) :
    deningerExpPoly (fun j : Fin (P.natDegree + 1) => P.coeff (j : ℕ))
        (fun j : Fin (P.natDegree + 1) => Real.exp ((j : ℕ) * δ))
      = fun s => P.eval (Complex.exp (-(δ : ℂ) * s)) := by
  funext s
  rw [deningerExpPoly, Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpos : (0 : ℝ) < Real.exp ((j : ℕ) * δ) := Real.exp_pos _
  have hne : ((Real.exp ((j : ℕ) * δ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (le_of_lt hpos), Real.log_exp,
    ← Complex.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- **Finite-jet universality of the source core.**  For any finite family of distinct nodes
avoiding `0` and `1`, and any prescribed finite jets at those nodes, there is an endpoint-corrected
Gaussian combination whose exponential polynomial realizes those jets. -/
theorem deningerGaussianJet_universality {K : ℕ} (σ : Fin K → ℂ) (hinj : Function.Injective σ)
    (hσ0 : ∀ i, σ i ≠ 0) (hσ1 : ∀ i, σ i ≠ 1) (m : Fin K → ℕ) (v : Fin K → ℕ → ℂ) :
    ∃ (N : ℕ) (c : Fin N → ℂ) (μ : Fin N → ℝ),
      (∀ j, 0 < μ j) ∧ deningerEndpointCorrected c μ ∧
      ∀ i : Fin K, ∀ k < m i, iteratedDeriv k (deningerExpPoly c μ) (σ i) = v i k := by
  classical
  obtain ⟨δ, hδpos, hinjOn⟩ :=
    deningerExpShift_injOn ((Finset.univ.image σ) ∪ ({0, 1} : Finset ℂ))
  have hmemσ : ∀ i, σ i ∈ ((Finset.univ.image σ) ∪ ({0, 1} : Finset ℂ)) := by
    intro i
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hmem0 : (0 : ℂ) ∈ ((Finset.univ.image σ) ∪ ({0, 1} : Finset ℂ)) := by
    refine Finset.mem_union_right _ ?_
    simp
  have hmem1 : (1 : ℂ) ∈ ((Finset.univ.image σ) ∪ ({0, 1} : Finset ℂ)) := by
    refine Finset.mem_union_right _ ?_
    simp
  set w : Fin K → ℂ := fun i => Complex.exp (-(δ : ℂ) * σ i) with hw
  have hδne : ((δ : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hδpos
  have hw0 : ∀ i, w i ≠ 0 := fun i => Complex.exp_ne_zero _
  have hwinj : Function.Injective w := by
    intro i i' hii
    exact hinj (hinjOn (hmemσ i) (hmemσ i') hii)
  have hu₁ : Complex.exp (-(δ : ℂ) * 0) = 1 := by
    rw [mul_zero, Complex.exp_zero]
  have hwu₁ : ∀ i, w i ≠ (1 : ℂ) := by
    intro i hcon
    have hstep : (fun s : ℂ => Complex.exp (-(δ : ℂ) * s)) (σ i)
        = (fun s : ℂ => Complex.exp (-(δ : ℂ) * s)) 0 := by
      show Complex.exp (-(δ : ℂ) * σ i) = Complex.exp (-(δ : ℂ) * 0)
      rw [hu₁]
      exact hcon
    exact hσ0 i (hinjOn (hmemσ i) hmem0 hstep)
  have hwu₂ : ∀ i, w i ≠ Complex.exp (-(δ : ℂ) * 1) := by
    intro i hcon
    have hstep : (fun s : ℂ => Complex.exp (-(δ : ℂ) * s)) (σ i)
        = (fun s : ℂ => Complex.exp (-(δ : ℂ) * s)) 1 := by
      show Complex.exp (-(δ : ℂ) * σ i) = Complex.exp (-(δ : ℂ) * 1)
      exact hcon
    exact hσ1 i (hinjOn (hmemσ i) hmem1 hstep)
  obtain ⟨P, hP1, hP2, hPjet⟩ :=
    deningerJet_interpolation (δ := (δ : ℂ)) hδne w hw0 hwinj 1 (Complex.exp (-(δ : ℂ) * 1))
      hwu₁ hwu₂ m v
  refine ⟨P.natDegree + 1, fun j => P.coeff (j : ℕ), fun j => Real.exp ((j : ℕ) * δ),
    fun j => Real.exp_pos _, ?_, ?_⟩
  · constructor
    · have h := deningerExpPoly_zero (fun j : Fin (P.natDegree + 1) => P.coeff (j : ℕ))
        (fun j : Fin (P.natDegree + 1) => Real.exp ((j : ℕ) * δ))
      rw [← h, deningerExpPoly_eq_eval δ P]
      show P.eval (Complex.exp (-(δ : ℂ) * 0)) = 0
      rw [hu₁]
      exact hP1
    · have h := deningerExpPoly_one (fun j : Fin (P.natDegree + 1) => P.coeff (j : ℕ))
        (fun j : Fin (P.natDegree + 1) => Real.exp ((j : ℕ) * δ))
      rw [← h, deningerExpPoly_eq_eval δ P]
      show P.eval (Complex.exp (-(δ : ℂ) * 1)) = 0
      exact hP2
  · intro i k hk
    rw [deningerExpPoly_eq_eval δ P, deningerExpComposite_iteratedDeriv]
    show ((deningerEulerOp (δ : ℂ))^[k] P).eval (Complex.exp (-(δ : ℂ) * σ i)) = v i k
    exact hPjet i k hk

end Universality

end RHTower
