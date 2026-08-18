import GaloisForLFunctions.RHTower.ConstrainedProlateRayleighFloor
import GaloisForLFunctions.RHTower.ProlateSignedNatBasis
import GaloisForLFunctions.RHTower.ProlateSignedLeakageOrdering

/-!
# Orthonormal expansions of the even carrier, and the phase-normalized signed modes

The signed prolate modes are determined only up to a unit complex factor.  Rotating each of them so
that its pairing with the central indicator becomes real and nonnegative turns the constraint
functional into the real coordinate sequence `ℓ_n = ‖⟪1_[−a,a], h_n⟫‖` that the secular transfer
theorems use, and changes neither orthonormality nor the leakage eigenvalue.

For a convergent expansion `f = ∑ x_j v_j` along any orthonormal family of leakage eigenvectors,

```text
‖f‖² = ∑ ‖x_j‖² ,   re⟪B f, f⟫ = ∑ d_j ‖x_j‖² ,   ⟪1_[−a,a], f⟫ = ∑ x_j ℓ_j ,
```

which is what carries a coordinate statement about the secular model to the operator itself.
-/

noncomputable section

open Filter Set
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-! ### Inner-product rewriting in the even carrier

The even carrier reaches its inner product through a different instance path than the generic
`InnerProductSpace` lemmas, so those are restated once here in the form the carrier presents. -/

theorem inner_even_smul_right (u w : evenSubspace) (r : ℂ) :
    inner ℂ u (r • w) = r * inner ℂ u w := inner_smul_right u w r

theorem inner_even_smul_left (u w : evenSubspace) (r : ℂ) :
    inner ℂ (r • u) w = (starRingEnd ℂ) r * inner ℂ u w := inner_smul_left u w r

theorem inner_even_conj_symm (u w : evenSubspace) :
    inner ℂ u w = (starRingEnd ℂ) (inner ℂ w u) := (inner_conj_symm (𝕜 := ℂ) u w).symm

/-- The modulus square of a complex number as a real cast. -/
theorem mul_conj_ofReal_norm_sq (z : ℂ) :
    z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.mul_conj]
  norm_cast

theorem inner_even_self_eq_norm_sq (u : evenSubspace) :
    (inner ℂ u u : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  have h : (inner ℂ u u : ℂ) = (‖u‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K u
  rw [h]
  push_cast
  ring

/-! ### Phase normalization of the signed modes -/

/-- The unit factor rotating the `n`-th signed mode so its constraint coordinate is nonnegative. -/
def signedModePhase (a : ℝ) (n : ℕ) : ℂ :=
  if evenProlateConstraintCoord a n = 0 then 1
  else (starRingEnd ℂ) (evenProlateConstraintCoord a n)
        / ((‖evenProlateConstraintCoord a n‖ : ℝ) : ℂ)

theorem norm_signedModePhase (a : ℝ) (n : ℕ) : ‖signedModePhase a n‖ = 1 := by
  rw [signedModePhase]
  split_ifs with h
  · exact norm_one
  · rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr h)

/-- The phase-normalized signed prolate mode. -/
def phasedSignedMode (a : ℝ) (n : ℕ) : evenSubspace :=
  signedModePhase a n • evenProlateSignedMode a n

theorem norm_phasedSignedMode {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ‖phasedSignedMode a n‖ = 1 := by
  rcases evenProlateSignedMode_norm_zero_or_one a n with h0 | h1
  · exact absurd h0
      (evenProlateSignedMode_ne_zero_of_value_ne_zero a (evenProlateSignedValue_ne_zero ha n))
  · rw [phasedSignedMode, norm_smul, norm_signedModePhase, h1, one_mul]

theorem inner_phasedSignedMode_of_ne (a : ℝ) {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (phasedSignedMode a m) (phasedSignedMode a n) = 0 := by
  rw [phasedSignedMode, phasedSignedMode, inner_even_smul_left, inner_even_smul_right,
    evenProlateSignedMode_orthogonal_of_ne a hmn, mul_zero, mul_zero]

theorem orthonormal_phasedSignedMode {a : ℝ} (ha : 0 < a) :
    Orthonormal ℂ (phasedSignedMode a) :=
  ⟨norm_phasedSignedMode ha, fun {_ _} h => inner_phasedSignedMode_of_ne a h⟩

/-- **The constraint coordinate of a phased mode is its own modulus** — real and nonnegative. -/
theorem inner_evenCentralIndicator_phasedSignedMode (a : ℝ) (n : ℕ) :
    inner ℂ (evenCentralIndicator a) (phasedSignedMode a n)
      = ((‖evenProlateConstraintCoord a n‖ : ℝ) : ℂ) := by
  rw [phasedSignedMode, inner_even_smul_right,
    show inner ℂ (evenCentralIndicator a) (evenProlateSignedMode a n)
      = evenProlateConstraintCoord a n from rfl, signedModePhase]
  set z := evenProlateConstraintCoord a n with hz
  split_ifs with h
  · rw [h]
    simp
  · have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr h)
    rw [div_mul_eq_mul_div, RCLike.conj_mul]
    field_simp
    norm_cast

/-- The phased modes carry the same leakage eigenvalues. -/
theorem evenProlateLeakage_apply_phasedSignedMode (a : ℝ) (n : ℕ) :
    evenProlateLeakage a (phasedSignedMode a n)
      = ((evenProlateSignedLeakage a n : ℝ) : ℂ) • phasedSignedMode a n := by
  rw [phasedSignedMode, map_smul, evenProlateLeakage_apply_signedMode, smul_comm]
  rfl

/-! ### Orthonormal expansions in the even carrier -/

/-- The coefficients of a convergent orthonormal expansion are the inner products. -/
theorem inner_eq_of_hasSum_smul {v : ℕ → evenSubspace} (hv : Orthonormal ℂ v)
    {x : ℕ → ℂ} {f : evenSubspace} (hf : HasSum (fun j : ℕ => x j • v j) f) (i : ℕ) :
    inner ℂ (v i) f = x i := by
  have h : HasSum (fun j : ℕ => (inner ℂ (v i) (x j • v j) : ℂ)) (inner ℂ (v i) f) :=
    (innerSL ℂ (v i)).hasSum hf
  have hite : (fun j : ℕ => (inner ℂ (v i) (x j • v j) : ℂ))
      = fun j : ℕ => if j = i then x i else 0 := by
    funext j
    rw [inner_even_smul_right]
    have ho : (inner ℂ (v i) (v j) : ℂ) = if i = j then 1 else 0 :=
      orthonormal_iff_ite.mp hv i j
    rw [ho]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hite] at h
  exact h.unique (hasSum_ite_eq i (x i))

/-- **Parseval along a convergent orthonormal expansion.** -/
theorem hasSum_norm_sq_of_hasSum_smul {v : ℕ → evenSubspace} (hv : Orthonormal ℂ v)
    {x : ℕ → ℂ} {f : evenSubspace} (hf : HasSum (fun j : ℕ => x j • v j) f) :
    HasSum (fun j : ℕ => ‖x j‖ ^ 2) (‖f‖ ^ 2) := by
  have h : HasSum (fun j : ℕ => (inner ℂ f (x j • v j) : ℂ)) (inner ℂ f f) :=
    (innerSL ℂ f).hasSum hf
  have hterm : ∀ j : ℕ, (inner ℂ f (x j • v j) : ℂ) = ((‖x j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [inner_even_smul_right, inner_even_conj_symm f (v j),
      inner_eq_of_hasSum_smul hv hf j, mul_conj_ofReal_norm_sq]
  simp only [hterm] at h
  rw [inner_even_self_eq_norm_sq] at h
  exact Complex.hasSum_ofReal.mp h

/-- **The leakage quadratic form along a convergent orthonormal expansion of eigenvectors.** -/
theorem hasSum_leakage_of_hasSum_smul {a : ℝ} {v : ℕ → evenSubspace} (hv : Orthonormal ℂ v)
    {D : ℕ → ℝ} (hD : ∀ j, evenProlateLeakage a (v j) = ((D j : ℝ) : ℂ) • v j)
    {x : ℕ → ℂ} {f : evenSubspace} (hf : HasSum (fun j : ℕ => x j • v j) f) :
    HasSum (fun j : ℕ => D j * ‖x j‖ ^ 2)
      ((inner ℂ (evenProlateLeakage a f) f : ℂ).re) := by
  have hBf : HasSum (fun j : ℕ => (((D j : ℝ) : ℂ) * x j) • v j) (evenProlateLeakage a f) := by
    have h := (evenProlateLeakage a).hasSum hf
    have heq : (fun j : ℕ => evenProlateLeakage a (x j • v j))
        = fun j : ℕ => (((D j : ℝ) : ℂ) * x j) • v j := by
      funext j
      rw [map_smul, hD j, smul_smul, mul_comm]
    rw [heq] at h
    exact h
  have h : HasSum (fun j : ℕ => (inner ℂ (evenProlateLeakage a f) (x j • v j) : ℂ))
      (inner ℂ (evenProlateLeakage a f) f) := (innerSL ℂ (evenProlateLeakage a f)).hasSum hf
  have hterm : ∀ j : ℕ, (inner ℂ (evenProlateLeakage a f) (x j • v j) : ℂ)
      = ((D j * ‖x j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [inner_even_smul_right, inner_even_conj_symm (evenProlateLeakage a f) (v j),
      inner_eq_of_hasSum_smul hv hBf j, map_mul, Complex.conj_ofReal,
      show x j * (((D j : ℝ) : ℂ) * (starRingEnd ℂ) (x j))
        = ((D j : ℝ) : ℂ) * (x j * (starRingEnd ℂ) (x j)) from by ring,
      mul_conj_ofReal_norm_sq]
    push_cast
    ring
  simp only [hterm] at h
  have hre := Complex.reCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  exact hre

/-- **The constraint functional along a convergent orthonormal expansion.** -/
theorem hasSum_constraint_of_hasSum_smul {a : ℝ} {v : ℕ → evenSubspace}
    {L : ℕ → ℝ} (hL : ∀ j, inner ℂ (evenCentralIndicator a) (v j) = ((L j : ℝ) : ℂ))
    {x : ℕ → ℂ} {f : evenSubspace} (hf : HasSum (fun j : ℕ => x j • v j) f) :
    HasSum (fun j : ℕ => x j * ((L j : ℝ) : ℂ))
      (inner ℂ (evenCentralIndicator a) f) := by
  have h : HasSum (fun j : ℕ => (inner ℂ (evenCentralIndicator a) (x j • v j) : ℂ))
      (inner ℂ (evenCentralIndicator a) f) := (innerSL ℂ (evenCentralIndicator a)).hasSum hf
  have heq : (fun j : ℕ => (inner ℂ (evenCentralIndicator a) (x j • v j) : ℂ))
      = fun j : ℕ => x j * ((L j : ℝ) : ℂ) := by
    funext j
    rw [inner_even_smul_right, hL j]
  rw [heq] at h
  exact h

end RHTower

end
