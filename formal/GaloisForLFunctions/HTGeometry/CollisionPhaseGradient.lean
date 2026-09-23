import GaloisForLFunctions.HTGeometry.RankEnergyLaw

/-!
# The phase gradient of the quartic collision functional

The collision functional of a phase orbit is the fourth power sum of the coordinates of `Uζ`, where
`ζ` runs over the coordinate phases.  Differentiating in one phase coordinate produces four times
the real part of one entry of `U*v`, where `v` is the cubic vector `‖y‖²y`.

Summing the squares of those derivatives and using unitarity therefore costs exactly sixteen times
the sixth power sum: the gradient energy of the quartic functional is controlled by the next
moment up.  This is the estimate that converts a Poincaré inequality into a variance bound.
-/

open Finset Complex
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Gradient

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The phase orbit of a unitary against the coordinate phases. -/
private def phaseOrbit (U : Matrix D D ℂ) (θ : D → ℝ) (j : D) : ℂ :=
  ∑ a, U j a * Complex.exp (Complex.I * (θ a : ℂ))

/-- The cubic vector attached to a phase orbit. -/
def cubicVector (U : Matrix D D ℂ) (θ : D → ℝ) (j : D) : ℂ :=
  (Complex.normSq (phaseOrbit U θ j) : ℂ) * phaseOrbit U θ j

/-- The quartic collision functional of a phase orbit. -/
def collisionFunctional (U : Matrix D D ℂ) (θ : D → ℝ) : ℝ :=
  ∑ j, Complex.normSq (phaseOrbit U θ j) ^ (2 : ℕ)

/-- The derivative of the collision functional in the `a`-th phase coordinate, in closed form. -/
def phaseDerivative (U : Matrix D D ℂ) (θ : D → ℝ) (a : D) : ℝ :=
  4 * (Complex.I * Complex.exp (Complex.I * (θ a : ℂ)) *
    (∑ j, (starRingEnd ℂ) (cubicVector U θ j) * U j a)).re

omit [DecidableEq D] in
/-- Each phase derivative is bounded by four times the modulus of the corresponding entry of the
adjoint applied to the cubic vector. -/
theorem abs_phaseDerivative_le (U : Matrix D D ℂ) (θ : D → ℝ) (a : D) :
    |phaseDerivative U θ a| ≤ 4 * ‖∑ j, (starRingEnd ℂ) (cubicVector U θ j) * U j a‖ := by
  rw [phaseDerivative, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
  have hre : (Complex.I * (θ a : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero, one_mul]

omit [DecidableEq D] in
/-- **The gradient energy of the quartic functional.**  Summing the squared phase derivatives costs
sixteen times the squared norm of the adjoint applied to the cubic vector. -/
theorem sum_sq_phaseDerivative_le (U : Matrix D D ℂ) (θ : D → ℝ) :
    ∑ a, phaseDerivative U θ a ^ (2 : ℕ)
      ≤ 16 * ∑ a, ‖∑ j, (starRingEnd ℂ) (cubicVector U θ j) * U j a‖ ^ (2 : ℕ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have habs := abs_phaseDerivative_le U θ a
  have hsq : phaseDerivative U θ a ^ (2 : ℕ) = |phaseDerivative U θ a| ^ (2 : ℕ) := (sq_abs _).symm
  rw [hsq]
  have hnn : (0 : ℝ) ≤ 4 * ‖∑ j, (starRingEnd ℂ) (cubicVector U θ j) * U j a‖ := by positivity
  calc |phaseDerivative U θ a| ^ (2 : ℕ)
      ≤ (4 * ‖∑ j, (starRingEnd ℂ) (cubicVector U θ j) * U j a‖) ^ (2 : ℕ) := by
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = 16 * ‖∑ j, (starRingEnd ℂ) (cubicVector U θ j) * U j a‖ ^ (2 : ℕ) := by ring

omit [DecidableEq D] in
/-- The cubic vector has squared norm the sixth power sum of the orbit. -/
theorem sum_normSq_cubicVector (U : Matrix D D ℂ) (θ : D → ℝ) :
    ∑ j, ‖cubicVector U θ j‖ ^ (2 : ℕ) = ∑ j, Complex.normSq (phaseOrbit U θ j) ^ (3 : ℕ) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cubicVector, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Complex.normSq_nonneg _), mul_pow, Complex.normSq_eq_norm_sq]
  ring

/-- **Unitarity preserves the energy of the cubic vector.**  The entries of the adjoint applied to a
vector have the same total energy as the vector. -/
theorem sum_normSq_vecMul_conj (U : Matrix D D ℂ) (hU : U * Uᴴ = 1) (v : D → ℂ) :
    ∑ a, ‖∑ j, (starRingEnd ℂ) (v j) * U j a‖ ^ (2 : ℕ) = ∑ j, ‖v j‖ ^ (2 : ℕ) := by
  classical
  have hsq : ∀ z : ℂ, ‖z‖ ^ (2 : ℕ) = (z * (starRingEnd ℂ) z).re := by
    intro z
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hentry : ∀ j k : D, ∑ a, U j a * (starRingEnd ℂ) (U k a) = if j = k then 1 else 0 := by
    intro j k
    have hjk := congrFun (congrFun hU j) k
    rw [Matrix.mul_apply] at hjk
    simpa [Matrix.conjTranspose_apply, Matrix.one_apply] using hjk
  have hcomplex : ∑ a, (∑ j, (starRingEnd ℂ) (v j) * U j a) *
      (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (v j) * U j a)
      = ∑ j, v j * (starRingEnd ℂ) (v j) := by
    have hconj : ∀ a : D, (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (v j) * U j a)
        = ∑ k, v k * (starRingEnd ℂ) (U k a) := by
      intro a
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_mul, Complex.conj_conj]
    calc ∑ a, (∑ j, (starRingEnd ℂ) (v j) * U j a) *
          (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (v j) * U j a)
        = ∑ a, ∑ j, ∑ k, ((starRingEnd ℂ) (v j) * v k) * (U j a * (starRingEnd ℂ) (U k a)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hconj a, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ j, ∑ k, ((starRingEnd ℂ) (v j) * v k) * ∑ a, (U j a * (starRingEnd ℂ) (U k a)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j, v j * (starRingEnd ℂ) (v j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_congr rfl fun k _ => by rw [hentry j k]]
          rw [Finset.sum_eq_single j]
          · simp
            ring
          · intro k _ hkj
            rw [if_neg (Ne.symm hkj)]
            ring
          · intro hj
            exact absurd (Finset.mem_univ j) hj
  calc ∑ a, ‖∑ j, (starRingEnd ℂ) (v j) * U j a‖ ^ (2 : ℕ)
      = ∑ a, ((∑ j, (starRingEnd ℂ) (v j) * U j a) *
          (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (v j) * U j a)).re :=
        Finset.sum_congr rfl fun a _ => hsq _
    _ = (∑ a, (∑ j, (starRingEnd ℂ) (v j) * U j a) *
          (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (v j) * U j a)).re := by
        rw [Complex.re_sum]
    _ = (∑ j, v j * (starRingEnd ℂ) (v j)).re := by rw [hcomplex]
    _ = ∑ j, ‖v j‖ ^ (2 : ℕ) := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun j _ => (hsq (v j)).symm

/-- **`(13)`: the phase-gradient energy of the collision functional.**  The squared phase gradient
is at most sixteen times the sixth power sum of the orbit. -/
theorem sum_sq_phaseDerivative_le_sixth (U : Matrix D D ℂ) (hU : U * Uᴴ = 1) (θ : D → ℝ) :
    ∑ a, phaseDerivative U θ a ^ (2 : ℕ)
      ≤ 16 * ∑ j, Complex.normSq (phaseOrbit U θ j) ^ (3 : ℕ) := by
  refine le_trans (sum_sq_phaseDerivative_le U θ) ?_
  rw [sum_normSq_vecMul_conj U hU (cubicVector U θ), sum_normSq_cubicVector]

/-! ## The derivative is what the closed form says -/

/-- The squared modulus along a differentiable path. -/
theorem hasDerivAt_normSq {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun s => Complex.normSq (f s)) (2 * ((starRingEnd ℂ) (f x) * f').re) x := by
  have hinner := h.inner (𝕜 := ℝ) h
  have hinner_eq : ∀ z w : ℂ, (inner ℝ z w : ℝ) = z.re * w.re + z.im * w.im := by
    intro z w
    simp [Complex.mul_re]
    ring
  have hfun : (fun s => Complex.normSq (f s)) = fun s => (inner ℝ (f s) (f s) : ℝ) := by
    funext s
    rw [hinner_eq, Complex.normSq_apply]
  rw [hfun]
  refine hinner.congr_deriv ?_
  rw [hinner_eq, hinner_eq]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The orbit depends on one phase coordinate through a single exponential. -/
theorem hasDerivAt_phaseOrbit (U : Matrix D D ℂ) (θ : D → ℝ) (a j : D) :
    HasDerivAt (fun s : ℝ => phaseOrbit U (Function.update θ a (θ a + s)) j)
      (U j a * (Complex.exp (Complex.I * (θ a : ℂ)) * Complex.I)) 0 := by
  classical
  have hsplit : ∀ s : ℝ, phaseOrbit U (Function.update θ a (θ a + s)) j
      = (∑ b ∈ Finset.univ.erase a, U j b * Complex.exp (Complex.I * (θ b : ℂ)))
        + U j a * Complex.exp (Complex.I * ((θ a : ℂ) + (s : ℂ))) := by
    intro s
    rw [phaseOrbit, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun b hb => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
    · rw [Function.update_self]
      congr 2
      push_cast
      ring
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * ((θ a : ℂ) + (s : ℂ))))
      (Complex.exp (Complex.I * ((θ a : ℂ) + ((0 : ℝ) : ℂ))) * Complex.I) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have h2 : HasDerivAt (fun s : ℝ => (θ a : ℂ) + (s : ℂ)) 1 0 := by
      simpa using h1.const_add ((θ a : ℂ))
    have h3 : HasDerivAt (fun s : ℝ => Complex.I * ((θ a : ℂ) + (s : ℂ))) Complex.I 0 := by
      simpa using h2.const_mul Complex.I
    simpa using h3.cexp
  have hmain := (hexp.const_mul (U j a)).const_add
    (∑ b ∈ Finset.univ.erase a, U j b * Complex.exp (Complex.I * (θ b : ℂ)))
  rw [funext hsplit]
  refine hmain.congr_deriv ?_
  norm_num

/-- **The closed form is the derivative.**  Differentiating the collision functional in one phase
coordinate gives `phaseDerivative`. -/
theorem hasDerivAt_collisionFunctional (U : Matrix D D ℂ) (θ : D → ℝ) (a : D) :
    HasDerivAt (fun s : ℝ => collisionFunctional U (Function.update θ a (θ a + s)))
      (phaseDerivative U θ a) 0 := by
  classical
  have hupd : Function.update θ a (θ a + 0) = θ := by
    funext b
    by_cases hb : b = a
    · subst hb
      rw [Function.update_self, add_zero]
    · rw [Function.update_of_ne hb]
  have hterm : ∀ j : D, HasDerivAt
      (fun s : ℝ => Complex.normSq (phaseOrbit U (Function.update θ a (θ a + s)) j) ^ (2 : ℕ))
      (2 * Complex.normSq (phaseOrbit U θ j) ^ (1 : ℕ) *
        (2 * ((starRingEnd ℂ) (phaseOrbit U θ j) *
          (U j a * (Complex.exp (Complex.I * (θ a : ℂ)) * Complex.I))).re)) 0 := by
    intro j
    have h2 := hasDerivAt_normSq (hasDerivAt_phaseOrbit U θ a j)
    rw [hupd] at h2
    have h3 := h2.mul h2
    rw [hupd] at h3
    have hfun : ((fun s : ℝ => Complex.normSq (phaseOrbit U (Function.update θ a (θ a + s)) j)) *
        fun s : ℝ => Complex.normSq (phaseOrbit U (Function.update θ a (θ a + s)) j))
        = fun s : ℝ => Complex.normSq (phaseOrbit U (Function.update θ a (θ a + s)) j) ^ (2 : ℕ) := by
      funext s
      simp only [Pi.mul_apply]
      ring
    rw [hfun] at h3
    refine h3.congr_deriv ?_
    ring
  have hsum : HasDerivAt (fun s : ℝ => collisionFunctional U (Function.update θ a (θ a + s)))
      (∑ j, 2 * Complex.normSq (phaseOrbit U θ j) ^ (1 : ℕ) *
        (2 * ((starRingEnd ℂ) (phaseOrbit U θ j) *
          (U j a * (Complex.exp (Complex.I * (θ a : ℂ)) * Complex.I))).re)) 0 := by
    have hfun2 : (fun s : ℝ => collisionFunctional U (Function.update θ a (θ a + s)))
        = ∑ j : D, (fun s : ℝ =>
            Complex.normSq (phaseOrbit U (Function.update θ a (θ a + s)) j) ^ (2 : ℕ)) := by
      funext s
      rw [collisionFunctional, Finset.sum_apply]
    rw [hfun2]
    exact HasDerivAt.sum (fun (j : D) (_ : j ∈ Finset.univ) => hterm j)
  refine hsum.congr_deriv ?_
  rw [phaseDerivative, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconj : (starRingEnd ℂ) (cubicVector U θ j)
      = ((Complex.normSq (phaseOrbit U θ j) : ℝ) : ℂ) * (starRingEnd ℂ) (phaseOrbit U θ j) := by
    rw [cubicVector, map_mul, Complex.conj_ofReal]
  rw [hconj]
  rw [show Complex.I * Complex.exp (Complex.I * (θ a : ℂ)) *
      (((Complex.normSq (phaseOrbit U θ j) : ℝ) : ℂ) *
        (starRingEnd ℂ) (phaseOrbit U θ j) * U j a)
      = ((Complex.normSq (phaseOrbit U θ j) : ℝ) : ℂ) *
        ((starRingEnd ℂ) (phaseOrbit U θ j) *
          (U j a * (Complex.exp (Complex.I * (θ a : ℂ)) * Complex.I))) by ring]
  rw [Complex.re_ofReal_mul]
  ring

end Gradient

end

end GaloisForLFunctions.HTGeometry
