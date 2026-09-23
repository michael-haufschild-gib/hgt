import GaloisForLFunctions.RHTower.CCMRationalResidualEvansMatrix
import GaloisForLFunctions.RHTower.CCMCharacteristicCrossingModes

/-!
# Every screw null vector has global logarithmic transformed-trace regularity

Four exact mechanisms of the card are formalized.

*From the damped symbol to the polynomial symbol.*  `(1+ξ²)^{L} b_a = p_a` turns the null equation
`b_a(D) v = 0` into `p_a(D) v = 0`.  This is `(6)` → `(7)`.

*Interior regularity.*  A solution of `p_a(D) v = 0` is an exponential polynomial, hence smooth, and
its square is integrable on every bounded interval: `(8)`.

*The empty-characteristic branch.*  If the real characteristic set is empty, `p_a` is a nonzero
constant, its solution space is `⊥`, and the interior trace vanishes identically.

*Transport of the kernel.*  A linear equivalence carries a trivial kernel to a trivial kernel, which
is the first equivalence of `(12)`; the second is the Gram determinant criterion of
`CCMRationalResidualEvansMatrix`.

The logarithmic multiplier `c_a(D)`, the coercive Dirichlet realization `C_{a,I}` and the bounded
cross-boundary block `(9)` are cited analytic parents and stay outside the Lean statement.
-/

open Complex MeasureTheory Set Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

open scoped ComplexOrder

/-! ## From the damped symbol to the polynomial symbol -/

/-- **Equations (6) → (7).**  Applying the local operator `(1+D²)^{L}` to the damped null equation
returns the polynomial null equation. -/
theorem polySymbol_eq_zero_of_dampedFactor {v : ℝ → ℂ} {p : Polynomial ℂ} {N : ℕ}
    (hzero : ∀ ξ : ℝ, dampedFactor p N ξ * v ξ = 0) (ξ : ℝ) :
    p.eval (ξ : ℂ) * v ξ = 0 := by
  have hstep : p.eval (ξ : ℂ) * v ξ
      = ((1 : ℂ) + (ξ : ℂ) ^ (2 : ℕ)) ^ N * (dampedFactor p N ξ * v ξ) := by
    rw [← localOperator_dampedFactor p N ξ]
    ring
  rw [hstep, hzero, mul_zero]

/-! ## Interior regularity -/

/-- **Equation (4) → (8), smoothness.**  Every interior solution is smooth. -/
theorem contDiff_of_mem_solutionSpace {L : Polynomial ℂ} {v : ℝ → ℂ}
    (hv : v ∈ solutionSpace L) : ContDiff ℝ (⊤ : ℕ∞) v := hv.1

/-- **Equation (8).**  Every interior solution is square-integrable on each bounded interval. -/
theorem integrableOn_normSq_of_mem_solutionSpace {L : Polynomial ℂ} {v : ℝ → ℂ}
    (hv : v ∈ solutionSpace L) (a b : ℝ) :
    IntegrableOn (fun x => ‖v x‖ ^ (2 : ℕ)) (Icc a b) volume := by
  have hcont : Continuous v := (contDiff_of_mem_solutionSpace hv).continuous
  have hsq : Continuous fun x : ℝ => ‖v x‖ ^ (2 : ℕ) := by fun_prop
  exact (hsq.continuousOn).integrableOn_compact isCompact_Icc

/-- **Equation (4).**  The interior trace of a null vector lies in the finite characteristic
space, and that space has dimension exactly `deg p_a`. -/
theorem finrank_interiorTrace_space {L : Polynomial ℂ} (hL : L ≠ 0) :
    Module.finrank ℂ (solutionSpace L) = L.natDegree :=
  finrank_solutionSpace hL

/-! ## The empty-characteristic branch -/

theorem finiteDimensional_modeSpace (L : Polynomial ℂ) :
    FiniteDimensional ℂ (modeSpace L) := by
  rw [modeSpace]
  exact Module.Finite.span_of_finite ℂ (Set.finite_range _)

/-- **The empty-characteristic branch.**  With no real characteristic crossing the polynomial factor
is a nonzero constant, so the interior trace vanishes identically. -/
theorem solutionSpace_eq_bot_of_natDegree_eq_zero {L : Polynomial ℂ} (hL : L ≠ 0)
    (hdeg : L.natDegree = 0) : solutionSpace L = ⊥ := by
  haveI := finiteDimensional_modeSpace L
  rw [solutionSpace_eq_modeSpace hL, ← Submodule.finrank_eq_zero, finrank_modeSpace, hdeg]

/-- **The empty-characteristic branch, pointwise.** -/
theorem eq_zero_of_mem_solutionSpace_of_natDegree_eq_zero {L : Polynomial ℂ} (hL : L ≠ 0)
    (hdeg : L.natDegree = 0) {v : ℝ → ℂ} (hv : v ∈ solutionSpace L) : v = 0 := by
  have hbot := solutionSpace_eq_bot_of_natDegree_eq_zero hL hdeg
  rw [hbot, Submodule.mem_bot] at hv
  exact hv

/-! ## Transport of the kernel -/

/-- **Equation (12), first equivalence.**  A linear equivalence carries a trivial kernel to a
trivial kernel: the screw null space and the residual null space vanish together. -/
theorem map_eq_bot_iff_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (S : Submodule ℂ V) :
    S.map (e : V →ₗ[ℂ] W) = ⊥ ↔ S = ⊥ := by
  constructor
  · intro h
    refine (Submodule.eq_bot_iff S).mpr fun x hx => ?_
    have hmem : e x ∈ S.map (e : V →ₗ[ℂ] W) := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    refine e.injective ?_
    rw [hmem, map_zero]
  · intro h
    rw [h]
    exact Submodule.map_bot _

/-- **Equation (12).**  The screw null space is trivial exactly when the Evans Gram determinant is
positive. -/
theorem eq_bot_iff_det_evansGramMatrix_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ x : Fin n → ℂ, x ∈ S ↔ A *ᵥ x = 0) :
    S = ⊥ ↔ 0 < (evansGramMatrix A).det := by
  rw [det_evansGramMatrix_pos_iff]
  constructor
  · intro hbot x hx
    have hmem : x ∈ S := (hS x).mpr hx
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  · intro hinj
    refine (Submodule.eq_bot_iff S).mpr fun x hx => ?_
    exact hinj x ((hS x).mp hx)

end GaloisForLFunctions.RHTower

end
