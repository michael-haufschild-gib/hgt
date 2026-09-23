import GaloisForLFunctions.HTGeometry.HermiteCompleteness
import GaloisForLFunctions.HTGeometry.SchwartzProduct

/-!
# `L²` bounds for the oscillator operators

The bilinear pairing of a Schwartz function against another is the `L²` inner product of the
conjugate of the first against the second, so Cauchy–Schwarz applies to it.  Conjugation commutes
with the creation and annihilation operators, whose coefficients are real.

Together with the adjointness of the two operators and the commutation relation this bounds the
`L²` norms of `A g` and `B g` by the `L²` norms of `g` and of the number operator applied to `g`:
`‖Ag‖₂² ≤ ‖g‖₂‖(N+4π)g‖₂` and `‖Bg‖₂² ≤ ‖g‖₂‖Ng‖₂`.  These are the estimates that let the
oscillator seminorms dominate the seminorms built from multiplication and differentiation.

* `schwartzPair_eq_inner`, `norm_schwartzPair_le` : Cauchy–Schwarz for the pairing.
* `conjSLM_creationCLM`, `conjSLM_annihilationCLM` : conjugation commutes with the operators.
* `norm_toLp_creationCLM_sq_le`, `norm_toLp_annihilationCLM_sq_le` : **the `L²` bounds.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Conjugation and the pairing -/

theorem conjSLM_conjSLM (f : 𝓢(ℝ, ℂ)) : SchwartzMap.conjSLM (SchwartzMap.conjSLM f) = f := by
  refine SchwartzMap.ext fun x => ?_
  rw [SchwartzMap.conjSLM_apply, SchwartzMap.conjSLM_apply, Complex.conj_conj]

/-- **The bilinear pairing is the `L²` inner product against the conjugate.** -/
theorem schwartzPair_eq_inner (u v : 𝓢(ℝ, ℂ)) :
    schwartzPair u v = inner ℂ ((SchwartzMap.conjSLM u).toLp 2 volume) (v.toLp 2 volume) := by
  rw [MeasureTheory.L2.inner_def, schwartzPair_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.conjSLM u) 2 volume,
    SchwartzMap.coeFn_toLp v 2 volume] with x hx hy
  rw [hx, hy, RCLike.inner_apply, SchwartzMap.conjSLM_apply, Complex.conj_conj]
  exact mul_comm _ _

theorem norm_toLp_conjSLM (u : 𝓢(ℝ, ℂ)) :
    ‖(SchwartzMap.conjSLM u).toLp 2 volume‖ = ‖u.toLp 2 volume‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine MeasureTheory.eLpNorm_congr_norm_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.conjSLM u) 2 volume,
    SchwartzMap.coeFn_toLp u 2 volume] with x hx hy
  rw [hx, hy, SchwartzMap.conjSLM_apply, RCLike.norm_conj]

/-- **Cauchy–Schwarz for the bilinear pairing.** -/
theorem norm_schwartzPair_le (u v : 𝓢(ℝ, ℂ)) :
    ‖schwartzPair u v‖ ≤ ‖u.toLp 2 volume‖ * ‖v.toLp 2 volume‖ := by
  rw [schwartzPair_eq_inner]
  refine le_trans (norm_inner_le_norm _ _) ?_
  rw [norm_toLp_conjSLM]

theorem norm_schwartzPair_conj_self (u : 𝓢(ℝ, ℂ)) :
    ‖schwartzPair (SchwartzMap.conjSLM u) u‖ = ‖u.toLp 2 volume‖ ^ (2 : ℕ) := by
  rw [schwartzPair_eq_inner, conjSLM_conjSLM, inner_self_eq_norm_sq_to_K, norm_pow,
    RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-! ## Conjugation and the oscillator operators -/

theorem conjSLM_derivSCLM (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.conjSLM (derivSCLM f) = derivSCLM (SchwartzMap.conjSLM f) := by
  refine SchwartzMap.ext fun x => ?_
  have hderiv : HasDerivAt (fun y : ℝ => (starRingEnd ℂ) (f y))
      ((starRingEnd ℂ) (deriv (f : ℝ → ℂ) x)) x := by
    have hL : HasFDerivAt (RCLike.conjCLE (K := ℂ) : ℂ →L[ℝ] ℂ)
        (RCLike.conjCLE (K := ℂ) : ℂ →L[ℝ] ℂ) (f x) :=
      ContinuousLinearMap.hasFDerivAt _
    exact hL.comp_hasDerivAt x (f.hasDerivAt x)
  rw [SchwartzMap.conjSLM_apply, derivSCLM_apply, derivSCLM_apply]
  have hfun : (fun y : ℝ => (SchwartzMap.conjSLM f) y) = fun y : ℝ => (starRingEnd ℂ) (f y) := by
    funext y
    rw [SchwartzMap.conjSLM_apply]
  rw [show ((SchwartzMap.conjSLM f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun y : ℝ => (starRingEnd ℂ) (f y) from hfun, hderiv.deriv]

theorem conjSLM_mulXCLM (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.conjSLM (mulXCLM f) = mulXCLM (SchwartzMap.conjSLM f) := by
  refine SchwartzMap.ext fun x => ?_
  rw [SchwartzMap.conjSLM_apply, mulXCLM_apply, mulXCLM_apply, SchwartzMap.conjSLM_apply,
    map_mul, Complex.conj_ofReal]

theorem conjSLM_starPi : (starRingEnd ℂ) (2 * (π : ℂ)) = 2 * (π : ℂ) := by
  rw [map_mul, Complex.conj_ofReal, map_ofNat]

theorem conjSLM_creationCLM (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.conjSLM (creationCLM f) = creationCLM (SchwartzMap.conjSLM f) := by
  rw [creationCLM_eq, creationCLM_eq (SchwartzMap.conjSLM f), map_sub, map_smulₛₗ,
    conjSLM_starPi, conjSLM_derivSCLM, conjSLM_mulXCLM]

theorem conjSLM_annihilationCLM (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.conjSLM (annihilationCLM f) = annihilationCLM (SchwartzMap.conjSLM f) := by
  rw [annihilationCLM_eq, annihilationCLM_eq (SchwartzMap.conjSLM f), map_add, map_smulₛₗ,
    conjSLM_starPi, conjSLM_derivSCLM, conjSLM_mulXCLM]

/-! ## The `L²` bounds -/

/-- **The `L²` norm of the creation operator is controlled by the number operator.** -/
theorem norm_toLp_creationCLM_sq_le (g : 𝓢(ℝ, ℂ)) :
    ‖(creationCLM g).toLp 2 volume‖ ^ (2 : ℕ)
      ≤ ‖g.toLp 2 volume‖ * ‖(numberCLM g + (4 * (π : ℂ)) • g).toLp 2 volume‖ := by
  have hBA : annihilationCLM (creationCLM g) = numberCLM g + (4 * (π : ℂ)) • g := by
    have h := annihilationCLM_creationCLM_sub g
    rw [sub_eq_iff_eq_add] at h
    rw [h, numberCLM_apply, add_comm]
  calc ‖(creationCLM g).toLp 2 volume‖ ^ (2 : ℕ)
      = ‖schwartzPair (SchwartzMap.conjSLM (creationCLM g)) (creationCLM g)‖ :=
        (norm_schwartzPair_conj_self _).symm
    _ = ‖schwartzPair (SchwartzMap.conjSLM g) (numberCLM g + (4 * (π : ℂ)) • g)‖ := by
        rw [conjSLM_creationCLM, schwartzPair_creationCLM, hBA]
    _ ≤ ‖(SchwartzMap.conjSLM g).toLp 2 volume‖
          * ‖(numberCLM g + (4 * (π : ℂ)) • g).toLp 2 volume‖ := norm_schwartzPair_le _ _
    _ = ‖g.toLp 2 volume‖ * ‖(numberCLM g + (4 * (π : ℂ)) • g).toLp 2 volume‖ := by
        rw [norm_toLp_conjSLM]

/-- **The `L²` norm of the annihilation operator is controlled by the number operator.** -/
theorem norm_toLp_annihilationCLM_sq_le (g : 𝓢(ℝ, ℂ)) :
    ‖(annihilationCLM g).toLp 2 volume‖ ^ (2 : ℕ)
      ≤ ‖g.toLp 2 volume‖ * ‖(numberCLM g).toLp 2 volume‖ := by
  have hadj : schwartzPair (annihilationCLM (SchwartzMap.conjSLM g)) (annihilationCLM g)
      = schwartzPair (SchwartzMap.conjSLM g) (creationCLM (annihilationCLM g)) := by
    have h := schwartzPair_creationCLM (annihilationCLM g) (SchwartzMap.conjSLM g)
    rw [schwartzPair_comm (annihilationCLM (SchwartzMap.conjSLM g)) (annihilationCLM g),
      schwartzPair_comm (SchwartzMap.conjSLM g) (creationCLM (annihilationCLM g))]
    exact h.symm
  calc ‖(annihilationCLM g).toLp 2 volume‖ ^ (2 : ℕ)
      = ‖schwartzPair (SchwartzMap.conjSLM (annihilationCLM g)) (annihilationCLM g)‖ :=
        (norm_schwartzPair_conj_self _).symm
    _ = ‖schwartzPair (SchwartzMap.conjSLM g) (numberCLM g)‖ := by
        rw [conjSLM_annihilationCLM, hadj, numberCLM_apply]
    _ ≤ ‖(SchwartzMap.conjSLM g).toLp 2 volume‖ * ‖(numberCLM g).toLp 2 volume‖ :=
        norm_schwartzPair_le _ _
    _ = ‖g.toLp 2 volume‖ * ‖(numberCLM g).toLp 2 volume‖ := by
        rw [norm_toLp_conjSLM]

end GaloisForLFunctions

end
