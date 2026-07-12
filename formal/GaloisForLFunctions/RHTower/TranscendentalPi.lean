import GaloisForLFunctions.RHTower.ExpEulerRelation
import GaloisForLFunctions.RHTower.PiTranscendenceSetup

/-!
# π is transcendental

`Real.pi` is transcendental over `ℚ`.  Mathlib provides only the analytic half of
Lindemann–Weierstrass (`LindemannWeierstrass.exp_polynomial_approx`); this completes it for the
Euler relation.  If `π` were algebraic, then `iπ` would be a nonzero algebraic number, so a nonzero
integer polynomial `μ` vanishes at `iπ`; its complete complex root set `θ_1,…,θ_d` (which includes
`iπ`) factors `μ.map = C ℓ · ∏_j (X − θ_j)`.  Euler's identity `e^{iπ} = −1` makes the factor
`1 + e^{iπ}` vanish, so `∏_j (1 + e^{θ_j}) = ∑_S e^{∑_{j∈S} θ_j} = 0`, and the non-monic
Lindemann–Weierstrass contradiction `exp_euler_relation_ne` applies.
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower

/-- Euler product expansion: `∏_j (e^{θ_j} + 1) = ∑_S e^{∑_{j∈S} θ_j}`. -/
theorem prod_exp_add_one_eq_sum_subsetSum {d : ℕ} (θ : Fin d → ℂ) :
    ∏ j : Fin d, (Complex.exp (θ j) + 1)
      = ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Complex.exp (∑ j ∈ S, θ j) := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.prod_const_one, mul_one, ← Complex.exp_sum]

theorem transcendental_pi : Transcendental ℚ (Real.pi : ℝ) := by
  intro hpi
  have hpiC : IsAlgebraic ℚ ((Real.pi : ℂ)) := by
    have h := hpi.algHom (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    simpa [Complex.coe_algebraMap] using h
  have hiπ : IsAlgebraic ℚ ((Real.pi : ℂ) * Complex.I) := isAlgebraic_pi_mul_I hpiC
  have hiπZ : IsAlgebraic ℤ ((Real.pi : ℂ) * Complex.I) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hiπ
  obtain ⟨μ, hμ0, hμeval⟩ := hiπZ
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hμmap0 : μ.map (Int.castRingHom ℂ) ≠ 0 := by
    intro h; exact hμ0 ((Polynomial.map_eq_zero_iff hinj).mp h)
  have hsplits : (μ.map (Int.castRingHom ℂ)).roots.card
      = (μ.map (Int.castRingHom ℂ)).natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  obtain ⟨l, hl⟩ := Quotient.exists_rep (μ.map (Int.castRingHom ℂ)).roots
  set θ : Fin l.length → ℂ := l.get with hθdef
  have hmap : Multiset.map θ Finset.univ.val = (μ.map (Int.castRingHom ℂ)).roots := by
    rw [Fin.univ_val_map, List.ofFn_get]; exact hl
  have hlc : (μ.map (Int.castRingHom ℂ)).leadingCoeff = ((μ.leadingCoeff : ℤ) : ℂ) := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hinj μ,
      Polynomial.coeff_map]; rfl
  have hθfac : μ.map (Int.castRingHom ℂ)
      = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (θ j)) Finset.univ.val).prod := by
    have h1 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hsplits
    rw [hlc] at h1
    have hroots : (Multiset.map (fun a => X - C a) (μ.map (Int.castRingHom ℂ)).roots)
        = Multiset.map (fun j => X - C (θ j)) Finset.univ.val := by
      rw [← hmap, Multiset.map_map]; rfl
    rw [hroots] at h1
    exact h1.symm
  -- iπ is a root of μ.map, hence equals some θ j₀
  have hiπroot : ((Real.pi : ℂ) * Complex.I) ∈ (μ.map (Int.castRingHom ℂ)).roots := by
    have heq : Polynomial.aeval ((Real.pi : ℂ) * Complex.I) μ
        = Polynomial.eval₂ (Int.castRingHom ℂ) ((Real.pi : ℂ) * Complex.I) μ := by
      rw [Polynomial.aeval_def, algebraMap_int_eq]
    rw [Polynomial.mem_roots hμmap0, Polynomial.IsRoot.def, Polynomial.eval_map, ← heq]
    exact hμeval
  rw [← hmap] at hiπroot
  obtain ⟨j₀, _, hj₀⟩ := Multiset.mem_map.mp hiπroot
  -- Euler relation vanishes
  have hprod0 : ∏ j : Fin l.length, (Complex.exp (θ j) + 1) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
    rw [hj₀, exp_pi_mul_I]; ring
  have hrel : ∑ S ∈ (Finset.univ : Finset (Fin l.length)).powerset,
      Complex.exp (∑ j ∈ S, θ j) = 0 := by
    rw [← prod_exp_add_one_eq_sum_subsetSum]; exact hprod0
  exact exp_euler_relation_ne μ hμ0 θ hθfac hrel

end GaloisForLFunctions.RHTower
