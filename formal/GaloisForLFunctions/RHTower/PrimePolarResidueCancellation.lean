import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone
import GaloisForLFunctions.RHTower.TentMellinFactor

/-!
# The polar cancellation at `s = 3/2`

The residue-cancellation heart of `prime-polar-moving-tent-divisor-tomography` §5 (eq. 23).  The two
terms of the continuation `(22)` that are singular at `s = 3/2` — the polar summand `8α²·ζ(s-½)` and
the prime summand `-2·I_L(s)·(-ζ'/ζ)(s-½)` — each have a simple pole there, and their residues
`+8α²` and `-2·I_L(3/2) = -8α²` cancel exactly (`α = 1 - e^{-L/2}`, `I_L(3/2) = 4α²`).  Hence the
combination is holomorphic at `s = 3/2`: `(s - 3/2)·(sum) → 0`.

The two residues are supplied by `polar_term_residue` (from `ζ`'s pole, via the half-shift) and
`neg_logDeriv_zeta_residue` (the residue `+1` of `-ζ'/ζ` at `1`), and the value `I_L(3/2) = 4α²` by
`rectangularWindowAmplitude_at_half`.
-/

open Filter Topology

namespace RHTower

/-- **Polar cancellation** (§5, eq. 23).  At `s = 3/2` the polar term `8α²·ζ(s-½)` and the prime term
`-2·I_L(s)·(-ζ'/ζ)(s-½)` have opposite residues `±8α²`, so their sum has residue `0` — it is
holomorphic at `s = 3/2`.  Here `I_L(s) = A_L(s-1)²` and `α = 1 - e^{-L/2}`. -/
theorem polar_cancellation (L : ℝ) :
    Tendsto (fun s => (s - 3 / 2) * (
        (8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ (2 : ℕ)) * riemannZeta (s - 1 / 2)
        - 2 * (rectangularWindowAmplitude L (s - 1)) ^ (2 : ℕ)
            * (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2))))
      (𝓝[≠] (3 / 2)) (𝓝 0) := by
  have hshift : Tendsto (fun s : ℂ => ((s - 1 / 2) - 1) *
      (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2))) (𝓝[≠] (3 / 2)) (𝓝 1) :=
    neg_logDeriv_zeta_residue.comp shift_half_tendsto
  have hILc := (((tentMellinFactor_differentiable L).continuous.tendsto (3 / 2)).const_mul 2)
  have h2 : (2 * (rectangularWindowAmplitude L ((3 / 2 : ℂ) - 1)) ^ (2 : ℕ))
      = 8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ (2 : ℕ) := by
    rw [rectangularWindowAmplitude_at_half]; ring
  have hIL : Tendsto (fun s => 2 * (rectangularWindowAmplitude L (s - 1)) ^ (2 : ℕ))
      (𝓝[≠] (3 / 2)) (𝓝 (8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ (2 : ℕ))) := by
    rw [← h2]; exact hILc.mono_left nhdsWithin_le_nhds
  have hsub := (polar_term_residue L).sub (hIL.mul hshift)
  rw [mul_one, sub_self] at hsub
  exact hsub.congr' (Filter.Eventually.of_forall (fun s => by ring))

/-- The shift `s ↦ s − c` carries the punctured neighbourhood of `a` to that of `a − c`. -/
theorem sub_const_punctured_tendsto (a c : ℂ) :
    Tendsto (fun s : ℂ => s - c) (𝓝[≠] a) (𝓝[≠] (a - c)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_id.sub continuous_const).tendsto' a (a - c) rfl).mono_left
    nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h; apply hs; rw [Set.mem_singleton_iff]; linear_combination h

/-- **Off-critical residue / divisor tomography** (§5, eqs. 24–25).  Each zeta zero `ρ` with
`Re ρ > 1/2` (`ρ ≠ 1`) produces a genuine simple pole of the prime term at `s = ρ + ½`, with residue
`2·m(ρ)·A_L(ρ-½)²` — nonzero because `m(ρ) ≥ 1` and the rectangular amplitude does not vanish in the
open right half-plane (`rectangularWindowAmplitude_ne_zero`).  So no off-critical pole cancels, and the
residue reads off the exact analytic multiplicity `m(ρ)`. -/
theorem offcritical_residue (L : ℝ) (hL : 0 < L) {ρ : ℂ}
    (hρre : 1 / 2 < ρ.re) (hζρ : riemannZeta ρ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s => (s - (ρ + 1 / 2)) *
          (-2 * (rectangularWindowAmplitude L (s - 1)) ^ (2 : ℕ)
            * (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2))))
        (𝓝[≠] (ρ + 1 / 2)) (𝓝 (2 * (m : ℂ) * (rectangularWindowAmplitude L (ρ - 1 / 2)) ^ (2 : ℕ)))
      ∧ (2 * (m : ℂ) * (rectangularWindowAmplitude L (ρ - 1 / 2)) ^ (2 : ℕ) ≠ 0) := by
  obtain ⟨m, hm1, hzres⟩ := neg_logDeriv_zeta_zero_residue hζρ
  refine ⟨m, hm1, ?_, ?_⟩
  · have hshift : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝[≠] (ρ + 1 / 2)) (𝓝[≠] ρ) := by
      have := sub_const_punctured_tendsto (ρ + 1 / 2) (1 / 2)
      rwa [show ρ + 1 / 2 - 1 / 2 = ρ by ring] at this
    have hzshift := hzres.comp hshift
    have hILc := (((tentMellinFactor_differentiable L).continuous.tendsto (ρ + 1 / 2)).const_mul (-2))
    have hIL : Tendsto (fun s => -2 * (rectangularWindowAmplitude L (s - 1)) ^ (2 : ℕ))
        (𝓝[≠] (ρ + 1 / 2)) (𝓝 (-2 * (rectangularWindowAmplitude L (ρ - 1 / 2)) ^ (2 : ℕ))) := by
      have h2 : (-2 * (rectangularWindowAmplitude L ((ρ + 1 / 2) - 1)) ^ (2 : ℕ))
          = -2 * (rectangularWindowAmplitude L (ρ - 1 / 2)) ^ (2 : ℕ) := by
        rw [show ρ + 1 / 2 - 1 = ρ - 1 / 2 by ring]
      rw [← h2]; exact hILc.mono_left nhdsWithin_le_nhds
    have hprod := hIL.mul hzshift
    rw [show (-2 * (rectangularWindowAmplitude L (ρ - 1 / 2)) ^ (2 : ℕ)) * (-(m : ℂ))
        = 2 * (m : ℂ) * (rectangularWindowAmplitude L (ρ - 1 / 2)) ^ (2 : ℕ) by ring] at hprod
    exact hprod.congr' (Filter.Eventually.of_forall
      (fun s => by simp only [Function.comp_apply]; ring))
  · refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_
    · exact_mod_cast Nat.one_le_iff_ne_zero.mp hm1
    · exact pow_ne_zero 2
        (rectangularWindowAmplitude_ne_zero hL (by simp [Complex.sub_re]; linarith))

end RHTower
