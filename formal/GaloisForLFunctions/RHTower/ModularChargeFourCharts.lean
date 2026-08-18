import GaloisForLFunctions.RHTower.XiHypertranscendentalModularResidueTransgression
import GaloisForLFunctions.RHTower.AdelicIntertwinerType

/-!
# One modular charge in four charts

The Hellinger acceleration, the positive-shell reflection rate, the Xi Julia current residue and
the adelic Weyl drift are the same number in four normalizations.  Two of the four are theorems of
this tree — the shell character's logarithmic modulus and the centered affine Xi residue — and the
other two are the accelerated type of the reflected sewing cost and the oriented prime Lyapunov
rate of the unramified intertwiner.
-/

open Complex

namespace RHTower

/-- **`(19)`: the positive-shell reflection rate.**  The cofinal shell drift between a zero and its
functional-equation reflection is `(2 Re ρ − 1) log 2`. -/
theorem shellReflectionRate_eq (ρ : ℂ) :
    Real.log ‖shellTransferCharacter (1 - star ρ)‖ - Real.log ‖shellTransferCharacter ρ‖
      = (2 * ρ.re - 1) * Real.log 2 := by
  rw [log_norm_shellTransferCharacter, log_norm_shellTransferCharacter]
  simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  ring

/-- **The four charts of the modular charge, with the tree's own coordinates.** -/
theorem modularCharge_dictionary_xi (ρ : ℂ) {m : ℝ} (hm : 0 < m) :
    (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 / 2 - ρ.re))
        = -(Real.exp (-Real.eulerMascheroniConstant) / Real.log 2)
          * (Real.log ‖shellTransferCharacter (1 - star ρ)‖
            - Real.log ‖shellTransferCharacter ρ‖) ∧
      (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 / 2 - ρ.re))
        = 2 * Real.exp (-Real.eulerMascheroniConstant) / m * (m * shellTransferEntropy ρ) ∧
      2 * (1 / 2 - ρ.re)
        = -((Real.log ‖shellTransferCharacter (1 - star ρ)‖
            - Real.log ‖shellTransferCharacter ρ‖) / Real.log 2) ∧
      2 * (1 / 2 - ρ.re) = 2 / m * (m * shellTransferEntropy ρ) ∧
      2 * (1 / 2 - ρ.re)
        = Real.exp Real.eulerMascheroniConstant
          * (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 / 2 - ρ.re)) ∧
      2 * (1 / 2 - ρ.re) = 1 - 2 * ρ.re := by
  refine modularCharge_dictionary (reρ := ρ.re) (mρ := m) hm ?_ ?_ rfl rfl rfl
  · exact shellReflectionRate_eq ρ
  · rw [shellTransferEntropy_eq]


/-- **The dictionary with the genuine Xi divisor residue in the third chart.**  At a Xi divisor
point of multiplicity `n` the centered affine residue is `n c_ρ`, so the four coordinates are the
Hellinger acceleration `2 e^(−γ) c_ρ`, the shell reflection rate `(2 Re ρ − 1) log 2`, that residue,
and the adelic Weyl drift `2 c_ρ`. -/
theorem modularCharge_dictionary_xi_residue (ρ : ℂ) {n : ℤ} (hn : 0 < n) :
    (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 / 2 - ρ.re))
        = -(Real.exp (-Real.eulerMascheroniConstant) / Real.log 2)
          * (Real.log ‖shellTransferCharacter (1 - star ρ)‖
            - Real.log ‖shellTransferCharacter ρ‖) ∧
      (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 / 2 - ρ.re))
        = 2 * Real.exp (-Real.eulerMascheroniConstant) / (n : ℝ)
          * (-((ρ - 1 / 2) * (n : ℂ))).re ∧
      2 * (1 / 2 - ρ.re)
        = -((Real.log ‖shellTransferCharacter (1 - star ρ)‖
            - Real.log ‖shellTransferCharacter ρ‖) / Real.log 2) ∧
      2 * (1 / 2 - ρ.re) = 2 / (n : ℝ) * (-((ρ - 1 / 2) * (n : ℂ))).re ∧
      2 * (1 / 2 - ρ.re)
        = Real.exp Real.eulerMascheroniConstant
          * (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 / 2 - ρ.re)) ∧
      2 * (1 / 2 - ρ.re) = 1 - 2 * ρ.re := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hres := re_centeredXiAffineResidue_eq_shellTransferEntropy ρ n
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := modularCharge_dictionary_xi ρ (m := (n : ℝ)) hn0
  refine ⟨h1, ?_, h3, ?_, h5, h6⟩
  · rw [hres]; exact h2
  · rw [hres]; exact h4


end RHTower
