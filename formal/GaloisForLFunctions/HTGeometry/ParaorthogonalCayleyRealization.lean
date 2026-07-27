import GaloisForLFunctions.HTGeometry.ParaorthogonalRootCount
import GaloisForLFunctions.HTGeometry.CayleyUnitCircleReality

/-!
# The Carathéodory--Fejér reality statement is inhabited

Reality in Cayley coordinates says that a paraorthogonal root of the form `lineCayley z` forces `z`
real.  Nothing produced such a root, so the statement had no instance.  Two elementary facts supply
one: the Cayley transform maps the real line onto the unit circle minus `1`, and the terminal
parameter can always be chosen so that `1` is not a root.

* `exists_lineCayley_preimage` — a unimodular `w ≠ 1` is the Cayley image of a real point;
* `exists_unimodular_terminal_not_isRoot_one`;
* **`exists_real_lineCayley_paraorthogonal_root`** — for every polynomial with roots in the open disk
  there is a unimodular terminal parameter and a real point whose Cayley image is a paraorthogonal
  root.
-/

open Polynomial Complex
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {p : ℂ[X]}

/-- Every unimodular point other than `1` is the Cayley image of a real point.  Reality of the
preimage is read off from the norm criterion rather than computed. -/
theorem exists_lineCayley_preimage {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) :
    ∃ z : ℂ, z.im = 0 ∧ lineCayley z = w := by
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  refine ⟨I * (1 + w) / (1 - w), ?_, ?_⟩
  · refine (norm_lineCayley_eq_one_iff_im_eq_zero _).mp ?_
    rw [show lineCayley (I * (1 + w) / (1 - w)) = w from ?_]
    · exact hw
    · have hzI : I * (1 + w) / (1 - w) + I ≠ 0 := by
        have : I * (1 + w) / (1 - w) + I = I * 2 / (1 - w) := by
          field_simp
          ring
        rw [this]
        exact div_ne_zero (by simp) h1w
      rw [lineCayley, div_eq_iff hzI]
      field_simp
      ring
  · have hzI : I * (1 + w) / (1 - w) + I ≠ 0 := by
      have : I * (1 + w) / (1 - w) + I = I * 2 / (1 - w) := by
        field_simp
        ring
      rw [this]
      exact div_ne_zero (by simp) h1w
    rw [lineCayley, div_eq_iff hzI]
    field_simp
    ring

/-- A polynomial with all roots in the open disk does not vanish at `1`. -/
theorem eval_one_ne_zero_of_roots_norm_lt_one (hp : p ≠ 0)
    (hroots : ∀ a ∈ p.roots, ‖a‖ < 1) : p.eval 1 ≠ 0 := by
  intro h
  have : (1 : ℂ) ∈ p.roots := (mem_roots hp).mpr h
  have := hroots 1 this
  simp at this

/-- The terminal parameter can be chosen unimodular so that `1` is not a paraorthogonal root. -/
theorem exists_unimodular_terminal_not_isRoot_one (hp : p ≠ 0)
    (hroots : ∀ a ∈ p.roots, ‖a‖ < 1) :
    ∃ τ : ℂ, ‖τ‖ = 1 ∧ ¬ (finiteParaorthogonalPolynomial p τ).IsRoot 1 := by
  have hp1 : p.eval 1 ≠ 0 := eval_one_ne_zero_of_roots_norm_lt_one hp hroots
  set c : ℂ := (p.map (starRingEnd ℂ)).reverse.eval 1 with hc
  have hval : ∀ τ : ℂ, (finiteParaorthogonalPolynomial p τ).eval 1 = p.eval 1 - τ * c := by
    intro τ
    simp [finiteParaorthogonalPolynomial, hc]
  by_cases hsum : p.eval 1 - c = 0
  · refine ⟨-1, by simp, ?_⟩
    have hcne : c ≠ 0 := by
      intro h0
      rw [h0, sub_zero] at hsum
      exact hp1 hsum
    have : p.eval 1 = c := by linear_combination hsum
    simp only [IsRoot, hval, this]
    intro h
    apply hcne
    linear_combination h / 2
  · exact ⟨1, norm_one, by simpa [IsRoot, hval] using hsum⟩

/-- **The reality statement is inhabited.**  For any polynomial with roots in the open disk there is
a unimodular terminal parameter and a real point whose Cayley image is a paraorthogonal root — so the
Carathéodory--Fejér real-zero theorem has instances. -/
theorem exists_real_lineCayley_paraorthogonal_root (hp : p ≠ 0)
    (hroots : ∀ a ∈ p.roots, ‖a‖ < 1) :
    ∃ (τ z : ℂ), ‖τ‖ = 1 ∧ z.im = 0 ∧
      (finiteParaorthogonalPolynomial p τ).IsRoot (lineCayley z) := by
  obtain ⟨τ, hτ, hone⟩ := exists_unimodular_terminal_not_isRoot_one hp hroots
  obtain ⟨w, hw⟩ := exists_isRoot_finiteParaorthogonalPolynomial hp τ
  have hwnorm : ‖w‖ = 1 := finiteParaorthogonalPolynomial_isRoot_norm_eq_one hp hroots hτ hw
  have hw1 : w ≠ 1 := by
    intro h
    exact hone (h ▸ hw)
  obtain ⟨z, hzim, hzw⟩ := exists_lineCayley_preimage hwnorm hw1
  exact ⟨τ, z, hτ, hzim, by rw [hzw]; exact hw⟩

/-- **The OPUC reality statement is inhabited.**  A positive definite Toeplitz section admits a
unimodular terminal parameter and a real Cayley point that is a paraorthogonal root. -/
theorem exists_real_lineCayley_finiteOPUC_root {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    ∃ (τ z : ℂ), ‖τ‖ = 1 ∧ z.im = 0 ∧
      (finiteParaorthogonalPolynomial (finiteOPUCPolynomial c hG) τ).IsRoot (lineCayley z) :=
  exists_real_lineCayley_paraorthogonal_root (finiteOPUCPolynomial_ne_zero c hG)
    (finiteOPUCPolynomial_roots_norm_lt_one c hG)

end GaloisForLFunctions.HTGeometry
