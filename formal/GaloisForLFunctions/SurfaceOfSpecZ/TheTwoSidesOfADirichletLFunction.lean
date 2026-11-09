import GaloisForLFunctions.SurfaceOfSpecZ.ARealZeroMasksTheShallowerZeros
import GaloisForLFunctions.SquareRootThreshold.DirichletLFunctionTwoBumpCriterion

/-!
# The two sides of a Dirichlet `L`-function

For a primitive character `χ` mod `q > 1` the nontrivial zeros of `L(s, χ)` form a tempered
configuration in the open strip (`SquareRootThreshold.temperedConfig_LZeros`), so the two one-sided
laws of the spline lag structure `S_χ` apply:

* `grh_iff_two_re_lagStructure_le`: GRH for `L(s, χ)` holds iff `2 Re S_χ(u) ≤ K` for `u ≥ 0`
  (`TheOtherSideSeesEveryZero`);
* `re_le_of_two_re_lagStructure_ge_L`: a lower bound `2 Re S_χ(u) ≥ −K` puts every zero at depth
  at most the depth of the deepest real zero (`ARealZeroMasksTheShallowerZeros`).

A real zero `β > ½` of `L(s, χ)`, such as a Siegel zero of a real character, therefore hides from the
Stepanov side exactly the zeros of depth `< β − ½`, and never from the other side.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **GRH from the other side.** -/
theorem grh_iff_two_re_lagStructure_le (hq : 1 < q) (hprim : χ.IsPrimitive) :
    (∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2) ↔
      ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u →
        2 * (lagStructure (ThmE.LZeros (ThmE.LSeam_of hq hprim)) (boxSpline 1 3) u).re ≤ K := by
  set Z := ThmE.LZeros (ThmE.LSeam_of hq hprim) with hZdef
  have hZ := temperedConfig_LZeros hq hprim
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  constructor
  · intro hon
    set L₀ := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ with hL₀
    refine ⟨2 * L₀, fun u _ => ?_⟩
    obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs u
    have hterm : ∀ z, ‖lagCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ =
        ‖lagCoeff Z (boxSpline 1 3) z‖ := by
      intro z
      by_cases hz : lagCoeff Z (boxSpline 1 3) z = 0
      · simp [hz]
      have hmem : (1 / 2 + z) ∈ Z.carrier := by
        by_contra h; exact hz (by rw [lagCoeff, Set.indicator_of_notMem h])
      have hre : z.re = 0 := by have := hon _ hmem; simp at this; linarith
      rw [norm_mul, Complex.norm_exp]
      simp [hre]
    have hle : ‖lagStructure Z (boxSpline 1 3) u‖ ≤ L₀ := by
      rw [he]
      calc ‖∑' z, lagCoeff Z (boxSpline 1 3) z * cexp (z * u)‖
          ≤ ∑' z, ‖lagCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ := norm_tsum_le_tsum_norm hs.norm
        _ = L₀ := tsum_congr hterm
    have h1 := (Complex.abs_re_le_norm (lagStructure Z (boxSpline 1 3) u)).trans hle
    linarith [(abs_le.mp h1).2]
  · rintro ⟨K, hK⟩
    exact onLine_of_two_re_lagStructure_le Z hZ (fun ρ hρ => hρ.2.2) hK

/-- **The Stepanov side of `L(s, χ)`.** If every real zero has depth `≤ x`, a lower bound on the
spline lag structure puts every zero at depth `≤ x`. -/
theorem re_le_of_two_re_lagStructure_ge_L (hq : 1 < q) (hprim : χ.IsPrimitive) {x : ℝ}
    (hx0 : 0 ≤ x)
    (hreal : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.im = 0 → ρ.re ≤ 1 / 2 + x)
    {K : ℝ} (hK : ∀ u : ℝ, 0 ≤ u →
      -K ≤ 2 * (lagStructure (ThmE.LZeros (ThmE.LSeam_of hq hprim)) (boxSpline 1 3) u).re) :
    ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re ≤ 1 / 2 + x :=
  re_le_of_two_re_lagStructure_ge_of_realDepth _ (temperedConfig_LZeros hq hprim) hx0 hreal hK

end GaloisForLFunctions.SurfaceOfSpecZ
