import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwinsContinuePastTheLine

/-!
# A finite layer can be edited away

The greedy edit of the target of a layer multiplies `ζ` by the factor `L = ∏ (s − ρ_j)(s − ρ̄_j)`.
The greedy edit of the opposite target divides by it.

**Theorem** (`exists_isEdit_layer_removed`).  For `Re ρ_j ≤ b < 1`, `β ∈ (b, 1)` and
`max(b − 13/30, b/2) < c ≤ 1` there is a two-sided edit of the rational primes with count
`A x + O(x^β)` and

`(s − 1) ζ_B(s) · L(s) = (s − 1) ζ(s) · C · e^{H(s)}`, `C ≠ 0`, `H` holomorphic on `Re s > c`.

So `(s − 1) ζ_B(s)` is meromorphic on `Re s > c`; a holomorphic continuation exists only if `ζ`
vanishes on the layer, and then its zeros off the layer are those of `ζ`
(`zero_iff_of_layer_removed`).

**World I** (`exists_isEdit_zero_free_of_finite_layer`).  If the zeros of `ζ` in `Re s > c` are
exactly a finite layer — `(s − 1) ζ(s) = L(s) · W(s)` with `W` holomorphic and zero-free on
`Re s > c` — then the edit has a zeta function without zeros in `Re s > c`: a system over the
rational primes with integer norms and a count rate whose zero-free half-plane is larger than
that of `ζ`.  So AAL follows if no edit with a count rate has a larger zero-free half-plane than
`ζ`; the statement is relative to `ζ` and no edit law decides it.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits

variable {ι : Type*}

/-- The logarithmic derivative of the inverse of a function. -/
theorem logDeriv_fun_inv {L : ℂ → ℂ} {s : ℂ} (h0 : L s ≠ 0) (hd : DifferentiableAt ℂ L s) :
    logDeriv (fun z => (L z)⁻¹) s = -logDeriv L s := by
  have h := hd.hasDerivAt.inv h0
  rw [logDeriv_apply, logDeriv_apply, h.deriv, div_div, pow_two, mul_assoc,
    mul_inv_cancel₀ h0, mul_one, neg_div]

/-- **A finite layer can be edited away.**  The greedy edit of the opposite target of a layer
divides `(s − 1) ζ(s)` by the factor of the layer, up to a zero-free factor on `Re s > c`. -/
theorem exists_isEdit_layer_removed (J : Finset ι) (ρ : ι → ℂ) {b c β : ℝ} (hb0 : 0 < b)
    (hb : b < 1) (hρ : ∀ j ∈ J, (ρ j).re ≤ b) (hc1 : b - 13 / 30 < c) (hc2 : b / 2 < c)
    (hc3 : c ≤ 1) (hβ : b < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ H {s : ℂ | c < s.re} ∧
        ∀ s : ℂ, 1 < s.re → (s - 1) * (editSystem e).zetaSeriesC s * layerFactor J ρ s =
          zetaResidueUnit s * (C * Complex.exp (H s)) := by
  have hρ1 : ∀ j ∈ J, (ρ j).re < 1 := fun j hj => lt_of_le_of_lt (hρ j hj) hb
  have hm : ∀ k : ℕ, 1 ≤ k → |-layerTarget J ρ k| ≤ 2 * J.card * (k : ℝ) ^ (-(1 - b)) :=
    fun k hk => by rw [abs_neg]; exact abs_layerTarget_le J ρ hρ hk
  have hA : (0 : ℝ) ≤ 2 * J.card := by positivity
  have hm0 : -layerTarget J ρ 0 = 0 := by rw [layerTarget_zero hρ1, neg_zero]
  have hfun : (fun k : ℕ => ((-layerTarget J ρ k : ℝ) : ℂ)) =
      -fun k : ℕ => (layerTarget J ρ k : ℂ) := by
    funext k
    simp
  have htwin : IsFactorTwinOn c (editSystem (gedit fun k => -layerTarget J ρ k))
      (fun s => (layerFactor J ρ s)⁻¹) := by
    refine isFactorTwinOn_gedit (m := fun k => -layerTarget J ρ k) (A := 2 * J.card)
      (η := 1 - b) hA (by linarith) (by linarith) (by linarith) (by linarith) hc3 hm0 hm
      (Φ₀ := fun s : ℂ => -∑ j ∈ J, (PrimeEdits.zetaRegular (s - (ρ j - 1)) +
        PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) (ρ j) - 1))))
      ?_ (fun s hs => ?_)
    · refine DifferentiableOn.neg (DifferentiableOn.fun_sum fun j _ => ?_)
      exact ((PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
        (PrimeEdits.differentiable_zetaRegular.comp
          (differentiable_id.sub_const _))).differentiableOn
    · obtain ⟨h1, h2, h3⟩ := logDeriv_layerFactor_eq J ρ hρ1 hs
      refine ⟨inv_ne_zero h1, h2.inv h1, ?_⟩
      rw [logDeriv_fun_inv h1 h2, h3, hfun, LSeries_neg]
      ring
  obtain ⟨C, H, hC, hH, hfac⟩ := htwin
  refine ⟨gedit fun k => -layerTarget J ρ k, isEdit_gedit _,
    editSystem_gedit_count (A := 2 * J.card) (η := 1 - b) hA (by linarith) hm (by linarith) hβ1,
    C, H, hC, hH, fun s hs => ?_⟩
  have h1 := (logDeriv_layerFactor_eq J ρ hρ1 hs).1
  rw [hfac s hs]
  calc zetaResidueUnit s * (C * (layerFactor J ρ s)⁻¹ * Complex.exp (H s)) * layerFactor J ρ s
      = zetaResidueUnit s * (C * Complex.exp (H s)) *
          ((layerFactor J ρ s)⁻¹ * layerFactor J ρ s) := by ring
    _ = zetaResidueUnit s * (C * Complex.exp (H s)) := by rw [inv_mul_cancel₀ h1, mul_one]

/-- **The zeros of the system with a layer removed.**  If `(s − 1) ζ_B(s) · L(s)` is
`(s − 1) ζ(s)` times a zero-free factor and `G` continues `(s − 1) ζ_B(s)` to `Re s > c`, then
`ζ` vanishes on the layer, and off the layer the zeros of `G` are those of `ζ`. -/
theorem zero_iff_of_layer_removed {B : BeurlingSystem} (J : Finset ι) (ρ : ι → ℂ) {c : ℝ}
    {C : ℂ} {H G : ℂ → ℂ} (hC : C ≠ 0) (hH : DifferentiableOn ℂ H {s : ℂ | c < s.re})
    (hfac : ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s * layerFactor J ρ s =
      zetaResidueUnit s * (C * Complex.exp (H s)))
    (hG : DifferentiableOn ℂ G {s : ℂ | c < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) {z : ℂ} (hz : c < z.re)
    (hz1 : z ≠ 1) :
    (layerFactor J ρ z = 0 → riemannZeta z = 0) ∧
      (layerFactor J ρ z ≠ 0 → (G z = 0 ↔ riemannZeta z = 0)) := by
  have heq := BalanceLaw.eqOn_halfPlane (c := c)
    (hG.mul (differentiable_layerFactor J ρ).differentiableOn)
    (differentiable_zetaResidueUnit.differentiableOn.mul
      ((differentiableOn_const C).mul hH.cexp))
    (fun s hs => by rw [hGeq s hs]; exact hfac s hs)
    (show z ∈ {s : ℂ | c < s.re} from hz)
  have hE : C * Complex.exp (H z) ≠ 0 := mul_ne_zero hC (Complex.exp_ne_zero _)
  have hu : zetaResidueUnit z = (z - 1) * riemannZeta z := zetaResidueUnit_of_ne hz1
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have heq' : G z * layerFactor J ρ z = (z - 1) * riemannZeta z * (C * Complex.exp (H z)) := by
    rw [← hu]
    exact heq
  refine ⟨fun hL => ?_, fun hL => ⟨fun hGz => ?_, fun hζ => ?_⟩⟩
  · rw [hL, mul_zero] at heq'
    rcases mul_eq_zero.mp heq'.symm with h | h
    · exact (mul_eq_zero.mp h).resolve_left hz1'
    · exact absurd h hE
  · rw [hGz, zero_mul] at heq'
    rcases mul_eq_zero.mp heq'.symm with h | h
    · exact (mul_eq_zero.mp h).resolve_left hz1'
    · exact absurd h hE
  · rw [hζ, mul_zero, zero_mul] at heq'
    exact (mul_eq_zero.mp heq').resolve_right hL

/-- **World I gives an edit with a larger zero-free half-plane.**  If the zeros of `ζ` in
`Re s > c` are exactly the points of a finite layer with their multiplicities, the edit that
removes the layer has a zeta function without zeros in `Re s > c`. -/
theorem exists_isEdit_zero_free_of_finite_layer (J : Finset ι) (ρ : ι → ℂ) {b c β : ℝ}
    (hb0 : 0 < b) (hb : b < 1) (hρ : ∀ j ∈ J, (ρ j).re ≤ b) (hc1 : b - 13 / 30 < c)
    (hc2 : b / 2 < c) (hc3 : c ≤ 1) (hβ : b < β) (hβ1 : β < 1) {W : ℂ → ℂ}
    (hW : DifferentiableOn ℂ W {s : ℂ | c < s.re}) (hW0 : ∀ s : ℂ, c < s.re → W s ≠ 0)
    (hζ : ∀ s : ℂ, c < s.re → zetaResidueUnit s = layerFactor J ρ s * W s) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | c < s.re} ∧
        (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
        ∀ s : ℂ, c < s.re → G s ≠ 0 := by
  obtain ⟨e, he, hcount, C, H, hC, hH, hfac⟩ :=
    exists_isEdit_layer_removed J ρ hb0 hb hρ hc1 hc2 hc3 hβ hβ1
  have hρ1 : ∀ j ∈ J, (ρ j).re < 1 := fun j hj => lt_of_le_of_lt (hρ j hj) hb
  refine ⟨e, he, hcount, fun s => W s * (C * Complex.exp (H s)),
    hW.mul ((differentiableOn_const C).mul hH.cexp), fun s hs => ?_,
    fun s hs => mul_ne_zero (hW0 s hs) (mul_ne_zero hC (Complex.exp_ne_zero _))⟩
  have hL := (logDeriv_layerFactor_eq J ρ hρ1 hs).1
  have h1 := hfac s hs
  rw [hζ s (lt_of_le_of_lt hc3 hs)] at h1
  have h2 : (s - 1) * (editSystem e).zetaSeriesC s * layerFactor J ρ s =
      W s * (C * Complex.exp (H s)) * layerFactor J ρ s := by
    rw [h1]
    ring
  exact (mul_right_cancel₀ hL h2).symm

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
