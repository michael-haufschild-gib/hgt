import GaloisForLFunctions.RHTower.ShiftedGammaNumericalRange
import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse

/-!
# Logarithmic coercivity of the Gamma-wall generator

The phase generator on the shifted line is

`B(x+iσ) = (1/2)(r(x+iσ)·I − T) + i/(2z)·I`,   `r(z) = ψ(1+iz) + ψ(1−iz) + 2γ`,

and its numerical range is governed entirely by the real part of the scalar symbol.  Each of the two
digamma abscissas `1−σ` and `1+σ` contributes a full logarithm of the frequency: the lower one
directly, by the archimedean coercivity of the digamma on a vertical line; the upper one after a
single step of the digamma recurrence, whose residue `1/(σ−ix)` has nonnegative real part.  The
branch factor `i/(2z)` likewise has nonnegative real part on the upper shifted line, and the
self-adjoint part costs at most `‖T‖/2`.  Hence

`Re⟪B(x+iσ)u, u⟫ ≥ (log(2+|x|) − C_σ/2 − ‖T‖/2)‖u‖²`

with an explicit constant, and the shifted generator `B + L·I` is boundedly invertible with the
reciprocal bound as soon as the sum of the frequency logarithm and the position `L` exceeds that
constant.

The two contributions add, and that is what makes the one-block estimate uniform: beyond the
threshold `C₀e^{max(0,−m)}` the frequency logarithm supplies `max(0,−m)`, which cancels the block
position `m` exactly, so the floor is bounded below by a constant that does not see the block.
-/

open Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The coercivity constant of the shifted Gamma symbol. -/
def wallSymbolCoercivityConst (σ : ℝ) : ℝ :=
  _root_.RHTower.digammaVerticalCoercivityConst (1 - σ)
    + _root_.RHTower.digammaVerticalCoercivityConst σ - 2 * Real.eulerMascheroniConstant

/-- The upper abscissa is reduced to the lower one by the digamma recurrence. -/
theorem re_digamma_upper_ge {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    Real.log (2 + |x|) - _root_.RHTower.digammaVerticalCoercivityConst σ
      ≤ (Complex.digamma (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I)).re := by
  set s : ℂ := ((σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by
    rw [hs]
    simp
  have hpoles : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hc
    have := congrArg Complex.re hc
    rw [hsre] at this
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hstep := Complex.digamma_apply_add_one s hpoles
  have hshift : s + 1 = ((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I := by
    rw [hs]
    push_cast
    ring
  have hinv : 0 ≤ (s⁻¹).re := by
    rw [Complex.inv_re, hsre]
    exact div_nonneg hσ0.le (Complex.normSq_nonneg s)
  have hbase := _root_.RHTower.re_digamma_vertical_ge hσ0 hσ1.le (-x)
  rw [abs_neg] at hbase
  rw [← hshift, hstep, Complex.add_re]
  linarith

/-- **The shifted Gamma symbol grows like twice the logarithm.**  Each of the two digamma
abscissas contributes a full logarithm: the lower one directly, the upper one after one step of the
digamma recurrence, whose residue `1/(σ - ix)` has nonnegative real part. -/
theorem two_log_sub_le_re_wallSymbol {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    2 * Real.log (2 + |x|) - wallSymbolCoercivityConst σ ≤ (wallSymbol σ x).re := by
  have hlow0 : (0 : ℝ) < 1 - σ := by linarith
  have hlow1 : (1 : ℝ) - σ ≤ 1 := by linarith
  have h₁ := _root_.RHTower.re_digamma_vertical_ge hlow0 hlow1 x
  have h₂ := re_digamma_upper_ge hσ0 hσ1 x
  have hγ : (2 * (Real.eulerMascheroniConstant : ℂ)).re = 2 * Real.eulerMascheroniConstant := by
    simp
  rw [wallSymbol, Complex.add_re, Complex.add_re, hγ, wallSymbolCoercivityConst]
  linarith [h₁, h₂]

/-! ## The generator -/

/-- The scalar part of the Gamma-wall phase generator on the shifted line. -/
def wallGeneratorScalar (σ x : ℝ) : ℂ :=
  wallSymbol σ x / 2 + Complex.I / (2 * ((x : ℂ) + (σ : ℂ) * Complex.I))

/-- The branch factor `i/(2z)` never lowers the numerical range on the upper shifted line. -/
theorem re_branchTerm_nonneg {σ : ℝ} (hσ0 : 0 < σ) (x : ℝ) :
    0 ≤ (Complex.I / (2 * ((x : ℂ) + (σ : ℂ) * Complex.I))).re := by
  set w : ℂ := 2 * ((x : ℂ) + (σ : ℂ) * Complex.I) with hw
  have him : w.im = 2 * σ := by
    rw [hw]
    simp
  have hre : (Complex.I / w).re = w.im / Complex.normSq w := by
    rw [Complex.div_re]
    simp
  rw [hre, him]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg w)

theorem re_wallGeneratorScalar_ge {σ : ℝ} (hσ0 : 0 < σ) (x : ℝ) :
    (wallSymbol σ x).re / 2 ≤ (wallGeneratorScalar σ x).re := by
  have h := re_branchTerm_nonneg hσ0 x
  have hdiv : (wallSymbol σ x / 2).re = (wallSymbol σ x).re / 2 := by
    rw [Complex.div_re]
    simp
    ring
  rw [wallGeneratorScalar, Complex.add_re, hdiv]
  linarith

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The Gamma-wall phase generator on the shifted line. -/
def wallGenerator (T : X →L[ℂ] X) (σ x : ℝ) : X →L[ℂ] X :=
  wallGeneratorScalar σ x • ContinuousLinearMap.id ℂ X - (1 / 2 : ℂ) • T

/-- The floor supplied by the symbol at a given frequency. -/
def wallFloor (T : X →L[ℂ] X) (σ x : ℝ) : ℝ :=
  Real.log (2 + |x|) - wallSymbolCoercivityConst σ / 2 - ‖T‖ / 2

/-- **`(15)`'s input: the generator has a logarithmically growing numerical floor.** -/
theorem re_inner_wallGenerator_ge {T : X →L[ℂ] X} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : ℝ) (u : X) :
    wallFloor T σ x * ‖u‖ ^ (2 : ℕ) ≤ (inner ℂ (wallGenerator T σ x u) u).re := by
  have happ : wallGenerator T σ x u = wallGeneratorScalar σ x • u - (1 / 2 : ℂ) • T u := by
    rw [wallGenerator]
    simp
  have hself : (inner ℂ u u : ℂ) = ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hinner : (inner ℂ (wallGenerator T σ x u) u : ℂ)
      = (starRingEnd ℂ) (wallGeneratorScalar σ x) * ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ)
        - (starRingEnd ℂ) (1 / 2 : ℂ) * (inner ℂ (T u) u : ℂ) := by
    rw [happ, inner_sub_left, inner_smul_left, inner_smul_left, hself]
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 : ℂ) / 2 := by
    simp [Complex.ext_iff]
  have hA : ((starRingEnd ℂ) (wallGeneratorScalar σ x) * ((‖u‖ ^ (2 : ℕ) : ℝ) : ℂ)).re
      = (wallGeneratorScalar σ x).re * ‖u‖ ^ (2 : ℕ) := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hB : (((1 : ℂ) / 2) * (inner ℂ (T u) u : ℂ)).re = (inner ℂ (T u) u).re / 2 := by
    rw [Complex.mul_re]
    norm_num
    ring
  have hre : (inner ℂ (wallGenerator T σ x u) u).re
      = (wallGeneratorScalar σ x).re * ‖u‖ ^ (2 : ℕ) - (inner ℂ (T u) u).re / 2 := by
    rw [hinner, hhalf, Complex.sub_re, hA, hB]
  have hT : (inner ℂ (T u) u).re ≤ ‖T‖ * ‖u‖ ^ (2 : ℕ) := by
    have h1 : (inner ℂ (T u) u).re ≤ ‖(inner ℂ (T u) u : ℂ)‖ := Complex.re_le_norm _
    have h2 : ‖(inner ℂ (T u) u : ℂ)‖ ≤ ‖T u‖ * ‖u‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    have h3 : ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
    calc (inner ℂ (T u) u).re ≤ ‖T u‖ * ‖u‖ := le_trans h1 h2
      _ ≤ (‖T‖ * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = ‖T‖ * ‖u‖ ^ (2 : ℕ) := by ring
  have hsym := two_log_sub_le_re_wallSymbol hσ0 hσ1 x
  have hscal := re_wallGeneratorScalar_ge hσ0 x
  have hnn : (0 : ℝ) ≤ ‖u‖ ^ (2 : ℕ) := sq_nonneg _
  rw [hre, wallFloor]
  nlinarith [hsym, hscal, hT, hnn]

/-! ## The block threshold -/

/-- **`(14)`: the frequency threshold turns the block index into a uniform floor.**  Beyond
`C₀e^{max(0,-m)}` the frequency logarithm supplies `max(0,-m)`, which cancels the position term `m`
of the block, so the floor is bounded below by a constant depending on nothing but `C₀`, the symbol
and the operator norm. -/
theorem wallFloor_add_ge_of_threshold {T : X →L[ℂ] X} {σ : ℝ} {C₀ m L x : ℝ} (hC₀ : 0 < C₀)
    (hx : C₀ * Real.exp (max 0 (-m)) ≤ |x|) (hL : m ≤ L) :
    Real.log C₀ - wallSymbolCoercivityConst σ / 2 - ‖T‖ / 2 ≤ wallFloor T σ x + L := by
  have hpos : (0 : ℝ) < C₀ * Real.exp (max 0 (-m)) := by positivity
  have h2x : C₀ * Real.exp (max 0 (-m)) ≤ 2 + |x| := by linarith
  have hlog : Real.log (C₀ * Real.exp (max 0 (-m))) ≤ Real.log (2 + |x|) :=
    Real.log_le_log hpos h2x
  have hsplit : Real.log (C₀ * Real.exp (max 0 (-m))) = Real.log C₀ + max 0 (-m) := by
    rw [Real.log_mul (ne_of_gt hC₀) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hmax : 0 ≤ max 0 (-m) + m := by
    rcases le_total 0 m with hm | hm
    · rw [max_eq_left (by linarith)]
      linarith
    · rw [max_eq_right (by linarith)]
      linarith
  rw [hsplit] at hlog
  rw [wallFloor]
  linarith

/-- **The threshold can be chosen to give any prescribed floor.** -/
theorem exists_threshold_wallFloor (T : X →L[ℂ] X) (σ μ₀ : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m L x : ℝ, C₀ * Real.exp (max 0 (-m)) ≤ |x| → m ≤ L →
      μ₀ ≤ wallFloor T σ x + L := by
  refine ⟨Real.exp (μ₀ + wallSymbolCoercivityConst σ / 2 + ‖T‖ / 2), Real.exp_pos _,
    fun m L x hx hL => ?_⟩
  have hbase := wallFloor_add_ge_of_threshold (T := T) (σ := σ) (Real.exp_pos _) hx hL
  rw [Real.log_exp] at hbase
  linarith

/-! ## The resolvent -/

variable [CompleteSpace X]

/-- **`(15)`: the shifted Gamma-wall generator is boundedly invertible, with the reciprocal
logarithmic bound.**  The position variable enters the floor additively, so the frequency logarithm
and the physical block index cooperate: either alone suffices to open the gap. -/
theorem exists_inverse_wallGenerator_shift {T : X →L[ℂ] X} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x L : ℝ) (hgap : 0 < wallFloor T σ x + L) :
    ∃ S : X →L[ℂ] X,
      (∀ v, (wallGenerator T σ x + (L : ℂ) • ContinuousLinearMap.id ℂ X) (S v) = v) ∧
      (∀ u, S ((wallGenerator T σ x + (L : ℂ) • ContinuousLinearMap.id ℂ X) u) = u) ∧
      ∀ v, ‖S v‖ ≤ (wallFloor T σ x + L)⁻¹ * ‖v‖ := by
  have hfloor : ∀ u : X,
      wallFloor T σ x * ‖u‖ ^ (2 : ℕ) ≤ (inner ℂ (wallGenerator T σ x u) u).re + 0 * ‖u‖ ^ (2 : ℕ) := by
    intro u
    have := re_inner_wallGenerator_ge (T := T) hσ0 hσ1 x u
    linarith
  have hg : 0 < wallFloor T σ x + L - 0 := by linarith
  have hres := GaloisForLFunctions.HTGeometry.exists_inverse_of_shifted hfloor hg
  obtain ⟨S, h₁, h₂, h₃⟩ := hres
  refine ⟨S, h₁, h₂, fun v => ?_⟩
  have := h₃ v
  rwa [sub_zero] at this

end GaloisForLFunctions.RHTower
