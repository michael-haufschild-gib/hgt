import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Weights

/-!
# The positive chamber is silent on the critical strip

A Gindikin–Karpelevich factor `Z(⟨λ, β∨⟩)/Z(⟨λ, β∨⟩ + 1)` has a pole on the **zero hyperplane**
`⟨λ, β∨⟩ = ρ − 1` of each zero `ρ`. Holomorphy of an Eisenstein series on a set `S` of spectral
parameters excludes the zeros in the **certified set** `{ρ : ⟨λ, β∨⟩ = ρ − 1, λ ∈ S, β > 0}`.

The a priori analytic information on Eisenstein series (absolute convergence in the Godement
chamber, Maass–Selberg positivity and holomorphy on the closed positive chamber and its unitary
boundary) lives on the closed positive chamber. For affine `A₁`:

* every positive real root pairs with the closed chamber in real part `≥ 0`
  (`rootArgument_re_nonneg`), so no zero hyperplane with `Re ρ < 1` meets it;
* the certified set of the closed chamber is exactly `{Re ρ ≥ 1}` (`certified_closedChamber`), the
  boundary line of the prime number theorem; that of the Godement chamber is `{Re ρ > 2}`
  (`certified_godementChamber`);
* in the image `w·C` of the closed chamber a zero hyperplane of a positive root `β` can only appear
  if `β` is inverted by `w⁻¹` (`mem_inversions_of_re_neg`): zeros reach the Tits cone only through
  the transported factors of the functional equations, which carry them as poles.
-/

namespace GaloisForLFunctions.RHTower.InfiniteSymmetry

open HTGeometry.LoopEisenstein.AffineA1

/-- The closed positive chamber in simple-coroot coordinates. -/
def ClosedChamber (lam : ℂ × ℂ) : Prop := 0 ≤ lam.1.re ∧ 0 ≤ lam.2.re

/-- The Godement chamber of absolute convergence. -/
def GodementChamber (lam : ℂ × ℂ) : Prop := 1 < lam.1.re ∧ 1 < lam.2.re

/-- Zeros excluded by holomorphy on `S`: those whose hyperplane `⟨λ, β∨⟩ = ρ − 1` meets `S`. -/
def certifiedZeroFree (S : Set (ℂ × ℂ)) : Set ℂ :=
  {ρ | ∃ lam ∈ S, ∃ β : Root, β.positive ∧ rootArgument lam β = ρ - 1}

lemma rootArgument_re (lam : ℂ × ℂ) (β : Root) :
    (rootArgument lam β).re = (β.corootZero : ℝ) * lam.1.re + (β.corootOne : ℝ) * lam.2.re := by
  simp [rootArgument, Complex.add_re, Complex.mul_re]

/-- Positive real roots pair with the closed chamber in nonnegative real part. -/
theorem rootArgument_re_nonneg {lam : ℂ × ℂ} (h : ClosedChamber lam) {β : Root}
    (hβ : β.positive) : 0 ≤ (rootArgument lam β).re := by
  obtain ⟨h₀, h₁⟩ := (Root.positive_iff_coroot β).mp hβ
  rw [rootArgument_re]
  have h₀' : (0 : ℝ) ≤ β.corootZero := by exact_mod_cast h₀
  have h₁' : (0 : ℝ) ≤ β.corootOne := by exact_mod_cast h₁
  exact add_nonneg (mul_nonneg h₀' h.1) (mul_nonneg h₁' h.2)

/-- No zero hyperplane of a zero with `Re ρ < 1` meets the closed chamber. -/
theorem zeroHyperplane_not_closedChamber {lam : ℂ × ℂ} (h : ClosedChamber lam) {β : Root}
    (hβ : β.positive) {ρ : ℂ} (hρ : ρ.re < 1) : rootArgument lam β ≠ ρ - 1 := by
  intro he
  have := rootArgument_re_nonneg h hβ
  rw [he, Complex.sub_re, Complex.one_re] at this
  linarith

/-- **Holomorphy on the closed chamber certifies exactly `Re ρ ≥ 1`.** -/
theorem certified_closedChamber :
    certifiedZeroFree {lam | ClosedChamber lam} = {ρ : ℂ | 1 ≤ ρ.re} := by
  ext ρ
  constructor
  · rintro ⟨lam, hlam, β, hβ, he⟩
    have := rootArgument_re_nonneg hlam hβ
    rw [he, Complex.sub_re, Complex.one_re] at this
    simp only [Set.mem_setOf_eq]
    linarith
  · intro hρ
    simp only [Set.mem_setOf_eq] at hρ
    refine ⟨(0, ρ - 1), ⟨by simp, by simp [hρ]⟩, .plus 0, by simp [Root.positive], ?_⟩
    simp [rootArgument, Root.corootZero, Root.corootOne]

/-- Absolute convergence certifies exactly `Re ρ > 2`. -/
theorem certified_godementChamber :
    certifiedZeroFree {lam | GodementChamber lam} = {ρ : ℂ | 2 < ρ.re} := by
  ext ρ
  constructor
  · rintro ⟨lam, ⟨h₀, h₁⟩, β, hβ, he⟩
    have hre := rootArgument_re lam β
    rw [he, Complex.sub_re, Complex.one_re] at hre
    obtain ⟨c₀, c₁⟩ := (Root.positive_iff_coroot β).mp hβ
    have hc := Root.coroot_ne_zero β
    have c₀' : (0 : ℝ) ≤ β.corootZero := by exact_mod_cast c₀
    have c₁' : (0 : ℝ) ≤ β.corootOne := by exact_mod_cast c₁
    have hsum : (1 : ℝ) ≤ β.corootZero + β.corootOne := by
      have : (1 : ℤ) ≤ β.corootZero + β.corootOne := by omega
      exact_mod_cast this
    -- `Re ρ − 1 ≥ (c₀ + c₁)(1 + m)` with `m = min(Re λ₀, Re λ₁) − 1 > 0`
    set m := min (lam.1.re - 1) (lam.2.re - 1)
    have hm : 0 < m := lt_min (by linarith) (by linarith)
    have e₀ := mul_le_mul_of_nonneg_left (min_le_left (lam.1.re - 1) (lam.2.re - 1)) c₀'
    have e₁ := mul_le_mul_of_nonneg_left (min_le_right (lam.1.re - 1) (lam.2.re - 1)) c₁'
    have e₂ := mul_le_mul_of_nonneg_right hsum hm.le
    simp only [Set.mem_setOf_eq]
    nlinarith
  · intro hρ
    simp only [Set.mem_setOf_eq] at hρ
    refine ⟨(2, ρ - 1), ⟨by simp, by simp; linarith⟩, .plus 0, by simp [Root.positive], ?_⟩
    simp [rootArgument, Root.corootZero, Root.corootOne]

/-- The closed chamber in affine-weight coordinates `(level − finite, finite)`. -/
def WeightChamber (L : Weight) : Prop := ClosedChamber (L.level - L.finite, L.finite)

/-- The level is Weyl-invariant, so the whole Tits cone has `Re(level) ≥ 0`. -/
theorem level_re_nonneg (L : Weight) (hL : WeightChamber L) (w : Weyl) :
    0 ≤ (weightAct w L).level.re := by
  rw [weightAct_level]
  obtain ⟨h₀, h₁⟩ := hL
  simp only [Complex.sub_re] at h₀ h₁
  linarith

/-- **Zeros enter `w·C` only through inverted roots.** If a positive root pairs with a point of
`w·C` in negative real part, it is inverted by `w⁻¹`; its ratio factor is one of the finitely many
factors transported by the functional equation from `C` to `w·C`. -/
theorem mem_inversions_of_re_neg (L : Weight) (hL : WeightChamber L) (w : Weyl) (β : Root)
    (hβ : β.positive)
    (h : (rootArgument ((weightAct w L).level - (weightAct w L).finite,
      (weightAct w L).finite) β).re < 0) :
    β ∈ inversions w⁻¹ := by
  rw [rootArgument_weightAct] at h
  rw [mem_inversions]
  refine ⟨hβ, fun hpos => ?_⟩
  exact absurd (rootArgument_re_nonneg hL hpos) (not_le.mpr h)

/-- In each chamber of the Tits cone only finitely many zero hyperplanes of positive roots appear. -/
theorem zeroHyperplanes_finite (L : Weight) (hL : WeightChamber L) (w : Weyl) :
    {β : Root | β.positive ∧ (rootArgument ((weightAct w L).level - (weightAct w L).finite,
      (weightAct w L).finite) β).re < 0}.Finite :=
  (inversions w⁻¹).finite_toSet.subset fun β hβ =>
    mem_inversions_of_re_neg L hL w β hβ.1 hβ.2

end GaloisForLFunctions.RHTower.InfiniteSymmetry
