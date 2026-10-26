import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheIsometriesOfAReflectionPair

/-!
# The elliptic localizers

Which operations of the spectral plane can localize at an off-line reflection pair
`{ρ, ρ* = 1 − ρ̄}` without acting on it hyperbolically?

* **The reflection-commuting affine group** (`affine_commute_rosatiRefl_iff`): an affine map
  `s ↦ a s + b` commutes with the Rosati reflection `s ↦ 1 − s̄` iff `a` is real and
  `Re b = (1 − a)/2`, i.e. it is `s ↦ ½ + a(s − ½) + iκ`. Such maps carry reflection pairs to
  reflection pairs.
* **The stabilizer of an off-line pair** (`affine_mem_pair_iff`): such a map sends an off-line
  point `ρ` into its pair iff it is the identity or the **point reflection**
  `σ_γ(s) = 1 + 2iγ − s`, `γ = Im ρ`; and `σ_γ` swaps the two points (`sigma_swaps`). A critical
  point `½ + iγ` is fixed by the whole one-parameter family `κ = (1 − a)γ` of dilations about it
  (`affine_fixes_critical_iff`).
* **`σ_γ` is the functional equation conjugated by the archimedean flow**
  (`sigma_eq_tau_comp_fe_comp_tau`): `σ_γ = τ_γ ∘ σ_0 ∘ τ_{−γ}`, `τ_κ(s) = s + iκ`,
  `σ_0(s) = 1 − s`. Point reflections compose to vertical translations (`sigma_comp_sigma`).
* **Elliptic fibres are definite.** On a fibre with the symmetry `G ∘ σ_γ = ± G` the local form is
  `± 2|G(ρ)|²` (`localForm_of_sigma_symmetric`, `localForm_of_sigma_antisymmetric`): the even
  sector is positive at every pair of ordinate `γ` — positivity there cannot exclude it — and the
  odd sector is negative — positivity there excludes it.
* **The dihedral dilemma** (`eq_zero_of_boost_swap_nonneg`): if the local form is nonnegative on
  the complex span of a fibre vector, its image under a boost and their swaps, the vector is zero.
  For Hecke boosts (`hecke_swap_blind`): a positive carrier stable under one Hecke operator and
  under `σ_γ` is blind at every off-line pair of ordinate `γ`.
* **The `σ_γ`-compatible Hecke symbols** (`heckeSymbol_sigma`, `twistedSymSymbol_sigma`,
  `twistedSymSymbol_pair`): `σ_γ` conjugates the Hecke symbol `p^{s−½}` to `p^{2iγ} p^{½−s}`; the
  twisted symmetric symbol `p^{s−½} + p^{2iγ} p^{½−s}` is `σ_γ`-invariant and takes equal values at
  the two points of every pair of ordinate `γ`: it acts there by a scalar, elliptically.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity

/-! ### 1. The reflection-commuting affine group -/

/-- The **Rosati reflection** `s ↦ 1 − s̄` of the spectral plane. -/
def rosatiRefl (s : ℂ) : ℂ := 1 - conj s

theorem rosatiRefl_rosatiRefl (s : ℂ) : rosatiRefl (rosatiRefl s) = s := by
  simp [rosatiRefl]

theorem rosatiRefl_re (s : ℂ) : (rosatiRefl s).re = 1 - s.re := by simp [rosatiRefl]

theorem rosatiRefl_im (s : ℂ) : (rosatiRefl s).im = s.im := by simp [rosatiRefl]

/-- A point is fixed by the Rosati reflection iff it lies on the critical line. -/
theorem rosatiRefl_eq_self_iff (s : ℂ) : rosatiRefl s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    rw [rosatiRefl_re] at this
    linarith
  · intro h
    apply Complex.ext <;> simp [rosatiRefl_re, rosatiRefl_im, h]; norm_num

/-- The affine map `s ↦ a s + b`. -/
def affine (a b : ℂ) (s : ℂ) : ℂ := a * s + b

/-- **Classification.** An affine map commutes with the Rosati reflection iff `a ∈ ℝ` and
`Re b = (1 − a)/2`. -/
theorem affine_commute_rosatiRefl_iff (a b : ℂ) :
    (∀ s, rosatiRefl (affine a b s) = affine a b (rosatiRefl s)) ↔
      a.im = 0 ∧ b.re = (1 - a.re) / 2 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [rosatiRefl, affine, mul_zero, zero_add, map_add, map_zero, sub_zero,
      map_one, mul_one, sub_self] at h0 h1
    have e1 := congrArg Complex.re h0
    have e2 := congrArg Complex.im h0
    have e3 := congrArg Complex.im h1
    simp at e1 e2 e3
    constructor <;> linarith
  · rintro ⟨ha, hb⟩ s
    apply Complex.ext <;>
      simp [rosatiRefl, affine, Complex.mul_re, Complex.mul_im, ha] <;> linarith

/-- **The stabilizer of an off-line point's pair.** A reflection-commuting affine map sends an
off-line point `ρ` into `{ρ, ρ*}` iff it is the identity or the point reflection about
`½ + i Im ρ`. -/
theorem affine_mem_pair_iff {a b ρ : ℂ} (ha : a.im = 0) (hb : b.re = (1 - a.re) / 2)
    (hρ : ρ.re ≠ 1 / 2) :
    (affine a b ρ = ρ ∨ affine a b ρ = rosatiRefl ρ) ↔
      (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 1 + 2 * ρ.im * I) := by
  have hd : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ
  constructor
  · rintro (h | h)
    · left
      have e1 := congrArg Complex.re h
      have e2 := congrArg Complex.im h
      simp [affine, Complex.mul_re, Complex.mul_im, ha] at e1 e2
      have har : a.re = 1 := by
        have : (a.re - 1) * (ρ.re - 1 / 2) = 0 := by rw [hb] at e1; linarith
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · exact absurd h' hd
      refine ⟨Complex.ext (by simp [har]) (by simp [ha]), Complex.ext ?_ ?_⟩
      · simp [hb, har]
      · simp; rw [har] at e2; linarith
    · right
      have e1 := congrArg Complex.re h
      have e2 := congrArg Complex.im h
      simp [affine, rosatiRefl, Complex.mul_re, Complex.mul_im, ha] at e1 e2
      have har : a.re = -1 := by
        have : (a.re + 1) * (ρ.re - 1 / 2) = 0 := by rw [hb] at e1; linarith
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · exact absurd h' hd
      refine ⟨Complex.ext (by simp [har]) (by simp [ha]), Complex.ext ?_ ?_⟩
      · simp [hb, har]
      · simp; rw [har] at e2; linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · left; simp [affine]
    · right
      apply Complex.ext <;> simp [affine, rosatiRefl] <;> ring

/-- A critical point `½ + iγ` is fixed by `s ↦ a s + b` (`a` real, `Re b = (1 − a)/2`) iff
`Im b = (1 − a) γ`: a one-parameter family of dilations about it. -/
theorem affine_fixes_critical_iff {a b : ℂ} (ha : a.im = 0) (hb : b.re = (1 - a.re) / 2) (γ : ℝ) :
    affine a b (1 / 2 + γ * I) = 1 / 2 + γ * I ↔ b.im = (1 - a.re) * γ := by
  constructor
  · intro h
    have := congrArg Complex.im h
    simp [affine, Complex.mul_im, ha] at this
    linarith
  · intro h
    apply Complex.ext <;> simp [affine, Complex.mul_re, Complex.mul_im, ha, hb, h] <;> ring

/-! ### 2. Point reflections and the archimedean flow -/

/-- The **point reflection** `σ_γ(s) = 1 + 2iγ − s` about `½ + iγ`. -/
def sigma (γ : ℝ) (s : ℂ) : ℂ := 1 + 2 * γ * I - s

/-- The **archimedean flow** `τ_κ(s) = s + iκ` on the spectral plane. -/
def tau (κ : ℝ) (s : ℂ) : ℂ := s + κ * I

theorem sigma_eq_affine (γ : ℝ) : sigma γ = affine (-1) (1 + 2 * γ * I) := by
  funext s; simp [sigma, affine]; ring

/-- **`σ_γ` is the functional equation conjugated by the archimedean flow.** -/
theorem sigma_eq_tau_comp_fe_comp_tau (γ : ℝ) (s : ℂ) :
    sigma γ s = tau γ (1 - tau (-γ) s) := by
  simp [sigma, tau]; ring

theorem sigma_zero (s : ℂ) : sigma 0 s = 1 - s := by simp [sigma]

theorem sigma_sigma (γ : ℝ) (s : ℂ) : sigma γ (sigma γ s) = s := by simp [sigma]

/-- Two point reflections compose to a vertical translation. -/
theorem sigma_comp_sigma (c d : ℝ) (s : ℂ) : sigma c (sigma d s) = tau (2 * (c - d)) s := by
  simp [sigma, tau]; ring

/-- `σ_γ` commutes with the Rosati reflection. -/
theorem sigma_rosatiRefl (γ : ℝ) (s : ℂ) : sigma γ (rosatiRefl s) = rosatiRefl (sigma γ s) := by
  apply Complex.ext <;> simp [sigma, rosatiRefl]; ring

/-- **`σ_γ` swaps the two points of every pair of ordinate `γ`.** -/
theorem sigma_swaps {ρ : ℂ} {γ : ℝ} (hγ : ρ.im = γ) :
    sigma γ ρ = rosatiRefl ρ ∧ sigma γ (rosatiRefl ρ) = ρ := by
  have h1 : sigma γ ρ = rosatiRefl ρ := by
    apply Complex.ext <;> simp [sigma, rosatiRefl, hγ]; ring
  exact ⟨h1, by rw [← h1, sigma_sigma]⟩

/-- `σ_γ` fixes exactly the point `½ + iγ`. -/
theorem sigma_eq_self_iff (γ : ℝ) (s : ℂ) : sigma γ s = s ↔ s = 1 / 2 + γ * I := by
  constructor
  · intro h
    have : 2 * s = 1 + 2 * γ * I := by rw [sigma] at h; linear_combination -h
    linear_combination this / 2
  · rintro rfl; simp [sigma]; ring

/-! ### 3. Elliptic fibres are definite -/

/-- **Even sector.** On a fibre with `G ∘ σ_γ = G` the local form of a pair of ordinate `γ` is
`2|G(ρ)|² ≥ 0`. -/
theorem localForm_of_sigma_symmetric {G : ℂ → ℂ} {γ : ℝ} (hG : ∀ s, G (sigma γ s) = G s)
    {ρ : ℂ} (hγ : ρ.im = γ) :
    localForm (G ρ) (G (rosatiRefl ρ)) = 2 * Complex.normSq (G ρ) := by
  rw [← (sigma_swaps hγ).1, hG, localForm_swap_fixed]

/-- **Odd sector.** On a fibre with `G ∘ σ_γ = −G` the local form of a pair of ordinate `γ` is
`−2|G(ρ)|² ≤ 0`. -/
theorem localForm_of_sigma_antisymmetric {G : ℂ → ℂ} {γ : ℝ} (hG : ∀ s, G (sigma γ s) = -G s)
    {ρ : ℂ} (hγ : ρ.im = γ) :
    localForm (G ρ) (G (rosatiRefl ρ)) = -2 * Complex.normSq (G ρ) := by
  rw [← (sigma_swaps hγ).1, hG, localForm, map_neg, mul_neg, Complex.neg_re, Complex.mul_conj,
    Complex.ofReal_re]
  ring

/-! ### 4. The dihedral dilemma -/

/-- **A boost and the swap together blind the pair.** If the local form is nonnegative on the
complex span of `(x, y)`, its boost `(βx, β′y)` (`β′ = β̄⁻¹`, `|β| ≠ 1`), its swap `(y, x)` and
the boosted swap `(βy, β′x)`, then `x = y = 0`. -/
theorem eq_zero_of_boost_swap_nonneg {β : ℂ} (hβ0 : β ≠ 0) (hβ : ‖β‖ ≠ 1) {x y : ℂ}
    (h : ∀ a b c d : ℂ, 0 ≤ localForm (a * x + b * β * x + c * y + d * β * y)
      (a * y + b * (conj β)⁻¹ * y + c * x + d * (conj β)⁻¹ * x)) :
    x = 0 ∧ y = 0 := by
  -- the boost lemma on the vectors `(x, y)`, `(x + y, y + x)` and `(x + iy, y + ix)`
  have h1 : x * conj y = 0 := mul_conj_eq_zero_of_cyclic_nonneg hβ0 hβ fun a b => by
    have := h a b 0 0
    simp only [zero_mul, add_zero] at this
    convert this using 2 <;> ring
  have h2 : (x + y) * conj (y + x) = 0 := mul_conj_eq_zero_of_cyclic_nonneg hβ0 hβ fun a b => by
    have := h a b a b
    convert this using 2 <;> ring
  have h3 : (x + I * y) * conj (y + I * x) = 0 :=
    mul_conj_eq_zero_of_cyclic_nonneg hβ0 hβ fun a b => by
      have := h a b (I * a) (I * b)
      convert this using 2 <;> ring
  -- `x + y = 0`, since `(x + y)(x̄ + ȳ) = |x + y|²`
  have hxy : x + y = 0 := by
    rw [add_comm y x, Complex.mul_conj] at h2
    exact Complex.normSq_eq_zero.mp (by exact_mod_cast h2)
  have hy : y = -x := by linear_combination hxy
  rw [hy] at h3
  have h4 : (2 : ℂ) * Complex.normSq x = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : (x + I * -x) * conj (-x + I * x) = -(2 * (conj x * x)) := by
      simp only [map_add, map_neg, map_mul, Complex.conj_I]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this] at h3
    linear_combination -h3
  have hx : x = 0 := by
    have h5 : (Complex.normSq x : ℂ) = 0 := by
      have h6 := h4
      rw [mul_eq_zero] at h6
      exact h6.resolve_left two_ne_zero
    exact Complex.normSq_eq_zero.mp (by exact_mod_cast h5)
  exact ⟨hx, by rw [hy, hx, neg_zero]⟩

/-- **Hecke separation and elliptic symmetry blind each other.** At an off-line pair, positivity of
the local form on the span of a fibre vector, its image under the Hecke operator at `p > 1`, and
their images under the swap forces the fibre vector to vanish. -/
theorem hecke_swap_blind {p : ℝ} (hp : 1 < p) {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) {x y : ℂ}
    (h : ∀ a b c d : ℂ,
      0 ≤ localForm (a * x + b * heckeSymbol p ρ * x + c * y + d * heckeSymbol p ρ * y)
        (a * y + b * heckeSymbol p (1 - conj ρ) * y + c * x + d * heckeSymbol p (1 - conj ρ) * x)) :
    x = 0 ∧ y = 0 := by
  refine eq_zero_of_boost_swap_nonneg (heckeSymbol_ne_zero p ρ)
    (fun h' => hρ ((norm_heckeSymbol_eq_one_iff hp ρ).mp h')) fun a b c d => ?_
  have := h a b c d
  rwa [heckeSymbol_reflect] at this

/-! ### 5. The `σ_γ`-compatible Hecke symbols -/

/-- **`σ_γ` conjugates a Hecke symbol to its twisted inverse**: `p^{σ_γ(s) − ½} = p^{2iγ} p^{½ − s}`. -/
theorem heckeSymbol_sigma (p γ : ℝ) (s : ℂ) :
    heckeSymbol p (sigma γ s) =
      Complex.exp (2 * γ * I * Real.log p) * (heckeSymbol p s)⁻¹ := by
  rw [heckeSymbol, heckeSymbol, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  simp [sigma]; ring

/-- The **twisted symmetric Hecke symbol** `p^{s−½} + p^{2iγ} p^{½−s}`. -/
def twistedSymSymbol (p γ : ℝ) (s : ℂ) : ℂ :=
  heckeSymbol p s + Complex.exp (2 * γ * I * Real.log p) * (heckeSymbol p s)⁻¹

/-- The twisted symmetric symbol is `σ_γ`-invariant. -/
theorem twistedSymSymbol_sigma (p γ : ℝ) (s : ℂ) :
    twistedSymSymbol p γ (sigma γ s) = twistedSymSymbol p γ s := by
  have he : Complex.exp (2 * γ * I * Real.log p) ≠ 0 := Complex.exp_ne_zero _
  have hh : heckeSymbol p s ≠ 0 := heckeSymbol_ne_zero p s
  rw [twistedSymSymbol, twistedSymSymbol, heckeSymbol_sigma, mul_inv, inv_inv]
  field_simp
  ring

/-- **The twisted symmetric symbol is scalar on every pair of ordinate `γ`.** -/
theorem twistedSymSymbol_pair (p : ℝ) {ρ : ℂ} {γ : ℝ} (hγ : ρ.im = γ) :
    twistedSymSymbol p γ (rosatiRefl ρ) = twistedSymSymbol p γ ρ := by
  rw [← (sigma_swaps hγ).1, twistedSymSymbol_sigma]

/-- At ordinate `γ` the twisted symmetric symbol is `2 p^{iγ} cosh((Re ρ − ½) log p)`. -/
theorem twistedSymSymbol_eq_cosh (p : ℝ) {ρ : ℂ} {γ : ℝ} (hγ : ρ.im = γ) :
    twistedSymSymbol p γ ρ =
      2 * Complex.exp (γ * I * Real.log p) * Complex.cosh (((ρ.re - 1 / 2 : ℝ) : ℂ) * Real.log p) := by
  have hρ : ρ - 1 / 2 = (((ρ.re - 1 / 2 : ℝ) : ℂ)) + γ * I := by
    rw [← hγ]; apply Complex.ext <;> simp
  rw [twistedSymSymbol, heckeSymbol, ← Complex.exp_neg, ← Complex.exp_add, hρ, Complex.cosh,
    show ∀ X Y Z : ℂ, 2 * X * ((Y + Z) / 2) = X * Y + X * Z from fun X Y Z => by ring,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1 <;> congr 1 <;> ring

end GaloisForLFunctions.ArithmeticPolarization
