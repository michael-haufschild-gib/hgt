import GaloisForLFunctions.RHTower.BohrSetCharacterSum
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.BohrAverage

/-!
# The dense model attached to a Bohr set

For a function `F` on `(ZMod q)ˣ` and a set `B ⊆ (ZMod q)ˣ`, the *dense model*

```
denseModel F B a = φ(q)/#B² · ∑_{b₁, b₂ ∈ B} F(a b₁ b₂⁻¹)
```

has Fourier coefficients equal to those of `F` scaled by `‖E_{b ∈ B} χ(b)‖²`
(`denseModel_fourier`, `denseModel_fourier_real`).  Since that factor lies in `[0,1]`, the model
never increases a coefficient (`norm_denseModel_fourier_le`) and the transference error never
exceeds the original coefficient (`norm_sub_denseModel_fourier_le`); at the principal character
the factor is `1`, so the total mass is preserved (`denseModel_mass`).  When `B` is a Bohr set for
`χ` of radius `c`, the factor is within `2c + c²` of `1`
(`norm_sub_denseModel_fourier_le_of_close`).

Finally, for the kernel of a quadratic character `ψ` — an index-two subgroup — the model preserves
the mass of any coset up to half the transference error at `ψ` (`denseModel_coset`).

These are items (ii), (iii), (iv) and (v) of the multiplicative dense model theorem of
Matomäki--Teräväinen (*Products of primes in arithmetic progressions*, Proposition 4.1; quoted as
Proposition 3.3 of *Linnik's problem for multiplicative functions*), in the group-theoretic form
that carries all of their content.
-/

open Finset

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.AddComb

variable {n : ℕ}

/-- The Fourier coefficient of a function on the unit group at a Dirichlet character. -/
def unitFourier (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ) (χ : DirichletCharacter ℂ (n + 1)) : ℂ :=
  ∑ u : (ZMod (n + 1))ˣ, (F u : ℂ) * (starRingEnd ℂ) (χ (u : ZMod (n + 1)))

/-- The normalised character average of a Bohr-type set. -/
def bohrAvg (n : ℕ) (B : Finset (ZMod (n + 1))ˣ) (χ : DirichletCharacter ℂ (n + 1)) : ℂ :=
  ((B.card : ℂ))⁻¹ * ∑ b ∈ B, χ (b : ZMod (n + 1))

/-- The dense model of `F` relative to a Bohr-type set `B`. -/
def denseModel (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ) (B : Finset (ZMod (n + 1))ˣ)
    (a : (ZMod (n + 1))ˣ) : ℝ :=
  ((n + 1).totient : ℝ) / ((B.card : ℝ) * (B.card : ℝ)) * ∑ b₁ ∈ B, ∑ b₂ ∈ B, F (a * b₁ * b₂⁻¹)

/-- The character `ψ` attached to a Dirichlet character on the unit group is multiplicative and
unimodular in the sense needed by `bohr_convolution_identity`. -/
theorem unitChar_mul (n : ℕ) (χ : DirichletCharacter ℂ (n + 1)) (x y : (ZMod (n + 1))ˣ) :
    χ (((x * y : (ZMod (n + 1))ˣ) : ZMod (n + 1)))
      = χ (x : ZMod (n + 1)) * χ (y : ZMod (n + 1)) := by
  rw [Units.val_mul, map_mul]

theorem unitChar_conj (n : ℕ) (χ : DirichletCharacter ℂ (n + 1)) (x : (ZMod (n + 1))ˣ) :
    (starRingEnd ℂ) (χ (x : ZMod (n + 1)))
      = χ (((x⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1))) := by
  rw [conj_char n χ x]
  congr 1
  exact ZMod.inv_coe_unit x

/-- **The Fourier transform of the dense model.**  Each coefficient is multiplied by
`|E_{b ∈ B} χ(b)|²`. -/
theorem denseModel_fourier (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ) (B : Finset (ZMod (n + 1))ˣ)
    (hB : B.Nonempty) (χ : DirichletCharacter ℂ (n + 1)) :
    ((((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
        (denseModel n F B a : ℂ) * (starRingEnd ℂ) (χ (a : ZMod (n + 1))))
      = bohrAvg n B χ * (starRingEnd ℂ) (bohrAvg n B χ) * unitFourier n F χ := by
  classical
  have hBcard : ((B.card : ℂ)) ≠ 0 := by
    have hpos : 0 < B.card := Finset.card_pos.2 hB
    exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
  have hphi : (((n + 1).totient : ℂ)) ≠ 0 := by
    have hpos : 0 < (n + 1).totient := Nat.totient_pos.2 (by omega)
    exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
  have hkey := bohr_convolution_identity
    (Γ := (ZMod (n + 1))ˣ)
    (fun x => χ (x : ZMod (n + 1))) (unitChar_mul n χ) (unitChar_conj n χ)
    (fun u => (F u : ℂ)) B
  have hcast : ∀ a : (ZMod (n + 1))ˣ, ((denseModel n F B a : ℝ) : ℂ)
      = (((n + 1).totient : ℂ)) / ((B.card : ℂ) * (B.card : ℂ))
        * ∑ b₁ ∈ B, ∑ b₂ ∈ B, ((F (a * b₁ * b₂⁻¹) : ℝ) : ℂ) := by
    intro a
    rw [denseModel]
    push_cast
    ring
  simp only [hcast]
  have hpull : ∑ a : (ZMod (n + 1))ˣ,
      ((((n + 1).totient : ℂ)) / ((B.card : ℂ) * (B.card : ℂ))
        * ∑ b₁ ∈ B, ∑ b₂ ∈ B, ((F (a * b₁ * b₂⁻¹) : ℝ) : ℂ))
        * (starRingEnd ℂ) (χ (a : ZMod (n + 1)))
      = (((n + 1).totient : ℂ)) / ((B.card : ℂ) * (B.card : ℂ))
        * ∑ a : (ZMod (n + 1))ˣ, (∑ b₁ ∈ B, ∑ b₂ ∈ B, ((F (a * b₁ * b₂⁻¹) : ℝ) : ℂ))
            * (starRingEnd ℂ) (χ (a : ZMod (n + 1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [hpull, hkey, bohrAvg, map_mul, map_inv₀, Complex.conj_natCast, unitFourier]
  field_simp


theorem norm_unitChar (n : ℕ) (χ : DirichletCharacter ℂ (n + 1)) (b : (ZMod (n + 1))ˣ) :
    ‖χ (b : ZMod (n + 1))‖ = 1 := by
  have h1 : χ (b : ZMod (n + 1)) * (starRingEnd ℂ) (χ (b : ZMod (n + 1))) = 1 := by
    rw [unitChar_conj n χ b, ← unitChar_mul n χ b b⁻¹]
    simp
  have h2 : ((‖χ (b : ZMod (n + 1))‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    exact h1
  have h3 : ‖χ (b : ZMod (n + 1))‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg (χ (b : ZMod (n + 1))), h3]

theorem norm_bohrAvg_le_one (n : ℕ) (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty)
    (χ : DirichletCharacter ℂ (n + 1)) : ‖bohrAvg n B χ‖ ≤ 1 := by
  have hcard : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hB
  rw [bohrAvg, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ b ∈ B, χ (b : ZMod (n + 1))‖ ≤ (B.card : ℝ) := by
    calc ‖∑ b ∈ B, χ (b : ZMod (n + 1))‖ ≤ ∑ b ∈ B, ‖χ (b : ZMod (n + 1))‖ :=
          norm_sum_le _ _
      _ = (B.card : ℝ) := by
          rw [Finset.sum_congr rfl (fun b _ => norm_unitChar n χ b), Finset.sum_const,
            nsmul_eq_mul, mul_one]
  rw [inv_mul_le_iff₀ hcard]
  linarith [hsum]

/-- The dense model's Fourier coefficients are the original ones scaled by a factor in `[0,1]`. -/
theorem denseModel_fourier_real (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ) (B : Finset (ZMod (n + 1))ˣ)
    (hB : B.Nonempty) (χ : DirichletCharacter ℂ (n + 1)) :
    ((((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
        (denseModel n F B a : ℂ) * (starRingEnd ℂ) (χ (a : ZMod (n + 1))))
      = ((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ := by
  rw [denseModel_fourier n F B hB χ, Complex.mul_conj']
  push_cast
  ring

/-- Item (iii) of the dense model theorem: the model never increases a Fourier coefficient. -/
theorem norm_denseModel_fourier_le (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ)
    (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty) (χ : DirichletCharacter ℂ (n + 1)) :
    ‖(((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
        (denseModel n F B a : ℂ) * (starRingEnd ℂ) (χ (a : ZMod (n + 1)))‖
      ≤ ‖unitFourier n F χ‖ := by
  rw [denseModel_fourier_real n F B hB χ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h1 : ‖bohrAvg n B χ‖ ^ 2 ≤ 1 := by
    nlinarith [norm_bohrAvg_le_one n B hB χ, norm_nonneg (bohrAvg n B χ)]
  nlinarith [norm_nonneg (unitFourier n F χ), h1]

/-- Item (iii), second half: the transference error never exceeds the original coefficient. -/
theorem norm_sub_denseModel_fourier_le (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ)
    (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty) (χ : DirichletCharacter ℂ (n + 1)) :
    ‖unitFourier n F χ - (((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
        (denseModel n F B a : ℂ) * (starRingEnd ℂ) (χ (a : ZMod (n + 1)))‖
      ≤ ‖unitFourier n F χ‖ := by
  rw [denseModel_fourier_real n F B hB χ]
  have hfac : unitFourier n F χ - ((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ
      = ((1 - ‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ := by
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖bohrAvg n B χ‖ ^ 2 ≤ 1 := by
    nlinarith [norm_bohrAvg_le_one n B hB χ, norm_nonneg (bohrAvg n B χ)]
  have h2 : |1 - ‖bohrAvg n B χ‖ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (bohrAvg n B χ)]
  nlinarith [norm_nonneg (unitFourier n F χ), h2]


theorem bohrAvg_one (n : ℕ) (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty) :
    bohrAvg n B (1 : DirichletCharacter ℂ (n + 1)) = 1 := by
  have hcard : ((B.card : ℂ)) ≠ 0 := by
    have hpos : 0 < B.card := Finset.card_pos.2 hB
    exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
  rw [bohrAvg]
  have hval : ∀ b ∈ B, (1 : DirichletCharacter ℂ (n + 1)) (b : ZMod (n + 1)) = 1 := by
    intro b _
    exact MulChar.one_apply_coe b
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, mul_one,
    inv_mul_cancel₀ hcard]

/-- Item (iv) of the dense model theorem: the model has the same total mass as the original. -/
theorem denseModel_mass (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ) (B : Finset (ZMod (n + 1))ˣ)
    (hB : B.Nonempty) :
    ((((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
        (denseModel n F B a : ℂ)
          * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ (n + 1)) (a : ZMod (n + 1))))
      = unitFourier n F (1 : DirichletCharacter ℂ (n + 1)) := by
  rw [denseModel_fourier_real n F B hB, bohrAvg_one n B hB]
  simp


/-- On a Bohr set, the normalised character average is close to `1`. -/
theorem norm_bohrAvg_sub_one_le (n : ℕ) (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty)
    (χ : DirichletCharacter ℂ (n + 1)) {c : ℝ}
    (hclose : ∀ b ∈ B, ‖χ (b : ZMod (n + 1)) - 1‖ ≤ c) :
    ‖bohrAvg n B χ - 1‖ ≤ c := by
  have hcardR : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB
  have hcard : ((B.card : ℂ)) ≠ 0 := by
    have hpos : 0 < B.card := Finset.card_pos.2 hB
    exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
  have hrw : bohrAvg n B χ - 1
      = ((B.card : ℂ))⁻¹ * ∑ b ∈ B, (χ (b : ZMod (n + 1)) - 1) := by
    rw [bohrAvg, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, mul_sub,
      inv_mul_cancel₀ hcard]
  rw [hrw, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ b ∈ B, (χ (b : ZMod (n + 1)) - 1)‖ ≤ (B.card : ℝ) * c := by
    calc ‖∑ b ∈ B, (χ (b : ZMod (n + 1)) - 1)‖
        ≤ ∑ b ∈ B, ‖χ (b : ZMod (n + 1)) - 1‖ := norm_sum_le _ _
      _ ≤ ∑ _b ∈ B, c := Finset.sum_le_sum hclose
      _ = (B.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [inv_mul_le_iff₀ hcardR]
  linarith [hsum]

/-- Item (ii) of the dense model theorem on the large spectrum: on a Bohr set the transference
error is governed by the Bohr radius. -/
theorem norm_sub_denseModel_fourier_le_of_close (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ)
    (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty) (χ : DirichletCharacter ℂ (n + 1))
    {c M : ℝ} (hM : 0 ≤ M)
    (hclose : ∀ b ∈ B, ‖χ (b : ZMod (n + 1)) - 1‖ ≤ c)
    (hbound : ‖unitFourier n F χ‖ ≤ M) :
    ‖unitFourier n F χ - (((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
        (denseModel n F B a : ℂ) * (starRingEnd ℂ) (χ (a : ZMod (n + 1)))‖
      ≤ (2 * c + c ^ 2) * M := by
  rw [denseModel_fourier_real n F B hB χ]
  have hfac : unitFourier n F χ - ((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ
      = ((1 - ‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ) * unitFourier n F χ := by
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hdist := norm_bohrAvg_sub_one_le n B hB χ hclose
  have hlow : ‖bohrAvg n B χ‖ ≤ 1 + c := by
    have := norm_sub_norm_le (bohrAvg n B χ) (1 : ℂ)
    simp only [norm_one] at this
    linarith [hdist, this]
  have hhigh : 1 - c ≤ ‖bohrAvg n B χ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (bohrAvg n B χ)
    rw [norm_sub_rev] at this
    simp only [norm_one] at this
    linarith [hdist, this]
  have hnn : (0 : ℝ) ≤ ‖bohrAvg n B χ‖ := norm_nonneg _
  have habs : |1 - ‖bohrAvg n B χ‖ ^ 2| ≤ 2 * c + c ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hnn, hlow, hhigh]
  nlinarith [habs, hbound, hM, norm_nonneg (unitFourier n F χ), abs_nonneg (1 - ‖bohrAvg n B χ‖ ^ 2)]


/-! ### Item (v): cosets of an index-two subgroup -/

/-- The indicator of the coset `b · ker ψ` of a quadratic character, written in terms of `ψ`. -/
def quadIndicator (n : ℕ) (ψ : DirichletCharacter ℂ (n + 1)) (b u : (ZMod (n + 1))ˣ) : ℂ :=
  (1 + ψ (u : ZMod (n + 1)) * (starRingEnd ℂ) (ψ (b : ZMod (n + 1)))) / 2

theorem quadIndicator_eq (n : ℕ) (ψ : DirichletCharacter ℂ (n + 1))
    (hψ : ∀ u : (ZMod (n + 1))ˣ,
      ψ (u : ZMod (n + 1)) = 1 ∨ ψ (u : ZMod (n + 1)) = -1) (b u : (ZMod (n + 1))ˣ) :
    quadIndicator n ψ b u
      = if ψ (u : ZMod (n + 1)) = ψ (b : ZMod (n + 1)) then 1 else 0 := by
  rw [quadIndicator]
  rcases hψ u with hu | hu <;> rcases hψ b with hb | hb <;>
    simp [hu, hb] <;> norm_num

/-- The mass of a function in a coset of the kernel of a quadratic character, expressed by its
Fourier coefficients at the principal and quadratic characters. -/
theorem sum_quadIndicator (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ)
    (ψ : DirichletCharacter ℂ (n + 1))
    (hψr : ∀ u : (ZMod (n + 1))ˣ,
      (starRingEnd ℂ) (ψ (u : ZMod (n + 1))) = ψ (u : ZMod (n + 1)))
    (b : (ZMod (n + 1))ˣ) :
    ∑ u : (ZMod (n + 1))ˣ, (F u : ℂ) * quadIndicator n ψ b u
      = (unitFourier n F (1 : DirichletCharacter ℂ (n + 1))
          + (starRingEnd ℂ) (ψ (b : ZMod (n + 1))) * unitFourier n F ψ) / 2 := by
  rw [unitFourier, unitFourier]
  simp only [quadIndicator]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [MulChar.one_apply_coe, hψr u]
  simp only [map_one]
  ring

/-- **Item (v) of the dense model theorem** for an index-two subgroup: the model preserves the mass
in a coset of `ker ψ` up to half the transference error at `ψ`. -/
theorem denseModel_coset (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ) (B : Finset (ZMod (n + 1))ˣ)
    (hB : B.Nonempty) (ψ : DirichletCharacter ℂ (n + 1))
    (hψr : ∀ u : (ZMod (n + 1))ˣ,
      (starRingEnd ℂ) (ψ (u : ZMod (n + 1))) = ψ (u : ZMod (n + 1)))
    (hψu : ∀ u : (ZMod (n + 1))ˣ, ‖ψ (u : ZMod (n + 1))‖ = 1)
    (b : (ZMod (n + 1))ˣ) :
    ‖(∑ u : (ZMod (n + 1))ˣ, (F u : ℂ) * quadIndicator n ψ b u)
        - (((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
            (denseModel n F B a : ℂ) * quadIndicator n ψ b a‖
      ≤ ‖unitFourier n F ψ - (((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
            (denseModel n F B a : ℂ) * (starRingEnd ℂ) (ψ (a : ZMod (n + 1)))‖ / 2 := by
  have hFside := sum_quadIndicator n F ψ hψr b
  have hGside := sum_quadIndicator n (denseModel n F B) ψ hψr b
  have hphi : ((((n + 1).totient : ℂ))) ≠ 0 := by
    have hpos : 0 < (n + 1).totient := Nat.totient_pos.2 (by omega)
    exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
  have hmass := denseModel_mass n F B hB
  rw [hFside, Finset.mul_sum]
  have hrw : ∑ a : (ZMod (n + 1))ˣ,
      ((((n + 1).totient : ℂ))⁻¹ * ((denseModel n F B a : ℂ) * quadIndicator n ψ b a))
      = (((n + 1).totient : ℂ))⁻¹
        * ((unitFourier n (denseModel n F B) (1 : DirichletCharacter ℂ (n + 1))
            + (starRingEnd ℂ) (ψ (b : ZMod (n + 1)))
              * unitFourier n (denseModel n F B) ψ) / 2) := by
    rw [← Finset.mul_sum, hGside]
  rw [hrw]
  have hone : (((n + 1).totient : ℂ))⁻¹
      * unitFourier n (denseModel n F B) (1 : DirichletCharacter ℂ (n + 1))
      = unitFourier n F (1 : DirichletCharacter ℂ (n + 1)) := by
    rw [← hmass, unitFourier]
  have hpsi : (((n + 1).totient : ℂ))⁻¹ * unitFourier n (denseModel n F B) ψ
      = (((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
          (denseModel n F B a : ℂ) * (starRingEnd ℂ) (ψ (a : ZMod (n + 1))) := by
    rw [unitFourier]
  have hsplit : (((n + 1).totient : ℂ))⁻¹
      * ((unitFourier n (denseModel n F B) (1 : DirichletCharacter ℂ (n + 1))
          + (starRingEnd ℂ) (ψ (b : ZMod (n + 1)))
            * unitFourier n (denseModel n F B) ψ) / 2)
      = (unitFourier n F (1 : DirichletCharacter ℂ (n + 1))
          + (starRingEnd ℂ) (ψ (b : ZMod (n + 1)))
            * ((((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
                (denseModel n F B a : ℂ) * (starRingEnd ℂ) (ψ (a : ZMod (n + 1)))))/ 2 := by
    rw [← hone, ← hpsi]
    ring
  rw [hsplit]
  have hfin : (unitFourier n F (1 : DirichletCharacter ℂ (n + 1))
        + (starRingEnd ℂ) (ψ (b : ZMod (n + 1))) * unitFourier n F ψ) / 2
      - (unitFourier n F (1 : DirichletCharacter ℂ (n + 1))
        + (starRingEnd ℂ) (ψ (b : ZMod (n + 1)))
          * ((((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
              (denseModel n F B a : ℂ) * (starRingEnd ℂ) (ψ (a : ZMod (n + 1))))) / 2
      = (starRingEnd ℂ) (ψ (b : ZMod (n + 1))) / 2
        * (unitFourier n F ψ - (((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
            (denseModel n F B a : ℂ) * (starRingEnd ℂ) (ψ (a : ZMod (n + 1))))  := by
    ring
  rw [hfin, norm_mul, norm_div, RCLike.norm_conj, hψu b]
  have : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [this]
  linarith [norm_nonneg (unitFourier n F ψ - (((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
    (denseModel n F B a : ℂ) * (starRingEnd ℂ) (ψ (a : ZMod (n + 1))))]

end RHTower
