import Zeta23.Defs
import GaloisForLFunctions.ArithmeticPolarization.TheEllipticLocalizers

/-!
# Twisted sectors collide quartets

The elliptic localizer `σ_γ` of `TheEllipticLocalizers`, realized on tests and on Weil's form.
Transforms are `tr f s = ∫ f(u) e^{(s − ½)u} du`, the `paperFT` of `Zeta23` at `γ_s = (s − ½)/i`.

* **Operations on tests.** The twist `e^{−iγu} f` shifts the transform, `tr f (s − iγ)`
  (`tr_twist`); the reflection `f(−u)` reflects it, `tr f (1 − s)` (`tr_fe`); the test localizer
  `σ_γ f = e^{−2iγu} f(−u)` acts by `tr f ∘ σ_γ` (`tr_sigmaTest`).
* **Sectors are twists.** `σ_γ`-symmetric (antisymmetric) tests are exactly the twists `e^{−iγu} r`
  of even (odd) tests `r` (`sigmaTest_twist_even`, `sigmaTest_twist_odd`,
  `exists_even_of_sigmaTest_eq`).
* **The twist identity** (`W_twist`): for every zero configuration, Weil's form on twisted tests
  is Weil's form of the vertically shifted configuration `Z − iγ` (`shiftConfig`), exactly.
* **Collision** (`shift_mem_real`, `shift_quartet`): a point of `Z` at ordinate `γ` becomes a real
  point of `Z − iγ`; an off-line quartet `{½ ± a ± iγ}` contributes the real pair `{½ ± a}`.
* **The sign of an elliptic sector** (`Wsummand_of_sigma_symmetric`,
  `Wsummand_of_sigma_antisymmetric`): at every point `ρ` of ordinate `γ` the summand of Weil's form
  is `+ m_ρ |tr f ρ|²` on the even sector and `− m_ρ |tr f ρ|²` on the odd sector. An off-line pair
  at ordinate `γ` is positive (invisible to positivity) on the even sector and negative on the odd
  sector; in the twisted picture this is the sign `± m |r̂(½ + a)|²` at a real pair
  (`Wsummand_real_even`, `Wsummand_real_odd`).
-/

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-! ### 1. Transforms and operations on tests -/

/-- The transform `tr f s = ∫ f(u) e^{(s − ½)u} du` at a spectral point `s`. -/
def tr (f : ℝ → ℂ) (s : ℂ) : ℂ := paperFT f (gammaOf s)

theorem tr_eq (f : ℝ → ℂ) (s : ℂ) : tr f s = ∫ u : ℝ, f u * Complex.exp ((s - 1 / 2) * u) := by
  rw [tr, paperFT, gammaOf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  congr 2
  field_simp

/-- The conjugate evaluation point of `Zeta23` is the reflected spectral point. -/
theorem paperFT_conj_gammaOf (g : ℝ → ℂ) (ρ : ℂ) :
    paperFT g (conj (gammaOf ρ)) = tr g (rosatiRefl ρ) := by
  rw [tr, gammaOf, gammaOf, rosatiRefl]
  congr 1
  rw [Complex.div_I, Complex.div_I]
  simp only [map_mul, map_sub, map_neg, Complex.conj_I, map_one, map_div₀, map_ofNat]
  ring

theorem reflect_eq_rosatiRefl (ρ : ℂ) : reflect ρ = rosatiRefl ρ := rfl

/-- The **twist** `e^{−iγu} f`: the archimedean flow on tests. -/
def twist (γ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => Complex.exp (-(γ * I * u)) * f u

/-- The reflection `u ↦ −u`: the functional equation on tests. -/
def fe (f : ℝ → ℂ) : ℝ → ℂ := fun u => f (-u)

/-- The **test localizer** `σ_γ f = e^{−2iγu} f(−u)`. -/
def sigmaTest (γ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => Complex.exp (-(2 * γ * I * u)) * f (-u)

/-- The twist shifts the transform: `tr (e^{−iγu} f) s = tr f (s − iγ)`. -/
theorem tr_twist (γ : ℝ) (f : ℝ → ℂ) (s : ℂ) : tr (twist γ f) s = tr f (s - γ * I) := by
  rw [tr_eq, tr_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [twist]
  rw [mul_comm (Complex.exp _) (f u), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The reflection reflects the transform: `tr (f(−·)) s = tr f (1 − s)`. -/
theorem tr_fe (f : ℝ → ℂ) (s : ℂ) : tr (fe f) s = tr f (1 - s) := by
  rw [tr_eq, tr_eq, ← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [fe, neg_neg, Complex.ofReal_neg]
  congr 2
  ring

/-- The test localizer acts on transforms by `σ_γ`. -/
theorem tr_sigmaTest (γ : ℝ) (f : ℝ → ℂ) (s : ℂ) : tr (sigmaTest γ f) s = tr f (sigma γ s) := by
  have e : sigmaTest γ f = twist (2 * γ) (fe f) := by
    funext u; simp [sigmaTest, twist, fe]
  rw [e, tr_twist, tr_fe]
  congr 1
  simp [sigma]; ring

/-! ### 2. Sectors are twists -/

/-- A twist of an even test is `σ_γ`-symmetric. -/
theorem sigmaTest_twist_even {γ : ℝ} {r : ℝ → ℂ} (hr : ∀ u, r (-u) = r u) :
    sigmaTest γ (twist γ r) = twist γ r := by
  funext u
  have e : Complex.exp (-(2 * γ * I * u)) * Complex.exp (-(γ * I * ((-u : ℝ) : ℂ))) =
      Complex.exp (-(γ * I * u)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [sigmaTest, twist, hr]
  rw [← e]; ring

/-- A twist of an odd test is `σ_γ`-antisymmetric. -/
theorem sigmaTest_twist_odd {γ : ℝ} {r : ℝ → ℂ} (hr : ∀ u, r (-u) = -r u) :
    sigmaTest γ (twist γ r) = fun u => -twist γ r u := by
  funext u
  have e : Complex.exp (-(2 * γ * I * u)) * Complex.exp (-(γ * I * ((-u : ℝ) : ℂ))) =
      Complex.exp (-(γ * I * u)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [sigmaTest, twist, hr]
  rw [← e]; ring

/-- Every `σ_γ`-symmetric test is the twist of an even test, namely of `e^{iγu} f`. -/
theorem exists_even_of_sigmaTest_eq {γ : ℝ} {f : ℝ → ℂ} (hf : sigmaTest γ f = f) :
    ∃ r : ℝ → ℂ, (∀ u, r (-u) = r u) ∧ f = twist γ r := by
  refine ⟨twist (-γ) f, fun u => ?_, ?_⟩
  · have h := congrFun hf u
    simp only [sigmaTest] at h
    simp only [twist]
    rw [← h]
    simp only [Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · funext u
    simp only [twist, ← mul_assoc, ← Complex.exp_add]
    rw [show -(γ * I * u) + -((-γ : ℝ) * I * u) = (0 : ℂ) by push_cast; ring, Complex.exp_zero,
      one_mul]

/-- Every `σ_γ`-antisymmetric test is the twist of an odd test. -/
theorem exists_odd_of_sigmaTest_eq_neg {γ : ℝ} {f : ℝ → ℂ} (hf : sigmaTest γ f = fun u => -f u) :
    ∃ r : ℝ → ℂ, (∀ u, r (-u) = -r u) ∧ f = twist γ r := by
  refine ⟨twist (-γ) f, fun u => ?_, ?_⟩
  · have h := congrFun hf u
    simp only [sigmaTest] at h
    simp only [twist]
    have e : Complex.exp (-((-γ : ℝ) * I * ((-u : ℝ) : ℂ))) =
        Complex.exp (-((-γ : ℝ) * I * u)) * Complex.exp (-(2 * γ * I * u)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e, mul_assoc, h]; ring
  · funext u
    simp only [twist, ← mul_assoc, ← Complex.exp_add]
    rw [show -(γ * I * u) + -((-γ : ℝ) * I * u) = (0 : ℂ) by push_cast; ring, Complex.exp_zero,
      one_mul]

/-- The transform of a `σ_γ`-symmetric test is `σ_γ`-invariant. -/
theorem tr_sigma_of_symmetric {γ : ℝ} {f : ℝ → ℂ} (hf : sigmaTest γ f = f) (s : ℂ) :
    tr f (sigma γ s) = tr f s := by
  rw [← tr_sigmaTest, hf]

/-- The transform of a `σ_γ`-antisymmetric test is `σ_γ`-anti-invariant. -/
theorem tr_sigma_of_antisymmetric {γ : ℝ} {f : ℝ → ℂ} (hf : sigmaTest γ f = fun u => -f u)
    (s : ℂ) : tr f (sigma γ s) = -tr f s := by
  rw [← tr_sigmaTest, hf, tr_eq, tr_eq, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp

/-! ### 3. The shifted configuration and the twist identity -/

section Shift

variable (Z : Zeta23.ZeroConfig)

/-- The configuration **shifted down by `γ`**: points `ρ − iγ`, with the multiplicities of `ρ`. -/
def shiftConfig (γ : ℝ) : Zeta23.ZeroConfig where
  carrier := (fun ρ => ρ - γ * I) '' Z.carrier
  mult := fun z => Z.mult (z + γ * I)
  one_le_mult := by
    rintro _ ⟨ρ, hρ, rfl⟩
    simpa using Z.one_le_mult ρ hρ
  strip := by
    rintro _ ⟨ρ, hρ, rfl⟩
    simpa using Z.strip ρ hρ
  reflect_mem := by
    rintro _ ⟨ρ, hρ, rfl⟩
    refine ⟨reflect ρ, Z.reflect_mem ρ hρ, ?_⟩
    apply Complex.ext <;> simp [reflect]; ring
  mult_reflect := by
    rintro _ ⟨ρ, hρ, rfl⟩
    have : reflect (ρ - γ * I) + γ * I = reflect ρ := by
      apply Complex.ext <;> simp [reflect]
    simp only [this, sub_add_cancel]
    exact Z.mult_reflect ρ hρ
  finite_window := by
    intro T₁ T₂
    refine ((Z.finite_window (T₁ + γ) (T₂ + γ)).image fun ρ => ρ - γ * I).subset ?_
    rintro _ ⟨⟨ρ, hρ, rfl⟩, h1, h2⟩
    refine ⟨ρ, ⟨hρ, ?_, ?_⟩, rfl⟩
    · simp at h1; linarith
    · simp at h2; linarith

theorem mem_shiftConfig {γ : ℝ} {ρ : ℂ} (hρ : ρ ∈ Z.carrier) : ρ - γ * I ∈ (shiftConfig Z γ).carrier :=
  ⟨ρ, hρ, rfl⟩

/-- The shift of the carrier, as an equivalence of carriers. -/
def shiftEquiv (γ : ℝ) : Z.carrier ≃ (shiftConfig Z γ).carrier :=
  Equiv.Set.image (fun ρ => ρ - γ * I) Z.carrier (sub_left_injective)

/-- **The summand identity.** The summand of Weil's form at `ρ` on twisted tests is the summand of
the shifted configuration at `ρ − iγ`. -/
theorem Wsummand_twist (γ : ℝ) (f g : ℝ → ℂ) (ρ : ℂ) :
    Z.Wsummand (twist γ f) (twist γ g) ρ = (shiftConfig Z γ).Wsummand f g (ρ - γ * I) := by
  simp only [Zeta23.ZeroConfig.Wsummand, shiftConfig, sub_add_cancel]
  rw [paperFT_conj_gammaOf, paperFT_conj_gammaOf, ← tr, ← tr, tr_twist, tr_twist]
  congr 3
  apply Complex.ext <;> simp [rosatiRefl]; ring

/-- **The twist identity.** Weil's form of `Z` on twisted tests is Weil's form of `Z − iγ`. -/
theorem W_twist (γ : ℝ) (f g : ℝ → ℂ) :
    Z.W (twist γ f) (twist γ g) = (shiftConfig Z γ).W f g := by
  rw [Zeta23.ZeroConfig.W, Zeta23.ZeroConfig.W, ← (shiftEquiv Z γ).tsum_eq]
  exact tsum_congr fun ρ => Wsummand_twist Z γ f g ρ

/-! ### 4. Collision -/

/-- **Collision.** A point of `Z` at ordinate `γ` is a real point of `Z − iγ`. -/
theorem shift_mem_real {γ : ℝ} {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hγ : ρ.im = γ) :
    ρ - γ * I ∈ (shiftConfig Z γ).carrier ∧ (ρ - γ * I).im = 0 ∧ (ρ - γ * I).re = ρ.re :=
  ⟨mem_shiftConfig Z hρ, by simp [hγ], by simp⟩

/-- **An off-line quartet at ordinate `γ` becomes a real pair.** If `½ + a + iγ ∈ Z` then the
shifted configuration contains the real points `½ + a` and `½ − a`. -/
theorem shift_quartet {γ a : ℝ} (hρ : (1 / 2 + a + γ * I : ℂ) ∈ Z.carrier) :
    ((1 / 2 + a : ℝ) : ℂ) ∈ (shiftConfig Z γ).carrier ∧ ((1 / 2 - a : ℝ) : ℂ) ∈ (shiftConfig Z γ).carrier := by
  have h1 := mem_shiftConfig Z (γ := γ) hρ
  have h2 := mem_shiftConfig Z (γ := γ) (Z.reflect_mem _ hρ)
  refine ⟨?_, ?_⟩
  · convert h1 using 1; push_cast; ring
  · convert h2 using 1
    apply Complex.ext <;> simp [reflect]; ring

/-! ### 5. The sign of an elliptic sector -/

/-- **Even sector.** At a point of ordinate `γ`, the summand of Weil's form on a `σ_γ`-symmetric
test is `m_ρ |tr f ρ|²`. -/
theorem Wsummand_of_sigma_symmetric {γ : ℝ} {f : ℝ → ℂ} (hf : sigmaTest γ f = f) {ρ : ℂ}
    (hγ : ρ.im = γ) :
    Z.Wsummand f f ρ = (Z.mult ρ : ℂ) * (Complex.normSq (tr f ρ) : ℂ) := by
  rw [Zeta23.ZeroConfig.Wsummand, paperFT_conj_gammaOf, ← tr, ← (sigma_swaps hγ).1,
    tr_sigma_of_symmetric hf, mul_assoc, Complex.mul_conj]

/-- **Odd sector.** At a point of ordinate `γ`, the summand of Weil's form on a
`σ_γ`-antisymmetric test is `−m_ρ |tr f ρ|²`. -/
theorem Wsummand_of_sigma_antisymmetric {γ : ℝ} {f : ℝ → ℂ}
    (hf : sigmaTest γ f = fun u => -f u) {ρ : ℂ} (hγ : ρ.im = γ) :
    Z.Wsummand f f ρ = -((Z.mult ρ : ℂ) * (Complex.normSq (tr f ρ) : ℂ)) := by
  rw [Zeta23.ZeroConfig.Wsummand, paperFT_conj_gammaOf, ← tr, ← (sigma_swaps hγ).1,
    tr_sigma_of_antisymmetric hf, map_neg, mul_neg, mul_assoc, Complex.mul_conj]

/-- **A real point on an even test**: the summand is `m |tr r ρ|²`. -/
theorem Wsummand_real_even {r : ℝ → ℂ} (hr : ∀ u, r (-u) = r u) {ρ : ℂ} (hρ : ρ.im = 0) :
    Z.Wsummand r r ρ = (Z.mult ρ : ℂ) * (Complex.normSq (tr r ρ) : ℂ) := by
  have hs : sigmaTest 0 r = r := by funext u; simp [sigmaTest, hr]
  exact Wsummand_of_sigma_symmetric Z hs hρ

/-- **A real point on an odd test**: the summand is `−m |tr r ρ|²`. -/
theorem Wsummand_real_odd {r : ℝ → ℂ} (hr : ∀ u, r (-u) = -r u) {ρ : ℂ} (hρ : ρ.im = 0) :
    Z.Wsummand r r ρ = -((Z.mult ρ : ℂ) * (Complex.normSq (tr r ρ) : ℂ)) := by
  have hs : sigmaTest 0 r = fun u => -r u := by funext u; simp [sigmaTest, hr]
  exact Wsummand_of_sigma_antisymmetric Z hs hρ

end Shift

end GaloisForLFunctions.ArithmeticPolarization
