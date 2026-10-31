import GaloisForLFunctions.AdelicKreinGeometry.MixingKillsNegativeSquares
import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation

/-!
# The index is twin-blind

A twin of an arithmetic state multiplies it by a unitary character: the Liouville twin by
`λ(nd)`, a sign flip by `ω_p`. On a Gram matrix such a twist is the congruence by the diagonal
unitary `diag(χ(x_a))`, because `χ(x_a⁻¹ x_b) = conj χ(x_a) · χ(x_b)`.

* **Twist invariance** (`negIndex_mul_unitaryChar`): `κ(k · χ) = κ(k)` for every Hermitian kernel
  and every unitary character `χ` of the group.
* **On `Aff(ℚ)`** (`negIndex_mul_slopeChar`, `isHeckeSupported_mul_slopeChar`,
  `hasHeightDecay_mul_slopeChar`): twisting by a unitary character of the slope keeps the index,
  Hecke support and height decay. In particular every twin of a Hecke state has the same index
  wall at `s = 1/2` (`negIndex_heckeState_mul_slopeChar`).

So the index calculus of this programme (induction, escape, mixing, the Kakutani wall) cannot
separate `ζ` from its twins. Selectivity has to enter through the dilation data themselves, Weil's
correlation with its pole and Gamma factor, which a twin changes; this is the affine form of the
twin-blindness of locality on `ℚ_{>0}` (`ArithmeticKreinLangerTheory.LocalityIsTwinBlind`).
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

section Group

variable {G : Type*} [Group G]

/-- A unitary character takes inverses to conjugates. -/
theorem unitaryChar_inv (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1) (g : G) : χ g⁻¹ = conj (χ g) := by
  have h1 : χ g⁻¹ * χ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : conj (χ g) * χ g = 1 := by
    rw [Complex.conj_mul', hχ g]; simp
  have hne : χ g ≠ 0 := fun h => by simp [h] at h1
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

/-- Twisting by a unitary character never raises the index. -/
theorem negIndex_mul_unitaryChar_le (k : G → ℂ) (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1) :
    negIndex (fun g => k g * χ g) ≤ negIndex k := by
  refine negIndex_le_iff.mpr fun n x => ?_
  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun c a => χ (x a) * c a
      map_add' := fun c d => funext fun a => by simp [mul_add]
      map_smul' := fun t c => funext fun a => by simp; ring }
  have hL : ∀ c, hermQuad (gram k x) (L c) = hermQuad (gram (fun g => k g * χ g) x) c := by
    intro c
    simp only [hermQuad_gram]
    congr 1
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_mul χ, unitaryChar_inv χ hχ]
    ring
  exact (Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _ L hL)).trans
    (hermNegIndex_gram_le_negIndex k x)

/-- **Twist invariance of the index.** -/
theorem negIndex_mul_unitaryChar (k : G → ℂ) (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1) :
    negIndex (fun g => k g * χ g) = negIndex k := by
  refine le_antisymm (negIndex_mul_unitaryChar_le k χ hχ) ?_
  -- the conjugate character undoes the twist
  let χ' : G →* ℂ :=
    { toFun := fun g => conj (χ g)
      map_one' := by simp
      map_mul' := fun g h => by simp }
  have hχ' : ∀ g, ‖χ' g‖ = 1 := fun g => by simp [χ', hχ g]
  have e : (fun g => (k g * χ g) * χ' g) = k := funext fun g => by
    simp only [χ', MonoidHom.coe_mk, OneHom.coe_mk]
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ g]
    simp
  have := negIndex_mul_unitaryChar_le (fun g => k g * χ g) χ' hχ'
  rwa [e] at this

end Group

/-! ### Twins of affine states -/

/-- A unitary character of the slope. -/
def slopeChar (χ : ℚˣ →* ℂ) : AffineGroupQ →* ℂ := χ.comp slopeUnit

theorem negIndex_mul_slopeChar (φ : AffineGroupQ → ℂ) (χ : ℚˣ →* ℂ) (hχ : ∀ u, ‖χ u‖ = 1) :
    negIndex (fun g => φ g * slopeChar χ g) = negIndex φ :=
  negIndex_mul_unitaryChar φ (slopeChar χ) fun _ => hχ _

theorem isHeckeSupported_mul_slopeChar {φ : AffineGroupQ → ℂ} (hφ : IsHeckeSupported φ)
    (χ : ℚˣ →* ℂ) : IsHeckeSupported fun g => φ g * slopeChar χ g := fun g hg =>
  hφ g (left_ne_zero_of_mul hg)

theorem hasHeightDecay_mul_slopeChar {φ : AffineGroupQ → ℂ} (hφ : HasHeightDecay φ)
    (χ : ℚˣ →* ℂ) (hχ : ∀ u, ‖χ u‖ = 1) : HasHeightDecay fun g => φ g * slopeChar χ g := by
  intro ε hε
  obtain ⟨N, hN⟩ := hφ ε hε
  exact ⟨N, fun g hg => by rw [norm_mul, slopeChar, MonoidHom.comp_apply, hχ, mul_one]; exact hN g hg⟩

/-- **Every twin of a Hecke state has the same index wall.** -/
theorem negIndex_heckeState_mul_slopeChar (s : ℝ) (χ : ℚˣ →* ℂ) (hχ : ∀ u, ‖χ u‖ = 1) :
    negIndex (fun g => heckeState s g * slopeChar χ g) = if 1 / 2 ≤ s then 0 else ⊤ := by
  rw [negIndex_mul_slopeChar _ χ hχ, negIndex_heckeState]

end GaloisForLFunctions.AdelicKreinGeometry
