import GaloisForLFunctions.ArithmeticKreinLangerTheory.TowerFaithfulSpectraAreDecidedByAlmostEveryTower
import GaloisForLFunctions.ArithmeticKreinLangerTheory.LocalConstituentsMeetOnlyAtTheIdentity

/-!
# Locality is twin-blind

A **twin** is a unitary character `ω` of the group acting on a kernel by `k ↦ ω · k`: on `ℚ_{>0}` the
Liouville character, a sign flip at finitely many primes, a vertical shift `u ↦ u^{iγ}`. On
Krein–Langer data it translates the spectrum: `ω · h_{χ,a} = h_{ωχ,a}` (`pairKernel_twist`), because
reflection commutes with unitary twists (`reflectChar_twistChar`), and `ω · p` stays positive
definite (`isPosDefKernel_twist`).

Unitarity at a tower and coincidence of nodes at a tower are unchanged by the common factor `ω(u_t)`,
so tower faithfulness is twin-invariant (`isTowerFaithful_twist`), and the tower Hasse principle holds
verbatim for every twin (`twin_finite_towers_negIndex_ne`). Locality cannot separate a kernel from its
twins: a selective statement has to enter through a count or a carrier, not through locality.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

variable {G : Type*} [Group G]

/-- The twisted character `u ↦ ω(u) χ(u)`. -/
def twistChar (ω χ : G →* ℂ) : G →* ℂ where
  toFun u := ω u * χ u
  map_one' := by simp
  map_mul' a b := by simp only [map_mul]; ring

theorem twistChar_apply (ω χ : G →* ℂ) (u : G) : twistChar ω χ u = ω u * χ u := rfl

/-- On a unitary character, `conj ω(u⁻¹) = ω(u)`. -/
theorem conj_map_inv_of_unitary {ω : G →* ℂ} (hω : IsUnitaryChar ω) (u : G) :
    conj (ω u⁻¹) = ω u := by
  rw [map_inv_eq_inv, map_inv₀, inv_conj_of_norm_eq_one (hω u)]

/-- **Reflection commutes with unitary twists.** -/
theorem reflectChar_twistChar {ω : G →* ℂ} (hω : IsUnitaryChar ω) (χ : G →* ℂ) :
    reflectChar (twistChar ω χ) = twistChar ω (reflectChar χ) := by
  ext u
  simp only [reflectChar_apply, twistChar_apply, map_mul, conj_map_inv_of_unitary hω]

/-- **A twin translates the pairs.** -/
theorem pairKernel_twist {ω : G →* ℂ} (hω : IsUnitaryChar ω) (χ : G →* ℂ) (a : ℂ) :
    (fun u => ω u * pairKernel χ a u) = pairKernel (twistChar ω χ) a := by
  funext u
  simp only [pairKernel, reflectChar_twistChar hω, twistChar_apply]
  ring

/-- The twin of a Krein–Langer kernel is the twisted positive part plus the translated pairs. -/
theorem twist_add_sum_pairKernel {ω : G →* ℂ} (hω : IsUnitaryChar ω) {κ : ℕ} (p : G → ℂ)
    (χ : Fin κ → G →* ℂ) (a : Fin κ → ℂ) :
    (fun g => ω g * (p g + ∑ j, pairKernel (χ j) (a j) g)) =
      fun g => ω g * p g + ∑ j, pairKernel (twistChar ω (χ j)) (a j) g := by
  funext g
  rw [mul_add, mul_sum]
  congr 1
  exact sum_congr rfl fun j _ => congrFun (pairKernel_twist hω (χ j) (a j)) g

/-- The nodes of a twisted family are the twisted nodes. -/
theorem node_twist {ω : G →* ℂ} (hω : IsUnitaryChar ω) {κ : ℕ} (χ : Fin κ → G →* ℂ)
    (m : Fin κ ⊕ Fin κ) : node (fun j => twistChar ω (χ j)) m = twistChar ω (node χ m) := by
  rcases m with j | j
  · rfl
  · exact reflectChar_twistChar hω (χ j)

/-- **Tower faithfulness is twin-invariant.** -/
theorem isTowerFaithful_twist {ω : G →* ℂ} (hω : IsUnitaryChar ω) {κ : ℕ} {T : Type*}
    {χ : Fin κ → G →* ℂ} {u : T → G} (hF : IsTowerFaithful χ u) :
    IsTowerFaithful (fun j => twistChar ω (χ j)) u := by
  refine ⟨fun j => (hF.1 j).subset fun t ht => ?_, fun m m' hmm' => (hF.2 m m' hmm').subset
    fun t ht => ?_⟩
  · simp only [Set.mem_setOf_eq, twistChar_apply, norm_mul, hω (u t), one_mul] at ht ⊢
    exact ht
  · simp only [Set.mem_setOf_eq, node_twist hω, twistChar_apply] at ht ⊢
    exact mul_left_cancel₀ (map_ne_zero ω (u t)) ht

/-- **The tower Hasse principle holds for every twin.** For a tower-faithful Krein–Langer kernel and
any unitary character `ω`, all but finitely many towers carry the whole index `κ` of the twin
`ω · k`. -/
theorem twin_finite_towers_negIndex_ne {ω : G →* ℂ} (hω : IsUnitaryChar ω) {κ : ℕ} {T : Type*}
    {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ) (a : Fin κ → ℂ)
    (ha : ∀ j, a j ≠ 0) (u : T → G) (hF : IsTowerFaithful χ u) :
    {t | negIndex ((fun g => ω g * (p g + ∑ j, pairKernel (χ j) (a j) g)) ∘
      zpowersHom G (u t)) ≠ κ}.Finite := by
  rw [twist_add_sum_pairKernel hω]
  exact finite_towers_negIndex_ne (isPosDefKernel_twist hω hp) _ a ha u (isTowerFaithful_twist hω hF)

end GaloisForLFunctions.ArithmeticKreinLangerTheory
