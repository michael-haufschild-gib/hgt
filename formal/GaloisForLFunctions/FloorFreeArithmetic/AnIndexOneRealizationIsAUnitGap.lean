import GaloisForLFunctions.HTGeometry.PontryaginNeutralEigenvectorBound
import GaloisForLFunctions.SurfaceOfSpecZ.OneSidedHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# A realization of index one is a unit gap

A zero `ρ` has the spectral point `i(ρ − ½)`, which lies in the upper half-plane exactly when
`ρ` is right of the critical line. Suppose the zeros right of the line are eigenvalues, at
their spectral points, of an operator that is symmetric for a sesquilinear form with at most
`κ` negative squares (positive definite on the kernel of a map to `ℂ^κ`). Eigenvectors at
distinct upper eigenvalues span a neutral subspace, on which the map to `ℂ^κ` is injective.

* `card_rightZeros_le_of_realization`: such a realization has at most `κ` zeros right of the
  line.
* `encard_rightZeros_le_of_realization`: hence the zeros right of the line are finitely many.
* `riemannHypothesis_of_indexOne_realization`: for `κ = 1` there is none, because the zeros
  right of the line come in conjugate pairs. A form with one negative square in which the zeros
  right of the line are a symmetric spectrum is a producer of the Riemann hypothesis; the
  count it gives has no floor in the depth.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open Zeta23 ArithmeticCastelnuovoSeveri

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The spectral point of a zero: `i(ρ − ½)`. -/
def spectralPoint (ρ : ℂ) : ℂ := I * (ρ - 1 / 2)

/-- The spectral point lies above the real axis by the depth of the zero. -/
theorem spectralPoint_im (ρ : ℂ) : (spectralPoint ρ).im = ρ.re - 1 / 2 := by
  have h : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  rw [spectralPoint, Complex.I_mul_im, Complex.sub_re, h]

theorem spectralPoint_injective : Function.Injective spectralPoint := fun _ _ h =>
  sub_left_injective (mul_left_cancel₀ Complex.I_ne_zero h)

/-- **A realization of index `κ` has at most `κ` zeros right of the line.** -/
theorem card_rightZeros_le_of_realization (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {κ : ℕ}
    (π : V →ₗ[ℂ] (Fin κ → ℂ)) (hπ : ∀ v, π v = 0 → v ≠ 0 → 0 < (B v v).re) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, B (T x) y = B x (T y))
    (hspec : ∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re →
      ∃ v : V, v ≠ 0 ∧ T v = spectralPoint ρ • v)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re) : S.card ≤ κ := by
  classical
  have hex : ∀ ρ : S, ∃ v : V, v ≠ 0 ∧ T v = spectralPoint ρ • v := fun ρ =>
    hspec ρ (hS ρ ρ.2).1 (hS ρ ρ.2).2
  choose w hw0 hTw using hex
  exact HTGeometry.card_upper_eigenvalues_le B π hπ T hT
    (fun i : Fin S.card => spectralPoint (S.equivFin.symm i))
    (fun i j hij => S.equivFin.symm.injective (Subtype.ext (spectralPoint_injective hij)))
    (fun i => by
      have h := (hS _ (S.equivFin.symm i).2).2
      simp only [spectralPoint_im]
      linarith only [h])
    (fun i => w (S.equivFin.symm i)) (fun i => hw0 _) (fun i => hTw _)

/-- The zeros right of the line of a realization of index `κ` are at most `κ`, as a set. -/
theorem encard_rightZeros_le_of_realization (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {κ : ℕ}
    (π : V →ₗ[ℂ] (Fin κ → ℂ)) (hπ : ∀ v, π v = 0 → v ≠ 0 → 0 < (B v v).re) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, B (T x) y = B x (T y))
    (hspec : ∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re →
      ∃ v : V, v ≠ 0 ∧ T v = spectralPoint ρ • v) :
    {ρ : ℂ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re}.encard ≤ κ := by
  classical
  by_contra hcon
  have hlt : (κ : ℕ∞) < {ρ : ℂ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re}.encard :=
    lt_of_not_ge hcon
  have hle : ((κ + 1 : ℕ) : ℕ∞) ≤
      {ρ : ℂ | ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re}.encard := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (ENat.add_one_le_iff (ENat.coe_ne_top κ)).mpr hlt
  obtain ⟨t, ht, hcard⟩ := Set.exists_subset_encard_eq hle
  have hfin : t.Finite := Set.finite_of_encard_eq_coe hcard
  have hc : hfin.toFinset.card = κ + 1 := by
    have h := hfin.encard_eq_coe_toFinset_card
    rw [hcard] at h
    exact_mod_cast h.symm
  have hbound := card_rightZeros_le_of_realization B π hπ T hT hspec hfin.toFinset
    (fun ρ hρ => ht ((Set.Finite.mem_toFinset hfin).mp hρ))
  omega

/-- **A realization of index one gives the Riemann hypothesis.** If the zeros right of the
critical line are eigenvalues, at their spectral points, of an operator symmetric for a form
that is positive definite on a hyperplane, there are no such zeros. -/
theorem riemannHypothesis_of_indexOne_realization (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (π : V →ₗ[ℂ] (Fin 1 → ℂ)) (hπ : ∀ v, π v = 0 → v ≠ 0 → 0 < (B v v).re) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, B (T x) y = B x (T y))
    (hspec : ∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re →
      ∃ v : V, v ≠ 0 ∧ T v = spectralPoint ρ • v) :
    RiemannHypothesis := by
  classical
  apply SurfaceOfSpecZ.riemannHypothesis_of_forall_re_le
  intro ρ hρ
  by_contra hgt
  have hre : 1 / 2 < ρ.re := lt_of_not_ge hgt
  have hρc := _root_.RHTower.conj_mem_zetaZeroConfig hρ
  have hrec : 1 / 2 < (conj ρ).re := by simpa using hre
  have hne : ρ ≠ conj ρ := by
    intro h
    apply zetaZeroConfig_im_ne_zero' ρ hρ
    have him := congrArg Complex.im h
    simp only [Complex.conj_im] at him
    linarith only [him]
  have hbound := card_rightZeros_le_of_realization B π hπ T hT hspec {ρ, conj ρ}
    (fun τ hτ => by
      rcases Finset.mem_insert.mp hτ with rfl | hτ
      · exact ⟨hρ, hre⟩
      · rw [Finset.mem_singleton.mp hτ]
        exact ⟨hρc, hrec⟩)
  rw [Finset.card_pair hne] at hbound
  omega

end GaloisForLFunctions.FloorFreeArithmetic
