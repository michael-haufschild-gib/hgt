import GaloisForLFunctions.RHTower.XiSignedFactorSquareClasses

/-!
# The square-class kernel of the marked Xi tower

The infinite marked field `M` adjoins square roots of `ξ·D₋(n)` for all labels `n ≥ 2`, where
`D_±(n) = 1 ± n^{-s}ξ`.  An element of the global meromorphic field becomes a square in `M` exactly
when one of its twists by a finite product of these radicands is already a square: the kernel of
`K^*/K^{*2} → M^*/M^{*2}` is the span of the classes `[ξ] + [D₋(n)]`.

Combined with the freeness of `[ξ]`, `[D₋(n)]`, `[D₊(n)]` in `K^*/K^{*2}` this gives the exact
signed criterion in `M`: `ξ^e ∏_S D₋ ∏_T D₊` is a square in `M` iff `e + |S|` is even and `T = ∅`.
Thus the negative classes collapse onto `[ξ]` while `[ξ]` and all `[D₊(n)]` stay independent.
-/

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

local instance : CharZero MeromorphicPlane :=
  charZero_of_injective_algebraMap constPlane_injective

private theorem isSquare_pow_iff_even {F : Type*} [Field F] {a : F} (ha : ¬ IsSquare a) (e : ℕ) :
    IsSquare (a ^ e) ↔ Even e := by
  have ha0 : a ≠ 0 := fun hz => ha (hz ▸ IsSquare.zero)
  refine ⟨fun hs => ?_, fun he => he.isSquare_pow a⟩
  by_contra he
  obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp he
  have h := hs.div (IsSquare.sq (a ^ k))
  have heq : a ^ (2 * k + 1) / (a ^ k) ^ 2 = a := by
    rw [pow_add, pow_one, show 2 * k = k * 2 by omega, pow_mul]
    field_simp
  rw [heq] at h
  exact ha h

private theorem radicand_ne_zero (n : ℕ) : radicand n ≠ 0 := by
  intro h
  apply prod_radicand_not_isSquare {n} (Finset.singleton_nonempty n)
  rw [Finset.prod_singleton, h]
  exact IsSquare.zero

/-- **Kummer kernel.**  An element of the global field becomes a square in the marked field
exactly when some finite radicand twist of it is a square. -/
theorem isSquare_markedExtension_iff (a : K) :
    IsSquare (algebraMap K markedExtension a) ↔
      ∃ T : Finset ℕ, IsSquare (a * ∏ n ∈ T, radicand n) := by
  constructor
  · intro hs
    by_contra h
    push Not at h
    exact not_isSquare_markedExtension_of_twists a h hs
  · rintro ⟨T, b, hb⟩
    set ρ : markedExtension := ∏ n ∈ T, markedRoot n
    have hρ : ρ * ρ = algebraMap K markedExtension (∏ n ∈ T, radicand n) := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun n _ => markedRoot_sq n)
    have hρ0 : ρ ≠ 0 := by
      intro h0
      rw [h0, zero_mul, eq_comm, map_eq_zero_iff _ (algebraMap K markedExtension).injective,
        Finset.prod_eq_zero_iff] at hρ
      obtain ⟨n, -, hn⟩ := hρ
      exact radicand_ne_zero n hn
    have hmap := congrArg (algebraMap K markedExtension) hb
    rw [map_mul, map_mul, ← hρ] at hmap
    refine ⟨algebraMap K markedExtension b / ρ, ?_⟩
    field_simp
    linear_combination hmap

/-- **Exact signed criterion in the marked field.**  For labels at least two,
`ξ^e ∏_S D₋ ∏_T D₊` is a square in the marked field iff `e + |S|` is even and `T = ∅`. -/
theorem signed_packet_isSquare_markedExtension_iff (S T : Finset ℕ) (e : ℕ)
    (hS : ∀ n ∈ S, 2 ≤ n) (hT : ∀ n ∈ T, 2 ≤ n) :
    IsSquare (algebraMap K markedExtension (xiElement ^ e * (∏ n ∈ S, factorElement n) *
      ∏ n ∈ T, augmentationElement n)) ↔ Even (e + S.card) ∧ T = ∅ := by
  set φ := algebraMap K markedExtension
  have hfac0 : ∀ n ∈ S, φ (factorElement n) ≠ 0 := by
    intro n hn h0
    apply factorElement_not_isSquare (hS n hn)
    rw [(map_eq_zero_iff φ φ.injective).mp h0]
    exact IsSquare.zero
  -- `ξ D₋(n)` is a square in the marked field.
  have hsq : IsSquare (φ xiElement ^ S.card * ∏ n ∈ S, φ (factorElement n)) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_induction _ IsSquare (fun _ _ => IsSquare.mul) IsSquare.one ?_
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hS n hn; omega⟩
    exact xi_mul_factor_isSquare_markedExtension m
  have hxi0 : φ xiElement ≠ 0 := fun h0 => xi_not_isSquare_markedExtension (h0 ▸ IsSquare.zero)
  have hP0 : (∏ n ∈ S, φ (factorElement n)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfac0
  have hW0 : φ xiElement ^ S.card * ∏ n ∈ S, φ (factorElement n) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hxi0) hP0
  -- Multiplying by the nonzero square `ξ^{|S|} ∏_S D₋` reduces to the positive packet.
  have hred : IsSquare (φ (xiElement ^ e * (∏ n ∈ S, factorElement n) *
        ∏ n ∈ T, augmentationElement n)) ↔
      IsSquare (φ (xiElement ^ (e + S.card) * ∏ n ∈ T, augmentationElement n)) := by
    have hprod : φ (xiElement ^ e * (∏ n ∈ S, factorElement n) * ∏ n ∈ T, augmentationElement n) *
        (φ xiElement ^ S.card * ∏ n ∈ S, φ (factorElement n)) =
        φ (xiElement ^ (e + S.card) * ∏ n ∈ T, augmentationElement n) *
          (∏ n ∈ S, φ (factorElement n)) ^ 2 := by
      simp only [map_mul, map_pow, map_prod, pow_add]; ring
    constructor
    · intro h
      have h2 := h.mul hsq
      rw [hprod] at h2
      have h3 := h2.div (IsSquare.sq (∏ n ∈ S, φ (factorElement n)))
      rwa [mul_div_cancel_right₀ _ (pow_ne_zero 2 hP0)] at h3
    · intro h
      have h2 := (h.mul (IsSquare.sq (∏ n ∈ S, φ (factorElement n)))).div hsq
      rwa [← hprod, mul_div_cancel_right₀ _ hW0] at h2
  rw [hred]
  constructor
  · intro h
    have hTe : T = ∅ := by
      by_contra hne
      exact augmentation_packet_not_isSquare_markedExtension T (e + S.card)
        (Finset.nonempty_iff_ne_empty.mpr hne) hT h
    subst hTe
    simp only [Finset.prod_empty, mul_one, map_pow] at h
    exact ⟨(isSquare_pow_iff_even xi_not_isSquare_markedExtension _).mp h, rfl⟩
  · rintro ⟨he, rfl⟩
    simp only [Finset.prod_empty, mul_one, map_pow]
    exact he.isSquare_pow _

end RHTower.XiGlobalKummer
