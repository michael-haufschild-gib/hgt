import GaloisForLFunctions.HTGeometry.RittSeedInduction
import GaloisForLFunctions.HTGeometry.RittExceptionalDescent
import GaloisForLFunctions.HTGeometry.RittGeneralInhomogeneity

/-!
# The three shapes reduce to jet order two

A collapse of the jet tower produces one of three data: a *seed* — the collapse relation itself, with
scalar `q/ρ^n` and a nonzero top Faà di Bruno coefficient — and the two *exceptional* data, the
homogeneous one (a homogeneous relation together with its companion) and the affine one
(`σ v = ρ^{−1}·v + h` with `h` a nonzero base constant).

Each drops a level: the seed by `ritt_affine_or_exceptional_of_seed`, the two exceptional data by
`excHom_descends` and `excAff_descends`.  At jet order two the seed and the affine datum are refuted
outright — the first because the level-two classification's monomial alternative needs the linear part
of the inhomogeneity to vanish and it does not, the second because the same alternative needs the
constant part to vanish.  So a strong induction on the level leaves Ritt's order-one form, an affine
transport equation, or the homogeneous exceptional datum at jet order two.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- **The three shapes reduce to jet order two.** -/
theorem ritt_affine_or_excHom_two (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ)) :
    ∀ m : ℕ, 2 ≤ m → (∀ j, j < m → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ)) →
      ((∃ (W : L) (A : ℕ → K), W ≠ 0 ∧ W ∈ Fr.jetPrefixField τ m ∧ A (m - 1) ≠ 0 ∧
          Fr.σ W = algebraMap K L (q / Fr.ρ ^ m) * W
            + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ) ∨
       (∃ (v z : L) (κ ν : K), v ≠ 0 ∧ κ ≠ 0 ∧ ν ≠ 0 ∧
          v ∈ Fr.jetPrefixField τ m ∧ z ∈ Fr.jetPrefixField τ m ∧
          Fr.σ v = algebraMap K L (q⁻¹ * Fr.ρ ^ (m - 1)) * v ∧
          Fr.σ z = algebraMap K L (q / Fr.ρ ^ m) * z + algebraMap K L κ / v
            - algebraMap K L ν * (Fr.σ (Fr.d^[m] τ)
                - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ)) ∨
       (∃ (v : L) (h : K), v ≠ 0 ∧ h ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m ∧
          Fr.σ v = algebraMap K L (Fr.ρ)⁻¹ * v + algebraMap K L h)) →
      (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
      (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) ∨
      (∃ (v z : L) (κ ν : K), v ≠ 0 ∧ κ ≠ 0 ∧ ν ≠ 0 ∧
        v ∈ Fr.jetPrefixField τ 2 ∧ z ∈ Fr.jetPrefixField τ 2 ∧
        Fr.σ v = algebraMap K L (q⁻¹ * Fr.ρ ^ (2 - 1)) * v ∧
        Fr.σ z = algebraMap K L (q / Fr.ρ ^ (2 : ℕ)) * z + algebraMap K L κ / v
          - algebraMap K L ν * (Fr.σ (Fr.d^[2] τ)
              - algebraMap K L (q / Fr.ρ ^ (2 : ℕ)) * Fr.d^[2] τ)) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm2 htr hdata
    -- the shape produced by the seed at a lower level, packaged for the induction
    have hpack : ∀ m' : ℕ, 2 ≤ m' → m' < m →
        ((∃ (v z : L) (κ : K), v ≠ 0 ∧ κ ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m' ∧
            z ∈ Fr.jetPrefixField τ m' ∧
            Fr.σ v = algebraMap K L (q⁻¹ * Fr.ρ ^ (m' - 1)) * v ∧
            Fr.σ z = algebraMap K L (q / Fr.ρ ^ m') * z + algebraMap K L κ / v
              - (2 : L) * (Fr.σ (Fr.d^[m'] τ)
                  - algebraMap K L (q / Fr.ρ ^ m') * Fr.d^[m'] τ)) ∨
         (∃ (v : L) (h : K), v ≠ 0 ∧ h ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m' ∧
            Fr.σ v = algebraMap K L (q / Fr.ρ ^ (m' + 1) / (q / Fr.ρ ^ m')) * v
              + algebraMap K L h)) →
        (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
        (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) ∨
        (∃ (v z : L) (κ ν : K), v ≠ 0 ∧ κ ≠ 0 ∧ ν ≠ 0 ∧
          v ∈ Fr.jetPrefixField τ 2 ∧ z ∈ Fr.jetPrefixField τ 2 ∧
          Fr.σ v = algebraMap K L (q⁻¹ * Fr.ρ ^ (2 - 1)) * v ∧
          Fr.σ z = algebraMap K L (q / Fr.ρ ^ (2 : ℕ)) * z + algebraMap K L κ / v
            - algebraMap K L ν * (Fr.σ (Fr.d^[2] τ)
                - algebraMap K L (q / Fr.ρ ^ (2 : ℕ)) * Fr.d^[2] τ)) := by
      intro m' hm'2 hm'lt hin
      have haK0 : q / Fr.ρ ^ m' ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
      have hcq : q / Fr.ρ ^ (m' + 1) ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
      rcases hin with ⟨v, z, κ, hv0, hκ0, hvmem, hzmem, hveq, hzeq⟩ |
          ⟨v, h, hv0, hh0, hvmem, hveq⟩
      · refine ih m' hm'lt hm'2 (fun j hj => htr j (by omega))
          (Or.inr (Or.inl ⟨v, z, κ, 2, hv0, hκ0, two_ne_zero, hvmem, hzmem, hveq, ?_⟩))
        rw [map_ofNat]
        exact hzeq
      · refine ih m' hm'lt hm'2 (fun j hj => htr j (by omega))
          (Or.inr (Or.inr ⟨v, h, hv0, hh0, hvmem, ?_⟩))
        have hscal : q / Fr.ρ ^ (m' + 1) / (q / Fr.ρ ^ m') = (Fr.ρ)⁻¹ := by
          rw [pow_succ]
          field_simp
        rw [← hscal]
        exact hveq
    rcases hdata with hseed | hhom | haff
    · -- the seed
      obtain ⟨W, A, hW0, hWmem, hAtop, hrel⟩ := hseed
      rcases ritt_affine_or_exceptional_of_seed Fr hqconst hshift hq hdρ htr0 htr1 m hm2 htr
          W A hW0 hWmem hAtop hrel with
          hritt | ⟨u, h, I, J, hu0, hh0, hbase⟩ |
          ⟨m', v, z, κ, hm'2, hm'lt, hv0, hκ0, hvmem, hzmem, hveq, hzeq⟩ |
          ⟨m', v, h, hm'2, hm'lt, hv0, hvmem, hh0, hveq⟩
      · exact Or.inl hritt
      · exact Or.inr (Or.inl ⟨u, h, I, J, hu0, hh0, hbase⟩)
      · exact hpack m' hm'2 hm'lt (Or.inl ⟨v, z, κ, hv0, hκ0, hvmem, hzmem, hveq, hzeq⟩)
      · exact hpack m' hm'2 hm'lt (Or.inr ⟨v, h, hv0, hh0, hvmem, hveq⟩)
    · -- the homogeneous exceptional datum
      obtain ⟨v, z, κ, ν, hv0, hκ0, hν0, hvmem, hzmem, hveq, hzeq⟩ := hhom
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · have hm : m = 2 := by omega
        subst hm
        exact Or.inr (Or.inr ⟨v, z, κ, ν, hv0, hκ0, hν0, hvmem, hzmem, hveq, hzeq⟩)
      · rcases excHom_descends Fr hqconst hshift hq hdρ hm3 htr hv0 hκ0 hν0 hvmem hzmem
            hveq hzeq with hseed | hhom' | haff'
        · exact ih (m - 1) (by omega) (by omega) (fun j hj => htr j (by omega)) (Or.inl (by
            obtain ⟨w, A, hw0, hwmem, hAtop, hrel⟩ := hseed
            exact ⟨w, A, hw0, hwmem, by rw [show m - 1 - 1 = m - 2 by omega]; exact hAtop,
              hrel⟩))
        · exact ih (m - 1) (by omega) (by omega) (fun j hj => htr j (by omega))
            (Or.inr (Or.inl hhom'))
        · exact ih (m - 1) (by omega) (by omega) (fun j hj => htr j (by omega))
            (Or.inr (Or.inr (by
              obtain ⟨v', h, hv'0, hh0, hv'mem, hv'eq⟩ := haff'
              exact ⟨v', h, hv'0, hh0, hv'mem, hv'eq⟩)))
    · -- the affine exceptional datum
      obtain ⟨v, h, hv0, hh0, hvmem, hveq⟩ := haff
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · have hm : m = 2 := by omega
        subst hm
        rcases ritt_or_affine_of_excAff_two Fr hqconst hshift hq htr0 htr1 hv0 hh0 hvmem hveq
          with hritt | ⟨u, I, J, hu0, hbase⟩
        · exact Or.inl hritt
        · exact Or.inr (Or.inl ⟨u, h, I, J, hu0, hh0, hbase⟩)
      · rcases excAff_descends Fr hqconst hshift hq hdρ hm3 htr hv0 hh0 hvmem hveq with
            hseed | haff' | hhom'
        · exact ih (m - 1) (by omega) (by omega) (fun j hj => htr j (by omega)) (Or.inl (by
            obtain ⟨w, A, hw0, hwmem, hAtop, hrel⟩ := hseed
            exact ⟨w, A, hw0, hwmem, by rw [show m - 1 - 1 = m - 2 by omega]; exact hAtop,
              hrel⟩))
        · exact ih (m - 1) (by omega) (by omega) (fun j hj => htr j (by omega))
            (Or.inr (Or.inr (by
              obtain ⟨v', hv'0, hv'mem, hv'eq⟩ := haff'
              exact ⟨v', h, hv'0, hh0, hv'mem, hv'eq⟩)))
        · obtain ⟨v', y, hv'0, hv'mem, hymem, hv'eq, hyeq⟩ := hhom'
          refine ih (m - 1) (by omega) (by omega) (fun j hj => htr j (by omega))
            (Or.inr (Or.inl ⟨v', y, q / Fr.ρ ^ (m - 1) * h * Fr.ρ, 1, hv'0, ?_, one_ne_zero,
              hv'mem, hymem, hv'eq, ?_⟩))
          · exact mul_ne_zero (mul_ne_zero (div_ne_zero hq (pow_ne_zero _ hρ0)) hh0) hρ0
          · rw [map_one, one_mul, hyeq]
            congr 2
            rw [map_mul, map_mul, map_inv₀]
            field_simp

end GaloisForLFunctions.HTGeometry
