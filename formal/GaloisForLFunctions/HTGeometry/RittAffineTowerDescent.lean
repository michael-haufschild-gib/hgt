import GaloisForLFunctions.HTGeometry.RittAffineRelationDescent
import GaloisForLFunctions.HTGeometry.RittPrefixFieldStability
import GaloisForLFunctions.HTGeometry.RittTowerDescentStep

/-!
# An affine relation over the jet tower descends to the base

Iterating `exists_affine_or_eigen_descent` down the jet prefix fields: an affine relation

`ν · σ W = W + γ`,  `W ≠ 0` in `K⟮τ, …, d^[n−1] τ⟯`, `ν`, `γ` in the base,

leaves a relation of the same shape in the base itself, with the scalar multiplied by a monomial in
`q` and `ρ` and the inhomogeneity either kept or dropped to zero.  The dropped case is the
homogeneous one, which `exists_rittForm_of_homogeneous_base_relation` turns into Ritt's order-one
relation as soon as the accumulated exponents do not both vanish.

So an affine relation anywhere in the jet tower is, at the base, either a *generalised affine
connection* `q^I·ρ^J·ψ(a) = a + γ` or an invariant differential.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The affine tower descent.** -/
theorem exists_base_affine_relation_of_tower (Fr : RittFrame K L) [CharZero L]
    {τ : L} {q : K} (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) (γ : K) :
    ∀ (n : ℕ), (∀ k, k < n → Transcendental ↥(Fr.jetPrefixField τ k) (Fr.d^[k] τ)) →
      ∀ (W : L) (ν γ' : K), W ≠ 0 → W ∈ Fr.jetPrefixField τ n → ν ≠ 0 →
        (γ' = γ ∨ γ' = 0) →
        algebraMap K L ν * Fr.σ W = W + algebraMap K L γ' →
        ∃ a ν' γ'' : K, a ≠ 0 ∧ ν' ≠ 0 ∧ (γ'' = γ ∨ γ'' = 0) ∧
          (∃ I J : ℤ, ν' = ν * q ^ I * Fr.ρ ^ J) ∧
          ν' * Fr.ψ a = a + γ'' := by
  intro n
  induction n with
  | zero =>
      intro _ W ν γ' hW0 hWmem hν hγ' hrel
      have hbot : Fr.jetPrefixField τ 0 = (⊥ : IntermediateField K L) := by
        rw [RittFrame.jetPrefixField,
          show {x : L | ∃ j < 0, x = Fr.d^[j] τ} = (∅ : Set L) by ext x; simp]
        exact IntermediateField.adjoin_empty K L
      rw [hbot, IntermediateField.mem_bot] at hWmem
      obtain ⟨a, ha⟩ := hWmem
      refine ⟨a, ν, γ', ?_, hν, hγ', ⟨0, 0, by simp⟩, ?_⟩
      · intro h
        exact hW0 (by rw [← ha, h, map_zero])
      · refine (algebraMap K L).injective ?_
        rw [map_add, map_mul, ← Fr.comp, ha]
        exact hrel
  | succ m ih =>
      intro htr W ν γ' hW0 hWmem hν hγ' hrel
      classical
      set E : IntermediateField K L := Fr.jetPrefixField τ m with hE
      have hEσ : ∀ x ∈ E, Fr.σ x ∈ E := Fr.sigma_mem_jetPrefixField hqconst hshift m
      set φ : ↥E →+* ↥E :=
        { toFun := fun x => ⟨Fr.σ (x : L), hEσ (x : L) x.2⟩
          map_one' := by ext; simp
          map_mul' := fun _ _ => by ext; simp
          map_zero' := by ext; simp
          map_add' := fun _ _ => by ext; simp } with hφ
      have hcompE : ∀ x : ↥E, Fr.σ (algebraMap ↥E L x) = algebraMap ↥E L (φ x) := fun _ => rfl
      have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
      set aK : K := q / Fr.ρ ^ m with haK
      have haK0 : aK ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
      set aE : ↥E := ⟨algebraMap K L aK, IntermediateField.algebraMap_mem _ _⟩ with haE
      have haE0 : aE ≠ 0 := by
        intro h
        exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr haK0) (congrArg Subtype.val h)
      set v : L := Fr.σ (Fr.d^[m] τ) - algebraMap K L aK * Fr.d^[m] τ with hv
      have hvE : v ∈ E := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · have h0 : Fr.σ (Fr.d^[m] τ) = algebraMap K L aK * Fr.d^[m] τ := by
            subst hm0
            simp [haK, hshift]
          rw [hv, h0, sub_self]
          exact zero_mem E
        · obtain ⟨p, rfl⟩ : ∃ p : ℕ, m = p + 1 := ⟨m - 1, by omega⟩
          exact Fr.jetSpan_le_intermediateField
            (fun j hj => Fr.jet_mem_jetPrefixField (by omega)) _
            (Fr.shift_jet_sub_mem_jetSpan hqconst hshift p)
      set bE : ↥E := ⟨v, hvE⟩ with hbE
      have hσt : Fr.σ (Fr.d^[m] τ)
          = algebraMap ↥E L aE * Fr.d^[m] τ + algebraMap ↥E L bE := by
        show Fr.σ (Fr.d^[m] τ) = algebraMap K L aK * Fr.d^[m] τ + v
        rw [hv]; ring
      set νE : ↥E := ⟨algebraMap K L ν, IntermediateField.algebraMap_mem _ _⟩ with hνE
      have hνE0 : νE ≠ 0 := by
        intro h
        exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hν) (congrArg Subtype.val h)
      set βE : ↥E := ⟨algebraMap K L γ', IntermediateField.algebraMap_mem _ _⟩ with hβE
      have hWmem' : W ∈ IntermediateField.adjoin ↥E ({Fr.d^[m] τ} : Set L) := by
        have := (jetPrefixField_succ_eq Fr τ m) ▸ hWmem
        exact this
      have hrelE : algebraMap ↥E L νE * Fr.σ W = W + algebraMap ↥E L βE := hrel
      obtain ⟨u, s, hu0, hcase⟩ :=
        exists_affine_or_eigen_descent Fr.σ φ hcompE (htr m (by omega)) haE0 hνE0 hσt hW0
          hWmem' hrelE
      -- pull the new scalar back to the base
      set ν2 : K := ν * aK ^ s with hν2
      have hν20 : ν2 ≠ 0 := mul_ne_zero hν (zpow_ne_zero _ haK0)
      have hνcast : ((νE * aE ^ s : ↥E) : L) = algebraMap K L ν2 := by
        rw [hν2, map_mul, map_zpow₀]
        rfl
      have huL : (u : L) ≠ 0 := fun h => hu0 (Subtype.ext (by simpa using h))
      have hexp : ∃ I J : ℤ, ν2 = ν * q ^ I * Fr.ρ ^ J := by
        refine ⟨s, -((m : ℤ) * s), ?_⟩
        rw [hν2, haK, div_zpow, ← zpow_natCast Fr.ρ m, ← zpow_mul, zpow_neg, div_eq_mul_inv,
          mul_assoc]
      rcases hcase with hc | hc
      · -- the affine shape survives
        have hrel2 : algebraMap K L ν2 * Fr.σ (u : L) = (u : L) + algebraMap K L γ' := by
          have h := congrArg (fun z : ↥E => (z : L)) hc
          simp only [hφ, hνE, haE, hβE] at h
          rw [← hνcast]
          push_cast at h ⊢
          linear_combination h
        obtain ⟨a, ν3, γ3, ha0, hν30, hγ3, ⟨I, J, hIJ⟩, hfin⟩ :=
          ih (fun k hk => htr k (by omega)) (u : L) ν2 γ' huL u.2 hν20 hγ' hrel2
        obtain ⟨I₀, J₀, hIJ₀⟩ := hexp
        exact ⟨a, ν3, γ3, ha0, hν30, hγ3, ⟨I + I₀, J + J₀, by
          rw [hIJ, hIJ₀, zpow_add₀ hq, zpow_add₀ hρ0]; ring⟩, hfin⟩
      · -- the relation degenerates to the homogeneous one
        have hrel2 : algebraMap K L ν2 * Fr.σ (u : L) = (u : L) + algebraMap K L 0 := by
          have h := congrArg (fun z : ↥E => (z : L)) hc
          simp only [hφ, hνE, haE] at h
          rw [← hνcast, map_zero, add_zero]
          push_cast at h ⊢
          linear_combination h
        obtain ⟨a, ν3, γ3, ha0, hν30, hγ3, ⟨I, J, hIJ⟩, hfin⟩ :=
          ih (fun k hk => htr k (by omega)) (u : L) ν2 0 huL u.2 hν20 (Or.inr rfl) hrel2
        obtain ⟨I₀, J₀, hIJ₀⟩ := hexp
        exact ⟨a, ν3, γ3, ha0, hν30, hγ3, ⟨I + I₀, J + J₀, by
          rw [hIJ, hIJ₀, zpow_add₀ hq, zpow_add₀ hρ0]; ring⟩, hfin⟩

end GaloisForLFunctions.HTGeometry
