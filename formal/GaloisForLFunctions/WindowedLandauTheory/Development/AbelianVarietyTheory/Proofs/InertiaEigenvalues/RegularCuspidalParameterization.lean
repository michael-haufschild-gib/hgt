import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularCuspidalCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.TeichmullerEmbedding

/-! The regular torus-to-cuspidal map for finite general linear groups. -/

open Polynomial GlobalTheory.GLq GlobalTheory.CuspGL GlobalTheory.Published
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.GreenRegular

variable {g : ℕ} [Fact g.Prime] in
private theorem radical_entries_iff {d a : ℕ} (ha : a < d) (u : Gn g d) :
    (∀ i j : Fin d, (u : Mt g d) i j = (if i = j then 1 else 0) ∨
      (i.val < a ∧ a ≤ j.val)) ↔
      InPar a (u : Mt g d) ∧ tl a (u : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (u : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rcases h i j with h1 | h1
      · rw [h1, if_neg]; rintro rfl; omega
      · omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : (i : ℕ) < d ∧ (j : ℕ) < d := by omega
      rcases h ⟨i, hij.1⟩ ⟨j, hij.2⟩ with h1 | h1
      · simp only [tl, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff]
      · simp only at h1; omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : a + (i : ℕ) < d ∧ a + (j : ℕ) < d := by omega
      rcases h ⟨a + i, hij.1⟩ ⟨a + j, hij.2⟩ with h1 | h1
      · simp only [br, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff, add_right_inj]
      · simp only at h1; omega
  · rintro ⟨h1, h2, h3⟩ i j
    have hi := i.2
    have hj := j.2
    by_cases hia : (i : ℕ) < a
    · by_cases hja : (j : ℕ) < a
      · left
        have := congrFun (congrFun h2 ⟨i, hia⟩) ⟨j, hja⟩
        simpa only [tl, entN, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply, Fin.ext_iff] using this
      · right; omega
    · left
      by_cases hja : (j : ℕ) < a
      · rw [h1 i j hja (by omega), if_neg]; rintro rfl; omega
      · have := congrFun (congrFun h3 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
        have e1 : a + (i - a) = (i : ℕ) := by omega
        have e2 : a + (j - a) = (j : ℕ) := by omega
        have e3 : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
        simpa only [br, entN, e1, e2, e3, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply,
          Fin.ext_iff] using this

/-- The regular characters of the finite-field torus give cuspidal characters with
the prescribed elliptic values and Frobenius equivalence. -/
theorem exists_cusp_of_regular : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) := by
  intro g _ d hd K _ _ hK
  have hgp : g.Prime := Fact.out
  have hcF : Nat.card (ZMod g) = g := Nat.card_zmod g
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]
  have hcardU : Nat.card Kˣ = g ^ d - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  have hN0 : 0 < g ^ d - 1 := by
    have := Nat.one_lt_pow hd.ne' hgp.one_lt
    omega
  obtain ⟨θ₀, hθ₀⟩ := TeichEmb.exists_teichmuller (ZMod g)
  let ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g) := IsAlgClosed.lift
  let lam : Kˣ →* ℂˣ := (Units.map θ₀).comp (Units.map (ι : K →* AlgebraicClosure (ZMod g)))
  have hlam : ∀ u : Kˣ, ((lam u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) := fun u => rfl
  have hlam_inj : Function.Injective lam := by
    intro u v h
    have h' := congrArg Units.val h
    rw [hlam, hlam] at h'
    exact Units.ext (ι.injective (hθ₀ _ _ ((map_ne_zero ι).2 u.ne_zero) ((map_ne_zero ι).2 v.ne_zero) h'))
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hprim : IsPrimitiveRoot (lam γ) (g ^ d - 1) := by
    rw [← hcardU, ← orderOf_eq_card_of_forall_mem_zpowers hγ, ← orderOf_injective lam hlam_inj γ]
    exact IsPrimitiveRoot.orderOf _
  have hmod : ∀ u : Kˣ, u ^ (g ^ d - 1) = 1 := fun u => by
    rw [← hcardU]; exact pow_card_eq_one'
  have hpow_eq : ∀ a b : ℕ, lam ^ a = lam ^ b ↔ a ≡ b [MOD g ^ d - 1] := by
    intro a b
    constructor
    · intro h
      have h1 := congrArg (fun f : Kˣ →* ℂˣ => f γ) h
      simp only [MonoidHom.pow_apply] at h1
      rwa [pow_eq_pow_iff_modEq, ← hprim.eq_orderOf] at h1
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.pow_apply, pow_eq_pow_iff_modEq]
      exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hmod, map_one])) h
  have hpow : ∀ θ : Kˣ →* ℂˣ, ∃ k, θ = lam ^ k := by
    intro θ
    have h1 : θ γ ^ (g ^ d - 1) = 1 := by rw [← map_pow, hmod, map_one]
    haveI : NeZero (g ^ d - 1) := ⟨hN0.ne'⟩
    have h1' : ((θ γ : ℂˣ) : ℂ) ^ (g ^ d - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨k, -, hk0⟩ := (IsPrimitiveRoot.coe_units_iff.2 hprim).eq_pow_of_pow_eq_one h1'
    have hk : lam γ ^ k = θ γ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk0)
    refine ⟨k, MonoidHom.ext fun u => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
    rw [map_zpow, map_zpow, MonoidHom.pow_apply, hk]
  let kOf : (Kˣ →* ℂˣ) → ℕ := fun θ => (hpow θ).choose
  have hkOf : ∀ θ, θ = lam ^ kOf θ := fun θ => (hpow θ).choose_spec
  have hreg : ∀ θ, IsRegularChar g d θ → ∀ i : ℕ, 0 < i → i < d →
      ¬ kOf θ * Nat.card (ZMod g) ^ i ≡ kOf θ [MOD Nat.card (ZMod g) ^ d - 1] := by
    intro θ hθ i hi hid hc
    rw [hcF] at hc
    have e : θ ^ g ^ i = θ ^ g ^ 0 := by
      rw [hkOf θ, ← pow_mul, ← pow_mul, pow_zero, mul_one]
      exact (hpow_eq _ _).2 hc
    exact absurd (hθ i 0 hid hd e) hi.ne'
  refine ⟨fun θ => greenRootCharacter θ₀ d (kOf θ), fun θ hθ => ?_, fun θ θ' hθ hθ' => ?_⟩
  · obtain ⟨V, hV, hχ, hdeg, hU⟩ :=
      exists_simple_regular_rootSum (ZMod g) θ₀ hθ₀ d (kOf θ) hd (hreg θ hθ)
    have hVeq : V.character = greenRootCharacter θ₀ d (kOf θ) := funext hχ
    refine ⟨⟨hd, ⟨V, hV, hχ⟩, ?_⟩, ?_, ?_⟩
    · intro a ha had
      have hz := hU a ha had
      rw [finsum_mem_def, finsum_eq_sum_of_fintype] at hz
      unfold res
      refine mul_eq_zero_of_right _ ((Finset.sum_congr rfl fun u _ => ?_).trans hz)
      by_cases hu : ∀ i j : Fin d, (u : Mt g d) i j = (if i = j then 1 else 0) ∨
          (i.val < a ∧ a ≤ j.val)
      · rw [if_pos ((radical_entries_iff had u).mp hu), Set.indicator_of_mem hu, hVeq]
      · rw [if_neg (mt ((radical_entries_iff had u).mpr) hu), Set.indicator_of_notMem hu]
    · rw [← hVeq, hdeg, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hq : 1 ≤ Nat.card (ZMod g) := Nat.card_pos
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, hcF]
    · intro y hy z hz
      have hadd := (rootSum_isAdditive_and_pow_X_sub_one θ₀ (kOf θ)).1
      have he := psi_of_irreducible_charpoly _ hadd (Fin d → ZMod g) (Matrix.toLin' (y : Mt g d))
        (by rwa [Matrix.charpoly_toLin'])
      unfold greenRootCharacter
      rw [he, Matrix.charpoly_toLin']
      congr 1
      have hz' : aeval (ι (z : K)) (y : Mt g d).charpoly = 0 := by
        rw [aeval_algHom_apply, hz, map_zero]
      have hmin : minpoly (ZMod g) (ι (z : K)) = (y : Mt g d).charpoly :=
        (minpoly.eq_of_irreducible_of_monic hy hz' (Matrix.charpoly_monic _)).symm
      have hnd : (y : Mt g d).charpoly.natDegree = d := by simp
      unfold rootSum
      rw [← hmin, roots_minpoly_eq_map_range, hmin, hnd, hcF, Multiset.map_map,
        Finset.sum_eq_multiset_sum]
      congr 1
      refine Multiset.map_congr rfl fun i _ => ?_
      conv_rhs => rw [hkOf θ]
      show θ₀ (ι ↑z ^ g ^ i) ^ kOf θ = _
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hlam, Units.val_pow_eq_pow_val, map_pow ι]
  · rw [greenRootCharacter_eq_iff (ZMod g) θ₀ hθ₀ hd (hreg θ hθ) (hreg θ' hθ'), hcF]
    constructor
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, ?_⟩
      rw [hkOf θ', hkOf θ, ← pow_mul]
      exact ((hpow_eq _ _).mpr h).symm
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, (hpow_eq _ _).mp ?_⟩
      rw [pow_mul, ← hkOf θ, ← hkOf θ']
      exact h.symm


end GlobalTheory.GreenRegular
