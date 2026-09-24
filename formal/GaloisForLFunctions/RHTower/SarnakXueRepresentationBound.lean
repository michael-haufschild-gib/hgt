import Mathlib

open Matrix Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup Module
open scoped MatrixGroups

/-!
# The Frobenius dimension bound for `SL(2, 𝔽_p)`

A finite-dimensional complex representation of `SL(2,ℤ)` that factors through `SL(2,ℤ)/Γ(p)` and has
no nonzero invariant vector has dimension at least `(p-1)/2` (`half_pred_le_finrank`).

This is the lower multiplicity bound in the Sarnak–Xue argument: the eigenspace of an exceptional
Laplace eigenvalue on `Γ(p)\ℍ` is such a representation once level one carries no exceptional
eigenvalue. The unipotent `T` has an eigenvalue `ζ ≠ 1`: if `T` acted trivially, `S³TSTS = T⁻¹` and
`S⁴ = 1` would make `S` act trivially, and `S, T` generate `SL(2,ℤ)`. Conjugation by lifts of `diag(a, a⁻¹)` gives `T ↦ T^{a²}` modulo `Γ(p)`, so every
`ζ^{a²}` is an eigenvalue.
-/

namespace GaloisForLFunctions.RHTower.SarnakXue

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem S_pow_four : S ^ 4 = 1 := by decide

theorem rho_inv_eq_one (ρ : Representation ℂ SL(2, ℤ) W) {g : SL(2, ℤ)} (hg : ρ g = 1) :
    ρ g⁻¹ = 1 := by
  have := congrArg ρ (inv_mul_cancel g)
  rwa [map_mul, hg, mul_one, map_one] at this

theorem rho_S_eq_one (ρ : Representation ℂ SL(2, ℤ) W) (hT : ρ T = 1) : ρ S = 1 := by
  have h := congrArg ρ T_S_rel
  simp only [smul_eq_mul, map_mul, hT, one_mul, rho_inv_eq_one ρ hT] at h
  have h5 : ρ S ^ 5 = 1 := by rw [← h]; simp [pow_succ, mul_assoc]
  have h4 : ρ S ^ 4 = 1 := by rw [← map_pow, S_pow_four, map_one]
  calc ρ S = ρ S * ρ S ^ 4 := by rw [h4, mul_one]
    _ = ρ S ^ 5 := by rw [pow_succ' _ 4]
    _ = 1 := h5

theorem rho_eq_one_of_T (ρ : Representation ℂ SL(2, ℤ) W) (hT : ρ T = 1) (g : SL(2, ℤ)) :
    ρ g = 1 := by
  have hS := rho_S_eq_one ρ hT
  have hg : g ∈ Subgroup.closure {S, T} := by rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hS
    · exact hT
  | one => exact map_one ρ
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
  | inv x _ hx => exact rho_inv_eq_one ρ hx

theorem T_pow_mem_Gamma (p : ℕ) : T ^ p ∈ Gamma p := by
  rw [← zpow_natCast, Gamma_mem, coe_T_zpow]
  simp

/-- Conjugating `T` by a lift of `diag(a, a⁻¹)` gives `T^{a²}` modulo `Γ(p)`. -/
theorem conj_T (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    ∃ D : SL(2, ℤ), ∃ γ ∈ Gamma p, D * T * D⁻¹ = T ^ (a.val ^ 2) * γ := by
  set A : ℤ := (a.val : ℤ)
  set B : ℤ := ((a⁻¹).val : ℤ)
  have hAB : ((A * B - 1 : ℤ) : ZMod p) = 0 := by
    simp [A, B, mul_inv_cancel₀ ha]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hAB
  let D : SL(2, ℤ) := ⟨!![A, k; (p : ℤ), B], by simp [det_fin_two_of]; linarith⟩
  refine ⟨D, (T ^ (a.val ^ 2))⁻¹ * (D * T * D⁻¹), ?_, by group⟩
  rw [Gamma_mem', map_mul, map_inv, map_mul, map_mul, map_inv, map_pow]
  set φ := SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p))
  have hTn : ((φ T ^ (a.val ^ 2) : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![1, a ^ 2; 0, 1] := by
    rw [← map_pow, ← zpow_natCast, SpecialLinearGroup.map_apply_coe, coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ZMod.natCast_val]
  have hT' : ((φ T : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 1; 0, 1] := by
    rw [SpecialLinearGroup.map_apply_coe, coe_T]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hD : ((φ D : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![a, (k : ZMod p); 0, a⁻¹] := by
    rw [SpecialLinearGroup.map_apply_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [D, A, B]
  have key : φ D * φ T = φ T ^ (a.val ^ 2) * φ D := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hTn, hT', hD]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · field_simp
      ring
  simp only [mul_assoc]
  rw [← mul_assoc (SpecialLinearGroup.map _ D), key]
  group


/-- A finite-order operator that is not the identity has an eigenvalue `μ ≠ 1` with `μ^p = 1`. -/
theorem exists_eigen_ne_one [FiniteDimensional ℂ W] {p : ℕ} (hp : 0 < p) (A : W →ₗ[ℂ] W)
    (hAp : A ^ p = 1) (hA : A ≠ 1) :
    ∃ μ : ℂ, ∃ u : W, u ≠ 0 ∧ A u = μ • u ∧ μ ≠ 1 ∧ μ ^ p = 1 := by
  set U := LinearMap.range (A - 1)
  have hU : ∀ x ∈ U, A x ∈ U := by
    rintro _ ⟨y, rfl⟩
    exact ⟨A y, by simp [LinearMap.sub_apply]⟩
  have hnt : Nontrivial U := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro h
    apply hA
    ext x
    have : (A - 1) x ∈ U := LinearMap.mem_range_self _ x
    rw [h, Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A.restrict hU)
  obtain ⟨u, hu⟩ := hμ.exists_hasEigenvector
  have hu0 : (u : W) ≠ 0 := by
    intro h; exact hu.2 (Subtype.ext h)
  have hAu : A u = μ • (u : W) := by
    have := congrArg Subtype.val hu.apply_eq_smul
    simpa [LinearMap.restrict_apply] using this
  have hpow : ∀ j : ℕ, (A ^ j) u = μ ^ j • (u : W) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hAu, smul_smul, pow_succ]
  refine ⟨μ, u, hu0, hAu, ?_, ?_⟩
  · intro h1
    obtain ⟨x, hx⟩ := u.2
    rw [h1, one_smul] at hAu
    have hstep : ∀ j : ℕ, (A ^ j) x = x + (j : ℂ) • (u : W) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, hAu]
        have : A x = x + (u : W) := by rw [← hx]; simp [LinearMap.sub_apply]
        rw [this]; push_cast; module
    have := hstep p
    rw [hAp, Module.End.one_apply, left_eq_add, smul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (by exact_mod_cast hp.ne')
    · exact hu0 h
  · have := hpow p
    rw [hAp, Module.End.one_apply] at this
    have h2 : (μ ^ p - 1) • (u : W) = 0 := by rw [sub_smul, ← this, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hu0

/-- **Frobenius dimension bound.** A nonzero finite-dimensional representation of `SL(2,ℤ)` that is
trivial on `Γ(p)` (`p` prime) and has no nonzero invariant vector has dimension at least
`(p - 1)/2`. The unipotent `T` has an eigenvalue `ζ ≠ 1`, and conjugation by lifts of `diag(a, a⁻¹)`
makes every `ζ^{a²}` an eigenvalue. -/
theorem half_pred_le_finrank [FiniteDimensional ℂ W] (p : ℕ) [hp : Fact p.Prime]
    (ρ : Representation ℂ SL(2, ℤ) W) (hΓ : ∀ γ ∈ Gamma p, ρ γ = 1)
    (hinv : ∀ w : W, (∀ g, ρ g w = w) → w = 0) (hW : Nontrivial W) :
    p - 1 ≤ 2 * finrank ℂ W := by
  have hTp : ρ T ^ p = 1 := by rw [← map_pow]; exact hΓ _ (T_pow_mem_Gamma p)
  have hT1 : ρ T ≠ 1 := by
    intro hT
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (hinv w (fun g => by rw [rho_eq_one_of_T ρ hT g, Module.End.one_apply]))
  obtain ⟨μ, u, hu0, hTu, hμ1, hμp⟩ := exists_eigen_ne_one hp.out.pos (ρ T) hTp hT1
  have hprim : IsPrimitiveRoot μ p := by
    have hdvd : orderOf μ ∣ p := orderOf_dvd_of_pow_eq_one hμp
    rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hμ1
    · exact h ▸ IsPrimitiveRoot.orderOf μ
  have hpowu : ∀ j : ℕ, (ρ T ^ j) u = μ ^ j • u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hTu, smul_smul, pow_succ]
  have hmod : ∀ n : ℕ, μ ^ n = μ ^ (n % p) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hμp, one_pow, mul_one]
  -- eigenvectors attached to nonzero squares
  have heig : ∀ a : ZMod p, a ≠ 0 → ∃ w : W, w ≠ 0 ∧ ρ T w = μ ^ (a ^ 2).val • w := by
    intro a ha
    obtain ⟨D, γ, hγ, hD⟩ := conj_T p a ha
    refine ⟨ρ D⁻¹ u, ?_, ?_⟩
    · intro h
      apply hu0
      have := congrArg (ρ D) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
        map_zero] at this
    · have hTD : T * D⁻¹ = D⁻¹ * (T ^ (a.val ^ 2) * γ) := by
        rw [← hD]; group
      rw [← Module.End.mul_apply, ← map_mul, hTD, map_mul, map_mul, map_pow, Module.End.mul_apply,
        Module.End.mul_apply, hΓ γ hγ, Module.End.one_apply, hpowu, map_smul, hmod, pow_two a,
        ZMod.val_mul, ← pow_two]
  choose! w hw0 hw using heig
  set s := (Finset.univ : Finset (ZMod p)).filter (fun a => a ≠ 0)
  set S := s.image (fun a : ZMod p => a ^ 2)
  have hS : ∀ c ∈ S, ∃ a, a ≠ 0 ∧ a ^ 2 = c := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨a, (Finset.mem_filter.mp ha).2, rfl⟩
  choose! r hr0 hr using hS
  set v : S → W := fun c => w (r c.1)
  have hv : ∀ c : S, Module.End.HasEigenvector (ρ T) (μ ^ (c.1.val)) (v c) := by
    intro c
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hw0 _ (hr0 c.1 c.2)⟩
    have := hw (r c.1) (hr0 c.1 c.2)
    rwa [hr c.1 c.2] at this
  have hinj : Function.Injective (fun c : S => μ ^ (c.1.val)) := by
    intro c d h
    exact Subtype.ext (ZMod.val_injective p (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have hli := Module.End.eigenvectors_linearIndependent' (ρ T) _ hinj v hv
  have hcard : S.card ≤ finrank ℂ W := by
    simpa using hli.fintype_card_le_finrank
  have hs : s.card = p - 1 := by
    simp only [s]
    rw [Finset.filter_ne' Finset.univ (0 : ZMod p), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  have hfib : s.card ≤ 2 * S.card := by
    apply Finset.card_le_mul_card_image
    intro c hc
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hc
    calc (s.filter (fun a => a ^ 2 = b ^ 2)).card ≤ ({b, -b} : Finset (ZMod p)).card := by
          apply Finset.card_le_card
          intro a ha
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp (Finset.mem_filter.mp ha).2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  omega

end GaloisForLFunctions.RHTower.SarnakXue
