import GaloisForLFunctions.RHTower.DenseModelPointwise
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.CircleCovering

/-!
# Existence of a large multiplicative Bohr set

`exists_bohrSet` produces, for a finite family `T` of Dirichlet characters modulo `q` and a
resolution `M` with `8π/M ≤ c`, a set `B ⊆ (ZMod q)ˣ` on which every character of `T` stays within
`c` of `1`, with `φ(q) ≤ M^{#T} · #B`.

The construction is the standard pigeonhole: the `M`-point net on the unit circle
(`exists_circlePoint_close`) turns the tuple of character values at a point into an element of a
set of size `M^{#T}`; a largest fibre `A` has `#A ≥ φ(q)/M^{#T}`, and `B = A · y₀⁻¹` for any
`y₀ ∈ A` inherits the Bohr property by the triangle inequality.

Together with the results of `DenseModelBohr` and `DenseModelPointwise` this supplies every
ingredient of the multiplicative dense model theorem of Matomäki--Teräväinen.
-/

open Finset

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.AddComb

/-- **Existence of a large multiplicative Bohr set.**  For any finite family `T` of Dirichlet
characters modulo `q` and any resolution `M` with `8π/M ≤ c`, there is a set `B ⊆ (ZMod q)ˣ` on
which every character of `T` is within `c` of `1`, of size at least `φ(q)/M^#T`. -/
theorem exists_bohrSet (n : ℕ) (T : Finset (DirichletCharacter ℂ (n + 1))) {c : ℝ}
    {M : ℕ} (hM : 2 * Real.pi ≤ (M : ℝ)) (hMc : 8 * Real.pi / (M : ℝ) ≤ c) :
    ∃ B : Finset (ZMod (n + 1))ˣ, B.Nonempty ∧
      (∀ χ ∈ T, ∀ b ∈ B, ‖χ (b : ZMod (n + 1)) - 1‖ ≤ c) ∧
      (((n + 1).totient : ℝ)) ≤ (M : ℝ) ^ T.card * (B.card : ℝ) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hMposR : (0 : ℝ) < (M : ℝ) := by linarith
  have hMnat : 0 < M := by exact_mod_cast hMposR
  haveI : NeZero M := ⟨by omega⟩
  have hchoice : ∀ (a : (ZMod (n + 1))ˣ) (χ : DirichletCharacter ℂ (n + 1)),
      ∃ m : Fin M, ‖χ (a : ZMod (n + 1)) - circlePoint M (m : ℕ)‖ ≤ 4 * Real.pi / (M : ℝ) := by
    intro a χ
    obtain ⟨m, hm, hmle⟩ := exists_circlePoint_close (norm_unitChar n χ a) hM
    exact ⟨⟨m, hm⟩, hmle⟩
  choose idx hidx using hchoice
  set Φ : (ZMod (n + 1))ˣ → (↥T → Fin M) :=
    fun a χ => idx a (χ : DirichletCharacter ℂ (n + 1)) with hΦdef
  have hcardUnits : (Finset.univ : Finset (ZMod (n + 1))ˣ).card = (n + 1).totient := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient]
  have hsum : (n + 1).totient
      = ∑ y : (↥T → Fin M), (Finset.univ.filter (fun a => Φ a = y)).card := by
    rw [← hcardUnits]
    exact Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ _)
  have hne : (Finset.univ : Finset (↥T → Fin M)).Nonempty := by
    have : Nonempty (↥T → Fin M) := ⟨fun _ => ⟨0, hMnat⟩⟩
    exact Finset.univ_nonempty
  obtain ⟨y, -, hy⟩ := Finset.exists_max_image (Finset.univ : Finset (↥T → Fin M))
    (fun y => (Finset.univ.filter (fun a => Φ a = y)).card) hne
  set A : Finset (ZMod (n + 1))ˣ := Finset.univ.filter (fun a => Φ a = y) with hAdef
  have hcardFun : (Finset.univ : Finset (↥T → Fin M)).card = M ^ T.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hAbound : (n + 1).totient ≤ M ^ T.card * A.card := by
    rw [hsum]
    calc ∑ y' : (↥T → Fin M), (Finset.univ.filter (fun a => Φ a = y')).card
        ≤ (Finset.univ : Finset (↥T → Fin M)).card • A.card :=
          Finset.sum_le_card_nsmul _ _ _ (fun y' _ => hy y' (Finset.mem_univ y'))
      _ = M ^ T.card * A.card := by rw [hcardFun, smul_eq_mul]
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hcon
    have h0 : A.card = 0 := by omega
    rw [h0, Nat.mul_zero] at hAbound
    have : 0 < (n + 1).totient := Nat.totient_pos.2 (by omega)
    omega
  obtain ⟨y₀, hy₀⟩ := hAne
  refine ⟨A.image (fun x => x * y₀⁻¹), ?_, ?_, ?_⟩
  · exact ⟨y₀ * y₀⁻¹, Finset.mem_image_of_mem _ hy₀⟩
  · intro χ hχ b hb
    rw [Finset.mem_image] at hb
    obtain ⟨x, hxA, rfl⟩ := hb
    have hxy : Φ x = Φ y₀ := by
      have h1 : Φ x = y := (Finset.mem_filter.1 hxA).2
      have h2 : Φ y₀ = y := (Finset.mem_filter.1 hy₀).2
      rw [h1, h2]
    have hidxeq : idx x χ = idx y₀ χ := by
      have := congrFun hxy ⟨χ, hχ⟩
      simpa [hΦdef] using this
    have hxc := hidx x χ
    have hy0c := hidx y₀ χ
    rw [hidxeq] at hxc
    have hclose : ‖χ (x : ZMod (n + 1)) - χ (y₀ : ZMod (n + 1))‖ ≤ 8 * Real.pi / (M : ℝ) := by
      calc ‖χ (x : ZMod (n + 1)) - χ (y₀ : ZMod (n + 1))‖
          ≤ ‖χ (x : ZMod (n + 1)) - circlePoint M ((idx y₀ χ : Fin M) : ℕ)‖
            + ‖circlePoint M ((idx y₀ χ : Fin M) : ℕ) - χ (y₀ : ZMod (n + 1))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 4 * Real.pi / (M : ℝ) + 4 * Real.pi / (M : ℝ) := by
            rw [norm_sub_rev (circlePoint M ((idx y₀ χ : Fin M) : ℕ))]
            exact add_le_add hxc hy0c
        _ = 8 * Real.pi / (M : ℝ) := by ring
    have hinvnorm : ‖χ ((y₀⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1))‖ = 1 := norm_unitChar n χ y₀⁻¹
    have hfac : χ (((x * y₀⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1))) - 1
        = χ ((y₀⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1))
          * (χ (x : ZMod (n + 1)) - χ (y₀ : ZMod (n + 1))) := by
      rw [unitChar_mul n χ x y₀⁻¹, mul_sub]
      have hone : χ (y₀ : ZMod (n + 1)) * χ ((y₀⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) = 1 := by
        rw [← unitChar_mul n χ y₀ y₀⁻¹]
        simp
      rw [mul_comm (χ ((y₀⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1))) (χ (y₀ : ZMod (n + 1))), hone]
      ring
    rw [hfac, norm_mul, hinvnorm, one_mul]
    linarith [hclose, hMc]
  · have hcardimg : (A.image (fun x => x * y₀⁻¹)).card = A.card := by
      apply Finset.card_image_of_injective
      intro u v huv
      exact mul_right_cancel huv
    rw [hcardimg]
    have : ((n + 1).totient : ℝ) ≤ ((M ^ T.card * A.card : ℕ) : ℝ) := by exact_mod_cast hAbound
    calc ((n + 1).totient : ℝ) ≤ ((M ^ T.card * A.card : ℕ) : ℝ) := this
      _ = (M : ℝ) ^ T.card * (A.card : ℝ) := by push_cast; ring

end RHTower
