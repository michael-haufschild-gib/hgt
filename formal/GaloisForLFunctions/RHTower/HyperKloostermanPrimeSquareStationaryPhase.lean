import GaloisForLFunctions.RHTower.HyperKloostermanSecondMomentKernel

/-!
# Hyper-Kloosterman sums modulo a prime square, without Deligne's theorem

Let `s` be a prime and `ε = s` in `ZMod (s²)`, so `ε² = 0` and `(1 + εt)⁻¹ = 1 - εt`. Every sum
over units is unchanged by the multiplicative shifts `u ↦ u(1 + εt)`, and for a phase `F` these
shifts change `F` by `ε t ∂F` exactly. Averaging over `t ∈ ZMod (s²)` with
`Σ_t e(ε t c / s²) = s² [s ∣ c]` keeps only the points where every `∂F ≡ 0 (mod s)`
(`sum_eq_sum_ite_of_shift`).

* **Size of `Kl₃(y; s²)`.** For a unit `y`, `Kl₃(y; s²) = Σ_{a,b} e((a + b + y a⁻¹b⁻¹)/s²)`. The
  surviving pairs have `a ≡ b` and `a³ ≡ y (mod s)`, so there are at most `3s²` of them and
  `|Kl₃(y; s²)| ≤ 3s²` (`norm_hyperKloosterman_prime_sq_le`).
* **Correlation bound.** For units `β₁, β₂` and `s ∤ γ`, the sum
  `Σ_{x unit} Kl₃(β₁x; s²) Kl₃(β₂x; s²) e(γx/s²)` has at most six critical points modulo `s`:
  `a ≡ b, c ≡ d, a³ ≡ β₁x, c³ ≡ β₂x, a + c + γx ≡ 0`. Hence `c = κa` with `κ³ = β₂/β₁` and
  `a² = -(1+κ)β₁/γ`. Each critical point has `s⁵` lifts, so the sum is at most `6s⁵`
  (`norm_corr_prime_sq_le`). This is square-root cancellation in the variable `x`.

These are the two complete-sum inputs for the prime-square factor of a moduli average of `Kl₃`
over moduli `p s²`. Only elementary algebra in `ZMod (s²)` and polynomial root counts over
`ZMod s` are used.
-/

open Finset

namespace GaloisForLFunctions.RHTower.HyperKloostermanPrimeSquare

open GaloisForLFunctions.RHTower.HyperKloosterman
open GaloisForLFunctions.RHTower.HyperKloostermanSecondMoment

noncomputable section

/-- For a unit argument, `Kl₃(y; n)` is the sum over pairs of units
`Σ_{a,b} e(a + b + y a⁻¹ b⁻¹)`. -/
theorem hyperKloosterman_three_units {n : ℕ} [NeZero n] (y : (ZMod n)ˣ) :
    hyperKloosterman ZMod.stdAddChar 3 (y : ZMod n) =
      ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ,
        ZMod.stdAddChar ((a : ZMod n) + (b : ZMod n) + (y : ZMod n) * ((a⁻¹ : (ZMod n)ˣ) : ZMod n) *
          ((b⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
  classical
  unfold hyperKloosterman
  rw [sum_fin_three]
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hinner : ∀ a b : ZMod n, (∑ c : ZMod n,
      if a * b * c = (y : ZMod n) then ZMod.stdAddChar (a + b + c) else 0) =
      if IsUnit a ∧ IsUnit b then ZMod.stdAddChar (a + b + (y : ZMod n) * a⁻¹ * b⁻¹) else 0 := by
    intro a b
    by_cases hab : IsUnit a ∧ IsUnit b
    · rw [if_pos hab]
      obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := hab
      have hiff : ∀ c : ZMod n, ((u : ZMod n) * v * c = y) ↔
          c = (y : ZMod n) * (u : ZMod n)⁻¹ * (v : ZMod n)⁻¹ := by
        intro c
        rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit]
        constructor
        · intro h
          rw [← h]
          have hu : (u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv u
          have hv : (v : ZMod n) * ((v⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv v
          linear_combination (-(c * ((v⁻¹ : (ZMod n)ˣ) : ZMod n) * (v : ZMod n))) * hu -
            c * hv
        · intro h
          rw [h]
          have hu : (u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv u
          have hv : (v : ZMod n) * ((v⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv v
          linear_combination ((y : ZMod n) * (v : ZMod n) * ((v⁻¹ : (ZMod n)ˣ) : ZMod n)) * hu +
            (y : ZMod n) * hv
      simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [if_neg hab]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      intro h
      apply hab
      have hy : IsUnit (a * b * c) := h ▸ Units.isUnit y
      exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hy),
        isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hy)⟩
  simp_rw [hinner]
  simp_rw [← ZMod.inv_coe_unit]
  set G : ZMod n → ZMod n → ℂ := fun a b =>
    ZMod.stdAddChar (a + b + (y : ZMod n) * a⁻¹ * b⁻¹) with hG
  have key2 : (∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ, G a b) =
      ∑ a : ZMod n, if IsUnit a then ∑ b : (ZMod n)ˣ, G a b else 0 :=
    sum_units_eq (fun a => ∑ b : (ZMod n)ˣ, G a b)
  have key : ∀ a : ZMod n, (∑ b : (ZMod n)ˣ, G a b) =
      ∑ b : ZMod n, if IsUnit b then G a b else 0 := fun a => sum_units_eq (fun b => G a b)
  change _ = ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ, G a b
  rw [key2]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : IsUnit a
  · rw [if_pos ha, key]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : IsUnit b
    · rw [if_pos ⟨ha, hb⟩, if_pos hb]
    · rw [if_neg (fun h => hb h.2), if_neg hb]
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (fun h => ha h.1)]

/-- Exchange of two pairs of finite sums. -/
theorem sum_comm_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (G : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, G a b c d = ∑ c, ∑ d, ∑ a, ∑ b, G a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, G a b c d = ∑ a, ∑ c, ∑ b, ∑ d, G a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, G a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, G a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, G a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

section PrimeSquare

variable {s : ℕ} [hs : Fact s.Prime]

instance neZero_sq : NeZero (s ^ 2) := ⟨pow_ne_zero 2 hs.out.ne_zero⟩

/-- Reduction modulo `s` on `ZMod (s²)`. -/
def red (s : ℕ) : ZMod (s ^ 2) →+* ZMod s :=
  ZMod.castHom (dvd_pow_self s two_ne_zero) (ZMod s)

omit hs in
/-- `s` squares to zero in `ZMod (s²)`. -/
theorem eps_sq : (s : ZMod (s ^ 2)) * (s : ZMod (s ^ 2)) = 0 := by
  rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]

theorem red_apply (c : ZMod (s ^ 2)) : red s c = (c.val : ZMod s) := by
  rw [red, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- `s · c = 0` in `ZMod (s²)` exactly when `c ≡ 0 (mod s)`. -/
theorem eps_mul_eq_zero_iff (c : ZMod (s ^ 2)) :
    (s : ZMod (s ^ 2)) * c = 0 ↔ red s c = 0 := by
  have hs0 : 0 < s := hs.out.pos
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, red_apply, ZMod.natCast_eq_zero_iff]
  generalize c.val = v
  rw [sq]
  exact Nat.mul_dvd_mul_iff_left hs0

/-- The unit `1 + s t` of `ZMod (s²)`, with inverse `1 - s t`. -/
def shiftUnit (t : ZMod (s ^ 2)) : (ZMod (s ^ 2))ˣ where
  val := 1 + (s : ZMod (s ^ 2)) * t
  inv := 1 - (s : ZMod (s ^ 2)) * t
  val_inv := by linear_combination (-(t * t)) * (eps_sq (s := s))
  inv_val := by linear_combination (-(t * t)) * (eps_sq (s := s))

omit hs in
theorem val_shiftUnit (t : ZMod (s ^ 2)) :
    ((shiftUnit t : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) = 1 + (s : ZMod (s ^ 2)) * t := rfl

omit hs in
theorem val_shiftUnit_inv (t : ZMod (s ^ 2)) :
    (((shiftUnit t)⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) = 1 - (s : ZMod (s ^ 2)) * t := rfl

omit hs in
/-- First-order expansion of the `Kl₃` phase under the shifts `a ↦ a(1+st₁)`, `b ↦ b(1+st₂)`. -/
theorem phase_shift (y : ZMod (s ^ 2)) (a b : (ZMod (s ^ 2))ˣ) (t₁ t₂ : ZMod (s ^ 2)) :
    ((a * shiftUnit t₁ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) +
        ((b * shiftUnit t₂ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) +
        y * (((a * shiftUnit t₁)⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
          (((b * shiftUnit t₂)⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) =
      ((a : ZMod (s ^ 2)) + (b : ZMod (s ^ 2)) + y * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
          ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) +
        t₁ * ((s : ZMod (s ^ 2)) * ((a : ZMod (s ^ 2)) -
          y * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)))) +
        t₂ * ((s : ZMod (s ^ 2)) * ((b : ZMod (s ^ 2)) -
          y * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)))) := by
  simp only [mul_inv_rev, Units.val_mul, val_shiftUnit, val_shiftUnit_inv]
  linear_combination (y * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
    ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * t₁ * t₂) * (eps_sq (s := s))

/-- **Stationary phase for `Kl₃` modulo a prime square.** For a unit `y`, only the pairs
`(a, b)` with `a ≡ b ≡ y a⁻¹ b⁻¹ (mod s)` survive:
`Kl₃(y; s²) = Σ_{a,b : s ∣ a - y a⁻¹b⁻¹, s ∣ b - y a⁻¹b⁻¹} e((a + b + y a⁻¹ b⁻¹)/s²)`.
Averaging over the multiplicative shifts `1 + s t` kills every other pair. -/
theorem hyperKloosterman_prime_sq_crit (y : (ZMod (s ^ 2))ˣ) :
    hyperKloosterman ZMod.stdAddChar 3 (y : ZMod (s ^ 2)) =
      ∑ a : (ZMod (s ^ 2))ˣ, ∑ b : (ZMod (s ^ 2))ˣ,
        if red s ((a : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
              ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) = 0 ∧
            red s ((b : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
              ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) = 0 then
          ZMod.stdAddChar ((a : ZMod (s ^ 2)) + (b : ZMod (s ^ 2)) + (y : ZMod (s ^ 2)) *
            ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)))
        else 0 := by
  classical
  rw [hyperKloosterman_three_units]
  set Φ : (ZMod (s ^ 2))ˣ → (ZMod (s ^ 2))ˣ → ℂ := fun a b =>
    ZMod.stdAddChar ((a : ZMod (s ^ 2)) + (b : ZMod (s ^ 2)) + (y : ZMod (s ^ 2)) *
      ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) with hΦ
  set X₁ : (ZMod (s ^ 2))ˣ → (ZMod (s ^ 2))ˣ → ZMod (s ^ 2) := fun a b =>
    (s : ZMod (s ^ 2)) * ((a : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) *
      ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) with hX₁
  set X₂ : (ZMod (s ^ 2))ˣ → (ZMod (s ^ 2))ˣ → ZMod (s ^ 2) := fun a b =>
    (s : ZMod (s ^ 2)) * ((b : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) *
      ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) with hX₂
  -- invariance under the shifts
  have hinv : ∀ t₁ t₂ : ZMod (s ^ 2), (∑ a, ∑ b, Φ a b) =
      ∑ a, ∑ b, Φ a b * ZMod.stdAddChar (t₁ * X₁ a b) * ZMod.stdAddChar (t₂ * X₂ a b) := by
    intro t₁ t₂
    have h1 : (∑ a, ∑ b, Φ a b) = ∑ a, ∑ b, Φ (a * shiftUnit t₁) (b * shiftUnit t₂) :=
      (Fintype.sum_equiv (Equiv.mulRight (shiftUnit t₁))
        (fun a => ∑ b, Φ (a * shiftUnit t₁) (b * shiftUnit t₂)) (fun a => ∑ b, Φ a b)
        (fun a => Fintype.sum_equiv (Equiv.mulRight (shiftUnit t₂)) _ _ (fun b => rfl))).symm
    rw [h1]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hΦ, hX₁, hX₂]
    rw [phase_shift, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  have hcard : ((Fintype.card (ZMod (s ^ 2)) : ℂ)) ^ 2 * (∑ a, ∑ b, Φ a b) =
      ∑ a, ∑ b, Φ a b * (if X₁ a b = 0 then ((s ^ 2 : ℕ) : ℂ) else 0) *
        (if X₂ a b = 0 then ((s ^ 2 : ℕ) : ℂ) else 0) := by
    calc ((Fintype.card (ZMod (s ^ 2)) : ℂ)) ^ 2 * (∑ a, ∑ b, Φ a b)
        = ∑ t₁ : ZMod (s ^ 2), ∑ t₂ : ZMod (s ^ 2), (∑ a, ∑ b, Φ a b) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
          ring
      _ = ∑ t₁ : ZMod (s ^ 2), ∑ t₂ : ZMod (s ^ 2), ∑ a, ∑ b,
            Φ a b * ZMod.stdAddChar (t₁ * X₁ a b) * ZMod.stdAddChar (t₂ * X₂ a b) := by
          refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => hinv t₁ t₂
      _ = ∑ a, ∑ b, Φ a b * (∑ t₁ : ZMod (s ^ 2), ZMod.stdAddChar (t₁ * X₁ a b)) *
            (∑ t₂ : ZMod (s ^ 2), ZMod.stdAddChar (t₂ * X₂ a b)) := by
          rw [sum_comm_four]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t₂ _ => ?_
          ring
      _ = _ := by
          simp_rw [sum_stdAddChar_mul]
  have hc : (Fintype.card (ZMod (s ^ 2)) : ℂ) = ((s ^ 2 : ℕ) : ℂ) := by rw [ZMod.card]
  have hne : ((s ^ 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (s ^ 2))
  rw [hc] at hcard
  have hterm : ∀ a b, Φ a b * (if X₁ a b = 0 then ((s ^ 2 : ℕ) : ℂ) else 0) *
      (if X₂ a b = 0 then ((s ^ 2 : ℕ) : ℂ) else 0) = ((s ^ 2 : ℕ) : ℂ) ^ 2 *
      (if red s ((a : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
              ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) = 0 ∧
            red s ((b : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
              ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) = 0 then Φ a b else 0) := by
    intro a b
    simp only [hX₁, hX₂, eps_mul_eq_zero_iff]
    split_ifs <;> first | (exfalso; tauto) | ring
  simp_rw [hterm, ← Finset.mul_sum] at hcard
  exact mul_left_cancel₀ (pow_ne_zero 2 hne) hcard

/-- Each residue class modulo `s` has at most `s` lifts to `ZMod (s²)`. -/
theorem card_red_fiber_le (v : ZMod s) :
    (univ.filter (fun x : ZMod (s ^ 2) => red s x = v)).card ≤ s := by
  classical
  calc (univ.filter (fun x : ZMod (s ^ 2) => red s x = v)).card ≤ (Finset.range s).card := by
        refine Finset.card_le_card_of_injOn (fun x => x.val / s) ?_ ?_
        · intro x _
          simp only [Finset.coe_range, Set.mem_Iio]
          apply Nat.div_lt_of_lt_mul
          have := ZMod.val_lt x
          calc x.val < s ^ 2 := this
            _ = s * s := sq s
        · intro x hx x' hx' hxx'
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hx'
          rw [red_apply] at hx hx'
          have hmod : x.val % s = x'.val % s :=
            (ZMod.natCast_eq_natCast_iff' _ _ _).1 (hx.trans hx'.symm)
          apply ZMod.val_injective
          simp only at hxx'
          rw [← Nat.div_add_mod x.val s, ← Nat.div_add_mod x'.val s, hmod, hxx']
    _ = s := Finset.card_range s

/-- At most `3s` residues of `ZMod (s²)` have cube `≡ c (mod s)`. -/
theorem card_red_cube_le (c : ZMod s) :
    (univ.filter (fun x : ZMod (s ^ 2) => red s x ^ 3 = c)).card ≤ 3 * s := by
  classical
  set T := (Polynomial.nthRoots 3 c).toFinset
  have hsub : univ.filter (fun x : ZMod (s ^ 2) => red s x ^ 3 = c) ⊆
      T.biUnion (fun v => univ.filter (fun x : ZMod (s ^ 2) => red s x = v)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨red s x, by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]; exact hx, rfl⟩
  calc (univ.filter (fun x : ZMod (s ^ 2) => red s x ^ 3 = c)).card
      ≤ (T.biUnion (fun v => univ.filter (fun x : ZMod (s ^ 2) => red s x = v))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ T, (univ.filter (fun x : ZMod (s ^ 2) => red s x = v)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ T, s := Finset.sum_le_sum fun v _ => card_red_fiber_le v
    _ = T.card * s := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 3 * s := Nat.mul_le_mul_right _
        ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 c))

/-- A sum of nonnegative terms over the units is at most the sum over all residues. -/
theorem sum_units_le_sum {n : ℕ} [NeZero n] (f : ZMod n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ u : (ZMod n)ˣ, f u ≤ ∑ x : ZMod n, f x := by
  rw [sum_units_eq]
  exact Finset.sum_le_sum fun x _ => by split_ifs <;> simp [hf x]

/-- **Deligne-free bound modulo a prime square:** `|Kl₃(y; s²)| ≤ 3s²` for every unit `y`. -/
theorem norm_hyperKloosterman_prime_sq_le (y : (ZMod (s ^ 2))ˣ) :
    ‖hyperKloosterman ZMod.stdAddChar 3 (y : ZMod (s ^ 2))‖ ≤ 3 * (s : ℝ) ^ 2 := by
  classical
  rw [hyperKloosterman_prime_sq_crit]
  set Y := red s (y : ZMod (s ^ 2))
  have hcrit : ∀ a b : (ZMod (s ^ 2))ˣ,
      red s ((a : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
          ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) = 0 →
      red s ((b : ZMod (s ^ 2)) - (y : ZMod (s ^ 2)) * ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
          ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))) = 0 →
      red s (a : ZMod (s ^ 2)) ^ 3 = Y ∧ red s (b : ZMod (s ^ 2)) = red s (a : ZMod (s ^ 2)) := by
    intro a b h1 h2
    have hu : red s ((a⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * red s (a : ZMod (s ^ 2)) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    have hv : red s ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * red s (b : ZMod (s ^ 2)) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rw [map_sub, map_mul, map_mul] at h1 h2
    have hb : red s (b : ZMod (s ^ 2)) = red s (a : ZMod (s ^ 2)) := by
      linear_combination h2 - h1
    refine ⟨?_, hb⟩
    linear_combination (red s (a : ZMod (s ^ 2)) * red s (b : ZMod (s ^ 2))) * h1 +
      (Y * (red s ((b⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * red s (b : ZMod (s ^ 2)))) * hu +
      Y * hv - red s (a : ZMod (s ^ 2)) ^ 2 * hb
  calc _ ≤ ∑ a : (ZMod (s ^ 2))ˣ, ∑ b : (ZMod (s ^ 2))ˣ,
        (if red s (a : ZMod (s ^ 2)) ^ 3 = Y ∧ red s (b : ZMod (s ^ 2)) = red s (a : ZMod (s ^ 2))
          then (1 : ℝ) else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        split_ifs with h h'
        · rw [AddChar.norm_apply]
        · exact absurd (hcrit a b h.1 h.2) h'
        · simp
        · simp
    _ ≤ ∑ x : ZMod (s ^ 2), ∑ x' : ZMod (s ^ 2),
        (if red s x ^ 3 = Y ∧ red s x' = red s x then (1 : ℝ) else 0) := by
        refine (sum_units_le_sum (fun x => ∑ b : (ZMod (s ^ 2))ˣ,
          (if red s x ^ 3 = Y ∧ red s (b : ZMod (s ^ 2)) = red s x then (1 : ℝ) else 0))
          (fun x => Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num)).trans ?_
        refine Finset.sum_le_sum fun x _ => ?_
        exact sum_units_le_sum (fun x' => if red s x ^ 3 = Y ∧ red s x' = red s x then (1 : ℝ) else 0)
          (fun x' => by split_ifs <;> norm_num)
    _ = ∑ x : ZMod (s ^ 2), (if red s x ^ 3 = Y then
          ((univ.filter (fun x' : ZMod (s ^ 2) => red s x' = red s x)).card : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs with hx
        · simp only [hx, true_and]
          rw [Finset.sum_boole]
        · simp [hx]
    _ ≤ ∑ x : ZMod (s ^ 2), (if red s x ^ 3 = Y then (s : ℝ) else 0) := by
        refine Finset.sum_le_sum fun x _ => ?_
        split_ifs
        · exact_mod_cast card_red_fiber_le (red s x)
        · exact le_rfl
    _ = ((univ.filter (fun x : ZMod (s ^ 2) => red s x ^ 3 = Y)).card : ℝ) * s := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * s : ℕ) * (s : ℝ) := by
        gcongr
        exact_mod_cast card_red_cube_le Y
    _ = 3 * (s : ℝ) ^ 2 := by push_cast; ring

/-- **Averaging over a first-order shift.** If right multiplication by `g t` multiplies `Φ` by the
character `e(t · X)`, then only the zeros of `X` contribute to `Σ Φ`. -/
theorem sum_eq_sum_ite_of_shift {G : Type*} [Group G] [Fintype G]
    (g : ZMod (s ^ 2) → G) (Φ : G → ℂ) (X : G → ZMod (s ^ 2))
    (h : ∀ v t, Φ (v * g t) = Φ v * ZMod.stdAddChar (t * X v)) :
    ∑ v, Φ v = ∑ v, if X v = 0 then Φ v else 0 := by
  classical
  have hne : ((s ^ 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (s ^ 2))
  have hshift : ∀ t, ∑ v, Φ v = ∑ v, Φ v * ZMod.stdAddChar (t * X v) := by
    intro t
    exact (Fintype.sum_equiv (Equiv.mulRight (g t)) (fun v => Φ v * ZMod.stdAddChar (t * X v))
      (fun v => Φ v) (fun v => (h v t).symm)).symm
  have hcard : ((s ^ 2 : ℕ) : ℂ) * ∑ v, Φ v = ((s ^ 2 : ℕ) : ℂ) * ∑ v, if X v = 0 then Φ v else 0 := by
    calc ((s ^ 2 : ℕ) : ℂ) * ∑ v, Φ v = ∑ t : ZMod (s ^ 2), ∑ v, Φ v := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = ∑ t : ZMod (s ^ 2), ∑ v, Φ v * ZMod.stdAddChar (t * X v) :=
          Finset.sum_congr rfl fun t _ => hshift t
      _ = ∑ v, Φ v * ∑ t : ZMod (s ^ 2), ZMod.stdAddChar (t * X v) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [sum_stdAddChar_mul]
          split_ifs <;> ring
  exact mul_left_cancel₀ hne hcard

theorem red_natCast_self : red s (s : ZMod (s ^ 2)) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

theorem red_shift (u : (ZMod (s ^ 2))ˣ) (t : ZMod (s ^ 2)) :
    red s (((u * shiftUnit t : (ZMod (s ^ 2))ˣ)) : ZMod (s ^ 2)) = red s (u : ZMod (s ^ 2)) := by
  rw [Units.val_mul, val_shiftUnit, map_mul, map_add, map_mul, red_natCast_self, map_one]
  ring

theorem red_shift_inv (u : (ZMod (s ^ 2))ˣ) (t : ZMod (s ^ 2)) :
    red s ((((u * shiftUnit t)⁻¹ : (ZMod (s ^ 2))ˣ)) : ZMod (s ^ 2)) =
      red s (((u⁻¹ : (ZMod (s ^ 2))ˣ)) : ZMod (s ^ 2)) := by
  rw [mul_inv_rev, Units.val_mul, val_shiftUnit_inv, map_mul, map_sub, map_mul, red_natCast_self,
    map_one]
  ring

/-- Five units `(x, a, b, c, d)`. -/
abbrev Five (s : ℕ) := (ZMod (s ^ 2))ˣ × (ZMod (s ^ 2))ˣ × (ZMod (s ^ 2))ˣ × (ZMod (s ^ 2))ˣ ×
  (ZMod (s ^ 2))ˣ

/-- Coordinates and inverse coordinates of five units, in `ZMod (s²)`. -/
abbrev cx (v : Five s) : ZMod (s ^ 2) := v.1
abbrev ca (v : Five s) : ZMod (s ^ 2) := v.2.1
abbrev cb (v : Five s) : ZMod (s ^ 2) := v.2.2.1
abbrev cc (v : Five s) : ZMod (s ^ 2) := v.2.2.2.1
abbrev cd (v : Five s) : ZMod (s ^ 2) := v.2.2.2.2
abbrev ia (v : Five s) : ZMod (s ^ 2) := ((v.2.1⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))
abbrev ib (v : Five s) : ZMod (s ^ 2) := ((v.2.2.1⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))
abbrev ic (v : Five s) : ZMod (s ^ 2) := ((v.2.2.2.1⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))
abbrev id' (v : Five s) : ZMod (s ^ 2) := ((v.2.2.2.2⁻¹ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2))

/-- The phase of the correlation sum `Σ_x Kl₃(β₁x) Kl₃(β₂x) e(γx)` in the variables
`(x, a, b, c, d)`. -/
def corrPhase (β₁ β₂ γ : ZMod (s ^ 2)) (v : Five s) : ZMod (s ^ 2) :=
  ca v + cb v + cc v + cd v + cx v * (β₁ * ia v * ib v + β₂ * ic v * id' v + γ)

/-- The five first derivatives of the phase, before multiplication by `s`. -/
def corrE (β₁ β₂ γ : ZMod (s ^ 2)) (v : Five s) : Fin 5 → ZMod (s ^ 2) :=
  ![cx v * (β₁ * ia v * ib v + β₂ * ic v * id' v + γ),
    ca v - cx v * β₁ * ia v * ib v, cb v - cx v * β₁ * ia v * ib v,
    cc v - cx v * β₂ * ic v * id' v, cd v - cx v * β₂ * ic v * id' v]

/-- The shift of the `j`-th coordinate by `1 + s t`. -/
def gShift : Fin 5 → ZMod (s ^ 2) → Five s :=
  ![fun t => (shiftUnit t, 1, 1, 1, 1), fun t => (1, shiftUnit t, 1, 1, 1),
    fun t => (1, 1, shiftUnit t, 1, 1), fun t => (1, 1, 1, shiftUnit t, 1),
    fun t => (1, 1, 1, 1, shiftUnit t)]

omit hs in
theorem corrPhase_shift (β₁ β₂ γ : ZMod (s ^ 2)) (v : Five s) (j : Fin 5) (t : ZMod (s ^ 2)) :
    corrPhase β₁ β₂ γ (v * gShift j t) =
      corrPhase β₁ β₂ γ v + t * ((s : ZMod (s ^ 2)) * corrE β₁ β₂ γ v j) := by
  obtain ⟨x, a, b, c, d⟩ := v
  fin_cases j <;>
  · simp only [gShift, corrPhase, corrE, Prod.mk_mul_mk, Fin.isValue, Fin.reduceFinMk,
      Fin.zero_eta, Fin.mk_one, mul_one, Units.val_mul, mul_inv_rev,
      val_shiftUnit, val_shiftUnit_inv, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, cx, ca, cb, cc, cd, ia, ib, ic, id']
    ring

theorem red_corrE_shift (β₁ β₂ γ : ZMod (s ^ 2)) (v : Five s) (i j : Fin 5) (t : ZMod (s ^ 2)) :
    red s (corrE β₁ β₂ γ (v * gShift j t) i) = red s (corrE β₁ β₂ γ v i) := by
  obtain ⟨x, a, b, c, d⟩ := v
  fin_cases j <;> fin_cases i <;>
  · simp only [gShift, corrE, Prod.mk_mul_mk, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, mul_one, map_add, map_mul, map_sub, red_shift, red_shift_inv,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, cx, ca, cb, cc, cd, ia, ib, ic,
      id']

/-- One averaging step: add the condition `red (E_j) = 0` to a shift-invariant condition. -/
theorem corr_step (β₁ β₂ γ : ZMod (s ^ 2)) (j : Fin 5) (P : Five s → Prop) [DecidablePred P]
    (hP : ∀ v t, P (v * gShift j t) ↔ P v) :
    ∑ v : Five s, (if P v then ZMod.stdAddChar (corrPhase β₁ β₂ γ v) else 0) =
      ∑ v : Five s, (if P v ∧ red s (corrE β₁ β₂ γ v j) = 0 then
        ZMod.stdAddChar (corrPhase β₁ β₂ γ v) else 0) := by
  classical
  rw [sum_eq_sum_ite_of_shift (gShift j)
    (fun v => if P v then ZMod.stdAddChar (corrPhase β₁ β₂ γ v) else 0)
    (fun v => (s : ZMod (s ^ 2)) * corrE β₁ β₂ γ v j) ?_]
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp only [eps_mul_eq_zero_iff]
    by_cases h1 : red s (corrE β₁ β₂ γ v j) = 0 <;> by_cases h2 : P v <;> simp [h1, h2]
  · intro v t
    simp only [hP, corrPhase_shift, AddChar.map_add_eq_mul]
    split_ifs <;> simp

/-- The five reduced critical conditions. -/
def CorrCrit (β₁ β₂ γ : ZMod (s ^ 2)) (v : Five s) : Prop :=
  red s (corrE β₁ β₂ γ v 0) = 0 ∧ red s (corrE β₁ β₂ γ v 1) = 0 ∧
    red s (corrE β₁ β₂ γ v 2) = 0 ∧ red s (corrE β₁ β₂ γ v 3) = 0 ∧
    red s (corrE β₁ β₂ γ v 4) = 0

instance (β₁ β₂ γ : ZMod (s ^ 2)) : DecidablePred (CorrCrit (s := s) β₁ β₂ γ) := by
  unfold CorrCrit; infer_instance

/-- **Stationary phase for the correlation sum:** only critical points modulo `s` survive. -/
theorem sum_corrPhase_eq_crit (β₁ β₂ γ : ZMod (s ^ 2)) :
    ∑ v : Five s, ZMod.stdAddChar (corrPhase β₁ β₂ γ v) =
      ∑ v : Five s, (if CorrCrit β₁ β₂ γ v then ZMod.stdAddChar (corrPhase β₁ β₂ γ v) else 0) := by
  classical
  have e0 : ∑ v : Five s, ZMod.stdAddChar (corrPhase β₁ β₂ γ v) =
      ∑ v : Five s, (if True then ZMod.stdAddChar (corrPhase β₁ β₂ γ v) else 0) := by simp
  rw [e0, corr_step β₁ β₂ γ 0 (fun _ => True) (fun _ _ => Iff.rfl)]
  rw [corr_step β₁ β₂ γ 1 _ (fun v t => by simp only [red_corrE_shift])]
  rw [corr_step β₁ β₂ γ 2 _ (fun v t => by simp only [red_corrE_shift])]
  rw [corr_step β₁ β₂ γ 3 _ (fun v t => by simp only [red_corrE_shift])]
  rw [corr_step β₁ β₂ γ 4 _ (fun v t => by simp only [red_corrE_shift])]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold CorrCrit
  simp only [true_and, and_assoc]
  exact if_congr Iff.rfl rfl rfl

/-- The critical conditions after reduction modulo `s`, in the variables `x, a, b, c, d`. -/
def CondRed (b₁ b₂ g X A B C D : ZMod s) : Prop :=
  B = A ∧ D = C ∧ A ^ 3 = b₁ * X ∧ C ^ 3 = b₂ * X ∧ A + C + g * X = 0 ∧ A ≠ 0

instance (b₁ b₂ g X A B C D : ZMod s) : Decidable (CondRed b₁ b₂ g X A B C D) := by
  unfold CondRed; infer_instance

theorem red_inv_mul (u : (ZMod (s ^ 2))ˣ) :
    red s (((u⁻¹ : (ZMod (s ^ 2))ˣ)) : ZMod (s ^ 2)) * red s (u : ZMod (s ^ 2)) = 1 := by
  rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

/-- A critical point reduces to a solution of `CondRed`. -/
theorem condRed_of_crit (β₁ β₂ γ : ZMod (s ^ 2)) (v : Five s) (h : CorrCrit β₁ β₂ γ v) :
    CondRed (red s β₁) (red s β₂) (red s γ) (red s (cx v)) (red s (ca v)) (red s (cb v))
      (red s (cc v)) (red s (cd v)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  simp only [corrE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, map_mul,
    map_add, map_sub] at h0 h1 h2 h3 h4
  have hA := red_inv_mul v.2.1
  have hB := red_inv_mul v.2.2.1
  have hC := red_inv_mul v.2.2.2.1
  have hD := red_inv_mul v.2.2.2.2
  set X := red s (cx v)
  set A := red s (ca v)
  set B := red s (cb v)
  set C := red s (cc v)
  set D := red s (cd v)
  set A' := red s (ia v)
  set B' := red s (ib v)
  set C' := red s (ic v)
  set D' := red s (id' v)
  have hBA : B = A := by linear_combination h2 - h1
  have hDC : D = C := by linear_combination h4 - h3
  refine ⟨hBA, hDC, ?_, ?_, ?_, ?_⟩
  · linear_combination (A * B) * h1 + (red s β₁ * X * (B' * B)) * hA +
      (red s β₁ * X) * hB - A ^ 2 * hBA
  · linear_combination (C * D) * h3 + (red s β₂ * X * (D' * D)) * hC +
      (red s β₂ * X) * hD - C ^ 2 * hDC
  · linear_combination h0 + h1 + h3
  · intro h0'
    rw [h0', mul_zero] at hA
    exact zero_ne_one hA

/-- **At most six critical points modulo `s`.** For `b₁, g ≠ 0` the system
`B = A, D = C, A³ = b₁X, C³ = b₂X, A + C + gX = 0, A ≠ 0` has at most six solutions:
`C = κA` with `κ³ = b₂/b₁` and `A² = -(1+κ)b₁/g`. -/
theorem card_condRed_le (b₁ b₂ g : ZMod s) (hb₁ : b₁ ≠ 0) (hg : g ≠ 0) :
    (univ.filter (fun p : ZMod s × ZMod s × ZMod s × ZMod s × ZMod s =>
      CondRed b₁ b₂ g p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).card ≤ 6 := by
  classical
  set T := (Polynomial.nthRoots 3 (b₂ * b₁⁻¹)).toFinset.biUnion (fun κ =>
    (Polynomial.nthRoots 2 (-(1 + κ) * b₁ * g⁻¹)).toFinset.image
      (fun A => (b₁⁻¹ * A ^ 3, A, A, κ * A, κ * A))) with hT
  have hsub : univ.filter (fun p : ZMod s × ZMod s × ZMod s × ZMod s × ZMod s =>
      CondRed b₁ b₂ g p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ⊆ T := by
    rintro ⟨X, A, B, C, D⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, CondRed] at hp
    obtain ⟨hBA, hDC, hA3, hC3, hsum, hA0⟩ := hp
    subst hBA hDC
    have hX : X = b₁⁻¹ * B ^ 3 := by
      rw [hA3]; field_simp
    have hX0 : X ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hA3; exact hA0 (pow_eq_zero_iff (by norm_num) |>.1 hA3)
    simp only [hT, Finset.mem_biUnion, Finset.mem_image, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots (by norm_num : 0 < 3), Polynomial.mem_nthRoots (by norm_num : 0 < 2)]
    refine ⟨D * B⁻¹, ?_, B, ?_, ?_⟩
    · rw [mul_pow, inv_pow, hC3, hA3]
      field_simp
    · rw [show D = -B - g * X by linear_combination hsum, hX]
      field_simp
      ring
    · rw [← hX]
      simp only [Prod.mk.injEq, true_and]
      constructor <;> field_simp
  calc (univ.filter (fun p : ZMod s × ZMod s × ZMod s × ZMod s × ZMod s =>
        CondRed b₁ b₂ g p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).card ≤ T.card :=
        Finset.card_le_card hsub
    _ ≤ ∑ κ ∈ (Polynomial.nthRoots 3 (b₂ * b₁⁻¹)).toFinset,
          ((Polynomial.nthRoots 2 (-(1 + κ) * b₁ * g⁻¹)).toFinset.image
            (fun A => (b₁⁻¹ * A ^ 3, A, A, κ * A, κ * A))).card := Finset.card_biUnion_le
    _ ≤ ∑ _κ ∈ (Polynomial.nthRoots 3 (b₂ * b₁⁻¹)).toFinset, 2 := by
        refine Finset.sum_le_sum fun κ _ => ?_
        exact Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans
          (Polynomial.card_nthRoots 2 _))
    _ = (Polynomial.nthRoots 3 (b₂ * b₁⁻¹)).toFinset.card * 2 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 3 * 2 := Nat.mul_le_mul_right _
        ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 _))

/-- Summing a nonnegative function of the reduction over the units of `ZMod (s²)` costs at most a
factor `s` against the sum over `ZMod s`. -/
theorem sum_units_red_le (f : ZMod s → ℝ) (hf : ∀ X, 0 ≤ f X) :
    ∑ u : (ZMod (s ^ 2))ˣ, f (red s (u : ZMod (s ^ 2))) ≤ s * ∑ X : ZMod s, f X := by
  classical
  refine (sum_units_le_sum (fun x => f (red s x)) (fun x => hf _)).trans ?_
  rw [← Finset.sum_fiberwise Finset.univ (red s) (fun x => f (red s x)), Finset.mul_sum]
  refine Finset.sum_le_sum fun X _ => ?_
  have hc : ∑ x ∈ Finset.univ.filter (fun x : ZMod (s ^ 2) => red s x = X), f (red s x) =
      (Finset.univ.filter (fun x : ZMod (s ^ 2) => red s x = X)).card * f X := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2]
  rw [hc]
  gcongr
  · exact hf X
  · exact_mod_cast card_red_fiber_le X

/-- **Deligne-free correlation bound modulo a prime square.** For units `β₁, β₂` and `s ∤ γ`,
`|Σ_{x unit} Kl₃(β₁x; s²) Kl₃(β₂x; s²) e(γx/s²)| ≤ 6 s⁵`. Averaging over the first-order shifts
leaves only critical points, and there are at most six of them modulo `s`, each with `s⁵` lifts. -/
theorem norm_corr_prime_sq_le (β₁ β₂ : (ZMod (s ^ 2))ˣ) (γ : ZMod (s ^ 2)) (hγ : red s γ ≠ 0) :
    ‖∑ x : (ZMod (s ^ 2))ˣ, hyperKloosterman ZMod.stdAddChar 3 ((β₁ : ZMod (s ^ 2)) * (x : ZMod (s ^ 2))) *
        hyperKloosterman ZMod.stdAddChar 3 ((β₂ : ZMod (s ^ 2)) * (x : ZMod (s ^ 2))) *
        ZMod.stdAddChar (γ * (x : ZMod (s ^ 2)))‖ ≤ 6 * (s : ℝ) ^ 5 := by
  classical
  have hb₁ : red s (β₁ : ZMod (s ^ 2)) ≠ 0 := by
    intro h0; have := red_inv_mul β₁; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hexp : ∑ x : (ZMod (s ^ 2))ˣ, hyperKloosterman ZMod.stdAddChar 3 ((β₁ : ZMod (s ^ 2)) * (x : ZMod (s ^ 2))) *
        hyperKloosterman ZMod.stdAddChar 3 ((β₂ : ZMod (s ^ 2)) * (x : ZMod (s ^ 2))) *
        ZMod.stdAddChar (γ * (x : ZMod (s ^ 2))) =
      ∑ v : Five s, ZMod.stdAddChar (corrPhase (β₁ : ZMod (s ^ 2)) β₂ γ v) := by
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Units.val_mul, ← Units.val_mul, hyperKloosterman_three_units,
      hyperKloosterman_three_units]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum_comm_four]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [corrPhase, cx, ca, cb, cc, cd, ia, ib, ic, id', Units.val_mul]
    ring
  rw [hexp, sum_corrPhase_eq_crit]
  set b₁ := red s (β₁ : ZMod (s ^ 2))
  set b₂ := red s (β₂ : ZMod (s ^ 2))
  set g := red s γ
  calc _ ≤ ∑ v : Five s, (if CondRed b₁ b₂ g (red s (cx v)) (red s (ca v)) (red s (cb v))
          (red s (cc v)) (red s (cd v)) then (1 : ℝ) else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
        split_ifs with h h'
        · rw [AddChar.norm_apply]
        · exact absurd (condRed_of_crit _ _ _ v h) h'
        · simp
        · simp
    _ = ∑ x : (ZMod (s ^ 2))ˣ, ∑ a : (ZMod (s ^ 2))ˣ, ∑ b : (ZMod (s ^ 2))ˣ,
          ∑ c : (ZMod (s ^ 2))ˣ, ∑ d : (ZMod (s ^ 2))ˣ,
          (if CondRed b₁ b₂ g (red s (x : ZMod (s ^ 2))) (red s (a : ZMod (s ^ 2)))
            (red s (b : ZMod (s ^ 2))) (red s (c : ZMod (s ^ 2))) (red s (d : ZMod (s ^ 2)))
            then (1 : ℝ) else 0) := by
        simp only [Fintype.sum_prod_type]
    _ ≤ s * ∑ X : ZMod s, (s * ∑ A : ZMod s, (s * ∑ B : ZMod s, (s * ∑ C : ZMod s,
          (s * ∑ D : ZMod s, (if CondRed b₁ b₂ g X A B C D then (1 : ℝ) else 0))))) := by
        refine (sum_units_red_le (fun X => ∑ a : (ZMod (s ^ 2))ˣ, ∑ b : (ZMod (s ^ 2))ˣ,
          ∑ c : (ZMod (s ^ 2))ˣ, ∑ d : (ZMod (s ^ 2))ˣ,
          (if CondRed b₁ b₂ g X (red s (a : ZMod (s ^ 2)))
            (red s (b : ZMod (s ^ 2))) (red s (c : ZMod (s ^ 2))) (red s (d : ZMod (s ^ 2)))
            then (1 : ℝ) else 0)) (fun X => by positivity)).trans ?_
        gcongr with X
        refine (sum_units_red_le (fun A => ∑ b : (ZMod (s ^ 2))ˣ,
          ∑ c : (ZMod (s ^ 2))ˣ, ∑ d : (ZMod (s ^ 2))ˣ,
          (if CondRed b₁ b₂ g X A
            (red s (b : ZMod (s ^ 2))) (red s (c : ZMod (s ^ 2))) (red s (d : ZMod (s ^ 2)))
            then (1 : ℝ) else 0)) (fun A => by positivity)).trans ?_
        gcongr with A
        refine (sum_units_red_le (fun B => ∑ c : (ZMod (s ^ 2))ˣ, ∑ d : (ZMod (s ^ 2))ˣ,
          (if CondRed b₁ b₂ g X A B (red s (c : ZMod (s ^ 2))) (red s (d : ZMod (s ^ 2)))
            then (1 : ℝ) else 0)) (fun B => by positivity)).trans ?_
        gcongr with B
        refine (sum_units_red_le (fun C => ∑ d : (ZMod (s ^ 2))ˣ,
          (if CondRed b₁ b₂ g X A B C (red s (d : ZMod (s ^ 2)))
            then (1 : ℝ) else 0)) (fun C => by positivity)).trans ?_
        gcongr with C
        exact sum_units_red_le (fun D => if CondRed b₁ b₂ g X A B C D then (1 : ℝ) else 0)
          (fun D => by positivity)
    _ = (s : ℝ) ^ 5 * ((univ.filter (fun p : ZMod s × ZMod s × ZMod s × ZMod s × ZMod s =>
          CondRed b₁ b₂ g p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        simp only [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun A _ =>
          Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun C _ =>
          Finset.sum_congr rfl fun D _ => ?_
        split_ifs <;> ring
    _ ≤ (s : ℝ) ^ 5 * 6 := by
        gcongr
        exact_mod_cast card_condRed_le b₁ b₂ g hb₁ hγ
    _ = 6 * (s : ℝ) ^ 5 := by ring

end PrimeSquare

end

end GaloisForLFunctions.RHTower.HyperKloostermanPrimeSquare
