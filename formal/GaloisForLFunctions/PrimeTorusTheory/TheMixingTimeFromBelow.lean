import GaloisForLFunctions.PrimeTorusTheory.TheBoxesOfTheTorus

/-!
# The mixing time from below

`exists_box_missed` finds a box of radius `π/2` that the orbit misses on `[0, T]` below `2^{π(y)}/θ(y)`. Smaller boxes are missed for longer.

**Dyadic codes.** The signs of `cos(2^a x)`, `a ≤ J`, locate `x` in a dyadic arc of length `π/2^{J+1}`, up to `x ↦ −x`. The arc centres `c_k = π(2k + 1)/2^{J+2}`, `k < 2^{J+1}`, have distinct sign vectors (`dyadic_code_injective`): the first sign says whether `k < 2^J`, and doubling with a reflection sends the remaining signs to level `J − 1`. Every point within `π/2^{J+3}` of `c_k` has the sign vector of `c_k` (`pos_cos_iff_of_near`), because `2^a c_k` stays at distance at least `2^a π/2^{J+2}` from the zeros of `cos`: their difference is `2^a π/2^{J+2}` times an odd integer (`le_abs_zero_sub_arc`).

**Theorem** (`exists_box_missed_dyadic`). On `[0, T]` the orbit visits at most `2 Σ_{p,a} (⌊T 2^a log p/π⌋ + 1) + 1` sign vectors of the steps `2^a log p` (`card_patterns_le`). Once this is below `2^{(J+1)π(y)}`, some arrangement of arc centres is never approached, so some box of radius `ρ = π/2^{J+3}` is missed on `[0, T]`.

In closed form (`exists_box_missed_dyadic_of_lt`): a box of radius `ρ` is missed as soon as `2(2^{J+1} T θ(y)/π + (J+1)π(y)) + 1 < 2^{(J+1)π(y)}`. So `log T_mix ≥ (J + 1) π(y) log 2 − log(2^{J+3} θ(y)/π) + o(1)`, that is `π(y) log(π/(4ρ))` up to lower order. For the box `bump > 1 − δ` the radius is `ρ = arccos(1 − 2δ) ≍ √δ`, so `log T_mix ≳ ½ π(y) log(1/δ)`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The centre `π(2k + 1)/2^{J+2}` of the `k`-th dyadic arc at level `J`. -/
def arcCentre (J k : ℕ) : ℝ := Real.pi * (2 * k + 1) / 2 ^ (J + 2)

/-- The sign of `cos(2^a x)`. -/
def dyadicSign (a : ℕ) (x : ℝ) : Prop := 0 < Real.cos (2 ^ a * x)

/-- At the first level the sign reads off the half: for `k < 2^{e+1}`, `0 < cos(π(2k+1)/2^{e+2})` iff `k < 2^e`. -/
theorem cos_arc_pos_iff {e k : ℕ} (hk : k < 2 ^ (e + 1)) :
    0 < Real.cos (Real.pi * (2 * k + 1) / 2 ^ (e + 2)) ↔ k < 2 ^ e := by
  have hpi := Real.pi_pos
  have h2 : (0 : ℝ) < 2 ^ (e + 2) := by positivity
  have hpow : (2 : ℝ) ^ (e + 2) = 2 ^ (e + 1) * 2 := pow_succ _ _
  have hk' : 2 * (k : ℝ) + 1 < 2 ^ (e + 2) := by
    have : 2 * k + 1 < 2 ^ (e + 2) := by rw [pow_succ]; omega
    exact_mod_cast this
  constructor
  · intro h
    by_contra hk2
    push Not at hk2
    have hk3 : (2 : ℝ) ^ (e + 1) ≤ 2 * (k : ℝ) + 1 := by
      have : 2 ^ (e + 1) ≤ 2 * k + 1 := by rw [pow_succ]; omega
      exact_mod_cast this
    have h4 : Real.pi / 2 ≤ Real.pi * (2 * k + 1) / 2 ^ (e + 2) := by
      rw [le_div_iff₀ h2, hpow]
      nlinarith
    have h5 : Real.pi * (2 * k + 1) / 2 ^ (e + 2) ≤ Real.pi + Real.pi / 2 := by
      rw [div_le_iff₀ h2]
      nlinarith
    exact absurd h (not_lt.mpr (Real.cos_nonpos_of_pi_div_two_le_of_le h4 h5))
  · intro hk2
    have hk3 : 2 * (k : ℝ) + 1 < 2 ^ (e + 1) := by
      have : 2 * k + 1 < 2 ^ (e + 1) := by rw [pow_succ]; omega
      exact_mod_cast this
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · have : 0 < Real.pi * (2 * k + 1) / 2 ^ (e + 2) := by positivity
      linarith
    · rw [div_lt_iff₀ h2, hpow]
      nlinarith

/-- Doubling moves one level down: `2^{a+1} c_k` at level `J + 1` is `2^a c_k` at level `J`. -/
theorem dyadicSign_succ (a J k : ℕ) :
    dyadicSign (a + 1) (arcCentre (J + 1) k) ↔ dyadicSign a (arcCentre J k) := by
  unfold dyadicSign arcCentre
  rw [show (2 : ℝ) ^ (a + 1) * (Real.pi * (2 * k + 1) / 2 ^ (J + 1 + 2)) =
      2 ^ a * (Real.pi * (2 * k + 1) / 2 ^ (J + 2)) by
    rw [pow_succ, show J + 1 + 2 = J + 2 + 1 by ring, pow_succ]
    field_simp]

/-- The reflection `x ↦ 2π − x` does not change the signs. -/
theorem dyadicSign_reflect {J k k' : ℕ} (h : k + k' + 1 = 2 ^ (J + 2)) (a : ℕ) :
    dyadicSign a (arcCentre J k) ↔ dyadicSign a (arcCentre J k') := by
  unfold dyadicSign
  have hs : (k : ℝ) + k' + 1 = 2 ^ (J + 2) := by exact_mod_cast h
  have e : (2 : ℝ) ^ a * arcCentre J k =
      -(2 ^ a * arcCentre J k') + (((2 ^ a : ℕ) : ℤ) : ℝ) * (2 * Real.pi) := by
    have h0 : (2 : ℝ) ^ a * arcCentre J k -
        (-(2 ^ a * arcCentre J k') + (((2 ^ a : ℕ) : ℤ) : ℝ) * (2 * Real.pi)) =
        (2 ^ a * Real.pi * 2 / 2 ^ (J + 2)) * ((k : ℝ) + k' + 1 - 2 ^ (J + 2)) := by
      unfold arcCentre
      push_cast
      field_simp
      ring
    rw [hs, sub_self, mul_zero, sub_eq_zero] at h0
    exact h0
  rw [e, Real.cos_add_int_mul_two_pi, Real.cos_neg]

/-- **The dyadic code is injective.** Distinct arc centres `k, k' < 2^{J+1}` have distinct sign vectors. -/
theorem dyadic_code_injective : ∀ (J : ℕ) {k k' : ℕ}, k < 2 ^ (J + 1) → k' < 2 ^ (J + 1) →
    (∀ a ≤ J, (dyadicSign a (arcCentre J k) ↔ dyadicSign a (arcCentre J k'))) → k = k'
  | 0, k, k', hk, hk', h => by
      have h0 := h 0 le_rfl
      unfold dyadicSign arcCentre at h0
      simp only [pow_zero, one_mul] at h0
      rw [cos_arc_pos_iff (e := 0) hk, cos_arc_pos_iff (e := 0) hk'] at h0
      norm_num at h0 hk hk'
      omega
  | J + 1, k, k', hk, hk', h => by
      have h0 := h 0 (Nat.zero_le _)
      unfold dyadicSign arcCentre at h0
      simp only [pow_zero, one_mul] at h0
      rw [cos_arc_pos_iff (e := J + 1) hk, cos_arc_pos_iff (e := J + 1) hk'] at h0
      have hp : 2 ^ (J + 2) = 2 * 2 ^ (J + 1) := by rw [pow_succ]; ring
      set f : ℕ → ℕ := fun k => if k < 2 ^ (J + 1) then k else 2 ^ (J + 2) - 1 - k with hf
      have hfl : ∀ k, k < 2 ^ (J + 2) → f k < 2 ^ (J + 1) := fun k hk => by
        simp only [hf]
        split_ifs <;> omega
      have hstep : ∀ k, k < 2 ^ (J + 2) → ∀ a,
          (dyadicSign (a + 1) (arcCentre (J + 1) k) ↔ dyadicSign a (arcCentre J (f k))) := by
        intro k hk a
        rw [dyadicSign_succ]
        simp only [hf]
        split_ifs with h1
        · exact Iff.rfl
        · exact dyadicSign_reflect (by omega) a
      have hk2 : k < 2 ^ (J + 2) := by rw [show J + 1 + 1 = J + 2 by ring] at hk; exact hk
      have hk2' : k' < 2 ^ (J + 2) := by rw [show J + 1 + 1 = J + 2 by ring] at hk'; exact hk'
      have := dyadic_code_injective J (hfl k hk2) (hfl k' hk2') fun a ha => by
        rw [← hstep k hk2 a, ← hstep k' hk2' a]
        exact h (a + 1) (by omega)
      simp only [hf] at this
      split_ifs at this <;> omega

/-- The zeros of `cos` stay away from the scaled centres: `|(2n+1)π/2 − 2^a c_k| ≥ 2^a π/2^{J+2}` for `a ≤ J`. -/
theorem le_abs_zero_sub_arc {J a : ℕ} (ha : a ≤ J) (k : ℕ) (n : ℤ) :
    2 ^ a * Real.pi / 2 ^ (J + 2) ≤ |(2 * n + 1) * Real.pi / 2 - 2 ^ a * arcCentre J k| := by
  set d : ℕ := J + 1 - a with hd
  have hd1 : 1 ≤ d := by omega
  have hJ : J + 2 = a + d + 1 := by omega
  set N : ℤ := (2 * n + 1) * 2 ^ d - (2 * k + 1) with hN
  have hN0 : N ≠ 0 := by
    have hpow2 : (2 : ℤ) ^ d = 2 * 2 ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hQ : (2 * n + 1) * (2 : ℤ) ^ d = 2 * ((2 * n + 1) * 2 ^ (d - 1)) := by
      rw [hpow2]
      ring
    set Q : ℤ := (2 * n + 1) * 2 ^ (d - 1)
    omega
  have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
  have hpow : (2 : ℝ) ^ (J + 2) = 2 ^ a * 2 ^ d * 2 := by rw [hJ, pow_succ, pow_add]
  have he : (2 * n + 1) * Real.pi / 2 - 2 ^ a * arcCentre J k = (2 ^ a * Real.pi / 2 ^ (J + 2)) * N := by
    unfold arcCentre
    rw [hN, hpow]
    push_cast
    field_simp
  rw [he, abs_mul, abs_of_pos (by positivity)]
  have h0 : 0 < 2 ^ a * Real.pi / 2 ^ (J + 2) := by positivity
  nlinarith

/-- If `cos` has no zero between `u` and `v`, it has the same sign at both. -/
theorem pos_cos_iff_of_no_zero {u v : ℝ} (h : ∀ w ∈ Set.uIcc u v, Real.cos w ≠ 0) :
    0 < Real.cos u ↔ 0 < Real.cos v := by
  have hc : ContinuousOn Real.cos (Set.uIcc u v) := Real.continuous_cos.continuousOn
  constructor
  · intro hu
    by_contra hv
    push Not at hv
    obtain ⟨w, hw, hw0⟩ := intermediate_value_uIcc hc
      (show (0 : ℝ) ∈ Set.uIcc (Real.cos u) (Real.cos v) from Set.mem_uIcc.mpr (Or.inr ⟨hv, hu.le⟩))
    exact h w hw hw0
  · intro hv
    by_contra hu
    push Not at hu
    obtain ⟨w, hw, hw0⟩ := intermediate_value_uIcc hc
      (show (0 : ℝ) ∈ Set.uIcc (Real.cos u) (Real.cos v) from Set.mem_uIcc.mpr (Or.inl ⟨hu, hv.le⟩))
    exact h w hw hw0

/-- **Near a centre the signs are those of the centre.** -/
theorem pos_cos_iff_of_near {J a k : ℕ} (ha : a ≤ J) {z : ℝ} {m : ℤ}
    (hz : |z - arcCentre J k - m * (2 * Real.pi)| < Real.pi / 2 ^ (J + 3)) :
    0 < Real.cos (2 ^ a * z) ↔ dyadicSign a (arcCentre J k) := by
  set ε : ℝ := z - arcCentre J k - m * (2 * Real.pi) with hε
  have e1 : (2 : ℝ) ^ a * z = (2 ^ a * arcCentre J k + 2 ^ a * ε) + (((2 ^ a : ℕ) * m : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hε]
    push_cast
    ring
  rw [e1, Real.cos_add_int_mul_two_pi]
  unfold dyadicSign
  refine pos_cos_iff_of_no_zero fun w hw hw0 => ?_
  obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp hw0
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  -- `w` is within `2^a |ε|` of `2^a c_k`.
  have h1 : |w - 2 ^ a * arcCentre J k| ≤ 2 ^ a * |ε| := by
    have h3 := Set.abs_sub_right_of_mem_uIcc hw
    rw [abs_sub_comm] at h3
    have e : 2 ^ a * arcCentre J k - (2 ^ a * arcCentre J k + 2 ^ a * ε) = -(2 ^ a * ε) := by ring
    rw [e, abs_neg, abs_mul, abs_of_pos h2a] at h3
    exact h3
  have h2 := le_abs_zero_sub_arc ha k n
  rw [hn] at h1
  have h3 : 2 ^ a * |ε| < 2 ^ a * Real.pi / 2 ^ (J + 2) := by
    have h4 : 2 ^ a * |ε| < 2 ^ a * (Real.pi / 2 ^ (J + 3)) := mul_lt_mul_of_pos_left hz h2a
    have h5 : (2 : ℝ) ^ a * (Real.pi / 2 ^ (J + 3)) ≤ 2 ^ a * Real.pi / 2 ^ (J + 2) := by
      have h6 : Real.pi / 2 ^ (J + 3) ≤ Real.pi / 2 ^ (J + 2) :=
        div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      calc (2 : ℝ) ^ a * (Real.pi / 2 ^ (J + 3)) ≤ 2 ^ a * (Real.pi / 2 ^ (J + 2)) :=
            mul_le_mul_of_nonneg_left h6 h2a.le
        _ = 2 ^ a * Real.pi / 2 ^ (J + 2) := by ring
    linarith
  linarith

/-- If `cos x > cos ρ` with `0 ≤ ρ`, then `x` is within `ρ` of `2πℤ`. -/
theorem exists_int_near_of_cos_lt {x ρ : ℝ} (hρ0 : 0 ≤ ρ) (h : Real.cos ρ < Real.cos x) : ∃ m : ℤ, |x - m * (2 * Real.pi)| < ρ := by
  have hpi := Real.pi_pos
  set m : ℤ := ⌊(x + Real.pi) / (2 * Real.pi)⌋ with hm
  refine ⟨m, ?_⟩
  have h2π : 0 < 2 * Real.pi := by positivity
  have hm1 : (m : ℝ) ≤ (x + Real.pi) / (2 * Real.pi) := Int.floor_le _
  have hm2 : (x + Real.pi) / (2 * Real.pi) < m + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ h2π] at hm1
  rw [div_lt_iff₀ h2π] at hm2
  have hx1 : -Real.pi ≤ x - m * (2 * Real.pi) := by nlinarith
  have hx2 : x - m * (2 * Real.pi) < Real.pi := by nlinarith
  have hcos : Real.cos |x - m * (2 * Real.pi)| = Real.cos x := by
    rw [Real.cos_abs, show x - m * (2 * Real.pi) = x + ((-m : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring,
      Real.cos_add_int_mul_two_pi]
  by_contra hge
  push Not at hge
  have h1 : Real.cos |x - m * (2 * Real.pi)| ≤ Real.cos ρ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hρ0 (abs_le.mpr ⟨by linarith, hx2.le⟩) hge
  linarith

open Classical in
/-- **Small boxes are missed below the mixing time.** As soon as the orbit visits fewer than `2^{(J+1)π(y)}` sign vectors of the steps `2^a log p`, `a ≤ J`, some box of radius `π/2^{J+3}` on the primes up to `y` is not entered on `[0, T]`. -/
theorem exists_box_missed_dyadic {y J : ℕ} {T : ℝ}
    (hlt : 2 * ∑ i : primesUpTo y × Fin (J + 1),
        (⌊T * (2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ)) / Real.pi⌋₊ + 1) + 1 <
      (2 ^ (J + 1)) ^ (primesUpTo y).card) :
    ∃ θ : ℕ → ℝ, ∀ t ∈ Set.Icc 0 T, ∃ p ∈ primesUpTo y,
      Real.cos (t * Real.log p - θ p) ≤ Real.cos (Real.pi / 2 ^ (J + 3)) := by
  set Y := primesUpTo y with hY
  set ℓ : Y × Fin (J + 1) → ℝ := fun i => 2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ) with hℓ
  have hℓ0 : ∀ i, 0 < ℓ i := fun i => mul_pos (by positivity)
    (Real.log_pos (by exact_mod_cast (prime_of_mem_primesUpTo i.1.2).one_lt))
  set Q : (Y → Fin (2 ^ (J + 1))) → (Y × Fin (J + 1) → Prop) :=
    fun κ i => dyadicSign i.2 (arcCentre J (κ i.1)) with hQ
  have hQi : Function.Injective Q := by
    intro κ κ' h
    funext p
    apply Fin.ext
    refine dyadic_code_injective J (κ p).2 (κ' p).2 fun a ha => ?_
    exact Iff.of_eq (congrFun h (p, ⟨a, by omega⟩))
  set θ : (Y → Fin (2 ^ (J + 1))) → ℕ → ℝ :=
    fun κ p => if h : p ∈ Y then arcCentre J (κ ⟨p, h⟩) else 0 with hθ
  by_contra hcon
  push Not at hcon
  choose! τ hτ1 hτ2 using fun κ => hcon (θ κ)
  -- The sign vector at `τ κ` is the code of `κ`.
  have hpat : ∀ κ, pattern ℓ (τ κ) = Q κ := by
    intro κ
    funext i
    apply propext
    obtain ⟨p, a⟩ := i
    have h1 := hτ2 κ p p.2
    simp only [hθ, dif_pos p.2, Subtype.coe_eta] at h1
    obtain ⟨m, hm⟩ := exists_int_near_of_cos_lt (by positivity) h1
    show 0 < Real.cos (τ κ * (2 ^ (a : ℕ) * Real.log p)) ↔ dyadicSign a (arcCentre J (κ p))
    rw [show τ κ * (2 ^ (a : ℕ) * Real.log p) = 2 ^ (a : ℕ) * (τ κ * Real.log p) by ring]
    exact pos_cos_iff_of_near (by omega) hm
  set A : Finset ℝ := (Finset.univ : Finset (Y → Fin (2 ^ (J + 1)))).image τ with hA
  have hAT : ∀ t ∈ A, t ∈ Set.Icc 0 T := by
    intro t ht
    obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp ht
    exact hτ1 κ
  have hle : (A.image (pattern ℓ)).card ≤ 2 * ∑ i : Y × Fin (J + 1),
      (⌊T * (2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ)) / Real.pi⌋₊ + 1) + 1 := card_patterns_le hℓ0 A hAT
  have hsub : (Finset.univ : Finset (Y → Fin (2 ^ (J + 1)))).image Q ⊆ A.image (pattern ℓ) := by
    intro P hP
    obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_image.mpr ⟨τ κ, Finset.mem_image_of_mem _ (Finset.mem_univ _), hpat κ⟩
  have hcard : ((Finset.univ : Finset (Y → Fin (2 ^ (J + 1)))).image Q).card = (2 ^ (J + 1)) ^ Y.card := by
    rw [Finset.card_image_of_injective _ hQi, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe]
  have h1 := Finset.card_le_card hsub
  omega

/-- The count in closed form: `Σ_{p,a} (⌊T 2^a log p/π⌋ + 1) ≤ 2^{J+1} T θ(y)/π + (J + 1)π(y)`. -/
theorem sum_dyadic_floor_le {y J : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    ((∑ i : primesUpTo y × Fin (J + 1),
        (⌊T * (2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ)) / Real.pi⌋₊ + 1) : ℕ) : ℝ) ≤
      2 ^ (J + 1) * T * (∑ p ∈ primesUpTo y, Real.log p) / Real.pi + (J + 1) * (primesUpTo y).card := by
  have hpi := Real.pi_pos
  push_cast
  have h1 : ∀ i : primesUpTo y × Fin (J + 1),
      ((⌊T * (2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ)) / Real.pi⌋₊ : ℕ) : ℝ) + 1 ≤
        T * (2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ)) / Real.pi + 1 := fun i => by
    have h2 : 0 ≤ T * (2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ)) / Real.pi :=
      div_nonneg (mul_nonneg hT (mul_nonneg (by positivity) (Real.log_natCast_nonneg _))) hpi.le
    linarith [Nat.floor_le h2]
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Fintype.sum_prod_type]
  have hgeom : ∀ p : primesUpTo y, ∑ a : Fin (J + 1), T * (2 ^ (a : ℕ) * Real.log (p : ℕ)) / Real.pi ≤
      2 ^ (J + 1) * T * Real.log (p : ℕ) / Real.pi := fun p => by
    have hs : ∑ a : Fin (J + 1), (2 : ℝ) ^ (a : ℕ) ≤ 2 ^ (J + 1) := by
      rw [Fin.sum_univ_eq_sum_range (fun a => (2 : ℝ) ^ a) (J + 1), geom_sum_eq (by norm_num)]
      norm_num
    have hl : 0 ≤ T * Real.log (p : ℕ) / Real.pi :=
      div_nonneg (mul_nonneg hT (Real.log_natCast_nonneg _)) hpi.le
    calc ∑ a : Fin (J + 1), T * (2 ^ (a : ℕ) * Real.log (p : ℕ)) / Real.pi
        = (∑ a : Fin (J + 1), (2 : ℝ) ^ (a : ℕ)) * (T * Real.log (p : ℕ) / Real.pi) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ ≤ 2 ^ (J + 1) * (T * Real.log (p : ℕ) / Real.pi) := mul_le_mul_of_nonneg_right hs hl
      _ = 2 ^ (J + 1) * T * Real.log (p : ℕ) / Real.pi := by ring
  have h3 := Finset.sum_le_sum fun p (_ : p ∈ (Finset.univ : Finset (primesUpTo y))) => hgeom p
  have h4 : ∑ p : primesUpTo y, 2 ^ (J + 1) * T * Real.log (p : ℕ) / Real.pi =
      2 ^ (J + 1) * T * (∑ p ∈ primesUpTo y, Real.log p) / Real.pi := by
    rw [Finset.sum_coe_sort (primesUpTo y) (fun p => 2 ^ (J + 1) * T * Real.log p / Real.pi),
      ← Finset.sum_div, ← Finset.mul_sum]
  rw [h4] at h3
  push_cast
  linarith

/-- **The mixing time from below, in closed form.** If `2(2^{J+1} T θ(y)/π + (J + 1)π(y)) + 1 < 2^{(J+1)π(y)}`, some box of radius `π/2^{J+3}` on the primes up to `y` is not entered on `[0, T]`. -/
theorem exists_box_missed_dyadic_of_lt {y J : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hlt : 2 * (2 ^ (J + 1) * T * (∑ p ∈ primesUpTo y, Real.log p) / Real.pi +
        (J + 1) * (primesUpTo y).card) + 1 < (2 : ℝ) ^ ((J + 1) * (primesUpTo y).card)) :
    ∃ θ : ℕ → ℝ, ∀ t ∈ Set.Icc 0 T, ∃ p ∈ primesUpTo y,
      Real.cos (t * Real.log p - θ p) ≤ Real.cos (Real.pi / 2 ^ (J + 3)) := by
  refine exists_box_missed_dyadic ?_
  have h1 := sum_dyadic_floor_le (y := y) (J := J) hT
  have h2 : ((2 * ∑ i : primesUpTo y × Fin (J + 1),
      (⌊T * (2 ^ (i.2 : ℕ) * Real.log (i.1 : ℕ)) / Real.pi⌋₊ + 1) + 1 : ℕ) : ℝ) <
      (((2 ^ (J + 1)) ^ (primesUpTo y).card : ℕ) : ℝ) := by
    push_cast at h1 ⊢
    rw [← pow_mul]
    linarith
  exact_mod_cast h2

end

end GaloisForLFunctions.PrimeTorusTheory
