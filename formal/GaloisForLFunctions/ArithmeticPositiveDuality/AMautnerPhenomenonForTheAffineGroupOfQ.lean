import GaloisForLFunctions.ArithmeticPositiveDuality.TheBostConnesTemperatureIsTheHeckeExponent
import GaloisForLFunctions.ArithmeticPositiveDuality.TheExtremalsOfTheHeckeLawAreTwistedHaarStates

/-!
# A Mautner phenomenon for the affine group of `ℚ`

Every successor state that sees the integers forces `p`-adic decay on the dilations: the integer
successor forces `(nd)^{−1/2}` (`normSq_dilation_le`), the Bost–Connes successors `(nd)^{−β/2}`
(`bc_successor_hecke_exponent`). This file shows that no `ℤ`-periodic successor is compatible with
an archimedean dilation part, except the trivial one.

* **Monotone densities** (`successorDensity_mul_le`). For a `ℤ`-periodic successor the density
  `A(q)` is the single average `q⁻¹Σ_{r<q}ψ(r/q)` (`successorDensity_eq_single`), and
  `A(kq) ≤ A(q)`: the averages `X_q`, `X_{kq}` satisfy `⟨X_q, X_{kq}⟩ = ⟨X_{kq}, X_{kq}⟩`, so the
  Gram form of `X_q − X_{kq}` is `A(q) − A(kq)`.
* **Mautner rigidity** (`translation_eq_of_continuousAt_dilation`). If `φ` is positive definite on
  `Aff(ℚ)`, its successor is `ℤ`-periodic and its dilation part on `ℚ_{>0}` is continuous at `1`,
  then `φ(x ↦ x + b) = φ(1)` for every `b ∈ ℚ`. Along `u = (kq+1)/(kq) → 1` the successor law gives
  `φ(1)² ≤ φ(1)·A(kq) ≤ φ(1)·A(q)`, so `A(q) = φ(1)` and the successor is constant on `(1/q)ℤ`.

In the GNS picture: a `ℤ`-invariant vector whose dilation orbit is continuous at the identity is
`ℚ`-invariant. The arithmetic of `ℤ ⊂ ℚ` is invisible to any archimedean dilation structure; a
successor-prescribed carrier for Weil's correlation must be adelic, not `ℤ`-periodic.
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

section Group

variable {G : Type*} [Group G] {φ : G → ℂ}

/-- A positive-definite function is bounded by its value at the identity:
`|φ(g)|² ≤ φ(1)²`. -/
theorem IsPosDefOnGroup.normSq_le (hφ : IsPosDefOnGroup φ) (g : G) :
    Complex.normSq (φ g) ≤ (φ 1).re ^ 2 := by
  obtain ⟨r0, hr0, h0⟩ := hφ.map_one_eq
  rw [h0, Complex.ofReal_re]
  have hFF : φ g * star (φ g) = (Complex.normSq (φ g) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  rcases hr0.lt_or_eq with hpos | hzero
  · obtain ⟨r, hr, h⟩ := hφ.two_point 1 g (r0 : ℂ) (-star (φ g))
    rw [inv_one, one_mul, mul_one, hφ.map_inv, h0, star_neg, star_star,
      show star (r0 : ℂ) = r0 from Complex.conj_ofReal r0] at h
    have e : ((r0 ^ 3 - r0 * Complex.normSq (φ g) : ℝ) : ℂ) = r := by
      rw [← h]; push_cast; linear_combination (r0 : ℂ) * hFF
    have h' := Complex.ofReal_injective e
    have h3 : 0 ≤ r0 * (r0 ^ 2 - Complex.normSq (φ g)) := by nlinarith
    have := (mul_nonneg_iff_of_pos_left hpos).mp h3
    linarith
  · subst hzero
    have hz : φ g = 0 := by
      refine eq_zero_of_forall_quadratic' le_rfl fun t => ?_
      obtain ⟨r, hr, h⟩ := hφ.two_point 1 g t 1
      refine ⟨r, hr, ?_⟩
      rw [← h]
      simp only [inv_one, one_mul, mul_one, hφ.map_inv, h0, star_one, Complex.ofReal_zero,
        mul_zero, zero_mul, add_zero]
    rw [hz, Complex.normSq_zero]; simp

end Group

/-- Successor densities are Gram values, hence real and nonnegative. -/
theorem successorDensity_eq_ofReal {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (q : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ successorDensity φ q = r := by
  obtain ⟨r, hr, h⟩ := hφ.form (fun a : Fin q => translation (((a : ℕ) : ℚ) / q))
    (fun _ => 1 / (q : ℂ))
  refine ⟨r, hr, ?_⟩
  rw [← h]
  unfold successorDensity
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [translation_inv_mul, star_div₀, star_one, star_natCast,
    show (((a' : ℕ) : ℚ) / q - ((a : ℕ) : ℚ) / q) = (((a' : ℕ) : ℚ) - (a : ℕ)) / q by ring]
  ring

/-! ### Successor densities of an integer-periodic successor -/

section Densities

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
  (hper : ∀ m : ℤ, φ (translation m) = φ 1)
include hφ hper

/-- An integer-periodic successor is periodic: `φ(x + b + m) = φ(x + b)`. -/
theorem translation_add_int (b : ℚ) (m : ℤ) :
    φ (translation (b + m)) = φ (translation b) := by
  have e : translation (b + m) = translation b * translation m := by
    refine affine_ext ?_ ?_
    · rw [affSlope_mul, affSlope_translation, affSlope_translation, one_mul, affSlope_translation]
    · rw [affShift_mul, affSlope_translation, affShift_translation, affShift_translation,
        affShift_translation]; ring
  rw [e, hφ.mul_right_eq (hper m)]

/-- Shifting the summation index: `Σ_{k<q} φ(x + (k − j)/q) = Σ_{r<q} φ(x + r/q)`. -/
theorem sum_translation_shift (q : ℕ) (hq : 0 < q) (j : Fin q) :
    ∑ k : Fin q, φ (translation ((((k : ℕ) : ℚ) - (j : ℕ)) / q)) =
      ∑ r : Fin q, φ (translation (((r : ℕ) : ℚ) / q)) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  refine Fintype.sum_equiv (Equiv.subRight j) _ _ fun k => ?_
  simp only [Equiv.subRight_apply]
  have hj : (j : ℕ) ≤ q := j.2.le
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ((k - j : Fin q) : ℕ) + q * D = (k : ℕ) + (q - (j : ℕ)) := by
    refine ⟨((q - (j : ℕ)) + k) / q, ?_⟩
    rw [Fin.val_sub]
    have := Nat.mod_add_div ((q - (j : ℕ)) + k) q
    omega
  have h1 : ((((k - j : Fin q) : ℕ) : ℚ)) + q * D = (k : ℕ) + ((q : ℚ) - (j : ℕ)) := by
    rw [← Nat.cast_sub hj]; exact_mod_cast hD
  have key : (((k : ℕ) : ℚ) - (j : ℕ)) / q =
      (((k - j : Fin q) : ℕ) : ℚ) / q + (((D : ℤ) - 1 : ℤ) : ℚ) := by
    have e : (((k : ℕ) : ℚ) - (j : ℕ)) = (((k - j : Fin q) : ℕ) : ℚ) + (((D : ℤ) - 1 : ℤ) : ℚ) * q := by
      push_cast; linear_combination -h1
    rw [e, add_div, mul_div_cancel_right₀ _ hqQ]
  rw [key, translation_add_int hφ hper]

/-- For an integer-periodic successor the density is the single average `q⁻¹Σ_{r<q}φ(x + r/q)`. -/
theorem successorDensity_eq_single (q : ℕ) (hq : 0 < q) :
    successorDensity φ q = (1 / (q : ℂ)) * ∑ r : Fin q, φ (translation (((r : ℕ) : ℚ) / q)) := by
  unfold successorDensity
  simp_rw [sum_translation_shift hφ hper q hq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- **Densities decrease along multiples**: `A(kq) ≤ A(q)`. The Gram form of
`q⁻¹Σ_{b<q}[x + b/q] − (kq)⁻¹Σ_{a<kq}[x + a/(kq)]` equals `A(q) − A(kq)`. -/
theorem successorDensity_mul_le (q k : ℕ) (hq : 0 < q) (hk : 0 < k) :
    (successorDensity φ (k * q)).re ≤ (successorDensity φ q).re := by
  have hkq : 0 < k * q := Nat.mul_pos hk hq
  set N := k * q with hN
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hkq.ne'
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hkq.ne'
  set P : Fin q ⊕ Fin N → AffineGroupQ :=
    Sum.elim (fun b => translation (((b : ℕ) : ℚ) / q))
      (fun a => translation (((a : ℕ) : ℚ) / N)) with hP
  set C : Fin q ⊕ Fin N → ℂ := Sum.elim (fun _ => 1 / (q : ℂ)) (fun _ => -(1 / (N : ℂ))) with hC
  obtain ⟨r, hr, hsum⟩ := hφ.form P C
  -- the cross block reduces to the single average at level `kq`
  have hcross : ∑ b : Fin q, ∑ a : Fin N, φ ((P (Sum.inl b))⁻¹ * P (Sum.inr a)) =
      (q : ℂ) * ∑ r : Fin N, φ (translation (((r : ℕ) : ℚ) / N)) := by
    have hb : ∀ b : Fin q, ∑ a : Fin N, φ ((P (Sum.inl b))⁻¹ * P (Sum.inr a)) =
        ∑ r : Fin N, φ (translation (((r : ℕ) : ℚ) / N)) := by
      intro b
      have hlt : k * (b : ℕ) < N := by rw [hN]; exact Nat.mul_lt_mul_of_pos_left b.2 hk
      rw [← sum_translation_shift hφ hper N hkq ⟨k * (b : ℕ), hlt⟩]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hP, Sum.elim_inl, Sum.elim_inr, translation_inv_mul]
      congr 2
      have hNq : (N : ℚ) = (k : ℚ) * q := by rw [hN]; push_cast; ring
      rw [hNq]; push_cast; field_simp
    rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hcross' : ∑ a : Fin N, ∑ b : Fin q, φ ((P (Sum.inr a))⁻¹ * P (Sum.inl b)) =
      star ((q : ℂ) * ∑ r : Fin N, φ (translation (((r : ℕ) : ℚ) / N))) := by
    rw [← hcross, star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hφ.map_inv, mul_inv_rev, inv_inv]
  have hsN := successorDensity_eq_single hφ hper N hkq
  -- reality of the level-`kq` density
  obtain ⟨rN, hrN, hNreal⟩ := successorDensity_eq_ofReal hφ N
  -- evaluate the Gram form
  have hval : ∑ x, ∑ y, star (C x) * φ ((P x)⁻¹ * P y) * C y =
      successorDensity φ q - successorDensity φ N := by
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_sum_type, hC, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
    have hs1 : star (1 / (q : ℂ)) = 1 / q := by rw [star_div₀, star_one, star_natCast]
    have hs2 : star (-(1 / (N : ℂ))) = -(1 / N) := by
      rw [star_neg, star_div₀, star_one, star_natCast]
    rw [hs1, hs2]
    have eXX : ∑ b : Fin q, ∑ b' : Fin q, 1 / (q : ℂ) * φ ((P (Sum.inl b))⁻¹ * P (Sum.inl b')) *
        (1 / q) = successorDensity φ q := by
      unfold successorDensity
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp only [hP, Sum.elim_inl, translation_inv_mul]
      rw [show (((b' : ℕ) : ℚ) / q - ((b : ℕ) : ℚ) / q) = (((b' : ℕ) : ℚ) - (b : ℕ)) / q by ring]
      field_simp
    have eZZ : ∑ a : Fin N, ∑ a' : Fin N, -(1 / (N : ℂ)) * φ ((P (Sum.inr a))⁻¹ * P (Sum.inr a')) *
        -(1 / N) = successorDensity φ N := by
      unfold successorDensity
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      simp only [hP, Sum.elim_inr, translation_inv_mul]
      rw [show (((a' : ℕ) : ℚ) / N - ((a : ℕ) : ℚ) / N) = (((a' : ℕ) : ℚ) - (a : ℕ)) / N by ring]
      field_simp
    have eXZ : ∑ b : Fin q, ∑ a : Fin N, 1 / (q : ℂ) * φ ((P (Sum.inl b))⁻¹ * P (Sum.inr a)) *
        -(1 / N) = -successorDensity φ N := by
      have : ∑ b : Fin q, ∑ a : Fin N, 1 / (q : ℂ) * φ ((P (Sum.inl b))⁻¹ * P (Sum.inr a)) *
          -(1 / N) = -(1 / ((q : ℂ) * N)) * ∑ b : Fin q, ∑ a : Fin N,
            φ ((P (Sum.inl b))⁻¹ * P (Sum.inr a)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        field_simp
      rw [this, hcross, hsN]
      field_simp
    have eZX : ∑ a : Fin N, ∑ b : Fin q, -(1 / (N : ℂ)) * φ ((P (Sum.inr a))⁻¹ * P (Sum.inl b)) *
        (1 / q) = -successorDensity φ N := by
      have : ∑ a : Fin N, ∑ b : Fin q, -(1 / (N : ℂ)) * φ ((P (Sum.inr a))⁻¹ * P (Sum.inl b)) *
          (1 / q) = -(1 / ((q : ℂ) * N)) * ∑ a : Fin N, ∑ b : Fin q,
            φ ((P (Sum.inr a))⁻¹ * P (Sum.inl b)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        field_simp
      rw [this, hcross', star_mul', star_natCast]
      have hstarN : star (∑ r : Fin N, φ (translation (((r : ℕ) : ℚ) / N))) =
          ∑ r : Fin N, φ (translation (((r : ℕ) : ℚ) / N)) := by
        have h1 : (∑ r : Fin N, φ (translation (((r : ℕ) : ℚ) / N))) = (N : ℂ) * rN := by
          rw [← hNreal, hsN]; field_simp
        rw [h1, star_mul', star_natCast, show star (rN : ℂ) = rN from Complex.conj_ofReal rN]
      rw [hstarN, hsN]
      field_simp
    rw [eXX, eXZ, eZX, eZZ]
    ring
  rw [hval] at hsum
  have := congrArg Complex.re hsum
  rw [Complex.sub_re, Complex.ofReal_re] at this
  linarith

/-- The density never exceeds `φ(1)`. -/
theorem successorDensity_le_one (q : ℕ) (hq : 0 < q) :
    (successorDensity φ q).re ≤ (φ 1).re := by
  have hk := successorDensity_mul_le hφ hper 1 q one_pos hq
  have h1 : successorDensity φ 1 = φ 1 := by
    simp [successorDensity, translation_zero]
  rw [mul_one, h1] at hk
  exact hk

end Densities

/-! ### Mautner rigidity -/

theorem natAbs_num_den_succ_div (q k : ℕ) (hq : 0 < q) (hk : 0 < k) :
    ((((k * q + 1 : ℕ) : ℚ) / ((k * q : ℕ) : ℚ)).num.natAbs = k * q + 1) ∧
      ((((k * q + 1 : ℕ) : ℚ) / ((k * q : ℕ) : ℚ)).den = k * q) := by
  have hpos : (0 : ℤ) < ((k * q : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos hk hq
  have hcop : Nat.Coprime ((k * q + 1 : ℕ) : ℤ).natAbs ((k * q : ℕ) : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    rw [show k * q + 1 = 1 + k * q by ring]
    exact Nat.coprime_add_self_left.mpr (Nat.coprime_one_left _)
  have hnum := Rat.num_div_eq_of_coprime hpos hcop
  have hden := Rat.den_div_eq_of_coprime hpos hcop
  push_cast at hnum hden
  refine ⟨?_, ?_⟩
  · push_cast; rw [hnum]; rfl
  · push_cast; exact_mod_cast hden

/-- **Mautner rigidity for `Aff(ℚ)`.** A positive-definite function with integer-periodic successor
and dilation part continuous at `1` has constant successor: `φ(x ↦ x + b) = φ(1)` for all `b`. -/
theorem translation_eq_of_continuousAt_dilation {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hper : ∀ m : ℤ, φ (translation m) = φ 1) {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hfφ : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = f (u : ℚ)) (b : ℚ) :
    φ (translation b) = φ 1 := by
  obtain ⟨r0, hr0, h0⟩ := hφ.map_one_eq
  -- bound `‖φ(g)‖ ≤ φ(1)`
  have hnorm : ∀ g, ‖φ g‖ ≤ r0 := fun g => by
    have h := hφ.normSq_le g
    rw [h0, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (φ g)]
  rcases hr0.lt_or_eq with hpos | hzero
  swap
  · have h1 := hnorm (translation b)
    rw [← hzero] at h1
    rw [norm_le_zero_iff.mp h1, h0, ← hzero, Complex.ofReal_zero]
  set q := b.den with hq_def
  have hq : 0 < q := b.den_pos
  have hf1 : f 1 = r0 := by
    have := hfφ 1 (by norm_num)
    rw [map_one, h0] at this
    simpa using this.symm
  have hA1 : ∀ q' : ℕ, 0 < q' → (successorDensity φ q').re ≤ r0 := fun q' hq' => by
    have := successorDensity_le_one hφ hper q' hq'
    rwa [h0, Complex.ofReal_re] at this
  have hA0 : ∀ q' : ℕ, 0 < q' → 0 ≤ (successorDensity φ q').re := fun q' hq' => by
    obtain ⟨r, hr, h⟩ := successorDensity_eq_ofReal hφ q'
    rw [h, Complex.ofReal_re]; exact hr
  -- the successor law along `u_k = (kq+1)/(kq)`
  have hbound : ∀ k : ℕ, 0 < k →
      Complex.normSq (f ((((k * q + 1 : ℕ) : ℚ) / ((k * q : ℕ) : ℚ) : ℚ) : ℝ)) ≤
        r0 * (successorDensity φ q).re := by
    intro k hk
    have hkq : 0 < k * q := Nat.mul_pos hk hq
    have hu0 : (((k * q + 1 : ℕ) : ℚ) / ((k * q : ℕ) : ℚ)) ≠ 0 := by positivity
    have hupos : 0 < (Units.mk0 _ hu0 : ℚˣ).val := by simp only [Units.val_mk0]; positivity
    have hlaw := normSq_dilation_le_successorDensity hφ hper (Units.mk0 _ hu0)
    obtain ⟨hn, hd⟩ := natAbs_num_den_succ_div q k hq hk
    simp only [Units.val_mk0] at hlaw hupos
    rw [hn, hd] at hlaw
    rw [← show φ (dilation (Units.mk0 _ hu0)) = f ((((k * q + 1 : ℕ) : ℚ) /
      ((k * q : ℕ) : ℚ) : ℚ) : ℝ) from hfφ _ (by simpa using hupos)]
    calc Complex.normSq (φ (dilation (Units.mk0 _ hu0)))
        ≤ (successorDensity φ (k * q + 1)).re * (successorDensity φ (k * q)).re := hlaw
      _ ≤ r0 * (successorDensity φ q).re :=
        mul_le_mul (hA1 _ (Nat.succ_pos _)) (successorDensity_mul_le hφ hper q k hq hk)
          (hA0 _ hkq) hr0
  -- pass to the limit
  have hlim_u : Tendsto (fun k : ℕ =>
      ((((((k + 1) * q + 1 : ℕ) : ℚ) / (((k + 1) * q : ℕ) : ℚ)) : ℚ) : ℝ)) atTop (𝓝 1) := by
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have e : ∀ k : ℕ, ((((((k + 1) * q + 1 : ℕ) : ℚ) / (((k + 1) * q : ℕ) : ℚ)) : ℚ) : ℝ) =
        1 + (1 / ((k : ℝ) + 1)) / q := by
      intro k
      push_cast
      field_simp
    simp_rw [e]
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat).div_const (q : ℝ)).const_add (1 : ℝ)
    simpa using this
  have hlim := (Complex.continuous_normSq.tendsto _).comp (hf.tendsto.comp hlim_u)
  rw [hf1, Complex.normSq_ofReal] at hlim
  have hle : r0 * r0 ≤ r0 * (successorDensity φ q).re :=
    le_of_tendsto' hlim fun k => hbound (k + 1) k.succ_pos
  have hAq : r0 ≤ (successorDensity φ q).re := le_of_mul_le_mul_left hle hpos
  -- an average of real parts `≤ φ(1)` equal to `φ(1)`: every value is `φ(1)`
  have hsingle := successorDensity_eq_single hφ hper q hq
  set v : Fin q → ℂ := fun r => φ (translation (((r : ℕ) : ℚ) / q)) with hv
  have hre : ∀ r, (v r).re ≤ r0 := fun r => (Complex.re_le_norm _).trans (hnorm _)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsumre : (successorDensity φ q).re = (1 / (q : ℝ)) * ∑ r, (v r).re := by
    rw [hsingle, show (1 / (q : ℂ)) = ((1 / (q : ℝ) : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      Complex.re_sum]
  have hall : ∀ r, (v r).re = r0 := by
    have hz : ∑ r, (r0 - (v r).re) = 0 := by
      have h1 : ∑ r, (r0 - (v r).re) ≤ 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        rw [hsumre] at hAq
        have h2 : (q : ℝ) * r0 ≤ ∑ r, (v r).re := by
          have := mul_le_mul_of_nonneg_left hAq hqR.le
          rwa [← mul_assoc, mul_one_div_cancel hqR.ne', one_mul] at this
        linarith
      exact le_antisymm h1 (Finset.sum_nonneg fun r _ => by linarith [hre r])
    intro r
    have := (Finset.sum_eq_zero_iff_of_nonneg fun r _ => by linarith [hre r]).mp hz r
      (Finset.mem_univ r)
    linarith
  have hval : ∀ r, v r = r0 := by
    intro r
    have h1 := hnorm (translation (((r : ℕ) : ℚ) / q))
    have h2 := hall r
    apply Complex.ext
    · rw [h2, Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      have hns : Complex.normSq (v r) ≤ r0 ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [Complex.normSq_apply, h2] at hns
      nlinarith [sq_nonneg (v r).im]
  -- reduce `b` modulo `ℤ` to the level `q = den b`
  have hb : b = (((b.num % (q : ℤ)).toNat : ℕ) : ℚ) / q + ((b.num / (q : ℤ) : ℤ) : ℚ) := by
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    have hmod := Int.emod_add_ediv_mul b.num q
    have hnn : 0 ≤ b.num % (q : ℤ) := Int.emod_nonneg _ hqz.ne'
    have hcast : (((b.num % (q : ℤ)).toNat : ℕ) : ℚ) = ((b.num % (q : ℤ) : ℤ) : ℚ) := by
      rw [show (((b.num % (q : ℤ)).toNat : ℕ) : ℚ) = ((((b.num % (q : ℤ)).toNat : ℕ) : ℤ) : ℚ) by
        push_cast; rfl, Int.toNat_of_nonneg hnn]
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hmodQ : ((b.num % (q : ℤ) : ℤ) : ℚ) + ((b.num / (q : ℤ) : ℤ) : ℚ) * q = b.num := by
      exact_mod_cast hmod
    rw [hcast, div_add' _ _ _ hqQ, eq_div_iff hqQ, hmodQ, hq_def, Rat.mul_den_eq_num]
  have hlt : (b.num % (q : ℤ)).toNat < q := by
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    have := Int.emod_lt_of_pos b.num hqz
    omega
  rw [hb, translation_add_int hφ hper, h0]
  exact hval ⟨_, hlt⟩

/-- Translations form a homomorphic image of `ℚ`: `x ↦ x + (a + b)` is `(x ↦ x + a)(x ↦ x + b)`. -/
theorem translation_add (a b : ℚ) : translation (a + b) = translation a * translation b :=
  affine_ext (by rw [affSlope_mul, affSlope_translation, affSlope_translation, one_mul,
      affSlope_translation])
    (by rw [affShift_mul, affSlope_translation, affShift_translation, affShift_translation,
      affShift_translation]; ring)

/-- Conjugating a translation by a dilation scales it: `u(x/u + b) = x + ub`. -/
theorem dilation_mul_translation_mul_inv (u : ℚˣ) (b : ℚ) :
    dilation u * translation b * (dilation u)⁻¹ = translation ((u : ℚ) * b) := by
  refine affine_ext ?_ ?_
  · rw [affSlope_mul, affSlope_mul, affSlope_inv, affSlope_dilation, affSlope_translation,
      affSlope_translation, mul_one, mul_inv_cancel₀ u.ne_zero]
  · simp only [affShift_mul, affShift_inv, affShift_dilation, affShift_translation,
      affSlope_dilation, neg_zero, zero_div, mul_zero, zero_add, add_zero]

/-- A single period generates a lattice of periods: `φ(x + b) = φ(1)` at `b = h` gives it at every
`b ∈ hℤ`, by bi-invariance. -/
theorem translation_zmul_eq {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {h : ℚ}
    (hper : φ (translation h) = φ 1) (m : ℤ) : φ (translation (h * m)) = φ 1 := by
  induction m using Int.induction_on with
  | zero => rw [Int.cast_zero, mul_zero, translation_zero]
  | succ m ih =>
    rw [Int.cast_add, Int.cast_one, mul_add, mul_one, translation_add, hφ.mul_right_eq hper, ih]
  | pred m ih =>
    have := hφ.mul_right_eq hper (translation (h * ((-(m : ℤ) - 1 : ℤ) : ℚ)))
    rw [← translation_add] at this
    rw [← this, ← ih]
    congr 2
    push_cast; ring

/-- **Mautner rigidity, one period.** If the successor of a positive-definite `φ` on `Aff(ℚ)` has a
single nonzero period, `φ(x ↦ x + h) = φ(1)`, and the dilation part on `ℚ_{>0}` is continuous at
`1`, then the successor is constant. Conjugation by `x ↦ hx` moves the period to `1` and fixes the
dilations. -/
theorem translation_eq_of_period {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {h : ℚ}
    (hh : h ≠ 0) (hper : φ (translation h) = φ 1) {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hfφ : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = f (u : ℚ)) (b : ℚ) :
    φ (translation b) = φ 1 := by
  set c : AffineGroupQ := dilation (Units.mk0 h hh) with hc
  have hψ : IsPosDefOnGroup (φ ∘ (MulAut.conj c).toMonoidHom) := hφ.comp_hom _
  have hconj : ∀ g, (φ ∘ (MulAut.conj c).toMonoidHom) g = φ (c * g * c⁻¹) := fun g => rfl
  have hψper : ∀ m : ℤ, (φ ∘ (MulAut.conj c).toMonoidHom) (translation m) =
      (φ ∘ (MulAut.conj c).toMonoidHom) 1 := fun m => by
    rw [hconj, hconj, hc, dilation_mul_translation_mul_inv, mul_one, mul_inv_cancel, Units.val_mk0,
      translation_zmul_eq hφ hper m]
  have hψdil : ∀ u : ℚˣ, 0 < (u : ℚ) → (φ ∘ (MulAut.conj c).toMonoidHom) (dilation u) =
      f (u : ℚ) := fun u hu => by
    rw [hconj, hc, ← map_inv, ← map_mul, ← map_mul, mul_inv_cancel_comm, hfφ u hu]
  have key := translation_eq_of_continuousAt_dilation hψ hψper hf hψdil (b / h)
  rw [hconj, hconj, hc, dilation_mul_translation_mul_inv, mul_one, mul_inv_cancel, Units.val_mk0,
    mul_div_cancel₀ b hh] at key
  exact key

end GaloisForLFunctions.ArithmeticPositiveDuality
