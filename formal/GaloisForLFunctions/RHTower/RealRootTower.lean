/-
The σ-equivariant (Real) root tower: one seam bit beyond the deck data at every level.

On the boundary of a symmetric window the reflection `θ ↦ π − θ` (fixed point `π/2`) acts on a
nonvanishing loop `γ` by Schwarz conjugation, `γ (π − θ) = conj (γ θ)`.  An *equivariant* `2^k`-th
root is a nonvanishing loop `V` commuting with the same reflection whose `2^k`-th power is `γ`.  Such
a root exists **iff** two conditions hold: the deck condition `2^k ∣ windingNumber γ` (the plain
tower obstruction, unchanged by the symmetry) and one seam bit — positivity of the fixed-angle value
`0 < (γ (π/2)).re`.

The seam bit is forced because a continuous logarithm of `γ` carries an integer reflection twist
`k₀` (`equivariant_log_twist`) whose parity is the fixed-angle sign (`twist_parity_eq_sign`), and a
log-branch adjustment by `2πi·ℤ` moves that twist by *even* integers only.  When the anchor sign is
positive the twist is even, so it can be cancelled to zero by a shift, producing a reflection-fixed
logarithm; dividing it by `2^k` and exponentiating gives the equivariant root exactly when the
winding is divisible by `2^k`.  The obstruction therefore saturates at a single bit for every level:
beyond the deck datum the seam adds only the anchor sign, never more.

A *full* equivariant tower — a compatible `2^k`-th root at every level `k` — exists iff the winding
vanishes and the anchor sign is positive: divisibility by every `2^k` forces the integer winding to
`0`, and conversely `0` is divisible at every level.  The Real tower is the plain root tower welded
to the seam sign.
-/
import GaloisForLFunctions.RHTower.SeamEquivariantTwist
import GaloisForLFunctions.RHTower.WindingNumber

open Complex

namespace RHTower

/-! ### §1 The per-level equivariant root: deck datum welded to one seam bit -/

/-- **The equivariant `2^k`-th root criterion.**  A symmetric nonvanishing loop `γ`
(`γ (π − θ) = conj (γ θ)`) admits a nonvanishing equivariant `2^k`-th root — a loop `V` commuting
with the reflection whose `2^k`-th power is `γ` — **iff** `2^k` divides the winding number *and* the
fixed-angle value is positive (`0 < (γ (π/2)).re`).

Forward: the root `V` is itself a nonvanishing loop, so `windingNumber γ = 2^k · windingNumber V`
gives the divisibility (`windingNumber_pow`); equivariance makes `V (π/2)` a nonzero real, and `γ`
at the fixed angle is that real to the even power `2^k`, hence positive.  Backward: with a positive
anchor the reflection twist `k₀` of `contLog γ` is even (`twist_parity_eq_sign`), so a shift by
`2πi·(−m₀)` (with `k₀ = 2 m₀`) cancels it to a reflection-fixed logarithm `L'`; when `2^k ∣` the
winding, `V := exp (L'/2^k)` closes up, commutes with the reflection, and powers back to `γ`. -/
theorem equivariant_pow_root_iff {γ : ℝ → ℂ} (hL : IsLoop γ 0 (2 * Real.pi))
    (heq : ∀ θ, γ (Real.pi - θ) = (starRingEnd ℂ) (γ θ)) (k : ℕ) (hk : k ≠ 0) :
    (∃ V : ℝ → ℂ, Continuous V ∧ (∀ θ, V θ ≠ 0) ∧ V 0 = V (2 * Real.pi) ∧
      (∀ θ, V (Real.pi - θ) = (starRingEnd ℂ) (V θ)) ∧
      (∀ θ, (V θ) ^ (2 ^ k) = γ θ))
    ↔ ((2 ^ k : ℤ) ∣ windingNumber γ 0 (2 * Real.pi) ∧ 0 < (γ (Real.pi / 2)).re) := by
  have hc2k : ((2 ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero k two_ne_zero
  have hconj_c2k : (starRingEnd ℂ) ((2 ^ k : ℕ) : ℂ) = ((2 ^ k : ℕ) : ℂ) :=
    map_natCast (starRingEnd ℂ) (2 ^ k)
  constructor
  · rintro ⟨V, hVc, hVne, hVcl, hVeq, hVpow⟩
    have hVloop : IsLoop V 0 (2 * Real.pi) := ⟨hVc, hVne, hVcl⟩
    refine ⟨?_, ?_⟩
    · -- deck condition: winding of `γ = V^{2^k}` is `2^k` times the winding of `V`
      refine ⟨windingNumber V 0 (2 * Real.pi), ?_⟩
      have hwind := windingNumber_pow hVloop (2 ^ k)
      rw [funext hVpow] at hwind
      rw [hwind]; push_cast; ring
    · -- seam bit: `V (π/2)` is a nonzero real, `γ (π/2)` is it to the even power `2^k`
      have him : (V (Real.pi / 2)).im = 0 := equivariant_midpoint_im_zero hVeq
      set x : ℝ := (V (Real.pi / 2)).re with hxdef
      have hxne : x ≠ 0 := fun hx =>
        hVne (Real.pi / 2) (Complex.ext (by rw [Complex.zero_re]; exact hx)
          (by rw [Complex.zero_im]; exact him))
      have hVreal : V (Real.pi / 2) = (x : ℂ) :=
        Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; exact him)
      have hxpow : 0 < x ^ (2 ^ k) := Even.pow_pos (Nat.even_pow.mpr ⟨even_two, hk⟩) hxne
      have hval : (γ (Real.pi / 2)).re = x ^ (2 ^ k) := by
        rw [← hVpow (Real.pi / 2), hVreal, ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hval]; exact hxpow
  · rintro ⟨hdvd, hsign⟩
    obtain ⟨hLc, hLe⟩ := contLog_spec hL.continuous hL.nonzero
    obtain ⟨k₀, htw₀⟩ := equivariant_log_twist heq hLc hLe
    have hk₀even : Even k₀ := (twist_parity_eq_sign hLe htw₀).mp hsign
    obtain ⟨m₀, hm₀⟩ := hk₀even
    have hkz : k₀ = 2 * m₀ := by omega
    set L' : ℝ → ℂ := fun θ => contLog γ θ + ((-m₀ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I)
      with hL'def
    have hL'c : Continuous L' := by rw [hL'def]; exact hLc.add continuous_const
    have hL'e : ∀ t, Complex.exp (L' t) = γ t := by
      intro t
      simp only [hL'def]
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      exact hLe t
    -- the shift by `2πi·(−m₀)` cancels the (even) twist: `L'` is reflection-fixed
    have htw' : ∀ θ, (starRingEnd ℂ) (L' (Real.pi - θ)) = L' θ := by
      intro θ
      have hconjm : (starRingEnd ℂ) (((-m₀ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I))
          = -(((-m₀ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
        simp only [map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal, map_ofNat]
        ring
      have hk : (k₀ : ℂ) = 2 * (m₀ : ℂ) := by exact_mod_cast hkz
      simp only [hL'def]
      rw [map_add, htw₀ θ, hconjm, hk]
      push_cast
      ring
    have hL'conj : ∀ θ, L' (Real.pi - θ) = (starRingEnd ℂ) (L' θ) := by
      intro θ
      have h := congrArg (starRingEnd ℂ) (htw' θ)
      rwa [Complex.conj_conj] at h
    refine ⟨fun θ => Complex.exp (L' θ / ((2 ^ k : ℕ) : ℂ)), ?_, ?_, ?_, ?_, ?_⟩
    · exact Complex.continuous_exp.comp (hL'c.div_const _)
    · intro θ; exact Complex.exp_ne_zero _
    · -- closure: `L' (2π) − L' 0 = 2πi·(winding)`, and `2^k ∣ winding` clears the endpoint jump
      show Complex.exp (L' 0 / ((2 ^ k : ℕ) : ℂ)) =
        Complex.exp (L' (2 * Real.pi) / ((2 ^ k : ℕ) : ℂ))
      obtain ⟨q, hq⟩ := hdvd
      have hincr : L' (2 * Real.pi) - L' 0
          = (windingNumber γ 0 (2 * Real.pi) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        have h := contLog_increment hL hLc hLe
        simp only [hL'def]
        linear_combination h
      have hnq : (windingNumber γ 0 (2 * Real.pi) : ℂ) = ((2 ^ k : ℕ) : ℂ) * (q : ℂ) := by
        rw [hq]; push_cast; ring
      rw [hnq] at hincr
      have hstep : L' (2 * Real.pi) / ((2 ^ k : ℕ) : ℂ)
          = L' 0 / ((2 ^ k : ℕ) : ℂ) + (q : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        field_simp
        linear_combination hincr
      rw [hstep, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · -- equivariance: `Λ (π−θ) = conj (Λ θ)` since `L'` is reflection-fixed and `2^k` is real
      intro θ
      show Complex.exp (L' (Real.pi - θ) / ((2 ^ k : ℕ) : ℂ)) =
        (starRingEnd ℂ) (Complex.exp (L' θ / ((2 ^ k : ℕ) : ℂ)))
      have harg : L' (Real.pi - θ) / ((2 ^ k : ℕ) : ℂ)
          = (starRingEnd ℂ) (L' θ / ((2 ^ k : ℕ) : ℂ)) := by
        rw [map_div₀, hconj_c2k, hL'conj θ]
      rw [harg]; exact Complex.exp_conj _
    · -- power: `(exp (L'/2^k))^{2^k} = exp L' = γ`
      intro θ
      show (Complex.exp (L' θ / ((2 ^ k : ℕ) : ℂ))) ^ (2 ^ k) = γ θ
      rw [← Complex.exp_nat_mul, mul_div_assoc', mul_div_cancel_left₀ (L' θ) hc2k]
      exact hL'e θ

/-! ### §2 The full equivariant tower: winding zero and positive anchor -/

/-- **The full equivariant tower criterion.**  A symmetric nonvanishing loop `γ` admits a compatible
equivariant `2^k`-th root at *every* level `k ≥ 1` **iff** its winding number vanishes and the
fixed-angle value is positive.

Forward: divisibility of the winding by `2^k` for all `k` forces the integer to `0` (it would
otherwise exceed its own absolute value at `k = |winding|`), and the anchor sign comes from the
level-`1` root.  Backward: `0` is divisible by every `2^k`, so the per-level criterion
(`equivariant_pow_root_iff`) supplies the root at each level. -/
theorem equivariant_full_tower_iff {γ : ℝ → ℂ} (hL : IsLoop γ 0 (2 * Real.pi))
    (heq : ∀ θ, γ (Real.pi - θ) = (starRingEnd ℂ) (γ θ)) :
    (∀ k : ℕ, k ≠ 0 → ∃ V : ℝ → ℂ, Continuous V ∧ (∀ θ, V θ ≠ 0) ∧ V 0 = V (2 * Real.pi) ∧
      (∀ θ, V (Real.pi - θ) = (starRingEnd ℂ) (V θ)) ∧ (∀ θ, (V θ) ^ (2 ^ k) = γ θ))
    ↔ (windingNumber γ 0 (2 * Real.pi) = 0 ∧ 0 < (γ (Real.pi / 2)).re) := by
  constructor
  · intro htower
    have hsign : 0 < (γ (Real.pi / 2)).re :=
      ((equivariant_pow_root_iff hL heq 1 one_ne_zero).mp (htower 1 one_ne_zero)).2
    have hdvd : ∀ k : ℕ, k ≠ 0 → (2 ^ k : ℤ) ∣ windingNumber γ 0 (2 * Real.pi) :=
      fun k hk => ((equivariant_pow_root_iff hL heq k hk).mp (htower k hk)).1
    refine ⟨?_, hsign⟩
    by_contra hn
    have hnabs : (windingNumber γ 0 (2 * Real.pi)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
    have hdvdk := hdvd (windingNumber γ 0 (2 * Real.pi)).natAbs hnabs
    have hdvd_nat : 2 ^ (windingNumber γ 0 (2 * Real.pi)).natAbs
        ∣ (windingNumber γ 0 (2 * Real.pi)).natAbs := by
      have h := Int.natAbs_dvd_natAbs.mpr hdvdk
      simpa [Int.natAbs_pow] using h
    have h2 : 2 ^ (windingNumber γ 0 (2 * Real.pi)).natAbs
        ≤ (windingNumber γ 0 (2 * Real.pi)).natAbs :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hnabs) hdvd_nat
    have h3 : (windingNumber γ 0 (2 * Real.pi)).natAbs
        < 2 ^ (windingNumber γ 0 (2 * Real.pi)).natAbs := Nat.lt_pow_self (by norm_num)
    omega
  · rintro ⟨hw, hsign⟩ k hk
    exact (equivariant_pow_root_iff hL heq k hk).mpr ⟨by rw [hw]; exact dvd_zero _, hsign⟩

end RHTower
