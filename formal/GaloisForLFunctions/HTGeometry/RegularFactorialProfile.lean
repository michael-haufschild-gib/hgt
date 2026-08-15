import GaloisForLFunctions.HTGeometry.GammaRealShiftProfile

/-!
# Profiles that grow exactly like a power of the factorial

A coefficient profile of Gevrey type `s` grows one step at a time by a factor comparable to
`(k+1)^s`.  Iterating that single-step comparison across a whole block turns the geometric factor
into a power and the polynomial factors into a ratio of factorials:

```text
Θ a · c₁^{b−a} · (b! / a!)^s  ≤  Θ b  ≤  Θ a · c₂^{b−a} · (b! / a!)^s .
```

Both directions are needed when a coefficient recursion is read at index `n`: the shifts below the
leading one have to be beaten by a growing factor and the shifts above it by a decaying one, and the
factorial form keeps the estimate sharp all the way out to shift `n`, where the crude bound
`b!/a! ≥ (a+1)^{b−a}` throws away everything.

The gamma profile `Γ(1 + s k)·β^k` is of this kind, with explicit constants coming from the
log-convexity shift bounds: for a natural `M` with `s < M < s + 1` — such an `M` exists exactly when
`s` is not an integer — one has `(s + 1 − M)(k+1) ≤ 1 + s(k+1) − M` and
`1 + s k + M ≤ (1 + M + s)(k+1)`.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- A positive sequence whose one-step ratio is comparable to `(k+1)^s`. -/
structure IsRegularFactorialProfile (s c₁ c₂ : ℝ) (Θ : ℕ → ℝ) : Prop where
  c₁_pos : 0 < c₁
  c₂_pos : 0 < c₂
  pos : ∀ k, 0 < Θ k
  lower : ∀ k : ℕ, c₁ * (((k : ℝ) + 1) ^ s * Θ k) ≤ Θ (k + 1)
  upper : ∀ k : ℕ, Θ (k + 1) ≤ c₂ * (((k : ℝ) + 1) ^ s * Θ k)

namespace IsRegularFactorialProfile

variable {s c₁ c₂ : ℝ} {Θ : ℕ → ℝ}

theorem factorial_div_pos {a b : ℕ} : 0 < ((b ! : ℝ)) / ((a ! : ℝ)) :=
  div_pos (Nat.cast_pos.mpr (Nat.factorial_pos b)) (Nat.cast_pos.mpr (Nat.factorial_pos a))

theorem factorial_succ_div_eq (a b : ℕ) :
    (((b + 1)! : ℝ)) / ((a ! : ℝ)) = ((b : ℝ) + 1) * ((((b ! : ℝ))) / ((a ! : ℝ))) := by
  have ha : ((a ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  rw [Nat.factorial_succ]
  push_cast
  field_simp

theorem rpow_factorial_succ_div (s : ℝ) (a b : ℕ) :
    ((((b + 1)! : ℝ)) / ((a ! : ℝ))) ^ s
      = ((b : ℝ) + 1) ^ s * ((((b ! : ℝ))) / ((a ! : ℝ))) ^ s := by
  rw [factorial_succ_div_eq a b,
    Real.mul_rpow (by positivity) (le_of_lt (factorial_div_pos (a := a) (b := b)))]

/-- **The block form of the lower step bound.** -/
theorem block_lower (h : IsRegularFactorialProfile s c₁ c₂ Θ) {a b : ℕ} (hab : a ≤ b) :
    Θ a * c₁ ^ (b - a) * (((b ! : ℝ)) / ((a ! : ℝ))) ^ s ≤ Θ b := by
  induction b, hab using Nat.le_induction with
  | base =>
      have hone : ((a ! : ℝ)) / ((a ! : ℝ)) = 1 :=
        div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))
      simp [hone]
  | succ b hb ih =>
      have hpos : (0 : ℝ) < ((b : ℝ) + 1) := by positivity
      have hcount : b + 1 - a = (b - a) + 1 := by omega
      have hkey : Θ a * c₁ ^ (b + 1 - a) * ((((b + 1)! : ℝ)) / ((a ! : ℝ))) ^ s
          = c₁ * (((b : ℝ) + 1) ^ s *
              (Θ a * c₁ ^ (b - a) * ((((b ! : ℝ))) / ((a ! : ℝ))) ^ s)) := by
        rw [hcount, rpow_factorial_succ_div, pow_succ]
        ring
      rw [hkey]
      refine le_trans ?_ (h.lower b)
      refine mul_le_mul_of_nonneg_left ?_ h.c₁_pos.le
      exact mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg hpos.le s)

/-- **The block form of the upper step bound.** -/
theorem block_upper (h : IsRegularFactorialProfile s c₁ c₂ Θ) {a b : ℕ} (hab : a ≤ b) :
    Θ b ≤ Θ a * c₂ ^ (b - a) * (((b ! : ℝ)) / ((a ! : ℝ))) ^ s := by
  induction b, hab using Nat.le_induction with
  | base =>
      have hone : ((a ! : ℝ)) / ((a ! : ℝ)) = 1 :=
        div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))
      simp [hone]
  | succ b hb ih =>
      have hpos : (0 : ℝ) < ((b : ℝ) + 1) := by positivity
      have hcount : b + 1 - a = (b - a) + 1 := by omega
      have hkey : Θ a * c₂ ^ (b + 1 - a) * ((((b + 1)! : ℝ)) / ((a ! : ℝ))) ^ s
          = c₂ * (((b : ℝ) + 1) ^ s *
              (Θ a * c₂ ^ (b - a) * ((((b ! : ℝ))) / ((a ! : ℝ))) ^ s)) := by
        rw [hcount, rpow_factorial_succ_div, pow_succ]
        ring
      rw [hkey]
      refine le_trans (h.upper b) ?_
      refine mul_le_mul_of_nonneg_left ?_ h.c₂_pos.le
      exact mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg hpos.le s)

/-- Scaling a profile by a positive constant keeps it regular, with the same constants. -/
theorem const_mul (h : IsRegularFactorialProfile s c₁ c₂ Θ) {K : ℝ} (hK : 0 < K) :
    IsRegularFactorialProfile s c₁ c₂ (fun k => K * Θ k) where
  c₁_pos := h.c₁_pos
  c₂_pos := h.c₂_pos
  pos k := mul_pos hK (h.pos k)
  lower k := by
    have h1 := mul_le_mul_of_nonneg_left (h.lower k) hK.le
    calc c₁ * (((k : ℝ) + 1) ^ s * (K * Θ k))
        = K * (c₁ * (((k : ℝ) + 1) ^ s * Θ k)) := by ring
      _ ≤ K * Θ (k + 1) := h1
  upper k := by
    have h1 := mul_le_mul_of_nonneg_left (h.upper k) hK.le
    calc K * Θ (k + 1) ≤ K * (c₂ * (((k : ℝ) + 1) ^ s * Θ k)) := h1
      _ = c₂ * (((k : ℝ) + 1) ^ s * (K * Θ k)) := by ring

end IsRegularFactorialProfile

/-! ### The gamma profile is a regular factorial profile -/

theorem isRegularFactorialProfile_gammaProfile {s β : ℝ} (hs : 0 < s) (hβ : 0 < β)
    {M : ℕ} (hM : s < M) (hM' : (M : ℝ) < s + 1) :
    IsRegularFactorialProfile s (β * (s + 1 - M) ^ s) (β * (1 + M + s) ^ s)
      (gammaProfile s β) where
  c₁_pos := by
    have h : (0 : ℝ) < s + 1 - (M : ℝ) := by linarith
    positivity
  c₂_pos := by
    have h : (0 : ℝ) < 1 + (M : ℝ) + s := by positivity
    positivity
  pos k := gammaProfile_pos hs.le hβ k
  lower k := by
    have hM0 : (0 : ℝ) < (M : ℝ) := lt_trans hs hM
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have h1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        rw [hz] at hM0
        norm_num at hM0)
      exact_mod_cast h1
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hcpos : (0 : ℝ) < s + 1 - (M : ℝ) := by linarith
    have hstep : (s + 1 - (M : ℝ)) * ((k : ℝ) + 1) ≤ (1 + s * (k : ℝ)) + s - (M : ℝ) := by
      nlinarith [mul_nonneg hknn (by linarith : (0 : ℝ) ≤ (M : ℝ) - 1)]
    have hy : (0 : ℝ) < (1 + s * (k : ℝ)) + s - (M : ℝ) := by
      have : (0 : ℝ) < (s + 1 - (M : ℝ)) * ((k : ℝ) + 1) := mul_pos hcpos hkpos
      linarith
    have hx : (0 : ℝ) < 1 + s * (k : ℝ) := by nlinarith
    have hGpos : (0 : ℝ) < Real.Gamma (1 + s * (k : ℝ)) := Real.Gamma_pos_of_pos hx
    have hlow := mul_rpow_le_Gamma_add (x := 1 + s * (k : ℝ)) hs hM hy
    have hmono : ((s + 1 - (M : ℝ)) * ((k : ℝ) + 1)) ^ s
        ≤ ((1 + s * (k : ℝ)) + s - (M : ℝ)) ^ s :=
      Real.rpow_le_rpow (by positivity) hstep hs.le
    have hsplit : ((s + 1 - (M : ℝ)) * ((k : ℝ) + 1)) ^ s
        = (s + 1 - (M : ℝ)) ^ s * ((k : ℝ) + 1) ^ s :=
      Real.mul_rpow hcpos.le hkpos.le
    have hchain : (s + 1 - (M : ℝ)) ^ s * ((k : ℝ) + 1) ^ s * Real.Gamma (1 + s * (k : ℝ))
        ≤ Real.Gamma ((1 + s * (k : ℝ)) + s) :=
      calc (s + 1 - (M : ℝ)) ^ s * ((k : ℝ) + 1) ^ s * Real.Gamma (1 + s * (k : ℝ))
          = Real.Gamma (1 + s * (k : ℝ)) * ((s + 1 - (M : ℝ)) * ((k : ℝ) + 1)) ^ s := by
            rw [hsplit]; ring
        _ ≤ Real.Gamma (1 + s * (k : ℝ)) * ((1 + s * (k : ℝ)) + s - (M : ℝ)) ^ s :=
            mul_le_mul_of_nonneg_left hmono hGpos.le
        _ ≤ Real.Gamma ((1 + s * (k : ℝ)) + s) := hlow
    have hcast : 1 + s * ((k + 1 : ℕ) : ℝ) = (1 + s * (k : ℝ)) + s := by
      push_cast
      ring
    rw [gammaProfile, gammaProfile, hcast, pow_succ]
    calc β * (s + 1 - (M : ℝ)) ^ s *
          (((k : ℝ) + 1) ^ s * (Real.Gamma (1 + s * (k : ℝ)) * β ^ k))
        = ((s + 1 - (M : ℝ)) ^ s * ((k : ℝ) + 1) ^ s * Real.Gamma (1 + s * (k : ℝ))) *
            (β ^ k * β) := by ring
      _ ≤ Real.Gamma ((1 + s * (k : ℝ)) + s) * (β ^ k * β) :=
          mul_le_mul_of_nonneg_right hchain (by positivity)
  upper k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hx : (0 : ℝ) < 1 + s * (k : ℝ) := by nlinarith
    have hGpos : (0 : ℝ) < Real.Gamma (1 + s * (k : ℝ)) := Real.Gamma_pos_of_pos hx
    have hup := Gamma_add_le_mul_rpow (x := 1 + s * (k : ℝ)) hx hs hM
    have hstep : (1 + s * (k : ℝ)) + (M : ℝ) ≤ (1 + (M : ℝ) + s) * ((k : ℝ) + 1) := by
      nlinarith [mul_nonneg hknn (by linarith : (0 : ℝ) ≤ 1 + (M : ℝ))]
    have hmono : ((1 + s * (k : ℝ)) + (M : ℝ)) ^ s ≤ ((1 + (M : ℝ) + s) * ((k : ℝ) + 1)) ^ s :=
      Real.rpow_le_rpow (by positivity) hstep hs.le
    have hsplit : ((1 + (M : ℝ) + s) * ((k : ℝ) + 1)) ^ s
        = (1 + (M : ℝ) + s) ^ s * ((k : ℝ) + 1) ^ s :=
      Real.mul_rpow (by positivity) hkpos.le
    have hchain : Real.Gamma ((1 + s * (k : ℝ)) + s)
        ≤ (1 + (M : ℝ) + s) ^ s * ((k : ℝ) + 1) ^ s * Real.Gamma (1 + s * (k : ℝ)) :=
      calc Real.Gamma ((1 + s * (k : ℝ)) + s)
          ≤ Real.Gamma (1 + s * (k : ℝ)) * ((1 + s * (k : ℝ)) + (M : ℝ)) ^ s := hup
        _ ≤ Real.Gamma (1 + s * (k : ℝ)) * ((1 + (M : ℝ) + s) * ((k : ℝ) + 1)) ^ s :=
            mul_le_mul_of_nonneg_left hmono hGpos.le
        _ = (1 + (M : ℝ) + s) ^ s * ((k : ℝ) + 1) ^ s * Real.Gamma (1 + s * (k : ℝ)) := by
            rw [hsplit]; ring
    have hcast : 1 + s * ((k + 1 : ℕ) : ℝ) = (1 + s * (k : ℝ)) + s := by
      push_cast
      ring
    rw [gammaProfile, gammaProfile, hcast, pow_succ]
    calc Real.Gamma ((1 + s * (k : ℝ)) + s) * (β ^ k * β)
        ≤ ((1 + (M : ℝ) + s) ^ s * ((k : ℝ) + 1) ^ s * Real.Gamma (1 + s * (k : ℝ))) *
            (β ^ k * β) := mul_le_mul_of_nonneg_right hchain (by positivity)
      _ = β * (1 + (M : ℝ) + s) ^ s *
            (((k : ℝ) + 1) ^ s * (Real.Gamma (1 + s * (k : ℝ)) * β ^ k)) := by ring

/-- For an irrational exponent the ceiling supplies the natural number the shift bounds need. -/
theorem isRegularFactorialProfile_gammaProfile_of_irrational {s β : ℝ} (hs : 0 < s)
    (hirr : Irrational s) (hβ : 0 < β) :
    IsRegularFactorialProfile s (β * (s + 1 - (⌈s⌉₊ : ℝ)) ^ s) (β * (1 + (⌈s⌉₊ : ℝ) + s) ^ s)
      (gammaProfile s β) := by
  have hle : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hne : s ≠ (⌈s⌉₊ : ℝ) := hirr.ne_nat ⌈s⌉₊
  have hlt : s < (⌈s⌉₊ : ℝ) := lt_of_le_of_ne hle hne
  have hup : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one hs.le
  exact isRegularFactorialProfile_gammaProfile hs hβ hlt hup

end GaloisForLFunctions.HTGeometry
