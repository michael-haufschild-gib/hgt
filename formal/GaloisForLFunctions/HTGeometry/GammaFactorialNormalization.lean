import Mathlib

/-!
# Gamma against powers of the factorial

Gevrey order has two standard normalizations, `|b_k| ≤ C A^k Γ(1 + r k)` and
`|b_k| ≤ C A^k (k!)^r`.  They define the same order because the two scales differ by a factor that
is itself of the form `C A^k`:

`c a^k (k!)^s ≤ Γ(1 + s k) ≤ A^k (k!)^s`.

Both bounds come from log-convexity of `Γ` alone — no Stirling estimate is used.  Log-convexity
gives the two Wendel-type shift bounds

`Γ(x) (x + s - M)^s ≤ Γ(x + s) ≤ Γ(x) (x + M)^s`   (`M` a natural number above `s`),

and the products of those bounds along `x = 1 + s k` telescope against `k!`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-! ### Integer shifts of `Γ` -/

/-- `Γ(x + N)` as `Γ(x)` times a rising factorial. -/
theorem Gamma_add_nat (x : ℝ) (hx : 0 < x) (N : ℕ) :
    Real.Gamma (x + N) = Real.Gamma x * ∏ i ∈ Finset.range N, (x + i) := by
  induction N with
  | zero => simp
  | succ N IH =>
      have hxN : x + (N : ℝ) ≠ 0 := by positivity
      have hstep : x + ((N + 1 : ℕ) : ℝ) = (x + (N : ℝ)) + 1 := by push_cast; ring
      rw [hstep, Real.Gamma_add_one hxN, IH, Finset.prod_range_succ]
      ring

/-- The rising factorial is bounded above by a power of its largest factor. -/
theorem prod_range_add_le (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ∏ i ∈ Finset.range N, (x + i) ≤ (x + N) ^ N := by
  calc ∏ i ∈ Finset.range N, (x + i)
      ≤ ∏ _i ∈ Finset.range N, (x + N) := by
        refine Finset.prod_le_prod (fun i _ => by positivity) (fun i hi => ?_)
        have : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_range.mp hi).le
        linarith
    _ = (x + N) ^ N := by simp

/-- The rising factorial is bounded below by a power of its smallest factor. -/
theorem le_prod_range_add (x : ℝ) (hx : 0 < x) (N : ℕ) :
    x ^ N ≤ ∏ i ∈ Finset.range N, (x + i) := by
  calc x ^ N = ∏ _i ∈ Finset.range N, x := by simp
    _ ≤ ∏ i ∈ Finset.range N, (x + i) := by
        refine Finset.prod_le_prod (fun i _ => hx.le) (fun i _ => ?_)
        have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith

/-! ### Wendel-type shift bounds from log-convexity -/

/-- **Upper shift bound.**  For `x > 0`, `s > 0` and a natural `M > s`,
`Γ(x + s) ≤ Γ(x) (x + M)^s`. -/
theorem Gamma_add_le_mul_rpow {x s : ℝ} (hx : 0 < x) (hs : 0 < s) {M : ℕ} (hM : s < M) :
    Real.Gamma (x + s) ≤ Real.Gamma x * (x + M) ^ s := by
  have hM0 : (0 : ℝ) < M := lt_trans hs hM
  have hxM : (0 : ℝ) < x + M := by positivity
  have hb : (0 : ℝ) < s / M := by positivity
  have ha : (0 : ℝ) < 1 - s / M := by
    have : s / M < 1 := (div_lt_one hM0).mpr hM
    linarith
  have hab : (1 - s / M) + s / M = 1 := by ring
  have hkey := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hxM ha hb hab
  have harg : (1 - s / M) * x + (s / M) * (x + M) = x + s := by
    field_simp
    ring
  rw [harg] at hkey
  have hGx : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hprod : Real.Gamma (x + M) ≤ Real.Gamma x * (x + M) ^ M := by
    rw [Gamma_add_nat x hx M]
    exact mul_le_mul_of_nonneg_left (prod_range_add_le x hx M) hGx.le
  have hGxM : (0 : ℝ) < Real.Gamma (x + M) := Real.Gamma_pos_of_pos hxM
  have hstep : Real.Gamma (x + M) ^ (s / M) ≤ (Real.Gamma x * (x + M) ^ M) ^ (s / M) :=
    Real.rpow_le_rpow hGxM.le hprod hb.le
  have hmono : Real.Gamma x ^ (1 - s / M) * Real.Gamma (x + M) ^ (s / M)
      ≤ Real.Gamma x ^ (1 - s / M) * (Real.Gamma x * (x + M) ^ M) ^ (s / M) :=
    mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hGx.le _)
  have hsimp : Real.Gamma x ^ (1 - s / M) * (Real.Gamma x * (x + M) ^ M) ^ (s / M)
      = Real.Gamma x * (x + M) ^ s := by
    rw [Real.mul_rpow hGx.le (by positivity), ← Real.rpow_natCast (x + M) M,
      ← Real.rpow_mul hxM.le, ← mul_assoc, ← Real.rpow_add hGx]
    have h1 : (1 - s / M) + s / M = 1 := by ring
    have h2 : (M : ℝ) * (s / M) = s := by field_simp
    rw [h1, h2, Real.rpow_one]
  linarith [hkey.trans (hmono.trans_eq hsimp)]

/-- **Lower shift bound.**  For `s > 0` and a natural `M > s`, whenever `x + s - M > 0`,
`Γ(x) (x + s - M)^s ≤ Γ(x + s)`. -/
theorem mul_rpow_le_Gamma_add {x s : ℝ} (hs : 0 < s) {M : ℕ} (hM : s < M)
    (hy : 0 < x + s - M) :
    Real.Gamma x * (x + s - M) ^ s ≤ Real.Gamma (x + s) := by
  have hM0 : (0 : ℝ) < M := lt_trans hs hM
  set y : ℝ := x + s - M with hydef
  have hx : (0 : ℝ) < x := by
    have : (M : ℝ) - s < x := by linarith
    have hMs : (0 : ℝ) < (M : ℝ) - s := by linarith
    linarith
  have hxs : (0 : ℝ) < x + s := by linarith
  have hb : (0 : ℝ) < s / M := by positivity
  have ha : (0 : ℝ) < 1 - s / M := by
    have : s / M < 1 := (div_lt_one hM0).mpr hM
    linarith
  have hab : (1 - s / M) + s / M = 1 := by ring
  have hkey := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hxs hy ha hb hab
  have harg : (1 - s / M) * (x + s) + (s / M) * y = x := by
    rw [hydef]
    field_simp
    ring
  rw [harg] at hkey
  have hGy : (0 : ℝ) < Real.Gamma y := Real.Gamma_pos_of_pos hy
  have hGxs : (0 : ℝ) < Real.Gamma (x + s) := Real.Gamma_pos_of_pos hxs
  have hyM : Real.Gamma (x + s) = Real.Gamma y * ∏ i ∈ Finset.range M, (y + i) := by
    have : x + s = y + (M : ℝ) := by rw [hydef]; ring
    rw [this, Gamma_add_nat y hy M]
  have hprod : Real.Gamma y * y ^ M ≤ Real.Gamma (x + s) := by
    rw [hyM]
    exact mul_le_mul_of_nonneg_left (le_prod_range_add y hy M) hGy.le
  have hGyle : Real.Gamma y ≤ Real.Gamma (x + s) / y ^ M := by
    rw [le_div_iff₀ (by positivity)]
    exact hprod
  have hstep : Real.Gamma y ^ (s / M) ≤ (Real.Gamma (x + s) / y ^ M) ^ (s / M) :=
    Real.rpow_le_rpow hGy.le hGyle hb.le
  have hmono : Real.Gamma (x + s) ^ (1 - s / M) * Real.Gamma y ^ (s / M)
      ≤ Real.Gamma (x + s) ^ (1 - s / M) * (Real.Gamma (x + s) / y ^ M) ^ (s / M) :=
    mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hGxs.le _)
  have hsimp : Real.Gamma (x + s) ^ (1 - s / M) * (Real.Gamma (x + s) / y ^ M) ^ (s / M)
      = Real.Gamma (x + s) / y ^ s := by
    rw [Real.div_rpow hGxs.le (by positivity), ← Real.rpow_natCast y M, ← Real.rpow_mul hy.le,
      ← mul_div_assoc, ← Real.rpow_add hGxs]
    have h1 : (1 - s / M) + s / M = 1 := by ring
    have h2 : (M : ℝ) * (s / M) = s := by field_simp
    rw [h1, h2, Real.rpow_one]
  have hfinal : Real.Gamma x ≤ Real.Gamma (x + s) / y ^ s := (hkey.trans (hmono.trans_eq hsimp))
  rw [le_div_iff₀ (by positivity)] at hfinal
  exact hfinal

/-! ### The two normalizations differ by a geometric factor -/

/-- **The Gamma scale is dominated by the factorial scale.**  With `M = ⌈s⌉ + 1`,

`Γ(1 + s k) ≤ ((1 + M + s)^s)^k (k!)^s`. -/
theorem Gamma_le_pow_mul_factorial_rpow {s : ℝ} (hs : 0 < s) (M : ℕ) (hM : s < M) (k : ℕ) :
    Real.Gamma (1 + s * k) ≤ (((1 : ℝ) + M + s) ^ s) ^ k * (k.factorial : ℝ) ^ s := by
  induction k with
  | zero => simp
  | succ k IH =>
      have hxk : (0 : ℝ) < 1 + s * k := by positivity
      have hstep : (1 : ℝ) + s * ((k + 1 : ℕ) : ℝ) = (1 + s * k) + s := by push_cast; ring
      have hup := Gamma_add_le_mul_rpow hxk hs hM
      rw [hstep]
      refine hup.trans ?_
      have hfac : ((k + 1 : ℕ).factorial : ℝ) ^ s
          = (k.factorial : ℝ) ^ s * ((k : ℝ) + 1) ^ s := by
        rw [Nat.factorial_succ]
        push_cast
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf
      have hbase : (1 : ℝ) + s * k + M ≤ ((1 : ℝ) + M + s) * ((k : ℝ) + 1) := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        nlinarith
      have hpow : ((1 : ℝ) + s * k + M) ^ s ≤ (((1 : ℝ) + M + s) * ((k : ℝ) + 1)) ^ s :=
        Real.rpow_le_rpow (by positivity) hbase hs.le
      have hsplit : (((1 : ℝ) + M + s) * ((k : ℝ) + 1)) ^ s
          = ((1 : ℝ) + M + s) ^ s * ((k : ℝ) + 1) ^ s :=
        Real.mul_rpow (by positivity) (by positivity)
      calc Real.Gamma (1 + s * k) * ((1 : ℝ) + s * k + M) ^ s
          ≤ ((((1 : ℝ) + M + s) ^ s) ^ k * (k.factorial : ℝ) ^ s)
              * (((1 : ℝ) + M + s) ^ s * ((k : ℝ) + 1) ^ s) := by
            refine mul_le_mul IH (hpow.trans_eq hsplit) (by positivity) (by positivity)
        _ = (((1 : ℝ) + M + s) ^ s) ^ (k + 1) * (((k.factorial : ℝ) ^ s) * ((k : ℝ) + 1) ^ s) := by
            ring
        _ = (((1 : ℝ) + M + s) ^ s) ^ (k + 1) * ((k + 1 : ℕ).factorial : ℝ) ^ s := by
            rw [hfac]

/-- Finitely many exceptional indices are absorbed into the constant. -/
theorem exists_const_of_eventually {f g : ℕ → ℝ} {c₀ : ℝ} {N : ℕ} (hc₀ : 0 < c₀)
    (hf : ∀ k, 0 < f k) (hg : ∀ k, 0 ≤ g k)
    (h : ∀ k, N ≤ k → c₀ * g k ≤ f k) :
    ∃ c : ℝ, 0 < c ∧ ∀ k, c * g k ≤ f k := by
  classical
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  set d : ℝ := (Finset.range (N + 1)).inf' hne (fun k => f k / max 1 (g k)) with hd
  have hmaxpos : ∀ k : ℕ, (0 : ℝ) < max 1 (g k) := fun k =>
    lt_of_lt_of_le one_pos (le_max_left 1 _)
  have hdpos : 0 < d := by
    rw [hd, Finset.lt_inf'_iff]
    exact fun k _ => div_pos (hf k) (hmaxpos k)
  refine ⟨min c₀ d, lt_min hc₀ hdpos, fun k => ?_⟩
  by_cases hk : N ≤ k
  · calc min c₀ d * g k ≤ c₀ * g k :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hg k)
      _ ≤ f k := h k hk
  · have hkmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hle : min c₀ d ≤ f k / max 1 (g k) :=
      le_trans (min_le_right _ _) (by rw [hd]; exact Finset.inf'_le _ hkmem)
    calc min c₀ d * g k ≤ (f k / max 1 (g k)) * g k :=
        mul_le_mul_of_nonneg_right hle (hg k)
      _ ≤ (f k / max 1 (g k)) * max 1 (g k) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg (hf k).le (hmaxpos k).le)
      _ = f k := div_mul_cancel₀ _ (hmaxpos k).ne'

/-- **The factorial scale is dominated by the Gamma scale.**  There are `c, a > 0` with
`c a^k (k!)^s ≤ Γ(1 + s k)` for every `k`. -/
theorem exists_pow_mul_factorial_rpow_le_Gamma {s : ℝ} (hs : 0 < s) :
    ∃ c a : ℝ, 0 < c ∧ 0 < a ∧ ∀ k : ℕ,
      c * (a ^ k * (k.factorial : ℝ) ^ s) ≤ Real.Gamma (1 + s * k) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, s < M := ⟨⌈s⌉₊ + 1, by push_cast; linarith [Nat.le_ceil s]⟩
  set a : ℝ := (s / 2) ^ s with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos (by positivity) s
  set N : ℕ := ⌈2 * ((M : ℝ) - 1) / s⌉₊ with hN
  have hNle : 2 * ((M : ℝ) - 1) / s ≤ (N : ℝ) := Nat.le_ceil _
  -- the step inequality above the threshold
  have hstepbound : ∀ k : ℕ, N ≤ k →
      (s / 2) * ((k : ℝ) + 1) ≤ 1 + s * ((k : ℝ) + 1) - M := by
    intro k hk
    have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1 : 2 * ((M : ℝ) - 1) / s ≤ (k : ℝ) + 1 := by linarith
    have h2 : 2 * ((M : ℝ) - 1) ≤ ((k : ℝ) + 1) * s := by
      rw [div_le_iff₀ hs] at h1
      linarith
    linarith
  have hGN : 0 < Real.Gamma (1 + s * N) := Real.Gamma_pos_of_pos (by positivity)
  have hfacpos : ∀ m : ℕ, (0 : ℝ) < (m.factorial : ℝ) ^ s :=
    fun m => Real.rpow_pos_of_pos (by exact_mod_cast m.factorial_pos) s
  -- the induction above the threshold
  have key : ∀ j : ℕ, Real.Gamma (1 + s * N) * (a ^ j * ((N + j).factorial : ℝ) ^ s)
      ≤ ((N.factorial : ℝ) ^ s) * Real.Gamma (1 + s * ((N : ℝ) + j)) := by
    intro j
    induction j with
    | zero => simp; nlinarith [hGN, hfacpos N]
    | succ j IH =>
        have hkge : N ≤ N + j := Nat.le_add_right N j
        have hxpos : (0 : ℝ) < 1 + s * ((N : ℝ) + j) := by positivity
        have hbound := hstepbound (N + j) hkge
        have hcast : ((N + j : ℕ) : ℝ) = (N : ℝ) + j := by push_cast; ring
        rw [hcast] at hbound
        have hpos : (0 : ℝ) < (1 + s * ((N : ℝ) + j)) + s - M := by
          have : (0 : ℝ) < (s / 2) * (((N : ℝ) + j) + 1) := by positivity
          have heq : (1 + s * ((N : ℝ) + j)) + s - M = 1 + s * (((N : ℝ) + j) + 1) - M := by ring
          rw [heq]
          linarith
        have hlow := mul_rpow_le_Gamma_add (x := 1 + s * ((N : ℝ) + j)) hs hM hpos
        have hstepeq : (1 + s * ((N : ℝ) + j)) + s = 1 + s * ((N : ℝ) + (j + 1 : ℕ)) := by
          push_cast; ring
        have hgrow : (s / 2) ^ s * (((N : ℝ) + j) + 1) ^ s
            ≤ ((1 + s * ((N : ℝ) + j)) + s - M) ^ s := by
          have hbase : (s / 2) * (((N : ℝ) + j) + 1) ≤ (1 + s * ((N : ℝ) + j)) + s - M := by
            have heq : (1 + s * ((N : ℝ) + j)) + s - M = 1 + s * (((N : ℝ) + j) + 1) - M := by ring
            rw [heq]; linarith
          calc (s / 2) ^ s * (((N : ℝ) + j) + 1) ^ s
              = ((s / 2) * (((N : ℝ) + j) + 1)) ^ s :=
                (Real.mul_rpow (by positivity) (by positivity)).symm
            _ ≤ _ := Real.rpow_le_rpow (by positivity) hbase hs.le
        have hchain : Real.Gamma (1 + s * ((N : ℝ) + j)) * (a * (((N : ℝ) + j) + 1) ^ s)
            ≤ Real.Gamma (1 + s * ((N : ℝ) + (j + 1 : ℕ))) := by
          rw [← hstepeq]
          refine le_trans ?_ hlow
          rw [ha]
          exact mul_le_mul_of_nonneg_left hgrow (Real.Gamma_pos_of_pos hxpos).le
        have hfacsucc : ((N + (j + 1)).factorial : ℝ) ^ s
            = ((N + j).factorial : ℝ) ^ s * (((N : ℝ) + j) + 1) ^ s := by
          have hidx : N + (j + 1) = (N + j) + 1 := by omega
          rw [hidx, Nat.factorial_succ]
          push_cast
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          ring_nf
        have hmul : Real.Gamma (1 + s * N) * (a ^ j * ((N + j).factorial : ℝ) ^ s)
            * (a * (((N : ℝ) + j) + 1) ^ s)
            ≤ ((N.factorial : ℝ) ^ s) * Real.Gamma (1 + s * ((N : ℝ) + j))
              * (a * (((N : ℝ) + j) + 1) ^ s) :=
          mul_le_mul_of_nonneg_right IH (by positivity)
        calc Real.Gamma (1 + s * N) * (a ^ (j + 1) * ((N + (j + 1)).factorial : ℝ) ^ s)
            = Real.Gamma (1 + s * N) * (a ^ j * ((N + j).factorial : ℝ) ^ s)
                * (a * (((N : ℝ) + j) + 1) ^ s) := by rw [hfacsucc]; ring
          _ ≤ ((N.factorial : ℝ) ^ s) * Real.Gamma (1 + s * ((N : ℝ) + j))
                * (a * (((N : ℝ) + j) + 1) ^ s) := hmul
          _ = ((N.factorial : ℝ) ^ s)
                * (Real.Gamma (1 + s * ((N : ℝ) + j)) * (a * (((N : ℝ) + j) + 1) ^ s)) := by ring
          _ ≤ ((N.factorial : ℝ) ^ s) * Real.Gamma (1 + s * ((N : ℝ) + (j + 1 : ℕ))) :=
              mul_le_mul_of_nonneg_left hchain (hfacpos N).le
  -- transfer to all `k ≥ N` and absorb the finitely many exceptions
  set c₀ : ℝ := Real.Gamma (1 + s * N) / ((N.factorial : ℝ) ^ s * a ^ N) with hc₀def
  have hc₀ : 0 < c₀ := div_pos hGN (by positivity)
  have heventual : ∀ k : ℕ, N ≤ k →
      c₀ * (a ^ k * (k.factorial : ℝ) ^ s) ≤ Real.Gamma (1 + s * k) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hcast : ((N + j : ℕ) : ℝ) = (N : ℝ) + j := by push_cast; ring
    have hkey := key j
    rw [hc₀def, hcast, pow_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc Real.Gamma (1 + s * N) * (a ^ N * a ^ j * ((N + j).factorial : ℝ) ^ s)
        = a ^ N * (Real.Gamma (1 + s * N) * (a ^ j * ((N + j).factorial : ℝ) ^ s)) := by ring
      _ ≤ a ^ N * (((N.factorial : ℝ) ^ s) * Real.Gamma (1 + s * ((N : ℝ) + j))) :=
          mul_le_mul_of_nonneg_left hkey (pow_nonneg hapos.le N)
      _ = Real.Gamma (1 + s * ((N : ℝ) + j)) * ((N.factorial : ℝ) ^ s * a ^ N) := by ring
  obtain ⟨c, hc, hall⟩ := exists_const_of_eventually (f := fun k => Real.Gamma (1 + s * k))
    (g := fun k => a ^ k * (k.factorial : ℝ) ^ s) hc₀
    (fun k => Real.Gamma_pos_of_pos (by positivity))
    (fun k => by positivity) heventual
  exact ⟨c, a, hc, hapos, hall⟩

end GaloisForLFunctions.HTGeometry
