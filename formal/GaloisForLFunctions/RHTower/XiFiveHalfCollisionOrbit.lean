import GaloisForLFunctions.RHTower.XiAffineCollisionControl
import GaloisForLFunctions.RHTower.Reflection

/-!
# The five-half affine collision orbit

The strict-right angular source of route HB carries the factor `ξ(5ρ/2 − 1)`.  Above `Re ρ = 2/3`
the map `ρ ↦ 5ρ/2 − 1` increases real parts geometrically, so iterating it along a chain of
collisions reaches the zero-free region `Re ≥ 4/5` in finitely many steps: every strict-right zero
with `Re ρ > 2/3` has a descendant strict-right zero, with no smaller real part, at which both the
five-half and the three-half factors are nonzero.  Below `Re ρ < 8/15` the reflected partner
`2 − 5ρ̄/2 = 1 − conj(5ρ/2 − 1)` of a colliding zero is a zero above `2/3`, and a three-half
collision moves to `3ρ/2`, also above `2/3`.  Hence outside the band `[8/15, 2/3]` both factors can
be made nonzero simultaneously, and a strict-right zero without a five-half-collision-free
descendant has its whole collision orbit trapped in that band or lands on the real part `3/5`,
whose partner lies on the critical line.
-/

namespace RHTower
open Complex

noncomputable section

theorem re_five_half_sub_one' (ρ : ℂ) : (5 * ρ / 2 - 1).re = 5 * ρ.re / 2 - 1 := by
  simp [Complex.div_ofNat_re, Complex.mul_re]

theorem im_five_half_sub_one' (ρ : ℂ) : (5 * ρ / 2 - 1).im = 5 * ρ.im / 2 := by
  simp [Complex.div_ofNat_im, Complex.mul_im]

theorem re_three_half' (ρ : ℂ) : (3 * ρ / 2).re = 3 * ρ.re / 2 := by
  simp [Complex.div_ofNat_re, Complex.mul_re]

theorem im_three_half' (ρ : ℂ) : (3 * ρ / 2).im = 3 * ρ.im / 2 := by
  simp [Complex.div_ofNat_im, Complex.mul_im]

/-! ## The ascent -/

/-- The five-half ascent orbit `ρ ↦ 5ρ/2 − 1`. -/
def xiFiveHalfAscent (ρ : ℂ) : ℕ → ℂ
  | 0 => ρ
  | n + 1 => 5 * xiFiveHalfAscent ρ n / 2 - 1

theorem xiFiveHalfAscent_zero (ρ : ℂ) : xiFiveHalfAscent ρ 0 = ρ := rfl

theorem xiFiveHalfAscent_succ (ρ : ℂ) (n : ℕ) :
    xiFiveHalfAscent ρ (n + 1) = 5 * xiFiveHalfAscent ρ n / 2 - 1 := rfl

theorem xiFiveHalfAscent_re (ρ : ℂ) (n : ℕ) :
    (xiFiveHalfAscent ρ n).re = 2 / 3 + (5 / 2) ^ n * (ρ.re - 2 / 3) := by
  induction n with
  | zero => simp [xiFiveHalfAscent]
  | succ n ih =>
    rw [xiFiveHalfAscent_succ, re_five_half_sub_one', ih]
    ring

theorem xiFiveHalfAscent_im (ρ : ℂ) (n : ℕ) :
    (xiFiveHalfAscent ρ n).im = (5 / 2) ^ n * ρ.im := by
  induction n with
  | zero => simp [xiFiveHalfAscent]
  | succ n ih =>
    rw [xiFiveHalfAscent_succ, im_five_half_sub_one', ih]
    ring

/-- Zeros propagate along the ascent as long as every five-half value vanishes. -/
theorem xi_xiFiveHalfAscent_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) (n : ℕ)
    (h : ∀ m < n, xi (5 * xiFiveHalfAscent ρ m / 2 - 1) = 0) :
    xi (xiFiveHalfAscent ρ n) = 0 := by
  cases n with
  | zero => simpa [xiFiveHalfAscent] using hρ
  | succ n => rw [xiFiveHalfAscent_succ]; exact h n (Nat.lt_succ_self n)

/-- Above `2/3` the ascent reaches the zero-free region `Re ≥ 4/5`. -/
theorem exists_xiFiveHalfAscent_five_half_ne_zero {ρ : ℂ} (h : 2 / 3 < ρ.re) :
    ∃ n, xi (5 * xiFiveHalfAscent ρ n / 2 - 1) ≠ 0 := by
  have hpos : 0 < ρ.re - 2 / 3 := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((2 / 15) / (ρ.re - 2 / 3)) (by norm_num : (1:ℝ) < 5 / 2)
  refine ⟨n, xi_five_half_sub_one_ne_zero_of_re ?_⟩
  rw [xiFiveHalfAscent_re]
  have := (div_lt_iff₀ hpos).mp hn
  linarith

/-- **Five-half ascent.** Every strict-right zero above `2/3` has a descendant strict-right zero,
with no smaller real part, at which the five-half and the three-half factors are both nonzero. -/
theorem exists_xi_zero_five_half_ne_zero_of_two_thirds_lt {ρ : ℂ} (hρ : xi ρ = 0)
    (h1 : 2 / 3 < ρ.re) (hi : ρ.im ≠ 0) :
    ∃ ρ' : ℂ, xi ρ' = 0 ∧ ρ.re ≤ ρ'.re ∧ ρ'.re < 1 ∧ ρ'.im ≠ 0 ∧
      xi (5 * ρ' / 2 - 1) ≠ 0 ∧ xi (3 * ρ' / 2) ≠ 0 := by
  classical
  have hex := exists_xiFiveHalfAscent_five_half_ne_zero h1
  have hzero : xi (xiFiveHalfAscent ρ (Nat.find hex)) = 0 :=
    xi_xiFiveHalfAscent_eq_zero hρ _ (fun m hm => not_not.mp (Nat.find_min hex hm))
  have hge : ρ.re ≤ (xiFiveHalfAscent ρ (Nat.find hex)).re := by
    rw [xiFiveHalfAscent_re]
    have : (1:ℝ) ≤ (5 / 2) ^ Nat.find hex := one_le_pow₀ (by norm_num)
    nlinarith
  refine ⟨xiFiveHalfAscent ρ (Nat.find hex), hzero, hge, ?_, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hge1
    exact xi_ne_zero_of_one_le_re (le_of_not_gt hge1) hzero
  · rw [xiFiveHalfAscent_im]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hi
  · exact xi_three_half_ne_zero_of_re (by linarith)

/-! ## The reflected partner -/

/-- The reflected five-half partner `2 − 5ρ̄/2 = 1 − conj(5ρ/2 − 1)`. -/
def xiFiveHalfReflect (ρ : ℂ) : ℂ := 2 - 5 * (starRingEnd ℂ) ρ / 2

theorem xiFiveHalfReflect_eq (ρ : ℂ) :
    xiFiveHalfReflect ρ = 1 - (starRingEnd ℂ) (5 * ρ / 2 - 1) := by
  simp only [xiFiveHalfReflect, map_sub, map_div₀, map_mul, map_ofNat, map_one]
  ring

theorem xiFiveHalfReflect_re (ρ : ℂ) : (xiFiveHalfReflect ρ).re = 2 - 5 * ρ.re / 2 := by
  simp [xiFiveHalfReflect, Complex.div_ofNat_re, Complex.mul_re]

theorem xiFiveHalfReflect_im (ρ : ℂ) : (xiFiveHalfReflect ρ).im = 5 * ρ.im / 2 := by
  simp [xiFiveHalfReflect, Complex.div_ofNat_im, Complex.mul_im]
  ring

theorem xi_xiFiveHalfReflect_eq_zero {ρ : ℂ} (h : xi (5 * ρ / 2 - 1) = 0) :
    xi (xiFiveHalfReflect ρ) = 0 := by
  rw [xiFiveHalfReflect_eq, xi_one_sub, xi_conj, h, map_zero]

/-- **Band reduction.** Every strict-right zero with real part outside `[8/15, 2/3]` has a
descendant strict-right zero at which the five-half and three-half factors are both nonzero. -/
theorem exists_xi_zero_five_half_three_half_ne_zero_of_not_mem_band {ρ : ℂ} (hρ : xi ρ = 0)
    (h1 : 1 / 2 < ρ.re) (hi : ρ.im ≠ 0) (hband : ρ.re < 8 / 15 ∨ 2 / 3 < ρ.re) :
    ∃ ρ' : ℂ, xi ρ' = 0 ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ ρ'.im ≠ 0 ∧
      xi (5 * ρ' / 2 - 1) ≠ 0 ∧ xi (3 * ρ' / 2) ≠ 0 := by
  rcases hband with hlo | hhi
  · by_cases hc : xi (5 * ρ / 2 - 1) = 0
    · have hz := xi_xiFiveHalfReflect_eq_zero hc
      have hre : 2 / 3 < (xiFiveHalfReflect ρ).re := by rw [xiFiveHalfReflect_re]; linarith
      have him : (xiFiveHalfReflect ρ).im ≠ 0 := by
        rw [xiFiveHalfReflect_im]
        exact div_ne_zero (mul_ne_zero (by norm_num) hi) (by norm_num)
      obtain ⟨ρ', h0, hge, hlt1, hi', h5, h3⟩ :=
        exists_xi_zero_five_half_ne_zero_of_two_thirds_lt hz hre him
      exact ⟨ρ', h0, by linarith, hlt1, hi', h5, h3⟩
    · by_cases hc3 : xi (3 * ρ / 2) = 0
      · obtain ⟨-, h34, -, -⟩ := xi_three_half_collision_partner h1 hc3
        have hre3 : 2 / 3 < (3 * ρ / 2).re := by linarith
        have him3 : (3 * ρ / 2).im ≠ 0 := by
          rw [im_three_half']
          exact div_ne_zero (mul_ne_zero (by norm_num) hi) (by norm_num)
        obtain ⟨ρ', h0, hge, hlt1, hi', h5, h3⟩ :=
          exists_xi_zero_five_half_ne_zero_of_two_thirds_lt hc3 hre3 him3
        exact ⟨ρ', h0, by linarith, hlt1, hi', h5, h3⟩
      · have hlt1 : ρ.re < 1 := by
          by_contra hge1
          exact xi_ne_zero_of_one_le_re (le_of_not_gt hge1) hρ
        exact ⟨ρ, hρ, h1, hlt1, hi, hc, hc3⟩
  · obtain ⟨ρ', h0, hge, hlt1, hi', h5, h3⟩ :=
      exists_xi_zero_five_half_ne_zero_of_two_thirds_lt hρ hhi hi
    exact ⟨ρ', h0, by linarith, hlt1, hi', h5, h3⟩

/-! ## The collision orbit inside the band -/

/-- The five-half collision step on strict-right zeros: direct above `3/5`, reflected below. -/
def xiFiveHalfStep (ρ : ℂ) : ℂ :=
  if 3 / 5 < ρ.re then 5 * ρ / 2 - 1 else xiFiveHalfReflect ρ

/-- The collision orbit. -/
def xiFiveHalfOrbit (ρ : ℂ) : ℕ → ℂ
  | 0 => ρ
  | n + 1 => xiFiveHalfStep (xiFiveHalfOrbit ρ n)

theorem xiFiveHalfOrbit_zero (ρ : ℂ) : xiFiveHalfOrbit ρ 0 = ρ := rfl

theorem xiFiveHalfOrbit_succ (ρ : ℂ) (n : ℕ) :
    xiFiveHalfOrbit ρ (n + 1) = xiFiveHalfStep (xiFiveHalfOrbit ρ n) := rfl

theorem xiFiveHalfStep_im (ρ : ℂ) : (xiFiveHalfStep ρ).im = 5 * ρ.im / 2 := by
  unfold xiFiveHalfStep
  split_ifs
  · exact im_five_half_sub_one' ρ
  · exact xiFiveHalfReflect_im ρ

theorem xiFiveHalfOrbit_im (ρ : ℂ) (n : ℕ) :
    (xiFiveHalfOrbit ρ n).im = (5 / 2) ^ n * ρ.im := by
  induction n with
  | zero => simp [xiFiveHalfOrbit]
  | succ n ih => rw [xiFiveHalfOrbit_succ, xiFiveHalfStep_im, ih]; ring

theorem xi_xiFiveHalfStep_eq_zero {ρ : ℂ} (h : xi (5 * ρ / 2 - 1) = 0) :
    xi (xiFiveHalfStep ρ) = 0 := by
  unfold xiFiveHalfStep
  split_ifs
  · exact h
  · exact xi_xiFiveHalfReflect_eq_zero h

/-- Off the real part `3/5` the step keeps strict-right points strict-right. -/
theorem xiFiveHalfStep_re_gt_half {ρ : ℂ} (h : ρ.re ≠ 3 / 5) :
    1 / 2 < (xiFiveHalfStep ρ).re := by
  unfold xiFiveHalfStep
  split_ifs with h'
  · rw [re_five_half_sub_one']; linarith
  · rw [xiFiveHalfReflect_re]
    have : ρ.re < 3 / 5 := lt_of_le_of_ne (not_lt.mp h') h
    linarith

/-- **Trapped-orbit dichotomy.** A strict-right nonreal zero either has a strict-right descendant
zero at which the five-half factor is nonzero, or its collision orbit lands on the real part `3/5`
(whose five-half partner lies on the critical line), or the whole collision orbit consists of zeros
with real parts trapped in `[8/15, 2/3]`. -/
theorem xiFiveHalf_trapped_orbit_dichotomy {ρ : ℂ} (hρ : xi ρ = 0) (h1 : 1 / 2 < ρ.re)
    (hi : ρ.im ≠ 0) :
    (∃ ρ' : ℂ, xi ρ' = 0 ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ ρ'.im ≠ 0 ∧ xi (5 * ρ' / 2 - 1) ≠ 0) ∨
    (∃ n, (xiFiveHalfOrbit ρ n).re = 3 / 5) ∨
    (∀ n, xi (xiFiveHalfOrbit ρ n) = 0 ∧ 8 / 15 ≤ (xiFiveHalfOrbit ρ n).re ∧
      (xiFiveHalfOrbit ρ n).re ≤ 2 / 3) := by
  by_cases hesc : ∃ ρ' : ℂ, xi ρ' = 0 ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ ρ'.im ≠ 0 ∧
      xi (5 * ρ' / 2 - 1) ≠ 0
  · exact Or.inl hesc
  by_cases h35 : ∃ n, (xiFiveHalfOrbit ρ n).re = 3 / 5
  · exact Or.inr (Or.inl h35)
  refine Or.inr (Or.inr ?_)
  push Not at hesc h35
  -- a strict-right zero outside the band would produce an escape
  have hband : ∀ σ : ℂ, xi σ = 0 → 1 / 2 < σ.re → σ.im ≠ 0 →
      8 / 15 ≤ σ.re ∧ σ.re ≤ 2 / 3 := by
    intro σ hσ hσ1 hσi
    by_contra hnot
    have hout : σ.re < 8 / 15 ∨ 2 / 3 < σ.re := by
      by_contra hcon
      push Not at hcon
      exact hnot ⟨hcon.1, hcon.2⟩
    obtain ⟨ρ', h0, hr1, hr2, hi', h5, -⟩ :=
      exists_xi_zero_five_half_three_half_ne_zero_of_not_mem_band hσ hσ1 hσi hout
    exact h5 (hesc ρ' h0 hr1 hr2 hi')
  intro n
  induction n with
  | zero =>
    refine ⟨hρ, ?_⟩
    simpa [xiFiveHalfOrbit] using hband ρ hρ h1 hi
  | succ n ih =>
    obtain ⟨hz, hlo, hhi⟩ := ih
    have hi' : (xiFiveHalfOrbit ρ n).im ≠ 0 := by
      rw [xiFiveHalfOrbit_im]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hi
    have hr1 : 1 / 2 < (xiFiveHalfOrbit ρ n).re := by linarith
    have hlt1 : (xiFiveHalfOrbit ρ n).re < 1 := by linarith
    -- the orbit point collides, else it would be an escape
    have hcol : xi (5 * xiFiveHalfOrbit ρ n / 2 - 1) = 0 := by
      by_contra hne
      exact hne (hesc _ hz hr1 hlt1 hi')
    have hz' : xi (xiFiveHalfOrbit ρ (n + 1)) = 0 := by
      rw [xiFiveHalfOrbit_succ]
      exact xi_xiFiveHalfStep_eq_zero hcol
    have hr1' : 1 / 2 < (xiFiveHalfOrbit ρ (n + 1)).re := by
      rw [xiFiveHalfOrbit_succ]
      exact xiFiveHalfStep_re_gt_half (h35 n)
    have hi'' : (xiFiveHalfOrbit ρ (n + 1)).im ≠ 0 := by
      rw [xiFiveHalfOrbit_im]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hi
    exact ⟨hz', hband _ hz' hr1' hi''⟩

end
end RHTower
