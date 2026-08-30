import GaloisForLFunctions.HTGeometry.RittFirstOrderForm

/-!
# A homogeneous base relation is Ritt's order-one form

Suppose the base carries a nonzero `u` with `ψ(u) = q^i · ρ^m · u` — an invariant differential of
weight `m` and eigenvalue `q^i` for the shift.  Then the element

`V = u · (d τ)^m · τ^{-i-m}`

of the ambient field is `σ`-invariant: the shift multiplies `u` by `q^i ρ^m`, the jet `d τ` by
`q/ρ`, and `τ` by `q`, and those three contributions cancel exactly at these exponents.  A
`σ`-invariant of a Ritt frame comes from the base, so `V = v` for some base `v`, and rearranging is

`(d τ)^m = (v/u) · τ^{i+m}`,

Ritt's order-one relation, as soon as `m ≠ 0`.  When `m = 0` the same computation gives
`τ^i = u/v`, and the logarithmic derivative turns that into `d τ = A·τ` whenever `i ≠ 0`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]

/-- **A homogeneous base relation gives Ritt's order-one form.** -/
theorem exists_rittForm_of_homogeneous_base_relation (Fr : RittFrame K L)
    {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    {u : K} (hu : u ≠ 0) {i m : ℤ} (him : i ≠ 0 ∨ m ≠ 0)
    (hrel : Fr.ψ u = q ^ i * Fr.ρ ^ m * u) :
    ∃ (r j : ℤ) (A : K), r ≠ 0 ∧ A ≠ 0 ∧ (Fr.d τ) ^ r = algebraMap K L A * τ ^ j := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hd := Fr.sigma_d_eq_of_shift hqconst hshift
  have huL : algebraMap K L u ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hu
  -- the invariant element
  set V : L := algebraMap K L u * (Fr.d τ) ^ m * τ ^ (-i - m) with hV
  have hV0 : V ≠ 0 :=
    mul_ne_zero (mul_ne_zero huL (zpow_ne_zero _ hdτ)) (zpow_ne_zero _ hτ)
  have hcancel : q ^ i * Fr.ρ ^ m * (q / Fr.ρ) ^ m * q ^ (-i - m) = 1 := by
    have h1 : (q / Fr.ρ) ^ m = q ^ m * (Fr.ρ ^ m)⁻¹ := by rw [div_zpow, div_eq_mul_inv]
    rw [h1, show q ^ i * Fr.ρ ^ m * (q ^ m * (Fr.ρ ^ m)⁻¹) * q ^ (-i - m)
      = (q ^ i * q ^ m * q ^ (-i - m)) * (Fr.ρ ^ m * (Fr.ρ ^ m)⁻¹) from by ring,
      mul_inv_cancel₀ (zpow_ne_zero _ hρ0), mul_one, ← zpow_add₀ hq, ← zpow_add₀ hq]
    simp
  have hfix : Fr.σ V = V := by
    rw [hV, map_mul, map_mul, map_zpow₀, map_zpow₀, hd, hshift, Fr.comp, hrel,
      mul_zpow, mul_zpow, ← map_zpow₀, ← map_zpow₀]
    calc algebraMap K L (q ^ i * Fr.ρ ^ m * u) * (algebraMap K L ((q / Fr.ρ) ^ m) * Fr.d τ ^ m)
          * (algebraMap K L (q ^ (-i - m)) * τ ^ (-i - m))
        = algebraMap K L (q ^ i * Fr.ρ ^ m * (q / Fr.ρ) ^ m * q ^ (-i - m))
            * (algebraMap K L u * Fr.d τ ^ m * τ ^ (-i - m)) := by
          simp only [map_mul]
          ring
      _ = V := by rw [hcancel, map_one, one_mul, hV]
  obtain ⟨v, hv⟩ := Fr.fixed V hfix
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact hV0 hv.symm
  by_cases hm : m = 0
  · -- weight zero: the relation is a power of the linearizer
    have hi : i ≠ 0 := him.resolve_right (by simpa using hm)
    rw [hV, hm] at hv
    simp only [zpow_zero, mul_one, sub_zero] at hv
    have hpow : τ ^ (-i) = algebraMap K L (v / u) := by
      rw [map_div₀]
      field_simp
      linear_combination -hv
    -- reduce to a positive exponent
    obtain ⟨n, hn, w, hw0, hw⟩ :
        ∃ n : ℕ, 0 < n ∧ ∃ w : K, w ≠ 0 ∧ τ ^ n = algebraMap K L w := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact ⟨(-i).toNat, by omega, v / u, div_ne_zero hv0 hu,
          by rw [← hpow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]⟩
      · refine ⟨i.toNat, by omega, (v / u)⁻¹, inv_ne_zero (div_ne_zero hv0 hu), ?_⟩
        rw [map_inv₀, ← hpow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, inv_inv]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    have hkK : ((k : K) + 1) ≠ 0 := by
      rw [show ((k : K) + 1) = ((k + 1 : ℕ) : K) by push_cast; ring]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hwL : algebraMap K L w ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hw0
    have hcast : algebraMap K L ((k : K) + 1) = (k : L) + 1 := by
      rw [map_add, map_natCast, map_one]
    have hderiv : algebraMap K L (Fr.dK w) = ((k : L) + 1) * τ ^ k * Fr.d τ := by
      rw [← Fr.d_base, ← hw, Fr.d_pow_succ]
    have hkey : algebraMap K L ((k : K) + 1) * algebraMap K L w * Fr.d τ
        = algebraMap K L (Fr.dK w) * τ := by
      calc algebraMap K L ((k : K) + 1) * algebraMap K L w * Fr.d τ
          = ((k : L) + 1) * τ ^ (k + 1) * Fr.d τ := by rw [← hw, hcast]
        _ = (((k : L) + 1) * τ ^ k * Fr.d τ) * τ := by ring
        _ = algebraMap K L (Fr.dK w) * τ := by rw [hderiv]
    refine ⟨1, 1, Fr.dK w / (((k : K) + 1) * w), one_ne_zero, ?_, ?_⟩
    · intro h0
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · rw [h0, map_zero, zero_mul] at hkey
        exact hdτ (by
          have hkL : algebraMap K L ((k : K) + 1) ≠ 0 :=
            (map_ne_zero_iff _ (algebraMap K L).injective).mpr hkK
          rcases mul_eq_zero.mp hkey with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · exact absurd h' hkL
            · exact absurd h' hwL
          · exact h)
      · rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hkK
        · exact absurd h hw0
    · rw [zpow_one, zpow_one, map_div₀, map_mul]
      have hkL : algebraMap K L ((k : K) + 1) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K L).injective).mpr hkK
      field_simp
      linear_combination hkey
  · -- positive weight: rearranging is the Ritt form
    refine ⟨m, i + m, v / u, hm, div_ne_zero hv0 hu, ?_⟩
    rw [hV] at hv
    have hvv : algebraMap K L v * τ ^ (i + m) = algebraMap K L u * Fr.d τ ^ m := by
      rw [hv, mul_assoc, ← zpow_add₀ hτ]
      simp
    rw [map_div₀]
    field_simp
    linear_combination -hvv
