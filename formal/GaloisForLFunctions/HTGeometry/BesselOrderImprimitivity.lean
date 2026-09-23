import GaloisForLFunctions.HTGeometry.BesselOrderRiccati
import GaloisForLFunctions.HTGeometry.RatFuncShiftSquareOrbit

/-!
# The order module of the Bessel order operator is not imprimitive

Imprimitivity of the rank-two difference module is the existence of `e, p ∈ ℂ(X)`, `p ≠ 0`, with

`(E) σe = e/p + 2b`,  `(P) p·σp = 1 + b·e + b²·p`,  `b = c·(X+1)`, `c ≠ 0`,

`e` and `p` being the symmetric functions of the two Riccati ratios.  There are none.

The proof is global.  The discriminant `Δ = e² − 4p` satisfies `σΔ·p² = Δ`, so its order is even at
every point — descend each integer orbit from where `Δ` has no zeros or poles — hence `Δ` is a
square and the two ratios `r₁, r₂ = (e ± k)/2` are themselves rational.  The pairs `{σr₁, σr₂}` and
`{b + 1/r₁, b + 1/r₂}` have the same sum and product, so they coincide; the identity assignment
makes `r₁` a rational solution of the Bessel Riccati equation, which is refuted, and the swap
assignment is refuted at infinity, because the ratio of degree `−1` cannot be the shift of a
function of degree `+1`.

* `intDegree_add_eq_of_lt`, `ratShift_eq_fieldShiftRatShift`;
* `no_imprimitive_pair` — the theorem.
-/

namespace GaloisForLFunctions

namespace HTGeometry

noncomputable section

open Polynomial

/-- **The strict ultrametric equality for the degree at infinity.** -/
theorem intDegree_add_eq_of_lt {K : Type*} [Field K] {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y.intDegree < x.intDegree) :
    x + y ≠ 0 ∧ (x + y).intDegree = x.intDegree := by
  have hne : x + y ≠ 0 := by
    intro h0
    have hxy : y = -x := by linear_combination h0
    rw [hxy, RatFunc.intDegree_neg] at h
    exact lt_irrefl _ h
  refine ⟨hne, le_antisymm ?_ ?_⟩
  · have := RatFunc.intDegree_add_le hy hne
    omega
  · have hback : x = (x + y) + (-y) := by ring
    have hle := RatFunc.intDegree_add_le (neg_ne_zero.mpr hy) (by rw [← hback]; exact hx)
    rw [← hback, RatFunc.intDegree_neg] at hle
    omega

/-- The two constructions of the unit shift agree. -/
theorem ratShift_eq_fieldShiftRatShift (r : RatFunc ℂ) :
    ratShift r = FieldShift.ratShift r := by
  have hQeq : r = algebraMap ℂ[X] (RatFunc ℂ) r.num / algebraMap ℂ[X] (RatFunc ℂ) r.denom :=
    (RatFunc.num_div_denom r).symm
  conv_lhs => rw [hQeq]
  conv_rhs => rw [hQeq]
  rw [map_div₀, map_div₀, ratShift_algebraMap, ratShift_algebraMap,
    FieldShift.ratShift_algebraMap, FieldShift.ratShift_algebraMap]

/-- The Riccati coefficient `b = c·(X+1)` of the Bessel order recurrence. -/
def besselB (c : ℂ) : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (C c * (X + C 1))

theorem natDegree_besselPoly {c : ℂ} (hc : c ≠ 0) :
    (C c * (X + C 1) : Polynomial ℂ).natDegree = 1 := by
  rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X_add_C]

theorem besselB_ne_zero {c : ℂ} (hc : c ≠ 0) : besselB c ≠ 0 := by
  rw [besselB]
  intro h0
  have hz : (C c * (X + C 1) : Polynomial ℂ) = 0 :=
    RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero])
  have hd := natDegree_besselPoly hc
  rw [hz, Polynomial.natDegree_zero] at hd
  exact absurd hd (by norm_num)

theorem intDegree_besselB {c : ℂ} (hc : c ≠ 0) : (besselB c).intDegree = 1 := by
  rw [besselB, RatFunc.intDegree_polynomial, natDegree_besselPoly hc]
  rfl

theorem intDegree_two : ((2 : RatFunc ℂ)).intDegree = 0 := by
  have h : (2 : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) 2 := by
    simpa using (map_ofNat (algebraMap (Polynomial ℂ) (RatFunc ℂ)) 2).symm
  rw [h, RatFunc.intDegree_polynomial]
  simp

/-- **The order module of the Bessel order operator is not imprimitive.** -/
theorem no_imprimitive_pair {c : ℂ} (hc : c ≠ 0) {e p : RatFunc ℂ} (hp : p ≠ 0)
    (hE : ratShift e = e / p + 2 * besselB c)
    (hP : p * ratShift p = 1 + besselB c * e + besselB c ^ (2 : ℕ) * p) : False := by
  set b : RatFunc ℂ := besselB c with hbdef
  have hb0 : b ≠ 0 := besselB_ne_zero hc
  have hbdeg : b.intDegree = 1 := intDegree_besselB hc
  have h2 : (2 : RatFunc ℂ) ≠ 0 := two_ne_zero
  -- the Riccati obstruction, in the form used four times below
  have hriccati : ∀ r : RatFunc ℂ, r ≠ 0 → ratShift r = b + 1 / r → False := by
    intro r hr hrs
    refine orderBesselRiccati_no_ratFunc_solution hc ⟨r, ?_⟩
    have hbb : (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (C c * (X + C 1)) = b := rfl
    rw [hrs, hbb]
    field_simp
    ring
  -- `e` is nonzero
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_div, zero_add] at hE
    rcases mul_eq_zero.mp hE.symm with h | h
    · exact h2 h
    · exact hb0 h
  -- the shifted equations, solved
  have hsp : ratShift p = (1 + b * e + b ^ (2 : ℕ) * p) / p := by
    field_simp
    linear_combination hP
  have h4s : ratShift (4 : RatFunc ℂ) = 4 := by simpa using map_ofNat ratShift 4
  have h2s : ratShift (2 : RatFunc ℂ) = 2 := by simpa using map_ofNat ratShift 2
  -- the discriminant identity
  have hkey : ratShift (e ^ (2 : ℕ) - 4 * p) * p ^ (2 : ℕ) = e ^ (2 : ℕ) - 4 * p := by
    rw [map_sub, map_pow, map_mul, hE, hsp, h4s]
    field_simp
    ring
  -- the discriminant is nonzero
  have hD0 : e ^ (2 : ℕ) - 4 * p ≠ 0 := by
    intro h0
    have hep : e ^ (2 : ℕ) = 4 * p := by linear_combination h0
    have he2 : e / 2 ≠ 0 := div_ne_zero he0 h2
    refine hriccati (e / 2) he2 ?_
    rw [map_div₀, hE, h2s]
    field_simp
    linear_combination hep
  -- the discriminant is a square
  have hsq : IsSquare (e ^ (2 : ℕ) - 4 * p) := by
    refine isSquare_of_ratShift_mul_sq hD0 hp ?_
    rw [← ratShift_eq_fieldShiftRatShift]
    exact hkey
  obtain ⟨k, hk⟩ := hsq
  have hkk : e ^ (2 : ℕ) - k * k = 4 * p := by linear_combination hk
  -- the two Riccati ratios
  set r₁ : RatFunc ℂ := (e + k) / 2 with hr₁def
  set r₂ : RatFunc ℂ := (e - k) / 2 with hr₂def
  have hsum : r₁ + r₂ = e := by rw [hr₁def, hr₂def]; field_simp; ring
  have hprod : r₁ * r₂ = p := by
    rw [hr₁def, hr₂def]
    field_simp
    linear_combination hkk
  have hr₁0 : r₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact hp hprod.symm
  have hr₂0 : r₂ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact hp hprod.symm
  -- degrees at infinity
  have hsD : ratShift (e ^ (2 : ℕ) - 4 * p) ≠ 0 := fun h0 =>
    hD0 (ratShift_injective (by rw [h0, map_zero]))
  have hsp0 : ratShift p ≠ 0 := fun h0 => hp (ratShift_injective (by rw [h0, map_zero]))
  have hpdeg : p.intDegree = 0 := by
    have h1 := congrArg RatFunc.intDegree hkey
    rw [RatFunc.intDegree_mul hsD (pow_ne_zero 2 hp), intDegree_ratShift,
      show p ^ (2 : ℕ) = p * p from sq p, RatFunc.intDegree_mul hp hp] at h1
    omega
  have h2bdeg : ((2 : RatFunc ℂ) * b).intDegree = 1 := by
    rw [RatFunc.intDegree_mul h2 hb0, intDegree_two, hbdeg, zero_add]
  have hedeg : e.intDegree = 1 := by
    have hepdiv : (e / p).intDegree = e.intDegree := by
      rw [RatFunc.intDegree_div he0 hp, hpdeg, sub_zero]
    have hge : 1 ≤ e.intDegree := by
      by_contra hlt
      push Not at hlt
      obtain ⟨hne, hdeg⟩ := intDegree_add_eq_of_lt (mul_ne_zero h2 hb0) (div_ne_zero he0 hp)
        (by omega)
      have hh := congrArg RatFunc.intDegree hE
      rw [intDegree_ratShift, add_comm (e / p), hdeg, h2bdeg] at hh
      omega
    by_contra hne1
    have hgt : 1 < e.intDegree := by omega
    have hb2p : (b ^ (2 : ℕ) * p).intDegree = 2 := by
      rw [RatFunc.intDegree_mul (pow_ne_zero 2 hb0) hp, show b ^ (2 : ℕ) = b * b from sq b,
        RatFunc.intDegree_mul hb0 hb0, hbdeg, hpdeg]
      norm_num
    have hone : ((1 : RatFunc ℂ)).intDegree = 0 := by simp
    obtain ⟨hne1', hdeg1⟩ :=
      intDegree_add_eq_of_lt (x := b ^ (2 : ℕ) * p) (y := 1) (mul_ne_zero (pow_ne_zero 2 hb0) hp)
        one_ne_zero (by rw [hone, hb2p]; norm_num)
    have hbe : (b * e).intDegree = 1 + e.intDegree := by
      rw [RatFunc.intDegree_mul hb0 he0, hbdeg]
    obtain ⟨hne2, hdeg2⟩ :=
      intDegree_add_eq_of_lt (x := b * e) (y := b ^ (2 : ℕ) * p + 1) (mul_ne_zero hb0 he0) hne1'
        (by rw [hdeg1, hb2p, hbe]; omega)
    have hPP : (1 : RatFunc ℂ) + b * e + b ^ (2 : ℕ) * p = b * e + (b ^ (2 : ℕ) * p + 1) := by ring
    have hlhs : (p * ratShift p).intDegree = 0 := by
      rw [RatFunc.intDegree_mul hp hsp0, intDegree_ratShift, hpdeg]
      norm_num
    have hh := congrArg RatFunc.intDegree hP
    rw [hlhs, hPP, hdeg2, hbe] at hh
    omega
  -- the two ratios have degrees `1` and `-1`
  have hrsum : r₁.intDegree + r₂.intDegree = 0 := by
    have h1 := congrArg RatFunc.intDegree hprod
    rw [RatFunc.intDegree_mul hr₁0 hr₂0, hpdeg] at h1
    omega
  have hrcase : (r₁.intDegree = 1 ∧ r₂.intDegree = -1)
      ∨ (r₂.intDegree = 1 ∧ r₁.intDegree = -1) := by
    rcases lt_trichotomy r₁.intDegree r₂.intDegree with h | h | h
    · obtain ⟨_, hd⟩ := intDegree_add_eq_of_lt hr₂0 hr₁0 h
      have hde : e.intDegree = r₂.intDegree := by rw [← hsum, add_comm]; exact hd
      right
      constructor <;> omega
    · exfalso
      have hle := RatFunc.intDegree_add_le hr₂0 (by rw [hsum]; exact he0)
      rw [hsum] at hle
      omega
    · obtain ⟨_, hd⟩ := intDegree_add_eq_of_lt hr₁0 hr₂0 h
      have hde : e.intDegree = r₁.intDegree := by rw [← hsum]; exact hd
      left
      constructor <;> omega
  -- the two pairs coincide
  have hsum' : (b + 1 / r₁) + (b + 1 / r₂) = ratShift r₁ + ratShift r₂ := by
    have hh : ratShift r₁ + ratShift r₂ = ratShift e := by rw [← map_add, hsum]
    rw [hh, hE, ← hprod, ← hsum]
    field_simp
    ring
  have hprod' : (b + 1 / r₁) * (b + 1 / r₂) = ratShift r₁ * ratShift r₂ := by
    have hh : ratShift r₁ * ratShift r₂ = ratShift p := by rw [← map_mul, hprod]
    rw [hh, hsp, ← hprod, ← hsum]
    field_simp
    ring
  have hroot : (ratShift r₁ - (b + 1 / r₁)) * (ratShift r₁ - (b + 1 / r₂)) = 0 := by
    linear_combination (-(ratShift r₁)) * hsum' + hprod'
  rcases mul_eq_zero.mp hroot with h | h
  · exact hriccati r₁ hr₁0 (by linear_combination h)
  · have hswap1 : ratShift r₁ = b + 1 / r₂ := by linear_combination h
    have hswap2 : ratShift r₂ = b + 1 / r₁ := by linear_combination -hsum' - h
    rcases hrcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hinv : (1 / r₁).intDegree = -1 := by
        rw [one_div, RatFunc.intDegree_inv, h1]
      obtain ⟨_, hd⟩ := intDegree_add_eq_of_lt hb0 (one_div_ne_zero hr₁0)
        (by rw [hinv, hbdeg]; norm_num)
      have hh := congrArg RatFunc.intDegree hswap2
      rw [intDegree_ratShift, hd, hbdeg] at hh
      omega
    · have hinv : (1 / r₂).intDegree = -1 := by
        rw [one_div, RatFunc.intDegree_inv, h1]
      obtain ⟨_, hd⟩ := intDegree_add_eq_of_lt hb0 (one_div_ne_zero hr₂0)
        (by rw [hinv, hbdeg]; norm_num)
      have hh := congrArg RatFunc.intDegree hswap1
      rw [intDegree_ratShift, hd, hbdeg] at hh
      omega

end

end HTGeometry

end GaloisForLFunctions
