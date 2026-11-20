import GaloisForLFunctions.FamilyContinuationTheory.TheBudgetInTheTwistExponent

/-!
# Cyclotomic Gauss-monomial parity, reflection-Hölder duality gap, planted dispersion saturation, and twist-coupling obstructions

Four structural obstructions govern higher-order cyclotomic extensions, higher-moment reflection
duality, arbitrary-weight multilinear character dispersion, and coherent twist-averaging couplings
in `FamilyContinuationTheory`:

* **Cyclotomic Gauss-monomial index conservation (`gcd_cubic_quadratic_index_eq_div_six`,
  `cubic_quadratic_span_unit_iff_eq_six`, `not_cubic_quadratic_span_twelve`,
  `unique_low_cover_quadratic_order`).** For `n > 0` with `6 ∣ n`, the cubic and quadratic Gauss
  indices `n / 3` and `n / 2` generate `gcd(gcd(n / 3, n / 2), n) = n / 6` modulo `n`, spanning unit
  character index if and only if `n = 6` (blocking `n = 12` modulo `2`). Among all even `n > 3` and
  prime cover orders `p₀ ≤ 3` dividing `n`, `gcd(gcd(n / p₀, n / 2), n) = 1 ↔ (p₀, n) = (3, 6)`.
* **$L^{2r}$ Hölder vs. Voronoi/Poisson reflection duality gap (`dual_reflection_shorter_iff`,
  `holder_reflection_gap_at_row_scale`).** The reflected dual length `2 r U - a` is strictly shorter
  than `a` iff `r U < a`; for `r ≥ 1`, `U ≥ 1`, and `a < 1`, `(2 r U - a) - a ≥ 2 (1 - a) > 0`.
* **Planted conjugate-character saturation of multilinear dispersion
  (`planted_conjugate_character_saturates_multilinear_sum`).** On any `k`-fold product
  `∏_{r < k} S_r`, the unit-modulus weights `w_r(x) = \overline{χ_{u₀, r}(x)}` eliminate all
  oscillation at `u₀ ∈ B`, forcing `∑_{u ∈ B} ‖∑_{x} ∏_r w_r(x_r) χ_{u, r}(x_r)‖² ≥ (∏_r |S_r|)²`.
* **Twist-coupling Cauchy–Schwarz ceiling and `lx`-shift penalty
  (`norm_sum_sq_le_card_mul_sum_norm_sq`, `twist_coupling_signal_le_noise_exp`,
  `twist_offdiag_double_sqrt_dominates`, `lowBoundaryGenOrder_shift_lx_ge`).** Coherent averaging
  over `V` obeys `‖∑_{v ∈ V} λ_v‖² ≤ |V| ∑_{v ∈ V} ‖λ_v‖²` (`Z^{ν/2} ≤ Z^{U/2}` and off-diagonal
  double-square-root noise `Z^{(U+ν)/2} ≥ Z^ν` for `ν ≤ U`, `Z ≥ 1`), while shifting `lx ↦ lx + ν`
  (`ν ≥ 0`, `n > 0`) raises `lowBoundaryGenOrder n (lx + ν) ly ℓ` by at least `ν / (2 n)`.
* **Double obstruction at `(1/3, 1/3, 1/3)`, outer-factor Cauchy–Schwarz `11/12` floor, and direct
  vs. reflected `w`-contour identity (`double_obstruction_at_one_third`,
  `short_sieve_split_impossible`, `outer_cs_reflection_forces_eleven_twelfths`,
  `directWExponentOrder_sub_endpointExponentOrder`).** At `(1/3, 1/3, 1/3)`, `lowBoundaryGen = 5/6`
  violates both the reflected tuple allowance and the floor bin (`1 - σ₀`); any outer-factor CS +
  non-lengthening Poisson reflection split forces `1 ≤ lx + ly` and `11/12 ≤ lowBoundaryGen`; and
  bypassing `w`-reflection shifts the high-side exponent by `(δ/2)(2 ly + lx - ℓ - 1)` identically.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.FamilyContinuationTheory

/-! ### Part 1: Cyclotomic Gauss-monomial index conservation and uniqueness of `(3, 6)` -/

/-- For every `n > 0` divisible by `6`, `gcd(gcd(n / 3, n / 2), n) = n / 6`. -/
theorem gcd_cubic_quadratic_index_eq_div_six {n : ℕ} (h6 : 6 ∣ n) :
    Nat.gcd (Nat.gcd (n / 3) (n / 2)) n = n / 6 := by
  obtain ⟨m, rfl⟩ := h6
  have h3 : 6 * m / 3 = 2 * m := by omega
  have h2 : 6 * m / 2 = 3 * m := by omega
  have h6' : 6 * m / 6 = m := by omega
  rw [h3, h2, h6', Nat.gcd_mul_right, show Nat.gcd 2 3 = 1 by decide, one_mul]
  exact Nat.gcd_eq_left ⟨6, by ring⟩

/-- Cubic (`n / 3`) and quadratic (`n / 2`) Gauss-sum indices span the primitive index `1` modulo
`n` (`n > 0`, `6 ∣ n`) if and only if `n = 6`. -/
theorem cubic_quadratic_span_unit_iff_eq_six {n : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) :
    (∃ a b : ℤ, a * ((n / 3 : ℕ) : ℤ) + b * ((n / 2 : ℕ) : ℤ) ≡ 1 [ZMOD (n : ℤ)]) ↔ n = 6 := by
  constructor
  · rintro ⟨a, b, hmod⟩
    obtain ⟨m, rfl⟩ := h6
    have hm_pos : 0 < m := by omega
    have h3 : ((6 * m / 3 : ℕ) : ℤ) = 2 * (m : ℤ) := by
      have : 6 * m / 3 = 2 * m := by omega
      rw [this]; push_cast; ring
    have h2 : ((6 * m / 2 : ℕ) : ℤ) = 3 * (m : ℤ) := by
      have : 6 * m / 2 = 3 * m := by omega
      rw [this]; push_cast; ring
    rw [h3, h2] at hmod
    have hdvd6m : ((6 * m : ℕ) : ℤ) ∣ 1 - (a * (2 * (m : ℤ)) + b * (3 * (m : ℤ))) :=
      Int.modEq_iff_dvd.mp hmod.symm
    have hdvdm1 : (m : ℤ) ∣ ((6 * m : ℕ) : ℤ) := ⟨6, by push_cast; ring⟩
    have hdvdm2 : (m : ℤ) ∣ a * (2 * (m : ℤ)) + b * (3 * (m : ℤ)) :=
      ⟨2 * a + 3 * b, by ring⟩
    have hdvdone : (m : ℤ) ∣ 1 := by
      have hsub := dvd_trans hdvdm1 hdvd6m
      have hadd := dvd_add hsub hdvdm2
      simpa using hadd
    have hm1 : m ∣ 1 := by simpa using Int.natAbs_dvd_natAbs.mpr hdvdone
    rw [Nat.eq_one_of_dvd_one hm1]
  · rintro rfl
    refine ⟨-1, 1, ?_⟩
    norm_num
    rfl

/-- Modulo `12`, no integer combination `4a + 6b` of the cubic (`4`) and quadratic (`6`) Gauss-sum
indices equals `1` (parity obstruction on `ℤ[ζ₁₂]`). -/
theorem not_cubic_quadratic_span_twelve :
    ¬ ∃ a b : ℤ, a * 4 + b * 6 ≡ 1 [ZMOD 12] := by
  have h := (cubic_quadratic_span_unit_iff_eq_six (n := 12) (by decide) ⟨2, rfl⟩).mp
  intro hex
  have h12 : (12 : ℕ) = 6 := h (by simpa using hex)
  omega

/-- **Uniqueness of `(p₀, n) = (3, 6)` among low-conductor even cyclotomic covers.** Among all prime
cover orders `p₀ ≤ 3` (`κ = p₀ - 1 ≤ 2`) and even residue orders `n > 3` divisible by `p₀`,
`gcd(gcd(n / p₀, n / 2), n) = 1` holds if and only if `p₀ = 3` and `n = 6`. -/
theorem unique_low_cover_quadratic_order {p₀ n : ℕ} (hp₀ : p₀.Prime) (hp₀3 : p₀ ≤ 3)
    (hn3 : 3 < n) (h2n : 2 ∣ n) (hp₀n : p₀ ∣ n) :
    Nat.gcd (Nat.gcd (n / p₀) (n / 2)) n = 1 ↔ p₀ = 3 ∧ n = 6 := by
  have hp_cases : p₀ = 2 ∨ p₀ = 3 := by
    have := hp₀.two_le
    omega
  rcases hp_cases with rfl | rfl
  · constructor
    · intro hgcd
      obtain ⟨k, rfl⟩ := h2n
      have hk : 2 * k / 2 = k := by omega
      rw [hk, Nat.gcd_self, Nat.gcd_eq_left ⟨2, by ring⟩] at hgcd
      omega
    · rintro ⟨h23, _⟩; omega
  · have h6n : 6 ∣ n := by
      have hcop : Nat.Coprime 2 3 := by decide
      simpa using hcop.mul_dvd_of_dvd_of_dvd h2n hp₀n
    rw [gcd_cubic_quadratic_index_eq_div_six h6n]
    obtain ⟨m, rfl⟩ := h6n
    have hdiv : 6 * m / 6 = m := by omega
    rw [hdiv]
    constructor
    · intro hm; subst hm; exact ⟨rfl, rfl⟩
    · rintro ⟨_, h6⟩; omega

/-! ### Part 2: $L^{2r}$ Hölder vs. Voronoi/Poisson reflection duality gap -/

/-- Under $L^{2r}$ Hölder followed by Poisson/Voronoi reflection of modulus `U^r`, the dual length
`2 r U - a` is strictly shorter than `a` if and only if `r U < a`. -/
theorem dual_reflection_shorter_iff (r U a : ℝ) :
    2 * r * U - a < a ↔ r * U < a := by
  constructor <;> intro h <;> linarith

/-- Whenever `r ≥ 1`, `U ≥ 1`, and the outer summation exponent satisfies `a < 1`, the reflected
dual exponent `2 r U - a` strictly exceeds `a` by at least `2 (1 - a) > 0`. -/
theorem holder_reflection_gap_at_row_scale {r U a : ℝ} (hr : 1 ≤ r) (hU : 1 ≤ U) (ha : a < 1) :
    a < 2 * r * U - a ∧ 2 * (1 - a) ≤ (2 * r * U - a) - a := by
  have hrU : 1 ≤ r * U := by nlinarith
  exact ⟨by linarith, by linarith⟩

/-! ### Part 3: Planted conjugate-character saturation of multilinear dispersion -/

/-- **Planted conjugate-character saturation.** On any `k`-fold Cartesian product `∏_{r < k} S_r`
and family `B` containing `u₀` with unit-modulus factors `‖χ u₀ r x‖ = 1` on `S_r`, the unit-modulus
weights `w r x = star (χ u₀ r x)` achieve zero cancellation `(∏_r |S_r|)²` in the `L²(B)` dispersion
sum. -/
theorem planted_conjugate_character_saturates_multilinear_sum {α β : Type*} [DecidableEq α]
    [DecidableEq β] {k : ℕ} (S : Fin k → Finset α) (B : Finset β) (χ : β → Fin k → α → ℂ)
    {u₀ : β} (hu₀ : u₀ ∈ B) (hunit : ∀ r : Fin k, ∀ x ∈ S r, ‖χ u₀ r x‖ = 1) :
    ∃ w : Fin k → α → ℂ,
      (∀ r : Fin k, ∀ x ∈ S r, ‖w r x‖ = 1) ∧
      ‖∑ x ∈ Fintype.piFinset S, ∏ r : Fin k, w r (x r) * χ u₀ r (x r)‖ =
        ∏ r : Fin k, ((S r).card : ℝ) ∧
      (∏ r : Fin k, ((S r).card : ℝ)) ^ 2 ≤
        ∑ u ∈ B, ‖∑ x ∈ Fintype.piFinset S, ∏ r : Fin k, w r (x r) * χ u r (x r)‖ ^ 2 := by
  refine ⟨fun r x => star (χ u₀ r x), fun r x hx => by rw [norm_star, hunit r x hx], ?_, ?_⟩
  · have hprod_one : ∀ x ∈ Fintype.piFinset S,
        (∏ r : Fin k, star (χ u₀ r (x r)) * χ u₀ r (x r)) = 1 := by
      intro x hx
      refine Finset.prod_eq_one fun r _ => ?_
      have hxr : x r ∈ S r := Fintype.mem_piFinset.mp hx r
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        hunit r (x r) hxr]
      norm_num
    rw [Finset.sum_congr rfl hprod_one, Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul,
      mul_one, Nat.cast_prod, Complex.norm_natCast]
  · have hterm_eq :
        ‖∑ x ∈ Fintype.piFinset S, ∏ r : Fin k, star (χ u₀ r (x r)) * χ u₀ r (x r)‖ =
          ∏ r : Fin k, ((S r).card : ℝ) := by
      have hprod_one : ∀ x ∈ Fintype.piFinset S,
          (∏ r : Fin k, star (χ u₀ r (x r)) * χ u₀ r (x r)) = 1 := by
        intro x hx
        refine Finset.prod_eq_one fun r _ => ?_
        have hxr : x r ∈ S r := Fintype.mem_piFinset.mp hx r
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          hunit r (x r) hxr]
        norm_num
      rw [Finset.sum_congr rfl hprod_one, Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul,
        mul_one, Nat.cast_prod, Complex.norm_natCast]
    rw [← hterm_eq]
    exact Finset.single_le_sum (fun u _ => sq_nonneg _) hu₀

/-! ### Part 4: Twist-coupling Cauchy–Schwarz ceiling and low-side `lx`-shift penalty -/

/-- Coherent diagonal square vs. `|V|` times diagonal `L²` norm on any finite twist packet `V`. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (V : Finset ι) (lam : ι → ℂ) :
    ‖∑ v ∈ V, lam v‖ ^ 2 ≤ (V.card : ℝ) * ∑ v ∈ V, ‖lam v‖ ^ 2 := by
  have htri : ‖∑ v ∈ V, lam v‖ ≤ ∑ v ∈ V, ‖lam v‖ := norm_sum_le V lam
  have hsq : ‖∑ v ∈ V, lam v‖ ^ 2 ≤ (∑ v ∈ V, ‖lam v‖ * 1) ^ 2 := by
    simp only [mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq V (fun v => ‖lam v‖) (fun _ => (1 : ℝ))
  simp only [one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  linarith

/-- Whenever `1 ≤ Z` and `0 ≤ ν ≤ U`, the coherent signal gain `Z^{ν/2}` never exceeds the ambient
conductor root-scale `Z^{U/2}`. -/
theorem twist_coupling_signal_le_noise_exp {Z ν U : ℝ} (hZ : 1 ≤ Z) (hνU : ν ≤ U) :
    Z ^ (ν / 2) ≤ Z ^ (U / 2) :=
  Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

/-- Whenever `1 ≤ Z` and `ν ≤ U` (so diagonal pairs exist), the off-diagonal double-square-root
exponent `(U + ν) / 2` over `Z^{U + ν}` twist pairs dominates the diagonal exponent `ν`, strictly
whenever `ν < U`. -/
theorem twist_offdiag_double_sqrt_dominates {Z ν U : ℝ} (hZ : 1 ≤ Z) (hνU : ν ≤ U) :
    Z ^ ν ≤ Z ^ ((U + ν) / 2) ∧ (ν < U → ν < (U + ν) / 2) :=
  ⟨Real.rpow_le_rpow_of_exponent_le hZ (by linarith), fun hlt => by linarith⟩

/-- **Universal low-side `lx`-shift penalty.** For every residue order `n > 0` and nonnegative scale
shift `ν ≥ 0`, shifting `lx ↦ lx + ν` increases `Budget.lowBoundaryGenOrder` by at least `ν / (2n)`
across both Gram regimes and both reflection regimes. -/
theorem lowBoundaryGenOrder_shift_lx_ge {n lx ly ℓ ν : ℝ} (hn : 0 < n) (hν : 0 ≤ ν) :
    Budget.lowBoundaryGenOrder n lx ly ℓ + ν / (2 * n) ≤
      Budget.lowBoundaryGenOrder n (lx + ν) ly ℓ := by
  unfold Budget.lowBoundaryGenOrder
  have hmax_diff : max 0 (ly - lx) - ν ≤ max 0 (ly - (lx + ν)) := by
    rcases le_total (ly - lx) 0 with hle | hgt
    · rw [max_eq_left hle, max_eq_left (by linarith)]
      linarith
    · rw [max_eq_right hgt]
      have h1 : ly - lx - ν = ly - (lx + ν) := by ring
      rw [h1]
      exact le_max_right 0 _
  have hmax_refl : max 0 (lx + ly + ℓ - 1) ≤ max 0 (lx + ν + ly + ℓ - 1) :=
    max_le_max_left 0 (by linarith)
  have hnum : (1 - (lx + ν) - max 0 (ly - (lx + ν)) / 2 + ℓ) ≤
      (1 - lx - max 0 (ly - lx) / 2 + ℓ) - ν / 2 := by
    linarith
  have hdiv : (1 - (lx + ν) - max 0 (ly - (lx + ν)) / 2 + ℓ) / n ≤
      (1 - lx - max 0 (ly - lx) / 2 + ℓ) / n - ν / (2 * n) := by
    have hstep := div_le_div_of_nonneg_right hnum hn.le
    have hrew : ((1 - lx - max 0 (ly - lx) / 2 + ℓ) - ν / 2) / n =
        (1 - lx - max 0 (ly - lx) / 2 + ℓ) / n - ν / (2 * n) := by
      rw [sub_div, div_div]
    linarith
  linarith

/-! ### Part 5: Double obstruction at `(1/3, 1/3, 1/3)`, outer-factor CS reflection floor, and direct vs. reflected `w`-contour identity -/

/-- **Double obstruction at the `5/6` low-side point `(1/3, 1/3, 1/3)`.** Although
`lowBoundaryGen (1/3) (1/3) (1/3) = 5/6`, it simultaneously violates the reflected marked-row
allowance `1 + 3ℓ ≤ 2(lx + ly)` and forces `1 - σ₀` in the floor bin (`δ = 0, q = 0, R = 1`). -/
theorem double_obstruction_at_one_third (σ₀ : ℝ) :
    Budget.lowBoundaryGen (1 / 3) (1 / 3) (1 / 3) = 5 / 6 ∧
      ¬ ((1 : ℝ) + 3 * (1 / 3) ≤ 2 * (1 / 3 + 1 / 3)) ∧
      Budget.endpointExponent (1 / 3) (1 / 3) (1 / 3) σ₀ 0 0 1 = 1 - σ₀ := by
  refine ⟨?_, by norm_num, ?_⟩
  · rw [← Budget.lowBoundaryGenOrder_six]
    norm_num [Budget.lowBoundaryGenOrder]
  · rw [← Budget.endpointExponentOrder_six]
    unfold Budget.endpointExponentOrder
    ring

/-- Splitting `T = 1 + ly + ℓ = a + b` into two blocks both inside the diagonal sieve range `U / 2`
(`U = 1 - lx + ℓ`) forces `lx + ly ≤ 0`. -/
theorem short_sieve_split_impossible {lx ly ℓ a b : ℝ}
    (hsplit : a + b = 1 + ly + ℓ)
    (ha : a ≤ (1 - lx + ℓ) / 2) (hb : b ≤ (1 - lx + ℓ) / 2) :
    lx + ly ≤ 0 := by
  linarith

/-- **Outer-factor Cauchy–Schwarz + non-lengthening Poisson reflection forces `11/12`.** Whenever
`0 ≤ lx` and `1 + ly + ℓ = a + b` satisfies the planted-diagonal bound
`2(a + b) ≤ 2(1 + ly + ℓ) + (1 - lx + ℓ)/3 - 1/3`, the Parseval-diagonal bound
`2a + (1 - lx + ℓ) + b ≤ 2(1 + ly + ℓ) + (1 - lx + ℓ)/3 - 1/3`, and non-lengthening reflection
`2(1 - lx + ℓ) - a ≤ a`, one has `1 ≤ lx + ly` and `11 / 12 ≤ Budget.lowBoundaryGen lx ly ℓ`
(attained at `(0, 1, 0, 1, 1)`). -/
theorem outer_cs_reflection_forces_eleven_twelfths {lx ly ℓ a b : ℝ} (hlx : 0 ≤ lx)
    (hsplit : a + b = 1 + ly + ℓ)
    (hplant : 2 * (a + b) ≤ 2 * (1 + ly + ℓ) + (1 - lx + ℓ) / 3 - 1 / 3)
    (hpars : 2 * a + (1 - lx + ℓ) + b ≤ 2 * (1 + ly + ℓ) + (1 - lx + ℓ) / 3 - 1 / 3)
    (hrefl : 2 * (1 - lx + ℓ) - a ≤ a) :
    1 ≤ lx + ly ∧ 11 / 12 ≤ Budget.lowBoundaryGen lx ly ℓ ∧
      Budget.lowBoundaryGen 0 1 0 = 11 / 12 := by
  have hlx_le_ℓ : lx ≤ ℓ := by linarith
  have hℓ0 : 0 ≤ ℓ := le_trans hlx hlx_le_ℓ
  have h3 : 3 + 2 * ℓ ≤ 5 * lx + 3 * ly := by linarith
  have hM1 : 1 ≤ lx + ly := by linarith
  refine ⟨hM1, ?_, ?_⟩
  · rw [← Budget.lowBoundaryGenOrder_six]
    unfold Budget.lowBoundaryGenOrder
    have hν : ly - lx ≤ max 0 (ly - lx) := le_max_right 0 (ly - lx)
    have hμ : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right 0 (lx + ly + ℓ - 1)
    generalize max 0 (ly - lx) = ν at hν ⊢
    generalize max 0 (lx + ly + ℓ - 1) = μ at hμ ⊢
    linarith
  · rw [← Budget.lowBoundaryGenOrder_six]
    norm_num [Budget.lowBoundaryGenOrder]

/-- High-side exponent obtained by shifting the direct `w`-contour without functional-equation
reflection. -/
def directWExponentOrder (n lx ly ℓ σ₀ δ q R : ℝ) : ℝ :=
  (1 + δ) / 2 - (1 - δ) * ly / 2 - σ₀ - ℓ / 2 + q * ℓ + (1 - lx + ℓ) * (R - 1 / n)

/-- **Exact difference between the direct and reflected `w`-contour high-side exponents.** Bypassing
the `w`-functional equation changes the high-side exponent by `(δ / 2)(2 ly + lx - ℓ - 1)`
identically, so for `0 ≤ δ` and `1 ≤ 2 ly + lx - ℓ` (in particular at `(17/48, 23/48, 1/6)` where
`2 ly + lx - ℓ = 55/48 > 1`), reflection strictly dominates or ties the direct `w`-contour. -/
theorem directWExponentOrder_sub_endpointExponentOrder (n lx ly ℓ σ₀ δ q R : ℝ) :
    directWExponentOrder n lx ly ℓ σ₀ δ q R -
      Budget.endpointExponentOrder n lx ly ℓ σ₀ δ q R =
        (δ / 2) * (2 * ly + lx - ℓ - 1) := by
  unfold directWExponentOrder Budget.endpointExponentOrder
  ring

theorem endpointExponentOrder_le_directWExponentOrder {n lx ly ℓ σ₀ δ q R : ℝ}
    (hδ : 0 ≤ δ) (hgeom : 1 ≤ 2 * ly + lx - ℓ) :
    Budget.endpointExponentOrder n lx ly ℓ σ₀ δ q R ≤
      directWExponentOrder n lx ly ℓ σ₀ δ q R := by
  have hdiff := directWExponentOrder_sub_endpointExponentOrder n lx ly ℓ σ₀ δ q R
  have hprod : 0 ≤ (δ / 2) * (2 * ly + lx - ℓ - 1) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

end GaloisForLFunctions.FamilyContinuationTheory
