import GaloisForLFunctions.BezoutValuationIncidence.MeanCenteredPronicGramRecurrenceAndCenteringDiscrepancyBridge
import GaloisForLFunctions.RHTower.PMRamanujanNearbyPrimeResonance

/-!
# Two-Prime Dilation Profile Identity and Prime-Star Shear Cancellation

This module resolves the prime-star shear and two-prime covariance structure of the pronic
Ramanujan Gram matrix `pmRamanujanPrimitiveGram` (`G(q, r)`), its energy-centered counterpart
`pmRamanujanEnergyCenteredGram` (`G^{ec}(q, r)`), and its mean-centered counterpart
`pmRamanujanMeanCenteredGram` (`G^{mc}(q, r)`):

1. **Exact Single-Prime and Two-Prime Dilation Profile Identities**:
   In `RHTower.PMRamanujanNearbyPrimeResonance`, the Hilbert step vector
   `f_r = pmRamanujanStepVector r hr : SoninL2` satisfies the exact prime-insertion law
   `f_{pr} = √p D_{p⁻¹} f_r - f_r` for any prime `p ∤ r`, and the two-prime covariance
   `G(pr, qr)` was previously compared to `√p √q Φ_r(p/q)` (`Φ_r = pmRamanujanDilationProfile r hr`)
   only up to an inequality with error `(√p + √q + 1) G(r, r)`.
   Here we prove the **exact single-prime dilation profile identity**
   (`pmRamanujanPrimitiveGram_prime_mul_add_diag_eq_dilationProfile`):
   $$G(pr, r) + G(r, r) = \sqrt{p}\,\Phi_r(p),$$
   and the **exact four-term two-prime dilation profile identity**
   (`pmRamanujanPrimitiveGram_two_prime_mul_eq_dilationProfile`):
   $$G(pr, qr) + G(pr, r) + G(qr, r) + G(r, r) = \sqrt{p}\sqrt{q}\,\Phi_r(p / q).$$
   Combining the single-prime identity with `tendsto_pmRamanujanPrimitiveGram_prime_mul` yields the
   exact asymptotic law (`tendsto_sqrt_mul_pmRamanujanDilationProfile_prime`):
   $$\lim_{p \to \infty,\,p\text{ prime}} \sqrt{p}\,\Phi_r(p) = \frac{\varphi(r)\,\Lambda(r)}{2},$$
   which vanishes for every composite non-prime-power `r` (`¬ IsPrimePow r`). Consequently, the
   apparent `O(√p + √q)` error terms in `G(pr, qr) - √p √q Φ_r(p/q)` actually converge to `0` as
   `p, q → ∞` whenever `¬ IsPrimePow r`, leaving only the constant offset `+G(r, r)`.

2. **Shifted Two-Mode and Prime-Star Shear Cancellation**:
   In the shifted basis `W = w₀ - ∑_{p ∈ S} w(p)` for a star `{r} ∪ {pr : p ∈ S}` of prime
   multiples of `r`, the quadratic form decomposes exactly (`prime_star_dilationProfile_decomposition`)
   into:
   - the shifted base energy `W² G(r, r)`,
   - the shifted cross-term `2 W ∑_{p ∈ S} w(p) (G(pr, r) + G(r, r))`, whose coefficients
     `G(pr, r) + G(r, r)` converge to `φ(r) Λ(r) / 2` (and vanish in the `p → ∞` limit for
     `¬ IsPrimePow r`), and
   - the pure dilation-profile quadratic form
     `∑_{p ∈ S} ∑_{q ∈ S} (w(p) √p) (w(q) √q) Φ_r(p / q)`.
   When the weights are shear-balanced (`w₀ = ∑_{p ∈ S} w(p)`), both the base energy and the
   cross-terms cancel identically (`prime_star_shear_balanced_eq_dilationProfile_form`).
-/

open scoped BigOperators Topology
open Finset Filter ArithmeticFunction RHTower

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ## §1. Shifted Two-Mode Prime-Dilation Shear Cancellation -/

/-- **Shifted Two-Mode Prime-Dilation Identity (Raw Pronic Gram)**:
For any prime `p` and modulus `r > 1` with `¬ p ∣ r`, changing coordinates from `(u, v)` on the
pair `(r, pr)` to `(u - v, v)` eliminates the raw off-diagonal shear `2 u v G(pr, r)` in favor of
the shifted covariance `G(pr, r) + G(r, r)` (which converges to `φ(r) Λ(r) / 2` as `p → ∞`) and
the amplified diagonal `p v² G(r, r)`. -/
theorem pmRamanujanPrimitiveGram_shifted_two_mode_eq {p r : ℕ}
    (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) (u v : ℝ) :
    u ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * u * v * pmRamanujanPrimitiveGram (p * r) r +
        v ^ 2 * pmRamanujanPrimitiveGram (p * r) (p * r) =
      (u - v) ^ 2 * pmRamanujanPrimitiveGram r r +
        (p : ℝ) * v ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * (u - v) * v *
          (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r) := by
  have hdiag := pmRamanujanPrimitiveGram_prime_mul_diag hp hr hpr
  rw [hdiag]
  ring

/-- **Shear-Balanced Two-Mode Identity (Raw Pronic Gram)**:
When `u = v` on `{r, pr}` (`p` prime, `¬ p ∣ r`), the off-diagonal cross-term cancels the `-G(r, r)`
drift in `G(pr, pr)` to leave exactly `p v² G(r, r)`. -/
theorem pmRamanujanPrimitiveGram_shear_balanced_two_mode {p r : ℕ}
    (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) (v : ℝ) :
    v ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * v * v * pmRamanujanPrimitiveGram (p * r) r +
        v ^ 2 * pmRamanujanPrimitiveGram (p * r) (p * r) =
      (p : ℝ) * v ^ 2 * pmRamanujanPrimitiveGram r r := by
  have h := pmRamanujanPrimitiveGram_shifted_two_mode_eq hp hr hpr v v
  linarith

/-- **Shifted Two-Mode Prime-Dilation Identity (Energy-Centered Gram)**:
For `G^{ec}(q, r) = pmRamanujanEnergyCenteredGram q r`, the two-mode quadratic form on `{r, pr}`
decomposes in the shifted coordinate `u - v` into the residual base energy `(u - v)² G^{ec}(r, r)`,
the `p`-amplified diagonal `p v² G^{ec}(r, r)`, the prime-power von Mangoldt term
`(p - 1) v² Λ(r)²`, and the shifted covariance `G^{ec}(pr, r) + G^{ec}(r, r)` (which converges to
`0` as `p → ∞` for every `¬ IsPrimePow r`). -/
theorem pmRamanujanEnergyCenteredGram_shifted_two_mode_eq {p r : ℕ}
    (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) (u v : ℝ) :
    u ^ 2 * pmRamanujanEnergyCenteredGram r r +
        2 * u * v * pmRamanujanEnergyCenteredGram (p * r) r +
        v ^ 2 * pmRamanujanEnergyCenteredGram (p * r) (p * r) =
      (u - v) ^ 2 * pmRamanujanEnergyCenteredGram r r +
        (p : ℝ) * v ^ 2 * pmRamanujanEnergyCenteredGram r r +
        ((p : ℝ) - 1) * v ^ 2 * (vonMangoldt r) ^ 2 +
        2 * (u - v) * v *
          (pmRamanujanEnergyCenteredGram (p * r) r + pmRamanujanEnergyCenteredGram r r) := by
  have hdiag := pmRamanujanEnergyCenteredGram_prime_mul_diag hp hr hpr
  rw [hdiag]
  ring

/-- **Shifted Two-Mode Prime-Dilation Identity (Mean-Centered Gram)**:
For `G^{mc}(q, r) = pmRamanujanMeanCenteredGram q r`, the two-mode quadratic form on `{r, pr}`
decomposes in the shifted coordinate `u - v` with the pure totient innovation
`(p (p - 1) / 4) φ(r)² v²`. -/
theorem pmRamanujanMeanCenteredGram_shifted_two_mode_eq {p r : ℕ}
    (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) (u v : ℝ) :
    u ^ 2 * pmRamanujanMeanCenteredGram r r +
        2 * u * v * pmRamanujanMeanCenteredGram (p * r) r +
        v ^ 2 * pmRamanujanMeanCenteredGram (p * r) (p * r) =
      (u - v) ^ 2 * pmRamanujanMeanCenteredGram r r +
        (p : ℝ) * v ^ 2 * pmRamanujanMeanCenteredGram r r +
        (p : ℝ) * ((p : ℝ) - 1) / 4 * (r.totient : ℝ) ^ 2 * v ^ 2 +
        2 * (u - v) * v *
          (pmRamanujanMeanCenteredGram (p * r) r + pmRamanujanMeanCenteredGram r r) := by
  have hdiag := pmRamanujanMeanCenteredGram_prime_mul_diag hp hr hpr
  rw [hdiag]
  ring

/-! ## §2. Exact Single-Prime and Two-Prime Dilation Profile Identities -/

/-- Helper: the real part of the `SoninL2` inner product between `D_{a⁻¹} f` and `f` equals
`pmRamanujanDilationProfile r hr a` for any `a > 0`. -/
private theorem re_inner_dilation_inv_self {r : ℕ} (hr : 1 < r) {a : ℝ} (ha : 0 < a) :
    (inner ℂ (dilation a⁻¹ (inv_pos.mpr ha) (pmRamanujanStepVector r hr))
      (pmRamanujanStepVector r hr)).re = pmRamanujanDilationProfile r hr a := by
  let f := pmRamanujanStepVector r hr
  have h := (dilation a ha).inner_map_map (dilation a⁻¹ (inv_pos.mpr ha) f) f
  rw [dilation_dilation_inv] at h
  have hray : rayDilate a f = dilation a ha f := rayDilate_of_pos ha f
  rw [pmRamanujanDilationProfile, hray, ← h]

/-- Helper: the real part of the `SoninL2` inner product between `f` and `D_{b⁻¹} f` also equals
`pmRamanujanDilationProfile r hr b` for any `b > 0`. -/
private theorem re_inner_self_dilation_inv {r : ℕ} (hr : 1 < r) {b : ℝ} (hb : 0 < b) :
    (inner ℂ (pmRamanujanStepVector r hr)
      (dilation b⁻¹ (inv_pos.mpr hb) (pmRamanujanStepVector r hr))).re =
        pmRamanujanDilationProfile r hr b := by
  let f := pmRamanujanStepVector r hr
  let v := dilation b⁻¹ (inv_pos.mpr hb) f
  have hsymm : (inner ℂ f v).re = (inner ℂ v f).re := by
    rw [← inner_conj_symm v f, Complex.conj_re]
  rw [hsymm]
  exact re_inner_dilation_inv_self hr hb

/-- **Exact Single-Prime Dilation Profile Identity**:
For any prime `p` and modulus `r > 1` with `¬ p ∣ r`, the shifted single-prime covariance
`G(pr, r) + G(r, r)` is exactly `√p` times the continuous dilation profile
`pmRamanujanDilationProfile r hr p` evaluated at scale `p`. -/
theorem pmRamanujanPrimitiveGram_prime_mul_add_diag_eq_dilationProfile {p r : ℕ}
    (hp : p.Prime) (hr : 1 < r) (hpr : ¬ p ∣ r) :
    pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r =
      Real.sqrt (p : ℝ) * pmRamanujanDilationProfile r hr (p : ℝ) := by
  let f := pmRamanujanStepVector r hr
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let u := dilation (p : ℝ)⁻¹ (inv_pos.mpr hpR) f
  have he := inner_pmRamanujanStepVector
    (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)) hr
  rw [pmRamanujanStepVector_prime_mul hp hr hpr] at he
  change inner ℂ ((Real.sqrt (p : ℝ) : ℂ) • u - f) f = _ at he
  simp only [inner_sub_left, inner_smul_left, Complex.conj_ofReal] at he
  have heR := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at heR
  have hff : (inner ℂ f f).re = pmRamanujanPrimitiveGram r r :=
    congrArg Complex.re (inner_pmRamanujanStepVector hr hr)
  have huf : (inner ℂ u f).re = pmRamanujanDilationProfile r hr (p : ℝ) :=
    re_inner_dilation_inv_self hr hpR
  rw [huf, hff] at heR
  linarith

/-- **Exact Four-Term Two-Prime Dilation Profile Identity**:
For any two primes `p, q` and any modulus `r > 1` with `¬ p ∣ r` and `¬ q ∣ r`, the four-term
combination of `G = pmRamanujanPrimitiveGram` on `{r, pr, qr}` equals `√p √q` times the continuous
dilation profile `pmRamanujanDilationProfile r hr (p / q)` at the scale ratio `p / q`:
$$G(pr, qr) + G(pr, r) + G(qr, r) + G(r, r) = \sqrt{p}\sqrt{q}\,\Phi_r(p / q).$$
This upgrades the inequality `pmRamanujanPrimitiveGram_nearby_error` into an exact identity. -/
theorem pmRamanujanPrimitiveGram_two_prime_mul_eq_dilationProfile {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : 1 < r)
    (hpr : ¬ p ∣ r) (hqr : ¬ q ∣ r) :
    pmRamanujanPrimitiveGram (p * r) (q * r) +
        pmRamanujanPrimitiveGram (p * r) r +
        pmRamanujanPrimitiveGram (q * r) r +
        pmRamanujanPrimitiveGram r r =
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
  let f := pmRamanujanStepVector r hr
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  let u := dilation (p : ℝ)⁻¹ (inv_pos.mpr hpR) f
  let v := dilation (q : ℝ)⁻¹ (inv_pos.mpr hqR) f
  have huv : (inner ℂ u v).re = pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
    have h := (dilation (p : ℝ) hpR).inner_map_map u v
    rw [dilation_dilation_inv, dilation_dilation] at h
    have hray : rayDilate ((p : ℝ) / q) f =
        dilation ((p : ℝ) * (q : ℝ)⁻¹) (mul_pos hpR (inv_pos.mpr hqR)) f := by
      simpa only [div_eq_mul_inv] using rayDilate_of_pos (div_pos hpR hqR) f
    rw [pmRamanujanDilationProfile, hray, ← h]
  have he := inner_pmRamanujanStepVector
    (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos))
    (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hq.pos))
  rw [pmRamanujanStepVector_prime_mul hp hr hpr,
    pmRamanujanStepVector_prime_mul hq hr hqr] at he
  change inner ℂ ((Real.sqrt (p : ℝ) : ℂ) • u - f)
    ((Real.sqrt (q : ℝ) : ℂ) • v - f) = _ at he
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal] at he
  have heR := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at heR
  have hff : (inner ℂ f f).re = pmRamanujanPrimitiveGram r r :=
    congrArg Complex.re (inner_pmRamanujanStepVector hr hr)
  have huf : Real.sqrt (p : ℝ) * (inner ℂ u f).re =
      pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r := by
    rw [re_inner_dilation_inv_self hr hpR,
      ← pmRamanujanPrimitiveGram_prime_mul_add_diag_eq_dilationProfile hp hr hpr]
  have hfv : Real.sqrt (q : ℝ) * (inner ℂ f v).re =
      pmRamanujanPrimitiveGram (q * r) r + pmRamanujanPrimitiveGram r r := by
    rw [re_inner_self_dilation_inv hr hqR,
      ← pmRamanujanPrimitiveGram_prime_mul_add_diag_eq_dilationProfile hq hr hqr]
  rw [huv, hff] at heR
  linarith

/-- **Energy-Centered Two-Prime Dilation Profile Identity for Composite Non-Prime-Power Moduli**:
When `¬ IsPrimePow r`, all von Mangoldt centering corrections on `r`, `pr`, and `qr` vanish, so
`pmRamanujanEnergyCenteredGram` satisfies the exact same four-term dilation profile identity. -/
theorem pmRamanujanEnergyCenteredGram_two_prime_mul_eq_dilationProfile {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : 1 < r) (hrp : ¬ IsPrimePow r)
    (hpr : ¬ p ∣ r) (hqr : ¬ q ∣ r) :
    pmRamanujanEnergyCenteredGram (p * r) (q * r) +
        pmRamanujanEnergyCenteredGram (p * r) r +
        pmRamanujanEnergyCenteredGram (q * r) r +
        pmRamanujanEnergyCenteredGram r r =
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
  have hpr1 : 1 < p * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)
  have hqr1 : 1 < q * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hq.pos)
  have hΛr : vonMangoldt r = 0 := vonMangoldt_eq_zero_iff.mpr hrp
  have hΛpr : vonMangoldt (p * r) = 0 := by
    rw [vonMangoldt_eq_zero_iff]
    intro h
    exact hrp (h.dvd (dvd_mul_left r p) (by omega))
  have hΛqr : vonMangoldt (q * r) = 0 := by
    rw [vonMangoldt_eq_zero_iff]
    intro h
    exact hrp (h.dvd (dvd_mul_left r q) (by omega))
  have h1 := pmRamanujanPrimitiveGram_eq_energyCentered hpr1 hqr1
  have h2 := pmRamanujanPrimitiveGram_eq_energyCentered hpr1 hr
  have h3 := pmRamanujanPrimitiveGram_eq_energyCentered hqr1 hr
  have h4 := pmRamanujanPrimitiveGram_eq_energyCentered hr hr
  simp only [hΛr, hΛpr, hΛqr, mul_zero, zero_add] at h1 h2 h3 h4
  linarith [pmRamanujanPrimitiveGram_two_prime_mul_eq_dilationProfile hp hq hr hpr hqr]

/-- **Prime-Limit Decay Law for the Dilation Profile**:
As `p → ∞` through primes, `√p Φ_r(p) = G(pr, r) + G(r, r)` converges to `φ(r) Λ(r) / 2`.
In particular, `Φ_r(p) = O(p⁻¹/²)` along primes rather than `O(1)`. -/
theorem tendsto_sqrt_mul_pmRamanujanDilationProfile_prime {r : ℕ} (hr : 1 < r) :
    Tendsto (fun p : {p : ℕ // p.Prime} =>
      Real.sqrt ((p : ℕ) : ℝ) * pmRamanujanDilationProfile r hr ((p : ℕ) : ℝ))
      atTop (𝓝 ((r.totient : ℝ) * vonMangoldt r / 2)) := by
  have hlim := (tendsto_pmRamanujanPrimitiveGram_prime_mul hr hr).add_const
    (pmRamanujanPrimitiveGram r r)
  have htarget :
      (r.totient : ℝ) * vonMangoldt r / 2 - pmRamanujanPrimitiveGram r r +
          pmRamanujanPrimitiveGram r r =
        (r.totient : ℝ) * vonMangoldt r / 2 := by ring
  rw [htarget] at hlim
  have hnd : ∀ᶠ p : {p : ℕ // p.Prime} in atTop, ¬ (p : ℕ) ∣ r := by
    obtain ⟨P, hP, hPrime⟩ := Nat.exists_infinite_primes (r + 1)
    letI : Nonempty {p : ℕ // p.Prime} := ⟨⟨P, hPrime⟩⟩
    apply eventually_atTop.2
    refine ⟨⟨P, hPrime⟩, fun p hpp => ?_⟩
    change P ≤ (p : ℕ) at hpp
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  refine hlim.congr' ?_
  filter_upwards [hnd] with p hpr
  exact pmRamanujanPrimitiveGram_prime_mul_add_diag_eq_dilationProfile p.property hr hpr

/-- For any composite non-prime-power modulus `r > 1`, `√p Φ_r(p) → 0` as `p → ∞` through primes. -/
theorem tendsto_sqrt_mul_pmRamanujanDilationProfile_prime_of_not_isPrimePow
    {r : ℕ} (hr : 1 < r) (hrp : ¬ IsPrimePow r) :
    Tendsto (fun p : {p : ℕ // p.Prime} =>
      Real.sqrt ((p : ℕ) : ℝ) * pmRamanujanDilationProfile r hr ((p : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hΛ : vonMangoldt r = 0 := vonMangoldt_eq_zero_iff.mpr hrp
  simpa [hΛ] using tendsto_sqrt_mul_pmRamanujanDilationProfile_prime hr

/-! ## §3. General Prime-Star Quadratic Decomposition and Shear Cancellation -/

/-- **General Prime-Star Algebraic Decomposition**:
For any base modulus `r`, any finite set of branch multipliers `S : Finset ℕ`, any base weight
`w₀ : ℝ`, and any branch weights `w : ℕ → ℝ`, the quadratic form of `pmRamanujanPrimitiveGram` on
`{r} ∪ {p * r : p ∈ S}` decomposes into:
1. the shifted base energy `(w₀ - ∑_{p ∈ S} w(p))² G(r, r)`,
2. the shifted cross-term `2 (w₀ - ∑_{p ∈ S} w(p)) ∑_{p ∈ S} w(p) (G(pr, r) + G(r, r))`, and
3. the four-term kernel quadratic form
   `∑_{p ∈ S} ∑_{q ∈ S} w(p) w(q) (G(pr, qr) + G(pr, r) + G(qr, r) + G(r, r))`. -/
theorem prime_star_primitiveGram_decomposition (r : ℕ) (S : Finset ℕ) (w₀ : ℝ) (w : ℕ → ℝ) :
    w₀ ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * w₀ * (∑ p ∈ S, w p * pmRamanujanPrimitiveGram (p * r) r) +
        (∑ p ∈ S, ∑ q ∈ S, w p * w q * pmRamanujanPrimitiveGram (p * r) (q * r)) =
      (w₀ - ∑ p ∈ S, w p) ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * (w₀ - ∑ p ∈ S, w p) *
          (∑ p ∈ S, w p * (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r)) +
        ∑ p ∈ S, ∑ q ∈ S, w p * w q *
          (pmRamanujanPrimitiveGram (p * r) (q * r) +
            pmRamanujanPrimitiveGram (p * r) r +
            pmRamanujanPrimitiveGram (q * r) r +
            pmRamanujanPrimitiveGram r r) := by
  have h1 :
      ∑ p ∈ S, w p * (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r) =
        (∑ p ∈ S, w p * pmRamanujanPrimitiveGram (p * r) r) +
          (∑ p ∈ S, w p) * pmRamanujanPrimitiveGram r r := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  have h2 :
      ∑ p ∈ S, ∑ q ∈ S, w p * w q *
          (pmRamanujanPrimitiveGram (p * r) (q * r) +
            pmRamanujanPrimitiveGram (p * r) r +
            pmRamanujanPrimitiveGram (q * r) r +
            pmRamanujanPrimitiveGram r r) =
        (∑ p ∈ S, ∑ q ∈ S, w p * w q * pmRamanujanPrimitiveGram (p * r) (q * r)) +
          2 * (∑ p ∈ S, w p) * (∑ p ∈ S, w p * pmRamanujanPrimitiveGram (p * r) r) +
          (∑ p ∈ S, w p) ^ 2 * pmRamanujanPrimitiveGram r r := by
    have hsplit :
        ∀ p q : ℕ,
          w p * w q *
              (pmRamanujanPrimitiveGram (p * r) (q * r) +
                pmRamanujanPrimitiveGram (p * r) r +
                pmRamanujanPrimitiveGram (q * r) r +
                pmRamanujanPrimitiveGram r r) =
            w p * w q * pmRamanujanPrimitiveGram (p * r) (q * r) +
              (w p * pmRamanujanPrimitiveGram (p * r) r) * w q +
              w p * (w q * pmRamanujanPrimitiveGram (q * r) r) +
              (w p * w q) * pmRamanujanPrimitiveGram r r := by
      intro p q; ring
    simp only [hsplit, Finset.sum_add_distrib]
    have ha :
        (∑ x ∈ S, ∑ y ∈ S, w x * pmRamanujanPrimitiveGram (x * r) r * w y) =
          (∑ p ∈ S, w p * pmRamanujanPrimitiveGram (p * r) r) * (∑ q ∈ S, w q) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    have hb :
        (∑ x ∈ S, ∑ y ∈ S, w x * (w y * pmRamanujanPrimitiveGram (y * r) r)) =
          (∑ p ∈ S, w p) * (∑ q ∈ S, w q * pmRamanujanPrimitiveGram (q * r) r) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    have hc :
        (∑ x ∈ S, ∑ y ∈ S, w x * w y * pmRamanujanPrimitiveGram r r) =
          (∑ p ∈ S, w p) ^ 2 * pmRamanujanPrimitiveGram r r := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, sq]
    rw [ha, hb, hc]
    ring
  rw [h1, h2]
  ring

/-- **Prime-Star Dilation Profile Decomposition**:
When `r > 1` and every `p ∈ S` is a prime not dividing `r`, the four-term kernel in
`prime_star_primitiveGram_decomposition` is replaced unconditionally by the exact dilation profile
`√p √q pmRamanujanDilationProfile r hr (p / q)`. -/
theorem prime_star_dilationProfile_decomposition {r : ℕ} (hr : 1 < r) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ r) (w₀ : ℝ) (w : ℕ → ℝ) :
    w₀ ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * w₀ * (∑ p ∈ S, w p * pmRamanujanPrimitiveGram (p * r) r) +
        (∑ p ∈ S, ∑ q ∈ S, w p * w q * pmRamanujanPrimitiveGram (p * r) (q * r)) =
      (w₀ - ∑ p ∈ S, w p) ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * (w₀ - ∑ p ∈ S, w p) *
          (∑ p ∈ S, w p * (pmRamanujanPrimitiveGram (p * r) r + pmRamanujanPrimitiveGram r r)) +
        ∑ p ∈ S, ∑ q ∈ S,
          (w p * Real.sqrt (p : ℝ)) * (w q * Real.sqrt (q : ℝ)) *
            pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
  rw [prime_star_primitiveGram_decomposition r S w₀ w]
  congr 1
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  have hp' := hS p hp
  have hq' := hS q hq
  rw [pmRamanujanPrimitiveGram_two_prime_mul_eq_dilationProfile hp'.1 hq'.1 hr hp'.2 hq'.2]
  ring

/-- **Shear-Balanced Prime-Star Identity**:
When the base weight balances the prime-branch weights (`w₀ = ∑_{p ∈ S} w(p)`), both the base
energy and the cross-term vanish identically, so the prime-star quadratic form equals the pure
dilation-profile quadratic form on `S`. -/
theorem prime_star_shear_balanced_eq_dilationProfile_form {r : ℕ} (hr : 1 < r) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ r) (w : ℕ → ℝ) :
    (∑ p ∈ S, w p) ^ 2 * pmRamanujanPrimitiveGram r r +
        2 * (∑ p ∈ S, w p) * (∑ p ∈ S, w p * pmRamanujanPrimitiveGram (p * r) r) +
        (∑ p ∈ S, ∑ q ∈ S, w p * w q * pmRamanujanPrimitiveGram (p * r) (q * r)) =
      ∑ p ∈ S, ∑ q ∈ S,
        (w p * Real.sqrt (p : ℝ)) * (w q * Real.sqrt (q : ℝ)) *
          pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
  have h := prime_star_dilationProfile_decomposition hr S hS (∑ p ∈ S, w p) w
  simpa [sub_self] using h

end GaloisForLFunctions.BezoutValuationIncidence
