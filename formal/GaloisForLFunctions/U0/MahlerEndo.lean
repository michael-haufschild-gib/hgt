/-
# The Mahler endomorphism on `ℂ(z) = RatFunc ℂ`

The substitution `z ↦ z²+c` is an injective `ℂ`-algebra endomorphism of `ℂ[z]` (composition with the
nonconstant `X²+c`); since it sends nonzero polynomials to nonzero polynomials, it extends to a
`ℂ`-algebra endomorphism `mahlerHom c` of the fraction field `ℂ(z) = RatFunc ℂ` — the **Mahler
operator**. This is the foundational object for the `n ≥ 2` norm-descent: the minimal polynomial of an
algebraic `φ_c`, its norm, and the divisibility `P(z,Y) ∣ P(σz,Y²)` all live over `ℂ(z)` and transform
under `mahlerHom`.
-/
import GaloisForLFunctions.U0.MahlerRatFunc

open Polynomial

namespace MahlerPolynomial

/-- Composition with the nonconstant `X²+c` preserves nonzero polynomials. -/
@[aesop safe]
theorem comp_quadratic_ne_zero {c : ℂ} {p : ℂ[X]} (hp : p ≠ 0) : p.comp (X ^ (2 : ℕ) + C c) ≠ 0 := by
  intro h
  rw [comp_eq_zero_iff] at h
  rcases h with h1 | ⟨_, h2⟩
  · exact hp h1
  · have hd : (X ^ (2 : ℕ) + C c).natDegree = 2 := by compute_degree!
    rw [h2, natDegree_C] at hd; exact absurd hd (by norm_num)

/-- The polynomial Mahler substitution `p ↦ p(z²+c)` as a `ℂ`-algebra hom into `ℂ(z)`. -/
noncomputable def mahlerPolyHom (c : ℂ) : Polynomial ℂ →ₐ[ℂ] RatFunc ℂ :=
  (IsScalarTower.toAlgHom ℂ (Polynomial ℂ) (RatFunc ℂ)).comp (aeval (X ^ (2 : ℕ) + C c))

@[aesop safe]
theorem mahlerPolyHom_apply (c : ℂ) (p : ℂ[X]) :
    mahlerPolyHom c p = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X ^ (2 : ℕ) + C c)) := by
  rw [mahlerPolyHom, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  congr 1

@[aesop safe]
theorem mahlerPolyHom_ne_zero {c : ℂ} {p : ℂ[X]} (hp : p ≠ 0) : mahlerPolyHom c p ≠ 0 := by
  rw [mahlerPolyHom_apply,
    map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))]
  exact comp_quadratic_ne_zero hp

/-- **The Mahler endomorphism on `ℂ(z)` (`z ↦ z²+c`).** The unique `ℂ`-algebra endomorphism of
`RatFunc ℂ` extending `p ↦ p(z²+c)`; it acts on a quotient as `mahlerHom (p/q) = p(z²+c)/q(z²+c)`. -/
noncomputable def mahlerHom (c : ℂ) : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.liftAlgHom (mahlerPolyHom c) (by
    intro x hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact mahlerPolyHom_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp hx))

/-- `mahlerHom` on the image of a polynomial `p` is `p(z²+c)`. -/
@[aesop safe]
theorem mahlerHom_algebraMap (c : ℂ) (p : ℂ[X]) :
    mahlerHom c (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X ^ (2 : ℕ) + C c)) := by
  rw [mahlerHom]
  have := RatFunc.liftAlgHom_apply_div (φ := mahlerPolyHom c)
    (hφ := by intro x hx; rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
              exact mahlerPolyHom_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp hx)) p 1
  simp only [map_one, div_one] at this
  rw [this, mahlerPolyHom_apply]

/-- **`mahlerHom g = g² ⟹ g constant` (PROVED).** A rational function fixed by the Mahler operator up
to squaring is constant (for `c ≠ 0`): pushing `mahlerHom` through `g = num/denom` and cross-multiplying
gives the polynomial Mahler cross-equation `num(σz)·denom² = num²·denom(σz)`, refuted-unless-constant by
`ratfunc_mahler_const`. This is the field-level form consumed by the n≥2 norm-descent: `N(φ_c)` satisfies
`mahlerHom(N) = N²`, hence is constant. -/
@[aesop safe]
theorem mahler_eq_sq_imp_const {c : ℂ} (hc : c ≠ 0) {g : RatFunc ℂ}
    (h : mahlerHom c g = g ^ (2 : ℕ)) :
    (RatFunc.num g).natDegree = 0 ∧ (RatFunc.denom g).natDegree = 0 := by
  apply ratfunc_mahler_const hc
  have hinj := IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)
  set N := RatFunc.num g with hN_def
  set D := RatFunc.denom g with hD_def
  have hD : D ≠ 0 := hD_def ▸ RatFunc.denom_ne_zero g
  have haD : algebraMap (Polynomial ℂ) (RatFunc ℂ) D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hD
  have haDσ : algebraMap (Polynomial ℂ) (RatFunc ℂ) (D.comp (X ^ (2 : ℕ) + C c)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact comp_quadratic_ne_zero hD
  have hgeq : g = algebraMap (Polynomial ℂ) (RatFunc ℂ) N
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) D := (RatFunc.num_div_denom g).symm
  have hmh : mahlerHom c g
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (N.comp (X ^ (2 : ℕ) + C c))
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (D.comp (X ^ (2 : ℕ) + C c)) := by
    rw [hgeq, map_div₀, mahlerHom_algebraMap, mahlerHom_algebraMap]
  have hg2 : g ^ (2 : ℕ) = (algebraMap (Polynomial ℂ) (RatFunc ℂ) N) ^ (2 : ℕ)
      / (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) ^ (2 : ℕ) := by rw [hgeq, div_pow]
  rw [hmh, hg2, div_eq_div_iff haDσ (pow_ne_zero 2 haD)] at h
  rw [← map_pow, ← map_mul, ← map_pow, ← map_mul] at h
  exact hinj h

/-- **Eval-at-0 extraction of the norm-Mahler equation (PROVED).** From the bivariate identity
`(m^σ)(Y²) = s·m(Y)·m(−Y)` over `ℂ(z)` (where `m^σ` applies the Mahler operator to the `Y`-coefficients),
evaluating at `Y = 0` yields `mahlerHom(m.coeff 0) = s·(m.coeff 0)²`. The constant term `m.coeff 0` is
(up to sign) the **norm** of the algebraic element; with `s` a unit this feeds `mahler_eq_sq_imp_const`
to force the norm constant. This is the pure-algebra core of the n≥2 norm-descent — the carrier only
needs to supply the identity `hid`. -/
@[aesop safe]
theorem mahler_coeff_zero_of_identity {c : ℂ} {m : Polynomial (RatFunc ℂ)} {s : RatFunc ℂ}
    (hid : (m.map (mahlerHom c).toRingHom).comp (X ^ (2 : ℕ)) = C s * m * m.comp (-X)) :
    mahlerHom c (m.coeff 0) = s * (m.coeff 0) ^ (2 : ℕ) := by
  have h := congrArg (Polynomial.eval 0) hid
  have hx2 : (X ^ (2 : ℕ) : (RatFunc ℂ)[X]).eval (0 : RatFunc ℂ) = 0 := by simp
  have hm0 : m.eval 0 = m.coeff 0 := (coeff_zero_eq_eval_zero m).symm
  rw [eval_comp, hx2, eval_map, eval₂_at_zero, eval_mul, eval_mul, eval_C, eval_comp,
      eval_neg, eval_X, neg_zero, hm0] at h
  rw [show (mahlerHom c).toRingHom (m.coeff 0) = mahlerHom c (m.coeff 0) from rfl] at h
  rw [h]; ring

end MahlerPolynomial
