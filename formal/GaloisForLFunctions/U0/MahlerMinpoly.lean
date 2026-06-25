/-
# Abstract Mahler divisibility: `minpoly K φ ∣ (minpoly K φ)^σ(Y²)`

The structural entry to the `n ≥ 2` norm-descent. If `φ` is algebraic over a field `K` and there is a
"Mahler operator" `τ : L → L` on the extension lying over a field endomorphism `σ : K → K`
(`τ ∘ algebraMap = algebraMap ∘ σ`) with `τ φ = φ²`, then the minimal polynomial `m = minpoly K φ`
**divides** its `σ`-transform composed with squaring, `(m.map σ).comp(X²)`: indeed `φ` is a root of the
latter, because evaluating `(m.map σ)` at `φ² = τ φ` equals `τ(m(φ)) = τ(0) = 0`.

For the Böttcher application `K = ℂ(z)`, `σ = mahlerHom` (`z ↦ z²+c`), `L` a function field where the
Böttcher coordinate `φ_c` lives, `τ` = precomposition by `z ↦ z²+c`, and `τ φ_c = φ_c²` is the
functional equation. The companion divisibility by `(m.comp(-X))` (from `τ(−φ) = φ²` as well) assembles
the full identity `(m^σ)(Y²) = ±·m(Y)·m(−Y)`.
-/
import GaloisForLFunctions.U0.MahlerEndo
import GaloisForLFunctions.U0.PolyAsymptotics

open Polynomial Filter Topology

namespace MahlerPolynomial

/-- **Evaluation transports along the Mahler operator.** For a Mahler pair `(σ, τ)` and `φ` with
`τ φ = φ²`, evaluating the `σ`-transform `p^σ` at `φ²` equals `τ` applied to `p` evaluated at `φ`:
`(p.map σ).aeval(φ²) = τ(p.aeval φ)`. Both sides are ring homs `K[Y] → L` agreeing on `C k` (`hcompat`)
and on `X` (`hτφ`). -/
theorem aeval_map_mahler {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : K →+* K) (τ : L →+* L)
    (hcompat : ∀ k : K, τ (algebraMap K L k) = algebraMap K L (σ k))
    {φ : L} (hτφ : τ φ = φ ^ 2) (p : K[X]) :
    aeval (φ ^ 2) (p.map σ) = τ (aeval φ p) := by
  induction p using Polynomial.induction_on with
  | C k => simp [hcompat]
  | add p q hp hq => simp [hp, hq]
  | monomial n k _ =>
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      map_mul, map_pow, aeval_C, aeval_X, hcompat, hτφ]

/-- **Abstract Mahler divisibility (PROVED).** With a Mahler operator `τ` over `σ` and `τ φ = φ²`, the
minimal polynomial of `φ` over `K` divides `(minpoly K φ).map σ ∘ (X²)` — the `σ`-twisted,
`Y↦Y²`-substituted minimal polynomial — because `φ` is a root of it (`aeval_map_mahler` +
`minpoly.aeval`). This is `P(z,Y) ∣ P(σz,Y²)` of the Mahler method, here as clean field theory. -/
theorem minpoly_dvd_mahler {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : K →+* K) (τ : L →+* L)
    (hcompat : ∀ k : K, τ (algebraMap K L k) = algebraMap K L (σ k))
    {φ : L} (hφ : IsIntegral K φ) (hτφ : τ φ = φ ^ 2) :
    minpoly K φ ∣ ((minpoly K φ).map σ).comp (X ^ 2) := by
  apply minpoly.dvd
  rw [aeval_comp, show aeval φ (X ^ 2 : K[X]) = φ ^ 2 by simp,
      aeval_map_mahler σ τ hcompat hτφ, minpoly.aeval, map_zero]

/-- **Bivariate Mahler identity from the divisibility (PROVED).** If `σ : K → K` is an injective field
endomorphism and `m ∈ K[Y]` is nonconstant with `m ∣ (m^σ)(Y²)` and `m(Y), m(−Y)` coprime, then
`(m^σ)(Y²) = s·m(Y)·m(−Y)` for a constant `s`. Proof: `(m^σ)(Y²)` is even in `Y`, so `m(−Y) ∣ (m^σ)(Y²)`
too; coprimality gives `m·m(−Y) ∣ (m^σ)(Y²)`, and both have degree `2·deg m`, so the cofactor is a
constant. This is the structural identity whose `Y=0` evaluation (`mahler_coeff_zero_of_identity`) drives
the norm-descent. -/
theorem mahler_identity_of_coprime {K : Type*} [Field K] {σ : K →+* K} (hσ : Function.Injective σ)
    {m : K[X]} (hdeg : 0 < m.natDegree)
    (hdvd : m ∣ (m.map σ).comp (X ^ 2)) (hcop : IsCoprime m (m.comp (-X))) :
    ∃ s : K, (m.map σ).comp (X ^ 2) = C s * m * m.comp (-X) := by
  have hmne : m ≠ 0 := fun h => by simp [h] at hdeg
  have hmcdeg : (m.comp (-X)).natDegree = m.natDegree := by
    rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  have hmcne : m.comp (-X) ≠ 0 := fun h => by rw [h, natDegree_zero] at hmcdeg; omega
  have hdvd2 : m.comp (-X) ∣ (m.map σ).comp (X ^ 2) := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c.comp (-X), ?_⟩
    have hQeven : ((m.map σ).comp (X ^ 2)).comp (-X) = (m.map σ).comp (X ^ 2) := by
      rw [comp_assoc, pow_comp, X_comp, neg_sq]
    rw [← mul_comp, ← hc, hQeven]
  obtain ⟨R, hR⟩ := hcop.mul_dvd hdvd hdvd2
  have hQne : (m.map σ).comp (X ^ 2) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    rintro (h1 | ⟨_, h2⟩)
    · exact (Polynomial.map_ne_zero_iff hσ).mpr hmne h1
    · have : (X ^ 2 : K[X]).natDegree = 2 := natDegree_X_pow 2
      rw [h2, natDegree_C] at this; exact absurd this (by norm_num)
  have hRne : R ≠ 0 := by
    intro h; rw [h, mul_zero] at hR; exact hQne hR
  have hdegQ : ((m.map σ).comp (X ^ 2)).natDegree = 2 * m.natDegree := by
    rw [natDegree_comp, natDegree_X_pow, natDegree_map_eq_of_injective hσ]; ring
  have hRdeg : R.natDegree = 0 := by
    have key : ((m.map σ).comp (X ^ 2)).natDegree
        = (m * m.comp (-X)).natDegree + R.natDegree := by
      rw [hR, natDegree_mul (mul_ne_zero hmne hmcne) hRne]
    rw [hdegQ, natDegree_mul hmne hmcne, hmcdeg] at key
    omega
  obtain ⟨s, hs⟩ := natDegree_eq_zero.mp hRdeg
  exact ⟨s, by rw [hR, ← hs]; ring⟩

/-- **The norm relation, assembled over `ℂ(z)` (PROVED).** For the Mahler operator `σ = mahlerHom c`,
a nonconstant `m ∈ ℂ(z)[Y]` with `m ∣ (m^σ)(Y²)` and `m(Y), m(−Y)` coprime yields the norm-Mahler
relation `mahlerHom(m.coeff 0) = s·(m.coeff 0)²` for a constant `s`. Chains `mahler_identity_of_coprime`
(divisibility → bivariate identity) with `mahler_coeff_zero_of_identity` (eval at `Y=0`). The constant
term `m.coeff 0` is, up to sign, the norm of the algebraic element; with `s` the appropriate unit,
`mahler_eq_sq_imp_const` then forces the norm constant — completing the norm-descent once the carrier
supplies the divisibility `hdvd` (via `minpoly_dvd_mahler`). -/
theorem mahler_norm_relation {c : ℂ} {m : (RatFunc ℂ)[X]} (hdeg : 0 < m.natDegree)
    (hdvd : m ∣ (m.map (mahlerHom c).toRingHom).comp (X ^ 2))
    (hcop : IsCoprime m (m.comp (-X))) :
    ∃ s : RatFunc ℂ, mahlerHom c (m.coeff 0) = s * (m.coeff 0) ^ 2 := by
  obtain ⟨s, hs⟩ := mahler_identity_of_coprime
    (σ := (mahlerHom c).toRingHom) (mahlerHom c).toRingHom.injective hdeg hdvd hcop
  exact ⟨s, mahler_coeff_zero_of_identity hs⟩

/-- **Carrier ⟹ norm relation (PROVED).** The complete algebraic norm-descent, as a single theorem
taking the *carrier* as hypotheses: a field `L ⊇ ℂ(z)` with a Mahler operator `τ` over `mahlerHom`
(`hcompat`), an algebraic `φ` with `τ φ = φ²` whose minimal polynomial is nonconstant with `m(Y),m(−Y)`
coprime. Then the constant term of `minpoly` (= ±norm of `φ`) satisfies the norm-Mahler equation
`mahlerHom(m.coeff 0) = s·(m.coeff 0)²`. Chains `minpoly_dvd_mahler` (functional equation ⟹ divisibility)
with `mahler_norm_relation` (divisibility ⟹ norm relation). The *only* inputs are carrier data — for the
Böttcher application `L = meroField(escapeOpen)`, `τ` = precomposition by `z↦z²+c`, `τ φ_c = φ_c²` from
`bottcherCoord_quadratic`. With `s` a sign (monic `m`), `mahler_eq_sq_imp_const` then forces the norm
constant — the first decoupled constraint of the n≥2 Nishioka system. -/
theorem carrier_norm_relation {c : ℂ} {L : Type*} [Field L] [Algebra (RatFunc ℂ) L]
    (τ : L →+* L)
    (hcompat : ∀ k : RatFunc ℂ,
      τ (algebraMap (RatFunc ℂ) L k) = algebraMap (RatFunc ℂ) L (mahlerHom c k))
    {φ : L} (hφ : IsIntegral (RatFunc ℂ) φ) (hτφ : τ φ = φ ^ 2)
    (hdeg : 0 < (minpoly (RatFunc ℂ) φ).natDegree)
    (hcop : IsCoprime (minpoly (RatFunc ℂ) φ) ((minpoly (RatFunc ℂ) φ).comp (-X))) :
    ∃ s : RatFunc ℂ, mahlerHom c ((minpoly (RatFunc ℂ) φ).coeff 0)
      = s * ((minpoly (RatFunc ℂ) φ).coeff 0) ^ 2 :=
  mahler_norm_relation hdeg
    (minpoly_dvd_mahler (mahlerHom c).toRingHom τ hcompat hφ hτφ) hcop

/-- **The degree-2 candidate forces the exceptional values (PROVED).** If `φ` satisfies the only
degree-2 candidate minimal polynomial `φ² = zφ + c/2` (the one the n=2 symmetric-function/norm analysis
pins down) together with its `σ`-transform `φ⁴ = (z²+c)φ² + c/2` (the shadow of `φ(z²+c)=φ(z)²`), then
`c²+2c = 0` — i.e. `c ∈ {0,−2}`, exactly the exceptional Böttcher values. So for nonexceptional `c` the
degree-2 candidate cannot satisfy the functional equation: this is the concrete functional-equation
obstruction at the heart of the `n=2` case (the remaining input — that `b₁=−z` is *forced*, ruling out
higher-degree `b₁` — is Ritt-type semi-conjugacy rigidity). -/
theorem candidate_forces_exceptional {R : Type*} [CommRing R] [Algebra ℂ R] [Nontrivial R]
    {z φ : R} {c : ℂ}
    (h1 : φ ^ 2 = z * φ + algebraMap ℂ R (c / 2))
    (h2 : φ ^ 4 = (z ^ 2 + algebraMap ℂ R c) * φ ^ 2 + algebraMap ℂ R (c / 2)) :
    c ^ 2 + 2 * c = 0 := by
  have hinj := FaithfulSMul.algebraMap_injective ℂ R
  have hhalf : algebraMap ℂ R (c / 2) + algebraMap ℂ R (c / 2) = algebraMap ℂ R c := by
    rw [← map_add]; congr 1; ring
  have e : (z * φ + algebraMap ℂ R (c / 2)) ^ 2
      = (z ^ 2 + algebraMap ℂ R c) * φ ^ 2 + algebraMap ℂ R (c / 2) := by
    rw [← h1, ← h2]; ring
  have hkey : algebraMap ℂ R (c ^ 2 + 2 * c) = 0 := by
    have hc2 : algebraMap ℂ R (c ^ 2 + 2 * c)
        = algebraMap ℂ R (c / 2) * algebraMap ℂ R (c / 2) * 4
          + (algebraMap ℂ R (c / 2) + algebraMap ℂ R (c / 2)) * 2 := by
      rw [show (c ^ 2 + 2 * c : ℂ) = (c / 2) * (c / 2) * 4 + ((c / 2) + (c / 2)) * 2 by ring]
      push_cast [map_add, map_mul, map_ofNat]
      ring
    rw [hc2]
    linear_combination -4 * e - 4 * (algebraMap ℂ R c) * h1
      + 4 * (z * φ + algebraMap ℂ R (c / 2)) * hhalf
  have := hinj (hkey.trans (map_zero (algebraMap ℂ R)).symm)
  exact this

/-- **Semi-conjugacy rigidity in degree 1 (PROVED).** If the degree-1 polynomial `b₁ = −X + a₀`
satisfies the semi-conjugacy `b₁(z²+c) = −b₁² + 2β`, then `a₀ = 0` and `c = −2β` — i.e. `b₁ = −z` and
`β = −c/2`. (Coefficient comparison: the `X¹` coefficient forces `a₀=0`, the `X⁰` coefficient forces
`c=−2β`.) Combined with the deg-forcing `deg b₁ = 1` (from the asymptotic `φ_c ~ z`), this pins the n=2
minimal polynomial to the candidate `Y²−zY−c/2`, which `candidate_forces_exceptional` then refutes. -/
theorem semiconj_degree_one {a₀ β c : ℂ}
    (h : (-X + C a₀ : ℂ[X]).comp (X ^ 2 + C c) = -((-X + C a₀) ^ 2) + C (2 * β)) :
    a₀ = 0 ∧ c = -2 * β := by
  have h0 := congrArg (Polynomial.eval (0 : ℂ)) h
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) h
  simp only [eval_comp, eval_add, eval_neg, eval_X, eval_C, eval_pow] at h0 h1
  norm_num at h0 h1
  have ha₀ : a₀ = 0 := by linear_combination (h0 - h1) / 2
  exact ⟨ha₀, by rw [ha₀] at h0; linear_combination -h0⟩

/-- **Pinning the n=2 minimal polynomial (PROVED).** If `b₁ ∈ ℂ[X]` has `b₁(t)/t → −1` along the real
ray (the asymptotic from `φ_c ~ z`) and satisfies the semi-conjugacy `b₁(z²+c) = −b₁² + 2β`, then
`b₁ = −z` and `c = −2β`. Chains the deg-forcing (`b₁(t)/t→−1` finite ⟹ `deg ≤ 1`, and `≠0` since the
limit is `≠0`), the leading-coefficient asymptotic (limit `= leadingCoeff = −1`), and
`semiconj_degree_one`. This pins the candidate minimal polynomial to `Y²−zY−c/2`. -/
theorem b1_pinned {c β : ℂ} {b₁ : ℂ[X]}
    (htend : Tendsto (fun t : ℝ => b₁.eval (t : ℂ) / (t : ℂ)) atTop (𝓝 (-1)))
    (hsc : b₁.comp (X ^ 2 + C c) = -(b₁ ^ 2) + C (2 * β)) :
    b₁ = -X ∧ c = -2 * β := by
  have hdeg : b₁.natDegree ≤ 1 := PolyAsymptotics.natDegree_le_one_of_div_id_tendsto htend
  have hd1 : b₁.natDegree = 1 := by
    rcases Nat.eq_zero_or_pos b₁.natDegree with h0 | hpos
    · exfalso
      rw [natDegree_eq_zero] at h0
      obtain ⟨a, ha⟩ := h0
      rw [← ha] at htend
      simp only [eval_C] at htend
      have hz : Tendsto (fun t : ℝ => (a : ℂ) / (t : ℂ)) atTop (𝓝 0) := by
        simp only [div_eq_mul_inv]
        simpa using (tendsto_const_nhds (x := a)).mul PolyAsymptotics.tendsto_inv_ofReal_atTop
      have := tendsto_nhds_unique htend hz
      norm_num at this
    · omega
  have hcoeff1 : b₁.coeff 1 = -1 := by
    have h2 := PolyAsymptotics.tendsto_eval_div_pow_natDegree b₁
    simp only [hd1, pow_one] at h2
    have heq := tendsto_nhds_unique htend h2
    rw [leadingCoeff, hd1] at heq
    exact heq.symm
  have hform : b₁ = -X + C (b₁.coeff 0) := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
    rw [hcoeff1, map_neg, map_one]; ring
  rw [hform] at hsc ⊢
  obtain ⟨ha₀, hcβ⟩ := semiconj_degree_one hsc
  rw [ha₀, map_zero, add_zero]
  exact ⟨rfl, hcβ⟩

end MahlerPolynomial
