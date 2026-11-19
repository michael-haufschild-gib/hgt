# Weil's theorem for curves over finite fields

- **ID:** leftovers-weil-theorem-for-curves
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION (classical theorem, no novelty)
- **Source:** [Weil-cone anatomy](../2-fully-proven/leftovers/weil-cone-pole-duality-anatomy.md), item (C)
- **Lean folder:** `formal/GaloisForLFunctions/CurvesOverFiniteFields/`, umbrella `CurvesOverFiniteFields.lean`

## Target

Let F be a finite field with q elements and K/F an algebraic function field of one variable with
exact constant field F, of genus g. Write B_d for the number of places of degree d and
N_r = Σ_{d | r} d B_d. Then there are α_1, …, α_{2g} ∈ ℂ with |α_i| = √q and
N_r = q^r + 1 − Σ_i α_i^r for all r ≥ 1. Consequently, with L = log q and weights
λ_K(k) = L·N_k on degrees k ≥ 1, the function-field Weil functional

W_{q,g}(λ, φ) = L Σ_{k∈ℤ} φ(kL)(q^{k/2} + q^{−k/2}) + (2g−2) L φ(0) − Σ_{k≥1} λ(k) q^{−k/2}(φ(kL) + φ(−kL))

equals L Σ_k φ(kL) Σ_i (α_i/√q)^k and is ≥ 0 on autocorrelations φ = f ⋆ f̃. This is item (C):
every curve of genus g over F lies in the cone of every other.

## Proof route (Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1, 3.6, 5)

1. Places as proper valuation subrings containing F; each is the local ring of a height-one prime
   of the integral closure of F[x] or F[1/x]; residue fields finite; finitely many places of each degree.
2. Divisors, principal divisors, deg (x)_0 = deg (x)_∞ = [K : F(x)].
3. Riemann–Roch spaces L(D): finite dimension, ℓ(D) ≤ deg D + 1; Riemann's inequality, genus.
4. Adeles, index of speciality, Weil differentials, canonical class; Riemann–Roch.
5. Zeta function: finiteness of effective divisors of given degree and of the class number;
   F. K. Schmidt (a divisor of degree 1); rationality Z = L/((1−t)(1−qt)), deg L = 2g, functional equation.
6. Constant field extensions K·F_{q^r}: place splitting, genus invariance, N_1(K_r) = N_r(K).
7. Bombieri's upper bound N_1 ≤ q + 1 + (2g+1)√q for square q > (g+1)^4.
8. Lower bound through a Galois extension of F(x) and its intermediate fields.
9. |α_i| = √q from two-sided bounds for all r; explicit formula and positivity of W_{q,g}.

## Status

Modules in `CurvesOverFiniteFields/`, all checked, wired into `CurvesOverFiniteFields.lean`:

| Module | Content |
|---|---|
| `Basic` | valuation ring at infinity is a DVR; finite chart (integral closure of F[x]) and infinite chart (integral closure of the ring at infinity) are Dedekind with fraction field K; places |
| `Residues` | residue field at infinity is spanned by constants; residue rings of all places are finite over F; finitely many infinite places |
| `ValuationSpaces` | spaces cut out by valuation bounds; raising a divisor by one at v adds exactly dim_F(R/v) (`finrank_valSpace_step`) |
| `MayerVietoris` | dim N/M = dim (N⊓U)/(M⊓U) + dim (N⊔U)/(M⊔U) |
| `EulerCharacteristic` | χ = dim(M⊓U) − dim V/(M⊔U) grows by dim N/M, finiteness both ways (`euler_step`, `euler_step_down`) |
| `Divisors` | divisors on finite and infinite places, `Divisor.deg`, L(D) = I(D) ⊓ J(D), H¹(D) = K/(I(D) ⊔ J(D)), χ = ℓ − h¹; one-place steps (`chi_raiseFin`, `chi_raiseInf`); if L(0), H¹(0) are finite then every D has finite L, H¹ and χ(D) = deg D + χ(0) (`chi_eq_deg_add_chi_zero`) |
| `Genus` | exact constant field ⇒ L(0) = F, ℓ(0) = 1; K/(A + O∞) finite-dimensional; genus g = h¹(0); Riemann's theorem ℓ(D) − h¹(D) = deg D + 1 − g (`riemann_roch_chi`), ℓ(D) ≥ deg D + 1 − g (`riemann_inequality`) |
| `Duality` | Weil differentials Ω(D) = (I(D) + J(D))^⊥, dim Ω(D) = h¹(D); h¹(D) = 0 in high degree; nonzero differentials are K-proportional; canonical divisor as the largest level; principal divisors `pdiv`; Riemann–Roch ℓ(D) − ℓ(W − D) = deg D + 1 − g, deg W = 2g − 2, ℓ(W) = g (`riemann_roch`) |
| `PrincipalDivisors` | `pdiv` multiplicative; multiplication by x maps I(D), J(D) onto I(D + (x)), J(D + (x)), so ℓ and h¹ are class invariants; deg (x) = 0 (`deg_pdiv`); x ∈ L(D) ⇔ (x) ≤ D; (x) = 0 only for constants |
| `FiniteCounts` | F finite: Frobenius a^{q^N} ≡ a mod P for deg P ∣ N; finitely many places of degree ≤ n (`finite_finPlace_deg_le`); finitely many effective divisors of each degree (`finite_effective`) |
| `ClassGroup` | principal divisors as a subgroup; effective divisors in the class of D ↔ projective space of L(D); their number is 1 + q + ⋯ + q^{ℓ(D)−1} (`card_effClass`) |

Next (step 5): finitely many classes of each degree (an effective representative of D + mP₀ once
deg ≥ g), class number h; A_n = Σ_classes (1 + ⋯ + q^{ℓ−1}) and A_n = h(1 + ⋯ + q^{n−g}) for
n > 2g − 2; Z(t) rational with denominator in t^δ (δ = gcd of degrees). Then constant field
extensions K_r = K ⊗ F_{q^r} (step 6): integral closure A ⊗ F_{q^r}, place splitting,
Z_{K_r}(t^r) = Π_{ζ^r=1} Z_K(ζt), F. K. Schmidt δ = 1, N_1(K_r) = N_r(K); then steps 7–9
(Bombieri's upper bound; lower bound through a Galois closure of K/F(x) and twisted Frobenius).
