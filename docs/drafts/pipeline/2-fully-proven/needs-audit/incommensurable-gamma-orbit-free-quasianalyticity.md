# Arbitrary-scale Gamma products obey an alien-charge hypertranscendence law

- **ID:** `incommensurable-gamma-orbit-free-quasianalyticity`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED] [NOVELTY UNVERIFIED]`
- **Statement:** Every finite signed product of positive-scale affine Gamma factors lies in exactly
  one of two positive carriers. Vanishing scaled Borel-residue character forces an
  exponential--rational product; nonvanishing character forces the product, its logarithmic
  derivative, and its second logarithmic derivative to be hypertranscendental. No rational
  relation among the scales is required.

## 1. Object and intrinsic charge

Let

```text
G(s)=exp(alpha s) product_(j=1)^d Gamma(lambda_j s+mu_j)^m_j,
lambda_j>0,  m_j in Z\{0}.                                 (1)
```

Put

```text
Psi=G'/G,
Tau=Psi'
   =sum_j m_j lambda_j^2 psi'(lambda_j s+mu_j).            (2)
```

The companion theorem
`../not_new_scientific_knowledge/scaled-gamma-borel-residue-character-completeness.md` defines the
intrinsic scaled charge

```text
R_G(t)=sum_(j: t/lambda_j in Z\{0})
          m_j lambda_j exp(-2 pi i (t/lambda_j)mu_j),
t in R\{0}.                                                (3)
```

The residue of the formal Borel transform of the complete Stirling expansion `hat Tau` at
`xi=2 pi i t` is `2 pi i t R_G(t)`. It also proves

```text
R_G=0
  iff every rational commensurability class has zero shift-orbit charge
  iff G(s)=C exp(beta s)R(s),  R in C(s)^x.                (4)
```

Thus `R_G` already classifies the elementary branch. What remained was to identify positively the
carrier forced by `R_G!=0`.

## 2. The finite commuting-shift constraint

For each factor set

```text
h_j=1/lambda_j,
Delta_j f(s)=f(s+h_j)-f(s).                                (5)
```

The trigamma recurrence gives

```text
Delta_j(m_j lambda_j^2 psi'(lambda_j s+mu_j))
  =-m_j lambda_j^2/(lambda_j s+mu_j)^2 in C(s).            (6)
```

Translations commute. Applying every `Delta_k` to `(2)`, and in the `j`th summand applying
`Delta_j` first, gives

```text
Delta_1...Delta_d Tau
 =sum_j (product_(k!=j) Delta_k)
         (-m_j lambda_j^2/(lambda_j s+mu_j)^2)
 in C(s).                                                  (7)
```

The same identity holds for the complete Laurent expansion `hat Tau in C((s^(-1)))`.

The bridge
`../not_new_scientific_knowledge/finite-commuting-shift-peeling-hypertranscendence-law.md` states
that any `f in C((s^(-1)))` satisfying

```text
Delta_1...Delta_d f in C(s)                               (8)
```

is rational or hypertranscendental over `C(s)`. Its proof repeatedly applies the
Adamczewski--Dreyfus--Hardouin one-shift dichotomy: if `Delta_h f=r in C(s)`, then `f` is rational
or HT. Assuming differential algebraicity peels one difference at a time and forces every
intermediate object, finally `f`, into `C(s)`. No common shift and no commensurability relation are
used.

## 3. Exact arbitrary-scale DA/HT classification

`[PROVED]` For `(1)`, exactly one of the following alternatives holds.

```text
R_G=0
  -> G=C exp(beta s)R(s), R in C(s)^x;
  -> Psi and Tau are rational and G is DA over C(s).       (9)

R_G!=0
  -> hat Tau, Tau, Psi, and G are HT over C(s).            (10)
```

### Proof

If `R_G=0`, equivalence `(4)` gives the asserted exponential--rational form. Its logarithmic
derivative and second logarithmic derivative are rational, and the product is differentially
algebraic.

Suppose `R_G!=0`. Identity `(7)` and the peeling theorem imply that `hat Tau` is rational or HT.
Because `hat Tau=O(s^(-1))`, a rational representative would be proper. Partial fractions reduce it
to `(s-a)^(-k)`, whose expansion at infinity has formal Borel transform

```text
B((s-a)^(-k))=xi^(k-1) exp(a xi)/(k-1)!,                  (8a)
```

an entire function. Hence every proper rational representative has entire Borel transform. The
explicit Borel germ of `hat Tau` has a unique meromorphic continuation given by the companion
formula, while `(3)` supplies a nonzero residue at some `2 pi i t`. Uniqueness of analytic
continuation contradicts rationality. Therefore `hat Tau` is HT.

If the analytic function `Tau` satisfied an algebraic differential equation over `C(s)`, taking its
complete upper-sector Poincare expansion would give the same equation for `hat Tau`; hence `Tau` is
HT. If `Psi` were DA, then `Psi'=Tau` would be DA. If `G` were DA, then the differential-field
closure of DA elements would make `G'/G=Psi` DA. Both conclusions contradict the preceding step.
This proves `(10)` and the dichotomy.

## 4. Positive carrier law

The theorem is not stated as the failure of a common-shift proof. It specifies the forced state of
every finite product:

> **Scaled-charge carrier law.** A finite signed positive-scale Gamma product must carry either an
> exponential--rational reduction or a nonzero scaled alien charge together with
> hypertranscendence. Incommensurable scales create no third differentially algebraic carrier.

The constraint hierarchy is

```text
finite Gamma datum
 -> finite commuting-shift rational source
 -> rational branch or HT branch
 -> R_G selects the branch exactly.                        (11)
```

This is constraint-side classification. The shifts do not propagate the object from initial data;
they jointly force which carrier the fixed object occupies.

## 5. Positive boundary resource law

The HT branch makes the logarithmic-derivative asymptotic map injective. Indeed, any nonzero
differential rational expression in `Psi` has a nonzero formal expansion, since otherwise its
numerator would give a differential algebraic relation for `hat Psi` and hence for `hat Tau`.

Under the neutral/recurrent hypotheses of the proved
`../not_new_scientific_knowledge/quasianalytic-exponential-log-phase-jet-law.md` theorem, the
Stirling normal form

```text
G=A exp(kappa s)s^gamma U(s),
hat U in 1+s^(-1)C[[s^(-1)]]                              (12)
```

therefore has an injective upper Poincare coefficient field and lands in the positive carrier chain

```text
C(s)<G>
 -> C[z,exp(kappa z),exp(-kappa z)]
 -> C[exp(kappa z),exp(-kappa z)].                         (13)
```

Arbitrary finite scale rank can enlarge the scaled alien-charge support, but it does not create an
unbounded terminal compact-character module. Gamma data can supply HT and arbitrarily deep local
polynomial jets while the recurrent compact phase remains finite-dimensional.

Consequently, for primes through `N`, define

```text
V_N=span_Q{log p:p<=N},
A_N=V_N/(V_N intersection D),                              (14)
```

where `D` is the differential-state frequency carrier of the proposed construction. Then every
successful cofinal architecture is forced to instantiate the arithmetic complement `A_N` or grow
`D` so that

```text
dim_Q A_N >= pi(N)-dim_Q D.                                (15)
```

This is the positive conclusion: the missing prime information must live somewhere identifiable.
It cannot be replaced merely by adding finitely many affine Gamma factors of arbitrary scales.

## 6. Required carriers in classical RH architectures

The theorem does not reject an RH-equivalent criterion. It tells each implementation what it must
contain beyond its finite archimedean completion.

1. **Hilbert--Polya and Connes-type spectra.** The operator domain, spectral measure, determinant,
   or quotient geometry must carry `A_N` cofinally and must prove that the carrier survives the
   `1/log N` horizontal boundary layer.
2. **de Branges-type spaces.** The Hermite--Biehler phase, canonical-system Hamiltonian, or nested
   space must carry the growing prime-frequency quotient; a fixed Gamma normalization supplies only
   the finite carrier `(13)`.
3. **Nyman--Beurling-type approximation.** The approximation spaces, dilation coefficients, or
   closure defect must retain the prime quotient through the limit. The archimedean factor may
   normalize the boundary but cannot pay the cofinal dimension in `(15)`.
4. **Weil positivity.** The test-function space or quadratic-form completion must represent the
   prime atoms and preserve them under completion; positivity without that source carrier is not
   yet an implementation.
5. **Li-type criteria.** The coefficient hierarchy must carry unbounded arithmetic state. Finite
   Gamma normalization contributes a fixed phase-jet carrier, so the required growth must occur in
   the Li coefficients, their generating function, or an equivalent divisor object.

These are positive implementation obligations: name the carrier, prove its dimension or injectivity,
and prove that the global completed constraint preserves it cofinally.

## 7. Attacks and boundaries

1. **Borel poles alone do not imply HT.** The proof uses them only to exclude the rational branch of
   the independent shift-peeling dichotomy.
2. **Finiteness is load-bearing.** A family whose number of Gamma factors grows with `N` may itself
   pay an unbounded state-complexity cost; the theorem requires that cost to be counted rather than
   declaring it impossible.
3. **The Laurent field is load-bearing.** Global meromorphic shift equations admit DA periodic and
   exponential solutions. The ADH `S_infinity` theorem applies to complete Laurent expansions at
   infinity.
4. **Positive scales are assumed.** Reflection of negative slopes introduces trigonometric carriers
   that require a separate classification.
5. **The boundary statement uses its stated neutral/recurrent hypotheses.** The DA/HT dichotomy
   `(9)`--`(10)` itself does not require neutrality or recurrence.
6. **No categorical RH no-go is claimed.** An architecture remains viable when it supplies the
   arithmetic complement or pays the corresponding growing-state cost.

## 8. Parent and novelty audit

- Adamczewski--Dreyfus--Hardouin prove the one-shift rational-or-HT dichotomy for Laurent-series
  solutions of rational linear shift equations.
- The trigamma recurrence, Gamma multiplication, Bernoulli Borel transform, and finite
  Fourier/Vandermonde uniqueness are classical.
- The many-shift peeling theorem is a short induction from the one-shift parent result and is
  classified `[BRIDGE]`.
- Preliminary searches did not locate the exact arbitrary-scale character classification
  `(9)`--`(10)` or its proof by combining scaled Borel residues with finite-shift peeling.

The paper theorem is complete, but its scientific novelty remains `[NOVELTY UNVERIFIED]` until a
full priority search across difference Galois theory, Gamma-product HT, and resurgent analysis is
independently checked.

Primary adjacent sources:

- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*,
  J. Amer. Math. Soc. 34 (2021), 475--503, Theorem 1.2, Case `S_infinity`.
- S. Bank, R. Kaufman, *A note on Holder's theorem concerning the Gamma function*, Math. Ann. 232
  (1978), 115--120.
- D. Sauzin, *Variations on the Resurgence of the Gamma Function*, arXiv:2112.15226.

## 9. Lean status

The tree already contains `trigamma_recurrence` in `GammaDifferentialFE.lean` and the common-shift
finite-pole obstruction `no_finitePole_solution_digammaShiftDerivative` in
`GammaProjectiveBoundary.lean`. It has no formal version of the ADH Laurent-series shift dichotomy,
Gamma Stirling/Borel residue calculus, or analytic-to-formal ADE transfer. The complete claim is
therefore not formalized and remains stage 2. Moving it to stage 3 requires an unconditional Lean
theorem for the whole classification, not wrappers for the elementary finite-difference induction.

The Section 2 many-shift peeling bridge (`(7)`–`(8)`) is formalized abstractly and axiom-free in
`formal/GaloisForLFunctions/FiniteCommutingShiftPeeling.lean`:

```text
shiftWord_dichotomy   -- given the one-shift dichotomy `R(Δ i g) → R g ∨ H g` and DA-descent
                      --   `H(Δ i g) → H g`, any shift word landing f in R forces R f ∨ H f
ht_of_ht_shiftWord    -- differential algebraicity descends through a shift word
```

Here the one-shift Adamczewski–Dreyfus–Hardouin Laurent dichotomy enters as the hypothesis `dich`;
mathlib has no difference-Galois substrate to discharge it, so the concrete classification `(9)`–`(10)`
(and the scaled-Borel-residue branch selector) remains the open part of the stage-3 gate.

## Gates

- [x] arbitrary positive scales allowed
- [x] scaled alien character and vanishing classification proved
- [x] finite commuting-shift rational constraint proved
- [x] nonzero-character HT implication proved
- [x] exact DA/HT dichotomy proved
- [x] positive carrier and RH implementation laws stated
- [x] edge cases and overclaims attacked
- [ ] full parent-literature and priority audit
- [~] Lean formalization: Section 2 finite-commuting-shift peeling bridge formalized abstractly and
  axiom-free (`FiniteCommutingShiftPeeling.lean`); concrete ADH one-shift dichotomy + scaled-Borel
  branch selector `(9)`–`(10)` still open (mathlib lacks the difference-Galois substrate)
