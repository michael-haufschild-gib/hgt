# Prime--Laplace data enter every finite Gamma jet clock but not its factorial Fock colimit

- **ID:** `prime-laplace-gamma-jet-incidence-phase-transition`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / HT-TO-RH INCIDENCE / COMPLETION NO-GO
- **Scientific status:** `[PROVED HERE] [FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `meixner-root-prime-laplace-value-frame.md` and
  `gamma-factorial-fock-polarization-boundary-charge.md`
- **Statement:** The Gamma--Meixner prime source maps Hilbert--Schmidtly into every finite raw-jet
  clock, and all finite clocks together recover every prime coefficient.  Nevertheless the same
  incidence is unbounded into the factorial Fock colimit.  Thus the exact HT-to-RH bridge is a
  faithful projective family with no naive Hilbert direct limit; a relative graph or
  shape-dependent completion is necessary.

## Finite prime-to-jet observation

Fix `theta>0`, put

```text
w_theta(p)=cosh(2log p)^(-theta/2),                       (1)
```

and choose a real base point `x_0>1/2`.  For `a in ell^2(Primes)`, define its weighted
prime--Laplace transform

```text
F_a(z)=sum_p a_p sqrt(w_theta(p)) p^(-z).                 (2)
```

Cauchy--Schwarz and `w_theta(p) asymp p^(-theta)` give locally uniform convergence on

```text
Re z>(1-theta)/2.                                        (3)
```

For `N>=1`, let the finite raw-jet observation be

```text
(J_(theta,x_0,N)a)_j
 =F_a^(j)(x_0)
 =sum_p a_p sqrt(w_theta(p))(-log p)^j p^(-x_0),
0<=j<N.                                                  (4)
```

This is exactly the raw-derivative coordinate system used by the finite Gamma Taylor clocks.

## Every finite observation is Hilbert--Schmidt

Equip the finite jet space with the factorial metric

```text
||y||_(F,N)^2=sum_(j=0)^(N-1)|y_j|^2/j!.                 (5)
```

Then

```text
||J_(theta,x_0,N)||_(S_2)^2
 =sum_p w_theta(p)p^(-2x_0)
    sum_(j=0)^(N-1)(log p)^(2j)/j!<infinity.             (6)
```

For fixed `N`, the inner sum is a polynomial in `log p`, while
`w_theta(p)p^(-2x_0)` is bounded by a constant times `p^(-theta-2x_0)`.  Since
`theta+2x_0>1`, comparison with the integer Dirichlet series proves `(6)`.

Thus every finite HT observation clock receives the complete prime source through a canonical
Hilbert--Schmidt incidence.

## The finite family is jointly faithful

If

```text
J_(theta,x_0,N)a=0 for every N,                           (7)
```

then every derivative of `F_a` at `x_0` vanishes.  Holomorphy on `(3)` makes `F_a` zero on a
neighborhood, hence on the whole half-plane.  Uniqueness of Dirichlet series on the strictly
increasing prime support then gives

```text
a_p sqrt(w_theta(p))=0 for every p,
```

so `a=0`.  Consequently

```text
intersection_(N>=1) ker J_(theta,x_0,N)={0}.             (8)
```

The projective clock family loses no prime coefficient even though each individual clock has
finite rank.

## Factorial Fock colimit no-go

Let `F_Fock` be the Hilbert space of all raw jets with norm

```text
||y||_F^2=sum_(j>=0)|y_j|^2/j!.                          (9)
```

The formal infinite observation sends a prime basis vector `e_p` to the coherent jet

```text
sqrt(w_theta(p))p^(-x_0)
  (1,-log p,(-log p)^2,...).                             (10)
```

Its exact squared Fock norm is

```text
w_theta(p)p^(-2x_0)
  sum_(j>=0)(log p)^(2j)/j!
 =w_theta(p)p^(-2x_0) exp((log p)^2).                    (11)
```

The logarithm of `(11)` is

```text
(log p)^2-(theta+2x_0)log p+O(1),                        (12)
```

which tends to `+infinity`.  Hence even the norms of the individual prime columns are unbounded,
and

```text
J_(theta,x_0,infinity):ell^2(Primes)->F_Fock
```

does not define a bounded operator for any fixed positive shape.

No polynomial prime loss and no Gamma--Meixner factor `p^(-theta)` can overcome the coherent-jet
growth `exp((log p)^2)`.

## Translation covariance and anomaly meaning

On the infinite analytic jet wherever both base points remain in `(3)`, Taylor's theorem gives

```text
jet_(x_0+1)(F_a)=E jet_(x_0)(F_a),                       (13)
```

with `E=exp(D)`.  Its finite shadows are exactly the Gamma clock translations, and their failure
to commute with backward truncation is the factorial boundary transfer already formalized in
HTGeometry.  Therefore `(4)` is a literal incidence of the prime source with the existing HT
clock/anomaly calculus, not a resemblance between two factorial formulas.

Equation `(11)` shows why that incidence must remain projective.  Hypertranscendental clock
capacity supplies all finite observations and the anomaly records their incompatibility; it does
not promise a bounded factorial-Fock direct limit.

## No-go and nontrivial positive successor

The naive proposal

```text
completed prime source -> one factorial Fock Hilbert space -> passive Lorentz block
```

is false by `(11)`.

The positive successor is exact:

1. every finite incidence is Hilbert--Schmidt by `(6)`;
2. the cofinal family is faithful by `(8)`;
3. translation covariance identifies its changing finite shadows with Gamma's rank-one boundary
   anomaly;
4. the only missing topology is a projective Mackey/relative-graph completion in which the
   Gamma--Meixner shape family is controlled without summing the coherent-jet norm `(11)`.

This agrees with the independently constructed rapid-Fock prime carrier: source-defined analytic
metrics can make critical all-prime incidence compact, but not Hilbert--Schmidt.  That carrier is a
possible relative completion, not the factorial Fock colimit disproved here.

For the RH route, the live statement is now a uniform **trace** estimate on the finite projective
family.  It must not be replaced by boundedness of the nonexistent infinite map.

## Parent-theory boundary

Derivative evaluation of Dirichlet series, Hilbert--Schmidt row maps, coherent-state norms, and
Dirichlet-series uniqueness are classical.  The result is classified as bridge infrastructure.
Its value is the exact separation between finite HT incidence and cofinal RH topology.


## 2026-08-19 — unconditional Lean formalization (stage 3)

`formal/GaloisForLFunctions/RHTower/PrimeLaplaceGammaJetIncidence.lean`, axiom-clean
(`propext, Classical.choice, Quot.sound`).

| Card item | Lean declaration |
|---|---|
| eq. (1), the Gamma–Meixner weight `w_θ(p) = cosh(2 log p)^{-θ/2}` | `meixnerPrimeWeight` |
| the two-sided comparison `p^{-θ} ≤ w_θ(p) ≤ 2^{θ/2} p^{-θ}` | `meixnerPrimeWeight_le`, `meixnerPrimeWeight_ge` |
| eq. (2), the weighted prime–Laplace transform | `primeLaplaceCoeff` and its `LSeries` |
| **eq. (3), absolute convergence for `Re z > (1-θ)/2`** | `lSeriesSummable_primeLaplaceCoeff`, `abscissaOfAbsConv_primeLaplaceCoeff_le` |
| eq. (4), the raw jet coordinates `F_a^{(j)}(x₀)` | `iteratedDeriv_primeLaplace_eq`, `primeLaplaceJet` |
| eq. (5), the factorial jet metric; eq. (6) column norms | `primeJetColumnFactorialNormSq` |
| **eq. (6), every finite clock is Hilbert–Schmidt** | `summable_primeJetColumnFactorialNormSq` |
| **eqs. (7)–(8), joint faithfulness of all finite clocks** | `eq_zero_of_forall_iteratedDeriv_eq_zero` |
| eqs. (9)–(11), the exact coherent-jet Fock column norm `w_θ(p) p^{-2x₀} e^{(log p)²}` | `primeFockColumnNormSq`, `tsum_primeJetColumn_eq_primeFockColumnNormSq` |
| **eq. (12), the Fock colimit no-go: the column norms are unbounded** | `not_bddAbove_primeFockColumnNormSq` |
| eq. (13), translation covariance `jet_{x₀+1} = E jet_{x₀}` | `hasSum_taylor_primeLaplaceJet` |

Faithfulness is proved through the analytic order at the base point: all raw derivatives vanishing
forces `analyticOrderAt = ⊤`, hence local vanishing, hence vanishing on the convex convergence
half plane, and Dirichlet-coefficient uniqueness then kills the prime vector.  The Hilbert–Schmidt
bound uses the corpus lemma `summable_abs_log_natCast_pow_mul_rpow_neg`; the Fock column norm is
the exponential series `∑_j (log p)^{2j}/j! = e^{(log p)²}`.

## Gates

- [x] construct the prime–Laplace-to-raw-jet incidence
- [x] prove every finite clock map is Hilbert–Schmidt
- [x] prove joint faithfulness of all finite clocks
- [x] compute the exact factorial Fock column norm
- [x] disprove boundedness of the naive cofinal map at every positive shape
- [x] replace it by a projective/relative-graph trace target
- [x] formalize the incidence, the Hilbert–Schmidt bound, faithfulness, the coherent-jet column
  norm and the colimit no-go unconditionally in Lean 4
