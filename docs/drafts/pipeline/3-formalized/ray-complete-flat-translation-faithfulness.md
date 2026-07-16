# Ray-complete flat carriers are translation-faithful

- **ID:** `ray-complete-flat-translation-faithfulness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED] [NOVELTY UNVERIFIED]`
- **Statement:** A right-half-plane Dirichlet carrier supported nontrivially on every positive
  multiple of infinitely many pairwise incommensurable frequency rays admits no nonzero finite
  constant-coefficient translation operator that sends it to `C(s)`. Its Poincare expansion is
  zero, so its formal-to-analytic translation-constraint defect is maximal. The logarithmic
  derivative of the Euler product is the canonical instance.

## 1. Analytic and formal constraint ideals

For `h in C`, write

```text
T_h f(s)=f(s+h).                                           (1)
```

Let

```text
A=C[(C,+)]                                                (2)
```

be the finite-support complex group algebra of additive translations. Thus every `P in A` has a
unique expression

```text
P=sum_(j=1)^r c_j T_(h_j),
c_j!=0, h_j pairwise distinct.                            (3)
```

The action is understood on a common sufficiently far right half-plane. If `f` has a complete
Poincare expansion `hat f`, define

```text
I_an(f) ={P in A : P f is a rational function},
I_for(f)={P in A : P hat f is the expansion of a rational function}.
                                                               (4)
```

Both are ideals of `A`: translations preserve `C(s)`. Compatibility of Poincare expansion with
finite translation gives

```text
I_an(f) subset I_for(f).                                  (5)
```

The quotient

```text
Q_flat(f)=I_for(f)/I_an(f)                                (6)
```

is the **flat translation-constraint defect**. It measures rational constraints visible to the
formal asymptotic shadow but not obeyed by the analytic function. This is a quotient of constraints,
not a remainder term chosen from an asymptotic summation.

## 2. Ray-complete carriers

Let `P` be an infinite index set and let `lambda_p>0` satisfy:

1. `lambda_p/lambda_q notin Q` for distinct `p,q`;
2. `inf_p lambda_p>0`;
3. the frequency set `{m lambda_p:p in P,m>=1}` is locally finite.

Consider an absolutely convergent generalized Dirichlet series on some right half-plane

```text
F(s)=sum_(p in P) sum_(m>=1) b_(p,m) exp(-m lambda_p s),
b_(p,m)!=0.                                               (7)
```

Call `(7)` **ray-complete**: every positive multiple of every primitive ray occurs, and distinct
rays are rationally incommensurable.

## 3. Translation-faithfulness theorem

`[PROVED]` Every ray-complete carrier `(7)` satisfies

```text
I_an(F)=0.                                                (8)
```

Equivalently, the representation

```text
A -> Hol(Re(s)>sigma_0)/C(s),
P |-> [P F]                                               (9)
```

is faithful.

### Proof

Take `P` as in `(3)` and suppose

```text
P F=R in C(s).                                            (10)
```

Absolute convergence and `inf lambda_p>0` imply exponential decay on the positive real axis:

```text
P F(x)=O(exp(-eta x))                                     (11)
```

for some `eta>0`. A nonzero rational function cannot decay exponentially along `x->+infinity`, so
`R=0`.

Uniqueness of absolutely convergent generalized Dirichlet series, using local finiteness of the
frequencies, now gives for every `p` and `m>=1`

```text
0=b_(p,m) sum_(j=1)^r c_j exp(-m lambda_p h_j).
                                                               (12)
```

Since every `b_(p,m)` is nonzero,

```text
sum_j c_j z_(p,j)^m=0,
z_(p,j)=exp(-lambda_p h_j),
m=1,2,... .                                               (13)
```

Choose one ray `p` for which the `z_(p,j)` are pairwise distinct. Such a ray exists. Indeed, for a
fixed pair `j!=k`, an alias

```text
exp(-lambda_p h_j)=exp(-lambda_p h_k)                     (14)
```

means

```text
lambda_p(h_j-h_k) in 2 pi i Z.                            (15)
```

The same pair cannot alias on two distinct rays `p,q`: dividing the two nonzero integer relations
would put `lambda_p/lambda_q` in `Q`. Thus each of the finitely many pairs excludes at most one ray,
while `P` is infinite.

For the chosen ray, equations `(13)` with `m=1,...,r` form the matrix

```text
(z_(p,j)^m)_(1<=m,j<=r),                                  (16)
```

a Vandermonde matrix times an invertible diagonal matrix. It is invertible, so every `c_j=0`.
Hence `P=0`, proving `(8)`.

## 4. Maximal flat defect

Every ray-complete `F` is exponentially small on the positive real axis, so its complete
inverse-power Poincare expansion is

```text
hat F=0.                                                  (17)
```

Therefore every finite translation operator annihilates its formal shadow modulo rational
functions:

```text
I_for(F)=A.                                               (18)
```

Combining `(8)` and `(18)` gives the exact positive classification

```text
Q_flat(F)=A.                                              (19)
```

> **Maximal flat-constraint law.** A ray-complete carrier is invisible to every inverse-power
> Poincare coefficient, yet the analytic function carries a faithful action of the entire finite
> translation algebra. Every formal rational constraint becomes a nonzero analytic defect class.

Thus asymptotic flatness is not absence of state. In this class it is maximal hidden
translation-constraint state.

## 5. Euler logarithmic-derivative tower

On `Re(s)>1`, put

```text
E(s)=-zeta'(s)/zeta(s)
    =sum_p sum_(m>=1) (log p) exp(-m(log p)s).             (20)
```

The primitive frequencies are `lambda_p=log p`. For distinct primes,

```text
log p/log q notin Q,                                      (21)
```

because a rational relation would give `p^a=q^b`. The frequencies `m log p=log(p^m)` are locally
finite, are bounded below by `log 2`, and every coefficient in `(20)` is nonzero. Hence `(20)` is
ray-complete.

The same is true after any fixed number `k>=0` of derivatives: the coefficient on the `p,m` ray is

```text
(log p)(-m log p)^k!=0.                                   (22)
```

Therefore

```text
I_an(E^(k))=0,
Q_flat(E^(k))=A,
k>=0.                                                     (23)
```

This is the **Euler flat-tower law**. It is stronger than saying that no one preferred shift works:
no nonzero finite linear combination of arbitrary complex translations can become rational.

## 6. Completion-injection law

`[PROVED]` Let `a` have a complete Poincare expansion and let `e` be flat with `I_an(e)=0`. Then
the natural map

```text
I_an(a) -> Q_flat(a+e),
P |-> P mod I_an(a+e)                                     (24)
```

is injective.

### Proof

If `P in I_an(a)`, then `P a` is rational. Since `hat e=0`, `P` belongs to `I_for(a+e)`. If its
class in `(24)` vanished, then `P(a+e)` would also be rational. Subtraction would make `P e`
rational, and `I_an(e)=0` would force `P=0`. This proves injectivity.

The law says positively what Euler completion does to an archimedean rational constraint: it turns
that constraint into a nonzero flat-defect probe.

## 7. Completed-zeta instance

Let

```text
Xi(s)=1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s),
Theta_Xi(s)=(Xi'(s)/Xi(s))'.                              (25)
```

Write

```text
Theta_Xi=a_infinity-E',                                   (26)
```

where

```text
a_infinity(s)=-1/s^2-1/(s-1)^2+1/4 psi'(s/2).             (27)
```

The trigamma recurrence gives

```text
(T_2-1)a_infinity in C(s).                                (28)
```

By `(23)`, `I_an(E')=0`. Applying the completion-injection law to `(26)` yields

```text
0!=(T_2-1) mod I_an(Theta_Xi) in Q_flat(Theta_Xi).         (29)
```

Equivalently,

```text
(T_2-1)hat Theta_Xi is rational,
(T_2-1)Theta_Xi is not rational.                          (30)
```

The finite archimedean constraint has not disappeared. It survives as a certified nonzero class
whose analytic content is exactly the flat Euler source.

The same argument applies to any finite positive-scale Gamma completion: every nonzero translation
operator that rationalizes its archimedean logarithmic-derivative tower injects into the flat defect
of the completed Euler--Gamma object.

## 8. Finite-stage ancestor filtration

For a finite prime cutoff set

```text
E_N(s)=sum_(p<=N) sum_(m>=1)(log p)p^(-ms),
J_N=I_an(E_N).                                             (31)
```

Each `J_N` is nonzero. Indeed

```text
P_N=product_(p<=N)(T_(2 pi i/log p)-1)                    (32)
```

annihilates `E_N`, because the factor indexed by `p` fixes every `p^m` term. Dirichlet uniqueness
also shows

```text
J_M subset J_N for M>=N.                                  (33)
```

For `lambda>0`, define the translation character

```text
chi_lambda(sum_j c_j T_(h_j))=sum_j c_j exp(-lambda h_j). (33a)
```

Coefficient uniqueness gives the exact finite-stage ideal

```text
J_N=intersection_(p<=N,m>=1) ker chi_(m log p).            (33b)
```

Each character kernel is maximal, so `J_N` is radical and

```text
B_N=A/J_N                                                 (33c)
```

is the reduced coordinate algebra of the prime-power translation characters through cutoff `N`.
For `M>=N`, inclusion `(33)` gives a surjection `B_M->B_N`.

The infinite theorem is exactly the cofinal separation law

```text
intersection_N J_N={0}.                                   (34)
```

Equivalently, the canonical map

```text
A -> inverse_limit_N B_N                                 (34a)
```

is injective.

Thus the Euler carrier is **cofinally cutoff-faithful**: every cutoff has explicit finite
translation constraints, but no nonzero constraint survives all prime cutoffs.

This is the positive finite-to-infinite carrier. A successful limiting construction must represent
the reduced character algebras `B_N`, their transition maps, and the injectivity in `(34a)`; merely
preserving each cutoff after collapsing their distinction does not carry the Euler source.

## 9. HT landscape law

The theorem separates two independent characteristics of HT functions.

```text
finite affine-Gamma HT:
  nonzero finite rational translation constraint;

Euler logarithmic-derivative HT:
  faithful finite-translation action and maximal flat defect. (35)
```

Hypertranscendence alone does not distinguish these species. The new characteristic is the
formal-to-analytic constraint quotient `Q_flat`: it records whether the information omitted by a
formal asymptotic shadow is inert or carries a faithful infinite-frequency source.

For the zeta landscape, the completed object is forced to contain both resources:

```text
archimedean finite constraint
  + Euler maximal flat defect
  -> completed nonzero constraint-defect carrier.          (36)
```

## 10. Positive requirements for RH architectures

The conclusion is not that an abstract equivalent criterion fails. It states the carrier that an
implementation must preserve.

1. **Hilbert--Polya and Connes.** The operator algebra, domain, resolvent, determinant, or quotient
   geometry must carry a representation of the finite translation algebra whose cutoff annihilators
   are `J_N` and whose cofinal kernel is zero.
2. **de Branges.** The Hermite--Biehler phase or canonical-system Hamiltonian must retain the
   ray-complete Euler translation response; the Stirling phase alone sees only `I_for`.
3. **Nyman--Beurling.** The dilation/translation representation on the approximation space must be
   faithful after the prime cutoffs are made cofinal. A fixed finite annihilator cannot survive the
   closure.
4. **Weil positivity.** The test-function and explicit-formula carrier must separate every nonzero
   finite translation operator through some prime-power ray.
5. **Li criteria.** The full coefficient hierarchy must retain the decreasing annihilator filtration
   `(J_N)`; any fixed finite recurrence must eventually be broken by a new prime ray.

These are positive obligations: construct the representation, identify its finite-stage kernels,
and prove their intersection is zero in the completed constraint.

## 11. Attacks and exact boundaries

1. **Ray completeness is load-bearing.** If only finitely many rays occur, `(32)` supplies a nonzero
   annihilator.
2. **Every multiple is stronger than necessary but clean.** The Vandermonde proof uses the first `r`
   multiples of one good ray. A support with sufficiently long blocks on infinitely many rays also
   works; sparse rays require a separate uniqueness set.
3. **Pairwise irrational ratios are load-bearing for the stated separator.** Rationally related rays
   can alias under the same translation and must first be combined into commensurability classes.
4. **The rational target is load-bearing.** The exponential-decay argument kills rational outputs;
   a larger target field containing flat Dirichlet series would have a nonzero constraint ideal.
5. **The theorem is not an HT criterion.** Translation faithfulness is an independent characteristic.
   Some HT functions have finite translation constraints, and a DA function need not satisfy any
   constant-coefficient translation equation.
6. **No route is rejected by name.** A route remains viable precisely by realizing the cofinally
   cutoff-faithful carrier `(31)`--`(34)`.

## 12. Parent and novelty audit

`[SEARCH]` Generalized Dirichlet-series uniqueness, rational asymptotics, and Vandermonde inversion
are classical. Difference independence of Gamma functions and Dirichlet-series classes is an active
literature, including Li--Tahir--Gao (2023) and Lu's zeta-specific 2024 theorem. Ostrowski's
structure theory and later functional-independence results are adjacent.

`[NOVELTY UNVERIFIED]` Preliminary exact searches did not locate the quotient `Q_flat`, the maximal
identity `(19)`, the ray-complete arbitrary-translation proof, or the completion injection `(24)`.
However, the proof is an elementary synthesis once the invariant is defined, and the full texts of
the two closest difference-independence papers were not accessible. The result must not be promoted
beyond `[NOVELTY UNVERIFIED]` without an exact theorem-by-theorem priority comparison.

Primary adjacent sources:

- X.-M. Li, H. Tahir, X.-Y. Gao, *On the Algebraic Difference Independence of the Euler Gamma
  Function and Dirichlet Series*, Constructive Approximation 58 (2023), 121--149.
- F. Lu, *On the algebraic difference independence of Gamma and zeta*, J. Math. Anal. Appl. 538
  (2024), article 128446.
- A. Ostrowski, *Uber Dirichletsche Reihen und algebraische Differentialgleichungen*, Math. Z. 8
  (1920), 241--298.
- J. Kaczorowski, A. Perelli, *Functional independence of the singularities of a class of Dirichlet
  series*, Amer. J. Math. 120 (1998), 289--303.

## 13. Lean status

`[FORMALIZED]` The algebraic core is fully machine-checked in
`formal/GaloisForLFunctions/RHTower/RayCompleteTranslationFaithful.lean` (axiom-clean:
`propext`, `Classical.choice`, `Quot.sound` only). The translation algebra is modelled as
`A = AddMonoidAlgebra ℂ ℂ`, and the analytic constraint ideal `I_an` is represented by the joint
kernel of the translation characters `χ_λ(∑_j c_j T_{h_j}) = ∑_j c_j e^{-λ h_j}` — the character
form to which `I_an` reduces by exponential decay of rationals and generalized-Dirichlet coefficient
uniqueness (the classical analytic bridge, cited but not re-proved).

Formalized declarations:

- `translationChar` / `translationChar_apply` — the characters `χ_λ` as algebra homs `A →ₐ[ℂ] ℂ`.
- `exists_injective_ray` — the aliasing lemma `(14)`–`(15)`: on an infinite set of positive rays
  with pairwise irrational ratios, some ray makes `h ↦ e^{-λ_p h}` injective on any finite support.
- `finset_moments_eq_zero` — the Vandermonde separation core, built on
  `vandermonde_moments_eq_zero_of_injective` via the diagonal factor `z_{p,j}`.
- `translationChar_moments_eq_zero` and `rayComplete_annIdeal_eq_bot` — the theorem `(8)`,
  `I_an(F) = 0`, in element and ideal form.
- `euler_translation_faithful`, `eulerLogDeriv_annIdeal_eq_bot`,
  `zeta_logDeriv_translation_faithful` — the Euler instance `(23)`, using `irrational_log_ratio` for
  the incommensurable rays and `zeta_logDeriv_frequencies_weld` to name the actual `-ζ'/ζ` carrier.
- `eulerFreqBelow` / `eulerJ` / `eulerJ_antitone` / `eulerJ_iInf_eq_bot` — the finite-stage ancestor
  filtration `(31)`–`(34)`: the decreasing chain `J_M ⊆ J_N` and the cofinal separation `⋂_N J_N = 0`.
- `completion_injection` and `completedZeta_nonzero_class` — the completion-injection law `(24)` and
  the completed-zeta nonzero-class instance `(29)`, over an abstract module of carriers with a
  rational subspace (the module algebra `P e = P(a+e) - P a`, exactly the paper proof).
- `annIdeal_single_ray_ne_bot` — the converse boundary (attack §11.1): a single ray has the nonzero
  annihilator `T_{2πi/λ} - 1`, so ray-completeness is load-bearing for `(8)`.

Not carried to Lean (classical analytic inputs, represented as the character-kernel interface rather
than reproved): generalized-Dirichlet coefficient uniqueness and exponential decay of nonzero
rationals; the formal Poincaré-shadow side `I_for` of `(17)`–`(19)`; and the specific trigamma
recurrence `(28)`, which enters `completedZeta_nonzero_class` as the hypothesis `hRat`.

## Gates

- [x] analytic and formal constraint ideals defined
- [x] ray-complete faithfulness theorem proved
- [x] maximal flat defect proved
- [x] Euler logarithmic-derivative tower instantiated
- [x] completion-injection law proved
- [x] completed-zeta defect instantiated
- [x] finite-stage ancestor filtration proved
- [x] positive route obligations stated
- [ ] exact priority audit against the full difference-independence literature
- [x] complete unconditional Lean formalization of the algebraic core (character/ideal frame):
      `RayCompleteTranslationFaithful.lean`, axiom-clean; analytic bridge (Dirichlet uniqueness,
      rational decay, `I_for`) represented as the character-kernel interface

## Formalization audit — 2026-07-15

`[FORMALIZED]` The former analytic and formal-shadow gaps are closed without assumptions.

- `GeneralizedDirichletSeriesInjectivity.lean` proves coefficient uniqueness for absolutely
  convergent generalized Dirichlet series with strictly increasing positive frequencies.
- `RationalExponentialDecay.lean` proves that a nonzero complex rational function cannot have
  exponential decay on the positive real ray.
- `RayCompleteTranslationAnalytic.lean` proves the literal analytic theorem and the exact
  rationalizing-set classification `I_an(F) = {0}`.
- `RayCompletePoincareFlatness.lean` proves zero complete inverse-power Poincare shadow for the
  carrier and all finite translations, hence the formal constraint ideal is the whole algebra.
- `EulerTranslationAnalyticFaithful.lean` instantiates every derivative order of the actual
  von-Mangoldt L-series and `-zeta'/zeta`, proving the full Euler flat-tower law.
- `EulerCutoffConstraintAlgebra.lean` proves the explicit nonzero cutoff annihilators, maximal
  character kernels, radical cutoff ideals, reduced quotient algebras, surjective transitions, and
  injective compatible cofinal quotient readout.
- `CompletedZetaTranslationDefect.lean` derives the explicit rational `T_2-1` archimedean response
  from the formalized trigamma recurrence and proves the completed nonzero flat-defect certificate:
  formally rational but not analytically rational.

Targeted leaf builds passed. `scripts/formal_tools.py lint` passed. The headline declarations use
only `propext`, `Classical.choice`, and `Quot.sound`. No full build was run.
