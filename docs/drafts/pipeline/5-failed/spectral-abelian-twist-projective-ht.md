# Failed route: arbitrary spectral abelian twists do not produce mixing projective HT

- **ID:** `spectral-abelian-twist-projective-ht`
- **Stage:** 5-failed
- **Type:** ROUTE KILL / YANG--BAXTER TWIST AUDIT
- **Scientific status:** `[PUBLISHED PARENT AUDITED] [GENERIC ICE-BLOCK NO-GO PROVED]`
  `[NOVELTY UNVERIFIED]`
- **Scope:** connected difference-form matrix scattering; no RH and no distinguished HT source
- **Parent:**
  `../2-fully-proven/needs-audit/projective-wigner-smith-nonabelian-ht-separation.md`
- **Failed conjecture:** Insert an arbitrary HT function into a noncentral abelian/Reshetikhin
  twist of a DA matrix `R`-matrix and preserve difference-form Yang--Baxter, positivity, and
  crossing.

## The abelian twist trichotomy

For the connected ice-block ansätze audited here, a functional abelian dressing falls into one of
three parent mechanisms:

```text
central CDD factor,
spectral one-particle coboundary,
constant projective Drinfeld cocycle.                       (1)
```

The first can carry physical HT but is scalar or commuting-channel data.  The second is gauge and
strict difference form forces it to be DA.  The third can change matrix phases but has no
rapidity-dependent HT coefficient.  None gives intrinsically mixing projective HT.

## Genuine Drinfeld--Reshetikhin twists are constant cocycles

A genuine twist is an invertible counital two-cocycle

```text
(F tensor 1)(Delta tensor id)F
 =(1 tensor F)(id tensor Delta)F,

R^F=F_21 R F^(-1).                                         (2)
```

Its coefficients belong to the underlying Hopf algebra and are not arbitrary functions of the
spectral difference.  Spectral dependence after evaluation comes from the representation of
algebra generators.  A constant toral twist may be noncentral and non-coboundary in rank at least
two, but it contributes only constant projective phases.  It cannot itself carry differential
transcendence.

## Arbitrary two-parameter functions are spectral gauges

Basu-Mallick--Ramadevi--Jagannathan allow arbitrary nonvanishing functions in particle-conserving
colored `R`-matrices.  Those functions attach separately to the two spectral/color parameters and
preserve the two-parameter colored Yang--Baxter equation.  At representation level this includes
the separable gauge

```text
R_tilde(lambda,mu)
 =(G(lambda) tensor G(mu)) R(lambda-mu)
  (G(lambda) tensor G(mu))^(-1).                            (3)
```

For diagonal `G=diag(exp(h_i))`, requiring `(3)` to depend only on
`u=lambda-mu` gives, on every connected channel,

```text
h_i(lambda)-h_j(lambda)-h_i(mu)+h_j(mu)=H_ij(lambda-mu).    (4)
```

Differentiating `(4)` shows that `h_i-h_j` is affine and

```text
H_ij(u)=kappa_ij u.                                         (5)
```

Thus the surviving factors are `exp(kappa_ij u)`: DA and pure one-particle gauge.  Abandoning
difference form restores arbitrary colored functions, but leaves the relativistic target.

## Direct rapidity-dependent toral twist fails on a connected six-vertex block

Consider a generic connected symmetric six-vertex matrix and a diagonal two-body twist whose
only projective effect is

```text
b_+(u)=q(u)b(u),
b_-(u)=q(u)^(-1)b(u),                                       (6)
```

with the exchange weight unchanged.  Put `w=u+v`.  One Yang--Baxter component and its
spin-reversed component have the form

```text
q(u)A+q(v)B=q(w)(A+B),
A/q(u)+B/q(v)=(A+B)/q(w),                                  (7)
```

where `A` and `B` are nonzero on a generic open set.  Multiplying the equations and eliminating
the common right side gives

```text
AB(q(u)/q(v)+q(v)/q(u)-2)=0,
(q(u)-q(v))^2=0.                                            (8)
```

Analyticity therefore makes `q` constant.  The related asymmetric exchange-weight deformation
obtained from a one-particle spectral gauge instead satisfies

```text
q(u+v)=q(u)q(v),                                            (9)
```

so analytic `q` is `exp(kappa u)`, again DA and gauge.

The exceptions are exactly the routes already separated elsewhere:

1. the twist is central or invisible on the matrix block;
2. the matrix is diagonal/simultaneously commuting, so arbitrary relative channel phases survive;
3. difference form is abandoned for a colored two-parameter family.

## Physical gates do not reopen the route

The regular quantum anchor is preserved by a genuine constant twist because

```text
F_21 P=P F_12.                                               (10)
```

Positive unitarity restricts constant twist parameters to phases.  Hermitian analyticity imposes
the corresponding Schwarz relation.  Crossing is not automatic and requires compatibility with
the antipode/charge-conjugation structure.  Physical-strip analyticity and boundedness are
strictly stronger than real-axis unitarity.  These conditions remove twists; they do not create a
new rapidity function after `(8)` or `(9)` has collapsed it.

Constant twists may also move to boundary data.  Ahn--Bajnok--Bombardelli--Nepomechie derive
twisted Bethe equations either from a twisted `S`-matrix or from the untwisted matrix with an
operatorial boundary twist.  This supplies no HT bulk-locality mechanism.

## Infinite-charge loophole, correctly bounded

Smirnov--Zamolodchikov separate the finite-dimensional principal matrix/Yang--Baxter deformations
from the infinite scalar CDD directions generated by local higher-spin charges.  Those scalar
directions can carry HT after all-orders completion, but they do not create mixing inside an
irreducible flavor block.

Doyon--Durnin--Yoshimura enlarge the charge space to complete extensive/quasilocal charges and can
generate arbitrary diagonal and some proposed non-diagonal real-axis phases.  Their paper
explicitly warns that generic quasilocal phases may lose the analyticity and other strong
requirements of relativistic QFT; the non-diagonal extension is only sketched and has an
additional unitarity condition.  This is a live different route, not a rescue of the direct toral
ansatz `(6)`.

## Failure insight

The Yang--Baxter equation couples spin-reversed channels strongly enough to detect a purported
noncentral functional twist.  Arbitrary functions survive only when the channel algebra has
already decomposed or when they are one-particle gauges.  The next projective-HT construction
must therefore leave at least one of these assumptions:

```text
direct toral two-body twist,
connected finite ice block,
strict rapidity difference,
finite-dimensional principal deformation.                 (11)
```

This is a route selector, not a general classification theorem for every matrix dimension and
every dynamical or quasi-Hopf twist.

## Anti-theatre and novelty gate

- Constant Reshetikhin twists, colored arbitrary-function gauges, scalar CDD completions, and
  complete-charge deformations are established parent theory.
- The calculation `(7)`--`(8)` is a generic connected-six-vertex obstruction, not a new
  classification of all Yang--Baxter twists.
- Focused searches found no published formulation of the exact trichotomy `(1)` in differential-
  algebraic language.  That negative evidence does not clear the novelty gate.
- No Lean wrapper is justified: the substantive hypotheses are the analytic/Yang--Baxter block
  classification and physical gauge semantics, not the two displayed scalar eliminations.

## Primary literature

- N. Reshetikhin, *Multiparameter quantum groups and twisted quasitriangular Hopf algebras*,
  Letters in Mathematical Physics **20** (1990), 331--335,
  <https://doi.org/10.1007/BF00626530>.
- B. Basu-Mallick, P. Ramadevi, and R. Jagannathan, *Multiparametric and coloured extensions of
  the quantum group `GL_q(N)` and the Yang--Baxter equation*,
  <https://arxiv.org/abs/q-alg/9511028>.
- F. A. Smirnov and A. B. Zamolodchikov, *On space of integrable quantum field theories*,
  <https://arxiv.org/abs/1608.05499>.
- B. Doyon, J. Durnin, and T. Yoshimura, *The Space of Integrable Systems from Generalised
  T bar T-Deformations*, <https://arxiv.org/abs/2105.03326>.
- C. Ahn, Z. Bajnok, D. Bombardelli, and R. I. Nepomechie, *Twisted Bethe equations from a twisted
  S-matrix*, <https://arxiv.org/abs/1010.3229>.

## Gates

- [x] genuine Hopf twist separated from spectral-function insertion
- [x] colored spectral gauge separated from strict difference form
- [x] affine/exponential collapse of difference-form one-particle gauges proved
- [x] connected six-vertex direct toral twist reduced to a constant
- [x] central, commuting, colored, and complete-charge loopholes classified
- [x] positive-unitary/crossing boundary audited
- [x] route retired without claiming a universal no-go
- [ ] classification-level novelty audit by an integrable-systems specialist
