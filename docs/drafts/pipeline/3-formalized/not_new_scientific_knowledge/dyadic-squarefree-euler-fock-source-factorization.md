# The Euler source is the dyadic Fock completion of the squarefree source

- **ID:** `dyadic-squarefree-euler-fock-source-factorization`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper) / CANONICAL SOURCE CHANNEL
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED PARENT THEORY] [NOT AN RH PROOF]`
- **Parents:** unique prime factorization, the Euler product, Hilbert tensor products, and
  `../mobius-fixed-current-von-mangoldt-critical-transport-weld.md`
- **Statement:** The normalized Euler state factors canonically into its signed squarefree parity
  state at `sigma` and an independent Euler state at `2 sigma`.  The factorization is unitary,
  transports the logarithmic observable exactly, and sends the critical squarefree Fisher
  connection to the Euler Fisher connection with an explicit Hilbert--Schmidt defect tending to
  zero.  Iteration gives the source-defined dyadic meta-constraint and its affine joint cutoff.

## 1. Arithmetic unitary

Every positive integer has a unique decomposition

```text
n=d m^2,   d squarefree.                                  (1)
```

Indeed, if `v_p(n)=epsilon_p+2j_p` with `epsilon_p in {0,1}`, take

```text
d=product_p p^(epsilon_p),   m=product_p p^(j_p).         (2)
```

Let

```text
H_E  =ell^2(N_(>=1)),
H_sq =ell^2({d>=1 : d squarefree}).                       (3)
```

Under the standard identification
`ell^2(Squarefree x N_(>=1))=H_sq tensor H_E`, define

```text
(U f)(d,m)=mu(d) f(d m^2).                                (4)
```

The coordinate map in `(1)` is a bijection and `|mu(d)|=1` on the squarefree locus.  Therefore
`U` sends an orthonormal coordinate basis to an orthonormal coordinate basis and is unitary.
This is a source-defined map: neither Xi nor its divisor occurs in `(1)`--`(4)`.

## 2. Exact factorization of the pointed states

For real `sigma>1`, put

```text
Z_sq(sigma)=sum_(d squarefree)d^(-sigma)
           =zeta(sigma)/zeta(2sigma),

e_sigma(n)=n^(-sigma/2)/sqrt(zeta(sigma)),
s_sigma(d)=mu(d)d^(-sigma/2)/sqrt(Z_sq(sigma)).           (5)
```

Both are unit vectors in their respective Hilbert spaces.  Since

```text
Z_sq(sigma) zeta(2sigma)=zeta(sigma),                    (6)
```

equations `(1)` and `(5)` give, coordinate by coordinate,

```text
U e_sigma=s_sigma tensor e_(2sigma).                     (7)
```

Explicitly, both sides at `(d,m)` equal

```text
mu(d)d^(-sigma/2)m^(-sigma)/sqrt(zeta(sigma)).            (8)
```

Thus the signed squarefree state is not merely asymptotically coupled to an Euler state.  It is
the exact parity factor of the Euler state, and the lost prime-power data is the independent
strict-right residual `e_(2sigma)`.

## 3. Exact logarithmic transport

Let `L_E` and `L_sq` be multiplication by `log n` and `log d`, initially on the finitely supported
cores.  From `log(d m^2)=log d+2log m`,

```text
U L_E U^*
 =L_sq tensor I + 2 I tensor L_E.                        (9)
```

The states in `(5)` lie in the domains of the squares of these multiplication operators.  Write

```text
b_sigma=<e_sigma,L_E e_sigma>,
a_sigma=<s_sigma,L_sq s_sigma>.                          (10)
```

Taking the expectation of `(9)` in `(7)` yields

```text
b_sigma=a_sigma+2b_(2sigma).                             (11)
```

This is the pointed Hilbert form of the logarithmic-current identity.

## 4. Fisher-tangent transport with exact defect

Put `epsilon=sigma-1` and define the centered critical tangents

```text
chi_E   =-2epsilon(L_E-b_sigma)e_sigma,
chi_sq  =-2epsilon(L_sq-a_sigma)s_sigma,
r_sigma =-4epsilon(L_E-b_(2sigma))e_(2sigma).            (12)
```

Substituting `(7)`, `(9)`, and `(11)` into `(12)` gives the exact vector identity

```text
U chi_E
 =chi_sq tensor e_(2sigma) + s_sigma tensor r_sigma.     (13)
```

Centeredness gives

```text
<s_sigma,chi_sq>=0,
<e_(2sigma),r_sigma>=0.                                  (14)
```

Hence the two summands in `(13)` are orthogonal and

```text
||chi_E||^2
 =||chi_sq||^2+||r_sigma||^2,

||r_sigma||^2
 =16epsilon^2 Var_(e_(2sigma))(log n).                   (15)
```

For `1<sigma<=3/2`, the variance in `(15)` is bounded by a constant times
`sum_n (log n)^2 n^(-2)`, which converges.  Therefore

```text
||r_sigma|| ->0   as sigma->1+.                          (16)
```

Define the canonical isometry

```text
V_sigma : H_sq -> H_E,
V_sigma x=U^*(x tensor e_(2sigma)).                       (17)
```

Then `(7)` and `(13)` become

```text
V_sigma s_sigma=e_sigma,
||chi_E-V_sigma chi_sq||=||r_sigma||->0.                 (18)
```

Unlike the monotone optimal-transport coupling, `(17)` is linear, pointed, and source-defined.

## 5. Exact transport of the polarized Fisher connection

For a unit vector `v` and a centered tangent `h perpendicular v`, define

```text
X(v,h)=2^(-1/2)(|h><v|+|v><h|),
P_v=|v><v|.                                              (19)
```

Let

```text
X_E=X(e_sigma,chi_E),
X_sq=X(s_sigma,chi_sq),
X_r=X(e_(2sigma),r_sigma).                               (20)
```

Expanding `(19)` using `(7)` and `(13)` gives

```text
U X_E U^*
 =X_sq tensor P_(e_(2sigma)) + P_(s_sigma) tensor X_r.   (21)
```

Equivalently,

```text
X_E-V_sigma X_sq V_sigma^*
 =U^*(P_(s_sigma) tensor X_r)U.                          (22)
```

For centered rank-two connections, `||X(v,h)||_HS^2=||h||^2`.  Consequently `(15)` and `(22)`
give the exact defect law

```text
||X_E-V_sigma X_sq V_sigma^*||_HS^2
 =16epsilon^2 Var_(e_(2sigma))(log n) ->0.               (23)
```

The two terms on the right of `(21)` are Hilbert--Schmidt orthogonal.  Thus the Euler Fisher
energy is the orthogonal sum of the squarefree parity energy and a strict-right residual energy;
there is no fitted contraction and no hidden scalar codiagonal.

## 6. Iterated meta-constraint

Iterating `(1)` gives, uniquely,

```text
n=d_0 d_1^2 ... d_(R-1)^(2^(R-1)) m^(2^R),              (24)
```

with every `d_r` squarefree.  Iterating `U` therefore gives a canonical unitary

```text
U_R e_sigma
 =s_sigma tensor s_(2sigma) tensor ...
    tensor s_(2^(R-1)sigma) tensor e_(2^R sigma),        (25)
```

up to the explicit product of the Mobius parity phases already included in the `s` factors, and

```text
U_R L_E U_R^*
 =sum_(r<R) 2^r L_sq,r + 2^R L_E,res.                   (26)
```

Equations `(25)`--`(26)` are the correct higher compatibility object behind the proposed family
of source matroids: a pointed dyadic tensor system with an additive logarithmic meta-constraint.
The squarefree layers are genuinely separate source coordinates, while `(26)` reconstructs the
Euler logarithmic morphism.

The scalar analytic shadow is the exact finite telescope

```text
zeta(s)
 =product_(r<R) Z_sq(2^r s) * zeta(2^R s),              (27)
```

and, with

```text
A(s)=-zeta'(s)/zeta(s),
J_sq(s)=-Z_sq'(s)/Z_sq(s),                              (28)
```

its exact morphism reconstruction is

```text
A(s)
 =sum_(r<R)2^r J_sq(2^r s)+2^R A(2^R s).               (29)
```

For `Re s>1`, the residuals in `(27)` and `(29)` tend respectively to `1` and `0`, giving the
infinite dyadic reconstruction.  The one-step residual `2A(2s)` is holomorphic near `s=1`, so the
base squarefree layer contains the whole critical pole while the residual is a strict-right
analytic channel.

## 7. Weyl-orbit and generator transport

Before imposing the cutoff, the same unitary reconstructs the bounded Weyl orbit which retains
the logarithmic current.  Let

```text
chi_c(z)=exp(-i c z).                                    (30)
```

At one prime, `k=e+2j` gives both

```text
k log p=e log p+2j log p,
chi_(k log p)(z)=chi_(e log p)(z)chi_(2j log p)(z).      (31)
```

Multiplying `(31)` by the signed-amplitude factorization proves the exact pointed phase law

```text
(-1)^e a_q(e+2j) chi_((e+2j)log p)
 =(s_q(e)chi_(e log p))(r_q(j)chi_(2j log p)).           (32)
```

The Wigner--Smith value of `chi_c` is `c`, so `(31)` also gives the additive generator law

```text
WS_(k log p)=WS_(e log p)+WS_(2j log p).                 (33)
```

Thus the dyadic source channel transports the bounded phase orbit and its unbounded tangent, not
only the static probability law.  The character in `(30)`--`(33)` is exactly the character proved
to arise from logarithmic-position conjugation of the physical Sonin dilation in
`SoninSemilocalWeylGenerator.lean`.  No fitted bounded response is introduced.

## 8. Cutoff hostile test and positive successor

Let `Q_T` be the sharp Euler multiplication cutoff `log n<T`.  Equation `(1)` gives

```text
U Q_T U^*
 =multiplication by 1_(log d+2log m<T).                  (34)
```

This is not the tensor product of independent cutoffs in `d` and `m`.  Therefore a theorem which
claims that `V_sigma` exactly intertwines the old single-layer squarefree cutoff with the Euler
cutoff is false.

The positive statement is exact: the source-selected cutoff is the affine joint cutoff `(34)`.
After `R` iterations it is

```text
sum_(r<R)2^r log d_r + 2^R log m < T.                   (35)
```

Thus the cutoff defect isolated in the contact-to-Xi route is not arbitrary error.  It is the
boundary incidence of the explicit affine constraint `(35)`.  Any Gamma/Sonin completion must
transport this joint projection; separately pinching the squarefree layers destroys the exact
Euler incidence.

## RH contribution and remaining seam

The theorem supplies the previously absent linear squarefree-to-Euler source channel and proves
its critical Fisher-connection nonexpansiveness in the stronger asymptotic-isometry form `(23)`.
It also replaces an unspecified cutoff defect by the exact affine boundary `(30)`--`(31)`.

It does **not** prove RH.  The remaining proof-bearing task is to apply the prime--Gamma
completion and the physical Sonin projection to this affine dyadic source system and prove that
the completed joint commutator converges on a cutoff-stable graph core to `[P_u,D_Xi]` without
increasing the Hilbert--Schmidt boundary energy.  Nothing in `(1)`--`(35)` assumes that target
incidence.

## Classification and Lean decision

The squarefree-times-square identity and the dyadic Euler telescope are classical consequences
of unique factorization.  The result is therefore classified as rediscovered parent theory, not
new scientific knowledge.  Its value is structural: it upgrades an abstract critical coupling
to the exact pointed linear channel required by the live RH card.

A faithful first Lean module should prove the arithmetic bijection and the one-step coefficient,
logarithmic, centered-tangent, and rank-two connection identities.  The analytic graph-core and
Gamma/Sonin limit must not be represented by hypotheses or wrappers.

## Gates

- [x] arithmetic parity--square bijection proved
- [x] exact pointed-state factorization proved
- [x] logarithmic observable and mean reconstruction proved
- [x] Fisher tangent split and vanishing residual proved
- [x] polarized connection transport and exact HS defect proved
- [x] iterated dyadic meta-constraint and analytic telescope proved
- [x] bounded Weyl orbit and Wigner--Smith generator compatibility proved
- [x] false independent-cutoff intertwining rejected
- [x] affine joint cutoff identified
- [x] formalize the one-prime probability/amplitude/mean/variance factor in Lean
- [x] formalize the global squarefree-times-square unitary and rank-two connection identity (2026-08-19)
- [ ] transport the affine joint cutoff through prime--Gamma completion
- [ ] prove cutoff-stable Sonin graph convergence and nonexpansiveness
- [ ] RH

## Lean status update (2026-08-19) — the card's theorem is fully formalized

Seven new unconditional modules complete the Lean chain `(1)`–`(35)`.  All `#print axioms` give
only `propext, Classical.choice, Quot.sound`.

`formal/GaloisForLFunctions/RHTower/EulerSquarefreeDyadicStateFactorization.lean`
- `eulerMass`, `squarefreeMass`, `rpow_dyadic_split`, `squarefreeMass_mul_eulerMass_two_mul` — `(6)`;
- `eulerPointedState`, `squarefreePointedState`, both unit vectors — `(5)`;
- `dyadicSquarefreeSignedUnitary` — the arithmetic unitary `(4)`, reindexing composed with the
  Möbius parity phase, as a `LinearIsometryEquiv`;
- `dyadicSquarefreeSignedUnitary_eulerPointedState` — `(7)`/`(8)` coordinatewise.

`.../EulerSquarefreeDyadicLogTransport.lean`
- `lpTensor`, `dyadicSquarefreeSignedUnitary_eq_tensor` — `(7)` as a vector identity;
- `dyadicSignedTransport_eulerLogMul` — `(9)`, for *arbitrary* coordinate functions (no core-domain
  hypothesis);
- `eulerLogMean`, `squarefreeLogMean`, their expectation forms, and `eulerLogMean_split` — `(10)`,
  `(11)`.

`.../EulerSquarefreeDyadicLogMoments.lean`
- convergence of every logarithmic moment on `σ > 1`;
- `eulerLogPowMass_split_zero/one/two` — the exact zeroth, first and second moment splits;
- `eulerLogVariance_split` — exact variance additivity `Var_σ(log n) = Var_σ(log d) + 4 Var_{2σ}(log m)`.

`.../EulerSquarefreeDyadicFisherTangent.lean`
- `eulerCenteredTangent`, `squarefreeCenteredTangent` — `(12)`;
- `normSq_eulerCenteredTangent`, `normSq_squarefreeCenteredTangent` — `‖χ‖² = c² Var`;
- `inner_eulerPointedState_eulerCenteredTangent`,
  `inner_squarefreePointedState_squarefreeCenteredTangent` — `(14)`;
- `dyadicSignedUnitary_eulerCenteredTangent` — `(13)`, coordinate and vector form.

`.../EulerSquarefreeDyadicFisherDefect.lean`
- `norm_lpTensor`, `lpTensorRight`, `dyadicSquarefreeEmbed` — the canonical isometry `V_σ` `(17)`;
- `dyadicSquarefreeEmbed_squarefreePointedState`, `norm_eulerCenteredTangent_sub_embed` — `(18)`;
- `normSq_eulerCenteredTangent_split` — `(15)`;
- `unitaryPush_fisherConnection_split` — `(21)`, with `X_sq ⊗ P` and `P_s ⊗ X_r` written as pointed
  connections of elementary tensors;
- `hsNormSq_fisherConnection_defect` — `(22)`/`(23)`, the exact Hilbert–Schmidt defect law;
- `criticalResidualEnergy`, `tendsto_criticalResidualEnergy` — `(16)`, the defect vanishes as
  `σ → 1⁺`.

`.../EulerSquarefreeDyadicTower.lean`
- `DyadTower`, `dyadicTowerEquiv` — `(24)`;
- `towerLog_dyadicTowerEquiv` — `(26)`;
- `dyadicTowerUnitary`, `dyadicTowerUnitary_eulerPointedState` — `(25)`;
- `eulerMass_tower_telescope` — the real form of `(27)`;
- `eulerLogCutoff_iff_towerCutoff` — `(35)`.

`.../EulerSquarefreeDyadicAnalyticTelescope.lean`
- `squarefreeZeta` (identified with `L(μ·μ, s)`), `riemannZeta_dyadic_telescope` — `(27)`;
- `eulerLogMorphism`, `squarefreeLogMorphism`, `eulerLogMorphism_step`,
  `eulerLogMorphism_dyadic_reconstruction` — `(28)`, `(29)`.

Already in the tree and unchanged: the one-prime probability/amplitude/mean/variance/Weyl layer
(`EulerSquarefreeDyadicFockLocal.lean`, §7 `(30)`–`(33)`), the global index equivalence
(`EulerSquarefreeDyadicGlobalCarrier.lean`), and the affine cutoff transport
(`EulerSquarefreeDyadicAffineProjection.lean`, §8 `(34)`).

The three unchecked gates below `(prime–Gamma completion, Sonin graph convergence, RH)` are the
explicitly-declared *successor* programme, not theorems of this card; the card's own statement
`(1)`–`(35)` is now unconditionally formalized.
