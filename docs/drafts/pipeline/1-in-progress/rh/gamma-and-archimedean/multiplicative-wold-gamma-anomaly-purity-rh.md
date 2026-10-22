# Multiplicative Wold--Gamma anomaly and source-cohomological purity

- **ID:** `multiplicative-wold-gamma-anomaly-purity-rh`
- **Stage:** 1 — in progress
- **Type:** POST-CONJECTURE MECHANISM HYPOTHESIS / SOURCE-SPECIFIC RH PROGRAM
- **Scientific status:** `[PROOF HYPOTHESIS] [EXACT CORE BRIDGES PAPER-PROVED]`
  `[GENERIC WOLD-EXACTNESS RETIRED] [EXTERNAL NOVELTY PROVISIONAL] [RH CHAIN INCOMPLETE]`
- **RH used:** no
- **Computation used:** no
- **Parents:**
  `../2-fully-proven/new_scientific_knowledge/prime-occupation-polarized-gamma-phase-survival.md`,
  `../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/bv-prime-window-polar-coefficient-decimation-law.md`,
  `../2-fully-proven/not_new_scientific_knowledge/burnol-copoisson-berezin-diagonal-reflection-law.md`,
  `../../../3-formalized/hypertranscendental-minimal-polarized-critical-completion-architecture.md`,
  `../../../3-formalized/source-producer-integral-realization-minimality.md`.
- **Frozen primary conjecture:**
  `source-curved-prime-torus-conormal-temperedness.md`.

## Mechanism in one sentence

The hypertranscendental Gamma phase is the regularized determinant of the Wold range defect of
multiplicative arithmetic dilation, while the BV zeta-pole residue is its missing first-trace
conormal coordinate; the RH-bearing object is the strict failure of the canonical Wold contraction
to survive the completed co-Poisson source differential, not exactness of the Wold defect itself.

This is not another positivity criterion.  It is one possible attack on the independently frozen
prime-Schwartz Xi conormal temperedness conjecture.  Failure of this mechanism does not change the
conjecture.

## 1. Arithmetic Wold system

Let `H=ell2(N_{>0})`, with standard basis `e_n`, and put

```text
Q e_n = n^(-1)e_n,
S_q e_n = e_(qn),                         q>=2,
E_q = I-S_q S_q^*.
```

Then:

1. `Q` is positive Hilbert--Schmidt and not trace class;
2. `S_q` is an isometry;
3. `E_q` is the projection onto coordinates `q` does not divide `n`;
4. `E_q` commutes with `Q`;
5. the arithmetic covariance is

   ```text
   S_q^* Q S_q = q^(-1) Q.                              (1)
   ```

The covariance is rigid.  If a positive diagonal operator `A e_n=a_n e_n` satisfies
`S_q^* A S_q=q^(-1)A` for every `q>=2` and `a_1=1`, then taking the matrix coefficient at `e_1`
with `q=n` gives `a_n=1/n`.  Thus the reciprocal occupation clock is forced by the multiplicative
semigroup and one normalization; it is not a fitted Gamma spectrum.

## 2. Exact Wold--Gamma determinant law

For a Hilbert--Schmidt operator `T`, write `det_2(I+T)` for the second regularized Fredholm
determinant.  Define the tangent-normalized polarized phase

```text
Phi(t)=det_2(I-tQ)/det_2(I+tQ).                          (2)
```

Euler's reciprocal-Gamma product gives the meromorphic identity

```text
Phi(t)=exp(2 gamma t) Gamma(1+t)/Gamma(1-t).             (3)
```

The orthogonal decomposition

```text
H=E_q H directSum S_q H
```

reduces `Q`, and `(1)` identifies its second summand with `Q/q`.  Multiplicativity of `det_2`
under orthogonal direct sums therefore proves

```text
Phi_q^def(t)
 :=det_2(I-t E_q Q)/det_2(I+t E_q Q)
 =Phi(t)/Phi(t/q).                                      (4)
```

Equation `(4)` is the **multiplicative Wold--Gamma anomaly law**.  The Gamma phase is the
regularized oriented determinant of the full occupation clock, and its scale cocycle is exactly
the determinant of the arithmetic Wold defect.

For `|t|<1`, logarithmic expansion gives

```text
log Phi_q^def(t)
 =-2 sum_(k>=1)
    (1-q^(-(2k+1))) zeta(2k+1) t^(2k+1)/(2k+1).         (5)
```

Thus the defect retains precisely the odd zeta tower.  The even/intensity tower is absent because
the determinant is polarized before completion.  This is the same HT channel isolated by the
prime-occupation theorem, now forced by an arithmetic dilation defect rather than recovered from
an unrelated Gamma product.

## 3. Missing first trace and the BV conormal coordinate

The regularization in `(2)` removes the nonsummable first trace.  On the Wold defect its finite
cutoff is exactly

```text
Tr_(n<=N)(E_q Q)
 =H_N-q^(-1) H_(floor(N/q)).                            (6)
```

Hence

```text
Tr_(n<=N)(E_q Q)
 -(1-q^(-1)) log N
 ->(1-q^(-1)) gamma+q^(-1) log q.                      (7)
```

The coefficient of the singular trace is the Wold density `1-q^(-1)`.

Independently, take the canonical BV prime-window polar coefficient `p_-` and its square-index
decimation `D_q`, with inflation `S_q` and coordinate projection `P_q=S_qD_q`.  The formal and
paper-proved source law is

```text
p_+=D_q p_-,
c_-=(I-P_q)p_-,
Res_rho(c_-)=(1-q^(-1)) Res_rho(p_-).                   (8)
```

For the corpus notation `q=r^2`, `(8)` is exactly the existing factor `1-r^(-2)`.

Equations `(7)` and `(8)` prove the new source identification:

> the off-multiple BV Laurent coordinate is weighted by exactly the singular first-trace density
> of the same multiplicative Wold defect whose regular determinant is the HT Gamma phase.

The regular Gamma phase and the meromorphic zeta conormal residue are therefore not two channels
that must be welded by an arbitrary positive covariance.  They are the regular and singular
layers of one source defect.

## 4. General HT insight: anomaly-cancelled source cohomology

The corpus minimality theorems force six information channels for a conservative HT theory.
The Wold--Gamma law shows how they can become one mathematical object.

There is a necessary sidedness correction. In the source metric forced by `(1)`, centered
multiplication is already an isometry:

```text
U_q^dagger U_q=I.
```

Its nonunitarity is the opposite Wold defect

```text
E_q=I-U_q U_q^dagger.                                    (8a)
```

The adjoint of an isometry can have every open-disk eigenvalue, so exactness of
`U_q^dagger U_q-I` would say nothing: that operator is already zero on the coefficient core.
The RH-bearing anomaly must cancel `(8a)`.

For a constrained HT source `F`, form a polarized source Hilbert complex

```text
(C_F^bullet,d_F,Q_F)
```

with:

1. integral source lattice and semigroup action in the coefficient term;
2. the completed source multiplier in the constraint differential;
3. Wold defect spaces as boundary terms;
4. the regularized polarized determinant line as the Gamma/HT term;
5. the missing first trace as a conormal boundary coordinate;
6. critical product bornology as the domain on which all terms close.

There is a second necessary correction.  The coefficient Wold complex is

```text
0 -> H_Q --U_q--> H_Q --E_q--> E_qH_Q -> 0.             (8b)
```

It is canonically split exact.  Its contraction is `h_q=(U_q^dagger,i_q)`, where
`i_q:E_qH_Q -> H_Q` is inclusion, because

```text
U_q^dagger U_q=I,
U_q U_q^dagger+E_q=I,
E_q i_q=I.                                               (8c)
```

Therefore neither contractibility of the coefficient Wold complex nor existential Hodge
exactness of `E_q` is an RH advance.

Let `mathcalD_(F,q)=partial_q+delta_F` be a source-fixed square-zero total differential on the
relative Wold complex and define

```text
I+mathcalA_(F,q)
 =mathcalD_(F,q) h_q+h_q mathcalD_(F,q),
mathcalA_(F,q)=delta_F h_q+h_q delta_F.                  (8d)
```

The left side commutes with `mathcalD_(F,q)`.  Wherever `I+mathcalA_(F,q)` has a continuous
inverse, `h_q(I+mathcalA_(F,q))^(-1)` contracts the total complex.  Nonzero completed source
cohomology can therefore occur only at a noninvertibility, domain, or closability defect of this
fixed homological-perturbation inverse.

The earlier proposed identity

```text
I-U_q U_q^dagger=d_F^* K_q+K_q^* d_F.                   (9)
```

is still a sufficient purity endpoint on a fixed independently constructed source complex, but it
is not the mechanism and supplies no evidence by itself.  It must be derived from the mixed
anomaly or replaced by the stronger support theorem below; it cannot be the conjecture merely
because it yields RH.

### Abstract purity consequence

Assume `(9)`, and assume the harmonic projection `P_F` is source-defined and commutes with `U_q`.
For a harmonic vector `h`,

```text
d_F h=0,   d_F^* h=0.
```

Taking its matrix coefficient in `(9)` gives

```text
<h,(I-U_q U_q^dagger)h>=0.                              (10)
```

The left side is nonnegative. Hence the range defect kills `h`; `U_q U_q^dagger h=h`.
Together with the chain-level isometry `U_q^dagger U_q=I`, source dilation is unitary on harmonic
cohomology. No global positive divisor measure, real-rooted approximation, self-adjoint zero
operator, or Weil-sign premise occurs.

This remains a valid abstract **polarized anomaly-cancellation purity lemma**.  The new conjecture
does not assume `(9)`: it predicts which strict failure class the independently fixed source
completion creates.

## 5. Riemann specialization

Burnol's co-Poisson quotient supplies source-defined annihilator evaluation vectors.  BV
continuation supplies the exact dilation character.  At a nontrivial zero `rho`, for an uncensored
fixed dyadic window,

```text
U_q^dagger k_rho=conj(q^(rho-1/2)) k_rho,   k_rho!=0.    (11)
```

The existing convention using `r` instead of `q=r^2` writes the same character as
`r^(2rho-1)`.

If the completed Wold--Gamma--co-Poisson totalization has strict failure locus equal to the Xi
principal conormal divisor and supported on unitary prime characters, then `k_rho!=0` lies in that
failure locus and

```text
|q^(rho-1/2)|=1,
Re(rho)=1/2.                                             (12)
```

Thus every nontrivial zero is critical and RH follows. Functional-equation reflection remains a
source symmetry of the construction but is not needed to repair a one-sided contraction estimate.

The proof mechanism is therefore:

```text
finite arithmetic decimation coisometry
  -> Wold defect
  -> regular layer = HT Gamma determinant cocycle
  -> singular layer = BV Laurent conormal coordinate
  -> canonical Wold contraction
  -> mixed contraction/source-differential anomaly
  -> strict failure locus = Xi conormal divisor
  -> failure support is unitary
  -> |q^(rho-1/2)|=1
  -> RH.                                                  (13)
```

## 6. Exact new open core

`WOLD-GAMMA-COPOISSON-PERTURBATION-SUPPORT`:

Construct the total source differential `mathcalD_(Xi,q)` before annihilator specialization,
transport the canonical contraction `(8c)`, and construct the closed cofinal mixed class
`mathcalA_Xi` with the following fixed blocks:

1. coefficient block: exact `D_q,S_q,E_q` Wold system;
2. regular boundary block: `Phi_q^def` from `(4)`;
3. conormal block: pole-cancelled BV/co-Poisson normal class, with `(8)`;
4. archimedean block: the same tangent-normalized Gamma phase, not its DA intensity;
5. source constraint block: completed co-Poisson multiplier and its adjoint;
6. harmonic effectivity: every uncensored annihilator conormal jet survives nontrivially.

The post-conjecture mechanism hypothesis is:

```text
regular relative determinant of mathcalA_Xi
  = Phi(t)/Phi(t/q);
singular trace of mathcalA_Xi
  = (1-q^(-1)) times the BV principal conormal;
strict failure support of I+mathcalA_Xi
  = the Xi principal conormal divisor with multiplicity;
every strict failure character is unitary.               (14)
```

The first construction test is the one-prime typed identity `(8d)` on a compact source core,
followed by proof that its graph and relative character survive cofinal completion.  These clauses
are a proposed proof mechanism, not the truth-hunch itself.

## 7. Why this is not a renamed old route

1. **Not Hilbert--Pólya.**  Zeros are annihilator characters on source cohomology, not postulated
   eigenvalues of a self-adjoint operator.
2. **Not Weil positivity.**  Chain-level form may be indefinite.  Isometry is proved only on
   harmonic source classes by exact transgression.
3. **Not the existing Hodge--Green moment route.**  No target moment cone or Stieltjes
   representation is inserted.  Gamma is identified with the actual Wold defect determinant
   before Xi moments are read.
4. **Not quasi-inner compactness.** Calkin or Hankel compactness permits discrete nonunitary
   fibres. Equation `(9)` is only a possible consequence of the mixed support theorem; the other
   isometry side is already fixed by the source metric.
5. **Not generic FE/positivity/HT.**  Off-line generalized-prime quartet models do not carry the
   literal integer multiplication coisometries, the BV off-multiple identity, and the completed
   co-Poisson differential simultaneously.
6. **Not a scalar Gamma coincidence.**  Equation `(4)` identifies every defect eigenvalue, and
   `(7)--(8)` identify the nonsummable trace density and the actual Laurent boundary coordinate.

## 8. Hostile falsifiers

Retire the RH mechanism if any of the following occurs.

1. The Gamma phase in `(4)` enters only as a scalar determinant and has no source map into the
   co-Poisson conormal graph.
2. The one-step mixed anomaly has no source-defined closed graph after the completed Gamma and
   polar boundary blocks are added.
3. The totalization or its domain depends on a chosen zero, a divisor residue norm, or Weil
   positivity.
4. The harmonic projection kills an uncensored BV conormal jet.
5. The total differential fails closability in the critical product bornology.
6. An explicit off-line Euler system carries all six fixed blocks and the same mixed anomaly
   class.
7. `I+mathcalA_Xi` fails at a nonunitary character, or an Xi principal conormal does not occur in
   its strict failure locus.

The strongest positive survivor after falsification would be a classification of the residual
Wold anomaly class.  It would identify the additional independent channel missing from the
current six-channel HT architecture.

## 9. Literature boundary

Parent ingredients are classical and not claimed as new:

- Wold decompositions and multiplication isometries;
- second regularized Fredholm determinants;
- Euler's reciprocal-Gamma product;
- Hilbert complexes, Hodge projection, and chain homotopy;
- Burnol's co-Poisson/Sonine quotient;
- Connes--Consani scaling and quasi-inner local-factor operators.

Homological perturbation and torsion of contractible/Koszul complexes are also parent theory.  In
particular, perturbing a contraction and reading secondary determinants is not itself new.
Relative cyclic cocycles, renormalized traces, and boundary eta cocycles for algebra extensions
are also parent theory. Perrot's `Extensions and renormalized traces` and Moriyoshi--Piazza's
relative eta-cocycle construction show that a regularized bulk cochain and a secondary boundary
cocycle naturally belong to one relative class. They support the extension/mapping-cone category
but do not identify the arithmetic Wold determinant with the BV conormal, construct
`mathcalA_Xi`, or prove `(14)`.

Targeted exact searches found Wold decomposition theory, Gamma/Fredholm determinant literature,
Connes--Consani quasi-inner local factors, and irregular/polarized Hodge theory, but no source
identifying the Gamma quotient as the polarized determinant cocycle of the arithmetic
multiplication Wold defect, its singular trace density with the BV off-multiple zeta conormal
residue, or the anomaly-inflow purity chain `(13)`.

Closest primary sources:

- Connes--Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>;
- Connes--Consani, *Quasi-inner functions and local factors*,
  <https://arxiv.org/abs/2008.10974>;
- Perrot, *Extensions and renormalized traces*, <https://arxiv.org/abs/0908.1757>;
- Moriyoshi--Piazza, *Eta cocycles, relative pairings and the Godbillon--Vey index theorem*,
  <https://arxiv.org/abs/1102.2876>;
- Sköldberg, *Algebraic Morse theory and homological perturbation theory*,
  <https://arxiv.org/abs/1311.5803>;
- Kaad, *Joint torsion of several commuting operators*,
  <https://arxiv.org/abs/1011.0356>;
- Sabbah, *Irregular Hodge theory*, <https://arxiv.org/abs/1511.00176>;
- Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, <https://www.numdam.org/articles/10.5802/jtnb.434/>.

This is a provisional noncollision report, not a priority proof.

## 10. Gates

- [x] multiplicative Wold covariance and rigidity proved on paper
- [x] exact polarized `det_2` Gamma cocycle proved on paper
- [x] exact singular first-trace asymptotic proved on paper
- [x] exact match with existing BV off-multiple residue coefficient
- [x] correct-sided range-defect-exactness-to-purity implication proved as a sufficient lemma
- [x] actual coefficient Wold resolution proved canonically split exact
- [x] generic Wold/Hodge exactness retired as non-frontier
- [x] exact RH consumer identified through existing Burnol/BV interfaces
- [x] internal exact-match search negative
- [x] preliminary external exact-match search negative
- [ ] construct one-step completed source differential and mixed class `mathcalA_(Xi,q)`
- [ ] prove critical closability and harmonic conormal survival
- [ ] identify strict failure locus with Xi conormal divisor
- [ ] prove strict failure support is unitary
- [ ] formalize only dependency-closed source theorems in Lean
- [ ] compose unconditional RH proof
