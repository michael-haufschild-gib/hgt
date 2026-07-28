# Multiplicative Wold--Gamma anomaly and source-cohomological purity

- **ID:** `multiplicative-wold-gamma-anomaly-purity-rh`
- **Stage:** 1 — in progress
- **Type:** GENERAL HT MECHANISM / SOURCE-SPECIFIC RH PROGRAM
- **Scientific status:** `[NEW MECHANISM] [EXACT CORE THEOREM PAPER-PROVED]`
  `[EXTERNAL NOVELTY PROVISIONAL] [RH CHAIN INCOMPLETE]`
- **RH used:** no
- **Computation used:** no
- **Parents:**
  `../2-fully-proven/new_scientific_knowledge/prime-occupation-polarized-gamma-phase-survival.md`,
  `../2-fully-proven/not_new_scientific_knowledge/bv-prime-window-polar-coefficient-decimation-law.md`,
  `../2-fully-proven/not_new_scientific_knowledge/burnol-copoisson-berezin-diagonal-reflection-law.md`,
  `../3-formalized/hypertranscendental-minimal-polarized-critical-completion-architecture.md`,
  `../3-formalized/source-producer-integral-realization-minimality.md`.

## Mechanism in one sentence

The hypertranscendental Gamma phase is the regularized determinant of the Wold defect of
multiplicative arithmetic dilation, while the BV zeta-pole residue is its missing first-trace
conormal coordinate; after these two layers are assembled into one source Hilbert complex,
chain-unitarity makes every zeta annihilator character pure, hence critical.

This is not another positivity criterion.  It identifies a previously missing source coupling
between the Gamma HT phase and the exact coefficient operator whose annihilator eigencharacter
measures horizontal zero displacement.

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

The source dilation `U_q` must be a chain map.  The decisive identity is not positivity of a
target kernel but **unitarity modulo the source differential**:

```text
U_q^* U_q-I=d_F^* K_q+K_q^* d_F.                        (9)
```

Equation `(9)` is the anomaly-inflow law.  The coefficient coisometry has a positive Wold defect;
the Gamma determinant and first-trace conormal term place that defect in the exact part of the
total source complex.

### Abstract purity consequence

Assume `(9)`, and assume the harmonic projection `P_F` is source-defined and commutes with `U_q`.
For a harmonic vector `h`,

```text
d_F h=0,   d_F^* h=0.
```

Taking its matrix coefficient in `(9)` gives

```text
||U_q h||^2-||h||^2=0.                                  (10)
```

Thus source dilation is isometric on harmonic cohomology.  No global positive divisor measure,
real-rooted approximation, self-adjoint zero operator, or Weil-sign premise occurs.

This is the proposed general **polarized anomaly-cancellation purity theorem** for constrained
hypertranscendental sources: source transport can be nonunitary on chains, but every effective
annihilator class is pure after its regular determinant and first-trace anomaly are retained.

## 5. Riemann specialization

Burnol's co-Poisson quotient supplies source-defined annihilator evaluation vectors.  BV
continuation supplies the exact dilation character.  At a nontrivial zero `rho`, for an uncensored
fixed dyadic window,

```text
U_q^* k_rho=conj(q^(rho-1/2)) k_rho,   k_rho!=0.         (11)
```

The existing convention using `r` instead of `q=r^2` writes the same character as
`r^(2rho-1)`.

If the completed Wold--Gamma--co-Poisson complex realizes `k_rho` as a harmonic conormal class,
then `(10)--(11)` imply

```text
|q^(rho-1/2)|<=1,
Re(rho)<=1/2.                                            (12)
```

Functional-equation reflection gives the opposite inequality for every nontrivial zero, hence
`Re(rho)=1/2` and RH.

The proof mechanism is therefore:

```text
finite arithmetic decimation coisometry
  -> Wold defect
  -> regular layer = HT Gamma determinant cocycle
  -> singular layer = BV Laurent conormal coordinate
  -> one completed source Hilbert complex
  -> chain-unitarity modulo completed co-Poisson differential
  -> purity of annihilator cohomology
  -> |q^(rho-1/2)|=1
  -> RH.                                                  (13)
```

## 6. Exact new open core

`WOLD-GAMMA-COPOISSON-ANOMALY-INFLOW`:

Construct the total source differential `d_Xi` before annihilator specialization and prove
`(9)` with the following fixed blocks:

1. coefficient block: exact `D_q,S_q,E_q` Wold system;
2. regular boundary block: `Phi_q^def` from `(4)`;
3. conormal block: pole-cancelled BV/co-Poisson normal class, with `(8)`;
4. archimedean block: the same tangent-normalized Gamma phase, not its DA intensity;
5. source constraint block: completed co-Poisson multiplier and its adjoint;
6. harmonic effectivity: every uncensored annihilator conormal jet survives nontrivially.

The first construction test is the one-step defect identity.  On a compact source core, exhibit
`K_q` for which the coefficient Wold projection `E_q` plus the Gamma boundary and first-trace
normal term equals `d_Xi^*K_q+K_q^*d_Xi`.  This must be checked before taking a cofinal limit.

## 7. Why this is not a renamed old route

1. **Not Hilbert--Pólya.**  Zeros are annihilator characters on source cohomology, not postulated
   eigenvalues of a self-adjoint operator.
2. **Not Weil positivity.**  Chain-level form may be indefinite.  Isometry is proved only on
   harmonic source classes by exact transgression.
3. **Not the existing Hodge--Green moment route.**  No target moment cone or Stieltjes
   representation is inserted.  Gamma is identified with the actual Wold defect determinant
   before Xi moments are read.
4. **Not quasi-inner compactness.**  Calkin or Hankel compactness permits discrete nonunitary
   fibres.  Equation `(9)` is an exact cohomological unitarity statement.
5. **Not generic FE/positivity/HT.**  Off-line generalized-prime quartet models do not carry the
   literal integer multiplication coisometries, the BV off-multiple identity, and the completed
   co-Poisson differential simultaneously.
6. **Not a scalar Gamma coincidence.**  Equation `(4)` identifies every defect eigenvalue, and
   `(7)--(8)` identify the nonsummable trace density and the actual Laurent boundary coordinate.

## 8. Hostile falsifiers

Retire the RH mechanism if any of the following occurs.

1. The Gamma phase in `(4)` enters only as a scalar determinant and has no source map into the
   co-Poisson conormal graph.
2. The one-step Wold defect represents a nonzero class after the completed Gamma and polar
   boundary blocks are added, so `(9)` is false.
3. The required `K_q` depends on a chosen zero, a divisor residue norm, or Weil positivity.
4. The harmonic projection kills an uncensored BV conormal jet.
5. The total differential fails closability in the critical product bornology.
6. An explicit off-line Euler system carries all six fixed blocks and satisfies `(9)`.

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

Targeted exact searches found Wold decomposition theory, Gamma/Fredholm determinant literature,
Connes--Consani quasi-inner local factors, and irregular/polarized Hodge theory, but no source
identifying the Gamma quotient as the polarized determinant cocycle of the arithmetic
multiplication Wold defect, its singular trace density with the BV off-multiple zeta conormal
residue, or the anomaly-inflow purity chain `(13)`.

Closest primary sources:

- Connes--Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>;
- Connes--Consani, *Quasi-inner functions and local factors*,
  <https://arxiv.org/abs/2008.10974>;
- Sabbah, *Irregular Hodge theory*, <https://arxiv.org/abs/1511.00176>;
- Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, <https://www.numdam.org/articles/10.5802/jtnb.434/>.

This is a provisional noncollision report, not a priority proof.

## 10. Gates

- [x] multiplicative Wold covariance and rigidity proved on paper
- [x] exact polarized `det_2` Gamma cocycle proved on paper
- [x] exact singular first-trace asymptotic proved on paper
- [x] exact match with existing BV off-multiple residue coefficient
- [x] abstract chain-unitarity-to-purity implication proved
- [x] exact RH consumer identified through existing Burnol/BV interfaces
- [x] internal exact-match search negative
- [x] preliminary external exact-match search negative
- [ ] construct one-step completed source differential and transgression `K_q`
- [ ] prove critical closability and harmonic conormal survival
- [ ] prove chain-unitarity for every integer `q>=2`
- [ ] formalize only dependency-closed source theorems in Lean
- [ ] compose unconditional RH proof
