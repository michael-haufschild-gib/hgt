# Hypertranscendental clock modular--spectral alternative

- **ID:** `hypertranscendental-clock-modular-spectral-alternative`
- **Stage:** 3-formalized
- **Type:** GENERAL HT POSITIVE-COMPLETION THEOREM / CLOCK COMPACTIFICATION LAW
- **Scientific status:** `[TWO-BRANCH THEOREM PROVED] [LEAN FORMALIZED] [EXHAUSTIVENESS CONJECTURAL] [EXTERNAL NOVELTY PROVISIONAL] [NOT AN RH RESULT]`
- **Parents:** `hypertranscendental-clock-normalization-symmetry-anomaly.md` and
  `../../3-formalized/finite-observable-conormal-corona.md`
- **Statement:** A normal positive realization of the infinite unit clock boundary has two exact
  mechanisms.  In a diagonal realization it carries a persistent modular anomaly.  In an exactly
  unitary non-diagonal realization it condenses into one canonical fixed spectral line, and the
  clock orbit cannot be Bessel.  Thus positivity can preserve either stable diagonal observability
  or exact clock symmetry, but not both while normalizing the boundary.

## 1. Algebraic boundary input

Let

```text
I=C^(N) subset P=C^N,       b=(1,1,1,...) in P.               (1)
```

The free HT jet clock has no nonzero finite-support constraint conormal.  Every finite prefix of
`b` is algebraically soluble, but `b` is the unique compatible product boundary and does not lie in
`I`.  A positive completion is therefore asked to do something genuinely infinitary: make `b`
normal without introducing a finite differential-polynomial relation.

## 2. Branch I: modular normalization

For a positive diagonal completion

```text
H_w={a : sum_n w_n |a_n|^2<infinity},    w_n>0,              (2)
```

normality of `b` is equivalent to `sum_n w_n<infinity`.  The clock-normalization theorem proves:

1. the ratio `Delta_w(n)=w_(n+1)/w_n` differs from `1` beyond every finite cutoff;
2. no bounded positive gauge makes the reweighted clock stationary;
3. reflection symmetry gives `Delta_w(-n-1)=Delta_w(n)^(-1)`;
4. on positive total-mass-one two-sided weights, `Delta_w` reconstructs `w` uniquely.

Thus the diagonal branch keeps coordinate observability but pays with a complete persistent modular
class.

## 3. Branch II: spectral condensation

Let `H` be a complex Hilbert space, `U:H->H` unitary, and `u_n`, `n in Z`, a total orbit:

```text
u_(n+1)=Uu_n,
[forall n, <u_n,z>=0] ==> z=0.                               (3)
```

Assume a normal boundary vector `b_H in H` realizes the infinite unit packet:

```text
<u_n,b_H>=1              for every n in Z.                   (4)
```

### Theorem A: fixed-point condensation

Equation `(4)` forces

```text
U b_H=b_H.                                                     (5)
```

Indeed, for every `n`, unitarity and `(3)` give

```text
<u_n,U^(-1)b_H-b_H>
 =<Uu_n,b_H>-<u_n,b_H>
 =<u_(n+1),b_H>-<u_n,b_H>=0.
```

Totality then gives `U^(-1)b_H=b_H`, hence `(5)`.

### Theorem B: uniqueness and one-dimensionality

The response condition `(4)` determines `b_H` uniquely.  Moreover every fixed vector `z`,
`Uz=z`, satisfies

```text
z=<u_0,z> b_H.                                                 (6)
```

The response `<u_n,z>` is independent of `n`; subtracting the right side of `(6)` leaves a vector
orthogonal to the total orbit.  Consequently

```text
Fix(U)=C b_H.                                                   (7)
```

The unique product boundary has become exactly one simple zero-frequency spectral atom.

### Theorem C: Bessel instability

If the forward orbit had a finite Bessel bound `B`, then applying that bound to `b_H` on the first
`N` modes would give

```text
N=sum_(n<N)|<u_n,b_H>|^2 <= B ||b_H||^2                       (8)
```

for every `N`, impossible.  Hence

```text
{u_n:n>=0} is not a Bessel sequence.                            (9)
```

This is not a negative dead end.  It is the exact positive description of how a non-diagonal
completion restores symmetry: it creates one canonical invariant boundary line and necessarily
makes the coordinate orbit redundantly coherent rather than stably synthesizable.

## 4. The normalization compactification law

The two branches admit one geometric reading.  The algebraic clock is a free infinite orbit with a
missing product boundary.

- A diagonal positive completion keeps the boundary distributed over the free orbit.  Finite mass
  then makes the measure quasi-invariant rather than invariant, and the boundary is recorded by its
  persistent modular cocycle.
- An exactly symmetric completion keeps the clock unitary by adjoining a fixed point at infinity.
  The boundary mass condenses at that point, producing the simple spectral atom `(7)` and destroying
  the Bessel property of the orbit that sees it with constant response.

Call the resulting datum a **pointed measured clock compactification**

```text
C_HT=(Xbar, tau, [mu], b_infinity),                            (10)
```

where the free clock orbit lies in `Xbar`, `b_infinity` is the corona boundary, and `[mu]` carries
both the Radon--Nikodym cocycle on the free sector and the invariant atomic sector.

The modular-corona class and the fixed spectral atom are therefore not competing metaphors.  They
are the two exact normal forms already forced by `(10)` in the diagonal and unitary cyclic models.

## 5. Bold completeness conjecture

**[CONJECTURE: MODULAR--SPECTRAL CLOCK COMPACTIFICATION.]**  Every source-defined positive rigging of
a finitely generated HT clock has a functorial decomposition, after passing to its minimal clock
compactification, into

```text
quasi-invariant free-orbit sector  +  invariant boundary-atomic sector.   (11)
```

Its modular-corona splitting stack is the derived moduli of admissible changes between the two
sectors.  Every persistent realization obstruction factors conservatively through `(11)`:

```text
spectral incompleteness = missing or misplaced boundary atom,
continuation failure    = failure to extend the quasi-invariant measure class,
positivity failure      = failure of positive mass or positive cocycle,
monodromy               = holonomy of its Radon--Nikodym class,
boundary noncanonicity  = multiplicity of invariant boundary sectors.    (12)
```

In the total scalar clock model, Theorems A--C prove that exact symmetry collapses the last item:
the boundary sector is one-dimensional and canonically normalized by `(4)`.  The next hard theorem
is to prove `(11)` for non-diagonal source riggings without assuming unitarity at the outset, using
the polar/Wold decomposition of the clock relation rather than choosing a carrier ad hoc.

## 6. What this says about hypertranscendence

The topology constraining an HT function faces an exact choice:

```text
normal boundary + stable coordinate observability  ==> modular anomaly,
normal boundary + exact clock symmetry              ==> simple spectral atom + Bessel failure.
                                                                    (13)
```

The boundary is not time.  It is the observable that represents the complete infinite clock packet.
The modular class measures the cost of distributing that observable across the free orbit; the
spectral atom is what it becomes when the topology instead fixes it at infinity.

This is a concrete answer to “what constrains hypertranscendental functions themselves?”: their
algebraic jet freedom forces every normal global constraint into the modular--spectral geometry of
a clock compactification.

## 7. External novelty gate

The novelty gate is only against external literature.

Classical parents include the spectral theorem for cyclic unitary operators, the identification of
point spectrum with atoms of the cyclic spectral measure, Bessel/frame inequalities, weighted-shift
theory, quasi-invariant measures, and Radon--Nikodym cocycles.  Representative modern frame work
includes Yu, *Frame-normalizable Sequences*, arXiv:2308.13071; standard spectral references include
the cyclic and unitary spectral theorems in Simon's *Operator Theory*; the modular parents are listed
in the normalization--symmetry card.

The fixed-vector calculation, one-dimensional cyclic eigenspace, and Bessel contradiction are
parent-level Hilbert-space facts.  The targeted search found no external result joining them to the
free Kähler clock of a hypertranscendental source and the algebraically invisible unit corona, nor a
normalization compactification theorem asserting the exact modular-versus-atomic alternative
`(13)`.  Candidate novelty lies in the HT implication `(13)` and the pointed measured clock object
`(10)`, not in spectral or frame theory separately.  This is a provisional absence claim, not a
priority claim.

## 8. Significance and anti-theatre verdict

- The diagonal-only anomaly is not universal; the spectral branch is an explicit positive escape.
- The escape is rigid rather than arbitrary: one canonical fixed line and unavoidable loss of
  Bessel stability.
- The two branches turn “spectral incompleteness” and “positivity failure” into exact alternative
  realizations of the same missing unit boundary.
- The theorem is general HT mathematics; no zeta datum occurs in its hypotheses.
- The proved two-branch law is a plausible central theorem of a standalone paper with the conormal
  corona and splitting-stack results.
- It is not yet Fields-scale because exhaustiveness of `(11)` for source-defined non-diagonal
  riggings remains conjectural.

## 9. Lean status

`formal/GaloisForLFunctions/HTGeometry/HypertranscendentalClockBoundary.lean` verifies:

- `unitaryClockBoundary_fixed_of_total_constantResponse`;
- `clockBoundary_unique_of_total_response`;
- `unitaryClock_fixedVector_eq_smul_boundary`.

`formal/GaloisForLFunctions/RHTower/DirichletHilbertRiggingBarrier.lean` already verifies the general
Bessel contradiction as `no_bessel_family_with_unit_response`.  The diagonal branch is verified by
the five modular theorems listed in the normalization--symmetry card.  The touched boundary module
passed direct Lean verification with cached dependencies; no build was run for it.

## Gates

- [x] prove boundary fixedness under exact unitary clock symmetry
- [x] prove uniqueness of the normal unit-response boundary
- [x] prove the fixed spectral sector is exactly one-dimensional
- [x] reuse the formal Bessel no-go without duplicating it
- [x] formalize all new spectral kernels in Lean
- [x] 2 -> 3: the proved diagonal modular branch, unitary fixed-line condensation,
  response uniqueness, one-dimensionality, and Bessel obstruction are Lean-formalized
- [x] identify cyclic spectral, frame, weighted-shift, and modular parent theories
- [ ] prove the modular--atomic decomposition for arbitrary positive clock relations
- [ ] construct it from one source-defined non-diagonal HT rigging
- [ ] prove three conservative obstruction representations of `(12)`
- [ ] complete specialist external priority review
