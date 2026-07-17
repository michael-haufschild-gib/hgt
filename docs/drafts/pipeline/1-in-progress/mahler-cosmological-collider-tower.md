# A Mahler cosmological-collider tower as a hypertranscendental primordial signal

- **ID:** `mahler-cosmological-collider-tower`
- **Stage:** 1-in-progress
- **Type:** COSMOLOGY CANDIDATE / OBSERVABLE HT SIGNATURE
- **Scientific status:** `[MATHEMATICAL HT CORE PROVED] [PHYSICAL REALIZATION OPEN]`
  `[NOVELTY UNVERIFIED] [NOT YET NEW SCIENTIFIC KNOWLEDGE]`
- **Scope:** general hypertranscendence in primordial correlators; no RH or distinguished
  special-function input
- **Statement:** An exact geometric tower of principal-series frequencies with the natural
  heavy-particle suppression has a smooth positive-frequency squeezed-limit signal given by a
  Mahler germ.  That analytic signal is hypertranscendental.  The open physics is to make the
  geometric tower and its residues source-natural rather than chosen after the fact.

## Exact mathematical signal

Fix an integer `p>=2` and define

```text
M_p(w)=sum_(k>=0) w^(p^k),          |w|<1.                  (1)
```

It satisfies the inhomogeneous Mahler constraint

```text
M_p(w)=w+M_p(w^p).                                         (2)
```

Applying the annihilator of the rational forcing term `w` gives a homogeneous second-order
Mahler equation over `C(w)`.  The Adamczewski--Dreyfus--Hardouin rational-or-HT theorem therefore
applies.  The support `{p^k}` has arbitrarily long zero gaps; an eventually recurrent rational
power series cannot have that support.  Hence `M_p` is not ramified rational and

```text
M_p is hypertranscendental over C(w).                       (3)
```

The derivation in the Mahler theorem is the Euler derivation `w d/dw`.

## Cosmological-collider interpretation

Let

```text
r=k_L/k_S in (0,1),       u=log r,
mu_k=p^k.                                                   (4)
```

A principal-series field of frequency `mu` contributes a nonanalytic squeezed-limit oscillation
with phase `exp(i mu u)`.  In the Bunch--Davies vacuum, heavy-particle production is generically
suppressed by `exp(-pi mu)`.  The idealized positive-frequency tower is therefore

```text
A_p(u)=sum_(k>=0) exp(-pi p^k) exp(i p^k u)
      =M_p(exp(-pi+i u)).                                  (5)
```

Unlike a Weierstrass series with merely geometric coefficient decay, `(5)` is real analytic in
`u`: every differentiated series is dominated by
`sum p^(mk) exp(-pi p^k)`.  The HT conclusion is not an artifact of nonsmooth data.

Put `z=exp(iu)`.  Then `A_p(u)=M_p(exp(-pi)z)`.  Nonzero constant argument scaling preserves
differential algebraicity and HT, and `d/du=i z d/dz`.  Thus the analytic positive-frequency
primordial signal is HT over the natural phase-coordinate field `C(z)`.

This conclusion concerns the complex wavefunction/positive-frequency coefficient.  The real
bispectrum contains it together with the negative-frequency conjugate.  Recovering the positive
Hardy component from complete log-momentum data is a bounded noncompact projection, which is the
correct reporter type for an infinite HT sector.  A proof for the actual survey window and transfer
map remains open.

## Why this is physically sharper than a chosen HT initial state

The coefficient `exp(-pi mu_k)` is the standard production suppression, and the phases in `(5)`
are the mass spectroscopy signal of the cosmological collider.  The construction does not insert
an arbitrary HT function as an initial condition.  It does, however, still prescribe the exact
geometric frequency tower and assumes shell-universal residues.  Those are the load-bearing open
inputs.

Finite particle content cannot produce `(3)`: every finite tower gives a finite exponential sum,
which is differentially algebraic.  The HT signal therefore certifies an irreducibly infinite
mass/frequency completion within this collider class.

## Source-internal comparison

The exact one-sided ultrametric boundary spectrum now supplies a source-derived geometric tower
inside a field Hessian; see
`../2-fully-proven/not_new_scientific_knowledge/ultrametric-one-loop-resolvent-hypertranscendence.md`.
For each Euclidean de Sitter harmonic, the first finite one-loop mass susceptibility is an HT
`q`-difference germ.  This closes the **field-internal tower** problem for a Gaussian, mode-resolved
effective-action reporter.

It does not close the present card.  The collider frequencies `(4)`, their principal-series
production weights, the complete wavefunction coefficient, and late-time transfer have not been
derived from that internal boundary operator.  Moreover the Gaussian influence hierarchy has
zero face-complete Wick--Kolchin profile.  A source-natural spectrum is therefore necessary but
not sufficient for the sought interacting primordial signal.

## Anti-theatre attacks

1. **Finite-diagram relabeling.**  A fixed finite collection of exchange diagrams gives a finite
   exponential/holonomic signal and is DA.  HT begins only at the infinite tower.
2. **Nonsmooth lacunarity.**  Coefficients `a^k` can make a unit-circle lacunary signal fail to be
   smooth.  The physical `exp(-pi p^k)` factor avoids that loophole.
3. **Transcendental-coordinate inflation.**  The claim is over the phase coordinate
   `z=exp(i log r)` with Euler derivation, which is exactly the coordinate in which collider
   frequencies are Fourier modes.  No claim over an unrelated rational `r` base is made.
4. **Real-part cancellation.**  HT of the positive-frequency component is proved.  HT of an
   arbitrary real symmetrization is not asserted without a stable Hardy reconstruction theorem.
5. **Tower by decree.**  Choosing `mu_k=p^k` after deciding to use Mahler theory is not a physical
   derivation.  The candidate is not promoted until a source-minimal sector forces the tower.
6. **Transfer-function engineering.**  Late-time propagation must be proved to retain the Hardy
   component; inserting an inverse transfer function by hand is circular.

## Novelty gate

Parent theories already contain:

- cosmological-collider oscillations and mass spectroscopy;
- Boltzmann suppression of heavy principal-series production;
- discrete and continuous towers in cosmological correlators;
- lacunary Mahler functions and their hypertranscendence;
- Hardy projections and Fourier recovery.

The focused search did not find the exact conclusion `(3)`--`(5)` stated as an HT primordial
observable, but this negative evidence is not a novelty proof.  Merely placing a classical Mahler
function into a collider template is parent-derived synthesis.  Candidate new science begins with
the physical selection theorem below.

## Fields/Nobel gate

`[CONJECTURE -- HORIZON-SHELL MAHLER SELECTION]` A source-minimal inflationary or de Sitter sector
exists in which horizon-shell decimation sends `mu_k` to `mu_(k+1)=p mu_k`, fixes the relative
production residues, and induces `(2)` on an intrinsic wavefunction coefficient.  The resulting
positive-frequency reporter survives gauge reduction and late-time transfer through a stable
noncompact channel.

Required proof obligations:

1. derive the geometric spectrum from a local unitary sector or an intrinsic RG/horizon-shell
   functor;
2. derive the exact residues, including spin and polynomial mass factors, without tuning each
   coupling separately;
3. compute the complete wavefunction coefficient rather than only its asymptotic squeezed term;
4. prove invariance under local counterterms, field redefinitions, and admissible initial-state
   choices;
5. prove stable recovery after cosmological transfer and finite survey windowing;
6. audit formula-level collisions with discrete-scale cosmology, clock signals, and infinite-tower
   collider models.

## Lean boundary

The existing HTGeometry corpus already supplies:

- formal support-gap irrationality for lacunary power series;
- formal inhomogeneous Mahler-equation solvability machinery;
- unconditional constant-argument-scaling invariance of differential algebraicity;
- unconditional HT equivalence with the logarithmic derivative;
- the compact-reporter observability wall.

The external rational-or-HT Mahler theorem is not formalized in the project.  The next useful Lean
target is the exact formal series `(1)`, its constraint `(2)`, and its support-gap nonrationality;
an abstract wrapper calling the external HT theorem would not be a proof.

## Primary literature

- N. Arkani-Hamed and J. Maldacena, *Cosmological Collider Physics*,
  <https://arxiv.org/abs/1503.08043>.
- S. Aoki, *Continuous Spectrum on Cosmological Collider*,
  <https://arxiv.org/abs/2301.07920>.
- Y. Yin, *The cosmological collider signal in the non-BD initial states*,
  <https://arxiv.org/abs/2309.05244>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
