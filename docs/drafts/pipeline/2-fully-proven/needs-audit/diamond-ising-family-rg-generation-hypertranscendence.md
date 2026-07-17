# Every branching diamond-Ising exact beta is hypertranscendental

- **ID:** `diamond-ising-family-rg-generation-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / EXACT PHYSICAL RG FAMILY
- **Scientific status:** `[PROVED HERE] [PARENT-DERIVED CLASSIFICATION]`
  `[INFINITE PHYSICAL MODEL FAMILY] [NOVELTY NEEDS AUDIT] [NOT YET CONTINUUM QFT]`
- **Scope:** general hypertranscendence in interacting exact renormalization; no
  Riemann-hypothesis or distinguished-special-function input
- **Statement:** For every integer `b >= 2`, the zero-field Ising model on the `b`-branch,
  two-bond diamond hierarchical lattice has a unique nontrivial thermal fixed point.  Its exact
  local beta field is hypertranscendental in physical transmissivity and in every locally
  invertible DA coupling scheme.

## Exact family of physical RG maps

Let `z_s` and `z_d` be the Boltzmann weights for equal and unequal endpoint spins, and use the
projective high-temperature coordinate

```text
t=(z_s-z_d)/(z_s+z_d)=tanh K.                                    (1)
```

One branch contains two bonds in series, and there are `b` identical branches in parallel.  Exact
summation of the internal spins gives the renormalized projective weights

```text
Z_s=(z_s^2+z_d^2)^b,                 Z_d=(2 z_s z_d)^b.           (2)
```

Writing `z_s=A(1+t)` and `z_d=A(1-t)` in `(2)` and taking
`(Z_s-Z_d)/(Z_s+Z_d)` gives

```text
             (1+t^2)^b-(1-t^2)^b
R_b(t) = --------------------------------.                        (3)
             (1+t^2)^b+(1-t^2)^b
```

For `b=2`, equation `(3)` is `2t^2/(1+t^4)`.  Thus the previously proved two-branch theorem is the
first member of an exact physical family, not a specially inserted rational map.

The denominator in `(3)` is, up to the nonzero projective factor, the one-block normalization
`Z_s+Z_d`.  Its complex zeros are the primitive block-normalization/Fisher divisor.  Pulling this
divisor back under repeated exact RG produces the corresponding higher-generation divisor tower.

## Unique nontrivial fixed point and its multiplier

On the physical interval put

```text
u=log((1+t)/(1-t))=2 arctanh(t),              t=tanh(u/2).        (4)
```

The identity

```text
(1+t^2)/(1-t^2)=cosh u                                         (5)
```

turns `(3)` into the analytically conjugate map

```text
G_b(u)=b log(cosh u).                                            (6)
```

Let `H_b(u)=G_b(u)-u` for `u>=0`.  Then

```text
H_b(0)=0,
H_b'(u)=b tanh u-1,
H_b''(u)=b sech^2 u>0,                                          (7)
```

and

```text
H_b(u)=(b-1)u-b log 2+o(1)             as u -> +infinity.       (8)
```

Therefore `H_b` first decreases, has one strict negative minimum at
`u_0=arctanh(1/b)`, and then increases to infinity.  It has exactly one positive zero `u_b`, and
`u_b>u_0`.  Hence

```text
c_b=tanh(u_b/2) in (0,1)                                       (9)
```

is the unique nontrivial physical fixed point.  Analytic conjugacy preserves its multiplier, so

```text
lambda_b=R_b'(c_b)=G_b'(u_b)=b tanh u_b>1.                      (10)
```

Thus `c_b` is the repelling thermal fixed point separating the high- and low-temperature basins.

## The critical portrait is never Ritt-integrable

The numerator and denominator in `(3)` are coprime: a common zero would force both
`(1+t^2)^b` and `(1-t^2)^b` to vanish.  Exactly one of their leading terms of degree `2b`
survives, according to the parity of `b`.  Hence

```text
deg R_b=2b.                                                       (11)
```

At the high-temperature fixed point,

```text
R_b(t)=b t^2+O(t^6),                                            (12)
```

so `0` is superattracting with local degree two.  At the low-temperature fixed point, write
`x=1-t^2`; then

```text
1-R_b(t)=2x^b/((2-x)^b+x^b).                                    (13)
```

Thus `1` is superattracting with local degree `b`.  In particular `R_b` has two distinct
superattracting fixed points, with local degrees `2` and `b`, both strictly below its global degree
`2b`.

Suppose the normalized Poincare function at `c_b` were differentially algebraic.  The
Ritt--Becker--Bergweiler classification leaves only three dynamical types.

1. **Power type.** A degree-`2b` power map has two superattracting fixed points, both totally
   ramified with local degree `2b`; an inverse power map has its totally ramified points in a
   two-cycle.  Neither portrait matches `(12)`--`(13)`.
2. **Signed Chebyshev type.** A signed Chebyshev polynomial has only its point at infinity as a
   superattracting fixed point; its finite critical points map to noncritical endpoints.  It cannot
   have the two superattracting fixed points in `(12)`--`(13)`.
3. **Elliptic/Weierstrass type.** The associated rational maps have empty Fatou set.  The
   superattracting basin of `0` already gives `R_b` a nonempty Fatou set.

Möbius conjugacy preserves global degree, local degrees, periodic critical portraits, and emptiness
of the Fatou set.  All DA cases are therefore impossible.  If `Phi_b` is the normalized Poincare
function at `c_b`, then

```text
Phi_b is hypertranscendental over C(z) for every b>=2.           (14)
```

## Exact beta and scheme theorem

Let `kappa_b=Phi_b^(-1)` locally and define

```text
beta_b(t)=(log lambda_b) kappa_b(t)/kappa_b'(t).                  (15)
```

DA germs are closed under local compositional inversion, so `Phi_b` is DA exactly when `kappa_b`
is DA.  If `beta_b` were DA, the first-order equation

```text
beta_b kappa_b'-(log lambda_b)kappa_b=0                          (16)
```

and transitivity of differential algebraicity would make `kappa_b`, hence `Phi_b`, DA.  This
contradicts `(14)`.  Therefore

```text
beta_b is hypertranscendental over C(t) for every b>=2.          (17)
```

For a locally invertible DA coupling scheme `v=h(t)` with DA inverse,

```text
beta_(b,h)(h(t))=h'(t) beta_b(t).                                (18)
```

DA closure applied in both directions makes `(17)` invariant under every such scheme.  An
arbitrary analytic chart can linearize the flow, but every such linearizing chart is itself HT.

## Physical interpretation: a Fisher-divisor obstruction to finite scale generation

This family identifies a source-level mechanism:

```text
internal-spin decimation
  -> complex block-normalization divisor
  -> nonexceptional branched RG portrait
  -> differential incoherence of the RG tower
  -> HT exact scale generator.                                  (19)
```

The appearance of partition-function zeros as boundaries or singular loci of complex RG flows is
parent science.  The new claim requiring audit is the last two arrows: their exact assembly into a
scheme-invariant HT generator theorem for the whole branching family.

The presence of complex zeros alone is not sufficient.  DA functions such as trigonometric and
elliptic functions also have infinite structured divisors, and the Ritt-integrable power and
Chebyshev maps are the exact counterexamples.  What matters is that the block divisor generates a
critical portrait outside every parabolic-orbifold/Ritt family.

## Anti-theatre and dual gate

The exact projective RG, the relation between hierarchical RG and Fisher zeros, analytic
linearization, and the Ritt--Becker--Bergweiler classification are parent results.  The work here is
the uniform fixed-point proof `(4)`--`(10)`, the family-wide critical-portrait exclusion, and the
physical HT interpretation `(19)`.

The significance gate improves on the isolated `b=2` result: RG-generation HT now holds for an
infinite family of interacting exact models with varying branching geometry.  The novelty gate is
still open pending formula-level review of hierarchical Ising/Potts complex dynamics and the
differential-transcendence literature.  This is not yet a continuum-QFT theorem.

## Lean boundary

The family formula `(3)`, its Boltzmann-weight derivation `(2)`, the fixed values `R_b(0)=0` and
`R_b(1)=1`, and the local algebra behind `(12)`--`(13)` are unconditional finite algebra.  They are
now formalized in
`../../3-formalized/diamond-ising-family-exact-rg-algebra.md`, through module
`GaloisForLFunctions.HTGeometry.DiamondIsingFamilyRG`.  The analytic fixed-point theorem and the external
Ritt--Becker--Bergweiler classification are not yet in the Lean corpus and must not be replaced by
hypotheses or axioms.

The formal module is substantive rather than a `b=2` wrapper: it derives both physical block
weights for arbitrary `b`, proves the exact normalization factors, proves quadratic contact at the
high-temperature anchor, and proves primitive numerator/denominator noncancellation over `C`.

## Primary sources

- J. De Simoi, *Potts models on hierarchical lattices and Renormalization Group dynamics II:
  examples and numerical results*, <https://arxiv.org/abs/0711.4610>.
- J. De Simoi and S. Marmi, *Potts models on hierarchical lattices and Renormalization Group
  dynamics*, <https://arxiv.org/abs/0708.0616>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.
- A. Denbleyker, D. Du, Y. Liu, Y. Meurice, and H. Zou,
  *Fisher's zeros as boundary of renormalization group flows in complex coupling spaces*,
  <https://arxiv.org/abs/1005.1993>.

## Gates

- [x] Exact `b`-branch physical map derived in projective transmissivity.
- [x] Unique nontrivial repelling physical fixed point proved for every `b>=2`.
- [x] Global and local degrees proved.
- [x] Every Ritt-integrable dynamical portrait excluded.
- [x] Exact beta HT and DA-scheme invariance proved for the whole family.
- [x] Fisher-divisor mechanism isolated without claiming that zeros alone imply HT.
- [ ] Formula-level novelty audit across hierarchical RG and complex dynamics completed.
- [x] Substantive unconditional family algebra formalized in HTGeometry with targeted verification
  and axiom audit.
- [ ] Continuum-QFT realization proved.
