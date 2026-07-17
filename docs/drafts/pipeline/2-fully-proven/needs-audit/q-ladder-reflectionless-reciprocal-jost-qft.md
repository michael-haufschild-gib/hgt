# A geometric q-ladder Hamiltonian has HT transmission and a reciprocal local-QFT lift

- **ID:** `q-ladder-reflectionless-reciprocal-jost-qft`
- **Stage:** 2-fully-proven / needs external novelty audit
- **Type:** THEOREM (paper) / PHYSICAL EXISTENCE BRIDGE / INVERSE SCATTERING
- **Scientific status:** `[PROVED HERE] [PHYSICAL SOURCE IN QUANTUM MECHANICS]`
  `[QFT SCATTERING-DATA LIFT PROVED] [NOVELTY UNVERIFIED] [SIGNIFICANCE GATE OPEN]`
- **Scope:** general hypertranscendence in quantum scattering and integrable QFT; no RH or
  distinguished special-function input
- **Parents:** `../../1-in-progress/geometric-cdd-hypertranscendental-local-qft.md`,
  `open-family-hypertranscendental-cdd-qft.md`, and
  `../../1-in-progress/geometric-cdd-higher-spin-completion-fracture.md`
- **Statement:** A smooth real reflectionless Schrodinger Hamiltonian with one geometric bound-state
  ladder has a hypertranscendental transmission coefficient and Wigner phase delay.  The determinant
  of its two-channel scattering matrix, evaluated at reciprocal relativistic momentum, is exactly
  the regular geometric CDD amplitude that reconstructs a local interacting factorizing QFT.

## The local Hamiltonian

Fix

```text
0 < q < 1,                  kappa > 0,
kappa_n = kappa q^n,        c_n = kappa_n,       n >= 0.       (1)
```

Then

```text
sum_n kappa_n < infinity,
sum_n c_n^2/kappa_n = sum_n kappa_n < infinity.               (2)
```

For finite `N`, let `V_N(s,x)` be the standard `N`-soliton KdV potential with discrete wave
numbers `kappa_0,...,kappa_(N-1)` and norming constants `c_0,...,c_(N-1)`.  The infinite-soliton
theorem of Gesztesy--Karwowski--Zhao applies to `(1)`--`(2)`.  It gives a real smooth limit

```text
H_infty(s) = -d^2/dx^2 + V_infty(s,x)                          (3)
```

with the following exact properties:

1. `V_infty` solves KdV and is the smooth local limit of the finite soliton potentials.
2. The absolutely continuous spectrum is `[0,infinity)`.
3. The simple discrete spectrum is exactly

   ```text
   {-kappa^2 q^(2n) : n >= 0}.                                (4)
   ```

4. Scattering is reflectionless and its two-channel matrix is

   ```text
   S_Sch(k) = diag(T(k),T(k)),
   T(k) = product_(n>=0) (k+i kappa q^n)/(k-i kappa q^n).      (5)
   ```

5. The scattering matrix, hence `T`, is independent of the KdV time `s`.

This is a local Hamiltonian realization.  The special function in `(5)` is a consequence of the
geometric spectrum of a reflectionless differential operator, not the definition of the model.

## Claim A -- hypertranscendental quantum transmission `[PROVED]`

Put

```text
z = i kappa/k,
F_q(z) = product_(n>=0) (1+q^n z)/(1-q^n z),
T(k) = F_q(i kappa/k).                                        (6)
```

Normal convergence away from the pole set makes `F_q` meromorphic, analytic at zero, and gives
the exact one-shell equation

```text
F_q(z) = (1+z)/(1-z) F_q(qz).                                 (7)
```

It has zeros at `-q^(-n)` and poles at `q^(-n)` for all `n>=0`, so it is not rational.  The
Adamczewski--Dreyfus--Hardouin rational-or-HT theorem for a Laurent-series solution of a linear
`q`-difference equation with rational coefficients applies to `(7)`.  Since the rational branch is
excluded by the infinite divisor,

```text
F_q is HT over C(z).                                           (8)
```

Rational substitution preserves differential algebraicity.  Therefore differential algebraicity
of `T(k)=F_q(i kappa/k)` over `C(k)` would contradict `(8)`.  Hence

```text
T is HT over C(k).                                             (9)
```

This is not a claim about an arbitrarily chosen amplitude: `(5)` is the physical transmission
coefficient of the smooth local Hamiltonian `(3)`.

## Claim B -- the measurable phase delay is HT `[PROVED]`

For real nonzero `k`, reflectionlessness gives `|T(k)|=1`.  The phase derivative is

```text
L(k) = T'(k)/T(k).                                             (10)
```

If `L` were DA over `C(k)`, then `T` would satisfy the first-order differential equation

```text
y' - L y = 0                                                   (11)
```

over a DA extension of `C(k)`.  Differential-algebraic transitivity would make `T` DA, contrary
to `(9)`.  Thus `L` is HT.  With nonrelativistic energy `E=k^2`, the Wigner phase delay

```text
tau_W(k) = -i d/dE log T(k) = -i L(k)/(2k)                    (12)
```

is HT as well.  The HT observable is a real scattering delay on the physical axis, not merely an
off-shell analytic continuation.

## Claim C -- the constraint is spectral, not evolutionary `[PROVED]`

Equation `(7)` is equivalently

```text
T(k) = (k+i kappa)/(k-i kappa) T(k/q),
T(k) -> 1 as k -> infinity.                                   (13)
```

The boundary condition at infinite momentum selects the one-sided completion.  Every finite
soliton truncation has a rational transmission coefficient and is DA.  The full geometric
spectral completion is HT:

```text
finite reflectionless bound-state set: rational/DA scattering,
complete q-ladder bound-state set:       HT scattering.        (14)
```

At the same time, `V_infty(s,x)` evolves by the differential-polynomial KdV equation while `T`
is independent of `s`.  Hypertranscendence is therefore an isospectral boundary invariant of a
local differential flow.  It is not generated by integrating the KdV vector field.  This is a
literal instance of the founding principle:

```text
the HT observable is fixed by an infinite spectral constraint,
not propagated by a finite differential flow.                 (15)
```

## Open-family extension -- finitely many geometric ladders `[PROVED]`

Let `kappa_1,...,kappa_r` be positive and assume their `q`-orbits are pairwise disjoint.  The
combined spectrum

```text
{-kappa_j^2 q^(2n) : 1 <= j <= r, n >= 0}                     (15a)
```

is simple and summable in wave number.  Taking `c_(j,n)=kappa_j q^n`, the same unconditional
infinite-soliton theorem produces a smooth real reflectionless Hamiltonian with transmission

```text
T_r(k) = product_(j=1)^r product_(n>=0)
           (k+i kappa_j q^n)/(k-i kappa_j q^n).                (15b)
```

With `z=i/k`, its normalized germ

```text
F_r(z) = product_(j=1)^r product_(n>=0)
           (1+kappa_j q^n z)/(1-kappa_j q^n z)                 (15c)
```

satisfies

```text
F_r(z) = B_r(z) F_r(qz),
B_r(z) = product_(j=1)^r (1+kappa_j z)/(1-kappa_j z).          (15d)
```

The divisor remains infinite, so the rational branch of the difference-Galois dichotomy is
impossible and `T_r` is HT.  Spiridonov's `r`-step `q`-periodic Darboux closure is the matching
operator architecture: it produces `r` geometric spectral ladders rather than inserting the
infinite product by hand.

After reciprocal momentum substitution, the determinant of the left/right scattering matrix is
the finite-positive-shell sector of `open-family-hypertranscendental-cdd-qft.md`, up to relabelling
the shell radii.  Repeating a factor with multiplicity `2m_j` is realized by the determinant of
`m_j` identical two-channel blocks.  It is **not** represented as a repeated eigenvalue of one
scalar one-dimensional Schrodinger operator, whose bound states are simple.  Thus the complete
finite-multiplicity open family has a canonical multichannel determinant source.

## Operator-level origin of the geometric ladder

Spiridonov's self-similar Darboux chain supplies a local operator mechanism for the spectral law
in `(4)`.  Its superpotential satisfies

```text
f'(x) + q f'(qx) + f(x)^2 - q^2 f(qx)^2 = K,                  (16)
```

and the dilation-dressed factorization operators obey the `q`-oscillator algebra

```text
A^- A^+ - q^2 A^+ A^- = K,
H A^+ = q^2 A^+ H,          H A^- = q^(-2) A^- H.             (17)
```

The resulting bound-state spectrum is a geometric ladder.  More generally, a `q`-periodic
closure of an `N`-step Darboux chain produces `N` geometric ladders and a finite rational shell in
the transmission equation.

The proof of Claims A--C uses the unconditional infinite-soliton theorem `(1)`--`(5)`, not an
unproved identification between a particular norming sequence and a particular solution of
`(16)`.  Equation `(16)` identifies the source architecture that can force the spectrum; matching
the complete inverse-scattering data of the two constructions is a separate audit target.

## Claim D -- reciprocal determinant lift to a local interacting QFT `[PROVED]`

Fix `C>1`.  For nonzero rapidity define the reciprocal spectral map

```text
k_C(theta) = kappa C/sinh(theta).                              (18)
```

Using the two-channel determinant in `(5)`, define

```text
S_C(theta) = -det S_Sch(k_C(theta)) = -T(k_C(theta))^2.        (19)
```

Direct substitution gives

```text
T(k_C(theta))
  = product_(n>=0) (C+i q^n sinh(theta))/(C-i q^n sinh(theta)),

S_C(theta)
  = -product_(n>=0)
       ((1+i q^n sinh(theta)/C)/(1-i q^n sinh(theta)/C))^2.    (20)
```

With the crossing coordinate

```text
t(theta) = -i sinh(theta)/C,                                  (21)
```

equation `(20)` becomes exactly

```text
S_C(theta)
  = -product_(n>=0) ((1-q^n t(theta))/(1+q^n t(theta)))^2.     (22)
```

This is the geometric CDD scattering function of the parent local-QFT card.  Therefore the square
in that model has a canonical origin:

```text
two asymptotic Schrodinger channels  ->  determinant T^2.      (23)
```

The reciprocal map has a second exact effect.  The Schrodinger eigenvalues accumulate at the
continuum threshold, `kappa q^n -> 0`.  Under `(18)` their divisor is sent to the outward CDD
orbit `q^(-n)`, away from the physical rapidity strip.  Thus reciprocity converts a threshold
ladder into a regular relativistic resonance completion.

The parent analysis then supplies, without a new hypothesis:

1. unitarity and crossing symmetry of `S_C`;
2. `S_C(0)=-1`, obtained from `T(infinity)=1` and the determinant sign in `(19)`;
3. analyticity and boundedness on an enlarged rapidity strip for `C>1`;
4. hypertranscendence in the canonical coordinate `(21)`;
5. reconstruction of an asymptotically complete local interacting Haag--Kastler net by Lechner's
   regular inverse-scattering theorem.

Since a square root algebraic over a DA extension is DA, `T^2` cannot be DA when `T` is HT.
Consequently the determinant lift retains, rather than cancels, the Kolchin obstruction.

## Exact physical boundary of Claim D

Claim D is an exact identity of scattering data followed by a rigorous inverse-scattering QFT
reconstruction.  It is not yet a functor from the Schrodinger Hilbert space to the Haag--Kastler
net, nor a derivation of `(18)` from a common microscopic action.

The missing source theorem is now sharply isolated:

> `[CONJECTURE -- RECIPROCAL JOST DUALITY]` There is a local interface, modular construction, or
> operator-flow duality whose induced map on the scalar scattering sector is
> `k -> kappa C/sinh(theta)` and whose channel determinant becomes the relativistic two-particle
> scattering function.

Proving this would upgrade `(19)` from a kinematic reciprocal lift to a dynamical derivation of the
HT QFT.  Until then, the local Schrodinger Hamiltonian is a genuine physical source for HT quantum
scattering, while its relation to the local interacting QFT is a proved scattering-data bridge.

The active child card
`../../1-in-progress/feshbach-reciprocal-jost-interface.md` proves the first source mechanism:
eliminating a locally coupled massless channel forces `k^2=g^2/p^2`, and its Schur-relative
Fredholm determinant is the inverse Jost transmission.  It also proves that the naive Euclidean
block is not positive and that a purely Gaussian parent cannot have `(19)` as an interacting bulk
two-particle amplitude.  The open core is therefore no longer the origin of reciprocity itself;
it is a positive non-Gaussian promotion of that exact local response mechanism.

## Why direct relativistic substitution fails

The tempting direct lift `k proportional to sinh(theta)` sends every Schrodinger pole
`k=i kappa q^n` into the physical rapidity strip.  These poles accumulate at the threshold
`theta=0`, so the resulting amplitude is not a bounded regular scattering function of Lechner's
class.  Reciprocal momentum in `(18)` is not cosmetic: it reverses the divisor and is exactly what
makes the local-QFT reconstruction possible.

## Cosmology pressure test

The scalar cosmological mode equation has Schrodinger form

```text
v_k''(eta) + (k^2-U(eta)) v_k(eta) = 0,
U(eta)=z''(eta)/z(eta)                                         (24)
```

for the Mukhanov--Sasaki pump field `z`, with analogous equations for tensor modes.  If an
admissible background realized `U=V_infty`, reflectionlessness would give zero
reflected/Bogoliubov coefficient and a transmitted coefficient equal, up to convention, to `T` or
`T^(-1)`.  The mode phase would then be HT and conserved by the isospectral KdV deformation.

The full-line realization is, however, ruled out by an exact sign obstruction.  The
infinite-soliton construction gives the pointwise identity

```text
V_infty(s,eta)
  = -4 sum_(n>=0) kappa_n psi_n(s,eta)^2 <= 0,                (25)

integral_R V_infty(s,eta) d eta
  = -4 sum_(n>=0) kappa_n < 0.                               (26)
```

Suppose a nonsingular cosmological pump were nonzero on the whole conformal-time line and obeyed
`z''/z=V_infty`.  Its sign would be constant, so replace `z` by `-z` if necessary and assume
`z>0`.  Equation `(25)` gives

```text
z'' = V_infty z <= 0.                                        (27)
```

Thus `z` is a positive concave function on all of `R`.  Such a function is constant: if
`z'(eta_0)>0`, monotonicity of `z'` forces `z` to become negative sufficiently far to the left;
if `z'(eta_0)<0`, it becomes negative sufficiently far to the right.  Therefore `z'=0`, and
`z''=V_infty z` forces `V_infty=0`, contradicting `(26)`.  Hence

```text
no everywhere-nonzero full-line cosmological pump has
z''/z = V_infty for a nontrivial reflectionless soliton well. (28)
```

This kills the naive cosmological embedding.  The live branches are narrower:

1. a finite or half-line conformal-time interval, where the global concavity argument does not
   apply;
2. a source transformation producing a sign-indefinite or positive pump potential while retaining
   the HT phase constraint;
3. a phase-sensitive higher-point or interference observable, since `|T|=1` makes a Gaussian
   two-point magnitude blind even when a mode-scattering realization exists.

No observational claim is made.

## Claim E -- the ground-state shift gives an exact HT cosmological mode problem `[PROVED]`

The canonical escape from `(28)` is already contained in the spectral data.  The lowest eigenvalue
of `H_infty` is `-kappa^2`.  By one-dimensional ground-state positivity, its real eigenfunction
`psi_0` can be chosen strictly positive on `R`.  Set

```text
z(eta) = psi_0(eta),
U(eta) = z''(eta)/z(eta).                                     (29)
```

The ground-state equation

```text
-z'' + V_infty z = -kappa^2 z                               (30)
```

gives the exact pump potential

```text
U = kappa^2 + V_infty.                                        (31)
```

This shift evades the concavity no-go because `U` is not everywhere nonpositive.  It is also
spectrally canonical: `H_infty+kappa^2` is nonnegative and has `z` as its zero mode.

For a cosmological comoving wave number `p`, the mode equation becomes

```text
v_p'' + (p^2-U)v_p
  = v_p'' + (p^2-kappa^2-V_infty)v_p = 0.                     (32)
```

For `p^2>kappa^2`, put `k=(p^2-kappa^2)^(1/2)`.  Equation `(32)` is exactly the scattering
equation for `H_infty` at energy `k^2`.  Therefore

```text
Bogoliubov reflection coefficient beta_p = 0,
transmission coefficient alpha_p = T(k)^(+1 or -1),            (33)
```

where the sign in the exponent depends only on the in/out convention.  Algebraic change of
spectral variable cannot remove hypertranscendence: if
`T((p^2-kappa^2)^(1/2))` were DA over `C(p)`, the inverse algebraic substitution
`p=(k^2+kappa^2)^(1/2)` would make `T(k)` DA over `C(k)`.  Hence the transmitted cosmological mode
phase is HT.

This is an unconditional realization at the linear mode-equation level.  It is not yet a complete
cosmological model:

1. If `z` is taken to be the tensor pump `a`, then the bound-state decay makes `a` tend to zero at
   both conformal ends; the associated flat-FRW spacetime is generically a finite-proper-time
   big-bang/big-crunch geometry rather than a nonsingular inflationary background.
2. If `z` is a scalar Mukhanov--Sasaki pump, one must reconstruct background fields satisfying the
   Einstein--matter equations and verify stability and energy conditions.
3. Since `|T|=1`, a standard Gaussian power-spectrum magnitude is blind to the HT phase.  The
   physical reporter must use interference, unequal-time data, a boundary observable, or
   higher-point phase information.

Inverse-scattering formulations of inflation already identify cosmological mode equations with
Schrodinger/Jost problems.  The candidate new content under audit is not that dictionary; it is the
geometric infinite-soliton source, its proved HT transmission, and the exact ground-state-shifted
mode family `(29)`--`(33)`.

## Anti-theatre and novelty gate

The following are parent knowledge and are not claimed as new:

- self-similar Darboux chains, `q`-oscillator algebras, and geometric spectra;
- smooth infinite-soliton reflectionless potentials and their product transmission coefficient;
- Jost/CDD and `q`-gamma hierarchies in integrable-model literature;
- rational-or-HT classification for linear `q`-difference equations;
- local QFT reconstruction from a prescribed regular factorizing scattering function.

Targeted formula searches found each parent separately but did not find the following conjunction:

1. a proof that the physical transmission coefficient of the geometric infinite-soliton
   Hamiltonian is HT;
2. the interpretation of this HT as a KdV-conserved scattering invariant;
3. the exact reciprocal determinant identity `(19)`--`(22)` with a regular local interacting QFT;
4. the explanation of the CDD multiplicity two as the determinant of the two asymptotic channels.
5. the ground-state-shifted reflectionless cosmological mode family with HT transmitted phase.

That negative search evidence is not a novelty proof.  The card remains in `needs-audit` until a
specialist literature audit checks inverse-scattering, self-similar-potential, Jost-function,
factorizing-S-matrix, and `q`-special-function sources at formula level.

The result clears a substantial significance threshold: it supplies a smooth local Hamiltonian
whose measurable scattering delay is HT and connects it exactly to a local interacting QFT at the
scattering-data level.  It does not yet clear the medal-level gate because the reciprocal map lacks
a physical derivation.

## Exact open core

1. Promote the massless-channel Schur interface of
   `../../1-in-progress/feshbach-reciprocal-jost-interface.md` to a positive non-Gaussian local
   dynamics whose exact two-particle amplitude is `(19)`.
2. Determine whether the q-self-similar Darboux potential and the explicit infinite-soliton norming
   family can be identified within one local operator model.
3. Classify matrix-coupled, rather than direct-sum, multichannel sources and the possible
   rational-coboundary exceptions.
4. Prove an action-level or finite-volume/TBA realization of the reciprocal determinant QFT.
5. Embed the ground-state-shifted pump in an admissible Einstein--matter background and identify a
   phase-sensitive cosmological observable.
6. Complete the external novelty audit.

## Failed source selectors recorded by this investigation

1. **Yang--Baxter/quantum-group symmetry alone.**  Scalar multiplication preserves the
   Yang--Baxter equation.  Quantum-group constructions determine a matrix part but retain a scalar
   dressing/CDD sector; they do not force the geometric shell.
2. **Longo--Witten data alone.**  The operator-algebraic construction takes scattering operators as
   input.  Its general massless and block-diagonal massive constructions do not select the scalar
   CDD factor, and strict locality is not automatic.
3. **A bare q-special function.**  Freund--Zabrodin already place q-deformed Jost and CDD factors in
   a hierarchy.  Merely renaming `(5)` as a q-gamma quotient would be rediscovery.  The new content
   under audit is the local-Hamiltonian HT theorem and reciprocal determinant lift.

## Lean boundary

The live HTGeometry tree was checked before this card was written.  It already contains:

- `GeometricCDDConstraint.lean` for finite shell shifting;
- `GeometricCDDBoundarySelection.lean` for convergence, the affine one-shell law, endpoint
  continuity, and uniqueness;
- general moment/Hankel infrastructure used by the higher-spin completion card.

The new theorem depends essentially on the analytic infinite-soliton inverse-scattering theorem,
meromorphic product transmission, the external difference-Galois dichotomy, and Lechner's
analytic QFT reconstruction.  Repackaging `(7)` or `(13)` as another finite algebraic Lean wrapper
would duplicate the existing corpus and leave every substantive implication external.  No Lean
edit or build is justified at this stage.  A future unconditional formalization should begin only
after there is a reusable analytic scattering interface expressing `(3)`--`(5)`.

## Primary literature

- F. Gesztesy, W. Karwowski, and Z. X. Zhao, *New types of soliton solutions*,
  <https://arxiv.org/abs/math/9210215>.
- V. Spiridonov, *Symmetries of the Self-Similar Potentials*,
  <https://arxiv.org/abs/hep-th/9303004>.
- P. G. O. Freund and A. V. Zabrodin, *A Hierarchic Array of Integrable Models*,
  <https://arxiv.org/abs/hep-th/9208033>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- S. Habib, K. Heitmann, and G. Jungman, *Inverse-Scattering Theory and the Density Perturbations
  from Inflation*, <https://arxiv.org/abs/astro-ph/0409599>.
- J. Mastache, F. Zago, and A. Kosowsky, *Inflationary Dynamics Reconstruction via
  Inverse-Scattering Theory*, <https://arxiv.org/abs/1611.03957>.
- M. Bischoff and Y. Tanimoto, *Integrable QFT and Longo--Witten endomorphisms*,
  <https://arxiv.org/abs/1305.2171>.
- A. Rej and F. Spill, *The Yangian of sl(n|m) and the universal R-matrix*,
  <https://arxiv.org/abs/1008.0872>.

## Gates

- [x] smooth local reflectionless Hamiltonian exists
- [x] exact geometric spectrum and transmission product are source-audited
- [x] transmission and Wigner delay HT proofs are complete
- [x] finite-union geometric-ladder family and multichannel multiplicities are classified
- [x] KdV conservation of the HT scattering invariant is source-audited
- [x] reciprocal determinant identity with the regular CDD QFT is exact
- [x] direct-lift obstruction and exact physical boundary are stated
- [x] naive full-line cosmological pump embedding is ruled out
- [x] ground-state-shifted HT cosmological mode equation is constructed
- [x] live Lean corpus checked; no wrapper build opened
- [ ] external formula-level novelty audit complete
- [ ] reciprocal Jost map derived from common physical dynamics
- [ ] admissible cosmological background and phase-sensitive reporter constructed
