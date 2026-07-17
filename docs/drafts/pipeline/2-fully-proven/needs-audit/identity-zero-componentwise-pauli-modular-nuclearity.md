# A braid identity zero retains the full factorial modular-nuclearity gain

- **ID:** `identity-zero-componentwise-pauli-modular-nuclearity`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / COMPACT-LOCAL QFT BRIDGE / CONVENTION REPAIR
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY UNVERIFIED]`
- **Scope:** regular finite-multiplet factorizing S-matrices in the operator-algebraic
  construction; no RH or distinguished special-function input
- **Parent:** `fermionic-zero-braid-anchor-commutation-gate.md`
- **Statement:** In the Alazzawi--Lechner modular-nuclearity theorem, replace the zero value
  `S(0)=-F` by `S(0)=-I_(K tensor K)` and require the same bounded analytic intertwiner to
  the corresponding constant-zero symmetric subspace.  Then the modular-nuclearity
  conclusion is unchanged: for sufficiently large double-cone separation, the map `Xi(s)`
  is nuclear.  The proof has the same `n^n/n!` particle-number bound.

## The identity-zero reference space

Write the one-particle Hilbert space as

```text
H_1=L^2(R) tensor K,
d=dim K<infinity.                                               (1)
```

Under the canonical regrouping

```text
H_1^(tensor n)
  = L^2(R^n) tensor K^(tensor n),                               (2)
```

the constant braid twist `S_0=-I_(K tensor K)` generates the permutation-group action

```text
D_n^(-I)(tau_k)=-T_k^(rap) tensor I_(K^(tensor n)),             (3)
```

where `T_k^(rap)` exchanges only the two rapidity variables.  Hence its invariant subspace
and orthogonal projection are

```text
H_n^(-I)=Exterior^n L^2(R) tensor K^(tensor n),
Q_n=P_n^(rap,-) tensor I_(K^(tensor n)).                        (4)
```

This is componentwise rapidity antisymmetry.  It is not the full exterior power
`Exterior^n H_1`, but it still supplies a factorial trace bound.

## Partial Pauli trace lemma

In the published Hardy-to-nuclear decomposition, the trace-class one-particle factors are

```text
hat R_(delta,r,epsilon)=R_(g,-epsilon r) tensor I_K             (5)
```

and the middle positive majorant has the form

```text
Z_hat=Z_0 tensor I_K.                                          (6)
```

The symmetric multiplier and the sum over all sign vectors commute with `Q_n`, exactly as
they commute with the full fermionic projection in the published proof.  The only trace
estimate that changes is

```text
Tr_(Q_n)(Z_hat^(tensor n))
  =d^n Tr_(Exterior^n L^2(R))(Z_0^(tensor n))
  <=d^n ||Z_0||_1^n/n!.                                       (7)
```

Since

```text
||Z_0||_1
  <=||R_(g,+r)||_1+||R_(g,-r)||_1,                             (8)
```

the factor `d^n` in `(7)` is exactly the internal multiplicity already present in the
published estimate through

```text
||R_(g,b) tensor I_K||_1=d ||R_(g,b)||_1.                      (9)
```

Therefore the identity-zero compression obeys the same bound as the full Pauli
compression:

```text
||Q_n X_(C_n,s)||_1
  <=(2^n/n!)
    [ d/(pi m_0/2)^(1/2)
      * exp(-s m_0 cos(c_n)/2)/(c_n (s cos(c_n))^(1/2)) ]^n.  (10)
```

No equal-mass hypothesis is needed.  As in the published proof, replacing all component
masses by the mass gap `m_0` produces a larger scalar-in-`K` operator before applying the
intertwiner and the projection.

## Identity-zero intertwiner theorem

Assume the same analytic data as the published intertwiner property: for every `n`, a
bounded analytic multiplication operator `I_n` on the Hardy tube, with

```text
||I_n||<=gamma^n,
||I_n^(-1)||<=gamma_tilde^n,                                   (11)
```

and whose boundary value maps the `S`-symmetric subspace onto `H_n^(-I)`.  With the
mass-gap replacement `X_tilde`, equation `(4)` gives

```text
I_n X_tilde
  =Q_n I_n X_tilde
  =Q_n X_tilde I_n.                                            (12)
```

Consequently

```text
||X_(C_n,s)||_1
  <=gamma_tilde^n gamma^n ||Q_n X_tilde_(C_n,s)||_1.           (13)
```

Inserting `(10)` into the unchanged Hardy factorization yields constants independent of
`n` such that

```text
||Xi_n(s)||_1
  <=C_1(s) [C_2 exp(-C_3 s)/sqrt(s)]^n n^n/n!.                 (14)
```

Since `n^n/n!<=e^n/sqrt(2 pi)`, the series over particle number is summable for all
sufficiently large `s`.  This proves modular nuclearity under the identity-zero
intertwiner hypothesis.

## What this theorem does and does not repair

For a standard physical quantum S-matrix with fermionic zero `R(0)=-P`, the convention-
correct braid conversion `B=R P` has `B(0)=-I`.  The theorem proves that this
zero value retains enough Pauli suppression; changing `-F` to `-I` does not destroy the
factorial nuclearity mechanism.

The right-flip reconstruction theorem proves that the standard-subspace crossing condition
for `B` is exactly the physical crossing condition for `R=B P`, and that Haag--Ruelle
scattering reconstructs `R` on the ordered rapidity chamber.  Thus only one independent
gate remains:

1. bounded analytic intertwiners to `H_n^(-I)` must be built uniformly in `n`.

The theorem is therefore a real compact-local bridge, not a completed construction of the
`O(N)` model or of a projective-HT nonabelian model.  It removes the zero-anchor trace
obstruction and leaves the analytic cocycle problem exposed.

## Physical consequence for projective HT

The exact nonabelian HT construction lane is now

```text
positive-unitary projective-HT quantum R, R(0)=-P
  -> braid conversion with zero -I
  -> identity-zero analytic intertwiner
  -> modular nuclearity and compact-local observables.         (15)
```

There is no state-dimension penalty in the trace mechanism beyond the existing exponential
factor `d^n`, which is dominated by `n!`.  Thus internal channel complexity and projective
HT are compatible with the nuclearity estimate in principle; the remaining obstruction is
analytic coherence of the Yang--Baxter cocycle, not thermodynamic state counting.

## Anti-theatre attacks

1. **`-I` called ordinary Fermi statistics.**  False.  It gives rapidity-only
   antisymmetry with untouched internal tensor order.
2. **Partial antisymmetry assumed to give the full-fermion trace.**  The proof explicitly
   pays `d^n`; it succeeds because the published estimate already contains that factor.
3. **Equal masses silently assumed.**  Not needed for the bound: the published mass-gap
   domination makes the relevant nuclear operator scalar on `K`.
4. **The `O(N)` model declared constructed.**  False.  Crossing and reconstruction are now
   convention-correct, but the all-particle analytic intertwiner remains open.
5. **An elementary trace estimate advertised as new physics.**  The scientific content is
   the removal of the purported Pauli obstruction on the convention-correct nonabelian
   locality lane.  Novelty still requires a literature audit.

## Novelty and significance gates

Focused searches for `modular nuclearity S(0)=-I intertwiner`, `componentwise
antisymmetry factorizing S-matrix`, and `identity-zero Pauli factorizing S-matrix` found no
published identity-zero extension of the matrix-valued theorem.  This is negative search
evidence, not a novelty certificate.

The significance gate is provisionally passed.  Combined with the convention theorem,
this result restores a mathematically viable compact-local route for intrinsically mixing
physical quantum S-matrices.  It shows that the braid zero `-I` still supplies exactly the
factorial improvement needed to overcome the `n^n` Hardy loss.

## Exact open core

1. Formulate the identity-zero intertwiner property independently of the source's
   convention-conflicted `O(N)` discussion.
2. Construct all-particle bounded analytic identity-zero intertwiners for a genuinely
   mixing physical model.
3. Audit later modular-nuclearity and twisted-Fock literature for this partial-
   antisymmetry theorem.
4. Formalize the finite permutation-projection and factorial trace skeleton in Lean only
   where the existing `HTGeometry` API supports a reusable unconditional statement.

## Primary literature

- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.
- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- G. Lechner and C. Schuetzenhofer, *Towards an Operator-Algebraic Construction of
  Integrable Global Gauge Theories*, <https://arxiv.org/abs/1208.2366>.

## Gates

- [x] identity-zero symmetric subspace identified
- [x] partial Pauli trace estimate proved
- [x] internal multiplicity tracked exactly
- [x] mass-gap replacement removes equal-mass dependence
- [x] modular-nuclearity summability proved under the identity-zero intertwiner
- [x] right-flip crossing and scattering-reconstruction audit
- [ ] all-particle analytic identity-zero intertwiner
- [ ] literature novelty audit
- [ ] unconditional Lean formalization of the finite reusable skeleton
- [ ] compact-local intrinsically mixing projective-HT quantum field theory
