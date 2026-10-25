# Finite cofactor index counts joint spectral multiplicity

- **ID:** finite-cofactor-index-counts-joint-spectral-multiplicity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Statement:** In the finite-dimensional branch of every actual cofactor
  module, the module hull is a finite set of joint generalized characters.
  Its closed-annihilator index is the sum of the positive dimensions of their
  joint generalized eigenspaces. These are module multiplicities, not yet
  identified with orders of arithmetic zeros.

## Inputs inspected in the corpus

The universal actual module has a unital commuting Wiener action and a cyclic
vector. Its finite dimension equals the dimension of its annihilator quotient.
`HTGeometry/MatrixPrincipalSymbolAbelianSpectrum.lean` implements independent,
exhaustive joint maximal generalized eigenspaces for arbitrary commuting
families in finite dimension. It also proves finiteness of the nonzero joint
sectors and linearity of their eigencharacters. Its underlying mathlib results
are in `LinearAlgebra/Eigenspace/Pi.lean` and `Triangularizable.lean`.

## Dependency-closed paper proof

Let H be a finite-dimensional actual module, W its critical Wiener algebra,
pi its representation, and I=ker(pi). For a function chi:W->C define

`J_chi = intersection_(a in W) maxGenEigenspace(pi(a), chi(a))`.

Commutativity makes every generalized eigenspace invariant under every pi(a).
The inspected joint decomposition therefore says that all J_chi are
independent, their sum is H, and only finitely many are nonzero. Write S for
those functions and m_chi=dim J_chi>0. Thus `dim H=sum_(chi in S) m_chi`.

Each chi in S is a unital complex algebra character. Linearity is already
available from the joint generalized eigencharacter lemma. For multiplication,
on J_chi put N_a=pi(a)-chi(a)Id and N_b=pi(b)-chi(b)Id. Both are nilpotent:
in finite dimension maximal generalized eigenspace membership gives a uniform
nilpotence exponent on J_chi. They commute. The operator

`pi(ab)-chi(a)chi(b)Id = chi(a)N_b+chi(b)N_a+N_a N_b`

is nilpotent too: a sufficiently high power expands into monomials in which
one of the two nilpotent exponents is exceeded. Hence J_chi also lies in the
generalized eigenspace of pi(ab) at chi(a)chi(b). Distinct generalized
eigenspaces are disjoint, so nonzero J_chi forces chi(ab)=chi(a)chi(b).
The identity operator similarly forces chi(1)=1. The character automatically
obeys the Banach-algebra spectral bound and is therefore a Wiener Bohr
evaluation. Every a in I acts as zero, so chi(a)=0. Thus all these points lie
in the module hull.

Conversely let phi be a hull character distinct from every chi in S. For each
chi choose a_chi with phi(a_chi)!=chi(a_chi). Choose N_chi so that
`(pi(a_chi)-chi(a_chi)Id)^N_chi` kills J_chi. The product

`b = product_(chi in S) (a_chi-chi(a_chi)1)^N_chi`

annihilates every J_chi, hence all H, by commutativity and the exhaustive
decomposition. Therefore b belongs to I. But phi(b) is a finite product of
nonzero numbers, contradicting that phi vanishes on I. This proves that the
hull consists exactly of the finite joint-character set.

Finally cyclicity identifies W/I linearly with H in finite dimension. Its
index is consequently the sum of `dim J_omega` over the distinct characters
of the module hull. This supplies
the module multiplicity needed by a finite index formula. Merely counting
distinct hull points discards all dimensions greater than one.

### Exact Bohr encoding

The existing `BohrPoint` structure leaves `omega(0)` unspecified. The corpus
already makes this distinction in `BohrPoint.eq_of_primes` and
`bohrEval_congr`: equality and evaluation are read on positive integers.
Thus a literal sum over the raw Bohr-point type is not the character sum.
Use the canonical section `omega(0)=0`, or equivalently the algebra characters.
Character extraction supplies this normalization. Evaluation is injective on
the normalized section: point masses recover every positive coordinate, and
both zero coordinates are fixed. Every raw hull point has the same evaluation
as its normalized representative. The all-one positive character has two raw
representatives (zero coordinate zero or one), so this is a substantive count
convention, not a theorem identifying the two structures.

## Scope and novelty audit

The decomposition and algebra argument are standard consequences of the
inspected finite-dimensional spectral theory; no new general theorem of
commutative algebra is claimed. The contribution is the exact index notion
available for every actual cofactor module, together with the separate
continuum alternative already proved for infinite actual modules. Nothing
here puts the characters on the Kronecker curve, identifies them with zeta
zeros, or identifies m_omega with a zero order. Those remain actual-source
classification questions.

## Gates

The first Lean draft is `/tmp/qiii_finite_joint_characters_body.lean`.
It uses the existing `HTGeometry.exists_common_eigenvector` inside each
nonzero joint sector to prove multiplicativity, avoiding a separate nilpotent
binomial expansion. It also derives the exact finite dimension sum from the
existing independent-supremum rank theorem. This draft is not checked yet;
Bohr identification and the converse hull inclusion remain to be drafted.

- [x] Dependency-closed paper argument, with all actual structural inputs proved.
- [x] Relevant corpus mechanisms inspected; no arithmetic hypothesis added.
- [ ] Lean finite joint decomposition and exact dimension sum.
- [ ] Multiplicative characters, finite Bohr hull equality, actual index formula.
- [ ] Transitive axiom audit, final source checks, umbrella imports.
