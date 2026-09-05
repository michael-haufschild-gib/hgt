# Cubic aggregate spectral current

**Open question:** For arbitrary orthogonal projections `P,Q,R`, does nuclearity of
`C=(R-P)^3-(R-Q)^3-(Q-P)^3` alone force `Tr C=0`?

**Status:** OPEN in Lean. Existing commuting-source and nuclear-adjacent-product theorems do not
answer this question. A continuous-symbol counterexample is under hostile audit below. This is a
scoped operator question within the source/index comparison, not an RH producer. No universal
retirement is justified.

**Checked sources:** `CommutingSourceCubicConservation`,
`MixedNuclearSourceCubicConservation`, `ModularCubicProjectionTransgression`,
`FormationAnchoredCubicHomotopyDefect`; current frontier map's shared Ward/boundary complex.
External parents: Avron–Seiler–Simon, JFA 120 (1994), 220–237, pair-index additivity under
compactness/Schatten assumptions; Coine–Le Merdy–Sukochev, arXiv:1706.01662, trace-class triple
operator integrals with Hilbert–Schmidt input factors. Neither premise is supplied by nuclearity
of this sum alone. Searches checked through 2026-09-05; no exhaustive priority claim.

## Derived statement to formalize — BRIDGE

Set `S=P+Q+R`, `K=[P,Q]+[Q,R]+[R,P]`. Projection algebra gives

`2 C = S K - K S`.

`S` is self-adjoint and `K` skew-adjoint. For aggregate eigenvectors `Sx=λx`, `Sy=μy`
with real eigenvalues,

`2 <x,Cy> = (λ-μ)<x,Ky>`.

Thus every same-eigenvalue compression of `C` vanishes. If `S` admits a complete orthonormal
eigenbasis and `C` is nuclear, its trace is zero, even without commuting projections or compact
individual displacements. Paper proof: expand the three cubes; the cyclic Jacobi identity cancels
the terms containing all three projections. Apply the adjoint identity to the left aggregate
factor and the eigenvector equation to the right factor. Finally sum the zero diagonal in an
orthonormal eigenbasis; only `C` needs trace-class admission.

This interprets the cubic as an inter-eigenvalue current, not diagonal mode occupation. It does
not prove trace cancellation on the remaining continuous spectral sector. A trace-class
commutator of bounded operators need not have zero trace: cyclicity cannot be used without its
actual ideal hypotheses. Finite matrices, finite block sums, and bounded unitary conjugation of
those models cannot settle that continuous-sector question.

## Novelty gate

BRIDGE: the identities above are algebra plus the standard basis trace formula. They are not the
significant beyond-literature result requested by the user. Keep the general question unchanged;
do not promote the discrete-sector theorem to an unconditional answer for all projections.

## Primary conjecture: a continuous cubic charge survives

**Exact target:** there exist three orthogonal projections on a separable complex Hilbert space
whose combined cubic associator is trace class and has trace `3√3/(2π)`. No individual cubic or
adjacent product is required to be trace class. Checked internal locks: the commuting and mixed
nuclear conservation theorems named above; corpus search also checked
`CCMArchimedeanRealTraceCocycle` and `ModularCubicProjectionTransgression`.

**Mechanism:** ordinary trace charge is not occupation of an aggregate eigenmode; it can instead
be the signed area swept by the joint continuous symbol of the aggregate and cyclic current.
This reconciles finite-block cancellation, cancellation under separate channel admission, and
survival of a trace-class commutator with non-trace-class factors. It is incompatible with the
conjecture that nuclearity of the combined cubic always forces trace zero.

**Candidate construction:** on the circle, take three rank-one matrix projection symbols with
Bloch vectors `(b cos φ_j, b sin φ_j, a)`, where `a²+b²=1`. Traverse `a:1→-1` with phases
`(0,2π/3,4π/3)`; return `a:-1→1` with reversed phases. Flatten the parametrization at the poles
so all three symbols are smooth. Their sum and cyclic current are diagonal:

`s = (3/2)I + (3a/2) Z`, `k = ± i(3√3/4)(1-a²) Z`.

Hence `[s,k]=0`, but `∮ tr(s dk)=6i√3`. Smooth Hardy Toeplitz compression followed by
trace-class projection correction would give genuine projections. If both steps preserve the
trace-class commutator charge, `2 Tr C = (2πi)⁻¹ ∮ tr(s dk)=3√3/π`.

**Formal open core:** instantiate the smooth projection-symbol loop on the corpus Hardy carrier,
round its three compressions, and transfer the exact trace. The paper argument below addresses
the projection-correction and trace-transfer hypotheses without splitting inadmissible products.
The circle trace formula is known mathematics, not a novelty claim. External audit has not found
this exact three-projection realization, but does not establish exhaustive priority.

**Verdict:** SURVIVES PRELIMINARY ATTACK; paper construction below, not yet a Lean theorem or an
RH source law. Falsification tests: an obstruction to smooth gluing, projection lifting, or trace
transfer; cancellation of the two orientations; or a known stronger theorem.

## Dependency-closed paper construction

Use normalized Hardy space `H²(T; C²)` and its compression `T_f` of multiplication by a smooth
matrix-valued circle function `f`. Write `tr` for the two-dimensional matrix trace, `Tr` for the
Hilbert-space trace, and `Z=diag(1,-1)`.

1. **Smooth loop.** Choose a smooth step `η:[0,1]→[0,1]`, constant near both endpoints, with
   values `η(0)=0`, `η(1)=1`. Set `θ=πη`, `a=cos θ`, `b=sin θ`. On the first half of a circle,
   take rank-one orthogonal projections

   `p_j = 1/2 [[1+a, b exp(-iφ_j)], [b exp(iφ_j), 1-a]]`,

   with `(φ_0,φ_1,φ_2)=(0,2π/3,4π/3)`. On the second half use the reversed parameter (so
   `a:-1→1`) and reversed phases. At each join all three projections are the same pole
   projection and are constant in a neighborhood. Therefore the three functions glue smoothly,
   not just continuously. The identity `a²+b²=1` proves `p_j²=p_j=p_j*`.

2. **Commuting aggregate symbols, nonzero integrated current.** Direct matrix multiplication
   gives

   `s=p_0+p_1+p_2=(3/2)I+(3a/2)Z`,
   `k=[p_0,p_1]+[p_1,p_2]+[p_2,p_0]=±i(3√3/4)(1-a²)Z`.

   Thus `[s,k]=0`. On the forward half `tr(s dk)=-i(9√3/2)a² da`, whose integral from
   `a=1` to `a=-1` is `3i√3`. On the return half both the phase orientation and direction of
   traversal reverse, so the integral is again `3i√3`. This uses the endpoint primitive
   `a³/3`, not monotonicity or a numerical integral. Consequently `∮tr(s dk)=6i√3`.

3. **The admitted Toeplitz trace.** For smooth matrix symbols, every defect
   `T_f T_g-T_(fg)` is trace class: it is the product of two Hilbert--Schmidt Hardy crossblocks.
   When `[f,g]=0`, the commutator is trace class and

   `Tr[T_f,T_g]=(2πi)⁻¹ ∮tr(f dg)`.

   To verify the normalization and hypotheses, its trace is the absolutely convergent series
   `Σ_(n≥1) n tr(f_(-n) g_n - g_(-n) f_n)`. Rapid Fourier decay justifies every rearrangement.
   Fourier integration of `tr(f dg)` gives precisely this series. The convention sends
   `[T_z,T_(z̄)]` to trace `-1`. Scalar versions and the Hankel product mechanism are standard;
   the matrix formula follows by a finite sum over entries.

4. **Genuine projection lifts.** Each `A_j=T_(p_j)` is a positive contraction and
   `D_j=A_j-A_j²` is positive trace class. The spectral projection
   `P_j=1_(1/2,1](A_j)` satisfies `P_j-A_j=r(A_j)D_j`, where

   `r(t)=-1/(1-t)` for `t≤1/2`, and `r(t)=1/t` for `t>1/2`.

   On `[0,1]` this is a bounded Borel function of norm at most `2`; hence the difference is
   trace class. A spectral value exactly `1/2` causes no gap in this argument. For a continuous
   functional-calculus formalization, instead choose any `b∈(0,1)` outside `spec(A_j)`;
   such a value exists because compactness of `A_j-A_j²` makes `spec(A_j)` countable.
   The two rational branches remain continuous on that spectrum and bounded there.

5. **Charge survives correction.** Set `S=P_0+P_1+P_2` and
   `K=[P_0,P_1]+[P_1,P_2]+[P_2,P_0]`. Then `S-T_s` and `K-T_k` are trace class, by step 3
   and the ideal property. Writing them as `E,F`, respectively, gives

   `[S,K]-[T_s,T_k]=[E,T_k]+[T_s,F]+[E,F]`.

   Each displayed commutator on the right has a trace-class factor and therefore trace zero.
   No cyclicity is applied to the separate products `T_s T_k` or `T_k T_s`. Thus `[S,K]`
   is trace class and has trace `3√3/π`.

6. **Exact cubic conclusion.** The algebraic identity already checked in Lean is `2C=[S,K]`.
   Therefore `C` is trace class and `Tr C=3√3/(2π)≠0`. In particular, combined trace-class
   admission cannot by itself imply cubic index additivity. This example cannot satisfy any of
   the corpus hypotheses that force zero trace: commuting source projections, nuclear adjacent
   product, or a complete aggregate eigenbasis.

**Positive significance, scoped:** a finite ordinary cubic charge can be an integrated orientation
of a continuous source family, despite vanishing of the pointwise cubic symbol. This distinguishes
total admission from separate-channel admission. Nothing here identifies that family with Xi,
preserves a particular prime-labelled source, or proves RH.

**External comparison:** [Avron's account of cubic index additivity](https://barrysimon.caltech.edu/documents/25866/barry_simonams_notices2016_08.pdf)
uses admitted pair traces; [Blower--Doust, IEOT 98 (2026), Proposition 3.13](https://link.springer.com/article/10.1007/s00020-025-02818-6)
supplies standard Toeplitz/Hankel curvature and trace-cocycle ancestry. Neither is credited here
as a newly discovered trace formula. The candidate novelty is the three-projection realization
under combined-only trace-class admission, not the parent operator theory.
