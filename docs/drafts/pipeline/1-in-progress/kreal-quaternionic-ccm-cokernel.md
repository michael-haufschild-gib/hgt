# A genuine \(K_{\mathbb R}\)-quaternionic lift of the CCM arithmetic \(H^1\)

- **ID:** `kreal-quaternionic-ccm-cokernel`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` with proved no-go boundary
- **Target:** construct Deninger's missing coefficient category and arithmetic \(H^1\) without
  inserting, duplicating, or assuming zeta zeros
- **Active claim:** one claim only - the genuine quaternionic lift below

## Claim ledger

- `[LITERATURE]` Connes--Consani--Marcolli define
  \[
    \mathcal H^1_{\mathrm{CCM}}(K)
      = \operatorname{coker}_{\overline{\mathrm{im}}}
        \left(
          \rho^\natural:
          \mathcal S(K^\times\ltimes\mathbb A_K)^\natural_0
          \longrightarrow
          \mathbf S^\natural(C_K,\mathcal L^1(\mathcal H_x))
        \right)
  \]
  in the abelian category of cyclic modules. Its derived cyclic realization carries the
  \(C_K\)-action and spectrally realizes zeros of Hecke \(L\)-functions.
- `[LITERATURE]` Deninger proves that the expected Artin-isotypic multiplicity formula cannot be
  the complexification of a functorial real-valued cohomology. He proposes instead the category
  \(K_{\mathbb R}\): a graded complex vector space with an anti-linear operator \(\sigma\) satisfying
  \(\sigma^2=(-1)^i\) in degree \(i\).
- `[LITERATURE]` Loday's quaternionic homology of an involutive algebra does not provide this
  missing sign over characteristic zero: when \(2\) is invertible,
  \(HQ_\ast(A)\cong HD_\ast(A)\), and the quaternion-group action attached to an ordinary
  involution factors through the dihedral quotient.
- `[LITERATURE]` Topological \(\Delta G\)-homology supplies a genuinely larger input:
  quaternionic THH accepts a twisted \(C_4\)-action
  \(t:R^{\mathrm{op}}\to R\), \(t^4\simeq 1\), and has a
  \(\operatorname{Pin}(2)\)-action. If \(t^2\simeq 1\), it collapses to inflated Real THH.
- `[CONJECTURE]` The CCM restriction morphism has a non-factorizing, conjugate-semilinear
  quaternionic lift whose central \(C_2\) acts by cohomological parity. This lift is the
  coefficient-theoretic arithmetic cohomology missing from the present Deninger program.
- `[OPEN CORE]` Construct the source-defined order-four anti-map and prove compatibility with
  \(\rho^\natural\). Positivity is deliberately not part of this claim.

## Exact conjecture

Let
\[
  A_K^\natural=\mathcal S(K^\times\ltimes\mathbb A_K)^\natural_0,\qquad
  B_K^\natural=\mathbf S^\natural(C_K,\mathcal L^1(\mathcal H_x)),
\]
and let \(\rho^\natural:A_K^\natural\to B_K^\natural\) be the CCM restriction morphism.

Write
\[
  Q_{4(n+1)}
   =\langle x_n,y_n\mid x_n^{n+1}=y_n^2,\;
      y_nx_ny_n^{-1}=x_n^{-1}\rangle
\]
and \(z_n=x_n^{n+1}=y_n^2\), the central element of order two.

> **Conjecture \(KQ_{\mathrm{CCM}}\).** There are conjugate-semilinear quaternionic derived
> cyclic objects \(\widetilde A_K,\widetilde B_K\) and a quaternionic morphism
> \(\widetilde\rho:\widetilde A_K\to\widetilde B_K\) such that:
>
> 1. forgetting quaternionic/Real structure identifies the realized cofiber of
>    \(\widetilde\rho\) with the single CCM realization \(H^\bullet_{\mathrm{CCM}}(K)\);
> 2. the odd generator \(y\) is anti-linear on the realized cohomology;
> 3. the central square \(z=y^2\) acts on \(H^i_{\mathrm{CCM}}(K)\) as
>    \((-1)^i\);
> 4. the lift is \(C_K\)-equivariant, so the infinitesimal scaling generator and its
>    spectral realization are unchanged;
> 5. the construction is functorial in finite extensions and compatible with Artin
>    isotypic decomposition.

Consequently the realized cohomology is \(K_{\mathbb R}\)-valued:
\[
  y^2=+1\quad\text{on }H^0,H^2,\qquad
  y^2=-1\quad\text{on }H^1.
\]
Condition 1 forbids a post-hoc quaternionic double and preserves zero multiplicities and the
existing trace formula.

## Why this is the correct first construction target

The prose object in `docs/Deninger program.md` requires four logically separate layers:

1. a cohomological carrier;
2. a scaling/Frobenius action with the zero spectrum;
3. the correct real/quaternionic coefficient category;
4. a positive polarization implying purity.

CCM supplies 1 and 2 as a relative cyclic construction. Deninger's 2023 theorem proves that
ordinary real coefficients cannot supply 3. The present conjecture targets exactly 3 and does
not relabel 4 as an axiom.

## Hostile attacks

### Attack A - ordinary involution

If the order-four anti-map factors through an involution, \(t^2=1\), then the central element
\(z\) acts trivially. Loday's characteristic-zero comparison gives \(HQ\simeq HD\), while the
topological comparison gives quaternionic THH as the pullback of Real THH along
\(\operatorname{Pin}(2)\to O(2)\). A nonzero \(H^1\) then cannot simultaneously have
\(y^2=1\) and \(y^2=-1\).

**Verdict:** `[DISPROVED AS TOO WEAK]`.

### Attack B - tensor with a quaternionic plane

Replacing \(H^1_{\mathrm{CCM}}\) by \(H^1_{\mathrm{CCM}}\otimes_\mathbb C\mathbb C^2\) produces
an anti-linear square \(-1\), but doubles every spectral multiplicity and squares the determinant.
It fails both the CCM trace formula and Deninger's Artin multiplicity requirement.

**Verdict:** `[DISPROVED AS UNFAITHFUL]`.

### Attack C - declare the central action to be the chain-degree sign

For a quaternionic module the face relations imply
\[
  d_i z_n=z_{n-1}d_i.
\]
Declaring \(z_n=(-1)^n\) on simplicial degree \(n\) would force every face map to be killed by
two. This is impossible over \(\mathbb C\). The parity sign must emerge on derived cohomology
from a genuine order-four extension, not from a degreewise sign convention.

**Verdict:** `[DISPROVED AS INCOHERENT]`.

### Attack D - inner square

If \(t^2\) is inner in the relevant derived cyclic category, it acts trivially on cyclic
homology. Such a lift again factors through the dihedral theory at the level that matters.

**Verdict:** `[DISPROVED AS HOMOLOGICALLY TRIVIAL]`.

### Attack E - metaplectic cover proves RH

The adelic metaplectic cocycle is globally split over the rational group by Weil reciprocity.
It may supply half-weight coefficient data, but its splitting is already part of the functional
equation and cannot supply the missing positive polarization.

**Verdict:** `[REDISCOVERED / STRUCTURAL ONLY]`.

### Attack F - hide positivity in the lift

Any requirement that the induced Weil form be positive is already RH-equivalent in the existing
CCM and Deninger formulations. Positivity cannot be included in the definition of the lift.

**Verdict:** `[CIRCULAR]`.

### Attack G - obtain the sign from an ungraded Fredholm phase

Let \(F=F^*=F^{-1}\) and put \(\kappa_F(T)=FT^*\).  If
\(FTF=(-1)^iT\), then
\[
  \kappa_F^2(T)=FTF=(-1)^iT.
\]
This initially looks like a source-defined construction of Deninger's sign.  Every commutator
\([F,a]\) is indeed odd under \(T\mapsto FTF\).  The argument fails for a general represented
quantized form
\[
  a_0[F,a_1]\cdots[F,a_n]:
\]
the coefficient \(a_0\) need not commute with \(F\), so the form need not have parity \(n\).
Thus an ungraded Fredholm module does not make the whole relative cyclic object
\(K_{\mathbb R}\)-valued.

**Verdict:** `[DISPROVED AS INSUFFICIENT]`.

### Attack H - add the standard even double

For an even Fredholm module with grading \(\gamma\), represented coefficients are even,
the phase \(F\) is odd, and every degree-\(n\) quantized form has
\(\gamma T\gamma=(-1)^nT\).  Hence
\[
  \kappa_\gamma(T)=\gamma T^*,\qquad
  \kappa_\gamma^2(T)=\gamma T\gamma=(-1)^nT.
\]
This is the exact algebraic \(K_{\mathbb R}\) sign.  However, CCM's target is the ungraded
field \(\mathcal L^1(\mathcal H_x)\).  Replacing every \(\mathcal H_x\) by the standard even
double \(\mathcal H_x\oplus\mathcal H_x\) merely reinstates Attack B unless a relative Chern
character proves that one intrinsic chiral sector, with its original trace, is exactly the
single CCM cokernel.

**Verdict:** `[CONDITIONAL SURVIVOR; SOURCE GRADING MISSING]`.

### Attack I - use the rational CCM Morita fiber, then take ordinary endomorphisms

For \(K=\mathbb Q\), CCM's canonical Morita fiber is
\(\mathcal H_b=\ell^2(\mathbb Q^\times)\).  It has the source-defined antiunitary
\[
  (\mathcal Jf)(q)=\operatorname{sgn}(q)\overline{f(-q)},\qquad
  \mathcal J^2=-1,
\]
with covariance
\[
  \mathcal JL_k=\operatorname{sgn}(k)L_k\mathcal J.
\]
This uses the existing pair \(q,-q\) and does not double the fiber.  However, its induced
anti-linear conjugation on kernels satisfies
\[
  \operatorname{Ad}_{\mathcal J}^2(T)
    =\mathcal J^2T\mathcal J^{-2}=T.
\]
Thus the central \(-1\) cancels when the Morita bimodule is paired with its dual to form
\(\mathcal L^1(\mathcal H_b)\), exactly before CCM applies ordinary cyclic trace.

**Verdict:** `[PROVED SOURCE CARRIER; ORDINARY MORITA TRACE TOO WEAK]`.

## Strongest positive survivor

`[NEW]` The exact coefficient boundary is:

> A viable arithmetic \(H^1\) must be a **non-factorizing twisted-\(C_4\) refinement** of the
> existing CCM cyclic cokernel. Its central square must be non-inner in the derived category
> and become the cohomological parity operator. Ordinary Real/dihedral refinements and external
> quaternionic doubling cannot work.

This survivor is stronger than the negative statement because it identifies the minimal new
datum: one compatible, non-inner order-four anti-map on the CCM restriction diagram.  The
operator calculation in Attack H gives an equivalent concrete target for such data: an intrinsic
even Fredholm-module grading and a no-doubling relative Chern equivalence.  Attack I sharpens the
rational case further: the quaternionic operator already exists on CCM's Morita bimodule, so the
open construction is an enhanced relative trace which retains one unpaired bimodule factor.

## Candidate construction lanes

### Lane 1 - half-Tate/genuine-metaplectic refinement

A half-Tate/genuine-metaplectic enhancement of the restriction diagram would:

1. retain the central \(\mu_2\) of the adelic Weil representation instead of passing immediately
   to the ordinary Fourier action;
2. form a genuine central-character sector at the level of the restriction correspondence, not
   by tensoring the final zero space;
3. prove that the Fourier/Poisson morphism lifts to an order-four anti-map on the relative cyclic
   object;
4. prove that its square is non-inner on relative \(H^1\), although the ordinary metaplectic
   cocycle globally splits;
5. verify that forgetting the genuine action returns the original CCM trace formula.

Steps 3 and 4 are an `[OPEN CORE]`. The prior spinor-half-Frobenius card proposed a metaplectic
square root abstractly; the present claim is strictly narrower and testable because it specifies
the CCM source, target, morphism, central element, parity law, and no-doubling condition.

### Lane 2 - graded quantized relative calculus

`[CONJECTURE]` There is a source-defined even Fredholm correspondence
\[
  (\pi_A,\pi_B,\gamma,F)
\]
over the CCM restriction diagram such that:

1. \(\gamma\pi_A(a)\gamma=\pi_A(a)\) and
   \(\gamma\pi_B(b)\gamma=\pi_B(b)\);
2. \(\gamma F\gamma=-F\);
3. the relative quantized Chern map is a \(C_K\)-equivariant quasi-isomorphism from its
   intrinsic chiral degree-one complex to the single CCM relative cyclic realization;
4. its trace agrees with the original CCM trace, without a factor of two.

Then \(\kappa_\gamma(T)=\gamma T^*\) gives the required anti-linear square \(-1\) on the
degree-one carrier before zeros are extracted.  Conditions 3 and 4 are the exact
`[OPEN CORE]`; without them this lane is only the forbidden standard double in new notation.

### Lane 3 - rational quaternionic relative trace with coefficients

For the zeta case, retain the sign-reflection quaternionic Morita bimodule
\[
  E_b=\ell^2(\mathbb Q^\times),\qquad
  (\mathcal Jf)(q)=\operatorname{sgn}(q)\overline{f(-q)}
\]
before replacing it by \(\operatorname{End}(E_b)\).  Kaledin's cyclic coefficients and
Real/quaternionic THH suggest the exact refinement:

`[CONJECTURE]` There is a quaternionic relative cyclic/THH object
\[
  \operatorname{RelTr}_{\mathcal J}(\rho)
\]
for the CCM restriction correspondence such that:

1. it contains one unpaired \(E_b\)-coefficient and its central square is \(-1\);
2. forgetting the coefficient action is quasi-isomorphic to the single CCM relative cyclic
   realization, not two copies;
3. the comparison intertwines the \(C_{\mathbb Q}\)-action and the CCM trace formula.

The source operator, its scaling covariance, its compatibility with CCM monomial supports, and
the endomorphism-erasure boundary are proved and formalized in
`CCMRationalQuaternionicMoritaFiber.lean`.  Existence and the no-doubling comparison in items
1--3 are the sharpened `[OPEN CORE]`.

## Lean interface audit

Existing reusable unconditional infrastructure:

- `RHTower.OmegaComplexStructure`: a real-linear \(J\) with \(J^2=-1\), even-rank consequences,
  polarization preservation, and skew-adjointness;
- `RHTower.SymplecticMultiplicity`: nondegenerate alternating forms force even generalized
  eigenspace dimension;
- `RHTower.SymplecticCyclicObstruction`: a nontrivial symplectic carrier cannot be cyclic;
- `RHTower.CliffordMultiplicity`: Clifford actions and exact multiplicity-divisibility walls;
- `RHTower.XiReciprocalCliffordSquare`: bare Clifford polarization is RH-equivalent and therefore
  only a consumer interface;
- `RHTower.WeightOneCliffordDirac`: source anticommutation exists, while Hilbert closure and
  determinant identification remain open;
- `HilbertMetric/*`: Gram, Fock, and metric infrastructure, but no arithmetic cyclic object or
  anti-linear \(K_{\mathbb R}\) coefficient structure.

No Lean file currently defines the CCM cyclic cokernel, a quaternionic cyclic object, a twisted
\(C_4\) anti-map, or Deninger's graded \(K_{\mathbb R}\) category. No Lean implementation begins
until the exact paper construction of \(\widetilde\rho\) is dependency-closed.

## Evidence and novelty audit

- Christopher Deninger, *There is no "Weil-"cohomology theory with real coefficients for
  arithmetic curves*, arXiv:2204.02714.
- Alain Connes, Caterina Consani, Matilde Marcolli, *The Weil proof and the geometry of the adeles
  class space*, arXiv:math/0703392.
- Jean-Louis Loday, *Homologies diedrale et quaternionique*, Adv. Math. 66 (1987), 119-148;
  also *Cyclic Homology*, §5.2.
- Gabriel Angelini-Knoll, Mona Merling, Maximilien Peroux, *Topological Delta G-homology of rings
  with twisted G-action*, arXiv:2409.18187.
- Emanuele Dotto, Kristian Moi, Irakli Patchkoria, Sune Precht Reeh,
  *Real topological Hochschild homology*, arXiv:1711.10226.

Searches for the exact conjunction
`Deninger K_R + CCM cyclic cokernel + quaternionic/Real THH` found no construction. This is
evidence of novelty, not proof of novelty.

## Gates

- [x] Internal corpus audited, including failed routes and requested Lean trees.
- [x] External state of art audited before conjecturing.
- [x] Conjecture stated with exact source, target, central element, and no-doubling test.
- [x] Ordinary-involution, external-double, chain-sign, inner-square, metaplectic-circularity,
      and positivity-circularity attacks recorded.
- [ ] Construct the non-factorizing twisted-\(C_4\) lift on paper.
- [ ] Prove compatibility with \(\rho^\natural\).
- [ ] Prove derived parity and no-doubling.
- [ ] Re-run exact novelty search after proof.
- [ ] Move to `2-fully-proven`.
- [ ] Formalize the exact proved theorem in Lean.

## Log

- 2026-07-25 - Created after audit of Deninger 2023, CCM 2007, Loday quaternionic homology,
  Real/quaternionic THH, existing metaplectic moonshot, and the three requested Lean trees.
  No numerical evidence and no Lean build used.
