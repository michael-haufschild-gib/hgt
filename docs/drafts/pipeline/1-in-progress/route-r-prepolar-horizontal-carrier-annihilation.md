# Route R pre-polar horizontal-carrier annihilation

- **ID:** `route-r-prepolar-horizontal-carrier-annihilation`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE / SOURCE PRODUCER
- **Route:** R
- **Scientific status:** `[OPEN CORE] [NOT RH PROOF]`
- **Statement:** Derive `BurnolXiCartierDividedShiftHeadFluxDissipativity` from a literal
  pre-divisor Euler--Gamma--Stokes law acting before polar completion, without importing an
  RH-equivalent annihilation, sewing, norm, or critical-line premise.

## Exact frontier

`SourceZeroHorizontalCarrier.lean` constructs and orients the multiplicity-exact, prime-labelled,
reflection-odd horizontal carrier and proves that its global vanishing is equivalent to RH.
`BurnolBocksteinLimit.lean` proves the Bockstein limit, forward/reflected residue landing, fixed
head-flux landing, and same-fibre Stokes transgression. These are closed receivers.

For every hypothetical right-half Xi divisor, Lean proves the landed current is strictly positive.
Consequently the desired nonpositive current cannot be obtained from post-landing positivity or
from an identity that already factors through critical-line placement. A valid producer must
independently make the hypothetical right-half source configuration inadmissible.

## Open claim

Construct a source-defined, pre-polar operation or pairing `A` on the two retained ordered cofinal
orientations such that:

1. `A` is defined from Euler, Gamma, rational-adelic/Stokes source data before Xi scalarization;
2. `A` retains prime, depth, divisor, multiplicity, and reflection provenance;
3. source exactness/positivity forces the fixed Burnol two-head defect to be nonpositive;
4. comparison with the already-formalized Bockstein/Stokes landing yields
   `BurnolXiCartierDividedShiftHeadFluxDissipativity`;
5. construction does not use RH, `Re rho = 1/2`, source-horizontal vanishing, source-dagger or
   same-fibre norm identity, forward/reflected sewing, or an equivalent endpoint predicate.

## Hostile falsifiers

- Completed-collar moment zero is insufficient: its kernel differs from Bockstein kernel and acts
  after the residue has been erased.
- Common determinant correction preserves the Bockstein zero radical and cannot create it.
- Fourier/reflection-invariant scalar readers erase the required odd orientation.
- Any claimed inequality obtained only after substituting an actual Xi divisor must be audited for
  equivalence to RH rather than accepted as source derivation.

## Gates

- [x] 0 → 1: exact source-pure question and circularity exclusions isolated
- [ ] conjecture survives internal and external audit
- [ ] complete dependency-closed paper proof
- [ ] Lean formalization
- [ ] RH

## Conjecture / proof-or-failure ledger

Active loop begins from the constructed horizontal carrier and the exact Burnol Bockstein/Stokes
landing. Each failed conjecture must record its killing mechanism and a stronger replacement.

## Log

- 2026-08-09 — reoriented after carrier construction and full Bockstein/Stokes formalization;
  independent pre-polar annihilation isolated as sole Route-R source producer.

## Heavy-loop ledger — 2026-08-09

### C1. Separate Stokes zero-moment laws

**Conjecture.** Forward and reflected orientations have independent zero-moment Stokes laws whose
difference forces the fixed two-head current to be nonpositive.

**Failure.** A prescribed forward head and a prescribed reflected head can each be cancelled by an
independent tail. Separate scalar exactness therefore imposes no comparison between the two head
norms. The missing statement is intrinsically cross-orientation.

**Pivot.** Couple the orientations before either scalar landing.

### C2. Kernel-only positive factorization

**Conjecture.** The Bockstein kernel is a completed Stokes boundary minus a positive square, making
its retained current nonpositive.

**Failure.** The completed collar has half-rate moment zero, whereas the Bockstein kernel has
half-rate moment `1/2`. Such a factorization would give a nonpositive half-rate moment on the right,
contradicting the exact positive moment on the left.

**Pivot.** Any valid annihilator must use the arithmetic source correlation, not only the universal
Gamma--Stein kernel.

### C3. Positive all-prime diagonal cancellation

For the prime window `[1/p,1]`, the two retained head sizes are `p-1` and `log p`. If
`1/2 < Re rho < 1`, then `|rho| > |1-rho|`, and for every prime `p`, `p-1 > log p`. Hence

```text
(p-1)^2 / |1-rho|^2 - (log p)^2 / |rho|^2 > 0.
```

**Failure.** Every nonzero nonnegative diagonal combination of ordinary-prime channels is strictly
positive at a hypothetical right-half point. Adding primes cannot cancel the dyadic defect.

**Pivot.** A surviving producer must be signed and off-diagonal, or a singular domain-admission
law; positive prime-diagonal energy is excluded.

### C4. Completion-current budget

**Conjecture.** Strict negativity of the completed Euler--Gamma current, together with negativity
of its completion-normal component, descends to nonpositivity of the bare Burnol head current.

**Failure.** The completed current is `A + J`. From `A+J<0` and `A<0`, no sign of `J` follows.
Indeed the already-proved right-half calculation gives `J>0` while the dressed current remains
negative. Completion hides the positive pre-polar channel instead of annihilating it.

**Pivot.** Work before polar completion and do not subtract two unrelated negative currents.

### C5. Source-blind regular Euler--Gamma operator

Let `phi(u)=exp(-u/2)` be the stable residue profile and `A = d/du + 1/2`, so `A phi=0`.
Let `tau_L` be translation by `L`; then `tau_L phi=exp(-L/2) phi`. Every finite operator
`Q(A,tau_L)` in the commuting regular Gamma--Stein/translation algebra therefore restricts on the
stable residue line to the scalar

```text
q = Q(0, exp(-L/2)).
```

If `q=0`, the operator kills the entire stable residue line and therefore erases every coefficient,
including the constructed carrier. If `q != 0`, it is coefficient-faithful but cannot annihilate a
nonzero carrier coefficient.

**Classification.** No source-independent finite regular Euler--Gamma Stein/dilation operator can
both retain and annihilate the constructed horizontal carrier.

**Pivot.** Remaining candidates are source-dependent cross-orientation pairings and singular,
unbounded domain-admission laws. Regular scalar functional calculus is closed.

### C6. Residue-Gram positivity

For arbitrary two-head coefficients `a,b`, put `B=(b-a)/2`. The two exterior residues are
`r=-a*conj(B)` and `rDual=b*conj(B)`. Directly,

```text
r + rDual = |a-b|^2 / 2 >= 0,
2 Re(r-rDual) = |a|^2 - |b|^2.
```

**Failure.** The positive Gram channel is the orientation-even sum. The desired current is the
orientation-odd difference and has no sign for arbitrary heads. Positivity of the residue Gram
matrix cannot orient it.

**Pivot.** A valid law must link the odd channel to a source boundary before endpoint evaluation;
endpoint positivity alone is structurally blind to the sign.

## Surviving producer class

After C1--C6, a valid independent producer must simultaneously be:

1. pre-polar and source-dependent;
2. cross-orientation and signed/off-diagonal;
3. coefficient-faithful on the stable residue line;
4. singular or domain-sensitive rather than finite regular Gamma--Stein functional calculus;
5. derived without assuming the Xi landing/sewing equality whose consequence is sought.

The concrete surviving realization already visible in the corpus is all-prime singular unsewing:
the sewn rational-adelic conormal is unconditionally square-summable, while membership in the
domain of the fixed inverse-completion operator is exactly the missing source admission. The next
conjecture must derive that domain admission from a pre-divisor source topology or Cartier boundary,
not restate it at Xi divisors.

## Same-carrier heavy loop -- 2026-08-09

### C7. Identify the two cyclic faces on the retained atom

**Conjecture.** The two ordinary cyclic faces have the same source trace, so the analytic dagger
must transport the retained coefficient through the same face.

**Failure.** The source face pair is diagonal `(c,c)`, while the analytic paracyclic face pair is
`(c, delta*c)`. Identifying these pairs is equivalent to `(delta-1)c=0`; coefficient faithfulness
then makes this the critical-line conclusion. Cyclicity does not identify the analytic dagger.

### C8. Symmetrize the ordinary-prime atom into a Hochschild cycle

**Conjecture.** Adding the cyclic rotation removes the ordinary Hochschild boundary and makes the
two transports chain-equal.

**Failure.** Symmetrization can close the source chain, but the physical landing is not known to be
a chain map for the analytic dagger. Adding that naturality square is the same missing equality.

### C9. Use prime--infinity product-formula cancellation

**Conjecture.** The adelic product formula identifies forward and reflected scale transports on one
source carrier.

**Failure.** The product formula gives reciprocal compatibility `alpha*beta=1` for every grade.
Physical annihilation needs `alpha=beta`. The two conditions meet only after the desired neutral
grade has already been supplied.

### C10. Compare multiplicative source clock and additive analytic response

**Conjecture.** The raw source clock law has a quadratic correction absent from the analytic
response, forcing the response to be neutral.

**Failure.** The logarithmic coordinate linearizes the multiplicative formal group exactly at
every grade. The raw correction is a coordinate artifact, not a source anomaly.

### C11. Transport the positive-shell conormal through finite ramified ambidexterity

**Conjecture.** The source Koszul conormal and finite ramified top-conormal adjunction canonically
identify the two physical Gamma transports.

**Failure.** Both conormals exist before the Xi divisor, but the strict coefficient-faithful map
from ramified power conormal to the singular physical Gamma dagger is absent. Finite
ambidexterity alone does not survive the all-prime singular landing.

### C12. Fisher-deconvolved fixed carrier

**Conjecture.** Move the universal Euler--Fisher density into the source topology instead of
inverting it after passage to the ordinary `ell^1` quotient. The remaining forward and reflected
half-character transports should then act coefficient-faithfully on one fixed carrier in opposite
horizontal chambers.

**Verdict.** `[PAPER-PROVED] [BRIDGE] [NOT RH PROOF]`.

Let `S = C^P`, where `P` is the set of ordinary primes, let

```text
d(p) = p/(p+1)^2,
I_d = {x in S : p |-> d(p)x(p) is summable},
Q_d = S/I_d.
```

This carrier is fixed before any spectral parameter. For a real centered grade `t`, define the
normalized forward and reflected transports

```text
u_t(p) = 1 + p^(-t),
u_t^vee(p) = u_(-t)(p) = 1 + p^t.
```

Every coefficient is strictly positive. The exact same-carrier theorem is

```text
M_(u_t) descends to a coefficient-faithful automorphism of Q_d  iff  0 <= t,
M_(u_t^vee) descends to a coefficient-faithful automorphism of Q_d  iff  t <= 0,
both descend on Q_d                                      iff  t = 0.
```

At `t=0` both transports are literally the same scalar multiplier `2`, not merely conjugate under
reflection.

#### Paper proof

For any prime sequence `m`, diagonal multiplication by `m` preserves `I_d` exactly when `m` is
bounded. If `m` is bounded, multiplication by `m` preserves summability and commutes with
multiplication by `d`. Conversely, suppose it preserves `I_d`. Given an arbitrary summable
sequence `y`, define `x(p)=y(p)/d(p)`. Positivity of `d(p)` gives `d*x=y`, hence `x in I_d`; the
preservation hypothesis gives `m*y=d*(m*x)` summable. Thus `m` preserves every `ell^1` sequence,
and the already-formalized diagonal multiplier theorem forces `m` bounded.

If `t>=0`, then `0<p^(-t)<=1`, so `1<=u_t(p)<=2`. Therefore both `u_t` and `u_t^-1` are bounded;
their descended maps are inverse automorphisms. If `t<0`, put `a=-t>0`. Ordinary primes tend to
infinity, so `p^a` and hence `u_t(p)=1+p^a` are unbounded. This proves the first equivalence. The
second follows after replacing `t` by `-t`; conjunction gives `t=0`. At zero both formulas reduce
pointwise to `2`.

The original comparison coefficient satisfies

```text
r_t(p) = d(p)u_t(p),
b_t(p) = -d(p)u_t(p)(p^t-1).
```

Thus the construction preserves the literal prime coefficient and divisor multiplicity scalar;
it changes only where the universal Fisher damping is stored. On `S/ell^1`, `M_(r_t)` is
surjective but noninjective and its reciprocal does not descend. On `Q_d`, the normalized
transport is an automorphism exactly in its oriented half-space. This is the required
coefficient-faithful, non-equivariant same-carrier classification.

#### Hostile audit and exact remaining producer

This theorem holds for every real `t` and uses no Xi zero, line placement, or vanishing premise.
It does **not** show that an actual Xi divisor supplies both quotient actions. Source involution
only moves an orientation-dependent carrier to its reflected carrier; it does not prove that both
normalized analytic actions preserve this fixed `I_d` carrier. Claiming simultaneous descent at
every Xi divisor would be equivalent to RH by the theorem above.

The remaining source law is therefore narrower and literal:

`[OPEN CORE] FISHER_DECONVOLVED_TWO_ORIENTATION_SOURCE_DESCENT` -- construct, from the
pre-divisor rational-adelic/Cartier source and before Xi scalarization, both normalized operations
on `Q_d`; prove their representative actions are `u_t` and `u_-t` while retaining prime labels,
divisor multiplicity, and the two reflection orientations. Equivariance, product formula, or an
orientation-dependent norm is insufficient.

### C13. Put both normalized coefficient fields in the carrier before asking for endomorphisms

**Conjecture.** The C12 endomorphism formulation asks too much: each orientation need not preserve
`I_d` separately in order for both coefficient fields to be compared inside `Q_d`. Define

```text
U_t = [p |-> 1 + p^(-t)] in Q_d,
U_t^vee = U_(-t) = [p |-> 1 + p^t] in Q_d.
```

Both classes exist unconditionally for every real `t` in the same fixed carrier. Their difference
is not an abstract comparison:

```text
d(p) * (U_t(p) - U_t^vee(p)) = b_t(p)
```

prime by prime, where `b_t` is the literal signed Gamma Bockstein.

**Verdict.** `[LEAN-PROVED] [BRIDGE] [NOT RH PROOF]`.

Because membership in `I_d` is summability after multiplication by `d`, equality in `Q_d` gives

```text
U_t = U_t^vee
  iff p |-> b_t(p) is absolutely summable
  iff t = 0.
```

The last equivalence is the already proved sharp all-prime Gamma-Bockstein trace wall. This is
strictly stronger than C12 as a representation result: both transports are now present on one
fixed carrier for every grade, and their coefficient-wise difference is identified without
inverting Fisher density in the ordinary quotient. Prime labels are never summed; a later nonzero
Xi leading-jet scalar may be attached without changing the equality radical, so divisor
multiplicity is retained.

Lean module:
`formal/GaloisForLFunctions/RHTower/FisherDeconvolvedSameCarrierOrientationLaw.lean`.
Principal theorem: `fisherDeconvolvedOrientationClass_eq_reflected_iff`.

**Exact remaining source producer.** C13 removes carrier and coefficient-identification gaps. The
only missing statement is now a non-equivariant pre-divisor relation proving `U_t=U_t^vee` for the
two analytic transports attached to each actual Xi divisor. Source involution gives
`U_t at rho` corresponding to `U_-t at J(rho)`; it does not identify them in one fixed fibre.
Any theorem making that final identification globally is RH-equivalent by C13 and must be derived
from new rational-adelic/Cartier boundary input, not asserted as naturality.

## Formalization extraction -- 2026-08-11

### C14. Ordinary-prime diagonal cone

The C3 pointwise sign is now `[LEAN-PROVED]`, including closure under every nonempty finite positive
prime-diagonal combination. Module:
`RHTower/BurnolPrimeWindowDiagonalHeadFluxNoGo.lean`. Stage-3 card:
`3-formalized/new_scientific_knowledge/burnol-prime-window-diagonal-head-flux-no-go.md`.

This closes the whole finite positive diagonal cone, not only the dyadic channel. It does not
annihilate the carrier; it proves that this producer class has the wrong strict sign.

### C15. Finite regular Gamma--Stein/translation algebra

The C5 classification is now `[LEAN-PROVED]`. A free finite expression syntax retains scalar
leaves, the Stein generator, arbitrary translations, addition, and noncommutative composition.
Every expression restricts to its recursively computed scalar gain on the stable residue line.
Annihilation is equivalent to zero gain and coefficient faithfulness to nonzero gain, so both are
incompatible. Module:
`RHTower/BurnolStableResidueRegularOperatorClassification.lean`. Stage-3 card:
`3-formalized/new_scientific_knowledge/burnol-stable-residue-regular-operator-classification.md`.

### C16. Functional-equation partner current

The reflection partner `rho^dagger=1-conj(rho)` exchanges the two reciprocal heads. The exact odd
current is

```text
(1+(log 2)^2)(2 Re rho-1)/(|rho|^2 |1-rho|^2),
```

while the bare pair sum is strictly positive. Completion cancels from the odd coordinate because
the partner preserves imaginary part. Therefore bare or dressed scalar partner equality on all Xi
divisors is exactly RH, not an independent functional-equation law. This is `[LEAN-PROVED]` in
`RHTower/RouteRBurnolReflectionPartnerCurrent.lean`; stage-3 card:
`3-formalized/new_scientific_knowledge/route-r-burnol-reflection-partner-current-classification.md`.

**Open core unchanged.** C14--C16 close three false producer classes and make their exact positive
survivors reusable. They do not supply the missing non-equivariant, singular pre-divisor
rational-adelic/Cartier relation identifying the two fixed-carrier orientations. The parent card
therefore remains stage 1.

### C17. Complete coefficient-module singular annihilation

**Conjecture.** A topology-changing or ideal-valued singular boundary may kill the cofinal
prime-log essential cap while retaining a nontrivial complete prime output.

**Verdict.** `[PAPER-PROVED NO-GO] [NOT RH PROOF]`.

Let `P` be the ordinary primes, let `A = ell-infinity(P,C)`, and let `M` be an `A`-module with a
distinguished complete-output vector `e`.  Identify a coefficient profile `g` with `g*e`.  For a
fixed Xi-divisor fibre `rho`, write

```text
S_rho = 2 * a_rho * c_rho,
a_rho = 2 Re(rho) - 1,
c_rho = first nonzero Xi Cartier jet at rho,
f_rho(p) = a_rho * (1-p^-1) * (2-p^-1) * c_rho.
```

The established essential-cap calculation gives `f_rho(p) -> S_rho`.  If `a_rho != 0`, then
`S_rho != 0`, because `c_rho != 0`.  More strongly, `f_rho` is a unit of `A`: every local factor
`(1-p^-1)(2-p^-1)` is positive, it converges to `2`, and its explicit inverse

```text
p |-> 1 / ((1-p^-1)(2-p^-1))
```

is bounded.  Multiplication by the nonzero scalar `(a_rho*c_rho)^-1` then gives the inverse of
`f_rho`.

Consequently, if `N` is any `A`-submodule of `M`, then

```text
f_rho*e in N  ==>  e in N  ==>  A*e subset N.
```

In particular, for `M=A`, every ideal containing `f_rho` is the unit ideal and the quotient is
zero.  More generally, after quotienting `M` by an `A`-submodule, annihilation of `f_rho*e` is
equivalent to annihilation of the distinguished cyclic vector `e`; in an algebra quotient the
image of `f_rho` is either invertible or the quotient has already killed its unit.

For a closed linear relation retaining all prime-coordinate idempotents, the same argument puts
every finite-coordinate output in the vertical fibre.  In the ordinary countable product
topology those outputs are dense; closedness therefore gives the full vertical fibre and

```text
R = dom(R) x C^N.
```

Thus an ideal, Calkin-style module quotient, or product-topology module boundary cannot both
annihilate the off-center cap and retain any output constraint.  This strengthens the earlier
`c0` hostile test: no choice of proper coefficient ideal works, because the actual cap profile is
already an invertible multiplier before taking an essential quotient.

**Exact survivor.** A still-viable producer must abandon at least one of:

1. module compatibility with the complete bounded prime coefficient algebra;
2. complete finite-coordinate retention;
3. ordinary product-topology closedness.

The first abandons coefficient-faithful rational-adelic transport, the second erases provenance,
and the third requires a genuinely infinite-prime strict topology.  Hence the only unclassified
Route-R producer is now a strict-topology, non-module constitutive selector constructed before
Xi scalarization.  Merely quotienting by a larger ideal or declaring the essential tail a
boundary is dependency-closed dead.

## C18. Fixed same-fibre positive polarizations are universally amplifying

The unweighted two-head energy is not special.  Let

\[
  L=\log 2,\qquad
  g_\rho={\overline\rho\over 1-\rho},\qquad
  g_\rho^\vee={1-\overline\rho\over\rho}={1\over\overline{g_\rho}}.
\]

The fixed source head vector is, up to a common sign, \(v_0=(1,L)\), and Cartier transfer sends it
to

\[
  v_\rho=(g_\rho,Lg_\rho^\vee).
\]

Consider any fixed positive-definite Hermitian form on the two physical heads which is invariant
under exchange of the two Gamma orientations.  Its matrix has equal diagonal entries,

\[
  M=\begin{pmatrix}A&C\\ \overline C&A\end{pmatrix},
  \qquad A>0,
\]

with the usual additional determinant inequality on \(C\).  This class includes the inverse-Gram
polarization of the two actual head Riesz vectors: cosine unitarity makes those vectors have equal
norm, so both their Gram matrix and its inverse have equal diagonals.

Put \(r_\rho=|g_\rho|^2=|\rho|^2/|1-\rho|^2\).  The mixed term of the Hermitian form is unchanged by
Cartier transfer, because

\[
  \overline{g_\rho}\,g_\rho^\vee=1.
\]

Consequently the full polarization defect is independent of \(C\):

\[
\begin{aligned}
  \langle v_\rho,Mv_\rho\rangle-
  \langle v_0,Mv_0\rangle
   &=A\bigl[(r_\rho-1)+L^2(r_\rho^{-1}-1)\bigr]\\
   &=A(r_\rho-1)\left(1-{L^2\over r_\rho}\right).
\end{aligned}
\tag{C18.1}
\]

If \(1/2<\Re\rho<1\), then \(r_\rho>1\), while \(0<L^2<1\).  Both factors on the last line of
\((\mathrm{C18.1})\) are therefore strictly positive.  Thus

\[
  \boxed{
  \langle v_0,Mv_0\rangle<\langle v_\rho,Mv_\rho\rangle
  }
\]

for every fixed orientation-symmetric positive Hermitian polarization, not merely for the
unweighted sum already formalized in `BurnolCartierZeroTransferHeadPolarization.lean`.

This kills the apparent inverse-Gram escape.  Nonorthogonality of the two head reporters cannot
repair the sign: the entire off-diagonal Gram correction is exactly conserved, while the equal
diagonal part is strictly amplified.  A positive same-fibre producer would have to abandon at
least one of:

1. fixedness before seeing the divisor;
2. Fourier/Gamma-orientation symmetry;
3. positive-definite Hermitian geometry on the physical two-head quotient.

A divisor-dependent metric can of course be tuned to the required sign, but then its construction
is itself the missing horizontal-divisor information and is not a pre-divisor producer.

## C19. FE pairing converts the Route-R defect into an archimedean Hodge square

Let \(\iota\rho=1-\overline\rho\).  Then

\[
  g_{\iota\rho}=g_\rho^{-1},\qquad
  r_{\iota\rho}=r_\rho^{-1}.
\]

Adding the two defects from \((\mathrm{C18.1})\) gives

\[
\begin{aligned}
  \Delta_M(\rho)+\Delta_M(\iota\rho)
    &=A(1+L^2)(r_\rho+r_\rho^{-1}-2)\\
    &=A(1+L^2){(|\rho|^2-|1-\rho|^2)^2
         \over |\rho|^2|1-\rho|^2}\\
    &=4A(1+L^2){(\Re\rho-1/2)^2
         \over |\rho|^2|1-\rho|^2}.
\end{aligned}
\tag{C19.1}
\]

This is nonnegative and has exact radical \(\Re\rho=1/2\).  Functional-equation pairing therefore
does not cancel the Route-R head defect.  It squares it into the same reflection-even horizontal
mass geometry isolated by `GaussHodgeMassCurrent.lean` and
`GaussHodgeSeamEnergyBridge.lean`.

The consequence for producer design is sharp.  Operator-level Poisson reflection or a source
dagger which merely exchanges the two Gamma orientations preserves the positive square
\((\mathrm{C19.1})\).
It cannot annihilate it.  To close Route R through this interface one needs an additional global
index/supertrace identity, sourced from arithmetic self-duality before scalarization, whose value
is zero while its positive ordinary trace is \((\mathrm{C19.1})\).  That is exactly the global
compressed-trace/Hodge gate; it is not a local head-metric comparison.

**Status:** paper proof complete; not yet formalized because the Lean corpus is under refactor.
The identities are elementary but scientifically useful: they close the whole fixed,
orientation-symmetric, positive same-fibre polarization class and fuse Route R's local head defect
with the global Hodge-mass socket without assuming RH or critical-line placement.

## C20. Classification of Cartier-conserved same-fibre Hermitian forms

The preceding computation gives a complete conservation theorem, not only an amplification
theorem.  Let

\[
  H=\begin{pmatrix}A&C\\ \overline C&B\end{pmatrix}
\]

be an arbitrary fixed Hermitian form and let

\[
  T_\rho=\operatorname{diag}(g_\rho,g_\rho^\vee),
  \qquad g_\rho^\vee=1/\overline{g_\rho}.
\]

Then

\[
  T_\rho^*HT_\rho-H=
  \begin{pmatrix}
    A(r_\rho-1)&0\\
    0&B(r_\rho^{-1}-1)
  \end{pmatrix}.
\tag{C20.1}
\]

The off-diagonal entry cancels exactly; no positivity or divisor hypothesis is used.  At any
off-line point, \(r_\rho\ne1\), so

\[
  T_\rho^*HT_\rho=H
  \quad\Longleftrightarrow\quad
  A=B=0.
\tag{C20.2}
\]

Thus every nonzero Cartier-conserved same-fibre Hermitian form is purely off-diagonal,

\[
  H_C=\begin{pmatrix}0&C\\ \overline C&0\end{pmatrix}.
\]

For \(C\ne0\), its eigenvalues are \(\pm|C|\), hence it has signature \((1,1)\).  In particular:

* no nonzero positive-semidefinite same-fibre Hermitian form is conserved at an off-line point;
* the pre-polar, sign-indefinite off-diagonal source form is not one candidate among many: it is
  the complete invariant family;
* its value on the physical vector is conserved and horizontal-blind,
  \(langle T_\rho v_0,H_C T_\rho v_0\rangle
    =\langle v_0,H_Cv_0\rangle=2L\Re C\);
* adding any positive diagonal polarization necessarily breaks conservation by the explicit
  diagonal cocycle in \((\mathrm{C20.1})\), whose FE-paired value is the Hodge square
  \((\mathrm{C19.1})\).

This is the exact source-dagger verdict.  The dagger supplies unconditional Hermiticity only for
the split off-diagonal form.  It cannot yield a positive same-fibre norm identity without already
annihilating the horizontal cocycle.  Therefore a `SourceDaggerIdentity` or
`SameFiberNormIdentity` based solely on fixed Cartier covariance has no unclassified metric
freedom left: its positive version is precisely the RH-strength step, while its unconditional
version is indefinite and blind.

**Status:** paper proof complete; Lean formalization deferred during corpus refactor.  The future
formal module should state the matrix identity \((\mathrm{C20.1})\), the off-line invariance
classification \((\mathrm{C20.2})\), signature of \(H_C\), and the positive-polarization cocycle
as a bridge to `GaussHodgeMassCurrent`.

## C21. Projective Stokes flatness is blind to the Cartier boost

The invariant form in C20 puts the two-head transport in canonical Krein coordinates.  Write

\[
  g_\rho=e^{\eta_\rho+i\phi_\rho},
  \qquad
  T_\rho=e^{i\phi_\rho}
    \begin{pmatrix}e^{\eta_\rho}&0\\0&e^{-\eta_\rho}\end{pmatrix},
  \qquad
  S=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

Here \(S\) exchanges the two Gamma orientations and

\[
  \eta_\rho=\log|g_\rho|
  ={1\over2}\log{|\rho|^2\over|1-\rho|^2}.
\]

The unconditional source-dagger relation is

\[
  S T_\rho S=e^{2i\phi_\rho}T_\rho^{-1}.
\tag{C21.1}
\]

Therefore the closed reflection/Cartier loop is already projectively flat for every horizontal
grade:

\[
  T_\rho S T_\rho S=e^{2i\phi_\rho}I.
\tag{C21.2}
\]

Neither \((\mathrm{C21.1})\) nor \((\mathrm{C21.2})\) forces \(\eta_\rho=0\).  They are satisfied by
the full one-parameter family of nontrivial boosts.  This gives an explicit two-dimensional
countermodel to any proposed annihilation derived only from dagger reversal, determinant
holonomy, projective monodromy, or ordinary Stokes flatness.

The horizontal obstruction is the failure of centrality, not the closed-loop holonomy:

\[
  [T_\rho,S]=
  \begin{pmatrix}
    0&g_\rho-g_\rho^\vee\\
    g_\rho^\vee-g_\rho&0
  \end{pmatrix},
\]

and

\[
\begin{aligned}
  {1\over2}\|[T_\rho,S]\|_{\mathrm{HS}}^2
    &=|g_\rho-g_\rho^\vee|^2\\
    &=r_\rho+r_\rho^{-1}-2\\
    &={4(\Re\rho-1/2)^2\over|\rho|^2|1-\rho|^2}.
\end{aligned}
\tag{C21.3}
\]

Combining C19 and C21 gives the exact commutator-energy form of the FE-paired physical defect:

\[
  \Delta_M(\rho)+\Delta_M(\iota\rho)
   ={A(1+L^2)\over2}\|[T_\rho,S]\|_{\mathrm{HS}}^2.
\tag{C21.4}
\]

Thus the quadratic anomaly is precisely what abelian/projective flatness forgets.  A viable
pre-divisor producer must prove a genuinely nonabelian statement whose physical consequence is

\[
  [T_\rho,S]=0,
\]

or an index/trace identity forcing the nonnegative quantity in \((\mathrm{C21.4})\) to vanish.
But the ordinary rational-adelic Fourier--dilation relation supplies only \(STS=T^{-1}\), which
the boost countermodel already satisfies.  Any proof using only that relation is
dependency-closed dead.

**Strongest positive survivor.**  Route R's missing producer is now typed as a nonabelian
centrality theorem, not a flatness theorem: arithmetic self-duality must kill the commutator
energy while retaining the prime-dilation class.  This is exactly where a global
compressed-trace/index construction could add information unavailable to the local
Fourier--dilation algebra.

**Status:** paper proof complete; Lean formalization deferred during refactor.

## C22. The Cartier commutator energy is a causal Hodge--Green resolvent with unit source

The new adiabatic Euler--Gamma--Möbius chain makes it tempting to try to kill the positive
commutator energy in C21 by ordinary Green--Stokes descent.  The exact transform below shows why
that cannot work, and identifies the one boundary term a viable arithmetic producer must cancel.

Write

\[
  \rho=x+iy,\qquad t=2x-1,\qquad 0<x<1,
\]

and put

\[
  \mathcal H_t(u)
    =hodgeMassShape(e^{u/2},t)
    =t\bigl(e^{tu/2}-e^{-tu/2}\bigr).
\]

For \(y\ne0\), define the causal sine--Laplace kernel

\[
  k_y(u)=e^{-u/2}{\sin(yu)\over y},\qquad u\ge0,
\]

and set \(k_0(u)=u e^{-u/2}\), its continuous \(y\to0\) limit.  Direct Laplace evaluation gives

\[
\begin{aligned}
 \int_0^\infty k_y(u)\mathcal H_t(u)\,du
 &=t\left(
   {1\over ((1-t)/2)^2+y^2}
   -{1\over ((1+t)/2)^2+y^2}\right)\\
 &= {t^2\over (x^2+y^2)((1-x)^2+y^2)}\\
 &= {1\over2}\|[T_\rho,S]\|_{\mathrm{HS}}^2.
\end{aligned}
\tag{C22.1}
\]

The integral is absolutely convergent because \(|t|<1\).  The same formula at \(y=0\) follows by
the elementary Laplace moment integral or by dominated passage on compact \(t\)-subintervals.
Thus the local Route-R Cartier obstruction and the global Gauss Hodge obstruction are not merely
comparable: the former is the exact causal Green reading of the latter.

This transform has a rigid boundary anomaly.  With \(D=d/du\), the kernel satisfies on the open
collar

\[
  \bigl((D+\tfrac12)^2+y^2\bigr)k_y=0,
  \qquad k_y(0)=0,
  \qquad (D+\tfrac12)k_y(0)=1.
\tag{C22.2}
\]

After causal extension by zero to the whole line, (C22.2) becomes the distribution identity

\[
  \boxed{
  \bigl((D+\tfrac12)^2+y^2\bigr)(\mathbf 1_{u\ge0}k_y)=\delta_0.
  }
\tag{C22.3}
\]

Hence the dual kernel required to read the physical commutator is a Green kernel, not a closed
Stokes test.  Its boundary charge is exactly one.  This is also unique: any causal solution of the
homogeneous interior equation with zero value and zero covariant derivative at \(u=0\) is
identically zero, and therefore cannot represent the nonzero functional in (C22.1).

Consequences:

1. `XI_BV_GREEN_STOKES_STRICT_DESCENT` does not supply the missing annihilation.  Its
   transgression is an exact source endpoint difference; pairing it with the only scalar Green
   kernel that reads the Cartier energy exposes the unit source (C22.3).
2. Ordinary source exactness, causal Green descent, or a claim that the physical dual test is
   Stokes-flat is dependency-closed dead.  Setting its boundary flux to zero deletes the physical
   reading itself.
3. A surviving producer must construct a *second*, arithmetic boundary contribution of charge
   \(-1\) before divisor specialization, so that the combined causal kernel is source-free while
   its physical specialization retains (C22.1).  This is a relative-index/anomaly-cancellation
   problem, not an absolute Stokes-flatness problem.

The transform and its source charge were numerically pre-certified at right-half, left-half,
high-ordinate, and \(y=0\) points before recording the proof.  No Xi-zero location, RH, critical
line placement, or physical annihilation is used.

**Status:** paper proof complete; Lean formalization deferred during corpus refactor.  This closes
the scalar causal Green--Stokes producer class and leaves one sharply typed survivor: construct an
independent rational-adelic boundary carrying the opposite unit source.

## C23. Local relative anomaly cancellation is incompatible with coefficient faithfulness

C22 leaves an apparent escape: add an independently constructed arithmetic boundary with opposite
unit source.  The local Poisson--Gaussian germ determines whether this can preserve the physical
carrier.  It cannot.

Fix an actual Xi divisor point ρ of multiplicity \(m\), let

\[
  Z(s)=\zeta(s),\qquad U(s)=archFactor(s),\qquad \Xi(s)=U(s)Z(s),
\]

and let \(D(s)\) be any coefficient-faithful Green denominator with a simple zero at ρ.  Thus

\[
  \operatorname{ord}_\rho Z=m,
  \qquad D(\rho)=0,
  \qquad D'(\rho)\ne0,
  \qquad U(\rho)\ne0.
\]

The canonical singular Poisson lift is

\[
  P(s)={1\over Z(s)D(s)}.
\]

It has order \(-(m+1)\), while completed transport has the universal simple Green pole

\[
  \Xi(s)P(s)={U(s)\over D(s)},
  \qquad
  \operatorname*{res}_{s=\rho}\Xi(s)P(s)
    ={U(\rho)\over D'(\rho)}\ne0.
\tag{C23.1}
\]

Now allow the most general local correction invisible at the level of the retained Green
principal coefficient: suppose a meromorphic lift Ṕ satisfies

\[
  Z(s)\widetilde P(s)=D(s)^{-1}+H(s)
\tag{C23.2}
\]

with \(H\) holomorphic at ρ.  Multiplication by the completed factor gives

\[
  \Xi(s)\widetilde P(s)
    =U(s)D(s)^{-1}+U(s)H(s).
\]

The second summand is holomorphic, so

\[
  \boxed{
  \operatorname*{res}_{s=\rho}\Xi(s)\widetilde P(s)
    ={U(\rho)\over D'(\rho)}\ne0.
  }
\tag{C23.3}
\]

Therefore no holomorphic correction, lower principal jet, source-exact term, or locally invisible
relative boundary changes the unit Green residue.

Conversely, let \(C\) be a second meromorphic boundary whose completed transport cancels the
residue in (C23.1).  Since \(U(\rho)\ne0\), the Poisson image \(ZC\) must have principal part

\[
  -D(s)^{-1}.
\]

Hence \(Z(P+C)\) is holomorphic at ρ: the correction cancels the retained physical Green
principal coefficient itself.  Cancellation and coefficient faithfulness are mutually exclusive
for every local relative lift.

This gives the promised hostile test for the survivor of C22:

* a boundary invisible to the physical principal part cannot cancel its unit source;
* a boundary that cancels the unit source necessarily erases that principal part;
* increasing source pole depth only changes lower jets: the completed top residue remains the
  same nonzero \(U(\rho)/D'(\rho)\).

The argument includes arbitrary Xi multiplicity and does not assume simplicity, RH, critical-line
placement, or a norm identity.  It is the germ-theoretic content behind the formal order laws in
`DeningerMeyerXiGaussianSingularPoissonLift.lean`, strengthened to a classification of all local
coefficient-faithful corrections.

**Verdict:** local singular Cartier/Poisson anomaly cancellation is dependency-closed dead.  Any
remaining Route-R producer must be nonlocal across divisor fibres or prime places and create a
global positive trace/index identity; no additional same-fibre Green boundary can do it.

**Status:** paper proof complete; Lean formalization deferred during corpus refactor.


## C24. Full Poisson symmetry leaves a nonzero double-endpoint theta shear

C17 and the vertical-gauge modules prove that rational scaling and the Real structure do not
select a Stokes primitive.  One possible escape was that the *full* additive Poisson law, together
with both CCM endpoints, might remove the residual shear.  It does not.  The obstruction can be
exhibited on the literal rational-adelic Bruhat core.

For a Schwartz--Bruhat tensor (t), write

\[
  \Theta_{\mathbb Q}(t)=\sum_{q\in\mathbb Q}t(q)
\]

for the rational theta distribution.  Global rational dilation merely reindexes the sum, while
adelic Poisson summation gives

\[
  \Theta_{\mathbb Q}(k\cdot t)=\Theta_{\mathbb Q}(t),
  \qquad
  \Theta_{\mathbb Q}(\mathcal Ft)=\Theta_{\mathbb Q}(t).
\tag{C24.1}
\]

Thus \(\Theta_{\mathbb Q}\) annihilates every rational-dilation difference and every Fourier
difference.  The issue is whether it vanishes after imposing both endpoint conditions.  It does
not.

Put

\[
  g_r(x)=e^{-\pi r^2x^2},
  \qquad
  f=g_1-4g_2+3g_3,
  \qquad
  t_f=f\otimes\mathbf 1_{\widehat{\mathbb Z}}.
\tag{C24.2}
\]

The two endpoint cancellations are exact:

\[
  f(0)=1-4+3=0,
  \qquad
  \int_{\mathbb R}f(x)\,dx=1-4\cdot\frac12+3\cdot\frac13=0.
\tag{C24.3}
\]

Hence \(t_f\in\ker\epsilon_0\cap\ker\epsilon_1\), and also
\(\widehat f(0)=0\).  On the other hand the finite-adelic factor restricts the rational orbit to
the integer lattice, so

\[
  \Theta_{\mathbb Q}(t_f)=\sum_{n\in\mathbb Z}f(n).
\]

This value is strictly positive.  Indeed the zero summand vanishes, and for \(n\ne0\), with
\(y=e^{-\pi n^2}\),

\[
  f(n)=y-4y^4+3y^9
      =y(1-4y^3+3y^8)>0,
\tag{C24.4}
\]

because \(0<y<1/2\) gives
\(1-4y^3+3y^8>1-4(1/2)^3=1/2\).  Absolute convergence is Schwartz decay.
The witness is real and even, so the same nonzero class survives the fixed Real orientation.

Consequently the Fourier-completed double-endpoint coinvariant is nonzero:

\[
  \boxed{
  \frac{\ker\epsilon_0\cap\ker\epsilon_1}
       {\sum_{k\in\mathbb Q^\times}\operatorname{im}(\alpha_k-1)
        +\operatorname{im}(\mathcal F-1)}\ne0 .}
\tag{C24.5}
\]

Equivalently, if \(R\) is any linear Stokes primitive satisfying the dilation, endpoint, Real,
and Poisson compatibilities, then

\[
  R_\lambda=R+\lambda\Theta_{\mathbb Q},\qquad \lambda\in\mathbb R,
\]

satisfies the same compatibilities.  Full additive self-duality therefore does not select the
physical coefficient at linear level.  Killing this theta line by normalization also kills the
rational orbit distribution whose Mellin transform carries the completed-zeta channel, so that
normalization is not coefficient-faithful.

**Verdict:** the complete *linear* rational-adelic/Euler--Gamma--Poisson producer class is dead,
including both endpoint conditions and both Gamma/Real orientations.  This strengthens the Haar
shear theorem: Fourier completion does not remove the ambiguity; it replaces the Haar witness by
the physical theta witness.

**Status:** paper proof complete.  The required Lean ingredients already exist separately in
`CCMRationalArchimedeanSchwartzPoisson.lean`,
`CCMRationalAdelicPureTensorHaarDualCancellation.lean`,
`CCMRationalAdelicMoritaTraceFormula.lean`, and
`CCMRationalAdelicPrimeIsotropyVerticalGauge.lean`; assembly is deferred during corpus refactor.

## C25. Every bounded positive prime-coinvariant pairing erases the atom

C24 forces a nonlinear or bilinear producer.  The first candidate is a positive Hilbert/GNS form
on the genuine Morita completion which descends through prime-dilation coinvariants.  This class
also admits a complete obstruction.

Let

\[
  \mathcal H=\ell^2(\mathbb Q^\times),
  \qquad
  U_p\delta_q=\delta_{pq}.
\]

The \(p\)-orbits are bilateral copies of \(\mathbb Z\).  If \(U_p^*\xi=\xi\), then the
coefficients of \(\xi\) are constant on every infinite orbit \(p^{\mathbb Z}q\); square
summability forces every such constant to be zero.  Therefore

\[
  \ker(U_p^*-1)=0,
  \qquad
  \overline{\operatorname{ran}(U_p-1)}
    =\ker(U_p^*-1)^\perp=\mathcal H.
\tag{C25.1}
\]

Let \(B\) be any bounded sesquilinear form on \(\mathcal H\) which descends through the
prime coinvariants in its first variable:

\[
  B((U_p-1)x,y)=0\qquad\text{for all }x,y\in\mathcal H.
\tag{C25.2}
\]

By Riesz representation, \(B(x,y)=\langle Tx,y\rangle\) for a bounded operator \(T\).
Equation (C25.2) says \(T(U_p-1)=0\).  The range in (C25.1) is dense, hence \(T=0\), and
therefore \(B=0\).  The same argument applies if descent is required in the second variable.
Positivity is not even needed for the vanishing; boundedness and homological descent suffice.

Thus

\[
  \boxed{
  \text{every bounded positive form on the Morita Hilbert completion that descends to }
  U_p\text{-coinvariants is zero}.}
\tag{C25.3}
\]

In particular it assigns zero norm to every localized rational basis vector and erases the
retained ordinary-prime atom.  A standard GNS quotient, bounded covariance operator, bounded
same-fibre metric, or bounded positive theta covariance cannot supply Route R's independent
annihilation while retaining the period-one class.

This explains the exact location of the wall in
`RouteRBoundedPrimeDepthCovarianceProducer.lean`: bounded covariance annihilates the Hodge-mate
coefficient, but the source prime orbit has no bounded primitive.  The natural logarithmic
primitive is unbounded, and replacing it by a bounded one is already the RH-strength assertion.

**Status:** paper proof complete; Lean formalization deferred during corpus refactor.

## C26. Positive invariant means also erase every localized prime class

One might evade C25 by leaving Hilbert space and using a singular positive invariant mean.  This
does not retain coefficient provenance either.

Let \(S\) be the bilateral shift on \(c_0(\mathbb Z)\), and let
\(\Lambda:c_0(\mathbb Z)\to\mathbb C\) be positive and shift invariant.  Positivity makes
\(\Lambda\) bounded.  Shift invariance gives a common value
\(c=\Lambda(e_n)\ge0\) on all coordinate atoms.  For
\(s_N=e_1+\cdots+e_N\),

\[
  Nc=\Lambda(s_N)\le\|\Lambda\|\,\|s_N\|_\infty=\|\Lambda\|.
\]

Hence \(c=0\).  Finite-support sequences are dense in \(c_0\), so \(\Lambda=0\).  Every
positive invariant mean on \(\ell^\infty(\mathbb Z)\) consequently restricts to zero on
\(c_0(\mathbb Z)\), and in particular on all finitely supported or trace-class orbit packets.
Orbitwise application gives the same conclusion for \(\mathbb Q^\times\) under prime dilation.

Therefore a positive singular mean can preserve dilation invariance only by deleting every
localized ordinary-prime coefficient.  An unnormalized orbit sum retains the atom but is not a
bounded positive mean; its failure of invariance under cutoff is precisely a boundary anomaly.

Combining C24--C26 gives a trichotomy:

1. linear Poisson/Stokes observers retain the atom but have a nontrivial theta shear;
2. bounded positive homological pairings descend uniquely only by becoming zero;
3. positive invariant singular means erase the localized atom.

The strongest surviving producer is therefore not another reader or GNS norm.  It must be a
**nonlocal relative index/self-product pairing**: a renormalized boundary supertrace whose signed
index is source-exact, whose ordinary positive part is the Hodge mass, and whose cross-place term
uses the diagonal embedding \(\mathbb Q\hookrightarrow\mathbb A_{\mathbb Q}\).  This is exactly
the bilinear Hodge/compressed-trace gate isolated by `GaussHodgeWeilPolarizationFusion.lean` and
`GaussHodgeWeilGNSSocket.lean`.  C24 proves why additive Poisson must be consumed at quadratic
self-product level; C25--C26 prove why neither ordinary Hilbert positivity nor an invariant mean
can replace that relative index.

**Route status:** still open.  These are dependency-closed no-go results and a sharper unique
survivor, not an RH proof and not yet an exhaustive death proof for the remaining relative-index
class.

**Status:** paper proof complete; Lean formalization deferred during corpus refactor.
