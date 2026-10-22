# Logarithmic toric boundaries and finite asymptotic values

- **ID:** logarithmic-toric-no-asymptotic-values
- **Stage:** 1-in-progress
- **Type:** CANDIDATE theorem with paper argument under hostile audit
- **Parent:** cosine-basepoint-secant-repair.md; labeled-lattice-section-periodicity.md
- **Purpose:** Close the actual basepoint repair obstruction by geometry of logarithmic coverings, then audit a general algebraic-curve criterion. No RH conclusion yet.

## Exact general candidate N

Let B be a closed affine algebraic curve in C², with projective closure meeting the line at infinity only outside RP¹. Work on its normalization. Let L(X,Y) be a Laurent polynomial whose two-dimensional Newton polygon contains (0,0) in its strict interior. Define

    F(u,v)=L(exp(i*u),exp(i*v)), (u,v) in B.

**Conjecture N:** F has no finite asymptotic value along any continuous path in B leaving every compact subset. The projective boundary condition is essential: B={v=u} and L=X+X^-1-Y-Y^-1 give the constant function zero. The Newton condition is essential: on B={v=i*u}, L=X has finite asymptotic value zero.

The concrete target uses B: u²+v²=2c², c=pi/9, and L=X+X^-1+Y+Y^-1. Its two points at infinity are [1:i:0] and [1:-i:0]. With alpha=4*pi²/27,

    u²=alpha*(w+1/12), v²=alpha*(-w+1/12),
    L(exp(i*u),exp(i*v))=2*(T(w)+T(-w)).

Do not confuse an asymptotic path with an arbitrary escaping sequence: the fibers themselves can be infinite. A continuous logarithmic lift is the decisive extra datum.

## Paper mechanism, explicit dependencies

### 1. Properness of the exponential map restricted to B

Claim: E_B:(u,v) -> (exp(i*u),exp(i*v)) is proper into (C*)².

If an escaping sequence in B had exponential images in a compact subset of (C*)², cover that compact set by finitely many relatively compact logarithm charts. On a subsequence one chart suffices: its logarithmic lifts differ from (u,v) by the real deck lattice (2pi*Z)². Compact chart lifts plus an escaping real lattice sequence have only real projective limiting directions. Projective compactness supplies such a direction at infinity on the closure of B, contradicting its disjointness from RP¹. Equivalently, the exact identities Im(u)=-log|X| and Im(v)=-log|Y| keep the imaginary coordinates compact. This is qualitative separation of boundary strata; no quantitative growth rate, root bound, positive kernel, energy or counting estimate is used. The real/nonreal incidence step must remain explicit in formalization; do not substitute an analytic growth estimate.

### 2. Finite boundary possibilities for a bounded level family

Suppose gamma is an escaping continuous path in B and F(gamma) tends to A in C. Compactify (C*)² by the toric surface of the Newton polygon (a smooth toric refinement can be used). Homogenize L-a over a in a compact neighborhood of A. Because 0 is strictly interior, changing the constant coefficient changes no edge polynomial. On every boundary divisor the finite-level family meets only the finitely many zeros of its edge polynomial, in the open torus of that divisor; it meets no toric fixed point. Thus all boundary cluster points are in a fixed finite set Z.

Step 1 rules out interior cluster points of E_B(gamma). Compactness and continuity now force E_B(gamma) to converge to one element of Z: disjoint neighborhoods of Z contain the entire sufficiently late connected tail, and nested such neighborhoods isolate a single limit. This step needs an actual proof, not an assertion that an arbitrary sequence chooses one corner.

### 3. The local character fixes a logarithmic direction

At a boundary point on an edge with primitive normal (m,n), choose the nonvanishing boundary character chi=X^n/Y^m. It tends to a nonzero complex number chi0. A local logarithm of chi exists near chi0. Since gamma's tail is connected, the integer difference between this logarithm and i*(n*u-m*v) is constant. Therefore n*u-m*v converges to a finite value. An escaping point of B must then have projective direction [m:n:0], which is real. This contradicts B's boundary hypothesis and proves the proposed N.

The argument must survive multiple edge roots and special finite levels; the edge point itself and chi0 remain fixed because the constant coefficient is interior. No normal-form claim for the varying curve is needed. A toric refinement must retain the nonvanishing edge character and the exclusion of fixed points.

## Fully explicit four-corner specialization

For L=X+X^-1+Y+Y^-1 the finite-level equation, with level d, is

    X²Y+XY²+X+Y-dXY=0.

In P¹ x P¹ its boundary consists of precisely (0,0), (0,infinity), (infinity,0), (infinity,infinity), for every finite d. At (0,0), dividing the equation by X+Y locally or using the implicit function theorem gives Y/X -> -1. At (infinity,infinity), invert both coordinates and obtain the same ratio limit. At the two mixed corners, invert the infinite coordinate and obtain XY -> -1. All four assertions also hold when d tends to a finite limit: the local linear terms are X+Y after the relevant inversion, and the derivative with respect to either local coordinate is 1 at the corner.

Hence exp(i*(u-v)) or exp(i*(u+v)) tends to -1. Local logarithm plus connectedness makes u-v or u+v converge. The exact identity

    (u+v)² + (u-v)² = 4c²

then prevents escape on B. Equivalently, its only points at infinity have nonreal slope. This is the concrete no-asymptotic proof to formalize first; a general toric library is not required before this application.

## From no escape to Conjecture E

Write S(w)=T(w)+T(-w). A path w->infinity lifts on its final tail to the square-root cover B (the two finite branch points are avoided); finite S along it would contradict the preceding argument. Thus the proposed specialization gives no finite asymptotic values of S.

S is transcendental. Its zero fiber has an exact infinite family: put h=n+1/2, n>=0, r=sqrt(81h²-1), and w=(3/2)*i*h*r. The square lifts u=pi*h+i*pi*r/9 and v=-pi*h+i*pi*r/9 differ by (2n+1)pi, so cos(u)+cos(v)=0. Their squared w-values form a nonconstant quartic in n and hence have infinite range. S is not identically zero, for example by its infinitely many distinct values 2*T(w_n) on the already certified diagonal family.

Classical Iversen: a transcendental meromorphic function taking a value only finitely many times has that value as an asymptotic value. Therefore every finite fiber of S is infinite. This is a named, established dependency, not a new conjecture or a hidden premise. Its available Lean status must be checked and, if missing, its exact needed form proved. An alternative is to continue the infinitely many simple zero-fiber inverse branches along a path avoiding the countable critical-value set, using no-escape to prevent breakdown; endpoint merging is finite by local analytic order. That alternative also needs a complete continuation proof.

Each real fiber of S is finite. If real w escaped while S(w) stayed at one finite value, the exponential pair would have to approach one of the four corners above. But for real w outside the two branch points, one of u,v is real, so one of X,Y lies on the unit circle. No corner has a unit-circle coordinate. Thus the real fiber is compact; discreteness of a nonconstant entire function makes it finite. No numerical interval or estimate for real zeros is required.

Apply this to S=2a with a=T(0): infinitely many solutions are nonreal. At a nonreal solution, T(w)!=a, since `source_eq_fiberValue_iff` places every a-fiber point on the real line. Hence T(w)!=T(-w), the denominator of the secant repair is nonzero, and V(w)=1 holomorphically. This would prove the strong form of E and exclude the canonical cancelled-basepoint repair. It would not exclude every negative-diagonal rational repair or prove C2-P/RH.

## Hostile audit and current status

- FALSE: arbitrary escaping sequences do exist in finite fibers; every no-escape statement here concerns a continuous asymptotic path. Connectedness fixes the logarithm sheet.
- CIRCULAR: compactification of the algebraic Laurent family, not properness of S, supplies the corner set. S is not proper when fibers are infinite.
- REDISCOVERED: Iversen, the Laurent elliptic family, elementary logarithm covering theory and toric edge polynomials are classical. General N and its precise geometric proof need a targeted novelty audit; no significant novelty claimed.
- BRIDGE: the current application excludes one concrete repair only. No hypothesis about arbitrary C2-P sections or Xi is supplied.
- CONSTRAINT AUDIT: the proposed proof uses local algebraic orders, covering lifts, compactification and nonreal boundary incidence. Do not replace these by a finite-order theorem, DCA, Nevanlinna estimates, cosh comparisons, Rouché estimates, or a positive-form criterion. Elementary real/complex incidence in Step 1 is a substantive point to retain and audit, not conceal.
- FORMAL: the regular-diagonal obstruction, basepoint boundary model, concrete conic no-escape theorem, and absence of finite asymptotic values of S are Lean-certified. General N, infinite fibers of S, finite real fibers and E are not yet formalized. Keep this card in progress until the complete application is checked.

## Source audit, 2026-10-07

Deep query `logarithmic cover affine quadric asymptotic path finite fiber inverse continuation`: 20 candidates and 20 source arguments inspected; none supplies the claimed theorem. The proposed fiber-entropy ingredient set is unrelated. `partial=false`, no errors, current coverage snapshot, compiler freshness incomplete; semantic coverage not measured.

[Bergweiler–Eremenko, On the singularities of the inverse to a meromorphic function, pp. 2 and 16](https://www.math.purdue.edu/~eremenko/dvi/bergo.pdf) supplies the inverse-surface definitions and explicitly states Iversen's finite-preimage/asymptotic-value theorem. None of that paper's finite-order or quantitative corollaries is used. [Juyal–Moody](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=931852) identifies the classical Laurent elliptic family. Searches for exponential-polynomial finite asymptotic values, proper exponentials of algebraic curves and Laurent-polynomial asymptotic values did not find the exact criterion; this is incomplete novelty evidence, not proof of absence.

The documented lexical query `Iversen` returns zero hits; no theorem with that name was found in the searched HTGeometry/mathlib complex-analysis sources. This does not prove the needed inverse-continuation machinery is absent under other names. The next search should target finite valence, inverse singularities, path continuation and Picard separately, rather than repeating the poor broad semantic query.

## Covering-limit prerequisite: complete paper proof

For topological spaces E, X, I, a map f:E→X, an evenly covered point y with sheet space I, and continuous u:ℝ→E, suppose f∘u tends to y at +∞. Then u tends to some e with f(e)=y. Indeed choose an evenly covered open neighborhood U and its homeomorphism H:f⁻¹(U)→U×I. A final closed ray lies over U. Its image under the discrete second coordinate of H is constant, because the ray is connected. The first coordinate converges to y. Applying the continuous inverse H⁻¹ gives the claimed lift limit and the projection identity gives f(e)=y. Neither compactness of E nor a bound on the sheet label is assumed. For complex exp this applies at every nonzero y. Verdict: classical BRIDGE, not novel knowledge; necessary dependency of the corner argument.

Current deep query `"finite valence" "inverse singularity" "path continuation" Picard --any` inspected all 20 candidates and 20 source arguments; returned Picard-iteration machinery does not supply the needed complex inverse theorem. Mathlib's little Picard proof uses Nevanlinna estimates and is inadmissible for this route. The exponential covering map is available and uses the local logarithm and discrete deck group.

## Exact corner exclusion: complete paper proof

Let a,b:ℝ→ℂ be continuous, with a²+b²=C pointwise. There is no finite limit d of `L(exp(a),exp(b))` if both exponentials tend to zero. Write X=exp(a), Y=exp(b), D=L(X,Y), and W=1+X²+XY-DX. Exact multiplication gives `(Y/X)W=-1`. Since W→1, Y/X→-1. Consequently exp(b-a)→-1, and the covering-limit theorem gives b-a→k. Also a escapes every compact subset: the image of any compact set under exp is compact and excludes zero. Topological inversion at infinity now gives 1/a→0; a is eventually nonzero. Thus b/a=(b-a)/a+1→1. Dividing a²+b²=C by a² gives `1+(b/a)²=C/a²`; taking limits gives 2=0, a contradiction. This is a boundary incidence calculation, with no estimated rate or bound. Sign changes a↦±a, b↦±b retain the conic and exchange each infinite exponential coordinate with its inverse, so this calculation treats all four corners.

The corpus already contains `Bottcher.tendsto_of_mapClusterPt_finite` in `DiskAlgebraicContinuation.lean`: compact support, an antitone connected-image filter basis, and finitely many cluster values force convergence. Reuse this engine for the four-corner selection instead of reproving it. Its exact proof uses connected intersections of compact sets; the surrounding disk-specific metric lemmas are not dependencies of that theorem.

## Interior exclusion without a quadratic estimate

Here is an exact compactification proof of the conic's interior step. Work along any ultrafilter for which exp(a) and exp(b) have finite nonzero limits and a²+b²=C. The identities Re(a)=log|exp(a)| and Re(b)=log|exp(b)| give finite real-part limits. Put z=a+i*b and w=a-i*b. Then zw=C and H=z+conj(w)=2*Re(a)+2i*Re(b) has a finite limit. The compactification ℂ∪{∞} gives either a finite z-limit or z→∞. In the second case z is eventually nonzero, so w=C/z→0, and z=H-conj(w) has a finite limit, contradiction. In the first case conj(w)=H-z has a finite limit, hence so do w,a,b. Thus an escaping conic path cannot have an interior exponential-pair cluster point. The mechanism is the product identity and two affine charts at infinity, not positivity or an estimate on a²+b².

To classify the remaining cluster points, suppose one exponential coordinate has a finite nonzero limit. Its reciprocal also converges; the Laurent relation forces Y+1/Y to a finite limit for the other coordinate. Y→0 contradicts `Y*(Y+1/Y)=Y²+1`; Y→∞ contradicts the same identity after inversion. Hence both coordinates are interior or both are in {0,∞}. On an escaping conic path only the four corners remain. Connected-tail finite-cluster convergence produces a single corner, which the preceding corner theorem excludes. This gives a dependency-closed topological proof of the concrete conic no-escape statement for arbitrary C, now checked in Lean.

The square-root transfer works for every complex c: `descendedCos(w)+descendedCos(c-w)` has no finite asymptotic value. Given an escaping continuous path, replace its initial part by a constant so the whole parameter line avoids {0,c}; the replacement agrees eventually with the original path. Contractibility of ℝ and the square covering over ℂ\{0} produce continuous roots u²=w, v²=c-w. Set a=i*u, b=i*v. They lie on a²+b²=-c, and their pair escapes because the continuous projection `(a,b)↦-a²` recovers w. The Laurent expression is exactly twice the cosine sum. The affine homeomorphism w↦α(w+1/12), α=(2*pi)²/27, then specializes c=α/6 to S(w)=T(w)+T(-w). Neither the covering lift nor this affine change assumes any zero classification for S.

## Formal closure of the concrete no-escape step, 2026-10-07

Five leaves supply the exact dependency chain: `EvenlyCoveredLimit` (connected sheet and compact escape), `ToricConicCorner` (limiting character and conic contradiction), `ConicInteriorLimit` (mixed product compactification), `ConicLaurentNoEscape` (all four corners), and `CosineSumNoEscape` (continuous square lifts and actual source). The final theorem is `GaloisForLFunctions.HTGeometry.CosineSumNoEscape.source_sum_no_finite_asymptotic_value`. The completed audit is recorded below. No inverse-singularity theorem is assumed in this certificate. It removes the concrete no-escape premise of E, not the infinite-fiber or real-fiber premises.

Final verification: all five leaves pass direct `lake env lean` with no warnings; targeted final build passes (3452 jobs). Six axiom checks report only `propext`, `Classical.choice`, `Quot.sound`. All five imports are wired once into HTGeometry. Global lint exits 1 on six unrelated unreachable modules: `ZetaLineResonatorLargeValues` and the five previously reported aperture/corona modules. None of the five no-escape leaves is flagged. Scoped diff whitespace checks pass. No full build, umbrella build, heartbeat increase, or numerical experiment was used.

`scripts/formal_tools.py index` completed and regenerated LEAN_API, LEAN_GAPS and LEAN_OVERVIEW. No owned process remains active after final checks. Significant novelty beyond literature remains unverified; this is a completed geometric premise, not RH or Conjecture E.

Hostile extension audit produced a [product-divisor repair](../../../5-failed/cosine-product-basepoint-repair.md). Its infinite regular 1-fiber and homogeneous 3ℤ containment are now formalized. The other two cube-root fibers have infinitely many genuine nonreal holomorphic points, proved by [analytic corner branches](../../../3-formalized/cosine-product-corner-unfolding.md), so the full candidate fails. Do not infer a general rational-repair obstruction from this sum theorem or this single candidate. Conjecture E remains separate.

[Heittokangas–Ishizaki–Tohge–Wen, arXiv:2202.01574v2](https://arxiv.org/pdf/2202.01574), abstract, contents and relevant algebraic/ODE sections inspected: it treats polynomial exponential phases and classical value distribution. Text search found no `asymptotic value` occurrence. The present source has algebraic phases on a conic; no precise N theorem was located. Do not adopt that survey's open problems as replacement targets or import its growth estimates.
