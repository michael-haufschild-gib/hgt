# Product-cosine marked fibers through an analytic corner

- **ID:** cosine-product-corner-unfolding
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); significant novelty unverified
- **Parent:** ../5-failed/cosine-product-basepoint-repair.md; ../1-in-progress/labeled-lattice-section-periodicity.md
- **Target:** Prove or refute the other two cube-root fiber requirements of the explicit product repair, retaining all cancellations.

## Theorem U [FORMAL]

Both nontrivial cube-root fibers of the product repair have infinitely many genuine nonreal points. Reciprocal reflection exchanges the two fibers, so one exact branch family suffices. This excludes the candidate from C2-P; C2-P and actual Xi no-lift remain open.

This exclusion is now verified by `CosineProductNonrealFibers.two_nonreal_cube_root_fibers`, with all marker and branch premises discharged. `exists_nonreal_mark_family` supplies the injective family and retains the nonzero denominator. `CosineCornerUnfolding.exists_corner_branch` is the positive local geometric survivor; its concrete instantiation proves the unconditional fiber statement.

## Proposed geometric mechanism

Let c=2π²/81 and use the conic lift u²+v²=c, with T(w)=cos u, T(-w)=cos v and w=27u²/(4π²)-1/12. Shift the first cover coordinate by 2πn. Introduce two independent complex parameters t,q near zero, later restricted to t=1/n and q=exp(-2πn). Put L=2π+t*u and choose the analytic root r(t,u)=sqrt(1-c*t²/L²) with r(0,u)=1. The expression

    e(t,u) = c*t/(L*(1+r(t,u)))

is analytic near the corner and satisfies (L/t)*r=L/t-e for t≠0. Thus for the reflected conic branch v=i*(u+2π/t)*r,

    exp(i*v) = q*exp(-u+e(t,u)).

This is an exact identity after the discrete specialization, not a remainder estimate. Writing z=q*exp(-u+e), the reciprocal reflected factor is

    1/(cos(v)-a) = 2*z/(1-2*a*z+z²).

Consequently the target equation H/K=d is an analytic equation in (t,q,u) at the corner:

    2*z/(1-2*a*z+z²) - 1/(cos(u)-a) = d.

At t=q=0 its root satisfies cos(u)=a-1/d. A simple nonreal limiting root would continue by the local analytic implicit-function theorem to exact marked-fiber points after t=1/n,q=exp(-2πn). Nonrealness and nonvanishing denominators are open conditions. Distinctness can follow from escape of the explicit quadratic source coordinate. No uniform cosine approximation or Rouché estimate is being assumed.

## Hostile checks and remaining proof obligations

- Audit exact constants and signs before formalization. For target λ, d=-i*(1+λ)/(1-λ), so the two cube roots give d=±1/sqrt(3). The proposed nonreal corner has cos(u)=a+sqrt(3), obtained from d=-1/sqrt(3).
- Establish a simple nonreal corner root explicitly; no numerical root search or growth bound. Elementary exact algebraic location of a marked value must not be presented as a positivity criterion for the proof.
- Verify the square-root branch is analytic at the corner and every specialization identity is exact, including the source conic and the canceled homogeneous pair.
- Supply the implicit branch without assuming the desired points, then prove the discrete parameter sequence reaches its domain and produces infinitely many distinct nonreal points.
- Positive survivor if the candidate fails: an actual analytic parameterization of its marked-fiber branches at the compactification corner, not merely a negative existence statement.
- Analytic unfolding/implicit-function methods are classical. A new coordinate formula alone does not establish scientific novelty. Primary literature and corpus audit remain in progress.

## Paper closure by two submersions

The square root can be removed entirely. First solve the polynomial equation

    2*(2π+t*u)*e - t*e² - c*t = 0

near (t,u,e)=(0,u0,0). Its e-derivative is 4π≠0, so it defines an analytic correction e(t,u). At t=1/n the identity is exactly 2*(u+2πn)*e-e²=c. Hence U=u+2πn and v=i*(U-e) obey U²+v²=c. This avoids choosing a square-root sheet in the final construction.

Put x=cos(π/9)+sqrt(3), β=arcosh(x), u0=iβ and d=-1/sqrt(3). Elementary exact location of this algebraic marked value gives x>1, so β≠0, cos(u0)=x and sin(u0)≠0. This is a fixed-marker check, not a positivity criterion or an estimate for the constructed function. At the corner the second equation F=0 has u-derivative -sin(u0)/(cos(u0)-a)²≠0. It therefore has an analytic solution u(t,q), with u(0,0)=u0. For t_n=1/n,q_n=exp(-2πn), continuity puts the discrete parameters in its domain eventually. The exact conic and exponential identities above then give genuine W-fiber points at η=(-1-i*sqrt(3))/2. Nonzero factors and denominator are retained explicitly.

Nonrealness requires no root-location estimate: u_n.im tends to β≠0 and 2π+t_n*u_n.re tends to 2π≠0, so both are eventually nonzero. The imaginary part of the quadratic source coordinate is a nonzero constant times (u_n.re+2πn)*u_n.im, hence is nonzero.

Distinctness can also avoid any separation estimate. Cosine is locally injective at u0 because its derivative is nonzero. Eventually all u_n lie in this inverse chart. If w_n=w_m, then cos(u_n)=cos(u_m), hence u_n=u_m. Equality of quadratic source coordinates gives U_n=U_m or U_n=-U_m. The first forces n=m; the second forces u_n.im=0, already excluded. Thus the tail family is injective. Reciprocal reflection gives the other nontrivial cube-root fiber.

This dependency-closed paper argument for U is now verified in Lean, including its constants and identities. Its positive survivor is the two-parameter analytic corner branch and its injective discrete specialization. The construction uses local submersions and covering coordinates; no Rouché comparison, uniform approximation bound, asymptotic remainder bound, Fourier or spectral input enters.

## Search audit

Deep corpus query `analytic implicit function parameter exponential square root branch cosine`: all 20 candidate statements and 20 source-argument statements inspected, partial=false, no errors; file inventory complete, compiler freshness incomplete. The useful existing result is the arbitrary-Banach-parameter scalar holomorphic implicit-function theorem `parametric_holo_implicit`; the other derivative, local-branch and uniqueness results do not supply the explicit corner or the specialization. No new generic IFT needs to be claimed. The legacy module name contains “Spectral”, but the theorem used is solely the scalar analytic submersion theorem and its proof has no spectral premise.

[Kristiansen, Blowup for flat slow manifolds](https://arxiv.org/abs/1603.01821), abstract checked, shows that adjoining an exponential variable is an established geometric idea. Its dynamical conclusions and estimates are not used here. Thus “adding q” is not a new field or a novelty claim. The concrete internal result is the exclusion of this repair through its remaining marked fibers.

## Verification and no-go closure

Five new leaves: `CosineCornerUnfolding`, `CosineCornerMarker`, `CosineCornerCoordinates`, `CosineCornerSequence`, `CosineProductNonrealFibers`. Targeted `lake build --old +GaloisForLFunctions.HTGeometry.CosineProductNonrealFibers` passes, 3449 jobs. Final direct `lake env lean <leaf>` passes separately for all five, without diagnostics. Three axiom checks (analytic branch, injective specialization, two-fiber certificate) report only `propext`, `Classical.choice`, `Quot.sound`. Each new leaf is wired once into HTGeometry. No full or umbrella build, heartbeat increase, numerical experiment, commit or push.

Global `scripts/formal_tools.py lint` exits 1 on six unrelated unreachable leaves: RHTower `WeilConeResonanceMoments`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. None of these five new leaves is flagged. Global lint is not reported as passing.

**Anti-theatre:** the submersion method is classical; scientific novelty beyond literature is not established. The internal frontier moved by excluding the full product candidate while retaining an actual analytic family, not by proving a generic implicit-function theorem. The next cycle targets [all non-coordinate algebraic fiber components](../2-fully-proven/cosine-algebraic-fiber-rigidity.md), with boundary multiplicities and cancellation retained. No RH or general C2-P conclusion follows here.

Scoped whitespace checks pass for all eight new source/card files and the touched tracked files. `scripts/formal_tools.py index` passes, regenerating LEAN_API, LEAN_GAPS and LEAN_OVERVIEW with two changed indexed files and zero removals. All owned jobs reached terminal exits. Seven owned scratch files were removed after their findings were recorded.
