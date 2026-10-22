# RP: native coprime square Abel budget

Status: source budget, native transport, and native sign obstruction passed
final leaf and axiom audits. Finite-prefix cross negativity remains paper-only.
Parent: rp-unconditional-history-floor-loop-2026-10-01.md, RP-44.
Final RH goal remains open. This candidate tests an integrated cross-work
sign, not RH itself. No claim of a history floor or critical square admission.

## Actual source and paper calculation

Let U=divisorContinuousUnitHead and H=mobiusDivisorFullHead. Both are literal
arithmetic sources. Put v(t)=sqrt(exp(-t))*U(exp t) and
u(t)=sqrt(exp(-t))*H(exp t). They vanish for t<=0. The finite homogeneous
dilation identity gives u=logarithmicMobiusInverse(v).

The corpus's complete coprime square identity gives

    S(t)=exp(-t)*logarithmicCoprimeEnergy(u,t)
        =exp(-t)*logarithmicMobiusInverse(v^2,t).

Its endpoint is exp(-t)*u(t)^2=H(exp t)^2/exp(2*t), the actual critical
square; all other coprime pairs are retained as signed cross work.

For epsilon>0, absolute interchange of the combined right side gives

    integral_0^infinity exp(-epsilon*t)*S(t) dt
      = (1/zeta(1+epsilon)) *
        integral_1^infinity U(x)^2*x^(-3-epsilon) dx.

This admits the combined source, not either of its two signed pieces
separately. The already-proved U(x)<=3/5*sqrt(x) pays the unsigned square
integral even at epsilon=0. The combined budget consequently tends to zero
as epsilon tends to zero from above. Its quotient by epsilon tends to the
strictly positive integral of U(x)^2/x^3.

The actual H has positive square mass on a fixed initial interval below2,
where the full Mobius sum has only its unit term. Hence the conjecture of
nonnegative integrated coprime cross work fails on sufficiently long finite
prefixes for every sufficiently small positive epsilon. This is a paper
consequence to audit, not a claimed Lean no-go. A finite lower bound on that
cross work, allowing negative values, is still the hard unpaid question.
No route is retired on the basis of this unaudited calculation.

## Formal route and positive survivor

Use reciprocal variable y and the actual weight

    W(y)=y*U(1/y)^2,
    A(y)=sum_n mu(n)*W(n*y).

W is measurable, nonnegative, bounded by9/25, vanishes outside(0,1), and is
positive on(1/2,1). For y>0 the sum defining A is pointwise finite. The exact
Mellin theorem in PMDilationMellin already proves absolute interchange:

    Mellin(A,s)=Mellin(W,s)/zeta(s), Re(s)>1.

At y=exp(-t), S(t)=y*A(y). Therefore the Mellin limit is exactly the physical
combined budget. Use zetaPoleUnit and continuity of Mellin(W,.) at1 to prove
the zero limit and the strictly positive first-order coefficient. Then
transport the generic coprime identity to H, and prove the finite-prefix
negative cross-work consequence. Keep the actual source and every cutoff.

Implemented leaves: RoutePCoprimeSquareMellin.lean for the source budget,
RoutePCoprimeSquareNative.lean for actual-head transport, and
RoutePCoprimeSquareSign.lean for the native pointwise sign obstruction.
The first two passed final leaf audits and their six principal theorems
have only standard axioms. The final ten-theorem axiom audit, including
the sign obstruction, also passed with only propext, Classical.choice,
Quot.sound. All three leaves are wired without building the umbrella.
No receiver assuming the desired critical moment, no generic model
substituted for H.

The sign argument uses a stronger obstruction exposed by the positive
survivor: if the entire source A were nonnegative, its real Mellin budget
would be antitone in epsilon. A positive first-order zero is incompatible
with that monotonicity. Hence the actual full coprime energy is negative
somewhere, and its cross work there is less than minus its endpoint square.
This does not yet formalize the eventual negative integrated-prefix claim.

## Novelty and applicability audit so far

RP-44 deep search returned the generic logarithmicCoprimeEnergy_mobiusInverse
and the different CCMPrimeDeficitCoprimeBalance source. No integral theorem
was found by exhaustive searches over logarithmicMobiusInverse users;
the exact lexical query with integral returned no declarations. Relevant
search hits are source-only, not compiler certificates. The actual U ceiling,
measurability, and PMDilationMellin theorem were read directly. This positive
combined budget does not pay the endpoint square: its cross term can cancel
that square, and the desired lower bound remains open.
