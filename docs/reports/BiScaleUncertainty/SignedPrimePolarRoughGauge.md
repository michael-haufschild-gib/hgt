# Chebyshev mean-square packet control for every compact continuous source

Let f be any real compact continuous source, with no differentiability assumption.
Fix real a,b,c; put A=exp(a), d=exp(b), η=exp(c), and

g(u)=d⁻¹∫_[A,A+d] f(u-y)dy,
k(u)=(f(u-A)-f(u-A-d))/d-g(u)/2.

Let R=autocorr(f,0), C=correlationAverage(f,a,b,0), B=collarEnergy(f,a,b),
δ=R+B-2C, and G=∫|k|. Write Q_N(f) for the actual signed prime–polar packet
energy, M_N for its total unsigned measure mass, L=log(N+2), and

e(x)=exp(-x/2)(ψ(exp x)-exp x),  E₂=∫_[0,L] e(x)²dx.

## Source-only upper control

All these integrals are admitted by the actual sources and the finite window.
For every f,a,b,c,N, the target theorem is

Q_N(f) ≤ 3(1+η)(10+e(L)²)B + 3(1+η)G²E₂ + (1+1/η)M_N²δ.

At c=0 this becomes

**Q_N(f) ≤ 6(10+e(L)²)B + 6G²E₂ + 2M_N²δ.**

The bound has no extra C¹, derivative, integrability, nonzero-source, grid-zero,
or prime-error hypothesis. The original von Mangoldt weights and full polar
density remain in Q_N and M_N. The roughness remainder M_N²δ is essential;
no cutoff-uniform estimate follows by discarding it.

## Proof

**Constructed regularity.** Change variable v=u-y in the collar integral:
g(u)=d⁻¹∫_[u-A-d,u-A] f(v)dv. The fundamental theorem of calculus for the
continuous f gives g'(u)=(f(u-A)-f(u-A-d))/d. This derivative is continuous.
Thus g is C¹, derived entirely from f's continuity. The collar source already
has compact support. Its derivative is a difference of translates of f and
therefore also has compact support. Consequently k=g'-g/2 is an actual compact
continuous source and |k| is integrable. This proves G is a genuine L¹ integral.

**Remainder admission.** The actual source r=f-g is compact continuous. Expanding
its square and using the verified identities ∫g²=B and ∫fg=C gives ∫r²=δ≥0.
No sign condition on C is needed.

**Exact packet splitting.** Finite sums and the compact-window polar integral
are linear in their source, so P_N(f)=P_N(g)+P_N(r). Every source integrand is
continuous on the finite polar window, justifying the integral splitting.
For η>0, the elementary square (ηx-y)²≥0 gives
(x+y)²≤(1+η)x²+(1+1/η)y². Integrating the actual square-integrable packets yields

Q_N(f)≤(1+η)Q_N(g)+(1+1/η)Q_N(r).

The verified total-mass bound gives Q_N(r)≤M_N²∫r²=M_N²δ. The neighboring
C¹ Chebyshev-gauge theorem, applied to the constructed g, gives

Q_N(g)≤3(10+e(L)²)B+3G²E₂.

Its C¹ hypothesis has just been proved from the actual original source. Substitute
these two bounds to obtain the weighted theorem and its c=0 specialization.

**Global scalar consequences.** Denote the fixed-constant upper bound by U_N(f,a,b).
The smoothing parameters a,b are independent of transport parameters u,v. At
N=N₀(f)+K, the verified coherent transport inequality is
(D∞(h)-W∞(u,v))²≤Q_N(f)δ(u,v). Multiplying Q_N(f)≤U_N(f,a,b) by δ(u,v)≥0 gives
the global coherent bound.

For every η₀=exp(c)>0, substitute the same upper bound into the previously proved
global Lévy transport estimate to obtain

|D∞(h)-W∞(u,v)| ≤ η₀ J(u,v)
 + U_N(f,a,b)/(2η₀ exp(2v)) ∫_[exp(u),exp(u)+exp(v)] exp(-y/2)sinh(y)dy.

The substitution preserves inequality because the reciprocal-weight integral
and its denominator are nonnegative. This gives a global scalar coupling with
explicit mean-square Chebyshev error, collar-source energy, gauge L¹ cost,
original-source roughness, and the exact archimedean reciprocal penalty.

## Significance and boundary

This discharges the smooth-source interface of the packet upper estimate without
restricting the original source class. The derivative appearing in the proof is
replaced in the final bound by the displayed finite difference of f. The tradeoff
between regularity cost G and roughness δ is explicit. This package does not
claim an arithmetic asymptotic, a uniform cutoff bound, or convergence of an
infinite signed source packet.

The neighboring C¹ theorem is an input, not a contribution claimed here. The
regularity construction, packet splitting, upper bound, and scalar transfer count
together as one contribution. Both leaves pass direct `lake --old env lean`
with empty diagnostics. Final scratch audit exits 0: nine new endpoints and the
reused C¹ dependency have only propext, Classical.choice, Quot.sound. Printed
main signatures have no extra premises. Imports are wired; index refresh passes.
Global lint flags only unrelated unwired `ChebyshevGaugeNyquistCellQuadrature`
at this verification snapshot. Evidence is recorded in the companion facts ledger.
This is verified contribution 5/100; the full research goal remains active.
