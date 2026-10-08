# GY certificate: retain the complex pole and its Fourier orientation

Status (8 October 2026): **BRIDGE / correction of a proof step**, not a PBAP solution,
not a disproof of the Goldston–Yıldırım certificate, and not a scientific novelty claim.

## Exact frontier and competing claims

The corpus's L385 proposes a truncated-divisor certificate but leaves its uniform
all-height estimate open. L398 later proposes a zero-driven obstruction. Neither
paper sketch is an unconditional formal theorem. The exact full-cone existence
problem remains open.

L385's coprime Möbius asymptotic needs its parameter range: Goldston–Yıldırım,
[Lemma 2.1 and (2.14)](https://arxiv.org/html/math/0111212v1), distinguish a restriction
on the coprimality parameter from the unrestricted error bound. Substituting
`Y=R/q` throughout `q<=R` does not give a uniformly small error near the endpoint.
Their correlation results also do not supply the requested all-height supremum.
The per-prime Euler-factor estimate alone does not justify factoring a truncated,
coupled numerator/denominator window.

L398 passes from a complex second-order pole to a Lorentzian Fourier size. This
must retain the orientation of the pole. Its local frozen-coefficient model is
incompatible with the exact identity below. This diagnoses that step only:
the full zeta factor, the other residues, multiplicities, contour shifts and
remainder estimates still require an independent argument. In particular this
audit proves neither zero-insensitivity nor a zero-free-region consequence for
the actual GY window sum.

For comparison, [Bettin–Gonek](https://arxiv.org/html/1604.02740v1) establish a
zero-free consequence of upper bounds for complete mollified second moments,
with explicit length/height quantifiers. Those are different objects and
quantifiers from a single GY coefficient window. Their proof retains a one-sided
Mellin kernel; it does not validate replacing a complex pole by its modulus.

## Dependency-closed positive survivor

For `delta>0`, let

`K(delta,x,t) = exp(2*pi*i*t*x)/(delta-2*pi*i*t)^2`.

Then, with Lebesgue measure on the real line,

`integral K(delta,x,t) dt = 0` for `x>=0`, and

`integral K(delta,x,t) dt = (-x)*exp(delta*x)` for `x<0`.

All integrals converge absolutely. Indeed the numerator has modulus one and
the denominator's modulus squared is `delta^2+(2*pi*t)^2`.
Replace `t` by `-t` and apply the corpus's proved Perron kernel identity at
`u=-x`: its exact answer is `u*exp(-delta*u)` on `u>0`, and zero otherwise.
This also proves the value at `x=0`, without a boundary half-weight.

More generally, for a finite index set, arbitrary complex coefficients `b_j`
and real frequencies `v_j`, define `A(t)=sum_j b_j*exp(-2*pi*i*t*v_j)`.
Absolute integrability of every term and finite linearity give the exact law

`integral A(t)*K(delta,x,t) dt
 = sum_{j: x<v_j} b_j*(v_j-x)*exp(-delta*(v_j-x))`.

Thus every frequency at or below `x` contributes exactly zero. Frequencies
above `x` are retained with their complex signs; no absolute-value replacement
is made. The formula identifies the surviving tail rather than merely giving
a negative verdict.

For the local frozen-zeta model in L398, `x=log(X/R)>0`; the bare pole integral
is therefore zero, not a positive exponential of `-delta*x`. A smooth Mellin
window still requires its exact sign convention and a justified interchange;
the theorem above alone is not the full window analysis.

## Formal status

The parent identity is `RHTower.perron_kernel_identity`. The reflected identity
and exact finite-frequency tail are paper-proved above; direct Lean verification
is pending. Do not count this diagnostic as full PBAP progress or retire GY.
