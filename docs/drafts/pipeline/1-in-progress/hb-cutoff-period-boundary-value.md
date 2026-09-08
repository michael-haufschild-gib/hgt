# HB: actual cutoff-period boundary value

Full chain: theta cusp → Xi occurrence → retained spin-two source → original
causal response and physical left-QNM pairing → independent Hawking-clock
extinction → RH.

## Exact target and paper proof

Evaluate the already admitted actual integral
`K(u,k)=integral_fd E_u C_k dmu`, with the original hyperbolic measure and
`C_k=Delta_H(eta*y^k)-eta*k*(k-1)*y^k`, `eta=smoothTransition(y-2)`.
Use endpoints one and four, outside the transition, to retain the original
cutoff while making both boundary germs literal constant germs.

The complete Fourier tail has proved zero horizontal mean. Thus the actual
fundamental-domain integral becomes the sum of its two Weyl coefficients
times `integral_1^4 y^(delta-2) C_k(y) dy`. This step needs the actual
measure transport and full field, not a prescribed constant term.

Let `h_k(y)=eta(y)*y^k` and
`W(delta,k;y)=y^delta*h_k'(y)-delta*y^(delta-1)*h_k(y)`.
Direct differentiation gives

`W' = y^(delta-2)*C_k + [k(k-1)-delta(delta-1)]*y^(delta-2)*h_k`.

The actual lower boundary is zero; the actual upper boundary is
`(k-delta)*4^(k+delta-1)`. Hence each power moment is that boundary value plus
`[delta(delta-1)-k(k-1)]*integral_1^4 y^(delta-2)*h_k(y) dy`.
This is an exact all-parameter value retaining the mismatch integral.

At testing parameter `u=k-1/2`, the two Weyl exponents are `k` and `1-k`.
Both mismatch integrals vanish. The matching branch has zero boundary flux;
the complementary branch contributes `(2k-1)` times its original Weyl
coefficient. No sign, nonzero, boundary-value, or RH premise is supplied.

## Physical Xi calibration

The original momentum definition gives `i*chi_q=(q-1)/2`. Its two Weyl
exponents are `q/2` and `1-q/2`; their original coefficients are `Lambda(q)`
and `Lambda(q-1)`. The first vanishes at every Xi divisor. The second is
nonzero: at the nonreal shifted point it equals the completed zeta value,
whose reflection is at `2-q`, in the proved zero-free half-plane.

Consequently the actual cutoff periods should satisfy

`K((q-1)/2,q/2)=(q-1)*Lambda(q-1) != 0`,

`K((q-1)/2,1-q/2)=0`.

The existing entire cleared scalar inversion theorem also descends to this
nonreal physical parameter, so the full testing field has its actual modular
inversion law. Prove these original-field statements in Lean. The calibration
does not by itself evaluate the native square-residual period or prove a
full physical QNM residue nonzero.

## Lean work

Extract the existing native cusp-field integration proof into a reusable
threshold theorem and keep its old source-pairing caller. Build actual
cutoff-height smoothness and Laplacian identities; transport the complete
scalar pairing to the finite height strip; prove and integrate the original
Wronskian; evaluate all Weyl channels and substitute into the complete source
projection. Check scratch leaves, audit only individual canonical modules,
wire imports without umbrella builds, check only new/changed declarations.

## Scope

This evaluates an actual source term in the pending physical left pairing.
The global physical advanced/adjoint boundary conditions, original joint
outgoing inverse, full residue, and independent extinction remain open.
Frontier map is read only. No numerical experiment is indicated.
