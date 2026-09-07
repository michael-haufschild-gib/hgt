## Active direct attack: exact common-divisor groups of the compensated Gram

The actual carrier has residue coordinates
`F(k)=sum_(d<=M) a(d)*(k mod d)/d`, with the literal raw or tapered coefficients.
Completing unweighted floor columns does not remove these normalized residues.
Before trying a separate estimate for every common-divisor group, test whether
that grouping preserves the cancellation seen in the complete carrier.

Define `E_q=sum_(k>=1)(sum_(q|d, d<=M)a(d)*(k mod d)/d)^2/[k(k+1)]`.
Finite Möbius inversion gives the exact-gcd group
`C_r=sum_(l<=M/r)mu(l)*E_(rl)` and `sum_r C_r=E_1`.
The proposed separate-group strategy needs a small total variation
`V=sum_r |C_r|`, not merely a small signed sum. Its numerical truth is unknown.
The frozen finite discriminator tests `V<=4*D`, where D is the actual full
Gram diagonal, at M=64,128,256,512 for raw coefficients and the literal
logarithmic taper with X=M/4. The factor four is a fixed diagnostic threshold,
not a fitted constant or a proposed universal theorem. Report every signed
group, the total variation, the diagonal, and the complete signed norm.

This experiment retains analytic bounds for every omitted infinite tail.
For k=qt+i, a multiples channel is exactly
`A_q(t)+(i/q)*H_q`, where
`A_q(t)=sum_j a(qj)*(t mod j)/j` and `H_q=sum_j a(qj)/j`.
This compresses the full weighted sum into q-block moments. Finite-block
moments use direct sums at small t and a convergent geometric expansion at
large t. The tail bound is `(sum_j |a(qj)|)^2/(q*B_q)`.
Choose block counts before seeing signed outcomes so that the sum of all
divisor-multiplicity-weighted tail bounds is at most 0.05. Numerical rounding
controls are separate from these analytic truncation bounds; none enters Lean.

Run only on the authorized RunPod, eight independent Python workers, native
thread pools limited to one, with a 180-second wall limit. Controls compare
compressed moments against direct finite sums and reconstruct the signed norm
by divisor inversion. If the lower bound on V exceeds 4D, a separate-group
majorant at that tested constant fails and the next attack must retain larger
joint groups. If every upper bound is below 4D, attack the actual groupwise
arithmetic estimate on paper. Neither outcome proves or disproves RH.

