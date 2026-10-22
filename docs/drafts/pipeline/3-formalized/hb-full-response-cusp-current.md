# HB: complete response corrections in the original cusp current

- **ID:** HB-QFCC
- **Stage:** 3-formalized
- **Type:** SOURCE ATTACHMENT proved
- **Parent:** [Native cusp-current trace](../3-formalized/hb-native-cusp-current-trace.md)
- **Route:** Literal theta source → Xi occurrence → retained spin two → physical causal/left-QNM action → common Hawking-clock extinction → RH

## Hard obstacle and current source target

The native trace theorem is verified and its current source hash agrees with
the audited leaf. This is verified progress from the preceding goal turn.
The current task is to carry that source-derived trace through the constructed
full quadratic angular responses, not to assume a zero physical boundary.

For each actual response branch b, the original assembly gives, on the
original cusp cell and y>3,

```
H_b(x,y) = P_b(y) + R_b(x,y).
```

P_b is the original particular response; R_b is the native forced response.
Prove its local vertical derivative, then integrate the complete product to get

```
M[(partial_y H_a)H_b] = (M H_a)'(M H_b) + J_ab,
y^N {M[(partial_y H_a)H_b]-(M H_a)'(M H_b)} -> 0.
```

The means must be the original fullMean/fullResponseCuspMean, retaining both
particular and native source coefficients and source tails. Adding P_b changes
the means, but cancels identically from the bilinear covariance remainder.

The actual angular Green current has the exact original coefficients

```
alpha_b (partial_y H_a)(H_b+Q)
  - alpha_a (partial_y H_b)(H_a+Q).
```

Restore its complete response-response contribution before treating the Q
contacts. The full scalar test has a nonconstant theta tail and is not
height-only. Subsequent current traces must include that factor, its derivative,
source-contact contributions and the other physical faces/channels.

This target does not redefine success: complete fixed-Hawking-clock extinction
and RH remain open. Horizontal modular translation is not physical-clock
translation. No frequency counterterm or covariance/extinction premise is allowed.

## Conjecture/proof loop

1. Conjecture: adding the source particular responses leaves the native
   nonconstant current unchanged. Derive the pointwise assembly and vertical
   derivative from actual equations; prove the finite source-cell identity.
2. Transfer the audited rapid native trace to these complete response products,
   then to the response-response part of the actual angular Green current.
3. Include Q-contact and physical scalar-test products. If a proposed
   conservation law leaves source work, preserve that work and test the next
   candidate against the complete action rather than assigning it zero.

Lean: use a new dependent leaf, scratch checking at default limits, one
foreground Lean process, exact leaf-only final audit, one umbrella import.

## Source proof and complete-current attachment, 12 September 2026

The full-response pair identity and every natural polynomially weighted
upper-trace limit passed `lake env lean /tmp/hb-full-response-cusp-current.lean`.
For y>3, the original cutoff equals one on the fundamental cusp cell, hence
H_b=P_b+R_b there. Local equality and the independently proved smoothness of
H_b and R_b give P_b' and H_b,y=P_b'+R_b,y. Integrating the four product terms
gives the displayed identity; the particular terms cancel from the covariance.
The actual fullMean equals fullResponseCuspMean, so both original native moment
tails and the selected homogeneous coefficient remain in the mean term.

For the original complete incoming current, write s=physicalRate(true),
t=physicalRate(false), p=s*t, alpha=parameter(true), beta=parameter(false),
and w_i=sourceWorkWeights(i). Its exact contact part is

```
K_j = Q*((w_0-p*beta/3)*partial_j H_true
        +(w_1+p*alpha/3)*partial_j H_false
        +(2*w_2/3)*partial_j Q).
```

Thus, with m_b=M H_b and gamma=-p/3,

```
M completeCurrent_1
  = gamma*(beta*m_true'*m_false-alpha*m_false'*m_true)
    + M K_1 + gamma*(beta*J_true,false-alpha*J_false,true).
```

The final term has zero upper trace after multiplication by every natural
power of height. This transports the native trace to the original complete
incoming current before the physical scalar test. The attachment and its
complex-height-weight extension passed the exact leaf audit.

Substitution of the original parameters alpha=(2*s+1)*(2*s+2),
beta=(2*t+1)*(2*t+2), d_s=s*(s-1)/4 and d_t=t*(t-1)/4 gives the paper identities

```
w_0-p*beta/3 = -2*s*d_t*((t+1)^2-p),
w_1+p*alpha/3 = 2*t*d_s*((s+1)^2-p),
2*w_2/3 = 4*d_s*d_t*(s-t)*(1-p)/3.
```

These are actual partial cancellations, not vanishing of K. In particular,
using s+t=-3, the last coefficient factors as
`p*(p+4)*(s-t)*(1-p)/12`. The established Re(p)>2 and nonzero Xi imaginary
part make every factor nonzero. This does not exclude compensation between
the full contact fields, full mean flux, bulk source work and other faces.

The physical test remains the entire completed Eisenstein scalar, not its
constant mode. The next source estimate must control its tail multiplying
the derivative-response products and preserve testDerivativeWork. The finite
tested balance also retains the lower cusp endpoint, reducedSourceWork and
the original temporal/horizon clock factors. Independent SS/SV/VV, retained
spin-two, changing metric weights, characteristic and source-contact faces
still require complete physical-action identification and cancellation.

The exact sufficient action estimate remains `Re C_phys >= 0` at the original
clock: together with `C_phys=-susceptibility*clockDefectEnergy`, positive
susceptibility and nonnegative energy, it forces zero defect. No such signed
estimate or complete fixed-clock invariance follows from the present cusp
identity, and none is added as a premise.

## Search and method audit

Both cached deep requests inspected candidate lemmas, source arguments and
ingredient sets. The first full-cusp request completed retrieval with source
inventory 57,167 files. The nonlinear source/contact/reciprocity request
inventoried 57,202 files but was partial after a reranking deadline; compiler
metadata mostly remained pending and semantic coverage was not measured.
Source inspection confirms the proposed transfer-equality ingredient is an
equivalence with current vanishing, not a source producer. The nonlinear
evolution hit likewise assumes FE covariance, and its existence is already
classified as RH-equivalent. Neither supplies an admissible missing premise.

Broad recent arXiv reciprocity searches found
[Khankhoje--Kundu, 12 June 2026](https://arxiv.org/html/2606.14486v1): its
Lorentz surface identity requires a source-free region and a linear medium
with the required material symmetries. Its insistence on retaining structural
scattering and finite-boundary terms motivates checking the full current,
but does not remove the present nonlinear source contacts.
[Vu et al., revised 6 September 2026](https://arxiv.org/html/2609.04169v2)
derive response restrictions from a symmetric invertible linear operator.
Complex transpose symmetry can suffice for their reciprocity statement; it
does not identify the nonlinear retarded response or its full boundary action
with a symmetric Hessian. The attempted transfer therefore fails at that
source identification. Broad date-sorted memory and Noether searches were
also attempted; the former mostly returned unrelated computing papers and
the latter endpoint failed to fetch. No theorem was inferred from those hits.

Optimization: the particular derivative follows from H-R on a neighborhood,
so the proof does not expand the three cusp powers or their denominators.
Finite integrals carry explicit integrability proofs, and local source fields
remain unexpanded during the polynomial current algebra. No resource override
or axiom-printing step was used.

## Remaining hard source task

The full scalar-tested centered current is now closed in
[HB-QTCC](hb-physical-tested-centered-current.md): all six differentiated
terms are retained and every complex-weighted upper trace vanishes. Its
improper density integral retains the negative original lower current.
[HB-QTMCC](../1-in-progress/hb-physical-tested-mean-contact-current.md)
carries the restored linear moments, full means and source contacts forward.
Full independent-channel physical-action identification, fixed-clock
extinction and RH remain open.

## Formal validation

Five definitions and eight public theorems are closed in
[ThetaCuspHawkingBMQuarticFullResponseCurrent.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMQuarticFullResponseCurrent.lean).
The assembled scratch passed without diagnostics. The exact cached
392-line leaf audit then passed `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticFullResponseCurrent`
in 134 seconds, without resource overrides. One umbrella import was added;
no umbrella or full build was run. Source SHA256:
`f68adba5bdee434d4ea3cdc4d703c4e3d2faee82ce27336692b9ec3ffcbf118a`.

The three surviving source-contact coefficient identities above are proved
by `completeContactCurrent_source`. The subsequent factorization and
nonvanishing discussion is a paper argument, not an additional Lean claim.

Final integration: index refreshed two changed source files; all thirteen API
rows, the single umbrella import, the unchanged audited source hash and audit
directory cleanup were verified. `scripts/formal_tools.py lint --check-generated`
exited 1 with one unrelated shared-tree error:

```
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.InversePowerCancellation
```

No global lint success is claimed. That unfinished module was not changed.
All owned Lean, search, index and lint processes completed. Log:
`formal/.lake/hb-extinction-scratch/full-response-current-lint.log`.
