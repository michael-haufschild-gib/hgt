# FZZ-P: Gamma normalization from the actual coupling insertion

- **Stage:** 1-in-progress
- **Type:** Source-factor theorem; complete source assembly open
- **Source:** `fzz-p-radial-zero-mode-ward.md`; literal exponential winding potential and its coupling insertion.

## Proof chain and hard obstacle

Fixed theta/FZZ occurrence → complete source-derived replica–momentum Ward identity → balanced external-Gamma vacuum-delay saturation → passivity → RH.

The complete Ward identity remains open. The previous radial-factor theorem retained the neutral boundary contribution. This attack derives the momentum-dependent Gamma factor from that actual insertion integral, rather than adding a Gamma factor to an unrelated response.

## Closed source-factor derivation

Write `b=exp(v)>0`, `t(x)=exp(u+b*x)`, and let

`w(u,v,x)=b*t(x)*exp(-t(x))`.

This is the slope-normalized negative logarithmic-coupling derivative of the previous radial kernel. Its characteristic, with the positive sign convention, is

`C(u,v,p)=integral_R w(u,v,x)*exp(i*p*x) dx`

`=exp(-i*p*u/b)*Gamma(1+i*p/b)`.

The change of variables `t=exp(u+b*x)` gives `w dx=exp(-t)dt` and `x=(log t-u)/b`. Euler's convergent Gamma integral has real parameter part one for every real `p`. Thus the source is integrable, has mass one, and its characteristic is nonzero at every real momentum. Varying `u` produces precisely a linear momentum phase; it does not permit an arbitrary cubic phase change within this source family.

The equality fixes the Gamma normalization of this radial factor. It does not identify the Fourier variable with the physical BRST label, construct the remaining external-leg Gamma factors, evaluate the nonzero-mode field integral, or force vacuum saturation.

The exact source coupling law is

`C(u+h,v,p)=exp(-i*p*h/b)*C(u,v,p)`,

`partial_u C(u,v,p)=(-i*p/b)*C(u,v,p)`.

Since `C` never vanishes, its coupling derivative vanishes exactly at `p=0`. The Ward equation itself holds at every momentum. The checked source therefore supplies a nonzero momentum response, not an independently established stationarity condition. Its normalized coupling derivative removes the Gamma factor but retains the momentum charge.

The Lean proof reuses the corpus's `Gamma_vertical_eq_fourier`, whose proof derives Euler's integral through exponential substitution, then proves the full affine Jacobian change for this exact source. Integrability follows from the nonzero evaluated integral and Lean's `integral_undef`; it is not an assumed input. The density is identified with the previously proved derivative of the original radial kernel.

## Conjecture, test, and pivot

1. **Conjecture:** the actual neutral coupling insertion produces a fixed Gamma phase. **Proved in Lean:** the original integral, positive unit mass, nonvanishing, coupling shift and derivative above.
2. **Attempt:** identify this factor directly with the balanced external-BRST normalization. **Fails at the argument level:** the current external-leg definitions at `k=4` use real parts `5/2` and `-3/2`, whereas this insertion gives real part `1`. The previous phase-order receiver does not supply this missing source identification.
3. **Attempt:** use the exact coupling Ward equation as a zero-response law. **Fails:** the equation holds at every `p`, and the derivative is explicitly nonzero for nonzero `p`. A complete source equation would have to account for the other insertions and boundary contributions.
4. **Charged-factor successor:** now [closed in Lean](fzz-p-subtracted-external-gamma.md). For `s=-3/2+i*y`, the original positive-ray integral `integral_0^infinity t^(s-1)*(exp(-t)-1+t) dt` equals `Gamma(s)`. Both integrations by parts, integrability, positive remainder, the exact original radial cutoff counterterms and their limit are proved. The charged source retains `exp(-s*u)/b`, giving logarithmic coupling response `-s` with real part `3/2` at every momentum. Identifying this prescription with the physical counterterm and proving the complete marked-source Ward balance remain open.

## Plan

- [x] Search current corpus, methods, and broad recent papers; inspect exact Gamma and change-of-variable APIs.
- [x] Prove the original insertion integral and normalization in scratch Lean, with no target hypotheses.
- [x] Derive the exact source coupling Ward equation and classify its dependence on the source coupling.
- [x] Check the remaining source assembly and phase-frame identification against the actual FZZ-P obstacle; direct external-leg identification fails, and the complete mixed Ward producer remains open.
- [x] Final leaf build, umbrella wiring, axiom audit and lint.

## Search and attempted transfers

2026-09-11: deep `Fourier transform exponential potential coupling insertion gamma characteristic affine substitution`; hybrid `gamma integral change variables exponential complex power`; deep `coupling insertion gamma radial momentum dual source Ward identity`; deep `Mellin continuation subtract Taylor polynomial endpoint integrability`. These returned partial results with pending coverage. The direct Fourier and affine change-of-variable proofs were inspected and used. The dual-source query mostly returned unrelated order-dual or gauge results; no conclusion of corpus-wide absence follows. The continuation search exposed exact Taylor-remainder methods; `BarnesSingleZetaContinuation` was inspected as a source-subtraction template. Its Barnes kernel is different and its theorem cannot be directly specialized to this source.

Broad arXiv terms: `intertwining`, `dephasing`, `modular`, preferring June–September 2026. [Jiang–Wang–Wu, 3 June 2026](https://arxiv.org/abs/2606.04383), studies GNS/KMS-symmetric bimodule Markov semigroups. The full HTML fetch exceeded the tool's size limit; the abstract supplies no identified theta/FZZ semigroup or source Ward law. A related broader hit, [Frassek et al., March 2026](https://arxiv.org/html/2603.09928v1), obtains exact boundary-driven intertwining through bulk telescoping and compatible boundary algebra. The attempted transfer would need the actual source generator and matching boundary algebra; neither has been supplied here. The radial boundary term already proved cannot simply be discarded to make that match.

Additional broad terms `renewal`, `dilation`, `subtraction` produced [Chakraborty, 15 June 2026](https://arxiv.org/html/2606.16664v1). Its unitary boundary dilation requires a completely contractive semigroup representation. The attempted transfer does not identify a representation of the actual theta/FZZ source or prove complete contractivity. A unitary dilation on a larger space would also not assert vacuum saturation of its original compressed response. This supplies no missing Ward equation.

## Status

Scratch `/tmp/fzzp_coupling_gamma.lean`: PASS, no warnings. Twelve public theorems have only real parameters and no hypothesis binders. New leaf `formal/GaloisForLFunctions/RHTower/FZZCigarCouplingInsertionGamma.lean` is wired into `RHTower.lean`.

- `lake build GaloisForLFunctions.RHTower.FZZCigarCouplingInsertionGamma`: PASS; only this leaf was built, with existing dependency reports replayed. No umbrella build.
- `lake env lean /tmp/fzzp_coupling_gamma_axioms.lean`: PASS; all twelve public theorem closures use only `propext`, `Classical.choice`, `Quot.sound`.
- `python3 scripts/formal_tools.py lint`: PASS; existing large-file warnings.
- All owned foreground Lean and research processes completed; no stale owned process remains.

Source-factor theorem and its charged continuation are closed. The card stays in progress for the complete mixed Ward producer. RH remains unproved.
