# FZZ-P: marked radial replica response

Status: radial source statements closed and audited in Lean, 2026-09-11. RH and the full integrated mixed Ward producer remain open.

## Obstacle and conjecture loop

The chain remains fixed theta/FZZ occurrence → source-framed integrated mixed replica–momentum Ward identity → external-Gamma vacuum-delay saturation → replica passivity → RH. The prior charged Gamma finite part retains a nonzero coupling response; it does not supply a replica insertion or stationarity.

The literal first-order marked radial weight from Halder–Jafferis (3.29) is `r(δ)=1−cδ`, where `b=exp(v)`, `k=2+b²`, and `c=k/(k−2)`. Keep the background potential and coupling fixed and insert this marked radial factor:

`Mδ(u,v,p)=∫ℝ b exp(u+r(δ)b x−exp(u+b x)) exp(i p x) dx`.

Conjecture A: near `δ=0`, with `q=p/b`, the original integral equals `exp((cδ−iq)u) Γ(1−cδ+iq)`. Its normalized replica derivative is `c[u−ψ(1+iq)]`. This contains a replica-dependent Gamma argument and escapes the replica-independent spectator cancellation. Only its first jet is identified with the cited marked operator; no higher-order off-shell CFT claim is made.

Conjecture B: reality of a reflection-paired replica response could force zero momentum. Test the actual product `Mδ(p) Mδ(−p)`, including its derivative. Conjugation predicts a real response for every momentum, so this candidate may fail; the positive survivor would be the exact surviving oriented response and precise paired cancellation.

Conjecture C, exposed by B: the real mixed derivative survives the pairing and is strict away from zero. The exact formula is `∂p[∂δ log(Mδ(p)Mδ(−p))|0] = (2c/b) Im ψ′(1+ip/b)`. The installed trigamma series theorem gives a negative sign at positive momentum. Conjugation gives the opposite sign at negative momentum and zero at the origin. Thus this radial mixed response vanishes exactly at `p=0`, independently of `u`. This is the positive survivor; proving its vanishing on complete theta-source occurrences remains the producer obligation.

Neither radial factor is the full compact/nonzero-mode torus correlator. Same-winding OPE cancellation already shows why dropping compact contributions is invalid. No identification of the Fourier momentum with external BRST momentum is assumed.

The current source recheck matters: (3.28) is the coordinated temperature/dilaton variation, (3.29) is the marked operator, and the paragraph following (3.29) explicitly excludes the reflected wave from that prescription. The reflection-paired test below is a mathematical diagnostic, not a claim that this prescription includes such a wave. Holding the effective winding coupling `u` fixed in the radial calculation has not been identified with holding the physical asymptotic string coupling fixed.

Momentum reflection `p↦−p` is also distinct from the winding-charge sum `Wδ⁺+Wδ⁻`. The product of two radial Fourier integrals is not identified with that sum or with the complete integrated correlator.

## Work plan

- [x] Prove original marked integral near zero and its derivative in Lean scratch.
- [x] Audit momentum reflection and the proposed reality selector: B fails; the exact paired response and its coupling zero set are proved.
- [x] Extract exact positive response law: C is proved, including strict sign and the complete momentum zero set. Remaining full-source terms are identified as obligations, not evaluated.
- [x] Targeted leaf audit, axiom audit, lint, umbrella import, and frontier update.

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarMarkedRadialReplicaResponse.lean`, namespace `GaloisForLFunctions.RHTower`, 22 public theorems, all without hypothesis binders. The scratch file `/tmp/fzzp_marked_radial.lean` passes without warnings. The module is wired into `RHTower.lean`; no umbrella build is requested.

Final audit:

- `lake build GaloisForLFunctions.RHTower.FZZCigarMarkedRadialReplicaResponse`: PASS; only this leaf compiled (66 seconds), dependencies cached/replayed. No full or umbrella build.
- `lake env lean /tmp/fzzp_marked_radial_axioms.lean`: PASS for all 22 public theorems; only `propext`, `Classical.choice`, `Quot.sound`.
- `python3 scripts/formal_tools.py lint`: PASS; existing large-file warnings only.
- Installed proof body matches the passing scratch exactly. Tracked-file whitespace check passes.
- Logs: `/tmp/fzzp-marked-radial-build.log`, `/tmp/fzzp-marked-radial-axioms.log`, `/tmp/fzzp-marked-radial-lint.log`.

## Dependency-closed paper proof of the radial statements

For `r=1−cδ>0`, substitute `t=exp(u+b*x)` in the original integral. Its Jacobian is `b*t`, and the result is `exp((1−r−iq)u)∫₀∞t^(r+iq−1)exp(−t)dt`. Euler's Gamma formula gives A in a neighborhood of zero. Right-half-plane Gamma nonvanishing allows division by `M0`; differentiating the evaluated integral gives `c[u−ψ(1+iq)]`.

To identify the integrated marked operator, the Mellin differentiation theorem proves both absolute integrability and evaluation of `t^(iq) log(t) exp(−t)`. The exponential substitution transports this to the integrable logarithmic moment `y exp(iqy) exp(y−exp(y))`. The affine substitution `y=u+b*x` gives the moment of `(u+b*x)M0(x)` as `M0 ψ(1+iq)`. Subtracting the integrable term `u M0(x)` then gives the exact integrated first jet `∫−c*b*x*M0(x)dx=c[u−ψ(1+iq)]M0`. Consequently the derivative of the original integral equals the integral of the literal radial marked derivative, with no unproved interchange.

Real weights imply `Mδ(−p)=conj Mδ(p)`. The product rule therefore makes its normalized replica response `2c[u−Re ψ(1+iq)]`, real at every momentum. B fails. Its zero set is exactly `u=Re ψ(1+iq)`, so fitting the effective coupling cannot select vacuum. Differentiating this real response in momentum instead yields C. The convergent reciprocal-square series for trigamma has strictly negative imaginary part at `1+iq` when `q>0`; conjugation completes the zero-set classification.

The zero-set theorem is not a vanishing theorem. The missing full-source identity must account for the compact contribution, nonzero modes, normalization, physical coupling transport, external momentum map, and the independently fixed asymptotic phase frame. The radial mixed response can be canceled by another contribution; no bound or cancellation law for those contributions is proved here.

Next attack: identify the remaining effective-coupling and worldsheet-position integral from the literal source, and derive its mixed logarithmic response. Track the momentum-dependent logarithmic coupling moments induced by the radial Fourier weight together with the compact marked-charge term. The remaining factor must come from that source integral, not be defined as an arbitrary quotient and assigned a vanishing response. This will test the actual cancellation needed beyond the now-closed radial insertion.

## Current-source research

Deep searches `/tmp/fzzp-complete-marked-source-deep.json` and `/tmp/fzzp-marked-gamma-shift-deep.json` returned partial coverage (generations 823043/823045, pending). Their source arguments included the existing normalized-spectator no-go, while several high-ranked hits were unrelated replica or metric-source statements. No full FZZ producer was found among inspected hits. Exact source reads identified `Gamma_vertical_eq_fourier`, right-half-plane Gamma differentiation, and `ReflectedDigammaAnomaly.digamma_conj` for the concrete integral attack.

Primary physical source: [Halder–Jafferis, 2402.00932v3](https://arxiv.org/html/2402.00932v3), equations (3.28)–(3.33). The area operator is a first replica derivative at fixed asymptotic string coupling; the torus one-point function is not evaluated there.

Broad arXiv searches used `interlacing`, `duality`, and `fluctuation`, with June–September 2026 date terms. [Xu–Zhang, 2606.28797v1, June 27](https://arxiv.org/html/2606.28797v1), §2.3, uses finite independent positive semidefinite matrix families and a matching-polynomial identity. Its block construction suggests checking paired components together; applying its existence theorem to a fixed theta/FZZ source would still require an independently identified positive matrix family and source-preserving selection. Neither is supplied by the signed marked OPE. [Dagnino–Pasquali, 2608.15199v1, August 15](https://arxiv.org/html/2608.15199v1) concerns quotient/comprehension duality in relational doctrines; no analytic source or Ward estimate was identified. [Cheng–Liu–Shao–Xu, 2609.07446v1, September 7](https://arxiv.org/abs/2609.07446) was inspected at abstract level (HTML unavailable): its disorder universality assumes independent entries and moment matching, with no such FZZ ensemble identified.

Method retrieval used deep mode with all retrieval views: `/tmp/fzzp-marked-replica-methods.json`, partial generation 823047, pending coverage. The CLI has no separate `methods` mode. Several retrieved method descriptions referred only to definitions containing `deriv`; these are not differentiation-under-integral theorems. The actual bridge uses the checked Mellin derivative theorem and its convergence conclusion from the installed corpus.
