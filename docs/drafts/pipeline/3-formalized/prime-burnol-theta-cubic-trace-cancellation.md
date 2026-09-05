# Literal Burnol–theta cubic trace cancellation

RH chain tested: literal Burnol–theta modular current → compatible singular sigma-trace with oriented unit mass → completed Xi/Fredholm horizon → RH. Gates sought: `ORD+LAND+COMP`.

## Exact result

[LEAN-PROVED] Let `sigma : A →+* A`, `tau : A →+ G`, with `tau(xy)=tau(sigma(y)x)`, and let `q²=q`. For any `p`,

`tau(A(sigma(q),q,p)) = tau((sigma(q)-p)^3 - (sigma(q)-sigma(p))^3)`,

where `A(r,q,p)=(r-p)^3-(r-q)^3-(q-p)^3`.
Thus a modular-fixed reference makes this cubic sigma-trace exactly zero.

Proof: `tau(sigma(x))=tau(x)`. Put `r=sigma(q)`; then `r²=r` and
`(r-q)^3=r-q-rqr+qrq`. Twisted cyclicity gives `tau(qrq)=tau(rqr)`, hence `tau((r-q)^3)=0`. Apply sigma-invariance to `(q-p)^3` and subtract. No positivity, finite dimension, continuity, or spectral premise is used.

[CORPUS] `primeBurnolDoubledModularAction_neutral` fixes the literal neutral reference. `sourceFramedElement_idempotent` supplies `q²=q`.

[LEAN-PROVED] Consequently **every** compatible sigma-trace kills `primeBurnolThetaCubicDefect` and `primeBurnolThetaCubicAnomaly`, at every grade and finite packet, despite nontrivial holonomy.

Stronger exact source cutoff law: put `c=D`, `q=UpU⁻¹`, `r=c⁻¹qc`, `d=r-q`, `b=q-p`. Then
`c A(r,q,p)=[b³,c]-[q,c d²]`.
Proof: `d²q=qd²`, `cd=qc-cq`, giving `cd³=[q,cd²]`; fixedness of `p` gives `c(r-p)³=b³c`. For every matrix cutoff `e` commuting with `p,q`, therefore `e c A=[b³,ec]-[q,ecd²]` has trace zero. Every literal prime-depth scalar mask `e=diag(w_i I₂)` commutes with both `p,q`. This also kills the filtered source trace, which need not itself satisfy the global sigma-trace identity.

For an arbitrary additive reporter, the exact remaining term is reference drift plus `epsilon((q-p)³)-epsilon(q)-delta(q sigma(q),q)`, where `epsilon(x)=tau(sigma(x))-tau(x)` and `delta(x,y)=tau(xy)-tau(sigma(y)x)`. This identifies the actual trace defects required of a different completion.

Scope: kills a nonzero sigma-trace of this literal exact cubic and all finite prime-depth scalar-mask trace regularizations. It does not kill domain-restricted traces where the displayed products are not admitted, a source-moving reference, or all Route P. Nuclearity of a commutator alone does not justify infinite-dimensional trace cyclicity.

## Audit and survivor

Checked exact source bodies: `PrimeBurnolThetaModularHolonomy`, `SourceFrameModularHolonomy`, `ModularCubicProjectionTransgression`; exhaustive references to `sourceFrameCubicDefect` and `IsSigmaTrace`. Existing generic nonzero rational witness does not have this constrained `(sigma(q),q,p)` triple with fixed `p`.

[LITERATURE] Twisted trace convention and modular Fredholm parent theory: Rennie–Sitarz–Yamashita, *Twisted Cyclic Cohomology and Modular Fredholm Modules* (2013), §§2–4, https://sigma-journal.com/2013/051/sigma13-051.pdf. Their modular index requires equivariant domain/projection data; it is not an arithmetic Xi admission theorem. No scientific-priority claim for elementary algebra above.

Positive survivor: exact reference-drift localization, not another zero-trace restatement. To carry a unit, source must generate nonzero reference drift or a genuine defect in twisted cyclicity/domain passage; noncommuting frame alone cannot do it.

[OPEN CORE] Construct such source-produced drift or boundary trace defect, with coefficient-faithful Xi admission and signed budget. No such producer proved here.

## Formal status

`formal/GaloisForLFunctions/RHTower/PrimeBurnolThetaCubicTraceCancellation.lean`, main source theorem `primeBurnolThetaPrimeDepthWeightedCubicTrace_eq_zero`; positive identities `cubic_modular_trace_defect_localization` and `weighted_sourceFrameCubicDefect_commutators`. Scratch and exact leaf `lake env lean` checks pass; leaf olean produced. Four scratch axiom audits use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import integrated by root; no umbrella/full build. This is scoped cancellation, not a completed RH chain or new modular-index parent theory.
