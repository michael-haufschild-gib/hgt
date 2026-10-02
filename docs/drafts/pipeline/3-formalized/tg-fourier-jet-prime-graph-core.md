# TG-C9.4: the literal prime-depth graph core

- **ID:** TG-C9.4-20261002-01a0
- **Stage:** 3-formalized
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetPrimeCore.lean`

## Exact result

For every prime p, the closure of the span of the literal columns
`(e_(p,n), M e_(p,n))` equals the entire maximal position-square graph on even physical
L2. Here M is the actual maximal multiplication operator by x²; all Euler amplitudes
remain in the source generators. This proves graph density, not merely ordinary L2
density.

Transport through the continuous assembly
`((f,Mf),(g,Mg)) ↦ ((f,g),(f+F g,M f+F M g))`
then identifies the closure of the finite prime-depth source graph with the closure of
the full even maximal-domain source graph. A separate exact membership theorem identifies
this graph with the previously defined Fourier–jet synthesis.

## Proof

Normalize the half-line source sum of orders zero and two by its actual nonzero Euler
amplitude. Its representative is `(1+r²)r exp(-(n+1)log(p)r)`. Orthogonality to every depth
gives all integer Laplace moments of the product of an L2 vector with the weighted base.
That product is L1, so the corpus's moment determinacy theorem forces it to vanish.
The base is nonzero on the half-line, proving weighted-source density.

The exact even-extension identity includes both sqrt(2) and the original depth-dependent
Euler amplitude. Actual maximal multiplication preserves evenness by AE reflection.
The bounded multiplier `B=(1+x²)^(-1)` gives the continuous graph map
`G h=(B h,h-B h)`. For every admitted f, `G(f+M f)=(f,M f)` exactly. Weighted-source
density supplies one graph inclusion; self-adjoint maximal multiplication and closedness
of the even carrier supply the reverse inclusion.

## Audit

- Scratch and production leaf checks: exit 0. Production command:
  `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetPrimeCore.olean GaloisForLFunctions/RHTower/PrimeBurnolFourierJetPrimeCore.lean`.
- Separate `#print axioms` audit of all four public theorems, including the subsequent
  literal-core recovery obstruction: exit 0; only
  `propext`, `Classical.choice`, `Quot.sound`.
- Wired into the RHTower umbrella without an umbrella build.
- The compiler emits one non-error `ring_nf` suggestion; no warning or hole is reported.
- Authoritative lint still reports unrelated unwired RHTower leaves; final session log
  records its exact current errors. No new TG leaf error.

## Frontier

C9.4 closes the literal arithmetic graph-domain gap. C9.5 also resolves the even
bounded-recovery question, with an independent parity proof and exact graph-core transfer:
`../5-failed/tg-fourier-jet-even-bounded-recovery.md`. The next source question is neutral
projection continuity in the stronger graph norm, not already excluded by output recovery.
Gamma–Xi identification, Hardy-index transfer and the sub-unit producer remain open;
RH is not proved or falsified.
