# Complete corrected BM Einstein source: experiment

RunPod symbolic calculation completed in 39.63 seconds using three workers on
32 cores (SymPy 1.13.3). All 96 background/first-order checks and the six known
angular-component checks passed. Exact outputs and code were downloaded; all
checksums match. The exact eight-file remote scratch directory was removed.
No experimental result is admitted into a Lean proof.

The experiment differentiates the full corrected metric before evaluating y=1
and B=1. All sixteen Einstein components are retained in each SS, VV and S+V
sector. SV is extracted by subtraction. The input correction and frozen question
are in [PROTOCOL.md](PROTOCOL.md).

## Findings

Every third scalar angular derivative cancels from every component in all three
channels. SS requires only S², S*dS and gradient squares. VV retains second-jet
squares in its orbit components. The corrected SV source has precisely eight
nonzero entries: time--angular and radial--angular components and their symmetric
partners. All orbit--orbit and angular--angular SV entries vanish.

The formulas below are a hand reorganization of the exact y=1 output. They are
candidates for an all-height tensor identity, not an independently proved
all-height source formula. Let

```
f = r²-1
lambda = (s+1)(s+2)
J = S*(Sy,-Sx)
N = y²*(Sx²+Sy²)
K = (partial_y N,-partial_x N)/2.
```

The mixed source has `E_tA=B²*(Pt*J_A+Qt*K_A)` and
`E_rA=B²*(Pr*J_A+Qr*K_A)`, with

```
Pt = s*[r²*(-s³+2s²+15s+8)+(s-1)*(s+1)*(s+2)²]/(2r⁵)
Qt = s*(s-1)*(r²-s-1)/(2r⁵)
Pr = s*[r²*(5s²+15s+4)+s*(s-1)*(s+2)²]/(2r⁴*f)
Qr = -s²*(s-1)/(2r⁴*f).
```

Since `B_r=s*B/(r*f)`, these coefficients suggest a conserved orbit current with
potential

```
W = B²*[(5s²+15s+4)/4+s*(s-1)*(s+2)²/(4r²)]*J
    -B²*s*(s-1)/(4r²)*K.
```

Specifically `r²*f*E_rA=partial_t W_A` and
`-r²*E_tA/f=-partial_r W_A`. These identities concern the candidate source current,
not existence, boundary admission, or extinction of its response.

In ingoing coordinates all rational source coefficients have finite horizon
values, as predicted by regularity of the input. Those values are saved explicitly
in each JSON file. They are generally nonzero. Regularity is a consistency check;
it does not solve the forced equation.

## Next proof obligation

The [complete vector master curl](../../3-formalized/hb-ingoing-correction-and-vector-master.md)
is now proved in Lean from the actual linearized Einstein contraction, independently
of this calculation, including all sixteen components and the exact sign and
normalization. Its constant and inverse-square radial factors have exact proved
images. The replacement angular correction also has proved radial endpoint
extension and boundary limits. Four leaf audits and all 22 new-theorem axiom
checks passed; the only axioms used are Lean's standard three.

The next obligation is the all-height nonlinear SV source identity, followed by
the specific angular resolvent and its physical causal admission. SS and VV
responses, nonlinear gauge, the actual causal left pairing and fixed-clock
extinction remain open. RH is not proved or falsified.
