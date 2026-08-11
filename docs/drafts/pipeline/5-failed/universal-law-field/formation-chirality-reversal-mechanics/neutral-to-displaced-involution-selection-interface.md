# Neutral-to-displaced involution selection interface

- **ID:** ULF-FCRM-FAIL-1
- **Status:** \`[FALSIFIED AS RH TYPING] [MATHEMATICAL SUBTHEOREM TRUE] [POSITIVE SURVIVOR EXTRACTED]\`
- **Parent:** \`formation-cumulant-chirality-and-involutive-selection-law.md\`

## Failed claim

The first formation-chirality interface proposed to model functional-equation reflection by an
involution exchanging a neutral law \(P_0\) with one displaced law \(P_u\). Strict directed-KL
asymmetry correctly proves that such an involution forces \(u=0\).

The mathematical implication is true. Its proposed RH typing is wrong: a centered reflection should
exchange two opposite endpoints \(P_{c-a}\) and \(P_{c+a}\), not the center with one endpoint.
Therefore the original interface does not represent the required transformation law.

## Exact why

The proof used only chirality of the pair \((0,u)\). Nothing identified the physical reflection pair
with that asymmetric choice of basepoint. Moving the basepoint by declaration would fit the desired
conclusion rather than derive a source law.

## Strongest positive survivor

For a nonzero positive-jump compound-Poisson Esscher family and every admitted \(s<t\),

\[
D(P_s\Vert P_t)-D(P_t\Vert P_s)
=\int e^{-sx}K((t-s)x)\,d\nu(x)>0,
\qquad K(a)=a-2+(a+2)e^{-a}.
\]

Thus directed relative entropy reconstructs the entire formation order. It gives the correctly
centered consequence

\[
\Theta_*P_{c-a}=P_{c+a},\quad \Theta^2=1,\quad a\ge0
\Longrightarrow a=0.
\]

More strongly, every finite-order measurable symmetry transporting the full family induces an
increasing finite-order self-map of its parameter interval and therefore fixes every parameter.

## Representation lesson

Formation chirality is not a scalar defect attached to one privileged neutral point. It is an
orientation of the entire formation interval. Reflection selection must be formulated as rigidity
of order-reversing or finite-order actions on that oriented family.

## Status of survivor

The stronger pairwise chronology, centered selection, and finite-order rigidity laws are
dependency-closed on paper in the Stage-2 parent card. Lean status: not yet formalized.
