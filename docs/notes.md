Current numbered live routes are:
C1, D2, E, G, L, N, O, P, Q, R.
Your list omits:
C1: singular Hedenmalm positivity or CCM trace-pairing/Hodge-sign construction.
N: uniform source-domain prime-normal sub-log-square estimate.
R: graded singular Cartier comparison; currently most developed corpus-native architecture.
Q is live but secondary; its fixed-Markov branch merges into P. S remains upstream infrastructure, not yet a complete proof route. A and M are terminal coordinates; remaining numbered routes are retired.

---

Exact external parent produces real delta: paracyclic geometry obeys d² = (1−T)S (Ponge), and 2026 Dold–Kan work characterizes cyclicity by identity monodromy on normalized chains. This matches two independent corpus shadows:
Route R: covariant square = triangle transport mismatch.
Route L: physical defect = (δ−1) times retained source residue.
So higher object is not ordinary sheaf/Hodge complex; it is a source-pointed para-S atlas. New open core: build one singular para-S comparison from honest cyclic source, with periodicity image nonzero. If constructed, source d²=0 forces target monodromy neutral, hence critical line. Updating active card to this sharper claim.

## route from cyclic homology research
It opens a genuinely different proof architecture, but not yet an RH proof. Its main impact is to rule out the previous “single spectral triple does everything” strategy.

The paper proves that one canonical object cannot simultaneously provide:

- an unbounded operator detecting the functional-equation orientation;
- a Lipschitz Real-corona projector;
- a local Connes–Moscovici formula for that projector.

The exact identity
\[
\|[D,e_R]x\|=\|D_{\mathrm{odd}}x\|
\]
shows why. Making \(e_R\) smooth forces the detecting odd component to be bounded. The unbounded spectral information must then move into the commuting even component, where local commutators cannot see orientation.

So the viable architecture is distributed:

\[
\begin{array}{c}
\text{even unbounded operator}\\
\text{absolute spectral energy}
\end{array}
\quad+\quad
\begin{array}{c}
\text{Clifford-corrected cyclic class }iL_c\\
\text{free-orbit orientation}
\end{array}
\quad+\quad
\begin{array}{c}
\text{multiplicity-sensitive cyclic trace}\\
\text{fixed real zeros}
\end{array}
\]

This changes the RH program in four ways.

1. Local index formulas cease to be the central route.  
   The canonical odd complete-divisor realization cannot support the required local projector class. The appropriate character must be nonlocal, entire, bivariant, or obtained through a Kasparov/Clifford product.

2. The functional-equation sign must be carried cyclically.  
   The untwisted Lefschetz correspondence is Real-even, so it cannot be the anti-Real corona character. The correct free-orbit object is \(iL_c\). This is not cosmetic: it identifies the required Clifford parity shift.

3. Absolute spectral energy and orientation must be separated.  
   An even operator can retain unbounded energies such as \(|\rho-\tfrac12|\), while the cyclic class retains which member of a reflection pair is being used. The old route tried to encode both in \(D\); the new route encodes them in different factors.

4. Ordinary \(K_0\) is insufficient at fixed zeros.  
   \(K_0\) sees only whether a fixed zero is present. Analytic rank requires primary multiplicity, supplied by a cyclic trace or equivalent local-length enrichment.

The resulting candidate RH architecture is:

```text
complete divisor
    ↓
even unbounded spectral cycle
    × Clifford-transgressed CCM class iL
    × fixed-sector multiplicity cycle
    ↓ bivariant/cyclic product
Weil explicit-formula pairing
    ↓ positivity theorem
Riemann hypothesis
```

The decisive missing theorem is a Clifford-corrected positivity bridge. One would need to construct a pairing \(\mathcal Q\) on the literal closed CCM quotient such that:

\[
\mathcal Q(f,f)=\text{Weil quadratic form}(f),
\]

with the free contribution represented by \(iL_c\), the fixed contribution counted with analytic multiplicity, and positivity following from genuine Hilbert-module or operator geometry—not from an assumption equivalent to RH.

A second essential theorem is reconstruction: prove that the distributed data

\[
(D_{\mathrm{ev}},\, iL_c,\, e_{\mathrm{fix}},\,\tau_{\mathrm{mult}})
\]

faithfully recover the complete signed divisor and explicit formula. Without reconstruction, splitting the information could lose exactly what RH concerns.

My blunt assessment:

- It closes the naive local spectral-triple route.
- It provides a new and structurally coherent nonlocal route.
- It substantially narrows what an RH proof object must look like.
- It does not yet overcome the fundamental positivity bottleneck.

The next hard target should therefore not be another spectral triple. It should be the construction of the Clifford-corrected bivariant product whose numerical pairing is exactly the Weil form, followed by a non-circular positivity theorem. If that succeeds, this paper becomes the architectural foundation of a new RH route rather than only a powerful obstruction theorem.


''''
Universal law and sharp sign classification now compile. Concrete outcome: \(L_c\) acts conformally on exact Weil pairing by positive \(|c|^{-1}\); even Xi reflection sector is a Hilbert norm square, odd sector its negative. This is non-circular scalar positivity with an exact maximal scope—and proves Clifford phases/flow cannot close RH sign gap by themselves.

###
Exact frontier now compiles too:
\[
\mathrm{RH}\iff \|E(F)-JE(F)\|^2\le \|E(F)+JE(F)\|^2
\quad\text{for every square-summable }F.
\]This removes ambiguity: remaining proof obligation is a source-geometric even-over-odd energy theorem. Gram positivity, Clifford phases, and Lefschetz flow are formally proved unable to supply it. Running one final target build and axiom check.