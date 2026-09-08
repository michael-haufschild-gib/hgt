# HB native cusp response coefficients

- **ID:** hb-native-cusp-response-coefficients
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** [cusp spectrum and causal continuation](../1-in-progress/hb-cusp-spectrum-and-causal-continuation.md)
- **Statement:** The actual native response has its full forced cusp ODE, absolutely convergent indicial source moments, exact boundary/source reconstruction, and a constructed dominant asymptotic coefficient.

RH remains open. Chain: literal theta cusp → Xi occurrence → retained spin-two
source → original causal response and left-QNM pairing → independent
Hawking-clock extinction → RH.

## Original response equation

Let h be the previously constructed globally smooth representative of the native
modular energy response to the full residual F. Its planar field is literally
`globalResponse(q,branch) composed with ofComplex`. Define its horizontal mean
`m(y)=integral_(-1/2,1/2] h(x+i*y) dx`.

For every positive-height chart field, continuous first derivatives have a
uniform bound on a compact horizontal/height rectangle. This supplies the
integrable majorant for differentiation under the actual mean. Applying the
same proof to the vertical derivative gives the second mean derivative.
The actual modular translation makes h horizontally periodic; differentiating
that identity and applying the fundamental theorem cancels the horizontal
second derivative exactly.

Averaging the original global classical equation therefore gives
`y^2*m''(y)-L*m(y)=Fbar(y)` at every positive height, where Fbar is the actual
global source mean. For y>2, the whole horizontal integration interval lies in
the closed modular cell. The source is then exactly the previous literal
forcing mean, including the complete cutoff region and all opposite Fourier
pairs. No smoothness, periodicity, response equation or source identification
premise is supplied for the actual Xi response theorem.

## Source moments and actual flux limits

Put `w=physicalRate(q,branch)`, `a=w+2`, `b=-w-1`, and `d=b-a`.
Both roots obey `p*(p-1)=L` and sum to one. The proved physical bounds
`-4<Re(w)<-2` give d nonzero for every Xi occurrence.

For either root p define the actual Wronskian flux and its source density:

`J_p(y)=y^p*m'(y)-p*y^(p-1)*m(y)`,

`g_p(y)=y^(p-2)*Fbar(y)`.

Differentiating the literal expression and using the actual mean equation gives
`J_p'(y)=g_p(y)`. Both functions retain their original values; no boundary flux
is prescribed. For positive endpoints A,Y, the fundamental theorem yields
`J_p(Y)-J_p(A)=integral_A^Y g_p`.

Above height three, the exact source mean is `(L/2)*mean(tail^2)`. The existing
full signed-tail theorem bounds both `y^p*tail` and `tail` uniformly over the
whole horizontal strip. Their product and the width-one norm integral bound
therefore give `|g_p(y)|<=C/y^2`. This proves absolute integrability on the
infinite cusp for both roots. No Hermitian replacement, positivity assumption,
finite Fourier truncation or numerical estimate is used.

The actual flux has the proved limit
`ell_p=J_p(4)+integral_4^infinity g_p`.
At every y>3,
`J_p(y)=ell_p-integral_y^infinity g_p`.
The boundary value J_p(4) retains m(4) and m'(4), so compact modular geometry and
the cutoff region remain in the coefficient through the original global solution.

## Exact reconstruction and dominant coefficient

The two flux equations give, without losing their Wronskian normalization,
`m(y)=(y^b*J_a(y)-y^a*J_b(y))/d`.
This also gives exact finite-height reconstruction from both boundary fluxes
and both finite source integrals.

Define `A=-ell_b/d` and `B=ell_a/d`. The complete original mean is exactly

`m(y)=A*y^a+B*y^b+(y^a*integral_y^infinity g_b-y^b*integral_y^infinity g_a)/d`

for y>3. Since `Re(a-b)<0`, the positive-real-base complex power `y^(a-b)`
tends to zero. Combining this with both proved flux limits gives the actual
asymptotic identity `m(y)/y^b -> B`.

These are coefficients of the original native energy response. The original
causal convergence chamber, its continued global response and any resulting
change of coefficients remain open. The native norm has now been transferred
to the actual mean and proves B=0; see
[native energy selection](hb-native-energy-selection-and-frequency-transport.md).
A has not been determined. Physical gauge, other response sectors, the actual
left-QNM pairing and independent Hawking-clock extinction remain separate
obligations.

## Lean surface and audit

Modules are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawkingBM`; namespace is `RHTower.D4BMCuspResponse`.

| Module suffix | New public theorems |
|---|---:|
| `CuspMeanDerivative` | 4 |
| `CuspMeanLaplacian` | 4 |
| `CuspResponseMean` | 5 |
| `CuspResponseFlux` | 4 |
| `CuspFluxMoment` | 3 |
| `CuspFluxReconstruction` | 5 |
| `CuspDominantCoefficient` | 1 |

The seven development scratch leaves passed. Each exact canonical leaf passed
its final `lake build <module>` audit through an isolated package using existing
import caches; only the requested new leaf compiled. All fourteen new olean/ilean
copies match the audited artifacts. Seven imports are wired exactly once into
the umbrella without building it. One scratch axiom audit checked only these
26 new public theorems: `propext`, `Classical.choice` and `Quot.sound` only.
No previous theorem was re-audited. No numerical experiment, computational
certificate, dependency rebuild, full build or umbrella build was used.

The source index was refreshed and scoped whitespace/import checks passed.
`scripts/formal_tools.py lint --check-generated` reported the unrelated concurrent
module `RHTower.DivisorSourceEntire` unreachable from its theorem-area umbrella,
plus existing large-file warnings. That module predated this work and was left
untouched. Owned scratch and audit files were removed; no owned Lean/Lake process
remains. The frontier map was not edited.
