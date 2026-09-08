# HB native cusp source projection

- **ID:** hb-native-cusp-source-projection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** [cusp spectrum and causal continuation](../1-in-progress/hb-cusp-spectrum-and-causal-continuation.md)
- **Statement:** Exact constant Fourier component of the entire original complex squared source, including cutoff derivatives; its actual native Hilbert pairing; sharp native cusp integrability of both physical indicial branches.

RH remains open. Chain: literal theta cusp → Xi occurrence → retained spin-two
source → original causal response and left-QNM pairing → independent
Hawking-clock extinction → RH.

## Exact source and infinite-series proof

The mean is the actual width-one Lebesgue integral over `(-1/2,1/2]`. Put

`a_N(u,y)=coefficient(u,0,N)*sqrt(y)*K_u(2*pi*(N+1)*y)`.

The coefficient and order-dependent Bessel function are the original full
angular-series definitions. At every positive height, the existing full-series
majorants prove `sum ||a_N||<infinity`, and their product proves absolute
convergence of the complex square sum. Write
`wave_N(x)=exp(2*pi*i*(N+1)*x)+exp(-2*pi*i*(N+1)*x)`.
The original tail is exactly `2*sum_N a_N*wave_N`, retaining both signs.

The integral of an integer character is one at frequency zero and zero
otherwise. Thus `mean(wave_N)=0` and `mean(wave_N*wave_M)=2` for `N=M`, zero
otherwise. The full product expansion has summable majorant
`(2*||a_N||)*(2*||a_M||)`. This justifies both the infinite product and its
termwise integration; diagonal selection then gives

`mean(tail)=0`,

`mean(tail^2)=mean(S^2-P^2)=8*sum_N a_N^2`,

`mean(S^2)=P(y)^2+8*sum_N a_N^2`.

Here S is the full scalar and P its original two-Weyl-power principal part.
The principal–tail cross terms disappear only after their mean is proved zero.
This is a complex bilinear square, not a Hermitian squared norm. The result
asserts neither positivity nor nonvanishing of the displayed series.

## Full cutoff and original Hilbert pairing

For an actual Xi occurrence q and either original branch, let L be the original
quadratic source parameter and `C(y)=cutoffResponse(q,branch)(0,y)`. This literal
height function is globally smooth, including the region where it vanishes.
Its full chart Laplacian is `y^2*C''(y)`. Consequently the complete residual
`F=(L/2)*S^2-(Delta-L)(cutoffResponse)` has mean

`Fbar(y)=(L/2)*(P(y)^2+8*sum_N a_N^2)-(y^2*C''(y)-L*C(y))`.

This identity holds at every positive height. Above height three, where the
cutoff is one, the principal response equation reduces it to
`Fbar(y)=4*L*sum_N a_N^2`. The transition region is retained in the global result.

For every constructed `CuspHeightTest h` in the original operator domain,

`<h.operatorVector,forcingVector>=integral_(y>2) conj(h(y))*Fbar(y)/y^2 dy`.

The proof begins with integrability of the two actual L2 vectors' inner
product. The original native measure is transported through the upper-half-plane
embedding with its exact density. The test vanishes below height two, so its
support lies in the full width-one cusp rectangle. Measure-preserving transport
and justified Fubini yield the displayed pairing. No source integrability,
operator-domain membership, modularity or critical-line premise is supplied
for this actual source theorem.

## Physical cusp branch classification

For every complex p, the native squared-norm density of `y^p` is
`y^(2*Re(p)-2)`. Its integral over `y>2` exists exactly when `Re(p)<1/2`.
The endpoint is excluded by the exact improper-power criterion.

Both original homogeneous cusp powers `y^(w+2)` and `y^(-w-1)` solve
`Delta_H f=(w+1)*(w+2)*f`. Their density integrability chambers are respectively
`Re(w)<-3/2` and `Re(w)>-3/2`. The two literal doubled Xi source rates are
`w=2*(rho-2)` and `w=2*(-rho-1)`. The already proved open-strip location of every
Xi occurrence gives `-4<Re(w)<-2` for both, without RH. Therefore the first
power has finite cusp mass there and the second does not.

This classifies the powers' native cusp densities. It does not assert that
these noncompact powers are global operator-domain vectors, that the right-hand
chamber is the retarded chamber, or that the forced response has a nonzero
coefficient of either power. The original causal convergence domain, continued
global response and resulting homogeneous coefficient remain to be derived,
including the compact modular scattering contribution. Physical gauge,
remaining response sectors, the actual left-QNM pairing and independent clock
extinction remain open.

## Lean surface and audit

Modules are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawkingBM`; declaration namespace is `RHTower.D4BMCuspProjection`.

| Module suffix | New public theorems |
|---|---:|
| `CuspMeanCharacter` | 5 |
| `CuspPairedFourier` | 7 |
| `CuspSourceMean` | 7 |
| `CuspCutoffMean` | 5 |
| `CuspNativeSourcePair` | 2 |
| `CuspIndicialSelection` | 6 |

All six development scratch checks passed without diagnostics. Each exact
canonical leaf passed its final `lake build <module>` audit through an isolated
package using the existing import caches; only the requested new leaf compiled.
The twelve new olean/ilean copies match the audited artifacts, and the six
imports are wired once into the umbrella without building it. One scratch axiom
audit checked only these 32 new public theorems: `propext`, `Classical.choice`
and `Quot.sound` only. No previous theorem was re-audited. No numerical experiment,
computational certificate, dependency rebuild, full build or umbrella build was
used. The source index was refreshed; scoped whitespace and import checks passed.

`scripts/formal_tools.py lint --check-generated` reported the unrelated concurrent
module `RHTower.DivisorSourceEntire` unreachable from its theorem-area umbrella,
plus existing large-file warnings. That module was present before this work and
was left untouched. All six new HB modules have exactly one umbrella import each.
Owned scratch files were removed; no owned Lean/Lake process remains. The frontier
map was not edited.
