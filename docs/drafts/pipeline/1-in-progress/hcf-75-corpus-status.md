# HCF 75%: Current State

- **Receiver:** five-center charge `Q ≥ 44/5`; deep copies `o(N)`; source ceiling `cN+o(N)` gives `N₀ ≥ (1-5c/22)N-o(N)`.
- **Threshold:** `c=11/10` gives asymptotic `75%`; any `c<11/10` gives eventual pointwise `75%`. Old `21/100` target gives `419/440` asymptotically.
- **Formal:** `HedenmalmCriticalFeatureSevenTenthsSharpAsymptoticReceiver.lean`.
- **Open:** prove source-only five-center Plemelj covariance ceiling `≤11N/10+o(N)`.
- **Known structure:** phase averaging removes nonzero aliases; source covariance + compact source boundary `=4πN+o(N)`; boundary `=4πN₀+o(N)`.
- **No-gos:** divisor-selected endpoints; fixed transverse shifts; finite entire Euler gauges; norm-square-only/unpaired/absolute-alias bounds; scalar diagonal minorants; rank--trace window refinement; squarefree Möbius critical-clock control.
