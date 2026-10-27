# Polar gluing of Lorentzian forms

Object: finite symmetric real forms sharing a vector of positive square. Write
`a_i = Q_i[e]`, `b_i(x) = Q_i(e,x)`, `A = Σ a_i`, `b = Σ b_i`.

Research target: exact obstruction to adding locally hyperbolic forms, including a constructive
repair and an associative law for assembling local pieces. No arithmetic signature is assumed.

Corpus lead: `HTGeometry.schurComplement_sum_eq` in
`HTGeometry/QuotientFusionProjectionGenesis.lean` already proves the scalar weighted-variance
identity. Reuse it. ALG already proves the hyperplane criterion, domination, CND closure,
trickle-down, and failure of unrestricted addition. The new content must be the matrix correction,
its signature theorem, and its composition law, not another scalar variance identity.

Proposed invariant: the positive form
`V(x) = Σ a_i (b_i(x)/a_i - b(x)/A)^2`.
The reserve of the sum equals the sum of local reserves minus `V`. Thus a useful arithmetic
decomposition must pay dispersion of local degrees, not merely prove each local sign.

Proposed construction: subtract the matrix of `V` from `Σ Q_i`. This preserves its anchor row,
adds local reserves exactly, and is hyperbolic for locally hyperbolic inputs. For rank-one inputs
this is the exact correction, and uncorrected closure requires alignment of normalized rows.

Composition target: correction within blocks plus correction between their sums equals correction
of the whole family. This gives a decomposition independent of grouping.

Arithmetic boundary: no equality, domination, or source estimate identifying this constructed form
with the full Weil intersection form is available. Such identification remains a research target.

Status: research and Lean development; no paper-only theorem claimed proved.
