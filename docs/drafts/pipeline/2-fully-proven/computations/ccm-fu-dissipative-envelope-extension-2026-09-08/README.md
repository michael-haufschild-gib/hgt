# Nonempty dissipation versus successor admission

Finite RunPod diagnostic; no numerical result enters Lean.
[Frozen protocol](../../../1-in-progress/ccm-fu-dissipative-envelope-extension.md).

## Result

Among all 8,860 saved states at cutoffs 1..32, 8,176 proper states satisfy
complete successor admission. Exactly one admits no next prime that both
preserves admission and does not increase nonempty energy.

At M=25, take P={2,7,11,13,17,19,23}. Only primes 3 and 5 remain.
Both choices preserve admission and strictly lower the complete successor
envelope. Both strictly increase V=Q−H².

| Quantity | Value |
| --- | ---: |
| Original diagonal | 0.840036942680707… |
| Current energy and envelope | 0.576384756052300… |
| Current V | 0.030551414101697… |
| V gain after 3 | 0.004759303636129… |
| V gain after 5 | 0.002655650445266… |
| Envelope after 3 | 0.569122106115641… |
| Envelope after 5 | 0.558745888586281… |
| Final energy | 0.294536867909024… |

The same state is the only nonempty-energy local trap in the entire saved
cube, including nonadmitted states. It is reachable from empty through
steps satisfying both proposed conditions. Nevertheless every cutoff
through 32 also has some complete path satisfying both conditions.
Thus the local extension claim fails at a reachable state; existence of
a more selectively chosen complete path survives this finite diagnostic.

## Independent source audit

The first failure of each local assertion is the same state. Its
independent 80-decimal-digit reconstruction confirms both failures.
The four retained fibres are approximately

`H=-0.738805347808611`,
`a=F{3}=0.008181375865577`,
`b=F{5}=0.013864781941782`,
`c=F{3,5}=0.174046680555390`.

The exact nonempty gains are `2bc−a²` and `2ac−b²`.
The exact full-energy gains are `2Ha+2bc` and `2Hb+2ac`.
The negative head releases enough square energy to pay the mandatory
growth in the nonempty field. Both complete remaining orders also
decrease full energy at their final step.

All reconstructed coefficients, fields, candidate gains and envelope
witnesses are retained in summary.json. The primary screen regenerated
no arithmetic channels. It recovered heads from stored isolated
late-prime energy differences and cross-checked every late anchor.
The independent audit reconstructed the defining divisor defects and
half-order sums directly.

## Execution and provenance

- Host: supplied RunPod SSH endpoint.
- Eight worker processes, one-thread numerical libraries.
- Successful screen and independent audit: 0.0615 seconds.
- Internal deadline: 50 seconds; external timeout: 60 seconds.
- One initial attempt reached the audit but failed because Python 3.8
  lacks int.bit_count. Replaced it with bin(mask).count('1') and reran
  the unchanged mathematical protocol. No cutoff or assertion was tuned.
- Script and result hashes match remote copies.
- Remote directory /tmp/ccm-dissipative-puo6l9dA and its three owned files
  were removed after successful download. The foreground process exited;
  no owned worker remained.

| File | SHA-256 |
| --- | --- |
| screen.py | 9db8f2a183054b79a8bf221bd7e7bcbc5ff4d770adb8aaa02b10deb4aaf56e20 |
| summary.json | a504e72a9fc9b2f822677276cad0672ea8594efddd322c2191900c0a7ce2d979 |
| Input subset-states.csv | ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9 |

## Mathematical consequence

This rejects universal extension by simultaneous V dissipation and
successor admission. It does not refute plain successor extension, the
existence of specially chosen dissipative paths, SD1 or RH.

The positive survivor is compensation by the actual head square during
forced transverse growth. A general two-coordinate bound gives a further
sharp boundary: one next V is at most 3/2 of current V, and equality is
attained by nonempty coordinates (1,1,2). The [analytic Lean certificate](../../../3-formalized/ccm-fu-transverse-dissipation-trap.md)
now proves the literal arithmetic witness and this sharp boundary without
numerical premises. All five new public theorems passed their axiom audit.
