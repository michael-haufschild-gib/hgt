# CCM-FU fixed-late greedy diagnostic

Numerical guidance only. No numerical result enters Lean. The containing
pipeline directory is the required computation archive, not a claim that
the selector or RH is proved.

Protocol: [middle selection with prescribed late order](../../../1-in-progress/ccm-fu-fixed-late-greedy.md).
Both fixed late relative orders retain every middle prime as an independent
choice and select the least next **complete** raw energy. Every prime is
processed. Every selected successor is regrouped directly; all signed
cofactor products enter the selection rule.

| M | Primes processed per policy | Initial energy | Increasing peak / initial | Decreasing peak / initial | Positive-gain states, increasing / decreasing |
|---:|---:|---:|---:|---:|---:|
| 512 | 97 | 311.5512693800 | 1 | 1 | 24 / 26 |
| 2048 | 309 | 4961.5003774403 | 1 | 1 | 91 / 70 |
| 8192 | 1028 | 79666.4609894105 | 1 | 1 | 180 / 131 |
| 32768 | 3512 | 1273163.8224173095 | 1 | 1 | 656 / 316 |

Peak includes the empty prefix. Positive-gain counts use the frozen screen
tolerance `1e-10 max(1,Q_empty)`; the independent-audit selection scans
the saved gains for strict positivity, as specified by the protocol.
At all eight paths this selects the same first nonscalar-positive state
as the screen's tolerance marker. Three repeated initial diagonals and
signed totals agree with saved joint-minimax data; its old policies were
not rerun. No factor-one crossing occurred. Finite passes establish no
cutoff-independent energy constant.

The frozen independent audit selects increasing-late policy at `M=512`,
before insertion index 20. Original time-sum coefficients are rebuilt
at 80 digits with independent trial factorization. All 41 allowed next
states are regrouped independently, confirming a strictly positive
minimum gain and the same selected prime 131.

- Original diagonal: `311.55126937994449`.
- Current energy: `35.02974706357684`.
- Selected next energy: `35.03330330902427`.
- Minimum gain: `0.00355624544742821`.
- Margin over second best: `0.00373583908558929`.
- Current head: `-0.0662891249504773`.
- Remaining late squares: `8.60233732245749`.
- Nonempty nonlate energy: `26.42301549303265`.
- Active nonscalar labels: 43.

The selected prime has only a head product. Every competing prime's head
increment and complete nonhead-product contribution are retained in
`audit.json`. In particular, prime 13 has positive head increment
`1.51416685498655`, nonhead products `1.48378516592664`, and full current
gain `1.28303957423449`. Negative scalar mergers can change that full
gain by changing the head. The saved path's six scalar insertions then
prime 13 produce an excursion returning below its starting energy;
the continuation was checked by screen regrouping, not by a second
high-precision audit. The unresolved analytic task is uniform control
of these excursions and of remaining prime supply through exhaustion.

Files:

- `screen.py`: four independent cutoff workers; increasing and decreasing policies.
- `source_screen.py`: unchanged imported source generator from joint-minimax diagnostic.
  Its old main program was never executed in this experiment.
- `baseline.json`: selected saved metadata with provenance; no regenerated baseline.
- `summary.json`: full prefix histories, candidate records if a crossing occurred, hashes and timings.
- `cutoff_*.json`: completed per-cutoff records, also contained in `summary.json`.
- `audit.py`, `audit.json`: independent original-sum audit and all allowed successors.

All mathematical computation ran on the specified RunPod. Screen runtime
`2.7044426 s`; audit runtime `0.0921103 s`. Each used at most four workers,
single-threaded BLAS/OpenMP/MKL, a 90-second internal deadline and
100-second outer timeout. Neither deadline fired. Results are high-precision
floating values, not interval certificates.

SHA-256 checked locally against RunPod:

```text
screen.py       615cd354fa5d6d07b229e6386ca7f3452b9436bcbc57fe793e9e51768870dc59
source_screen.py 77bcc9058e05d01f20fdbe49536ab800b5a046512324cb2e5e2605cde2313427
baseline.json   18815e50f58be4d450d2d01d88c3c7d4d2e02ef8eae7e3fc672b61faadad1375
summary.json    0d94afe4d3695afc431cc07c3b11b5d45b4dd8cf47834b0e17e585718782d2bd
audit.py        45fc862235333e3b68132428121a5e3f22fd89265dcf250dbe12146013f945f9
audit.json      ba15af5c59b1894707b60073a964bea38fd7f719e49102ee2675a9e8ab7340d3
cutoff_512.json 851b0311c0c2f8f88438d4a319ca05b0842c6c570e13a1d084eb7af3fa2cd973
cutoff_2048.json d7c1cd7b8ac530879555428e130e815b4fe02bd5e2f5d5e5fbb08533a6b0af25
cutoff_8192.json d758a29be9982125b56ace98e49179fd03b0cac8a10dc92c51f9ac4b08796566
cutoff_32768.json f6f3d85e57a084dd2699437ace358ede3707226851dac4553a564c3db49cf7bf
```

Owned remote directory removed after download and hash verification.
All computation processes terminated normally. No Lean process was started;
no build, umbrella build or repeated axiom check was run. Frontier map
remained read only.
