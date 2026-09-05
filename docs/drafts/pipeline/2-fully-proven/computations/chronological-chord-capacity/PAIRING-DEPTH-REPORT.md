# Perfect-pairing enclosure depth: numerical leads

**Outcome:** no validated numerical counterexample was found to depth-one stabilization in degrees three or four, or to depth-two stabilization in degree four. This finite search proves none of those universal statements. The known cubic reversal form has independently proved exact depth one; other coefficient combinations remain open.

## Question and method

For each noncrossing perfect pairing D on 2d ordered endpoints, form its gap polynomial `P_D=∏_(i,j∈D) Σ_(i≤q<j) g_q`. These give 5 generators in degree three and 14 in degree four. We searched coefficient combinations P for a signed variation-one probe with `|S^k P(g)|` greater than the monotone capacity, where S is total displacement.

The search ran on the authorized Runpod, in `/root/chronological-chord-capacity`, using 24 independent worker processes. Degree/depth pairs were (3,1), (4,1), and (4,2), with eight deterministic seeds each. BLAS/OpenMP environment variables were set to one thread before importing NumPy. SciPy 1.10.1 and NumPy 1.24.4 were used. The additional HiGHS `threads` option emitted `Unknown solver options: threads`; do not interpret the JSON's `library_threads` field as a measured backend thread count. The environment caps and 24-process pool are explicit in the source. The warning filter was broadened after the run to suppress this repeated diagnostic; numerical code is unchanged.

For each seed:

- A simplex grid plus 800 random monotone probes supplied 1,801 initial constraints in degree three or 2,516 in degree four.
- Linear programming selected coefficients against 40 signed target probes. Columns were scaled by their sampled maxima for conditioning.
- The best three candidates underwent at most ten rounds of monotone constraint exchange and optimization inside the signed probe's orthant, using analytic gradients and SLSQP.
- A first normalization check used 20,000 fresh monotone probes and local optimization.
- A separate validation used another 30,000 monotone probes per candidate, plus both the previously found monotone witness and the absolute value of the purported signed witness as optimization starts.

All 24 jobs completed. Three individual LP calls failed and were handled without treating their outputs as candidates. The search and validation are heuristic global searches; both can miss optima.

## Results and a rejected apparent violation

| Degree d | Depth k | Seeds | Largest validated response/monotone estimate |
|---|---|---|---|
| 3 | 1 | 8 | 0.9999999999999998 |
| 4 | 1 | 8 | 0.9999999999999980 |
| 4 | 2 | 8 | 1.0000000000000027 |

The last excess is floating-point scale. There is no robust violation in these results.

The initial degree-four, depth-two run at seed 6 reported a ratio of about 1.001605. Its signed probe was approximately `(0.2197901333,0,0,0.4505246355,0,0.3296852312,0)`, with only roundoff-sized negative entries. This is already a monotone probe. The apparent violation therefore exposed a missed monotone maximum. Including that probe in the monotone search removed the apparent excess. Future searches must always include the absolute signed candidate in monotone normalization, and should inspect negative mass before interpreting a ratio above one.

The LP/optimization loop frequently converged to monotone maximizers and positive-coefficient forms. This is a search limitation, not evidence that all signed coefficient combinations are controlled. A useful next step is a symbolic convex-hull or straightening argument for the five-generator cubic space, or a search deliberately constrained to retain nonzero reversal mass.

## Reproduction and artifacts

Execute on the Runpod, in the directory above:

```sh
python3 pairing_depth_probe.py
python3 pairing_depth_validate.py
```

Sources: `pairing_depth_probe.py`, `pairing_depth_validate.py`.
Raw results: `pairing-depth-results.json`.
Validated results: `pairing-depth-validation.json`.

Both result files were downloaded to this directory. No numerical output was used in Lean. The independently completed `SharpDepth.lean` and `PairingDepth.lean` results concern exact general-window sharpness and four-endpoint pairing depth zero, respectively; neither relies on this search.
