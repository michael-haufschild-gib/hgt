# Bernoulli prime-energy guidance

Frozen question: [PE5](../../../5-failed/ccm-fu-bernoulli-prime-energy.md). Process each prime independently with probability one half and compare average retained energy with the original diagonal.

`screen.py` first reuses every saved subset state through32, then computes the half-probability mean head and diagonal at dyadic cutoffs `2^5,...,2^18`. It uses the already established complete-block/terminal-block channel formula; no greedy search or exponential subset enumeration is repeated. Output: `screen.json`.

The averaged energy through32 stays below the diagonal. The necessary lower bound from squared mean head first exceeds the diagonal in the dyadic screen at1024, by a ratio about1.36655. The ratio reaches about30.4082 at262144. This does not locate the first failing integer.

`audit.py` independently evaluates every defining half-order sum at1024 with80-digit arithmetic, computing divisor counts and prime factorizations independently. Output: `direct-audit.json`. It confirms mean-square excess `457.863502688528174234073139716...` over diagonal `1249.109767690844815361248296555...`. The final signed sum's squared/diagonal ratio remains about0.11031 there.

Each new run took under one second. These files are numerical guidance only, never Lean proof inputs. The analytic obstruction on the linked card uses the fractional Euler factor and zeta's pole, without numerical channel bounds or a Tauberian asymptotic.
