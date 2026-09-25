# CLG/TTF compact determinant: integer proof-format experiment

**Purpose:** Test whether clearing rational denominators reduces the cost of the still-open full determinant identity. This is a proof-engineering experiment, not a new sign scan or a mathematical positivity result.

**Execution:** Runpod `root@157.157.221.29:27094`, Python 3.8, seven worker processes. Inputs were the seven existing `PolynomialODEEvenCompactMoment{Zero,One,Two,Three,Four,Five,Six}.lean` files. The script extracts exact coefficient tables, chooses one positive denominator for each moment and emits candidate integer-numerator definitions and symbolic Lean equality proofs. Outputs were downloaded; remote scratch was removed.

`generate.py` is the executed generator. `output/metadata.json` records all denominators and term counts. `output/*.lean` records emitted candidates. Generation verifies no theorem. Every emitted identity subsequently passed `lake env lean`, taking approximately 3–6 seconds per file. Checked modules are wired into the HTGeometry umbrella without building it.

The denominators are `230400`, `8294400000`, `298598400000000`, `10749542400000000000`, `128994508800000000000000`, `13931406950400000000000000000`, and `501530650214400000000000000000000`. Their arithmetic supplies no sign premise. The determinant check uses a fourth power of a shared denominator, including the correction's factor 19, before expanding integer numerators.

**Current boundary:** Positive lower polynomial, every nonnegative discarded remainder, and literal source normalization are checked. Full determinant incidence and actual compact positive-definiteness remain unproved until their independent Lean checks pass.
