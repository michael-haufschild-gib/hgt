# BAG complete critical Mellin deformation — Lean audited

Paper proof: [exact deformation and sharp vertical bound](../2-fully-proven/bag-critical-mellin-deformation.md).
Source: `ChiRamanujanCriticalMellinDeformation.lean`, 306 lines,
12 public theorems and two definitions.

The actual one-balanced labelled term is its balanced value times
q^(1-s)/r^(1-s). The full masked source has the exact excluded-row formula;
the family on s=1+i*tau has no extra hypotheses. Its entire vertical norm
is bounded sharply by its balanced norm. All complementary prime factors,
both exclusions, and the allowed first/second label collision are retained.
The literal prime-power/exponential response is explicit. Four normalized
local rational identities cover the base, first tag, third tag and
coincident first/second tag for the two-variable moving-source problem.

Final production28970: `lake --old env lean` on this leaf with its own
`-o` target, exit0 and empty output. Axiom31311: all14 public declarations
use only `propext`, `Classical.choice`, `Quot.sound`. Index99071 passed;
all14 API names verified and the RHTower umbrella import occurs once.
Lint19933 reports unrelated unreachable modules and existing large-file
warnings; no finding in this leaf or forbidden proof declaration. Global
lint is NOT clean; its exact totals are recorded in the working log.

Scratch14567 checked the full masked formula; scratch76107 additionally
checked the sharp vertical bound. Scratch58299 checked all four general
local formulas. Required missing compiled dependencies were repaired with
individual foreground leaf audits only. No full or umbrella build,
subagent, numerical experiment, added axiom or heartbeat/recursion hack.

Scope: exact moving-source control on one balanced boundary, not the
growing two-variable near-pole limit or a signed physical cubic saving.
The paper argument for the joint profile and its outstanding formal
obligations live in P1 `bag-growing-near-pole-source`. Full axes saving,
growing moments/cofactors and common-height self-return remain open.
