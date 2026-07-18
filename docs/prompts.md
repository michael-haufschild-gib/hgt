## formalize
/goal

work through all cards directly in docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge that start with "constraint-prolate" and formalize in lean any proven theorem in there.
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm-pair-weil-polarization-law.md
rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function

before any build make sure you have the most efficient lean code, e.g. do not pull unnecessary modules.
do not constantly build and fix and build and fix, be efficient with lean and this laptop's resources.

skip cards that are not relevant for hypertranscendental functions nor for the riemann zeta function
before any build make sure you have the most efficient lean code, e.g. do not pull unnecessary modules.
for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corpus


## research and formalize
/goal

perform exhaustive research for these cards one by one:
- docs/drafts/pipeline/1-in-progress/hurwitz-sonin-tropical-loop-rh.md
- docs/drafts/pipeline/1-in-progress/symmetric-prime-gamma-contour-hermite-rh.md
- docs/drafts/pipeline/1-in-progress/suzuki-coupled-error-boundary-energy-attack.md

task: use the hgt-fields-medalist skill to complete the research and formalize unconditionally all proofs in lean. discover new knowledge, do not stop at current SOTA research.

rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function

- before any build make sure you have the most efficient lean code, e.g. do not pull unnecessary modules.
- for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corpus

## physics
/goal
use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill and conjecturing to create a sufficiently broad theory or solve a central problem in the field of hypertranscendental functions. your approach is the lense of a physicist - we assume that the landscape of hypertranscendental functions is the mathematics of a fundamental physical process or phenomen.

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function

research rules:
- check from time to time the lean code for new additions and pipeline cards for new additions that aren't yet formalized
- for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corpus

## ht

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research new and significant scientific knowledge about the nature of hypertranscendental functions and the mathematical landscape they are part of.

research rules:
- check from time to time the lean code for new additions and pipeline cards for new additions that aren't yet formalized
- for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corpus

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function

## ht to rh

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research and formalize a proof that the riemann hypothesis is false.

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function

research rules:
- constraint vs flow rule is softened - whatever brings the proof is acceptable
- novelty gate is softened - it does not matter if it is new or not, if it delivers the proof
- check from time to time the lean code for new additions and pipeline cards for new additions that aren't yet formalized
- for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corpus

## physics

use literature research and our existing lean code base in formal/GaloisForLFunctions/HTGeometry and formal/GaloisForLFunctions/RHTower to identify interesting and useful value relations between our codebase and other topics that can do the following:
- expand a theorem
- close gaps between theorems
- connect theorems into new theorems
- discharge a hypothesis or prop interfaces

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

topics:
- everything "quantum ..."
- everything physics
- everything chemistry
- unified field theory, gravity, weak and strong force, electromagnetism
- cosmology, black holes, singularities, many world
- mathematical sound fringe theories

go deep, also consider arxiv papers
for any nogo always try to find an interesting significant positive statement
do this until nothing new can be found


## grouping

Use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research this topic:

Our RH proof research so far always cumulated into the question "we need one object that combines a lot of different constraints". But what if the zeros on the critical line are not a combined class, they just appear like it. In fact the zeta zeros divide into different groups of zeros that are all forced onto the critical line for different reasons.

Your task is to follow this rabbit hole and find possible groups and prove the RH for single groups of zeros instead of all zeros.

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

- for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corpus


## new research

Based on the current status report of our research in docs/reports/rh-status-1707.md, use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research the research programme number 3 outlined in docs/reports/rh-status-1707.md

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

other rules:
- for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corp


Research and create progress and new knowledge and ultimately create the RH proof following this program: docs/reports/rh-proof-shape-1707.md

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.


the goal is met when no further proof or conjecture is possible and no meaningful contribution or pivot can be made


## proof

Build on the extensive research corpus we have gathered in the lean code base formal/GaloisForLFunctions and "paper" research pipeline docs/drafts/pipeline and expand it into delivering a formal proof of the Riemann Hypothesis.

Use the hgt-fields-medalist skill, bold conjecturing, wide literature research, and anti-theatre tests to develop the missing new scientific knowledge to complete the task.

Approach the task from the perspective of a Fields-medalist mathematician: How would they approach this task? What questions would they ask? What topics would they research? How would they proceed to develop the new mathematics needed for this proof?

Avoid getting stuck on one chain or "classic" proof routes. Be open-minded to what the proof chain could look like and be open to pivot also into unconvential chains.

Use subagents as you please, but be mindful of resource limitations of this laptop when it comes to lean builds - there are several other agents also working on the lean codebase (this is a competition between claude fable, openai gtp 5.6 sol and moonshot kimi k3, all having the same instructions to test who gets the farthest in discovering new scientific knowledge or even delivering the proof).

lean rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

keep a working log to retain important information across the automatic context window compactions:
claude fable: logs/rhproof-fable.md
openai gpt: logs/rhproof-gpt.md
moonshot ai kimi k3: logs/rhproof-kimi.md

Non-negotiable: This is a multi-month research task with unclear outcome. Never use effort estimation to decide against doing something. Nothing here can be done in one session. Keep going. Never stop.


## Lean work
Use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research this topic:

lean folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function

Our lean corpus in the rhtower and htgeometry folders contains thousands of theorems and nogos. Your task is to "connect the dots". Find and formalize opportunities to:
1. Create a general law that subsumes several theorems into a more general law.
2. Advances the lean body using value relations and value reflections.
3. Closes gaps between theorems.
4. Discharges hypothesis and prop interfaces.

All these must be significant and ideally novel science.

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself.
2. Be efficient, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code.
4. lean proofs must be unconditional
5. always check first what the project lean code already offers
6. no computations.

Goal is met when there is after full review truly nothing you can add or change anymore.
