## formalize
/goal

work through all cards directly in docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge and formalize in lean any proven theorem in there.

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

skip cards that are not relevant for hypertranscendental functions nor for the riemann zeta function
before any build make sure you have the most efficient lean code, e.g. do not pull unnecessary modules.
for any nogo always try to find an interesting significant positive statement
- you can use subagents for read-only research into literature and our own research corpus
-
## research and formalize
/goal

work through this card: docs/drafts/pipeline/1-in-progress/watson-flatness-discharge.md

task: use the /hgt-fields-medalist skill to complete the research and formalize unconditionally all proofs in lean

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
