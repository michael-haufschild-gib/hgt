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

before any build make sure you have the most efficient lean code, e.g. do not pull unnecessary modules.


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
- goal is a paper worthy a fields medal
- conjecture boldly, think big
- use anti-theatre and novelty gates to avoid work that's just rediscovery of known knowledge
- novelty gate refers to literature, not to our own research corpus
- check from time to time the lean code for new additions and pipeline cards for new additions that aren't yet formalized

## ht

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to develop and formalize a "unified field theory" of hypertranscendental functions that can explain the different obstructions we have met in all our different rh proof chains and resolve them.

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
- goal is a paper worthy a fields medal
- conjecture boldly, think bg
- use anti-theatre and novelty gates to avoid work that's just rediscovery of known knowledge
- novelty gate refers to literature, not to our own research corpus
- check from time to time the lean code for new additions and pipeline cards for new additions that aren't yet formalized


## ht to rh

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research how the existing and ongoing research into hypertranscenental functions can be applied to develop an rh proof.

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
- goal is the rh proof no matter what
- constraint vs flow rule is softened - whatever brings the proof is acceptable
- novelty gate is softened - it does not matter if it is new or not, if it delivers the proof
- conjecture boldly, think bg
- use anti-theatre and novelty gates to avoid work that's just rediscovery of known dead ends
- check from time to time the lean code for new additions and pipeline cards for new additions that aren't yet formalized
