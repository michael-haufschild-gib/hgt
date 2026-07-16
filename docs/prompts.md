#formalize
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

#research and formalize
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
