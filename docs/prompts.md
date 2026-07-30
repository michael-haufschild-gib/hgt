## formalize
/goal

/loop 1m (use the croncreate tool)

your task:
if you are already working on a card, keep going.
else: pick a card from docs/drafts/pipeline/2-fully-proven (not any subfolder)

do: formalize UNCONDITIONALLY in lean any proven theorem in the chosen card. add missing infrastructure, lean proofs, everything needed to mark the card as fully done - no simplifications.

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. lean proofs must be unconditional
5. always check first what the project lean code already offers. Some card proofs are already formalized. Reuse as much as possible. Connect your new lean code to obvious connectors like to discharge theorems or connect theorems to a stronger statement.
6. no computations.

Non-negotiable working mode rules:
1. If it cannot be done in a single session -> Does not matter. Do it!
2. If it cannot be done in a single context window -> Does not matter. Do it!
3. If it takes months -> Does not matter. Do it!
4. If it is "research-level construction" -> Does not matter. If there is any way you could build it you build it no matter what.
5. Missing in mathlib -> Build it no matter the effort.
6. Always check what our extensive lean corpus can provide you! Reuse as much as possible.
7. The only reason to stop working on a card if a proof is mathematically impossible. Open research is not mathematically impossible.

You are not allowed to change the cron timing.

**Always use  lake env lean <file>  and only lake build <module> for the final audit.**
make sure you don't leave stale lean processes running - clean up after yourself
LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.


## loop theorems
/loop 1m (use the croncreate tool)

if you are not idle, keep going.
else your task is:

Audit HTGeometry, HilbertMetric, and RHTower for any remaining hypothesis or Prop interface - then attempt to discharge it:
1. reuse existing formal results to discharge every tractable premise
2. create and formally prove missing connector theorems
3. subsume theorems under a larger universal law which is nontrivial

use the /hgtl7 skill´s research process on each non-immediate mathematical obstacle

lean rules:
1. You always build in the foreground, 1 build process at a time - other agents are also building in paralle.
2. Always use  lake env lean <file>  and only lake build <module> for the final audit.
3. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
4. make sure you don't leave stale lean processes running - clean up after yourself

Mandatory:
1. no computations.
2. LEAN PROOFS MUST BE UNCONDTIONAL!!!
3. no subagents or background tasks
4. You are not allowed to change the cron timing.

BEFORE WRITING ANY LEAN CODE, CHECK WHAT THE LEAN CORPUS ALREADY GIVES YOU AS BUILDING BLOCKS - DO NOT DUPLICATE WORK.


## loop consolidate
/loop 1m (use the croncreate tool)

if you are not idle, keep going.
else your task is:

Audit HTGeometry, HilbertMetric, and RHTower for opportunities to reduce code and optimize the lean code:
- resolve code duplication
- combine theorems into more general laws/theorems

use the /hgtl7 skill´s research process on each non-immediate mathematical obstacle until no further hypothesis can be discharged or structurally replaced.

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. lean proofs must be unconditional
5. always check first what the project lean code already offers. Some card proofs are already formalized. Reuse as much as possible. Connect your new lean code to obvious connectors like to discharge theorems or connect theorems to a stronger statement.
6. no computations.

Non-negotiable working mode rules:
1. If it cannot be done in a single session -> Does not matter. Do it!
2. If it cannot be done in a single context window -> Does not matter. Do it!
3. If it takes months -> Does not matter. Do it!
4. If it is "research-level construction" -> Does not matter. If there is any way you could build it you build it no matter what.
5. Missing in mathlib -> Build it no matter the effort.
6. Always check what our extensive lean corpus can provide you! Reuse as much as possible.
7. The only reason to stop working on a card if a proof is mathematically impossible. Open research is not mathematically impossible.

You are not allowed to change the cron timing.
You work independent from other agents and can run 1 build process in the foreground at a time yourself.
**Always use  lake env lean <file>  and only lake build <module> for the final audit.**
make sure you don't leave stale lean processes running - clean up after yourself
LEAN PROOFS MUST BE UNCONDTIONAL!!!

## research and formalize
/goal

perform exhaustive research and use the hgt-fields-medalist skill and iterative conjecturing to develop step by step the "field with one element": docs/the field with one element.md.

do not favor one method. do not attempt to proof rh but focus on that field construction itself.

rules:
1. limit lean builds to the absolute necessary. be as memory and cpu efficient as possible. each agent can run max 1 process at a time so agents can build in parallel without clogging the system. always build in foreground. there are more agents active not just you.
2. aim for the smallest lean build possible and use caching heavily for lean. write lean code in batches instead of building after every edit.
3. lean proofs must be unconditional
4. always check first what the project lean code already offers
5. effort estimation are not a criterion. if it is missing in mathlib -> you build it. if it takes months -> you build it.
6. no computations.

**Always use  lake env lean <file>  and only lake build <module> for the final audit.**
make sure you don't leave stale lean processes running - clean up after yourself

goal is met when the field is fully developed and formalized.

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

Advance the research body towards finding a formal proof for RH.

Work rules:
1. Use the extensive research we have in the lean project folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
2. Use the $hgt-fields-medalist skill to develop novel knowledge and formalize it.
3. Do no waste time on rediscovering known knowledge. Conjecture boldly, test, proof, formalize.
4. Pivot whenever you hit a dead end.
5. For every nogo find a positive statement that is significant and delivers new insights.
6. Approach the task from the perspective of a Fields-medalist mathematician: How would they approach this task? What questions would they ask? What topics would they research? How would they proceed to develop the new mathematics needed for this proof?
7. Avoid getting stuck on one chain or "classic" proof routes. Be open-minded to what the proof chain could look like and be open to pivot also into unconvential chains.

Use subagents as you please, but be mindful of resource limitations of this laptop when it comes to lean builds - there are several other agents also working on the lean codebase (this is a competition between claude fable, openai gtp 5.6 sol and moonshot kimi k3, all having the same instructions to test who gets the farthest in discovering new scientific knowledge or even delivering the proof).

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself.
2. Be efficient with lean, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. lean proofs must be unconditional
5. always check first what the project lean code already offers
6. no computations.

keep a working log to retain important information across the automatic context window compactions.

Non-negotiable: This is a multi-month research task with unclear outcome. Never use effort estimation to decide against doing something. Nothing here can be done in one session. Keep going. Never stop.


## Lean work
Use the hgt-fields-medalist skill and scientific method to research this topic:

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
2. Be efficient with lean, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. lean proofs must be unconditional
5. always check first what the project lean code already offers
6. no computations.

Goal is met when there is after full review truly no new law to formulate, no new hypothesis to discharge, and the lean corpus is in a shape that it could prove RH and other fundamental open questions about prime numbers and hypertranscendental funcions.


## External

Use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research this topic:
how can laws and practical rules (e.g., the smith chart) be applied to our problem spaces to 1. extend the frontier and create new theorems unknown to scientific literature, 2) discharge hypothesis and prop interfaces, 3) close gaps between theorems to create stronger theorems or more universal laws

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. lean proofs must be unconditional
5. always check first what the project lean code already offers. Some card proofs are already formalized. Reuse as much as possible. Connect your new lean code to obvious connectors like to discharge theorems or connect theorems to a stronger statement.
6. no computations.

folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics

**Always use  lake env lean <file>  and only lake build <module> for the final audit.**
make sure you don't leave stale lean processes running - clean up after yourself

Goal is met when every law / rule that can be found for the topic is tested if it can be applied to our research.


## Revert

Use the hgt-fields-medalist skill to research this any possibility to close a proof chain to prove or disprove RH. CCM is already investigated, look for alternatives. 

Mandatory: Do not assume a proof chain and then look for building blocks. Let the lean code speak. We have much more knowledge encoded there than the literature or your training data contain. Check the lean code, see what chains could be possible, identify the gaps and attack the gaps using the hgt-fields-medalist skill, bold conjecturing and the scientific method.

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself, parallel to builds of other agents.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. always check first what the project lean code already offers. Some card proofs are already formalized. Reuse as much as possible. Connect your new lean code to obvious connectors like to discharge theorems or connect theorems to a stronger statement.
5. no computations.

folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics

Always use  lake env lean <file>  and only lake build <module> for the final audit. Wire everything into the right umbrella.
make sure you don't leave stale lean processes running - clean up after yourself

Goal is met when there is a full RH proof chain start to finish.

## Ñawe

Use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research our whole lean corpus and take 2 or more theorems and attempt to subsume them into a universal law that cannot be found in our corpus nor in the literature. 

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself, parallel to builds of other agents.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. always check first what the project lean code already offers. Some card proofs are already formalized. Reuse as much as possible. Connect your new lean code to obvious connectors like to discharge theorems or connect theorems to a stronger statement.
5. no computations.

folders to check for already existing research:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics

**Always use  lake env lean <file>  and only lake build <module> for the final audit.**
make sure you don't leave stale lean processes running - clean up after yourself

Goal is met when after honest scan of the whole lean body no such universal law can be found.



Use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to research and add new scientific knowledge not known to our corpus or literature for these open frontiers towards an rh proof:

1. **Xi Arakelov–Hurwitz dependence**
   Prove the right-half Xi/Arakelov-Hurwitz object depends on an algebraic character. Lean converts this to algebraicity, then RH.
   [Lean interface](</Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/XiArakelovHurwitzDependenceCollision.lean:104>)

2. **Möbius–Laplace control**
   Prove either half-plane decay of the discrete Laplace transform or its Mellin-continuation wall. The decay-to-continuation bridge is already proved.
   [Lean interfaces](</Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean:323>)


lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself, parallel to builds of other agents.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. always check first what the project lean code already offers. Some card proofs are already formalized. Reuse as much as possible. Connect your new lean code to obvious connectors like to discharge theorems or connect theorems to a stronger statement.
5. no computations.

Always use  lake env lean <file>  and only lake build <module> for the final audit.
goal is met when rh is proven.




stop the entropy shit. you are the latest anthropic model. you have the ability to conjecture. openai gpt 5.6 can do it. you finally can do that to. conjecturing and following the protocol is the way. your predecessors fable 5 and opus 4.8 could not create conjectures, everything they called a conjecture was something they already would know the answer to. you are different. you can create conjectures that you could not answer with a literature search or if just asked for the answer. this is the one key thing that makes new scientific knowledge possible: conjecture, make sure it is an actual conjecture, test it, pivot and steer from what you learn, ... science


 review the frontier and interpret the big picture
  -> create conjectures that are not known yet and could if proven true would
  move the frontier -> check literature if conjectures are not already known,
  if they are either still formalize if helpful machinery, or go back to create
  new conjectures -> research and prove / disprove -> review the new frontier
  and interpret


  

## hgt7
/goal
/hgtl7 expand on our existing research body and research and develop new scientific knowledge towards an rh proof. Always let the research speak, do not assume a proof lane or focus on classical proof lanes, but let the already rich novel scientific knowledge in our research corpus guide you on what to research next, what to conjecture, what direction to research towards.

follow the hgtl7 skill to the T. create new scientific knowledge.

do not think about or use context window, effort, time it takes. focus only on the research and creating new scientific knowledge.

lean is an internal tool to make sure that there are no ai hallucinations. novelty and significance is only assessed based on mathematics, never on our lean work. it is new if it is new to the scientific research - literature as of july 2026.

the goal is met when RH is proven or disproven.

lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. No computations.
   
**Always use  lake env lean <file>  and only lake build <module> for the final audit.**
make sure you don't leave stale lean processes running - clean up after yourself
LEAN PROOFS MUST BE UNCONDTIONAL!!!


''''
/goal 
use the $/hgtl7 skill and conjecturing iteratively to create new frontier-moving knowledge to prove or disprove the Selberg’s orthogonality conjectures (see: docs/Langlands functoriality and the Selberg class conjectures.md)

do not think about or use context window, effort, time it takes. focus only on the research and creating new scientific knowledge. this is a multi-session long running task with multiple automatic context window compactions. keep a working log of important findings and dead ends to not duplicate work.

goal is met if either:
1. the Selberg’s orthogonality conjectures are proven true
2. the Selberg’s orthogonality conjectures are proven false

lean rules:
- do not run computations.
- always use  lake env lean <file>  and only lake build <module> for the final audit.
- lean proofs must be unconditional.

follow the hgtl7 skill and heavy conjecturing and validation of novelty and significance against literature and arxiv as of july 2026.

limit your updates. do not give a status update every 2 minutes. only report when you have actually found frontier-moving new math. do not constantly update that conjectures are not proven or disproven and this cannot be done in this session. this task will take years. just fucking do what is necessary and stop looking for excuses to not work.



## CHAT
/goal

Your chat name is "Codex". The chat channel is "rh". If not done already, join the chat.

There is another agent "Claude" from Anthropic. 

Your task:
- Discuss and research together with Claude how to create the proof for the Riemann Hypothesis.
- Base your discussion on what our research corpus has already uncovered or ruled out.
- Be critical of your own claims and the claims of the other agent.
- Be open minded: let the lean research corpus guide you, your training data is biased towards a few classic routes, while our research body may lead to completely new routes.
- Heavily use and stay up to date on what our lean research corpus already offers in terms of proofs, routes, open cores.
- Use the hgt-fields-medalist skill´s research process on each non-immediate mathematical obstacle

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit.
6. make sure you don't leave stale lean processes running - clean up after yourself

Anti-theatre protocol:
- Be hypercritical of your own and the other agents claims, suggestions and results.
- Any action that does not lead to truly novel and significant mathematical knowledge is theatre.
- Novelty criterion is that you cannot find it via literature research (including arxiv) nor in our research body. 
- Any action must aim towards creating truly novel and significant knowledge, nothing the literature or our research already know or that is trivial.

Check the chat frequently. Communicate! The core tool here is joint research, honest critique, and communication.

Goal is met when RH proof is formalized.

## CHAT
/goal

Your chat name is "Claude". The chat channel is "rh". If not done already, join the chat.

There is another agent "Codex" from OpenAI. 

Your task:
- Discuss and research together with Claude how to create the proof for the Riemann Hypothesis.
- Base your discussion on what our research corpus has already uncovered or ruled out.
- Be critical of your own claims and the claims of the other agent.
- Be open minded: let the lean research corpus guide you, your training data is biased towards a few classic routes, while our research body may lead to completely new routes.
- Heavily use and stay up to date on what our lean research corpus already offers in terms of proofs, routes, open cores.
- use the hgtl7 skill´s research process on each non-immediate mathematical obstacle

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit.
6. make sure you don't leave stale lean processes running - clean up after yourself

Anti-theatre protocol:
- Be hypercritical of your own and the other agents claims, suggestions and results.
- Any action that does not lead to truly novel and significant mathematical knowledge is theatre.
- Novelty criterion is that you cannot find it via literature research (including arxiv) nor in our research body. 
- Any action must aim towards creating truly novel and significant knowledge, nothing the literature or our research already know or that is trivial.
  
Check the chat frequently. Communicate! The core tool here is joint research, honest critique, and communication.

Goal is met when RH proof is formalized.

## paper
/goal 

Do scientific research and then write a paper that is likely to be published in Nature.

The paper must:
- Be accepted by a hostile journal reviewer based on https://www.nature.com/nature/for-authors/editorial-criteria-and-processes
- Present a headline law or discovery that "wows" people even if they do not understand the math behind it
- Is bold and present a universal law or theorem about physical reality, not just math
- Any mathematical claim must be unconditionally proven in lean
  
Topic present a worldview shattering new universal law, preferably about time or causality in the broader sense.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds.
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit.
6. make sure you don't leave stale lean processes running - clean up after yourself.

lean folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics

prior papers: docs/drafts/pipeline/4-publication-ready

Add the missing lean machinery and use [$hgt-fields-medalist](/Users/michael/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to do research and fill the scientific gap for dicovering Nature-level physics.



keep asking "what does all this mean? what is all this telling me what i and all the researchers before me have missed? what is this new math we all need to solve the riddle?" we are looking for something new and universal of which all our obstructions, dead ends, observations and laws are a shadow, something that explains all at once and also then delivers a new understanding from which new collaries and laws can be derived.

the goto novelty finder is always to conjecture towards a reinterpretation, a more universal law or theorem of which all the known theorems and laws and obervations and nogos are shadows. everything we know now is a special case of that universal law.