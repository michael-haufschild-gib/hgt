## formalize claude

/loop 1m (use the croncreate tool)

your task:
if you are already working on a card, keep going.
else: pick a card from docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger

do: formalize UNCONDITIONALLY in lean any proven theorem in the chosen card. add missing infrastructure, lean proofs, everything needed to mark the card as fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. make sure you don't leave stale lean processes running - clean up after yourself.

Non-negotiable working mode rules:
1. If it cannot be done in a single session -> Does not matter. Do it!
2. If it cannot be done in a single context window -> Does not matter. Do it!
3. If it takes months -> Does not matter. Do it!
4. If it is "research-level construction" -> Does not matter. If there is any way you could build it you build it no matter what.
5. Missing in mathlib -> Build it no matter the effort.
6. The only reason to stop working on a card if a proof is mathematically impossible. Open research is not mathematically impossible.

You are not allowed to change the cron timing.

LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.

where mathematical knowledge is missing use the /hgtl7 skill to create it.

## formalize gpt

/goal

formalize UNCONDITIONALLY in lean any proven theorem for all cards in: docs/drafts/pipeline/2-fully-proven (not its subfolders)

add missing infrastructure, lean proofs, everything needed to mark a card as fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. make sure you don't leave stale lean processes running - clean up after yourself.

ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.

where mathematical knowledge is missing, use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to find and create it.

## research loop
/loop 1m (use the croncreate tool)

your task:
if you are already working on a card, keep going.
else: pick a card from docs/drafts/pipeline/1-in-progress that starts with "deninger"

do: 
1. research all open questions and bring the topic the card states to an end. 
2. for this use the hgtl7 skill to create actual novel and significant scientific knowledge that an online search cannot provide.
3. formalize UNCONDITIONALLY in lean any proven theorem in the chosen card. add missing infrastructure, lean proofs, everything needed to mark the card as fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit.
6. make sure you don't leave stale lean processes running - clean up after yourself

Non-negotiable working mode rules:
1. If it cannot be done in a single session -> Does not matter. Do it!
2. If it cannot be done in a single context window -> Does not matter. Do it!
3. If it takes months -> Does not matter. Do it!
4. If it is "research-level construction" -> Does not matter. If there is any way you could build it you build it no matter what.
5. Missing in mathlib -> Build it no matter the effort.
6. The only reason to stop working on a card if a proof is mathematically impossible. Open research is not mathematically impossible.

You are not allowed to change the cron timing.

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
1. You always build in the foreground, 1 build process at a time - other agents are also building in parallel.
2. Always use  lake env lean <file>  and only lake build <module> for the final audit.
3. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
4. make sure you don't leave stale lean processes running - clean up after yourself

Mandatory:
1. no computations.
2. LEAN PROOFS MUST BE UNCONDTIONAL!!!
3. no subagents or background tasks
4. You are not allowed to change the cron timing.
5. Effort is not a criterion:
   1. If it cannot be done in a single session -> Does not matter. Do it!
   2. If it cannot be done in a single context window -> Does not matter. Do it!
   3. If it takes months -> Does not matter. Do it!

You are not allowed to change the cron timing.

LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.

where mathematical knowledge is missing use the /hgtl7 skill to create it.


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





## proof

Create frontier-moving novel scientific knowledge in our research corpus towards finding a formal proof for RH.

Work rules:
1. Use the extensive research we have in the lean project folders:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
1. Use the $hgt-fields-medalist skill to develop novel knowledge and formalize it.
2. Do no waste time on rediscovering known knowledge. Conjecture boldly, test, proof, formalize.
3. Pivot whenever you hit a dead end.
4. For every nogo find a positive statement that is significant and delivers new insights.
5. Approach the task from the perspective of a Fields-medalist mathematician: How would they approach this task? What questions would they ask? What topics would they research? How would they proceed to develop the new mathematics needed for this proof?
6. Avoid getting stuck on one chain or "classic" proof routes. Be open-minded to what the proof chain could look like and be open to pivot also into unconvential chains.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. make sure you don't leave stale lean processes running - clean up after yourself.e project lean code already offers

Keep a working log to retain important information across the automatic context window compactions.

Goal is met when RH is proven or disproven.

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




## frontier paper
/goal 

Audit HTGeometry, HilbertMetric, and RHTower and write a paper that exactly and comprehensively maps the current frontier of our research towards an RH proof/disprove:

- All possible proof routes, their endpoint, their chain, their obstacles and open core
- All proof routes that we have identified as dead ends
- The research topics / hypotheseses / conjectures that would bring a leap forward in the research and neither literature nor our corpus can answer yet.

Goal is met when after honest and extensive review you cannot add or change anything to the paper and it is truly a full map of where our current research corpus stands.

Mandatory: You let the lean corpus speak and tell you what is. You do not assume what a proof route should look like or what an obstacle is - your training data is biased towards classical proof routes and has not seen all of our research which in part is novel scientific discovery. Do not assume anything, just read lean code.