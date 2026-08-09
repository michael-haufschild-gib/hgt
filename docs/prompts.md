## formalize claude

/loop 1m (use the croncreate tool)

your task:
if you are already working on a card, keep going.
else: pick a card from these: docs/drafts/pipeline/2-fully-proven/universal-law-field (oldest card by modified at file date first)

do: formalize UNCONDITIONALLY in lean any proven theorem in the chosen card. add missing infrastructure, lean proofs, everything needed to mark the card as fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
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

## formalize goal
/goal

formalize UNCONDITIONALLY in lean any proven theorem from these cards: 

  
add missing infrastructure, lean proofs, everything needed to mark a card as fully done and move it to stage 3 of the pipeline - no simplifications. 

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
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

LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK. 

where mathematical knowledge is missing use the /hgtl7 skill to create it.+

GOAL IS MET WHEN ALL CARDS ARE FULLY FORMALIZED AND CAN BE MOVED TO STEP 3 OF THE PIPELINE. NO SHORTCUTS OR FAKING IT!

## formalize gpt

/goal

formalize UNCONDITIONALLY in lean any proven theorem for:
- docs/drafts/pipeline/2-fully-proven/universal-law-field/abelian-zeta-gas-two-observable-divisor-dictionary-and-condensation-wall-law.md

add missing infrastructure, lean proofs, everything needed to mark a card as fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Do not run full builds, build missing module olean when needed.
6. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
7. make sure you don't leave stale lean processes running - clean up after yourself.

ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.

where mathematical knowledge is missing, use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to find and create it.

goal is met when cards are fully formalized and moved to step 3 in the pipeline.

## loop theorems claude
/loop 1m (use the croncreate tool)

if you are not idle, keep going.
else your task is:

Audit lean corpus for opportunities to reuse existing formal results to discharge or simplify a hypothesis, prop interface, premise.

lean corpus:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics
  
lean rules:
1. You always build in the foreground, 1 build process at a time - other agents are also building in parallel.
2. Always use  lake env lean <file>  and only lake build <module> for the final audit.
3. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
4. make sure you don't leave stale lean processes running - clean up after yourself

Mandatory work rules:
1. no computations.
2. LEAN PROOFS MUST BE UNCONDTIONAL!!!
3. no subagents or background tasks
4. You are not allowed to change the cron timing.
5. Effort is not a criterion:
   1. If it cannot be done in a single session -> Does not matter. Do it!
   2. If it cannot be done in a single context window -> Does not matter. Do it!
   3. If it takes months -> Does not matter. Do it!

LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.

where mathematical knowledge is missing use the /hgtl7 skill to create it.


## goal theorems gpt

/goal
Audit lean corpus for any remaining hypothesis or Prop interface - then attempt to discharge it:
1. reuse existing formal results to discharge every tractable premise
2. create and formally prove missing connector theorems
3. subsume theorems under a larger universal law which is nontrivial
4. use the $hgt-fields-medalist skill´s research process on each non-immediate mathematical obstacle

lean corpus:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics

read only corpus:
- formal/GaloisForLFunctions/QuantumAlg for lean related to quantum algorithm around prime numbers
- formal/GaloisForLFunctions/QECLean.lean for lean related to Quantum Error Correction
- formal/GaloisForLFunctions/PNTPlus.lean for lean related to Prime Number Theorem
  
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

where mathematical knowledge is missing use the $hgt-fields-medalist skill to create it.

## research paper

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to create novel and significant new knowledge about:
- Brown–Susskind’s full growth–plateau–recurrence law
- the black hole interior volume paradox
- Quantum Recurrence

wtf are you wasting time on novelty research for single steps. your goal is clear: Prove, unconditionally, Brown–Susskind’s full growth–plateau–recurrence law for ordinary time-independent local Hamiltonians, and prove that maximal complexity occurs while locality remains permanently distinguishable from Haar randomness.

collect enough novel and significant knowledge to write a paper that meets the publishing requirements of Nature: the paper must report a fundamental new insight or startling discovery that significantly shifts the scientific conversation across multiple fields.

research rules:
- use heavy conjecturing
- always check that you do not play theatre and actually are creating new knowledge
- focus on hard problems

add missing infrastructure, lean proofs, everything needed to get this route fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent. You can run builds in parallel to other agents, but only 1 at a time.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Do not run full builds, build missing module olean when needed.
6. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
7. make sure you don't leave stale lean processes running - clean up after yourself.

goal is met when paper is written and passes a hostile review that confirms that the paper is on a quality level to be published in Nature.

## research Route

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to create novel and significant new knowledge about:

collect enough novel and significant knowledge to overcome the obstacles. do not get married to a specific route. our research corpus is ahead of your training data and literature, never assume how the solution must look like but let our research corpus guide you. 

research rules:
- use heavy conjecturing
- always check that you do not play theatre and actually are creating new knowledge
- focus on hard problems, NO THEATRE, NO INFRASTRUCTURE, EVERY STEP MUST DELIVER PROGRESS
- take a step back and look at the big picture and conjecture how you could reinterpret everything we know so far and where the reasons we got stuck are shadows of a higher universal principle
- pivot when necessary.

add missing infrastructure, lean proofs, everything needed to get this route fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent. You can run builds in parallel to other agents, but only 1 at a time.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Do not run full builds, build missing module olean when needed.
6. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
7. make sure you don't leave stale lean processes running - clean up after yourself.

folders to check for already existing research:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics
- formal/GaloisForLFunctions/QuantumAlg for lean related to quantum algorithm around prime numbers
- formal/GaloisForLFunctions/QECLean.lean for lean related to Quantum Error Correction
- formal/GaloisForLFunctions/PNTPlus.lean for lean related to Prime Number Theorem
  
goal is met when lean corpus has an uncondtional formal proof for rh.


## Revert

Use the hgt-fields-medalist skill to research this any possibility to close a proof chain to prove or disprove RH.
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


lean rules:
1. You work independent from other agents and can run 1 build process in the foreground at a time yourself, parallel to builds of other agents.
2. Be efficient with lean builds, do not constantly do minor edits and build, but batch changes and builds.
3. Optimize lean code. Use caching and limit rebuilds of dependencies to only what is truly necessary for your work.
4. always check first what the project lean code already offers. Some card proofs are already formalized. Reuse as much as possible. Connect your new lean code to obvious connectors like to discharge theorems or connect theorems to a stronger statement.
5. no computations.

Always use  lake env lean <file>  and only lake build <module> for the final audit.
goal is met when rh is proven.


## frontier paper
/goal 

Audit HTGeometry, HilbertMetric, and RHTower and write a paper that exactly and comprehensively maps the current frontier of our research towards an RH proof/disprove:

- All possible proof routes, their endpoint, their chain, their obstacles and open core
- All proof routes that we have identified as dead ends
- The research topics / hypotheseses / conjectures that would bring a leap forward in the research and neither literature nor our corpus can answer yet.

Goal is met when after honest and extensive review you cannot add or change anything to the paper and it is truly a full map of where our current research corpus stands.

Mandatory: You let the lean corpus speak and tell you what is. You do not assume what a proof route should look like or what an obstacle is - your training data is biased towards classical proof routes and has not seen all of our research which in part is novel scientific discovery. Do not assume anything, just read lean code.



## loop 
/loop 1m (use the croncreate tool)

if you are not idle, keep going.
else your task is:

search our htgeometry and rhtower lean corpus for any opportunity of a value relation or value reflection that can do either of these:
1. allows to discharge of simplify a tractable premise
2. create and formally prove missing connector theorems
3. subsume theorems under a larger universal law which is nontrivial
4. opens a new proof route for the riemann hypothesis
5. simplifies the proof burden towards the riemann hypothesis

then formalize everything useful in lean.
  
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

## research paper only

/goal 

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to create novel and significant new knowledge about this problem:

"All our attempts and different routes towards a proof of the Riemann Hypothesis indicate that the key to the problem is to develop a completely new, unknown to literature, geometry or topology in which all the obstacles we have met translate into a new representation object that becomes clear and solvable."

research rules:
- you can and should also check lean corpus, but not write lean  
- for creating that missing knowledge use a heavy loop of conjecturing -> proof or fail -> conjecturing -> proof or fail -> conjecturing -> ...
- always check that you do not play theatre and actually are creating new knowledge
- focus on hard problems, NO THEATRE, EVERY STEP MUST DELIVER PROGRESS
- take a step back and look at the big picture and conjecture how you could reinterpret everything we know so far and where the reasons we got stuck are shadows of a higher universal principle
- pivot when necessary.
- use arxiv search with wide keywords and look for latest preprints - search is good when it returns a lot of useless results. never search for stupid narrow searches that are basically "please give me the solution to my problem". 

collect enough novel and significant knowledge to overcome the obstacles. do not get married to a specific route. our research corpus is ahead of your training data and literature, never assume how the solution must look like but let our research corpus guide you. 

DO NOT WRITE LEAN CODE OR BUILD LEAN. ONLY WRITE PAPER PROOFS FOR STEP 2 IN THE PIPELINE. PAPER PROOFS MUST BE AS CLOSED AND UNCONDITIONAL AS POSSIBLE SO THAT THEY ARE AS EASY AS POSSIBLE TO FORMALIZE IN LEAN LATER. (leave notes if you already know what lean files to use or edit)

goal is met when after careful and hostile review you truly cannot add anything new to the research topic.


······
Prove, unconditionally, Brown–Susskind’s full growth–plateau–recurrence law for ordinary time-independent local Hamiltonians, and prove that maximal complexity occurs while locality remains permanently distinguishable from Haar randomness.

Lean rules:
1. Proofs must be unconditional in lean.
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. make sure you don't leave stale lean processes running - clean up after yourself.

ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.

where mathematical knowledge is missing, use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to find and create it.




### Formalize paper research

/goal 

formalize everything significant you have found until here in the paper-only research session.

add missing infrastructure, lean proofs, everything needed to mark a card as fully done and move it to stage 3 of the pipeline - no simplifications.

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. make sure you don't leave stale lean processes running - clean up after yourself.


## universal law

Using the hgtl7 skill and the HTGeometry / RhTower lean corpus, create a genuinely new geometry/topology through sustained conjecture→paper-proof-or-failure loops that does more than rename or classify known RH obstructions: it must yield new unconditional mathematical leverage on all live RH proof-route obstructions. 

Audit Lean corpus without writing or building Lean; search broad current arXiv literature; pivot aggressively; subject every claim to hostile novelty, correctness, and significance review. Put this research program's cards in dedicated subfolders under pipeline 1 and pipeline 2, promote only dependency-closed unconditional paper proofs, record failed routes and positive survivors, and do not mark the goal complete while the work remains merely explanatory. Completion requires that exhaustive hostile review finds no further meaningful conjecture, proof attack, salvage, or pivot capable of adding new knowledge to the topic.

prior research: docs/drafts/pipeline/2-fully-proven/universal-law-field



### mathematician
how would a fields medal mathematician approach this problem? what our corpus is, is technically decades of research with a lot of minor advancements beyond current sota research by other researchers. but the mathematician sees that all routes get stuck sooner or later, that something is missing, that they are looking at the problem from the wrong point of view and there must be some higher mathematical theory in play that is not yet known to humanity. how would they approach finding this higher mathematical theory? what questions would they ask? what research would they do? what would they do?