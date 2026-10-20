## MISC

optimize lean code. no raising heartbeat hacks.

do not pivot on unanswered mathematical problems. your job is precisely to solve problems that neither our lean corpus nor literature have solved yet. EVEN IF THIS MEANS TO INVENT A COMPLETE NEW FIELD OR BRANCH OF MATHEMATICS and to fail for weeks and months on tens of thousands of conjectures.

do not just optimize numbers and estimates - solve the true hard obstacles that block your route from turning into a proof of the riemann hypothesis. 

always use the search tool for our lean corpus. make sure you are note missing existing work, or things that you could use to create new interesting insights. do not just blindly look for mathlib, but use the search tool to find research we have done.

are you actually working on removing roadblocks and mathematical obstacles to close route CHMD for the final RH proof, or are you taking shortcuts just to create lean files that build? this here does not look like you are actually solving the problems but are just busy creating lean code that does nothing to our research problem

do not just search. create new knowledge with an open-ended loop of conjecture -> proof or fail and learn and pivot ->  conjecture -> proof or fail and learn and pivot ->  ... do not give up after a few failed conjectures. always learn and pivot even if it takes thousands of conjectures. be creative. follow unusual and fringe ideas as well as straight forward ideas. it cost almost nothing to try things.

Reminder: 
1. create new knowledge, do not just search and pivot when hitting an unsolved problem - solve it using an open-ended loop of conjecture -> proof or fail and learn and pivot ->  conjecture -> proof or fail and learn and pivot ->  ... do not give up after a few failed conjectures. always learn and pivot even if it takes thousands of conjectures.
2. always use the search tool for our lean corpus AND ALWAYS BASE YOUR CONJECTURES ON OUR LEAN CORPUS, YOUR TRAINING DATA IS OUTDATED.
3. WORK ONLY ON THE HARDEST MATHEMATICAL PROBLEMS, NOT ON OPTIMIZING SOME NUMBERS OR BOUNDS. HARD FRONTIER RESEARCH.
4. Effort is not a reason to pivot. If something is missing in our lean corpus and mathlib, you build it no matter the effort.

also apply here noether´s theorem in both directions in the naive form "every continuous symmetry of the action of a physical system with conservative forces has a corresponding conservation law." so 1. for a conservation law, can we find the action and symmetry, and 2. can we identify elements in our lean corpus that can be interpreted as action and symmetry of a physical system and find the conservation law for it?


On every turn state what the proof route is you are working on. State what the hard open mathematical problems are you have to solve. Evaluate if your last activities have contributed to solving the open hard mathematical problems - if not, explain what you will different in this turn to attack and solve the hard open mathematical problems. Any action that is not moving the frontier on your route towards the final RH proof is a waste of token and time.

## formalize goal
/goal

formalize UNCONDITIONALLY in lean all proven theorem for every single card in: 
- docs/drafts/pipeline/2-fully-proven/thim-dyadic-antichain-prime-capacity.md


the lean code for these goes into formal/GaloisForLFunctions/TransHorizonIncidenceMechanics

add missing infrastructure, lean proofs, everything needed to mark a card as fully done and move it to stage 3 of the pipeline - no simplifications. 

Lean rules:
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

Non-negotiable working mode rules:
1. If it cannot be done in a single session -> Does not matter. Do it!
2. If it cannot be done in a single context window -> Does not matter. Do it!
3. If it takes months -> Does not matter. Do it!
4. If it is "research-level construction" -> Does not matter. If there is any way you could build it you build it no matter what.
5. Missing in mathlib -> Build it no matter the effort.
6. The only reason to stop working on a card if a proof is mathematically impossible. Open research is not mathematically impossible.
7. Missing mathematical knowledge: create it with the hgtl7 or hgt-fields-medalist skill workflow and heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...

LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK. USE THE SEARCH TOOL FOR THE LEAN CORPUS, NOT JUST RG OR GREP.

GOAL IS MET WHEN ALL CARDS ARE FULLY FORMALIZED AND CAN BE MOVED TO STEP 3 OF THE PIPELINE. NO SHORTCUTS OR FAKING IT!


## research Route

Goal: Create a formal proof or falsification of the Riemann Hypothesis using Route TT from docs/reports/rh-current-frontier-map.md

Goal: Create a formal proof or falsification of the Parity-Drift Hypothesis for π: docs/partity-drift-pi.md

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

**Working mode rules:**
1. Use the search tool for our lean corpus heavily.
2. Do not just search but also create missing knowledge via a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... 
3. Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Your conjectures based on it are bullshit. Use THE WHOLE LEAN CORPUS WITH MUCH MORE IDEAS, SOLUTIONS, TOY PROBLEMS, INNOVATIVE APPROACHES. NEVER EVER USE YOUR TRAINING DATA AS STARTING POINT - IT IS OUTDATED.
4. on every turn state the research topic, what the hard mathematical obstacles are, how your last work has made progress and how your next steps will make progress solving these obstacles. 
5. any work that does not attack and try to solve the hard mathematical obstacles is theatre and a waste of time

Keep a working log for yourself and do not pay too much attention what other agents are doing. 

## research Route claude

Goal: Create a formal proof or falsification of the Riemann Hypothesis using Route TT from docs/reports/rh-current-frontier-map.md

Goal: Create a formal proof or falsification of the Parity-Drift Hypothesis for π: docs/partity-drift-pi.md

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
4. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
5. make sure you don't leave staleclean up after yourself.
6. Optimize lean code. No raising heartbeat hacks.

**Working mode rules:**
1. Use the search tool for our lean corpus heavily.
2. Do not just search but also create missing knowledge via a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... 
3. Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Your conjectures based on it are bullshit. Use THE WHOLE LEAN CORPUS WITH MUCH MORE IDEAS, SOLUTIONS, TOY PROBLEMS, INNOVATIVE APPROACHES. NEVER EVER USE YOUR TRAINING DATA AS STARTING POINT - IT IS OUTDATED.
4. use the hgtl7 skill workflow on every turn including answering the questions.

**Computation rules:**
1. Run computations only on runpod: ssh root@157.157.221.30 -p 43625 -i ~/.ssh/id_ed25519
2. no computations that you could also predict the result of if you would honestly try
3. use extensively the scientific methods to design experiments and mingle-mangle experiments: docs/meta/scientific-method.md - every experiment you design turn into multiple experiments using these methods
4. no hour long computations
5. optimize for multi-core
6. when an experiment has finished, download results into a folder in computations/. write a report in the folder with the results for future agents - no large diary, just enough to understand what you did compute, what the outcome and interpretation/consequences are. 

Keep a working log for yourself and do not pay too much attention what other agents are doing. 
- https://arxiv.org/abs/math/0205003
- https://arxiv.org/abs/math/0008177
- - 
  
## apply external paper to corpus experiment
find as many places as possible in our lean corpus to apply theorems-lemmas-propositions-correlateries from the listed papers to our lean corpus, formalize them and see what happens. this is experimental. it does not have to be about rh or anything, purely mechanical. it has no goal other than this task done in as many places as possible. explain in chat whenever you find something what this could be about.

papers:
- https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
   
Non-negotiable working mode rules:
1. If an idea would be interesting, but is missing lean infrastructure, build it no matter the effort, instead of pivoting.
2. use the search tool for our lean corpus. do not read cards or anything, only work directly on lean.
3. Missing mathematical knowledge: create it with a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...
   
use the search tool for the lean corpus to check what already was formalized so you do not duplicate existing work.


## Research 2
**Goal:** Move the frontier of our lean corpus towards a formal proof of the Selberg 1/4 conjecture.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

**Mandatory reasearch and conjecturing rules:** 
1. always use the search tool for our lean corpus to find ideas, existing work. conjecture based on the lean corpus, not your training data which is behind our research in the lean corpus.
2. always tackle the hardest mathematical problem that neither our lean corpus nor literature have solved yet. missing infrastructure or no existing proof is not reason to pivot but to build the infrastructure and to solve the open problem yourself.
3. to create new knowledge use the heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...  
4. On every turn use the hgtl7 skill workflow.

Goal is met when the Selberg 1/4 conjecture is formally and unconditionally proven or falsified in our Lean corpus.


## computations

question: are there any computations you could make that you do not already know the result of and that would significantly narrow for you where to point your research at or what research routes are a dead end?

here is a runpod to run these computations on: ssh root\@216.81.151.68 -p 16020 -i \~/.ssh/id\_ed25519
download results and document them in docs/drafts/pipeline/2-fully-proven/computations.
do not use computations in any form in lean proofs, only take them to kill routes or identify new or sharpen research routes.
optimize python code for multicore.

once all computations are done, write a report in the folder with the results for future agents - no large diary, just enough to understand what you did compute, what the outcome and interpretation/consequences are

good. hope this helped. continue now your lean work only without computations.


## computation research

**Goal:** Create novel and significant knowledge for our rh research.

Use computations and formalize lean to discover new routes, kill routes, sharpen routes, discharge premises and finally close a formal RH proof chain.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

**Mandatory reasearch and conjecturing rules:** 
1. always use the search tool for our lean corpus to find ideas, existing work. conjecture based on the lean corpus, not your training data which is behind our research in the lean corpus.
2. always tackle the hardest mathematical problem that neither our lean corpus nor literature have solved yet. missing infrastructure or no existing proof is not reason to pivot but to build the infrastructure and to solve the open problem yourself.
3. to create new knowledge use the hgt-fields-medalist skill workflow and heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...  

**Mandatory computation rules:**
1. Computations run always on runpod: ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519
2. optimize python code for multicore.
3. download results and document them in docs/drafts/pipeline/2-fully-proven/computations.
4. Only compute things you cannot already predict the result of.
5. Do not run hours long computations.

goal is met when RH proof is formalized.




## computations
lets change the method and run experiments with computations.
task:
- design computations that can deliver new insights and knowledge or could simply surprise you
- use extensively the scientific methods to design experiments and mingle-mangle experiments: docs/meta/scientific-method.md


here is a runpod for you to use for computations if needed:
ssh root@213.173.111.73 -p 21771 -i ~/.ssh/id_ed25519

**Computation rules:**

- no computations that you could also predict the result of if you would honestly try
- no hour long computations
- optimize for multi-core
- when computations have finished, download results into a folder in computations/. write a report in the folder with the results for future agents - no large diary, just enough to understand what you did compute, what the outcome and interpretation/consequences are
- document noteworthy new insights/facts in most token-efficient form for future ai agents to read in computations/results.md (short facts, no file references, no log, no diary, just the pure facts)
  
**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.


use the scientific methods to design experiments: docs/meta/scientific-method.md 
do not run hour long computation and do not run computations whose result you could also predict by reasoning.


## Scientist

Act like a scientist. Always ask what a scientist would do in your situation.

1. Apply these methods:
   a. docs/meta/stroke-of-genius-method.md
   b. docs/meta/scientific-method.md

2) For every new insight, for every new failure, ask: "What does it mean for the whole route?"

3) Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Always use the search tool for the lean corpus to understand the real frontier we have proven and open problems and conjecture based on that and develop experiments around actual problems we have, not what your training data tells you.

4) Always ask "am I actually working on the right problem? Is this what I should be working on to bring the whole route forward? Or am I tunnelviewing on a minor problem that adds little to nothing while not moving the route as a whole?"

5) Keep a crisp "fact log" for your own research (do not meddle with logs of other agents). Only record facts and nogos, things you have found out - it is not a diary or history log, it is a token-efficient log of the insights you have made during your research.

6)  use the search tool and deep search and method search extensively

7)  do not just search, also attack open problems using conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... loops

8) use arxiv search and single word and broad searches for finding papers not directly related to the problem and see if there is anything useful in the found papers - do not search for your problem or narrow searches, prefer most receent papers (january to september 2026). example searches: "hawking", "commutator", "recurrence", "cauchy", ... - these are examples, create your own search terms. most papers will be useless, but a few will allow to bring in solutions from fields far away from your actual problem

##  create new knowledge - one new fact

read fully and understand especially the traps: 
1. formal/GaloisForLFunctions/BiScaleUncertainty/README.md
2. formal/GaloisForLFunctions/BezoutValuationIncidence/README.md
   
On every new turn:

make one significant contribution to our BiScaleUncertainty and/or BezoutValuationIncidence framework and one or more proof routes from docs/reports/rh-current-frontier-map.md. it must overcome a hard obstacle and remove an obstruction or prop interface or hypothesis which significantly moves the frontier in the RH proof route and cleary moves us closer to finalizing the formal rh proof. be biased towards producers, but not exclusively.

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the problem and its possible solutions. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures. web search will not deliver the solution.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

do not use websearch, do not check for novelty, do not read old markdown files. read our lean corpus, use the whole lean corpus for leads and ideas, use the search tool for our lean corpus and go from what the lean corpus tells you. 

docs/reports/rh-current-frontier-map.md and formal/GaloisForLFunctions/BiScaleUncertainty/README.md and formal/GaloisForLFunctions/BezoutValuationIncidence/README.md are read only for you

goal is met when RH is proven unconditionally in lean.

## create new knowledge - cross route towards one route

On every new turn:

make one significant contribution that overcomes a hard mathematical obstacle in route CTF from docs/reports/rh-current-frontier-map. the contribution must clearly and significantly bring us closer to closing the full route for the RH proof.

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the problem and its possible solutions. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures. web search will not deliver the solution.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

do not use websearch, do not check for novelty, do not read old markdown files. read our lean corpus, use the whole lean corpus for leads and ideas, use the search tool for our lean corpus and go from what the lean corpus tells you. 

docs/reports/rh-current-frontier-map.md is read only for you

goal is met when you have found 20 such signficant insights.



## Remove premises

Work on our lean corpus in increments on any randomly picked premise on a receiver or significant proof step in any of our existing or a new proof route you identify towards a formal proof of the riemann hypothesis. Our research in a nutshell: docs/reports/rh-current-frontier-map.md

Find ways to either:
- discharge a premise
- partially discharge a premise or otherwise reduce the proof burden
- reframe a premise or receiver in a different mathematical language that offer a new approach to a discharge
- identify value correlation, equivalences, exclusions that deliver new insights

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the problem and its possible solutions. do not blindly follow an idea or judgment because it is in your training data. understand what our research is hinting at.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

Keep a working log for yourself and do not pay too much attention what other agents are doing. 

The goal is met when a proof or falsificiation route of the Riemann Hypothesis is fully formalized in lean - unconditionally without premises. You are free to pick what to work on and when to pivot to another target. But never mark this goal as unachievable - there is always work to do.

## value relations
Work on our lean corpus in increments on any randomly picked theorems, lemmas, premises.

Test, ideate, speculate and identify value relations, functional dependencies, correspondences, proportionalities to either:
- discharge a premise
- partially discharge a premise or otherwise reduce the proof burden
- reframe a premise or receiver in a different mathematical language that offer a new approach to a discharge
- create a new lemma/theorem or new RH receiver that delivers significant new mathematical insights (even if not solving RH)

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

always look at the big picture, try to understand what our lean research is trying to tell you about the nature of the problem and its possible solutions. do not blindly follow an idea or judgment because it is in your training data. understand what our research is hinting at.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

Keep a working log for yourself and do not pay too much attention what other agents are doing. 

The goal is met when every lemma, theorem, premise has been inspected and nothing new can be found anymore. You are free to pick what to work on and when to pivot to another target. But never mark this goal as unachievable - there is always work to do.

## paper
the last paper we have written: docs/drafts/pipeline/4-publication-ready/universal-quantum-recurrence-anatomy more research is already in the lean corpus or as paper proof in the pipeline.

continue our existing research and create novel and significant new knowledge about:
- Brown–Susskind’s full growth–plateau–recurrence law
- the black hole interior volume paradox
- Quantum Recurrence

collect enough novel and significant knowledge to write a paper that meets the publishing requirements of Nature: the paper must report a fundamental new insight or startling discovery that significantly shifts the scientific conversation across multiple fields.

one step towards this goal is: 

prove Brown–Susskind’s full growth–plateau–recurrence law for ordinary time-independent local Hamiltonians, and prove that maximal complexity occurs while locality remains permanently distinguishable from Haar randomness.

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

Keep a working log for yourself and do not pay too much attention what other agents are doing. 

goal is met when paper is written and passes a hostile review that confirms that the paper is on a quality level to be published in Nature.

## rh proof

find and formalize an uncoditional proof or falsification of the riemann hypothesis using any route from docs/reports/rh-current-frontier-map.md or a new route not yet explored by us.

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

Do not use subagents.

Keep a working log for yourself and do not pay too much attention what other agents are doing. 

The goal is met when a proof or falsificiation of the Riemann Hypothesis is fully formalized in lean - unconditionally without premises.

## Weil work packages

use the hgtl7 skill workflow on every turn for this open end research task: 

contribute significant pieces of knowledge to our lean corpus that moves the frontier and finds a solution for this problem: docs/reports/weil-work/07-higher-denominator-rigidity.md

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the problem and its possible solutions. do not blindly follow a route because it is in your training data. understand what our research is hinting at.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.

Keep a working log for yourself and do not pay too much attention what other agents are doing. 

The goal is met when your assigned problem is fully solved and provably solved via lean formalization.


##
Our current map of routes and route candidates for a formal proof of the Riemann Hypothesis: docs/reports/rh-current-frontier-map.md

A ledger of crisp facts about what the proof must or cannot be like: docs/reports/STATUS.md

Your task: Assume all our routes and route candidate are dead ends and will not deliver the RH proof no matter how much time we spend on them. They all will get stuck at some point at an obstacle they are unable to overcome. Some are already stuck, some routes are killed. 

But all the work so far and especially the failures tell us something about the nature of the problem. I want you to do a deep research on our lean corpus, on the routes and route candidates, on the failures/nogos/positive findings and come up with a new route that is founded on learning from all these failures and is able to circumvent them through an innovative rethinking and change of perspective.

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are - we are further than literature in many parts.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the problem and its possible solutions. do not blindly follow a route because it is in your training data. understand what our research is hinting at.

maintain working log for yourself. do not write lean code yet. understand why we failed so far on every route and what this teaches us about where the actual proof route must go - potentially through developing a whole new field of mathematics.



## Open Research - New field of mathematics 

do not use the hgtl7 skill. do not focus on the RH. this is open research into developing a new field of mathematics. read fully line by line and understand the motivation and context of that field and traps to consider: formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md

On every new turn:

make one significant contribution to your research topic. a contribution is significant if it does at least one of the following:
- overcomes a mathematical obstacle in the field
- delivers new valuable insights into the nature of the field
- develops a mathematical tool that helps to overcome a significant mathematical obstacle in other parts of our lean corpus
- delivers a new proven fact that answers questions arising from the nature of the field and its underlying motivation
- broadens or sharpens the mathematical toolset of the field to be able to answer new questions, provide solutions otherwise not possible, or even ask new questions
- closes gaps to turn the field as whole into a true new field of mathematics by established standards in the mathematical community

your main tool for this is an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are, also to find existing building blocks for your work to not duplicate existing work.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Lean code relevant for the field  goes into formal/GaloisForLFunctions/TransHorizonIncidenceMechanics


Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md is read-only for you

use the search tool for our lean corpus, not just rg or grep.

Your topic of research: 

Multi-Point Window Defect Averaging & Periodic Modulus Conservation
- **Target Module:** `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/MultiPointDefectAveragingAndPeriodConservation.lean`
- **Builds On:** Pillar XIII ([SuccessorStateObstructionAndPhaseRefinement.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/SuccessorStateObstructionAndPhaseRefinement.lean)) and Pillar XIV ([ArithmeticUncertaintyAndSpikeCancellation.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ArithmeticUncertaintyAndSpikeCancellation.lean)).
- **Mathematical Problem:**
  Pillar XIII proved that `sieveSeq N c` is periodic with period $L_N = \operatorname{horizonObservationModulus}(N) = \operatorname{lcm}(1, \dots, N)$, and Pillar XIV proved the two-point consecutive defect sum identity `sieveRenormalizedPrefixDefect_pred_add_self_eq` and the path Poincaré inequality.
- **Concrete Deliverables in Lean 4:**
  1. Prove the **Period Shift Law for `sieveRenormalizedPrefixDefect`**: shifting the observation endpoint $M \mapsto M + L_N$ changes $2\widetilde{\mathcal{D}}_N(M; c)$ by exactly minus the full-period Dirichlet oscillation energy $-\sum_{k=M+1}^{M+L_N} (s_{N,c}(k+1) - s_{N,c}(k))^2 \le 0$!
  2. Deduce **Monotonicity Across Period Multiples**: for every $M \ge 1$ and $q \ge 0$, $\widetilde{\mathcal{D}}_N(M + q L_N; c) \le \widetilde{\mathcal{D}}_N(M; c)$, and if `sieveSeq N c` is non-constant over a period, $\widetilde{\mathcal{D}}_N(M + q L_N; c) \to -\infty$ linearly in $q$!



Goal is met when you have made 100 signifcant contributions to the new field of mathematics.

## Open Research - New field of mathematics 

do not use the hgtl7 skill. this is open research into developing a new fields of mathematics. 

read fully line by line and understand the motivation and context of the fields including traps to avoid:  formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md
 
on every turn: 

ideate and develop a novel and significant contribution to the research in this new field of mathematics we are working on. novel and significant is 

**Rules for what counts as significant contribution:**
- Must be native to the field by using the field and its objects, language, mechanisms. 
- Being part of the field is necessary - it cannot be just something that already exists in different "clothes". 
- It expands the ability of the field and its lean corpus to explain or to solve mathematical problems - see the Motivation section in the README.md. Or it solves an actual problem or discharges a premise in our lean corpus outside of the field showing that the field can provide solutions not possible without it.
- It expands the field beyond what known mathematics already offers.
  
**Tools to use:**
1. Search: use the search tool for our lean corpus, not just rg or grep. make good use of the search tool to find existing work, building blocks, and new ideas. Try to apply existing lean research, try to identify problems and questions the field with your contribution could explain or solve.

2. Conjecture loop: use an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.
 
the README.md is read-only for you.

the goal is met when you have made 100 such significant contributions.

the goal is met when all walls are demolished and no longer a mathematical obstacle.


## research after review

we did a review of our current research: 

based on your review:
docs/reports/review-2010/hard-obstacles.md
docs/reports/review-2010/hard-obstacles-summary.md

your task: work through the research tasks from section "## 2.1 Tasks that are just work" in docs/reports/review-2010/hard-obstacles-summary.md

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

Do not clutter any document with useless ledgers or diary entries or otherwise add content that is not in the spirit of the document´s purpose. Best you only keep it to pipeline cards and your own log.

Always make good use the search tool for our lean corpus to find existing work, building blocks, and leads for new ideas and solutions.


## research review
/l7
take a fresh look at the our whole research program.

status quo:
- our route ledger: docs/reports/rh-current-frontier-map.md
- analysis of hard mathematical obstales: docs/reports/review-2010/hard-obstacles.md

we have then started several research programs to develop new theories and the mathematical tools that will allow us to overcome these obstacles:
- formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md
- formal/GaloisForLFunctions/BiScaleUncertainty/README.md
- formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md
- formal/GaloisForLFunctions/BezoutValuationIncidence/README.md
- formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md
- formal/GaloisForLFunctions/SquareRootThreshold/README.md
- formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md
  
problem: despite all this work, we have not come close to overcome any of the hard obstacles and close a proof route.

questions:
1. what mathematical tools are we or mathematics as a whole missing?
2. what to research next in each of the research programs
3. do we need another research program to develop new mathematics that nobody has developed yet? if so, what would it be about and what would it try to answer and do?

work rules:
1. use the search tool for our lean corpus.
2. do only read the documents i mentioned and lean code. do not waste time and token on reading other markdown files. 

write your whole report in docs/reports/review-2010/fable.md

## update obstacles
previously we had created these two documents:
- docs/reports/review-2010/hard-obstacles.md
- docs/reports/review-2010/hard-obstacles-summary.md

the review tasks was:
based on route ledger: docs/reports/rh-current-frontier-map.md and ledger of hard obstacles (walls) docs/reports/walls/walls-ledger.md create
1. a complete report for each route and route candidate what the hard mathematical obstacles are that block us from closing the route. split these into a) obstacles that we can solve and are "just work", and b) obstacles that are open mathematical problems nobody has a solution to
2. then create a summary document that combines all the information and:
   2.1 lists all tasks / obstacles that we can solve and are "just work"
   2.2 lists the open mathematical obstacles/research topics nobody has a solution to
   2.3 ideates whether solving these obstacles in 2.2 would require a new field of mathematics, what this field would be about, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover


this review is incorrect and outdated. redo it.

the reports are not diaries or history log, but status quo reports.

rewrite the existing reports in folder docs/reports/review-2010/

## update programme README.mds
go one by one through the following research programmes and update their README.md - we have done a lot of research in these programmes which may or may not change the content of the README.md:

- formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md
- formal/GaloisForLFunctions/BiScaleUncertainty/README.md
- formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md
- formal/GaloisForLFunctions/BezoutValuationIncidence/README.md
- formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md
- formal/GaloisForLFunctions/SquareRootThreshold/README.md
- formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md
  
important: the readme.md is not a ledger or status report but a foundational document that explains a new research agent the why, how, what - the motivation, the objects, the language, the mechanisms of the field, traps to avoid, the open research topics.


