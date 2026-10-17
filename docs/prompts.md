## MISC

optimize lean code. no raising heartbeat hacks.

do not pivot on unanswered mathematical problems. your job is precisely to solve problems that neither our lean corpus nor literature have solved yet. EVEN IF THIS MEANS TO INVENT A COMPLETE NEW FIELD OR BRANCH OF MATHEMATICS and to fail for weeks and months on tens of thousands of conjectures.

do not just optimize numbers and estimates - solve the true hard obstacles that block your route from turning into a proof of the riemann hypothesis. 

your route is HF

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
- docs/drafts/pipeline/2-fully-proven/leftovers
- docs/drafts/pipeline/2-fully-proven/route TT
  
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

LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK. 

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

## apply external paper to corpus experiment
find as many places as possible in our lean corpus to apply theorems-lemmas-propositions-correlateries from the listed papers to our lean corpus, formalize them and see what happens. this is experimental. it does not have to be about rh or anything, purely mechanical. it has no goal other than this task done in as many places as possible. explain in chat whenever you find something what this could be about.


papers:
- https://arxiv.org/abs/2610.10584
- https://arxiv.org/abs/2609.20367
- https://arxiv.org/abs/2609.24149

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

On every new turn:

make one significant contribution that overcomes a hard mathematical obstacle for route PA from docs/reports/rh-current-frontier-map.md. it must overcome a hard obstacle and remove an obstruction or prop interface or hypothesis which significantly moves the frontier in the proof route and cleary moves us closer to finalizing the formal rh proof.

make one significant contribution that overcomes a hard mathematical obstacle or delivers a highly significant insight by combining multiple frontier theorems from multiple routes from docs/reports/rh-current-frontier-map.md your finding must contribute something of significant value directly or indirectly to routes CHMD + HF + OWU + EWU. 

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

do not look for shortcuts - we are too far in the research, there are no more shortcuts.


## create new knowledge - cross route towards one route
On every new turn:

make one significant contribution that overcomes a hard mathematical obstacle or delivers a highly significant insight by combining multiple frontier theorems from multiple routes from docs/reports/rh-current-frontier-map.md your finding must contribute something of significant value directly or indirectly to routes CHMD + HF + OWU + EWU. 

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



