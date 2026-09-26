## MISC

optimize lean code. no raising heartbeat hacks.

do not pivot on unanswered mathematical problems. your job is precisely to solve problems that neither our lean corpus nor literature have solved yet. 

do not just search. create new knowledge with an open-ended loop of conjecture -> proof or fail and learn and pivot ->  conjecture -> proof or fail and learn and pivot ->  ... do not give up after a few failed conjectures. always learn and pivot even if it takes thousands of conjectures.

Reminder: 
1. create new knowledge, do not just search and pivot when hitting an unsolved problem - solve it using an open-ended loop of conjecture -> proof or fail and learn and pivot ->  conjecture -> proof or fail and learn and pivot ->  ... do not give up after a few failed conjectures. always learn and pivot even if it takes thousands of conjectures.
2. always use the search tool for our lean corpus AND ALWAYS BASE YOUR CONJECTURES ON OUR LEAN CORPUS, YOUR TRAINING DATA IS OUTDATED.
3. WORK ONLY ON THE HARDEST MATHEMATICAL PROBLEMS, NOT ON OPTIMIZING SOME NUMBERS OR BOUNDS. HARD FRONTIER RESEARCH.
4. Effort is not a reason to pivot. If something is missing in our lean corpus and mathlib, you build it no matter the effort.


## formalize goal
/goal

formalize UNCONDITIONALLY in lean all proven theorem for every single card in: 
- docs/drafts/pipeline/2-fully-proven/chronological
  
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

Goal: Create a formal proof or falsification of the Ramanujan–Petersson conjecture for Maass forms.

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

goal is met when lean corpus has an uncondtional formal proof/falsification of the conjecture.


## apply external paper to corpus experiment
find as many places as possible in our lean corpus to apply theorems-lemmas-propositions-correlateries from the listed papers to our lean corpus, formalize them and see what happens. this is experimental. it does not have to be about rh or anything, purely mechanical. it has no goal other than this task done in as many places as possible. explain in chat whenever you find something what this could be about.

this is a freak fringe paper and clearly has issues, but take the core ideas seriously for a moment and ask "what if?" "how could i make this work?" "where could it add something interesting to our research?" "is there something that when applied to our lean corpus could suprise us?"

papers:
- docs/others/einstein-fringe2.md
  
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

here are two runpods for you to use:
ssh root\@213.173.105.94 -p 47180 -i \~/.ssh/id\_ed25519
ssh root\@213.173.105.97 -p 40850 -i \~/.ssh/id\_ed25519

task:
- design computations that can deliver new insights and knowledge or could simply surprise you
- use extensively the scientific methods to design experiments and mingle-mangle experiments: docs/meta/scientific-method.md&#x20;
- computations should be related to:
  1. HB chain Identification: does the complete physical action actually produce the diagnostic used by the RH receiver, with all corrections and boundary terms retained?
  2. HB chain Selection: does the source enforce its vanishing, for a reason independent of RH, while permitting the known critical-line zeros?
  3. HB route in general
  4. Riemann hypothesis and riemann zeta function in general
  5. Anything that can deliver new insights directly or indirectly for our problem space of the riemann hypotheses

Computation rules:

- no computations that you could also predict the result of if you would honestly try
- no hour long computations
- optimize for multi-core
- when an experiment has finished, download results into a folder in docs/drafts/pipeline/2-fully-proven/computations. write a report in the folder with the results for future agents - no large diary, just enough to understand what you did compute, what the outcome and interpretation/consequences are
- document noteworthy new insights/facts in most token-efficient form for future ai agents to read in docs/drafts/pipeline/2-fully-proven/computations/results.md (short facts, no file references, no log, no diary, just the pure facts)
  
only run computations that can suprise you and lead to new insights and ideas and approaches to solve the hard open mathematical problems we are stuck at.
use the scientific methods to design experiments: docs/meta/scientific-method.md 
do not run hour long computation and do not run computations whose result you could also predict by reasoning.

h, also attack open problems using conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... loops

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

## hgtl7 create new knowledge
/hgtl7
contribute one significant piece of knowledge to our lean corpus that moves the frontier in any existing route or any new route towards a proof or falsification of the riemann hypothesis. the new knowledge cannot appear anywhere in public literature, your training data nor our lean corpus.

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