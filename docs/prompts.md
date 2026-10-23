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


do not run lake build!!!!! 

Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas. Do not build umbrellas or run large builds.

proofs must be unconditional without hypotheses or otherwise unproven premises.


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

## Open Research - New field of mathematics 



read fully the movitation and context of our recent research programmes:
- formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md
- formal/GaloisForLFunctions/BiScaleUncertainty/README.md
- formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md
- formal/GaloisForLFunctions/BezoutValuationIncidence/README.md
- formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md
- formal/GaloisForLFunctions/SquareRootThreshold/README.md
- formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md
- formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md
- formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md
- formal/GaloisForLFunctions/ArithmeticCompensationTheory/README.md
- formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md
- formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/README.md

on every turn: 
use the search tool for the lean corpus across the whole corpus, not just these programs, and combine proofs from across to corpus to either:
1. discharge a significant hypothesis.
2. significantly reduce the proof burden for the RH proof.
3. deliver a significant new insight or mathematical tool that allows us to solve problems we or mathematics as a whole couldn´t solve before.

do not use the hgtl7 skill. this is open research into developing a new fields of mathematics. 

read fully line by line and understand the motivation and context of the fields including traps to avoid:  
- formal/GaloisForLFunctions/TransThresholdPairCorrelation/README.md
    
on every turn: 
create a significant novel contribution to the fields open research topics and problems, so that that the field either 
- answers one of the field´s open questions
- gains one of the mathematical tool it aims to develop

Not valid are improvements of numbers, nogos, redressing existing knowledge in new language, anything that does not clearly count as significant progress, or that is not something that needs to exist in this field and couldnt exist otherwise.

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

do not use the README.md as a working log or diary. It is a foundational document, keep it crisp. Maintain a working log in logs/.

the goal is met when you have made 250 such significant contributions.



the goal is met when all walls are demolished and no longer a mathematical obstacle.


## cleanup - consolidate

do not use the hgtl7 skill

on every turn:
use the search tool for our lean corpus, and find instances where multiple "dots" in our corpus can be connected to discharge a premise/hypotheses/conditional prop interface.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

goal is met when 250 discharges could be made.

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
- formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md
- formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md
    
problem: despite all this work, we have not come close to overcome any of the hard obstacles and close a proof route.

questions:
1. what mathematical tools are we or mathematics as a whole missing?
2. what to research next in each of the research programs
3. do we need another research program to develop new mathematics that nobody has developed yet? if so, what would it be about and what would it try to answer and do?

work rules:
1. use the search tool for our lean corpus.
2. do only read the documents i mentioned and lean code. do not waste time and token on reading other markdown files. 

write your whole report in docs/reports/review-2210/astra.md

## update obstacles
previously we had created these documentss:
- docs/reports/review-2310/walls-ledger.md
- docs/reports/review-2310/hard-obstacles.md
- docs/reports/review-2310/hard-obstacles-summary.md
- docs/reports/review-2310/route-unification-ledger.md

also we have:
- docs/reports/rh-current-frontier-map.md
- docs/reports/rh-killed-routes.md

update the reviews to reflect the current status quo and frontier of our research:
1. a complete report about each route and route candidate and what the hard mathematical obstacles are that block us from closing the route. split these into a) obstacles that we can solve and are "just work", and b) obstacles that are open mathematical problems nobody has a solution to
2. then create a summary document that combines all the information and:
   2.1 lists all tasks / obstacles that we can solve and are "just work"
   2.2 lists the open mathematical obstacles/research topics nobody has a solution to
   2.3 ideates whether solving these obstacles in 2.2 would require a new field of mathematics, what this field would be about, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover
3. based on that an updated wall-ledger where walls have changed, were solved, or new walls were added.
4. also provide a new version of the route-unification-ledger.md which shows which routes are just different faces of the same problem similar to the wall-ledger unifies all walls into 3 core problem families.
   
do not read other markdown files, only the ones i mentioned.
do not rely only on these markdown files which are partly outdated. use the search tool for our lean corpus to research what our research currently shows. keep a working log in logs/ to write down research findings, so they do not get lost during context window compaction. the expectation is that you do real in-depth research and not just read the markdown files and do some spot checks on recently changed files.

the reports are not diaries or history log, but status quo reports.

write the new reports in folder docs/reports/review-2310/

## update programme README.mds
go one by one through the following research programmes and update their README.md - we have done a lot of research in these programmes which may or may not change the content of the README.md:

- formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md
- formal/GaloisForLFunctions/BiScaleUncertainty/README.md
- formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md
- formal/GaloisForLFunctions/BezoutValuationIncidence/README.md
- formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md
- formal/GaloisForLFunctions/SquareRootThreshold/README.md
- formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md
- formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md
- formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md
- formal/GaloisForLFunctions/ArithmeticCompensationTheory/README.md
- formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md
- formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/README.md
- formal/GaloisForLFunctions/TransThresholdPairCorrelation/README.md
- formal/GaloisForLFunctions/ArithmeticOrientationTheory/README.md

important: the readme.md is not a ledger or status report but a foundational document that explains a new research agent the why, how, what - the motivation, the objects, the language, the mechanisms of the field, traps to avoid, the open research topics, the questions it aims to answer, the tools it aims to create, its foundational pillar theorems, where it sits in the context of our whole research, how it relates to other research programmes.


## review
Read the following documents:
1. Route ledger: docs/reports/rh-current-frontier-map.md
2. Failed/Killed approaches: docs/reports/rh-killed-routes.md
3. Unification of the routes: docs/reports/review-2310/route-unification-ledger.md
4. Hard obstacles: docs/reports/review-2310/hard-obstacles.md
5. The hard obstacles (Walls) we have identified and not overcome: docs/reports/review-2310/walls-ledger.md

and read the current research programmes:
- formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md
- formal/GaloisForLFunctions/BiScaleUncertainty/README.md
- formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md
- formal/GaloisForLFunctions/BezoutValuationIncidence/README.md
- formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md
- formal/GaloisForLFunctions/SquareRootThreshold/README.md
- formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md
- formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md
- formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md
- formal/GaloisForLFunctions/ArithmeticCompensationTheory/README.md
- formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md
- formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/README.md
- formal/GaloisForLFunctions/TransThresholdPairCorrelation/README.md
- formal/GaloisForLFunctions/ArithmeticOrientationTheory/README.md

Only read these documents, no other markdown files.

Use the search tool for our lean corpus to research what we have proven and not proven. Do not assume, our research is far ahead of your training data. Take the time to search and understand. 

Keep a log file in logs/ for your research to note down facts and findings, since this research will go over multiple context window compactions that otherwise may lose information.

The questions for you to answer:
1. Do you see any opportunity for a new proof mechanism or route that circumvents the walls?
2. You can interpret the walls as questions we need to answer and for which we and mathematics as a whole do not have the tools to create these answer - if we would create a new field of mathematics that can supply these tools, what would this field be? What would the questions be, what would be its approach/point of view, what its objects, language, foundational principals, criteria it must fulfill, its research topics?

Write a report in docs docs/reports/review-2310/fable.md

do not run any builds.

## Init new field programme

Do not use the hgtl7 skill.

Read fully docs/reports/review-2310/fable.md

It describes the big picture of our current research, the obstacles, and why we arrive at developing a new field/research programme called "Arithmetic Orientation Theory"

Your task: develop this new field / programme.

Follow the example of other research programmes: formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri

1. All lean code goes into its own subfolder and has its own umbrella.
2. When enough information is established write a foundational README.md:
   2.1 the README.md is not a ledger or diary or working log but a foundational document explaning the why, what, how
   2.2 it explains: motivation, objects, language, mechanisms, traps, questions the programme aims to answer, tools it aims to develop, open research topics, foundational pillar theorems, where this field/programme sits in the context of our hole research and how it relates to other research programmes in our corpus, success criteria and criteria for what a contribution to the field/programme must be like.
3. Research and develop the field and add "meat to the bone" with significant contributions to the core research topics, tools and questions of the new field.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Make good use of the search tool for our lean corpus to find existing work and get leads for new ideas and solutions for your work.

The goal is done when the field is fully developed, the questions are answered, the tools are developed as described in the original document.


## research something

Task: Research, derive and formalize an unconditional proof of the Twin Prime conjecture.

All directly related lean code goes into formal/GaloisForLFunctions/twin-prime with its own umbrella

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

Goal is met when the conjecture is proven in lean.

## argon single task open question
formal/GaloisForLFunctions/TransThresholdPairCorrelation/README.md

read all about route "CHMD" in docs/reports/rh-current-frontier-map.md

find and fully formalize a definite and complete and final solution for entry 3 and 4 from "## 7. Open problems and research topics"

find a definite, final answer/solution, not just criterias or nogos. formalize every consequence and collary of this answer/solution and see where it can be applied to the rest of our corpus to advance the research.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Do keep changes in the README.md informative and crips - it is a foundational document describing the programme as a whole, it is not a history log or theorem/module ledger or diary.

Make good use of the search tool for our lean corpus to find existing work and get leads for new ideas and solutions for your work.