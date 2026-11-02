## MISC

do formalize every significant finding and dont leave it as paper proof. things are only proven when they are formalized in lean.

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
- docs/drafts/pipeline/2-fully-proven/leftovers

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

## research a route

Read and understand proof route ACS:
- docs/reports/rh-current-frontier-map.md
- docs/reports/rh-killed-routes.md
- docs/reports/review-2810/route-obstacles.md
- formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md
  
On every turn:
1. State in chat the proof route.
2. State the hard open mathematical blockers to solve.
3. Research, find and formalize either a theorem or discharge a premise that significantly brings us closer to solve one of the significant mathematical obstacles on that proof route. We are not looking for improving a number, finding more criteria, more nogos, redressing already known facts, but actual tangible progress in closing this proof route.

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

Do not use web search. Do not run novelty checks.

Make good use of the search tool for our lean corpus to find existing work and get leads for new ideas and solutions for your work.

The goal is met when route ACS is fully closed and formalized unconditionally in lean.

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

## Quantum reccurence paper
A while ago we researched and wrote this paper docs/drafts/pipeline/4-publication-ready/universal-quantum-recurrence-anatomy

Since then a lot of new research and mathematical tools has entered our lean corpus.

Do a full in depth research to understand what the strongest form of this paper is we can write now and write this new paper.

Stronger means:
1. More universal laws/principle
2. Answers a question that is actually of interest to the scientific community
3. Increases the likelihood to pass a hostile review by a reviewer at a scientific journal
4. Is novel and significant.

**Rules:**
1. Mathematical proofs in the paper must be proven in Lean. If it is not in Lean, it does not go into the paper.
2. Use the search tool for our lean corpus. Do not assume things based on your training data only. This is about research not in your training data or in the website.

**Lean Rules**
1. Lean proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.


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


do not use the hgtl7 skill. 

our current research programmes:
__ LIST README FILES FROM ## review HERE __

research, derive, formalize a significant contribution to either:
- overcome an open hard obstacle in a route docs/reports/review-2610/hard-obstacles.md
- finds a solution for removing a wall in docs/reports/review-2610/walls-ledger.md
- find an answer to an open question in a research programme
- gain one of the mathematical tools a research programme is missing
- gain a deeper insight about the problem the field is exploring and the nature of the field itself 
- prove a significant theorem that significantly advances our research about the RH as a whole 
  
Not valid are improvements of numbers, nogos, redressing existing knowledge in new language, or anything that does not clearly count as significant progress.

do not use the hgtl7 skill. this is open research into developing a new fields of mathematics. 

read fully:
formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/README.md

on every turn: 
research, derive, formalize a significant contribution to the field that significantly helps to either:
- find an answer to an open question in a research programme
- gain one of the mathematical tools a research programme is missing
- gain a deeper insight about the problem the field is exploring and the nature of the field itself 
- prove a significant theorem that significantly advances our research about the RH as a whole 

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

Maintain a working log in logs/. Do not use the README.md as a diary or working log or theorem ledger. Only update when the foundational information in it changes.

the goal is met when you have made 250 such significant contributions.


## Open Research - Connect the dots 

do not use the hgtl7 skill. 

your task on every turn:
find an opportunity to "connect the dots" between different parts of our lean corpus to either:
- overcome an open hard obstacle in a route docs/reports/review-3110/route-obstacles.md
- finds a solution for removing a wall in docs/reports/review-3110/walls-ledger.md

Not valid are mere improvements of insignificant numbers, nogos, more receivers, redressing existing knowledge in new language, or anything that does not clearly count as significant progress.

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

Maintain a working log in logs/. Do not use the README.md as a diary or working log or theorem ledger. Only update when the foundational information in it changes.

the goal is met when you have made 250 such significant "connect the dots" contributions.


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


## update obstacles
earlier we created these documents:
- docs/reports/review-0211/walls-ledger.md
- docs/reports/review-0211/route-obstacles.md
- docs/reports/review-0211/route-unification-ledger.md
- docs/reports/review-0211/obstacles-summary.md
  
read:
- docs/reports/rh-current-frontier-map.md
- docs/reports/rh-killed-routes.md

write new reports to reflect the current status quo and frontier of our research taking into account all new lean proofs and changes done since the original reports were written:
1. a complete report about each route and route candidate and what the hard mathematical obstacles are that block us from closing the route. split these into a) obstacles that we can solve and are "just work", and b) obstacles that are open mathematical problems nobody has a solution to
2. then create a summary document that combines all the information and:
   2.1 lists all tasks / obstacles that we can solve and are "just work"
   2.2 lists the open mathematical obstacles/research topics nobody has a solution to
   2.3 suggest if you see any opportunity for a "frankenstein" route that creates an RH proof by assembling building blocks from different routes and allowing this way to circumvent the blockers in a single route
   2.4 suggest if you see any opportunity for a wildy different route that is not at all like all the routes we have and does not face the same walls our existing routes and candidates face. say if you see none. the wildly different route does not have to be closed yet, just show that there could possibly be a wildly different route to the rh proof far away from our current routes.
   2.5 ideate and describe a breakthrough question that is less "hard" than proving RH or quasi-RH and would bring a real advance and breakthrough in:
   2.5.1 our RH proof research as a whole
   2.5.2 route PM
   2.5.3 route WD
   2.5.4 route HF
   2.6 ideate and describe a breakthrough question that would clearly open wide the path to the RH proof for:
   2.6.1 our RH proof research as a whole
   2.6.2 route PM
   2.6.3 route WD
   2.6.4 route HF
   2.7 ideates whether solving all obstacles to reach the RH proof would require a new field of mathematics, what this field would be about, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover
   2.8 What is the one question the is less hard than proving RH or quasiRH outright and would, when answered, bring a real breakthrough and push the door wide open for us for finding the RH proof?
3. based on that an updated wall-ledger where walls have changed, were solved, or new walls were added.
4. also provide a new version of the route-unification-ledger.md which shows which routes are just different faces of the same problem similar to the wall-ledger unifies all walls into 3 core problem families.

do not read other markdown files, only the ones i mentioned.
do not rely only on these markdown files which are partly outdated. use the search tool for our lean corpus to research what our research currently shows. 

first collect information in a working log in logs/ - facts, not process or status updates. only after having collected all information, interprete it, do additional research where new questions arise, and only when no more questions can be asked write the final reports. the expectation is that you do real in-depth research and not just read the markdown files or do some spot checks on recently changed files.

the reports are not diaries or history log, but status quo reports.

replace the reports in folder docs/reports/review-0211/ without history language or "this changed since last review".
do not run builds. this is not a task to verify the work of other agents but to create consolidated reports and "big picture" interpretations on their research results.


## update programme README.mds
do not use the hgtl7 skill. 

go one by one through the following research programmes and rewrite their README.md:

docs/reports/research-programmes.md

1. keep a working log where you write down mathematical facts, not process or status updates. 
2. actually read every lean proof in the research programme and take notes
3. rewrite the README.md with correct informantion:
   1. Motivation
   2. Objects
   3. Language
   4. Mechanisms
   5. Pillar theorems
   6. Tools developed and tools still to build
   7. Open questions and research topics
   8. Traps
   9. Where the research programme sits in the context of the other programmes and our research as a whole
   10. A big picture interpreation without much mathematical facts that tells us what this research programme is telling us about our RH proof research as a whole and what its finding are telling us about the RH proof and our research

important: the readme.md is not a ledger or status report but a foundational document. remove any form of theorem ledger and overly verbose explanations. 

write clean, simple, to the point. the readers are not humans but AI agents like you - so make sure you optimize for maximum information in minimum token usage.

keep the files under 2500 lines.
do not run any builds. do not read anything outside the formal/ folder. do not run web searches. use the search tool for the lean corpus when searching the lean corpus.

## review
Read the following documents:
1. Route ledger: docs/reports/rh-current-frontier-map.md
2. Failed/Killed approaches: docs/reports/rh-killed-routes.md
3. Unification of the routes: docs/reports/review-0111/route-unification-ledger.md
4. Hard obstacles: docs/reports/review-0111/route-obstacles.md
5. The hard obstacles (Walls) we have identified and not overcome: docs/reports/review-0111/walls-ledger.md
   
and read the current research programmes from oldest to newest: docs/reports/research-programmes.md
    
Only read these documents, no other markdown files.

Use the search tool for our lean corpus to research what we have proven and not proven. Do not assume, our research is far ahead of your training data. Take the time to search and understand. 

Keep a log file in logs/ for your research to note down facts and findings, since this research will go over multiple context window compactions that otherwise may lose information.

The questions for you to answer:
1. Do you see any opportunity for a new proof mechanism or route that circumvents the walls or destroy a wall?
2. Do you see any approach for an RH proof that is wildly different to all the routes and candidates we have so far, going a wildly different way not even touching the walls the existing routes face?
3. ideate and describe a breakthrough question that is less "hard" than proving RH or quasi-RH and would bring a real advance and breakthrough in:
   3.1 our RH proof research as a whole
   3.2 route PM
   3.3 route MC
   3.4 route WD
   3.5 route HF
4. ideate and describe a breakthrough question that would clearly open wide the path to the RH proof for:
   4.1 our RH proof research as a whole
   4.2 route PM
   4.3 route MC
   4.4 route WD
   4.5 route HF
5. What are the 3 open questions we should focus our research on to make the most progress to make a real breakthrough and progress towards the RH proof?
6. What is the one question the is less hard than proving RH or quasiRH outright and would, when answered, bring a real breakthrough and push the door wide open for us for finding the RH proof?
7. You can interpret the walls as questions we need to answer and for which we and mathematics as a whole do not have the tools to create these answer - if we would create a new field of mathematics that can supply these tools, what would this field be? What would the questions be, what would be its approach/point of view, what its objects, language, foundational principals, criteria it must fulfill, its research topics?

Write a report in docs docs/reports/review-0111/fable.md

do not run any builds. do not search the web. do not grep for sorry or other shit. your job is not to verify of other agents but to write a consolidated report and big picture interpretation of their research. focus on the mathematics.

## Init new field programme

Do not use the hgtl7 skill.

read and understand docs/reports/review-0211/obstacles-summary.md

under "## 2.7 Does closing RH need a new field?" it describes a new field/research programme called "theory of the window tower of Spec ℤ"

Your task: develop this field/research programme and do the actual research and formalization.

Follow the example of other research programmes: formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri or formal/GaloisForLFunctions/ArithmeticOrientationGeometry

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

Start with writing the first draft of README.md

## openings
Do not use the hgtl7 skill.

Read fully docs/reports/review-2410/fable.md

In section "C. The index exit: an independent count for the collision charge or the Hodge defect (AOG, ACS)." it describes 6 approaches to finally make a break-through in our research.

Your task: take on the formalization of "F. The coalescent prime surplus (TTPC).". Solve its open questions, deliver what it asks to deliver, formalize this openening fully.

We are not looking for estimates, improving on numbers, nogos, busy-work, more infrastructure, but an actual solution and formalization of this opening. 

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

Goal is achieved when the opening/input is fully developed.

## research something
Do not use the hgtl7 skill. 

Research, derive and formalize a complete solution of the open mathematical obstacles to fully close the route for one or more routes in docs/reports/rh-current-frontier-map.md

We are not looking for more criteria, improving some numbers, more nogos, we are looking for actual progress on solving the stated open problems and close a route to the RH proof.

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

Goal is met when a proof route is fully closed and formalized in lean and RH is proven. Do not stop until an RH proof is fully formalized.

## argon do breakthrough

do not use the hgtl7 skill.

read: docs/reports/review-0211/obstacles-summary.md

the document asks two questions, gives two tasks to bring use forward in our RH research via route PM:

1. Build from the Mayer operator alone (geodesic Euler product, Lewis period functions, whose three-term relation carries the reflection `s ↔ 1 − s`) a function real on the critical line of the scattering parameter whose sign changes are the scattering resonances — the operator analogue of Hardy's `Z(t)` — and prove infinitely many sign changes (Hardy's theorem), then a positive proportion.
2. Find a positive-definite Hermitian structure on the space of Lewis period functions (or on the scattering channel of the Mayer operator) invariant under the reflection `ψ(z) ↦ z^{−2s}ψ(1/z)`, such that a resonance off `Re s = 1/4` produces a negative norm — a Krein or Lax–Phillips realization where the resonances are eigenvalues of a definite operator.

your task: answer both questions, find a complete solution for them and unconditionally formalize them and its implications and collaries in lean.

We are not interested in estimates, criterias what the answer could be like, what is not the answer, busywork - we accept only a full and final answer/solution to the posed questions/tasks.

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

Put all lean code for the answer into relevant subfolders to not bloat RHTower and HTGeometry folders further.

## argon single task open question

Do not use the hgtl7 skill.

read and understand route WD from docs/reports/rh-current-frontier-map.md

read this todo list for closing route WD docs/reports/review-0111/route-WD.md

your task: work step by step through the todos in docs/reports/review-0111/route-WD.md and bring each step to a full and final solution and formalization.

we are not interested in busywork, redressing of existing knowledge, building unnecessary lean infrastructure. stay focused on the task and tackle the actual problems. do not just write lean code for the sake of doing something. solve the actual problems.
  
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

Put lean code into the correct subfolder(s), do not bloat RHTower or HTGeometry folders more.


## Walls

Do not use the hgtl7 skill.

read and understand docs/reports/review-0211/obstacles-summary.md

under "## 2.4 A wildly different route" it describes an approach to a different proof route.

Your task: develop this proof route and do the actual research and formalization.
 
we are not interested in busywork, redressing of existing knowledge, building unnecessary lean infrastructure. focus on the task and solve the actual hard problems to develop this route.
  
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

Put lean code into the correct subfolder(s), do not bloat RHTower or HTGeometry folders more.

Do not use the wall ledger as diary. Only update status, do not add more.

Goal is met when there are no more open or partially solved or sharpened walls.

## Obstacles

Do not use the hgtl7 skill.

read the wall ledger (a wall is a mathematical obstacle in our research): docs/reports/review-0111/walls-ledger.md

on every turn:
conjecture, derive, formalize a way to either
- turn an open or sharpened wall into partially solved or solved.
- turn a partially solved wall into a solved wall.
 
we are not interested in busywork, redressing of existing knowledge, building unnecessary lean infrastructure. you turn walls not solved yet into solved walls or you are wasting time and token.
  
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

Put lean code into the correct subfolder(s), do not bloat RHTower or HTGeometry folders more.

Do not use the wall ledger as diary. Only update status, do not add more.

Goal is met when there are no more open or partially solved or sharpened walls.

## Deep understanding

Mandatory:
- The source of truth is our lean corpus. Do not read files outside of the formal/GaloisForLFunctions folder unless user specifies specific files to read.
- Do not assume anything based on your training data. Our lean corpus is SOTA research ahead of anything you have seen during your training or could find via websearch.
- Do not use websearch. Our lean corpus is the SOTA research.

Context:
- Current reports on where our research stands: docs/reports/review-3010
- Our most recent research programmes from oldest to newest: docs/reports/research-programmes.md

The problem: Our research corpus is so large that we have lost the way. Our consolidated reports may name many routes and candidates, but ultimately we are kind of dancing around the idea of making Weils proof for Q work for Z. 

We have indications that our lean corpus is actually already providing a lot of signs and hints that the solution is something very different, that we even have many building blocks. We just do not see the "forest because of all the trees". 

Your task: Do an honest, in-depth research into our lean corpus. What does it really say? What does it actually hint at? If we do not assume what the solution must be like and where it has to live and what our problems are, what does it tell us where to look? 

Be open-minded, do not assume a solution or route, but let the lean corpus speak. 

Method:
- Interrogate the lean corpus and understand not only what it does but why it does it and what "what if...?" questions could be ask and where they lead? 
- Take apart lean proofs and ask why they are this way, what they do, why certain bounds, objects, relations, exclusions exist and what would happen if they would be different?
- Ask questions to the lean corpus. Ask "what if?" and "why?" and what is the big picture and birds view? Interprete the proofs, do not just explain it.

Work in phases:
1. Collect information.
2. Collect more information.
3. Collect even more information.
4. Keep the actual full interpretation of all the information you have collected and writing the final report for the end.

Keep a log for mathematical facts you discover. Not a working log. Facts and information you discovered.

The final report goes into docs/reports/review-3010/opus-reboot.md


## Deep understanding - Consoldiate

Mandatory:
- The source of truth is our lean corpus. Do not read files outside of the formal/GaloisForLFunctions folder unless user specifies specific files to read.
- Do not assume anything based on your training data. Our lean corpus is SOTA research ahead of anything you have seen during your training or could find via websearch.
- Do not use websearch. Our lean corpus is the SOTA research.

Context:
We have given two ai agents (OpenAI Astra and Anthropic Opus) the task to do an honest open-minded review of our lean corpus because it has become more and more obvious that we have maneuvered us into a corner, a tunnel view only looking at making Weil proof for Q somehow work for Z and positivity is the only way.

They wrote logs of facts they found:
- docs/reports/review-3010/opus-reboot-facts.md
- docs/reports/review-3010/corpus-facts.md

The reports with their conclusions:
- docs/reports/review-3010/what-the-corpus-is-telling-us.md
- docs/reports/review-3010/opus-reboot.md

We assume that both reports are not going deep enough and have still not uncovered the real truth:  What does our lean corpus really say? What does it actually hint at? If we do not assume what the solution must be like and where it has to live and what our problems are, what does it tell us where to look? 

Your task: Not only review both reports but go beyond them. Be antagonistic to their reports and claims. Assume they assumed too much and were still too much influenced by their training data and the bias in our research towards Weil and positivitiy and have not really interpreted the lean corpus solely based on what it tells us. Do your own investigation and then write a new report that also includes a concrete research programme outline.

Keep a log for mathematical facts you discover. Not a working log. Facts and information you discovered.

The final report goes into docs/reports/review-3010/reboot-final.md