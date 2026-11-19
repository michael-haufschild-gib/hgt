## MISC

do formalize every significant finding and dont leave it as paper proof. things are only proven when they are formalized in lean.

do not pivot on unanswered mathematical problems. your job is precisely to solve problems that neither our lean corpus nor literature have solved yet. EVEN IF THIS MEANS TO INVENT A COMPLETE NEW FIELD OR BRANCH OF MATHEMATICS and to fail for weeks and months on tens of thousands of conjectures.

do not just optimize numbers and estimates - solve the true hard obstacles that block your route from turning into a proof of the riemann hypothesis. 

always use the search tool for our lean corpus. make sure you are note missing existing work, or things that you could use to create new interesting insights. do not just blindly look for mathlib, but use the search tool to find research we have done.

are you actually working on removing roadblocks and mathematical obstacles to close route CHMD for the final RH proof, or are you taking shortcuts just to create lean files that build? this here does not look like you are actually solving the problems but are just busy creating lean code that does nothing to our research problem

reminder: do not just search. create new knowledge with an open-ended loop of conjecture -> proof or fail and learn and pivot ->  conjecture -> proof or fail and learn and pivot ->  ... do not give up after a few failed conjectures. always learn and pivot even if it takes thousands of conjectures. be creative. follow unusual and fringe ideas as well as straight forward ideas. it cost almost nothing to try things.

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
- docs/drafts/pipeline/2-fully-proven/acs-pvc-cancellation-on-square-multiple-cofactors.md
- docs/drafts/pipeline/2-fully-proven/acs-pvc-first-primes-beyond-the-conductor.md
- docs/drafts/pipeline/2-fully-proven/acs-pvc-interior-shell-at-seven-fourths.md
- docs/drafts/pipeline/2-fully-proven/acs-pvc-the-quadratic-product-divider.md

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

Read and understand proof route QIC:
- docs/reports/rh-current-frontier-map.md
- docs/reports/rh-killed-routes.md

On every turn:
1. State in chat the proof route.
2. State the hard open mathematical blockers to solve.
3. Research, find and formalize either a theorem or discharge a premise that significantly brings us closer to solve one of the significant mathematical obstacles on that proof route. We are not looking for improving a number, finite proofs for something that is infinite, finding more criteria, more nogos, redressing already known facts, but actual tangible progress in closing this proof route.

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

Do not use web search for things you already know from your training data or can be found in our lean corpus. 

Make good use of the search tool for our lean corpus to find existing work and get leads for new ideas and solutions for your work.

The goal is met when route QIC is fully closed and formalized unconditionally in lean.

## list
1x
- https://arxiv.org/abs/2611.16156 many more odd zeta values are irrational
- https://arxiv.org/abs/2611.17317 c1a reularity of w22 q-valued maps with small laplacian
- https://arxiv.org/abs/2611.13468 a cyclotomic artin-tate formula and sphere packing for K3 surfaces 
- https://arxiv.org/abs/2611.15808 a short route to diening´s averaging criterion in spaces of homogeneous types

2 x
- https://arxiv.org/abs/2611.12500 horizontal estimates for kloosterman sums under hecke eigenvalue constraints
- https://arxiv.org/abs/2611.41332 kloosterman sums and pluecker height zeta functions
- https://arxiv.org/abs/2611.16169 wasserstein rates of all orders for the sato-tate law of kloosterman sums
- https://arxiv.org/abs/2611.08029 on sufficient conditions for rank zero in families of elliptic curves
- https://arxiv.org/abs/2611.24399 stevens approach to klooserman sums on split groups
- https://arxiv.org/abs/2611.13848 a moment proof of the hollman-xiang conjectures on kloosterman polynomials


3x
- https://arxiv.org/abs/2611.11708 derived invariance of the space of holomorphic two-forms
- https://arxiv.org/abs/2611.14090 equivarent quantisation of hypertoric varieties via symplectic cuts
- https://arxiv.org/abs/2611.10478 motivic generating functions and l'derivatives of cohomological automorphic representations
- https://arxiv.org/abs/2611.10255 automorphism of kummer and artin-schreier curves defined by chebyshev polynomials
- https://arxiv.org/abs/2611.08316 p-parity conjecture for panchishkin galois representations
- https://arxiv.org/abs/2611.11955 gauge rigdity and holonomy classifications of time-scaled intertwining cocylces on hilbert bundles

4x
- https://arxiv.org/abs/2611.15605 representation theory and the algebraic k-theory of geometric fields
- https://arxiv.org/abs/2611.14073 explicit plane models for all galois quotients of the hermitian curve
- https://arxiv.org/abs/2611.13963 euclidian and hermitian self-orthogonal codes from divisible codes

5x
- https://arxiv.org/abs/2611.15912 entire boosted hypersurfaces of vanishing mean curvature in schwarzschild spacetime
- https://arxiv.org/abs/2611.16083 tendex lines and short-time deformations: the geometry of lunar tides
- https://arxiv.org/abs/2611.13085 time direction entanglement entropy of free fermion ground states

6x
- https://arxiv.org/abs/2611.16078 simple length multiplicity on X(n)
- https://arxiv.org/abs/2611.16799 nevanlinna theory for generalized tropical meromorphic functions and applications to ultra-discrete equations
- https://arxiv.org/abs/2611.39739 lp integrability of functions with fourier support on high codimension manifolds

7x kronecker
- https://arxiv.org/abs/2611.06256
- https://arxiv.org/abs/2611.16354
- https://arxiv.org/abs/2611.15182
- https://arxiv.org/abs/2611.11593
- https://arxiv.org/abs/2611.10761
- https://arxiv.org/abs/2611.08007  

8x kummer
- https://arxiv.org/abs/2611.16593
- https://arxiv.org/abs/2611.15943
- https://arxiv.org/abs/2611.14187
- https://arxiv.org/abs/2611.12294
- https://arxiv.org/abs/2611.10924
- https://arxiv.org/abs/2611.04118
- https://arxiv.org/abs/2611.00362

9 groessencharacter
- https://arxiv.org/abs/2611.14812
- https://arxiv.org/abs/2611.12844
- https://arxiv.org/abs/2611.09220

10x hochschild
- https://arxiv.org/abs/1302.6534
- https://arxiv.org/abs/1910.09992
- https://arxiv.org/abs/2106.16082
- https://arxiv.org/abs/2611.05915
- https://arxiv.org/abs/2611.04022
- https://arxiv.org/abs/2611.01508

11x dirichlet 1
- https://arxiv.org/abs/2611.17326
- https://arxiv.org/abs/2611.17317
- https://arxiv.org/abs/2611.17253
- https://arxiv.org/abs/2611.17054
- https://arxiv.org/abs/2611.16997
- https://arxiv.org/abs/2611.16978
- https://arxiv.org/abs/2611.16828
  
12 mellin
- https://arxiv.org/abs/2611.18472
- https://arxiv.org/abs/2611.17352
- https://arxiv.org/abs/2611.18526
- https://arxiv.org/abs/2611.15660
- https://arxiv.org/abs/2611.13534
- https://arxiv.org/abs/2611.13129
- https://arxiv.org/abs/2611.13086
- https://arxiv.org/abs/2611.12516
- https://arxiv.org/abs/2611.11028
- https://arxiv.org/abs/2611.09821
- https://arxiv.org/abs/2611.07571
- https://arxiv.org/abs/2611.07186
 
13x Karamata
- https://arxiv.org/abs/2611.24340
- https://arxiv.org/abs/2608.08337
- https://arxiv.org/abs/2605.25591
- https://arxiv.org/abs/2603.08959
  
14 uncertainty
- https://arxiv.org/abs/2611.24604
- https://arxiv.org/abs/2611.24538
- https://arxiv.org/abs/2611.24374
- https://arxiv.org/abs/2611.23922
- https://arxiv.org/abs/2611.23709

15x beurling
- https://arxiv.org/abs/2611.24046
- https://arxiv.org/abs/2611.18900
- https://arxiv.org/abs/2611.17392
- https://arxiv.org/abs/2611.03356
- https://arxiv.org/abs/2610.42022

16x stirling
- https://arxiv.org/abs/2611.21429
- https://arxiv.org/abs/2611.18873
- https://arxiv.org/abs/2611.11194
- https://arxiv.org/abs/2610.35783
- https://arxiv.org/abs/2610.34775

17 Plancherel
- https://arxiv.org/abs/1607.06150
- https://arxiv.org/abs/2611.11593
- https://arxiv.org/abs/2611.09555
- https://arxiv.org/abs/2611.05863
- https://arxiv.org/abs/2611.00445
- https://arxiv.org/abs/2610.40099
- https://arxiv.org/abs/2610.37750

18 liouville
- https://arxiv.org/abs/2611.24842
- https://arxiv.org/abs/2611.24299
- https://arxiv.org/abs/2611.23833
- https://arxiv.org/abs/2611.22698
- https://arxiv.org/abs/2611.22568
- https://arxiv.org/abs/2611.20739
- https://arxiv.org/abs/2611.20600

19 Sobolev
- https://arxiv.org/abs/2611.24828
- https://arxiv.org/abs/2611.24746
- https://arxiv.org/abs/2611.24536
- https://arxiv.org/abs/2611.24317
- https://arxiv.org/abs/2611.23995
- https://arxiv.org/abs/2611.23210
- https://arxiv.org/abs/2611.22942
- https://arxiv.org/abs/2611.22924
- https://arxiv.org/abs/2611.22706

## apply external paper to corpus experiment

task:
find as many places as possible in our lean corpus to apply theorems-lemmas-propositions-correlateries from the listed papers to our lean corpus, formalize them and see what happens. this is experimental. it does not have to be about rh or anything, purely mechanical. it has no goal other than this task done in as many places as possible. explain in chat whenever you find something what this could be about.

papers:
- https://arxiv.org/abs/2611.21429
- https://arxiv.org/abs/2611.18873
- https://arxiv.org/abs/2611.11194
- https://arxiv.org/abs/2610.35783
- https://arxiv.org/abs/2610.34775

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.
   
Non-negotiable working mode rules:
1. If an idea would be interesting, but is missing lean infrastructure, build it no matter the effort, instead of pivoting.
2. use the search tool for our lean corpus. do not read cards or anything, only work directly on lean.
3. Missing mathematical knowledge: create it with a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...
   
use the search tool for the lean corpus to check what already was formalized so you do not duplicate existing work.

put new code into the relevant subfolders to not bloat RHTower and HTGeometry folders even more

goal is met when 250 significant contributions to our lean corpus and research have been made. focus on providing solutions answers insights to the problems in docs/reports/review-1911/todo.md

do not edit the todo.md

formal/GaloisForLFunctions/ExclusionOfTheCriticalState and formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri but not exclusively on them.


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
- overcome an open hard obstacle in a route docs/reports/review-0711/hard-obstacles.md
- finds a solution for removing a wall in docs/reports/review-0711/walls-ledger.md
- find an answer to an open question in a research programme
- gain one of the mathematical tools a research programme is missing
- gain a deeper insight about the problem the field is exploring and the nature of the field itself 
- prove a significant theorem that significantly advances our research about the RH as a whole 
  
Not valid are improvements of numbers, nogos, redressing existing knowledge in new language, or anything that does not clearly count as significant progress.
    
do not use the hgtl7 skill. this is open research into developing a new fields of mathematics. 

research programmes in focus of this task:
- formal/GaloisForLFunctions/ArithmeticLefschetzStepanovTheory/README.md
              
on every turn: 
research, derive, formalize a significant contribution to the field that significantly helps to either:
- find an answer to an open question in the research programme(s)
- gain one of the mathematical tools the research programme(s) is missing
- gain a deeper insight about the problem the field(s) is exploring and the nature of the field(s) itself 
- prove a significant theorem that significantly advances our research about the RH as a whole 

Not valid are improvements of not signficant numbers, redressing existing knowledge in new language, anything that does not clearly count as significant progress.

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
find an opportunity to "connect the dots" between different parts of our lean corpus to overcome an open mathematical obstacle from "## 2.2 Open obstacles" in docs/reports/review-1511/obstacles-summary.md

Not valid are mere improvements of insignificant numbers, redressing existing knowledge in new language, "sidequests" or anything that does not clearly count as significant progress to solve one of the open obstacles.

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

Maintain a working log in logs/. Do not use a README.md as a diary or working log or theorem ledger. Only update when the foundational information in it changes.

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
a while ago we did create these documents:
- docs/reports/review-1911/walls-ledger.md
- docs/reports/review-1911/route-obstacles.md
- docs/reports/review-1911/route-unification-ledger.md
- docs/reports/review-1911/obstacles-summary.md
  
read also but do not edit:
- docs/reports/rh-current-frontier-map.md
- docs/reports/rh-killed-routes.md
  
write new reports from scratch to reflect the current status quo and frontier of our research taking into account all new lean proofs and changes done since the original reports were written:
1. a complete report about each route and route candidate and what the hard mathematical obstacles are that block us from closing the route. split these into a) obstacles that we can solve and are "just work", and b) obstacles that are open mathematical problems nobody has a solution to
2. then create a summary document that combines all the information and:
   2.1 lists all tasks / obstacles that we can solve and are "just work"
   2.2 lists the open mathematical obstacles/research topics nobody has a solution to
   2.3 suggest if you see any opportunity for a "frankenstein" route that creates an RH proof by assembling building blocks from different routes and allowing this way to circumvent the blockers in a single route
   2.4 ideate and describe a breakthrough question that is less "hard" than proving RH or quasi-RH and would bring a real advance and breakthrough to our RH proof research as a whole.
   2.5 ideate and describe a breakthrough question that would bring a breakthrough in our search to find a positivity producer.
   2.6 assume that neither positivity, weil positivity, "spektral" in any form can be part of any rh proof. ideate and describe a breakthrough question that would clearly open wide the path to the RH proof.
   2.7 assume that RH is the mathematical face of a physical phenomen. What is this phenomen? What is a breakthrough question that would either falsify this idea or "put meat on the bone"? 
   2.8 assume that RH is a problem of topology or geometry. ideate and describe a breakthrough question that would clearly open wide the path to the RH proof.
   2.9 ideate whether solving all obstacles to reach the RH proof would require a new field of mathematics, what this field would be about, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
   2.10 ideate whether solving all obstacles to reach an AAL proof/falsification would require a new field of mathematics, what this field would be about, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
   2.11 assume that neither positivity, weil positivity, "spektral" in any form can be part of any rh proof. ideate whether solving all obstacles to reach the RH proof would require a new field of mathematics, what this field would be about, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover
   2.12 assume that RH is a problem of topology or geometry. ideate whether solving all obstacles to reach the RH proof would require a new field of mathematics, what this field would be about, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover
   2.13 design a research programme aiming at constructing (\(\mathbb{F}_{1}\)) (the field with one element),  what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
   2.14. Design a research programme aiming at closing the RH proof route ACS, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
   2.15. Design a research programme aiming at closing the RH proof route ZCG, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
   2.16. Design a research programme aiming at closing the RH proof route ECS, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
   2.17. Design a research programme aiming at closing the RH proof route PM, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
   2.18. Design a research programme aiming at proving the 5/6 quasiRH bound, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.   
   2.19 What is the one big question the is less hard than proving RH outright and would, when answered, bring a real breakthrough in our research because it may kill several routes, establish a new route, or solve a hard mathematical obstacle blocking several routes?
   2.20 Ideate based on everything you have understood about RH, the differente routes in our lean corpus, the advancements and nogos we have proven surpassing external SOTA research, and knowing that likely new mathematics are needed and there is no shortcut and no known mathematical mechanism will deliver the RH proof as otherwise somebody would have found it already, give it your best shot: what is the most likely RH proof route you see - regardless of whether it is already a route we follow or completely new or a "frankenstein"? describe it in form of a research programme with its proof mechanism, steps, possible failures and what these failures would teach us.  
3. based on that an updated wall-ledger where walls have changed, were solved, or new walls were added.
4. also provide a new version of the route-unification-ledger.md which shows which routes are just different faces of the same problem similar to the wall-ledger unifies all walls into 3 core problem families.

do not read other markdown files, only the ones i mentioned.
do not rely only on these markdown files which are partly outdated. use the search tool for our lean corpus to research what our research currently shows. 

first collect information in a working log in logs/ - facts, not process or status updates. only after having collected all information, interprete it, do additional research where new questions arise, and only when no more questions can be asked write the final reports. the expectation is that you do real in-depth research and not just read the markdown files or do some spot checks on recently changed files.

the reports are not diaries or history log, but status quo reports.

replace the reports in folder docs/reports/review-1911/ without history language or "this changed since last review".
do not run builds. this is not a task to verify the work of other agents but to create consolidated reports and "big picture" interpretations on their research results.

make sure to validate every claim. we have seen in previous rounds you simply restating old reports without actually validating that the old report facts were still valid. 

keep in mind that our actual ultimate research goal is to find a full formal proof of RH, not to just make any type of mathematical discoveries.

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
3. Unification of the routes: docs/reports/review-1411/route-unification-ledger.md
4. Hard obstacles: docs/reports/review-1411/route-obstacles.md
5. The hard obstacles (Walls) we have identified and not overcome: docs/reports/review-1411/walls-ledger.md
   
Do not rely only on these markdown files which are partly outdated. Use the search tool for our lean corpus to research what our research currently shows. Do not assume, our research is far ahead of your training data - our lean corpus is the Sota research. Take the time to search and understand. We are expected an accurate, in-depth research and report, not superficial ai-slop that is useless to our frontier research.

Keep a log file in logs/ for your research to note down facts and findings, since this research will go over multiple context window compactions that otherwise may lose information.

The questions for you to answer:
1. What is the big picture of our research? What hard obstacles have we solved? What hard obstacles are still standing between us and an RH proof/falsificiation?
2. Do you see any opportunity to overcome one or more obstacles or significantly solve them partially?
3. Do you see a clear path towards proving quasi-RH?
4. Do you see a clear path towards proving that at least 70% of the zeros of the riemann zeta function lie on the critical line?
5. What is the one big question the is less hard than proving RH or quasiRH outright and would, when answered, bring a real breakthrough in our research because it may kill several routes, establish a new route, or solve a hard mathematical obstacle blocking several routes?
6. Assume that neither positivity, weil positivity, "spectral" in any form can be part of any rh proof. Then what is the one big question the is less hard than proving RH or quasiRH outright and would, when answered, bring a real breakthrough in our research because it may kill several routes, establish a new route, or solve a hard mathematical obstacle blocking several routes?
7. You can interpret the walls as questions we need to answer and for which we and mathematics as a whole do not have the tools to create these answer - if we would create a new field of mathematics that can supply these tools, what would this field be? What would the questions be, what would be its approach/point of view, what its objects, language, foundational principals, criteria it must fulfill, its research topics?
8. Assume that neither positivity, weil positivity, "spectral" in any form can be part of any rh proof. Then you can interpret the walls as questions we need to answer and for which we and mathematics as a whole do not have the tools to create these answer - if we would create a new field of mathematics that can supply these tools, what would this field be? What would the questions be, what would be its approach/point of view, what its objects, language, foundational principals, criteria it must fulfill, its research topics?
9. Design a research programme aiming at constructing (\(\mathbb{F}_{1}\)) (the field with one element),  what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
10. Design a research programme aiming at closing the RH proof route WD, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
11.  Design a research programme aiming at closing the RH proof route ACS, what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
12. Design a research programme to develop general Galois theory that treats the nontrivial zeta zeros as roots of an algebraic equation and classifies their permutation by a corresponding Galois group. what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
13. Lets assume that RH is false. Design a research programme to a) prove that RH is wrong, b) find a concrete counterexample (without computation). s the nontrivial zeta zeros as roots of an algebraic equation and classifies their permutation by a corresponding Galois group. what it would be like, what criteria it must meet, what questions it must answer, what tools it aims to develop, what objects and language and mechanisms it must be built on or would aim to discover.
14. Missed opportunities: Do you see anything in our lean corpus that are missed opportunities to assemble theorems that would bring us a significant breakthrough in solving AAL, ZAL, B13, quasiRH, or RH, or kill a proof route so we do not waste time on researching something that will become a dead end?  

Write a report in docs docs/reports/review-1411/fable.md

do not run any builds. do not search the web. do not grep for sorry or other shit. your job is not to verify of other agents but to write a consolidated report and big picture interpretation of their research. focus on the mathematics.

keep your eyes on the rh proof, that´s the ultimate goal. 

## Init new field programme

read and understand docs/reports/review-1811/obstacles-summary.md

under "## 2.9 What new mathematics might a full proof need?" it suggest a new research programme

Your task: develop this field/research programme and do the actual research and formalization.
We are not interested in busywork, trivial work and discoveries, work on finite solution when the problem is infinite, optimizing numbers that provide nothing for the - we are only interested in focused work on solving the actual problems and questions and topics and move the frontier with every new lean module.

Follow the example of other research programmes: formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri or formal/GaloisForLFunctions/ArithmeticOrientationGeometry

1. All lean code goes into its own subfolder and has its own umbrella per programme.
2. When enough information is established write a foundational README.md per programme:
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

Make good use of the search tool for our lean corpus to find existing work and get leads for new ideas and solutions for your work. But do not just search. create new knowledge with an open-ended loop of conjecture -> proof or fail and learn and pivot ->  conjecture -> proof or fail and learn and pivot ->  ... do not give up after a few failed conjectures. always learn and pivot even if it takes thousands of conjectures. be creative. follow unusual and fringe ideas as well as straight forward ideas. it cost almost nothing to try things.


The goal is done when the programme is fully developed, the questions are answered, the tools are developed as described in the original document.

Start with writing the first draft of README.md for the the programme



read and understand docs/reports/review-1811/obstacles-summary.md

under "## 2.11 Mathematics for a proof by signed cancellation alone" it suggest a new research programme

Your task: develop this research programme and do the actual research and formalization, until all open questions are answered, and a viable producer is found.

Follow the example of other research programmes: formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri or formal/GaloisForLFunctions/ArithmeticOrientationGeometry

1. All lean code goes into its own subfolder and has its own umbrella per programme.
2. When enough information is established write a foundational README.md per programme:
   2.1 the README.md is not a ledger or diary or working log but a foundational document explaning the why, what, how
   2.2 it explains: motivation, objects, language, mechanisms, traps, questions the programme aims to answer, tools it aims to develop, open research topics, foundational pillar theorems, where this field/programme sits in the context of our hole research and how it relates to other research programmes in our corpus, success criteria and criteria for what a contribution to the field/programme must be like.
3. Research and develop the field and add "meat to the bone" with significant contributions to the core research topics, tools and questions of the new field.
4. 
**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Make good use of the search tool for our lean corpus to find existing work and get leads for new ideas and solutions for your work. But do not just search. create new knowledge with an open-ended loop of conjecture -> proof or fail and learn and pivot ->  conjecture -> proof or fail and learn and pivot ->  ... do not give up after a few failed conjectures. always learn and pivot even if it takes thousands of conjectures. be creative. follow unusual and fringe ideas as well as straight forward ideas. it cost almost nothing to try things.


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

read and understand docs/reports/review-1811/obstacles-summary.md

under "## 2.18 Best prospect for a full formal proof" it suggest a new fields/research programme for a RH proof route

it combines elements of route ACS and route PVC. read more about these routes here:
docs/reports/rh-current-frontier-map.md and docs/reports/rh-killed-routes.md

Your task: Research, derive and formalize step by step this proof route as described in the document.

We are not looking for busywork, improving some trivial numbers, redressing of existing knowledge. We are looking for actual progress on solving open problems and closing the route to the RH proof.

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

Goal is met when a proof route is fully closed and formalized in lean and RH is proven. Do not stop until an RH proof is fully formalized.

## new route

do not use the hgtl7 skill.

read: docs/reports/review-1711/obstacles-summary.md

the document suggests under "## 2.3 Where a combined route could work" -> "ECS + ZCG + actual prime counts" a new proof route for RH that combines parts of several routes.

your task: work through this route and assemble it, build the formal bridges and missing connections and missing proofs, solve the open mathematical obstacles. where mathematical infrastructure is required but absent from our lean corpus and mathlib, build it even if effort is high.

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

Goal is met when the RH is proven or the route is provably refuted.

## just work

Do not use the hgtl7 skill.

read docs/reports/review-1711/obstacles-summary.md and understand what problem B13 is about.

your task: work through the open problems unconditionally, formalize their solutions and collaries. start with the easiest tasks and work towards the hardest. do so until you have found and proven a solution for B13.

where necessary lean infrastructure is absent from our lean corpus and mathlib -> build it no matter the effort.

we are not interested in busywork, redressing of existing knowledge, building unnecessary lean infrastructure. solve the tasks.

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

Goal is met when a solution for B13 is found and formalized.

## question paper

docs/reports/review-1911/todo.md asks 18 questions / asks for 18 proofs.

your task: work through each question/proof one by one, answer the question, find a complete solution for it and unconditionally formalize the answer and its implications and collaries as paper proofs ready for another ai agent to formalize in lean.

work backwards, start with question 18, then 17, then 16, ...

We are not interested in estimates, criterias what the answer could be like, what is not the answer, busywork - we accept only a full and final answer/solution to the posed question.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ... 
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Make good use of the search tool for our lean corpus.

Put lean code into the correct subfolder(s), do not bloat RHTower or HTGeometry folders more.


## question

read and understand fully: docs/reports/review-1911/obstacles-summary.md

under "## 2.19 The one smaller question with the largest shared payoff" it asks a question.

your task: answer the question. find a complete solution for everything asked and unconditionally formalize the answer and its implications and collaries in lean.

We are not interested in estimates, criterias what the answer could be like, what is not the answer, busywork - we accept only a full and final answer/solution to the posed question.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ... 
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Make good use of the search tool for our lean corpus.

Put lean code into the correct subfolder(s), do not bloat RHTower or HTGeometry folders more.


Keep your own working log in logs/ to document findings. Do not edit the aal.md file.

Do not use the wall ledger as diary. Only update status, do not add more.

Goal is met when there are no more open or partially solved or sharpened walls.

## Walls

Do not use the hgtl7 skill.

read: docs/reports/review-0911/obstacles-summary.md

on every turn:
conjecture, derive, formalize a significant contribution to solve open mathematical obstacle B13.
 
your ultimate goal is to solve the problems, but do not attempt to solve them outright, but the research towards solving them is the valuable activitity. 

we are not interested in busywork, redressing of existing knowledge, building unnecessary lean infrastructure. you create tangible significant progress to solve B13 or you are wasting time and token.
  
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

Goal is met when you fully solved B13.

Do not edit the summary. Keep a working log in logs/ for documenting mathematical facts you find, not for documenting work activity that has no value for anybody.

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


## wall breaking
context - reports summarizing the current frontier of our research:
docs/reports/review-0811/route-obstacles.md
docs/reports/review-0811/walls-ledger.md
docs/reports/review-0811/route-unification-ledger.md
docs/reports/review-0811/obstacles-summary.md
docs/reports/rh-current-frontier-map.md
docs/reports/rh-killed-routes.md

docs/reports/review-0811/obstacles-summary.md lists under "### Γ — selection, reflection and transport" several open mathematical problems.

your task: solve one of these problems, find and formalize a full solution.

formalize any significant finding you make during your research, if it is not yet in our lean corpus, even if it does not yet solve one of the open mathematical problems. we are not interested in busywork, but actual significant progress and ultimately a full solution to at least one of the open mathemical problems.

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

## Report AAL

Context:
- docs/reports/review-0711/astra.md
- docs/reports/review-0711/astra.md
- docs/reports/review-0711/obstacles-summary.md
- docs/reports/review-0711/route-obstacles.md
- docs/reports/review-0711/walls-ledger.md
- docs/reports/review-0711/route-unification-ledger.md
- docs/reports/rh-killed-routes.md
- docs/reports/rh-current-frontier-map.md

Our next big target is to find a solution to AAL - to either prove or disprove it.

Your task: Research, compile and write a complete report about AAL:
- State clearly what needs to be proven/disproven as mathematical statement.
- List everything we know about the problem directly or indirectly, supporting facts, nogos, possible attack routes, partial solutions, milestones, obstacles already identified, what a proof cannot be like, what a proof must be like, etc.

The outcome is to have an in-depth report we can give to research agents and they understand what AAL is, what is meant by a task to prove or disprove AAL, what information is already available to them and backed up by the corpus and what are the open problems to solve.

Do not rely only on these markdown files which are partly outdated. Use the search tool for our lean corpus to research what our research currently shows. Do not assume, our research is far ahead of your training data - our lean corpus is the Sota research. Take the time to search and understand. We are expected an accurate, in-depth research and report, not superficial ai-slop that is useless to our frontier research.

Keep a log file in logs/ for your research to note down facts and findings, since this research will go over multiple context window compactions that otherwise may lose information.

Put the final report into docs/reports/review-0711/aal.md


Focus only on contributions to our lean code that can contribute to solve any of the mathematical obstacles in:
docs/reports/review-1411/route-obstacles.md or docs/reports/review-1411/walls-ledger.md

## b13
Read these older reports:
- docs/reports/review-1611/obstacles-summary.md
- docs/reports/review-1611/route-obstacles.md

Understand what open obstacle B13 is all about.

Task: Do a 360 degree, in-depth review of our lean corpus and write a detailed report about B13.

Questions:
- In short: What is B13 about?
- Why is it important?
- What questions have we already answered?
- What questions are open?
- What are the open mathematical obstacles to solve that are "just work" most likely and could be done today? 
- What are the open mathematical obstacles to solve that are not just work?
- Is there any missed opportunity in our lean corpus to connect existing proofs to the B13 problem that could deliver insights or even partial solutions to open problems?
- Design a research programme around solving B13: what would it be about, what questions does it answer, what tools does it develop, what language and objects does it use, what are traps, pillar theorems, ... follow examples of research programmes like formal/GaloisForLFunctions/BezoutValuationIncidence/README.md

Use the search tool for our lean corpus extensively.

Keep a log in logs/ to record any mathematically relevant finding, so context window compaction does not lead to information loss. First build this knowledge ledger before writing your final report

Place the final report in docs/reports/review-1711/b13.md