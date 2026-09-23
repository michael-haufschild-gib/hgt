## formalize claude

/loop 1m (use the croncreate tool)

your task:
if you are already working on a card, keep going.
else: pick a card from any subfolder within docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/02-analytic-da-entire-functions

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

formalize UNCONDITIONALLY in lean all proven theorem for every single card in: 
- docs/drafts/pipeline/2-fully-proven/chronological
  
add missing infrastructure, lean proofs, everything needed to mark a card as fully done and move it to stage 3 of the pipeline - no simplifications. 

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
7. make sure you don't leave stale lean processes running - clean up after yourself.

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

do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds. every agent can run exactly 1 build process at a time.

do not add hypotheses. always use our custom search tool check first what the lean corpus already contains, to not duplicate existing work.

be efficient with lean. clean up after yourself. do not run large rebuilds. do not run umbrella builds. do only check axioms for what you have created - no need to constantly check stuff we have already checked.

only use the search tool for our lean corpus, not rg.


to create new knowledge use the hgt-fields-medalist skill workflow and heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...

optimize lean code. only build what is necessary. you can yourself only start 1 build procress at a time. be mindful that you are not the only agent working on the lean codebase right now.

note: our research is in several places ahead of literature and your training data, let the lean corpus guide you. do not assume, because your assumptions are based on your outdated training data, not our actual research.

do not touch git. for searching in our lean corpus use the search tool for it. pull in ideas wide from our lean corpus and arxiv, do not just search for direct solutions but indirect and vaguely related topics to get inspiration and new ideas for a solution of a problem.


optimize lean code. only build what is necessary. you can yourself only start 1 build procress at a time. be mindful that you are not the only agent working on the lean codebase right now.

do not touch git. for searching in our lean corpus use the search tool for it. pull in ideas wide from our lean corpus and arxiv, to find solutions to a problem. where mathematical / lean infrastructure is missing in our corpus, build it.


## goal theorems gpt

/goal
Use the search tool for our lean corpus to audit for any remaining hypothesis, prop interface, premise - then attempt to discharge them:
1. reuse existing formal results to discharge every tractable premise
2. create and formally prove missing connector theorems
3. subsume theorems under a larger universal law which is nontrivial
4. use the $hgt-fields-medalist skill´s research process on each non-immediate mathematical obstacle
5. use any tool of ideation possible including but not exclusively value relations and value reflections

lean corpus:
- formal/GaloisForLFunctions/HTGeometry for lean about hypertranscendental functions in general
- formal/GaloisForLFunctions/RHTower for lean about the riemann zeta function
- formal/GaloisForLFunctions/HilbertMetric for lean about hilber spaces and metrics

read only corpus:
- formal/GaloisForLFunctions/QuantumAlg for lean related to quantum algorithm around prime numbers
- formal/GaloisForLFunctions/QECLean.lean for lean related to Quantum Error Correction
- formal/GaloisForLFunctions/PNTPlus.lean for lean related to Prime Number Theorem
  
lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. No computational results can be used in lean proof - computations only support ideas and guidance.
4. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave stale lean processes running - clean up after yourself.


## research paper

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to create novel and significant new knowledge to prove or disprove Artin holomorphy conjecture (https://en.wikipedia.org/wiki/Artin_L-function#The_Artin_conjecture)

research rules:
- use heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... 
- always check that you do not play theatre and actually are creating new knowledge
- focus on hard problems, NO THEATRE, NO INFRASTRUCTURE, EVERY STEP MUST DELIVER PROGRESS
- take a step back and look at the big picture and conjecture how you could reinterpret everything we know so far and where the reasons we got stuck are shadows of a higher universal principle
- pivot when necessary.

add missing infrastructure, lean proofs, everything needed to get this route fully done - no simplifications.

Lean rules:
1. Proofs must be unconditional in lean, no hypotheses, new axioms, prop interfaces, ...
2. Always build in the foreground, 1 process per single agent. You can run builds in parallel to other agents, but only 1 at a time.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Do not run full builds, build missing module olean when needed.
6. Always use  lake env lean <file>  and only lake build <module> for the final audit. Do not forget to wire new modules into the umbrellas.
7. make sure you don't leave stale lean processes running - clean up after yourself.

goal is met when the conjecture is proven or disproven unconditionally without hypotheses or other premises in lean.

goal is met when paper is written and passes a hostile review that confirms that the paper is on a quality level to be published in Nature.
HB — theta-cusp Hawking causal scattering

## research Route

Goal: Create a formal proof or falsification of the riemann hypothesis using one or a combination of routes/route candidates STC, CSB, U, RG, BPC, K-RVM, MPLF, RG-ETA, RG-HF, RHist from docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md

**Lean rules:**
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
7. make sure you don't leave stale lean processes running - clean up after yourself.

**Working mode rules:**
1. Use the search tool for our lean corpus heavily.
2. Do not just search but also create missing knowledge via a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... 
3. Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Your conjectures based on it are bullshit. Use THE WHOLE LEAN CORPUS WITH MUCH MORE IDEAS, SOLUTIONS, TOY PROBLEMS, INNOVATIVE APPROACHES. NEVER EVER USE YOUR TRAINING DATA AS STARTING POINT - IT IS OUTDATED.
4. on every turn state the research topic, what the hard mathematical obstacles are, how your last work has made progress and how your next steps will make progress solving these obstacles. 
5. any work that does not attack and try to solve the hard mathematical obstacles is theatre and a waste of time

goal is met when lean corpus has an uncondtional formal proof/falsification of the RH.


-----
2-form integration + Stokes on manifolds or Radó's triangulation theorem 
What I did not prove, explicitly: the manifold-level statement ∫∫_M K dA = 2πχ(M) for an abstract compact Riemannian surface. It needs either 2-form integration + Stokes on manifolds or Radó's triangulation theorem — neither exists in mathlib,
https://arxiv.org/pdf/2607.24830

## Formalize

Formalize all foundations needed for using "irregular microlocal Riemann–Hilbert theory" in our rh proof research. Once the foundations are formalized, start applying it to existing RH research and expand the lean corpus with significant meaningful infrastructure and possibly novel knowledge.

Skip everything already present in our corpus or mathlib.
Any missing infrastructure you build no matter the effort.

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
7. make sure you don't leave stale lean processes running - clean up after yourself.

Non-negotiable working mode rules:
1. If it cannot be done in a single session -> Does not matter. Do it!
2. If it cannot be done in a single context window -> Does not matter. Do it!
3. If it takes months -> Does not matter. Do it!
4. If it is "research-level construction" -> Does not matter. If there is any way you could build it you build it no matter what.
5. Missing in mathlib -> Build it no matter the effort.
   
do not add hypotheses.

always use our custom search tool check first what the lean corpus already contains, to not duplicate existing work.

goal is met when rh is proven through the lense of "irregular microlocal Riemann–Hilbert theory".




## frontier paper
/goal 

Audit HTGeometry, HilbertMetric, and RHTower and write a paper that exactly and comprehensively maps the current frontier of our research towards an RH proof/disprove:

- All possible proof routes, their endpoint, their chain, their obstacles and open core
- All proof routes that we have identified as dead ends
- The research topics / hypotheseses / conjectures that would bring a leap forward in the research and neither literature nor our corpus can answer yet.

Goal is met when after honest and extensive review you cannot add or change anything to the paper and it is truly a full map of where our current research corpus stands.

Mandatory: You let the lean corpus speak and tell you what is. You do not assume what a proof route should look like or what an obstacle is - your training data is biased towards classical proof routes and has not seen all of our research which in part is novel scientific discovery. Do not assume anything, just read lean code.


## research paper only

/goal 

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to create novel and significant new knowledge about this problem: 

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





## theorem experiment
find as many places as possible in our lean corpus to apply theorems-lemmas-propositions-correlateries from the listed papers to our lean corpus, formalize them and see what happens. this is experimental. it does not have to be about rh or anything, purely mechanical. it has no goal other than this task done in as many places as possible. explain in chat whenever you find something what this could be about.

papers:
- https://arxiv.org/abs/2609.02882
  
Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
7. make sure you don't leave stale lean processes running - clean up after yourself.
   
Non-negotiable working mode rules:
1. If an idea would be interesting, but is missing lean infrastructure, build it no matter the effort, instead of pivoting.
2. use the search tool for our lean corpus. do not read cards or anything, only work directly on lean.
3. Missing mathematical knowledge: create it with a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...
   
use the search tool for the lean corpus to check what already was formalized so you do not duplicate existing work.


are you sure, you are not duplicating work? we have extensive prior work in our lean corpus exactly about this. always use the search tool for our lean corpus.

be efficient with lean. clean up after yourself. do not run large rebuilds. do not run umbrella builds. do only check axioms for what you have created - no need to constantly check stuff we have already checked.

do not pivot on unanswered mathematical problems. your job is precisely to solve problems that neither our lean corpus nor literature have solved yet. use the hgt-fields-medalist skill workflow and heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...

## Research 2
**Goal:** Create novel and significant knowledge about the universal laws and principles of quantum recurrence.

Novel and significant means: It solves a problem neither our lean corpus nor literature have solved yet (as of August 2026).

**Lean rules:**
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. No computations.
4. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave stale lean processes running - clean up after yourself.

**Mandatory reasearch and conjecturing rules:** 
1. always use the search tool for our lean corpus to find ideas, existing work. conjecture based on the lean corpus, not your training data which is behind our research in the lean corpus.
2. always tackle the hardest mathematical problem that neither our lean corpus nor literature have solved yet. missing infrastructure or no existing proof is not reason to pivot but to build the infrastructure and to solve the open problem yourself.
3. to create new knowledge use the hgt-fields-medalist skill workflow and heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...  

goal is met when no further knowledge can be created.


1. Arithmetic signed-incidence / Ward: CCM-FU, D2, E, G, G-CE, P, SP-E, SCE, T1, T2, HC, CFI, PPM, HJ, BW, MSC, PEP, EWQ-V, LI.
2. Global spectral / cofinal operator selection: C1, NB/BD, F2, STC, CSB, O, Q, CLG/TTF, U, SV2, BSH, UEB, PBM, IRK, SEC, BPC, MPLF, W1C, K-RVM, GTA, APF, AKC, S6F, WS2.
3. Singular descent / provenance / completion: CDC, L, TK, PSRC, SC, PCS, TCD, JAS, WBF, XST, NDS, KMSS.
4. Nonlinear scattering / dynamical selection: HB, FZZ-P, RBH, PW-B.

Reminder: 
1. create new knowledge, do not just search and pivot when hitting an unsolved problem - solve it using conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...
2. always use the search tool for our lean corpus AND ALWAYS BASE YOUR CONJECTURES ON OUR LEAN CORPUS, YOUR TRAINING DATA IS OUTDATED
3. WORK ONLY ON THE HARDEST MATHEMATICAL PROBLEMS, NOT ON OPTIMIZING SOME NUMBERS OR BOUNDS. HARD FRONTIER RESEARCH.

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
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. No computations.
4. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave stale lean processes running - clean up after yourself.

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


## create new RH knowledge
create significant novel knowledge towards the riemann hypothesis, riemann zetas, that answers an important question no literature up to september 2026 has answered yet (check arxiv and journals).

Missing mathematical knowledge: create it with a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...

Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Your conjectures based on it are bullshit. Use THE WHOLE LEAN CORPUS WITH MUCH MORE IDEAS, SOLUTIONS, TOY PROBLEMS, INNOVATIVE APPROACHES. NEVER EVER USE YOUR TRAINING DATA AS STARTING POINT - IT IS OUTDATED.

write down high level interpretation of significant facts about the RH problem and solution in docs/drafts/pipeline/1-in-progress/universal-law-field/STATUS.md. it is not a diary or working log, but key points of guiding future research agents where to look and where to not look for a solution of the form "Must be this", "Must be like this", "Must do this", "Must have this", "Must be able to do this", "Cannot be this", "Cannot be like this", "Must have this", "Must be able to do this". If the entry cannot be understood without first researching a specific route, it is not valid.

if computations can help you to find new leads or answer questions which you truly could not find or answer by reasoning, then computations are allowed

run the computations on this runpod: ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519
download results and document them in a subfolder in docs/drafts/pipeline/2-fully-proven/computations. optimize python code for multicore. once all computations are done, write a report in the folder with the results for future agents - no large diary, just enough to understand what you did compute, what the outcome and interpretation/consequences are


## new idea
Create significant knowledge and progress across all our RH proof routes and route candidates and finalize a formal proof of RH in lean: docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md

Use the search tool for the lean corpus, not to find ready solutions but new ideas to brainstorm and conjecture about. Do not just search, but also create missing mathematical knowledge with a heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...

Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Your conjectures based on it are bullshit. Use THE WHOLE LEAN CORPUS WITH MUCH MORE IDEAS, SOLUTIONS, TOY PROBLEMS, INNOVATIVE APPROACHES. NEVER EVER USE YOUR TRAINING DATA AS STARTING POINT - IT IS OUTDATED.

**Lean rules:**
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. No computations
4. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave stale lean processes running - clean up after yourself.
   
**Work rules:**
1. Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Your conjectures based on it are bullshit. Use THE WHOLE LEAN CORPUS WITH MUCH MORE IDEAS, SOLUTIONS, TOY PROBLEMS, INNOVATIVE APPROACHES. NEVER EVER USE YOUR TRAINING DATA AS STARTING POINT - IT IS OUTDATED.
2. Document high level knowledge about the problem as a whole independent of routes in docs/drafts/pipeline/1-in-progress/universal-law-field/STATUS.md. Entries document compact knowledge about RH and its solution in the form "Must be this", "Must be like this", "Must do this", "Must have this", "Must be able to do this", "Cannot be this", "Cannot be like this", Cannot have this", "Cannot be able to do this". If the entry cannot be understood without first researching a specific route, it does not belong here.
3. Update docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md only as a current state, no history, no diary, not logging - only document the current state of all routes and route candidates.
4. Any new turn starts with you stating in chat what the full proof chain is that you are working on and how your new work will deliver significant progress for it.
5. Missing in our Lean corpus or mathlib - Build no matter the effort.

**Computations:**
if computations can help you to find new leads or answer questions which you truly could not find or answer by reasoning, then computations are allowed.

run the computations on this runpod: ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519
download results and document them in a subfolder in docs/drafts/pipeline/2-fully-proven/computations. optimize python code for multicore. once all computations are done, write a report in the folder with the results for future agents - no large diary, just enough to understand what you did compute, what the outcome and interpretation/consequences are

Goal is met when RH is proven or disproven in lean.

again: a radical new proof architecture. no suzuki, no hedenmalm, no weyl positivity, no connes, no burnol, no hilbert-polyia, no spectral shit, no theta shit, no gamma, none of these and other usual suspects.

and use the search tool for our lean corpus


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
  


you are a scientist. use these and other methods to mingle and mangle your conjectures and experiments:
1\. **\*\*Split it into subclaims.\*\*** Prove or test each part separately.
2\. **\*\*Attack it as false.\*\*** Search for counterexamples and edge cases.
3\. **\*\*Reverse it.\*\*** Ask whether the converse, contrapositive, or inverse is easier.
4\. **\*\*Change the viewpoint.\*\*** Rotate it, reflect it, rephrase it, or look at it from another angle.
5\. **\*\*Make it visual.\*\*** Turn it into a shape, machine, path, game, or physical object.
6\. **\*\*Ask what action is happening.\*\*** Are you moving, preserving, compressing, cutting, joining, sorting, counting, or transforming something?
7\. **\*\*Strip it to essentials.\*\*** Keep only the properties truly needed. Remove decoration.
8\. **\*\*Look for similar objects.\*\*** Ask what else has the same key properties.
9\. **\*\*Test small cases.\*\*** Work out the first few examples by hand.
10\. **\*\*Test extreme cases.\*\*** Check zero, one, maximum, infinite, symmetric, degenerate, or pathological cases.
11\. **\*\*Run experiments.\*\*** Generate examples, compute data, draw diagrams, and look for patterns.
12\. **\*\*Find an invariant.\*\*** Ask what stays unchanged while the object changes.
13\. **\*\*Find a monotone quantity.\*\*** Look for something that only increases, decreases, or cannot cross a boundary.
14\. **\*\*Prove a weaker bridge.\*\*** Keep the frozen conjecture unchanged; label any easier statement
&#x20;   \`[BRIDGE]\` rather than silently replacing the hunch.
15\. **\*\*Form a new stronger hunch only independently.\*\*** If failure suggests a different statement,
&#x20;   freeze it as a new conjecture before attacking it; do not add structure merely to rescue the old
&#x20;   conjecture.
16\. **\*\*Use a minimal counterexample.\*\*** Assume the smallest counterexample exists, then try to make it smaller.
17\. **\*\*Change representation.\*\*** Rewrite it as algebra, geometry, graph theory, matrices, probability, order, or optimization.
18\. **\*\*Look for the right theorem.\*\*** Ask what known technique the problem resembles.
19\. **\*\*Write the fake proof.\*\*** Draft the proof you wish worked, then identify the exact gap.
20\. **\*\*Name the missing lemma.\*\*** Turn repeated obstacles into smaller claims.
21\. **\*\*Build a dependency chain.\*\*** Ask: “What would be enough to prove this?” until you reach something manageable.
22\. **\*\*Compare nearby false statements.\*\*** Change assumptions until it breaks; the breaking point reveals the structure.
23\. **\*\*Classify boundary cases.\*\*** Study when equality, failure, or sharpness occurs.
24\. **\*\*Extract the positive residue.\*\*** After every no-go, seek the strongest positive theorem exposed
&#x20;   by the obstruction, state the new insight exactly, and formalize it in Lean once its paper proof
&#x20;   is dependency-closed. If none survives, record the serious attempts explicitly.


only run computations that can suprise you and lead to new insights and ideas and approaches to solve the hard open mathematical problems we are stuck at.
use the scientific methods to design experiments: docs/meta/scientific-method.md 
do not run hour long computation and do not run computations whose result you could also predict by reasoning.

h, also attack open problems using conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... loops



working rules:
1. on every turn state the proof chain, what the hard mathematical obstacles are, how your last work has made progress and how your next steps will make progress solving these obstacles. 
2. any work that does not attack and try to solve the hard mathematical obstacles is theatre and a waste of time
3. use the search tool and deep search and method search extensively
4. do not just search, also attack open problems using conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... loops
5. use arxiv search and single word and broad searches for finding papers not directly related to the problem and see if there is anything useful in the found papers - do not search for your problem or narrow searches, prefer most receent papers (june to september 2026). example searches: "hawking", "commutator", "recurrence", "cauchy", ... - these are examples, create your own search terms. most papers will be useless, but a few will allow to bring in solutions from fields far away from your actual problem

 Do not conjecture or judge or assume or anything on your training data. Your training data is outdated. Your conjectures based on it are bullshit. Use THE WHOLE LEAN CORPUS WITH MUCH MORE IDEAS, SOLUTIONS, TOY PROBLEMS, INNOVATIVE APPROACHES. NEVER EVER USE YOUR TRAINING DATA AS STARTING POINT - IT IS OUTDATED.

 And be a scientist man, do not just focus on one fucking narrow thing that you have somehow decided is the only way to solve the riddle, but always ask what it means for the whole proof chain when you learn something new or see something fail


 install -d -m 700 /root/.ssh
printf '%s\n' 'ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIP8vO+PBmlBuPv8KtZBV3FSoeHt+xUw5pS+rcugVNfHj michael-macbook' >> /root/.ssh/authorized_keys
chmod 600 /root/.ssh/authorized_keys
ssh-keygen -lf /etc/ssh/ssh_host_ed25519_key.pub


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



 establish the two core bridges to confirm that the proposed proof chain can even work:
1. Identification: does the complete physical action actually produce the diagnostic used by the RH receiver, with all corrections and boundary terms retained?
2. Selection: does the source enforce its vanishing, for a reason independent of RH, while permitting the known critical-line zeros?
**Lean rules:**
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. No computations
4. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave stale lean processes running - clean up after yourself.