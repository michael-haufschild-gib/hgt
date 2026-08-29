## formalize claude

/loop 1m (use the croncreate tool)

your task:
if you are already working on a card, keep going.
else: pick a card from any subfolder within docs/drafts/pipeline/2-fully-proven/universal-law-field/ 

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

formalize UNCONDITIONALLY in lean any proven theorem from all these cards: 
- docs/drafts/pipeline/2-fully-proven/bessel-order-intensity-hypertranscendence.md
- docs/drafts/pipeline/2-fully-proven/deninger-algebraic-cyclotomic-milnor-amplitude.md
- docs/drafts/pipeline/2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md
- docs/drafts/pipeline/2-fully-proven/route-e-coprime-square-root-mobius-product-sign-law.md
- docs/drafts/pipeline/2-fully-proven/route-e-forbidden-support-e3-stability.md
- docs/drafts/pipeline/2-fully-proven/route-e-growing-reciprocal-marker-low-breadth-transport.md
  
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

do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.

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
Audit lean corpus for any remaining hypothesis or Prop interface - then attempt to discharge it:
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


LEAN PROOFS MUST BE UNCONDTIONAL!!! ALWAYS CHECK BEFORE WRITING NEW LEAN CODE WHAT THE PROJECT LEAN CODE ALREADY CONTAINS AS PROOF OR BUILDING BLOCK YOU SO YOU DO NOT DUPLICATE WORK.

where mathematical knowledge is missing use the $hgt-fields-medalist skill to create it.

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

## research Route

use the [$hgt-fields-medalist](/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md) skill to create novel and significant new knowledge towards the lean formalized proof or falsification of the riemann hypothesis.

Current ledger of the major routes and route candidates: docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md
Current ledger of possible RH endpoints and their proof obligations: docs/reports/endpoints.md

research rules:
- do not get "married" to a single route. use the whole lean corpus for fresh and inovative ideas. look for hidden gems and for possibilities to solve problems using building blocks from several routes and the lean corpus not directly related to rh.
- do not waste time on rediscovering what literature already proves - instead formalize what literature proves and only then start your own research to expand beyond that.
- use heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ... 
- always check that you do not play theatre and actually are creating and significant new knowledge
- focus on hard problems, NO THEATRE, NO INFRASTRUCTURE, EVERY STEP MUST DELIVER PROGRESS
- take a step back and look at the big picture and conjecture how you could reinterpret everything we know so far and where the reasons we got stuck are shadows of a higher universal principle
- pivot when necessary.

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use lake env lean \<file>. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
7. make sure you don't leave stale lean processes running - clean up after yourself.
   
Non-negotiable working mode rules:
1. use the search tool for our lean corpus. do not read cards or anything, only work directly on lean.
2. every action you take must be aimed at moving the actual frontier of our research and to create signficant knowledge that is not known to your training data or current SOTA literature in arxiv or similar platforms. always attack and overcome the research frontier.
3. never pivot because of something is missing in our lean corpus. build the missing thing.
4. be creative, for example see if you can reformulate your problem in a different framework like using Noether´s theorem to turn a conservation question into a question of symmetry, or ask what if - like "what if i treat prime packets as light-like physical entities, what property or laws about light and light cones could i test if they translate to my problem?" or "what if i make this finite thing infinite?" or "for this no-go, for what thing is this no-go actually a positive necessity and what other properties or constraints or laws for this thing could i translate for my actual problem?"
5. use the scientific method tools.
      
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






### mathematician
how would a fields medal mathematician approach this problem? what our corpus is, is technically decades of research with a lot of minor advancements beyond current sota research by other researchers. but the mathematician sees that all routes get stuck sooner or later, that something is missing, that they are looking at the problem from the wrong point of view and there must be some higher mathematical theory in play that is not yet known to humanity. how would they approach finding this higher mathematical theory? what questions would they ask? what research would they do? what would they do?


## theorem experiment
find as many places as possible in our lean corpus to apply any form of the Korteweg–De Vries equation, Kawahara equation, Kadomtsev–Petviashvili equation, Shrira-Pesenson equation, Nonlinear Schrödinger equation, Solitons math and physics, formalize it and see what happens. this is experimental. it does not have to be about rh or anything, purely mechanical. it has no goal other than this task done in as many places as possible. explain in chat whenever you find something what this could be about.

Construct source-defined graded/Fredholm object carrying an odd index or weight. Reflection should follow from duality, horizontal orientation from eta/spectral flow or polarization, and infinite completion from index stability. Xi should appear only afterward as determinant or trace formula.

Lean rules:
1. Proofs must be unconditional and closed in lean, no premises, no hypotheses, no added axioms, ....
2. Always build in the foreground, 1 process per single agent.
3. Be efficient, use caching, batch instead of running constant loops of tiny edits and rebuilds
4. No computations.
5. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
6. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
7. make sure you don't leave stale lean processes running - clean up after yourself.
   
Non-negotiable working mode rules:
1. If an idea/conjecture would be interesting, but is missing lean infrastructure, build it no matter the effort, instead of pivoting.
2. use the search tool for our lean corpus. do not read cards or anything, only work directly on lean.
3. Missing mathematical knowledge: create it with the hgtl7 or hgt-fields-medalist skill workflow and heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...
   
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
3. No computational results can be used in lean proof - computations only support ideas and guidance.
4. Always use  lake env lean \<file>  and only lake build \<module> for the final audit. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check in scratch, build only oleans that are needed, wire finished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave stale lean processes running - clean up after yourself.

**Mandatory reasearch and conjecturing rules:** 
1. always use the search tool for our lean corpus to find ideas, existing work. conjecture based on the lean corpus, not your training data which is behind our research in the lean corpus.
2. always tackle the hardest mathematical problem that neither our lean corpus nor literature have solved yet. missing infrastructure or no existing proof is not reason to pivot but to build the infrastructure and to solve the open problem yourself.
3. to create new knowledge use the hgt-fields-medalist skill workflow and heavy conjecturing loop workflow: conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  conjecture -> proof or fail and pivot ->  ...  

**Mandatory computation rules:**
1. Computations run always on runpod: ssh root\@216.81.151.68 -p 16020 -i \~/.ssh/id\_ed25519
2. optimize python code for multicore.
3. download results and document them in docs/drafts/pipeline/2-fully-proven/computations.
4. Only compute things you cannot already predict the result of.
5. Do not run hours long computations.

goal is met when RH proof is formalized.