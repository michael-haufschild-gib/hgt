# PW-B actual Gamma-source adjoint defect

- **ID:** PW-B-GAMMA-ADJOINT-SOURCE-TEST-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** Every positive integer Gamma mode has finite reversible weighted squared norm and finite strictly positive ground-to-mode cross-mass. The literal admitted forward and reflected-ground response pairings differ by -log(n) times that mass, strictly negatively for every n>1.

## Actual source and admission

With the existing Q(x)=sqrt(x)*exp(-x) and reversible density
w(x)=exp(-x-1/x)/x on x>0, define

`phi_n(x)=sqrt(n)*exp(-(n-1)*x)`.

Lean identifies this with the literal source ratio Q(n*x)/Q(x). For
positive integer n, it is positive and at most sqrt(n). Therefore
w*phi_n and w*phi_n^2 are integrable by the admitted density w and
constant majorants. The cross-mass

`M_n=integral_0^infinity w(x)*phi_n(x) dx`

is strictly positive: its integrand is positive throughout the positive
ray, which has positive measure. This is an admitted finite mass, not
a totalized integral used without integrability.

The forward response is defined using the actual weighted translation:

`[T_h(Q(n*·))(x)-exp(-h)*Q(n*x)]/[h*Q(x)]`.

The existing atom transport identity makes it phi_n(x) times the full
Frullani difference kernel. That kernel is integrable, with integral
-log(n), so the complete forward response is -log(n)*phi_n(x).
The reflected-ground response is defined separately from the literal
reflected translation:

`[R T_h R Q(x)-exp(-h)*Q(x)]/[h*Q(x)]`.

Source fixation makes it zero. Its complete integral is admitted.
Finally the outer weighted response products are admitted before their
integrals are compared.

## Exact obstruction and positive survivor

The difference between the ground-paired forward response and the
mode-paired backward ground response is exactly

`-log(n)*M_n`.

For n>1 this is strictly negative. Thus the uncorrected adjoint pairing
identity fails on these actual source modes. This does not assume that
a closed operator with a specified domain has already been constructed;
it tests the literal admitted integrals that such an identity would
have to identify if its domain included these modes.

The positive survivors are the finite positive cross-mass, the exact
all-mode defect formula and weighted square admission. They preserve the
source information that an adjoint correction must account for. The
[literal cutoff theorem](pw-b-gamma-adjoint-cutoff-contact.md) supplies
a retained 2*log(x) contact. The [admitted logarithmic pairing](pw-b-gamma-adjoint-log-moment.md)
now proves that its integral against this same cross-density equals the
whole defect, using the actual reciprocal derivative and substitution.
The full original cutoff transposition and operator domain remain open.

PW-B is not retired. A complete corrected adjoint, common arithmetic
domain, physical requirement for the pairing, actual Xi occurrence and
independently source-forced fixed-grade balance remain open. RH is
unproved. The [continuing attack](../1-in-progress/pw-b-gamma-reversible-pairing.md)
keeps these obligations distinct.

## Verification

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaAdjointSourceTest.lean`.
The final scratch passes all28 public declarations, with only propext,
Classical.choice and Quot.sound in every axiom report. Identical proof
bodies are promoted and one RHTower umbrella import is wired. The
targeted leaf build passed in230s, rebuilding only this leaf. Index
regeneration passed (five changed entries, zero removals in the shared
tree); all28 public names are unique in source and API, and every proof
body matches the passing scratch. Repository formal lint passed. All
source-test scratch/build/index/lint processes are terminal. No full or
umbrella build, numerical experiment, added axiom, commit or push was
used.

The [search record](../1-in-progress/pw-b-gamma-adjoint-contact-searches.json)
and [attack journal](../1-in-progress/pw-b-source-orientation-attack.md)
retain partial corpus coverage, method checks and recent broad primary
literature reads. Generic conditional adjoint or finite matrix results
were not used to assert an adjoint for these singular source responses.
