# Route-R raw-resolved-relative cone character law

- **ID:** `route-r-raw-resolved-relative-cone-character-law`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / NO-GO CORRECTION WITH POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [RAW PREDIFFERENTIAL NON-NILPOTENCE]`
  `[RESOLVED ABSOLUTE FACTORIZATION NO-GO] [ORDINARY RELATIVE CONE CHARACTER]`
  `[UNRESTRICTED COMPLEX NO-GO RETRACTED] [NOVELTY UNVERIFIED] [NOT RH] [NO LEAN WRITTEN]`
- **Statement:** Literal raw Route-R reporter is non-nilpotent off centre, and every nonzero
  physical orientation fails to factor through resolved absolute cohomology. Retained source class
  instead gives a nonzero relative mapping-cone class carrying two ordinary cone characters whose
  values are exactly the forward and reflected physical Cartier classes.
- **Inputs:**
  `../../1-in-progress/route-r-prime-depth-bv-wold-curved-source-differential.md`,
  `../../3-formalized/new_scientific_knowledge/route-r-resolved-bv-wold-source-frame-annihilation.md`,
  `../../3-formalized/new_scientific_knowledge/ccm/rational-adelic-prime-isotropy-relative-xi-chain-map.md`,
  `../../1-in-progress/route-r-graded-variable-ideal-fixed-xi-comparison.md`,
  `../../3-formalized/new_scientific_knowledge/ccm/graded-variable-ideal-fixed-xi-comparison.md`.

## Goal

Test two precise claims:

1. whether raw scalar Route-R maps themselves form a cochain complex;
2. whether fixed-ideal physical character factors through constructed resolved absolute complex.

Ordinary stabilizations, alternative extensions, and relative-cone characters are allowed. This
scope is essential: an earlier unrestricted anti-complex claim was false.

## 1. Literal objects

Fix actual Xi divisor copy `rho`, set

\[
 t=t_\rho=2\Re\rho-1\in(-1,1),
 \qquad
 c_\rho=\Xi_{\mathbb C}^{(m_\rho)}(\rho)\ne0,
 \tag{RRC.1}
\]

and use ordinary prime `p=2`. Grade-uniform algebraic formulas below remain valid for arbitrary
real `t`; “physical same-fibre” always means specialization `(RRC.1)`.

### Raw scalar reporter

For prime-depth vertices `i_e=(2,e)`, let

\[
 (D_t^0f)(i,j)=U_t(i,j)f(j)-f(i),
 \tag{RRC.2}
\]

\[
 (D_t^1\omega)(i,j,k)
 =U_t(i,j)\omega(j,k)-\omega(i,k)+\omega(i,j).
 \tag{RRC.3}
\]

Corpus proves

\[
 \theta_{01}+\theta_{12}-\theta_{02}=-\frac{\log2}{8},
 \qquad U_t(i,j)=e^{t\theta_{ij}}.
 \tag{RRC.4}
\]

This scalar reporter forgets diagonal clock factors of actual triangular source frame. It is not
itself functorial source transport away from centre.

### Source, resolved complex, and Stokes functional

Let

\[
 C_p^0=A,
 \qquad C_p^1=A\oplus\mathbb C,
 \qquad C_p^2=\mathbb C,
 \tag{RRC.5}
\]

with

\[
 D_0x=(\alpha_px-x,\epsilon_0x),
 \qquad D_1(y,z)=\epsilon_0(y).
 \tag{RRC.6}
\]

Then `D_1D_0=0`, and

\[
 \eta_p=(0,1)\in Z^1(C_p),
 \qquad [\eta_p]\ne0.
 \tag{RRC.7}
\]

The bilateral Stokes regulator

\[
 I_p(y,z)=z-R_p^A(y)
 \tag{RRC.8}
\]

satisfies `I_pD_0=0`, so it descends on all source cohomology:

\[
 \bar I_p:H^1(C_p)\longrightarrow\mathbb C,
 \qquad
 \bar I_p([(y,z)])=I_p(y,z),
 \qquad \bar I_p([\eta_p])=1.
 \tag{RRC.9}
\]

Let `(X_t^\bullet,delta)` be resolved Route-R complex and

\[
 \Phi_p:C_p^\bullet\longrightarrow X_t^\bullet
 \tag{RRC.10}
\]

the constructed strict cochain map. For prime-localized Xi conormal `L_p in X_t^0`,

\[
 \Phi_p^1(\eta_p)=\delta_0L_p.
 \tag{RRC.11}
\]

### Fixed physical quotient

Put

\[
 \mathcal S=\mathbb C^{\mathcal P},
 \qquad I=\ell^1(\mathcal P),
 \qquad V=\mathcal S/I,
 \tag{RRC.12}
\]

and `F_t(p)=p^t p/(p+1)^2`. Define forward and reflected physical characters

\[
 P^{\mathrm{fwd}}_{t,\rho}([x])
 =c_\rho\bar I_p([x])[F_{-t}],
 \qquad
 P^{\mathrm{ref}}_{t,\rho}([x])
 =c_\rho\bar I_p([x])[F_t].
 \tag{RRC.13}
\]

On retained source class their values are

\[
 c_\rho[F_{-t}],
 \qquad c_\rho[F_t].
 \tag{RRC.14}
\]

Forward value is nonzero exactly for `t<=0`; reflected value is nonzero exactly for `t>=0`.

## 2. Theorem A — raw pair is not a complex off centre

Direct expansion gives

\[
 (D_t^1D_t^0f)(i_0,i_1,i_2)
 =\bigl(U_{01}U_{12}-U_{02}\bigr)f(i_2).
 \tag{RRC.15}
\]

By `(RRC.4)`,

\[
 \frac{U_{01}U_{12}}{U_{02}}=2^{-t/8},
 \tag{RRC.16}
\]

hence

\[
 (D_t^1D_t^0f)(i_0,i_1,i_2)
 =U_{02}(2^{-t/8}-1)f(i_2).
 \tag{RRC.17}
\]

For `t ne 0` and `f(i_2) ne 0`, `(RRC.17)` is nonzero. Therefore unaugmented pair
`(D_t^0,D_t^1)` is not itself an ordinary cochain complex away from centre. This does not exclude
enlarged ordinary complex incorporating `K_t=D_t^1D_t^0` as correction data. `[PROVED HERE]`

## 3. Theorem B — exactification creates nonzero relative class

Use cone convention

\[
 \operatorname{Cone}(\Phi_p)^n=X_t^n\oplus C_p^{n+1},
 \qquad
 d(x,c)=(\delta x-\Phi_pc,-D c),
 \tag{RRC.18}
\]

with complexes extended by zero outside displayed degrees. Then

\[
 \kappa_{p,\rho}=(L_p,\eta_p)
 \in\operatorname{Cone}(\Phi_p)^0
 \tag{RRC.19}
\]

is closed because

\[
 d\kappa_{p,\rho}
 =(\delta_0L_p-\Phi_p^1\eta_p,-D_1\eta_p)=0.
 \tag{RRC.20}
\]

It is not boundary. A degree-zero boundary has second coordinate `-D_0c`; equality to
`eta_p` contradicts `[eta_p] ne 0`. Therefore

\[
 [\kappa_{p,\rho}]\ne0
 \in H^0(\operatorname{Cone}(\Phi_p)).
 \tag{RRC.21}
\]

Its projection to shifted source cohomology is `[eta_p]`. Resolved absolute cohomology kills source
class, while relative cone cohomology retains it. `[PROVED HERE]`

## 4. Theorem C — nonzero orientation cannot factor through resolved absolute complex

Regard `V[1]` as `V` in cochain degree one with zero differential. Suppose cochain map

\[
 \Psi:X_t^\bullet\longrightarrow V[1]
 \tag{RRC.22}
\]

agreed after `Phi_p` with one physical orientation on `eta_p`. Then

\[
 \Psi^1\Phi_p^1(\eta_p)
 =\Psi^1(\delta_0L_p)
 =d_V\Psi^0(L_p)=0.
 \tag{RRC.23}
\]

For forward orientation this contradicts `(RRC.14)` when `t<=0`; for reflected orientation it
contradicts `(RRC.14)` when `t>=0`. At off-centre grade, vanishing orientation factors through zero
map; no stronger claim is made. At `t=0`, neither orientation factors. `[PROVED HERE]`

Thus physical observer does not descend through resolved **absolute** cohomology whenever its
literal value is nonzero.

## 5. Theorem D — two displayed degree-zero sequences have zero connecting maps

Variable-ideal extension

\[
 0\longrightarrow J_t\longrightarrow E_t
 \xrightarrow{\operatorname{Reg}_t}\mathbb C\longrightarrow0
 \tag{RRC.24}
\]

splits by `c mapsto c e_t`. Fixed quotient is

\[
 0\longrightarrow I\longrightarrow\mathcal S\longrightarrow V\longrightarrow0.
 \tag{RRC.25}
\]

Regarded with current degree-zero complex structures, both have zero connecting homomorphism into
degree one. In `(RRC.24)` this also follows from explicit splitting. Physical map is direct
coefficient multiplication, not Bockstein of either displayed sequence. `[PROVED HERE]`

No claim is made about other extensions, shifted complexes, topological derived categories,
mapping cylinders, or curvature-corrected stabilizations.

## 6. Theorem E — physical values are ordinary relative cone characters

Define source cochain maps

\[
 \widehat P^{\mathrm{fwd}},\widehat P^{\mathrm{ref}}:
 C_p^\bullet\longrightarrow V[1]
 \tag{RRC.26}
\]

by zero in all degrees except degree one, where

\[
 \widehat P^{\mathrm{fwd},1}(y,z)
 =c_\rho I_p(y,z)[F_{-t}],
 \qquad
 \widehat P^{\mathrm{ref},1}(y,z)
 =c_\rho I_p(y,z)[F_t].
 \tag{RRC.27}
\]

They are cochain maps because `I_pD_0=0`.

For either orientation `epsilon`, define

\[
 \chi^\epsilon:\operatorname{Cone}(\Phi_p)^\bullet\longrightarrow V[0]
 \tag{RRC.28}
\]

by

\[
 (\chi^\epsilon)^0(x,c)=\widehat P^{\epsilon,1}(c),
 \qquad
 (\chi^\epsilon)^n=0\quad(n\ne0).
 \tag{RRC.29}
\]

Only nontrivial chain identity occurs from cone degree `-1`. For `(0,a)` with `a in C_p^0`,

\[
 (\chi^\epsilon)^0d(0,a)
 =-\widehat P^{\epsilon,1}(D_0a)=0.
 \tag{RRC.30}
\]

Thus each `chi^epsilon` is ordinary cochain map. On relative class,

\[
 \boxed{
 \chi^{\mathrm{fwd}}_*([\kappa_{p,\rho}])=c_\rho[F_{-t}],
 \qquad
 \chi^{\mathrm{ref}}_*([\kappa_{p,\rho}])=c_\rho[F_t].}
 \tag{RRC.31}
\]

Hence physical value does factor through **relative cone cohomology**. Character reads shifted
source coordinate, not chosen primitive `L_p`. No Toda bracket, differential character, or
genuinely secondary operation is forced. `[PROVED HERE]`

## 7. Countertheorem — raw curvature also admits ordinary stabilization

Let raw reporter spaces be `R_t^0,R_t^1,R_t^2` and `K_t=D_t^1D_t^0`. Define

\[
 \widetilde R_t^0=R_t^0,
 \qquad
 \widetilde R_t^1=R_t^1\oplus R_t^0,
 \qquad
 \widetilde R_t^2=R_t^2,
 \tag{RRC.32}
\]

\[
 \widetilde d_0f=(D_t^0f,f),
 \qquad
 \widetilde d_1(\omega,g)=D_t^1\omega-K_tg.
 \tag{RRC.33}
\]

Then

\[
 \widetilde d_1\widetilde d_0f
 =D_t^1D_t^0f-K_tf=0.
 \tag{RRC.34}
\]

Therefore an enlarged ordinary complex can retain raw maps and exact curvature correction. Direct
sum with `Cone(Phi_p)` contains raw curvature, relative class, and physical cone character. This
stabilization may be nonminimal and source-nonnatural, but it refutes every unrestricted claim
that ordinary complexes cannot encode all data. Excluding it requires explicit naturality,
minimality, or source-admission axioms. `[PROVED HERE]`

## 8. Exact positive survivor

Strongest dependency-closed package is

\[
 \boxed{
 \left(
 \operatorname{Cone}(\Phi_p),
 [\kappa_{p,\rho}],
 \chi^{\mathrm{fwd}},
 \chi^{\mathrm{ref}}
 \right),}
 \tag{RRC.35}
\]

with evaluations `(RRC.31)`. Exact results force distinction between:

1. raw predifferential curvature;
2. resolved absolute exactification;
3. relative cone class;
4. fixed-ideal relative characters.

They do not force a new cohomology operation. Actual open theorem is source-derived simultaneous
nonerasure of two fixed-orientation evaluations on distinguished retained class.

## 9. RH leverage and exact boundary

Within critical strip, `(RRC.31)` gives:

\[
 \chi^{\mathrm{fwd}}_*([\kappa])\ne0\iff t\le0,
 \qquad
 \chi^{\mathrm{ref}}_*([\kappa])\ne0\iff t\ge0.
 \tag{RRC.36}
\]

Both are nonzero exactly at `t=0`. Global simultaneous nonerasure on every actual Xi divisor is
equivalent to RH. Theorem constructs relative carrier and characters but does not source-force
simultaneous nonerasure.

## 10. No-go closure

- **Killed overclaim:** raw curvature, resolved Stokes class, and physical Cartier value cannot be
  encoded in any ordinary complex.
- **Exact killing mechanism:** curvature-corrected stabilization `(RRC.32)`--`(RRC.34)` and ordinary
  cone characters `(RRC.28)`--`(RRC.31)` are explicit counterexamples.
- **Strongest positive survivor:** nonzero relative cone class with two exact ordinary physical
  characters `(RRC.35)`.
- **New insight:** physical obstruction is failure of descent through resolved **absolute**
  cohomology, not failure of ordinary homological representation. Relative cohomology is sufficient.
- **Status:** corrected theorem is dependency-closed on paper and passed independent hostile audit.

## 11. Hostile falsifiers

1. Reject Theorem A if raw reporter is silently replaced by resolved triangular transport.
2. Reject same-fibre wording unless `t=2 Re(rho)-1`.
3. Reject Theorem C orientation-by-orientation when corresponding physical value vanishes.
4. Reject any unrestricted ordinary-complex no-go because `(RRC.32)` is countermodel.
5. Reject “secondary” or primitive-sensitive language: cone character ignores `L_p`.
6. Reject RH claim: source law forcing both pairings remains open.
7. Reject finite-prime scalarization: finitely supported sequences vanish in `S/I`.

## 12. Novelty boundary

Mapping cones, curvature-corrected stabilizations, and relative characters are classical.
Corpus-specific formulas and their conjunction may be new to project; external priority and
significance are unverified. No abstract novelty claim is made.

## Lean-return note

No Lean work authorized. Corpus already formalizes all literal inputs. Later target is finite
homological wrapper: cone closed/nonboundary class, relative characters, absolute-factor no-go,
and stabilization countermodel. Search existing mapping-cone modules before selecting files.

## Gates

- [x] 0 → 1: literal objects and typed questions isolated
- [x] 1 → 2: dependency-closed corrected paper proof
- [x] strongest positive survivor extracted
- [x] hostile counterexample integrated
- [x] no circular critical-line/nonerasure assumption
- [ ] Lean formalization
- [ ] source-defined simultaneous two-orientation law
- [ ] RH

## Log

- 2026-08-08 — raw nonnilpotence, relative cone class, and absolute factorization no-go proved.
- 2026-08-08 — hostile review refuted unrestricted ordinary-complex/secondary-operation claim;
  ordinary cone characters and curvature-corrected stabilization added as exact stronger survivor.
