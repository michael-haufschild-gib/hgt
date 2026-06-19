# Multi-`q`-Difference Galois Theory for L-Functions
## Part III — The Dynamical Realization

*Manuscript draft (publication prose). Continues Parts I–II. This is the field's most novel layer: the boundary of the
prime-lattice connection is a quasiperiodic cocycle, and the motivic/Hodge-theoretic invariants of a module coincide
with the dynamical (Lyapunov, Oseledets, rotation-number) invariants of that cocycle. We are careful to state the
dictionary in its correct, typed form — several naive equivalences are false, and we say so.*

---

### 7. Weight, Newton, and Lyapunov

A module `M` over the arithmetic base, restricted to the boundary `|x_p| = |q_p|^{1/2}`, defines a cocycle over the
prime-lattice dynamical system: the transfer matrices `A_p` iterated along the flow. The asymptotics of this cocycle
carry the module's arithmetic.

**Realization 7.1 (weight = Oseledets filtration).** *This is a definitional identification — the dynamical
realization — not a coincidence of two independently-defined objects:* the boundary cocycle of `M` is a specific
object, and we *identify* its dynamical invariants with the module's weight data. The exponential growth rate of
`\|A_p^{(n)}\|` along the boundary cocycle is, by definition, the Lyapunov exponent of `M`; the associated filtration by
growth rates is the Oseledets filtration (whose existence is the Oseledets multiplicative ergodic theorem [import]). A
module is *pure* of a single rate exactly when this filtration is trivial — after a semisimple/unitary normalization
that removes unipotent polynomial growth. *The only theorem-level (non-definitional) content in this section is the
Mazur inequality 7.2.*

We emphasize a distinction that an earlier draft conflated. *Weight* has two avatars. The **Newton polygon** of the
module — the polygon of Lyapunov slopes — is a dynamical object. The **Hodge filtration** — the de Rham filtration of
the connection — is a different, algebraic object. They are not equal; the comparison between them is the content of:

**Import 7.2 (Newton ≥ Hodge = Mazur).** Over function fields, the Newton polygon lies on or above the Hodge polygon;
this is Mazur's inequality. In the dynamical language it states that the Lyapunov slopes dominate the Hodge slopes —
a constraint, not an identity.

The correct slogan is therefore *Newton = Lyapunov*, with *Newton ≥ Hodge* an inequality. The conflation of Newton and
Hodge weight was a genuine error of the discovery phase, corrected here.

---

### 8. Boundary cocycles and the difference Morales–Ramis correspondence

The classical Morales–Ramis theorem relates the integrability of a Hamiltonian system to the solvability of the
differential Galois group of its variational equation. The field has a difference analogue, relating the Galois group
of a module to the dynamics of its boundary cocycle. We state it in the typed form that is actually true; the naive
"solvable ⟺ reducible ⟺ `L=0`" triple equivalence is *false*, and the failures are instructive.

**Theorem 8.1 (the typed dictionary).** Let `M` be a module with boundary cocycle of Lyapunov exponent `L`.
1. If the cocycle is unitary or tempered (bounded transfer matrices) then `L = 0`.
2. If `L > 0` then the cocycle admits no bounded/unitary normalization; in particular `M` is not tempered.
3. Reducibility of `G_M` and `L = 0` are *independent* in general: a compact nonabelian irreducible cocycle (for
   instance an `SU(2)`-valued one) has `L = 0` while being irreducible, and a scalar cocycle of non-unit modulus is
   abelian (reducible) yet has `L > 0`.

The safe implications are the typed ones of (1)–(2); the equivalences must be qualified by the cocycle type
(unitary/tempered versus general). This corrects an earlier overstatement.

**Theorem 8.2 (arithmetic cocycles are elliptic).** Every arithmetic module (the `L`-function locus, with Satake
parameters on the unit circle under Ramanujan) has `L = 0`. The CM and non-CM cases are distinguished not by Lyapunov
exponent — both vanish — but by reducibility: CM is reducible (imprimitive, induced from a Hecke character), non-CM is
irreducible-primitive with equidistributed Satake angles (Sato–Tate). (Imports: Ramanujan/Deligne for temperedness;
Sato–Tate/BLGHT for equidistribution; Avila's global theory of `SL_2` cocycles for the rank-two dynamics.)

This is the dynamical face of the organizing principle: arithmetic lives in the *elliptic* (`L=0`) regime, the
non-generic boundary of the generically-hyperbolic (`L>0`) flora. The supercritical generic cocycle, with `L>0`, is
the transcendence-maximal non-arithmetic inhabitant. The Lyapunov computations supporting this picture are archived
(`computations/lyapunov_dmr`, `computations/satake_angles_cm_noncm`).

---

### 9. Periods are dynamical invariants

The field's transcendence theory (Part IV) rests on identifying its periods with dynamical quantities.

**Theorem 9.1 (realization comparison).** The de Rham fiber functor (governing transcendence) and the Betti fiber
functor (governing the boundary dynamics) of a module are isomorphic over `ℂ`; the comparison isomorphism is the period
matrix. Its entries are the dynamical invariants of the boundary cocycle: Lyapunov exponents, rotation numbers, and
boundary values. Transport along the comparison preserves invariant subspaces across the two realizations.

*Proof (structural).* Both functors are tensor-exact and faithful into `\mathrm{Vec}_ℂ`; a neutral Tannakian category
has any two fiber functors isomorphic over `ℂ` (the torsor of isomorphisms is trivialized over the algebraically closed
field). The identification of the comparison entries with dynamical invariants is the boundary specialization of the
connection. ∎

A caution, recorded honestly: maximal transcendence is *not* a formal consequence of irreducibility. That the period
matrix has maximal transcendence degree requires a genuine transcendence input — a period theorem of
Siegel–Shidlovsky / analytic-subgroup type — available in the imported special settings (function fields, CM), and
conjectural in general (Part IV, the Grothendieck period conjecture). The realization comparison sets up the problem;
it does not by itself solve it.

The proven instances of "periods are dynamical" are concrete: the gap-labelling theorem realizes rotation-number
periods as elements of `ℤ + ℤα` (rank-two case, certified in `computations/gap_labelling_periods`); Chudnovsky's
theorem realizes CM periods as the dimension of the CM torus orbit; Papanikolas's theorem realizes, over function
fields, the *full* period conjecture as the dimension of the difference-Galois group. These are the validations on
which Part IV builds.

---

*End of Part III. The dynamical realization is the field's novel contribution to the dictionary between arithmetic and
dynamics — weight as Oseledets filtration, Newton as Lyapunov spectrum, periods as cocycle invariants — stated in the
corrected, typed form. Part IV (transcendence and periods: the infinite-base Siegel–Shidlovsky, the period conjecture
on its known loci, and the hypertranscendence theorem) develops the transcendence consequences. The research draft
§21–33, §39 carries the full development, including the self-corrections (#7 Newton vs Hodge, #8 the typed dictionary)
reflected above.*
