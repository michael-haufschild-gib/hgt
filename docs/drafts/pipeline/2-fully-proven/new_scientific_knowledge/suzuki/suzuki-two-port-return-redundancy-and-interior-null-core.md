# Suzuki's exterior two-port return is redundant; the interior null equation is the whole scale gap

- **ID:** `suzuki-two-port-return-redundancy-and-interior-null-core`
- **Stage:** 2-fully-proven
- **Type:** EXACT LOGICAL CLASSIFICATION / FAILED-CONNECTOR THEOREM
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-wiener-cutoff-closed-graph-relation.md`,
  `suzuki-carleman-flat-port-weighted-strip-barrier.md`

## 1. Result

The condition called `SUZUKI-CLOSED-TWO-PORT-RETURN` does not add a new exterior equation to
Suzuki's completed zero-mode problem.  On the exact graph relation it collapses to the original
interior null equation.

Let \(I=(-a,a)\), \(P=1_I\), and let

```text
A=p_a(D)
```

be Suzuki's literal whole-line multiplier.  Let \(\chi\) be the high-pass cutoff used in the
valuation-Wiener inverse.  For

```text
u in D_A(I)
 ={u in L2(R): Pu=u and Au in L2(R)},                   (1)
```

put \(b=Au\).  The exact coefficient construction gives one \(c\in L^2_x(\ell^1)\) and the
low-frequency port \(u_{\rm low}=(1-\chi)(D)u\) such that

```text
Ev(c)=chi(D)u,
u=Ev(c)+u_low.                                           (2)
```

Then:

1. the exterior evaluation condition is automatic:

   ```text
   (1-P)[Ev(c)+u_low]=0;                                 (3)
   ```

2. the completed interior return condition is exactly

   ```text
   Pb=0  iff  P A u=0;                                   (4)
   ```

3. hence graph relation + exterior evaluation + completed interior return is precisely

   ```text
   u in D_A(I),       P A u=0.                           (5)
   ```

No third constraint remains.  In particular,

```text
SUZUKI-CLOSED-TWO-PORT-RETURN
```

is not a stronger coupled theorem from which trace-zero regularity could be derived.  After
unfolding its definitions it is exactly

```text
Pu=u,  PAu=0,  beta_+(u)=beta_-(u)=0
  -> u in H1_0(I).                                      (6)
```

That is the original completed trace-zero scale-gap theorem.

The flat Carleman profile from the predecessor card already belongs to the full multiplier graph
domain and satisfies `(3)`.  Thus exterior evaluation cannot be the hypothesis that removes it.
Only the literal equation \(PAu=0\) can do so.

## 2. Exact redundancy proof

Equation `(2)` is the reconstruction identity of the closed Wiener relation.  Since \(Pu=u\) in
the definition `(1)`,

```text
(1-P)[Ev(c)+u_low]
 =(1-P)u
 =0,
```

which proves `(3)`.  This argument uses neither \(b\), the zero equation, endpoint traces, nor a
Carleman estimate.  Therefore exterior evaluation is not a return law: it is the support
condition rewritten after a high/low decomposition.

By definition \(b=Au\).  Applying \(P\) gives

```text
Pb=PAu.
```

This is `(4)`.  Combining `(1)`, `(3)`, and `(4)` proves `(5)`.

Conversely, any \(u\) satisfying `(5)` enters the graph construction.  Its coefficient state and
low port obey `(2)`, hence `(3),` and \(Pb=PAu=0\).  Thus the implication works in both
directions: the supposedly coupled conditions define exactly the original supported nullspace.
`QED`

## 3. The cutoff commutator is an identity, not extra return data

The coefficient state obeys

```text
(a_a(D)+T_a)Pc
 =P chi(D)S b+[a_a(D),P]c.                              (7)
```

When \(Pb=0\), the first term is the analytic low-pass leakage

```text
P chi(D)S b=-P(1-chi)(D)S b.                            (8)
```

The remaining cross block is

```text
P[a_a(D),P]c=-P a_a(D)(1-P)c.                           (9)
```

Equations `(7)`--`(9)` are exact decompositions of \(PAu=0\) after introducing the Wiener
parametrix and cutting it componentwise.  They do not impose a second boundary condition on
\((1-P)c\).  Indeed \((1-P)c\) is already determined by \(u\) through the global inverse.

Therefore a proof which treats `(9)` as an independently constrained Feshbach return gains no
information.  The positive Feshbach self-energy becomes useful only after an independently
coercive exterior equation has been specified.  Here the exterior residual \(b=(1-P)Au\) is free
output data of the supported Dirichlet problem, not a vanishing exterior equation.

## 4. The flat profile lies in the complete graph relation

Take, near the right endpoint,

```text
F(L)=exp(-sqrt(L)),
u(a-r)=F(log(1/r)),                                     (10)
```

and multiply by a smooth cutoff supported in a one-sided endpoint collar.  Then \(u\) is bounded,
compactly supported, and of bounded variation.  Indeed the uncut endpoint germ is monotone and
has total variation equal to its endpoint-to-collar change; the smooth cutoff adds finite
variation.

Every compactly supported bounded-variation function on \(\mathbb R\) belongs to \(H^s(\mathbb
R)\) for every \(0<s<1/2\).  One direct proof uses

```text
||u(.+h)-u||_2^2
 <=||u(.+h)-u||_1 ||u(.+h)-u||_infinity
 <=2||u||_infinity Var(u)|h|,                           (11)
```

and the translation-difference characterization of \(H^s\):

```text
integral_(|h|<1)
 ||u(.+h)-u||_2^2/|h|^(1+2s) dh<infinity
 iff s<1/2.                                             (12)
```

Choose any \(s\in(0,1/2)\).  Since

```text
log<xi><=C_s(1+|xi|^s),                                 (13)
```

`(12)` implies

```text
log<D>u in L2.                                          (14)
```

Every other part of \(p_a(D)\) is bounded on \(L^2\): the prime term is a finite sum of
translations, \(q_a(D)\) is a bounded multiplier, and the scalar term is bounded.  Hence

```text
p_a(D)u in L2,
```

so `(10)` belongs to \(D_A(I)\).  The exact Wiener coefficient state exists, `(2)` holds, and
therefore its exterior evaluation satisfies `(3)`.

The predecessor calculation proves

```text
sqrt(L)F(L)->0,
u notin H1,
exp(sigma L)d_L Carleman(u) notin L2
for every sigma>0.                                      (15)
```

Thus even the **complete** graph relation, exact high/low reconstruction, support return, both
low counterterms, and zero trace do not imply the desired weighted estimate.  The sole missing
hypothesis is \(PAu=0\).  This proves that the interior null equation is genuinely load-bearing,
not merely one item in a three-condition list. `QED`

## 5. Correct frontier

The previous frontier diagram

```text
exterior evaluation
+ interior completed equation
+ trace zero
 -> weighted Carleman decay
```

suggested three independent inputs.  The correct diagram is

```text
support + graph reconstruction
  -> exterior evaluation automatically;

literal supported null equation PAu=0
+ both half-log traces zero
  -> H1_0 ?                                              (16)
```

The question mark in `(16)` is the entire trace-zero problem.  Any successful proof must extract
a new coercive, quasianalytic, sign, or arithmetic consequence from Suzuki's exact interior
operator.  More carrier reconstruction, exterior support bookkeeping, Carleman boundedness, or
Feshbach terminology cannot supply it.

This also separates the nonzero-trace Evans problem.  Root-port return/injectivity may still be
an independent RH-bearing boundary theorem for modes with nonzero half-log trace, but it does not
strengthen the zero-trace branch through `(3)`.

## 6. Hostile audit

1. **No claim that the interior equation is redundant.**  It is the unique load-bearing
   hypothesis and remains open.
2. **No flat zero mode claimed.**  The flat profile satisfies graph membership and exterior
   reconstruction, not \(PAu=0\).
3. **No abstract-carrier gain claimed.**  Equations `(7)`--`(9)` are recognized as equivalent
   bookkeeping for the original equation.
4. **No Feshbach sign deletion.**  Positive self-energy remains correct when a genuine exterior
   block is eliminated; the theorem shows there is no independently vanishing exterior equation
   in this Dirichlet reconstruction.
5. **No RH claim.**  Trace-zero interior nullspace, nonzero-trace return, and raw Evans
   injectivity remain open.

## 7. Novelty boundary

Support projections, high/low reconstruction, and graph domains are classical.  Candidate-new
source knowledge is the exact negative classification for Suzuki's completed carrier:

```text
the proposed exterior-return hypothesis is identically the support hypothesis,
the flat obstruction already satisfies the entire graph/exterior relation,
and the only remaining discriminator is the literal interior null equation. (17)
```

This prevents another layer of source-reconstruction work from being mistaken for progress on
the RH-bearing scale gap.  External priority is unaudited.

## 8. Lean certificate

Sections 1--3 are formalized unconditionally in

```text
formal/GaloisForLFunctions/HTGeometry/TwoPortReturnRedundancy.lean
```

```text
exterior_evaluation_of_support   (3): P u = u and u = Ev c + u_low force
                                 (Ev c + u_low) - P (Ev c + u_low) = 0
interior_return_eq               (4): b = A u gives P b = P A u
twoPortReturn_iff                (5): support ∧ exterior evaluation ∧ interior return
                                 ↔ support ∧ interior equation
twoPortReturn_iff_of_residual    the same with the residual named as the card writes it
commutator, proj_commutator_apply
                                 (9): for idempotent P, P [a,P] c = -P a (1-P) c, so the cross
                                 block imposes nothing on (1-P) c
highPass_eq_neg_lowPass          (8): a vanishing full pass makes the high- and low-pass parts
                                 negatives of each other
```

The statements are proved for an arbitrary linear map and idempotent on an arbitrary module, which
is the right generality: the theorem is a *logical* classification of the three conditions, and it
therefore applies verbatim to whichever concrete multiplier `p_a(D)` and cutoff `chi` the source
supplies.  Formalizing it did not require the analytic graph construction, because the
construction enters only through the reconstruction identity `(2)`, which is a hypothesis of the
statement in exactly the way the card states it.

Section 4's `H^s` criterion is now formal, in

```text
formal/GaloisForLFunctions/HTGeometry/SobolevWeightDecay.lean
```

```text
MemSobolevWeight                 square integrability against the weight (1+ξ²)^s
normSq_le_of_bounded_of_decay    a transform bounded by M and by K/|ξ| obeys
                                 ‖F ξ‖² ≤ (2M²+2K²)/(1+ξ²)
integrable_sobolevWeight_decay   (1+ξ²)^{s-1} is integrable on the line exactly for s < 1/2
memSobolevWeight_of_decay        hence such a transform lies in every weight below one half
```

This is the exact threshold the section uses.  The two bounds it consumes are themselves theorems,
in

```text
formal/GaloisForLFunctions/HTGeometry/FourierDecayFromDerivative.lean
```

```text
norm_fourier_le_integral_norm            ‖f̂(ξ)‖ ≤ ‖f‖₁
norm_fourier_mul_le_integral_norm_deriv  ‖f̂(ξ)‖ · 2π|ξ| ≤ ‖f'‖₁
memSobolevWeight_of_integrable_deriv     hence f̂ lies in every Sobolev weight below one half
```

So an integrable function with integrable derivative — which is what a monotone bounded profile on
a compact collar is, its total variation being exactly `‖f'‖₁` — meets the criterion, and `1/2` is
the borderline precisely because the decay is of order one.

What remains for the specific flat profile is the differentiability hypothesis at the endpoint
itself: `exp(-sqrt(log(1/r)))` has an infinite one-sided derivative there, so it is covered by the
bounded-variation form of the estimate rather than the differentiable form proved here.  Extending
`norm_fourier_mul_le_integral_norm_deriv` from `Differentiable` to `BV` is one Stieltjes
integration by parts.  No Lean theorem here assumes it.

## Gates

- [x] prove exterior evaluation equals reconstructed support
- [x] prove completed return equals the original interior null equation
- [x] identify the proposed coupled theorem with the original trace-zero scale gap
- [x] prove the flat profile belongs to the complete multiplier graph domain
- [x] prove it satisfies exact high/low exterior reconstruction
- [x] isolate \(PAu=0\) as the unique hypothesis absent from the flat obstruction
- [ ] derive a new source-specific consequence from \(PAu=0\)
- [ ] prove or refute trace-zero nullspace regularity
- [ ] prove completed Evans injectivity
- [ ] RH or whole-Connes no-go
