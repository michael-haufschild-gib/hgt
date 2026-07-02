I can’t honestly give an unconditional proof of either missing statement as written. The reason is not just that it is “hard”; it is that the first statement is **exactly** the strict-a.e. theorem that was missing, and the second beta-preimage version is **not implied** by the positive-measure information already proved. The file explicitly asks for a complete proof of the open problem, defines one-sidedness by ball-connectivity, and warns that density alone does not solve W2.

What I can provide rigorously is the following “no-free-lunch” theorem: it proves that the missing step cannot be manufactured from harmonic measure positivity plus density of beta-preimages. Any valid solution must add a genuinely new dynamical/geometric input.

## Theorem: the missing alternatives are genuinely new inputs

Let (c\in M\setminus{0,-2}), and let

[
S_c={p\in J_c:\ p\text{ is one-sided in the strict ball-connectivity sense}}.
]

Then:

1. The assertion

[
\text{every positive }\mu_c\text{-measure subset of }J_c\text{ contains a point of }S_c
]

is equivalent to

[
\mu_c(S_c)=1.
]

So proving it is exactly proving strict one-sidedness for harmonic-measure-a.e. Julia point.

2. The beta-preimage substitute

[
\partial W\setminus K_{c_2}
\text{ contains a strict beta-preimage point of }J_{c_1}
]

does not follow from positive (\mu_{c_1})-measure of (\partial W\setminus K_{c_2}), nor from density of beta-preimages. The beta-preimage set is countable and (\mu_{c_1})-null.

Therefore the two missing routes from my earlier response are not lemmas already contained in the known facts. They are additional theorems one would have to prove.

## Proof of part 1

Let

[
S_c={p\in J_c:\exists \rho_0>0\ \forall 0<\rho\le \rho_0,\ B(p,\rho)\setminus K_c
\text{ is connected}}.
]

This is exactly the file’s definition of one-sidedness.

Assume first that

[
\mu_c(S_c)=1.
]

Let (E\subset J_c) be any Borel set with

[
\mu_c(E)>0.
]

If (E\cap S_c=\varnothing), then

[
E\subset J_c\setminus S_c,
]

so

[
\mu_c(E)\le \mu_c(J_c\setminus S_c)=0,
]

contradiction. Hence every positive-measure subset of (J_c) contains a strict one-sided point.

Conversely, assume every positive (\mu_c)-measure subset of (J_c) contains a point of (S_c). If

[
\mu_c(J_c\setminus S_c)>0,
]

then the positive-measure set

[
E=J_c\setminus S_c
]

contains no point of (S_c), contradicting the assumption. Therefore

[
\mu_c(J_c\setminus S_c)=0,
]

equivalently

[
\mu_c(S_c)=1.
]

Thus the proposed selection lemma is not weaker than strict-a.e. one-sidedness. It is precisely the same theorem.

## Proof of part 2

Let

[
B_c={\text{iterated }f_c\text{-preimages of the }\beta\text{-fixed point along branches avoiding }0}.
]

The file states that these beta-preimage points are one-sided and dense in (J_c).

But (B_c) is countable. Indeed, at depth (n), the equation

[
f_c^n(z)=\beta_c
]

has at most (2^n) solutions. Hence

[
B_c\subseteq \bigcup_{n\ge 0} f_c^{-n}(\beta_c)
]

is a countable union of finite sets.

The equilibrium measure (\mu_c) is non-atomic. Therefore

[
\mu_c(B_c)=0.
]

Consequently, a positive-measure set can completely avoid all beta-preimages. In fact,

[
J_c\setminus B_c
]

has full (\mu_c)-measure and contains no beta-preimage at all.

So if one has only proved that

[
E:=\partial W\setminus K_{c_2}
]

has positive (\mu_{c_1})-measure, that does **not** imply

[
E\cap B_{c_1}\neq\varnothing.
]

A positive-measure set may avoid any prescribed countable dense set.

This is exactly why the file warns that density of one-sided points is insufficient: after the suitable index choice, (\partial W\setminus K_{c_2}) is a nonempty subset of (J_{c_1}), but it need not be relatively open in (J_{c_1}).

## What a real completion would have to prove

A valid completion must prove one of the following genuinely new statements.

Either:

[
\boxed{\mu_c(S_c)=1
\quad\text{for every }c\in M\setminus{0,-2}.}
]

Then the harmonic-measure argument works.

Or, more specifically for the two-set problem:

[
\boxed{
(\partial W\setminus K_{c_2})\cap S_{c_1}\neq\varnothing
}
]

after choosing the index as in Known Fact 4. Known Fact 4 gives only that, after a swap,

[
\partial W\setminus K_{c_2}
]

is a nonempty subset of (J_{c_1}).  It does not give openness inside (J_{c_1}), and without such openness, density of beta-preimages cannot select a point.

So the honest conclusion is:

[
\boxed{
\text{I cannot supply the requested unconditional proof without proving a new strict-a.e. theorem.}
}
]

The previous harmonic-measure proof reduces the original problem to that theorem, but does not prove it. Any proof that merely invokes Fatou–Lindelöf–Zdunik/Zakeri accessibility still proves only a uniaccessible point, not the file’s strict ball-connectivity point.

---

# Audit note (2026-07-02)

This file restates, as a standalone "no-free-lunch" theorem, the two results already
delivered and audited in `06-answer-addition.md`: Part 1 is the equivalence
(selection lemma) ⟺ (`μ_c(S_c) = 1`), Part 2 is the β-preimage no-go (countable +
non-atomic ⟹ `μ_c(B_c) = 0`, so positive measure never forces meeting a countable
dense set). Both are correct; no new mathematics beyond that file. The same
measurability footnote applies: taking `E = J_c ∖ S_c` as a positive-measure set
presumes `S_c` is `μ_c`-measurable — the clean formulation is via a Borel hull, as in
the restated problem. The two boxed completion targets at the end are exactly the
full form and the (W1) special-set form of
[07-full-measure-one-sided.md](07-full-measure-one-sided.md), where the residual now
lives (with the calibration `μ_{−2}(S_{−2}) = 0` showing non-smoothness must be used,
and the comb-vs-arc dichotomy locating the crux). Status of Problem 6 is unchanged:
PARTIALLY ANSWERED, potential-theoretic half proven, selection half open as Problem 7.
