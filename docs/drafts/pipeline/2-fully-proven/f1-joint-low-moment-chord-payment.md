# Joint first- and third-moment payment

- **ID:** F1-JC
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [Two-moment payment](../1-in-progress/f1-primitive-variance-joint-payment.md)
- **Statement:** Every real odd C² unit-window test satisfies
  `Q(F)+(3203/320)(∫xF)²≥∫F²/1000`.

## Paper proof

[PROVED HERE]

Let `B₀` be the audited polynomial reflection operator, `m=19/50`, `M=37/20`,
`p₁=u`, `p₃=P₃`, and `Eᵢⱼ=⟨pᵢ,B₀pⱼ⟩` on `(0,1)`.
The required exact polynomial bounds are

`E₁₁≥12/25`, `E₃₃≥51/500`, `0≤E₁₃≤1/30`.

For `s=2−2log2`, the reflection entries are

`R₁₁=s−s²+s³/6`,
`R₁₃=s−7s²/2+7s³/2−5s⁴/4+s⁵/8`,
`R₃₃=s−6s²+11s³−35s⁴/4+27s⁵/8−5s⁶/8+5s⁷/112`.

The interval `613705638/10⁹≤s≤613705640/10⁹` gives
`R₁₁≥27/100`, `−7/100≤R₁₃≤−3/50`, `R₃₃≥−83/1000`.
Use `49/100≤w≤4902/10000`, `a≥11/20`, and the exact multiplication entries

`a/3+1/10+1/28+1/54+1/88`,
`1/35+1/63+1/99+1/143`,
`a/7+23/630+13/924+7/858+19/3432`.

Young's inequality then gives
`E_B₀(xp₁+yp₃)≥(7/25)x²+(217/2250)y²`.
The inverse chord therefore has the joint upper bound

`((m+M)‖xp₁+yp₃‖²−E_B₀(xp₁+yp₃))/(mM)
 ≤(249/250)((2/3)x²+(20/63)y²)`.

Put `L=(3/2)⟨p₁,G⟩²+(63/20)⟨p₃,G⟩²` and choose
`P=(3/2)⟨p₁,G⟩p₁+(63/20)⟨p₃,G⟩p₃` in the audited inverse-chord
Young inequality. It yields `E_B₀(G)≥(251/250)L`.
Together with `E_B₀(G)≥(19/50)‖G‖²`, this gives
`E_B₀(G)−L≥19‖G‖²/12550≥‖G‖²/1000`.
The established comparison with `D` and `Q`, followed by dilation, gives the statement.

## Status

Exact rational certificates pass a Lean scratch check. Joint Lean proof underway. This pays `3/2` of the
first-moment coefficient `5123/1280`; its remaining `3203/1280` and full positivity
are still open.
