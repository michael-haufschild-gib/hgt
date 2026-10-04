# Critical transverse slope beyond the global affine barrier

- **ID:** tt-critical-transverse-slope (C71)
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** TT, global actual third-minor slope.
- **Statement:** Determine whether q>b(h) suffices for S>0; if it does
  not, identify and prove the actual nonlinear constraint excluding the
  remaining transverse adverse mode.

## Corpus and precise conjecture

C70 proves actual q>b(h)=1/12−7h/72 globally. C69 proves actual S>0
on a tail. C65 gives P=h17*minor, Q=h19*S and Q0=−648C(r−12t).
The exact first critical jet suggests restricting t=r*b(h), then
studying the second h jet. This is a structural sign test, not numeric
bound tuning. Searches: /tmp/tt_c71_affine_slope_search.json
(partialfalse, gen1225438); /tmp/tt_c71_jet_factor_search.json (partial,
gen1225546, no useful restricted hits); /tmp/tt_c71_pderiv_comm_search.json.
Source proofs of polynomial flow conjugacy and commuting partials read.

## Exact learning so far

The complete second pUU and mixed pUJ tenth-moment jets passed Lean
in /tmp/TTC71AffineSplitJets.lean. Full-polynomial expansion exceeded
default heartbeats; splitting the existing source parts passed without
raising limits. pJJ tenth moment vanishes on the critical face. The
first U eighth-moment jet has the predicted constant plus linear r.

The next audit derives the directional statements, not yet claimed:

    d/dh M10(h,r,r*b(h)) at 0 = 0,
    d²/dh² M10 at 0 = −2*6^12*945*24^5+(6^12*1679616/6)*r²,
    d/dh M8 at 0 = 6^10*105*24^4,
    d²/dh² P at 0 = 2*axisMinorMass−(C/6)*r².

If these hold, conjugating the full field to s=t−r*b(h) gives, at
h=s=0, g=(0,−108r,0) and ∂h²g_s=−(9/2)r². Since P_s=12C,
the predicted second slope jet is −108Cr², hence a negative h²
coefficient −54Cr² on the affine barrier. This sign is NOT yet proved.
A small strict positive affine error of order h² would still leave
negative slope. This would close only the strengthened static cone,
not actual-source positivity or RH.

## Candidate positive survivor / next source invariant

The nonlinear condition q−Tq²>b(h), T=9−u²=r*h², cancels exactly
the predicted next adverse coefficient. Its global validity is open.
The exact field split for y=q−Tq²−b was kernel-certified in
/tmp/TTC71QuadraticField.lean:

    Hy=6T*R+6(1−2Tq)A*y,
    R=(1−2Tq)(D+q²A)+(7/216)q*Hh+2Vq².

No sign of R, no actual nonlinear barrier, and no global S sign has
been proved. Next: finish the exact slope jet, then attack this
nonlinear boundary dynamics using the actual global orbit constraints.

## Audit status

C70 fully migrated/wired/indexed, standard3. C71 scratch work only.
One owned foreground Lean audit at a time. No computations outside
Lean's checked symbolic algebra; Python only handles source text.

C71 affine minor second jet now VERIFIED: MinorJet audit3 exit0,
standard3 for affineMinor_second and affineMoment10_second. Thus the
full directional formulas above are established. Two early audits had
only script errors (eval map change, constructor inequality, complex
HasDerivAt instance equality); corrected without changing statements.
Chart audit1 active: polynomial shift s=t−r*b(h), exact flow conjugacy,
and critical field second jet. No slope jet yet asserted.

Next nonlinear dynamics insight: use z=(q−b)/T−q², not y=Tz.
The exact source ODE predicts
 z′=(k/u)*([A(1−2Tq)+2V]*z+R).
C70 already gives z≥−q². Thus negative z cannot escape to −infinity
on the actual tail, without proving a new bounded rescaled remainder.
The known q=b+o(h), T=o(h) determine the leading tail sign of R/h.
This gives a concrete route to tail positivity. Global proof still
requires a new inward sign on R=0 while z≤0; there C70 and Tq<h give
b≤q≤b/(1−h). This is a narrowed source region, not a proved R sign.

C71 full second slope jet VERIFIED: SlopeJet audit2 exit0 standard3,
planeJet2 r (affineShift scaledSlope)=−108*C*r². Exact flow conjugacy
and transverse field jets used; no sign or source premise. A factor
Q(h,r,r*b(h))=h²*core_r(h), core_r(0)=−54*C*r², and the resulting
negative boundary sign are now under audit. The next positive survivor
will be the exact sign classification under a quadratic displacement
s=a*h², predicting core_r,a(0)=54*C*(144a−r²). Its threshold matches
the proposed nonlinear source barrier q−Tq²>b to leading order.

C71 quadratic classification VERIFIED: QuadraticDisplacement audit2
exit0 standard3. Exact factor Q(h,r,r*b(h)+a*h²)=h² core_r,a(h),
core_r,a(0)=54C(144a−r²). Hence fixed real r,a give an eventually
positive slope if r²<144a, negative if 144a<r². Equality remains open.
This is the positive no-go survivor: a sharp second transverse sign
classification, not merely negation of the affine-cone claim.
The explicit r1,a1/288 family is now under coarse-cone audit; it has
strict q>b and retains the negative second slope coefficient.

C71 COMPLETE: unconditional exists_affineCone_negative_slope falsifies
coarse-cone plus strict C70 affine barrier as a pointwise criterion.
Positive survivor quadraticSlope_sign classifies both signs by the
exact threshold 144a=r² along t=r*b(h)+a*h²; equality remains open.
Seven production leaves passed direct serial leaf audits; eleven
imported capstones standard3, audit exit0. RHTower umbrella wired;
index exit0. P5 tt-third-slope-affine-cone contains dependency-closed
paper proof; frontier map updated. C72 nonlinear actual invariant
q−Tq²>b is now the active conjecture, with inward forcing sign open.
Global actual slope/fullquadratic/fourthgap/join/allrank/RH remain OPEN.
