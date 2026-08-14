# Unweighted pro-Kummer holonomy action selects zero charge

- **ID:** ULF-DFPM-FAIL-4
- **Stage:** 5-failed
- **Conjecture:** Summing the chordal cost of all finite root holonomies forces an integer divisor
  charge to vanish.
- **Verdict:** [FALSE] [SHARP LINEAR-CAPACITY SURVIVOR]

For charge (q\in\mathbb Z), depth-(n) root holonomy is

\[
 h_n(q)=e^{2\pi iq/n}.
\]

As (n\to\infty),

\[
 |1-h_n(q)|^2\sim\frac{4\pi^2q^2}{n^2}.
\]

Therefore the unweighted action

\[
 \sum_{n\ge2}|1-h_n(q)|^2
\]

is finite for every integer (q), including nonzero charges.  An infinite root tower and finite
cyclic recurrence do not by themselves provide selection.

The positive survivor is exact: with weights (w_n\ge0), nonzero charge has infinite action if and
only if

\[
 \sum_n\frac{w_n}{n^2}=\infty.
\]

For polynomial capacity (w_n=n^a), the sharp threshold is (a=1).  Linear depth capacity is the
least polynomial weight that selects zero charge.  Full theorem: ULF-DFPM-2.

