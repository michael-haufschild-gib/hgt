# PW-B source-amplitude-uniform incidence test

- **Chain:** literal two-event CTP → source-faithful oriented optical incidence → fixed-grade magnitude/extinction → RH.
- **Hard obstacle:** establish incidence without suppressing cap/lift or choosing a fitted phase/normalization.
- **Corpus basis:** `fullCausalSourcePair_amplitude_biquadratic`, `pwb_fullCircleCrossBranch_eq_fullCausalSourcePair`, `weakSourceFlux_eq`, `weakSourceFlux_pair`, `pwb_weakSourceMass_pos`, and critical-fibre CTP cancellation.

**Frozen conjecture.** Scale the literal quadratic source by a real amplitude `r`, and scale its linear weak response and forcing by `r²`. The completed CTP scales as `r⁴`; the crossed optical flux (flux times opposite-branch mass) scales as `r⁸`. Hence one fixed oriented incidence at both `r=1` and `r=2` forces the crossed flux to vanish, and strict source mass then forces `Re ρ=1/2`. This would kill amplitude-uniform incidence as an off-line producer, while retaining fixed-amplitude/renormalized contact possibilities.

**Falsifier:** corpus CTP may acquire additional amplitude dependence through its full kernel, or weak optical mass may fail strict positivity. Test both in Lean using the exact literal definitions. No numerical computation.
