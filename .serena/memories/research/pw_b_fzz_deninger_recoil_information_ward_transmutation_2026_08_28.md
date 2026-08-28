# PW-B/FZZ-P/Deninger recoil--information--Ward transmutation (HC40, 2026-08-28)

Formalized
`GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFZZDeningerWardTransmutation`.

At every Borel grade `k`, the first-winding Parikh--Wilczek functional-equation partner real-growth
imbalance equals `-P_k` times HC38's real Deninger reflect-gauge Ward charge, where
`P_k=2(2k+1)/(k+1)^2>0`. It also equals the strictly positive ratio `P_k/C(Re q)` times HC37's
nonlinear FZZ information force. Consequently PW imbalance and FZZ force have identical strict
orientation off line; PW balance, FZZ equilibrium, and Deninger reflect-gauge equivariance are
pointwise equivalent. Universal balance at any one grade is equivalent to RH.

New bounded-audit route knowledge: PW recoil activation brightness is not the selector. Reflected
Hawking/CPT partner balance carries exactly the same shared Ward charge as FZZ information and
Deninger equivariance. Remaining producer is a coefficient-faithful physical theorem forcing this
partner balance on all divisor modes.

Verification: direct Lean check passed; targeted module build passed (8834 jobs); all eight public
theorems use only `propext`, `Classical.choice`, `Quot.sound`; lint had no HC40 finding; module wired
into RHTower umbrella without full umbrella build. Frontier map remained read-only.
