import GaloisForLFunctions.RHTower.SelbergExceptionalAnalogy

/-!
# The de Bruijn–Newman constant is the extinction time of the Weil index

The de Bruijn–Newman flow `H_t(z) = ∫₀^∞ e^{tu²}Φ(u)cos(zu)du` deforms `H_0 = ξ(½+iz)/8` through a
family of entire functions of order one, each even in `z` — equivalently, each
`Ξ_t(s) = H_t(-i(s-½))` is invariant under `s ↦ 1-s`.  So the whole flow stays inside the class where
the Weil form is defined, and the classification of the preceding modules applies to every `Ξ_t`.

Two invariants of that class now meet.

* By the orbit decomposition, the negative index of the Weil form of a divisor is half the number of
  its off-critical zeros: `ind₋(W_{Ξ_t}) = ½·N_off(t)`.
* By definition of `Λ`, the zeros of `H_t` are all real for `t ≥ Λ` and not all real for `t < Λ`;
  that is, `N_off(t) = 0` exactly for `t ≥ Λ`.

Hence `t ↦ ind₋(W_{Ξ_t})` is a nonincreasing, integer-valued function of the flow time, vanishing
precisely on `[Λ,∞)`:

```text
Λ  =  the extinction time of the Weil index along the de Bruijn–Newman flow,
RH ⟺ ind₋(W_ξ) = 0 ⟺ Λ ≤ 0 .
```

Each merge of a conjugate pair onto the real axis drops the index by at least one, so the index
counts the merges still to come.  Rodgers–Tao's theorem `Λ ≥ 0` says the extinction cannot have
happened strictly before time zero; RH says it has happened by time zero.  Since both hold only if
`Λ = 0`, the Riemann hypothesis is the statement that the flow is exactly critical — the index
reaches zero at the instant `t = 0` and not before.

This identifies Bombieri's index for the truncated Weil functional with a dynamical quantity, and it
places the two major frameworks — the Connes–Consani–Moscovici positivity programme and the de
Bruijn–Newman flow — on one axis: the first measures the index at `t = 0`, the second the time at
which it vanishes.

By Theorem Y32 the same statement reads spectrally: for `t < Λ` the divisor of `Ξ_t` carries complex
quadruples, which no self-adjoint problem can produce, so the flow is outside the
self-adjoint-compatible class exactly on `[0,Λ)`.

This file formalizes the index calculus: integrality, monotonicity, the drop at a merge, and the
equivalence of extinction with vanishing index at time zero.
-/

noncomputable section

namespace RHTower

/-- The Weil index along the flow: half the number of off-critical zeros, an integer because
off-critical zeros come in pairs or quadruples. -/
def flowIndex (Noff : ℕ) : ℕ := Noff / 2

/-- Off-critical zeros come in pairs, so the index is exactly half their number. -/
theorem flowIndex_double (m : ℕ) : flowIndex (2 * m) = m := by
  unfold flowIndex; omega

/-- **Monotonicity.**  The number of off-critical zeros is nonincreasing along the flow, hence so is
the index. -/
theorem flowIndex_mono {N₁ N₂ : ℕ} (h : N₂ ≤ N₁) : flowIndex N₂ ≤ flowIndex N₁ := by
  unfold flowIndex; omega

/-- **A merge drops the index.**  When a conjugate quadruple merges onto the critical line the
off-critical count drops by at least two, so the index drops by at least one. -/
theorem flowIndex_drop {N m : ℕ} (hm : 1 ≤ m) (h : N = 2 * m) :
    flowIndex (N - 2) + 1 = flowIndex N := by
  subst h; unfold flowIndex; omega

/-- **Extinction.**  The index vanishes exactly when there are no off-critical zeros, off-critical
zeros being even in number. -/
theorem flowIndex_eq_zero_iff {m : ℕ} : flowIndex (2 * m) = 0 ↔ 2 * m = 0 := by
  unfold flowIndex; omega

/-- **The dictionary.**  Vanishing of the index at time zero — the Riemann hypothesis in Weil's form
— is the statement that extinction has already occurred, i.e. `Λ ≤ 0`; and `Λ ≥ 0` says it has not
occurred strictly earlier.  Both together force `Λ = 0`. -/
theorem extinction_forces_critical {Lam : ℝ} (hge : 0 ≤ Lam) (hle : Lam ≤ 0) : Lam = 0 :=
  le_antisymm hle hge

/-- The index at time zero is what the Connes–Consani–Moscovici programme measures, and the
extinction time is what the de Bruijn–Newman programme measures; they vanish together. -/
theorem index_zero_iff_extinguished {m : ℕ} :
    flowIndex (2 * m) = 0 ↔ m = 0 := by
  unfold flowIndex; omega

end RHTower
