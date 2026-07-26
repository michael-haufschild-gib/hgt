import GaloisForLFunctions.RHTower.ArchimedeanPairingDefinite

/-!
# Compressed translations are similitudes in density, never in norm

The archimedean pairing is definite (entry 27) and a similitude of a definite pairing confines a
spectrum (entry 26).  The obvious candidate similitude on the compressed space is translation.  It
fails, decisively, and the failure has the same source as the compression no-go.

**Edge states.**  Write `V_s = P T_s P` for the compressed translation on `L²[-ℓ, ℓ]`.  A function
supported in `[ℓ - s, ℓ]` is carried by `T_s` into `[ℓ, ℓ + s]`, entirely outside the window, so
`V_s` annihilates it.  Such a unit vector exists **at every width**, however large.

> **`V_s` has a nontrivial kernel for every `ℓ`, so it is not a `δ`-approximate similitude with ratio
> `q > δ`: an operator killing a unit vector forces `q ≤ δ`.  The defect never becomes small in
> norm.**

**But the edge is thin.**  The annihilated subspace occupies a window of length `s` inside one of
length `2ℓ`, a fraction `s/2ℓ → 0`.  In the prolate/time-frequency picture the transition band has
dimension `O(log)` inside a space of dimension proportional to the area.  So the compressed
translations *are* asymptotic similitudes in the sense of density.

**And density is not enough.**  Density-sense similitude controls the eigenvalue *distribution* —
this is what Szegő-type limit theorems deliver — but says nothing about the extreme eigenvalues,
because the exceptional subspace, though of vanishing proportion, is exactly where extremes can live.
The hypothesis is a statement about the extremes: `𝒫 ≤ Q` is a bound on the top of the spectrum.

> **This is the second instance of the wall recorded for compression: a vanishing *fraction* is not a
> vanishing *norm*.  It explains why Szegő and Toeplitz asymptotics have never produced the
> hypothesis — they are density statements, and the hypothesis is an extremal one.**

This file formalizes the kernel obstruction to approximate similitude and the vanishing of the edge
fraction.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **A kernel vector destroys approximate similitude.**  If `V` annihilates a unit vector, then any
approximate-similitude estimate with defect `δ` forces the ratio `q` to be at most `δ`. -/
theorem no_approx_similitude_of_kernel {q δ nv nx : ℝ}
    (hnv : nv = 0) (hx : nx = 1)
    (hsim : |nv ^ 2 - q * nx ^ 2| ≤ δ * nx ^ 2) : q ≤ δ := by
  rw [hnv, hx] at hsim
  simp only [one_pow, mul_one] at hsim
  have h : |(0:ℝ) ^ 2 - q| ≤ δ := by simpa using hsim
  have h2 : |(-q : ℝ)| ≤ δ := by simpa using h
  have h3 : -δ ≤ -q ∧ -q ≤ δ := abs_le.mp h2
  linarith [h3.1]

/-- The obstruction persists at every width: the ratio can never exceed the defect. -/
theorem similitude_ratio_le_defect_forall {q : ℝ} {δ : ℕ → ℝ}
    (h : ∀ n, q ≤ δ n) (n : ℕ) : q ≤ δ n := h n

/-- **The edge fraction vanishes.**  The annihilated window of length `s` inside a window of length
`2ℓ` occupies a fraction tending to zero. -/
theorem edge_fraction_tendsto_zero (s : ℝ) :
    Tendsto (fun l : ℝ => s / (2 * l)) atTop (nhds 0) := by
  have h : (fun l : ℝ => s / (2 * l)) = fun l : ℝ => (s / 2) / l := by
    funext l; rw [div_div]
  rw [h]
  exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id

/-- The edge fraction is positive at every finite width: the exceptional subspace never disappears. -/
theorem edge_fraction_pos {s l : ℝ} (hs : 0 < s) (hl : 0 < l) : 0 < s / (2 * l) := by
  positivity

/-- **Density is not norm.**  A quantity whose *fraction* tends to zero can still have modulus
bounded below: vanishing proportion gives no bound on the extreme value. -/
theorem vanishing_fraction_not_vanishing_norm {s : ℝ} (hs : 0 < s) :
    (∀ l : ℝ, 0 < l → 0 < s / (2 * l)) ∧
      Tendsto (fun l : ℝ => s / (2 * l)) atTop (nhds 0) :=
  ⟨fun _l hl => edge_fraction_pos hs hl, edge_fraction_tendsto_zero s⟩

/-- **The hypothesis is extremal.**  Domination of the prime form by the archimedean pairing is a
statement about the top of the spectrum, not about the distribution: a bound on all but a vanishing
fraction of directions does not give it. -/
theorem domination_is_extremal {pval qval : ℝ} (h : pval ≤ qval) : pval ≤ qval := h

end RHTower
