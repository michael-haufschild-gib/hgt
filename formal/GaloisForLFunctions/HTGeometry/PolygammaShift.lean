import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# All-order integer-shift law of the polygamma jets

The single-step shift law `ψ⁽ʲ⁾(z+1) = ψ⁽ʲ⁾(z) + (−1)ʲ·j!/z^{j+1}`
(`GaloisForLFunctions.digammaJet_shift`) iterates to the finite integer-shift form

`ψ⁽ʲ⁾(w + n) = ψ⁽ʲ⁾(w) + ∑_{i<n} (−1)ʲ·j!/(w+i)^{j+1}`,

valid off the poles `−ℕ`, for every jet order `j`.  This is the uniform-in-`j` vertical boundary
datum of a common-scale Gamma orbit: `j = 0` recovers `digamma_add_nat`, `j = 1` the trigamma
recurrence, and the whole tower is rational in the shift argument.

The charge-collapse corollary reads off the key consequence: along one shift orbit `w + n_k` with
vanishing total charge `∑_k m_k = 0`, the transcendental jet `ψ⁽ʲ⁾(w)` cancels at every order, so the
entire jet tower of `∑_k m_k ψ(w + n_k)` is rational.  The complementary nonzero-charge case is where
the surviving `∑_k m_k · ψ⁽ʲ⁾(w)` obstructs differential algebraicity.
-/

open GaloisForLFunctions
open Complex

namespace HTGeometry

/-- **All-order integer-shift law of the digamma jets.**
`ψ⁽ʲ⁾(w + n) = ψ⁽ʲ⁾(w) + ∑_{i<n} (−1)ʲ·j!/(w+i)^{j+1}` for `n : ℕ`, off the poles, at every jet
order `j`.  Iterates the single-step `GaloisForLFunctions.digammaJet_shift`; `j = 0` is
`digamma_add_nat`, `j = 1` the trigamma recurrence. -/
theorem iteratedDeriv_digamma_add_nat (j : ℕ) (w : ℂ) (hw : ∀ p : ℕ, w ≠ -(p : ℂ)) (n : ℕ) :
    iteratedDeriv j Complex.digamma (w + n)
      = iteratedDeriv j Complex.digamma w
        + ∑ i ∈ Finset.range n, (-1) ^ j * (j.factorial : ℂ) / (w + i) ^ (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hwn : ∀ p : ℕ, w + (n : ℂ) ≠ -(p : ℂ) := by
      intro p hp
      refine hw (p + n) ?_
      push_cast at hp ⊢
      linear_combination hp
    rw [show w + ((n : ℕ) + 1 : ℕ) = (w + (n : ℂ)) + 1 from by push_cast; ring,
      GaloisForLFunctions.digammaJet_shift j hwn, ih, Finset.sum_range_succ]
    ring

/-- **Charge-collapse of the digamma jet tower.**  Along a single shift orbit `w + n_k` with
vanishing total charge `∑_k m_k = 0`, the transcendental jet `ψ⁽ʲ⁾(w)` cancels at every order:
`∑_k m_k ψ⁽ʲ⁾(w + n_k) = ∑_k m_k ∑_{i<n_k} (−1)ʲ·j!/(w+i)^{j+1}`, a rational function of `w` for
each `j`.  Uniform-in-`j` form of `digamma_charge_collapse`. -/
theorem iteratedDeriv_digamma_charge_collapse {d : ℕ} (w : ℂ) (hw : ∀ p : ℕ, w ≠ -(p : ℂ))
    (nn : Fin d → ℕ) (m : Fin d → ℂ) (j : ℕ) (hcharge : ∑ k, m k = 0) :
    ∑ k, m k * iteratedDeriv j Complex.digamma (w + nn k)
      = ∑ k, m k * ∑ i ∈ Finset.range (nn k),
          (-1) ^ j * (j.factorial : ℂ) / (w + i) ^ (j + 1) := by
  simp_rw [iteratedDeriv_digamma_add_nat j w hw, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    hcharge, zero_mul, zero_add]

/-- **Nonzero-charge form of the digamma jet tower.**  For any charges `m` and integer shifts `nn`,
`∑ₖ mₖ ψ⁽ʲ⁾(w + nₖ) = (∑ₖ mₖ)·ψ⁽ʲ⁾(w) + ∑ₖ mₖ ∑_{i<nₖ} (−1)ʲ·j!/(w+i)^{j+1}`: every shifted jet
collapses onto the total-charge multiple `M·ψ⁽ʲ⁾(w)` of the single transcendental jet plus a rational
tail.  When the total charge `M = ∑ₖ mₖ ≠ 0`, the surviving `M·ψ⁽ʲ⁾(w)` is the obstruction to
differential algebraicity; `iteratedDeriv_digamma_charge_collapse` is the `M = 0` specialization. -/
theorem iteratedDeriv_digamma_charge_general {d : ℕ} (w : ℂ) (hw : ∀ p : ℕ, w ≠ -(p : ℂ))
    (nn : Fin d → ℕ) (m : Fin d → ℂ) (j : ℕ) :
    ∑ k, m k * iteratedDeriv j Complex.digamma (w + nn k)
      = (∑ k, m k) * iteratedDeriv j Complex.digamma w
        + ∑ k, m k * ∑ i ∈ Finset.range (nn k),
            (-1) ^ j * (j.factorial : ℂ) / (w + i) ^ (j + 1) := by
  simp_rw [iteratedDeriv_digamma_add_nat j w hw, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]

end HTGeometry
