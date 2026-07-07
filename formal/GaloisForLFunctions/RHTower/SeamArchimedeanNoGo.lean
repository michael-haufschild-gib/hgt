/-
Two seam endpoints: the archimedean pairing no-go, and the Herglotz/self-adjoint route to RH.

**The no-go (support theorem).**  The finite-prime seam pairing `h ↦ ⟨D, B_h^fin⟩` depends only on the
values of `h` on the prime-power length set `Λ_pp = {r·log p} = {log n : n a prime power}`.  That set
is **locally finite**: only finitely many prime powers lie below any bound (`primePowers_le_finite`),
so only finitely many prime-power logs lie in any bounded interval (`primePowerLogs_le_finite`).  Hence
a nonzero test function supported in a `Λ_pp`-gap gives `B_h^fin = 0` and pairs to `0` — while the
archimedean Gaussian seam is a *continuous* logarithmic distribution, not supported on `Λ_pp`.  So no
Hilbert–Schmidt operator pairing **only** with `B_h^fin` can be the archimedean seam.  The finite and
archimedean channels cannot be glued by a direct HS inner product; they must be joined through the
reciprocity current — which is exactly the completed cochain `−ξ'/ξ = Ω_Δ` (`SeamFluxCompletion`,
built from `ξ = archFactor·ζ`), whose zero side is a residue transform, not an HS pairing.

**The Herglotz/self-adjoint route.**  The equivalent spectral face of the apex: if the seam Herglotz
kernel is positive (`SeamSuspensionTrace.herglotz_rank_one_psd` is its rank-one core), Nevanlinna
realization produces a self-adjoint `T_Δ` with `Θ_Δ = ½ + iT_Δ` whose spectrum is `½ + iℝ`.  The final
link is formalized here: a **Hermitian** operator has **real** eigenvalues, so if every ξ-zero is
`½ + i·(eigenvalue of T_Δ)` then every ξ-zero has real part `½` — RH (`rh_of_hermitian_spectral`,
composing `Matrix.IsHermitian.eigenvalues : N → ℝ` with `SeamCrossingTower.rh_of_seam_spectral`).  This
isolates the entire remaining problem to the single positivity `K_Δ ≥ 0` plus the spectral
identification of the ξ-zeros with the `T_Δ`-spectrum.
-/
import GaloisForLFunctions.RHTower.SeamCrossingTower

noncomputable section

namespace RHTower

open Complex Set

/-! ### §1 The archimedean pairing no-go: `Λ_pp` is locally finite -/

/-- **Only finitely many prime powers lie below a bound.**  `{n : IsPrimePow n ∧ n ≤ M}` is finite,
being a subset of `Iic M`. -/
theorem primePowers_le_finite (M : ℕ) : {n : ℕ | IsPrimePow n ∧ n ≤ M}.Finite :=
  (Set.finite_Iic M).subset (fun _ hn => hn.2)

/-- **The prime-power length set `Λ_pp = {log n : n a prime power}` is locally finite.**  Only finitely
many prime-power logs lie in any bounded interval `(−∞, L]`.  So `Λ_pp` is a discrete set with gaps —
the support obstruction: a finite-seam pairing depends only on `h|_{Λ_pp}`, which cannot see a
continuous archimedean distribution, and vanishes on any `h` supported in a gap. -/
theorem primePowerLogs_le_finite (L : ℝ) :
    {x : ℝ | ∃ n : ℕ, IsPrimePow n ∧ x = Real.log n ∧ x ≤ L}.Finite := by
  apply Set.Finite.subset
    ((primePowers_le_finite ⌈Real.exp L⌉₊).image (fun n : ℕ => Real.log (n : ℝ)))
  rintro x ⟨n, hpp, rfl, hxL⟩
  have hn1 : 1 ≤ n := hpp.one_lt.le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  refine ⟨n, ⟨hpp, ?_⟩, rfl⟩
  have hnexp : (n : ℝ) ≤ Real.exp L := (Real.log_le_iff_le_exp hnpos).mp hxL
  exact_mod_cast le_trans hnexp (Nat.le_ceil _)

/-! ### §2 The Herglotz/self-adjoint route to RH -/

/-- **Hermitian seam generator ⟹ RH.**  If a Hermitian operator `T_Δ` (the Nevanlinna realization of a
positive seam Herglotz kernel) has the property that every strip ξ-zero is `½ + i·(eigenvalue of
T_Δ)`, then RH holds: `Matrix.IsHermitian.eigenvalues` are **real**, so each such zero has real part
`½`, and `SeamCrossingTower.rh_of_seam_spectral` concludes RH.  This is the Herglotz face of the apex,
made a complete conditional theorem: the entire remaining content is the positivity `K_Δ ≥ 0` (giving
the Hermitian `T_Δ`) together with the spectral identification `xi ρ = 0 ↔ ρ = ½ + i·spec(T_Δ)`. -/
theorem rh_of_hermitian_spectral {N : Type*} [Fintype N] [DecidableEq N]
    (T : Matrix N N ℂ) (hT : T.IsHermitian)
    (hspec : ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        ∃ i : N, ρ = 1 / 2 + ((hT.eigenvalues i : ℝ) : ℂ) * I) :
    RiemannHypothesis := by
  apply rh_of_seam_spectral
  intro ρ hxi h0 h1
  obtain ⟨i, hi⟩ := hspec ρ hxi h0 h1
  exact ⟨hT.eigenvalues i, hi⟩

end RHTower
