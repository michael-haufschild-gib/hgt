/-
# Angular dephasing on the nearest-neighbour Pauli shell

The card's own ensemble is the unit sphere of coefficients of the nearest-neighbour Pauli family.
Feeding the chain-span nonflatness witness into the shell dephasing capstone gives the plateau law's
angular dephasing there, with no hypothesis beyond balancedness of the spectral character.

Main results:
* `exists_energy_witness_of_span_witness_at` — the coordinate witness at a single rate.
* `spectralDiscriminantPoly_chainPauliFin_ne_zero` — the chain family has a simple-spectrum member.
* `exists_shell_energy_witness_pauliChain` — **Theorem A on the card's own ensemble**.
* `tendsto_integral_exp_sortedSpectralAction_zero_pauliChain` — **angular dephasing on the card's
  own nearest-neighbour Pauli shell**.
-/
import GaloisForLFunctions.HTGeometry.PauliChainSpanWitness
import GaloisForLFunctions.HTGeometry.ShellQuadraticRateWitness
import GaloisForLFunctions.HTGeometry.SpectralActionDephasingCapstone
import GaloisForLFunctions.HTGeometry.ConcreteTwoHamiltonianSpectralActionWitness

open Filter Topology MeasureTheory Metric Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **The coordinate witness at a single rate.**  One Hamiltonian in the real span of the family,
with a simple root packet on which no relabelled quadratic-rate relation holds *at the rate `κ`*,
supplies a shell coefficient vector at which no labelling of the canonical spectrum satisfies the
relation at that rate. -/
theorem exists_energy_witness_of_span_witness_at {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (hdisc : spectralDiscriminantPoly P ≠ 0) (k : Fin D → ℝ)
    {H₀ : Matrix (Fin D) (Fin D) ℂ} (hspan : H₀ ∈ Submodule.span ℝ (Set.range P))
    {energy₀ : Fin D → ℂ} (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i, matrixCharpolyRelation (H₀, energy₀ i) = 0)
    (κ : ℝ)
    (hfail : ∀ σ : Equiv.Perm (Fin D),
      (∑ j, ((k (σ.symm j) : ℝ) : ℂ) * energy₀ j) ^ 2
        - ((κ : ℝ) : ℂ) * ∑ j, energy₀ j ^ 2 ≠ 0) :
    ∃ θ₀ : Fin N → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ 2
        ≠ κ * ∑ i, ((isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) ^ 2 := by
  classical
  obtain ⟨q, hq, hgood⟩ := exists_mem_real_shell_quadraticRate_ne_zero_of_mem_span P
    (fun j => ((k j : ℝ) : ℂ)) ((κ : ℝ) : ℂ) hspan hinj₀ hroot₀ hfail
    (isOpen_discNonzero P) (nonempty_discNonzero hdisc)
  refine ⟨q, fun π hπ => ?_⟩
  set hHerm := isHermitian_spectralEnsembleMatrix hP q with hHermDef
  have hinj : Function.Injective (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) := by
    intro i j hij
    exact injective_eigenvalues_of_disc_ne_zero hP hq (Complex.ofReal_injective (by exact hij))
  have hroot : ∀ i, matrixCharpolyRelation
      (∑ a, ((q a : ℝ) : ℂ) • P a, ((hHerm.eigenvalues i : ℝ) : ℂ)) = 0 := by
    intro i
    have hmat : (∑ a, ((q a : ℝ) : ℂ) • P a) = spectralEnsembleMatrix P q := rfl
    rw [hmat]
    exact charpolyRelation_eigenvalues hHerm i
  have hkey := hgood (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) hinj hroot π
  refine hkey ?_
  have hsum : (∑ j, ((k (π.symm j) : ℝ) : ℂ) * ((hHerm.eigenvalues j : ℝ) : ℂ))
      = ∑ i, ((k i : ℝ) : ℂ) * ((hHerm.eigenvalues (π i) : ℝ) : ℂ) := by
    refine (Equiv.sum_comp π
      (fun j => ((k (π.symm j) : ℝ) : ℂ) * ((hHerm.eigenvalues j : ℝ) : ℂ))).symm.trans ?_
    exact Finset.sum_congr rfl fun i _ => by rw [Equiv.symm_apply_apply]
  rw [hsum]
  have hL : (∑ i, ((k i : ℝ) : ℂ) * ((hHerm.eigenvalues (π i) : ℝ) : ℂ))
      = (((∑ i, k i * hHerm.eigenvalues (π i) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hR : (∑ j, ((hHerm.eigenvalues j : ℝ) : ℂ) ^ 2)
      = (((∑ j, (hHerm.eigenvalues j) ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => by push_cast; ring
  rw [hL, hR, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub, hπ]
  simp

/-! ## The chain family -/

/-- **The nearest-neighbour Pauli family has a simple-spectrum member.** -/
theorem spectralDiscriminantPoly_chainPauliFin_ne_zero (k : ℕ)
    {kvec : Fin (2 ^ (k + 3)) → ℝ} (hksum : ∑ j, kvec j = 0) (hkne : kvec ≠ 0) :
    spectralDiscriminantPoly (chainPauliFin (k + 3)) ≠ 0 := by
  classical
  obtain ⟨H₀, energy₀, hspan, hinj₀, hroot₀, -⟩ :=
    exists_pauliChain_spanWitness k 0 kvec hksum hkne
  obtain ⟨θ, hθ⟩ := exists_realCoeff_of_mem_span (chainPauliFin (k + 3)) hspan
  have hEq : spectralEnsembleMatrix (chainPauliFin (k + 3)) θ = H₀ := hθ.symm
  refine spectralDiscriminantPoly_ne_zero (chainPauliFin_isHermitian (k + 3)) (θ₀ := θ) ?_
  refine hermitianEigenvalues_injective_of_injective_rootPacket _
    (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ)
    energy₀ hinj₀ ?_
  intro i
  rw [hEq]
  exact hroot₀ i

/-- **Theorem A on the card's own ensemble.**  At every rate and every balanced nonzero spectral
character there is a shell coefficient vector at which no labelling of the canonical spectrum
satisfies the quadratic-rate relation -- so no projective spectral action is flat. -/
theorem exists_shell_energy_witness_pauliChain (k : ℕ)
    (kvec : Fin (2 ^ (k + 3)) → ℝ) (hksum : ∑ j, kvec j = 0) (hkne : kvec ≠ 0) (κ : ℝ) :
    ∃ θ₀ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ,
      ∀ π : Equiv.Perm (Fin (2 ^ (k + 3))),
        (∑ j, kvec j * (isHermitian_spectralEnsembleMatrix
            (chainPauliFin_isHermitian (k + 3)) θ₀).eigenvalues (π j)) ^ 2
          ≠ κ * ∑ i, ((isHermitian_spectralEnsembleMatrix
            (chainPauliFin_isHermitian (k + 3)) θ₀).eigenvalues i) ^ 2 := by
  obtain ⟨H₀, energy₀, hspan, hinj₀, hroot₀, hfail⟩ :=
    exists_pauliChain_spanWitness k κ kvec hksum hkne
  exact exists_energy_witness_of_span_witness_at (chainPauliFin_isHermitian (k + 3))
    (spectralDiscriminantPoly_chainPauliFin_ne_zero k hksum hkne) kvec hspan hinj₀ hroot₀ κ hfail

/-- **Angular dephasing on the card's own nearest-neighbour Pauli shell.**  For every balanced
nonzero spectral character and every bounded measurable amplitude, the oscillatory shell integral of
the canonically labelled spectral action tends to zero. -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_pauliChain (k : ℕ)
    (kvec : Fin (2 ^ (k + 3)) → ℝ) (hksum : ∑ j, kvec j = 0) (hkne : kvec ≠ 0)
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3))))) 1 → ℂ)
    (hg : Measurable g) {Cb : ℝ} (hC0 : 0 ≤ Cb) (hC : ∀ x, ‖g x‖ ≤ Cb) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction (chainPauliFin_isHermitian (k + 3)) kvec
            (WithLp.ofLp (x : EuclideanSpace ℝ
              (Fin (Fintype.card (ChainLabel (k + 3)))))) : ℝ) : ℂ) * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) := by
  classical
  have hdisc := spectralDiscriminantPoly_chainPauliFin_ne_zero k hksum hkne
  have hc : (0 : ℝ) < 2 ^ (k + 3) := by positivity
  have hwit : ∀ κ : ℝ, ∃ θ₀ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ,
      ∀ π : Equiv.Perm (Fin (2 ^ (k + 3))),
        (∑ j, kvec j * (isHermitian_spectralEnsembleMatrix
            (chainPauliFin_isHermitian (k + 3)) θ₀).eigenvalues (π j)) ^ 2
          ≠ κ * ∑ i, ((isHermitian_spectralEnsembleMatrix
            (chainPauliFin_isHermitian (k + 3)) θ₀).eigenvalues i) ^ 2 := by
    intro κ
    obtain ⟨H₀, energy₀, hspan, hinj₀, hroot₀, hfail⟩ :=
      exists_pauliChain_spanWitness k κ kvec hksum hkne
    exact exists_energy_witness_of_span_witness_at (chainPauliFin_isHermitian (k + 3)) hdisc
      kvec hspan hinj₀ hroot₀ κ hfail
  exact tendsto_integral_exp_sortedSpectralAction_zero_of_energy_witness
    (chainPauliFin_isHermitian (k + 3)) hdisc kvec hc (trace_chainPauliFin_mul (k + 3))
    hwit g hg hC0 hC

end

end GaloisForLFunctions.HTGeometry
