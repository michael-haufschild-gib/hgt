/-
# From the shell quadratic-rate globalisation to the nonconstancy witness

The globalisation produces, inside every nonempty open set of shell coefficients, a Hamiltonian on
whose simple root packets no relabelling of the quadratic-rate relation holds.  Choosing the open
set to be the nondegenerate locus of the spectral discriminant makes the canonical eigenvalues of
that Hamiltonian a simple root packet, so the relabelling failure applies to them -- which is
exactly the witness the nonconstancy criterion consumes.

Main results:
* `charpolyRelation_eigenvalues` — the canonical eigenvalues satisfy the characteristic relation.
* `exists_energy_witness_of_span_witness` — **the energy-form witness from a span witness**.
* `tendsto_integral_exp_sortedSpectralAction_zero_of_span_witness` — **angular dephasing from the
  quadratic-rate rigidity of one Hamiltonian in the family**.
-/
import GaloisForLFunctions.HTGeometry.SpectralEnergyWitnessBridge
import GaloisForLFunctions.HTGeometry.SpanCoordinateJunction
import GaloisForLFunctions.HTGeometry.SiteFactorLiftedSpectrum

open Filter Topology MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The canonical eigenvalues of a Hermitian matrix satisfy its characteristic relation. -/
theorem charpolyRelation_eigenvalues {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian)
    (i : Fin D) :
    matrixCharpolyRelation (M, ((hM.eigenvalues i : ℝ) : ℂ)) = 0 :=
  (mem_range_hermitianEigenvalues_iff hM (hM.eigenvalues i)).mp ⟨i, rfl⟩

/-- The nondegenerate locus of the spectral discriminant is open and nonempty. -/
theorem isOpen_discNonzero (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    IsOpen {q : Fin N → ℝ | MvPolynomial.eval q (spectralDiscriminantPoly P) ≠ 0} :=
  isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const

theorem nonempty_discNonzero {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hdisc : spectralDiscriminantPoly P ≠ 0) :
    {q : Fin N → ℝ | MvPolynomial.eval q (spectralDiscriminantPoly P) ≠ 0}.Nonempty := by
  by_contra hcon
  refine hdisc (MvPolynomial.funext fun x => ?_)
  have := Set.not_nonempty_iff_eq_empty.mp hcon
  have hx : x ∉ {q : Fin N → ℝ | MvPolynomial.eval q (spectralDiscriminantPoly P) ≠ 0} := by
    rw [this]
    exact Set.notMem_empty x
  simpa using not_not.mp hx

/-- **The energy-form witness from a span witness.**  One Hamiltonian in the real span of the
interaction family, with a simple root packet on which no relabelled quadratic-rate relation holds,
supplies at every rate a shell coefficient vector at which no labelling of the canonical spectrum
satisfies the relation. -/
theorem exists_energy_witness_of_span_witness {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (hdisc : spectralDiscriminantPoly P ≠ 0) (k : Fin D → ℝ)
    {H₀ : Matrix (Fin D) (Fin D) ℂ} (hspan : H₀ ∈ Submodule.span ℝ (Set.range P))
    {energy₀ : Fin D → ℂ} (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i, matrixCharpolyRelation (H₀, energy₀ i) = 0)
    (hfail : ∀ (κ : ℝ) (σ : Equiv.Perm (Fin D)),
      (∑ j, ((k (σ.symm j) : ℝ) : ℂ) * energy₀ j) ^ (2 : ℕ)
        - ((κ : ℝ) : ℂ) * ∑ j, energy₀ j ^ (2 : ℕ) ≠ 0)
    (κ : ℝ) :
    ∃ θ₀ : Fin N → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ (2 : ℕ)
        ≠ κ * ∑ i, ((isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) ^ (2 : ℕ) := by
  classical
  obtain ⟨q, hq, hgood⟩ := exists_mem_real_shell_quadraticRate_ne_zero_of_mem_span P
    (fun j => ((k j : ℝ) : ℂ)) ((κ : ℝ) : ℂ) hspan hinj₀ hroot₀ (hfail κ)
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
  have hR : (∑ j, ((hHerm.eigenvalues j : ℝ) : ℂ) ^ (2 : ℕ))
      = (((∑ j, (hHerm.eigenvalues j) ^ (2 : ℕ) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => by push_cast; ring
  rw [hL, hR, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub, hπ]
  simp

section Dephasing

variable {m : ℕ}

/-- **Angular dephasing from the quadratic-rate rigidity of one Hamiltonian in the family.** -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_of_span_witness
    {P : Fin m → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hdisc : spectralDiscriminantPoly P ≠ 0) (k : Fin D → ℝ) {c : ℝ} (hc : 0 < c)
    (hON : ∀ a b, (P a * P b).trace = if a = b then ((c : ℝ) : ℂ) else 0)
    {H₀ : Matrix (Fin D) (Fin D) ℂ} (hspan : H₀ ∈ Submodule.span ℝ (Set.range P))
    {energy₀ : Fin D → ℂ} (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i, matrixCharpolyRelation (H₀, energy₀ i) = 0)
    (hfail : ∀ (κ : ℝ) (σ : Equiv.Perm (Fin D)),
      (∑ j, ((k (σ.symm j) : ℝ) : ℂ) * energy₀ j) ^ (2 : ℕ)
        - ((κ : ℝ) : ℂ) * ∑ j, energy₀ j ^ (2 : ℕ) ≠ 0)
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction hP k
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin m))) : ℝ) : ℂ) * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) :=
  tendsto_integral_exp_sortedSpectralAction_zero_of_energy_witness hP hdisc k hc hON
    (fun κ => exists_energy_witness_of_span_witness hP hdisc k hspan hinj₀ hroot₀ hfail κ)
    g hg hC0 hC

end Dephasing

end

end GaloisForLFunctions.HTGeometry
