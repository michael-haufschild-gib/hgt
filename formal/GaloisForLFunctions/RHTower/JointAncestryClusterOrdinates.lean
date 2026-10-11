import GaloisForLFunctions.RHTower.JointAncestryClusterCoherence

/-!
# The cluster test is a mean square of the ordinate sum over smooth numbers

The members of a cluster of zeros differ from the target by height shifts `Δ_j = γ_j − γ*`, and the
prime-phase pattern of a shift is `p ↦ p^{iΔ}` (`jasHeightPattern`).  On `P`-smooth `m` its Euler
coefficient is `m^{iΔ}` (`jasEulerCoeff_jasHeightPattern`).  So the cluster quantities of
`JointAncestryClusterIdentity` and `JointAncestryClusterCoherence` are smoothed mean squares of the
*ordinate sum*

`D(t) = Σ_j u_j e^{iΔ_j t}`   at `t = log m`:

`Σ_{j,k} u_j u_k Π_{p∈P} (1 − p^{i(Δ_j − Δ_k)} p^{−σ})⁻¹ = Σ_{m P-smooth} m^{−σ} |D(log m)|²`
(`sum_sum_prod_inv_eq_tsum_ordinates`).

With the coherence threshold (`jasCluster_re_le_ordinates`), a cluster of zeros near `Re s = 1`
cancels the negative JAS test of its members only if its ordinate sum `D` is exponentially small in
mean square over the `P`-smooth integers:
`Σ_m m^{−σ} |D(log m)|² ≲ 6 e^{−S/60} (Σ|u_j|)² Π_p (1 − p^{−σ})⁻¹`.
-/

open Complex

namespace RHTower

open scoped ComplexConjugate

noncomputable section

/-- The prime-phase pattern `p ↦ p^{iΔ}` of a height shift `Δ`. -/
def jasHeightPattern (P : Finset Nat.Primes) (Δ : ℝ) : ↥P → ℂ :=
  fun i => Complex.exp (((Δ * Real.log (((i : Nat.Primes) : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)

theorem norm_jasHeightPattern (P : Finset Nat.Primes) (Δ : ℝ) (i : ↥P) :
    ‖jasHeightPattern P Δ i‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem log_eq_sum_factored {P : Finset Nat.Primes} (m : Nat.factoredNumbers (jasPrimeNats P)) :
    Real.log ((m : ℕ) : ℝ) = ∑ i : ↥P, ((m : ℕ).factorization ((i : Nat.Primes) : ℕ) : ℝ) *
      Real.log (((i : Nat.Primes) : ℕ) : ℝ) := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  have hsub : (m : ℕ).factorization.support ⊆ jasPrimeNats P := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact (Nat.mem_factoredNumbers.mp m.2).2 p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)
  rw [Finsupp.sum_of_support_subset _ hsub _ (fun p _ => by simp)]
  unfold jasPrimeNats
  rw [Finset.sum_map]
  exact (Finset.sum_coe_sort P (fun q : Nat.Primes =>
    ((m : ℕ).factorization (q : ℕ) : ℝ) * Real.log ((q : ℕ) : ℝ))).symm

/-- On `P`-smooth `m` the Euler coefficient of the pattern of `Δ` is `m^{iΔ}`. -/
theorem jasEulerCoeff_jasHeightPattern {P : Finset Nat.Primes} (Δ : ℝ)
    (m : Nat.factoredNumbers (jasPrimeNats P)) :
    jasEulerCoeff P (jasHeightPattern P Δ) m =
      Complex.exp (((Δ * Real.log ((m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
  unfold jasEulerCoeff jasHeightPattern
  simp_rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum, log_eq_sum_factored, Finset.mul_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem jasHeightPattern_mul_conj (P : Finset Nat.Primes) (Δ Δ' : ℝ) (i : ↥P) :
    jasHeightPattern P Δ i * conj (jasHeightPattern P Δ' i) = jasHeightPattern P (Δ - Δ') i := by
  unfold jasHeightPattern
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **The cluster average as an ordinate mean square.** -/
theorem sum_sum_prod_inv_eq_tsum_ordinates {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (P : Finset Nat.Primes) (Δ : ι → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
      ∏ i : ↥P, (1 - jasHeightPattern P (Δ j - Δ k) i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ =
    ∑' m : Nat.factoredNumbers (jasPrimeNats P), ((((m : ℕ) : ℝ) ^ (-σ) *
      Complex.normSq (∑ j ∈ t, (u j : ℂ) *
        Complex.exp (((Δ j * Real.log ((m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) : ℝ) : ℂ) := by
  have h := sum_sum_prod_inv_eq_tsum_of_one t u P (ψ := fun j => jasHeightPattern P (Δ j))
    (fun j i => (norm_jasHeightPattern P _ i).le) hσ
  simp_rw [jasHeightPattern_mul_conj] at h
  rw [h]
  refine tsum_congr fun m => ?_
  simp_rw [jasEulerCoeff_jasHeightPattern]

/-- **Coherence threshold in ordinate form.**  The twisted cluster average of the zeros at height
shifts `Δ_j` is at most `−½ Σ_m m^{−σ}|D(log m)|² + 3(Σ|u_j|)² Π_p (1 − p^{−σ})⁻¹ e^{−S/60}`. -/
theorem jasCluster_re_le_ordinates {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    (Δ : ι → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hS : 0 < ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) :
    (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * ∏ i : ↥P,
        (1 - Complex.exp (((Real.pi / ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.I) * jasHeightPattern P (Δ j - Δ k) i *
            (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re ≤
      -(1 / 2) * ∑' m : Nat.factoredNumbers (jasPrimeNats P), ((m : ℕ) : ℝ) ^ (-σ) *
        Complex.normSq (∑ j ∈ t, (u j : ℂ) *
          Complex.exp (((Δ j * Real.log ((m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) +
      3 * (∑ j ∈ t, |u j|) ^ 2 * (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
  have h := jasCluster_re_le t u P (ψ := fun j => jasHeightPattern P (Δ j))
    (fun j i => (norm_jasHeightPattern P _ i).le) hσ hb hS
  simp_rw [mul_assoc (Complex.exp _), jasHeightPattern_mul_conj] at h
  rw [sum_sum_prod_inv_eq_tsum_ordinates t u P Δ hσ, ← Complex.ofReal_tsum,
    Complex.ofReal_re] at h
  simpa only [mul_assoc] using h

end

end RHTower
