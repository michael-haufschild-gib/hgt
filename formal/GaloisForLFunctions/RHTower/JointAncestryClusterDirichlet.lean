import GaloisForLFunctions.RHTower.JointAncestryClusterOrdinates

/-!
# The cluster test is a Dirichlet-polynomial mean square

A member of a cluster of zeros enters the dressed JAS test through its shift `s_j` relative to the
target (`Re s_j ≥ 0` after normalising by the farthest member): its prime pattern is `p ↦ p^{−s_j}`
(`jasShiftPattern`), and on `P`-smooth `m` the Euler coefficient of this pattern is `m^{−s_j}`
(`jasEulerCoeff_jasShiftPattern`).  So, with member-dependent real parts allowed,

`Σ_{j,k} u_j u_k Π_{p∈P} (1 − p^{−(σ + s_j + s̄_k)})⁻¹ = Σ_{m P-smooth} m^{−σ} |Σ_j u_j m^{−s_j}|²`
(`sum_sum_prod_inv_eq_tsum_dirichlet`),

and the coherence threshold reads (`jasCluster_re_le_dirichlet`): the twisted cluster average with
the design `e^{iπ/S}` is at most

`−½ Σ_m m^{−σ} |Σ_j u_j m^{−s_j}|² + 3 (Σ_j |u_j|)² Π_p (1 − p^{−σ})⁻¹ e^{−S/60}`.

A cluster can therefore cancel the negative test of its members only if the Dirichlet polynomial
`Σ_j u_j m^{−s_j}` built from its shifts is exponentially small in mean square over the `P`-smooth
integers.  Pure height shifts `s_j = −iΔ_j` recover `JointAncestryClusterOrdinates`.
-/

open Complex

namespace RHTower

open scoped ComplexConjugate

noncomputable section

/-- The prime pattern `p ↦ p^{−s}` of a complex shift `s`. -/
def jasShiftPattern (P : Finset Nat.Primes) (s : ℂ) : ↥P → ℂ :=
  fun i => (((i : Nat.Primes) : ℕ) : ℂ) ^ (-s)

theorem natCast_cpow_eq_exp_log {p : ℕ} (hp : 0 < p) (z : ℂ) :
    ((p : ℂ) ^ z) = Complex.exp ((Real.log p : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg p)]

theorem prime_cpow_eq_exp (q : Nat.Primes) (z : ℂ) :
    (((q : ℕ) : ℂ) ^ z) = Complex.exp ((Real.log (q : ℕ) : ℂ) * z) :=
  natCast_cpow_eq_exp_log q.2.pos z

theorem norm_jasShiftPattern_le (P : Finset Nat.Primes) {s : ℂ} (hs : 0 ≤ s.re) (i : ↥P) :
    ‖jasShiftPattern P s i‖ ≤ 1 := by
  unfold jasShiftPattern
  rw [Complex.norm_natCast_cpow_of_pos (i : Nat.Primes).2.pos, Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (i : Nat.Primes).2.one_lt.le)
    (by linarith)

/-- On `P`-smooth `m` the Euler coefficient of the pattern of `s` is `m^{−s}`. -/
theorem jasEulerCoeff_jasShiftPattern {P : Finset Nat.Primes} (s : ℂ)
    (m : Nat.factoredNumbers (jasPrimeNats P)) :
    jasEulerCoeff P (jasShiftPattern P s) m = ((m : ℕ) : ℂ) ^ (-s) := by
  have hm := Nat.pos_of_ne_zero (ne_zero_of_mem_factoredNumbers m)
  unfold jasEulerCoeff jasShiftPattern
  simp_rw [prime_cpow_eq_exp, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum, natCast_cpow_eq_exp_log hm, log_eq_sum_factored]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem jasShiftPattern_mul_conj (P : Finset Nat.Primes) (s s' : ℂ) (i : ↥P) :
    jasShiftPattern P s i * conj (jasShiftPattern P s' i) =
      (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(s + conj s')) := by
  unfold jasShiftPattern
  have hp := (i : Nat.Primes).2.pos
  rw [natCast_cpow_eq_exp_log hp, natCast_cpow_eq_exp_log hp, natCast_cpow_eq_exp_log hp, ← Complex.exp_conj,
    ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  ring

/-- **The cluster average as a Dirichlet-polynomial mean square.** -/
theorem sum_sum_prod_inv_eq_tsum_dirichlet {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (P : Finset Nat.Primes) {s : ι → ℂ} (hs : ∀ j, 0 ≤ (s j).re) {σ : ℝ} (hσ : 0 < σ) :
    ∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
      ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(s j + conj (s k))) *
        (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ =
    ∑' m : Nat.factoredNumbers (jasPrimeNats P), ((((m : ℕ) : ℝ) ^ (-σ) *
      Complex.normSq (∑ j ∈ t, (u j : ℂ) * ((m : ℕ) : ℂ) ^ (-s j)) : ℝ) : ℂ) := by
  have h := sum_sum_prod_inv_eq_tsum_of_one t u P (ψ := fun j => jasShiftPattern P (s j))
    (fun j i => norm_jasShiftPattern_le P (hs j) i) hσ
  simp_rw [jasShiftPattern_mul_conj] at h
  rw [h]
  refine tsum_congr fun m => ?_
  simp_rw [jasEulerCoeff_jasShiftPattern]

/-- **Coherence threshold in Dirichlet form.** -/
theorem jasCluster_re_le_dirichlet {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    {s : ι → ℂ} (hs : ∀ j, 0 ≤ (s j).re) {σ : ℝ} (hσ : 0 < σ)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hS : 0 < ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) :
    (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * ∏ i : ↥P,
        (1 - Complex.exp (((Real.pi / ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.I) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(s j + conj (s k))) *
            (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re ≤
      -(1 / 2) * ∑' m : Nat.factoredNumbers (jasPrimeNats P), ((m : ℕ) : ℝ) ^ (-σ) *
        Complex.normSq (∑ j ∈ t, (u j : ℂ) * ((m : ℕ) : ℂ) ^ (-s j)) +
      3 * (∑ j ∈ t, |u j|) ^ 2 * (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
  have h := jasCluster_re_le t u P (ψ := fun j => jasShiftPattern P (s j))
    (fun j i => norm_jasShiftPattern_le P (hs j) i) hσ hb hS
  simp_rw [mul_assoc (Complex.exp _), jasShiftPattern_mul_conj] at h
  rw [sum_sum_prod_inv_eq_tsum_dirichlet t u P hs hσ, ← Complex.ofReal_tsum,
    Complex.ofReal_re] at h
  simpa only [mul_assoc] using h

end

end RHTower
