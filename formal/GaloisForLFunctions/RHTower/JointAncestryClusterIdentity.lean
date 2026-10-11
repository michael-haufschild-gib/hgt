import GaloisForLFunctions.RHTower.JointAncestryWeilEulerBridge

/-!
# The cluster self-averaging identity

Let a finite family `j ∈ t` of points `ψ j` of the closed polydisc (prime-phase patterns with
`‖ψ_{j,p}‖ ≤ 1`) carry real weights `u j`, and let `θ ∈ T^P`.  Averaging the twisted Euler products of all differences
`θ · ψ_j · ψ̄_k` with weights `u_j u_k` gives a Dirichlet series whose coefficients are, up to the
single twist `θ`, squared moduli (`sum_sum_prod_inv_eq_tsum`):

`Σ_{j,k} u_j u_k Π_{p∈P} (1 − θ_p ψ_{j,p} ψ̄_{k,p} p^{−z})⁻¹ = Σ_{m P-smooth} e_θ(m) m^{−z} |Σ_j u_j e_{ψ_j}(m)|²`.

In route JAS the left side is the b-side of the zero-sum density, averaged over the design points of
the members of a cluster of zeros: `ψ_j` is the pattern `p^{−s_j}` of the member's shift `s_j`
(`Re s_j ≥ 0`; a pure phase `p^{iγ_j}` when the members share their real part) and `θ` the common
phase design.  The Euler products are supplied for arbitrary local parameters `w_p` with
`‖w_p‖ p^{−Re z} < 1` (`hasSum_jasEulerHom_of_lt`).  So the cluster contributes a twisted *positive* Dirichlet series.  With
`θ ≡ 1` it is literally a sum of squares (`sum_sum_prod_inv_eq_tsum_of_one`), and a design `θ`
that turns a single member negative turns the whole averaged cluster negative unless the squared
moduli cancel.

Cancellation between two members needs a phase offset `Σ_p b_p sin x_p ≈ π`, and that costs a
modulus deficit (`sq_sum_mul_sin_le`):

`(Σ_p b_p sin x_p)² ≤ 2 (Σ_p b_p) Σ_p b_p (1 − cos x_p)`.

So an anti-phase pair always loses at least `π²/(2S)` with `S = Σ_p b_p`.
-/

open Complex

namespace RHTower

open scoped ComplexConjugate

noncomputable section

/-! ### Euler products with arbitrary local parameters -/

theorem jasEulerCoeff_prime_of_not_mem {P : Finset Nat.Primes} (w : ↥P → ℂ) {p : ℕ}
    (hp : p.Prime) (hnot : p ∉ jasPrimeNats P) : jasEulerCoeff P w p = 1 := by
  classical
  unfold jasEulerCoeff
  rw [Nat.Prime.factorization hp]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Finsupp.single_apply, if_neg, pow_zero]
  intro h
  apply hnot
  rw [h]
  exact Finset.mem_map.mpr ⟨i.1, i.2, rfl⟩

theorem norm_jasEulerHom_prime_lt_of_lt {P : Finset Nat.Primes} {w : ↥P → ℂ} {z : ℂ}
    (hz : 0 < z.re) (hw : ∀ i : ↥P, ‖w i‖ * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) < 1)
    {p : ℕ} (hp : p.Prime) : ‖jasEulerHom P w z p‖ < 1 := by
  classical
  rw [jasEulerHom_apply w z hp.ne_zero, norm_mul,
    Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  by_cases hmem : p ∈ jasPrimeNats P
  · obtain ⟨q, hq, hpq⟩ := Finset.mem_map.mp hmem
    have hpq' : ((q : Nat.Primes) : ℕ) = p := hpq
    subst hpq'
    have := jasEulerCoeff_prime w ⟨q, hq⟩
    simp only at this
    rw [this]
    exact hw ⟨q, hq⟩
  · rw [jasEulerCoeff_prime_of_not_mem w hp hmem, norm_one, one_mul]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- **Euler product over `P`-smooth integers with local parameters `w_p`, `‖w_p‖ p^{−Re z} < 1`.** -/
theorem hasSum_jasEulerHom_of_lt {P : Finset Nat.Primes} {w : ↥P → ℂ} {z : ℂ} (hz : 0 < z.re)
    (hw : ∀ i : ↥P, ‖w i‖ * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) < 1) :
    HasSum (fun m : Nat.factoredNumbers (jasPrimeNats P) => jasEulerHom P w z m)
      (∏ i : ↥P, (1 - w i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-z))⁻¹) := by
  classical
  obtain ⟨-, h2⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := jasEulerHom P w z) (fun hp => norm_jasEulerHom_prime_lt_of_lt hz hw hp) (jasPrimeNats P)
  have hfilter : (jasPrimeNats P).filter Nat.Prime = jasPrimeNats P :=
    Finset.filter_true_of_mem fun p hp => by
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp
      exact q.2
  have heq : ∏ p ∈ (jasPrimeNats P).filter Nat.Prime, (1 - jasEulerHom P w z p)⁻¹ =
      ∏ i : ↥P, (1 - w i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-z))⁻¹ := by
    rw [hfilter, jasPrimeNats, Finset.prod_map, ← Finset.prod_attach, Finset.univ_eq_attach]
    refine Finset.prod_congr rfl fun i _ => ?_
    show (1 - jasEulerHom P w z ((i.1 : Nat.Primes) : ℕ))⁻¹ = _
    rw [jasEulerHom_apply w z i.1.2.ne_zero, jasEulerCoeff_prime]
  rw [heq] at h2
  exact h2

theorem norm_jasEulerCoeff_le_one {P : Finset Nat.Primes} {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ ≤ 1)
    (m : ℕ) : ‖jasEulerCoeff P w m‖ ≤ 1 := by
  unfold jasEulerCoeff
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hw i)

theorem jasEulerCoeff_mul (P : Finset Nat.Primes) (w w' : ↥P → ℂ) (m : ℕ) :
    jasEulerCoeff P (fun i => w i * w' i) m = jasEulerCoeff P w m * jasEulerCoeff P w' m := by
  unfold jasEulerCoeff
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _

/-- **Cluster self-averaging identity.** -/
theorem sum_sum_prod_inv_eq_tsum {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    {θ : ↥P → ℂ} (hθ : ∀ i, ‖θ i‖ = 1) {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ ≤ 1)
    {z : ℂ} (hz : 0 < z.re) :
    ∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
      ∏ i : ↥P, (1 - θ i * ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-z))⁻¹ =
    ∑' m : Nat.factoredNumbers (jasPrimeNats P), jasEulerHom P θ z m *
      (Complex.normSq (∑ j ∈ t, (u j : ℂ) * jasEulerCoeff P (ψ j) m) : ℂ) := by
  classical
  have hw : ∀ j k, ∀ i : ↥P, ‖θ i * ψ j i * conj (ψ k i)‖ *
      (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) < 1 := fun j k i => by
    have h1 : ‖θ i * ψ j i * conj (ψ k i)‖ ≤ 1 := by
      rw [norm_mul, norm_mul, Complex.norm_conj, hθ, one_mul]
      exact mul_le_one₀ (hψ j i) (norm_nonneg _) (hψ k i)
    have h2 : (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (i : Nat.Primes).2.one_lt) (by linarith)
    calc ‖θ i * ψ j i * conj (ψ k i)‖ * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re)
        ≤ 1 * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ < 1 := by rw [one_mul]; exact h2
  have hS : ∀ j k, HasSum (fun m : Nat.factoredNumbers (jasPrimeNats P) =>
      (u j : ℂ) * u k * jasEulerHom P (fun i => θ i * ψ j i * conj (ψ k i)) z m)
      ((u j : ℂ) * u k * ∏ i : ↥P, (1 - θ i * ψ j i * conj (ψ k i) *
        (((i : Nat.Primes) : ℕ) : ℂ) ^ (-z))⁻¹) :=
    fun j k => (hasSum_jasEulerHom_of_lt hz (hw j k)).mul_left _
  have hsum := hasSum_sum fun j (_ : j ∈ t) => hasSum_sum fun k (_ : k ∈ t) => hS j k
  rw [← hsum.tsum_eq]
  refine tsum_congr fun m => ?_
  have hm := ne_zero_of_mem_factoredNumbers m
  have hcoef : ∀ j k, jasEulerHom P (fun i => θ i * ψ j i * conj (ψ k i)) z m =
      jasEulerHom P θ z m * (jasEulerCoeff P (ψ j) m * conj (jasEulerCoeff P (ψ k) m)) := by
    intro j k
    rw [jasEulerHom_apply _ _ hm, jasEulerHom_apply _ _ hm,
      jasEulerCoeff_mul P (fun i => θ i * ψ j i) (fun i => conj (ψ k i)),
      jasEulerCoeff_mul P θ (ψ j), jasEulerCoeff_conj]
    ring
  simp_rw [hcoef]
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- Without a twist the averaged cluster is a sum of squares. -/
theorem sum_sum_prod_inv_eq_tsum_of_one {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (P : Finset Nat.Primes) {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ ≤ 1) {σ : ℝ} (hσ : 0 < σ) :
    ∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
      ∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ =
    ∑' m : Nat.factoredNumbers (jasPrimeNats P), ((((m : ℕ) : ℝ) ^ (-σ) *
      Complex.normSq (∑ j ∈ t, (u j : ℂ) * jasEulerCoeff P (ψ j) m) : ℝ) : ℂ) := by
  have h := sum_sum_prod_inv_eq_tsum t u P (θ := fun _ => 1) (fun _ => by simp) hψ
    (z := (σ : ℂ)) (by simpa using hσ)
  simp only [one_mul] at h
  rw [h]
  refine tsum_congr fun m => ?_
  have hm := ne_zero_of_mem_factoredNumbers m
  have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [jasEulerHom_apply _ _ hm]
  have h1 : jasEulerCoeff P (fun _ => (1 : ℂ)) m = 1 := by
    unfold jasEulerCoeff; simp
  rw [h1, one_mul, Complex.ofReal_mul, Complex.ofReal_cpow hm0, Complex.ofReal_neg]
  push_cast
  ring

/-- **Phase costs modulus.**  A total phase offset `Σ_p b_p sin x_p` forces the modulus deficit
`Σ_p b_p (1 − cos x_p)` to be at least its square over `2 Σ_p b_p`. -/
theorem sq_sum_mul_sin_le {α : Type*} (s : Finset α) {b x : α → ℝ} (hb : ∀ a ∈ s, 0 ≤ b a) :
    (∑ a ∈ s, b a * Real.sin (x a)) ^ 2 ≤
      2 * (∑ a ∈ s, b a) * ∑ a ∈ s, b a * (1 - Real.cos (x a)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => Real.sqrt (b a))
    (fun a => Real.sqrt (b a) * Real.sin (x a))
  have h1 : ∀ a ∈ s, Real.sqrt (b a) * (Real.sqrt (b a) * Real.sin (x a)) =
      b a * Real.sin (x a) := fun a ha => by
    rw [← mul_assoc, Real.mul_self_sqrt (hb a ha)]
  have h2 : ∀ a ∈ s, Real.sqrt (b a) ^ 2 = b a := fun a ha => Real.sq_sqrt (hb a ha)
  have h3 : ∀ a ∈ s, (Real.sqrt (b a) * Real.sin (x a)) ^ 2 ≤ 2 * (b a * (1 - Real.cos (x a))) :=
    fun a ha => by
      rw [mul_pow, h2 a ha]
      have hsc := Real.sin_sq_add_cos_sq (x a)
      have hs : Real.sin (x a) ^ 2 ≤ 2 * (1 - Real.cos (x a)) := by
        nlinarith [sq_nonneg (1 - Real.cos (x a))]
      calc b a * Real.sin (x a) ^ 2 ≤ b a * (2 * (1 - Real.cos (x a))) :=
            mul_le_mul_of_nonneg_left hs (hb a ha)
        _ = 2 * (b a * (1 - Real.cos (x a))) := by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at hcs
  calc (∑ a ∈ s, b a * Real.sin (x a)) ^ 2
      ≤ (∑ a ∈ s, b a) * ∑ a ∈ s, (Real.sqrt (b a) * Real.sin (x a)) ^ 2 := hcs
    _ ≤ (∑ a ∈ s, b a) * ∑ a ∈ s, 2 * (b a * (1 - Real.cos (x a))) := by
        gcongr with a ha
        · exact Finset.sum_nonneg hb
        · exact h3 a ha
    _ = 2 * (∑ a ∈ s, b a) * ∑ a ∈ s, b a * (1 - Real.cos (x a)) := by
        rw [← Finset.mul_sum]; ring

end

end RHTower
