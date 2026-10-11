import GaloisForLFunctions.RHTower.JointAncestryClusterCoherence

/-!
# The two-sided cluster identity

At a point `w` of the circle the local factor of the JAS zero-sum density is
`(1 − a w)⁻¹ + (1 − b w̄)⁻¹ − 1 = (1 − a b)(1 − a w)⁻¹(1 − b w̄)⁻¹`
(`jasHoloLocal_eq_mul_inv_mul_inv`), with the a-side parameter `a = p^{−(ρ+c)}` and the b-side
parameter `b = p^{−(1−ρ+c)}` of a zero `ρ`.  For zeros with a common real part `β` these are
`a = p^{−(β+c)} ψ̄_p` and `b = p^{−(1−β+c)} ψ_p` with the phase pattern `ψ_p = p^{iγ}`, so that
`a b = p^{−(1+2c)}` is the same for every member.

Averaging the two-sided products of all members `k` at the design points `w = θ ψ_j` of all
members `j`, with real weights `u_j u_k`, gives a double Dirichlet series whose coefficients are,
up to the twist `e_θ(m) ē_θ(n)`, squared moduli (`jasTwoSidedCluster_eq_tsum`):

`Σ_{j,k} u_j u_k Π_p (1 − θ_p ψ_{j,p} ψ̄_{k,p} p^{−a})⁻¹ (1 − θ̄_p ψ̄_{j,p} ψ_{k,p} p^{−b})⁻¹
   = Σ_{m,n P-smooth} e_θ(m) ē_θ(n) m^{−a} n^{−b} |Σ_j u_j e_{ψ_j}(m) ē_{ψ_j}(n)|²`.

**Two-sided coherence threshold** (`jasClusterTwoSided_re_le`).  Let `b_p = p^{−σ} ≤ 1/100`,
`S = Σ_p b_p`, let the a-side `α_p = p^{−a} ≤ 1/100` have total mass `Σ_p α_p ≤ S/100`, and let
`θ_p = e^{iπ/S}`.  Then

`Re(twisted average) ≤ −½ (untwisted average) + 5 (Σ_j |u_j|)² Π_p (1 − α_p)⁻¹ Π_p (1 − b_p)⁻¹ e^{−S/60}`.

The twist of the term `(m, n)` is `cos(π(Ω(n) − Ω(m))/S)`, which is at most `−½` once
`Ω(m) ≤ S/12` and `3S/4 ≤ Ω(n) ≤ 4S/3`.  The three tails are Chernoff bounds with the tilts
`2^{Ω(m)}`, `(5/6)^{Ω(n)}` and `(6/5)^{Ω(n)}`.  So for a cluster of zeros with a common real part
the full two-sided local kernel obeys the exponential coherence threshold of its b-side.
-/

open Complex

namespace RHTower

open scoped ComplexConjugate

noncomputable section

/-- `‖e_w(m) m^{−z}‖ ≤ m^{−Re z}` in the closed polydisc. -/
theorem norm_jasEulerHom_le_of_norm_le {P : Finset Nat.Primes} {w : ↥P → ℂ}
    (hw : ∀ i, ‖w i‖ ≤ 1) (z : ℂ) (m : Nat.factoredNumbers (jasPrimeNats P)) :
    ‖jasEulerHom P w z m‖ ≤ ((m : ℕ) : ℝ) ^ (-z.re) := by
  rw [jasEulerHom_apply w z (ne_zero_of_mem_factoredNumbers m), norm_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (ne_zero_of_mem_factoredNumbers m)),
    Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (norm_jasEulerCoeff_le_one hw m)

/-- **The local factor on the circle** is `(1 − ab)(1 − aw)⁻¹(1 − bw̄)⁻¹`. -/
theorem jasHoloLocal_eq_mul_inv_mul_inv {a b w : ℂ} (hw : ‖w‖ = 1) (ha : 1 - a * w ≠ 0)
    (hb : 1 - b * conj w ≠ 0) :
    jasHoloLocal a b w = (1 - a * b) * ((1 - a * w)⁻¹ * (1 - b * conj w)⁻¹) := by
  have hww : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  have hx : (1 - a * w) * (1 - a * w)⁻¹ = 1 := mul_inv_cancel₀ ha
  have hy : (1 - b * conj w) * (1 - b * conj w)⁻¹ = 1 := mul_inv_cancel₀ hb
  unfold jasHoloLocal
  linear_combination (-((1 - a * w)⁻¹ - (1 - a * w) * (1 - a * w)⁻¹)) * hy +
    (-((1 - b * conj w)⁻¹ - 1)) * hx + (-(a * b) * (1 - a * w)⁻¹ * (1 - b * conj w)⁻¹) * hww

/-- The cluster average of the two-sided local products. -/
def jasTwoSidedCluster {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    (ψ : ι → ↥P → ℂ) (θ : ↥P → ℂ) (a b : ℂ) : ℂ :=
  ∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
    ((∏ i : ↥P, (1 - θ i * ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-a))⁻¹) *
      ∏ i : ↥P, (1 - conj (θ i) * conj (ψ j i) * ψ k i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-b))⁻¹)

/-- **Two-sided cluster identity.** -/
theorem jasTwoSidedCluster_eq_tsum {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (P : Finset Nat.Primes) {θ : ↥P → ℂ} (hθ : ∀ i, ‖θ i‖ = 1) {ψ : ι → ↥P → ℂ}
    (hψ : ∀ j i, ‖ψ j i‖ ≤ 1) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    jasTwoSidedCluster t u P ψ θ a b =
    ∑' x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P),
      jasEulerHom P θ a x.1 * jasEulerHom P (fun i => conj (θ i)) b x.2 *
        (Complex.normSq (∑ j ∈ t, (u j : ℂ) *
          (jasEulerCoeff P (ψ j) x.1 * conj (jasEulerCoeff P (ψ j) x.2))) : ℂ) := by
  classical
  have hθ' : ∀ i, ‖θ i‖ ≤ 1 := fun i => (hθ i).le
  have hψc : ∀ j i, ‖conj (ψ j i)‖ ≤ 1 := fun j i => by rw [Complex.norm_conj]; exact hψ j i
  have hlt : ∀ {w : ↥P → ℂ} {z : ℂ}, 0 < z.re → (∀ i, ‖w i‖ ≤ 1) →
      ∀ i : ↥P, ‖w i‖ * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) < 1 := by
    intro w z hz hw i
    have h2 : (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (i : Nat.Primes).2.one_lt)
        (by linarith)
    calc ‖w i‖ * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re)
        ≤ 1 * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-z.re) :=
          mul_le_mul_of_nonneg_right (hw i) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ < 1 := by rw [one_mul]; exact h2
  have hnorm : ∀ {w : ↥P → ℂ} {z : ℂ}, 0 < z.re → (∀ i, ‖w i‖ ≤ 1) →
      Summable fun m : Nat.factoredNumbers (jasPrimeNats P) => ‖jasEulerHom P w z m‖ :=
    fun hz hw => (summable_rpow_neg_factored hz P).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_jasEulerHom_le_of_norm_le hw _)
  have hAd : ∀ j k, ∀ i, ‖θ i * ψ j i * conj (ψ k i)‖ ≤ 1 := fun j k i => by
    rw [norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (hθ' i) (norm_nonneg _) (hψ j i)) (norm_nonneg _) (hψc k i)
  have hBd : ∀ j k, ∀ i, ‖conj (θ i) * conj (ψ j i) * ψ k i‖ ≤ 1 := fun j k i => by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (mul_le_one₀ (hθ' i) (norm_nonneg _) (hψc j i)) (norm_nonneg _) (hψ k i)
  have hpair : ∀ j k, HasSum (fun x : Nat.factoredNumbers (jasPrimeNats P) ×
      Nat.factoredNumbers (jasPrimeNats P) => (u j : ℂ) * u k *
        (jasEulerHom P (fun i => θ i * ψ j i * conj (ψ k i)) a x.1 *
          jasEulerHom P (fun i => conj (θ i) * conj (ψ j i) * ψ k i) b x.2))
      ((u j : ℂ) * u k *
        ((∏ i : ↥P, (1 - θ i * ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-a))⁻¹) *
          ∏ i : ↥P, (1 - conj (θ i) * conj (ψ j i) * ψ k i *
            (((i : Nat.Primes) : ℕ) : ℂ) ^ (-b))⁻¹)) := by
    intro j k
    have hsA : HasSum (fun m : Nat.factoredNumbers (jasPrimeNats P) =>
        jasEulerHom P (fun i => θ i * ψ j i * conj (ψ k i)) a m)
        (∏ i : ↥P, (1 - θ i * ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-a))⁻¹) :=
      hasSum_jasEulerHom_of_lt ha (hlt ha (hAd j k))
    have hsB : HasSum (fun n : Nat.factoredNumbers (jasPrimeNats P) =>
        jasEulerHom P (fun i => conj (θ i) * conj (ψ j i) * ψ k i) b n)
        (∏ i : ↥P, (1 - conj (θ i) * conj (ψ j i) * ψ k i *
          (((i : Nat.Primes) : ℕ) : ℂ) ^ (-b))⁻¹) :=
      hasSum_jasEulerHom_of_lt hb (hlt hb (hBd j k))
    have hnA := hnorm ha (hAd j k)
    have hnB := hnorm hb (hBd j k)
    have hprod : (∏ i : ↥P, (1 - θ i * ψ j i * conj (ψ k i) *
          (((i : Nat.Primes) : ℕ) : ℂ) ^ (-a))⁻¹) *
        ∏ i : ↥P, (1 - conj (θ i) * conj (ψ j i) * ψ k i *
          (((i : Nat.Primes) : ℕ) : ℂ) ^ (-b))⁻¹ =
        ∑' x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P),
          jasEulerHom P (fun i => θ i * ψ j i * conj (ψ k i)) a x.1 *
            jasEulerHom P (fun i => conj (θ i) * conj (ψ j i) * ψ k i) b x.2 := by
      rw [← hsA.tsum_eq, ← hsB.tsum_eq]
      exact tsum_mul_tsum_of_summable_norm hnA hnB
    rw [hprod]
    exact (summable_mul_of_summable_norm hnA hnB).hasSum.mul_left _
  have hsum := hasSum_sum fun j (_ : j ∈ t) => hasSum_sum fun k (_ : k ∈ t) => hpair j k
  rw [jasTwoSidedCluster, ← hsum.tsum_eq]
  refine tsum_congr fun x => ?_
  have hm := ne_zero_of_mem_factoredNumbers x.1
  have hn := ne_zero_of_mem_factoredNumbers x.2
  have hcA : ∀ j k, jasEulerHom P (fun i => θ i * ψ j i * conj (ψ k i)) a x.1 =
      jasEulerHom P θ a x.1 *
        (jasEulerCoeff P (ψ j) x.1 * conj (jasEulerCoeff P (ψ k) x.1)) := by
    intro j k
    rw [jasEulerHom_apply _ _ hm, jasEulerHom_apply _ _ hm,
      jasEulerCoeff_mul P (fun i => θ i * ψ j i) (fun i => conj (ψ k i)),
      jasEulerCoeff_mul P θ (ψ j), jasEulerCoeff_conj]
    ring
  have hcB : ∀ j k, jasEulerHom P (fun i => conj (θ i) * conj (ψ j i) * ψ k i) b x.2 =
      jasEulerHom P (fun i => conj (θ i)) b x.2 *
        (conj (jasEulerCoeff P (ψ j) x.2) * jasEulerCoeff P (ψ k) x.2) := by
    intro j k
    rw [jasEulerHom_apply _ _ hn, jasEulerHom_apply _ _ hn,
      jasEulerCoeff_mul P (fun i => conj (θ i) * conj (ψ j i)) (ψ k),
      jasEulerCoeff_mul P (fun i => conj (θ i)) (fun i => conj (ψ j i)),
      jasEulerCoeff_conj P (ψ j) x.2]
    ring
  simp_rw [hcA, hcB]
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- Doubling the a-side tilt costs at most `e^{(50/49) α}` per prime. -/
theorem prod_tilt_double_le {P : Finset Nat.Primes} {α : ↥P → ℝ} (hα0 : ∀ i, 0 ≤ α i)
    (hα : ∀ i, α i ≤ 1 / 100) :
    ∏ i : ↥P, (1 - 2 * α i)⁻¹ ≤
      (∏ i : ↥P, (1 - α i)⁻¹) * Real.exp (50 / 49 * ∑ i : ↥P, α i) := by
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => (inv_pos.mpr (by linarith [hα i])).le) fun i _ => ?_
  have h1 : 0 < 1 - α i := by linarith [hα i]
  have h2 : 0 < 1 - 2 * α i := by linarith [hα i]
  have h3 : (1 - α i) / (1 - 2 * α i) ≤ Real.exp (50 / 49 * α i) := by
    rw [div_le_iff₀ h2]
    have := Real.add_one_le_exp (50 / 49 * α i)
    nlinarith [hα0 i, hα i]
  calc (1 - 2 * α i)⁻¹ = (1 - α i)⁻¹ * ((1 - α i) / (1 - 2 * α i)) := by
        field_simp
    _ ≤ (1 - α i)⁻¹ * Real.exp (50 / 49 * α i) :=
        mul_le_mul_of_nonneg_left h3 (inv_pos.mpr h1).le

theorem re_exp_mul_I_mul_conj_exp_mul_I (x y : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I) * conj (Complex.exp ((y : ℂ) * Complex.I))).re =
      Real.cos (x - y) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add,
    show (x : ℂ) * Complex.I + (y : ℂ) * -Complex.I = ((x - y : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_ofReal_mul_I_re]

theorem normSq_twoSided_le {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ ≤ 1) (m n : ℕ) :
    Complex.normSq (∑ j ∈ t, (u j : ℂ) *
      (jasEulerCoeff P (ψ j) m * conj (jasEulerCoeff P (ψ j) n))) ≤ (∑ j ∈ t, |u j|) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h : ‖∑ j ∈ t, (u j : ℂ) * (jasEulerCoeff P (ψ j) m * conj (jasEulerCoeff P (ψ j) n))‖ ≤
      ∑ j ∈ t, |u j| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (mul_le_one₀ (norm_jasEulerCoeff_le_one (hψ j) m) (norm_nonneg _)
        (norm_jasEulerCoeff_le_one (hψ j) n))
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem jasTwoSided_term_re (P : Finset Nat.Primes) (a σ τ : ℝ)
    (m n : Nat.factoredNumbers (jasPrimeNats P)) (r : ℝ) :
    (jasEulerHom P (fun _ => Complex.exp ((τ : ℂ) * Complex.I)) (a : ℂ) m *
        jasEulerHom P (fun _ => conj (Complex.exp ((τ : ℂ) * Complex.I))) (σ : ℂ) n *
          (r : ℂ)).re =
      Real.cos (τ * jasDeg P m - τ * jasDeg P n) *
        (((m : ℕ) : ℝ) ^ (-a) * ((n : ℕ) : ℝ) ^ (-σ) * r) := by
  rw [jasEulerHom_apply _ _ (ne_zero_of_mem_factoredNumbers m),
    jasEulerHom_apply _ _ (ne_zero_of_mem_factoredNumbers n), jasEulerCoeff_const,
    jasEulerCoeff_const, rpow_natCast_neg_ofReal, rpow_natCast_neg_ofReal, ← map_pow,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have e1 : ((jasDeg P m : ℕ) : ℂ) * ((τ : ℂ) * Complex.I) =
      ((τ * jasDeg P m : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e2 : ((jasDeg P n : ℕ) : ℂ) * ((τ : ℂ) * Complex.I) =
      ((τ * jasDeg P n : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e1, e2]
  have hrw : Complex.exp (((τ * jasDeg P m : ℝ) : ℂ) * Complex.I) *
        (((((m : ℕ) : ℝ) ^ (-a) : ℝ)) : ℂ) *
        (conj (Complex.exp (((τ * jasDeg P n : ℝ) : ℂ) * Complex.I)) *
          (((((n : ℕ) : ℝ) ^ (-σ) : ℝ)) : ℂ)) * (r : ℂ) =
      Complex.exp (((τ * jasDeg P m : ℝ) : ℂ) * Complex.I) *
        conj (Complex.exp (((τ * jasDeg P n : ℝ) : ℂ) * Complex.I)) *
          ((((m : ℕ) : ℝ) ^ (-a) * ((n : ℕ) : ℝ) ^ (-σ) * r : ℝ) : ℂ) := by
    push_cast; ring
  rw [hrw, Complex.re_mul_ofReal, re_exp_mul_I_mul_conj_exp_mul_I]

/-- **The twisted cluster average as a cosine series.** -/
theorem re_jasTwoSidedCluster_exp_eq {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (P : Finset Nat.Primes) {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ ≤ 1) {a σ : ℝ} (ha : 0 < a)
    (hσ : 0 < σ) (τ : ℝ) :
    (jasTwoSidedCluster t u P ψ (fun _ => Complex.exp ((τ : ℂ) * Complex.I)) a σ).re =
      ∑' x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P),
        Real.cos (τ * jasDeg P x.1 - τ * jasDeg P x.2) *
          (((x.1 : ℕ) : ℝ) ^ (-a) * ((x.2 : ℕ) : ℝ) ^ (-σ) *
            Complex.normSq (∑ j ∈ t, (u j : ℂ) *
              (jasEulerCoeff P (ψ j) x.1 * conj (jasEulerCoeff P (ψ j) x.2)))) := by
  have hθ : ∀ i : ↥P, ‖(fun _ : ↥P => Complex.exp ((τ : ℂ) * Complex.I)) i‖ = 1 := fun _ =>
    Complex.norm_exp_ofReal_mul_I τ
  have hθc : ∀ i : ↥P, ‖(fun _ : ↥P => conj (Complex.exp ((τ : ℂ) * Complex.I))) i‖ = 1 :=
    fun _ => by rw [Complex.norm_conj]; exact Complex.norm_exp_ofReal_mul_I τ
  have ha' : 0 < (a : ℂ).re := by rw [Complex.ofReal_re]; exact ha
  have hσ' : 0 < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact hσ
  rw [jasTwoSidedCluster_eq_tsum t u P hθ hψ ha' hσ', Complex.re_tsum]
  · exact tsum_congr fun x => jasTwoSided_term_re P a σ τ x.1 x.2 _
  · have hs := (summable_rpow_neg_factored' ha P).mul_of_nonneg
      (summable_rpow_neg_factored' hσ P) (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    refine Summable.of_norm_bounded (hs.mul_left ((∑ j ∈ t, |u j|) ^ 2)) fun x => ?_
    rw [norm_mul, norm_mul, norm_jasEulerHom_factored hθ, norm_jasEulerHom_factored hθc,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.ofReal_re, Complex.ofReal_re]
    have := normSq_twoSided_le t u P hψ x.1 x.2
    have h1 := Real.rpow_nonneg (Nat.cast_nonneg ((x.1 : ℕ))) (-a)
    have h2 := Real.rpow_nonneg (Nat.cast_nonneg ((x.2 : ℕ))) (-σ)
    calc ((x.1 : ℕ) : ℝ) ^ (-a) * ((x.2 : ℕ) : ℝ) ^ (-σ) * _
        ≤ ((x.1 : ℕ) : ℝ) ^ (-a) * ((x.2 : ℕ) : ℝ) ^ (-σ) * (∑ j ∈ t, |u j|) ^ 2 :=
          mul_le_mul_of_nonneg_left this (mul_nonneg h1 h2)
      _ = _ := by ring

/-- Chernoff tail of the a-side count above `S/12`, when the a-side mass is at most `S/100`. -/
theorem jasTwoSided_tail_a_le {P : Finset Nat.Primes} {a S : ℝ} (ha : 0 < a) (hS : 0 ≤ S)
    (hα : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤ 1 / 100)
    (hαS : ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤ S / 100) :
    ∑' m : Nat.factoredNumbers (jasPrimeNats P),
        (if S / 12 < (jasDeg P m : ℝ) then ((m : ℕ) : ℝ) ^ (-a) else 0) ≤
      (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) * Real.exp (-(S / 60)) := by
  have hα0 : ∀ i : ↥P, 0 ≤ (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) := fun i =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 := tsum_tail_above_le (P := P) (A := S / 12) ha (by norm_num : (1:ℝ) ≤ 2)
    (fun i => by have := hα i; linarith)
  have h2 := prod_tilt_double_le hα0 hα
  have hlog : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num); norm_num at this ⊢
    linarith
  have hGa : 0 ≤ ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹ :=
    Finset.prod_nonneg fun i _ => (inv_pos.mpr (by linarith [hα i])).le
  have h3 : Real.exp (-(S / 12 * Real.log 2)) *
      Real.exp (50 / 49 * ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a)) ≤
      Real.exp (-(S / 60)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  calc _ ≤ Real.exp (-(S / 12 * Real.log 2)) *
        ∏ i : ↥P, (1 - 2 * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹ := h1
    _ ≤ Real.exp (-(S / 12 * Real.log 2)) *
        ((∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
          Real.exp (50 / 49 * ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
        (Real.exp (-(S / 12 * Real.log 2)) *
          Real.exp (50 / 49 * ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hGa

/-- Chernoff tail of the b-side count above `4S/3`. -/
theorem jasTwoSided_tail_up_le {P : Finset Nat.Primes} {σ : ℝ} (hσ : 0 < σ)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100) :
    ∑' n : Nat.factoredNumbers (jasPrimeNats P),
        (if 4 * (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 3 < (jasDeg P n : ℝ) then
          ((n : ℕ) : ℝ) ^ (-σ) else 0) ≤
      (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
  have hb0 : ∀ i : ↥P, 0 ≤ (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) := fun i =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hS : 0 ≤ ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) :=
    Finset.sum_nonneg fun i _ => hb0 i
  have h1 := tsum_tail_above_le (P := P)
    (A := 4 * (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 3) hσ
    (by norm_num : (1:ℝ) ≤ 6 / 5) (fun i => by have := hb i; linarith)
  have h2 := prod_tilt_up_le hb0 hb
  have hlog : 1 / 6 ≤ Real.log (6 / 5) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 6 / 5 by norm_num); norm_num at this ⊢
    linarith
  have hGb : 0 ≤ ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ :=
    Finset.prod_nonneg fun i _ => (inv_pos.mpr (by linarith [hb i])).le
  have h3 : Real.exp (-(4 * (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 3 *
        Real.log (6 / 5))) *
      Real.exp (100 / 494 * ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) ≤
      Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hGb

/-- Chernoff tail of the b-side count below `3S/4`. -/
theorem jasTwoSided_tail_dn_le {P : Finset Nat.Primes} {σ : ℝ} (hσ : 0 < σ)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100) :
    ∑' n : Nat.factoredNumbers (jasPrimeNats P),
        (if (jasDeg P n : ℝ) < 3 * (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 4 then
          ((n : ℕ) : ℝ) ^ (-σ) else 0) ≤
      (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
  have hb0 : ∀ i : ↥P, 0 ≤ (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) := fun i =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hS : 0 ≤ ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) :=
    Finset.sum_nonneg fun i _ => hb0 i
  have h1 := tsum_tail_below_le (P := P)
    (A := 3 * (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 4) hσ
    (by norm_num : (0:ℝ) < 5 / 6) (by norm_num) (fun i => by have := hb i; linarith)
  have h2 := prod_tilt_down_le hb0 hb
  have hlog : -(1 / 5) ≤ Real.log (5 / 6) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 5 / 6 by norm_num); norm_num at this ⊢
    linarith
  have hGb : 0 ≤ ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ :=
    Finset.prod_nonneg fun i _ => (inv_pos.mpr (by linarith [hb i])).le
  have h3 : Real.exp (-(3 * (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 4 *
        Real.log (5 / 6))) *
      Real.exp (-(1 / 6 * ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))) ≤
      Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hGb

/-- **The cosine series of a two-sided cluster is at most `−½` of its mass, up to the tails.** -/
theorem jasTwoSided_cos_tsum_le {P : Finset Nat.Primes} {a σ S : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (hα : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤ 1 / 100)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hSdef : S = ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) (hS : 0 < S)
    (hαS : ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤ S / 100)
    {W : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P) → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hW0 : ∀ x, 0 ≤ W x)
    (hWle : ∀ x, W x ≤ K * (((x.1 : ℕ) : ℝ) ^ (-a) * ((x.2 : ℕ) : ℝ) ^ (-σ))) :
    ∑' x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P),
        Real.cos (Real.pi / S * jasDeg P x.1 - Real.pi / S * jasDeg P x.2) * W x ≤
      -(1 / 2) * ∑' x : Nat.factoredNumbers (jasPrimeNats P) ×
          Nat.factoredNumbers (jasPrimeNats P), W x +
        5 * K * (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
          (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) * Real.exp (-(S / 60)) := by
  classical
  have hpos : ∀ (m : Nat.factoredNumbers (jasPrimeNats P)) (s : ℝ), 0 ≤ ((m : ℕ) : ℝ) ^ s :=
    fun m s => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsa := summable_rpow_neg_factored' ha P
  have hsb := summable_rpow_neg_factored' hσ P
  have hsab : Summable fun x : Nat.factoredNumbers (jasPrimeNats P) ×
      Nat.factoredNumbers (jasPrimeNats P) => ((x.1 : ℕ) : ℝ) ^ (-a) * ((x.2 : ℕ) : ℝ) ^ (-σ) :=
    hsa.mul_of_nonneg hsb (fun m => hpos m _) (fun n => hpos n _)
  have hWs : Summable W := (hsab.mul_left K).of_nonneg_of_le hW0 hWle
  -- indicators of the three tails
  obtain ⟨Ia, hIa⟩ : ∃ f : Nat.factoredNumbers (jasPrimeNats P) → ℝ, ∀ m,
      f m = if S / 12 < (jasDeg P m : ℝ) then ((m : ℕ) : ℝ) ^ (-a) else 0 :=
    ⟨fun m => if S / 12 < (jasDeg P m : ℝ) then ((m : ℕ) : ℝ) ^ (-a) else 0, fun _ => rfl⟩
  obtain ⟨Iup, hIup⟩ : ∃ f : Nat.factoredNumbers (jasPrimeNats P) → ℝ, ∀ n,
      f n = if 4 * S / 3 < (jasDeg P n : ℝ) then ((n : ℕ) : ℝ) ^ (-σ) else 0 :=
    ⟨fun n => if 4 * S / 3 < (jasDeg P n : ℝ) then ((n : ℕ) : ℝ) ^ (-σ) else 0, fun _ => rfl⟩
  obtain ⟨Idn, hIdn⟩ : ∃ f : Nat.factoredNumbers (jasPrimeNats P) → ℝ, ∀ n,
      f n = if (jasDeg P n : ℝ) < 3 * S / 4 then ((n : ℕ) : ℝ) ^ (-σ) else 0 :=
    ⟨fun n => if (jasDeg P n : ℝ) < 3 * S / 4 then ((n : ℕ) : ℝ) ^ (-σ) else 0, fun _ => rfl⟩
  have hIa0 : ∀ m, 0 ≤ Ia m := fun m => by
    have := hpos m (-a)
    rw [hIa]; split_ifs <;> linarith
  have hIu0 : ∀ m, 0 ≤ Iup m := fun m => by
    have := hpos m (-σ)
    rw [hIup]; split_ifs <;> linarith
  have hId0 : ∀ m, 0 ≤ Idn m := fun m => by
    have := hpos m (-σ)
    rw [hIdn]; split_ifs <;> linarith
  have hIas : Summable Ia := hsa.of_nonneg_of_le hIa0 fun m => by
    have := hpos m (-a)
    rw [hIa]; split_ifs <;> linarith
  have hIus : Summable Iup := hsb.of_nonneg_of_le hIu0 fun m => by
    have := hpos m (-σ)
    rw [hIup]; split_ifs <;> linarith
  have hIds : Summable Idn := hsb.of_nonneg_of_le hId0 fun m => by
    have := hpos m (-σ)
    rw [hIdn]; split_ifs <;> linarith
  obtain ⟨Bad, hBad⟩ : ∃ f : Nat.factoredNumbers (jasPrimeNats P) ×
      Nat.factoredNumbers (jasPrimeNats P) → ℝ,
      f = fun x => Ia x.1 * ((x.2 : ℕ) : ℝ) ^ (-σ) + ((x.1 : ℕ) : ℝ) ^ (-a) * (Iup x.2 + Idn x.2) :=
    ⟨_, rfl⟩
  have hBadx : ∀ x, Bad x = Ia x.1 * ((x.2 : ℕ) : ℝ) ^ (-σ) +
      ((x.1 : ℕ) : ℝ) ^ (-a) * (Iup x.2 + Idn x.2) := fun x => by rw [hBad]
  have hBad0 : ∀ x, 0 ≤ Bad x := fun x => by
    rw [hBad]
    exact add_nonneg (mul_nonneg (hIa0 _) (hpos _ _))
      (mul_nonneg (hpos _ _) (add_nonneg (hIu0 _) (hId0 _)))
  have hIule : ∀ n : Nat.factoredNumbers (jasPrimeNats P), Iup n ≤ ((n : ℕ) : ℝ) ^ (-σ) :=
    fun n => by have := hpos n (-σ); rw [hIup]; split_ifs <;> linarith
  have hIdle : ∀ n : Nat.factoredNumbers (jasPrimeNats P), Idn n ≤ ((n : ℕ) : ℝ) ^ (-σ) :=
    fun n => by have := hpos n (-σ); rw [hIdn]; split_ifs <;> linarith
  have hIale : ∀ m : Nat.factoredNumbers (jasPrimeNats P), Ia m ≤ ((m : ℕ) : ℝ) ^ (-a) :=
    fun m => by have := hpos m (-a); rw [hIa]; split_ifs <;> linarith
  have hs1 : Summable fun x : Nat.factoredNumbers (jasPrimeNats P) ×
      Nat.factoredNumbers (jasPrimeNats P) => Ia x.1 * ((x.2 : ℕ) : ℝ) ^ (-σ) :=
    hsab.of_nonneg_of_le (fun x => mul_nonneg (hIa0 _) (hpos _ _))
      (fun x => mul_le_mul_of_nonneg_right (hIale x.1) (hpos _ _))
  have hs2 : Summable fun x : Nat.factoredNumbers (jasPrimeNats P) ×
      Nat.factoredNumbers (jasPrimeNats P) => ((x.1 : ℕ) : ℝ) ^ (-a) * (Iup x.2 + Idn x.2) :=
    (hsab.mul_left 2).of_nonneg_of_le
      (fun x => mul_nonneg (hpos _ _) (add_nonneg (hIu0 _) (hId0 _)))
      (fun x => by
        have := mul_le_mul_of_nonneg_left (add_le_add (hIule x.2) (hIdle x.2)) (hpos x.1 (-a))
        linarith)
  have hsum2 : Summable fun n : Nat.factoredNumbers (jasPrimeNats P) => Iup n + Idn n :=
    hIus.add hIds
  have hBads : Summable Bad := by rw [hBad]; exact hs1.add hs2
  -- pointwise bound
  have hpt : ∀ x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P),
      Real.cos (Real.pi / S * jasDeg P x.1 - Real.pi / S * jasDeg P x.2) * W x ≤
        -(1 / 2) * W x + 3 / 2 * K * Bad x := by
    intro x
    have hm0 := hpos x.1 (-a)
    have hn0 := hpos x.2 (-σ)
    have hKB : 0 ≤ 3 / 2 * K * Bad x := mul_nonneg (by positivity) (hBad0 x)
    by_cases hmid : (jasDeg P x.1 : ℝ) ≤ S / 12 ∧ 3 * S / 4 ≤ (jasDeg P x.2 : ℝ) ∧
        (jasDeg P x.2 : ℝ) ≤ 4 * S / 3
    · have hdeg0 : (0 : ℝ) ≤ jasDeg P x.1 := Nat.cast_nonneg _
      have hc : Real.cos (Real.pi / S * jasDeg P x.1 - Real.pi / S * jasDeg P x.2) ≤ -(1 / 2) := by
        rw [← Real.cos_neg, neg_sub, ← mul_sub]
        apply cos_le_neg_half
        · rw [div_mul_eq_mul_div, le_div_iff₀ hS]; nlinarith [Real.pi_pos, hmid.1, hmid.2.1]
        · rw [div_mul_eq_mul_div, div_le_iff₀ hS]; nlinarith [Real.pi_pos, hmid.2.2, hdeg0]
      nlinarith [hW0 x]
    · have hind : ((x.1 : ℕ) : ℝ) ^ (-a) * ((x.2 : ℕ) : ℝ) ^ (-σ) ≤ Bad x := by
        have hu := hIu0 x.2
        have hd := hId0 x.2
        by_cases h1 : S / 12 < (jasDeg P x.1 : ℝ)
        · have hIx : Ia x.1 = ((x.1 : ℕ) : ℝ) ^ (-a) := by rw [hIa, if_pos h1]
          rw [hBadx, hIx]
          nlinarith [mul_nonneg hm0 (add_nonneg hu hd)]
        · push Not at h1
          have hn1 : 0 ≤ Ia x.1 := hIa0 x.1
          by_cases h3 : 4 * S / 3 < (jasDeg P x.2 : ℝ)
          · have hIx : Iup x.2 = ((x.2 : ℕ) : ℝ) ^ (-σ) := by rw [hIup, if_pos h3]
            rw [hBadx, hIx]
            nlinarith [mul_nonneg hn1 hn0, mul_nonneg hm0 hd]
          · have h4 : (jasDeg P x.2 : ℝ) < 3 * S / 4 := by
              by_contra h5
              push Not at h3 h5
              exact hmid ⟨h1, h5, h3⟩
            have hIx : Idn x.2 = ((x.2 : ℕ) : ℝ) ^ (-σ) := by rw [hIdn, if_pos h4]
            rw [hBadx, hIx]
            nlinarith [mul_nonneg hn1 hn0, mul_nonneg hm0 hu]
      have hc := Real.cos_le_one (Real.pi / S * jasDeg P x.1 - Real.pi / S * jasDeg P x.2)
      have := hWle x
      nlinarith [hW0 x, mul_le_mul_of_nonneg_left hind hK]
  have hcs : Summable fun x : Nat.factoredNumbers (jasPrimeNats P) ×
      Nat.factoredNumbers (jasPrimeNats P) =>
      Real.cos (Real.pi / S * jasDeg P x.1 - Real.pi / S * jasDeg P x.2) * W x :=
    hWs.of_norm_bounded fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 x)]
      exact mul_le_of_le_one_left (hW0 x) (Real.abs_cos_le_one _)
  have hsplit := Summable.tsum_le_tsum hpt hcs ((hWs.mul_left (-(1 / 2))).add (hBads.mul_left _))
  rw [Summable.tsum_add (hWs.mul_left _) (hBads.mul_left _), tsum_mul_left, tsum_mul_left]
    at hsplit
  -- the bad mass
  have hnormI : ∀ {f : Nat.factoredNumbers (jasPrimeNats P) → ℝ}, Summable f → (∀ m, 0 ≤ f m) →
      Summable fun m => ‖f m‖ := fun hf h0 =>
    hf.congr fun m => (Real.norm_of_nonneg (h0 m)).symm
  have hBadEq : ∑' x : Nat.factoredNumbers (jasPrimeNats P) ×
        Nat.factoredNumbers (jasPrimeNats P), Bad x =
      (∑' m : Nat.factoredNumbers (jasPrimeNats P), Ia m) *
          (∑' n : Nat.factoredNumbers (jasPrimeNats P), ((n : ℕ) : ℝ) ^ (-σ)) +
        (∑' m : Nat.factoredNumbers (jasPrimeNats P), ((m : ℕ) : ℝ) ^ (-a)) *
          ((∑' n : Nat.factoredNumbers (jasPrimeNats P), Iup n) +
            ∑' n : Nat.factoredNumbers (jasPrimeNats P), Idn n) := by
    rw [hBad, Summable.tsum_add hs1 hs2, ← Summable.tsum_add hIus hIds,
      tsum_mul_tsum_of_summable_norm (hnormI hIas hIa0) (hnormI hsb fun n => hpos n _),
      tsum_mul_tsum_of_summable_norm (hnormI hsa fun m => hpos m _)
        (hnormI hsum2 fun n => add_nonneg (hIu0 n) (hId0 n))]
  have hZa : ∑' m : Nat.factoredNumbers (jasPrimeNats P), ((m : ℕ) : ℝ) ^ (-a) =
      ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹ := by
    have h := hasSum_tilt (P := P) (t := 1) ha zero_le_one (fun i => by
      have := hα i; rw [one_mul]; linarith)
    simp only [one_pow, one_mul] at h
    exact h.tsum_eq
  have hZb : ∑' n : Nat.factoredNumbers (jasPrimeNats P), ((n : ℕ) : ℝ) ^ (-σ) =
      ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ := by
    have h := hasSum_tilt (P := P) (t := 1) hσ zero_le_one (fun i => by
      have := hb i; rw [one_mul]; linarith)
    simp only [one_pow, one_mul] at h
    exact h.tsum_eq
  have hGa : 0 ≤ ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹ :=
    Finset.prod_nonneg fun i _ => (inv_pos.mpr (by linarith [hα i])).le
  have hGb : 0 ≤ ∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ :=
    Finset.prod_nonneg fun i _ => (inv_pos.mpr (by linarith [hb i])).le
  have hta : ∑' m : Nat.factoredNumbers (jasPrimeNats P), Ia m ≤
      (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) * Real.exp (-(S / 60)) := by
    rw [tsum_congr hIa]
    exact jasTwoSided_tail_a_le ha hS.le hα hαS
  have htu : ∑' n : Nat.factoredNumbers (jasPrimeNats P), Iup n ≤
      (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) * Real.exp (-(S / 60)) := by
    have h := jasTwoSided_tail_up_le (P := P) hσ hb
    rw [← hSdef] at h
    rw [tsum_congr hIup]
    exact h
  have htd : ∑' n : Nat.factoredNumbers (jasPrimeNats P), Idn n ≤
      (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) * Real.exp (-(S / 60)) := by
    have h := jasTwoSided_tail_dn_le (P := P) hσ hb
    rw [← hSdef] at h
    rw [tsum_congr hIdn]
    exact h
  have hE := (Real.exp_pos (-(S / 60))).le
  have hBadle : ∑' x : Nat.factoredNumbers (jasPrimeNats P) ×
        Nat.factoredNumbers (jasPrimeNats P), Bad x ≤
      3 * (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
        (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) * Real.exp (-(S / 60)) := by
    rw [hBadEq, hZa, hZb]
    nlinarith [mul_le_mul_of_nonneg_right hta hGb,
      mul_le_mul_of_nonneg_left (add_le_add htu htd) hGa, mul_nonneg (mul_nonneg hGa hGb) hE]
  nlinarith [mul_le_mul_of_nonneg_left hBadle (show 0 ≤ 3 / 2 * K by positivity),
    mul_nonneg (mul_nonneg (mul_nonneg hK hGa) hGb) hE]

/-- **Two-sided exponential coherence threshold.** -/
theorem jasClusterTwoSided_re_le {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ ≤ 1) {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (hα : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤ 1 / 100)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hS : 0 < ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))
    (hαS : ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a) ≤
      (∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 100) :
    (jasTwoSidedCluster t u P ψ
        (fun _ => Complex.exp (((Real.pi / ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.I)) a σ).re ≤
      -(1 / 2) * (jasTwoSidedCluster t u P ψ (fun _ => 1) a σ).re +
      5 * (∑ j ∈ t, |u j|) ^ 2 * (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-a))⁻¹) *
        (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) := ⟨_, rfl⟩
  rw [← hSdef] at hS hαS ⊢
  have h1 := re_jasTwoSidedCluster_exp_eq t u P hψ ha hσ (Real.pi / S)
  have h0 := re_jasTwoSidedCluster_exp_eq t u P hψ ha hσ 0
  have hone : (fun _ : ↥P => Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) = fun _ => 1 := by
    funext _; rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [hone] at h0
  simp only [zero_mul, sub_zero, Real.cos_zero, one_mul] at h0
  rw [h1, h0]
  refine jasTwoSided_cos_tsum_le ha hσ hα hb hSdef hS hαS (sq_nonneg _)
    (fun x => mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Complex.normSq_nonneg _)) fun x => ?_
  rw [mul_comm ((∑ j ∈ t, |u j|) ^ 2)]
  exact mul_le_mul_of_nonneg_left (normSq_twoSided_le t u P hψ _ _)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end

end RHTower
