import GaloisForLFunctions.RHTower.PoissonPrimeKernelCalkinModel
import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-!
# Clock commutators of the prime Poisson kernel

Let `K(p,q) = (pq)^{-1/2} h(x_p - x_q)` be the all-aperture prime Poisson kernel, `x_p = log log p`
the Mertens clock and `t_p = log p` the physical clock.

* **Mertens clock.**  Multiplication by `x_p` is unbounded, but `K` maps finitely supported vectors
  into its domain and the core commutator `XK - KX` is the bounded skew-adjoint operator `C` with
  matrix `(x_p - x_q) K(p,q)`.  `C` is not compact: `‖C‖_ess ≥ h(3)`.
* **Physical clock powers.**  For `β < 0` the multiplier `T^β` is compact, so `[T^β, K]` is compact;
  at `β = 0` the commutator vanishes and its derivative in `β` is `C`; for `0 < β < 1` every column
  `K δ_q` lies in the domain of `T^β` but the commutator matrix `(t_p^β - t_q^β) K(p,q)` is the matrix
  of no bounded operator; for `β ≥ 1` no column lies in the domain of `T^β`.
* **Reflected kernels.**  For `g ≠ 0` no column of `K(p,q) cosh(g(t_p+t_q)/2)` or of
  `K(p,q) sinh(g(t_p+t_q)/2)` is square summable.

The lower bounds use the normalized shell vectors `e_n = ∑_{p ∈ S_n} (m_n p)^{-1/2} δ_p` over the
Mertens shells `S_n = {n ≤ x_p < n + 1}`: on `S_n × S_{n+2}` the clock gap lies in `(1, 3)`, so the
cross-shell pairing is at least `h(3) √(m_n m_{n+2}) → h(3)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ### Finite combinations of basis vectors -/

theorem inner_lpBasisVec_lpBasisVec (p q : Nat.Primes) :
    inner ℂ (lpBasisVec p) (lpBasisVec q) = if p = q then (1 : ℂ) else 0 := by
  classical
  rw [← coord_eq_inner, lpBasisVec, lp.single_apply]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg h, Pi.single_eq_of_ne h]

/-- Coordinates of an operator on a finite combination of basis vectors. -/
theorem coord_apply_sum {T : ℓ²P →L[ℂ] ℓ²P} {M : Nat.Primes → Nat.Primes → ℂ} (hT : HasLpMatrix T M)
    (s : Finset Nat.Primes) (c : Nat.Primes → ℂ) (p : Nat.Primes) :
    (T (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) p = ∑ q ∈ s, c q * M p q := by
  rw [coord_eq_inner, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, inner_smul_right, ← coord_eq_inner, hT p q]

theorem coord_sum (s : Finset Nat.Primes) (c : Nat.Primes → ℂ) (p : Nat.Primes) :
    ((∑ q ∈ s, c q • lpBasisVec q : ℓ²P) : Nat.Primes → ℂ) p = if p ∈ s then c p else 0 := by
  classical
  rw [coord_eq_inner, inner_sum]
  simp_rw [inner_smul_right, inner_lpBasisVec_lpBasisVec, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-! ### Shell vectors -/

/-- The shell coefficient `(m_n p)^{-1/2}`. -/
def shellCoeff (n : ℕ) (p : Nat.Primes) : ℝ := (Real.sqrt (mertensShellMass n * (p : ℕ)))⁻¹

theorem shellCoeff_nonneg (n : ℕ) (p : Nat.Primes) : 0 ≤ shellCoeff n p :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- The normalized shell vector `e_n = ∑_{p ∈ S_n} (m_n p)^{-1/2} δ_p`. -/
def mertensShellVec (n : ℕ) : ℓ²P :=
  ∑ p ∈ mertensShell n, ((shellCoeff n p : ℝ) : ℂ) • lpBasisVec p

theorem shellCoeff_sq {n : ℕ} (hn : 0 < mertensShellMass n) (p : Nat.Primes) :
    shellCoeff n p ^ 2 = 1 / (mertensShellMass n * (p : ℕ)) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  rw [shellCoeff, inv_pow, Real.sq_sqrt (by positivity), one_div]

theorem shellCoeff_div_sqrt {n : ℕ} (hn : 0 < mertensShellMass n) (p : Nat.Primes) :
    shellCoeff n p / Real.sqrt (p : ℕ) = (Real.sqrt (mertensShellMass n))⁻¹ * (1 / (p : ℕ)) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  rw [shellCoeff, Real.sqrt_mul hn.le]
  have h1 := Real.sqrt_pos.mpr hn
  have h2 := Real.sqrt_pos.mpr hp
  have h3 := Real.sq_sqrt hp.le
  field_simp
  rw [h3]

theorem sum_shellCoeff_div_sqrt {n : ℕ} (hn : 0 < mertensShellMass n) :
    ∑ p ∈ mertensShell n, shellCoeff n p / Real.sqrt (p : ℕ) = Real.sqrt (mertensShellMass n) := by
  simp_rw [shellCoeff_div_sqrt hn]
  rw [← Finset.mul_sum]
  change (Real.sqrt (mertensShellMass n))⁻¹ * mertensShellMass n = _
  have h1 := Real.sqrt_pos.mpr hn
  have h2 := Real.sq_sqrt hn.le
  field_simp
  rw [h2]

/-- **Cross-shell pairing.**  `⟪e_n, T e_m⟫ = ∑_{p ∈ S_n, q ∈ S_m} (m_n p)^{-1/2} (m_m q)^{-1/2} M(p,q)`. -/
theorem inner_mertensShellVec {T : ℓ²P →L[ℂ] ℓ²P} {M : Nat.Primes → Nat.Primes → ℂ}
    (hT : HasLpMatrix T M) (n m : ℕ) :
    inner ℂ (mertensShellVec n) (T (mertensShellVec m)) =
      ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell m,
        ((shellCoeff n p * shellCoeff m q : ℝ) : ℂ) * M p q := by
  rw [mertensShellVec, sum_inner]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [inner_smul_left, Complex.conj_ofReal, ← coord_eq_inner, mertensShellVec,
    coord_apply_sum hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast; ring

theorem norm_mertensShellVec {n : ℕ} (hn : 0 < mertensShellMass n) : ‖mertensShellVec n‖ = 1 := by
  have hid : HasLpMatrix (ContinuousLinearMap.id ℂ ℓ²P)
      fun p q => (if p = q then (1 : ℂ) else 0) := fun p q => by
    rw [ContinuousLinearMap.id_apply, coord_eq_inner, inner_lpBasisVec_lpBasisVec]
  have h := inner_mertensShellVec hid n n
  rw [ContinuousLinearMap.id_apply] at h
  have hsum : ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell n,
      ((shellCoeff n p * shellCoeff n q : ℝ) : ℂ) * (if p = q then (1 : ℂ) else 0) =
      ((∑ p ∈ mertensShell n, shellCoeff n p ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hp]
    ring
  have hval : ∑ p ∈ mertensShell n, shellCoeff n p ^ 2 = 1 := by
    simp_rw [shellCoeff_sq hn]
    have : ∑ p ∈ mertensShell n, 1 / (mertensShellMass n * ((p : ℕ) : ℝ)) =
        (mertensShellMass n)⁻¹ * mertensShellMass n := by
      rw [mertensShellMass, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [one_div, mul_inv, one_div]
    rw [this, inv_mul_cancel₀ hn.ne']
  rw [hsum, hval] at h
  have h2 : ‖mertensShellVec n‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, h]; simp
  nlinarith [norm_nonneg (mertensShellVec n), sq_nonneg (‖mertensShellVec n‖ - 1)]

theorem inner_mertensShellVec_eq_zero {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (mertensShellVec m) (mertensShellVec n) = 0 := by
  have hid : HasLpMatrix (ContinuousLinearMap.id ℂ ℓ²P)
      fun p q => (if p = q then (1 : ℂ) else 0) := fun p q => by
    rw [ContinuousLinearMap.id_apply, coord_eq_inner, inner_lpBasisVec_lpBasisVec]
  have h := inner_mertensShellVec hid m n
  rw [ContinuousLinearMap.id_apply] at h
  rw [h]
  refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
  have hpq : p ≠ q := fun e => by
    subst e
    exact Finset.disjoint_left.mp (disjoint_mertensShell hmn) hp hq
  rw [if_neg hpq, mul_zero]

/-- Late shells have mass at least `1/2`. -/
theorem exists_mertensShellMass_gt : ∃ N : ℕ, ∀ n ≥ N, 1 / 2 < mertensShellMass n :=
  eventually_atTop.mp (tendsto_mertensShellMass.eventually (lt_mem_nhds (by norm_num)))

/-- The late shell vectors form an orthonormal family. -/
theorem orthonormal_mertensShellVec_shift {N : ℕ} (hN : ∀ n ≥ N, 1 / 2 < mertensShellMass n)
    (k : ℕ) : Orthonormal ℂ fun n => mertensShellVec (N + n + k) := by
  rw [orthonormal_iff_ite]
  intro i j
  split_ifs with h
  · subst h
    rw [inner_self_eq_norm_sq_to_K, norm_mertensShellVec (by linarith [hN (N + i + k) (by omega)])]
    norm_num
  · exact inner_mertensShellVec_eq_zero (by omega)

/-- **Sign pairing.**  If `M(p,q) ≤ -κ/(√p √q)` on `S_n × S_{n+2}`, then
`Re ⟪e_n, T e_{n+2}⟫ ≤ -κ √(m_n m_{n+2})`. -/
theorem re_inner_mertensShellVec_le {T : ℓ²P →L[ℂ] ℓ²P} {M : Nat.Primes → Nat.Primes → ℝ}
    (hT : HasLpMatrix T fun p q => (M p q : ℂ)) {n : ℕ} {κ : ℝ}
    (hM : ∀ p ∈ mertensShell n, ∀ q ∈ mertensShell (n + 2),
      M p q ≤ -(κ / (Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ))))
    (hn : 0 < mertensShellMass n) (hn2 : 0 < mertensShellMass (n + 2)) :
    (inner ℂ (mertensShellVec n) (T (mertensShellVec (n + 2)))).re ≤
      -(κ * Real.sqrt (mertensShellMass n * mertensShellMass (n + 2))) := by
  rw [inner_mertensShellVec hT]
  have hre : (∑ p ∈ mertensShell n, ∑ q ∈ mertensShell (n + 2),
      ((shellCoeff n p * shellCoeff (n + 2) q : ℝ) : ℂ) * (M p q : ℂ)).re =
      ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell (n + 2),
        shellCoeff n p * shellCoeff (n + 2) q * M p q := by
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  calc ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell (n + 2),
        shellCoeff n p * shellCoeff (n + 2) q * M p q
      ≤ ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell (n + 2), shellCoeff n p *
          shellCoeff (n + 2) q * -(κ / (Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ))) := by
        refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
        exact mul_le_mul_of_nonneg_left (hM p hp q hq)
          (mul_nonneg (shellCoeff_nonneg _ _) (shellCoeff_nonneg _ _))
    _ = -(κ * ((∑ p ∈ mertensShell n, shellCoeff n p / Real.sqrt (p : ℕ)) *
          ∑ q ∈ mertensShell (n + 2), shellCoeff (n + 2) q / Real.sqrt (q : ℕ))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = -(κ * Real.sqrt (mertensShellMass n * mertensShellMass (n + 2))) := by
        rw [sum_shellCoeff_div_sqrt hn, sum_shellCoeff_div_sqrt hn2,
          Real.sqrt_mul hn.le]

/-! ### Clock gaps across shells -/

theorem mertensPrimeClock_eq (p : Nat.Primes) :
    mertensPrimeClock p = Real.log (Real.log ((p : ℕ) : ℝ)) := rfl

theorem clock_gap_of_shell {n : ℕ} {p q : Nat.Primes} (hp : p ∈ mertensShell n)
    (hq : q ∈ mertensShell (n + 2)) :
    1 < mertensPrimeClock q - mertensPrimeClock p ∧ mertensPrimeClock q - mertensPrimeClock p < 3 := by
  rw [mem_mertensShell] at hp hq
  rw [mertensPrimeClock_eq, mertensPrimeClock_eq]
  push_cast at hq
  constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]

/-- `u h(u) ≥ h(3)` for `1 ≤ u ≤ 3`. -/
theorem sechSqHalf_three_le_mul {u : ℝ} (h1 : 1 ≤ u) (h3 : u ≤ 3) :
    sechSqHalf 3 ≤ u * sechSqHalf u := by
  have hh : sechSqHalf 3 ≤ sechSqHalf u := sechSqHalf_le_of_le (by linarith) h3
  have := sechSqHalf_pos u
  nlinarith

theorem sechSqHalf_three_pos : 0 < sechSqHalf 3 := sechSqHalf_pos 3

/-! ### The Mertens-clock commutator -/

/-- **`C` has essential norm at least `h(3)`.**  In particular it is not compact. -/
theorem sechSqHalf_three_le_essentialNorm_poissonPrimeCommOp :
    sechSqHalf 3 ≤ essentialNorm poissonPrimeCommOp := by
  obtain ⟨N, hN⟩ := exists_mertensShellMass_gt
  have hmass : ∀ n ≥ N, 0 < mertensShellMass n := fun n hn => by linarith [hN n hn]
  have hT : HasLpMatrix poissonPrimeCommOp fun p q =>
      (((mertensPrimeClock p - mertensPrimeClock q) * stcPrimePoissonKernel p q : ℝ) : ℂ) :=
    hasLpMatrix_poissonPrimeCommOp.congr fun p q => by push_cast; ring
  have hsign : ∀ n, ∀ p ∈ mertensShell n, ∀ q ∈ mertensShell (n + 2),
      (mertensPrimeClock p - mertensPrimeClock q) * stcPrimePoissonKernel p q ≤
        -(sechSqHalf 3 / (Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ))) := by
    intro n p hp q hq
    obtain ⟨h1, h3⟩ := clock_gap_of_shell hp hq
    have hpq : (0 : ℝ) < Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ) := by
      have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
      have : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.pos
      positivity
    rw [stcPrimePoissonKernel_eq_sechSqHalf, ← neg_sub (mertensPrimeClock q), sechSqHalf_neg,
      mul_div_assoc', neg_mul, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (sechSqHalf_three_le_mul h1.le h3.le) hpq.le
  set f : ℕ → ℓ²P := fun n => mertensShellVec (N + n + 0)
  set g : ℕ → ℓ²P := fun n => mertensShellVec (N + n + 2)
  have hf : ∀ n, ‖f n‖ ≤ 1 := fun n => (norm_mertensShellVec (hmass _ (by omega))).le
  have hg : ∀ n, ‖g n‖ ≤ 1 := fun n => (norm_mertensShellVec (hmass _ (by omega))).le
  have hgw := Orthonormal.weakly_tendsto_zero (orthonormal_mertensShellVec_shift hN 2)
  refine le_essentialNorm_of_pairing hf hg hgw (b := fun n => sechSqHalf 3 *
    Real.sqrt (mertensShellMass (N + n) * mertensShellMass (N + n + 2))) ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    have h := re_inner_mertensShellVec_le hT (hsign (N + n)) (hmass _ (by omega))
      (hmass _ (by omega))
    have hre := (neg_le_abs _).trans (Complex.abs_re_le_norm (inner ℂ (mertensShellVec (N + n))
      (poissonPrimeCommOp (mertensShellVec (N + n + 2)))))
    simp only [f, g, add_zero]
    linarith
  · have hm := tendsto_mertensShellMass
    have h1 : Tendsto (fun n => mertensShellMass (N + n)) atTop (𝓝 1) :=
      hm.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩)
    have h2 : Tendsto (fun n => mertensShellMass (N + n + 2)) atTop (𝓝 1) :=
      hm.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩)
    have := ((h1.mul h2).sqrt).const_mul (sechSqHalf 3)
    simpa using this

theorem not_isCompactOperator_poissonPrimeCommOp : ¬ IsCompactOperator poissonPrimeCommOp :=
  fun h => by
    have h0 := essentialNorm_eq_zero_of_isCompactOperator h
    have := sechSqHalf_three_le_essentialNorm_poissonPrimeCommOp
    rw [h0] at this
    linarith [sechSqHalf_three_pos]

/-- **The Mertens clock is unbounded:** no bounded operator has the diagonal matrix `x_p`. -/
theorem not_exists_hasLpMatrix_mertensClock :
    ¬ ∃ T : ℓ²P →L[ℂ] ℓ²P,
      HasLpMatrix T fun p q => if p = q then (mertensPrimeClock p : ℂ) else 0 := by
  rintro ⟨T, hT⟩
  have hbound : ∀ n, mertensPrimeClock (nthPrime n) ≤ ‖T‖ := by
    intro n
    have h1 := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (T (lpBasisVec (nthPrime n)))
      (nthPrime n)
    rw [hT] at h1
    simp only [if_true, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 : ‖T (lpBasisVec (nthPrime n))‖ ≤ ‖T‖ := by
      refine (T.le_opNorm _).trans ?_
      rw [lpBasisVec, lp.norm_single (by norm_num), norm_one, mul_one]
    exact (le_abs_self _).trans (h1.trans h2)
  have hlim : Tendsto (fun n => mertensPrimeClock (nthPrime n)) atTop atTop := by
    have hp : Tendsto (fun n => ((nthPrime n : ℕ) : ℝ)) atTop atTop := by
      have hle : ∀ n : ℕ, (n : ℝ) ≤ ((nthPrime n : ℕ) : ℝ) := fun n => by
        exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOf_prime).id_le n
      exact tendsto_atTop_mono hle tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hp)
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_atTop ‖T‖)).exists
  exact absurd (hbound n) (not_le.mpr hn)

/-- **The core commutator.**  For a finitely supported `f = ∑ c_q δ_q`,
`x_p (K f)_p = (C f)_p + (K X f)_p`: the vector `K f` lies in the domain of the Mertens clock and
`X K f - K X f = C f`. -/
theorem mertensClock_mul_poissonPrimeOp_core (s : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (p : Nat.Primes) :
    (mertensPrimeClock p : ℂ) * (poissonPrimeOp (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) p =
      (poissonPrimeCommOp (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) p +
        (poissonPrimeOp (∑ q ∈ s, ((mertensPrimeClock q : ℂ) * c q) • lpBasisVec q) :
          Nat.Primes → ℂ) p := by
  rw [coord_apply_sum hasLpMatrix_poissonPrimeOp, coord_apply_sum hasLpMatrix_poissonPrimeCommOp,
    coord_apply_sum hasLpMatrix_poissonPrimeOp, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

theorem memℓp_mertensClock_mul_poissonPrimeOp_core (s : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Memℓp (fun p => (mertensPrimeClock p : ℂ) *
      (poissonPrimeOp (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) p) 2 := by
  have h := (lp.memℓp (poissonPrimeCommOp (∑ q ∈ s, c q • lpBasisVec q))).add
    (lp.memℓp (poissonPrimeOp (∑ q ∈ s, ((mertensPrimeClock q : ℂ) * c q) • lpBasisVec q)))
  have e : (fun p => (mertensPrimeClock p : ℂ) *
      (poissonPrimeOp (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) p) =
      (poissonPrimeCommOp (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) +
        (poissonPrimeOp (∑ q ∈ s, ((mertensPrimeClock q : ℂ) * c q) • lpBasisVec q) :
          Nat.Primes → ℂ) := funext fun p => mertensClock_mul_poissonPrimeOp_core s c p
  rw [e]
  exact h

/-! ### Physical clock powers -/

theorem stcClock_ge_log_two (p : Nat.Primes) : Real.log 2 ≤ stcClock p :=
  Real.log_le_log (by norm_num) (by exact_mod_cast p.prop.two_le)

theorem stcClock_rpow_eq_exp (p : Nat.Primes) (β : ℝ) :
    stcClock p ^ β = Real.exp (β * mertensPrimeClock p) := by
  rw [Real.rpow_def_of_pos (stcClock_pos' p), mertensPrimeClock, mul_comm]

theorem stcPrimePoissonKernel_nonneg (p q : Nat.Primes) : 0 ≤ stcPrimePoissonKernel p q := by
  have := stcClock_pos' p
  have := stcClock_pos' q
  unfold stcPrimePoissonKernel
  positivity

/-- `K(p,q) ≤ 4 t_q / (√p √q t_p)`. -/
theorem stcPrimePoissonKernel_le (p q : Nat.Primes) :
    stcPrimePoissonKernel p q ≤
      4 * stcClock q / (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) * stcClock p) := by
  have hp := stcClock_pos' p
  have hq := stcClock_pos' q
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast p.prop.pos)
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast q.prop.pos)
  unfold stcPrimePoissonKernel
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : stcClock p ^ 2 ≤ (stcClock p + stcClock q) ^ 2 := by nlinarith
  have h1 : 0 < Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤
    4 * stcClock q * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)))]

/-- `K(p,q) ≥ c_q / (√p t_p)` with `c_q = 4 t_q / (√q (1 + t_q / log 2)²)`. -/
theorem stcPrimePoissonKernel_ge (p q : Nat.Primes) :
    4 * stcClock q / (Real.sqrt (q : ℝ) * (1 + stcClock q / Real.log 2) ^ 2) /
        (Real.sqrt (p : ℝ) * stcClock p) ≤ stcPrimePoissonKernel p q := by
  have hp := stcClock_pos' p
  have hq := stcClock_pos' q
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpl := stcClock_ge_log_two p
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast p.prop.pos)
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast q.prop.pos)
  have hsum : stcClock p + stcClock q ≤ stcClock p * (1 + stcClock q / Real.log 2) := by
    have : stcClock q ≤ stcClock p * (stcClock q / Real.log 2) := by
      rw [mul_div_assoc', le_div_iff₀ hl2]; nlinarith
    nlinarith
  unfold stcPrimePoissonKernel
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq2 : (stcClock p + stcClock q) ^ 2 ≤ (stcClock p * (1 + stcClock q / Real.log 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum 2
  have hA : 0 ≤ 4 * stcClock q * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq2 hA]

/-- The physical clock multiplier `T^β`, `β ≤ 0`, bounded by `(log 2)^β`. -/
def physicalClockPowOp {β : ℝ} (hβ : β ≤ 0) : ℓ²P →L[ℂ] ℓ²P :=
  LpDiagonal.lpDiag (fun p => ((stcClock p ^ β : ℝ) : ℂ)) (Real.log 2 ^ β)
    (Real.rpow_nonneg (Real.log_pos (by norm_num)).le _) fun p => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (stcClock_pos' p).le _)]
      exact Real.rpow_le_rpow_of_nonpos (Real.log_pos (by norm_num)) (stcClock_ge_log_two p) hβ

theorem hasLpMatrix_physicalClockPowOp {β : ℝ} (hβ : β ≤ 0) :
    HasLpMatrix (physicalClockPowOp hβ)
      fun p q => if p = q then ((stcClock p ^ β : ℝ) : ℂ) else 0 := by
  classical
  intro p q
  show _ = if p = q then ((stcClock p ^ β : ℝ) : ℂ) else 0
  rw [physicalClockPowOp, lpBasisVec, LpDiagonal.lpDiag_single, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, smul_eq_mul]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]

theorem tendsto_stcClock_cofinite : Tendsto stcClock cofinite atTop := by
  have h1 : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]; exact Subtype.val_injective.tendsto_cofinite
  exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp h1)

/-- **Negative powers.**  For `β < 0` the multiplier `T^β` is compact, hence so is `[T^β, K]`. -/
theorem isCompactOperator_physicalClockPowOp {β : ℝ} (hβ : β < 0) :
    IsCompactOperator (physicalClockPowOp hβ.le) := by
  refine LpDiagonal.isCompactOperator_lpDiag _ _ _ _ ?_
  have h := (tendsto_rpow_neg_atTop (y := -β) (by linarith)).comp tendsto_stcClock_cofinite
  refine h.congr fun p => ?_
  simp only [Function.comp_apply, neg_neg]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (stcClock_pos' p).le _)]

theorem isCompactOperator_physicalClockPow_commutator {β : ℝ} (hβ : β < 0) :
    IsCompactOperator (physicalClockPowOp hβ.le ∘L poissonPrimeOp -
      poissonPrimeOp ∘L physicalClockPowOp hβ.le) := by
  have hD := isCompactOperator_physicalClockPowOp hβ
  exact (hD.comp_clm poissonPrimeOp).sub (hD.clm_comp poissonPrimeOp)

/-- **The zero power.**  The commutator matrix vanishes at `β = 0` and its `β`-derivative there is the
matrix of `C`. -/
theorem physicalClockPow_commutator_zero (p q : Nat.Primes) :
    (stcClock p ^ (0 : ℝ) - stcClock q ^ (0 : ℝ)) * stcPrimePoissonKernel p q = 0 := by
  simp

theorem hasDerivAt_physicalClockPow_commutator (p q : Nat.Primes) :
    HasDerivAt (fun β : ℝ => (stcClock p ^ β - stcClock q ^ β) * stcPrimePoissonKernel p q)
      ((mertensPrimeClock p - mertensPrimeClock q) * stcPrimePoissonKernel p q) 0 := by
  have hp := (Real.hasStrictDerivAt_const_rpow (stcClock_pos' p) 0).hasDerivAt
  have hq := (Real.hasStrictDerivAt_const_rpow (stcClock_pos' q) 0).hasDerivAt
  have h := (hp.sub hq).mul_const (stcPrimePoissonKernel p q)
  refine h.congr_deriv ?_
  simp [mertensPrimeClock]

/-- **Subcritical powers admit every column.**  For `β < 1`, `∑_p (t_p^β K(p,q))² < ∞`. -/
theorem summable_physicalClockPow_column {β : ℝ} (hβ : β < 1) (q : Nat.Primes) :
    Summable fun p => (stcClock p ^ β * stcPrimePoissonKernel p q) ^ 2 := by
  have hs : 0 < 2 - 2 * β := by linarith
  set C : ℝ := 16 * stcClock q ^ 2 / (q : ℝ)
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_)
    ((Sieve.summable_primes_one_div_mul_log_rpow hs).mul_left C)
  have ht := stcClock_pos' p
  have hq := stcClock_pos' q
  have hpr : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hqr : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.pos
  have hK0 := stcPrimePoissonKernel_nonneg p q
  have hKle := stcPrimePoissonKernel_le p q
  have hb : 0 ≤ stcClock p ^ β := Real.rpow_nonneg ht.le _
  have hsq := pow_le_pow_left₀ (mul_nonneg hb hK0) (mul_le_mul_of_nonneg_left hKle hb) 2
  refine hsq.trans (le_of_eq ?_)
  have hsp := Real.sq_sqrt hpr.le
  have hsq' := Real.sq_sqrt hqr.le
  have hrp : stcClock p ^ (2 * (1 - β)) * (stcClock p ^ β) ^ 2 = stcClock p ^ 2 := by
    rw [← Real.rpow_natCast (stcClock p ^ β) 2, ← Real.rpow_mul ht.le, ← Real.rpow_add ht,
      show 2 * (1 - β) + β * ((2 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hlogp : Real.log ((p : ℕ) : ℝ) = stcClock p := rfl
  rw [hlogp]
  have hrpos : 0 < stcClock p ^ (2 - 2 * β) := Real.rpow_pos_of_pos ht _
  simp only [C]
  have hsp0 : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpr).ne'
  have hsq0 : Real.sqrt (q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hqr).ne'
  rw [show 2 - 2 * β = 2 * (1 - β) by ring]
  field_simp
  linear_combination (4 ^ 2 * ((q : ℕ) : ℝ) * ((p : ℕ) : ℝ)) * hrp -
    (16 * stcClock p ^ 2 * Real.sqrt ((q : ℕ) : ℝ) ^ 2) * hsp -
    (16 * stcClock p ^ 2 * ((p : ℕ) : ℝ)) * hsq'

/-- **Supercritical powers admit no column.**  For `β ≥ 1`, no column `K δ_q` lies in the domain
of `T^β`. -/
theorem not_summable_physicalClockPow_column {β : ℝ} (hβ : 1 ≤ β) (q : Nat.Primes) :
    ¬ Summable fun p => (stcClock p ^ β * stcPrimePoissonKernel p q) ^ 2 := by
  intro hsum
  apply stcPrimePoissonKernel_physical_column_not_summable q
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 2 ^ (β - 1)
  have hc : 0 < c := Real.rpow_pos_of_pos hl2 _
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_)
    (hsum.mul_left (c ^ 2)⁻¹)
  have ht := stcClock_pos' p
  have hK0 := stcPrimePoissonKernel_nonneg p q
  have hpow : c * stcClock p ≤ stcClock p ^ β := by
    have h1 : c ≤ stcClock p ^ (β - 1) :=
      Real.rpow_le_rpow hl2.le (stcClock_ge_log_two p) (by linarith)
    calc c * stcClock p ≤ stcClock p ^ (β - 1) * stcClock p :=
          mul_le_mul_of_nonneg_right h1 ht.le
      _ = stcClock p ^ β := by
          rw [← Real.rpow_add_one ht.ne']; ring_nf
  have h2 : c * (stcClock p * stcPrimePoissonKernel p q) ≤
      stcClock p ^ β * stcPrimePoissonKernel p q := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hpow hK0
  have h3 := pow_le_pow_left₀ (by positivity) h2 2
  rw [mul_pow] at h3
  rw [le_inv_mul_iff₀ (by positivity)]
  exact h3

/-- **Positive powers have no bounded commutator.**  For `β > 0` the commutator matrix
`(t_p^β - t_q^β) K(p,q)` is the matrix of no bounded operator: on the shell pairs its entries are at
most `-e^{β(n+1)}(e^β - 1) h(3) / √(pq)`. -/
theorem not_exists_hasLpMatrix_physicalClockPow_commutator {β : ℝ} (hβ : 0 < β) :
    ¬ ∃ B : ℓ²P →L[ℂ] ℓ²P, HasLpMatrix B fun p q =>
      (((stcClock p ^ β - stcClock q ^ β) * stcPrimePoissonKernel p q : ℝ) : ℂ) := by
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := exists_mertensShellMass_gt
  set d : ℕ → ℝ := fun n => Real.exp (β * (n + 1)) * (Real.exp β - 1) * sechSqHalf 3
  have hsign : ∀ n, ∀ p ∈ mertensShell n, ∀ q ∈ mertensShell (n + 2),
      (stcClock p ^ β - stcClock q ^ β) * stcPrimePoissonKernel p q ≤
        -(d n / (Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ))) := by
    intro n p hp q hq
    obtain ⟨h1, h3⟩ := clock_gap_of_shell hp hq
    have hpm := (mem_mertensShell.mp hp)
    have hqm := (mem_mertensShell.mp hq)
    rw [← mertensPrimeClock_eq] at hpm hqm
    push_cast at hqm
    have hpq : (0 : ℝ) < Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ) := by
      have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
      have : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.pos
      positivity
    have hep : Real.exp (β * mertensPrimeClock p) ≤ Real.exp (β * (n + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpm.2.le hβ.le)
    have heq : Real.exp (β * (n + 2)) ≤ Real.exp (β * mertensPrimeClock q) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hqm.1 hβ.le)
    have hgap : Real.exp (β * (n + 2)) = Real.exp (β * (n + 1)) * Real.exp β := by
      rw [← Real.exp_add]; ring_nf
    have hdiff : Real.exp (β * mertensPrimeClock p) - Real.exp (β * mertensPrimeClock q) ≤
        -(Real.exp (β * (n + 1)) * (Real.exp β - 1)) := by nlinarith
    have hh : sechSqHalf 3 ≤ sechSqHalf (mertensPrimeClock p - mertensPrimeClock q) := by
      rw [← neg_sub, sechSqHalf_neg]; exact sechSqHalf_le_of_le (by linarith) h3.le
    have hd0 : 0 ≤ Real.exp (β * (n + 1)) * (Real.exp β - 1) := by
      have : 1 ≤ Real.exp β := Real.one_le_exp hβ.le
      positivity
    rw [stcClock_rpow_eq_exp, stcClock_rpow_eq_exp, stcPrimePoissonKernel_eq_sechSqHalf,
      mul_div_assoc', ← neg_div]
    refine div_le_div_of_nonneg_right ?_ hpq.le
    simp only [d]
    have hpos := sechSqHalf_pos (mertensPrimeClock p - mertensPrimeClock q)
    nlinarith [mul_le_mul_of_nonneg_left hh hd0]
  have hbound : ∀ n ≥ N, d n * (1 / 2) ≤ ‖B‖ := by
    intro n hn
    have hmn : 1 / 2 < mertensShellMass n := hN n hn
    have hmn2 : 1 / 2 < mertensShellMass (n + 2) := hN (n + 2) (by omega)
    have h := re_inner_mertensShellVec_le hB (hsign n) (by linarith) (by linarith)
    have hre := (neg_le_abs _).trans (Complex.abs_re_le_norm (inner ℂ (mertensShellVec n)
      (B (mertensShellVec (n + 2)))))
    have hinner : ‖inner ℂ (mertensShellVec n) (B (mertensShellVec (n + 2)))‖ ≤ ‖B‖ := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [norm_mertensShellVec (by linarith), one_mul]
      refine (B.le_opNorm _).trans ?_
      rw [norm_mertensShellVec (by linarith), mul_one]
    have hsqrt : 1 / 2 ≤ Real.sqrt (mertensShellMass n * mertensShellMass (n + 2)) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith
    have hd0 : 0 ≤ d n := by
      simp only [d]
      have : 1 ≤ Real.exp β := Real.one_le_exp hβ.le
      have := sechSqHalf_pos 3
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hd0]
  have hlim : Tendsto d atTop atTop := by
    have hc : 0 < (Real.exp β - 1) * sechSqHalf 3 := by
      have : 1 < Real.exp β := Real.one_lt_exp_iff.mpr hβ
      have := sechSqHalf_pos 3
      nlinarith
    have he : Tendsto (fun n : ℕ => Real.exp (β * (n + 1))) atTop atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      refine Tendsto.const_mul_atTop hβ ?_
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    refine (he.atTop_mul_const hc).congr fun n => ?_
    simp only [d]; ring
  obtain ⟨n, hn⟩ := ((hlim.eventually (eventually_gt_atTop (2 * ‖B‖))).and
    (eventually_ge_atTop N)).exists
  have := hbound n hn.2
  linarith [hn.1]

/-! ### Reflected kernels -/

/-- **Reflected columns.**  If `|F(y)| ≥ (e^{|y|} - 1)/2` (for instance `F = cosh` or `F = sinh`)
and `g ≠ 0`, then no column of `K(p,q) F(g(t_p + t_q)/2)` is square summable. -/
theorem not_summable_reflected_column {g : ℝ} (hg : g ≠ 0) (q : Nat.Primes) {F : ℝ → ℝ}
    (hF : ∀ y, (Real.exp |y| - 1) / 2 ≤ |F y|) :
    ¬ Summable fun p => (stcPrimePoissonKernel p q * F (g * (stcClock p + stcClock q) / 2)) ^ 2 := by
  intro hsum
  apply Nat.Primes.not_summable_one_div
  set cq : ℝ := 4 * stcClock q / (Real.sqrt (q : ℝ) * (1 + stcClock q / Real.log 2) ^ 2)
  have hq := stcClock_pos' q
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcq : 0 < cq := by
    have : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast q.prop.pos)
    positivity
  set a : ℝ := |g| / 2
  have ha : 0 < a := by have := abs_pos.mpr hg; positivity
  set c : ℝ := (cq * a / 2) ^ 2
  have hc : 0 < c := by positivity
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hsum.mul_left c⁻¹)
  have ht := stcClock_pos' p
  have hpr : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpr
  have hK := stcPrimePoissonKernel_ge p q
  have hFy : a * stcClock p / 2 ≤ |F (g * (stcClock p + stcClock q) / 2)| := by
    refine le_trans ?_ (hF _)
    have habs : a * stcClock p ≤ |g * (stcClock p + stcClock q) / 2| := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < stcClock p + stcClock q),
        abs_two]
      simp only [a]
      have := abs_nonneg g
      nlinarith
    have hexp := Real.add_one_le_exp |g * (stcClock p + stcClock q) / 2|
    linarith
  have hprod : cq * a / 2 / Real.sqrt (p : ℝ) ≤
      |stcPrimePoissonKernel p q * F (g * (stcClock p + stcClock q) / 2)| := by
    rw [abs_mul, abs_of_nonneg (stcPrimePoissonKernel_nonneg p q)]
    calc cq * a / 2 / Real.sqrt (p : ℝ) = cq / (Real.sqrt (p : ℝ) * stcClock p) *
          (a * stcClock p / 2) := by field_simp
      _ ≤ stcPrimePoissonKernel p q * |F (g * (stcClock p + stcClock q) / 2)| :=
          mul_le_mul hK hFy (by positivity) (stcPrimePoissonKernel_nonneg p q)
  have hsq := pow_le_pow_left₀ (by positivity) hprod 2
  rw [sq_abs] at hsq
  rw [le_inv_mul_iff₀ hc]
  calc c * (1 / ((p : ℕ) : ℝ)) = (cq * a / 2 / Real.sqrt (p : ℝ)) ^ 2 := by
        simp only [c, div_pow, Real.sq_sqrt hpr.le]
        ring
    _ ≤ _ := hsq

theorem half_exp_abs_sub_one_le_abs_cosh (y : ℝ) : (Real.exp |y| - 1) / 2 ≤ |Real.cosh y| := by
  rw [abs_of_pos (Real.cosh_pos y), Real.cosh_eq]
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-y)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos y]

theorem half_exp_abs_sub_one_le_abs_sinh (y : ℝ) : (Real.exp |y| - 1) / 2 ≤ |Real.sinh y| := by
  rw [Real.abs_sinh, Real.sinh_eq]
  have : Real.exp (-|y|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])
  linarith

/-- **The even reflected kernel admits no column for `g ≠ 0`.** -/
theorem not_summable_evenReflected_column {g : ℝ} (hg : g ≠ 0) (q : Nat.Primes) :
    ¬ Summable fun p =>
      (stcPrimePoissonKernel p q * Real.cosh (g * (stcClock p + stcClock q) / 2)) ^ 2 :=
  not_summable_reflected_column hg q half_exp_abs_sub_one_le_abs_cosh

/-- **The odd reflected kernel admits no column for `g ≠ 0`.** -/
theorem not_summable_oddReflected_column {g : ℝ} (hg : g ≠ 0) (q : Nat.Primes) :
    ¬ Summable fun p =>
      (stcPrimePoissonKernel p q * Real.sinh (g * (stcClock p + stcClock q) / 2)) ^ 2 :=
  not_summable_reflected_column hg q half_exp_abs_sub_one_le_abs_sinh

/-- At `g = 0` the even reflected kernel is `K` and the odd one vanishes. -/
theorem reflected_kernels_zero (p q : Nat.Primes) :
    stcPrimePoissonKernel p q * Real.cosh (0 * (stcClock p + stcClock q) / 2) =
        stcPrimePoissonKernel p q ∧
      stcPrimePoissonKernel p q * Real.sinh (0 * (stcClock p + stcClock q) / 2) = 0 := by
  simp

end

end RHTower
