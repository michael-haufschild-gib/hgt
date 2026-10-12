import GaloisForLFunctions.RHTower.JointAncestryLargePrimeAbscissa
import GaloisForLFunctions.RHTower.JointAncestryMaximalOffLineExclusion
import GaloisForLFunctions.RHTower.JointAncestryPrimeSumOneLine

/-!
# A maximal off-line zero is detected by large primes

The maximal off-line exclusion holds for positivity restricted to primes `p > X`: if a Xi zero
`ρ₀` maximizes `|Re ρ − ½|`, then `JasDressedPSDAbove X σ` fails for every `σ ≤ 1 + |Re ρ₀ − ½|`,
including the endpoint (`not_jasDressedPSDAbove_of_maximal_offLine_of_le`).  At the endpoint the
target exponent is `1`, where the twisted comparison comes from the exponent-one prime sums.  The proof is the Bernoulli test at the twisted
Kronecker point of `ρ₀` over the primes in `(X, N]`; it uses the primes only through
`S_α(X, N) = Σ_{X < p ≤ N} p^{−α} → ∞`, the comparison `S_{α'} = o(S_α)` for `α < α'`, and the loss of a
fixed proportion under twists `p^{iΔ}`, `Δ ≠ 0` — all inherited from the sums over `p ≤ N` because
the primes `p ≤ X` contribute a bounded amount.

The test is a rank-one product vector on squarefree characters, so for `σ ≥ ½` the exclusion
holds already for positivity of the Bernoulli product tests
(`not_jasProductPositiveAbove_of_maximal_offLine_of_le`).

With the chain case this gives the large-prime abscissa `½ + Θ` for every configuration under a
half-plane bound below `½` (`largePrime_abscissa_eq_of_xiZeroHalfPlaneBound`).
-/

open Complex Filter MeasureTheory
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The primes in `(X, N]`. -/
def jasPrimesBetween (X N : ℕ) : Finset Nat.Primes :=
  (jasPrimesUpTo N).filter fun p => X < (p : ℕ)

/-- `S_α(X, N) = Σ_{X < p ≤ N} p^{−α}`. -/
def jasPrimeRpowSumB (X : ℕ) (α : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ jasPrimesBetween X N, Real.exp (-α * Real.log p)

theorem jasPrimeRpowSumB_add (X : ℕ) (α : ℝ) {N : ℕ} (h : X ≤ N) :
    jasPrimeRpowSumB X α N + jasPrimeRpowSum α X = jasPrimeRpowSum α N := by
  unfold jasPrimeRpowSumB jasPrimeRpowSum jasPrimesBetween
  rw [← Finset.sum_filter_add_sum_filter_not (jasPrimesUpTo N) (fun p : Nat.Primes => X < (p : ℕ))]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, mem_jasPrimesUpTo, not_lt]
  omega

theorem tendsto_jasPrimeRpowSumB_atTop {X : ℕ} {α : ℝ} (hα : α ≤ 1) :
    Tendsto (jasPrimeRpowSumB X α) atTop atTop := by
  have h := (tendsto_jasPrimeRpowSum_atTop hα).atTop_add (tendsto_const_nhds (x := -jasPrimeRpowSum α X))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop X] with N hN
  have := jasPrimeRpowSumB_add X α hN
  linarith

theorem eventually_jasPrimeRpowSumB_le {X : ℕ} {α α' : ℝ} (hα : α ≤ 1) (hαα' : α < α') {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, jasPrimeRpowSumB X α' N ≤ ε * jasPrimeRpowSumB X α N := by
  filter_upwards [eventually_jasPrimeRpowSum_le hα hαα' (half_pos hε),
    (tendsto_jasPrimeRpowSumB_atTop (X := X) hα).eventually_ge_atTop (jasPrimeRpowSum α X),
    eventually_ge_atTop X] with N h1 h2 hN
  have e1 := jasPrimeRpowSumB_add X α hN
  have e2 := jasPrimeRpowSumB_add X α' hN
  have h0 := jasPrimeRpowSum_nonneg α' X
  nlinarith

theorem exists_twisted_jasPrimeRpowSumB_le {X : ℕ} {α Δ : ℝ} (h0 : 0 < α) (h1 : α ≤ 1)
    (hΔ : Δ ≠ 0) :
    ∃ κ : ℝ, κ < 1 ∧ ∀ᶠ N in atTop,
      ‖∑ p ∈ jasPrimesBetween X N, (Real.exp (-α * Real.log p) : ℂ) *
          cexp (((Δ * Real.log p : ℝ) : ℂ) * I)‖ ≤ κ * jasPrimeRpowSumB X α N := by
  obtain ⟨κ, hκ1, hev⟩ := exists_twisted_jasPrimeRpowSum_le_of_le_one h0 h1 hΔ
  have hκ' : (1 + max κ 0) / 2 < 1 := by have := max_lt hκ1 one_pos; linarith
  refine ⟨(1 + max κ 0) / 2, hκ', ?_⟩
  set C := jasPrimeRpowSum α X with hC
  have hC0 : 0 ≤ C := jasPrimeRpowSum_nonneg α X
  filter_upwards [hev, (tendsto_jasPrimeRpowSumB_atTop (X := X) h1).eventually_ge_atTop
    (2 * (1 + 1) * C / (1 - max κ 0)), eventually_ge_atTop X] with N hN hbig hXN
  have hsplit := jasPrimeRpowSumB_add X α hXN
  set f : Nat.Primes → ℂ := fun p => (Real.exp (-α * Real.log p) : ℂ) *
    cexp (((Δ * Real.log p : ℝ) : ℂ) * I) with hf
  have hnorm : ∀ p, ‖f p‖ = Real.exp (-α * Real.log p) := fun p => by
    rw [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hdec : ∑ p ∈ jasPrimesUpTo N, f p =
      ∑ p ∈ jasPrimesBetween X N, f p + ∑ p ∈ (jasPrimesUpTo N).filter (fun p : Nat.Primes => ¬ X < (p : ℕ)), f p := by
    unfold jasPrimesBetween; exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : ‖∑ p ∈ (jasPrimesUpTo N).filter (fun p : Nat.Primes => ¬ X < (p : ℕ)), f p‖ ≤ C := by
    refine (norm_sum_le _ _).trans ?_
    simp_rw [hnorm]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => (Real.exp_pos _).le
    rw [Finset.mem_filter, not_lt] at hp
    exact mem_jasPrimesUpTo.mpr hp.2
  have hmid : ‖∑ p ∈ jasPrimesBetween X N, f p‖ ≤ κ * jasPrimeRpowSum α N + C := by
    have heq : ∑ p ∈ jasPrimesBetween X N, f p = ∑ p ∈ jasPrimesUpTo N, f p -
        ∑ p ∈ (jasPrimesUpTo N).filter (fun p : Nat.Primes => ¬ X < (p : ℕ)), f p := by
      rw [hdec]; ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hκm : κ ≤ max κ 0 := le_max_left _ _
  have hm0 : 0 ≤ max κ 0 := le_max_right _ _
  have hS0 : 0 ≤ jasPrimeRpowSumB X α N := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hbig' : 4 * C ≤ (1 - max κ 0) * jasPrimeRpowSumB X α N := by
    rw [div_le_iff₀ (by linarith)] at hbig; linarith
  have : κ * jasPrimeRpowSum α N ≤ max κ 0 * jasPrimeRpowSum α N :=
    mul_le_mul_of_nonneg_right hκm (by linarith [jasPrimeRpowSum_nonneg α N])
  nlinarith

/-- **Monotonicity.**  A positive dressing stays positive under further dressing. -/
theorem JasDressedPSDOn.mono {S : Finset Nat.Primes} {σ' σ : ℝ} (h : JasDressedPSDOn S σ')
    (hle : σ' ≤ σ) : JasDressedPSDOn S σ := by
  intro ι t c n hinj hsupp
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact h ι t c n hinj hsupp
  set κ := σ - σ' with hκ
  have hκ0 : 0 < κ := sub_pos.mpr hlt
  set μ := primePoissonMeasure κ 0 hκ0 with hμ
  have hsplit : ∀ m : Nat.Primes →₀ ℤ, jasDressedLagAggregate σ m =
      jasDressedLagAggregate σ' m * ∫ x, infiniteTorusFourier m x ∂μ := by
    intro m
    rw [hμ, integral_infiniteTorusFourier_primePoissonMeasure_real, jasDressedLagAggregate,
      jasDressedLagAggregate, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  have hint : ∀ m : Nat.Primes →₀ ℤ, Integrable (fun x => infiniteTorusFourier m x) μ :=
    integrable_infiniteTorusFourier μ
  have hpt : ∀ x, ∑ i ∈ t, ∑ j ∈ t, (c i * infiniteTorusFourier (n i) x) *
      conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j) =
      ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) *
        (jasDressedLagAggregate σ' (n i - n j) * infiniteTorusFourier (n i - n j) x) := by
    intro x
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sub_eq_add_neg, infiniteTorusFourier_add, infiniteTorusFourier_neg, map_mul]
    ring
  have heq : ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ (n i - n j) =
      ∫ x, ∑ i ∈ t, ∑ j ∈ t, (c i * infiniteTorusFourier (n i) x) *
        conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j) ∂μ := by
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, integral_const_mul, hsplit]
      · intro j _; exact ((hint _).const_mul _).const_mul _
    · intro i _
      exact integrable_finsetSum _ fun j _ => ((hint _).const_mul _).const_mul _
  have hInt : Integrable (fun x => ∑ i ∈ t, ∑ j ∈ t, (c i * infiniteTorusFourier (n i) x) *
      conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j)) μ := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    have : Continuous fun x => (c i * infiniteTorusFourier (n i) x) *
        conj (c j * infiniteTorusFourier (n j) x) * jasDressedLagAggregate σ' (n i - n j) := by
      fun_prop
    exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre := integral_re hInt
  simp only [RCLike.re_to_complex] at hre
  rw [heq, ← hre]
  exact integral_nonneg fun x => h ι t (fun i => c i * infiniteTorusFourier (n i) x) n hinj hsupp

theorem JasDressedPSDAbove.mono {X : ℕ} {σ' σ : ℝ} (h : JasDressedPSDAbove X σ') (hle : σ' ≤ σ) :
    JasDressedPSDAbove X σ := fun S hS => (h S hS).mono hle

theorem eventually_jasHead_le_of_ltB {X : ℕ} {α α' g : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hαα' : α < α')
    (hg : 0 < g) {η : ℝ} (hη : 0 < η) {r₁ r₂ : Nat.Primes → ℝ}
    (hr₁ : ∀ p, r₁ p = Real.exp (-α * Real.log p)) (hr₂ : ∀ p, 0 ≤ r₂ p)
    (F : ℝ → Nat.Primes → ℂ) (hF : ∀ φ p, ‖F φ p‖ ≤ 2 * (1 + Real.exp (-α' * Real.log p))) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      g * jasPrimeRpowSumB X α N ≤ ∑ p ∈ jasPrimesBetween X N, (r₁ p - r₂ p) →
      Real.sin φ * ∑ p ∈ jasPrimesBetween X N, (r₁ p - r₂ p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesBetween X N, F φ p‖ ≤
        η * ‖∏ p ∈ jasPrimesBetween X N, jasTwistedValue (r₁ p) (r₂ p) φ‖ := by
  set T₀ := max 1 (max (64 * Real.pi ^ 2 / g ^ 2) (2 + 4 * |Real.log η|)) with hT₀
  filter_upwards [eventually_jasPrimeRpowSumB_le hα1 hαα' (ε := 1 / 8) (by norm_num),
    eventually_jasPrimeRpowSumB_le hα1 (show α < 2 * α by linarith) (ε := 1 / 2) (by norm_num),
    (tendsto_jasPrimeRpowSumB_atTop hα1).eventually_ge_atTop T₀] with N h1 h2 h3
  intro φ h0 hφ1 hT hsin
  set S := jasPrimeRpowSumB X α N with hS
  have hS1 : 1 ≤ S := (le_max_left _ _).trans h3
  have hS0 : 0 < S := by linarith
  have hSg : 64 * Real.pi ^ 2 / g ^ 2 ≤ S := ((le_max_left _ _).trans (le_max_right _ _)).trans h3
  have hSη : 2 + 4 * |Real.log η| ≤ S := ((le_max_right _ _).trans (le_max_right _ _)).trans h3
  have hc0 : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
  have hc1 := Real.cos_le_one φ
  have hr₁0 : ∀ p, 0 ≤ r₁ p := fun p => by rw [hr₁]; exact (Real.exp_pos _).le
  have hr₁1 : ∀ p, r₁ p ≤ 1 := fun p => by
    rw [hr₁, Real.exp_le_one_iff]; nlinarith [log_prime_pos p]
  have hcos := one_sub_cos_mul_le h0 hφ1 hg hS0 hT hsin
  have hcos1 : (1 - Real.cos φ) * S ≤ 1 := by
    refine hcos.trans ?_
    rw [div_le_one (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hSg
    linarith
  have hsumr₁ : ∑ p ∈ jasPrimesBetween X N, r₁ p = S := by
    rw [hS, jasPrimeRpowSumB]; exact Finset.sum_congr rfl fun p _ => hr₁ p
  have hsumsq : ∑ p ∈ jasPrimesBetween X N, r₁ p ^ 2 = jasPrimeRpowSumB X (2 * α) N := by
    rw [jasPrimeRpowSumB]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hr₁, sq, ← Real.exp_add]; congr 1; ring
  refine (norm_prod_le_exp_mul_norm_prod _ (F φ) (fun p => jasTwistedValue (r₁ p) (r₂ p) φ)
    (fun p => Real.exp (-α' * Real.log p))
    (fun p => r₁ p * Real.cos φ / 2) (fun p _ => by have := hr₁0 p; positivity)
    (fun p _ => ?_) (fun p _ => hF φ p)).trans ?_
  · have := two_add_mul_cos_le_norm_jasTwistedValue (r₁ p) (r₂ p) φ
    nlinarith [hr₂ p]
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hexp : ∑ p ∈ jasPrimesBetween X N, (Real.exp (-α' * Real.log p) - r₁ p * Real.cos φ / 2 +
        (r₁ p * Real.cos φ / 2) ^ 2) ≤ -S / 4 + 1 / 2 := by
      have hv2 : ∀ p, (r₁ p * Real.cos φ / 2) ^ 2 ≤ r₁ p ^ 2 / 4 := fun p =>
        sq_mul_div_two_le hc0 hc1
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have e1 : ∑ p ∈ jasPrimesBetween X N, Real.exp (-α' * Real.log p) = jasPrimeRpowSumB X α' N := rfl
      have e2 : ∑ p ∈ jasPrimesBetween X N, r₁ p * Real.cos φ / 2 = Real.cos φ * S / 2 := by
        rw [← hsumr₁, Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun p _ => by ring
      have e3 : ∑ p ∈ jasPrimesBetween X N, (r₁ p * Real.cos φ / 2) ^ 2 ≤ S / 8 := by
        calc _ ≤ ∑ p ∈ jasPrimesBetween X N, r₁ p ^ 2 / 4 := Finset.sum_le_sum fun p _ => hv2 p
          _ = jasPrimeRpowSumB X (2 * α) N / 4 := by rw [← Finset.sum_div, hsumsq]
          _ ≤ S / 8 := by linarith
      rw [e1, e2]
      nlinarith
    have hlog : -S / 4 + 1 / 2 ≤ Real.log η := by
      have := neg_abs_le (Real.log η)
      linarith
    calc Real.exp _ ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr (hexp.trans hlog)
      _ = η := Real.exp_log hη

/-- The exponent estimate behind the twisted head bound, for any finite prime set. -/
theorem twist_exponent_le {P : Finset Nat.Primes} {r₁ r₂ : Nat.Primes → ℝ} {φ Δ m κ ε S : ℝ}
    (hr₂0 : ∀ p, 0 ≤ r₂ p) (hr₂₁ : ∀ p, r₂ p ≤ r₁ p) (hm : 0 < m)
    (hc0 : 0 ≤ Real.cos φ) (hc1 : Real.cos φ ≤ 1)
    (hsumr₁ : ∑ p ∈ P, r₁ p = S) (hsumr₂ : ∑ p ∈ P, r₂ p ≤ ε * S)
    (hsumsq : ∑ p ∈ P, r₁ p ^ 2 ≤ ε * S)
    (hosc : ∑ p ∈ P, r₁ p * Real.cos (φ + Δ * Real.log p) ≤ κ * S)
    (hcos1 : (1 - Real.cos φ) * S ≤ 1) (hε : ε * (3 + 1 / m) = 1 - κ) :
    ∑ p ∈ P, (((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2 -
        r₁ p * Real.cos φ / 2 + (r₁ p * Real.cos φ / 2) ^ 2) ≤ -(1 - κ) * S / 4 + 1 / 2 := by
  have hu : ∀ p, ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2
      ≤ r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p / 2 + r₁ p ^ 2 / (4 * m) := by
    intro p
    have hc := Real.cos_le_one (φ + Δ * Real.log p)
    have h2 : r₂ p * Real.cos (φ + Δ * Real.log p) ≤ r₂ p := by nlinarith [hr₂0 p]
    have h3 : (r₁ p - r₂ p) ^ 2 ≤ r₁ p ^ 2 := by nlinarith [hr₂0 p, hr₂₁ p]
    have h4 : (r₁ p - r₂ p) ^ 2 / (2 * m) ≤ r₁ p ^ 2 / (2 * m) :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have h5 : r₁ p ^ 2 / (2 * m) / 2 = r₁ p ^ 2 / (4 * m) := by field_simp; ring
    calc ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2
        = r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p * Real.cos (φ + Δ * Real.log p) / 2 +
            (r₁ p - r₂ p) ^ 2 / (2 * m) / 2 := by ring
      _ ≤ r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p / 2 + r₁ p ^ 2 / (2 * m) / 2 := by
          linarith
      _ = _ := by rw [h5]
  have hv2 : ∀ p, (r₁ p * Real.cos φ / 2) ^ 2 ≤ r₁ p ^ 2 / 4 := fun p => sq_mul_div_two_le hc0 hc1
  have hU : ∑ p ∈ P, ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2
      ≤ κ * S / 2 + ε * S / 2 + ε * S / (4 * m) := by
    calc _ ≤ ∑ p ∈ P, (r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p / 2 + r₁ p ^ 2 / (4 * m)) :=
          Finset.sum_le_sum fun p _ => hu p
      _ = (∑ p ∈ P, r₁ p * Real.cos (φ + Δ * Real.log p)) / 2 + (∑ p ∈ P, r₂ p) / 2 +
            (∑ p ∈ P, r₁ p ^ 2) / (4 * m) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div,
            Finset.sum_div]
      _ ≤ κ * S / 2 + ε * S / 2 + ε * S / (4 * m) := by
          have := div_le_div_of_nonneg_right hsumsq (show (0 : ℝ) ≤ 4 * m by positivity)
          linarith
  have hV : ∑ p ∈ P, r₁ p * Real.cos φ / 2 = Real.cos φ * S / 2 := by
    rw [← hsumr₁, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hV2 : ∑ p ∈ P, (r₁ p * Real.cos φ / 2) ^ 2 ≤ ε * S / 4 := by
    calc _ ≤ ∑ p ∈ P, r₁ p ^ 2 / 4 := Finset.sum_le_sum fun p _ => hv2 p
      _ = (∑ p ∈ P, r₁ p ^ 2) / 4 := by rw [Finset.sum_div]
      _ ≤ ε * S / 4 := by linarith
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hV]
  have hεm : ε * S / 2 + ε * S / (4 * m) + ε * S / 4 = (1 - κ) * S / 4 := by
    have e : ε * S / 2 + ε * S / (4 * m) + ε * S / 4 = ε * (3 + 1 / m) * S / 4 := by
      field_simp; ring
    rw [e, hε]
  linarith only [hU, hV2, hεm, hcos1]

/-- Competitors at the same distance from the line and another height. -/

theorem eventually_jasHead_le_of_twistB {X : ℕ} {α α₂ Δ g m : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαα₂ : α < α₂) (hΔ : Δ ≠ 0) (hg : 0 < g) (hm : 0 < m) {η : ℝ} (hη : 0 < η)
    {r₁ r₂ : Nat.Primes → ℝ} (hr₁ : ∀ p, r₁ p = Real.exp (-α * Real.log p))
    (hr₂ : ∀ p, r₂ p = Real.exp (-α₂ * Real.log p)) (F : ℝ → Nat.Primes → ℂ)
    (hF : ∀ φ p, ‖F φ p‖ ≤ 2 + (r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) +
      (r₁ p - r₂ p) ^ 2 / (2 * m)) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      g * jasPrimeRpowSumB X α N ≤ ∑ p ∈ jasPrimesBetween X N, (r₁ p - r₂ p) →
      Real.sin φ * ∑ p ∈ jasPrimesBetween X N, (r₁ p - r₂ p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesBetween X N, F φ p‖ ≤
        η * ‖∏ p ∈ jasPrimesBetween X N, jasTwistedValue (r₁ p) (r₂ p) φ‖ := by
  obtain ⟨κ, hκ1, hκev⟩ := exists_twisted_jasPrimeRpowSumB_le hα0 hα1 hΔ
  set ε := (1 - κ) / (3 + 1 / m) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos (by linarith); positivity
  set T₀ := max 1 (max (64 * Real.pi ^ 2 / g ^ 2) ((2 + 4 * |Real.log η|) / (1 - κ))) with hT₀
  filter_upwards [hκev, eventually_jasPrimeRpowSumB_le hα1 hαα₂ hε0,
    eventually_jasPrimeRpowSumB_le hα1 (show α < 2 * α by linarith) hε0,
    (tendsto_jasPrimeRpowSumB_atTop hα1).eventually_ge_atTop T₀] with N hK h1 h2 h3
  intro φ h0 hφ1 hT hsin
  set S := jasPrimeRpowSumB X α N with hS
  have hS1 : 1 ≤ S := (le_max_left _ _).trans h3
  have hS0 : 0 < S := by linarith
  have hSg : 64 * Real.pi ^ 2 / g ^ 2 ≤ S := ((le_max_left _ _).trans (le_max_right _ _)).trans h3
  have hSη : (2 + 4 * |Real.log η|) / (1 - κ) ≤ S :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans h3
  have hc0 : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
  have hc1 := Real.cos_le_one φ
  have hr₁0 : ∀ p, 0 ≤ r₁ p := fun p => by rw [hr₁]; exact (Real.exp_pos _).le
  have hr₂0 : ∀ p, 0 ≤ r₂ p := fun p => by rw [hr₂]; exact (Real.exp_pos _).le
  have hr₂₁ : ∀ p, r₂ p ≤ r₁ p := fun p => by
    rw [hr₁, hr₂]; exact Real.exp_le_exp.mpr (by nlinarith [log_prime_pos p])
  have hcos := one_sub_cos_mul_le h0 hφ1 hg hS0 hT hsin
  have hcos1 : (1 - Real.cos φ) * S ≤ 1 := by
    refine hcos.trans ?_
    rw [div_le_one (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hSg
    linarith
  have hsumr₁ : ∑ p ∈ jasPrimesBetween X N, r₁ p = S := by
    rw [hS, jasPrimeRpowSumB]; exact Finset.sum_congr rfl fun p _ => hr₁ p
  have hsumr₂ : ∑ p ∈ jasPrimesBetween X N, r₂ p = jasPrimeRpowSumB X α₂ N := by
    rw [jasPrimeRpowSumB]; exact Finset.sum_congr rfl fun p _ => hr₂ p
  have hsumsq : ∑ p ∈ jasPrimesBetween X N, r₁ p ^ 2 = jasPrimeRpowSumB X (2 * α) N := by
    rw [jasPrimeRpowSumB]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hr₁, sq, ← Real.exp_add]; congr 1; ring
  -- the oscillating sum
  have hosc : ∑ p ∈ jasPrimesBetween X N, r₁ p * Real.cos (φ + Δ * Real.log p) ≤ κ * S := by
    have hterm : ∀ p : Nat.Primes, r₁ p * Real.cos (φ + Δ * Real.log p) =
        (cexp ((φ : ℂ) * I) * ((Real.exp (-α * Real.log p) : ℂ) *
          cexp (((Δ * Real.log p : ℝ) : ℂ) * I))).re := by
      intro p
      rw [mul_left_comm, ← Complex.exp_add, ← hr₁,
        show (φ : ℂ) * I + ((Δ * Real.log p : ℝ) : ℂ) * I = ((φ + Δ * Real.log p : ℝ) : ℂ) * I by
          push_cast; ring, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← Complex.re_sum, ← Finset.mul_sum]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hK
  refine (norm_prod_le_exp_mul_norm_prod _ (F φ) (fun p => jasTwistedValue (r₁ p) (r₂ p) φ)
    (fun p => ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2)
    (fun p => r₁ p * Real.cos φ / 2) (fun p _ => by have := hr₁0 p; positivity)
    (fun p _ => ?_) (fun p _ => by have := hF φ p; linarith)).trans ?_
  · have := two_add_mul_cos_le_norm_jasTwistedValue (r₁ p) (r₂ p) φ
    nlinarith [hr₂0 p]
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hε2 : jasPrimeRpowSumB X (2 * α) N ≤ ε * S := h2
    have hε1 : jasPrimeRpowSumB X α₂ N ≤ ε * S := h1
    have hexp := twist_exponent_le (P := jasPrimesBetween X N) hr₂0 hr₂₁ hm hc0 hc1
      hsumr₁ (hsumr₂.trans_le hε1) (hsumsq.trans_le hε2) hosc hcos1 (show ε * (3 + 1 / m) = 1 - κ by
        rw [hε]; field_simp)
    have hlog : -(1 - κ) * S / 4 + 1 / 2 ≤ Real.log η := by
      have hk : 0 < 1 - κ := by linarith
      rw [div_le_iff₀ hk] at hSη
      have := neg_abs_le (Real.log η)
      linarith
    calc Real.exp _ ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr (hexp.trans hlog)
      _ = η := Real.exp_log hη

/-! ## The dominant zero -/

theorem jasPrimeRpowSumB_dressed {X : ℕ} (ρ : ℂ) (c : ℝ) (N : ℕ) :
    jasPrimeRpowSumB X (ρ.re + c) N = ∑ p ∈ jasPrimesBetween X N, jasR1 (ρ + c) p :=
  Finset.sum_congr rfl fun p _ => (jasR1_dressed ρ c p).symm

theorem jasGap_mul_sum_leB {X : ℕ} {ρ : ℂ} (hβ : ρ.re < 1 / 2) (c : ℝ) (N : ℕ) :
    jasGap ρ * jasPrimeRpowSumB X (ρ.re + c) N ≤
      ∑ p ∈ jasPrimesBetween X N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) := by
  rw [jasPrimeRpowSumB_dressed, Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ => jasGap_mul_le hβ c p


/-- A competitor zero is eventually negligible at the twisted Kronecker points of `ρ`. -/
theorem eventually_jasCompetitor_leB {X : ℕ} {ρ q : ℂ} {c η : ℝ} (hβ0 : 0 < ρ.re) (hβ : ρ.re < 1 / 2)
    (hc0 : 0 ≤ c) (hα1 : ρ.re + c ≤ 1) (hη : 0 < η) (hq : |q.re - 1 / 2| ≤ 1 / 2 - ρ.re)
    (hqD : ¬ (q.im = ρ.im ∧ |q.re - 1 / 2| = 1 / 2 - ρ.re)) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      jasGap ρ * jasPrimeRpowSumB X (ρ.re + c) N ≤
        ∑ p ∈ jasPrimesBetween X N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) →
      Real.sin φ * ∑ p ∈ jasPrimesBetween X N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesBetween X N, jasDressedBernoulli q c p (jasTwistedPoint ρ φ p)‖ ≤
        η * ‖∏ p ∈ jasPrimesBetween X N,
          jasTwistedValue (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) φ‖ := by
  have hα0 : 0 < ρ.re + c := by linarith
  have hr₁ : ∀ p, jasR1 (ρ + c) p = Real.exp (-(ρ.re + c) * Real.log p) := jasR1_dressed ρ c
  have hR1 : ∀ p, 0 ≤ jasR1 (q + c) p := fun p => by rw [jasR1_dressed]; exact (Real.exp_pos _).le
  have hR2 : ∀ p, 0 ≤ jasR2 (q - c) p := fun p => by rw [jasR2_dressed]; exact (Real.exp_pos _).le
  have hr₂0 : ∀ p, 0 ≤ jasR2 (ρ - c) p := fun p => by
    rw [jasR2_dressed]; exact (Real.exp_pos _).le
  rcases lt_or_eq_of_le hq with hlt | heq
  · refine eventually_jasHead_le_of_ltB hα0 hα1 (α' := 1 / 2 - |q.re - 1 / 2| + c) (by linarith)
      (jasGap_pos hβ) hη hr₁ hr₂0 _ fun φ p => ?_
    rw [jasDressedBernoulli_twisted_general]
    refine (norm_jasTwistedValue_le_add (hR1 p) (hR2 p) _).trans ?_
    have := jasR1_add_jasR2_le_two_mul q c p
    linarith
  · have him : q.im ≠ ρ.im := fun h => hqD ⟨h, heq⟩
    have hr₂ : ∀ p, jasR2 (ρ - c) p = Real.exp (-(1 - ρ.re + c) * Real.log p) := jasR2_dressed ρ c
    refine eventually_jasHead_le_of_twistB hα0 hα1 (by linarith) (Δ := ρ.im - q.im)
      (sub_ne_zero.mpr (Ne.symm him)) (jasGap_pos hβ) (jasMargin_pos hα0) hη hr₁ hr₂ _
      fun φ p => ?_
    rw [jasDressedBernoulli_twisted_general]
    have hm := jasMargin_le (c := c) hβ.le hα0.le p
    have hr₁0 : 0 ≤ jasR1 (ρ + c) p := by rw [hr₁]; exact (Real.exp_pos _).le
    rcases (abs_eq (by linarith : (0 : ℝ) ≤ 1 / 2 - ρ.re)).mp heq with h | h
    · have e1 : jasR1 (q + c) p = jasR2 (ρ - c) p := by
        rw [jasR1_dressed, jasR2_dressed]; congr 2; linarith
      have e2 : jasR2 (q - c) p = jasR1 (ρ + c) p := by
        rw [jasR1_dressed, jasR2_dressed]; congr 2; linarith
      rw [e1, e2]
      have := norm_jasTwistedValue_le_cos (r₁ := jasR2 (ρ - c) p) (r₂ := jasR1 (ρ + c) p)
        (hr₂0 p) hr₁0 (jasMargin_pos hα0) (by linarith) (φ + (ρ.im - q.im) * Real.log p)
      rw [add_comm (jasR2 (ρ - c) p), show (jasR2 (ρ - c) p - jasR1 (ρ + c) p) ^ 2 =
        (jasR1 (ρ + c) p - jasR2 (ρ - c) p) ^ 2 by ring] at this
      exact this
    · have e1 : jasR1 (q + c) p = jasR1 (ρ + c) p := by
        rw [jasR1_dressed, jasR1_dressed]; congr 2; linarith
      have e2 : jasR2 (q - c) p = jasR2 (ρ - c) p := by
        rw [jasR2_dressed, jasR2_dressed]; congr 2; linarith
      rw [e1, e2]
      exact norm_jasTwistedValue_le_cos hr₁0 (hr₂0 p) (jasMargin_pos hα0) hm _

/-- The zeros outside a finite set are bounded by `∏ (2 + r₁ + r₂) ≤ 2 |G|` eventually. -/

theorem eventually_jasTail_leB {X : ℕ} {ρ : ℂ} {c : ℝ} (hβ : ρ.re < 1 / 2) (hα1 : ρ.re + c ≤ 1) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      Real.sin φ * ∑ p ∈ jasPrimesBetween X N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) ≤ 8 * Real.pi →
      ∏ p ∈ jasPrimesBetween X N, (2 + (jasR1 (ρ + c) p + jasR2 (ρ - c) p)) ≤
        2 * ‖∏ p ∈ jasPrimesBetween X N, jasTwistedValue (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) φ‖ := by
  have hg := jasGap_pos hβ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [(tendsto_jasPrimeRpowSumB_atTop hα1).eventually_ge_atTop
    (max 1 (64 * Real.pi ^ 2 / (jasGap ρ ^ 2 * Real.log 2)))] with N hN
  intro φ h0 h1 hsin
  have hS0 : 0 < jasPrimeRpowSumB X (ρ.re + c) N := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hN)
  have hc0' : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hcos := one_sub_cos_mul_le h0 h1 hg hS0 (jasGap_mul_sum_leB hβ c N) hsin
  have hr₁0 : ∀ p, 0 ≤ jasR1 (ρ + c) p := fun p => by rw [jasR1_dressed]; exact (Real.exp_pos _).le
  have hr₂0 : ∀ p, 0 ≤ jasR2 (ρ - c) p := fun p => by rw [jasR2_dressed]; exact (Real.exp_pos _).le
  refine (prod_two_add_le_exp_mul_norm_prod _ _ (fun p => jasR1 (ρ + c) p + jasR2 (ρ - c) p) hc0'
    (fun p _ => by linarith [hr₁0 p, hr₂0 p])
    (fun p _ => two_add_mul_cos_le_norm_jasTwistedValue _ _ _)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hsum : ∑ p ∈ jasPrimesBetween X N, (jasR1 (ρ + c) p + jasR2 (ρ - c) p) * (1 - Real.cos φ) / 2 ≤
      (1 - Real.cos φ) * jasPrimeRpowSumB X (ρ.re + c) N := by
    have hc1 := Real.cos_le_one φ
    calc _ ≤ ∑ p ∈ jasPrimesBetween X N, jasR1 (ρ + c) p * (1 - Real.cos φ) :=
          Finset.sum_le_sum fun p _ => by
            have := jasR2_dressed_le_jasR1 (c := c) hβ.le p
            nlinarith [hr₂0 p]
      _ = (1 - Real.cos φ) * jasPrimeRpowSumB X (ρ.re + c) N := by
          rw [jasPrimeRpowSumB_dressed, ← Finset.sum_mul, mul_comm]
  have hlg : (1 - Real.cos φ) * jasPrimeRpowSumB X (ρ.re + c) N ≤ Real.log 2 := by
    refine hcos.trans ?_
    have hS' : 64 * Real.pi ^ 2 / (jasGap ρ ^ 2 * Real.log 2) ≤ jasPrimeRpowSumB X (ρ.re + c) N :=
      (le_max_right _ _).trans hN
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hS'
    linarith
  calc Real.exp _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (hsum.trans hlg)
    _ = 2 := Real.exp_log (by norm_num)


theorem not_jasProductPositiveAbove_of_maximal_offLine_of_lt_of_le (X : ℕ) (q₀ : XiZeroCopy)
    (hβ : (q₀.1 : ℂ).re < 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσh : 1 / 2 ≤ σ) (hσ : σ ≤ 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasProductPositiveAbove X σ := by
  classical
  intro hPP
  have hβ0 : 0 < (q₀.1 : ℂ).re := (xi_divisor_support_re_mem_open_unit q₀.1).1
  have habs : |(q₀.1 : ℂ).re - 1 / 2| = 1 / 2 - (q₀.1 : ℂ).re := by
    rw [abs_of_neg (by linarith)]; ring
  rw [habs] at hσ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = σ - 1 / 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hα1 : (q₀.1 : ℂ).re + c ≤ 1 := by rw [hc]; linarith
  have hα0 : 0 < (q₀.1 : ℂ).re + c := by linarith
  have hPP' : JasProductPositiveAbove X (1 / 2 + c) := by
    rw [show 1 / 2 + c = σ by rw [hc]; ring]; exact hPP
  have hρ0 : (q₀.1 : ℂ) ≠ 0 := fun h => by rw [h] at hβ0; simp at hβ0
  have hρ1 : 1 - (q₀.1 : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨w₀, hw₀⟩ : ∃ w : ℂ, w = 1 / ((q₀.1 : ℂ) * (1 - (q₀.1 : ℂ))) := ⟨_, rfl⟩
  have hw₀n : 0 < ‖w₀‖ :=
    norm_pos_iff.mpr (by rw [hw₀]; exact one_div_ne_zero (mul_ne_zero hρ0 hρ1))
  obtain ⟨wq, hwq⟩ : ∃ wq : XiZeroCopy → ℝ,
      wq = fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := ⟨_, rfl⟩
  have hwq0 : ∀ q, 0 ≤ wq q := fun q => by rw [hwq]; exact norm_nonneg _
  have hwsum : Summable wq := by rw [hwq]; exact summable_inv_mul_one_sub.norm
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q, wq q := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact tsum_nonneg hwq0
  have hη0 : 0 < ‖w₀‖ / (4 * (W + 1)) := by positivity
  obtain ⟨F, hFtail, hq₀F⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, wq q) < ‖w₀‖ / 8 ∧ q₀ ∈ F := by
    have h1 := (tendsto_tsum_compl_atTop_zero wq).eventually
      (gt_mem_nhds (show (0 : ℝ) < ‖w₀‖ / 8 by positivity))
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, {q₀} ⊆ F := eventually_ge_atTop {q₀}
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    exact ⟨F, hF1, hF2 (Finset.mem_singleton_self q₀)⟩
  let D : XiZeroCopy → Prop := fun q =>
    (q.1 : ℂ).im = (q₀.1 : ℂ).im ∧ |(q.1 : ℂ).re - 1 / 2| = 1 / 2 - (q₀.1 : ℂ).re
  have hhead : ∀ q ∈ F.filter (fun q => ¬ D q), ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ →
      φ ≤ Real.pi / 2 →
      jasGap (q₀.1 : ℂ) * jasPrimeRpowSumB X ((q₀.1 : ℂ).re + c) N ≤
        ∑ p ∈ jasPrimesBetween X N, (jasR1 ((q₀.1 : ℂ) + c) p - jasR2 ((q₀.1 : ℂ) - c) p) →
      Real.sin φ * ∑ p ∈ jasPrimesBetween X N,
          (jasR1 ((q₀.1 : ℂ) + c) p - jasR2 ((q₀.1 : ℂ) - c) p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesBetween X N, jasDressedBernoulli (q.1 : ℂ) c p (jasTwistedPoint (q₀.1 : ℂ) φ p)‖ ≤
        ‖w₀‖ / (4 * (W + 1)) * ‖∏ p ∈ jasPrimesBetween X N,
          jasTwistedValue (jasR1 ((q₀.1 : ℂ) + c) p) (jasR2 ((q₀.1 : ℂ) - c) p) φ‖ :=
    fun q hq => eventually_jasCompetitor_leB hβ0 hβ hc0 hα1 hη0 (habs ▸ hmax q)
      (Finset.mem_filter.mp hq).2
  obtain ⟨N, hNhead, hNtail, hNsize⟩ :=
    (((Filter.eventually_all_finset _).mpr hhead).and ((eventually_jasTail_leB hβ hα1).and
      ((tendsto_jasPrimeRpowSumB_atTop hα1).eventually_ge_atTop
        (8 * Real.pi / jasGap (q₀.1 : ℂ))))).exists
  have hTN := jasGap_mul_sum_leB (X := X) hβ c N
  have hgN : 8 * Real.pi ≤ jasGap (q₀.1 : ℂ) * jasPrimeRpowSumB X ((q₀.1 : ℂ).re + c) N := by
    rw [div_le_iff₀ (jasGap_pos hβ)] at hNsize; linarith
  have hθ0 : 0 ≤ Real.pi - w₀.arg := by linarith [Complex.arg_le_pi w₀]
  have hθ2 : Real.pi - w₀.arg < 2 * Real.pi := by linarith [Complex.neg_pi_lt_arg w₀]
  obtain ⟨φ, hφ0, hφ1, hΘ, hsinθ⟩ := exists_jasTwist (P := jasPrimesBetween X N)
    (r₁ := fun p => jasR1 ((q₀.1 : ℂ) + c) p) (r₂ := fun p => jasR2 ((q₀.1 : ℂ) - c) p)
    (fun p => by rw [jasR2_dressed]; exact (Real.exp_pos _).le)
    (fun p => jasR2_dressed_le_jasR1 hβ.le p) (fun p => jasR1_dressed_lt_one hα0 p) hθ0
    (by linarith)
  have hsin8 : Real.sin φ * ∑ p ∈ jasPrimesBetween X N,
      (jasR1 ((q₀.1 : ℂ) + c) p - jasR2 ((q₀.1 : ℂ) - c) p) ≤ 8 * Real.pi := by linarith
  -- the Bernoulli test at the twisted Kronecker point
  have hB := hPP' (jasPrimesBetween X N) (fun p hp => (Finset.mem_filter.mp hp).2)
    (jasTwistedPoint (q₀.1 : ℂ) φ)
  rw [show (1 / 2 + c - 1 / 2 : ℝ) = c by ring] at hB
  obtain ⟨T, hT⟩ : ∃ T : XiZeroCopy → ℂ, T = fun q =>
      (∏ p ∈ jasPrimesBetween X N, jasDressedBernoulli (q.1 : ℂ) c p (jasTwistedPoint (q₀.1 : ℂ) φ p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := ⟨_, rfl⟩
  have hBT : 0 ≤ (∑' q, T q).re := by rw [hT]; exact hB
  obtain ⟨G, hG⟩ : ∃ G : ℂ, G = ∏ p ∈ jasPrimesBetween X N,
      jasTwistedValue (jasR1 ((q₀.1 : ℂ) + c) p) (jasR2 ((q₀.1 : ℂ) - c) p) φ := ⟨_, rfl⟩
  have hG0 : 0 < ‖G‖ := by
    rw [hG]
    refine norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun p _ => fun h0 => ?_)
    have hr1 : 0 ≤ jasR1 ((q₀.1 : ℂ) + c) p := by rw [jasR1_dressed]; exact (Real.exp_pos _).le
    have hr2 : 0 ≤ jasR2 ((q₀.1 : ℂ) - c) p := by rw [jasR2_dressed]; exact (Real.exp_pos _).le
    have := re_jasTwistedValue_pos hr1 (jasR1_dressed_lt_one hα0 p) hr2
      ((jasR2_dressed_le_jasR1 (c := c) hβ.le p).trans_lt (jasR1_dressed_lt_one hα0 p)) φ
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have halign : (w₀ * G).re = -(‖w₀‖ * ‖G‖) := by
    rw [hG]; exact re_mul_prod_eq_neg_of_sum_arg hΘ
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = ∏ p ∈ jasPrimesBetween X N,
      (2 + (jasR1 ((q₀.1 : ℂ) + c) p + jasR2 ((q₀.1 : ℂ) - c) p)) := ⟨_, rfl⟩
  have hterm_norm : ∀ q : XiZeroCopy, ‖T q‖ ≤ Bd * wq q := by
    intro q
    rw [hT, hwq, hBd]
    simp only
    rw [div_eq_mul_one_div, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_prod_jasDressedBernoulli_le (ρ := (q₀.1 : ℂ))
      (q := (q.1 : ℂ)) (c := c) (φ := φ) (jasPrimesBetween X N) (hmax q)) (norm_nonneg _)
  have hsumm : Summable T := Summable.of_norm_bounded (hwsum.mul_left Bd) hterm_norm
  have hBG : Bd ≤ 2 * ‖G‖ := by rw [hBd, hG]; exact hNtail φ hφ0 hφ1 hsin8
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    refine Finset.prod_nonneg fun p _ => ?_
    have h1 : 0 ≤ jasR1 ((q₀.1 : ℂ) + c) p := by rw [jasR1_dressed]; exact (Real.exp_pos _).le
    have h2 : 0 ≤ jasR2 ((q₀.1 : ℂ) - c) p := by rw [jasR2_dressed]; exact (Real.exp_pos _).le
    linarith
  refine absurd hBT (not_le.mpr (re_tsum_neg_of_dominant hsumm F D (A := ‖w₀‖ * ‖G‖)
    (mul_pos hw₀n hG0) ?_ ?_ ?_))
  · -- the dominant pair
    have hDpart : ∀ q ∈ F.filter D, (T q).re = (w₀ * G).re := by
      intro q hq
      obtain ⟨him, habsq⟩ := (Finset.mem_filter.mp hq).2
      rw [hT]
      exact (re_jasDominant_term _ him (habsq.trans habs.symm)).trans (by rw [hw₀, hG])
    rw [Complex.re_sum, Finset.sum_congr rfl hDpart, Finset.sum_const, nsmul_eq_mul, halign]
    have hcard : (1 : ℝ) ≤ ((F.filter D).card : ℝ) := by
      have hq₀D : q₀ ∈ F.filter D := Finset.mem_filter.mpr ⟨hq₀F, show D q₀ from ⟨rfl, habs⟩⟩
      exact_mod_cast Finset.card_pos.mpr ⟨q₀, hq₀D⟩
    have : 0 ≤ ‖w₀‖ * ‖G‖ := by positivity
    nlinarith
  · -- the competitors in the finite set
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ q ∈ F.filter (fun q => ¬ D q), ‖T q‖ ≤ wq q * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) := by
      intro q hq
      have h1 := hNhead q hq φ hφ0 hφ1 hTN hsin8
      rw [← hG] at h1
      rw [hT, hwq]
      simp only
      rw [div_eq_mul_one_div, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    calc ∑ q ∈ F.filter (fun q => ¬ D q), ‖T q‖
        ≤ ∑ q ∈ F.filter (fun q => ¬ D q), wq q * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) :=
          Finset.sum_le_sum hle
      _ = (∑ q ∈ F.filter (fun q => ¬ D q), wq q) * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) := by
          rw [Finset.sum_mul]
      _ ≤ W * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) := by
          gcongr
          rw [hW]
          exact hwsum.sum_le_tsum _ fun q _ => hwq0 q
      _ ≤ ‖w₀‖ * ‖G‖ / 4 := by
          have : W / (W + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          calc W * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) = W / (W + 1) * (‖w₀‖ * ‖G‖ / 4) := by
                field_simp
            _ ≤ 1 * (‖w₀‖ * ‖G‖ / 4) := by gcongr
            _ = ‖w₀‖ * ‖G‖ / 4 := one_mul _
  · -- the tail
    have hs1 : Summable (fun q : {x // x ∉ F} => ‖T q‖) := hsumm.norm.subtype _
    have hs2 : Summable (fun q : {x // x ∉ F} => Bd * wq q) := (hwsum.mul_left Bd).subtype _
    calc ‖∑' q : {x // x ∉ F}, T q‖ ≤ ∑' q : {x // x ∉ F}, ‖T q‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : {x // x ∉ F}, Bd * wq q := Summable.tsum_le_tsum (fun q => hterm_norm q) hs1 hs2
      _ = Bd * ∑' q : {x // x ∉ F}, wq q := tsum_mul_left
      _ ≤ (2 * ‖G‖) * (‖w₀‖ / 8) :=
          mul_le_mul hBG hFtail.le (tsum_nonneg fun q => hwq0 q) (by positivity)
      _ = ‖w₀‖ * ‖G‖ / 4 := by ring

theorem not_jasDressedPSDAbove_of_maximal_offLine_of_lt_of_le (X : ℕ) (q₀ : XiZeroCopy)
    (hβ : (q₀.1 : ℂ).re < 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ : σ ≤ 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasDressedPSDAbove X σ := fun hPSD =>
  not_jasProductPositiveAbove_of_maximal_offLine_of_lt_of_le X q₀ hβ hmax (le_max_right σ (1 / 2))
    (max_le hσ (by linarith [abs_nonneg ((q₀.1 : ℂ).re - 1 / 2)]))
    (hPSD.mono (le_max_left σ (1 / 2))).productPositive

theorem not_jasDressedPSDAbove_of_maximal_offLine_of_lt (X : ℕ) (q₀ : XiZeroCopy) (hβ : (q₀.1 : ℂ).re < 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasDressedPSDAbove X σ :=
  not_jasDressedPSDAbove_of_maximal_offLine_of_lt_of_le X q₀ hβ hmax hσ.le

/-- **A maximal off-line zero excludes large-prime positivity up to and including
`σ = 1 + δ`.** -/
theorem not_jasDressedPSDAbove_of_maximal_offLine_of_le (X : ℕ) (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ : σ ≤ 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasDressedPSDAbove X σ := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact not_jasDressedPSDAbove_of_maximal_offLine_of_lt_of_le X q₀ hlt hmax hσ
  · have hval : (((xiZeroCopyReflectEquiv q₀).1 : ℂ)) = 1 - (q₀.1 : ℂ) := rfl
    have habs : |((xiZeroCopyReflectEquiv q₀).1 : ℂ).re - 1 / 2| = |(q₀.1 : ℂ).re - 1 / 2| := by
      rw [hval, Complex.sub_re, Complex.one_re, show 1 - (q₀.1 : ℂ).re - 1 / 2 =
        -((q₀.1 : ℂ).re - 1 / 2) by ring, abs_neg]
    exact not_jasDressedPSDAbove_of_maximal_offLine_of_lt_of_le X (xiZeroCopyReflectEquiv q₀)
      (by rw [hval, Complex.sub_re, Complex.one_re]; linarith) (fun q => habs ▸ hmax q)
      (habs ▸ hσ)

/-- **A maximal off-line zero excludes product-test positivity up to `σ = 1 + δ`.**  The
Bernoulli tests at the twisted Kronecker point of the maximal zero are rank-one product tests. -/
theorem not_jasProductPositiveAbove_of_maximal_offLine_of_le (X : ℕ) (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσh : 1 / 2 ≤ σ) (hσ : σ ≤ 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasProductPositiveAbove X σ := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact not_jasProductPositiveAbove_of_maximal_offLine_of_lt_of_le X q₀ hlt hmax hσh hσ
  · have hval : (((xiZeroCopyReflectEquiv q₀).1 : ℂ)) = 1 - (q₀.1 : ℂ) := rfl
    have habs : |((xiZeroCopyReflectEquiv q₀).1 : ℂ).re - 1 / 2| = |(q₀.1 : ℂ).re - 1 / 2| := by
      rw [hval, Complex.sub_re, Complex.one_re, show 1 - (q₀.1 : ℂ).re - 1 / 2 =
        -((q₀.1 : ℂ).re - 1 / 2) by ring, abs_neg]
    exact not_jasProductPositiveAbove_of_maximal_offLine_of_lt_of_le X (xiZeroCopyReflectEquiv q₀)
      (by rw [hval, Complex.sub_re, Complex.one_re]; linarith) (fun q => habs ▸ hmax q) hσh
      (habs ▸ hσ)

/-- **A maximal off-line zero excludes JAS positivity below `σ = 1 + δ`.**  If a Xi zero `ρ₀` off
the critical line maximizes `|Re ρ - 1/2|` over all Xi zeros, then the dressed aggregate is not
positive semidefinite for any `σ < 1 + |Re ρ₀ - 1/2|`. -/

theorem not_jasDressedPSDAbove_of_maximal_offLine (X : ℕ) (q₀ : XiZeroCopy) (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasDressedPSDAbove X σ := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact not_jasDressedPSDAbove_of_maximal_offLine_of_lt X q₀ hlt hmax hσ
  · have hval : (((xiZeroCopyReflectEquiv q₀).1 : ℂ)) = 1 - (q₀.1 : ℂ) := rfl
    have habs : |((xiZeroCopyReflectEquiv q₀).1 : ℂ).re - 1 / 2| = |(q₀.1 : ℂ).re - 1 / 2| := by
      rw [hval, Complex.sub_re, Complex.one_re, show 1 - (q₀.1 : ℂ).re - 1 / 2 =
        -((q₀.1 : ℂ).re - 1 / 2) by ring, abs_neg]
    exact not_jasDressedPSDAbove_of_maximal_offLine_of_lt X (xiZeroCopyReflectEquiv q₀)
      (by rw [hval, Complex.sub_re, Complex.one_re]; linarith) (fun q => habs ▸ hmax q)
      (habs ▸ hσ)

/-- **The large-prime abscissa is `½ + Θ` under quasi-RH.**  Under a half-plane bound below `½`,
off RH: positivity above any `X` at `σ` forces `σ ≥ 1 + δ*`, and for every `0 < ε ≤ 1` positivity
holds above some `X` at `1 + δ* + ε`. -/
theorem largePrime_abscissa_eq_of_xiZeroHalfPlaneBound {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) (hRH : ¬ RiemannHypothesis) :
    (∀ (X : ℕ) (σ : ℝ), JasDressedPSDAbove X σ →
        1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ σ) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ X : ℕ, JasDressedPSDAbove X
        (1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) + ε) := by
  by_cases hch : JasOffLineChain
  · exact largePrime_abscissa_eq_of_chain halpha0 halpha hXi hch
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  obtain ⟨q₀, hoff, hmax⟩ := exists_farthest_offLine_of_not_jasOffLineChain hch hRH
  have hsup : sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) =
      |(q₀.1 : ℂ).re - 1 / 2| :=
    le_antisymm (csSup_le (Set.range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact hmax q))
      (le_csSup hbdd ⟨q₀, rfl⟩)
  refine ⟨fun X σ h => ?_, fun ε hε hε1 => ?_⟩
  · by_contra hlt
    push Not at hlt
    rw [hsup] at hlt
    exact not_jasDressedPSDAbove_of_maximal_offLine X q₀ hoff hmax hlt h
  · have hXiS : XiZeroHalfPlaneBound |(q₀.1 : ℂ).re - 1 / 2| := by
      intro ρ hρ
      obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
      have := le_abs_self ((q.1 : ℂ).re - 1 / 2)
      linarith [hmax q]
    obtain ⟨X, hX⟩ := exists_nat_gt (Real.exp (1 / ε + 1))
    rw [hsup]
    exact ⟨X + 2, jasDressedPSDAbove_of_xiZeroHalfPlaneBound (abs_nonneg _) hXiS hε hε1 (by omega)
      (le_of_lt (Real.lt_log_iff_exp_lt (by positivity) |>.mpr (by push_cast; linarith)))⟩

end

end RHTower
