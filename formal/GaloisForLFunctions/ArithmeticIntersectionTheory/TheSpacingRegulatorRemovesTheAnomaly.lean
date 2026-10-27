import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization

/-!
# The spacing regulator removes the anomaly

The Abel regularization uses one radius `r` for every orbit, and the Hecke correspondence `[t]`
moves it: the anomaly `log t` (`TheProjectionFormulaAndTheRegulatorAnomaly`,
`TheHeckeCocycleOfRenormalization`). The torsion points of order `n` are spaced `2π/n` apart, so the
natural regulator of `O_n` scales with `1/n`. Give `O_n` the radius `ρ_n = e^{−ε/n}` and the pair
`(O_m, O_n)` the radius `ρ_m ρ_n` (`spacingRadius`).

* **Positivity at every `ε`** (`spacingForm_nonneg`): `Σ x_m x_n G(m,n) T_{ρ_mρ_n}(m,n)/√(mn) ≥ 0`. The
  energy is the Gram matrix of the vectors `k ↦ ρ_m^k c_m(k)/√k` of Ramanujan sums, Schur-multiplied
  by the gcd twist.
* **A scalar counterterm** (`tendsto_spacingForm`): the divergence is `log(1/(2ε))` per unit mass,
  the same for every orbit, and the renormalized limit is
  `−Σ x_m x_n P(m,n) + Σ x_n² e(n)`, `e(n) = Σ_{p ∣ n} log p/(p − 1)` (the tame different).
* **The anomaly is gone** (`spacingLimit_transport`): under `[t]` the limit changes by
  `Σ x_n² (e(tn) − e(n)) = Σ x_n² Σ_{p ∣ t, p ∤ n} log p/(p − 1)`, the tame ramification only; on
  saturated cycles it is Hecke invariant (`spacingLimit_transport_of_saturated`). Compare
  `β(n, t) = log t − (tame part)` for the Abel radius: scaling the regulator with the spacing removes
  exactly the archimedean degree `log t`.
* **No sign survives** (`spacingLimit_not_nonneg`): the limit is indefinite, already on the orders
  `{1, 2}`. The counterterm is a scalar multiple of the identity, whose null cone is `{0}`: by the
  survival law (RBG `TheRenormalizationSurvivalLaw`) positivity before the limit carries no
  information after it.

So covariance can be restored at the cost of the sign: the spacing regulator is Hecke covariant up
to tame ramification and positive at every `ε`, and its limit is not positive. A covariant regulator
whose counterterm has a nontrivial null cone is what the Hodge index would need.
-/

noncomputable section

open Finset Filter Topology
open scoped ComplexConjugate ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-- The **spacing radius** `ρ_m ρ_n = e^{−ε(1/m + 1/n)}` of the pair `(O_m, O_n)`. -/
def spacingRadius (ε : ℝ) (m n : ℕ) : ℝ := Real.exp (-ε * ((m : ℝ)⁻¹ + (n : ℝ)⁻¹))

/-- The spacing-regularized torsion energy. -/
def spacingEnergy (ε : ℝ) (m n : ℕ) : ℝ := torsionEnergy (spacingRadius ε m n) m n

theorem spacingRadius_nonneg (ε : ℝ) (m n : ℕ) : 0 ≤ spacingRadius ε m n := (Real.exp_pos _).le

theorem spacingRadius_lt_one {ε : ℝ} (hε : 0 < ε) {m n : ℕ} (hm : 0 < m) :
    spacingRadius ε m n < 1 := by
  rw [spacingRadius, Real.exp_lt_one]
  have : (0 : ℝ) < (m : ℝ)⁻¹ := by positivity
  have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  nlinarith

theorem spacingRadius_pow (ε : ℝ) (m n k : ℕ) :
    spacingRadius ε m n ^ k = Real.exp (-ε * (m : ℝ)⁻¹) ^ k * Real.exp (-ε * (n : ℝ)⁻¹) ^ k := by
  rw [spacingRadius, ← mul_pow, ← Real.exp_add]
  ring_nf

/-- **Gram positivity with spacing radii**: `Σ y_m y_n T_{ρ_mρ_n}(m,n) = Σ_k (1/k)|Σ y_m ρ_m^k c_m(k)|²`. -/
theorem sum_sum_spacingEnergy_nonneg {ε : ℝ} (hε : 0 < ε) {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    (y : ℕ → ℝ) : 0 ≤ ∑ m ∈ S, ∑ n ∈ S, y m * y n * spacingEnergy ε m n := by
  have h := hasSum_sum fun m (hm : m ∈ S) => hasSum_sum fun n (_ : n ∈ S) =>
    (hasSum_torsionEnergy (spacingRadius_nonneg ε m n) (spacingRadius_lt_one hε (hS m hm))
      m n).mul_left (y m * y n)
  refine h.nonneg fun k => ?_
  set ρ : ℕ → ℝ := fun m => Real.exp (-ε * (m : ℝ)⁻¹) ^ k
  have hsq : ∑ m ∈ S, ∑ n ∈ S, y m * y n * (spacingRadius ε m n ^ k / k *
      (ramanujanSum m k * conj (ramanujanSum n k)).re) =
      1 / (k : ℝ) * Complex.normSq (∑ m ∈ S, ((y m * ρ m : ℝ) : ℂ) * ramanujanSum m k) := by
    rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, sum_mul_sum,
      Complex.re_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Complex.re_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_ofReal, show ((y m * ρ m : ℝ) : ℂ) * ramanujanSum m k *
      (((y n * ρ n : ℝ) : ℂ) * conj (ramanujanSum n k)) = ((y m * ρ m * (y n * ρ n) : ℝ) : ℂ) *
        (ramanujanSum m k * conj (ramanujanSum n k)) by push_cast; ring, Complex.re_ofReal_mul,
      spacingRadius_pow]
    simp only [ρ]
    ring
  rw [hsq]
  exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)

/-- The spacing-regularized twisted form `Σ x_m x_n G(m,n) T_{ρ_mρ_n}(m,n)/√(mn)`. -/
def spacingForm (ε : ℝ) (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy (spacingRadius ε m n) m n

/-- **Positivity at every regulator.** -/
theorem spacingForm_nonneg {ε : ℝ} (hε : 0 < ε) {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    (x : ℕ → ℝ) : 0 ≤ spacingForm ε S x := by
  classical
  set y : ℕ → ℝ := fun n => x n / Real.sqrt n
  set E := S.biUnion Nat.divisors
  set z : ℕ → ℕ → ℝ := fun e m => if e ∣ m then y m else 0
  have hG : ∀ m ∈ S, ∀ n ∈ S, gcdTwist m n =
      ∑ e ∈ E, if e ∣ m ∧ e ∣ n then twistWeight e else 0 := by
    intro m hm n hn
    rw [gcdTwist, ← sum_filter]
    congr 1
    ext e
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, E, mem_biUnion]
    constructor
    · rintro ⟨⟨hem, hen⟩, -⟩
      exact ⟨⟨m, hm, hem, (hS m hm).ne'⟩, hem, hen⟩
    · rintro ⟨-, hem, hen⟩
      exact ⟨⟨hem, hen⟩, (Nat.gcd_pos_of_pos_left n (hS m hm)).ne'⟩
  have hpt : ∀ m ∈ S, ∀ n ∈ S, x m * x n * twistedEnergy (spacingRadius ε m n) m n =
      ∑ e ∈ E, twistWeight e * (z e m * z e n * spacingEnergy ε m n) := by
    intro m hm n hn
    rw [twistedEnergy, Real.sqrt_mul (Nat.cast_nonneg m), hG m hm n hn]
    rw [show x m * x n * ((∑ e ∈ E, if e ∣ m ∧ e ∣ n then twistWeight e else 0) *
        torsionEnergy (spacingRadius ε m n) m n / (Real.sqrt m * Real.sqrt n)) =
        ∑ e ∈ E, (if e ∣ m ∧ e ∣ n then twistWeight e else 0) *
          (y m * y n * spacingEnergy ε m n) by
      rw [sum_mul, sum_div, mul_sum]
      refine sum_congr rfl fun e _ => ?_
      simp only [y, spacingEnergy]
      field_simp]
    refine sum_congr rfl fun e _ => ?_
    by_cases hem : e ∣ m <;> by_cases hen : e ∣ n <;> simp [z, hem, hen]
  unfold spacingForm
  rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hpt m hm n hn]
  rw [sum_congr rfl fun m _ => sum_comm, sum_comm]
  refine sum_nonneg fun e _ => ?_
  simp_rw [← mul_sum]
  exact mul_nonneg (twistWeight_nonneg e) (sum_sum_spacingEnergy_nonneg hε hS (z e))

/-! ### The renormalized limit -/

theorem tendsto_spacingRadius (m n : ℕ) :
    Tendsto (fun ε : ℝ => spacingRadius ε m n) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous fun ε : ℝ => spacingRadius ε m n := by unfold spacingRadius; fun_prop
  have := (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa [spacingRadius] using this

/-- `log(1 − e^{−u}) − log u → 0` as `u → 0⁺`. -/
theorem tendsto_log_one_sub_exp_neg_sub_log :
    Tendsto (fun u : ℝ => Real.log (1 - Real.exp (-u)) - Real.log u) (𝓝[>] 0) (𝓝 0) := by
  have hlo : Tendsto (fun u : ℝ => -u) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hu : (0 : ℝ) < u := hu
    have h1 : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
      have := Real.add_one_le_exp u
      have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-u)]
    have hpos : 0 < u * Real.exp (-u) := mul_pos hu (Real.exp_pos _)
    have := Real.log_le_log hpos h1
    rw [Real.log_mul hu.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    linarith
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hu : (0 : ℝ) < u := hu
    have h1 : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
    have hpos : 0 < 1 - Real.exp (-u) := by
      have := Real.exp_lt_one.mpr (show -u < 0 by linarith); linarith
    have := Real.log_le_log hpos h1
    linarith

/-- The diagonal: `T_{ρ_n²}(n,n)/φ(n) + log(2ε) → −c(n) + log n = e(n)`. -/
theorem tendsto_spacing_diagonal {n : ℕ} (hn : 0 < n) :
    Tendsto (fun ε : ℝ => twistedEnergy (spacingRadius ε n n) n n + Real.log (2 * ε)) (𝓝[>] 0)
      (𝓝 (tameDifferent n)) := by
  have hφ : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  -- the twisted diagonal is `T/φ(n)`
  have hdiag : ∀ r, twistedEnergy r n n = torsionEnergy r n n / Nat.totient n := by
    intro r
    rw [twistedEnergy, gcdTwist_eq, Nat.gcd_self, Real.sqrt_mul_self hnr.le]
    field_simp
  -- AET: `T_r(n,n) + φ(n) log|1 − r| → −I(n, n)`
  have hA := (tendsto_torsionEnergy_self_add_log n).comp (tendsto_spacingRadius n n)
  have hA' := hA.div_const (Nat.totient n : ℝ)
  -- `log|1 − ρ_n²| − log(2ε/n) → 0`
  have hu : Tendsto (fun ε : ℝ => 2 * ε / n) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_const.mul continuous_id).div_const (n : ℝ)).tendsto (0 : ℝ)
        |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos (by linarith [show (0 : ℝ) < ε from hε]) hnr
  have hB := tendsto_log_one_sub_exp_neg_sub_log.comp hu
  have hsum := hA'.sub hB
  have hval : -orbitIntersection n n / Nat.totient n - 0 + Real.log n = tameDifferent n := by
    have := selfIntersection_eq hn
    rw [selfIntersection] at this
    rw [neg_div, this]; ring
  rw [← hval]
  refine (hsum.add_const (Real.log n)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : (0 : ℝ) < ε := hε
  have hr : spacingRadius ε n n = Real.exp (-(2 * ε / n)) := by
    rw [spacingRadius]; congr 1; field_simp; ring
  have h1r : 0 < 1 - spacingRadius ε n n := by
    have := spacingRadius_lt_one hε hn (n := n); linarith
  simp only [Function.comp_def, hdiag, hr]
  rw [abs_of_pos (by rw [← hr]; exact h1r), Real.log_div (by positivity) hnr.ne',
    Real.log_mul two_ne_zero hε.ne'] at *
  rw [Real.log_div (by positivity) hnr.ne', Real.log_mul two_ne_zero hε.ne']
  field_simp
  ring

/-- The renormalized spacing limit `−Σ x_m x_n P(m,n) + Σ x_n² e(n)`. -/
def spacingLimit (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  -primeForm S x + ∑ n ∈ S, x n ^ 2 * tameDifferent n

/-- **The spacing regulator has a scalar counterterm.** `Q_ε(x) + log(2ε)|x|² → −P(x) + Σ x_n² e(n)`. -/
theorem tendsto_spacingForm {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (x : ℕ → ℝ) :
    Tendsto (fun ε : ℝ => spacingForm ε S x + Real.log (2 * ε) * ∑ n ∈ S, x n ^ 2) (𝓝[>] 0)
      (𝓝 (spacingLimit S x)) := by
  classical
  -- split each row into its diagonal and off-diagonal parts
  have hsplit : ∀ ε, spacingForm ε S x + Real.log (2 * ε) * ∑ n ∈ S, x n ^ 2 =
      ∑ m ∈ S, (x m ^ 2 * (twistedEnergy (spacingRadius ε m m) m m + Real.log (2 * ε)) +
        ∑ n ∈ S.erase m, x m * x n * twistedEnergy (spacingRadius ε m n) m n) := by
    intro ε
    rw [spacingForm, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m hm => ?_
    rw [← add_sum_erase _ _ hm]
    ring
  have hlim : spacingLimit S x = ∑ m ∈ S, (x m ^ 2 * tameDifferent m +
      ∑ n ∈ S.erase m, x m * x n * -weilPrimeKernel m n) := by
    rw [spacingLimit, primeForm, sum_add_distrib, add_comm, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun m hm => ?_
    rw [← add_sum_erase _ _ hm, ← sum_neg_distrib]
    simp only [weilPrimeKernel, ne_eq, not_true_eq_false, and_false, if_false, mul_zero, neg_zero,
      zero_add]
    refine sum_congr rfl fun n _ => ?_
    ring
  simp_rw [hsplit]
  rw [hlim]
  refine tendsto_finsetSum _ fun m hm => ?_
  refine ((tendsto_spacing_diagonal (hS m hm)).const_mul _).add
    (tendsto_finsetSum _ fun n hn => ?_)
  have hmn : n ≠ m := ne_of_mem_erase hn
  exact ((tendsto_twistedEnergy_of_ne (hS m hm) (hS n (mem_of_mem_erase hn)) hmn.symm).comp
    (tendsto_spacingRadius m n)).const_mul _

/-! ### Covariance and the absence of a sign -/

/-- **The anomaly is gone**: under `[t]` the spacing limit changes only by the tame ramification. -/
theorem spacingLimit_transport {S : Finset ℕ} {t : ℕ} (ht : 0 < t) (x : ℕ → ℝ) :
    spacingLimit (S.image (t * ·)) (heckeTransport t x) - spacingLimit S x =
      ∑ n ∈ S, x n ^ 2 * (tameDifferent (t * n) - tameDifferent n) := by
  simp only [spacingLimit, primeForm, sum_image_mul_left ht, heckeTransport_mul ht,
    weilPrimeKernel_mul_left ht, mul_sub, sum_sub_distrib]
  ring

/-- On saturated cycles the spacing limit is Hecke invariant. -/
theorem spacingLimit_transport_of_saturated {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) {t : ℕ}
    (ht : 0 < t) (hsat : ∀ n ∈ S, t.primeFactors ⊆ n.primeFactors) (x : ℕ → ℝ) :
    spacingLimit (S.image (t * ·)) (heckeTransport t x) = spacingLimit S x := by
  have h := spacingLimit_transport (S := S) ht x
  rw [sum_eq_zero fun n hn => by
    rw [tameDifferent_mul_of_subset (hS n hn) ht (hsat n hn), sub_self, mul_zero]] at h
  linarith

/-- **No sign survives**: the spacing limit is indefinite. On `{1, 2}` with `x = (1, 1)` it equals
`(1 − √2) log 2 < 0`. -/
theorem spacingLimit_not_nonneg : ¬ ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
    0 ≤ spacingLimit S x := by
  intro h
  have h12 := h {1, 2} (fun _ => 1) (by intro n hn; simp at hn; omega)
  have hP12 : weilPrimeKernel 1 2 = Real.log 2 / Real.sqrt 2 := by
    rw [weilPrimeKernel, if_pos ⟨one_dvd 2, by norm_num⟩]
    norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hP21 : weilPrimeKernel 2 1 = Real.log 2 / Real.sqrt 2 := by
    rw [weilPrimeKernel, if_neg (by norm_num), if_pos ⟨one_dvd 2, by norm_num⟩]
    norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have he1 : tameDifferent 1 = 0 := by simp [tameDifferent]
  have he2 : tameDifferent 2 = Real.log 2 := by
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num, tameDifferent_prime_pow Nat.prime_two one_ne_zero]
    norm_num
  simp only [spacingLimit, primeForm] at h12
  rw [sum_pair (by norm_num : (1 : ℕ) ≠ 2), sum_pair (by norm_num : (1 : ℕ) ≠ 2),
    sum_pair (by norm_num : (1 : ℕ) ≠ 2), sum_pair (by norm_num : (1 : ℕ) ≠ 2)] at h12
  simp only [one_mul, mul_one, one_pow, he1, he2, hP12, hP21] at h12
  have h11 : weilPrimeKernel 1 1 = 0 := by simp [weilPrimeKernel]
  have h22 : weilPrimeKernel 2 2 = 0 := by simp [weilPrimeKernel]
  rw [h11, h22] at h12
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have : Real.log 2 / Real.sqrt 2 > Real.log 2 / 2 := div_lt_div_of_pos_left hl hs0 hs
  linarith

end GaloisForLFunctions.ArithmeticIntersectionTheory
