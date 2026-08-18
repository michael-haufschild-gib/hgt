/-
# Sublogarithmic divisors on an arbitrary index

A divisor is presented as a family `a : ι → ℂ` over an arbitrary index type, locally finite (every
disc meets it in a finite set) and of sublogarithmic density `n(r) = o(log r)`.  No ordering of the
family is assumed, so the results apply directly to the zero divisor of an entire function indexed
by `Σ (w : zero), Fin (multiplicity w)`.

The convergence exponent of such a divisor is zero: `∑_i ‖a i‖^{-α} < ∞` for every `α > 0`.  The
proof replaces Abel summation by a bucket decomposition — index `i` by `⌊log ‖a i‖⌋` and use that
the bucket `n` is contained in the disc of radius `e^{n+1}`, hence has at most `n+1` elements once
`n` is large.  `summable_of_bucket` isolates this as a general criterion: a nonnegative family with
finite fibers over `ℕ` and a summable fiberwise majorant is summable.

Summability of `‖a i‖⁻¹` makes the genus-zero canonical product `∏_i (1 - z / a i)` converge, with
`log ‖P(z)‖ ≤ ∑_i log(1 + ‖z‖ / ‖a i‖)`.
-/
import Mathlib

noncomputable section

open Filter Topology Set Asymptotics Metric

namespace GaloisForLFunctions.CountableDivisor

/-! ## A bucket criterion for summability -/

/-- **Bucketed summability.**  A nonnegative family whose index type is partitioned into finite
fibers by `b`, with a fiberwise majorant `M` whose weighted total converges, is summable. -/
theorem summable_of_bucket {ι : Type*} (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) (b : ι → ℕ)
    (hfib : ∀ n, {i | b i = n}.Finite)
    (M : ℕ → ℝ) (hM : ∀ i, g i ≤ M (b i))
    (hMsum : Summable (fun n : ℕ => ({i | b i = n}.ncard : ℝ) * M n)) :
    Summable g := by
  classical
  have hequiv := (Equiv.sigmaFiberEquiv b).summable_iff (f := g)
  rw [← hequiv, Function.comp_def]
  rw [summable_sigma_of_nonneg (fun p => hg _)]
  constructor
  · intro n
    haveI : Finite {i // b i = n} := Set.Finite.to_subtype (hfib n)
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => hg _)) (fun n => ?_) hMsum
    haveI : Fintype {x // b x = n} := (hfib n).fintype
    rw [tsum_fintype]
    have hcard : (Finset.univ : Finset {x // b x = n}).card = {i | b i = n}.ncard := by
      haveI hf : Fintype ↑{i | b i = n} := (hfib n).fintype
      rw [← Nat.card_coe_set_eq, @Nat.card_eq_fintype_card _ hf, Finset.card_univ]
      exact Fintype.card_congr (Equiv.refl _)
    calc ∑ p : {i // b i = n}, g ((Equiv.sigmaFiberEquiv b) ⟨n, p⟩)
        ≤ ∑ _p : {i // b i = n}, M n := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          have := hM ((Equiv.sigmaFiberEquiv b) ⟨n, p⟩)
          have hb : b ((Equiv.sigmaFiberEquiv b) ⟨n, p⟩) = n := p.2
          rwa [hb] at this
      _ = ({i | b i = n}.ncard : ℝ) * M n := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-! ## Divisors with sublogarithmic density on an arbitrary index -/

variable {ι : Type*}

/-- The number of divisor points, with multiplicity, in the closed disc of radius `r`. -/
def divisorIdxCount (a : ι → ℂ) (r : ℝ) : ℕ := {i : ι | ‖a i‖ ≤ r}.ncard

/-- Every disc contains only finitely many divisor points. -/
def LocallyFiniteDivisor (a : ι → ℂ) : Prop := ∀ r : ℝ, {i : ι | ‖a i‖ ≤ r}.Finite

/-- The divisor has sublogarithmic density, `n(r) = o(log r)`. -/
def SublogDensityIdx (a : ι → ℂ) : Prop :=
  Tendsto (fun r : ℝ => (divisorIdxCount a r : ℝ) / Real.log r) atTop (𝓝 0)

theorem eventually_count_le {a : ι → ℂ} (hden : SublogDensityIdx a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, (divisorIdxCount a r : ℝ) ≤ ε * Real.log r := by
  have hev : ∀ᶠ r : ℝ in atTop, (divisorIdxCount a r : ℝ) / Real.log r < ε :=
    hden.eventually_lt_const hε
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with r hr h1
  have hlog : 0 < Real.log r := Real.log_pos h1
  rw [div_lt_iff₀ hlog] at hr
  linarith

/-- The logarithmic bucket index of a divisor point. -/
def logBucket (a : ι → ℂ) (i : ι) : ℕ := ⌊Real.log ‖a i‖⌋₊

theorem logBucket_fiber_subset {a : ι → ℂ} (n : ℕ) :
    {i : ι | logBucket a i = n} ⊆ {i : ι | ‖a i‖ ≤ Real.exp ((n : ℝ) + 1)} := by
  intro i hi
  simp only [Set.mem_setOf_eq, logBucket] at hi ⊢
  by_contra hgt
  rw [not_le] at hgt
  have hpos : (0 : ℝ) < ‖a i‖ := lt_trans (Real.exp_pos _) hgt
  have hlog : (n : ℝ) + 1 < Real.log ‖a i‖ := by
    have := Real.log_lt_log (Real.exp_pos ((n : ℝ) + 1)) hgt
    rwa [Real.log_exp] at this
  have hfloor : n + 1 ≤ ⌊Real.log ‖a i‖⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith
  omega

theorem finite_logBucket_fiber {a : ι → ℂ} (hloc : LocallyFiniteDivisor a) (n : ℕ) :
    {i : ι | logBucket a i = n}.Finite :=
  (hloc (Real.exp ((n : ℝ) + 1))).subset (logBucket_fiber_subset n)

theorem ncard_logBucket_fiber_le {a : ι → ℂ} (hloc : LocallyFiniteDivisor a) (n : ℕ) :
    ({i : ι | logBucket a i = n}.ncard : ℝ)
      ≤ (divisorIdxCount a (Real.exp ((n : ℝ) + 1)) : ℝ) := by
  have h := Set.ncard_le_ncard (logBucket_fiber_subset (a := a) n)
    (hloc (Real.exp ((n : ℝ) + 1)))
  exact_mod_cast h

end GaloisForLFunctions.CountableDivisor

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

/-! ## Exponent of convergence zero -/

theorem summable_linear_expNeg {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-α * n)) := by
  have hbase : ‖Real.exp (-α)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-α) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := Real.exp (-α)) hbase
  have hgeo0 : Summable (fun n : ℕ => Real.exp (-α) ^ n) :=
    summable_geometric_of_norm_lt_one hbase
  refine ((hgeo.add hgeo0)).congr (fun n => ?_)
  have hexp : Real.exp (-α * n) = Real.exp (-α) ^ n := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [hexp]
  ring

theorem norm_rpow_le_expBucket {a : ι → ℂ} {i : ι} (h1 : 1 < ‖a i‖) {α : ℝ} (hα : 0 < α) :
    ‖a i‖ ^ (-α) ≤ Real.exp (-α * (logBucket a i : ℝ)) := by
  have hpos : (0 : ℝ) < ‖a i‖ := by linarith
  have hlognn : 0 ≤ Real.log ‖a i‖ := Real.log_nonneg h1.le
  have hfloor : ((⌊Real.log ‖a i‖⌋₊ : ℕ) : ℝ) ≤ Real.log ‖a i‖ := Nat.floor_le hlognn
  have hexple : Real.exp ((logBucket a i : ℝ)) ≤ ‖a i‖ := by
    rw [logBucket]
    calc Real.exp ((⌊Real.log ‖a i‖⌋₊ : ℝ)) ≤ Real.exp (Real.log ‖a i‖) :=
          Real.exp_le_exp.mpr hfloor
      _ = ‖a i‖ := Real.exp_log hpos
  have hbpos : (0 : ℝ) < Real.exp ((logBucket a i : ℝ)) := Real.exp_pos _
  calc ‖a i‖ ^ (-α) ≤ (Real.exp ((logBucket a i : ℝ))) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos hbpos hexple (by linarith)
    _ = Real.exp (-α * (logBucket a i : ℝ)) := by
        rw [← Real.exp_mul]
        ring_nf

/-- **Exponent of convergence zero.**  A sublogarithmic divisor has summable inverse powers for
every positive exponent. -/
theorem summable_rpow_neg_idx {a : ι → ℂ}
    (hloc : LocallyFiniteDivisor a) (hden : SublogDensityIdx a) {α : ℝ} (hα : 0 < α) :
    Summable (fun i : ι => ‖a i‖ ^ (-α)) := by
  classical
  set S : Set ι := {i : ι | ‖a i‖ ≤ 1} with hS
  rw [← summable_subtype_and_compl (s := S)]
  constructor
  · haveI : Finite ↑S := Set.Finite.to_subtype (hloc 1)
    exact Summable.of_finite
  · have hgt : ∀ p : ↑(Sᶜ), 1 < ‖a p.1‖ := by
      intro p
      have hp := p.2
      simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hp
      exact hp
    have hle : ∀ n : ℕ, ({p : ↑(Sᶜ) | logBucket a p.1 = n}).ncard
        ≤ {i : ι | logBucket a i = n}.ncard := by
      intro n
      exact Set.ncard_le_ncard_of_injOn (fun p : ↑(Sᶜ) => (p : ι))
        (fun p hp => hp) (fun p _ q _ h => Subtype.ext h)
        (finite_logBucket_fiber hloc n)
    have hfib : ∀ n : ℕ, {p : ↑(Sᶜ) | logBucket a p.1 = n}.Finite := by
      intro n
      refine Set.Finite.ofFinset ((finite_logBucket_fiber hloc n).toFinset.preimage
        (fun p : ↑(Sᶜ) => (p : ι)) (fun p _ q _ h => Subtype.ext h)) ?_
      intro p
      simp [Set.Finite.mem_toFinset]
    refine summable_of_bucket _ (fun p => Real.rpow_nonneg (norm_nonneg _) _)
      (fun p => logBucket a p.1) hfib (fun n => Real.exp (-α * (n : ℝ)))
      (fun p => norm_rpow_le_expBucket (hgt p) hα) ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (eventually_count_le hden (ε := 1) (by norm_num))
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge N
    have hbound : ∀ n : ℕ, N₀ ≤ n →
        ({p : ↑(Sᶜ) | logBucket a p.1 = n}.ncard : ℝ) ≤ (n : ℝ) + 1 := by
      intro n hn
      have hcast : (N₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      have hexp : (n : ℝ) ≤ Real.exp ((n : ℝ) + 1) := by
        have := Real.add_one_le_exp ((n : ℝ) + 1)
        linarith
      have h2 := hN (Real.exp ((n : ℝ) + 1)) (by linarith)
      rw [one_mul, Real.log_exp] at h2
      have h3 : (({p : ↑(Sᶜ) | logBucket a p.1 = n}).ncard : ℝ)
          ≤ ({i : ι | logBucket a i = n}.ncard : ℝ) := by exact_mod_cast hle n
      exact le_trans h3 (le_trans (ncard_logBucket_fiber_le hloc n) h2)
    rw [← summable_nat_add_iff N₀]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((summable_nat_add_iff N₀).mpr (summable_linear_expNeg hα)))
    have hb := hbound (n + N₀) (by omega)
    exact mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)

end GaloisForLFunctions.CountableDivisor

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

/-! ## The genus-zero canonical product on an arbitrary index -/

theorem summable_inv_norm_idx {a : ι → ℂ}
    (hloc : LocallyFiniteDivisor a) (hden : SublogDensityIdx a) :
    Summable (fun i : ι => ‖a i‖⁻¹) := by
  refine (summable_rpow_neg_idx hloc hden (α := 1) one_pos).congr (fun i => ?_)
  rw [Real.rpow_neg_one]

/-- The genus-zero canonical product `∏_i (1 - z / a i)`. -/
def genusZeroProductIdx (a : ι → ℂ) (z : ℂ) : ℂ := ∏' i : ι, (1 - z / a i)

theorem multipliable_genusZeroIdx {a : ι → ℂ} (hinv : Summable (fun i => ‖a i‖⁻¹)) (z : ℂ) :
    Multipliable (fun i : ι => 1 - z / a i) := by
  have h : Summable (fun i : ι => ‖-(z / a i)‖) := by
    have hfun : ∀ i : ι, ‖-(z / a i)‖ = ‖z‖ * ‖a i‖⁻¹ := by
      intro i
      rw [norm_neg, norm_div, div_eq_mul_inv]
    rw [funext hfun]
    exact hinv.mul_left ‖z‖
  refine (multipliable_one_add_of_summable h).congr (fun i => ?_)
  ring

theorem summable_logOnePlusIdx {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hinv : Summable (fun i => ‖a i‖⁻¹)) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun i : ι => Real.log (1 + r / ‖a i‖)) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hinv.mul_left r)
  · refine Real.log_nonneg ?_
    have : 0 ≤ r / ‖a i‖ := by positivity
    linarith
  · have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
    have h1 : Real.log (1 + r / ‖a i‖) ≤ r / ‖a i‖ := by
      have := Real.log_le_sub_one_of_pos (x := 1 + r / ‖a i‖) (by positivity)
      linarith
    rw [div_eq_mul_inv] at h1
    exact h1

/-- The maximum modulus of the genus-zero product is controlled by the logarithmic sum. -/
theorem log_norm_genusZeroProductIdx_le {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hinv : Summable (fun i => ‖a i‖⁻¹)) (z : ℂ) :
    Real.log ‖genusZeroProductIdx a z‖ ≤ ∑' i : ι, Real.log (1 + ‖z‖ / ‖a i‖) := by
  classical
  set S : ℝ := ∑' i : ι, Real.log (1 + ‖z‖ / ‖a i‖) with hS
  have hsum := summable_logOnePlusIdx hane hinv (r := ‖z‖) (norm_nonneg z)
  have hnn : ∀ i : ι, 0 ≤ Real.log (1 + ‖z‖ / ‖a i‖) := by
    intro i
    refine Real.log_nonneg ?_
    have : 0 ≤ ‖z‖ / ‖a i‖ := by positivity
    linarith
  have hfin : ∀ s : Finset ι, ‖∏ i ∈ s, (1 - z / a i)‖ ≤ Real.exp S := by
    intro s
    have h1 : ‖∏ i ∈ s, (1 - z / a i)‖ ≤ ∏ i ∈ s, (1 + ‖z‖ / ‖a i‖) := by
      rw [norm_prod]
      refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
      calc ‖1 - z / a i‖ ≤ ‖(1 : ℂ)‖ + ‖z / a i‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ / ‖a i‖ := by rw [norm_one, norm_div]
    have h2 : ∏ i ∈ s, (1 + ‖z‖ / ‖a i‖)
        = Real.exp (∑ i ∈ s, Real.log (1 + ‖z‖ / ‖a i‖)) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      refine (Real.exp_log ?_).symm
      have : 0 ≤ ‖z‖ / ‖a i‖ := by positivity
      linarith
    have h3 : ∑ i ∈ s, Real.log (1 + ‖z‖ / ‖a i‖) ≤ S :=
      hsum.sum_le_tsum s (fun i _ => hnn i)
    calc ‖∏ i ∈ s, (1 - z / a i)‖ ≤ ∏ i ∈ s, (1 + ‖z‖ / ‖a i‖) := h1
      _ = Real.exp (∑ i ∈ s, Real.log (1 + ‖z‖ / ‖a i‖)) := h2
      _ ≤ Real.exp S := Real.exp_le_exp.mpr h3
  have hprod : HasProd (fun i : ι => 1 - z / a i) (genusZeroProductIdx a z) :=
    (multipliable_genusZeroIdx hinv z).hasProd
  have hle : ‖genusZeroProductIdx a z‖ ≤ Real.exp S := by
    refine le_of_tendsto (Filter.Tendsto.norm hprod) ?_
    exact Filter.Eventually.of_forall hfin
  rcases eq_or_lt_of_le (norm_nonneg (genusZeroProductIdx a z)) with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact tsum_nonneg hnn
  · calc Real.log ‖genusZeroProductIdx a z‖ ≤ Real.log (Real.exp S) :=
          Real.log_le_log hpos hle
      _ = S := Real.log_exp S

end GaloisForLFunctions.CountableDivisor

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

/-- A locally finite divisor of nonzero points is bounded away from the origin. -/
theorem exists_pos_lower_bound {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hloc : LocallyFiniteDivisor a) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ ‖a i‖ := by
  classical
  set T : Finset ι := (hloc 1).toFinset with hT
  by_cases hne : T.Nonempty
  · set m : ℝ := min 1 (T.inf' hne (fun i => ‖a i‖)) with hm
    have hinfpos : 0 < T.inf' hne (fun i => ‖a i‖) := by
      rw [Finset.lt_inf'_iff]
      intro i _
      exact norm_pos_iff.mpr (hane i)
    refine ⟨m, by positivity, fun i => ?_⟩
    by_cases hi : ‖a i‖ ≤ 1
    · have hmem : i ∈ T := by
        rw [hT, Set.Finite.mem_toFinset]
        exact hi
      exact le_trans (min_le_right _ _) (Finset.inf'_le _ hmem)
    · exact le_trans (min_le_left _ _) (le_of_lt (lt_of_not_ge hi))
  · refine ⟨1, one_pos, fun i => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    exact hne ⟨i, by rw [hT, Set.Finite.mem_toFinset]; exact hlt.le⟩

/-- The card counts a finite selection of divisor points inside a disc. -/
theorem card_filter_le {a : ι → ℂ} (hloc : LocallyFiniteDivisor a) (s : Finset ι) (t : ℝ) :
    ((s.filter (fun i => ‖a i‖ ≤ t)).card : ℝ) ≤ (divisorIdxCount a t : ℝ) := by
  classical
  have hsub : (↑(s.filter (fun i => ‖a i‖ ≤ t)) : Set ι) ⊆ {i : ι | ‖a i‖ ≤ t} := by
    intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi
    exact hi.2
  have h1 : (s.filter (fun i => ‖a i‖ ≤ t)).card
      = (↑(s.filter (fun i => ‖a i‖ ≤ t)) : Set ι).ncard := (Set.ncard_coe_finset _).symm
  have h2 : (↑(s.filter (fun i => ‖a i‖ ≤ t)) : Set ι).ncard ≤ divisorIdxCount a t :=
    Set.ncard_le_ncard hsub (hloc t)
  rw [h1]
  exact_mod_cast h2

/-- **The three-bucket bound.**  The logarithmic sum splits into a near part counted by
`n(√r)`, a middle part counted by `n(r²)`, and a far tail bounded by the convergent half-power
series. -/
theorem tsum_log_le {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hloc : LocallyFiniteDivisor a) (hden : SublogDensityIdx a)
    {m : ℝ} (hm : 0 < m) (hmle : ∀ i, m ≤ ‖a i‖) {r : ℝ} (hr : 1 ≤ r) :
    ∑' i : ι, Real.log (1 + r / ‖a i‖)
      ≤ (divisorIdxCount a (Real.sqrt r) : ℝ) * Real.log (1 + r / m)
        + (divisorIdxCount a (r ^ 2) : ℝ) * Real.log (1 + Real.sqrt r)
        + ∑' i : ι, ‖a i‖ ^ (-(1 / 2) : ℝ) := by
  classical
  have hinv := summable_inv_norm_idx hloc hden
  have hsum := summable_logOnePlusIdx hane hinv (r := r) (by linarith)
  have hhalf := summable_rpow_neg_idx hloc hden (α := (1 / 2 : ℝ)) (by norm_num)
  have hnn : ∀ i : ι, 0 ≤ Real.log (1 + r / ‖a i‖) := by
    intro i
    refine Real.log_nonneg ?_
    have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
    have : 0 ≤ r / ‖a i‖ := by positivity
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt r := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hr
  refine hsum.tsum_le_of_sum_le (fun s => ?_)
  -- split the finite sum into the three buckets
  have hsplit1 := Finset.sum_filter_add_sum_filter_not s
    (fun i => ‖a i‖ ≤ Real.sqrt r) (fun i => Real.log (1 + r / ‖a i‖))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))) (fun i => ‖a i‖ ≤ r ^ 2)
    (fun i => Real.log (1 + r / ‖a i‖))
  -- bucket one
  have hb1 : ∑ i ∈ s.filter (fun i => ‖a i‖ ≤ Real.sqrt r), Real.log (1 + r / ‖a i‖)
      ≤ (divisorIdxCount a (Real.sqrt r) : ℝ) * Real.log (1 + r / m) := by
    have hterm : ∀ i ∈ s.filter (fun i => ‖a i‖ ≤ Real.sqrt r),
        Real.log (1 + r / ‖a i‖) ≤ Real.log (1 + r / m) := by
      intro i _
      have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
      refine Real.log_le_log (by positivity) ?_
      have : r / ‖a i‖ ≤ r / m := by
        refine div_le_div_of_nonneg_left (by linarith) hm (hmle i)
      linarith
    have hcard := card_filter_le hloc s (Real.sqrt r)
    have hlognn : 0 ≤ Real.log (1 + r / m) := by
      refine Real.log_nonneg ?_
      have : 0 ≤ r / m := by positivity
      linarith
    calc ∑ i ∈ s.filter (fun i => ‖a i‖ ≤ Real.sqrt r), Real.log (1 + r / ‖a i‖)
        ≤ ∑ _i ∈ s.filter (fun i => ‖a i‖ ≤ Real.sqrt r), Real.log (1 + r / m) :=
          Finset.sum_le_sum hterm
      _ = ((s.filter (fun i => ‖a i‖ ≤ Real.sqrt r)).card : ℝ) * Real.log (1 + r / m) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (divisorIdxCount a (Real.sqrt r) : ℝ) * Real.log (1 + r / m) :=
          mul_le_mul_of_nonneg_right hcard hlognn
  -- bucket two
  have hb2 : ∑ i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
      (fun i => ‖a i‖ ≤ r ^ 2), Real.log (1 + r / ‖a i‖)
      ≤ (divisorIdxCount a (r ^ 2) : ℝ) * Real.log (1 + Real.sqrt r) := by
    have hterm : ∀ i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
        (fun i => ‖a i‖ ≤ r ^ 2),
        Real.log (1 + r / ‖a i‖) ≤ Real.log (1 + Real.sqrt r) := by
      intro i hi
      simp only [Finset.mem_filter, not_le] at hi
      have hgt : Real.sqrt r < ‖a i‖ := hi.1.2
      have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (by linarith)
      refine Real.log_le_log (by positivity) ?_
      have hle : r / ‖a i‖ ≤ Real.sqrt r := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖a i‖)]
        calc r = Real.sqrt r * Real.sqrt r := hsq.symm
          _ ≤ Real.sqrt r * ‖a i‖ := by nlinarith
      linarith
    have hcard : (((s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
        (fun i => ‖a i‖ ≤ r ^ 2)).card : ℝ) ≤ (divisorIdxCount a (r ^ 2) : ℝ) := by
      have hsub : (↑((s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
          (fun i => ‖a i‖ ≤ r ^ 2)) : Set ι) ⊆ {i : ι | ‖a i‖ ≤ r ^ 2} := by
        intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi
        exact hi.2
      have h1 : ((s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
          (fun i => ‖a i‖ ≤ r ^ 2)).card
          = (↑((s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
              (fun i => ‖a i‖ ≤ r ^ 2)) : Set ι).ncard := (Set.ncard_coe_finset _).symm
      have h2 := Set.ncard_le_ncard hsub (hloc (r ^ 2))
      rw [h1]
      exact_mod_cast h2
    have hlognn : 0 ≤ Real.log (1 + Real.sqrt r) := by
      refine Real.log_nonneg ?_
      have : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
      linarith
    calc ∑ i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
          (fun i => ‖a i‖ ≤ r ^ 2), Real.log (1 + r / ‖a i‖)
        ≤ ∑ _i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
            (fun i => ‖a i‖ ≤ r ^ 2), Real.log (1 + Real.sqrt r) := Finset.sum_le_sum hterm
      _ = (((s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
            (fun i => ‖a i‖ ≤ r ^ 2)).card : ℝ) * Real.log (1 + Real.sqrt r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (divisorIdxCount a (r ^ 2) : ℝ) * Real.log (1 + Real.sqrt r) :=
          mul_le_mul_of_nonneg_right hcard hlognn
  -- bucket three
  have hb3 : ∑ i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
      (fun i => ¬ (‖a i‖ ≤ r ^ 2)), Real.log (1 + r / ‖a i‖)
      ≤ ∑' i : ι, ‖a i‖ ^ (-(1 / 2) : ℝ) := by
    have hterm : ∀ i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
        (fun i => ¬ (‖a i‖ ≤ r ^ 2)),
        Real.log (1 + r / ‖a i‖) ≤ ‖a i‖ ^ (-(1 / 2) : ℝ) := by
      intro i hi
      simp only [Finset.mem_filter, not_le] at hi
      have hgt : r ^ 2 < ‖a i‖ := hi.2
      have hpos : (0 : ℝ) < ‖a i‖ := by nlinarith
      have hlog : Real.log (1 + r / ‖a i‖) ≤ r / ‖a i‖ := by
        have := Real.log_le_sub_one_of_pos (x := 1 + r / ‖a i‖) (by positivity)
        linarith
      have hsqrtle : r ≤ ‖a i‖ ^ ((1 / 2) : ℝ) := by
        have h1 : (r ^ 2 : ℝ) ^ ((1 / 2) : ℝ) ≤ ‖a i‖ ^ ((1 / 2) : ℝ) :=
          Real.rpow_le_rpow (by positivity) hgt.le (by norm_num)
        have h2 : (r ^ 2 : ℝ) ^ ((1 / 2) : ℝ) = r := by
          rw [← Real.rpow_natCast r 2, ← Real.rpow_mul (by linarith)]
          norm_num
        rwa [h2] at h1
      have hinvpow : ‖a i‖ ^ (-(1 / 2) : ℝ) = (‖a i‖ ^ ((1 / 2) : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hpos)]
      have hprod : ‖a i‖ ^ ((1 / 2) : ℝ) * ‖a i‖ ^ ((1 / 2) : ℝ) = ‖a i‖ := by
        rw [← Real.rpow_add hpos]
        norm_num
      have hsp : (0 : ℝ) < ‖a i‖ ^ ((1 / 2) : ℝ) := Real.rpow_pos_of_pos hpos _
      have hcalc : (‖a i‖ ^ ((1 / 2) : ℝ))⁻¹ * ‖a i‖ = ‖a i‖ ^ ((1 / 2) : ℝ) := by
        rw [inv_mul_eq_iff_eq_mul₀ hsp.ne']
        exact hprod.symm
      have hkey : r / ‖a i‖ ≤ ‖a i‖ ^ (-(1 / 2) : ℝ) := by
        rw [hinvpow, div_le_iff₀ hpos, hcalc]
        exact hsqrtle
      linarith
    have hnnhalf : ∀ i : ι, 0 ≤ ‖a i‖ ^ (-(1 / 2) : ℝ) := fun i =>
      Real.rpow_nonneg (norm_nonneg _) _
    calc ∑ i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
          (fun i => ¬ (‖a i‖ ≤ r ^ 2)), Real.log (1 + r / ‖a i‖)
        ≤ ∑ i ∈ (s.filter (fun i => ¬ (‖a i‖ ≤ Real.sqrt r))).filter
            (fun i => ¬ (‖a i‖ ≤ r ^ 2)), ‖a i‖ ^ (-(1 / 2) : ℝ) := Finset.sum_le_sum hterm
      _ ≤ ∑' i : ι, ‖a i‖ ^ (-(1 / 2) : ℝ) :=
          hhalf.sum_le_tsum _ (fun i _ => hnnhalf i)
  linarith [hsplit1, hsplit2]

end GaloisForLFunctions.CountableDivisor

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

/-- **The converse direction.**  A sublogarithmic divisor makes the genus-zero canonical product
grow at most like `o((log r)²)`. -/
theorem logSum_isLittleO_sq {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hloc : LocallyFiniteDivisor a) (hden : SublogDensityIdx a) :
    (fun r : ℝ => ∑' i : ι, Real.log (1 + r / ‖a i‖)) =o[atTop]
      fun r : ℝ => (Real.log r) ^ 2 := by
  obtain ⟨m, hm, hmle⟩ := exists_pos_lower_bound hane hloc
  set C : ℝ := ∑' i : ι, ‖a i‖ ^ (-(1 / 2) : ℝ) with hCdef
  have hCnn : 0 ≤ C := tsum_nonneg (fun i => Real.rpow_nonneg (norm_nonneg _) _)
  set K₁ : ℝ := Real.log (1 + 1 / m) with hK₁def
  rw [isLittleO_iff]
  intro c hc
  set ε : ℝ := c / 3 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (eventually_count_le hden hε)
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
  have hRR₀ : R₀ ≤ R := le_max_left _ _
  set K₂ : ℝ := (ε / 2) * K₁ + 2 * ε * Real.log 2 with hK₂def
  set D : ℝ := |K₂| + C with hDdef
  have hDnn : 0 ≤ D := by positivity
  have hlogtend : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (R ^ 2), eventually_ge_atTop (1 : ℝ),
    hlogtend.eventually_ge_atTop (max 1 (D / (3 * ε / 2)))] with r hrR hr1 hlogr
  have hLnn : (1 : ℝ) ≤ Real.log r := le_trans (le_max_left _ _) hlogr
  have hL2 : D / (3 * ε / 2) ≤ Real.log r := le_trans (le_max_right _ _) hlogr
  have hrpos : (0 : ℝ) < r := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt r := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hr1
  have hsqrtR : R ≤ Real.sqrt r := by
    rw [show R = Real.sqrt (R ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hrR
  have hrR' : R ≤ r := by nlinarith
  -- the two counting bounds
  have hcount1 : (divisorIdxCount a (Real.sqrt r) : ℝ) ≤ (ε / 2) * Real.log r := by
    have h := hR₀ (Real.sqrt r) (le_trans hRR₀ hsqrtR)
    rw [Real.log_sqrt (by linarith)] at h
    linarith
  have hcount2 : (divisorIdxCount a (r ^ 2) : ℝ) ≤ 2 * ε * Real.log r := by
    have hrr : R₀ ≤ r ^ 2 := by nlinarith
    have h := hR₀ (r ^ 2) hrr
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  -- the two logarithmic factors
  have hlog1 : Real.log (1 + r / m) ≤ Real.log r + K₁ := by
    have hle : 1 + r / m ≤ r * (1 + 1 / m) := by
      have : r / m = r * (1 / m) := by ring
      rw [this]
      nlinarith [mul_pos hrpos (by positivity : (0:ℝ) < 1 / m)]
    calc Real.log (1 + r / m) ≤ Real.log (r * (1 + 1 / m)) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log r + K₁ := by
          rw [Real.log_mul (by linarith) (by positivity), hK₁def]
  have hlog2 : Real.log (1 + Real.sqrt r) ≤ Real.log 2 + Real.log r / 2 := by
    have hle : 1 + Real.sqrt r ≤ 2 * Real.sqrt r := by linarith
    calc Real.log (1 + Real.sqrt r) ≤ Real.log (2 * Real.sqrt r) :=
          Real.log_le_log (by linarith) hle
      _ = Real.log 2 + Real.log r / 2 := by
          rw [Real.log_mul (by norm_num) (by linarith), Real.log_sqrt (by linarith)]
  -- nonnegativity of the factors
  have hlognn1 : 0 ≤ Real.log (1 + r / m) := by
    refine Real.log_nonneg ?_
    have : 0 ≤ r / m := by positivity
    linarith
  have hlognn2 : 0 ≤ Real.log (1 + Real.sqrt r) := by
    refine Real.log_nonneg ?_
    linarith
  have hA : (divisorIdxCount a (Real.sqrt r) : ℝ) * Real.log (1 + r / m)
      ≤ ((ε / 2) * Real.log r) * (Real.log r + K₁) :=
    mul_le_mul hcount1 hlog1 hlognn1 (by positivity)
  have hB : (divisorIdxCount a (r ^ 2) : ℝ) * Real.log (1 + Real.sqrt r)
      ≤ (2 * ε * Real.log r) * (Real.log 2 + Real.log r / 2) :=
    mul_le_mul hcount2 hlog2 hlognn2 (by positivity)
  have hmain := tsum_log_le hane hloc hden hm hmle hr1
  have hnn : 0 ≤ ∑' i : ι, Real.log (1 + r / ‖a i‖) := by
    refine tsum_nonneg (fun i => ?_)
    refine Real.log_nonneg ?_
    have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
    have : 0 ≤ r / ‖a i‖ := by positivity
    linarith
  -- the quadratic absorption
  have habs : K₂ * Real.log r + C ≤ (3 * ε / 2) * (Real.log r) ^ 2 := by
    have hstep : D ≤ (3 * ε / 2) * Real.log r := by
      rw [div_le_iff₀ (by positivity)] at hL2
      linarith
    nlinarith [abs_nonneg K₂, le_abs_self K₂]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.log r) ^ 2)]
  nlinarith [hmain, hA, hB, habs]

end GaloisForLFunctions.CountableDivisor

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

/-- The logarithmic sum is monotone in the radius. -/
theorem tsum_log_mono {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hinv : Summable (fun i => ‖a i‖⁻¹)) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    ∑' i : ι, Real.log (1 + r / ‖a i‖) ≤ ∑' i : ι, Real.log (1 + s / ‖a i‖) := by
  refine Summable.tsum_le_tsum (fun i => ?_) (summable_logOnePlusIdx hane hinv hr)
    (summable_logOnePlusIdx hane hinv (le_trans hr hrs))
  have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
  refine Real.log_le_log (by positivity) ?_
  have : r / ‖a i‖ ≤ s / ‖a i‖ := by
    exact div_le_div_of_nonneg_right hrs hpos.le
  linarith

/-- **The converse direction of the quadratic-subtype equivalence.**  The genus-zero canonical
product over a locally finite divisor of sublogarithmic density has `log M(r) = o((log r)²)`. -/
theorem quadraticSubtypeZero_genusZeroProductIdx {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hloc : LocallyFiniteDivisor a) (hden : SublogDensityIdx a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r →
      Real.log ‖genusZeroProductIdx a z‖ ≤ ε * (Real.log r) ^ 2 := by
  have hinv := summable_inv_norm_idx hloc hden
  have hlo := logSum_isLittleO_sq hane hloc hden
  have hev := (isLittleO_iff.mp hlo) hε
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with r hr hr0 z hz
  have h1 : Real.log ‖genusZeroProductIdx a z‖ ≤ ∑' i : ι, Real.log (1 + ‖z‖ / ‖a i‖) :=
    log_norm_genusZeroProductIdx_le hane hinv z
  have h2 : ∑' i : ι, Real.log (1 + ‖z‖ / ‖a i‖) ≤ ∑' i : ι, Real.log (1 + r / ‖a i‖) :=
    tsum_log_mono hane hinv (norm_nonneg z) hz
  have hnn : 0 ≤ ∑' i : ι, Real.log (1 + r / ‖a i‖) := by
    refine tsum_nonneg (fun i => ?_)
    refine Real.log_nonneg ?_
    have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
    have : 0 ≤ r / ‖a i‖ := by positivity
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.log r) ^ 2)] at hr
  linarith

end GaloisForLFunctions.CountableDivisor

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

theorem summable_norm_sub_one {a : ι → ℂ} (hinv : Summable (fun i => ‖a i‖⁻¹)) (z : ℂ) :
    Summable (fun i : ι => ‖(1 - z / a i) - 1‖) := by
  refine (hinv.mul_left ‖z‖).congr (fun i => ?_)
  rw [show (1 - z / a i) - 1 = -(z / a i) by ring, norm_neg, norm_div, div_eq_mul_inv]

theorem genusZeroProductIdx_hasProdLocallyUniformlyOn {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hinv : Summable (fun i => ‖a i‖⁻¹)) :
    HasProdLocallyUniformlyOn (fun (i : ι) (z : ℂ) => 1 - z / a i)
      (genusZeroProductIdx a) Set.univ := by
  have hball : ∀ S : ℝ, 0 < S →
      HasProdLocallyUniformlyOn (fun (i : ι) (z : ℂ) => 1 - z / a i)
        (genusZeroProductIdx a) (Metric.ball 0 S) := by
    intro S hSpos
    set f : ι → ℂ → ℂ := fun i z => -(z / a i) with hf
    have hu : Summable (fun i : ι => S * ‖a i‖⁻¹) := hinv.mul_left S
    have hbound : ∀ᶠ i in cofinite, ∀ z ∈ Metric.ball (0 : ℂ) S,
        ‖f i z‖ ≤ S * ‖a i‖⁻¹ := by
      refine Eventually.of_forall (fun i z hz => ?_)
      have hzS : ‖z‖ < S := mem_ball_zero_iff.mp hz
      have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
      simp only [hf, norm_neg, norm_div]
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hzS.le (by positivity)
    have hcts : ∀ i : ι, ContinuousOn (f i) (Metric.ball (0 : ℂ) S) := by
      intro i
      have : Continuous (f i) := by simp only [hf]; fun_prop
      exact this.continuousOn
    have hpl := Summable.hasProdLocallyUniformlyOn_one_add isOpen_ball hu hbound hcts
    convert hpl using 1
    · ext i z
      simp only [hf]
      ring
    · funext z
      exact tprod_congr (fun i => by simp only [hf]; ring)
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hKcompact
  obtain ⟨S, hSpos, hKS⟩ : ∃ S : ℝ, 0 < S ∧ K ⊆ Metric.ball (0 : ℂ) S :=
    hKcompact.isBounded.subset_ball_lt 0 0
  exact ((hball S hSpos).mono hKS).hasProdUniformlyOn_of_isCompact hKcompact

theorem genusZeroProductIdx_analytic {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hinv : Summable (fun i => ‖a i‖⁻¹)) :
    AnalyticOnNhd ℂ (genusZeroProductIdx a) Set.univ := by
  have hpl := genusZeroProductIdx_hasProdLocallyUniformlyOn hane hinv
  have hdiff : ∀ᶠ s : Finset ι in atTop,
      DifferentiableOn ℂ (fun z => ∏ i ∈ s, (1 - z / a i)) Set.univ :=
    Eventually.of_forall fun s => (Differentiable.fun_finsetProd fun i _ => by
      fun_prop).differentiableOn
  exact (show TendstoLocallyUniformlyOn
      (fun s : Finset ι => fun z => ∏ i ∈ s, (1 - z / a i))
      (genusZeroProductIdx a) atTop Set.univ from hpl).differentiableOn
        hdiff isOpen_univ |>.analyticOnNhd isOpen_univ

theorem genusZeroProductIdx_ne_zero {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hinv : Summable (fun i => ‖a i‖⁻¹)) {z : ℂ} (hz : ∀ i, z ≠ a i) :
    genusZeroProductIdx a z ≠ 0 := by
  rw [genusZeroProductIdx]
  set f : ι → ℂ := fun i => (1 - z / a i) - 1 with hf
  have hfnorm : Summable (fun i => ‖f i‖) := summable_norm_sub_one hinv z
  have hfne : ∀ i, 1 + f i ≠ 0 := by
    intro i
    simp only [hf]
    rw [show 1 + ((1 - z / a i) - 1) = 1 - z / a i by ring, sub_ne_zero]
    intro h
    exact hz i ((div_eq_one_iff_eq (hane i)).mp h.symm)
  have heq : (fun i => 1 + f i) = (fun i => 1 - z / a i) := by
    funext i
    simp only [hf]
    ring
  rw [← heq]
  exact tprod_one_add_ne_zero_of_summable hfne hfnorm

/-- The multiplicity fiber over a divisor point is finite. -/
theorem finite_fiber {a : ι → ℂ} (hloc : LocallyFiniteDivisor a) (w : ℂ) :
    {i : ι | a i = w}.Finite := by
  refine (hloc ‖w‖).subset (fun i hi => ?_)
  simp only [Set.mem_setOf_eq] at hi ⊢
  rw [hi]

end GaloisForLFunctions.CountableDivisor

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem genusZeroProductIdx_split {a : ι → ℂ} (hinv : Summable (fun i => ‖a i‖⁻¹))
    (s : Set ι) (z : ℂ) :
    (∏' x : s, (1 - z / a x)) * (∏' x : ↑(sᶜ), (1 - z / a x)) = genusZeroProductIdx a z := by
  have h1 : Multipliable (fun x : s => 1 - z / a x.1) :=
    multipliable_genusZeroIdx (a := fun x : s => a x.1) (hinv.subtype (· ∈ s)) z
  have h2 : Multipliable (fun x : ↑(sᶜ) => 1 - z / a x.1) :=
    multipliable_genusZeroIdx (a := fun x : ↑(sᶜ) => a x.1) (hinv.subtype (· ∈ sᶜ)) z
  exact Multipliable.tprod_mul_tprod_compl (f := fun i : ι => 1 - z / a i) h1 h2

theorem tprod_fiber_eq {a : ι → ℂ} (hloc : LocallyFiniteDivisor a) (w z : ℂ) :
    (∏' x : ({i : ι | a i = w} : Set ι), (1 - z / a x))
      = (1 - z / w) ^ ({i : ι | a i = w}.ncard) := by
  haveI : Fintype ({i : ι | a i = w} : Set ι) := (finite_fiber hloc w).fintype
  have hcongr : ∀ x : ({i : ι | a i = w} : Set ι), (1 - z / a x) = 1 - z / w := by
    intro x
    rw [x.2]
  rw [tprod_congr hcongr, tprod_fintype, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem genusZeroProductIdx_eq_pow_mul {a : ι → ℂ} (hinv : Summable (fun i => ‖a i‖⁻¹))
    (hloc : LocallyFiniteDivisor a) (w : ℂ) :
    genusZeroProductIdx a
      = (fun z : ℂ => (1 - z / w) ^ ({i : ι | a i = w}.ncard))
        * genusZeroProductIdx (fun x : ↑(({i : ι | a i = w} : Set ι)ᶜ) => a x.1) := by
  funext z
  rw [Pi.mul_apply, ← genusZeroProductIdx_split hinv {i : ι | a i = w} z,
    tprod_fiber_eq hloc w z]
  rfl

theorem analyticOrderAt_oneSubDiv {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (fun z : ℂ => 1 - z / w) w = 1 := by
  have han : AnalyticAt ℂ (fun z : ℂ => 1 - z / w) w := by fun_prop
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
  · show (1 : ℂ) - w / w = 0
    rw [div_self hw]
    ring
  · have hd : HasDerivAt (fun z : ℂ => 1 - z / w) (-(1 / w)) w := by
      have hbase : HasDerivAt (fun z : ℂ => z / w) (1 / w) w := by
        simpa using (hasDerivAt_id w).div_const w
      simpa using hbase.const_sub 1
    rw [hd.deriv]
    simp [hw]

/-- **The divisor of the genus-zero product.**  Its order at every nonzero point is exactly the
multiplicity of that point in the index family. -/
theorem analyticOrderAt_genusZeroProductIdx {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hloc : LocallyFiniteDivisor a) (hinv : Summable (fun i => ‖a i‖⁻¹)) {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (genusZeroProductIdx a) w = (({i : ι | a i = w}.ncard : ℕ) : ℕ∞) := by
  set F : Set ι := {i : ι | a i = w} with hF
  set T : ↑(Fᶜ) → ℂ := fun x => a x.1 with hT
  have hTane : ∀ x : ↑(Fᶜ), T x ≠ 0 := fun x => hane x.1
  have hTinv : Summable (fun x : ↑(Fᶜ) => ‖T x‖⁻¹) := hinv.subtype (· ∈ Fᶜ)
  have hTne : ∀ x : ↑(Fᶜ), w ≠ T x := by
    intro x
    have hx := x.2
    simp only [hF, Set.mem_compl_iff, Set.mem_setOf_eq] at hx
    exact fun h => hx h.symm
  have hQne : genusZeroProductIdx T w ≠ 0 := genusZeroProductIdx_ne_zero hTane hTinv hTne
  have hQan : AnalyticAt ℂ (genusZeroProductIdx T) w :=
    genusZeroProductIdx_analytic hTane hTinv w (Set.mem_univ _)
  have hGan : AnalyticAt ℂ (fun z : ℂ => (1 - z / w) ^ (F.ncard)) w := by
    have hbase : AnalyticAt ℂ (fun z : ℂ => 1 - z / w) w := by fun_prop
    exact hbase.pow _
  have hsplit := genusZeroProductIdx_eq_pow_mul hinv hloc w
  rw [hsplit, analyticOrderAt_mul hGan hQan, hQan.analyticOrderAt_eq_zero.mpr hQne, add_zero]
  have hpow : (fun z : ℂ => (1 - z / w) ^ (F.ncard))
      = (fun z : ℂ => 1 - z / w) ^ (F.ncard) := by
    funext z
    rw [Pi.pow_apply]
  rw [hpow, analyticOrderAt_pow (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 - z / w) w),
    analyticOrderAt_oneSubDiv hw]
  simp

end GaloisForLFunctions.CountableDivisor
