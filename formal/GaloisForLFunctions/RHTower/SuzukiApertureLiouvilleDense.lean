import GaloisForLFunctions.RHTower.SuzukiAperturePolynomialType
import GaloisForLFunctions.RHTower.TwoDilationDivisorMetric

/-!
# Logarithmic-Liouville apertures are dense

Almost every aperture has finite logarithmic type, but not every one.  For each depth `k` the
apertures carrying an event of logarithmic depth `k` from some valuation of `ℓ¹` length at least `k`
form an open set, and that set is dense as soon as the valuation lattice is dense on the line: only
finitely many valuations are short, so a dense lattice still approaches every interval with a long
valuation, and a point slightly displaced from such a lattice centre is a nonresonant aperture with
an arbitrarily deep event.

The countable intersection over the depths is therefore comeagre, hence dense.  Every aperture in it
has infinite logarithmic type, so no logarithmic bound on the event clock can hold for all apertures.

In rank at least two the valuation lattice is dense: two distinct prime logarithms have irrational
ratio, so the group they generate is not cyclic.
-/

open Set Filter Topology

namespace RHTower

noncomputable section

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ## Infinite logarithmic type -/

/-- `(3)` at the opposite end of the scale: an event clock of **infinite** logarithmic type exceeds
every multiple of the logarithmic shell scale for infinitely many valuations. -/
def HasInfiniteLogType (τ : (P → ℤ) → ℝ) : Prop :=
  ∀ M : ℝ, ∃ᶠ ν in Filter.cofinite, M * Real.log (2 + (orbitLength ν : ℝ)) ≤ τ ν

omit [DecidableEq P] in
/-- Infinite logarithmic type excludes every logarithmic bound on the clock. -/
theorem not_logType_of_hasInfiniteLogType {τ : (P → ℤ) → ℝ} (h : HasInfiniteLogType τ) :
    ¬ ∃ Q : ℝ, ∀ᶠ ν in Filter.cofinite, τ ν ≤ Q * Real.log (2 + (orbitLength ν : ℝ)) := by
  rintro ⟨Q, hQ⟩
  obtain ⟨ν, h1, h2⟩ := ((h (Q + 1)).and_eventually hQ).exists
  have hlog : 0 < Real.log (2 + (orbitLength ν : ℝ)) := by
    refine Real.log_pos ?_
    have : (0 : ℝ) ≤ (orbitLength ν : ℝ) := by positivity
    linarith
  nlinarith [h1, h2, hlog]

/-! ## The comeagre set of deep apertures -/

/-- The apertures carrying an event of logarithmic depth `k` from a valuation of `ℓ¹` length at
least `k`. -/
def apertureLiouvilleStage (ℓ : (P → ℤ) → ℝ) (k : ℕ) : Set ℝ :=
  ⋃ ν : P → ℤ, ⋃ _ : k ≤ orbitLength ν,
    {a : ℝ | 0 < |2 * a - ℓ ν| ∧ |2 * a - ℓ ν| < (2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ))}

omit [DecidableEq P] in
theorem isOpen_apertureLiouvilleStage (ℓ : (P → ℤ) → ℝ) (k : ℕ) :
    IsOpen (apertureLiouvilleStage ℓ k) := by
  refine isOpen_iUnion fun ν => isOpen_iUnion fun _ => ?_
  have hcont : Continuous fun a : ℝ => |2 * a - ℓ ν| := by fun_prop
  exact (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)

/-- **Each depth stage is dense** once the valuation lattice is dense on the line. -/
theorem dense_apertureLiouvilleStage {ℓ : (P → ℤ) → ℝ} (hℓ : Dense (Set.range ℓ)) (k : ℕ) :
    Dense (apertureLiouvilleStage ℓ k) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  have hWopen : IsOpen ((fun t : ℝ => t / 2) ⁻¹' U) := hU.preimage (by fun_prop)
  have hWne : ((fun t : ℝ => t / 2) ⁻¹' U).Nonempty := by
    obtain ⟨z, hz⟩ := hUne
    refine ⟨2 * z, ?_⟩
    simp only [Set.mem_preimage]
    rw [show 2 * z / 2 = z by ring]
    exact hz
  have hfin : (ℓ '' {ν : P → ℤ | orbitLength ν < k}).Finite :=
    (finite_orbitLength_lt k).image ℓ
  obtain ⟨y, hyW, hyr, hynot⟩ :
      ∃ y : ℝ, y ∈ (fun t : ℝ => t / 2) ⁻¹' U ∧ y ∈ Set.range ℓ
        ∧ y ∉ ℓ '' {ν : P → ℤ | orbitLength ν < k} := by
    obtain ⟨y, hy1, hy2⟩ :=
      (dense_iff_inter_open.mp (hℓ.sdiff_finite hfin)) _ hWopen hWne
    exact ⟨y, hy1, hy2.1, hy2.2⟩
  obtain ⟨ν, hν⟩ := hyr
  subst hν
  have hk : k ≤ orbitLength ν := by
    by_contra hcon
    exact hynot ⟨ν, Nat.lt_of_not_le hcon, rfl⟩
  have hxU : ℓ ν / 2 ∈ U := hyW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hxU
  have hr : (0 : ℝ) < (2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨ℓ ν / 2 + min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) / 2, ?_, ?_⟩
  · refine hball ?_
    have hδ : 0 < min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) :=
      lt_min (by linarith) (by linarith)
    have hδe : min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) ≤ ε / 2 :=
      min_le_left _ _
    rw [Metric.mem_ball, Real.dist_eq,
      show ℓ ν / 2 + min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) / 2 - ℓ ν / 2
        = min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) / 2 by ring,
      abs_of_pos (by linarith)]
    linarith
  · have hδ : 0 < min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) :=
      lt_min (by linarith) (by linarith)
    have hδr : min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2)
        ≤ (2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2 := min_le_right _ _
    refine Set.mem_iUnion.mpr ⟨ν, Set.mem_iUnion.mpr ⟨hk, ?_⟩⟩
    have hval : 2 * (ℓ ν / 2 + min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) / 2)
        - ℓ ν = min (ε / 2) ((2 + (orbitLength ν : ℝ)) ^ (-(k : ℝ)) / 2) := by ring
    simp only [Set.mem_setOf_eq, hval, abs_of_pos hδ]
    exact ⟨hδ, by linarith⟩

omit [DecidableEq P] in
/-- Every aperture in the comeagre intersection has infinite logarithmic type. -/
theorem hasInfiniteLogType_of_mem_iInter {ℓ : (P → ℤ) → ℝ} {a : ℝ}
    (ha : a ∈ ⋂ k : ℕ, apertureLiouvilleStage ℓ k) :
    HasInfiniteLogType (apertureEventClock ℓ a) := by
  intro M
  rw [Filter.frequently_cofinite_iff_infinite]
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := (hfin.image orbitLength).bddAbove
  have hak : a ∈ apertureLiouvilleStage ℓ (max (N + 1) (⌈M⌉₊ + 1)) :=
    Set.mem_iInter.mp ha _
  simp only [apertureLiouvilleStage, Set.mem_iUnion, Set.mem_setOf_eq] at hak
  obtain ⟨ν, hlen, h0, h1⟩ := hak
  have hpos : (0 : ℝ) < 2 + (orbitLength ν : ℝ) := by positivity
  have hlogpos : 0 < Real.log (2 + (orbitLength ν : ℝ)) := by
    refine Real.log_pos ?_
    have : (0 : ℝ) ≤ (orbitLength ν : ℝ) := by positivity
    linarith
  have hlt := Real.log_lt_log h0 h1
  rw [Real.log_rpow hpos] at hlt
  have hMk : M ≤ ((max (N + 1) (⌈M⌉₊ + 1) : ℕ) : ℝ) := by
    refine le_trans (Nat.le_ceil M) ?_
    have hle : ⌈M⌉₊ ≤ max (N + 1) (⌈M⌉₊ + 1) := le_trans (Nat.le_succ _) (Nat.le_max_right _ _)
    exact_mod_cast hle
  have hclock : M * Real.log (2 + (orbitLength ν : ℝ)) ≤ apertureEventClock ℓ a ν := by
    rw [apertureEventClock]
    refine le_trans ?_ (le_max_right _ _)
    nlinarith [hlt, hMk, hlogpos]
  have hle : orbitLength ν ≤ N := hN ⟨ν, hclock, rfl⟩
  have hge : N + 1 ≤ orbitLength ν := le_trans (Nat.le_max_left _ _) hlen
  omega

/-- **§6: logarithmic-Liouville apertures are dense.**  The polynomial-carrier class is of full
measure but not all apertures. -/
theorem dense_hasInfiniteLogType {ℓ : (P → ℤ) → ℝ} (hℓ : Dense (Set.range ℓ)) :
    Dense {a : ℝ | HasInfiniteLogType (apertureEventClock ℓ a)} := by
  have hres : (⋂ k : ℕ, apertureLiouvilleStage ℓ k) ∈ residual ℝ :=
    countable_iInter_mem.mpr fun k =>
      residual_of_dense_open (isOpen_apertureLiouvilleStage ℓ k)
        (dense_apertureLiouvilleStage hℓ k)
  exact Dense.mono (fun a ha => hasInfiniteLogType_of_mem_iInter ha)
    (dense_of_mem_residual hres)

/-! ## The prime-log lattice is dense in rank at least two -/

/-- Distinct primes are multiplicatively independent. -/
theorem prime_pow_ne_prime_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m n : ℕ) (hm : 0 < m) (_hn : 0 < n) : p ^ m ≠ q ^ n := by
  intro hcon
  have hdvd : p ∣ q ^ n := by
    rw [← hcon]
    exact dvd_pow_self p hm.ne'
  have := hp.dvd_of_dvd_pow hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp this)

/-- **The prime-log valuation lattice is dense in rank at least two.**  Two distinct prime
logarithms have irrational ratio, so the subgroup they generate is not cyclic. -/
theorem dense_range_primeLogValuation (pr : P → ℕ) (hpr : ∀ p, (pr p).Prime)
    (hinj : Function.Injective pr) {p₀ p₁ : P} (hne : p₀ ≠ p₁) :
    Dense (Set.range fun ν : P → ℤ => ∑ p, (ν p : ℝ) * Real.log (pr p)) := by
  have h0 : 2 ≤ pr p₀ := (hpr p₀).two_le
  have h1 : 2 ≤ pr p₁ := (hpr p₁).two_le
  have hy0 : Real.log (pr p₀) ≠ 0 := by
    refine ne_of_gt (Real.log_pos ?_)
    exact_mod_cast lt_of_lt_of_le one_lt_two h0
  have hirr : Irrational (Real.log (pr p₁) / Real.log (pr p₀)) :=
    irrational_log_div_log h1 h0
      (prime_pow_ne_prime_pow (hpr p₁) (hpr p₀) fun h => hne (hinj h).symm)
  refine Dense.mono ?_ (dense_closure_pair_of_irrational hy0 hirr)
  intro z hz
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hz
  refine ⟨fun p => if p = p₁ then m else if p = p₀ then n else 0, ?_⟩
  have hsub : ∑ p, ((if p = p₁ then (m : ℤ) else if p = p₀ then n else 0 : ℤ) : ℝ)
      * Real.log (pr p)
      = ∑ p ∈ ({p₀, p₁} : Finset P),
        ((if p = p₁ then (m : ℤ) else if p = p₀ then n else 0 : ℤ) : ℝ) * Real.log (pr p) := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_).symm
    have hp₀ : p ≠ p₀ := fun h => hp (by simp [h])
    have hp₁ : p ≠ p₁ := fun h => hp (by simp [h])
    simp [hp₀, hp₁]
  show ∑ p, ((if p = p₁ then (m : ℤ) else if p = p₀ then n else 0 : ℤ) : ℝ)
      * Real.log (pr p) = z
  rw [hsub, Finset.sum_pair hne]
  simp only [if_neg hne]
  rw [← hmn, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring

/-- **The full §6 statement.**  In rank at least two, the apertures of infinite logarithmic type are
dense: the finite-type class is of full measure but is not everything. -/
theorem dense_hasInfiniteLogType_primeLogValuation (pr : P → ℕ) (hpr : ∀ p, (pr p).Prime)
    (hinj : Function.Injective pr) {p₀ p₁ : P} (hne : p₀ ≠ p₁) :
    Dense {a : ℝ |
      HasInfiniteLogType
        (apertureEventClock (fun ν : P → ℤ => ∑ p, (ν p : ℝ) * Real.log (pr p)) a)} :=
  dense_hasInfiniteLogType (dense_range_primeLogValuation pr hpr hinj hne)

end

end RHTower
