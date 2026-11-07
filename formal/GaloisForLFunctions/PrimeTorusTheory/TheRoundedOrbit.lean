import GaloisForLFunctions.PrimeTorusTheory.TheDiagonalRange

/-!
# The rounded orbit: diagonal data cannot exclude a return

Round every `log p` to the nearest point of the lattice `(2π/T)ℤ`. The result is a phase system with the same weights and
steps within `π/T` of the true ones.

* **It returns exactly at `T`** (`roundedSystem_column_eq_size`): every phase is `1` there. The column reaches its size.
* **It agrees with the true orbit up to `cT`** (`abs_rounded_column_sub_le`): the columns differ by at most `S π|t|/T`.
* **Its moments over one period are exactly the diagonal** (`rounded_moment_eq_diagonal`): when `2kπ y^k < T`, products of
  `k` primes `≤ y` keep their identities after rounding, and the period mean of `|P̃|^{2k}` is the Steinhaus moment
  `Σ_{Πu = Πv} A_u A_v`.

So **no theorem using only diagonal moments through `k ≈ log T / log y`, group closure, or the values of the orbit up to time
`cT` can exclude a return at time `T`** (`diagonal_data_cannot_exclude_return`). The rounded system is a one-parameter
subgroup, with the same moments and the same early orbit, and it does return.

**The boundary.** Past the mixing range the rounded system loses unique factorization (`exists_collision`): two distinct
products get the same rounded step. That is exactly where `le_of_aligned` stops applying to it, and exactly what the integers
do not do. Every non-alignment theorem must use `log p` at a resolution finer than `1/T`, through pairs of products past the
diagonal range.
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The nearest lattice index of `log r`. -/
def roundedIndex (T : ℝ) (r : ℕ) : ℤ := round (T * Real.log r / (2 * Real.pi))

/-- The rounded step. -/
def roundedStep (T : ℝ) (r : ℕ) : ℝ := 2 * Real.pi / T * roundedIndex T r

theorem abs_roundedStep_sub_le {T : ℝ} (hT : 0 < T) (r : ℕ) :
    |roundedStep T r - Real.log r| ≤ Real.pi / T := by
  have hpi := Real.pi_pos
  have h := abs_sub_round (T * Real.log r / (2 * Real.pi))
  have e : roundedStep T r - Real.log r =
      -(2 * Real.pi / T * (T * Real.log r / (2 * Real.pi) - roundedIndex T r)) := by
    unfold roundedStep
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / T)]
  have e2 : Real.pi / T = 2 * Real.pi / T * (1 / 2) := by ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The rounded phase system. -/
def roundedSystem (Q : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) (T : ℝ) : PhaseSystem Q where
  step r := roundedStep T r
  weight r := a r
  weight_nonneg r := ha r r.2

variable {Q : Finset ℕ} {a : ℕ → ℝ} {ha : ∀ r ∈ Q, 0 ≤ a r} {T : ℝ}

/-- **The exact return.** All phases of the rounded system are `1` at time `T`. -/
theorem roundedSystem_defect_eq_zero (hT : 0 < T) (n : ℤ) :
    (roundedSystem Q a ha T).defect (n * T) = 0 := by
  rw [PhaseSystem.defect_eq_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  have e : (n : ℝ) * T * (roundedSystem Q a ha T).step r =
      ((n * roundedIndex T r : ℤ) : ℝ) * (2 * Real.pi) := by
    show (n : ℝ) * T * roundedStep T r = _
    unfold roundedStep
    push_cast
    field_simp
  rw [e, Real.cos_int_mul_two_pi]
  simp

theorem roundedSystem_column_eq_size (hT : 0 < T) :
    (roundedSystem Q a ha T).column T = (roundedSystem Q a ha T).size := by
  have h := roundedSystem_defect_eq_zero (Q := Q) (a := a) (ha := ha) hT 1
  simp only [Int.cast_one, one_mul] at h
  unfold PhaseSystem.defect at h
  linarith

/-- **The rounded orbit agrees with the true orbit up to `cT`.** -/
theorem abs_rounded_column_sub_le (hT : 0 < T) (t : ℝ) :
    |(roundedSystem Q a ha T).column t - (primeSystem Q a ha).column t| ≤
      (primeSystem Q a ha).size * (|t| * (Real.pi / T)) := by
  unfold PhaseSystem.column PhaseSystem.size
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hw : 0 ≤ (primeSystem Q a ha).weight r := (primeSystem Q a ha).weight_nonneg r
  have e1 : (roundedSystem Q a ha T).weight r = (primeSystem Q a ha).weight r := rfl
  rw [e1, ← mul_sub, abs_mul, abs_of_nonneg hw]
  refine mul_le_mul_of_nonneg_left ?_ hw
  refine (abs_cos_sub_cos_le _ _).trans ?_
  have e2 : t * (roundedSystem Q a ha T).step r - t * (primeSystem Q a ha).step r =
      t * (roundedStep T r - Real.log (r : ℕ)) := by
    show t * roundedStep T r - t * Real.log (r : ℕ) = _
    ring
  rw [e2, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_roundedStep_sub_le hT r) (abs_nonneg t)

/-- The step of a tuple in the rounded system, on the lattice. -/
theorem rounded_tupleStep {k : ℕ} (u : Fin k → Q) :
    (roundedSystem Q a ha T).tupleStep u =
      2 * Real.pi / T * ((∑ s, roundedIndex T (u s) : ℤ) : ℝ) := by
  unfold PhaseSystem.tupleStep
  push_cast
  rw [Finset.mul_sum]
  rfl

/-- Rounding moves the step of a `k`-tuple by at most `kπ/T`. -/
theorem abs_rounded_tupleStep_sub_le (hQ : ∀ r ∈ Q, r.Prime) (hT : 0 < T) {k : ℕ} (u : Fin k → Q) :
    |(roundedSystem Q a ha T).tupleStep u - Real.log (tupleProd u)| ≤ k * (Real.pi / T) := by
  have e : Real.log (tupleProd u) = ∑ s, Real.log ((u s : Q) : ℕ) := by
    have := primeSystem_tupleStep hQ a ha u
    rw [← this]
    rfl
  rw [e]
  unfold PhaseSystem.tupleStep
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin k))
    (fun s => |(roundedSystem Q a ha T).step (u s) - Real.log ((u s : Q) : ℕ)|) (Real.pi / T)
    fun s _ => abs_roundedStep_sub_le hT _
  simpa [nsmul_eq_mul] using this

/-- Equal products have equal rounded steps: they are permutations. -/
theorem rounded_tupleStep_eq_of_prod_eq (hQ : ∀ r ∈ Q, r.Prime) {k : ℕ} {u v : Fin k → Q}
    (h : tupleProd u = tupleProd v) :
    (roundedSystem Q a ha T).tupleStep u = (roundedSystem Q a ha T).tupleStep v := by
  have hp := perm_of_tupleProd_eq hQ h
  have hsum := (hp.map fun r : ℕ => roundedStep T r).sum_eq
  rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn, List.sum_ofFn] at hsum
  exact hsum

/-- Below the resolution, distinct products keep distinct rounded steps. -/
theorem rounded_tupleStep_ne_of_prod_ne (hQ : ∀ r ∈ Q, r.Prime) (hT : 0 < T) {y k : ℕ} (hy : 1 ≤ y)
    (hyQ : ∀ r ∈ Q, r ≤ y) (hgap : 2 * (k : ℝ) * Real.pi * (y : ℝ) ^ k < T) {u v : Fin k → Q}
    (h : tupleProd u ≠ tupleProd v) :
    (roundedSystem Q a ha T).tupleStep u ≠ (roundedSystem Q a ha T).tupleStep v := by
  intro heq
  have h1 := abs_rounded_tupleStep_sub_le (a := a) (ha := ha) hQ hT u
  have h2 := abs_rounded_tupleStep_sub_le (a := a) (ha := ha) hQ hT v
  rw [heq] at h1
  have hlog : |Real.log (tupleProd u) - Real.log (tupleProd v)| ≤ 2 * k * (Real.pi / T) := by
    have e : Real.log (tupleProd u) - Real.log (tupleProd v) =
        ((roundedSystem Q a ha T).tupleStep v - Real.log (tupleProd v)) -
          ((roundedSystem Q a ha T).tupleStep v - Real.log (tupleProd u)) := by ring
    rw [e]
    have := abs_sub ((roundedSystem Q a ha T).tupleStep v - Real.log (tupleProd v))
      ((roundedSystem Q a ha T).tupleStep v - Real.log (tupleProd u))
    linarith
  have hgapint := HTGeometry.inv_max_le_abs_log_sub_log (tupleProd_pos hQ u) (tupleProd_pos hQ v) h
  have hy' : (0 : ℝ) < (y : ℝ) ^ k := pow_pos (by exact_mod_cast hy) k
  have hmax : ((max (tupleProd u) (tupleProd v) : ℕ) : ℝ) ≤ (y : ℝ) ^ k := by
    exact_mod_cast max_le (tupleProd_le hyQ u) (tupleProd_le hyQ v)
  have hmaxpos : (0 : ℝ) < ((max (tupleProd u) (tupleProd v) : ℕ) : ℝ) := by
    have : 0 < max (tupleProd u) (tupleProd v) := lt_max_of_lt_left (tupleProd_pos hQ u)
    exact_mod_cast this
  have hinv : ((y : ℝ) ^ k)⁻¹ ≤ 2 * k * (Real.pi / T) :=
    (inv_anti₀ hmaxpos hmax).trans (hgapint.trans hlog)
  have h5 : T * ((y : ℝ) ^ k)⁻¹ ≤ 2 * k * Real.pi := by
    calc
      T * ((y : ℝ) ^ k)⁻¹ ≤ T * (2 * k * (Real.pi / T)) := mul_le_mul_of_nonneg_left hinv hT.le
      _ = 2 * k * Real.pi := by field_simp
  rw [← div_eq_mul_inv, div_le_iff₀ hy'] at h5
  linarith

/-- The period mean of a pure cosine on the lattice. -/
theorem integral_cos_lattice (hT : 0 < T) (n : ℤ) :
    ∫ t in (0 : ℝ)..T, Real.cos (t * (2 * Real.pi / T * n)) = if n = 0 then T else 0 := by
  have hpi := Real.pi_pos
  split_ifs with hn
  · subst hn
    simp
  · have hν : 2 * Real.pi / T * (n : ℝ) ≠ 0 := by
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      positivity
    set ν := 2 * Real.pi / T * (n : ℝ) with hνdef
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun t => Real.sin (t * ν) / ν)
        (Real.cos (t * ν)) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => t * ν) ν t := by
        simpa using (hasDerivAt_id' t).mul_const ν
      exact (h2.sin.div_const ν).congr_deriv (by field_simp)
    have hc : Continuous fun t : ℝ => Real.cos (t * ν) := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hc.intervalIntegrable _ _)]
    have e : T * ν = ((2 * n : ℤ) : ℝ) * Real.pi := by
      rw [hνdef]
      push_cast
      field_simp
    rw [e, Real.sin_int_mul_pi]
    simp

open Classical in
/-- The diagonal mass: the pairs of `k`-tuples with equal product. This is the Steinhaus moment. -/
def diagonalMass (Q : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) (k : ℕ) : ℝ :=
  ∑ u : Fin k → Q, ∑ v : Fin k → Q, if tupleProd u = tupleProd v then
    (primeSystem Q a ha).tupleWeight u * (primeSystem Q a ha).tupleWeight v else 0

open Classical in
/-- **The rounded moments are exactly diagonal.** -/
theorem rounded_moment_eq_diagonal (hQ : ∀ r ∈ Q, r.Prime) (hT : 0 < T) {y k : ℕ} (hy : 1 ≤ y)
    (hyQ : ∀ r ∈ Q, r ≤ y) (hgap : 2 * (k : ℝ) * Real.pi * (y : ℝ) ^ k < T) :
    (1 / T) * ∫ t in (0 : ℝ)..T, ‖(roundedSystem Q a ha T).poly t‖ ^ (2 * k) =
      diagonalMass Q a ha k := by
  set S := roundedSystem Q a ha T with hS
  simp_rw [PhaseSystem.norm_poly_pow_eq]
  have hterm : ∀ u v : Fin k → Q, Continuous fun t : ℝ => S.tupleWeight u * S.tupleWeight v *
      Real.cos (t * (S.tupleStep u - S.tupleStep v)) := by
    intro u v
    fun_prop
  have hterm2 : ∀ u : Fin k → Q, Continuous fun t : ℝ => ∑ v : Fin k → Q,
      S.tupleWeight u * S.tupleWeight v * Real.cos (t * (S.tupleStep u - S.tupleStep v)) :=
    fun u => continuous_finsetSum _ fun v _ => hterm u v
  rw [intervalIntegral.integral_finsetSum fun u _ => (hterm2 u).intervalIntegrable _ _,
    Finset.mul_sum]
  unfold diagonalMass
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [intervalIntegral.integral_finsetSum fun v _ => (hterm u v).intervalIntegrable _ _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hlat : S.tupleStep u - S.tupleStep v =
      2 * Real.pi / T * ((∑ s, roundedIndex T (u s) - ∑ s, roundedIndex T (v s) : ℤ) : ℝ) := by
    rw [hS, rounded_tupleStep, rounded_tupleStep]
    push_cast
    ring
  rw [hlat, integral_cos_lattice hT]
  have hw : S.tupleWeight u * S.tupleWeight v =
      (primeSystem Q a ha).tupleWeight u * (primeSystem Q a ha).tupleWeight v := rfl
  rw [hw]
  by_cases hprod : tupleProd u = tupleProd v
  · have hstep := rounded_tupleStep_eq_of_prod_eq (a := a) (ha := ha) (T := T) hQ hprod
    rw [← hS, rounded_tupleStep, rounded_tupleStep] at hstep
    have hne : (2 * Real.pi / T) ≠ 0 := by
      have := Real.pi_pos
      positivity
    have hint := mul_left_cancel₀ hne hstep
    have h0 : ∑ s, roundedIndex T (u s) - ∑ s, roundedIndex T (v s) = 0 := by
      have : ((∑ s, roundedIndex T (u s) : ℤ) : ℝ) = ((∑ s, roundedIndex T (v s) : ℤ) : ℝ) := hint
      have h3 : (∑ s, roundedIndex T (u s) : ℤ) = ∑ s, roundedIndex T (v s) := by exact_mod_cast this
      omega
    rw [if_pos h0, if_pos hprod]
    field_simp
  · have hstep := rounded_tupleStep_ne_of_prod_ne (a := a) (ha := ha) hQ hT hy hyQ hgap hprod
    have h0 : ∑ s, roundedIndex T (u s) - ∑ s, roundedIndex T (v s) ≠ 0 := by
      intro h1
      apply hstep
      rw [← hS, rounded_tupleStep, rounded_tupleStep]
      have : (∑ s, roundedIndex T (u s) : ℤ) = ∑ s, roundedIndex T (v s) := by omega
      rw [this]
    rw [if_neg h0, if_neg hprod]
    simp

open Classical in
/-- **Diagonal data cannot exclude a return.** For every finite set of primes `≤ y` and every `T` there is a phase system
with the same weights and steps within `π/T` of `log p`, with an exact return at `T`, whose `j`-th moments over one period
are exactly diagonal for all `j` with `2jπ y^j < T`. -/
theorem diagonal_data_cannot_exclude_return (hQ : ∀ r ∈ Q, r.Prime) (hT : 0 < T) {y : ℕ}
    (hy : 1 ≤ y) (hyQ : ∀ r ∈ Q, r ≤ y) :
    ∃ S' : PhaseSystem Q,
      (∀ r, S'.weight r = a r) ∧ (∀ r : Q, |S'.step r - Real.log (r : ℕ)| ≤ Real.pi / T) ∧
      S'.column T = ∑ r ∈ Q, a r ∧
      ∀ j : ℕ, 2 * (j : ℝ) * Real.pi * (y : ℝ) ^ j < T →
        (1 / T) * ∫ t in (0 : ℝ)..T, ‖S'.poly t‖ ^ (2 * j) = diagonalMass Q a ha j := by
  refine ⟨roundedSystem Q a ha T, fun _ => rfl, fun r => abs_roundedStep_sub_le hT r, ?_,
    fun j hj => rounded_moment_eq_diagonal hQ hT hy hyQ hj⟩
  rw [roundedSystem_column_eq_size hT]
  exact Finset.sum_coe_sort Q a

/-- **Past the mixing range the rounded system loses unique factorization.** Two distinct squarefree products of `k` primes
have the same rounded step as soon as their number exceeds the number of available lattice points. -/
theorem exists_collision (hQ : ∀ r ∈ Q, r.Prime) (hT : 0 < T) {y k : ℕ} (hy : 1 ≤ y)
    (hyQ : ∀ r ∈ Q, r ≤ y)
    (hcard : ⌊T * k * Real.log y / (2 * Real.pi) + 2 * k⌋₊ + 1 < Q.card.choose k) :
    ∃ A ∈ Q.powersetCard k, ∃ B ∈ Q.powersetCard k, A ≠ B ∧
      ∑ r ∈ A, roundedStep T r = ∑ r ∈ B, roundedStep T r := by
  classical
  have hpi := Real.pi_pos
  have hy' : (1 : ℝ) ≤ y := by exact_mod_cast hy
  set box : Finset ℕ → ℕ := fun A => (∑ r ∈ A, roundedIndex T r + k).toNat with hbox
  have hbounds : ∀ A ∈ Q.powersetCard k, 0 ≤ ∑ r ∈ A, roundedIndex T r + (k : ℤ) ∧
      ((∑ r ∈ A, roundedIndex T r + (k : ℤ) : ℤ) : ℝ) ≤ T * k * Real.log y / (2 * Real.pi) + 2 * k := by
    intro A hA
    obtain ⟨hA1, hA2⟩ := Finset.mem_powersetCard.mp hA
    have hx : ∀ r ∈ A, 0 ≤ T * Real.log r / (2 * Real.pi) := fun r _ =>
      div_nonneg (mul_nonneg hT.le (Real.log_natCast_nonneg r)) (by positivity)
    have hlow : ∀ r ∈ A, (-(1 : ℤ)) ≤ roundedIndex T r := by
      intro r hr
      have h1 := abs_sub_round (T * Real.log r / (2 * Real.pi))
      have h2 := (abs_le.mp h1).2
      have h3 : (-(1 : ℝ)) < (roundedIndex T r : ℝ) := by
        unfold roundedIndex
        linarith [hx r hr]
      have : (-(1 : ℤ) : ℝ) < (roundedIndex T r : ℝ) := by exact_mod_cast h3
      exact_mod_cast this.le
    have hup : ∀ r ∈ A, (roundedIndex T r : ℝ) ≤ T * Real.log y / (2 * Real.pi) + 1 := by
      intro r hr
      have h1 := abs_sub_round (T * Real.log r / (2 * Real.pi))
      have h2 := (abs_le.mp h1).1
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (hQ r (hA1 hr)).pos
      have h3 : T * Real.log r / (2 * Real.pi) ≤ T * Real.log y / (2 * Real.pi) := by
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hT.le) (by positivity)
        exact Real.log_le_log hr0 (by exact_mod_cast hyQ r (hA1 hr))
      unfold roundedIndex at *
      linarith
    constructor
    · have := Finset.card_nsmul_le_sum A (fun r => roundedIndex T r) (-(1 : ℤ)) hlow
      rw [hA2, nsmul_eq_mul] at this
      linarith
    · have h4 := Finset.sum_le_card_nsmul A (fun r => (roundedIndex T r : ℝ))
        (T * Real.log y / (2 * Real.pi) + 1) hup
      rw [hA2, nsmul_eq_mul] at h4
      push_cast
      have h5 : (k : ℝ) * (T * Real.log y / (2 * Real.pi) + 1) =
          T * k * Real.log y / (2 * Real.pi) + k := by ring
      linarith
  have hmaps : Set.MapsTo box (Q.powersetCard k : Set (Finset ℕ))
      (Finset.range (⌊T * k * Real.log y / (2 * Real.pi) + 2 * k⌋₊ + 1) : Set ℕ) := by
    intro A hA
    obtain ⟨h1, h2⟩ := hbounds A (Finset.mem_coe.mp hA)
    simp only [Finset.coe_range, Set.mem_Iio, hbox]
    rw [Nat.lt_succ_iff]
    refine Nat.le_floor ?_
    have e : ((∑ r ∈ A, roundedIndex T r + (k : ℤ)).toNat : ℝ) =
        ((∑ r ∈ A, roundedIndex T r + (k : ℤ) : ℤ) : ℝ) := by
      have := Int.toNat_of_nonneg h1
      exact_mod_cast this
    rw [e]
    exact h2
  have hcard' : (Finset.range (⌊T * k * Real.log y / (2 * Real.pi) + 2 * k⌋₊ + 1)).card <
      (Q.powersetCard k).card := by
    rw [Finset.card_range, Finset.card_powersetCard]
    exact hcard
  obtain ⟨A, hA, B, hB, hne, hsame⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard' hmaps
  have hA' := Finset.mem_coe.mp hA
  have hB' := Finset.mem_coe.mp hB
  refine ⟨A, hA', B, hB', hne, ?_⟩
  have h1 := Int.toNat_of_nonneg (hbounds A hA').1
  have h2 := Int.toNat_of_nonneg (hbounds B hB').1
  have hs : (∑ r ∈ A, roundedIndex T r + (k : ℤ)).toNat = (∑ r ∈ B, roundedIndex T r + (k : ℤ)).toNat :=
    hsame
  have hz : ∑ r ∈ A, roundedIndex T r = ∑ r ∈ B, roundedIndex T r := by
    rw [hs] at h1
    linarith
  unfold roundedStep
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  exact_mod_cast hz

end

end GaloisForLFunctions.PrimeTorusTheory
