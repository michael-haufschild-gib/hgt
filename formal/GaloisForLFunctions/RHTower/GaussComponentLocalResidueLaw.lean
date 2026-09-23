import GaloisForLFunctions.RHTower.GaussComponentAmplitude
import GaloisForLFunctions.RHTower.GaussComponentVerticalPhase
import GaloisForLFunctions.RHTower.GaussPairedDiagonalResidue
import GaloisForLFunctions.HTGeometry.DixmierIdeal

/-!
# Exact critical residue of one Gauss component

The Fourier-diagonal model of the `m`-fold Gauss component at a prime `p` has the exact
logarithmic mean `2 (p^m - 1)^(2 : ℕ) / (m^(2 : ℕ) log p)`.  Restoring the local-factor coefficient
`((p-1)/p)^{2m}` of the isometric source reduction turns this into the arithmetic channel residue

`2 (p-1)^{2m} (p^m - 1)^(2 : ℕ) / (p^{2m} m^(2 : ℕ) log p)`,

which is the value carried by the critical `2m`-energy of the component defect.  The value does
not depend on the component label `k`, although the labels index pairwise distinct Gamma
arguments.

The residue is realized by an explicit diagonal operator on `ℓ²`: its critical `2m`-energy has
exactly this logarithmic mean, it lies in the weak class `S_{2m,∞}` and in no ordinary Schatten
class at or below `2m`, and its `2m`-th power has singular values `R/(n+1)`, hence lies in the
Dixmier ideal `L^{1,∞}` with logarithmic mean `R`.
-/

open Filter Topology Finset

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-! ## The local-factor coefficient -/

/-- Local-factor coefficient `((p-1)/p)^{2m}` restored by the isometric source reduction. -/
def gaussLocalFactorWeight (m : ℕ) (p : Nat.Primes) : ℝ :=
  (((p : ℝ) - 1) / (p : ℝ)) ^ (2 * m)

theorem gaussLocalFactorWeight_pos (m : ℕ) (p : Nat.Primes) :
    0 < gaussLocalFactorWeight m p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  rw [gaussLocalFactorWeight]
  exact pow_pos (div_pos (sub_pos.mpr hp) (lt_trans zero_lt_one hp)) _

/-- Restoring the local factor converts the Fourier-diagonal mean into the arithmetic channel
residue. -/
theorem gaussLocalFactorWeight_mul_principalResidue {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    gaussLocalFactorWeight m p *
        (2 * ((p : ℝ) ^ m - 1) ^ 2 / ((m : ℝ) ^ 2 * Real.log (p : ℝ)))
      = gaussChannelResidue m p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    exact hpos.ne'
  have hL : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  rw [gaussLocalFactorWeight, gaussChannelResidue, div_pow]
  field_simp

/-! ## The localized Fourier diagonal and formula (A) -/

/-- The principal Fourier diagonal of the component defect, with the local-factor coefficient
restored. -/
def gaussComponentLocalDiagonalTerm {m : ℕ} (k : Fin m) (p : Nat.Primes) (n : ℕ) : ℂ :=
  (gaussLocalFactorWeight m p : ℂ) * gaussPrincipalDiagonalTerm k p n

/-- **Exact critical residue of a Gauss component.**  The logarithmic mean of the localized
Fourier diagonal is the arithmetic channel residue
`2 (p-1)^{2m} (p^m - 1)^(2 : ℕ) / (p^{2m} m^(2 : ℕ) log p)`. -/
theorem gaussComponentLocalDiagonalTerm_logResidue
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, gaussComponentLocalDiagonalTerm k p n) / (Real.log N : ℂ))
      atTop (nhds ((gaussChannelResidue m p : ℝ) : ℂ)) := by
  have hbase := gaussPrincipalDiagonalTerm_logResidue hm k p
  have hscaled := hbase.const_mul ((gaussLocalFactorWeight m p : ℝ) : ℂ)
  have hlimit :
      ((gaussLocalFactorWeight m p : ℝ) : ℂ) *
          ((2 * ((p : ℝ) ^ m - 1) ^ 2 / ((m : ℝ) ^ 2 * Real.log (p : ℝ)) : ℝ) : ℂ)
        = ((gaussChannelResidue m p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, gaussLocalFactorWeight_mul_principalResidue hm p]
  rw [hlimit] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with N
  simp only [gaussComponentLocalDiagonalTerm]
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Critical residue extracted from the `k`th Gauss component at `p`. -/
def gaussComponentCriticalResidue {m : ℕ} (k : Fin m) (p : Nat.Primes) : ℂ :=
  limUnder atTop (fun N : ℕ =>
    (∑ n ∈ Finset.range N, gaussComponentLocalDiagonalTerm k p n) / (Real.log N : ℂ))

/-- The extracted residue is the arithmetic channel residue. -/
theorem gaussComponentCriticalResidue_eq {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    gaussComponentCriticalResidue k p = ((gaussChannelResidue m p : ℝ) : ℂ) :=
  (gaussComponentLocalDiagonalTerm_logResidue hm k p).limUnder_eq

/-- **Component independence.**  The critical residue does not depend on the Gauss-component
label. -/
theorem gaussComponentCriticalResidue_independent_of_component
    {m : ℕ} (hm : 1 ≤ m) (k l : Fin m) (p : Nat.Primes) :
    gaussComponentCriticalResidue k p = gaussComponentCriticalResidue l p := by
  rw [gaussComponentCriticalResidue_eq hm, gaussComponentCriticalResidue_eq hm]

/-- The extracted residue is real and strictly positive. -/
theorem gaussComponentCriticalResidue_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    gaussComponentCriticalResidue k p ≠ 0 := by
  rw [gaussComponentCriticalResidue_eq hm]
  exact_mod_cast (gaussChannelResidue_pos hm p).ne'

/-! ## The components indexed by distinct labels are distinct -/

/-- Distinct component labels give distinct real offsets. -/
theorem gaussComponentOffset_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (gaussComponentOffset (m := m)) := by
  intro k l hkl
  have hm0 : (m : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    exact hpos.ne'
  rw [gaussComponentOffset, gaussComponentOffset] at hkl
  have hval : ((k : ℕ) : ℝ) = ((l : ℕ) : ℝ) := by
    field_simp at hkl
    exact hkl
  exact Fin.ext (by exact_mod_cast hval)

/-- Distinct component labels give distinct Gamma arguments at every height, so the
label-independence of the residue is not a statement about a single function. -/
theorem gaussComponentVerticalUpperArg_ne_of_ne
    {m : ℕ} (hm : 1 ≤ m) {k l : Fin m} (hkl : k ≠ l) (z : ℂ) :
    gaussComponentVerticalUpperArg k z ≠ gaussComponentVerticalUpperArg l z := by
  intro h
  rw [gaussComponentVerticalUpperArg, gaussComponentVerticalUpperArg] at h
  have hoff : (gaussComponentOffset k : ℂ) = (gaussComponentOffset l : ℂ) := by
    have := add_right_cancel h
    exact this
  exact hkl (gaussComponentOffset_injective hm (by exact_mod_cast hoff))

/-! ## Operator realization at one prime -/

theorem gaussPairedChannelResidue_unit {m : ℕ} (p : Nat.Primes) :
    gaussPairedChannelResidue m (fun _ : Unit => p) = gaussChannelResidue m p := by
  simp [gaussPairedChannelResidue]

/-- Explicit `ℓ²` realization of the localized Gauss-component defect at a single prime. -/
def gaussComponentCriticalOperator {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    EllTwo →L[ℂ] EllTwo :=
  gaussPairedCriticalDiagonalOperator hm (fun _ : Unit => p)

/-- The realization has the critical `2m`-asymptotic with the exact arithmetic constant. -/
theorem tendsto_gaussComponentCriticalOperator_approxNumber
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    Tendsto (fun n : ℕ =>
      approxNumber (gaussComponentCriticalOperator hm p) n ^ ((2 * m : ℕ) : ℝ) *
        ((n : ℝ) + 1))
      atTop (nhds (gaussChannelResidue m p)) := by
  have h := tendsto_gaussPairedCriticalDiagonalOperator_approxNumber_rpow_mul_succ hm
    (fun _ : Unit => p)
  rwa [gaussPairedChannelResidue_unit] at h

/-- **Measurability at the critical order.**  The critical `2m`-energy of the realization has an
honest logarithmic mean, equal to the arithmetic residue. -/
theorem hasSchattenLogResidue_gaussComponentCriticalOperator
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    HasSchattenLogResidue ((2 * m : ℕ) : ℝ) (gaussComponentCriticalOperator hm p)
      (gaussChannelResidue m p) :=
  hasSchattenLogResidue_of_tendsto_mul_succ
    (tendsto_gaussComponentCriticalOperator_approxNumber hm p)

/-- Weak endpoint membership of the realization. -/
theorem memWeakSchattenClass_gaussComponentCriticalOperator
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    MemWeakSchattenClass ((2 * m : ℕ) : ℝ) (gaussComponentCriticalOperator hm p) :=
  memWeakSchattenClass_of_tendsto_mul_succ
    (tendsto_gaussComponentCriticalOperator_approxNumber hm p)

/-- **Exact critical order.**  The realization belongs to no Schatten class at or below `2m` and
to every Schatten class strictly above `2m`. -/
theorem gaussComponentCriticalOperator_exact_schattenDepth
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    (∀ q : ℝ, 0 < q → q ≤ ((2 * m : ℕ) : ℝ) →
        ¬ MemSchattenClass q (gaussComponentCriticalOperator hm p)) ∧
      (∀ q : ℝ, ((2 * m : ℕ) : ℝ) < q →
        MemSchattenClass q (gaussComponentCriticalOperator hm p)) :=
  exact_schattenDepth_of_tendsto_mul_succ
    (by exact_mod_cast (show 0 < 2 * m by omega))
    (gaussChannelResidue_pos hm p)
    (tendsto_gaussComponentCriticalOperator_approxNumber hm p)

/-! ## The critical power and the Dixmier ideal -/

theorem criticalDiagonalMultiplier_rpow {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (n : ℕ) :
    criticalDiagonalMultiplier p c n ^ p = c / ((n : ℝ) + 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := criticalDiagonalMultiplier_rpow_mul_succ hp hc n
  field_simp at h ⊢
  linarith [h]

/-- The `2m`-th power of the Gauss-component realization: a diagonal operator whose singular
values are `R/(n+1)`. -/
def gaussComponentCriticalPowerOperator {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    EllTwo →L[ℂ] EllTwo :=
  criticalDiagonalOperator 1 (gaussChannelResidue m p) one_pos (gaussChannelResidue_pos hm p)

theorem approxNumber_gaussComponentCriticalPowerOperator
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (n : ℕ) :
    approxNumber (gaussComponentCriticalPowerOperator hm p) n =
      gaussChannelResidue m p / ((n : ℝ) + 1) := by
  rw [gaussComponentCriticalPowerOperator, approxNumber_criticalDiagonalOperator_eq,
    criticalDiagonalMultiplier]
  norm_num

/-- The power operator really is the `2m`-th power at the level of approximation numbers. -/
theorem approxNumber_gaussComponentCriticalOperator_rpow
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (n : ℕ) :
    approxNumber (gaussComponentCriticalOperator hm p) n ^ ((2 * m : ℕ) : ℝ) =
      approxNumber (gaussComponentCriticalPowerOperator hm p) n := by
  have hmpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * m by omega)
  rw [approxNumber_gaussComponentCriticalPowerOperator hm p n,
    gaussComponentCriticalOperator, gaussPairedCriticalDiagonalOperator,
    approxNumber_criticalDiagonalOperator_eq,
    criticalDiagonalMultiplier_rpow hmpos
      (by rw [gaussPairedChannelResidue_unit]; exact gaussChannelResidue_pos hm p) n,
    gaussPairedChannelResidue_unit]

/-- **Dixmier-ideal bound.**  The singular-value partial sums of the `2m`-th power grow at most
logarithmically, with the arithmetic residue as constant. -/
theorem gaussComponentCriticalPowerOperator_partialSum_le
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, approxNumber (gaussComponentCriticalPowerOperator hm p) n
      ≤ gaussChannelResidue m p * (1 + Real.log N) := by
  have hR : 0 ≤ gaussChannelResidue m p := (gaussChannelResidue_pos hm p).le
  have hrewrite :
      ∑ n ∈ Finset.range N, approxNumber (gaussComponentCriticalPowerOperator hm p) n
        = gaussChannelResidue m p * ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [approxNumber_gaussComponentCriticalPowerOperator hm p n, mul_one_div]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.sum_inv_succ_le_one_add_log N hN) hR

/-- Weak `L^{1,∞}` membership of the `2m`-th power. -/
theorem memWeakSchattenClass_gaussComponentCriticalPowerOperator
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    MemWeakSchattenClass 1 (gaussComponentCriticalPowerOperator hm p) := by
  refine ⟨gaussChannelResidue m p, (gaussChannelResidue_pos hm p).le, fun n => ?_⟩
  rw [approxNumber_gaussComponentCriticalPowerOperator hm p n, Real.rpow_one]

/-- **The Dixmier trace value.**  The `2m`-th power of the realization is Connes measurable at
order one with logarithmic mean the arithmetic residue. -/
theorem hasSchattenLogResidue_gaussComponentCriticalPowerOperator
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    HasSchattenLogResidue 1 (gaussComponentCriticalPowerOperator hm p)
      (gaussChannelResidue m p) := by
  refine hasSchattenLogResidue_of_tendsto_mul_succ ?_
  have hfun : (fun n : ℕ =>
      approxNumber (gaussComponentCriticalPowerOperator hm p) n ^ (1 : ℝ) * ((n : ℝ) + 1))
      = fun _ : ℕ => gaussChannelResidue m p := by
    funext n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [approxNumber_gaussComponentCriticalPowerOperator hm p n, Real.rpow_one,
      div_mul_cancel₀ _ hn]
  rw [hfun]
  exact tendsto_const_nhds

/-! ## The closed law -/

/-- **Gauss-component critical residue law.**  For every `m ≥ 1`, every component label `k`, and
every prime `p`:

* the localized Fourier diagonal has logarithmic mean the arithmetic residue
  `2 (p-1)^{2m} (p^m - 1)^(2 : ℕ) / (p^{2m} m^(2 : ℕ) log p)`;
* that value does not depend on `k`, although distinct labels index distinct Gamma arguments;
* an explicit diagonal operator realizes it, with exact critical order `2m`;
* its `2m`-th power lies in the Dixmier ideal with the same logarithmic mean. -/
theorem gaussComponent_criticalResidue_law {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    (∀ k : Fin m, Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, gaussComponentLocalDiagonalTerm k p n) / (Real.log N : ℂ))
        atTop (nhds ((gaussChannelResidue m p : ℝ) : ℂ))) ∧
      (∀ k l : Fin m, gaussComponentCriticalResidue k p = gaussComponentCriticalResidue l p) ∧
      (∀ k l : Fin m, k ≠ l → ∀ z : ℂ,
        gaussComponentVerticalUpperArg k z ≠ gaussComponentVerticalUpperArg l z) ∧
      0 < gaussChannelResidue m p ∧
      MemWeakSchattenClass ((2 * m : ℕ) : ℝ) (gaussComponentCriticalOperator hm p) ∧
      HasSchattenLogResidue ((2 * m : ℕ) : ℝ) (gaussComponentCriticalOperator hm p)
        (gaussChannelResidue m p) ∧
      (∀ q : ℝ, 0 < q → q ≤ ((2 * m : ℕ) : ℝ) →
        ¬ MemSchattenClass q (gaussComponentCriticalOperator hm p)) ∧
      (∀ q : ℝ, ((2 * m : ℕ) : ℝ) < q →
        MemSchattenClass q (gaussComponentCriticalOperator hm p)) ∧
      (∀ n : ℕ, approxNumber (gaussComponentCriticalOperator hm p) n ^ ((2 * m : ℕ) : ℝ) =
        approxNumber (gaussComponentCriticalPowerOperator hm p) n) ∧
      MemWeakSchattenClass 1 (gaussComponentCriticalPowerOperator hm p) ∧
      HasSchattenLogResidue 1 (gaussComponentCriticalPowerOperator hm p)
        (gaussChannelResidue m p) :=
  ⟨fun k => gaussComponentLocalDiagonalTerm_logResidue hm k p,
    fun k l => gaussComponentCriticalResidue_independent_of_component hm k l p,
    fun _ _ hkl z => gaussComponentVerticalUpperArg_ne_of_ne hm hkl z,
    gaussChannelResidue_pos hm p,
    memWeakSchattenClass_gaussComponentCriticalOperator hm p,
    hasSchattenLogResidue_gaussComponentCriticalOperator hm p,
    (gaussComponentCriticalOperator_exact_schattenDepth hm p).1,
    (gaussComponentCriticalOperator_exact_schattenDepth hm p).2,
    fun n => approxNumber_gaussComponentCriticalOperator_rpow hm p n,
    memWeakSchattenClass_gaussComponentCriticalPowerOperator hm p,
    hasSchattenLogResidue_gaussComponentCriticalPowerOperator hm p⟩

end

end RHTower
