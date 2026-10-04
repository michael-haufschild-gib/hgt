import GaloisForLFunctions.RHTower.SoninPrimePolarCofinalGroundEnergy
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Arithmetic selection on the native Sonin ground grid

The unchanged chronological ground vectors have reciprocal-maximum covariance.
Their thin-annulus differences force every change of a binary selection mask to
amplify physical energy. Bounded selection is possible exactly for eventually
constant masks; contractive selection is possible exactly for constant masks.
Explicit continuous coefficient duals construct the bounded extensions.

Neither the prime mask nor the prime-power mask has such an extension. This
excludes a universal physical selector argument from the jet's algebraic
idempotence. It does not decide the signed prime-polar source's energy.
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped Topology InnerProductSpace
namespace RHTower

/-- The unchanged chronological ground grid of the native prime-polar source. -/
def soninGroundGridVector (a : ℝ) (n : ℕ) : SoninL2 :=
  soninGroundEntry a (Real.log (n+2:ℝ))

private theorem grid_inner (a : ℝ) (ha : 0 ≤ a) {i j : ℕ} (hij : i ≤ j) :
    inner ℂ (soninGroundGridVector a i) (soninGroundGridVector a j) =
      ((2*a/(j+2:ℝ):ℝ):ℂ) := by
  have hi : (0:ℝ) < i+2 := by positivity
  have hj : (0:ℝ) < j+2 := by positivity
  rw [soninGroundGridVector, soninGroundGridVector,
    inner_soninGroundEntry_of_le a ha _ _ (Real.log_le_log hi (by exact_mod_cast Nat.add_le_add_right hij 2)),
    Real.exp_neg, Real.exp_log hj]
  simp only [div_eq_mul_inv]

private theorem grid_inner_reverse (a : ℝ) (ha : 0 ≤ a) {i j : ℕ} (hji : j ≤ i) :
    inner ℂ (soninGroundGridVector a i) (soninGroundGridVector a j) =
      ((2*a/(i+2:ℝ):ℝ):ℂ) := by
  rw [← inner_conj_symm, grid_inner a ha hji, Complex.conj_ofReal]

private theorem grid_norm_sq (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖soninGroundGridVector a n‖^2 = 2*a/(n+2:ℝ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), grid_inner a ha le_rfl]
  rfl

/-- Adjacent chronological vectors have the exact thin-annulus energy. -/
theorem soninGroundGridDifference_norm_sq (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖soninGroundGridVector a n-soninGroundGridVector a (n+1)‖^2 =
      2*a/((n+2:ℝ)*(n+3:ℝ)) := by
  rw [norm_sub_sq (𝕜 := ℂ), grid_norm_sq a ha, grid_norm_sq a ha,
    grid_inner a ha (Nat.le_succ n)]
  change 2*a/(n+2:ℝ)-2*(2*a/((n+1:ℕ)+2:ℝ))+2*a/((n+1:ℕ)+2:ℝ)=_
  push_cast
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  have hn' : (n:ℝ)+3 ≠ 0 := by positivity
  field_simp
  ring

private def gridPrefixDual (a : ℝ) (n : ℕ) : SoninL2 :=
  (((n+2:ℝ)*(n+3:ℝ)/(2*a):ℝ):ℂ) •
    (soninGroundGridVector a n-soninGroundGridVector a (n+1))

private theorem gridPrefixDual_inner (a : ℝ) (ha : 0 < a) (i j : ℕ) :
    inner ℂ (gridPrefixDual a i) (soninGroundGridVector a j) =
      if j ≤ i then 1 else 0 := by
  rw [gridPrefixDual, inner_smul_left, inner_sub_left, Complex.conj_ofReal]
  by_cases hji : j ≤ i
  · rw [if_pos hji, grid_inner_reverse a ha.le hji,
      grid_inner_reverse a ha.le (hji.trans (Nat.le_succ i))]
    simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul]
    norm_cast
    have ha0 : a ≠ 0 := ha.ne'
    have hi : (i:ℝ)+2 ≠ 0 := by positivity
    have hi' : (i:ℝ)+3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · rw [if_neg hji, grid_inner a ha.le (by omega), grid_inner a ha.le (by omega),
      sub_self, mul_zero]

/-- Explicit physical dual that recovers one unchanged chronological coefficient. -/
def soninGroundGridCoefficientDual (a : ℝ) : ℕ → SoninL2
  | 0 => gridPrefixDual a 0
  | n+1 => gridPrefixDual a (n+1)-gridPrefixDual a n

/-- All chronological coefficients have exact continuous duals; no carrier is changed. -/
theorem soninGroundGridCoefficientDual_inner (a : ℝ) (ha : 0 < a) (n j : ℕ) :
    inner ℂ (soninGroundGridCoefficientDual a n) (soninGroundGridVector a j) =
      if n = j then 1 else 0 := by
  cases n with
  | zero =>
      rw [soninGroundGridCoefficientDual, gridPrefixDual_inner a ha]
      by_cases hj : j = 0
      · subst j; simp
      · simp [show ¬ j ≤ 0 by omega, Ne.symm hj]
  | succ n =>
      rw [soninGroundGridCoefficientDual, inner_sub_left,
        gridPrefixDual_inner a ha, gridPrefixDual_inner a ha]
      split_ifs <;> first | omega | ring

/-- Literal binary selection on the original ground grid. -/
def SoninGroundGridSelects (a : ℝ) (mask : ℕ → Bool) (T : SoninL2 →L[ℂ] SoninL2) : Prop :=
  ∀ n, T (soninGroundGridVector a n) = if mask n then soninGroundGridVector a n else 0

private theorem switch_energy_lower (a : ℝ) (ha : 0 < a) (mask : ℕ → Bool)
    (T : SoninL2 →L[ℂ] SoninL2) (hT : SoninGroundGridSelects a mask T)
    (n : ℕ) (hswitch : mask n ≠ mask (n+1)) :
    2*a/(n+3:ℝ) ≤ ‖T (soninGroundGridVector a n-soninGroundGridVector a (n+1))‖^2 := by
  rw [map_sub,hT n,hT (n+1)]
  cases hn : mask n <;> cases hm : mask (n+1)
  · exact (hswitch (hn.trans hm.symm)).elim
  · norm_num [grid_norm_sq a ha.le, add_assoc]
  · have h : 2*a/(n+3:ℝ) ≤ 2*a/(n+2:ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    simpa [grid_norm_sq a ha.le] using h
  · exact (hswitch (hn.trans hm.symm)).elim

/-- Every switch has an unavoidable physical amplification growing with its clock index. -/
theorem soninGroundGridSelector_switch_cost (a : ℝ) (ha : 0 < a) (mask : ℕ → Bool)
    (T : SoninL2 →L[ℂ] SoninL2) (hT : SoninGroundGridSelects a mask T)
    (n : ℕ) (hswitch : mask n ≠ mask (n+1)) : (n:ℝ)+2 ≤ ‖T‖^2 := by
  have hl := switch_energy_lower a ha mask T hT n hswitch
  have hn := T.le_opNorm (soninGroundGridVector a n-soninGroundGridVector a (n+1))
  have hs : ‖T (soninGroundGridVector a n-soninGroundGridVector a (n+1))‖^2 ≤
      ‖T‖^2*‖soninGroundGridVector a n-soninGroundGridVector a (n+1)‖^2 := by
    nlinarith [norm_nonneg (T (soninGroundGridVector a n-soninGroundGridVector a (n+1))),
      mul_nonneg (norm_nonneg T)
        (norm_nonneg (soninGroundGridVector a n-soninGroundGridVector a (n+1)))]
  rw [soninGroundGridDifference_norm_sq a ha.le] at hs
  have hb := hl.trans hs
  have hp : (0:ℝ) < n+2 := by positivity
  have hq : (0:ℝ) < n+3 := by positivity
  have hmul := (div_le_iff₀ hq).mp hb
  have hden : (n:ℝ)+2 ≠ 0 := hp.ne'
  have hden' : (n:ℝ)+3 ≠ 0 := hq.ne'
  field_simp at hmul
  nlinarith

private def maskScalar (mask : ℕ → Bool) (n : ℕ) : ℂ := if mask n then 1 else 0

private theorem maskScalar_smul (mask : ℕ → Bool) (n : ℕ) (v : SoninL2) :
    maskScalar mask n • v = if mask n then v else 0 := by
  unfold maskScalar
  split <;> simp

/-- An explicit bounded extension of every finite change of a constant arithmetic mask. -/
def soninGroundGridFiniteSelector (a : ℝ) (mask : ℕ → Bool) (N : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  maskScalar mask N • (1:SoninL2 →L[ℂ] SoninL2) +
    ∑ i ∈ range N, (maskScalar mask i-maskScalar mask N) •
      InnerProductSpace.rankOne ℂ (soninGroundGridVector a i) (soninGroundGridCoefficientDual a i)

/-- The finite-rank repair realizes precisely the original mask through its cutoff
and its constant tail afterwards. -/
theorem soninGroundGridFiniteSelector_apply (a : ℝ) (ha : 0 < a)
    (mask : ℕ → Bool) (N j : ℕ) :
    soninGroundGridFiniteSelector a mask N (soninGroundGridVector a j) =
      if j < N then
        (if mask j then soninGroundGridVector a j else 0)
      else (if mask N then soninGroundGridVector a j else 0) := by
  have hterm (i : ℕ) :
      ((maskScalar mask i-maskScalar mask N) •
        InnerProductSpace.rankOne ℂ (soninGroundGridVector a i) (soninGroundGridCoefficientDual a i))
        (soninGroundGridVector a j) =
      if i = j then (maskScalar mask j-maskScalar mask N) • soninGroundGridVector a j else 0 := by
    change (maskScalar mask i-maskScalar mask N) •
      (inner ℂ (soninGroundGridCoefficientDual a i) (soninGroundGridVector a j) •
        soninGroundGridVector a i) = _
    rw [soninGroundGridCoefficientDual_inner a ha]
    by_cases hij : i = j
    · subst i; simp
    · simp [hij]
  rw [soninGroundGridFiniteSelector, add_apply, smul_apply, one_apply_eq_self,
    _root_.sum_apply]
  simp_rw [hterm]
  by_cases hj : j < N
  · simp only [sum_ite_eq', Finset.mem_range, hj, ↓reduceIte]
    rw [← maskScalar_smul]
    module
  · simp only [sum_ite_eq', Finset.mem_range, hj, ↓reduceIte, add_zero, maskScalar_smul]

/-- Sharp boundedness classification on the unchanged physical grid. -/
theorem soninGroundGridSelector_bounded_iff (a : ℝ) (ha : 0 < a) (mask : ℕ → Bool) :
    (∃ T : SoninL2 →L[ℂ] SoninL2, SoninGroundGridSelects a mask T) ↔
      ∃ N : ℕ, ∀ n, N ≤ n → mask n = mask N := by
  constructor
  · rintro ⟨T,hT⟩
    obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖^2)
    have hstep (n : ℕ) (hn : N ≤ n) : mask n = mask (n+1) := by
      by_contra hne
      have h := soninGroundGridSelector_switch_cost a ha mask T hT n hne
      have hnR : (N:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    refine ⟨N,?_⟩
    have htail (k : ℕ) : mask (N+k) = mask N := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.add_succ, ← hstep (N+k) (by omega)]
          exact ih
    intro n hn
    have h := htail (n-N)
    simpa only [Nat.add_sub_of_le hn] using h
  · rintro ⟨N,hN⟩
    refine ⟨soninGroundGridFiniteSelector a mask N,?_⟩
    intro n
    rw [soninGroundGridFiniteSelector_apply a ha]
    by_cases hn : n < N
    · rw [if_pos hn]
    · rw [if_neg hn, hN n (by omega)]

/-- Genuine primes never admit a bounded selector in the native TG ground geometry. -/
theorem soninGroundGrid_primeSelector_unbounded (a : ℝ) (ha : 0 < a) :
    ¬ ∃ T : SoninL2 →L[ℂ] SoninL2,
      ∀ n, T (soninGroundGridVector a n) =
        if (n+2).Prime then soninGroundGridVector a n else 0 := by
  intro h
  have hs : ∃ T : SoninL2 →L[ℂ] SoninL2,
      SoninGroundGridSelects a (fun n => decide (n+2).Prime) T := by
    simpa only [SoninGroundGridSelects, decide_eq_true_eq] using h
  obtain ⟨N,hN⟩ := (soninGroundGridSelector_bounded_iff a ha _).mp hs
  obtain ⟨p,hpN,hp⟩ := Nat.exists_infinite_primes (max (N+2) 3)
  have hp3 : 3 ≤ p := (le_max_right _ _).trans hpN
  have hNp : N+2 ≤ p := (le_max_left _ _).trans hpN
  have hnp : ¬ (p+1).Prime := by
    intro hprime
    obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
    have he : Even (p+1) := ⟨k+1, by omega⟩
    have htwo := hprime.even_iff.mp he
    omega
  have h1 := hN (p-2) (by omega)
  have h2 := hN (p-1) (by omega)
  have hmask := h1.trans h2.symm
  have he1 : p-2+2 = p := by omega
  have he2 : p-1+2 = p+1 := by omega
  simp [he1,he2,hp,hnp] at hmask

/-- Contractive selection is even more rigid: the binary mask must be constant
on the entire original grid. -/
theorem soninGroundGridSelector_contractive_iff (a : ℝ) (ha : 0 < a) (mask : ℕ → Bool) :
    (∃ T : SoninL2 →L[ℂ] SoninL2, SoninGroundGridSelects a mask T ∧ ‖T‖ ≤ 1) ↔
      ∀ n, mask n = mask 0 := by
  constructor
  · rintro ⟨T,hT,hbound⟩
    have hstep (n : ℕ) : mask n = mask (n+1) := by
      by_contra hne
      have h := soninGroundGridSelector_switch_cost a ha mask T hT n hne
      have hnorm := norm_nonneg T
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (hstep n).symm.trans ih
  · intro h
    refine ⟨if mask 0 then 1 else 0,?_,?_⟩
    · intro n
      rw [h n]
      cases mask 0 <;> simp
    · cases mask 0 <;> simp

private theorem not_primePow_six_multiple (N : ℕ) : ¬ IsPrimePow (6*(N+1)) := by
  have hn : 2 ≤ 6*(N+1) := by omega
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le hn]
  refine ⟨2,Nat.mem_primeFactors.mpr ⟨Nat.prime_two,?_,by omega⟩,
    3,Nat.mem_primeFactors.mpr ⟨Nat.prime_three,?_,by omega⟩,by norm_num⟩
  · exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) _
  · exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _

/-- The actual prime-power mask exposed by the jet's divisor transform also
has no bounded extension on the native TG ground grid. -/
theorem soninGroundGrid_primePowerSelector_unbounded (a : ℝ) (ha : 0 < a) :
    ¬ ∃ T : SoninL2 →L[ℂ] SoninL2,
      ∀ n, T (soninGroundGridVector a n) =
        if IsPrimePow (n+2) then soninGroundGridVector a n else 0 := by
  intro h
  have hs : ∃ T : SoninL2 →L[ℂ] SoninL2,
      SoninGroundGridSelects a (fun n => decide (IsPrimePow (n+2))) T := by
    simpa only [SoninGroundGridSelects, decide_eq_true_eq] using h
  obtain ⟨N,hN⟩ := (soninGroundGridSelector_bounded_iff a ha _).mp hs
  obtain ⟨p,hNp,hp⟩ := Nat.exists_infinite_primes (N+2)
  have h1 := hN (p-2) (by omega)
  have h2 := hN (6*N+4) (by omega)
  have hmask := h1.trans h2.symm
  have he1 : p-2+2 = p := by omega
  have he2 : 6*N+4+2 = 6*(N+1) := by omega
  simp [he1,he2,hp.isPrimePow,not_primePow_six_multiple N] at hmask

end RHTower
