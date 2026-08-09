import GaloisForLFunctions.RHTower.BurnolFirstWallResiduePolarization

/-!
# The universal dyadic commutator staircase

Let `P_a` be multiplication by the indicator of the aperture `(0,a)` and let

`T₂ f(t) = ∑_{n ≥ 1} 2^{-n} f(t/2ⁿ)`

be the causal dyadic Euler inverse.  If `f` is constant equal to `c` on the aperture, the
commutator `[P_a, T₂] f` vanishes inside the aperture and is the geometric staircase `-c 2^{-k}`
on the dyadic shell `[a 2^k, a 2^{k+1})`.  Because the shells tile `[a, ∞)` and the `k`-th shell has
length `a 2^k`, the squared `L²`-norm of the commutator on the positive ray is exactly `2 a |c|²`.

Applied at the fixed Route-R aperture `a = 1/2` to the two Fourier orientations of the zero-divided
source, whose heads are `a_ρ` and `b_ρ`, the difference of the two squared commutator norms is
exactly the oriented Burnol current `|a_ρ|² - |b_ρ|²`.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-- Multiplication by the indicator of the aperture `(0,a)`. -/
def burnolAperturePart (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => if t ∈ Ioo (0 : ℝ) a then f t else 0

/-- The causal dyadic Euler inverse `T₂ f(t) = ∑_{n ≥ 1} 2^{-n} f(t/2ⁿ)`. -/
def burnolDyadicLadder (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∑' n : ℕ, ((1 : ℂ) / 2) ^ (n + 1) * f (t / 2 ^ (n + 1))

/-- The aperture commutator `[P_a, T₂] f`. -/
def burnolApertureCommutator (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => burnolAperturePart a (burnolDyadicLadder f) t -
    burnolDyadicLadder (burnolAperturePart a f) t

/-! ## The staircase -/

/-- Every point of `[a, ∞)` lies in a dyadic shell. -/
theorem exists_burnolDyadicShell {a t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    ∃ k : ℕ, a * 2 ^ k ≤ t ∧ t < a * 2 ^ (k + 1) := by
  have hset : ∃ n : ℕ, t < a * 2 ^ n := by
    refine ⟨⌈t / a⌉₊, ?_⟩
    have h1 : t / a ≤ (⌈t / a⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈t / a⌉₊ : ℝ) < 2 ^ (⌈t / a⌉₊ : ℕ) := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : t / a < 2 ^ (⌈t / a⌉₊ : ℕ) := lt_of_le_of_lt h1 h2
    rwa [div_lt_iff₀ ha, mul_comm] at h3
  classical
  set n₀ : ℕ := Nat.find hset with hn₀
  have hn₀spec : t < a * 2 ^ n₀ := Nat.find_spec hset
  have hpos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exfalso
      rw [h] at hn₀spec
      simp only [pow_zero, mul_one] at hn₀spec
      linarith
    · exact h
  refine ⟨n₀ - 1, ?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd hcon (Nat.find_min hset (m := n₀ - 1) (by omega))
  · rwa [show n₀ - 1 + 1 = n₀ by omega]

/-- Inside the aperture the commutator vanishes, for every source: all dyadic samples of an
aperture point stay inside the aperture. -/
theorem burnolApertureCommutator_eq_zero_of_mem {a : ℝ} {f : ℝ → ℂ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) a) :
    burnolApertureCommutator a f t = 0 := by
  have hin : ∀ n : ℕ, t / 2 ^ (n + 1) ∈ Ioo (0 : ℝ) a := by
    intro n
    have hpow : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    refine ⟨div_pos ht.1 hpow, ?_⟩
    have h1 : t / 2 ^ (n + 1) ≤ t := div_le_self ht.1.le (one_le_pow₀ (by norm_num))
    exact lt_of_le_of_lt h1 ht.2
  have hladder : burnolDyadicLadder f t = burnolDyadicLadder (burnolAperturePart a f) t := by
    rw [burnolDyadicLadder, burnolDyadicLadder]
    refine tsum_congr (fun n => ?_)
    rw [burnolAperturePart, if_pos (hin n)]
  rw [burnolApertureCommutator, burnolAperturePart, if_pos ht, hladder, sub_self]

/-- **The universal dyadic commutator staircase.**  On the `k`-th dyadic shell the commutator has
the constant value `-c 2^{-k}`. -/
theorem burnolApertureCommutator_shell {a : ℝ} {c : ℂ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : ∀ s, s ∈ Ioo (0 : ℝ) a → f s = c) {k : ℕ} {t : ℝ}
    (hlo : a * 2 ^ k ≤ t) (hhi : t < a * 2 ^ (k + 1)) :
    burnolApertureCommutator a f t = -c * ((1 : ℂ) / 2) ^ k := by
  have hone : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hta : a ≤ t := le_trans (by nlinarith) hlo
  have hnotmem : t ∉ Ioo (0 : ℝ) a := fun hmem => absurd hmem.2 (not_lt.mpr hta)
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le ha hta
  have hmem : ∀ n : ℕ, (t / 2 ^ (n + 1) ∈ Ioo (0 : ℝ) a) ↔ k ≤ n := by
    intro n
    have hpow : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    constructor
    · intro hin
      by_contra hcon
      rw [not_le] at hcon
      have hle : (2 : ℝ) ^ (n + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have hmul : a * 2 ^ (n + 1) ≤ a * 2 ^ k := by nlinarith
      have h2 := hin.2
      rw [div_lt_iff₀ hpow] at h2
      linarith
    · intro hkn
      refine ⟨div_pos htpos hpow, ?_⟩
      rw [div_lt_iff₀ hpow]
      have hle : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hmul : a * 2 ^ (k + 1) ≤ a * 2 ^ (n + 1) := by nlinarith
      linarith
  have hterm : ∀ n : ℕ, ((1 : ℂ) / 2) ^ (n + 1) * burnolAperturePart a f (t / 2 ^ (n + 1)) =
      if k ≤ n then c * ((1 : ℂ) / 2) ^ (n + 1) else 0 := by
    intro n
    rw [burnolAperturePart]
    by_cases hkn : k ≤ n
    · rw [if_pos ((hmem n).mpr hkn), if_pos hkn, hf _ ((hmem n).mpr hkn)]
      ring
    · rw [if_neg (fun hc => hkn ((hmem n).mp hc)), if_neg hkn, mul_zero]
  have hgeom : HasSum (fun n : ℕ => if k ≤ n then c * ((1 : ℂ) / 2) ^ (n + 1) else 0)
      (c * ((1 : ℂ) / 2) ^ k) := by
    have hbase : HasSum (fun n : ℕ => ((1 : ℂ) / 2) ^ n) ((1 - (1 : ℂ) / 2)⁻¹) :=
      hasSum_geometric_of_norm_lt_one (by norm_num)
    have hscaled := hbase.mul_left (c * ((1 : ℂ) / 2) ^ (k + 1))
    have hval : c * ((1 : ℂ) / 2) ^ (k + 1) * (1 - (1 : ℂ) / 2)⁻¹ = c * ((1 : ℂ) / 2) ^ k := by
      rw [pow_succ]
      norm_num
      ring
    rw [hval] at hscaled
    have hfun : (fun n : ℕ => c * ((1 : ℂ) / 2) ^ (k + 1) * ((1 : ℂ) / 2) ^ n) =
        fun n : ℕ => (fun m : ℕ => if k ≤ m then c * ((1 : ℂ) / 2) ^ (m + 1) else 0) (n + k) := by
      funext n
      show c * ((1 : ℂ) / 2) ^ (k + 1) * ((1 : ℂ) / 2) ^ n =
        if k ≤ n + k then c * ((1 : ℂ) / 2) ^ (n + k + 1) else 0
      rw [if_pos (by omega), mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hfun] at hscaled
    have hshift := (hasSum_nat_add_iff (f := fun m : ℕ =>
      if k ≤ m then c * ((1 : ℂ) / 2) ^ (m + 1) else 0) k).mp hscaled
    have hzero : ∑ i ∈ Finset.range k,
        (if k ≤ i then c * ((1 : ℂ) / 2) ^ (i + 1) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [if_neg (by omega)]
    rwa [hzero, add_zero] at hshift
  have hsum : burnolDyadicLadder (burnolAperturePart a f) t = c * ((1 : ℂ) / 2) ^ k := by
    rw [burnolDyadicLadder, tsum_congr hterm]
    exact hgeom.tsum_eq
  rw [burnolApertureCommutator, burnolAperturePart, if_neg hnotmem, hsum]
  ring

/-! ## The exact squared norm of the staircase -/

theorem burnolDyadicShells_disjoint {a : ℝ} (ha : 0 < a) :
    Pairwise (Function.onFun Disjoint
      (fun k : ℕ => Ico (a * 2 ^ k) (a * 2 ^ (k + 1)))) := by
  have hkey : ∀ i j : ℕ, i < j →
      Disjoint (Ico (a * 2 ^ i) (a * 2 ^ (i + 1))) (Ico (a * 2 ^ j) (a * 2 ^ (j + 1))) := by
    intro i j hlt
    refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
    have hstep : a * 2 ^ (i + 1) ≤ a * 2 ^ j := by
      have h2 : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    exact absurd hx.2 (not_lt.mpr (le_trans hstep hx'.1))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hkey i j h
  · exact (hkey j i h).symm

theorem burnolDyadicShells_cover {a : ℝ} (ha : 0 < a) :
    Ici a = ⋃ k : ℕ, Ico (a * 2 ^ k) (a * 2 ^ (k + 1)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨k, hk1, hk2⟩ := exists_burnolDyadicShell ha ht
    exact Set.mem_iUnion.mpr ⟨k, ⟨hk1, hk2⟩⟩
  · intro ht
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
    have hone : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hle : a ≤ a * 2 ^ k := by nlinarith
    exact le_trans hle hk.1

/-- **Exact `L²` norm of the aperture commutator.** -/
theorem lintegral_burnolApertureCommutator_normSq {a : ℝ} {c : ℂ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : ∀ s, s ∈ Ioo (0 : ℝ) a → f s = c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖burnolApertureCommutator a f t‖ ^ 2) =
      ENNReal.ofReal (2 * a * ‖c‖ ^ 2) := by
  have hsplit : Ioi (0 : ℝ) = Ioo (0 : ℝ) a ∪ Ici a := (Set.Ioo_union_Ici_eq_Ioi ha).symm
  have hdisj : Disjoint (Ioo (0 : ℝ) a) (Ici a) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx' (not_le.mpr hx.2)
  have hinner : ∫⁻ t in Ioo (0 : ℝ) a,
      ENNReal.ofReal (‖burnolApertureCommutator a f t‖ ^ 2) = 0 := by
    have h0 : EqOn (fun t => ENNReal.ofReal (‖burnolApertureCommutator a f t‖ ^ 2))
        (fun _ => (0 : ENNReal)) (Ioo (0 : ℝ) a) := by
      intro t ht
      simp only
      rw [burnolApertureCommutator_eq_zero_of_mem ht, norm_zero]
      norm_num
    rw [setLIntegral_congr_fun measurableSet_Ioo h0, lintegral_zero]
  have hshell : ∀ k : ℕ, ∫⁻ t in Ico (a * 2 ^ k) (a * 2 ^ (k + 1)),
      ENNReal.ofReal (‖burnolApertureCommutator a f t‖ ^ 2) =
        ENNReal.ofReal (a * ‖c‖ ^ 2 * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hval : ∀ t ∈ Ico (a * 2 ^ k) (a * 2 ^ (k + 1)),
        ENNReal.ofReal (‖burnolApertureCommutator a f t‖ ^ 2) =
          ENNReal.ofReal (‖c‖ ^ 2 * (1 / 4 : ℝ) ^ k) := by
      intro t ht
      rw [burnolApertureCommutator_shell ha hf ht.1 ht.2, norm_mul, norm_neg, norm_pow,
        show ‖(1 : ℂ) / 2‖ = (1 / 2 : ℝ) by norm_num, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    rw [setLIntegral_congr_fun measurableSet_Ico hval, setLIntegral_const,
      Real.volume_Ico, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hstep : a * 2 ^ (k + 1) - a * 2 ^ k = a * 2 ^ k := by ring
    rw [hstep, div_pow, one_pow, div_pow, one_pow]
    field_simp
    ring_nf
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, Nat.mul_comm 2 k]
  have hsummable : Summable (fun k : ℕ => a * ‖c‖ ^ 2 * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htsum : ∑' k : ℕ, (a * ‖c‖ ^ 2 * (1 / 2 : ℝ) ^ k) = 2 * a * ‖c‖ ^ 2 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    ring
  rw [hsplit, lintegral_union measurableSet_Ici hdisj, hinner, zero_add,
    burnolDyadicShells_cover ha,
    lintegral_iUnion (fun k => measurableSet_Ico) (burnolDyadicShells_disjoint ha)]
  rw [tsum_congr hshell, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsummable,
    htsum]

/-- **Exact same-fibre dyadic boundary transgression.**  At the fixed Route-R aperture the
difference of the two squared commutator norms is the oriented Burnol current. -/
theorem burnolApertureCommutator_normSq_difference (rho : ℂ) {f g : ℝ → ℂ}
    (hf : ∀ s, s ∈ Ioo (0 : ℝ) (1 / 2) → f s = burnolFirstWallHead rho)
    (hg : ∀ s, s ∈ Ioo (0 : ℝ) (1 / 2) → g s = burnolFirstWallCosineHead rho) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖burnolApertureCommutator (1 / 2) f t‖ ^ 2)).toReal -
        (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (‖burnolApertureCommutator (1 / 2) g t‖ ^ 2)).toReal =
      burnolCartierDividedShiftHeadFlux rho := by
  rw [lintegral_burnolApertureCommutator_normSq (by norm_num) hf,
    lintegral_burnolApertureCommutator_normSq (by norm_num) hg,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ← burnolFirstWallResidue_sub_cosineResidue_re_eq_headFlux,
    burnolFirstWallResidue_sub_cosineResidue_re]
  ring

end RHTower
