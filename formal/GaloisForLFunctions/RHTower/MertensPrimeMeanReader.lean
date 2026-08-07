import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces

/-!
# The signed Mertens mean of a prime coefficient field

The weighted Euler coefficient spaces are built from the seminorm
`(1 / log X) · ∑_{p ≤ X} (log p / p) |b_p|`, which measures size.  Its signed companion

`M_X(b) = (1 / log X) · ∑_{p ≤ X} (log p / p) b_p`

is a *linear* functional, and it reads a coefficient: Mertens' first theorem normalises the constant
field to one, and the critical summable layer is exactly a class the functional annihilates.  So a
field differing from a constant by a critically summable error has that constant as its Mertens mean.

This is the linear reader that the layer file does not build; the layers themselves supply both of its
defining properties.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Signed logarithmic prime mean of a coefficient field at cutoff `X`. -/
def mertensPrimeMean (b : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * b n) / Real.log X

theorem tendsto_log_nat_atTop : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_const_div_log_nat (C : ℝ) :
    Tendsto (fun X : ℕ => C / Real.log X) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_log_nat_atTop

/-! ## The two reader properties -/

theorem mertensPrimeMean_unit_eq (X : ℕ) :
    mertensPrimeMean (fun _ => (1 : ℝ)) X =
      primeLogMass (fun _ => (1 : ℝ)) X / Real.log X := by
  rw [mertensPrimeMean, primeLogMass]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by simp

/-- **Mertens' first theorem is the reader normalisation.**  The constant field
has Mertens mean one. -/
theorem tendsto_mertensPrimeMean_unit :
    Tendsto (mertensPrimeMean fun _ => (1 : ℝ)) atTop (nhds 1) := by
  have hzero : Tendsto
      (fun X : ℕ => mertensPrimeMean (fun _ => (1 : ℝ)) X - 1) atTop (nhds 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_const_div_log_nat mertensPrimeConstant).eventually
        (gt_mem_nhds hε)] with X hX hlt
    have hlogX : 0 < Real.log X := log_cutoff_pos hX
    have hup := primeLogMass_unit_le X (by omega)
    have hlo := le_primeLogMass_unit X (by omega)
    have hC : mertensPrimeConstant < ε * Real.log X := by
      rw [div_lt_iff₀ hlogX] at hlt
      exact hlt
    rw [mertensPrimeMean_unit_eq, Real.norm_eq_abs, abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hlogX]
      nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hlogX]
      nlinarith
  have hsum := hzero.add (tendsto_const_nhds (x := (1 : ℝ)))
  simpa using hsum

theorem abs_mertensPrimeMean_le (b : ℕ → ℝ) {X : ℕ} (hX : 2 ≤ X) :
    |mertensPrimeMean b X| ≤ marcinkiewiczLogQuotient b X := by
  have hlogX : 0 < Real.log X := log_cutoff_pos hX
  rw [mertensPrimeMean, marcinkiewiczLogQuotient, abs_div,
    abs_of_pos hlogX]
  refine div_le_div_of_nonneg_right ?_ hlogX.le
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_of_eq (Finset.sum_congr rfl fun n hn => ?_)
  have hnp : n.Prime := (Finset.mem_filter.mp hn).2
  have hlogn : 0 ≤ Real.log n / n := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnp.two_le
    have : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
    positivity
  rw [abs_mul, abs_of_nonneg hlogn]

/-- The critical summable layer is annihilated by the Mertens mean. -/
theorem tendsto_mertensPrimeMean_zero_of_criticalSummable {b : ℕ → ℝ}
    (hb : MemCriticalSummableLayer b) :
    Tendsto (mertensPrimeMean b) atTop (nhds 0) := by
  set f : ℕ → ℝ :=
    {p : ℕ | p.Prime}.indicator fun n => Real.log n / n * |b n| with hf
  have hfnn : ∀ n, 0 ≤ f n := by
    intro n
    rw [hf]
    by_cases hn : n ∈ {p : ℕ | p.Prime}
    · rw [Set.indicator_of_mem hn]
      have hnp : n.Prime := hn
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnp.two_le
      have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
      positivity
    · rw [Set.indicator_of_notMem hn]
  have hmass : ∀ X : ℕ, primeLogMass b X ≤ ∑' n, f n := by
    intro X
    have hEq : primeLogMass b X =
        ∑ n ∈ Finset.Icc 1 X with n.Prime, f n := by
      rw [primeLogMass]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnp : n.Prime := (Finset.mem_filter.mp hn).2
      rw [hf, Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hnp)]
    rw [hEq]
    exact Summable.sum_le_tsum _ (fun n _ => hfnn n) hb
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_const_div_log_nat (∑' n, f n)).eventually (gt_mem_nhds hε)]
    with X hX hlt
  have hlogX : 0 < Real.log X := log_cutoff_pos hX
  have h1 := abs_mertensPrimeMean_le b hX
  have h2 : marcinkiewiczLogQuotient b X ≤ (∑' n, f n) / Real.log X := by
    rw [marcinkiewiczLogQuotient]
    exact div_le_div_of_nonneg_right (hmass X) hlogX.le
  rw [Real.norm_eq_abs]
  linarith

/-! ## The vanishing-tail layer is annihilated as well -/

/-- Heads are annihilated: a head mass is bounded uniformly in the cutoff. -/
theorem tendsto_mertensPrimeMean_head_zero (b : ℕ → ℝ) (P : ℕ) :
    Tendsto (mertensPrimeMean (primeCoefficientHead b P)) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_const_div_log_nat (primeLogMass b P)).eventually
      (gt_mem_nhds hε)] with X hX hlt
  have hlogX : 0 < Real.log X := log_cutoff_pos hX
  have h1 := abs_mertensPrimeMean_le (primeCoefficientHead b P) hX
  have h2 : marcinkiewiczLogQuotient (primeCoefficientHead b P) X ≤
      primeLogMass b P / Real.log X := by
    rw [marcinkiewiczLogQuotient]
    exact div_le_div_of_nonneg_right (primeLogMass_head_le b P X) hlogX.le
  rw [Real.norm_eq_abs]
  linarith

theorem mertensPrimeMean_head_add_tail (b : ℕ → ℝ) (P X : ℕ) :
    mertensPrimeMean b X =
      mertensPrimeMean (primeCoefficientHead b P) X +
        mertensPrimeMean (primeCoefficientTail b P) X := by
  rw [mertensPrimeMean, mertensPrimeMean, mertensPrimeMean, ← add_div,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hP : P < n
  · simp [primeCoefficientHead, primeCoefficientTail, hP]
  · simp [primeCoefficientHead, primeCoefficientTail, hP]

/-- **The vanishing-tail layer is annihilated by the Mertens mean.**  Strictly
stronger than the critically summable case, since `T_1 ⊆ M_0`. -/
theorem tendsto_mertensPrimeMean_zero_of_vanishingTail {b : ℕ → ℝ}
    (hb : MemVanishingTailLayer b) :
    Tendsto (mertensPrimeMean b) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨P, hP⟩ := hb (ε / 2) (by positivity)
  have hhead := tendsto_mertensPrimeMean_head_zero b P
  rw [NormedAddGroup.tendsto_nhds_zero] at hhead
  filter_upwards [eventually_ge_atTop 2, hhead (ε / 2) (by positivity)]
    with X hX hh
  have htail := abs_mertensPrimeMean_le (primeCoefficientTail b P) hX
  have hq := hP X hX
  have htri := abs_add_le (mertensPrimeMean (primeCoefficientHead b P) X)
    (mertensPrimeMean (primeCoefficientTail b P) X)
  rw [Real.norm_eq_abs] at hh ⊢
  rw [mertensPrimeMean_head_add_tail b P X]
  linarith

/-! ## The reader law -/

/-- **The Mertens mean reads the constant coefficient.**  A field differing from
a constant by an error with uniformly vanishing truncation tails has that
constant as its Mertens mean. -/
theorem tendsto_mertensPrimeMean_of_vanishingTail {b : ℕ → ℝ} {c : ℝ}
    (hb : MemVanishingTailLayer fun n => b n - c) :
    Tendsto (mertensPrimeMean b) atTop (nhds c) := by
  have hsplit : ∀ X : ℕ,
      mertensPrimeMean b X =
        c * mertensPrimeMean (fun _ => (1 : ℝ)) X +
          mertensPrimeMean (fun n => b n - c) X := by
    intro X
    have hnum : (∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * b n) =
        c * (∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * 1) +
          ∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * (b n - c) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [mertensPrimeMean, mertensPrimeMean, mertensPrimeMean, hnum, add_div,
      mul_div_assoc]
  have hlim := ((tendsto_mertensPrimeMean_unit.const_mul c).add
    (tendsto_mertensPrimeMean_zero_of_vanishingTail hb))
  rw [mul_one, add_zero] at hlim
  exact hlim.congr fun X => (hsplit X).symm

/-- The critically summable case, now a corollary of the vanishing-tail case
through the corpus inclusion `T_1 ⊆ M_0`. -/
theorem tendsto_mertensPrimeMean {b : ℕ → ℝ} {c : ℝ}
    (hb : MemCriticalSummableLayer fun n => b n - c) :
    Tendsto (mertensPrimeMean b) atTop (nhds c) :=
  tendsto_mertensPrimeMean_of_vanishingTail
    (memVanishingTailLayer_of_memCriticalSummableLayer hb)

/-- **The Mertens mean is blind to any single prime.**  A coordinate field is
critically summable, hence has mean zero: no individual prime contributes. -/
theorem tendsto_mertensPrimeMean_coordinate_zero (p : ℕ) :
    Tendsto (mertensPrimeMean (primeCoordinateField p)) atTop (nhds 0) :=
  tendsto_mertensPrimeMean_zero_of_criticalSummable
    primeCoordinateField_memCriticalSummableLayer

/-- **The constant is unique.**  A field cannot lie within the vanishing-tail
layer of two different constants; the Mertens mean is a genuine coordinate on
`M_0 + R·1`. -/
theorem mertensPrimeMean_const_unique {b : ℕ → ℝ} {c d : ℝ}
    (hc : MemVanishingTailLayer fun n => b n - c)
    (hd : MemVanishingTailLayer fun n => b n - d) : c = d :=
  tendsto_nhds_unique (tendsto_mertensPrimeMean_of_vanishingTail hc)
    (tendsto_mertensPrimeMean_of_vanishingTail hd)

/-! ## The vanishing-tail layer is a subspace -/

theorem primeLogMass_smul (k : ℝ) (b : ℕ → ℝ) (X : ℕ) :
    primeLogMass (fun n => k * b n) X = |k| * primeLogMass b X := by
  rw [primeLogMass, primeLogMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [abs_mul]
  ring

theorem marcinkiewiczLogQuotient_smul (k : ℝ) (b : ℕ → ℝ) (X : ℕ) :
    marcinkiewiczLogQuotient (fun n => k * b n) X =
      |k| * marcinkiewiczLogQuotient b X := by
  rw [marcinkiewiczLogQuotient, marcinkiewiczLogQuotient, primeLogMass_smul,
    mul_div_assoc]

theorem primeLogMass_add_le (b b' : ℕ → ℝ) (X : ℕ) :
    primeLogMass (fun n => b n + b' n) X ≤
      primeLogMass b X + primeLogMass b' X := by
  rw [primeLogMass, primeLogMass, primeLogMass, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  have hnn := primeLog_term_nonneg (fun _ => (1 : ℝ)) n
  have hterm : (0 : ℝ) ≤ Real.log n / n := by
    simpa using hnn
  have habs : |b n + b' n| ≤ |b n| + |b' n| := abs_add_le _ _
  nlinarith [habs, hterm]

theorem memVanishingTailLayer_smul {b : ℕ → ℝ}
    (hb : MemVanishingTailLayer b) (k : ℝ) :
    MemVanishingTailLayer fun n => k * b n := by
  intro ε hε
  rcases eq_or_ne k 0 with hk | hk
  · refine ⟨0, fun X hX => ?_⟩
    have hzero : ∀ n, primeCoefficientTail (fun n => k * b n) 0 n = 0 := by
      intro n
      rw [primeCoefficientTail, hk]
      split_ifs <;> simp
    have : marcinkiewiczLogQuotient
        (primeCoefficientTail (fun n => k * b n) 0) X = 0 := by
      rw [marcinkiewiczLogQuotient, primeLogMass]
      simp [hzero]
    rw [this]
    exact hε.le
  · have hkpos : 0 < |k| := abs_pos.mpr hk
    obtain ⟨P, hP⟩ := hb (ε / |k|) (by positivity)
    refine ⟨P, fun X hX => ?_⟩
    have hEq : primeCoefficientTail (fun n => k * b n) P =
        fun n => k * primeCoefficientTail b P n := by
      funext n
      rw [primeCoefficientTail, primeCoefficientTail]
      split_ifs <;> simp
    rw [hEq, marcinkiewiczLogQuotient_smul]
    have := hP X hX
    calc |k| * marcinkiewiczLogQuotient (primeCoefficientTail b P) X ≤
          |k| * (ε / |k|) := by
          exact mul_le_mul_of_nonneg_left this hkpos.le
      _ = ε := by field_simp

theorem marcinkiewiczLogQuotient_add_le (b b' : ℕ → ℝ) {X : ℕ} (hX : 2 ≤ X) :
    marcinkiewiczLogQuotient (fun n => b n + b' n) X ≤
      marcinkiewiczLogQuotient b X + marcinkiewiczLogQuotient b' X := by
  have hlogX : 0 < Real.log X := log_cutoff_pos hX
  rw [marcinkiewiczLogQuotient, marcinkiewiczLogQuotient,
    marcinkiewiczLogQuotient, ← add_div]
  exact div_le_div_of_nonneg_right (primeLogMass_add_le b b' X) hlogX.le

theorem memVanishingTailLayer_add {b b' : ℕ → ℝ}
    (hb : MemVanishingTailLayer b) (hb' : MemVanishingTailLayer b') :
    MemVanishingTailLayer fun n => b n + b' n := by
  intro ε hε
  obtain ⟨P₁, hP₁⟩ := hb (ε / 2) (by positivity)
  obtain ⟨P₂, hP₂⟩ := hb' (ε / 2) (by positivity)
  refine ⟨max P₁ P₂, fun X hX => ?_⟩
  have hlogX : 0 < Real.log X := log_cutoff_pos hX
  have hEq : primeCoefficientTail (fun n => b n + b' n) (max P₁ P₂) =
      fun n => primeCoefficientTail b (max P₁ P₂) n +
        primeCoefficientTail b' (max P₁ P₂) n := by
    funext n
    rw [primeCoefficientTail, primeCoefficientTail, primeCoefficientTail]
    split_ifs <;> simp
  have h1 : marcinkiewiczLogQuotient (primeCoefficientTail b (max P₁ P₂)) X ≤
      ε / 2 :=
    le_trans (by
      rw [marcinkiewiczLogQuotient, marcinkiewiczLogQuotient]
      exact div_le_div_of_nonneg_right
        (primeLogMass_tail_anti b (le_max_left P₁ P₂) X) hlogX.le)
      (hP₁ X hX)
  have h2 : marcinkiewiczLogQuotient (primeCoefficientTail b' (max P₁ P₂)) X ≤
      ε / 2 :=
    le_trans (by
      rw [marcinkiewiczLogQuotient, marcinkiewiczLogQuotient]
      exact div_le_div_of_nonneg_right
        (primeLogMass_tail_anti b' (le_max_right P₁ P₂) X) hlogX.le)
      (hP₂ X hX)
  rw [hEq, marcinkiewiczLogQuotient]
  have hadd := primeLogMass_add_le (primeCoefficientTail b (max P₁ P₂))
    (primeCoefficientTail b' (max P₁ P₂)) X
  rw [marcinkiewiczLogQuotient] at h1 h2
  rw [div_le_iff₀ hlogX] at h1 h2 ⊢
  linarith

/-! ## The other two layers are subspaces as well -/

theorem memMarcinkiewiczLogLayer_smul {b : ℕ → ℝ}
    (hb : MemMarcinkiewiczLogLayer b) (k : ℝ) :
    MemMarcinkiewiczLogLayer fun n => k * b n := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨|k| * C, fun X hX => ?_⟩
  rw [marcinkiewiczLogQuotient_smul]
  exact mul_le_mul_of_nonneg_left (hC X hX) (abs_nonneg k)

theorem memMarcinkiewiczLogLayer_add {b b' : ℕ → ℝ}
    (hb : MemMarcinkiewiczLogLayer b) (hb' : MemMarcinkiewiczLogLayer b') :
    MemMarcinkiewiczLogLayer fun n => b n + b' n := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨C', hC'⟩ := hb'
  refine ⟨C + C', fun X hX => ?_⟩
  exact le_trans (marcinkiewiczLogQuotient_add_le b b' hX)
    (add_le_add (hC X hX) (hC' X hX))

theorem criticalTerm_nonneg (b : ℕ → ℝ) (n : ℕ) :
    0 ≤ ({p : ℕ | p.Prime}.indicator fun n => Real.log n / n * |b n|) n := by
  by_cases hn : n ∈ {p : ℕ | p.Prime}
  · rw [Set.indicator_of_mem hn]
    exact primeLog_term_nonneg b n
  · rw [Set.indicator_of_notMem hn]

theorem memCriticalSummableLayer_smul {b : ℕ → ℝ}
    (hb : MemCriticalSummableLayer b) (k : ℝ) :
    MemCriticalSummableLayer fun n => k * b n := by
  refine (Summable.mul_left |k| hb).congr fun n => ?_
  by_cases hn : n ∈ {p : ℕ | p.Prime}
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, abs_mul]
    ring
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, mul_zero]

theorem memCriticalSummableLayer_add {b b' : ℕ → ℝ}
    (hb : MemCriticalSummableLayer b) (hb' : MemCriticalSummableLayer b') :
    MemCriticalSummableLayer fun n => b n + b' n := by
  refine Summable.of_nonneg_of_le (fun n => criticalTerm_nonneg _ n)
    (fun n => ?_) (Summable.add hb hb')
  by_cases hn : n ∈ {p : ℕ | p.Prime}
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn,
      Set.indicator_of_mem hn]
    have hterm : (0 : ℝ) ≤ Real.log n / n := by
      simpa using primeLog_term_nonneg (fun _ => (1 : ℝ)) n
    have habs : |b n + b' n| ≤ |b n| + |b' n| := abs_add_le _ _
    nlinarith [habs, hterm]
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn,
      Set.indicator_of_notMem hn]
    norm_num

end

end RHTower
