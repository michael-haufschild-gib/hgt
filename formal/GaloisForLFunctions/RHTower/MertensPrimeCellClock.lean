import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Prime reciprocal cells and the Mertens step clock

Give the prime `p` the half-open cell `I_p = [y_p, y_p + 1/p)` of length `1/p`, where
`y_p = ∑_{q < p} 1/q`.  Consecutive cells abut, and the cells tile `[0, ∞)` because the prime
harmonic series diverges.  On `I_p` the step clock is `φ(y) = log log p + B`, with `B` the
Meissel–Mertens constant.  Mertens' second theorem with its decaying error `O(1/log p)` says exactly

`|φ(y) - y| ≤ D e^{-y}`    for all `y ≥ 0`,

because `y ≈ log log p + B` on `I_p`.  The shells `S_n = {p : n ≤ log log p < n + 1}` are finite and
their reciprocal masses `∑_{p ∈ S_n} 1/p` tend to `1`.
-/

namespace RHTower

open Filter Topology Set MeasureTheory

noncomputable section
set_option autoImplicit false

/-! ### Prime reciprocal mass -/

/-- The reciprocal mass of the primes below `n`: `∑_{p < n} 1/p`. -/
def primeRecipMass (n : ℕ) : ℝ := ∑ p ∈ Nat.primesBelow n, (1 : ℝ) / p

theorem primeRecipMass_zero : primeRecipMass 0 = 0 := by
  simp [primeRecipMass]

theorem primeRecipMass_nonneg (n : ℕ) : 0 ≤ primeRecipMass n :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem primeRecipMass_succ (n : ℕ) :
    primeRecipMass (n + 1) = primeRecipMass n + if n.Prime then (1 : ℝ) / n else 0 := by
  unfold primeRecipMass
  rw [Nat.primesBelow_succ]
  split_ifs
  · rw [Finset.sum_insert (Nat.notMem_primesBelow n), add_comm]
  · rw [add_zero]

theorem primeRecipMass_mono : Monotone primeRecipMass := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [primeRecipMass_succ]
  split_ifs
  · exact le_add_of_nonneg_right (by positivity)
  · exact (add_zero _).ge

theorem primeRecipMass_succ_eq_mertensS (N : ℕ) : primeRecipMass (N + 1) = Sieve.mertensS N := rfl

/-- The prime reciprocal masses are unbounded (Euler). -/
theorem exists_lt_primeRecipMass (y : ℝ) : ∃ n, y < primeRecipMass n := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply Nat.Primes.not_summable_one_div
  refine summable_of_sum_le (c := y) (fun p => by positivity) fun u => ?_
  obtain ⟨n, hn⟩ : ∃ n, ∀ p ∈ u, (p : ℕ) < n :=
    ⟨u.sup (fun p => (p : ℕ)) + 1, fun p hp => Nat.lt_succ_of_le (Finset.le_sup (f := fun p :
      Nat.Primes => (p : ℕ)) hp)⟩
  calc ∑ p ∈ u, 1 / ((p : ℕ) : ℝ) = ∑ p ∈ u.map (Function.Embedding.subtype _), (1 : ℝ) / p := by
        rw [Finset.sum_map]; rfl
    _ ≤ primeRecipMass n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro m hm
        obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hm
        exact Nat.mem_primesBelow.mpr ⟨hn p hp, p.property⟩
    _ ≤ y := h n

/-! ### Mertens' second theorem at a real cut -/

/-- The constant in `|∑_{p<X} 1/p - log log X - B| ≤ D / log X`. -/
def primeRecipMassConst : ℝ := 4 * Sieve.mertensFirstConst + 2

theorem primeRecipMassConst_nonneg : 0 ≤ primeRecipMassConst := by
  unfold primeRecipMassConst
  linarith [Sieve.mertensFirstConst_nonneg]

/-- **Mertens' second theorem at a real cut.**  For `X ≥ 3`,
`|∑_{p<X} 1/p - log log X - B| ≤ D / log X`. -/
theorem abs_primeRecipMass_ceil_sub_le {X : ℝ} (hX : 3 ≤ X) :
    |primeRecipMass ⌈X⌉₊ - Real.log (Real.log X) - Sieve.meisselMertensConst| ≤
      primeRecipMassConst / Real.log X := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hceil : ⌈X⌉₊ = (⌈X⌉₊ - 1) + 1 := by
    have : 0 < ⌈X⌉₊ := Nat.ceil_pos.mpr (by linarith)
    omega
  set N := ⌈X⌉₊ - 1 with hNdef
  have hNX : (N : ℝ) < X := by
    have h1 := Nat.ceil_lt_add_one hX0
    rw [hceil] at h1
    push_cast at h1
    linarith
  have hXN : X ≤ N + 1 := by
    have h1 := Nat.le_ceil X
    rw [hceil] at h1
    push_cast at h1
    exact h1
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hA := Sieve.abs_mertensS_sub_logLog_sub_const_le hN2
  rw [← primeRecipMass_succ_eq_mertensS, ← hceil] at hA
  have hlogXN : Real.log X - Real.log N ≤ 1 / N := by
    have h := Real.log_le_sub_one_of_pos (x := X / N) (by positivity)
    rw [Real.log_div (by linarith) (by linarith)] at h
    have : X / N - 1 ≤ 1 / N := by
      rw [div_sub_one (by linarith), div_le_div_iff_of_pos_right (by linarith)]
      linarith
    linarith
  have hlogle : Real.log N ≤ Real.log X := Real.log_le_log (by linarith) hNX.le
  have hll0 : 0 ≤ Real.log (Real.log X) - Real.log (Real.log N) := by
    have := Real.log_le_log hlogN hlogle
    linarith
  have hll1 : Real.log (Real.log X) - Real.log (Real.log N) ≤ 1 / (2 * Real.log N) := by
    have h := Real.log_le_sub_one_of_pos (x := Real.log X / Real.log N) (by positivity)
    rw [Real.log_div hlogX.ne' hlogN.ne'] at h
    have h2 : Real.log X / Real.log N - 1 ≤ 1 / (2 * Real.log N) := by
      rw [div_sub_one hlogN.ne', div_le_div_iff₀ hlogN (by positivity)]
      have : Real.log X - Real.log N ≤ 1 / 2 :=
        hlogXN.trans (by rw [div_le_iff₀ (by linarith)]; linarith)
      nlinarith
    linarith
  have hX2 : Real.log X ≤ 2 * Real.log N := by
    rw [← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    rw [show ((N : ℝ) ^ (2 : ℝ)) = N * N by rw [Real.rpow_two]; ring]
    nlinarith
  have hc : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    linarith [Sieve.mertensFirstConst_nonneg]
  have hsplit : primeRecipMass ⌈X⌉₊ - Real.log (Real.log X) - Sieve.meisselMertensConst =
      (primeRecipMass ⌈X⌉₊ - Sieve.logLog N - Sieve.meisselMertensConst) -
        (Real.log (Real.log X) - Real.log (Real.log N)) := by
    unfold Sieve.logLog
    ring
  rw [hsplit]
  calc _ ≤ |primeRecipMass ⌈X⌉₊ - Sieve.logLog N - Sieve.meisselMertensConst| +
        |Real.log (Real.log X) - Real.log (Real.log N)| := abs_sub _ _
    _ ≤ (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log N + 1 / (2 * Real.log N) := by
        rw [abs_of_nonneg hll0]
        exact add_le_add hA hll1
    _ = (2 * Sieve.mertensFirstConst + 1) / Real.log N := by
        field_simp
        ring
    _ ≤ primeRecipMassConst / Real.log X := by
        unfold primeRecipMassConst
        rw [div_le_div_iff₀ hlogN hlogX]
        nlinarith

/-! ### Prime cells -/

/-- Left endpoint `y_p = ∑_{q < p} 1/q` of the cell of `p`. -/
def primeCellStart (p : ℕ) : ℝ := primeRecipMass p

/-- The cell `I_p = [y_p, y_p + 1/p)` of `p`. -/
def primeCell (p : ℕ) : Set ℝ := Ico (primeCellStart p) (primeCellStart p + 1 / p)

theorem primeCellStart_nonneg (p : ℕ) : 0 ≤ primeCellStart p := primeRecipMass_nonneg p

theorem primeCellStart_add {p : ℕ} (hp : p.Prime) :
    primeCellStart p + 1 / p = primeRecipMass (p + 1) := by
  rw [primeRecipMass_succ, if_pos hp]
  rfl

theorem measurableSet_primeCell (p : ℕ) : MeasurableSet (primeCell p) := measurableSet_Ico

theorem volume_primeCell (p : ℕ) :
    volume (primeCell p) = ENNReal.ofReal (1 / p) := by
  rw [primeCell, Real.volume_Ico]
  congr 1
  ring

theorem primeCell_subset_Ici (p : ℕ) : primeCell p ⊆ Ici 0 :=
  fun _ hy => (primeCellStart_nonneg p).trans hy.1

/-- Cells of distinct primes are ordered: the cell of `p < q` ends before the cell of `q` starts. -/
theorem primeCellStart_add_le {p q : ℕ} (hp : p.Prime) (hpq : p < q) :
    primeCellStart p + 1 / p ≤ primeCellStart q := by
  rw [primeCellStart_add hp]
  exact primeRecipMass_mono hpq

theorem disjoint_primeCell {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Disjoint (primeCell p) (primeCell q) := by
  rcases lt_or_gt_of_ne hpq with h | h
  · have := primeCellStart_add_le hp h
    exact Set.disjoint_left.mpr fun y hy1 hy2 => by
      simp only [primeCell, mem_Ico] at hy1 hy2
      linarith
  · have := primeCellStart_add_le hq h
    exact Set.disjoint_left.mpr fun y hy1 hy2 => by
      simp only [primeCell, mem_Ico] at hy1 hy2
      linarith

theorem pairwise_disjoint_primeCell :
    Pairwise (Function.onFun Disjoint fun p : Nat.Primes => primeCell p) :=
  fun p q hpq => disjoint_primeCell p.property q.property fun h => hpq (Subtype.ext h)

/-! ### The cell index -/

theorem exists_lt_primeRecipMass_succ (y : ℝ) : ∃ m, y < primeRecipMass (m + 1) := by
  obtain ⟨n, hn⟩ := exists_lt_primeRecipMass y
  exact ⟨n, hn.trans_le (primeRecipMass_mono (Nat.le_succ n))⟩

open Classical in
/-- The index of the cell containing `y`: the least `m` with `y < ∑_{p ≤ m} 1/p`. -/
def primeCellIndex (y : ℝ) : ℕ := Nat.find (exists_lt_primeRecipMass_succ y)

theorem measurable_primeCellIndex : Measurable primeCellIndex := by
  classical
  exact measurable_find exists_lt_primeRecipMass_succ fun k => measurableSet_Iio

theorem primeCellIndex_spec {y : ℝ} (hy : 0 ≤ y) :
    (primeCellIndex y).Prime ∧ y ∈ primeCell (primeCellIndex y) := by
  classical
  have hlt : y < primeRecipMass (primeCellIndex y + 1) :=
    Nat.find_spec (exists_lt_primeRecipMass_succ y)
  have hle : primeRecipMass (primeCellIndex y) ≤ y := by
    rcases Nat.eq_zero_or_eq_succ_pred (primeCellIndex y) with h | h
    · rw [h, primeRecipMass_zero]; exact hy
    · have hmin := Nat.find_min (exists_lt_primeRecipMass_succ y)
        (m := (primeCellIndex y).pred) (by unfold primeCellIndex at h ⊢; omega)
      rw [h]
      exact not_lt.mp hmin
  rw [primeRecipMass_succ] at hlt
  by_cases hp : (primeCellIndex y).Prime
  · rw [if_pos hp] at hlt
    exact ⟨hp, hle, hlt⟩
  · rw [if_neg hp, add_zero] at hlt
    exact absurd hle (not_le.mpr hlt)

theorem primeCellIndex_eq {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : y ∈ primeCell p) :
    primeCellIndex y = p := by
  classical
  unfold primeCellIndex
  rw [Nat.find_eq_iff]
  refine ⟨?_, fun k hk => ?_⟩
  · rw [← primeCellStart_add hp]; exact hy.2
  · exact not_lt.mpr ((primeRecipMass_mono (Nat.succ_le_of_lt hk)).trans hy.1)

theorem iUnion_primeCell : (⋃ p : Nat.Primes, primeCell p) = Ici 0 := by
  refine Subset.antisymm (iUnion_subset fun p => primeCell_subset_Ici p) fun y hy => ?_
  obtain ⟨hp, hmem⟩ := primeCellIndex_spec (mem_Ici.mp hy)
  exact mem_iUnion.mpr ⟨⟨_, hp⟩, hmem⟩

/-! ### The Mertens step clock -/

/-- The step clock `φ(y) = log log p + B` on the cell `I_p`. -/
def mertensStepClock (y : ℝ) : ℝ :=
  Real.log (Real.log (primeCellIndex y)) + Sieve.meisselMertensConst

theorem measurable_mertensStepClock : Measurable mertensStepClock :=
  (measurable_from_nat (f := fun m : ℕ => Real.log (Real.log m) + Sieve.meisselMertensConst)).comp
    measurable_primeCellIndex

theorem mertensStepClock_of_mem {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : y ∈ primeCell p) :
    mertensStepClock y = Real.log (Real.log p) + Sieve.meisselMertensConst := by
  rw [mertensStepClock, primeCellIndex_eq hp hy]

/-- The constant of the clock estimate at the scale `1/log p`. -/
def mertensClockConst : ℝ :=
  max (primeRecipMassConst + 1)
    ((|Real.log (Real.log 2)| + |Sieve.meisselMertensConst| + 1) * Real.log 2)

theorem mertensClockConst_nonneg : 0 ≤ mertensClockConst :=
  le_max_of_le_left (by linarith [primeRecipMassConst_nonneg])

/-- On the cell of `p`, the step clock is within `E / log p` of the identity. -/
theorem abs_mertensStepClock_sub_le_div_log {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : y ∈ primeCell p) :
    |mertensStepClock y - y| ≤ mertensClockConst / Real.log p := by
  rw [mertensStepClock_of_mem hp hy]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hy1 := hy.1
  have hy2 := hy.2
  unfold primeCellStart at hy1 hy2
  rcases hp.two_le.eq_or_lt with h2 | h3
  · subst h2
    have h0 : primeRecipMass 2 = 0 := by
      rw [primeRecipMass, show Nat.primesBelow 2 = ∅ by decide, Finset.sum_empty]
    rw [h0] at hy1 hy2
    norm_num at hy1 hy2
    have hb : |Real.log (Real.log ((2 : ℕ) : ℝ)) + Sieve.meisselMertensConst - y| ≤
        |Real.log (Real.log 2)| + |Sieve.meisselMertensConst| + 1 := by
      push_cast
      refine (abs_sub _ _).trans ?_
      refine add_le_add ((abs_add_le _ _)) ?_
      rw [abs_of_nonneg hy1]
      linarith
    calc _ ≤ |Real.log (Real.log 2)| + |Sieve.meisselMertensConst| + 1 := hb
      _ = (|Real.log (Real.log 2)| + |Sieve.meisselMertensConst| + 1) * Real.log 2 /
            Real.log ((2 : ℕ) : ℝ) := by push_cast; field_simp
      _ ≤ mertensClockConst / Real.log ((2 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (le_max_right _ _) hlog.le
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast h3
    have hM := abs_primeRecipMass_ceil_sub_le hp3
    rw [Nat.ceil_natCast] at hM
    have hinv : 1 / (p : ℝ) ≤ 1 / Real.log p :=
      one_div_le_one_div_of_le hlog ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
    have hsplit : Real.log (Real.log p) + Sieve.meisselMertensConst - y =
        -(primeRecipMass p - Real.log (Real.log p) - Sieve.meisselMertensConst) +
          (primeRecipMass p - y) := by ring
    rw [hsplit]
    have hy' : |primeRecipMass p - y| ≤ 1 / p := by
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ |primeRecipMass p - Real.log (Real.log p) - Sieve.meisselMertensConst| +
          |primeRecipMass p - y| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg]
      _ ≤ primeRecipMassConst / Real.log p + 1 / Real.log p := add_le_add hM (hy'.trans hinv)
      _ = (primeRecipMassConst + 1) / Real.log p := by ring
      _ ≤ mertensClockConst / Real.log p :=
          div_le_div_of_nonneg_right (le_max_left _ _) hlog.le

/-- **The Mertens clock estimate.**  There is `D ≥ 0` with `|φ(y) - y| ≤ D e^{-y}` for all `y ≥ 0`. -/
theorem exists_abs_mertensStepClock_sub_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y, 0 ≤ y → |mertensStepClock y - y| ≤ D * Real.exp (-y) := by
  set E := mertensClockConst
  set B := Sieve.meisselMertensConst
  have hE := mertensClockConst_nonneg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨E * Real.exp (B + E / Real.log 2), by positivity, fun y hy => ?_⟩
  obtain ⟨hp, hmem⟩ := primeCellIndex_spec hy
  set p := primeCellIndex y
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogp2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hmain := abs_mertensStepClock_sub_le_div_log hp hmem
  rw [mertensStepClock_of_mem hp hmem] at hmain
  have hEL : E / Real.log p ≤ E / Real.log 2 := div_le_div_of_nonneg_left hE hlog2 hlogp2
  have hyup : y ≤ Real.log (Real.log p) + B + E / Real.log 2 := by
    have := (abs_le.mp hmain).1
    linarith
  have hexp : Real.exp (-(B + E / Real.log 2)) / Real.log p ≤ Real.exp (-y) := by
    rw [div_le_iff₀ hlog]
    calc Real.exp (-(B + E / Real.log 2)) = Real.exp (-y) * Real.exp (y - (B + E / Real.log 2)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-y) * Real.log p := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          calc Real.exp (y - (B + E / Real.log 2)) ≤ Real.exp (Real.log (Real.log p)) :=
                Real.exp_le_exp.mpr (by linarith)
            _ = Real.log p := Real.exp_log hlog
  calc |mertensStepClock y - y| ≤ E / Real.log p := by
        rw [mertensStepClock_of_mem hp hmem]; exact hmain
    _ = E * Real.exp (B + E / Real.log 2) * (Real.exp (-(B + E / Real.log 2)) / Real.log p) := by
        rw [Real.exp_neg]
        field_simp
    _ ≤ E * Real.exp (B + E / Real.log 2) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ### Mertens shells -/

/-- The cut `⌈exp(exp c)⌉`, the least integer that is not below `exp(exp c)`. -/
def mertensShellCut (c : ℝ) : ℕ := ⌈Real.exp (Real.exp c)⌉₊

/-- The shell `S_n = {p : n ≤ log log p < n + 1}`. -/
def mertensShell (n : ℕ) : Finset Nat.Primes :=
  (Nat.primesBelow (mertensShellCut (n + 1)) \ Nat.primesBelow (mertensShellCut n)).preimage
    (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn

theorem lt_mertensShellCut_iff {p : ℕ} (hp : p.Prime) (c : ℝ) :
    p < mertensShellCut c ↔ Real.log (Real.log p) < c := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  rw [mertensShellCut, Nat.lt_ceil, ← Real.log_lt_iff_lt_exp (by linarith),
    ← Real.log_lt_iff_lt_exp hlog]

theorem mem_mertensShell {n : ℕ} {p : Nat.Primes} :
    p ∈ mertensShell n ↔
      (n : ℝ) ≤ Real.log (Real.log (p : ℕ)) ∧ Real.log (Real.log (p : ℕ)) < n + 1 := by
  rw [mertensShell, Finset.mem_preimage, Finset.mem_sdiff, Nat.mem_primesBelow,
    Nat.mem_primesBelow, lt_mertensShellCut_iff p.property, lt_mertensShellCut_iff p.property]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨not_lt.mp fun h => h2 ⟨h, p.property⟩, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2, p.property⟩, fun h => (not_lt.mpr h1) h.1⟩

theorem disjoint_mertensShell {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (mertensShell m) (mertensShell n) := by
  refine Finset.disjoint_left.mpr fun p hm hn => ?_
  rw [mem_mertensShell] at hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith [hm.2, hn.1]
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith [hn.2, hm.1]

/-- The reciprocal mass `m_n = ∑_{p ∈ S_n} 1/p` of a shell. -/
def mertensShellMass (n : ℕ) : ℝ := ∑ p ∈ mertensShell n, (1 : ℝ) / (p : ℕ)

theorem mertensShellMass_nonneg (n : ℕ) : 0 ≤ mertensShellMass n :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem mertensShellCut_mono {c d : ℝ} (h : c ≤ d) : mertensShellCut c ≤ mertensShellCut d :=
  Nat.ceil_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr h))

theorem mertensShellMass_eq (n : ℕ) :
    mertensShellMass n =
      primeRecipMass (mertensShellCut (n + 1)) - primeRecipMass (mertensShellCut n) := by
  classical
  unfold mertensShellMass mertensShell primeRecipMass
  rw [Finset.sum_preimage (fun p : Nat.Primes => (p : ℕ)) _ Subtype.val_injective.injOn
    (fun p : ℕ => (1 : ℝ) / p) fun p hp hnot =>
      absurd ⟨⟨p, (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2⟩, rfl⟩ hnot]
  refine Finset.sum_sdiff_eq_sub fun p hp => ?_
  rw [Nat.mem_primesBelow] at hp ⊢
  exact ⟨hp.1.trans_le (mertensShellCut_mono (by linarith)), hp.2⟩

theorem abs_primeRecipMass_mertensShellCut_sub_le {c : ℝ} (hc : 1 ≤ c) :
    |primeRecipMass (mertensShellCut c) - c - Sieve.meisselMertensConst| ≤
      primeRecipMassConst * Real.exp (-c) := by
  have hX : (3 : ℝ) ≤ Real.exp (Real.exp c) := by
    have h1 : Real.exp 1 ≤ Real.exp c := Real.exp_le_exp.mpr hc
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.exp 2 ≤ Real.exp (Real.exp c) := Real.exp_le_exp.mpr (by linarith)
    have h4 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  have h := abs_primeRecipMass_ceil_sub_le hX
  rw [Real.log_exp, Real.log_exp] at h
  rw [mertensShellCut, Real.exp_neg, ← div_eq_mul_inv]
  exact h

/-- **Shell masses tend to one.** -/
theorem tendsto_mertensShellMass : Tendsto mertensShellMass atTop (𝓝 1) := by
  set D := primeRecipMassConst
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |mertensShellMass n - 1| ≤ 2 * D * Real.exp (-(n : ℝ)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 := abs_primeRecipMass_mertensShellCut_sub_le (c := (n : ℝ) + 1) (by linarith)
    have h0 := abs_primeRecipMass_mertensShellCut_sub_le (c := (n : ℝ)) hn1
    have hsplit : mertensShellMass n - 1 =
        (primeRecipMass (mertensShellCut ((n : ℝ) + 1)) - ((n : ℝ) + 1) - Sieve.meisselMertensConst) -
          (primeRecipMass (mertensShellCut n) - n - Sieve.meisselMertensConst) := by
      rw [mertensShellMass_eq]; ring
    have hexp : Real.exp (-((n : ℝ) + 1)) ≤ Real.exp (-(n : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hD := primeRecipMassConst_nonneg
    rw [hsplit]
    calc _ ≤ D * Real.exp (-((n : ℝ) + 1)) + D * Real.exp (-(n : ℝ)) :=
          (abs_sub _ _).trans (add_le_add h1 h0)
      _ ≤ D * Real.exp (-(n : ℝ)) + D * Real.exp (-(n : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hexp hD) le_rfl
      _ = 2 * D * Real.exp (-(n : ℝ)) := by ring
  have hlim : Tendsto (fun n : ℕ => 2 * D * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 * D)
    simpa [Function.comp_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  exact hbound n hn

end

end RHTower
