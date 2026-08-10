import GaloisForLFunctions.RHTower.DeningerBarAlgebra
import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightPower

/-!
# Positive powers and the reflection relations on the bar source

Raising every letter of a word to a positive power multiplies the arithmetic character by that
power and raises the product of the letter heights to it, leaving the word length untouched.  The
induced push-forward on coefficients therefore rescales the height index of the two-parameter
seminorms,

`P_{k,R}(V_q c) = P_{qk,R}(c)`,

and commutes with the bar differential, because the unit letter is fixed by the power map.

Reflection sends the sector `γ` to the sector `-γ`, exchanges the two Hardy halves, and
anticommutes with the total prime-log generator.

* `deningerBarPower` : the power map with `deningerBarSeminormR_power`.
* `deningerBarPower_diff` : it is a chain map.
* `deningerBarReflect_sector`, `deningerBarReflect_hardy`, `deningerBarReflect_totalGenerator`.
-/

namespace RHTower

open GaloisForLFunctions

open scoped Classical

noncomputable section

/-! ## The power map on words -/

/-- Raise every letter of a word to the `q`-th power. -/
def deningerBarPowerWord (q : ℕ) (w : DeningerBarWord) : DeningerBarWord :=
  ⟨w.1, fun j => q • w.2 j⟩

/-- Divide every letter of a word by `q`. -/
def deningerBarDivWord (q : ℕ) (w : DeningerBarWord) : DeningerBarWord :=
  ⟨w.1, fun j => deningerDivExponent q (w.2 j)⟩

theorem deningerBarDivWord_powerWord {q : ℕ} (hq : 0 < q) (w : DeningerBarWord) :
    deningerBarDivWord q (deningerBarPowerWord q w) = w := by
  obtain ⟨r, f⟩ := w
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext j
  exact deningerDivExponent_nsmul hq (f j)

theorem deningerBarPowerWord_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (deningerBarPowerWord q) := by
  intro w w' h
  have hd := congrArg (deningerBarDivWord q) h
  rwa [deningerBarDivWord_powerWord hq, deningerBarDivWord_powerWord hq] at hd

@[simp]
theorem deningerBarPowerWord_length (q : ℕ) (w : DeningerBarWord) :
    deningerBarLength (deningerBarPowerWord q w) = deningerBarLength w := rfl

theorem deningerBarPowerWord_height (q : ℕ) (w : DeningerBarWord) :
    deningerBarHeight (deningerBarPowerWord q w) = deningerBarHeight w ^ q := by
  obtain ⟨r, f⟩ := w
  show (∏ j, deningerHeight (q • f j)) = (∏ j, deningerHeight (f j)) ^ q
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => deningerHeight_nsmul q (f j)

theorem deningerBarPowerWord_char (q : ℕ) (w : DeningerBarWord) :
    deningerBarChar (deningerBarPowerWord q w) = q • deningerBarChar w := by
  obtain ⟨r, f⟩ := w
  show (∑ j, q • f j) = q • ∑ j, f j
  rw [Finset.smul_sum]

/-! ## The power map on coefficients -/

/-- The coefficient sequence of the power map. -/
def deningerBarPowerCoe (q : ℕ) (c : DeningerBarWord → ℂ) : DeningerBarWord → ℂ :=
  fun w => if deningerBarPowerWord q (deningerBarDivWord q w) = w
    then c (deningerBarDivWord q w) else 0

theorem deningerBarPowerCoe_apply {q : ℕ} (hq : 0 < q) (c : DeningerBarWord → ℂ)
    (v : DeningerBarWord) :
    deningerBarPowerCoe q c (deningerBarPowerWord q v) = c v := by
  rw [deningerBarPowerCoe, deningerBarDivWord_powerWord hq, if_pos rfl]

theorem deningerBarPowerCoe_eq_zero {q : ℕ} (c : DeningerBarWord → ℂ)
    {w : DeningerBarWord} (hw : w ∉ Set.range (deningerBarPowerWord q)) :
    deningerBarPowerCoe q c w = 0 := by
  rw [deningerBarPowerCoe, if_neg]
  intro hc
  exact hw ⟨deningerBarDivWord q w, hc⟩

private theorem deningerBarPower_mem {q : ℕ} (hq : 0 < q) (c : DeningerBarKothe) :
    deningerBarPowerCoe q (c : DeningerBarWord → ℂ) ∈ DeningerBarKothe := by
  intro k
  have hR : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  refine (Function.Injective.summable_iff (f := fun w : DeningerBarWord =>
      deningerBarKotheData.w k w *
        ‖deningerBarPowerCoe q (c : DeningerBarWord → ℂ) w‖)
    (deningerBarPowerWord_injective hq) ?_).mp ?_
  · intro w hw
    rw [deningerBarPowerCoe_eq_zero _ hw, norm_zero, mul_zero]
  · refine (deningerBarSeminormR_summable (k := q * k) hR c).congr fun v => ?_
    show ((k : ℝ) + 1) ^ deningerBarLength v * deningerBarHeight v ^ (q * k) *
        ‖(c : DeningerBarWord → ℂ) v‖
      = deningerBarKotheData.w k (deningerBarPowerWord q v) *
        ‖deningerBarPowerCoe q (c : DeningerBarWord → ℂ) (deningerBarPowerWord q v)‖
    rw [deningerBarKotheData_w, deningerBarPowerWord_height, deningerBarPowerWord_length,
      deningerBarPowerCoe_apply hq, ← pow_mul]
    ring

/-- **The power map** `V_q` on the bar source. -/
def deningerBarPower (q : ℕ) (hq : 0 < q) : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe where
  toFun c := ⟨deningerBarPowerCoe q (c : DeningerBarWord → ℂ), deningerBarPower_mem hq c⟩
  map_add' a b := by
    ext w
    show deningerBarPowerCoe q ((a + b : DeningerBarKothe) : DeningerBarWord → ℂ) w = _
    simp only [Submodule.coe_add, Pi.add_apply, deningerBarPowerCoe]
    by_cases h : deningerBarPowerWord q (deningerBarDivWord q w) = w
    · simp [h]
    · simp [h]
  map_smul' t a := by
    ext w
    show deningerBarPowerCoe q ((t • a : DeningerBarKothe) : DeningerBarWord → ℂ) w = _
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, deningerBarPowerCoe]
    by_cases h : deningerBarPowerWord q (deningerBarDivWord q w) = w
    · simp [h]
    · simp [h]

@[simp]
theorem deningerBarPower_coe {q : ℕ} (hq : 0 < q) (c : DeningerBarKothe)
    (w : DeningerBarWord) :
    ((deningerBarPower q hq c : DeningerBarKothe) : DeningerBarWord → ℂ) w
      = deningerBarPowerCoe q (c : DeningerBarWord → ℂ) w := rfl

/-- **The power map rescales the height index**: `P_{k,R}(V_q c) = P_{qk,R}(c)`. -/
theorem deningerBarSeminormR_power {q : ℕ} (hq : 0 < q) {k : ℕ} {R : ℝ}
    (c : DeningerBarKothe) :
    deningerBarSeminormR k R (deningerBarPower q hq c)
      = deningerBarSeminormR (q * k) R c := by
  rw [deningerBarSeminormR_eq, deningerBarSeminormR_eq]
  rw [← Function.Injective.tsum_eq (deningerBarPowerWord_injective hq)
    (f := fun w : DeningerBarWord => deningerBarWeightR k R w *
      ‖((deningerBarPower q hq c : DeningerBarKothe) : DeningerBarWord → ℂ) w‖) ?_]
  · refine tsum_congr fun v => ?_
    simp only [deningerBarPower_coe, deningerBarPowerCoe_apply hq, deningerBarWeightR,
      deningerBarPowerWord_height, deningerBarPowerWord_length, ← pow_mul]
  · intro w hw
    rw [Function.mem_support] at hw
    by_contra hrange
    apply hw
    rw [deningerBarPower_coe, deningerBarPowerCoe_eq_zero _ hrange, norm_zero, mul_zero]

/-! ## The power map is a chain map -/

theorem deningerBarPowerWord_insert {r : ℕ} (q : ℕ) (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    deningerBarPowerWord q (deningerInsertUnitWord t f)
      = deningerInsertUnitWord t (fun j => q • f j) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  refine Fin.succAboveCases (α := fun i =>
      q • deningerInsertUnit t f i = deningerInsertUnit t (fun j => q • f j) i) t ?_ ?_ i
  · rw [deningerInsertUnit_same, deningerInsertUnit_same, smul_zero]
  · intro k
    rw [deningerInsertUnit_succAbove, deningerInsertUnit_succAbove]

/-- A word is a `q`-th power exactly when each of its letters is. -/
theorem deningerBarPowerWord_div_eq_iff (q : ℕ) (w : DeningerBarWord) :
    deningerBarPowerWord q (deningerBarDivWord q w) = w
      ↔ ∀ j, q • deningerDivExponent q (w.2 j) = w.2 j := by
  obtain ⟨r, f⟩ := w
  constructor
  · intro h j
    exact congrFun (eq_of_heq (Sigma.mk.inj_iff.mp h).2) j
  · intro h
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext j
    exact h j

theorem deningerBarPowerWord_insert_div_iff {r : ℕ} (q : ℕ) (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerLattice) :
    deningerBarPowerWord q (deningerBarDivWord q (deningerInsertUnitWord t f))
        = deningerInsertUnitWord t f
      ↔ deningerBarPowerWord q (deningerBarDivWord q (⟨r, f⟩ : DeningerBarWord))
        = (⟨r, f⟩ : DeningerBarWord) := by
  rw [deningerBarPowerWord_div_eq_iff, deningerBarPowerWord_div_eq_iff]
  constructor
  · intro h k
    have hk := h (t.succAbove k)
    show q • deningerDivExponent q (f k) = f k
    have hval : (deningerInsertUnitWord t f).snd (t.succAbove k) = f k :=
      deningerInsertUnit_succAbove t f k
    rwa [hval] at hk
  · intro h i
    refine Fin.succAboveCases (α := fun i =>
        q • deningerDivExponent q (deningerInsertUnit t f i)
          = deningerInsertUnit t f i) t ?_ ?_ i
    · rw [deningerInsertUnit_same]
      show q • deningerDivExponent q (0 : DeningerLattice) = 0
      have hz : deningerDivExponent q (0 : DeningerLattice) = 0 := by
        ext p
        show (0 : DeningerLattice) p / (q : ℤ) = 0
        simp
      rw [hz, smul_zero]
    · intro k
      rw [deningerInsertUnit_succAbove]
      exact h k

theorem deningerLattice_nsmul_eq_zero_iff {q : ℕ} (hq : 0 < q) (m : DeningerLattice) :
    q • m = 0 ↔ m = 0 := by
  constructor
  · intro h
    ext p
    have hp := congrArg (fun x : DeningerLattice => x p) h
    have hval : (q : ℤ) * m p = 0 := by
      have : (q • m) p = 0 := hp
      rwa [Finsupp.smul_apply, nsmul_eq_mul] at this
    have hqne : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have := (mul_eq_zero.mp hval).resolve_left hqne
    simpa using this
  · intro h
    rw [h, smul_zero]

/-- **The power map commutes with the bar differential.** -/
theorem deningerBarPower_diff {q : ℕ} (hq : 0 < q) (c : DeningerBarWord → ℂ) :
    deningerBarDiffCoe (deningerBarPowerCoe q c)
      = deningerBarPowerCoe q (deningerBarDiffCoe c) := by
  funext w
  obtain ⟨s, f⟩ := w
  by_cases hdiv : deningerBarPowerWord q (deningerBarDivWord q (⟨s, f⟩ : DeningerBarWord))
      = (⟨s, f⟩ : DeningerBarWord)
  · set g : Fin (s + 1) → DeningerLattice :=
      fun j => deningerDivExponent q (f j) with hg
    have hfg : ∀ j, q • g j = f j := (deningerBarPowerWord_div_eq_iff q _).mp hdiv
    have hfibre : ∀ j : Fin (s + 1),
        deningerBarFibreSum (deningerBarPowerCoe q c) f j
          = deningerBarFibreSum c g j := by
      intro j
      have hzero : f j = 0 ↔ g j = 0 := by
        rw [← hfg j, deningerLattice_nsmul_eq_zero_iff hq]
      have hins : ∀ t : Fin (s + 2),
          deningerBarPowerCoe q c (deningerInsertUnitWord t f)
            = c (deningerInsertUnitWord t g) := by
        intro t
        have hpow : deningerBarPowerWord q (deningerInsertUnitWord t g)
            = deningerInsertUnitWord t f := by
          rw [deningerBarPowerWord_insert]
          congr 1
          exact funext hfg
        rw [← hpow, deningerBarPowerCoe_apply hq]
      rw [deningerBarFibreSum, deningerBarFibreSum]
      by_cases h : f j = 0
      · rw [if_pos h, if_pos (hzero.mp h), hins]
      · rw [if_neg h, if_neg (fun hc => h (hzero.mpr hc)), hins, hins]
    have hrhs : deningerBarPowerCoe q (deningerBarDiffCoe c) (⟨s, f⟩ : DeningerBarWord)
        = deningerBarDiffCoe c (⟨s, g⟩ : DeningerBarWord) := by
      show (if deningerBarPowerWord q (deningerBarDivWord q (⟨s, f⟩ : DeningerBarWord))
          = (⟨s, f⟩ : DeningerBarWord) then
            deningerBarDiffCoe c (deningerBarDivWord q (⟨s, f⟩ : DeningerBarWord)) else 0)
        = deningerBarDiffCoe c (⟨s, g⟩ : DeningerBarWord)
      rw [if_pos hdiv]
      rfl
    rw [hrhs]
    show (∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) *
        deningerBarFibreSum (deningerBarPowerCoe q c) f j) = _
    show _ = ∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) * deningerBarFibreSum c g j
    exact Finset.sum_congr rfl fun j _ => by rw [hfibre j]
  · have hrhs : deningerBarPowerCoe q (deningerBarDiffCoe c) (⟨s, f⟩ : DeningerBarWord) = 0 := by
      rw [deningerBarPowerCoe, if_neg hdiv]
    rw [hrhs]
    have hins : ∀ t : Fin (s + 2),
        deningerBarPowerCoe q c (deningerInsertUnitWord t f) = 0 := by
      intro t
      show (if deningerBarPowerWord q (deningerBarDivWord q (deningerInsertUnitWord t f))
          = deningerInsertUnitWord t f then
            c (deningerBarDivWord q (deningerInsertUnitWord t f)) else 0) = 0
      rw [if_neg]
      intro hc
      exact hdiv ((deningerBarPowerWord_insert_div_iff q t f).mp hc)
    show (∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) *
        deningerBarFibreSum (deningerBarPowerCoe q c) f j) = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [deningerBarFibreSum]
    by_cases h : f j = 0
    · rw [if_pos h, hins, mul_zero]
    · rw [if_neg h, hins, hins, add_zero, mul_zero]

/-! ## Reflection relations -/

theorem deningerBarReflect_sector (γ : DeningerLattice) (c : DeningerBarWord → ℂ) :
    deningerBarCharMulCoe (fun m => if m = -γ then (1 : ℂ) else 0)
        (fun w => c (deningerBarReflectWord w))
      = fun w => deningerBarCharMulCoe (fun m => if m = γ then (1 : ℂ) else 0) c
          (deningerBarReflectWord w) := by
  funext w
  rw [deningerBarCharMulCoe_apply, deningerBarCharMulCoe_apply,
    deningerBarReflectWord_char]
  by_cases h : deningerBarChar w = -γ
  · have h' : -deningerBarChar w = γ := by rw [h, neg_neg]
    rw [if_pos h, if_pos h']
  · have h' : ¬ (-deningerBarChar w = γ) := by
      intro hc
      exact h (by rw [← hc, neg_neg])
    rw [if_neg h, if_neg h']

theorem deningerBarReflect_totalGenerator (c : DeningerBarWord → ℂ) :
    deningerBarCharMulCoe (fun m => ((deningerFreq m : ℝ) : ℂ))
        (fun w => c (deningerBarReflectWord w))
      = fun w => -(deningerBarCharMulCoe (fun m => ((deningerFreq m : ℝ) : ℂ)) c
          (deningerBarReflectWord w)) := by
  funext w
  rw [deningerBarCharMulCoe_apply, deningerBarCharMulCoe_apply,
    deningerBarReflectWord_char, deningerFreq_neg]
  push_cast
  ring

theorem deningerBarReflect_hardy (c : DeningerBarWord → ℂ) :
    deningerBarCharMulCoe (fun m => if 0 < deningerFreq m then (1 : ℂ) else 0)
        (fun w => c (deningerBarReflectWord w))
      = fun w => deningerBarCharMulCoe
          (fun m => if deningerFreq m < 0 then (1 : ℂ) else 0) c
          (deningerBarReflectWord w) := by
  funext w
  rw [deningerBarCharMulCoe_apply, deningerBarCharMulCoe_apply,
    deningerBarReflectWord_char, deningerFreq_neg]
  by_cases h : 0 < deningerFreq (deningerBarChar w)
  · have h' : -deningerFreq (deningerBarChar w) < 0 := by linarith
    rw [if_pos h', if_pos h]
  · have h' : ¬ (-deningerFreq (deningerBarChar w) < 0) := by
      intro hc
      exact h (by linarith)
    rw [if_neg h', if_neg h]

end

end RHTower
