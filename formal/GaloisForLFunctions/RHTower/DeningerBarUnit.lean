import GaloisForLFunctions.RHTower.DeningerBarDifferential

/-!
# The extra degeneracy of the entire word-height bar source

Prepending the unit letter multiplies the word length weight by `R` and leaves the product of the
letter heights unchanged, so the extra degeneracy is continuous with

`P_{k,R}(sc) = R · P_{k,R}(c)`,

exactly one exponential length step.  Its coefficient description reads off the tail of a word
whose first letter is the unit, and the words with unit first letter are exactly the words with
the unit inserted at the front.

* `deningerBarUnitCoe`, `deningerBarUnit` : the extra degeneracy.
* `deningerBarSeminormR_unit` : **the exact length-weight identity.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- **The extra degeneracy on coefficients**: prepend the unit letter. -/
def deningerBarUnitCoe (c : DeningerBarWord → ℂ) : DeningerBarWord → ℂ := fun w =>
  match w with
  | ⟨0, _⟩ => 0
  | ⟨r + 1, f⟩ => if f 0 = 0 then c (⟨r, Fin.tail f⟩ : DeningerBarWord) else 0

@[simp]
theorem deningerBarUnitCoe_one (c : DeningerBarWord → ℂ)
    (f : Fin 1 → DeningerLattice) :
    deningerBarUnitCoe c (⟨0, f⟩ : DeningerBarWord) = 0 := rfl

theorem deningerBarUnitCoe_succ (c : DeningerBarWord → ℂ) {r : ℕ}
    (f : Fin (r + 2) → DeningerLattice) :
    deningerBarUnitCoe c (⟨r + 1, f⟩ : DeningerBarWord)
      = if f 0 = 0 then c (⟨r, Fin.tail f⟩ : DeningerBarWord) else 0 := rfl

theorem deningerBarUnitCoe_insert_zero (c : DeningerBarWord → ℂ) {r : ℕ}
    (g : Fin (r + 1) → DeningerLattice) :
    deningerBarUnitCoe c (deningerInsertUnitWord (0 : Fin (r + 2)) g)
      = c (⟨r, g⟩ : DeningerBarWord) := by
  rw [deningerInsertUnitWord, deningerBarUnitCoe_succ,
    if_pos (deningerInsertUnit_zero_apply_zero g), deningerInsertUnit_zero_tail]

theorem deningerBarUnitCoe_insert_succ (c : DeningerBarWord → ℂ) {r : ℕ}
    (u : Fin (r + 1)) (f : Fin (r + 1) → DeningerLattice) (hf : f 0 ≠ 0) :
    deningerBarUnitCoe c (deningerInsertUnitWord u.succ f) = 0 := by
  rw [deningerInsertUnitWord, deningerBarUnitCoe_succ,
    if_neg (by rw [deningerInsertUnit_succ_apply_zero]; exact hf)]

/-! ## Linearity -/

theorem deningerBarUnitCoe_add (a b : DeningerBarWord → ℂ) :
    deningerBarUnitCoe (a + b) = deningerBarUnitCoe a + deningerBarUnitCoe b := by
  funext w
  obtain ⟨r, f⟩ := w
  cases r with
  | zero => simp
  | succ r =>
      rw [deningerBarUnitCoe_succ]
      show _ = deningerBarUnitCoe a (⟨r + 1, f⟩ : DeningerBarWord)
        + deningerBarUnitCoe b (⟨r + 1, f⟩ : DeningerBarWord)
      rw [deningerBarUnitCoe_succ, deningerBarUnitCoe_succ]
      by_cases h : f 0 = 0
      · rw [if_pos h, if_pos h, if_pos h]
        rfl
      · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem deningerBarUnitCoe_smul (t : ℂ) (a : DeningerBarWord → ℂ) :
    deningerBarUnitCoe (t • a) = t • deningerBarUnitCoe a := by
  funext w
  obtain ⟨r, f⟩ := w
  cases r with
  | zero => simp
  | succ r =>
      rw [deningerBarUnitCoe_succ]
      show _ = t * deningerBarUnitCoe a (⟨r + 1, f⟩ : DeningerBarWord)
      rw [deningerBarUnitCoe_succ]
      by_cases h : f 0 = 0
      · rw [if_pos h, if_pos h]
        rfl
      · rw [if_neg h, if_neg h, mul_zero]

/-! ## The length-weight identity -/

private theorem deningerBarUnit_slice {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe)
    (r : ℕ) :
    (Summable fun f : Fin (r + 2) → DeningerLattice =>
        deningerBarWeightR k R (⟨r + 1, f⟩ : DeningerBarWord) *
          ‖deningerBarUnitCoe (c : DeningerBarWord → ℂ) (⟨r + 1, f⟩ : DeningerBarWord)‖) ∧
      (∑' f : Fin (r + 2) → DeningerLattice,
          deningerBarWeightR k R (⟨r + 1, f⟩ : DeningerBarWord) *
            ‖deningerBarUnitCoe (c : DeningerBarWord → ℂ) (⟨r + 1, f⟩ : DeningerBarWord)‖)
        = R * deningerBarSliceR k R (c : DeningerBarWord → ℂ) r := by
  classical
  have hRpos : (0 : ℝ) < R := by linarith
  set F : (Fin (r + 2) → DeningerLattice) → ℝ := fun f =>
    deningerBarWeightR k R (⟨r + 1, f⟩ : DeningerBarWord) *
      ‖deningerBarUnitCoe (c : DeningerBarWord → ℂ) (⟨r + 1, f⟩ : DeningerBarWord)‖ with hF
  have hsupp : Function.support F ⊆
      Set.range (deningerInsertUnit (r := r) (0 : Fin (r + 2))) := by
    intro f hf
    rw [Function.mem_support, hF] at hf
    by_cases h : f 0 = 0
    · exact ⟨Fin.tail f, deningerInsertUnit_zero_of_apply_zero h⟩
    · refine absurd ?_ hf
      show deningerBarWeightR k R (⟨r + 1, f⟩ : DeningerBarWord) *
        ‖deningerBarUnitCoe (c : DeningerBarWord → ℂ) (⟨r + 1, f⟩ : DeningerBarWord)‖ = 0
      rw [deningerBarUnitCoe_succ, if_neg h, norm_zero, mul_zero]
  have hcompose : ∀ g : Fin (r + 1) → DeningerLattice,
      F (deningerInsertUnit (0 : Fin (r + 2)) g)
        = R * (deningerBarWeightR k R (⟨r, g⟩ : DeningerBarWord) *
            ‖(c : DeningerBarWord → ℂ) (⟨r, g⟩ : DeningerBarWord)‖) := by
    intro g
    have hw : deningerBarWeightR k R (⟨r + 1, deningerInsertUnit (0 : Fin (r + 2)) g⟩ :
        DeningerBarWord) = R * deningerBarWeightR k R (⟨r, g⟩ : DeningerBarWord) :=
      deningerBarWeightR_insert k R (0 : Fin (r + 2)) g
    rw [hF]
    show deningerBarWeightR k R (⟨r + 1, deningerInsertUnit (0 : Fin (r + 2)) g⟩ :
        DeningerBarWord) *
        ‖deningerBarUnitCoe (c : DeningerBarWord → ℂ)
          (deningerInsertUnitWord (0 : Fin (r + 2)) g)‖ = _
    rw [hw, deningerBarUnitCoe_insert_zero]
    ring
  have hsummable : Summable F := by
    refine (Function.Injective.summable_iff
      (deningerInsertUnit_injective (r := r) (0 : Fin (r + 2)))
      (fun f hf => ?_)).mp ?_
    · by_contra hne
      exact hf (hsupp (by rwa [Function.mem_support]))
    · refine ((deningerBarSlice_summable (k := k) hR c r).mul_left R).congr fun g => ?_
      exact (hcompose g).symm
  refine ⟨hsummable, ?_⟩
  have hreindex : (∑' f : Fin (r + 2) → DeningerLattice, F f)
      = ∑' g : Fin (r + 1) → DeningerLattice,
          F (deningerInsertUnit (0 : Fin (r + 2)) g) :=
    (Function.Injective.tsum_eq
      (deningerInsertUnit_injective (r := r) (0 : Fin (r + 2))) hsupp).symm
  rw [hreindex, tsum_congr hcompose,
    Summable.tsum_mul_left _ (deningerBarSlice_summable hR c r), deningerBarSliceR]

theorem deningerBarUnitCoe_mem (c : DeningerBarKothe) :
    deningerBarUnitCoe (c : DeningerBarWord → ℂ) ∈ DeningerBarKothe := by
  intro k
  have hR : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnn : ∀ w : DeningerBarWord,
      0 ≤ deningerBarKotheData.w k w *
        ‖deningerBarUnitCoe (c : DeningerBarWord → ℂ) w‖ := fun w =>
    mul_nonneg (deningerBarKotheData.pos k w).le (norm_nonneg _)
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun r => ?_, ?_⟩
  · cases r with
    | zero =>
        refine summable_of_hasFiniteSupport (Set.Finite.subset (Set.finite_empty) ?_)
        intro f hf
        rw [Function.mem_support] at hf
        exact absurd (by rw [deningerBarUnitCoe_one, norm_zero, mul_zero]) hf
    | succ r =>
        refine ((deningerBarUnit_slice (k := k) hR c r).1).congr fun f => ?_
        rw [deningerBarKotheData_eq_weightR]
  · have hshift : Summable fun r : ℕ =>
        ((k : ℝ) + 1) * deningerBarSliceR k ((k : ℝ) + 1) (c : DeningerBarWord → ℂ) r :=
      (deningerBarSliceR_summable hR c).mul_left _
    refine (summable_nat_add_iff 1).mp ?_
    refine hshift.congr fun r => ?_
    rw [← (deningerBarUnit_slice (k := k) hR c r).2]
    refine tsum_congr fun f => ?_
    rw [deningerBarKotheData_eq_weightR]

/-- **The extra degeneracy** of the entire word-height bar source. -/
def deningerBarUnit : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe where
  toFun c := ⟨deningerBarUnitCoe (c : DeningerBarWord → ℂ), deningerBarUnitCoe_mem c⟩
  map_add' a b := by
    ext w
    show deningerBarUnitCoe ((a + b : DeningerBarKothe) : DeningerBarWord → ℂ) w
        = ((⟨deningerBarUnitCoe (a : DeningerBarWord → ℂ), deningerBarUnitCoe_mem a⟩ +
            ⟨deningerBarUnitCoe (b : DeningerBarWord → ℂ), deningerBarUnitCoe_mem b⟩ :
              DeningerBarKothe) : DeningerBarWord → ℂ) w
    rw [Submodule.coe_add, deningerBarUnitCoe_add, Submodule.coe_add, Pi.add_apply]
  map_smul' t a := by
    ext w
    show deningerBarUnitCoe ((t • a : DeningerBarKothe) : DeningerBarWord → ℂ) w
        = ((t • (⟨deningerBarUnitCoe (a : DeningerBarWord → ℂ),
            deningerBarUnitCoe_mem a⟩ : DeningerBarKothe)) : DeningerBarWord → ℂ) w
    rw [Submodule.coe_smul, deningerBarUnitCoe_smul]

@[simp]
theorem deningerBarUnit_coe (c : DeningerBarKothe) (w : DeningerBarWord) :
    ((deningerBarUnit c : DeningerBarKothe) : DeningerBarWord → ℂ) w
      = deningerBarUnitCoe (c : DeningerBarWord → ℂ) w := rfl

/-- **The extra degeneracy costs exactly one exponential length step**:
`P_{k,R}(sc) = R · P_{k,R}(c)`. -/
theorem deningerBarSeminormR_unit {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe) :
    deningerBarSeminormR k R (deningerBarUnit c) = R * deningerBarSeminormR k R c := by
  have hslice : ∀ r : ℕ,
      deningerBarSliceR k R
          ((deningerBarUnit c : DeningerBarKothe) : DeningerBarWord → ℂ) (r + 1)
        = R * deningerBarSliceR k R (c : DeningerBarWord → ℂ) r := fun r =>
    (deningerBarUnit_slice hR c r).2
  have hzero : deningerBarSliceR k R
      ((deningerBarUnit c : DeningerBarKothe) : DeningerBarWord → ℂ) 0 = 0 := by
    rw [deningerBarSliceR]
    have hterm : ∀ f : Fin 1 → DeningerLattice,
        deningerBarWeightR k R (⟨0, f⟩ : DeningerBarWord) *
          ‖((deningerBarUnit c : DeningerBarKothe) : DeningerBarWord → ℂ)
            (⟨0, f⟩ : DeningerBarWord)‖ = 0 := by
      intro f
      rw [deningerBarUnit_coe, deningerBarUnitCoe_one, norm_zero, mul_zero]
    rw [tsum_congr hterm, tsum_zero]
  rw [deningerBarSeminormR_eq_tsum_slice hR (deningerBarUnit c),
    deningerBarSeminormR_eq_tsum_slice hR c,
    Summable.tsum_eq_zero_add (deningerBarSliceR_summable hR (deningerBarUnit c)),
    hzero, zero_add, tsum_congr hslice,
    Summable.tsum_mul_left _ (deningerBarSliceR_summable hR c)]

end

end RHTower
