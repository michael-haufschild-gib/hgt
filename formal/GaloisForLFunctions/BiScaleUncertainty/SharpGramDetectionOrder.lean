import GaloisForLFunctions.BiScaleUncertainty.SharpCycleGramRealization

/-!
# Exact Gram-determinant detection order

For the literal separated smooth source, opposite amplitudes are distinguished
by a Gram determinant of size n exactly when the amplitude is nonzero and n
exceeds the gap. An explicit minimal cycle detects the sign; adding a distant
sample multiplies both determinants by their common positive mass.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SharpCycle
open SeparatedCycle (gramDet rawProduct)
set_option autoImplicit false

def GramDetects (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) : Prop :=
  ∃ t : Fin n → ℝ, gramDet (source T (-a)) n t ≠ gramDet (source T a) n t

/-- Every determinant below the strict cycle threshold agrees at every configuration. -/
theorem gram_same_or_order (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) (t : Fin n → ℝ) :
    gramDet (source T (-a)) n t = gramDet (source T a) n t ∨ (T : ℝ) < n := by
  by_cases ht : (T : ℝ) < n
  · exact Or.inr ht
  left
  dsimp only [gramDet]
  rw [Matrix.det_apply, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  apply congrArg (fun z : ℝ => Equiv.Perm.sign σ • z)
  let l := List.ofFn (fun i => t (σ i) - t i)
  have hs : l.sum = 0 := by
    dsimp [l]
    rw [List.sum_ofFn, Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
  have ho : ¬ (T : ℝ) < l.length := by simpa only [l, List.length_ofFn] using ht
  have he := (closed_product_same_or_order T a ⟨l, hs⟩).resolve_right ho
  simpa only [rawProduct, l, List.map_ofFn, List.prod_ofFn, Function.comp_def] using he

def farSample (T : Ioi (2 : ℝ)) (n : ℕ) (t : Fin n → ℝ) : ℝ :=
  (∑ i, |t i|) + T + 2

def paddedSamples (T : Ioi (2 : ℝ)) (n : ℕ) (t : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (farSample T n t) t

private theorem farSample_gap (T : Ioi (2 : ℝ)) (n : ℕ) (t : Fin n → ℝ) (i : Fin n) :
    (T : ℝ) + 1 < farSample T n t - t i := by
  have hs : |t i| ≤ ∑ j, |t j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
  have ht := le_abs_self (t i)
  dsimp only [farSample]
  linarith only [hs, ht]

private theorem source_zero_right (T : Ioi (2 : ℝ)) (a x : ℝ)
    (hx : (T : ℝ) + 1 ≤ x) : autocorr (source T a) x = 0 := by
  have hT : (2 : ℝ) < T := T.property
  have h0 : 1 ≤ x := by linarith only [hx, hT]
  have hm : 1 ≤ x - T := by linarith only [hx]
  have hp : 1 ≤ x + T := by linarith only [hx, hT]
  rw [source_correlation,
    (seed_correlation_eq_zero_iff _).mpr (h0.trans (le_abs_self _)),
    (seed_correlation_eq_zero_iff _).mpr (hm.trans (le_abs_self _)),
    (seed_correlation_eq_zero_iff _).mpr (hp.trans (le_abs_self _))]
  ring

/-- The explicit separated point adds a positive diagonal factor. -/
theorem gramDet_padded (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) (t : Fin n → ℝ) :
    gramDet (source T a) (n + 1) (paddedSamples T n t) =
      autocorr (source T a) 0 * gramDet (source T a) n t := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => autocorr (source T a) (paddedSamples T n t i - paddedSamples T n t j)
  have hrow (j : Fin n) : A 0 j.succ = 0 := by
    simpa only [A, paddedSamples, Fin.cons_zero, Fin.cons_succ] using
      source_zero_right T a (farSample T n t - t j) (farSample_gap T n t j).le
  have h00 : A 0 0 = autocorr (source T a) 0 := by simp [A, paddedSamples]
  have hm : A.submatrix Fin.succ (0 : Fin (n + 1)).succAbove =
      (fun i j : Fin n => autocorr (source T a) (t i - t j)) := by
    ext i j
    simp [A, paddedSamples, Matrix.submatrix_apply]
  change A.det = autocorr (source T a) 0 *
    (Matrix.det (fun i j : Fin n => autocorr (source T a) (t i - t j)))
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, h00, hrow, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, hm]

private theorem gramDetects_succ (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ)
    (h : GramDetects T a n) : GramDetects T a (n + 1) := by
  rcases h with ⟨t, ht⟩
  refine ⟨paddedSamples T n t, ?_⟩
  intro he
  rw [gramDet_padded, gramDet_padded] at he
  have hm : autocorr (source T (-a)) 0 = autocorr (source T a) 0 := by
    simp only [source_mass, neg_sq]
  rw [hm] at he
  exact ht (mul_left_cancel₀ (source_mass_pos T a).ne' he)

private theorem gramDetects_add (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ)
    (h : GramDetects T a n) (r : ℕ) : GramDetects T a (n + r) := by
  induction r with
  | zero => simpa only [Nat.add_zero] using h
  | succ r ih => simpa only [Nat.add_succ] using gramDetects_succ T a (n + r) ih

/-- Complete detection classification, with an actual configuration at every allowed order. -/
theorem gramDetects_iff (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) :
    GramDetects T a n ↔ a ≠ 0 ∧ (T : ℝ) < n := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨?_, (gram_same_or_order T a n t).resolve_left ht⟩
    intro ha
    subst a
    exact ht (by rw [neg_zero])
  · rintro ⟨ha, ht⟩
    have hfirst : GramDetects T a (firstOrder T) := by
      rw [← cycleExcess_size T]
      exact ⟨cycleSamples T, (gram_cycle_distinct_iff T a).mpr ha⟩
    have hT0 : 0 ≤ (T : ℝ) := by linarith only [show (2 : ℝ) < T from T.property]
    have hf : ⌊(T : ℝ)⌋₊ < n := (Nat.floor_lt hT0).mpr ht
    have hq : firstOrder T ≤ n := by dsimp only [firstOrder]; omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
    exact gramDetects_add T a (firstOrder T) hfirst r

theorem gramDetects_iff_floor (T : Ioi (2 : ℝ)) (a : ℝ) (n : ℕ) :
    GramDetects T a n ↔ a ≠ 0 ∧ ⌊(T : ℝ)⌋₊ < n := by
  rw [gramDetects_iff,
    Nat.floor_lt (by linarith only [show (2 : ℝ) < T from T.property] : 0 ≤ (T : ℝ))]

theorem firstOrder_gramDetects_iff (T : Ioi (2 : ℝ)) (a : ℝ) :
    GramDetects T a (firstOrder T) ↔ a ≠ 0 := by
  rw [gramDetects_iff_floor]
  simp [firstOrder]

theorem lower_gram_orders_agree (T : Ioi (2 : ℝ)) (a : ℝ) (n : Fin (firstOrder T)) :
    ¬ GramDetects T a n := by
  rw [gramDetects_iff_floor]
  intro h
  have hn := n.isLt
  dsimp only [firstOrder] at hn
  omega

/-- Smooth equal-mass polar-distinct sources with the exact Gram detection threshold. -/
theorem sharp_gram_polar_pair (T : Ioi (2 : ℝ)) :
    ∃ f g : C_c(ℝ, ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (g : ℝ → ℝ) ∧
      0 < autocorr f 0 ∧ autocorr g 0 = autocorr f 0 ∧
      normalizedPolarMoment f = 0 ∧ 0 < normalizedPolarMoment g ∧
      ∀ n : ℕ, (∃ t : Fin n → ℝ, gramDet g n t ≠ gramDet f n t) ↔ (T : ℝ) < n := by
  refine ⟨source T (polarAmplitude T), source T (-polarAmplitude T),
    source_smooth _ _, source_smooth _ _, source_mass_pos _ _, ?_, source_polar_zero T, ?_, ?_⟩
  · simp only [source_mass, neg_sq]
  · rw [source_polar_plus]
    exact mul_pos (by positivity) seed_polar_pos
  · intro n
    change GramDetects T (polarAmplitude T) n ↔ (T : ℝ) < n
    constructor
    · intro h
      exact ((gramDetects_iff T (polarAmplitude T) n).mp h).2
    · intro h
      exact (gramDetects_iff T (polarAmplitude T) n).mpr ⟨(polarAmplitude_pos T).ne', h⟩

end GaloisForLFunctions.BiScaleUncertainty.SharpCycle
