import GaloisForLFunctions.RHTower.Suzuki.SuzukiFlatFluxBlockValue

/-!
# The backward flux tail in unit blocks

A flux with no terminal charge is the backward integral of its source, so its size on a unit block
is at most the total mass of the source past that block.  Cutting the terminal ray into unit blocks
and using Cauchy–Schwarz on each one turns that into

`y_n ≤ Σ_{k ≥ 0} (block norm of the source at n+k)`,

and the exponentially localized block bound for the source turns *that* into the card's `(13)`

`y_n ≤ D₀ Σ_{k ≥ 0} (E f)_{n+k} + Σ_{k ≥ 0} h_{n+k}`.

Everything is in `ℝ≥0∞`, so the tail sums exist unconditionally and no integrability hypothesis on
the flux or the source is needed.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Cutting a terminal ray into unit blocks -/

theorem Ici_eq_iUnion_unitBlocks (a : ℝ) :
    Ici a = ⋃ k : ℕ, Ico (a + k) (a + k + 1) := by
  ext x
  simp only [mem_Ici, mem_iUnion, mem_Ico]
  constructor
  · intro hx
    refine ⟨⌊x - a⌋₊, ?_, ?_⟩
    · have h := Nat.floor_le (by linarith : (0 : ℝ) ≤ x - a)
      linarith
    · have h := Nat.lt_floor_add_one (x - a)
      linarith
  · rintro ⟨k, h1, _⟩
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

theorem pairwise_disjoint_unitBlocksNat (a : ℝ) :
    Pairwise (Function.onFun Disjoint (fun k : ℕ => Ico (a + k) (a + k + 1))) := by
  intro i j hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [mem_Ico] at hx hx'
  have h1 : (i : ℝ) < (j : ℝ) + 1 := by linarith [hx.1, hx'.2]
  have h2 : (j : ℝ) < (i : ℝ) + 1 := by linarith [hx'.1, hx.2]
  have h1' : i < j + 1 := by exact_mod_cast h1
  have h2' : j < i + 1 := by exact_mod_cast h2
  exact hij (by omega)

theorem lintegral_Ici_eq_blockSum (g : ℝ → ℝ≥0∞) (a : ℝ) :
    (∫⁻ t in Ici a, g t) = ∑' k : ℕ, ∫⁻ t in Ico (a + k) (a + k + 1), g t := by
  rw [Ici_eq_iUnion_unitBlocks a]
  exact lintegral_iUnion (μ := (volume : Measure ℝ)) (fun k => measurableSet_Ico)
    (pairwise_disjoint_unitBlocksNat a) g

omit [NormedSpace ℝ X] in
/-- **The terminal mass is dominated by the tail of the block norms.** -/
theorem lintegral_Ioi_le_blockTail {G : ℝ → X} (hGm : Measurable fun x => ‖G x‖ₑ) (n : ℤ) :
    (∫⁻ t in Ioi (n : ℝ), ‖G t‖ₑ) ≤ ∑' k : ℕ, blockNorm G (n + (k : ℤ)) := by
  have hsub : (∫⁻ t in Ioi (n : ℝ), ‖G t‖ₑ) ≤ ∫⁻ t in Ici (n : ℝ), ‖G t‖ₑ :=
    lintegral_mono_set Ioi_subset_Ici_self
  rw [lintegral_Ici_eq_blockSum] at hsub
  refine hsub.trans (ENNReal.tsum_le_tsum fun k => ?_)
  have hEq : Ico ((n : ℝ) + k) ((n : ℝ) + k + 1)
      = Ico (((n + (k : ℤ) : ℤ) : ℝ)) (((n + (k : ℤ) : ℤ) : ℝ) + 1) := by
    congr 1 <;> push_cast <;> ring
  rw [hEq]
  exact lintegral_block_le_blockNorm hGm (n + (k : ℤ))

/-! ## From a pointwise bound to a block norm -/

omit [NormedSpace ℝ X] in
/-- On a unit block a uniform pointwise bound is a bound for the block norm. -/
theorem blockNorm_le_of_bound {Y : ℝ → X} {n : ℤ} {c : ℝ≥0∞}
    (h : ∀ L ∈ Ico (n : ℝ) ((n : ℝ) + 1), ‖Y L‖ₑ ≤ c) : blockNorm Y n ≤ c := by
  have hsq : blockNormSq Y n ≤ c ^ 2 := by
    rw [blockNormSq]
    calc (∫⁻ t in Ico (n : ℝ) ((n : ℝ) + 1), ‖Y t‖ₑ ^ 2)
        ≤ ∫⁻ _t in Ico (n : ℝ) ((n : ℝ) + 1), c ^ 2 :=
          setLIntegral_mono' measurableSet_Ico fun t ht => pow_le_pow_left' (h t ht) 2
      _ = c ^ 2 * volume (Ico (n : ℝ) ((n : ℝ) + 1)) := by
          rw [setLIntegral_const]
      _ = c ^ 2 := by
          rw [Real.volume_Ico]
          norm_num
  have hrw : c = (c ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast c 2, ← ENNReal.rpow_mul]
    norm_num
  rw [blockNorm, hrw]
  exact ENNReal.rpow_le_rpow hsq (by norm_num)

/-- The extended norm of a backward integral is at most the terminal mass of its integrand. -/
theorem enorm_terminal_flux_le {Y g : ℝ → X} {L : ℝ}
    (hY : Y L = -∫ t in Ioi L, g t) :
    ‖Y L‖ₑ ≤ ∫⁻ t in Ioi L, ‖g t‖ₑ := by
  rw [hY, enorm_neg]
  exact enorm_integral_le_lintegral_enorm _

/-- **The flux block norm is dominated by the tail of the source block norms.**  This is the
operator input of `(13)`: no terminal charge, hence the backward integral, hence the tail. -/
theorem blockNorm_flux_le_blockTail {Y g : ℝ → X} (hgm : Measurable fun x => ‖g x‖ₑ) (n : ℤ)
    (hY : ∀ L ∈ Ico (n : ℝ) ((n : ℝ) + 1), Y L = -∫ t in Ioi L, g t) :
    blockNorm Y n ≤ ∑' k : ℕ, blockNorm g (n + (k : ℤ)) := by
  refine blockNorm_le_of_bound fun L hL => ?_
  refine (enorm_terminal_flux_le (hY L hL)).trans ?_
  refine le_trans (lintegral_mono_set ?_) (lintegral_Ioi_le_blockTail hgm n)
  exact Ioi_subset_Ioi hL.1

/-! ## The tail estimate -/

/-- **`(13)`: the backward flux tail.**  A flux dominated blockwise by the tail of a source, whose
blocks are in turn dominated by an envelope of the value plus a zero-order term, obeys the coupled
tail inequality the flat Volterra argument consumes. -/
theorem blockTail_le {y u f h : ℤ → ℝ≥0∞} {d : ℝ≥0∞} {μ : ℝ}
    (hy : ∀ n, y n ≤ ∑' k : ℕ, u (n + (k : ℤ)))
    (hu : ∀ m, u m ≤ d * expEnvelopeZ μ f m + h m) (n : ℤ) :
    y n ≤ d * (∑' k : ℕ, expEnvelopeZ μ f (n + (k : ℤ))) + ∑' k : ℕ, h (n + (k : ℤ)) := by
  refine (hy n).trans ?_
  calc (∑' k : ℕ, u (n + (k : ℤ)))
      ≤ ∑' k : ℕ, (d * expEnvelopeZ μ f (n + (k : ℤ)) + h (n + (k : ℤ))) :=
        ENNReal.tsum_le_tsum fun k => hu (n + (k : ℤ))
    _ = (∑' k : ℕ, d * expEnvelopeZ μ f (n + (k : ℤ))) + ∑' k : ℕ, h (n + (k : ℤ)) :=
        ENNReal.tsum_add
    _ = d * (∑' k : ℕ, expEnvelopeZ μ f (n + (k : ℤ))) + ∑' k : ℕ, h (n + (k : ℤ)) := by
        rw [ENNReal.tsum_mul_left]

end GaloisForLFunctions.RHTower
