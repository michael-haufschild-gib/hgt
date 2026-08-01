import GaloisForLFunctions.HTGeometry.BohrMultiFejerMean
import GaloisForLFunctions.HTGeometry.BohrHullCharCombination

/-!
# The Fejér multipliers of the multi-dimensional kernel

Convolving a character `e^{iλt}` with the multi-dimensional Fejér kernel multiplies it by a real
number: the mass the kernel puts on the frequency `λ`.  For an integer combination
`λ = ∑_j m_j β_j` of the `ℚ`-independent base, rational independence identifies the frequencies of
the kernel that contribute — those `v` with `(v_j)_2 − (v_j)_1 = m_j` — and counting them in the
index box gives the classical Fejér multiplier

`∏_j (1 − |m_j|/(N_j+1))`,

which tends to one as the orders grow.  This is the diagonal action of the Bochner–Fejér operator on
trigonometric polynomials.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The classical Fejér multiplier of a frequency with integer coordinates `m` at orders `N`. -/
def fejerMultiplier {ι : Type*} [Fintype ι] (N : ι → ℕ) (m : ι → ℤ) : ℝ :=
  ∏ j : ι, (1 - ((m j).natAbs : ℝ) / ((N j : ℝ) + 1))

/-- The one-dimensional fibre of the difference map over an integer `m` has `N + 1 − |m|`
elements. -/
theorem card_fejerFibre (N : ℕ) (m : ℤ) (hm : m.natAbs ≤ N) :
    ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        fun p : ℕ × ℕ => ((p.2 : ℤ) - (p.1 : ℤ)) = m).card = N + 1 - m.natAbs := by
  classical
  rcases le_or_gt 0 m with hpos | hneg
  · have hset : ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        fun p : ℕ × ℕ => ((p.2 : ℤ) - (p.1 : ℤ)) = m)
        = (Finset.range (N + 1 - m.natAbs)).image fun a : ℕ => (a, a + m.natAbs) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨p.1, ?_, ?_⟩
        · have : (p.2 : ℤ) = (p.1 : ℤ) + m := by omega
          omega
        · have hsnd : p.2 = p.1 + m.natAbs := by omega
          exact Prod.ext rfl hsnd.symm
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · show a < N + 1
          omega
        · show a + m.natAbs < N + 1
          omega
        · show ((a + m.natAbs : ℕ) : ℤ) - ((a : ℕ) : ℤ) = m
          rw [Nat.cast_add]
          omega
    rw [hset, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).1),
      Finset.card_range]
  · have hset : ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        fun p : ℕ × ℕ => ((p.2 : ℤ) - (p.1 : ℤ)) = m)
        = (Finset.range (N + 1 - m.natAbs)).image fun a : ℕ => (a + m.natAbs, a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨p.2, ?_, ?_⟩
        · omega
        · have hfst : p.1 = p.2 + m.natAbs := by omega
          exact Prod.ext hfst.symm rfl
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · show a + m.natAbs < N + 1
          omega
        · show a < N + 1
          omega
        · show ((a : ℕ) : ℤ) - ((a + m.natAbs : ℕ) : ℤ) = m
          rw [Nat.cast_add]
          omega
    rw [hset, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).2),
      Finset.card_range]

/-- Rational independence identifies the kernel frequencies contributing to an integer
combination. -/
theorem multiFejer_fibre_iff {ι : Type*} [Fintype ι] {β : ι → ℝ}
    (hind : LinearIndependent ℚ β) (v : ι → ℕ × ℕ) (m : ι → ℤ) :
    (∑ j : ι, (m j : ℝ) * β j) + (∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j) = 0
      ↔ ∀ j : ι, ((v j).2 : ℤ) - ((v j).1 : ℤ) = m j := by
  constructor
  · intro hv j
    have hq : ∑ i : ι, ((m i : ℚ) + (((v i).1 : ℚ) - ((v i).2 : ℚ))) • β i = 0 := by
      have hcast : ∀ i : ι, ((m i : ℚ) + (((v i).1 : ℚ) - ((v i).2 : ℚ))) • β i
          = (m i : ℝ) * β i + (((v i).1 : ℝ) - ((v i).2 : ℝ)) * β i := by
        intro i
        rw [Rat.smul_def]
        push_cast
        ring
      rw [Finset.sum_congr rfl fun i _ => hcast i, Finset.sum_add_distrib]
      exact hv
    have hzero := (Fintype.linearIndependent_iff.mp hind)
      (fun i => (m i : ℚ) + (((v i).1 : ℚ) - ((v i).2 : ℚ))) hq j
    have : ((v j).2 : ℚ) - ((v j).1 : ℚ) = (m j : ℚ) := by linarith [hzero]
    exact_mod_cast this
  · intro hv
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : (m j : ℝ) = ((v j).2 : ℝ) - ((v j).1 : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (hv j)
      push_cast at h
      linarith [h]
    rw [hj]
    ring

/-- **The Fejér multiplier.**  Convolving a character whose frequency is an integer combination of
the base against the multi-dimensional kernel multiplies it by `∏_j (1 − |m_j|/(N_j+1))`. -/
theorem bohrMean_expChar_mul_multiFejerKernel {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → ℝ}
    (hind : LinearIndependent ℚ β) (N : ι → ℕ) (m : ι → ℤ) (hm : ∀ j, (m j).natAbs ≤ N j) :
    bohrMean (fun u => expChar (∑ j : ι, (m j : ℝ) * β j) u * multiFejerKernel β N u)
      = ((fejerMultiplier N m : ℝ) : ℂ) := by
  classical
  set lam : ℝ := ∑ j : ι, (m j : ℝ) * β j with hlam
  set Box : Finset (ι → ℕ × ℕ) :=
    Fintype.piFinset fun j : ι => Finset.range (N j + 1) ×ˢ Finset.range (N j + 1) with hBox
  set C : ℂ := ∏ j : ι, ((N j : ℂ) + 1)⁻¹ with hC
  set mu : (ι → ℕ × ℕ) → ℝ :=
    fun v => ∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j with hmu
  have hfun : (fun u => expChar lam u * multiFejerKernel β N u)
      = fun u => ∑ v ∈ Box, C * expChar (lam + mu v) u := by
    funext u
    rw [multiFejerKernel_eq_sum β N u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [expChar_add_frequency]
    ring
  rw [hfun, bohrMean_sum_expChar Box (fun _ => C) (fun v => lam + mu v)]
  -- only the fibre over `m` contributes
  have hstep : ∀ v ∈ Box,
      (if lam + mu v = 0 then C else 0)
        = if (∀ j : ι, ((v j).2 : ℤ) - ((v j).1 : ℤ) = m j) then C else 0 := by
    intro v _
    by_cases hd : ∀ j : ι, ((v j).2 : ℤ) - ((v j).1 : ℤ) = m j
    · rw [if_pos hd, if_pos ((multiFejer_fibre_iff hind v m).mpr hd)]
    · rw [if_neg hd, if_neg]
      intro hz
      exact hd ((multiFejer_fibre_iff hind v m).mp hz)
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
  -- the fibre is a product of one-dimensional fibres
  have hfilter : (Box.filter fun v => ∀ j : ι, ((v j).2 : ℤ) - ((v j).1 : ℤ) = m j)
      = Fintype.piFinset fun j : ι => (Finset.range (N j + 1) ×ˢ Finset.range (N j + 1)).filter
          fun p : ℕ × ℕ => ((p.2 : ℤ) - (p.1 : ℤ)) = m j := by
    ext v
    simp only [Finset.mem_filter, hBox, Fintype.mem_piFinset, Finset.mem_filter]
    constructor
    · rintro ⟨hv, hd⟩
      exact fun j => ⟨hv j, hd j⟩
    · intro h
      exact ⟨fun j => (h j).1, fun j => (h j).2⟩
  rw [hfilter, Finset.sum_const, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl fun j _ => card_fejerFibre (N j) (m j) (hm j), nsmul_eq_mul, hC]
  rw [fejerMultiplier, Complex.ofReal_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hne : ((N j : ℂ) + 1) ≠ 0 := by
    intro hz
    have hR : ((N j : ℝ) + 1) = 0 := by exact_mod_cast hz
    have : (0 : ℝ) < (N j : ℝ) + 1 := by positivity
    linarith
  have hsub : ((N j + 1 - (m j).natAbs : ℕ) : ℂ) = (N j : ℂ) + 1 - ((m j).natAbs : ℂ) := by
    have hle : (m j).natAbs ≤ N j + 1 := le_trans (hm j) (Nat.le_succ _)
    push_cast [Nat.cast_sub hle]
    ring
  rw [hsub]
  push_cast
  field_simp

end

end GaloisForLFunctions
