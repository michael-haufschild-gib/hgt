import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusSourcePositiveSupport
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusRealHorizonMoments

/-!
# Complete source law between adjacent real horizons

For `A=B+2+t`, literal source-value frequencies on `floor(A*N)` converge
to the sample-size weighted mixture of the two adjacent integer laws.
The common upper alphabet has total mass one. Every upper level has positive
mass as soon as t is positive; at t=0 the exact lower alphabet remains.

Cardinal polynomials extract actual level counts from the verified moment
transport. This refines the classical quadratic law cited in
`CofinalMobiusSourceValueLaw`; it does not assert a convergence rate.
-/

open Filter Topology Finset Polynomial
open RHTower RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- Literal level count at a real ratio between two adjacent integer horizons. -/
def moebiusSourceRealHorizonLevelCount (B : ℕ) (t : Set.Icc (0 : ℝ) 1)
    (N : ℕ) (a : ℝ) : ℕ := by
  classical
  exact ((Icc 1 ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊).filter
    (fun k => sieveSeq N moebiusReal k = a)).card

/-- The real-horizon law is the sample-size weighted mixture of its endpoint laws. -/
def cofinalMobiusRealHorizonDensity (B : ℕ) (t : Set.Icc (0 : ℝ) 1) (a : ℝ) : ℝ :=
  ((1 - (t : ℝ)) * ((B + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity B a +
    (t : ℝ) * ((B + 3 : ℕ) : ℝ) * cofinalMobiusSourceDensity (B + 1) a) /
      (((B + 2 : ℕ) : ℝ) + (t : ℝ))

private theorem horizon_bounds (B N : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (B + 2) * N ≤ ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ ∧
      ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ ≤ (B + 3) * N := by
  have hlo : (((B + 2) * N : ℕ) : ℝ) ≤
      (((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N := by
    rw [Nat.cast_mul]
    nlinarith [mul_nonneg t.property.1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hhi : (((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N ≤ (((B + 3) * N : ℕ) : ℝ) := by
    have hB : ((B + 3 : ℕ) : ℝ) = ((B + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [Nat.cast_mul, hB]
    nlinarith [mul_nonneg (show 0 ≤ 1 - (t : ℝ) by linarith [t.property.2])
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  constructor
  · simpa only [Nat.floor_natCast] using Nat.floor_mono hlo
  · simpa only [Nat.floor_natCast] using Nat.floor_mono hhi

private theorem cardinal_eval {B : ℕ} (a x : ℝ)
    (hx : x ∈ moebiusLinearHorizonAlphabet (B + 1)) :
    (cofinalMobiusSourceCardinal B a).eval x = if x = a then 1 else 0 := by
  classical
  by_cases ha : a ∈ moebiusLinearHorizonAlphabet (B + 1)
  · simp only [cofinalMobiusSourceCardinal, if_pos ha]
    by_cases hxa : x = a
    · subst x
      simpa using Lagrange.eval_basis_self (v := (id : ℝ → ℝ))
        (fun _ _ _ _ h => h) ha
    · simpa [hxa] using
        Lagrange.eval_basis_of_ne (v := (id : ℝ → ℝ)) (Ne.symm hxa) hx
  · have hxa : x ≠ a := fun h => ha (h ▸ hx)
    simp [cofinalMobiusSourceCardinal, ha, hxa]

private theorem prefix_count_eq_cardinal_sum (B N M : ℕ) (a : ℝ)
    (hN : 1 ≤ N) (hM : M ≤ (B + 3) * N) :
    (((Icc 1 M).filter (fun k => sieveSeq N moebiusReal k = a)).card : ℝ) =
      ∑ k ∈ Icc 1 M,
        (cofinalMobiusSourceCardinal (B + 1) a).eval (sieveSeq N moebiusReal k) := by
  classical
  have he (k : ℕ) (hk : k ∈ Icc 1 M) :
      (cofinalMobiusSourceCardinal (B + 1) a).eval (sieveSeq N moebiusReal k) =
        if sieveSeq N moebiusReal k = a then 1 else 0 := by
    apply cardinal_eval
    have hk1 := (mem_Icc.mp hk).1
    have hkM := (mem_Icc.mp hk).2.trans hM
    have h := moebius_source_mem_linear_horizon_alphabet (B + 1) ⟨N, by omega⟩
      ⟨k - 1, by simpa [Nat.add_assoc] using
        (show k - 1 < (B + 3) * N by omega)⟩
    change sieveSeq N moebiusReal (k - 1 + 1) ∈ _ at h
    simpa only [Nat.sub_add_cancel hk1] using h
  rw [Finset.sum_congr rfl he]
  simp [Finset.sum_boole]

private theorem polynomial_average (s : Finset ℕ) (f : ℕ → ℝ) (z : ℝ) (p : ℝ[X]) :
    (∑ k ∈ s, p.eval (f k)) / z =
      ∑ m ∈ p.support, p.coeff m * ((∑ k ∈ s, (f k) ^ m) / z) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.mul_sum]
  ring

private theorem integer_count_mean (C : ℕ) (a : ℝ) :
    Tendsto (fun N : ℕ => (moebiusSourceLevelCount C N a : ℝ) / (N : ℝ)) atTop
      (𝓝 (((C + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity C a)) := by
  have h := (tendsto_moebiusSourceLevelFrequency C a).const_mul (((C + 2 : ℕ) : ℝ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hCR : ((C + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_mul]
  field_simp

private theorem cardinal_endpoint (B C : ℕ) (hC : C ≤ B + 1) (a : ℝ) :
    (∑ m ∈ (cofinalMobiusSourceCardinal (B + 1) a).support,
      (cofinalMobiusSourceCardinal (B + 1) a).coeff m * cofinalMobiusMomentProfile C m) =
        ((C + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity C a := by
  have hp : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ((C + 2) * N),
        (cofinalMobiusSourceCardinal (B + 1) a).eval (sieveSeq N moebiusReal k)) / (N : ℝ))
      atTop (𝓝 (∑ m ∈ (cofinalMobiusSourceCardinal (B + 1) a).support,
        (cofinalMobiusSourceCardinal (B + 1) a).coeff m * cofinalMobiusMomentProfile C m)) := by
    simp_rw [polynomial_average]
    exact tendsto_finsetSum _ fun m _ => (tendsto_sieveSeq_moment_linear_horizon C m).const_mul _
  have hc : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ((C + 2) * N),
        (cofinalMobiusSourceCardinal (B + 1) a).eval (sieveSeq N moebiusReal k)) / (N : ℝ))
      atTop (𝓝 (((C + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity C a)) := by
    apply (integer_count_mean C a).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact congrArg (fun x : ℝ => x / (N : ℝ))
      (prefix_count_eq_cardinal_sum B N ((C + 2) * N) a hN
        (Nat.mul_le_mul_right N (by omega)))
  exact tendsto_nhds_unique hp hc

private theorem real_count_mean (B : ℕ) (t : Set.Icc (0 : ℝ) 1) (a : ℝ) :
    Tendsto (fun N : ℕ => (moebiusSourceRealHorizonLevelCount B t N a : ℝ) / (N : ℝ))
      atTop (𝓝 ((1 - (t : ℝ)) * ((B + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity B a +
        (t : ℝ) * ((B + 3 : ℕ) : ℝ) * cofinalMobiusSourceDensity (B + 1) a)) := by
  let p := cofinalMobiusSourceCardinal (B + 1) a
  have he : (∑ m ∈ p.support, p.coeff m *
      ((1 - (t : ℝ)) * cofinalMobiusMomentProfile B m +
        (t : ℝ) * cofinalMobiusMomentProfile (B + 1) m)) =
      (1 - (t : ℝ)) * ((B + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity B a +
        (t : ℝ) * ((B + 3 : ℕ) : ℝ) * cofinalMobiusSourceDensity (B + 1) a := by
    calc
      _ = (1 - (t : ℝ)) * (∑ m ∈ p.support, p.coeff m * cofinalMobiusMomentProfile B m) +
          (t : ℝ) * (∑ m ∈ p.support, p.coeff m * cofinalMobiusMomentProfile (B + 1) m) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = _ := by
        rw [cardinal_endpoint B B (by omega) a, cardinal_endpoint B (B + 1) le_rfl a]
        simp only [Nat.add_assoc]
        ring
  have hp : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊,
        p.eval (sieveSeq N moebiusReal k)) / (N : ℝ)) atTop
      (𝓝 ((1 - (t : ℝ)) * ((B + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity B a +
        (t : ℝ) * ((B + 3 : ℕ) : ℝ) * cofinalMobiusSourceDensity (B + 1) a)) := by
    simp_rw [polynomial_average]
    rw [← he]
    exact tendsto_finsetSum _ fun m _ =>
      (tendsto_sieveSeq_moment_adjacent_real_horizon B t m).const_mul (p.coeff m)
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (congrArg (fun x : ℝ => x / (N : ℝ))
    (prefix_count_eq_cardinal_sum B N _ a hN (horizon_bounds B N t).2)).symm

/-- Every literal real-horizon level frequency converges to the endpoint mixture. -/
theorem tendsto_moebiusSourceRealHorizonLevelFrequency (B : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (a : ℝ) :
    Tendsto (fun N : ℕ => (moebiusSourceRealHorizonLevelCount B t N a : ℝ) /
      (⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ : ℝ)) atTop
      (𝓝 (cofinalMobiusRealHorizonDensity B t a)) := by
  have hA : 0 < ((B + 2 : ℕ) : ℝ) + (t : ℝ) := by
    have := t.property.1
    positivity
  have hf : Tendsto (fun N : ℕ =>
      (⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ : ℝ) / (N : ℝ)) atTop
      (𝓝 (((B + 2 : ℕ) : ℝ) + (t : ℝ))) := by
    exact (tendsto_nat_floor_mul_div_atTop hA.le).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have h := (real_count_mean B t a).div hf (ne_of_gt hA)
  change Tendsto _ _ (𝓝 (cofinalMobiusRealHorizonDensity B t a)) at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  change ((moebiusSourceRealHorizonLevelCount B t N a : ℝ) / (N : ℝ)) /
    ((⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ : ℝ) / (N : ℝ)) = _
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hM : (⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ : ℝ) ≠ 0 := by
    have hbound := (horizon_bounds B N t).1
    have hpos := Nat.mul_pos (show 0 < B + 2 by omega) (show 0 < N by omega)
    exact_mod_cast (show ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ ≠ 0 by omega)
  field_simp

/-- Real-horizon masses are nonnegative. -/
theorem cofinalMobiusRealHorizonDensity_nonneg (B : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (a : ℝ) :
    0 ≤ cofinalMobiusRealHorizonDensity B t a := by
  exact ge_of_tendsto' (tendsto_moebiusSourceRealHorizonLevelFrequency B t a)
    (fun _ => by positivity)

private theorem alphabet_mono (B : ℕ) :
    moebiusLinearHorizonAlphabet (B + 1) ⊆ moebiusLinearHorizonAlphabet (B + 2) := by
  classical
  intro a ha
  simp only [moebiusLinearHorizonAlphabet, mem_union, mem_singleton, mem_biUnion] at ha ⊢
  rcases ha with hz | ⟨l, hl, d, hd, ha⟩
  · exact Or.inl hz
  · have hlhi := (mem_Icc.mp hl).2
    exact Or.inr ⟨l, mem_Icc.mpr ⟨(mem_Icc.mp hl).1, by omega⟩, d, hd, ha⟩

private theorem density_zero_outside (B : ℕ) (a : ℝ)
    (ha : a ∉ moebiusLinearHorizonAlphabet (B + 1)) :
    cofinalMobiusSourceDensity B a = 0 := by
  exact (cofinalMobiusSourceDensity_support B a).resolve_right ha

/-- The endpoint mixture has total mass one on the common upper alphabet. -/
theorem sum_cofinalMobiusRealHorizonDensity (B : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (∑ a ∈ moebiusLinearHorizonAlphabet (B + 2), cofinalMobiusRealHorizonDensity B t a) = 1 := by
  classical
  have hlo : (∑ a ∈ moebiusLinearHorizonAlphabet (B + 2), cofinalMobiusSourceDensity B a) = 1 := by
    rw [← Finset.sum_subset (alphabet_mono B) (fun a _ ha => density_zero_outside B a ha)]
    exact sum_cofinalMobiusSourceDensity B
  have hhi : (∑ a ∈ moebiusLinearHorizonAlphabet (B + 2), cofinalMobiusSourceDensity (B + 1) a) = 1 := by
    simpa only [Nat.add_assoc] using sum_cofinalMobiusSourceDensity (B + 1)
  have hA : ((B + 2 : ℕ) : ℝ) + (t : ℝ) ≠ 0 := by
    have := t.property.1
    positivity
  simp only [cofinalMobiusRealHorizonDensity]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hlo, hhi, mul_one, mul_one]
  field_simp
  push_cast
  ring

/-- Within an integer interval, every upper alphabet level has positive mass as
soon as the real horizon exceeds the lower endpoint. -/
theorem cofinalMobiusRealHorizonDensity_pos_iff_mem (B : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (a : ℝ) :
    0 < cofinalMobiusRealHorizonDensity B t a ↔
      ((t : ℝ) = 0 ∧ a ∈ moebiusLinearHorizonAlphabet (B + 1)) ∨
        (0 < (t : ℝ) ∧ a ∈ moebiusLinearHorizonAlphabet (B + 2)) := by
  have hK : (0 : ℝ) < ((B + 2 : ℕ) : ℝ) := by positivity
  have hJ : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) := by positivity
  have hA : 0 < ((B + 2 : ℕ) : ℝ) + (t : ℝ) := by linarith [t.property.1]
  by_cases ht : (t : ℝ) = 0
  · have he : cofinalMobiusRealHorizonDensity B t a = cofinalMobiusSourceDensity B a := by
      simp only [cofinalMobiusRealHorizonDensity, ht, sub_zero, one_mul, zero_mul, add_zero]
      field_simp
    simpa [ht, he] using cofinalMobiusSourceDensity_pos_iff_mem B a
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have he : 0 < cofinalMobiusRealHorizonDensity B t a ↔
        a ∈ moebiusLinearHorizonAlphabet (B + 2) := by
      constructor
      · intro hp
        by_contra ha
        have hlo := density_zero_outside B a (fun h => ha (alphabet_mono B h))
        have hhi := density_zero_outside (B + 1) a (by simpa only [Nat.add_assoc] using ha)
        simp [cofinalMobiusRealHorizonDensity, hlo, hhi] at hp
      · intro ha
        have hp := (cofinalMobiusSourceDensity_pos_iff_mem (B + 1) a).mpr
          (by simpa only [Nat.add_assoc] using ha)
        have hlo : 0 ≤ (1 - (t : ℝ)) * ((B + 2 : ℕ) : ℝ) * cofinalMobiusSourceDensity B a :=
          mul_nonneg (mul_nonneg (by linarith [t.property.2]) hK.le)
            (cofinalMobiusSourceDensity_nonneg B a)
        exact div_pos (add_pos_of_nonneg_of_pos hlo (mul_pos (mul_pos htp hJ) hp)) hA
    simpa [ht, htp] using he

end
end GaloisForLFunctions.BezoutValuationIncidence
