import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.MovingDivisorsBelowTheSquareRoot

/-!
# The signed large-divisor moments of the prime wave

Beyond every moving cutoff below the square root, the whole zeroth
Möbius moment cancels to exponential square accuracy. The first logarithmic
moment recovers the polar-subtracted prime-power wave with the same accuracy.
All tails use increasing divisor order.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  HTGeometry

private def shortRow (w : ℕ → ℝ) (Φ : ℝ → ℝ) (A α t : ℝ) : ℝ :=
  ∑' d : ℕ, if Real.log d ≤ α*t then w d*centredMultipleRow Φ A d t else 0

/-- The finite sum above the moving cutoff, in its natural order. -/
def lateDivisorPartial (w : ℕ → ℝ) (Φ : ℝ → ℝ) (A α t : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ range (N+1), if α*t < Real.log d then w d*centredMultipleRow Φ A d t else 0

private theorem summable_before_cutoff (v : ℕ → ℝ) (T : ℝ) :
    Summable (fun d : ℕ => if Real.log d ≤ T then v d else 0) := by
  apply summable_of_ne_finset_zero (s := range (⌊Real.exp T⌋₊+1))
  intro d hd
  apply if_neg
  intro h
  apply hd
  rw [mem_range,Nat.lt_succ_iff]
  rcases Nat.eq_zero_or_pos d with rfl | h0
  · exact Nat.zero_le _
  apply Nat.le_floor
  have hd' : (0:ℝ) < d := by exact_mod_cast h0
  simpa only [Real.exp_log hd'] using Real.exp_le_exp.2 h

private theorem tendsto_lateDivisorPartial {w : ℕ → ℝ} {Φ : ℝ → ℝ} {A α t L : ℝ}
    (h : Tendsto (fun N : ℕ => ∑ d ∈ range (N+1), w d*centredMultipleRow Φ A d t) atTop (𝓝 L)) :
    Tendsto (lateDivisorPartial w Φ A α t) atTop (𝓝 (L-shortRow w Φ A α t)) := by
  have hs := (summable_before_cutoff (fun d => w d*centredMultipleRow Φ A d t) (α*t)).hasSum.tendsto_sum_nat
  apply (h.sub (hs.comp (tendsto_add_atTop_nat 1))).congr'
  refine Eventually.of_forall fun N => ?_
  change (∑ d ∈ range (N+1), _) - (∑ d ∈ range (N+1), _) = _
  rw [← sum_sub_distrib,lateDivisorPartial]
  refine sum_congr rfl fun d _ => ?_
  by_cases h : Real.log d ≤ α*t
  · simp only [if_pos h,if_neg (not_lt_of_ge h),sub_self]
  · simp only [if_neg h,if_pos (lt_of_not_ge h),sub_zero]

private theorem weighted_shortRow_memLp {w : ℕ → ℝ} {Φ : ℝ → ℝ} {A α b : ℝ} {k : ℕ}
    (hN : Continuous (integerReferenceWave Φ)) (hw : ∀ d, |w d| ≤ (Real.log d)^k)
    (he : MemLp (fun t => Real.exp (b*t)*smallDivisorEnvelope Φ A α k t) 2) :
    MemLp (fun t => Real.exp (b*t)*shortRow w Φ A α t) 2 := by
  have hm : Measurable (shortRow w Φ A α) := Measurable.tsum fun d =>
    Measurable.ite (measurableSet_le measurable_const (by fun_prop)) (by unfold centredMultipleRow; fun_prop) measurable_const
  apply he.mono' (by fun_prop)
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  let f := fun d : ℕ => if Real.log d ≤ α*t then w d*centredMultipleRow Φ A d t else 0
  let g := fun d : ℕ => if Real.log d ≤ α*t then (Real.log d)^k*|centredMultipleRow Φ A d t| else 0
  have hf : Summable f := summable_before_cutoff _ _
  have hg : Summable g := summable_before_cutoff _ _
  change |∑' d, f d| ≤ ∑' d, g d
  apply (show |∑' d, f d| ≤ ∑' d, |f d| by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm).trans
  apply hf.abs.tsum_le_tsum _ hg
  intro d
  by_cases h : Real.log d ≤ α*t
  · simp only [f,g,if_pos h,abs_mul]
    exact mul_le_mul_of_nonneg_right (hw d) (abs_nonneg _)
  · simp only [f,g,if_neg h,abs_zero,le_refl]

/-- The full zeroth and first moments restricted to the large divisors.
Both describe one physical prime wave, with a common moving lower cutoff. -/
theorem criticalState_large_divisor_moments {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {α b : ℝ} (hα : 0 < α) (hb0 : 0 ≤ b) (hroom : b+α < 1/2) :
    let A := ∫ u, Real.exp (-u/2)*Φ u
    let E := fun t : ℝ => (∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t)-Real.exp (t/2)*A
    let μ := fun n : ℕ => ((moebius n : ℤ):ℝ)
    ∃ Z L : ℝ → ℝ, MemLp (fun t => Real.exp (b*t)*Z t) 2 ∧
      MemLp (fun t => Real.exp (b*t)*(E t-L t)) 2 ∧
      ∀ t : ℝ, 0 ≤ t →
        Tendsto (lateDivisorPartial μ Φ A α t) atTop (𝓝 (Z t)) ∧
        Tendsto (lateDivisorPartial (fun d => -μ d*Real.log d) Φ A α t) atTop (𝓝 (L t)) := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let E := fun t : ℝ => (∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t)-Real.exp (t/2)*A
  let μ := fun n : ℕ => ((moebius n : ℤ):ℝ)
  let w := fun n : ℕ => -μ n*Real.log n
  let z := shortRow μ Φ A α
  let l := shortRow w Φ A α
  have hN := continuous_integerReferenceWave hc hC hb
  have hm (n : ℕ) : |μ n| ≤ 1 := by dsimp only [μ]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have henv := fun k => criticalState_smallDivisorEnvelope hW ht hF hc he hC hb hα hb0 hroom k
  have hz : MemLp (fun t => Real.exp (b*t)*z t) 2 := weighted_shortRow_memLp hN
    (fun n => (hm n).trans_eq (pow_zero _).symm) (henv 0)
  have hl : MemLp (fun t => Real.exp (b*t)*l t) 2 := weighted_shortRow_memLp hN (k := 1) (fun n => by
    simp only [w,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg n),pow_one]
    exact (mul_le_mul_of_nonneg_right (hm n) (Real.log_natCast_nonneg n)).trans_eq (one_mul _)) (henv 1)
  refine ⟨fun t => -z t,fun t => E t-l t,?_,?_,fun t ht0 => ?_⟩
  · simpa only [mul_neg,Pi.neg_apply] using hz.neg
  · simpa only [sub_sub_cancel] using hl
  · have h0 := tendsto_lateDivisorPartial (α := α) (tendsto_moebius_centredMultipleRow hb A t)
    rw [hs t ht0,zero_sub] at h0
    exact ⟨h0,tendsto_lateDivisorPartial (tendsto_moebius_log_centredMultipleRow hb A t)⟩

/-- The actual state forced by failure of RH exhibits signed cancellation
across the entire moving large-divisor tail. -/
theorem riemannHypothesis_or_large_divisor_moments : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ α b : ℝ, 0 < α → 0 ≤ b → b+α < 1/2 →
        let A := ∫ u, Real.exp (-u/2)*Φ u
        let μ := fun n : ℕ => ((moebius n : ℤ):ℝ)
        let E := fun t : ℝ => (∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t)-Real.exp (t/2)*A
        ∃ Z L : ℝ → ℝ, MemLp (fun t => Real.exp (b*t)*Z t) 2 ∧
          MemLp (fun t => Real.exp (b*t)*(E t-L t)) 2 ∧
          ∀ t : ℝ, 0 ≤ t →
            Tendsto (lateDivisorPartial μ Φ A α t) atTop (𝓝 (Z t)) ∧
            Tendsto (lateDivisorPartial (fun d => -μ d*Real.log d) Φ A α t) atTop (𝓝 (L t)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun _ _ =>
    criticalState_large_divisor_moments hW ht hF hc he hs hC hb⟩

#print axioms riemannHypothesis_or_large_divisor_moments
end GaloisForLFunctions.ExclusionOfTheCriticalState
