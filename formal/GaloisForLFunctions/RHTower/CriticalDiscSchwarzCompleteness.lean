import GaloisForLFunctions.RHTower.CriticalDiscAnalyticCompleteness

/-!
# Schwarz-real critical-disc completeness

This file constructs the literal Schwarz involution on the critical closed
disc and verifies that the actual paired Euler tangents are fixed by it.
-/

noncomputable section

namespace RHTower

open Complex Metric Set ComplexConjugate

/-- Complex conjugation preserves the critical closed disc. -/
def criticalDiscConjugation (r : ℝ) : C(CriticalClosedDisc r, CriticalClosedDisc r) where
  toFun z := ⟨conj z, by
    have hz := z.prop
    rw [mem_closedBall, dist_eq] at hz ⊢
    have hhalf : conj (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact RCLike.conj_ofReal _
    have heq : conj (z : ℂ) - 1 / 2 = conj ((z : ℂ) - 1 / 2) := by
      rw [map_sub, hhalf]
    rw [heq, RCLike.norm_conj]
    exact hz⟩
  continuous_toFun := Continuous.subtype_mk
    (Complex.continuous_conj.comp continuous_subtype_val) _

@[simp]
theorem criticalDiscConjugation_involutive
    (r : ℝ) (z : CriticalClosedDisc r) :
    criticalDiscConjugation r (criticalDiscConjugation r z) = z := by
  apply Subtype.ext
  simp [criticalDiscConjugation]

@[simp]
theorem criticalDiscCoordinate_conjugation
    (r : ℝ) (z : CriticalClosedDisc r) :
    criticalDiscCoordinate r (criticalDiscConjugation r z) =
      conj (criticalDiscCoordinate r z) := rfl

/-- Schwarz conjugation of a continuous function on the critical disc. -/
def criticalSchwarzTransform
    (r : ℝ) (g : C(CriticalClosedDisc r, ℂ)) : C(CriticalClosedDisc r, ℂ) where
  toFun z := conj (g (criticalDiscConjugation r z))
  continuous_toFun := Complex.continuous_conj.comp
    (g.continuous.comp (criticalDiscConjugation r).continuous)

@[simp]
theorem criticalSchwarzTransform_apply
    (r : ℝ) (g : C(CriticalClosedDisc r, ℂ)) (z : CriticalClosedDisc r) :
    criticalSchwarzTransform r g z =
      conj (g (criticalDiscConjugation r z)) := rfl

theorem criticalSchwarzTransform_add
    (r : ℝ) (f g : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (f + g) =
      criticalSchwarzTransform r f + criticalSchwarzTransform r g := by
  ext z
  simp [criticalSchwarzTransform]

theorem criticalSchwarzTransform_smul
    (r : ℝ) (c : ℂ) (f : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (c • f) =
      conj c • criticalSchwarzTransform r f := by
  ext z
  simp [criticalSchwarzTransform]

theorem criticalSchwarzTransform_neg
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (-f) = -criticalSchwarzTransform r f := by
  ext z
  simp [criticalSchwarzTransform]

theorem criticalSchwarzTransform_sub
    (r : ℝ) (f g : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (f - g) =
      criticalSchwarzTransform r f - criticalSchwarzTransform r g := by
  rw [sub_eq_add_neg, criticalSchwarzTransform_add,
    criticalSchwarzTransform_neg, sub_eq_add_neg]

theorem criticalSchwarzTransform_one (r : ℝ) :
    criticalSchwarzTransform r (1 : C(CriticalClosedDisc r, ℂ)) = 1 := by
  ext z
  simp [criticalSchwarzTransform]

theorem criticalSchwarzTransform_mul
    (r : ℝ) (f g : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (f * g) =
      criticalSchwarzTransform r f * criticalSchwarzTransform r g := by
  ext z
  simp [criticalSchwarzTransform, map_mul]

@[simp]
theorem criticalSchwarzTransform_involutive
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (criticalSchwarzTransform r f) = f := by
  ext z
  simp [criticalSchwarzTransform]

/-- Schwarz conjugation is an involutive ring equivalence on the compact
critical-disc Banach algebra. -/
def criticalSchwarzRingEquiv (r : ℝ) :
    C(CriticalClosedDisc r, ℂ) ≃+* C(CriticalClosedDisc r, ℂ) where
  toFun := criticalSchwarzTransform r
  invFun := criticalSchwarzTransform r
  left_inv := criticalSchwarzTransform_involutive r
  right_inv := criticalSchwarzTransform_involutive r
  map_add' := criticalSchwarzTransform_add r
  map_mul' := criticalSchwarzTransform_mul r

@[simp]
theorem criticalSchwarzRingEquiv_apply
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzRingEquiv r f = criticalSchwarzTransform r f := rfl

theorem norm_criticalSchwarzTransform_le
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    ‖criticalSchwarzTransform r f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro z
  rw [criticalSchwarzTransform_apply, RCLike.norm_conj]
  exact ContinuousMap.norm_coe_le_norm f _

@[simp]
theorem norm_criticalSchwarzTransform
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    ‖criticalSchwarzTransform r f‖ = ‖f‖ := by
  apply le_antisymm (norm_criticalSchwarzTransform_le r f)
  have h := norm_criticalSchwarzTransform_le r (criticalSchwarzTransform r f)
  simpa using h

/-- On the critical disc the compact tangent agrees pointwise with the literal
actual-source formula. -/
theorem criticalDisc_compactPrimeEulerUnitTangent_apply
    {r : ℝ} (hr : r < 1 / 2) (p : Nat.Primes)
    (z : CriticalClosedDisc r) :
    compactPrimeEulerUnitTangent (criticalDiscCoordinate r) (p : ℕ) z =
      primeEulerUnitTangent (p : ℕ) z := by
  have hδ : 0 < 1 / 2 - r := by linarith
  have hlog : 0 < Real.log ((p : Nat.Primes) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hq : ‖compactExponentialTest (criticalDiscCoordinate r)
      (Real.log (p : ℝ))‖ < 1 := by
    apply norm_compactExponentialTest_lt_one_of_re_pos
      (criticalDiscCoordinate r) _
      (Real.log (p : ℝ) * (1 / 2 - r)) (mul_pos hlog hδ)
    intro k
    have hk := criticalDiscCoordinate_re_lower k
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left hk hlog.le
  exact compactPrimeEulerUnitTangent_apply
    (criticalDiscCoordinate r) p.prop.two_le z
      (lt_of_lt_of_le hδ (criticalDiscCoordinate_re_lower z)) hq

/-- The compact paired Euler tangent is the literal FE-paired actual-source
tangent pointwise. -/
theorem criticalDisc_compactPrimeEulerUnitFETangent_apply
    {r : ℝ} (hr : r < 1 / 2) (p : Nat.Primes)
    (z : CriticalClosedDisc r) :
    compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r) (p : ℕ) z =
      primeEulerUnitFETangent (p : ℕ) z := by
  unfold compactPrimeEulerUnitFETangent primeEulerUnitFETangent
  rw [ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    criticalDisc_compactPrimeEulerUnitTangent_apply hr,
    criticalDisc_compactPrimeEulerUnitTangent_apply hr]
  rfl

/-- Every actual paired Euler tangent is Schwarz fixed. -/
theorem criticalSchwarzTransform_primeEulerUnitFETangent
    {r : ℝ} (hr : r < 1 / 2) (p : Nat.Primes) :
    criticalSchwarzTransform r
      (compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r) (p : ℕ)) =
      compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r) (p : ℕ) := by
  ext z
  rw [criticalSchwarzTransform_apply,
    criticalDisc_compactPrimeEulerUnitFETangent_apply hr,
    criticalDisc_compactPrimeEulerUnitFETangent_apply hr]
  change conj (primeEulerUnitFETangent (p : ℕ) (conj (z : ℂ))) =
    primeEulerUnitFETangent (p : ℕ) (z : ℂ)
  rw [primeEulerUnitFETangent_conj p.prop.two_le]
  simp

/-- The real-linear projection onto the Schwarz-fixed subspace. -/
def criticalSchwarzAverage
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) : C(CriticalClosedDisc r, ℂ) :=
  (2 : ℝ)⁻¹ • (f + criticalSchwarzTransform r f)

theorem norm_criticalSchwarzAverage_le
    (r : ℝ) (f : C(CriticalClosedDisc r, ℂ)) :
    ‖criticalSchwarzAverage r f‖ ≤ ‖f‖ := by
  calc
    ‖criticalSchwarzAverage r f‖ =
        ‖(2 : ℝ)⁻¹‖ * ‖f + criticalSchwarzTransform r f‖ := by
          rw [criticalSchwarzAverage, norm_smul]
    _ ≤ ‖(2 : ℝ)⁻¹‖ *
        (‖f‖ + ‖criticalSchwarzTransform r f‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖f‖ := by rw [norm_criticalSchwarzTransform]; norm_num; ring

theorem criticalSchwarzAverage_sub
    (r : ℝ) (f g : C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzAverage r (f - g) =
      criticalSchwarzAverage r f - criticalSchwarzAverage r g := by
  rw [criticalSchwarzAverage, criticalSchwarzAverage, criticalSchwarzAverage,
    criticalSchwarzTransform_sub]
  module

theorem criticalSchwarzAverage_eq_self
    {r : ℝ} {f : C(CriticalClosedDisc r, ℂ)}
    (hf : criticalSchwarzTransform r f = f) :
    criticalSchwarzAverage r f = f := by
  rw [criticalSchwarzAverage, hf]
  norm_num
  module

@[simp]
theorem criticalSchwarzTransform_zero (r : ℝ) :
    criticalSchwarzTransform r (0 : C(CriticalClosedDisc r, ℂ)) = 0 := by
  ext z
  simp [criticalSchwarzTransform]

theorem criticalSchwarzTransform_sum
    {r : ℝ} {I : Type*} (t : Finset I)
    (f : I → C(CriticalClosedDisc r, ℂ)) :
    criticalSchwarzTransform r (∑ i ∈ t, f i) =
      ∑ i ∈ t, criticalSchwarzTransform r (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      simp [ha, criticalSchwarzTransform_add, ih]

/-- Schwarz averaging sends the complex span of Schwarz-fixed generators into
their real span.  This is the algebraic descent that prevents complex
coefficients from creating spurious real directions. -/
theorem criticalSchwarzAverage_mem_real_span
    {r : ℝ} {s : Set C(CriticalClosedDisc r, ℂ)}
    (hs : ∀ g ∈ s, criticalSchwarzTransform r g = g)
    {f : C(CriticalClosedDisc r, ℂ)} (hf : f ∈ Submodule.span ℂ s) :
    criticalSchwarzAverage r f ∈ Submodule.span ℝ s := by
  obtain ⟨c, t, hts, -, rfl⟩ :=
    (Submodule.mem_span_iff_exists_finset_subset.mp hf)
  have htransform :
      criticalSchwarzTransform r (∑ a ∈ t, c a • a) =
        ∑ a ∈ t, conj (c a) • a := by
    rw [criticalSchwarzTransform_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [criticalSchwarzTransform_smul, hs a (hts ha)]
  have heq :
      criticalSchwarzAverage r (∑ a ∈ t, c a • a) =
        ∑ a ∈ t, (c a).re • a := by
    rw [criticalSchwarzAverage, htransform]
    ext z
    simp only [ContinuousMap.coe_smul, Pi.smul_apply,
      ContinuousMap.add_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_ofNat]
    change (2 : ℂ)⁻¹ *
        ((∑ a ∈ t, c a * a z) + (∑ a ∈ t, conj (c a) * a z)) =
      ∑ a ∈ t, ((c a).re : ℂ) * a z
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have hc : ((2 : ℂ)⁻¹ * (c a + conj (c a))) = ((c a).re : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    calc
      (2 : ℂ)⁻¹ * (c a * a z) +
          (2 : ℂ)⁻¹ * (conj (c a) * a z) =
          ((2 : ℂ)⁻¹ * (c a + conj (c a))) * a z := by ring
      _ = ((c a).re : ℂ) * a z := by rw [hc]
  rw [heq]
  exact Submodule.sum_mem _ fun a ha ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (hts ha))

/-- Complex closed-span density descends to real closed-span density on the
Schwarz-fixed subspace. -/
theorem criticalSchwarzAverage_mem_real_topologicalClosure
    {r : ℝ} {s : Set C(CriticalClosedDisc r, ℂ)}
    (hs : ∀ g ∈ s, criticalSchwarzTransform r g = g)
    {f : C(CriticalClosedDisc r, ℂ)}
    (hfix : criticalSchwarzTransform r f = f)
    (hf : f ∈ (Submodule.span ℂ s).topologicalClosure) :
    f ∈ (Submodule.span ℝ s).topologicalClosure := by
  change f ∈ closure (↑(Submodule.span ℝ s) : Set C(CriticalClosedDisc r, ℂ))
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hfc :
      f ∈ closure (↑(Submodule.span ℂ s) : Set C(CriticalClosedDisc r, ℂ)) := hf
  obtain ⟨g, hg, hdist⟩ := (Metric.mem_closure_iff.mp hfc) ε hε
  refine ⟨criticalSchwarzAverage r g,
    criticalSchwarzAverage_mem_real_span hs hg, ?_⟩
  rw [dist_eq_norm, ← criticalSchwarzAverage_eq_self hfix,
    ← criticalSchwarzAverage_sub]
  have hnorm : ‖f - g‖ < ε := by
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  exact lt_of_le_of_lt (norm_criticalSchwarzAverage_le r (f - g)) hnorm

/-- Full real form of critical-disc Euler-tangent completeness.  After deleting
any finite set of primes, every analytic function that is FE odd and Schwarz
real on the critical disc is uniformly approximable there by **real** finite
linear combinations of the literal paired Euler-unit tangents. -/
theorem criticalDisc_analytic_odd_schwarz_mem_realClosedSpan_compl_finset
    (f : ℂ → ℂ) {r₀ r₁ : ℝ}
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁))
    (hodd : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z)
    (hschwarz : ∀ z : ℂ, f (conj z) = conj (f z))
    (S : Finset Nat.Primes) :
    criticalDiscRestriction f r₀
        (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le)) ∈
      (Submodule.span ℝ
        (Set.range fun p : {p : Nat.Primes // p ∉ S} ↦
          compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
            (p : Nat.Primes))).topologicalClosure := by
  let s : Set C(CriticalClosedDisc r₀, ℂ) :=
    Set.range fun p : {p : Nat.Primes // p ∉ S} ↦
      compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
        (p : Nat.Primes)
  apply criticalSchwarzAverage_mem_real_topologicalClosure (s := s)
  · rintro g ⟨p, rfl⟩
    exact criticalSchwarzTransform_primeEulerUnitFETangent
      (hr01.trans hr1) (p : Nat.Primes)
  · ext z
    rw [criticalSchwarzTransform_apply]
    change conj (f (conj (z : ℂ))) = f (z : ℂ)
    rw [hschwarz]
    simp
  · exact criticalDisc_analytic_odd_mem_closedSpan_compl_finset
      f hr₀ hr01 hr1 hf hodd S

end RHTower
