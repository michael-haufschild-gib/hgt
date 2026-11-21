import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Fractional moments from geometric threshold probabilities -/
open Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.PassageMoments
noncomputable section

/-- Between two successive thresholds, the variable is bounded by the
larger threshold and the mass by the tail at the smaller one. -/
theorem integrable_rpow_of_geometric_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    {A B b C p : ℝ} (hA : 0 < A) (hB : 1 < B) (hb : 0 ≤ b) (hp : 0 < p)
    (hr : B^p*b < 1) (ht : ∀ n : ℕ, μ.real {x | A*B^n < f x} ≤ C*b^n) :
    Integrable (fun x => (f x)^p) μ := by
  let t (n : ℕ) := A*B^n
  let g (x : X) := (f x)^p
  let S (n : ℕ) := {x | t n < f x ∧ f x ≤ t (n+1)}
  have Bpos := zero_lt_one.trans hB
  have tm (n : ℕ) : 0 < t n := mul_pos hA (pow_pos Bpos n)
  have gm : Measurable g := hf.pow_const p
  have normg (x : X) : ‖g x‖ = (f x)^p := Real.norm_of_nonneg (Real.rpow_nonneg (hn x) p)
  have Sm (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)
  have bound {E : Set X} (hE : MeasurableSet E) {V : ℝ} (hV : ∀ x ∈ E, f x ≤ V) :
      ∀ᵐ x ∂μ.restrict E, ‖g x‖ ≤ V^p := by
    filter_upwards [ae_restrict_mem hE] with x hx
    rw [normg]
    exact Real.rpow_le_rpow (hn x) (hV x hx) hp.le
  have si (n : ℕ) : IntegrableOn g (S n) μ := μ.integrableOn_of_bounded (measure_ne_top _ _)
    gm.aestronglyMeasurable (bound (Sm n) (fun _ h => h.2))
  have cap (n : ℕ) : (∫ x in S n, ‖g x‖ ∂μ) ≤ (A*B)^p*C*(B^p*b)^n := by
    have hs := integral_mono_ae (si n).norm (integrable_const ((t (n+1))^p)) (bound (Sm n) (fun _ h => h.2))
    rw [setIntegral_const,smul_eq_mul,mul_comm] at hs
    have hmass := (measureReal_mono (μ := μ) (show S n ⊆ {x | t n < f x} from fun _ h => h.1)).trans (ht n)
    apply hs.trans
    calc
      _ ≤ (t (n+1))^p*(C*b^n) := mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg (tm _).le _)
      _ = _ := by
        rw [show t (n+1)=(A*B)*B^n by dsimp only [t]; rw [pow_succ]; ring,
          Real.mul_rpow (mul_nonneg hA.le Bpos.le) (pow_nonneg Bpos.le n),
          ←Real.rpow_natCast_mul Bpos.le, mul_comm (n:ℝ) p, Real.rpow_mul Bpos.le,
          Real.rpow_natCast,mul_pow]
        ring
  have summ := (summable_geometric_of_lt_one (mul_nonneg (Real.rpow_nonneg Bpos.le _) hb) hr).mul_left ((A*B)^p*C)
  have hs := integrableOn_iUnion_of_summable_integral_norm si
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) cap summ)
  let low := {x | f x ≤ A}
  have hlow : IntegrableOn g low μ := μ.integrableOn_of_bounded (measure_ne_top _ _)
    gm.aestronglyMeasurable (bound (measurableSet_le hf measurable_const) (fun _ h => h))
  have cover : univ ⊆ low ∪ ⋃ n, S n := by
    intro x _
    by_cases hl : f x ≤ A
    · exact Or.inl hl
    · have he : ∃ n : ℕ, f x ≤ t n :=
        (((tendsto_pow_atTop_atTop_of_one_lt hB).const_mul_atTop hA).eventually_ge_atTop (f x)).exists
      classical
      let n := Nat.find he
      have hlast : f x ≤ t n := Nat.find_spec he
      have hn0 : n ≠ 0 := by
        intro hh
        rw [hh] at hlast
        exact hl (by simpa [t] using hlast)
      have hsucc : n-1+1 = n := by omega
      refine Or.inr (mem_iUnion.mpr ⟨n-1,lt_of_not_ge ?_,hsucc.symm ▸ hlast⟩)
      exact Nat.find_min he (show n-1 < n by omega)
  exact integrableOn_univ.mp ((hlow.union hs).mono_set cover)

#print axioms integrable_rpow_of_geometric_tail
end
end GaloisForLFunctions.HTGeometry.PassageMoments
