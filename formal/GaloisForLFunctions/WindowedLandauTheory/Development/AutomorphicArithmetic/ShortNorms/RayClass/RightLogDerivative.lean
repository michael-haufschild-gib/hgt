import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.Continuation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.DirichletSeriesBounds

/-! The right-half-plane logarithmic derivative is the series of the twisted Mangoldt coefficients. -/

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk
open scoped Classical

namespace GlobalTheory.Hk.LogDeriv

open LSeries
open scoped LSeries.notation

variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

lemma norm_lamChi_le (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  show ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ 2 * Λ n
  calc ‖∑ g, χ g * (𝓕.lam g n : ℂ)‖ ≤ ∑ g, ‖χ g * (𝓕.lam g n : ℂ)‖ := norm_sum_le _ _
    _ = ∑ g, 𝓕.lam g n := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_of_nonneg (𝓕.lam_nonneg g n)]
    _ ≤ 2 * Λ n := 𝓕.lam_le n

lemma aChi_one : 𝓕.aChi χ 1 = 1 := by
  show ∑ g, χ g * (𝓕.a g 1 : ℂ) = 1
  rw [Finset.sum_eq_single (0 : 𝓕.G)]
  · rw [AddChar.map_zero_eq_one, 𝓕.a_one]
    simp
  · intro g _ hg
    rw [𝓕.a_one_ne g hg]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma conv_chi (n : ℕ) : Complex.log n * 𝓕.aChi χ n = (𝓕.lamChi χ ⍟ 𝓕.aChi χ) n := by
  rw [LSeries.convolution_def]
  show Complex.log (n : ℂ) * ∑ g, χ g * (𝓕.a g n : ℂ) =
    ∑ p ∈ n.divisorsAntidiagonal, (∑ h, χ h * (𝓕.lam h p.1 : ℂ)) * ∑ g, χ g * (𝓕.a g p.2 : ℂ)
  have step : ∀ g, Complex.log (n : ℂ) * (χ g * (𝓕.a g n : ℂ)) =
      ∑ h, ∑ p ∈ n.divisorsAntidiagonal, χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) := by
    intro g
    have hc := congrArg (fun r : ℝ => (r : ℂ)) (𝓕.conv g n)
    simp only [Complex.ofReal_mul, Complex.ofReal_sum] at hc
    simp_rw [← Finset.mul_sum]
    rw [← hc, ← Complex.natCast_log]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun g _ => step g)]
  calc ∑ g, ∑ h, ∑ p ∈ n.divisorsAntidiagonal,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ))
      = ∑ h, ∑ g, ∑ p ∈ n.divisorsAntidiagonal,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) := Finset.sum_comm
    _ = ∑ h, ∑ p ∈ n.divisorsAntidiagonal, ∑ g,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ h, ∑ g,
        χ g * ((𝓕.lam h p.1 : ℂ) * (𝓕.a (g - h) p.2 : ℂ)) := Finset.sum_comm
    _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ h, ∑ g,
        χ h * (𝓕.lam h p.1 : ℂ) * (χ g * (𝓕.a g p.2 : ℂ)) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun h _ => ?_
        refine Fintype.sum_equiv (Equiv.subRight h) _ _ fun g => ?_
        have hχ : χ g = χ h * χ (g - h) := by
          rw [← AddChar.map_add_eq_mul]
          congr 1
          abel
        simp only [Equiv.subRight_apply]
        rw [hχ]
        ring
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        (∑ h, χ h * (𝓕.lam h p.1 : ℂ)) * ∑ g, χ g * (𝓕.a g p.2 : ℂ) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]

theorem logDeriv_F : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 < s.re → LSeriesSummable (𝓕.lamChi χ) s ∧ ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries (𝓕.aChi χ) s‖ ∧ 𝓕.F χ s ≠ 0 ∧ -(deriv (𝓕.F χ) s / 𝓕.F χ s) + (if χ = 1 then 1 / (s - 1) else 0) = LSeries (𝓕.lamChi χ) s := by
  intro 𝓕 χ s hs
  obtain ⟨-, hLS, -, -⟩ := GlobalTheory.Hk.RayCont.continuation_growth 𝓕 χ
  have ha : ∀ z : ℂ, 1 < z.re → LSeriesSummable (𝓕.aChi χ) z := fun z hz => (hLS z hz).1
  have hl : ∀ z : ℂ, 1 < z.re → LSeriesSummable (𝓕.lamChi χ) z := fun z hz =>
    summable_of_le (norm_lamChi_le 𝓕 χ) z hz
  have hlb := norm_ge_of_conv ha (norm_lamChi_le 𝓕 χ) (aChi_one 𝓕 χ)
    (fun n _ => conv_chi 𝓕 χ n) hs
  have hσ : 0 < (s.re - 1) / s.re := div_pos (by linarith) (by linarith)
  have hL0 : LSeries (𝓕.aChi χ) s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlb
    linarith [pow_pos hσ 2]
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hder := hasDerivAt_of_conv ha hl (fun n _ => conv_chi 𝓕 χ n) hs
  have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨hl s hs, hlb, ?_, ?_⟩
  · rw [(hLS s hs).2]
    split_ifs <;> simp [hs1, hL0]
  · by_cases h : χ = 1
    · have hev : 𝓕.F χ =ᶠ[𝓝 s] fun z => (z - 1) * LSeries (𝓕.aChi χ) z :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun z hz => by
          rw [(hLS z hz).2, if_pos h]
      have hd : HasDerivAt (fun z => (z - 1) * LSeries (𝓕.aChi χ) z)
          (1 * LSeries (𝓕.aChi χ) s +
            (s - 1) * (-(LSeries (𝓕.lamChi χ) s * LSeries (𝓕.aChi χ) s))) s :=
        ((hasDerivAt_id s).sub_const (1 : ℂ)).mul hder
      rw [hev.deriv_eq, hd.deriv, (hLS s hs).2, if_pos h, if_pos h]
      field_simp
      ring
    · have hev : 𝓕.F χ =ᶠ[𝓝 s] LSeries (𝓕.aChi χ) :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun z hz => by
          rw [(hLS z hz).2, if_neg h, one_mul]
      rw [hev.deriv_eq, hder.deriv, (hLS s hs).2, if_neg h, if_neg h, one_mul]
      field_simp
      ring

end GlobalTheory.Hk.LogDeriv
