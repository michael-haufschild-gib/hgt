import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailSampling
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailWeilGrowth

/-! Sharp sampling scale and a relative positive margin for the actual smoothed
tail family. The margin concerns individual sources, not their linear span. -/

open MeasureTheory Filter Set
open scoped Topology
open _root_.Zeta23
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

private theorem weil_norm_le_square_mass (f : ℝ → ℂ)
    (hf : Summable (zetaZeroSquareSummand f)) :
    ‖zetaZeroConfig.W f f‖ ≤ zetaZeroSquareMass f := by
  let r : zetaZeroConfig.carrier → zetaZeroConfig.carrier :=
    fun ρ => ⟨reflect ρ,zetaZeroConfig.reflect_mem _ ρ.2⟩
  have hr : Function.Involutive r := fun ρ => by
    apply Subtype.ext
    exact Tail.reflect_reflect ρ
  let e := hr.toPerm r
  have he (ρ : zetaZeroConfig.carrier) : zetaZeroSquareSummand f (e ρ) =
      (zetaZeroConfig.mult ρ : ℝ)*‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖^2 := by
    change (zetaZeroConfig.mult (reflect ρ) : ℝ)*‖paperFT f (gammaOf (reflect ρ))‖^2 = _
    rw [zetaZeroConfig.mult_reflect _ ρ.2,Tail.gammaOf_reflect]
  let b : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (zetaZeroSquareSummand f ρ+zetaZeroSquareSummand f (e ρ))/2
  have hb : Summable b := (hf.add (hf.comp_injective e.injective)).div_const 2
  have hpoint (ρ : zetaZeroConfig.carrier) : ‖zetaZeroConfig.Wsummand f f ρ‖ ≤ b ρ := by
    dsimp only [b]
    rw [he ρ]
    unfold zetaZeroSquareSummand ZeroConfig.Wsummand
    simp only [norm_mul,Complex.norm_natCast,RCLike.norm_conj]
    have hs := mul_nonneg (Nat.cast_nonneg (zetaZeroConfig.mult ρ) : (0 : ℝ) ≤ _)
      (sq_nonneg (‖paperFT f (gammaOf ρ)‖-‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖))
    nlinarith only [hs]
  have hs : Summable (fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f f ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hb
  calc
    ‖zetaZeroConfig.W f f‖ ≤ ∑' ρ : zetaZeroConfig.carrier,‖zetaZeroConfig.Wsummand f f ρ‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' ρ,b ρ := hs.tsum_le_tsum hpoint hb
    _ = zetaZeroSquareMass f := by
      dsimp only [b]
      have hfe : Summable (fun ρ => zetaZeroSquareSummand f (e ρ)) :=
        hf.comp_injective e.injective
      rw [tsum_div_const,hf.tsum_add hfe,e.tsum_eq (zetaZeroSquareSummand f)]
      unfold zetaZeroSquareMass
      ring

/-- Absolute sampling dominates the literal signed Weil diagonal. -/
theorem factorialSmoothedTail_weil_norm_le_zeroSquare (n k : ℕ) :
    ‖zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))‖ ≤
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) :=
  weil_norm_le_square_mass _ (factorialSmoothedTail_zeroSquare_summable n k)

/-- The logarithm in the uniform upper bound is necessary for fine smoothing. -/
theorem factorialSmoothedTail_zeroSquare_log_lower :
    ∀ᶠ n : ℕ in atTop,∀ᶠ k : ℕ in atTop,
      Real.log ((n+1 : ℕ) : ℝ)/(2048*((n+1 : ℕ) : ℝ)) ≤
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) := by
  filter_upwards [factorialMuntzSmoothedTail_weil_log_rate] with n hn
  filter_upwards [hn] with k hk
  exact hk.trans ((Complex.re_le_norm _).trans (factorialSmoothedTail_weil_norm_le_zeroSquare n k))

/-- The positive diagonal controls a fixed fraction of the independent absolute
sampling mass, with the original scale-then-smoothing quantifiers. -/
theorem exists_factorialSmoothedTail_relative_positive_margin :
    ∃ δ : ℝ,0 < δ ∧ ∀ᶠ n : ℕ in atTop,∀ᶠ k : ℕ in atTop,
      δ*zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ≤
        (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
          (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re := by
  obtain ⟨C,hC,hbound⟩ := exists_factorialTail_raw_and_smoothed_zeroSquare_bound
  let δ : ℝ := 1/(4096*C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  have ht : Tendsto (fun n : ℕ => Real.log ((n+1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  filter_upwards [factorialMuntzSmoothedTail_weil_log_rate,
    ht.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hlog
  filter_upwards [hn] with k hk
  have hraw : 0 ≤ zetaZeroSquareMass (fun x => (factorialMuntzCorrectedTail n x : ℂ)) :=
    tsum_nonneg (fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hu := (le_add_of_nonneg_left hraw).trans (hbound n k)
  have hscale : δ*(C*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ)) ≤
      Real.log ((n+1 : ℕ) : ℝ)/(2048*((n+1 : ℕ) : ℝ)) := by
    have hL : 1 ≤ Real.log (n+1 : ℝ) := by exact_mod_cast hlog
    calc
      δ*(C*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ)) =
          (1+Real.log (n+1 : ℝ))/(4096*(n+1 : ℝ)) := by
        dsimp [δ]
        field_simp
      _ ≤ (2*Real.log (n+1 : ℝ))/(4096*(n+1 : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith only [hL]) (by positivity)
      _ = Real.log ((n+1 : ℕ) : ℝ)/(2048*((n+1 : ℕ) : ℝ)) := by
        have hN : (n : ℝ)+1 ≠ 0 := by positivity
        push_cast
        field_simp
        ring
  exact ((mul_le_mul_of_nonneg_left hu hδ.le).trans hscale).trans hk

end
end GaloisForLFunctions.ArithmeticPositivityTheory
