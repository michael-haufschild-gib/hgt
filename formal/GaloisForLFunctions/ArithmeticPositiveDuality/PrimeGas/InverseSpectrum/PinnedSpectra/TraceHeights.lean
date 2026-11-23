import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Support
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.OperatorTrace

/-! # One fixed prime apparatus calibrated by ordinary operator traces -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set ContinuousLinearMap

/-- The largest height consistent with every ordinary even trace of the measured propagator. -/
def operatorHeight (P : Projection) : ℝ := sSup {t : ℝ | 0 < t ∧ ∀ m : ℕ,
  (riemannZeta ((m+2:ℕ):ℂ)).re-(opTrace (projected P^(2*(m+2)))).re ≤ (1/t^2)^(m+2)}

theorem even_trace_heights (P : Projection) (hd : MissingDimension P 1) (hc : Conserving (projected P)) :
    {t : ℝ | 0 < t ∧ ∀ m : ℕ, (riemannZeta ((m+2:ℕ):ℂ)).re-(opTrace (projected P^(2*(m+2)))).re ≤ (1/t^2)^(m+2)} =
      passingHeights (physicalSpectrum P hd hc) := by
  ext t
  apply and_congr_right
  intro ht
  have hh := (one_div_pos.mpr (sq_pos_of_pos ht)).le
  exact (even_operator_traces_cutoff P hd hc hh).trans (all_moment_ceilings_iff _ hh).symm

theorem operatorHeight_eq (P : Projection) (hd : MissingDimension P 1) (hc : Conserving (projected P)) :
    operatorHeight P = lastHeight (physicalSpectrum P hd hc) := congrArg sSup (even_trace_heights P hd hc)

private theorem reciprocal_amplitude_iff {s : ℂ} {n : ℕ+} (hn : 1 < (n:ℕ)) {T : ℝ} (hT : T = Real.sqrt (n:ℕ)) :
    T*‖heat s n‖ = 1 ↔ ∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x = split s f x := by
  rw [split_isometric_iff]
  have hn' : (1:ℝ) < (n:ℕ) := by exact_mod_cast hn
  have hsq : (T*‖heat s n‖)^2 = shellMass s n := by
    rw [mul_pow,hT,Real.sq_sqrt (Nat.cast_nonneg _),shellMass_eq]
  have hpos : 0 ≤ T*‖heat s n‖ := hT ▸ mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hE : energy n ≠ 0 := (Real.log_pos hn').ne'
  constructor
  · intro h
    rw [h,one_pow] at hsq
    have hz := (Real.exp_eq_one_iff _).mp hsq.symm
    have he := (mul_eq_zero.mp hz).resolve_right hE
    linarith only [he]
  · intro h
    have hm : shellMass s n = 1 := by rw [shellMass,h]; norm_num
    rw [hm] at hsq
    nlinarith only [hsq,hpos]

/-- For every prime, one fixed conserving omission measures global split isometry through its even traces and that prime's heat amplitude. -/
theorem fixed_prime_trace_apparatus (p : Nat.Primes) :
    ∃ (P : Projection) (_ : MissingDimension P 1) (_ : Conserving (projected P)),
      operatorHeight P = Real.sqrt (p:ℕ) ∧
      ∀ s : ℂ, operatorHeight P*‖heat s ⟨(p:ℕ),p.property.pos⟩‖ = 1 ↔
        ∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x = split s f x := by
  let n : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
  obtain ⟨j,hj⟩ := number_surjective n
  obtain ⟨b,⟨P,hd,hc,rfl⟩,hfirst⟩ := realize_first_move j
  have hnum : (j:ℝ)+1 = (p:ℕ) := by
    have he : j+1 = (p:ℕ) := congrArg PNat.val hj
    exact_mod_cast he
  have he := (operatorHeight_eq P hd hc).trans ((lastHeight_of_first_move hfirst).trans (congrArg Real.sqrt hnum))
  exact ⟨P,hd,hc,he,fun s => reciprocal_amplitude_iff (s := s) (n := ⟨(p:ℕ),p.property.pos⟩) p.property.one_lt he⟩

/-- Each individual experiment with a nonvacuum first change has the same calibration law. -/
theorem fixed_omission_reciprocity (P : Projection) (hd : MissingDimension P 1) (hc : Conserving (projected P))
    {j : ℕ} (hj : FirstMove (physicalSpectrum P hd hc) j) (hn : 0 < j) (s : ℂ) :
    operatorHeight P*‖heat s (number j)‖ = 1 ↔ ∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x = split s f x := by
  have he := (operatorHeight_eq P hd hc).trans (lastHeight_of_first_move hj)
  apply reciprocal_amplitude_iff (s := s) (n := number j) (show 1 < (j+1:ℕ) by omega)
  simpa only [number,Nat.cast_add,Nat.cast_one] using he

/-- Ordinary even traces of a fixed omitted direction locate its first occupied shell. -/
theorem even_trace_height_from_support {v : MissingWave} {j : ℕ} (hj : FirstOccupied v j) :
    operatorHeight (omitLine v.val) = Real.sqrt ((j:ℝ)+1) := by
  have hd : MissingDimension (omitLine v.val) 1 := (missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩
  have hc := ((nonzero_line_conserves_iff v.val).mpr v.property).2
  exact (operatorHeight_eq _ hd hc).trans (last_height_from_support hj)

#print axioms even_trace_height_from_support
#print axioms even_trace_heights
#print axioms operatorHeight_eq
#print axioms fixed_prime_trace_apparatus
#print axioms fixed_omission_reciprocity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
