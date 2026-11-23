import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Sector
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.FunctionalTrace

/-! # Fractional powers of the shifted surviving heat -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

/-- The real power of the inserted squared amplitude is the Gibbs multiplier. -/
theorem sectorWeight_power_heat (a : ℕ+) (q : ℝ) : ((sectorWeight a^q:ℝ):ℂ) = heat (q:ℂ) a := by
  have ha : 0 < (a.val:ℝ) := by exact_mod_cast a.pos
  rw [sectorWeight_eq_inv,Real.inv_rpow ha.le,Real.rpow_def_of_pos ha,← Real.exp_neg,
    Complex.ofReal_exp,heat,energy]
  push_cast
  congr 1
  ring

private theorem moment_eigen {v y : Gas} {t q : ℝ}
    (he : (projected (omitLine v)^2) y = (t:ℂ) • y) (hq : 0 ≤ q) :
    momentOperator (omitLine v) q y = ((t^q:ℝ):ℂ) • y :=
  HTGeometry.cfc_apply_eigenvector_rankOne _ (projected_square_positive _).isSelfAdjoint he
    (Real.continuous_rpow_const hq).continuousOn

theorem inserted_moment_off (a : ℕ+) (v : Gas) (n : ℕ+) (hn : n ∉ Set.range (insertLabels a))
    {q : ℝ} (hq : 0 ≤ q) :
    momentOperator (omitLine (insertWave a v)) q (modeWave n) = heat (q:ℂ) n • modeWave n := by
  rw [moment_eigen (omitted_square_off a v n hn) hq,sectorWeight_power_heat]

/-- On the whole inserted sector the q-th moment scales by the Gibbs multiplier of the added factor. -/
theorem inserted_moment_on (a : ℕ+) (v : MissingWave) {q : ℝ} (hq : 0 ≤ q) (x : Gas) :
    momentOperator (omitLine (insertMissing a v).val) q (insertWave a x) =
      heat (q:ℂ) a • insertWave a (momentOperator (omitLine v.val) q x) := by
  let P := omitLine v.val
  let P' := omitLine (insertMissing a v).val
  let V := (insertWave a).toContinuousLinearMap
  have hd : MissingDimension P 1 := (missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩
  have hc : Conserving (projected P) := ((nonzero_line_conserves_iff _).mpr v.property).2
  obtain ⟨e,he⟩ := exists_physical_heat_basis P hd hc
  let b := physicalSpectrum P hd hc
  have hi (n : ℕ) : (projected P'^2) (insertWave a (e n)) = ((sectorWeight a*(b n).val:ℝ):ℂ) • insertWave a (e n) := by
    change (projected (omitLine (insertWave a v.val))^2) _ = _
    rw [omitted_square_insert,he n,map_smul,smul_smul,Complex.ofReal_mul]
  have hmaps : momentOperator P' q ∘L V = heat (q:ℂ) a • (V ∘L momentOperator P q) := by
    refine ContinuousLinearMap.ext_on (s := Set.range e) (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span) ?_
    rintro _ ⟨n,rfl⟩
    change momentOperator P' q (insertWave a (e n)) = heat (q:ℂ) a • insertWave a (momentOperator P q (e n))
    rw [moment_eigen (hi n) hq,moment_eigen (he n) hq,map_smul,smul_smul,
      Real.mul_rpow (sectorWeight_pos a).le (band_pos b n).le,Complex.ofReal_mul,sectorWeight_power_heat]
  exact congrArg (fun T : GasOp => T x) hmaps

#print axioms sectorWeight_power_heat
#print axioms inserted_moment_off
#print axioms inserted_moment_on

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
