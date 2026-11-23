import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Insertion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.NativeKnots

/-! # The squared propagator on a multiplicative occupation sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace
open _root_.RHTower.PrimeCoShift
open scoped InnerProductSpace

/-- The squared amplitude by which a new occupation scales critical heat. -/
def sectorWeight (a : ℕ+) : ℝ := attenuation a^2

theorem sectorWeight_pos (a : ℕ+) : 0 < sectorWeight a := sq_pos_of_pos (attenuation_pos a)

theorem sectorWeight_eq_inv (a : ℕ+) : sectorWeight a = (a.val:ℝ)⁻¹ := by
  rw [sectorWeight,attenuation,inv_pow,gain_sq]

theorem insert_mode (a n : ℕ+) : insertWave a (modeWave n) = modeWave (a*n) :=
  _root_.RHTower.lpScalarInjection_single _ (mulLeft_injective a) n 1

theorem remove_insert (a : ℕ+) (x : Gas) : primeCoShift a (insertWave a x) = x :=
  restrict_extend (insertLabels a) x

theorem remove_mode_off (a n : ℕ+) (hn : n ∉ Set.range (insertLabels a)) :
    primeCoShift a (modeWave n) = 0 := by
  apply lp.ext
  funext k
  change (lp.single 2 n (1:ℂ) : Gas) (a*k) = 0
  have hne : a*k ≠ n := fun h => hn ⟨k,h⟩
  rw [lp.single_apply,Pi.single_eq_of_ne hne]

private theorem square_insert (a : ℕ+) (x : Gas) :
    squareHeat.val (insertWave a x) = (sectorWeight a:ℂ) • insertWave a (squareHeat.val x) := by
  change criticalOperator (criticalOperator (insertWave a x)) = _
  rw [heat_insertWave,map_smul,heat_insertWave,smul_smul,← sq,← Complex.ofReal_pow]
  rfl

private theorem line_square_action (v x : Gas) :
    (projected (omitLine v)^2) x = squareHeat.val x -
      (((‖v‖^2:ℝ):ℂ)⁻¹*inner ℂ (criticalOperator v) x) • criticalOperator v := by
  rw [line_square]
  change squareHeat.val x-((‖v‖^2:ℝ):ℂ)⁻¹ • (inner ℂ (criticalOperator v) x • criticalOperator v) = _
  rw [smul_smul]

/-- The entire compressed squared heat intertwines under insertion, including the coherent rank-one correction. -/
theorem omitted_square_insert (a : ℕ+) (v x : Gas) :
    (projected (omitLine (insertWave a v))^2) (insertWave a x) =
      (sectorWeight a:ℂ) • insertWave a ((projected (omitLine v)^2) x) := by
  rw [line_square_action,line_square_action,square_insert,heat_insertWave,LinearIsometry.norm_map,
    inner_smul_left,Complex.conj_ofReal,LinearIsometry.inner_map_map,map_sub,map_smul,smul_sub,smul_smul,smul_smul]
  congr 2
  simp only [sectorWeight,Complex.ofReal_pow]
  ring

/-- A native basis state outside the inserted sector survives at its original eigenvalue. -/
theorem omitted_square_off (a : ℕ+) (v : Gas) (n : ℕ+) (hn : n ∉ Set.range (insertLabels a)) :
    (projected (omitLine (insertWave a v))^2) (modeWave n) = (sectorWeight n:ℂ) • modeWave n := by
  have hw : criticalOperator (insertWave a v) n = 0 := by rw [critical_apply,insertWave_off _ _ _ hn,mul_zero]
  have ho : inner ℂ (criticalOperator (insertWave a v)) (modeWave n) = 0 := by
    simp only [modeWave,lp.inner_single_right,hw,inner_zero_left]
  rw [line_square_action,ho,mul_zero,zero_smul,sub_zero]
  change criticalOperator (criticalOperator (modeWave n)) = _
  rw [heat_modeWave,map_smul,heat_modeWave,smul_smul,← sq,← Complex.ofReal_pow]
  rfl

#print axioms sectorWeight_pos
#print axioms sectorWeight_eq_inv
#print axioms insert_mode
#print axioms remove_insert
#print axioms remove_mode_off
#print axioms omitted_square_insert
#print axioms omitted_square_off

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
