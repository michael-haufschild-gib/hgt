import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitStrictTransverseCurvature
import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation

/-!
# Cold-vacuum saturation no-go for the pole-unit discriminator

P-G42 proves that arithmetic initially contracts every nontrivial rapidity split.  A natural next
conjecture is that repeating this contraction could force zero rapidity.  The exact cold endpoint
kills that conjecture.

Along every positive affine aperture ray, each squarefree partition tends to the same vacuum value
`1`.  Hence the literal normalized finite Gram tends to `1` even when the apertures are distinct.
Equivalently, the pole-unit correction tends to the exact reciprocal of the universal boost Gram:

`Q_infinity = y^2 / (x z) = K_universal^{-2}`.

Thus the arithmetic correction spends the entire universal rapidity defect at the cold endpoint.
Cold saturation is universal vacuum collapse, not rigidity and not an RH mechanism.  Any successful
continuation must retain a non-vacuum conserved charge while transporting the strict P-G42 sign.
-/

open Complex Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

private theorem tendsto_squarefreePartition_one_add_natCast_mul
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ =>
      _root_.GaloisForLFunctions.squarefreePartition
        (1 + (x : ℂ) * (n : ℂ))) atTop (nhds 1) := by
  let w : ℕ → ℂ := fun n => 1 + (x : ℂ) * (n : ℂ)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hxnat : Tendsto (fun n : ℕ => x * (n : ℝ)) atTop atTop :=
    hnat.const_mul_atTop hx
  have hwre : Tendsto (fun n => (w n).re) atTop atTop := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hadd := hconst.add_atTop hxnat
    simpa [w] using hadd
  have hnum := RHTower.tendsto_riemannZeta_of_re_atTop hwre
  have hdenre : Tendsto (fun n => (2 * w n).re) atTop atTop := by
    have hmul := hwre.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    simpa [mul_re] using hmul
  have hden := RHTower.tendsto_riemannZeta_of_re_atTop hdenre
  change Tendsto
    ((fun n : ℕ => riemannZeta (w n)) /
      (fun n : ℕ => riemannZeta (2 * w n))) atTop (nhds 1)
  simpa using hnum.div hden (by norm_num : (1 : ℂ) ≠ 0)

/-- **Universal cold-vacuum saturation.**  Distinct positive apertures are not separated by the
cold normalized squarefree Gram: every such Gram tends to `1`. -/
theorem tendsto_squarefreeMobiusFiniteUnitHardyGramSq_natCast_atTop
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Tendsto (fun n : ℕ =>
      squarefreeMobiusFiniteUnitHardyGramSq (n : ℂ) (x : ℂ) (z : ℂ))
      atTop (nhds 1) := by
  let y : ℝ := (x + z) / 2
  have hy : 0 < y := by dsimp [y]; linarith
  have hmid := tendsto_squarefreePartition_one_add_natCast_mul hy
  have hleft := tendsto_squarefreePartition_one_add_natCast_mul hx
  have hright := tendsto_squarefreePartition_one_add_natCast_mul hz
  have hden := hleft.mul hright
  have hquot := (hmid.pow 2).div hden (by norm_num : (1 : ℂ) * 1 ≠ 0)
  change Tendsto
    ((fun n : ℕ => _root_.GaloisForLFunctions.squarefreePartition
      (1 + (((x : ℂ) + (z : ℂ)) / 2) * (n : ℂ)) ^ 2) /
      (fun n : ℕ =>
        _root_.GaloisForLFunctions.squarefreePartition
          (1 + (x : ℂ) * (n : ℂ)) *
        _root_.GaloisForLFunctions.squarefreePartition
          (1 + (z : ℂ) * (n : ℂ)))) atTop (nhds 1)
  simpa [y] using hquot

/-- **Exact cold budget law.**  Pole-unit arithmetic asymptotically cancels the complete universal
boost defect, including for `x ≠ z`. -/
theorem tendsto_squarefreeMobiusPoleUnitCorrection_natCast_atTop
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Tendsto (fun n : ℕ =>
      squarefreeMobiusPoleUnitCorrection (n : ℂ) (x : ℂ) (z : ℂ))
      atTop (nhds (((((x + z) / 2) ^ 2) / (x * z) : ℝ) : ℂ)) := by
  let y : ℝ := (x + z) / 2
  have hy : 0 < y := by dsimp [y]; linarith
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hz0 : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  have hy0 : (((x : ℂ) + (z : ℂ)) / 2) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast (ne_of_gt (add_pos hx hz))) (by norm_num)
  have hsum0 : (x : ℂ) + (z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos hx hz))
  have hgram := tendsto_squarefreeMobiusFiniteUnitHardyGramSq_natCast_atTop hx hz
  have heq : (fun n : ℕ =>
      squarefreeMobiusPoleUnitCorrection (n : ℂ) (x : ℂ) (z : ℂ)) =ᶠ[atTop]
      fun n : ℕ =>
        (((((x : ℂ) + (z : ℂ)) / 2) ^ 2) / ((x : ℂ) * (z : ℂ))) *
          squarefreeMobiusFiniteUnitHardyGramSq (n : ℂ) (x : ℂ) (z : ℂ) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => Nat.one_le_iff_ne_zero.mp hn⟩] with n hn
    have hfactor :=
      squarefreeMobiusFiniteUnitHardyGramSq_eq_universal_mul_poleUnitCorrection
        (show (n : ℂ) ≠ 0 by exact_mod_cast hn) hx0 hz0 hy0
    rw [hfactor]
    field_simp [hx0, hz0, hy0, hsum0]
  have hconst : Tendsto (fun _ : ℕ =>
      (((((x : ℂ) + (z : ℂ)) / 2) ^ 2) / ((x : ℂ) * (z : ℂ))))
      atTop (nhds (((((x : ℂ) + (z : ℂ)) / 2) ^ 2) / ((x : ℂ) * (z : ℂ)))) :=
    tendsto_const_nhds
  have hscaled := hconst.mul hgram
  have hscaled' : Tendsto (fun n : ℕ =>
      (((((x : ℂ) + (z : ℂ)) / 2) ^ 2) / ((x : ℂ) * (z : ℂ))) *
        squarefreeMobiusFiniteUnitHardyGramSq (n : ℂ) (x : ℂ) (z : ℂ))
      atTop (nhds (((((x + z) / 2) ^ 2) / (x * z) : ℝ) : ℂ)) := by
    simpa using hscaled
  exact hscaled'.congr' heq.symm

/-- Cold saturation persists for every genuinely split pair, so it cannot imply aperture rigidity. -/
theorem coldVacuumSaturation_of_ne
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) (_hxz : x ≠ z) :
    Tendsto (fun n : ℕ =>
      squarefreeMobiusFiniteUnitHardyGramSq (n : ℂ) (x : ℂ) (z : ℂ))
      atTop (nhds 1) :=
  tendsto_squarefreeMobiusFiniteUnitHardyGramSq_natCast_atTop hx hz

end

end RHTower.HedenmalmThetaSource
