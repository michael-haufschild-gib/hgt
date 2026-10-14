import GaloisForLFunctions.RHTower.PaperHurwitzQuadraticScaling

/-! # Finite Fredholm limits from a fixed native source approach

Rounding a prescribed coupling density to natural lattice indices preserves
its limiting density. The native perturbations converge to zero in operator
norm while their actual determinants retain the square of that density.
-/

namespace RHTower
noncomputable section
open Filter GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt
open scoped Topology

def paperHurwitzFiniteIndex (c : ℝ) (N : ℕ) : ℕ := ⌊|c| * ((N : ℝ) + 3)⌋₊

def paperHurwitzFiniteDensity (c : ℝ) (N : ℕ) : ℝ :=
  (paperHurwitzFiniteIndex c N : ℝ) / ((N : ℝ) + 3)

def paperHurwitzFinitePerturbation (t c : ℝ) (N : ℕ) :
    PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  paperHurwitzQuadraticPerturbation t N (paperHurwitzFiniteIndex c N)

def paperHurwitzFiniteFredholmValue (t c : ℝ) (N : ℕ) : ℂ :=
  fredholmDetOp (lpBasis ℕ) (paperHurwitzFinitePerturbation t c N)

def paperHurwitzFiniteFredholmLimit (c : ℝ) : ℝ := Real.exp (c ^ 2 * Real.log 2)

theorem paperHurwitzFiniteDensity_tendsto (c : ℝ) :
    Tendsto (paperHurwitzFiniteDensity c) atTop (𝓝 |c|) := by
  change Tendsto (fun N : ℕ => (⌊|c| * ((N : ℝ) + 3)⌋₊ : ℝ) / ((N : ℝ) + 3))
    atTop (𝓝 |c|)
  exact (tendsto_nat_floor_mul_div_atTop (abs_nonneg c)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (3 : ℝ))))

theorem paperHurwitzFiniteAngle_tendsto_zero (c : ℝ) :
    Tendsto (fun N => paperHurwitzQuadraticAngle N (paperHurwitzFiniteIndex c N))
      atTop (𝓝 0) := by
  simp_rw [paperHurwitzQuadraticAngle_eq]
  simpa only [paperHurwitzFiniteDensity, mul_zero] using
    (paperHurwitzFiniteDensity_tendsto c).mul paperHurwitzApproachStep_tendsto_zero

theorem paperHurwitzFiniteExponent_tendsto (c : ℝ) :
    Tendsto (fun N => paperHurwitzFiniteDensity c N ^ 2 * Real.log 2)
      atTop (𝓝 (c ^ 2 * Real.log 2)) := by
  simpa only [sq_abs] using ((paperHurwitzFiniteDensity_tendsto c).pow 2).mul_const (Real.log 2)

theorem paperHurwitzFinitePerturbation_traceClass (t c : ℝ) (N : ℕ) :
    MemSchattenClass 1 (paperHurwitzFinitePerturbation t c N) :=
  paperHurwitzQuadraticPerturbation_traceClass t N (paperHurwitzFiniteIndex c N)

theorem paperHurwitzFinitePerturbation_traceCost_zero (t c : ℝ) (N : ℕ) :
    compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzFinitePerturbation t c N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr
    (paperHurwitzQuadraticPerturbation_compact t N (paperHurwitzFiniteIndex c N))

theorem norm_paperHurwitzFinitePerturbation (t c : ℝ) (N : ℕ) :
    ‖paperHurwitzFinitePerturbation t c N‖ =
      Real.sinh (paperHurwitzFiniteDensity c N * paperHurwitzApproachStep N) ^ 2 := by
  rw [paperHurwitzFinitePerturbation, norm_paperHurwitzQuadraticPerturbation,
    paperHurwitzQuadraticAngle_eq]
  rfl

theorem paperHurwitzFinitePerturbation_tendsto_zero (t c : ℝ) :
    Tendsto (paperHurwitzFinitePerturbation t c) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := ((Real.continuous_sinh.tendsto 0).comp
    (paperHurwitzFiniteAngle_tendsto_zero c)).pow 2
  simpa only [paperHurwitzFinitePerturbation, norm_paperHurwitzQuadraticPerturbation,
    Function.comp_apply, Real.sinh_zero, zero_pow (by omega : 2 ≠ 0)] using h

theorem paperHurwitzFiniteFredholmValue_exact (t c : ℝ) (N : ℕ) :
    paperHurwitzFiniteFredholmValue t c N =
      ((Real.cosh (paperHurwitzQuadraticAngle N (paperHurwitzFiniteIndex c N)) *
        Real.exp (paperHurwitzFiniteDensity c N ^ 2 * Real.log 2) : ℝ) : ℂ) :=
  paperHurwitzQuadraticFredholmValue_exact t N (paperHurwitzFiniteIndex c N)

theorem paperHurwitzFiniteFredholmValue_tendsto (t c : ℝ) :
    Tendsto (paperHurwitzFiniteFredholmValue t c) atTop
      (𝓝 (paperHurwitzFiniteFredholmLimit c : ℂ)) := by
  have hh := (Real.continuous_cosh.tendsto 0).comp (paperHurwitzFiniteAngle_tendsto_zero c)
  have he := (Real.continuous_exp.tendsto (c ^ 2 * Real.log 2)).comp
    (paperHurwitzFiniteExponent_tendsto c)
  have hr := hh.mul he
  simp only [Real.cosh_zero, one_mul] at hr
  have hc := (Complex.continuous_ofReal.tendsto _).comp hr
  refine hc.congr' (Eventually.of_forall fun N => ?_)
  exact (paperHurwitzFiniteFredholmValue_exact t c N).symm

end
end RHTower
