import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.BoundarySpectrum

/-! # The sharp trace floor between two consecutive squared shell amplitudes

Mixing the two neighboring occupations as an omitted direction attains
the universal two-moment lower bound in the closure of physical readings.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace

def squaredReadings : Set (ℝ × ℝ) :=
  Set.range fun G : Propagator => (‖criticalOperator^2-G.val^2‖,traceLoss G.val)

private theorem continuous_squared_distance {X : Type*} [NormedRing X] (d : X) :
    Continuous (fun x : X => ‖d-x^2‖) := (continuous_const.sub (continuous_id.pow 2)).norm

private theorem squared_line_contact (f : Gas) (hf : ‖f‖ = 1) :
    (‖criticalOperator f‖^2,lineLoss f) ∈ closure squaredReadings := by
  have h := observable_closure (fun G : Propagator => G.val) (fun G => traceLoss G.val)
    (fun T : GasOp => ‖criticalOperator^2-T^2‖) (continuous_squared_distance (criticalOperator^2 : GasOp)) (projected (omitLine f),lineLoss f) (line_reading_mem_closure f)
  change (‖squareHeat.val-projected (omitLine f)^2‖,lineLoss f) ∈ closure squaredReadings at h
  simpa only [line_square,sub_sub_cancel,hf,one_pow,Complex.ofReal_one,inv_one,one_smul,norm_rankOne,← pow_two] using h

private abbrev basisWave (n : ℕ+) : Gas := HilbertSchmidt.lpBasis ℕ+ n

private theorem heat_wave (n : ℕ+) :
    criticalOperator (basisWave n) = (attenuation n:ℂ) • basisWave n := by
  rw [basisWave,HilbertSchmidt.lpBasis_apply]
  exact HTGeometry.LpDiagonal.lpDiag_single _ _ _ _ _

private theorem wave_norm {i j : ℕ+} (hij : i ≠ j) (a b : ℝ) :
    ‖(a:ℂ) • basisWave i+(b:ℂ) • basisWave j‖^2 = a^2+b^2 := by
  have hz := (HilbertSchmidt.lpBasis ℕ+).orthonormal.inner_eq_zero hij
  have hi : inner ℂ ((a:ℂ) • basisWave i) ((b:ℂ) • basisWave j) = 0 := by
    rw [inner_smul_left,inner_smul_right,show inner ℂ (basisWave i) (basisWave j) = 0 from hz,mul_zero,mul_zero]
  rw [@norm_add_sq ℂ _ _ _ _,hi]
  simp only [map_zero,mul_zero,add_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    show ‖basisWave i‖ = 1 from (HilbertSchmidt.lpBasis ℕ+).orthonormal.norm_eq_one i,
    show ‖basisWave j‖ = 1 from (HilbertSchmidt.lpBasis ℕ+).orthonormal.norm_eq_one j,mul_one,sq_abs]

private theorem heat_two (i j : ℕ+) (a b : ℝ) :
    criticalOperator ((a:ℂ) • basisWave i+(b:ℂ) • basisWave j) =
      ((a*attenuation i:ℝ):ℂ) • basisWave i+((b*attenuation j:ℝ):ℂ) • basisWave j := by
  rw [map_add,map_smul,map_smul,heat_wave,heat_wave,smul_smul,smul_smul,Complex.ofReal_mul,Complex.ofReal_mul]

/-- Every adjacent two-shell mixture gives a least trace deficit for its squared-operator error. -/
theorem two_shell_floor (k : ℕ) (t : Set.Icc (0:ℝ) 1) :
    let a := occupationWeight k
    let b := occupationWeight (k+1)
    let q := t.val*a+(1-t.val)*b
    IsLeast {y : ℝ | (q,y) ∈ closure squaredReadings} (2*(a+b)*q-2*a*b-q^2) := by
  let i := number k
  let j := number (k+1)
  let a := occupationWeight k
  let b := occupationWeight (k+1)
  let q := t.val*a+(1-t.val)*b
  change IsLeast {y : ℝ | (q,y) ∈ closure squaredReadings} (2*(a+b)*q-2*a*b-q^2)
  have hij : i ≠ j := fun h => Nat.ne_of_lt (Nat.lt_succ_self k) (number_injective h)
  let c := Real.sqrt t.val
  let d := Real.sqrt (1-t.val)
  have hc : c^2 = t.val := Real.sq_sqrt t.property.1
  have hd : d^2 = 1-t.val := Real.sq_sqrt (sub_nonneg.mpr t.property.2)
  let f := (c:ℂ) • basisWave i+(d:ℂ) • basisWave j
  have hf : ‖f‖ = 1 := by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp
    change ‖(c:ℂ) • basisWave i+(d:ℂ) • basisWave j‖^2 = 1^2
    rw [wave_norm hij,hc,hd,one_pow]
    ring
  have hm : ‖criticalOperator f‖^2 = q := by
    change ‖criticalOperator ((c:ℂ) • basisWave i+(d:ℂ) • basisWave j)‖^2 = _
    rw [heat_two,wave_norm hij,mul_pow,mul_pow,hc,hd]
    rfl
  have hs : ‖squareHeat.val f‖^2 = t.val*a^2+(1-t.val)*b^2 := by
    change ‖criticalOperator (criticalOperator ((c:ℂ) • basisWave i+(d:ℂ) • basisWave j))‖^2 = _
    rw [heat_two,heat_two,wave_norm hij]
    simp only [mul_pow,hc,hd]
    change (t.val*a)*a+((1-t.val)*b)*b = _
    ring
  constructor
  · have h := squared_line_contact f hf
    rw [hm,lineLoss,hs,hm,hf,one_pow,div_one,div_one] at h
    have he : 2*(t.val*a^2+(1-t.val)*b^2)-q^2 = 2*(a+b)*q-2*a*b-q^2 := by
      dsimp only [q]
      ring
    rwa [he] at h
  · have hclosed : IsClosed {z : ℝ × ℝ | 2*(a+b)*z.1 ≤ z.2+z.1^2+2*a*b} :=
      isClosed_le (continuous_const.mul continuous_fst)
        ((continuous_snd.add (continuous_fst.pow 2)).add continuous_const)
    have hsub : squaredReadings ⊆ {z : ℝ × ℝ | 2*(a+b)*z.1 ≤ z.2+z.1^2+2*a*b} := by
      rintro _ ⟨G,rfl⟩
      exact squared_error_gap G k
    intro y hy
    have hh := (hclosed.closure_subset_iff.mpr hsub) hy
    change 2*(a+b)*q ≤ y+q^2+2*a*b at hh
    linarith only [hh]

#print axioms two_shell_floor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
