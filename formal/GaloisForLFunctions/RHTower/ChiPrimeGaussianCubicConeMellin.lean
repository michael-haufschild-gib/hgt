import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicTransverse
import GaloisForLFunctions.RHTower.ChiRamanujanRationalCofactors
import GaloisForLFunctions.HTGeometry.PositiveQuadrantLogSchwartz
/-!
# Full physical cone Mellin pairing

The complete three-coordinate Fourier Schwartz amplitude restricts to a
Schwartz function on the polynomial cone (x,y,-xy). Full two-variable
Mellin inversion and an absolute summable majorant pair this actual test
with the complete distinguished rational source. Both numerator cofactors
and both physical label exclusions remain in the Euler/cofactor integral.

The original physical cutoff family retains its negligible sharp/smooth
comparison. The near-cone region, other frequency sectors and their joint
signed estimate are separate from this exact positive-cone identity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform ContDiff Topology BigOperators
namespace RHTower.BAGTrace


abbrev BAGConeSpace := EuclideanSpace ℝ (Fin 2)

def bagCubicConeNode (v : BAGConeSpace) : BAGPhysicalSpace :=
  WithLp.toLp 2 ![v 0,v 1,-v 0*v 1]

private lemma node_growth : bagCubicConeNode.HasTemperateGrowth := by
  let e (i : Fin 3) : BAGPhysicalSpace := WithLp.toLp 2 (Pi.single i 1)
  have hg (i : Fin 2) : (fun v : BAGConeSpace => v i).HasTemperateGrowth :=
    (EuclideanSpace.proj i).hasTemperateGrowth
  have he : bagCubicConeNode = fun v => v 0 • e 0 + v 1 • e 1 + (-v 0*v 1) • e 2 := by
    funext v
    ext i
    fin_cases i <;> simp [bagCubicConeNode,e]
  rw [he]
  exact (((hg 0).smul (Function.HasTemperateGrowth.const (e 0))).add
    ((hg 1).smul (Function.HasTemperateGrowth.const (e 1)))).add
      (((hg 0).neg.mul (hg 1)).smul (Function.HasTemperateGrowth.const (e 2)))

private lemma node_lower (v : BAGConeSpace) : ‖v‖ ≤ 1+‖bagCubicConeNode v‖ := by
  have hv := EuclideanSpace.norm_sq_eq v
  have he : ‖bagCubicConeNode v‖^2=v 0^2+v 1^2+(v 0*v 1)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [bagCubicConeNode,Fin.sum_univ_succ]
    ring
  simp [Fin.sum_univ_succ] at hv
  nlinarith [norm_nonneg v,norm_nonneg (bagCubicConeNode v),sq_nonneg (v 0*v 1)]

def bagCubicConeSchwartz (f : SchwartzMap BAGPhysicalSpace ℂ) : SchwartzMap BAGConeSpace ℂ :=
  SchwartzMap.compCLM ℂ node_growth ⟨1,1,by simpa using node_lower⟩ (𝓕 f)

theorem bagCubicConeSchwartz_apply (f : SchwartzMap BAGPhysicalSpace ℂ) (v : BAGConeSpace) :
    bagCubicConeSchwartz f v=(𝓕 f) (bagCubicConeNode v) := rfl

open HTGeometry

private abbrev RationalPair (P : Finset Nat.Primes) :=
  DenominatorRational P × DenominatorRational P

def criticalRationalMass (P : Finset Nat.Primes) (w : RationalPair P) : ℂ :=
  criticalRationalCone P 0 0 w

def criticalRationalPoint (P : Finset Nat.Primes) (w : RationalPair P) : BAGConeSpace :=
  WithLp.toLp 2 ![(w.1.val.val : ℝ),(w.2.val.val : ℝ)]

private lemma cone_factor (P : Finset Nat.Primes) (s t : ℂ) (w : RationalPair P) :
    criticalRationalCone P s t w=criticalRationalMass P w*
      rationalCharacter s w.1.val*rationalCharacter t w.2.val := by
  classical
  simp only [criticalRationalMass,criticalRationalCone,criticalRationalLabelCone,
    rationalCharacter,neg_zero,Complex.cpow_zero,mul_one,Finset.sum_mul,ite_mul,zero_mul]

private lemma cone_line (P : Finset Nat.Primes) (w : RationalPair P) (v : BAGConeSpace) :
    criticalRationalCone P (quadrantMellinLine (v 0)) (quadrantMellinLine (v 1)) w=
      criticalRationalMass P w*quadrantMellinKernel (w.1.val.val : ℝ) (w.2.val.val : ℝ) v := by
  rw [cone_factor]
  change _ = criticalRationalMass P w*(rationalCharacter _ w.1.val*rationalCharacter _ w.2.val)
  ring

private lemma cone_norm (P : Finset Nat.Primes) (w : RationalPair P) (v : BAGConeSpace) :
    ‖criticalRationalCone P (quadrantMellinLine (v 0)) (quadrantMellinLine (v 1)) w‖=
      ‖criticalRationalCone P 2 2 w‖ := by
  have he : criticalRationalCone P 2 2 w=
      criticalRationalCone P (quadrantMellinLine ((0 : BAGConeSpace) 0))
        (quadrantMellinLine ((0 : BAGConeSpace) 1)) w := by simp [quadrantMellinLine]
  rw [he,cone_line,cone_line,norm_mul,norm_mul,
    norm_quadrantMellinKernel (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property),
    norm_quadrantMellinKernel (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property)]

/-- The entire rational cone paired with any full three-coordinate Schwartz
Fourier profile. Both numerator cofactors, both label exclusions, and both
Mellin frequencies remain in the absolutely justified identity. -/
theorem criticalRationalCone_physical_hasSum (P : Finset Nat.Primes)
    (f : SchwartzMap BAGPhysicalSpace ℂ) :
    HasSum (fun w : RationalPair P => criticalRationalMass P w*
      (𝓕 f) (bagCubicConeNode (criticalRationalPoint P w)))
      (∫ v : BAGConeSpace,
        criticalCompletedConeEuler P (quadrantMellinLine (v 0)) (quadrantMellinLine (v 1))*
          quadrantMellinProfile (bagCubicConeSchwartz f) v) := by
  let Φ := bagCubicConeSchwartz f
  let Ψ := quadrantMellinProfile Φ
  let A (w : RationalPair P) (v : BAGConeSpace) : ℂ :=
    criticalRationalCone P (quadrantMellinLine (v 0)) (quadrantMellinLine (v 1)) w*Ψ v
  let B (w : RationalPair P) (v : BAGConeSpace) : ℝ :=
    ‖criticalRationalCone P 2 2 w‖*‖Ψ v‖
  have hsum : Summable (fun w : RationalPair P => ‖criticalRationalCone P 2 2 w‖) :=
    (criticalRationalCone_hasSum P (by norm_num) (by norm_num)).summable.norm
  have hmeas (w : RationalPair P) : AEStronglyMeasurable (A w) volume := by
    have h : A w=fun v => (criticalRationalMass P w*
        quadrantMellinKernel (w.1.val.val : ℝ) (w.2.val.val : ℝ) v)*Ψ v := by
      funext v
      dsimp only [A]
      rw [cone_line]
    rw [h]
    exact ((continuous_const.mul (continuous_quadrantMellinKernel
      (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property))).mul
        Ψ.continuous).aestronglyMeasurable
  have hbound (w : RationalPair P) : ∀ᵐ v : BAGConeSpace,
      ‖A w v‖ ≤ B w v := by
    filter_upwards [] with v
    dsimp only [A,B]
    exact le_of_eq (by rw [norm_mul,cone_norm])
  have hbsum : ∀ᵐ v : BAGConeSpace, Summable (fun w => B w v) := by
    filter_upwards [] with v
    exact hsum.mul_right ‖Ψ v‖
  have hbint : Integrable (fun v : BAGConeSpace => ∑' w, B w v) := by
    have he : (fun v : BAGConeSpace => ∑' w, B w v)=fun v =>
        (∑' w : RationalPair P, ‖criticalRationalCone P 2 2 w‖)*‖Ψ v‖ := by
      funext v
      exact tsum_mul_right
    rw [he]
    exact Ψ.integrable.norm.const_mul _
  have hlim : ∀ᵐ v : BAGConeSpace,
      HasSum (fun w => A w v)
        (criticalCompletedConeEuler P (quadrantMellinLine (v 0)) (quadrantMellinLine (v 1))*Ψ v) := by
    filter_upwards [] with v
    apply HasSum.mul_right
    apply criticalRationalCone_hasSum P <;> simp [quadrantMellinLine]
  have h := hasSum_integral_of_dominated_convergence B hmeas hbound hbsum hbint hlim
  apply h.congr_fun
  intro w
  symm
  change (∫ v : BAGConeSpace, A w v)=_
  have he : A w=fun v => criticalRationalMass P w*
      (quadrantMellinKernel (w.1.val.val : ℝ) (w.2.val.val : ℝ) v*Ψ v) := by
    funext v
    dsimp only [A]
    rw [cone_line,mul_assoc]
  rw [he,integral_const_mul]
  have hinv := quadrantMellin_inversion Φ (x := (w.1.val.val : ℝ)) (y := (w.2.val.val : ℝ))
    (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property)
  rw [hinv]
  rfl


/-- The cone restriction retains the entire r integral and the complete
physical-window Mellin transition, with exactly zero transverse defect. -/
theorem bagCubicConeSchwartz_physical {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) (v : BAGConeSpace) :
    bagCubicConeSchwartz (bagCubicPhysicalSchwartz hN hη hz) v=
      ∫ r : ℝ, (2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)*
        bagCubicTransverseProfile N η r (v 0) (v 1) := by
  rw [bagCubicConeSchwartz_apply]
  have h := (bagCubicPhysicalFourier_eq_transverse hN hη hc hz (bagCubicConeNode v)).2
  simpa [bagCubicConeNode,bourgainOscillation] using h

/-- Unconditional actual cutoff family with its full positive rational cone
Mellin pairing and the original negligible sharp/smooth comparison. -/
theorem exists_bagCubicPhysicalConeMellinFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        (∀ a : BAGPhysicalSpace, Summable (fun k : ℤ × ℤ × ℤ =>
          ‖(𝓕 (A N)) (bagIntegerTriple k+a)‖))) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal (N : ℝ)-
          primeGaussianCubicSmoothedOffDiagonal N (η N)‖) atTop (𝓝 0) ∧
      (∀ (N : ℕ) (P : Finset Nat.Primes),
        HasSum (fun w : RationalPair P => criticalRationalMass P w*
          (𝓕 (A N)) (bagCubicConeNode (criticalRationalPoint P w)))
          (∫ v : BAGConeSpace,
            criticalCompletedConeEuler P (quadrantMellinLine (v 0)) (quadrantMellinLine (v 1))*
              quadrantMellinProfile (bagCubicConeSchwartz (A N)) v)) := by
  obtain ⟨η,A,hreg,herr⟩ := exists_bagCubicPhysicalFourierFamily
  exact ⟨η,A,hreg,herr,fun N P => criticalRationalCone_physical_hasSum P (A N)⟩

end RHTower.BAGTrace
