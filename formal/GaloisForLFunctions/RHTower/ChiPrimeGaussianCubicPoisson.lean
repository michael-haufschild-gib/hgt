import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicFourierLattice
import GaloisForLFunctions.RHTower.ChiCompactLatticePoisson

/-!
# Complete physical cubic Poisson matching

The entire three-coordinate physical amplitude has an exact twisted Poisson
identity at every real frequency. All integer lifts are retained, with
absolute Fourier summability proved from Schwartz decay. The unconditional
family retains the literal amplitude and negligible sharp/smooth edge error.
This identity supplies no signed estimate uniform in the growing scale.
-/

open MeasureTheory
noncomputable section
open scoped FourierTransform ContDiff Topology
namespace RHTower.BAGTrace

namespace FullPoisson
open scoped FourierTransform

private def triples : Z ≃ ℤ × ℤ × ℤ where
  toFun n := (n 0,n 1,n 2)
  invFun n := ![n.1,n.2.1,n.2.2]
  left_inv n := by ext i; fin_cases i <;> rfl
  right_inv n := rfl

private lemma triples_point (n : Z) : WithLp.toLp 2 (ip n)=bagIntegerTriple (triples n) := by
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> rfl

private lemma character (k : Z) (x : X) :
    UnitAddTorus.mFourier (-k) (q x) =
      Complex.exp ((-2*Real.pi*inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (ip k)) : ℝ)*Complex.I) := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,q,fourier_coe_apply,
    Pi.neg_apply,Int.cast_neg,Complex.ofReal_one,div_one,PiLp.inner_apply,
    ip]
  simp only [Fin.prod_univ_succ,Fin.sum_univ_succ,Fin.prod_univ_zero,Fin.sum_univ_zero,
    mul_one,add_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  simp only [Real.inner_apply]
  push_cast
  ring

private def twist (f : BAGPhysicalSpace → ℂ) (a : BAGPhysicalSpace) (x : X) : ℂ :=
  Complex.exp ((2*Real.pi*inner ℝ (WithLp.toLp 2 x) a : ℝ)*Complex.I)*f (WithLp.toLp 2 x)

private lemma twist_continuous (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) :
    Continuous (twist f a) := by
  unfold twist
  have ht : Continuous (WithLp.toLp 2 : X → BAGPhysicalSpace) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.continuous
  exact ((Complex.continuous_ofReal.comp (continuous_const.mul
    (ht.inner continuous_const))).mul continuous_const).cexp.mul (f.continuous.comp ht)

private lemma twist_compact (f : SchwartzMap BAGPhysicalSpace ℂ) (hf : HasCompactSupport (f : BAGPhysicalSpace → ℂ))
    (a : BAGPhysicalSpace) : HasCompactSupport (twist f a) := by
  apply HasCompactSupport.mul_left
  exact hf.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm

private lemma twist_coefficient (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) (k : Z) :
    (∫ x, UnitAddTorus.mFourier (-k) (q x)*twist f a x) =
      (𝓕 f) (WithLp.toLp 2 (ip k)-a) := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 X).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [character]
  simp only [twist,smul_eq_mul,← mul_assoc,← Complex.exp_add]
  congr 2
  rw [inner_sub_right]
  push_cast
  ring

/-- Full twisted lattice matching for compact Schwartz inputs. -/
theorem full_poisson (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hf : HasCompactSupport (f : BAGPhysicalSpace → ℂ)) (a : BAGPhysicalSpace) :
    (∑' k : ℤ × ℤ × ℤ, (𝓕 f) (bagIntegerTriple k-a)) =
      ∑' n : ℤ × ℤ × ℤ,
        Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple n) a : ℝ)*Complex.I)*f (bagIntegerTriple n) := by
  have hs : Summable (fun k : Z => (𝓕 f) (WithLp.toLp 2 (ip k)-a)) := by
    have h := (summable_norm_bagFourierIntegerTriple f (-a)).of_norm
    simpa only [Function.comp_def,triples_point,sub_eq_add_neg] using h.comp_injective triples.injective
  have h := poisson (twist_continuous f a) (twist_compact f hf a) (by
    simpa only [twist_coefficient] using hs)
  simp only [twist_coefficient] at h
  calc
    _ = ∑' k : Z, (𝓕 f) (bagIntegerTriple (triples k)-a) :=
      (triples.tsum_eq (fun k => (𝓕 f) (bagIntegerTriple k-a))).symm
    _ = ∑' n : Z, Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple (triples n)) a : ℝ)*Complex.I)*
        f (bagIntegerTriple (triples n)) := by
      simpa only [twist,triples_point] using h
    _ = _ := triples.tsum_eq (fun n : ℤ × ℤ × ℤ =>
      Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple n) a : ℝ)*Complex.I)*
        f (bagIntegerTriple n))
end FullPoisson

/-- Unconditional physical family with the complete twisted Poisson identity
at every frequency, all Fourier lifts summable, and negligible edge error. -/
theorem exists_bagCubicPhysicalPoissonFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in Filter.atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Set.Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Set.Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        HasCompactSupport (A N : BAGPhysicalSpace → ℂ) ∧
        (∀ a : BAGPhysicalSpace, Summable (fun k : ℤ × ℤ × ℤ =>
          ‖(𝓕 (A N)) (bagIntegerTriple k-a)‖)) ∧
        (∀ a : BAGPhysicalSpace,
          (∑' k : ℤ × ℤ × ℤ, (𝓕 (A N)) (bagIntegerTriple k-a)) =
            ∑' n : ℤ × ℤ × ℤ,
              Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple n) a : ℝ)*Complex.I)*
                A N (bagIntegerTriple n))) ∧
      Filter.Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal (N : ℝ)-
          primeGaussianCubicSmoothedOffDiagonal N (η N)‖) Filter.atTop (nhds 0) := by
  obtain ⟨η,A,hA,herr⟩ := exists_bagCubicPhysicalFourierFamily
  refine ⟨η,A,?_,herr⟩
  filter_upwards [hA] with N hN
  obtain ⟨hsm,hco,hbo,hze,hpl,heq,hfs⟩ := hN
  have hc : HasCompactSupport (A N : BAGPhysicalSpace → ℂ) := by
    rw [show (A N : BAGPhysicalSpace → ℂ)=bagCubicPhysicalAmplitude N (η N) from funext heq]
    exact hasCompactSupport_bagCubicPhysicalAmplitude N hze
  refine ⟨hsm,hco,hbo,hze,hpl,heq,hc,?_,?_⟩
  · intro a
    simpa only [sub_eq_add_neg] using hfs (-a)
  · exact fun a => FullPoisson.full_poisson (A N) hc a

end RHTower.BAGTrace
