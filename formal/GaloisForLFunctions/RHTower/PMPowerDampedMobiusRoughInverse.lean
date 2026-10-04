import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSlab
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteDeletion

/-!
# Exact rough-factor inversion of the finite PM source

Integer Möbius inversion and a finite divisor-antidiagonal interchange give
the full rough dilation sum. The identity retains all repeated prime factors
and requires no convergence or square-integrability premise.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace RHTower

private theorem pmr_core_coefficient (S : Finset ℕ) (n : ℕ) :
    (CoprimeMobius.mobiusAF (↑S : Set ℕ)ᶜ n : ℂ) =
      finitePrimeApertureMobiusCoefficient S n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [finitePrimeApertureMobiusCoefficient,mobiusComplexCoefficient]
  · have hf : CoprimeMobius.IsFree (↑S : Set ℕ)ᶜ n ↔ n.primeFactors ⊆ S := by
      simp [CoprimeMobius.IsFree,hn,Finset.subset_iff]
    simp [CoprimeMobius.mobiusAF,pmul_apply,CoprimeMobius.freeAF,hf,
      finitePrimeApertureMobiusCoefficient,mobiusComplexCoefficient]

private theorem pmr_rough_inverse (S : Finset ℕ) (n : ℕ) :
    (∑ md ∈ n.divisorsAntidiagonal,
      (CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ md.1 : ℂ)*(moebius md.2 : ℂ)) =
      finitePrimeApertureMobiusCoefficient S n := by
  have hz : CoprimeMobius.mobiusAF (↑S : Set ℕ)ᶜ*(zeta : ArithmeticFunction ℤ) =
      CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ := by
    ext k
    rw [coe_mul_zeta_apply]
    exact CoprimeMobius.sum_divisors_mobiusAF _ k
  have hi : CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ*moebius =
      CoprimeMobius.mobiusAF (↑S : Set ℕ)ᶜ := by
    rw [← hz,mul_assoc,coe_zeta_mul_moebius,mul_one]
  have hn := congrArg (fun f : ArithmeticFunction ℤ => f n) hi
  rw [ArithmeticFunction.mul_apply] at hn
  rw [← pmr_core_coefficient]
  exact_mod_cast hn

private theorem pmr_fermi_mul (d m t : ℝ) :
    fermiNymanGen d (m*t) = fermiNymanGen (m*d) t := by
  unfold fermiNymanGen GaloisForLFunctions.NymanMellin.nymanGen
  rw [show d*(m*t) = (m*d)*t by ring,
    show (2*d)*(m*t) = (2*(m*d))*t by ring]

/-- The exact positive rough-factor inverse of a finite prime aperture.
Every rough integer is retained, including repeated prime factors. -/
theorem pmFinitePrimePowerDampedFermiSource_rough_inverse {S : Finset ℕ}
    (hS : ∀ p ∈ S,p.Prime) (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    pmFinitePrimePowerDampedFermiSource S ε t =
      ∑ m ∈ Finset.Icc 1 ⌊1/t⌋₊,
        (CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ m : ℂ)*
          (((m : ℝ)^(-ε) : ℝ) : ℂ)*pmPowerDampedFermiSource ε ((m : ℝ)*t) := by
  classical
  let N : ℕ := ⌊1/t⌋₊
  let F : ℕ → ℕ → ℂ := fun m d =>
    (CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ m : ℂ)*(moebius d : ℂ)*
      ((((m*d : ℕ) : ℝ)^(-ε) : ℝ) : ℂ)*fermiNymanGen (m*d : ℕ) t
  have hinner (m : ℕ) (hm : m ∈ Finset.Icc 1 N) :
      (CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ m : ℂ)*
        (((m : ℝ)^(-ε) : ℝ) : ℂ)*pmPowerDampedFermiSource ε ((m : ℝ)*t) =
        -(∑ d ∈ Finset.Icc 1 (N/m),F m d) := by
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hfloor : ⌊1/((m : ℝ)*t)⌋₊ = N/m := by
      rw [show 1/((m : ℝ)*t) = (1/t)/(m : ℝ) by ring,Nat.floor_div_natCast]
    rw [pmPowerDampedFermiSource_eq_sum ε (mul_pos hm0 ht) (le_of_eq hfloor),
      mul_neg,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [pmr_fermi_mul]
    simp only [F,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg d),
      Complex.ofReal_mul,Complex.ofReal_intCast]
    ring
  have hsum : (∑ m ∈ Finset.Icc 1 N,
      (CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ m : ℂ)*
        (((m : ℝ)^(-ε) : ℝ) : ℂ)*pmPowerDampedFermiSource ε ((m : ℝ)*t)) =
      -(∑ n ∈ Finset.Icc 1 N,∑ md ∈ n.divisorsAntidiagonal,F md.1 md.2) := by
    rw [Sieve.sum_Icc_divisorsAntidiagonal_swap F N]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hinner
  rw [pmFinitePrimePowerDampedFermiSource_eq_sum hS ε ht (le_refl N)]
  change -(∑ d ∈ Finset.Icc 1 N,finitePrimeApertureMobiusCoefficient S d*
    (((d : ℝ)^(-ε) : ℝ) : ℂ)*fermiNymanGen d t) = _
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hterm (md : ℕ × ℕ) (hmd : md ∈ n.divisorsAntidiagonal) :
      F md.1 md.2 =
      ((CoprimeMobius.smoothAF (↑S : Set ℕ)ᶜ md.1 : ℂ)*(moebius md.2 : ℂ))*
        (((n : ℝ)^(-ε) : ℝ) : ℂ)*fermiNymanGen n t := by
    dsimp [F]
    rw [(Nat.mem_divisorsAntidiagonal.mp hmd).1]
  rw [Finset.sum_congr rfl hterm,← Finset.sum_mul,← Finset.sum_mul,pmr_rough_inverse]

end RHTower
