import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.BinaryProbe
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Classification
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Parseval

/-! # The unique prime sampling exponent that recovers every finite gas norm -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- Mean over elementary labels with the squared heat weights. -/
def sample (σ : ℝ) (N : ℕ) (f : ℕ → ℝ) :=
  (∑ p ∈ primes N, bornWeight σ p * f p) / bornMass σ N

/-- Born mean of the intensity of a finite gas preparation read at prime clocks. -/
def preparationMean {M : ℕ} (σ : ℝ) (a : Fin M → ℂ) (N : ℕ) :=
  sample σ N (fun p => ‖_root_.RHTower.Sieve.dirPoly M a (-log p)‖^2)

theorem sampled_intensity (σ t : ℝ) (N k : ℕ) (b : ℂ) :
    intensityMean (bornLaw σ t N) b k =
      sample σ N (fun p => intensity b k (phase t p)) := by
  have pos : 0 < bornMass σ N := by
    apply sum_pos' (fun p _ => rpow_nonneg (Nat.cast_nonneg p) _)
    exact ⟨2,Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩,rpow_pos_of_pos (by norm_num) _⟩
  exact integral_normalizedFiniteRealAtomicMeasure _ _ _ (fun p _ =>
    rpow_nonneg (Nat.cast_nonneg p) _) pos _

/-- The vacuum and the last shell in the packet have relative amplitude b. -/
private def pairCoeff (K : ℕ) (b : ℂ) (j : Fin (K+1)) : ℂ :=
  (if 0=j then 1 else 0) + (if Fin.last K=j then b else 0)

private theorem pair_norm {K : ℕ} (hK : 0<K) (b : ℂ) :
    ∑ j, ‖pairCoeff K b j‖^2 = 1+‖b‖^2 := by
  have distinct : Fin.last K ≠ (0 : Fin (K+1)) := by
    intro e
    have h := congrArg Fin.val e
    change K=0 at h
    omega
  have term (j : Fin (K+1)) : ‖pairCoeff K b j‖^2 =
      (if 0=j then (1:ℝ) else 0) + (if Fin.last K=j then ‖b‖^2 else 0) := by
    by_cases hz : 0=j
    · subst j; simp [pairCoeff,distinct]
    · by_cases he : Fin.last K=j <;> simp [pairCoeff,hz,he]
  simp only [term,sum_add_distrib,sum_ite_eq,mem_univ,if_true]

private def width (k : ℕ) := 2^(k+1)-1

private theorem width_succ (k : ℕ) : width k+1=2^(k+1) :=
  Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (by norm_num) _))

private theorem width_pos (k : ℕ) : 0<width k := by
  have h := one_lt_pow₀ (by norm_num : 1<(2:ℕ)) (Nat.succ_ne_zero k)
  have e := width_succ k
  omega

private theorem pair_amplitude (b : ℂ) (k p : ℕ) :
    _root_.RHTower.Sieve.dirPoly (width k+1) (pairCoeff (width k) b) (-log p) =
      1+b*(phase (log 2) p : ℂ)^(k+1) := by
  simp only [_root_.RHTower.Sieve.dirPoly,pairCoeff,add_mul,ite_mul,one_mul,zero_mul,
    sum_add_distrib,sum_ite_eq,mem_univ,if_true,Fin.val_zero,Nat.cast_zero,zero_add,
    log_one,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,Fin.val_last]
  have e : ((width k:ℝ)+1) = (2:ℝ)^(k+1) := by exact_mod_cast width_succ k
  rw [e,log_pow,phase,Circle.coe_exp,←Complex.exp_nat_mul]
  congr 3
  push_cast
  ring

/-- Both quadratures at each power of two force the critical exponent. -/
theorem binary_sample_iff (σ : ℝ) :
    (∀ k : ℕ, Tendsto (fun N => sample σ N (fun p => intensity 1 (k+1) (phase (log 2) p)))
        atTop (𝓝 2) ∧
      Tendsto (fun N => sample σ N (fun p => intensity Complex.I (k+1) (phase (log 2) p)))
        atTop (𝓝 2)) ↔ σ=1/2 := by
  simpa only [sampled_intensity] using
    (haar_iff_binary_probes (bornLaw σ (log 2))).symm.trans
      (haar_iff_half σ (log_pos (by norm_num : (1:ℝ)<2)).ne')

/-- Mean-square recovery of every finite coherent gas preparation
characterizes the harmonic Born weights. -/
theorem full_norm_iff (σ : ℝ) :
    (∀ (M : ℕ) (a : Fin M → ℂ), Tendsto (preparationMean σ a) atTop
      (𝓝 (∑ n, ‖a n‖^2))) ↔ σ=1/2 := by
  constructor
  · intro h
    apply (binary_sample_iff σ).mp
    intro k
    have lim (b : ℂ) (hb : ‖b‖=1) :
        Tendsto (fun N => sample σ N (fun p => intensity b (k+1) (phase (log 2) p))) atTop (𝓝 2) := by
      have hh := h (width k+1) (pairCoeff (width k) b)
      rw [pair_norm (width_pos k),hb,one_pow,one_add_one_eq_two] at hh
      exact hh.congr (fun N => by simp only [preparationMean,pair_amplitude,intensity])
    exact ⟨lim 1 norm_one,lim Complex.I Complex.norm_I⟩
  · rintro rfl M a
    have w (p : ℕ) : bornWeight (1/2) p = weight p := by
      simp only [bornWeight,weight,show (2:ℝ)*(1/2)=1 by norm_num,rpow_neg_one]
    have eq (N : ℕ) : bornMass (1/2) N = mass N := by simp only [bornMass,w,mass]
    exact (preparation_mean_square a).congr (fun N => by simp only [preparationMean,sample,w,eq])

theorem full_norm_iff_split (s : ℂ) :
    (∀ (M : ℕ) (a : Fin M → ℂ), Tendsto (preparationMean s.re a) atTop
      (𝓝 (∑ n, ‖a n‖^2))) ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  (full_norm_iff s.re).trans (split_isometric_iff s).symm

#print axioms sampled_intensity
#print axioms binary_sample_iff
#print axioms full_norm_iff
#print axioms full_norm_iff_split

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
