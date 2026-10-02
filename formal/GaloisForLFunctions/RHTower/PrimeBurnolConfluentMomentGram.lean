import GaloisForLFunctions.RHTower.PrimeBurnolFiniteOffDiagonalFaithfulness
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialVandermonde
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Literal Burnol confluent moment Gram

The original radial columns and their first radial jets form a linearly independent L2 family
for every finite injective prime-depth packet. Their full mixed Gram has the factorial Laplace
moment entries proved here. Its Schur complement is invertible and its inverse is the lower
block of the full confluent inverse. These are finite-packet identities; no uniform inverse
bound or Hardy-index comparison is asserted.
-/

open Complex Matrix Set MeasureTheory Polynomial
open scoped BigOperators
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

def primeBurnolRadialJet (pe : Nat.Primes × ℕ) (m : ℕ) (r : ℝ) : ℂ :=
  primeBurnolAmplitude pe * ((r : ℂ)^(m+1) *
    Complex.exp (-((primeBurnolLogFrequency pe : ℂ)*(r : ℂ))))

theorem continuous_primeBurnolRadialJet (pe : Nat.Primes × ℕ) (m : ℕ) :
    Continuous (primeBurnolRadialJet pe m) := by unfold primeBurnolRadialJet; fun_prop

theorem memLp_primeBurnolRadialJet (pe : Nat.Primes × ℕ) (m : ℕ) :
    MemLp (primeBurnolRadialJet pe m) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_primeBurnolRadialJet pe m).aestronglyMeasurable.restrict).2
  have hl := primeBurnolLogFrequency_pos pe
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (((m+1)*2 : ℕ) : ℝ)) (p := (1 : ℝ))
    (b := 2*primeBurnolLogFrequency pe)
    (by have h : (0 : ℝ) ≤ ((m+1)*2 : ℕ) := Nat.cast_nonneg _; linarith)
    (by norm_num) (by positivity)
  have hi' : IntegrableOn (fun r : ℝ =>
      r^((m+1)*2)*Real.exp (-(2*primeBurnolLogFrequency pe)*r)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using hi
  have hs : IntegrableOn (fun r : ℝ => ‖primeBurnolAmplitude pe‖^2 *
      (r^((m+1)*2)*Real.exp (-(2*primeBurnolLogFrequency pe)*r))) (Ioi 0) :=
    hi'.const_mul _
  apply hs.congr_fun _ measurableSet_Ioi
  intro r hr
  symm
  change ‖primeBurnolRadialJet pe m r‖^2 = _
  rw [primeBurnolRadialJet, norm_mul, norm_natPow_mul_cexp hr.le,
    mul_pow, mul_pow, ← pow_mul]
  simp only [Complex.ofReal_re]
  rw [show Real.exp (-(primeBurnolLogFrequency pe*r))^2 =
      Real.exp (-(2*primeBurnolLogFrequency pe)*r) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]

def primeBurnolRadialJetLp (pe : Nat.Primes × ℕ) (m : ℕ) : primeBurnolHalfLineL2 :=
  (memLp_primeBurnolRadialJet pe m).toLp (primeBurnolRadialJet pe m)

theorem primeBurnolRadialJetLp_coeFn (pe : Nat.Primes × ℕ) (m : ℕ) :
    (primeBurnolRadialJetLp pe m : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      primeBurnolRadialJet pe m := (memLp_primeBurnolRadialJet pe m).coeFn_toLp

private theorem radialJet_sum_coe {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (pe : ι → Nat.Primes × ℕ) (m : ι → ℕ) :
    ((∑ i ∈ s, c i • primeBurnolRadialJetLp (pe i) (m i) : primeBurnolHalfLineL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => ∑ i ∈ s, c i * primeBurnolRadialJet (pe i) (m i) r := by
  induction s using Finset.induction_on with
  | empty =>
    exact (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))).trans
      (Filter.Eventually.of_forall fun _ => rfl)
  | @insert i s hi ih =>
    filter_upwards [Lp.coeFn_add (c i • primeBurnolRadialJetLp (pe i) (m i))
        (∑ j ∈ s, c j • primeBurnolRadialJetLp (pe j) (m j)),
      Lp.coeFn_smul (c i) (primeBurnolRadialJetLp (pe i) (m i)),
      primeBurnolRadialJetLp_coeFn (pe i) (m i), ih] with r hadd hsmul hjet hsum
    rw [Finset.sum_insert hi, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
      smul_eq_mul, hjet, hsum, Finset.sum_insert hi]

theorem primeBurnolConfluentPair_linearIndependent {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    LinearIndependent ℂ (fun i : Fin N × Fin 2 => primeBurnolRadialJetLp (pe i.1) i.2.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hraw : (fun r : ℝ => ∑ j : Fin N × Fin 2,
      c j * primeBurnolRadialJet (pe j.1) j.2.val r)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
    have hcoe := radialJet_sum_coe Finset.univ c (fun j => pe j.1) (fun j => j.2.val)
    rw [show (∑ j ∈ Finset.univ, c j • primeBurnolRadialJetLp (pe j.1) j.2.val) = 0 by
      simpa using hc] at hcoe
    exact hcoe.symm.trans (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ))))
  have hpoint := Measure.eqOn_open_of_ae_eq (μ := volume) hraw isOpen_Ioi
    (by unfold primeBurnolRadialJet; fun_prop : ContinuousOn (fun r : ℝ => ∑ j : Fin N × Fin 2,
      c j * primeBurnolRadialJet (pe j.1) j.2.val r) (Ioi 0)) continuousOn_const
  let z : Fin N → ℂ := fun j => (Real.exp (-primeBurnolLogFrequency (pe j)) : ℂ)
  let P : Fin N → Polynomial ℂ := fun j =>
    C (c (j,0)*primeBurnolAmplitude (pe j))*X +
    C (c (j,1)*primeBurnolAmplitude (pe j))*X^2
  have hz : Function.Injective z := by
    intro j l hjl
    apply pe.injective
    apply primeBurnolLogFrequency_injective
    have he : Real.exp (-primeBurnolLogFrequency (pe j)) =
        Real.exp (-primeBurnolLogFrequency (pe l)) := Complex.ofReal_injective hjl
    exact neg_injective (Real.exp_injective he)
  have hP := expPolySum_eq_zero z Finset.univ hz.injOn
    (fun j _ => by dsimp [z]; exact_mod_cast (Real.exp_pos _).ne') P (by
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have h := hpoint hnpos
      dsimp at h
      rw [Fintype.sum_prod_type] at h
      simp only [Fin.sum_univ_two] at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_pow, z, primeBurnolRadialJet]
      rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
      simp only [Complex.ofReal_neg, Complex.ofReal_natCast, Fin.val_zero,
        Fin.val_one, zero_add, one_add_one_eq_two, pow_one]
      rw [show (n : ℂ) * -(primeBurnolLogFrequency (pe j) : ℂ) =
        -((primeBurnolLogFrequency (pe j) : ℂ)*(n : ℂ)) by ring]
      ring)
  have hp0 := hP i.1 (Finset.mem_univ i.1)
  rcases i with ⟨j,b⟩
  fin_cases b
  · have h1 := congrArg (fun f : Polynomial ℂ => f.coeff 1) hp0
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h1
    norm_num at h1
    exact h1.resolve_right (primeBurnolAmplitude_ne_zero (pe j))
  · have h2 := congrArg (fun f : Polynomial ℂ => f.coeff 2) hp0
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] at h2
    norm_num at h2
    exact h2.resolve_right (primeBurnolAmplitude_ne_zero (pe j))

def primeBurnolConfluentPairGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ :=
  Matrix.gram ℂ (fun i => primeBurnolRadialJetLp (pe i.1) i.2.val)

theorem det_primeBurnolConfluentPairGram_ne_zero {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) : (primeBurnolConfluentPairGram pe).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (primeBurnolConfluentPair_linearIndependent pe)

theorem star_primeBurnolRadialJet (pe : Nat.Primes × ℕ) (m : ℕ) (r : ℝ) :
    star (primeBurnolRadialJet pe m r) = primeBurnolRadialJet pe m r := by
  simp [primeBurnolRadialJet, star_primeBurnolAmplitude,
    ← Complex.exp_conj]

theorem inner_primeBurnolRadialJetLp_eq (u v : Nat.Primes × ℕ) (m n : ℕ) :
    inner ℂ (primeBurnolRadialJetLp u m) (primeBurnolRadialJetLp v n) =
      primeBurnolAmplitude u * primeBurnolAmplitude v *
        (((m+n+2).factorial : ℂ) /
          ((primeBurnolLogFrequency u + primeBurnolLogFrequency v : ℝ) : ℂ)^(m+n+3)) := by
  rw [MeasureTheory.L2.inner_def]
  have hi : (∫ r : ℝ, inner ℂ
      ((primeBurnolRadialJetLp u m : primeBurnolHalfLineL2) r)
      ((primeBurnolRadialJetLp v n : primeBurnolHalfLineL2) r)
      ∂volume.restrict (Ioi (0 : ℝ))) =
      ∫ r : ℝ in Ioi 0, primeBurnolAmplitude u * primeBurnolAmplitude v *
        ((r : ℂ)^(m+n+2) * Complex.exp
          (-(((primeBurnolLogFrequency u + primeBurnolLogFrequency v : ℝ) : ℂ)*(r : ℂ)))) := by
    apply integral_congr_ae
    filter_upwards [primeBurnolRadialJetLp_coeFn u m,
      primeBurnolRadialJetLp_coeFn v n] with r hu hv
    rw [hu, hv, RCLike.inner_apply, starRingEnd_apply, mul_comm,
      star_primeBurnolRadialJet]
    unfold primeBurnolRadialJet
    calc
      _ = primeBurnolAmplitude u * primeBurnolAmplitude v *
          ((r : ℂ)^(m+1) * (r : ℂ)^(n+1) *
            (Complex.exp (-((primeBurnolLogFrequency u : ℂ)*(r : ℂ))) *
              Complex.exp (-((primeBurnolLogFrequency v : ℂ)*(r : ℂ))))) := by ring
      _ = _ := by
        rw [← pow_add, ← Complex.exp_add]
        congr 2
        · congr 1; omega
        · congr 1
          push_cast
          ring
  rw [hi, MeasureTheory.integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_Ioi_pow_mul_cexp
      (by simpa only [Complex.ofReal_re] using
        add_pos (primeBurnolLogFrequency_pos u) (primeBurnolLogFrequency_pos v)) (m+n+2)]

def primeBurnolMomentMatrix {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (m : ℕ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  primeBurnolAmplitude (pe i) * primeBurnolAmplitude (pe j) *
    (((m+2).factorial : ℂ) /
      ((primeBurnolLogFrequency (pe i)+primeBurnolLogFrequency (pe j) : ℝ) : ℂ)^(m+3))

def primeBurnolConfluentBlockGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (primeBurnolMomentMatrix pe 0) (primeBurnolMomentMatrix pe 1)
    (primeBurnolMomentMatrix pe 1) (primeBurnolMomentMatrix pe 2)

theorem primeBurnolConfluentBlockGram_eq_gram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    primeBurnolConfluentBlockGram pe = Matrix.gram ℂ
      (Sum.elim (fun i => primeBurnolRadialJetLp (pe i) 0)
        (fun i => primeBurnolRadialJetLp (pe i) 1)) := by
  ext (i | i) (j | j) <;>
    simp [primeBurnolConfluentBlockGram, Matrix.gram_apply,
      inner_primeBurnolRadialJetLp_eq, primeBurnolMomentMatrix]

theorem det_primeBurnolConfluentBlockGram_ne_zero {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) : (primeBurnolConfluentBlockGram pe).det ≠ 0 := by
  rw [primeBurnolConfluentBlockGram_eq_gram]
  apply Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
  have hinj : Function.Injective (Sum.elim
      (fun i : Fin N => (i,(0 : Fin 2))) (fun i : Fin N => (i,(1 : Fin 2)))) := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y <;> simp_all
  have hli := (primeBurnolConfluentPair_linearIndependent pe).comp _ hinj
  have heq : ((fun i : Fin N × Fin 2 => primeBurnolRadialJetLp (pe i.1) i.2.val) ∘
      Sum.elim (fun i : Fin N => (i,(0 : Fin 2))) (fun i : Fin N => (i,(1 : Fin 2)))) =
      Sum.elim (fun i => primeBurnolRadialJetLp (pe i) 0)
        (fun i => primeBurnolRadialJetLp (pe i) 1) := by
    ext (i | i) <;> rfl
  rw [heq] at hli
  exact hli

/-- Radial-moment residual after projecting onto all original packet columns. -/
def primeBurnolRadialSchurComplement {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  primeBurnolMomentMatrix pe 2 - primeBurnolMomentMatrix pe 1 *
    (primeBurnolMomentMatrix pe 0)⁻¹ * primeBurnolMomentMatrix pe 1

theorem primeBurnolMomentMatrix_zero_eq {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    primeBurnolMomentMatrix pe 0 = primeBurnolWindowGramMatrix pe (fun _ => 0) := by
  ext i j
  rw [primeBurnolWindowGramMatrix_apply]
  simp [primeBurnolMomentMatrix, primeBurnolPairRate]

theorem primeBurnolRadialSchurComplement_leftInverse {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    (primeBurnolConfluentBlockGram pe)⁻¹.toBlocks₂₂ *
      primeBurnolRadialSchurComplement pe = 1 := by
  let G := primeBurnolMomentMatrix pe 0
  let M := primeBurnolMomentMatrix pe 1
  let D := primeBurnolMomentMatrix pe 2
  let R := (primeBurnolConfluentBlockGram pe)⁻¹
  have hG : G*G⁻¹=1 := by
    apply Matrix.mul_nonsing_inv
    dsimp [G]
    rw [primeBurnolMomentMatrix_zero_eq]
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (primeBurnolWindowGramMatrix_isUnit pe pe.injective (fun _ => 0))
  have hfull : R * Matrix.fromBlocks G M M D = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (det_primeBurnolConfluentBlockGram_ne_zero pe))
  rw [← Matrix.fromBlocks_toBlocks R, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one] at hfull
  have h21 := congrArg Matrix.toBlocks₂₁ hfull
  have h22 := congrArg Matrix.toBlocks₂₂ hfull
  simp only [Matrix.toBlocks_fromBlocks₂₁] at h21
  simp only [Matrix.toBlocks_fromBlocks₂₂] at h22
  have h21' : R.toBlocks₂₁ = -(R.toBlocks₂₂*M*G⁻¹) := by
    have h := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A*G⁻¹) h21
    simp only [add_mul, Matrix.zero_mul, Matrix.mul_assoc, hG, Matrix.mul_one] at h
    simpa only [Matrix.mul_assoc] using eq_neg_of_add_eq_zero_left h
  change R.toBlocks₂₂*(D-M*G⁻¹*M)=1
  rw [h21'] at h22
  calc
    R.toBlocks₂₂*(D-M*G⁻¹*M) = -(R.toBlocks₂₂*M*G⁻¹)*M+R.toBlocks₂₂*D := by
      noncomm_ring
    _ = 1 := h22

theorem primeBurnolRadialSchurComplement_inverse {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    (primeBurnolRadialSchurComplement pe)⁻¹ =
      (primeBurnolConfluentBlockGram pe)⁻¹.toBlocks₂₂ :=
  Matrix.inv_eq_left_inv (primeBurnolRadialSchurComplement_leftInverse pe)

theorem det_primeBurnolRadialSchurComplement_ne_zero {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) : (primeBurnolRadialSchurComplement pe).det ≠ 0 := by
  intro hzero
  have h := congrArg Matrix.det (primeBurnolRadialSchurComplement_leftInverse pe)
  simp [Matrix.det_mul, hzero] at h

end
end RHTower
