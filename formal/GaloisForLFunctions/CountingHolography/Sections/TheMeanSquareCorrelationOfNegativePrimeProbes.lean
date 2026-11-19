import GaloisForLFunctions.CountingHolography.Sections.PrimeDisplacementGramAndModeQuotients
import GaloisForLFunctions.HTGeometry.SpectralEnsembleEigenvalueBound
import Mathlib.Algebra.Order.Chebyshev

/-!
# Mean-square correlation of negative prime probes

Normalize each negative diagonal to minus one. Cauchy–Schwarz on the negative
eigenspace bounds the square of the trace by the negative index times the
squared Frobenius norm. This gives a lower bound on the mean square correlation
of distinct probes in a finite off-line layer. Conversely, a single bound on
the total pair energy detects any prescribed number of right zeros.
-/

open Finset Matrix Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.CountingHolography.Sections

open ArithmeticScatteringHolography CountingHolography HTGeometry
open HeckeKreinToeplitz ArithmeticCastelnuovoSeveri RenormalizedIntersectionTheory
open Zeta23 ExclusionOfTheCriticalState

noncomputable section

/-- A negative trace costs negative index, even if positive eigenvalues are present. -/
theorem neg_trace_sq_le_negative_index_energy {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (ht : H.trace.re ≤ 0) :
    H.trace.re^2 ≤ (hermNegIndex H : ℝ)*((H^2).trace).re := by
  let e := hH.eigenvalues
  let S := univ.filter (fun i => e i < 0)
  have htr : ∑ i, e i = H.trace.re := by
    simpa only [Complex.re_sum,Complex.ofReal_re] using (congrArg Complex.re hH.trace_eq_sum_eigenvalues).symm
  have hpart := sum_filter_add_sum_filter_not univ (fun i => e i < 0) e
  have hrest : 0 ≤ ∑ i ∈ univ.filter (fun i => ¬e i < 0), e i :=
    sum_nonneg fun i hi => le_of_not_gt (mem_filter.mp hi).2
  have hle : -H.trace.re ≤ ∑ i ∈ S, -e i := by
    rw [sum_neg_distrib]
    change -H.trace.re ≤ -(∑ i ∈ univ.filter (fun i => e i < 0), e i)
    linarith only [hpart,hrest,htr]
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => -e i)
  simp only [neg_sq] at hcs
  have hsub := sum_le_sum_of_subset_of_nonneg (filter_subset (fun i => e i < 0) univ)
    (fun i _ _ => sq_nonneg (e i))
  rw [negIndex_eq_card_neg_eigenvalues hH,←sum_sq_eigenvalues_eq_trace_sq_re hH]
  calc _ = (-H.trace.re)^2 := (neg_sq _).symm
       _ ≤ _ := (pow_le_pow_left₀ (neg_nonneg.mpr ht) hle 2).trans
         (hcs.trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg S.card)))

/-- Normalized Krein pairing, with diagonal minus one on negative probes. -/
def probeCorrelation {m N : ℕ} (a : Fin m → (Fin N → ℤ)) (i j : Fin m) : ℝ :=
  probePairing N (a i) (a j) / Real.sqrt (probePairing N (a i) (a i)*probePairing N (a j) (a j))

/-- Sum over ordered pairs of distinct probes. -/
def distinctProbeEnergy {m N : ℕ} (a : Fin m → (Fin N → ℤ)) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, (probeCorrelation a i j)^2

private theorem probe_energy_nn {m N : ℕ} (a : Fin m → (Fin N → ℤ)) : 0 ≤ distinctProbeEnergy a :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- A finite family of m negative probes pays m² in trace energy. This is the
Welch bound with negative index in place of the ambient dimension. -/
theorem probe_negative_index_energy {m N : ℕ} (a : Fin m → (Fin N → ℤ))
    (hd : ∀ i, probePairing N (a i) (a i) < 0) :
    (m:ℝ)^2 ≤ (hermNegIndex (probeGramMatrix N a) : ℝ)*(m+distinctProbeEnergy a) := by
  let d (i : Fin m) := Real.sqrt (-probePairing N (a i) (a i))
  have hd' (i : Fin m) : 0 < d i := Real.sqrt_pos.mpr (neg_pos.mpr (hd i))
  have hs (i : Fin m) : d i*d i = -probePairing N (a i) (a i) := Real.mul_self_sqrt (neg_nonneg.mpr (hd i).le)
  have hden (i j : Fin m) : d i*d j = Real.sqrt (probePairing N (a i) (a i)*probePairing N (a j) (a j)) := by
    dsimp only [d]
    rw [←Real.sqrt_mul (neg_nonneg.mpr (hd i).le),neg_mul_neg]
  let D : Matrix (Fin m) (Fin m) ℂ := diagonal fun i => ((d i)⁻¹ : ℝ)
  let H := Dᴴ * probeGramMatrix N a * D
  have hD : IsUnit D := isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i =>
    isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (inv_ne_zero (hd' i).ne')))
  have hH := isHermitian_conjTranspose_mul_mul D (probeGramMatrix_isHermitian N a)
  have he (i j : Fin m) : H i j = (probeCorrelation a i j : ℂ) := by
    simp only [H,D,conjTranspose_diagonal,diagonal_mul,mul_diagonal,probeGramMatrix,Matrix.of_apply,
      Function.comp_apply,Pi.star_apply,Complex.star_def,Complex.conj_ofReal]
    rw [probeCorrelation,←hden,div_eq_mul_inv]
    push_cast
    ring
  have heq (i : Fin m) : probeCorrelation a i i = -1 := by
    rw [probeCorrelation,←hden,hs,div_neg,div_self (hd i).ne]
  have hsym (i j : Fin m) : probeCorrelation a i j = probeCorrelation a j i := by
    unfold probeCorrelation
    rw [probePairing_symm N (a i) (a j),mul_comm]
  have htr : H.trace.re = -(m:ℝ) := by
    simp only [Matrix.trace,Matrix.diag_apply,Complex.re_sum,he,heq,Complex.ofReal_re,sum_const,
      card_univ,Fintype.card_fin,nsmul_eq_mul,mul_neg_one]
  have hsum (i : Fin m) : ∑ j, (probeCorrelation a i j)^2 =
      1+∑ j ∈ univ.erase i, (probeCorrelation a i j)^2 := by
    rw [←add_sum_erase univ _ (mem_univ i),heq]
    norm_num
  have htr₂ : ((H^2).trace).re = m+distinctProbeEnergy a := by
    simp only [sq,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Complex.re_sum,he,←Complex.ofReal_mul,Complex.ofReal_re]
    calc _ = ∑ i, ∑ j, (probeCorrelation a i j)^2 := by
               apply sum_congr rfl
               intro i _
               exact sum_congr rfl fun j _ => by rw [hsym j i,sq]
         _ = _ := by simp only [hsum,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
                     mul_one,distinctProbeEnergy]
  have h := neg_trace_sq_le_negative_index_energy (H := H) hH (htr ▸ neg_nonpos.mpr (Nat.cast_nonneg _))
  rwa [htr,neg_sq,htr₂,show hermNegIndex H = _ from negIndex_conjugate _ hD] at h

private theorem index_le_right {m N : ℕ} (a : Fin m → (Fin N → ℤ)) :
    (hermNegIndex (probeGramMatrix N a) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  rw [rightZeros_encard_eq_sectionIndex]
  simp only [sectionMatrix_eq_atomGram]
  exact (show (hermNegIndex (probeGramMatrix N a) : ℕ∞) ≤ hermNegIndex (atomGram N) by
    exact_mod_cast hermNegIndex_probeGramMatrix_le N a).trans
      (le_iSup (fun K : ℕ => (hermNegIndex (atomGram K) : ℕ∞)) N)

/-- Finite right support forces pair correlation in every family of negative probes,
regardless of the signs of the mixed pairings or their conductors. -/
theorem finite_right_support_forces_probe_energy {r m N : ℕ}
    (hr : (rightZeros zetaZeroConfig).encard ≤ r) (a : Fin m → (Fin N → ℤ))
    (hd : ∀ i, probePairing N (a i) (a i) < 0) :
    (m:ℝ)*((m:ℝ)-r) ≤ r*distinctProbeEnergy a := by
  have hidx : hermNegIndex (probeGramMatrix N a) ≤ r := by exact_mod_cast (index_le_right a).trans hr
  have h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hidx : (hermNegIndex (probeGramMatrix N a) : ℝ) ≤ r)
    (add_nonneg (Nat.cast_nonneg m) (probe_energy_nn a))
  linarith only [h,probe_negative_index_energy a hd]

/-- The number of right zeros is detected by a single total mixed-square budget
on a disjoint family above any specified prime cutoff. -/
theorem rightZeros_ge_iff_distinct_probe_energy (r P : ℕ) :
    ((r+1 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard ↔
      ∃ (N : ℕ) (a : Fin (r+1) → (Fin N → ℤ)), P < N ∧
        (∀ i, isSignedPrimeSupported (a i)) ∧
        (∀ i (l : Fin N), a i l ≠ 0 → P < l.val+1) ∧
        (∀ i j, i ≠ j → Disjoint (activeConductors (a i)) (activeConductors (a j))) ∧
        (∀ i, probePairing N (a i) (a i) < 0) ∧ r*distinctProbeEnergy a < (r+1:ℝ) := by
  constructor
  · intro h
    let ε : ℝ := ((r:ℝ)+1)⁻¹
    have hε : 0 < ε := inv_pos.mpr (by positivity)
    have hε₁ : ε ≤ 1 := inv_le_one_of_one_le₀ (by dsimp [ε]; linarith only [Nat.cast_nonneg (R := ℝ) r])
    obtain ⟨N,a,hN,hs,hgt,hdis,hd,hrow⟩ :=
      (disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge (r+1) P hε hε₁).1.mp h
    refine ⟨N,a,hN,hs,hgt,hdis,hd,?_⟩
    have hnorm (i j) : |probeCorrelation a i j| =
        |probePairing N (a i) (a j)|/Real.sqrt (probePairing N (a i) (a i)*probePairing N (a j) (a j)) := by
      rw [probeCorrelation,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    have h₁ (i : Fin (r+1)) : ∑ j ∈ univ.erase i, |probeCorrelation a i j| < ε := by
      simpa only [hnorm] using hrow i
    have hs' (i : Fin (r+1)) : ∑ j ∈ univ.erase i, (probeCorrelation a i j)^2 ≤ ε := by
      apply le_trans (sum_le_sum fun j hj => ?_) (h₁ i).le
      have h := (single_le_sum (f := fun j => |probeCorrelation a i j|) (fun _ _ => abs_nonneg _) hj).trans (h₁ i).le
      rw [←sq_abs]
      simpa only [sq,mul_one] using mul_le_mul_of_nonneg_left (h.trans hε₁) (abs_nonneg (probeCorrelation a i j))
    have ht := sum_le_sum (s := univ) (fun i _ => hs' i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add_one] at ht
    change distinctProbeEnergy a ≤ ((r:ℝ)+1)*((r:ℝ)+1)⁻¹ at ht
    rw [mul_inv_cancel₀ (by positivity)] at ht
    linarith only [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (R := ℝ) r)]
  · rintro ⟨N,a,_,_,_,_,hd,he⟩
    by_contra! hn
    have hc : (rightZeros zetaZeroConfig).encard ≤ r := Order.le_of_lt_succ hn
    have h := finite_right_support_forces_probe_energy hc a hd
    push_cast at h
    linarith only [h,he]

#print axioms probe_negative_index_energy
#print axioms finite_right_support_forces_probe_energy
#print axioms rightZeros_ge_iff_distinct_probe_energy

end

end GaloisForLFunctions.CountingHolography.Sections
