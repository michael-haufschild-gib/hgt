import GaloisForLFunctions.HTGeometry.Quantum.SharpCopyThresholdForThreeChargeLevels
import GaloisForLFunctions.HTGeometry.Quantum.IntegerEdgeCostsForJointChargeObservation
import Mathlib.RingTheory.Int.Basic

/-!
# Sharp detection thresholds for two coprime charge gaps

In the three-level density matrix with no direct edge between the last
two levels, assign the occupied edges coprime charges a,b. The visible
frequencies are precisely a·t at cost (a+b)|t|. In particular consecutive
gaps attain the universal finite copy bound, although every matrix in the
phase family has the same spectrum.
-/

noncomputable section
open Finset Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels

def twoCharges (a b : ℕ) (i : Fin 3) : ℤ := a*smallLabel i+b*phaseLabel i

private theorem gap_relation (a b : ℕ) (hab : a.Coprime b) (s d : ℤ)
    (h : (a : ℤ)*s+b*d=0) : ∃ t : ℤ, d=a*t ∧ s= -(b : ℤ)*t := by
  obtain ⟨u,v,he⟩ := (Int.isCoprime_iff_nat_coprime (a:=(a : ℤ)) (b:=(b : ℤ))).2 hab
  refine ⟨u*d-v*s,?_,?_⟩
  · linear_combination -d*he+v*h
  · linear_combination -s*he+u*h

private theorem cost_lower (a b n : ℕ) (hab : a.Coprime b) (d : ℤ)
    (h : d∈frequencies (twoCharges a b) phaseLabel base n) :
    ∃ t : ℤ, d=a*t ∧ (a+b)*t.natAbs≤n := by
  obtain ⟨u,v,hu,hq,rfl⟩ := (balanced_word _ _ _ _ _).2 h
  let s := displacement smallLabel u v
  let d := displacement phaseLabel u v
  have he : (a : ℤ)*s+b*d=0 := by
    simpa only [s,d,displacement,twoCharges,show ∀ i j : Fin 3,
      (a : ℤ)*smallLabel i+b*phaseLabel i-(a*smallLabel j+b*phaseLabel j)=
        a*(smallLabel i-smallLabel j)+b*(phaseLabel i-phaseLabel j) from fun _ _ => by ring,
      sum_add_distrib,← mul_sum] using hq
  obtain ⟨t,hd,hs⟩ := gap_relation _ _ hab s d he
  have hc : |s|+|d|≤(n : ℤ) := by
    refine (add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _)).trans ?_
    rw [← sum_add_distrib]
    exact (sum_le_sum fun k _ => edge_cost _ _ (hu k)).trans_eq (by simp)
  have hc' : ((a : ℤ)+b)*|t|≤(n : ℤ) := by
    rw [hs,hd,abs_mul,abs_mul,abs_neg,abs_of_nonneg (Int.natCast_nonneg a),
      abs_of_nonneg (Int.natCast_nonneg b)] at hc
    linarith only [hc]
  refine ⟨t,hd,?_⟩
  exact_mod_cast (show ((a+b : ℕ) : ℤ)*(t.natAbs : ℤ)≤(n : ℤ) by simpa using hc')

private theorem base_hermitian : base.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [base,conjTranspose_apply]

private theorem cost_attained (a b : ℕ) (t : ℤ) :
    (a : ℤ)*t∈frequencies (twoCharges a b) phaseLabel base ((a+b)*t.natAbs) := by
  let e : Edge base := ⟨(1,0),by norm_num [base]⟩
  let f : Edge base := ⟨(2,0),by norm_num [base]⟩
  have qe : edgeGap (twoCharges a b) e=a := by simp [e,edgeGap,twoCharges,smallLabel,phaseLabel]
  have qf : edgeGap (twoCharges a b) f=b := by simp [f,edgeGap,twoCharges,smallLabel,phaseLabel]
  have be : edgeGap phaseLabel e=0 := by simp [e,edgeGap,phaseLabel]
  have bf : edgeGap phaseLabel f=1 := by simp [f,edgeGap,phaseLabel]
  have h := pair_frequency (twoCharges a b) phaseLabel base_hermitian e f (-(b : ℤ)*t) ((a : ℤ)*t)
    (by rw [qe,qf]; ring)
  simpa only [be,bf,mul_zero,mul_one,zero_add,Int.natAbs_mul,Int.natAbs_neg,Int.natAbs_natCast,
    ← Nat.add_mul,Nat.add_comm b a] using h

/-- Exact spectrum for every number of copies, including opposite
orientations, unused copies and the zero frequency. -/
theorem coprime_spectrum (a b n : ℕ) (hab : a.Coprime b) (d : ℤ) :
    d∈frequencies (twoCharges a b) phaseLabel base n ↔
      ∃ t : ℤ, d=a*t ∧ (a+b)*t.natAbs≤n := by
  refine ⟨cost_lower a b n hab d,?_⟩
  rintro ⟨t,rfl,ht⟩
  have hm : Monotone (frequencies (twoCharges a b) phaseLabel base) :=
    monotone_nat_of_le_succ fun k => frequencies_mono _ _ _ 0 (by norm_num [base]) k
  exact hm ht (cost_attained a b t)

/-- Below the threshold the entire phase circle is invisible. At and
above the threshold exactly the a-th root ambiguity survives. -/
theorem coprime_observations (a b n : ℕ) (hab : a.Coprime b) (z w : Circle) :
    observe (twoCharges a b) (state z) n=observe (twoCharges a b) (state w) n ↔
      n<a+b ∨ z^(a : ℤ)=w^(a : ℤ) := by
  rw [state,state,indistinguishable_iff]
  constructor
  · intro h
    by_cases hn : n<a+b
    · exact Or.inl hn
    · exact Or.inr (h _ ((coprime_spectrum a b n hab _).2 ⟨1,by rw [mul_one],by simpa using le_of_not_gt hn⟩))
  · intro h d hd
    obtain ⟨t,rfl,ht⟩ := (coprime_spectrum a b n hab d).1 hd
    rcases h with hn | he
    · have hz : t=0 := by
        by_contra hne
        have hp := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
        have hc := Nat.mul_le_mul_left (a+b) hp
        omega
      rw [hz,mul_zero,_root_.zpow_zero,_root_.zpow_zero]
    · rw [_root_.zpow_mul,_root_.zpow_mul,he]

/-- Consecutive gaps r+1,r+2 first detect the (r+1)-st power at exactly
2r+3 copies. This attains the bound 2Q−1 at every Q≥2. -/
theorem consecutive_threshold (r n : ℕ) (z w : Circle) :
    observe (twoCharges (r+1) (r+2)) (state z) n=observe (twoCharges (r+1) (r+2)) (state w) n ↔
      n<2*r+3 ∨ z^((r+1 : ℕ) : ℤ)=w^((r+1 : ℕ) : ℤ) := by
  have h : (r+1).Coprime (r+2) := by simp
  simpa only [show r+1+(r+2)=2*r+3 by omega] using coprime_observations (r+1) (r+2) n h z w

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.coprime_spectrum
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.coprime_observations
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.consecutive_threshold
