import GaloisForLFunctions.SelbergClass.LocalFactors.PowerSumsDetectTheDeterminant
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCurveCameraIdentifiesAtTheGenus

/-!
# Rigidity and a stability bound at the Newton determinant threshold

A Newton coefficient is the mean of the signed lower-degree trace products.
The distance of those products from their mean is paid for by the deficit
in the squared exterior bound. At a saturated determinant every lower
degree saturates. The first trace then determines the complete multiset.
-/

noncomputable section
open Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.SelbergClass.LocalPowerSums

/-- Signed coefficient of the inverse local Euler factor. -/
def signedExterior (s : Multiset ℂ) (k : ℕ) := (-1 : ℂ)^k*s.esymm k

private theorem interior_sum (k : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k}, f a.1 a.2) =
      ∑ i ∈ (range k).erase 0, f i (k-i) := by
  apply sum_nbij' Prod.fst (fun i => (i,k-i))
  · rintro ⟨i,j⟩ h
    have ht := (mem_filter.mp h).2
    exact mem_erase.mpr ⟨ht.1.ne',mem_range.mpr ht.2⟩
  · intro i hi
    obtain ⟨h₀,hk⟩ := mem_erase.mp hi
    have h := mem_range.mp hk
    exact mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (by dsimp; omega),Nat.pos_of_ne_zero h₀,h⟩
  · rintro ⟨i,j⟩ h
    have he := Finset.mem_antidiagonal.mp (mem_filter.mp h).1
    exact Prod.ext rfl (by dsimp at he ⊢; omega)
  · exact fun _ _ => rfl
  · rintro ⟨i,j⟩ h
    have he := Finset.mem_antidiagonal.mp (mem_filter.mp h).1
    exact congrArg (f i) (by dsimp at he ⊢; omega)

/-- Newton's identity identifies the signed mean of the k lower trace products. -/
theorem newton_mean (s : Multiset ℂ) (k : ℕ) (hk : 0 < k) :
    (∑ i ∈ range k, signedExterior s i*tracePow s (k-i)) = (k : ℂ)*(-signedExterior s k) := by
  have h := multiset_newton_general s k hk
  rw [eq_sub_iff_add_eq] at h
  change tracePow s k + (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
    signedExterior s a.1*tracePow s a.2) = _ at h
  rw [interior_sum k (fun i j => signedExterior s i*tracePow s j)] at h
  rw [← sum_erase_add (range k) (fun i => signedExterior s i*tracePow s (k-i)) (mem_range.mpr hk)]
  have h₀ : signedExterior s 0=1 := by simp [signedExterior,Multiset.esymm]
  rw [h₀,Nat.sub_zero,one_mul,add_comm,h]
  unfold signedExterior
  rw [pow_succ]
  ring

private theorem mean_square {α : Type*} (S : Finset α) (z : α → ℂ) (u : ℂ)
    (h : (∑ i ∈ S,z i)=(S.card : ℂ)*u) :
    (∑ i ∈ S, normSq (z i-u)) = (∑ i ∈ S,normSq (z i))-(S.card : ℝ)*normSq u := by
  have hh : (∑ i ∈ S, (z i*conj u).re)=(S.card : ℝ)*normSq u := by
    rw [← re_sum,← sum_mul,h,mul_assoc,mul_conj]
    simp
  simp only [normSq_sub,sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,hh]
  ring

private theorem term_bound (s : Multiset ℂ) (B : NNReal) (k : ℕ)
    (h : ∀ j, 0 < j → j ≤ k → ‖tracePow s j‖ ≤ (B : ℝ)^j) {i : ℕ} (hi : i<k) :
    ‖signedExterior s i*tracePow s (k-i)‖ ≤ (B : ℝ)^k := by
  simp only [signedExterior,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  calc
    _ ≤ (B : ℝ)^i*(B : ℝ)^(k-i) :=
      mul_le_mul (exterior_bound s B i (fun j h₁ h₂ => h j h₁ (h₂.trans hi.le)))
        (h _ (by omega) (Nat.sub_le ..)) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add,Nat.add_sub_of_le hi.le]

/-- Squared errors of all Newton summands from their common extremal value
are bounded even away from equality. -/
theorem newton_variance (s : Multiset ℂ) (B : NNReal) (k : ℕ) (hk : 0<k)
    (h : ∀ j, 0 < j → j ≤ k → ‖tracePow s j‖ ≤ (B : ℝ)^j) :
    (∑ i ∈ range k, ‖signedExterior s i*tracePow s (k-i)+signedExterior s k‖^2) ≤
      (k : ℝ)*(((B : ℝ)^k)^2-‖s.esymm k‖^2) := by
  let z (i : ℕ) := signedExterior s i*tracePow s (k-i)
  have he := mean_square (range k) z (-signedExterior s k) (by simpa [z] using newton_mean s k hk)
  simp only [sub_neg_eq_add,normSq_eq_norm_sq,norm_neg,card_range] at he
  have hh : (∑ i ∈ range k, ‖z i‖^2) ≤ (k : ℝ)*((B : ℝ)^k)^2 := by
    calc
      _ ≤ ∑ _i ∈ range k, ((B : ℝ)^k)^2 := sum_le_sum fun i hi =>
        pow_le_pow_left₀ (norm_nonneg _) (term_bound s B k h (mem_range.mp hi)) _
      _ = _ := by simp
  have hn : ‖signedExterior s k‖=‖s.esymm k‖ := by simp [signedExterior,norm_mul]
  rw [hn] at he
  change (∑ i ∈ range k, ‖z i+signedExterior s k‖^2) ≤ _
  linarith only [he,hh]

/-- At saturation each single Newton product has the same complex phase and magnitude. -/
theorem saturated_terms (s : Multiset ℂ) (B : NNReal) (k : ℕ) (hk : 0<k)
    (h : ∀ j, 0 < j → j ≤ k → ‖tracePow s j‖ ≤ (B : ℝ)^j)
    (he : ‖s.esymm k‖=(B : ℝ)^k) (i : ℕ) (hi : i<k) :
    signedExterior s i*tracePow s (k-i) = -signedExterior s k := by
  have hh := newton_variance s B k hk h
  rw [he,sub_self,mul_zero] at hh
  have hb := single_le_sum (fun (j : ℕ) (_ : j ∈ range k) =>
    sq_nonneg ‖signedExterior s j*tracePow s (k-j)+signedExterior s k‖) (mem_range.mpr hi)
  have hz : ‖signedExterior s i*tracePow s (k-i)+signedExterior s k‖=0 :=
    by nlinarith only [hb.trans hh]
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp hz)

/-- Saturation at one positive degree forces every earlier exterior bound to saturate. -/
theorem saturation_descends (s : Multiset ℂ) (B : NNReal) (k : ℕ) (hk : 0<k)
    (h : ∀ j, 0 < j → j ≤ k → ‖tracePow s j‖ ≤ (B : ℝ)^j)
    (he : ‖s.esymm k‖=(B : ℝ)^k) (i : ℕ) (hi : i≤k) :
    ‖s.esymm i‖=(B : ℝ)^i := by
  have hU := exterior_bound s B i fun j h₁ h₂ => h j h₁ (h₂.trans hi)
  rcases eq_or_lt_of_le hi with rfl | hlt
  · exact he
  by_cases hB : (B : ℝ)=0
  · cases i with
    | zero => simp [Multiset.esymm]
    | succ i => rw [hB,zero_pow (Nat.succ_ne_zero _)] at hU ⊢; exact le_antisymm hU (norm_nonneg _)
  have hc := congrArg norm (saturated_terms s B k hk h he i hlt)
  simp only [signedExterior,norm_mul,norm_neg,norm_pow,norm_one,one_pow,one_mul,he] at hc
  have hp := h (k-i) (by omega) (Nat.sub_le ..)
  have hb := mul_le_mul_of_nonneg_left hp (norm_nonneg (s.esymm i))
  have hpow : (B : ℝ)^k=(B : ℝ)^i*(B : ℝ)^(k-i) := by rw [← pow_add,Nat.add_sub_of_le hi]
  rw [hc] at hb
  conv_lhs at hb => rw [hpow]
  exact le_antisymm hU (le_of_mul_le_mul_right hb (pow_pos (lt_of_le_of_ne B.property hB.symm) _))

/-- For an extremal nonempty spectrum all first r moments form one signed geometric
progression. Its single parameter is the negative of the first trace. -/
theorem extremal_moments (s : Multiset ℂ) (B : NNReal) (r : ℕ) (hr : 0<r)
    (h : ∀ j, 0 < j → j ≤ r → ‖tracePow s j‖ ≤ (B : ℝ)^j)
    (he : ‖s.esymm r‖=(B : ℝ)^r) :
    ∀ j, 0 < j → j ≤ r → tracePow s j = -(-tracePow s 1)^j := by
  have atDegree (k : ℕ) (hk : 0<k) (hkr : k≤r) (i : ℕ) (hi : i<k) :=
    saturated_terms s B k hk (fun j hj hjk => h j hj (hjk.trans hkr))
      (saturation_descends s B r hr h he k hkr) i hi
  have hc₀ : signedExterior s 0=1 := by simp [signedExterior,Multiset.esymm]
  have first := atDegree 1 one_pos hr 0 one_pos
  rw [hc₀,one_mul,Nat.sub_zero] at first
  intro j
  induction j with
  | zero => omega
  | succ j ih =>
    intro _ hjr
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have h₀ := atDegree (j+1) (Nat.succ_pos _) hjr 0 (Nat.succ_pos _)
      have h₁ := atDegree (j+1) (Nat.succ_pos _) hjr 1 (by omega)
      rw [hc₀,one_mul,Nat.sub_zero] at h₀
      rw [Nat.add_sub_cancel,show signedExterior s 1= -tracePow s 1 from by rw [first,neg_neg],
        ih hj (by omega)] at h₁
      rw [h₀,← h₁,pow_succ]
      ring

/-- At the extremal determinant, a single trace identifies the full unordered
spectrum in each rank. The radii may be specified independently. -/
theorem first_trace_identifies_extremizers (s t : Multiset ℂ) (B C : NNReal)
    (hr : 0<s.card) (hcard : s.card=t.card)
    (hs : ∀ j, 0<j → j≤s.card → ‖tracePow s j‖ ≤ (B : ℝ)^j)
    (ht : ∀ j, 0<j → j≤t.card → ‖tracePow t j‖ ≤ (C : ℝ)^j)
    (hds : ‖s.prod‖=(B : ℝ)^s.card) (hdt : ‖t.prod‖=(C : ℝ)^t.card) :
    s=t ↔ tracePow s 1=tracePow t 1 := by
  refine ⟨fun h => h ▸ rfl,fun h => ?_⟩
  apply multiset_eq_of_esymm_eq hcard
  apply (ZeroConfigurationGeometry.powerSum_eq_iff_esymm_eq s t s.card).1
  intro j hj hk
  have hs' := extremal_moments s B s.card hr hs (by rwa [multiset_esymm_card_eq_prod]) j hj hk
  have ht' := extremal_moments t C t.card (hcard ▸ hr) ht
    (by rwa [multiset_esymm_card_eq_prod]) j hj (hcard ▸ hk)
  exact hs'.trans ((congrArg (fun a : ℂ => -(-a)^j) h).trans ht'.symm)

end GaloisForLFunctions.SelbergClass.LocalPowerSums

#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.newton_mean
#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.newton_variance
#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.saturated_terms
#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.saturation_descends
#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.extremal_moments
#print axioms GaloisForLFunctions.SelbergClass.LocalPowerSums.first_trace_identifies_extremizers
