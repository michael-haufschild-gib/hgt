import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.LabelledArrangementRecovery
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Log

/-!
# Rigidity of optimal labelled point counts

Equality in the information bound forces a complete interval of distinct subset
sums. Binary place values then determine every coordinate alphabet.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- A lossless subset-sum code exhausts its information-theoretic range
exactly when its weights, up to permutation, are consecutive binary places. -/
theorem completeWeights_rigid (w : ι → ℕ)
    (E : Finset ι ≃ Fin (2^Fintype.card ι))
    (hE : ∀ S, (E S).val = ∑ i ∈ S, w i) :
    ∃ e : ι ≃ Fin (Fintype.card ι), ∀ i, w i = 2^(e i).val := by
  let M := 2^Fintype.card ι
  have hs (i : ι) : (E {i}).val = w i := by simp [hE]
  have hw (i : ι) : 0 < w i := by
    by_contra! h
    have he : E {i} = E ∅ := Fin.ext (by simp [hs,hE,Nat.eq_zero_of_le_zero h])
    simpa using E.injective he
  have hi : Function.Injective w := by
    intro i j he
    have hh : E {i} = E {j} := Fin.ext (by simpa only [hs] using he)
    simpa using E.injective hh
  have hprod (z : ℂ) : (∏ i, (1+z^(w i))) = ∑ k ∈ range M, z^k := by
    rw [prod_one_add,powerset_univ,← Fin.sum_univ_eq_sum_range]
    simp only [prod_pow_eq_pow_sum]
    exact Fintype.sum_equiv E _ _ fun S => by rw [hE]
  have hpow (i : ι) : ∃ j < Fintype.card ι, w i = 2^j := by
    let z := Complex.exp (2*Real.pi*Complex.I/(2*w i:ℕ))
    have hz : IsPrimitiveRoot z (2*w i) :=
      Complex.isPrimitiveRoot_exp _ (by have := hw i; omega)
    have hsq : (z^(w i))^2 = 1 := by rw [← pow_mul,Nat.mul_comm,hz.pow_eq_one]
    have hn : z^(w i) ≠ 1 := by
      intro h
      have hh := Nat.le_of_dvd (hw i) ((hz.pow_eq_one_iff_dvd _).mp h)
      omega
    have hminus := (sq_eq_one_iff.mp hsq).resolve_left hn
    have hzsum : (∑ k ∈ range M, z^k) = 0 := by
      rw [← hprod]
      exact prod_eq_zero (mem_univ i) (by rw [hminus]; ring)
    have hh := geom_sum_mul z M
    rw [hzsum,zero_mul] at hh
    have hd := (hz.pow_eq_one_iff_dvd M).mp (sub_eq_zero.mp hh.symm)
    obtain ⟨j,hj,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (dvd_trans (dvd_mul_left (w i) 2) hd)
    have hb := (E {i}).isLt
    rw [hs,he] at hb
    exact ⟨j,(Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hb,he⟩
  let f (i : ι) : Fin (Fintype.card ι) := ⟨(hpow i).choose,(hpow i).choose_spec.1⟩
  have hf (i : ι) : w i = 2^(f i).val := (hpow i).choose_spec.2
  have hinj : Function.Injective f := by
    intro i j he
    apply hi
    rw [hf i,hf j,he]
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,by simp⟩),hf⟩

/-- Size of the fiber for one prescribed marked-coordinate pattern. -/
def faceWeight {A : ι → Type*} [∀ i, Fintype (A i)] (D : ∀ i, Finset (A i))
    (S : Finset ι) := ∏ i, if i ∈ S then (D i).card else Fintype.card (A i)-(D i).card

/-- In an optimal arrangement experiment every face has a different binary
place as its fiber size. This applies to arbitrary distinguished subsets. -/
theorem optimalArrangement_strata {A : ι → Type*} [∀ i, Fintype (A i)] (D : ∀ i, Finset (A i))
    (hi : Function.Injective (fun K => (arrangementWords D K).card))
    (hc : Fintype.card (∀ i, A i)+1 = 2^(2^Fintype.card ι)) :
    ∃ e : Finset ι ≃ Fin (2^Fintype.card ι), ∀ S, faceWeight D S = 2^(e S).val := by
  let f (K : Finset (Finset ι)) : Fin (2^(Fintype.card (Finset ι))) :=
    ⟨(arrangementWords D K).card,by rw [Fintype.card_finset,← hc]; exact
      Nat.lt_succ_of_le (arrangementWords D K).card_le_univ⟩
  let E := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨fun _ _ h => hi (congrArg Fin.val h),by simp⟩)
  have h := completeWeights_rigid (faceWeight D) E (fun K => card_arrangementWords D K)
  simpa only [Fintype.card_finset] using h

/-- Changing which side of a coordinate split is called distinguished is an
involution on the labelled face lattice. -/
private def switchFace (s : Finset ι) : Finset ι ≃ Finset ι where
  toFun t := (s \ t) ∪ (t \ s)
  invFun t := (s \ t) ∪ (t \ s)
  left_inv t := by ext i; simp only [mem_union,mem_sdiff]; tauto
  right_inv t := by ext i; simp only [mem_union,mem_sdiff]; tauto

private theorem faceWeight_switch {A : ι → Type*} [∀ i, Fintype (A i)]
    (D : ∀ i, Finset (A i)) (s : Finset ι) (hs : faceWeight D s = 1) (T : Finset ι) :
    faceWeight D (switchFace s T) = ∏ i ∈ T, (Fintype.card (A i)-1) := by
  have h := Finset.prod_eq_one_iff.mp hs
  have he (i : ι) : (if i ∈ switchFace s T then (D i).card else Fintype.card (A i)-(D i).card) =
      if i ∈ T then Fintype.card (A i)-1 else 1 := by
    have hb := h i (mem_univ i)
    have hc := (D i).card_le_univ
    by_cases his : i ∈ s <;> by_cases hit : i ∈ T <;>
      simp [switchFace,his,hit] at hb ⊢ <;> omega
  simp only [faceWeight,he,prod_ite,prod_const_one,mul_one]
  congr 1
  ext i
  simp

/-- For any optimal marked alphabets each coordinate split has a singleton side;
the full alphabet sizes must be the first Fermat numbers, up to permutation. -/
theorem optimalArrangement_alphabets {A : ι → Type*} [∀ i, Fintype (A i)] (D : ∀ i, Finset (A i))
    (hi : Function.Injective (fun K => (arrangementWords D K).card))
    (hc : Fintype.card (∀ i, A i)+1 = 2^(2^Fintype.card ι)) :
    (∀ i, (D i).card = 1 ∨ ((D i)ᶜ).card = 1) ∧
    ∃ e : ι ≃ Fin (Fintype.card ι), ∀ i, Fintype.card (A i) = 2^(2^(e i).val)+1 := by
  obtain ⟨E,hE⟩ := optimalArrangement_strata D hi hc
  let s := E.symm ⟨0,by positivity⟩
  have hs : faceWeight D s = 1 := by rw [hE]; simp [s]
  constructor
  · intro i
    have hb := Finset.prod_eq_one_iff.mp hs i (mem_univ i)
    by_cases his : i ∈ s
    · exact Or.inl (by simpa [his] using hb)
    · exact Or.inr (by simpa [his,card_compl] using hb)
  · let F := (switchFace s).trans E
    have hf (T : Finset ι) :
        (∏ i ∈ T, (Fintype.card (A i)-1)) = 2^(F T).val :=
      (faceWeight_switch D s hs T).symm.trans (hE _)
    let u (i : ι) := (F {i}).val
    have hu (i : ι) : Fintype.card (A i)-1 = 2^(u i) := by simpa only [prod_singleton] using hf {i}
    have he (T : Finset ι) : (F T).val = ∑ i ∈ T, u i := by
      have h := hf T
      simp_rw [hu,prod_pow_eq_pow_sum] at h
      exact (pow_right_strictMono₀ Nat.one_lt_two).injective h.symm
    obtain ⟨e,hh⟩ := completeWeights_rigid u F he
    refine ⟨e,fun i => ?_⟩
    have hb := hu i
    rw [hh i] at hb
    have hp : 0 < 2^(2^(e i).val) := by positivity
    omega

/-- Necessary and sufficient conditions for one marked-alphabet experiment to
decode all face families with the smallest possible number of words. Flipping
the distinguished side at any coordinate and permuting coordinates are the
only freedoms in the optimum. -/
theorem optimalArrangement_iff {A : ι → Type*} [∀ i, Fintype (A i)] (D : ∀ i, Finset (A i)) :
    (Function.Injective (fun K => (arrangementWords D K).card) ∧
      Fintype.card (∀ i, A i)+1 = 2^(2^Fintype.card ι)) ↔
      (∀ i, (D i).card=1 ∨ ((D i)ᶜ).card=1) ∧
      ∃ e : ι ≃ Fin (Fintype.card ι), ∀ i, Fintype.card (A i) = 2^(2^(e i).val)+1 := by
  refine ⟨fun ⟨hi,hc⟩ => optimalArrangement_alphabets D hi hc,?_⟩
  rintro ⟨hsides,e,hcard⟩
  let s := univ.filter fun i => (D i).card=1
  have hs : faceWeight D s = 1 := by
    apply prod_eq_one
    intro i _
    rcases hsides i with h | h
    · simp [s,h]
    · by_cases hi : (D i).card=1
      · simp [s,hi]
      · simpa [s,hi,card_compl] using h
  let f := e.toEmbedding.trans Fin.valEmbedding
  let u (T : Finset ι) := faceIndex f Tᶜ
  have hu : Function.Injective u := (faceIndex_injective f).comp compl_injective
  have hw (T : Finset ι) : faceWeight D (switchFace s T) = 2^(u T) := by
    rw [faceWeight_switch D s hs]
    simp only [hcard,Nat.add_sub_cancel,prod_pow_eq_pow_sum,u,faceIndex,compl_compl,sum_map]
    rfl
  let v (T : Finset ι) := u ((switchFace s).symm T)
  have hv : Function.Injective v := hu.comp (switchFace s).symm.injective
  have hg (K : Finset (Finset ι)) : (arrangementWords D K).card = ∑ k ∈ K.image v, 2^k := by
    rw [card_arrangementWords,sum_image hv.injOn]
    refine sum_congr rfl fun T _ => ?_
    simpa only [Equiv.apply_symm_apply,v] using hw ((switchFace s).symm T)
  constructor
  · intro K L h
    simp only [hg] at h
    have hh := congrArg (fun n : ℕ => n.bitIndices.toFinset) h
    simp only [toFinset_bitIndices_sum_two_pow] at hh
    exact (Finset.image_injective hv) hh
  · let n := Fintype.card ι
    calc
      Fintype.card (∀ i, A i)+1 = (∏ i, (2^(2^(e i).val)+1))+1 := by
        rw [Fintype.card_pi]; simp_rw [hcard]
      _ = (∏ i : Fin n, (2^(2^i.val)+1))+1 :=
        congrArg (·+1) (Fintype.prod_equiv e _ _ fun _ => rfl)
      _ = _ := by
        have h := labelledWordSpace_optimal n
        rw [Fintype.card_pi] at h
        exact h

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
