/-
Divisor allocations adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.ExceptionalProfilesAndHeckeSlots

/-!
# Divisor allocations

Divisor allocations and Hecke row weights; formal reduction factors and live and frozen
indices of raw divisors; retained profiles, row rectangles and volume control.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask
local notation "O" => Eisenstein.O

def rowWeight (η : Character) (m A z : O) (t : ℝ) : Ideal O →*₀ ℂ where
  toFun I := (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)
  map_one' := by simp only [map_one,Nat.cast_one,Complex.one_cpow,one_mul]
  map_zero' := by simp only [map_zero,zero_mul,mul_zero]
  map_mul' I J := by
    have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t) =
        (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm I) : (0:ℝ) ≤ Ideal.absNorm I)
        (Nat.cast_nonneg (Ideal.absNorm J) : (0:ℝ) ≤ Ideal.absNorm J) (Complex.I*t)
    simp only [map_mul,Nat.cast_mul,hpow]
    ring

theorem rowTwistedSum_eq_weight (η : Character) (m A z : O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
    (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem live_slot_product (η : Character) (m A z : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (t : ℝ) :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem common_extracted_slot_rectangle (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      rowWeight η m A z t (B₁*B₂)*
        ∑ v : (i : ι) → S i, (∏ i,β i (v i))*
          ∑' I : Ideal O, ∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
              idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
                (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) =
      rowWeight η m A z t (B₁*B₂)*
        (rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
            (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J) := by
    rw [CenteredMomentExtraction.idealRectangle_extract]
    simp only [map_mul]
    ring
  simp_rw [ht,tsum_mul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end CenteredMomentHeckeExpansion

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorAllocation
open  UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def nonemptySelections (s : Finset ι) : Finset (Finset ι) := s.powerset.erase ∅

omit [DecidableEq ι] in
theorem prime_complement (P : Ideal O) (hP : Prime P) (s : Finset ι) (v : ι → Ideal O) :
    (∏ i ∈ s, (1-(if P ∣ v i then (1:ℂ) else 0))) =
      if P ∣ ∏ i ∈ s,v i then 0 else 1 := by
  by_cases h : P ∣ ∏ i ∈ s,v i
  · rw [if_pos h]
    obtain ⟨i,hi,hd⟩ := (hP.dvd_finsetProd_iff v).mp h
    exact Finset.prod_eq_zero hi (by simp only [if_pos hd,sub_self])
  · rw [if_neg h]
    apply Finset.prod_eq_one
    intro i hi
    have hd : ¬P∣v i := fun hh => h ((hP.dvd_finsetProd_iff v).mpr ⟨i,hi,hh⟩)
    simp only [if_neg hd,sub_zero]

theorem prime_factor_allocation (P : Ideal O) (hP : Prime P)
    (s : Finset ι) (v : ι → Ideal O) :
    (if P ∣ ∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
        ∏ i ∈ J, if P ∣ v i then (1:ℂ) else 0 := by
  let f := fun J : Finset ι => (-1:ℂ)^J.card*∏ i ∈ J,if P∣v i then (1:ℂ) else 0
  have he : (∑ J ∈ nonemptySelections s,f J)+1 =
      if P ∣ ∏ i ∈ s,v i then (0:ℂ) else 1 := by
    have hr := Finset.sum_erase_add s.powerset f (Finset.mem_powerset.mpr (Finset.empty_subset s))
    have hh := Finset.prod_sub (fun _i : ι => (1:ℂ))
      (fun i => if P∣v i then (1:ℂ) else 0) s
    simp only [Finset.prod_const_one,mul_one] at hh
    rw [prime_complement P hP s v] at hh
    simpa only [nonemptySelections,f,Finset.card_empty,pow_zero,Finset.prod_empty,one_mul] using hr.trans hh.symm
  have hn : (∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
      ∏ i ∈ J,if P∣v i then (1:ℂ) else 0) = -(∑ J ∈ nonemptySelections s,f J) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f]
    rw [pow_succ]
    ring
  rw [hn]
  by_cases h : P∣∏ i ∈ s,v i <;> simp only [h,ite_true,ite_false] at he ⊢ <;>
    linear_combination he

theorem squarefree_dvd_iff (D I : Ideal O) (hD : Squarefree D) :
    D∣I ↔ ∀ P ∈ primeSupport D,P∣I := by
  constructor
  · intro hd P hP
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hd
  · intro h
    rw [← squarefree_support_product_self hD]
    apply Finset.prod_dvd_of_coprime ?_ h
    intro P hP Q hQ hne
    let : P.IsMaximal := (Ideal.isPrime_of_prime (support_prime hP)).isMaximal (support_prime hP).ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime (support_prime hQ)).isMaximal (support_prime hQ).ne_zero
    exact Ideal.isCoprime_of_isMaximal hne

abbrev Allocation (D : Ideal O) (s : Finset ι) :=
  (P : primeSupport D) → nonemptySelections s

def allocationTerm (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)*
    ∏ i ∈ (a P).val, if (P:Ideal O)∣v i then (1:ℂ) else 0

theorem squarefree_mask_allocation (D : Ideal O) (hD : Squarefree D)
    (s : Finset ι) (v : ι → Ideal O) :
    (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ a : Allocation D s, allocationTerm D s v a := by
  have hprod : (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∏ P : primeSupport D, if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0 := by
    by_cases hd : D∣∏ i ∈ s,v i
    · rw [if_pos hd]
      symm
      apply Finset.prod_eq_one
      intro P hP
      rw [if_pos ((squarefree_dvd_iff _ _ hD).mp hd P P.property)]
    · rw [if_neg hd]
      obtain ⟨P,hP,hnd⟩ := not_forall.mp (fun h => hd ((squarefree_dvd_iff _ _ hD).mpr h))
        |> fun h => by simpa only [not_forall,_root_.not_imp] using h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨P,hP⟩ : primeSupport D)) (by simp only [if_neg hnd])
  rw [hprod]
  have hl (P : primeSupport D) :
      (if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J : nonemptySelections s, (-1:ℂ)^(J.val.card+1)*
        ∏ i ∈ J.val, if (P:Ideal O)∣v i then (1:ℂ) else 0 := by
    rw [prime_factor_allocation P (support_prime P.property) s v]
    exact (Finset.sum_coe_sort (nonemptySelections s) (fun J =>
      (-1:ℂ)^(J.card+1)*∏ i ∈ J,if (P:Ideal O)∣v i then (1:ℂ) else 0)).symm
  simp_rw [hl]
  exact Fintype.prod_sum _

theorem allocationTerm_norm_le_one (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ‖allocationTerm D s v a‖ ≤ 1 := by
  unfold allocationTerm
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro P hP
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i hi
  split_ifs <;> norm_num

theorem allocation_card_bound (D : Ideal O) (s : Finset ι) :
    Fintype.card (Allocation D s) ≤ (2^(primeSupport D).card)^s.card := by
  have hc : (nonemptySelections s).card ≤ 2^s.card := by
    simpa only [nonemptySelections,Finset.card_powerset] using
      (Finset.card_erase_le (s := s.powerset) (a := (∅:Finset ι)))
  change Fintype.card (primeSupport D → nonemptySelections s) ≤ _
  simp only [Fintype.card_fun,Fintype.card_coe]
  calc
    _ ≤ (2^s.card)^(primeSupport D).card := Nat.pow_le_pow_left hc _
    _ = _ := by simp only [← pow_mul,Nat.mul_comm]

theorem allocation_mass_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      ∀ v : ι → Ideal O, (∑ a : Allocation D s, ‖allocationTerm D s v a‖) ≤
        C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := CompletedGauss.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C ^ N,pow_pos hC _,?_⟩
  intro D hD s hs v
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ∑ _a : Allocation D s,(1:ℝ) := Finset.sum_le_sum (fun a _ => allocationTerm_norm_le_one D s v a)
    _ = (Fintype.card (Allocation D s):ℝ) := by simp
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C ^ N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

end CenteredMomentDivisorAllocation

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorExtraction
open  CenteredMomentDivisorAllocation
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def selectedPrimes (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)

def selectedDivisor (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal O)

theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [if_neg h])

theorem selectedDivisor_ne_zero (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)

theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

theorem exists_factor_quotients (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) :
    ∃ q : ι → Ideal O, ∀ i, v i=selectedDivisor D s a i*q i := by
  choose q hq using (fun i => selectedDivisor_dvd D s v a hn i)
  exact ⟨q,hq⟩

theorem selected_prime_slot (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) (hv : Prime (v i)) :
    v i=(P:Ideal O) :=
  ((prime_dvd_prime_iff_eq (support_prime P.property) hv).mp
    (selected_divides_factor D s v a hn P i hi)).symm

theorem double_selected_prime_slot_zero (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (P Q : primeSupport D) (hPQ : P ≠ Q)
    (i : ι) (hPi : i ∈ (a P).val) (hQi : i ∈ (a Q).val) (hv : Prime (v i)) :
    allocationTerm D s v a=0 := by
  by_contra hn
  apply hPQ
  apply Subtype.ext
  exact (selected_prime_slot D s v a hn P i hPi hv).symm.trans
    (selected_prime_slot D s v a hn Q i hQi hv)

end CenteredMomentDivisorExtraction

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorTensor
open  CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def allocationSign (D : Ideal O) (s : Finset ι) (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)

theorem allocationSign_norm (D : Ideal O) (s : Finset ι) (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  simp only [allocationSign,norm_prod,norm_pow,norm_neg,norm_one,one_pow,Finset.prod_const_one]

theorem allocationTerm_eq_ite (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [if_pos hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [if_pos (hPi.trans (hh i his))]
    rw [he,mul_one]
  · rw [if_neg hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [if_pos hh,Finset.prod_eq_one (fun i hi => by rw [if_pos (hh i hi)]),mul_one]
  · rw [if_neg hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [if_neg hnd]),mul_zero]

theorem selected_plain_sum (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (hD : D ≠ 0) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : Ideal O, if D∣I then rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) else 0) =
      rowWeight η m A z t D*rowTwistedSum η m A z W t (X/Ideal.absNorm D) := by
  rw [tsum_ideal_divisible D hD, rowTwistedSum_eq_weight,← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [map_mul]
  have he : (Ideal.absNorm (D*I):ℝ)/X = (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm D:ℝ)) := by
    simp only [map_mul,Nat.cast_mul,div_div_eq_mul_div]
    ring
  rw [he]
  ring

theorem selected_plain_scales (D₁ D₂ : Ideal O) (X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/Ideal.absNorm D₁)*(X₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) ∧
    (Y₁/Ideal.absNorm D₁)*(Y₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) :=
  CenteredMomentExtraction.extracted_product_scale X₁ X₂ Y₁ Y₂ T D₁ D₂ hX hY

end CenteredMomentDivisorTensor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorSlots
open  CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_slot_exact (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [if_neg hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem selectedDivisor_empty (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

theorem allocated_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : ∀ I ∈ S, ‖β I‖ ≤ M)
    (hN : ∀ I ∈ S, β I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ H) :
    ‖rowSlot η m A z S (fun I => if selectedDivisor D s a i∣I then β I else 0) t‖ ≤
      if (selectedPrimes D s a i).Nonempty then M else 128*M*H := by
  by_cases hn : (selectedPrimes D s a i).Nonempty
  · rw [if_pos hn]
    obtain ⟨P,hP⟩ := hn
    exact selected_slot_bound η m A z t (selectedDivisor D s a i) P (support_prime P.property)
      (Finset.dvd_prod_of_mem _ hP) S hS β M hM hβ
  · rw [if_neg hn]
    have he := selectedDivisor_empty D s a i (Finset.not_nonempty_iff_eq_empty.mp hn)
    simp only [he,one_dvd,ite_true]
    exact rowSlot_bound η m A z S β t H M hH hM hβ hN

end CenteredMomentDivisorSlots

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorBoundary
open  CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def frozenSlots (D : Ideal O) (s slots : Finset ι) (a : Allocation D s) : Finset ι :=
  slots.filter (fun i => (selectedPrimes D s a i).Nonempty)

def extractedProduct (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) : Ideal O :=
  (∏ i ∈ plain,selectedDivisor D s a i)*(∏ i ∈ frozenSlots D s slots a,v i)

theorem divisor_dvd_extractedProduct (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0) :
    D∣extractedProduct D s plain slots a v := by
  apply (squarefree_dvd_iff _ _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  have hne : (a PP).val.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp (a PP).property).1
  obtain ⟨i,hi⟩ := hne
  have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a PP).property)) hi
  have hip : PP ∈ selectedPrimes D s a i := Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  rcases Finset.mem_union.mp (hs his) with hp | hslot
  · apply dvd_mul_of_dvd_left
    exact (Finset.dvd_prod_of_mem (fun Q : primeSupport D => (Q:Ideal O)) hip).trans
      (Finset.dvd_prod_of_mem (fun i => selectedDivisor D s a i) hp)
  · apply dvd_mul_of_dvd_right
    exact (selected_divides_factor D s v a hn PP i hi).trans
      (Finset.dvd_prod_of_mem v (Finset.mem_filter.mpr ⟨hslot,⟨PP,hip⟩⟩))

theorem extractedProduct_ne_zero (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0) :
    extractedProduct D s plain slots a v ≠ 0 :=
  mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => selectedDivisor_ne_zero D s a i))
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hv i (Finset.mem_filter.mp hi).1))

theorem actual_divisor_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) :
    Ideal.absNorm D ≤ (∏ i ∈ plain,Ideal.absNorm (selectedDivisor D s a i))*
      (∏ i ∈ frozenSlots D s slots a,Ideal.absNorm (v i)) := by
  have hd := divisor_dvd_extractedProduct D hD s plain slots hs a v hn
  have hnorm := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (extractedProduct_ne_zero D s plain slots a v hv))) (map_dvd Ideal.absNorm hd)
  simpa only [extractedProduct,map_mul,map_prod] using hnorm

theorem actual_divisor_log_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  have hnorm : (Ideal.absNorm D:ℝ) ≤
      (∏ i ∈ plain,(Ideal.absNorm (selectedDivisor D s a i):ℝ))*
      (∏ i ∈ frozenSlots D s slots a,(Ideal.absNorm (v i):ℝ)) := by
    exact_mod_cast actual_divisor_norm_boundary D hD s plain slots hs a v hn hv
  have hp (i : ι) : (Ideal.absNorm (selectedDivisor D s a i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D s a i))
  have hq (i : ι) (hi : i ∈ frozenSlots D s slots a) : (Ideal.absNorm (v i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i (Finset.mem_filter.mp hi).1))
  have hh := Real.logb_le_logb_of_le hZ (show (0:ℝ)< Ideal.absNorm D by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)) hnorm
  rw [Real.logb_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr hq), Real.logb_prod _ _ (fun i _ => hp i),
    Real.logb_prod _ _ hq] at hh
  exact hh

def formalReduction (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (P : ι → ℝ) (Z : ℝ) : ℝ :=
  (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
    ∑ i ∈ frozenSlots D s slots a,Real.logb Z (P i)

def frozenRatio (D : Ideal O) (s slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) (P : ι → ℝ) (Z : ℝ) : ℝ :=
  ∑ i ∈ frozenSlots D s slots a,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)

theorem formal_reduction_add_ratio (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0)
    (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i) (Z : ℝ) :
    formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z =
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  unfold formalReduction frozenRatio
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have his := (Finset.mem_filter.mp hi).1
  rw [Real.logb_div (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i his))) (hP i his).ne']
  ring

theorem actual_formal_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z := by
  rw [formal_reduction_add_ratio D s plain slots a v hv P hP Z]
  exact actual_divisor_log_boundary D hD s plain slots hs a v hn hv Z hZ

theorem divisor_dyad_card (Ds : Finset (Ideal O)) (T : ℝ) (hT : 1 ≤ T)
    (hD : ∀ D ∈ Ds,D ≠ 0) (hN : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T) :
    (Ds.card:ℝ) ≤ 256*T := by
  have h := EisensteinLatticeCount.finite_ideal_count_real Ds (2*T) (by linarith) hD
    (fun D hD => (hN D hD).le)
  linarith

theorem paired_raw_divisor_bound (Ds : Finset (Ideal O)) (T Z θ : ℝ)
    (hT : 1 ≤ T) (hZ : 1 < Z) (r₁ r₂ w₁ w₂ : Ideal O → ℝ)
    (hD : ∀ D ∈ Ds,D ≠ 0)
    (hlo : ∀ D ∈ Ds,T ≤ (Ideal.absNorm D:ℝ))
    (hhi : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T)
    (hleft : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₁ D+w₁ D)
    (hright : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₂ D+w₂ D)
    (hw : ∀ D ∈ Ds,w₁ D+w₂ D ≤ 2*θ) :
    (∑ D ∈ Ds,Z^(-(r₁ D+r₂ D)/2)) ≤ 256*Z^θ := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have he (D : Ideal O) (hmem : D ∈ Ds) : Z^(-(r₁ D+r₂ D)/2) ≤ Z^θ/T := by
    have hn := Real.logb_le_logb_of_le hZ hT0 (hlo D hmem)
    have h₁ := hleft D hmem
    have h₂ := hright D hmem
    have hω := hw D hmem
    have hh : -(r₁ D+r₂ D)/2 ≤ θ-Real.logb Z T := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hh
    rw [Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' hT0] at hpow
    exact hpow
  calc
    _ ≤ ∑ _D ∈ Ds,Z^θ/T := Finset.sum_le_sum (fun D hD => he D hD)
    _ = (Ds.card:ℝ)*(Z^θ/T) := by simp
    _ ≤ (256*T)*(Z^θ/T) := mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT hD hhi) (by positivity)
    _ = _ := by field_simp

end CenteredMomentDivisorBoundary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentHeckeExpansion CenteredMomentMask CenteredMomentRectangle HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def factorTuple (v : ι → Ideal O) (I J : Ideal O) : (ι ⊕ Fin 2) → Ideal O :=
  Sum.elim v (fun j => if j=0 then I else J)

def selectedPlain (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) : Ideal O := selectedDivisor D Finset.univ a (Sum.inr j)

def selectedSlot (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) : Ideal O := selectedDivisor D Finset.univ a (Sum.inl i)

theorem allocationTerm_rectangle (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O) :
    allocationTerm D Finset.univ (factorTuple v I J) a =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i ∣ v i then (1:ℂ) else 0)*
        (if selectedPlain D a 0 ∣ I then 1 else 0)*
        (if selectedPlain D a 1 ∣ J then 1 else 0) := by
  rw [allocationTerm_eq_product,Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,
    selectedPlain,selectedSlot]
  simp only [mul_assoc]
  rfl

theorem double_selected_reindex (D₁ D₂ : Ideal O) (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0)
    (F : Ideal O → Ideal O → ℂ) :
    (∑' I : Ideal O,∑' J : Ideal O,
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J) =
      ∑' I : Ideal O,∑' J : Ideal O,F (D₁*I) (D₂*J) := by
  have he (I J : Ideal O) :
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J =
        if D₁∣I then (if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  have hi (I : Ideal O) :
      (∑' J : Ideal O,if D₁∣I then (if D₂∣J then F I J else 0) else 0) =
        if D₁∣I then (∑' J : Ideal O,if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hi]
  rw [tsum_ideal_divisible D₁ h₁]
  exact tsum_congr (fun I => tsum_ideal_divisible D₂ h₂ (F (D₁*I)))

theorem allocated_rectangle_reindex (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ∑ v : (i : ι) → S i,
          (∏ i,if selectedSlot D a i ∣ (v i:Ideal O) then β i (v i) else 0)*
          ∑' I : Ideal O,∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
            idealRectangle W₁ W₂
              (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
              (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1)) I J := by
  let F (v : (i : ι) → S i) (I J : Ideal O) :=
    rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        ((if selectedPlain D a 0∣I then (1:ℂ) else 0)*
          (if selectedPlain D a 1∣J then 1 else 0)*F v I J) := by
    rw [allocationTerm_rectangle]
    dsimp only [F]
    ring
  have hint (v : (i : ι) → S i) :
      (∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        (∑' I : Ideal O,∑' J : Ideal O,F v (selectedPlain D a 0*I) (selectedPlain D a 1*J)) := by
    simp_rw [he]
    have ht := double_selected_reindex (selectedPlain D a 0) (selectedPlain D a 1)
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)) (F v)
    rw [← ht,← tsum_mul_left]
    apply tsum_congr
    intro I
    exact tsum_mul_left
  simp_rw [hint]
  have hβ (v : (i : ι) → S i) :
      (∏ i,β i (v i))*(allocationSign D Finset.univ a*
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0)) =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then β i (v i) else 0) := by
    rw [mul_left_comm,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp
  simp_rw [← mul_assoc]
  simp only [← mul_assoc] at hβ
  simp_rw [hβ]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  dsimp only [F]
  rw [common_extracted_slot_rectangle η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t
    W₁ W₂ X₁ X₂ Y₁ Y₂ (selectedPlain D a 0) (selectedPlain D a 1)]
  simp only [mul_assoc]

end CenteredMomentDivisorRectangle

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentDivisorRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentDivisorRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRectangle HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

theorem allocatedRectangle_eq_rows (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ((rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
          rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1)))*
          ∏ i,rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t) := by
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedRectangle
  rw [allocated_rectangle_reindex]
  rw [actual_slot_rectangle_sum η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t W₁ W₂ b₁ b₂
    _ _ _ _ hW₁ hW₂ (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1))
    (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))]

theorem allocatedRectangle_norm_le (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      ‖rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
        rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))‖ *
        ∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖ := by
  rw [allocatedRectangle_eq_rows η m A z t S β D a W₁ W₂ b₁ b₂ _ _ _ _
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂,norm_mul,norm_mul,allocationSign_norm,one_mul,norm_mul,norm_prod]
  apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact row_twisted_coefficient_norm η m A z t _ (mul_ne_zero
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))

end CenteredMomentDivisorRows

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentDivisorFullMask
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => Eisenstein.O

 theorem annular_hasFiniteSupport (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (fun I : Ideal O => W ((Ideal.absNorm I:ℝ)/X)).HasFiniteSupport := by
  apply (Ideal.finite_setOf_absNorm_le (S := O) (Nat.ceil (b*X))).subset
  intro I hI
  have hn := (div_le_iff₀ hX).mp (hs hI)
  exact_mod_cast hn.trans (Nat.le_ceil (b*X))

theorem rectangle_hasFiniteSupport (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (fun v : Ideal O × Ideal O => idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2).HasFiniteSupport := by
  have h₁ := (annular_hasFiniteSupport W₁ b₁ X₁ hX₁ hW₁).union
    (annular_hasFiniteSupport W₁ b₁ Y₁ hY₁ hW₁)
  have h₂ := (annular_hasFiniteSupport W₂ b₂ X₂ hX₂ hW₂).union
    (annular_hasFiniteSupport W₂ b₂ Y₂ hY₂ hW₂)
  apply (h₁.prod h₂).subset
  intro v hv
  constructor
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,zero_mul,sub_self])
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,mul_zero,sub_self])

theorem rectangle_tsum_sum {α : Type*} [Fintype α]
    (f : α → Ideal O → Ideal O → ℂ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O,∑' J : Ideal O,
      ∑ a, f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a,∑' I : Ideal O,∑' J : Ideal O,f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by
  have hs (a : α) : Summable (fun v : Ideal O × Ideal O =>
      f a v.1 v.2*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2) :=
    summable_of_hasFiniteSupport ((rectangle_hasFiniteSupport W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
      hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).mul_right _)
  have hi (I : Ideal O) := Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod_factor I)
  simp_rw [hi]
  exact Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem factorTuple_product (v : ι → Ideal O) (I J : Ideal O) :
    (∏ i,factorTuple v I J i)=(∏ i,v i)*I*J := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,
    show (1:Fin 2) ≠ 0 by decide,ite_false,mul_assoc]

theorem full_mask_eq_allocated_rectangles (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O) (hD : Squarefree D)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0) =
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a := by
    rw [← factorTuple_product]
    exact squarefree_mask_allocation D hD Finset.univ _
  simp_rw [he,Finset.sum_mul]
  simp_rw [rectangle_tsum_sum _ W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

end CenteredMomentDivisorFullMask

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorSlots
open CenteredMomentDivisorRectangle CenteredMomentDivisorRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => (selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

def liveIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => ¬(selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

theorem split_slot_product {M : Type*} [CommMonoid M] (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (f : ι → M) :
    (∏ i∈frozenIndices D a,f i)*(∏ i∈liveIndices D a,f i)=∏ i,f i :=
  Finset.prod_filter_mul_prod_filter_not _ _ _

theorem selected_live_slot (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ liveIndices D a) (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t =
      rowSlot η m A z S β t := by
  have he := selectedDivisor_empty D Finset.univ a (Sum.inl i)
    (Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hi).2)
  simp only [selectedSlot,he,one_dvd,ite_true]

theorem selected_frozen_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ frozenIndices D a) (S : Finset (Ideal O))
    (hS : ∀ I∈S,Prime I) (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hβ : ∀ I∈S,‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t‖ ≤ M := by
  obtain ⟨P,hP⟩ := (Finset.mem_filter.mp hi).2
  exact selected_slot_bound η m A z t (selectedSlot D a i) P
    (support_prime P.property) (Finset.dvd_prod_of_mem _ hP)
    S hS β M hM hβ

theorem selected_slot_product_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M : ι → ℝ) (hM : ∀ i,0 ≤ M i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i) :
    (∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖) ≤
      (∏ i∈frozenIndices D a,M i)*∏ i∈liveIndices D a,‖rowSlot η m A z (S i) (β i) t‖ := by
  rw [← split_slot_product D a]
  apply mul_le_mul
  · apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i hi
    exact selected_frozen_slot_bound η m A z t D a i hi (S i) (hS i) (β i) (M i) (hM i) (hβ i)
  · apply le_of_eq
    apply Finset.prod_congr rfl
    intro i hi
    rw [selected_live_slot η m A z t D a i hi]
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => hM i)

def selectedNorm (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  (Ideal.absNorm (selectedPlain D a 0):ℝ)*(Ideal.absNorm (selectedPlain D a 1):ℝ)

theorem selectedNorm_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    0 < selectedNorm D a := by
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a _))

def rawRemaining (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) : ℝ := (T/selectedNorm D a)*∏ i∈liveIndices D a,P i

def formalReductionFactor (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ) : ℝ := selectedNorm D a*∏ i∈frozenIndices D a,P i

theorem raw_scale_identity (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) :
    rawRemaining D a T P*formalReductionFactor D a P=T*∏ i,P i := by
  unfold rawRemaining formalReductionFactor
  rw [← split_slot_product D a P]
  field_simp [(selectedNorm_pos D a).ne']

end CenteredMomentDivisorRaw

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_norm_sq (T : ℝ) (hT : 0 < T) (x : ℂ) :
    ‖(Real.sqrt T:ℂ)⁻¹*x‖^2=‖x‖^2/T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt hT.le]
  ring

def residualCenteredRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  centeredSlotRow η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
    (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1))
    (T/selectedNorm D a)

theorem allocated_raw_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 := by
  let R : ℂ :=
    rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
    rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))
  let L : ℂ := R*∏ i∈liveIndices D a,rowSlot η m A z (S i) (β i) t
  have hn : ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      (∏ i∈frozenIndices D a,M i)*‖L‖ := by
    apply (allocatedRectangle_norm_le η m A z t S β D a W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).trans
    have hh := mul_le_mul_of_nonneg_left
      (selected_slot_product_bound η m A z t D a S hS β M hM hβ) (norm_nonneg R)
    dsimp only [L]
    rw [norm_mul,norm_prod]
    convert hh using 1 ; ring
  have hraw : 0 < rawRemaining D a T P := mul_pos (div_pos hT (selectedNorm_pos D a))
    (Finset.prod_pos (fun i _ => hP i))
  have hformal : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hres : ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 =
      ‖L‖^2/rawRemaining D a T P := by
    unfold residualCenteredRow centeredSlotRow
    rw [Finset.prod_coe_sort (liveIndices D a) P,
      Finset.prod_coe_sort (liveIndices D a) (fun i => rowSlot η m A z (S i) (β i) t)]
    exact normalized_norm_sq _ hraw L
  rw [normalized_norm_sq _ htotal,hres]
  calc
    _ ≤ ((∏ i∈frozenIndices D a,M i)*‖L‖)^2/(T*∏ i,P i) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) htotal.le
    _ = _ := by
      rw [← raw_scale_identity D a T P,mul_pow]
      field_simp [hraw.ne',hformal.ne']

end CenteredMomentDivisorRawEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorEnergy
open  CenteredMomentDivisorAllocation
local notation "O" => Eisenstein.O
variable {ι α ρ : Type*} [DecidableEq ι]

def allocatedPolynomial (D : Ideal O) (s : Finset ι) (T : Finset α)
    (v : α → ι → Ideal O) (F : ρ → α → ℂ) (a : Allocation D s) (h : ρ) : ℂ :=
  ∑ j ∈ T, allocationTerm D s (v j) a*F h j

theorem finite_mask_regroup (D : Ideal O) (hD : Squarefree D) (s : Finset ι)
    (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (h : ρ) :
    (∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocatedPolynomial D s T v F a h := by
  have ht (j : α) : (if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocationTerm D s (v j) a*F h j := by
    have he := congrArg (fun w : ℂ => w*F h j) (squarefree_mask_allocation D hD s (v j))
    simpa only [ite_mul,one_mul,zero_mul,Finset.sum_mul] using he
  simp_rw [ht]
  rw [Finset.sum_comm]
  rfl

theorem allocation_card_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      (Fintype.card (Allocation D s):ℝ) ≤ C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := CompletedGauss.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C ^ N,pow_pos hC _,?_⟩
  intro D hD s hs
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C ^ N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

theorem allocated_energy_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), Squarefree D → ∀ s : Finset ι, s.card ≤ N →
      ∀ (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (rows : Finset ρ),
      (∑ h ∈ rows, ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι) N hN ε hε
  refine ⟨C,hC,?_⟩
  intro D hD s hs T v F rows
  have hrow (h : ρ) : ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2 ≤
      (Fintype.card (Allocation D s):ℝ)*∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 := by
    rw [finite_mask_regroup D hD s T v F h]
    calc
      _ ≤ (∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _a : Allocation D s => (1:ℝ))
          (fun a => ‖allocatedPolynomial D s T v F a h‖))
  calc
    _ ≤ ∑ h ∈ rows, (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero s hs)
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end CenteredMomentDivisorEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentDivisorRowEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRows CenteredMomentDivisorFullMask
open CenteredMomentDivisorEnergy CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

theorem actual_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) («ω» : O → ℝ),(∀ z ∈ rows,0 ≤ «ω» z) →
      (∑ z ∈ rows,«ω» z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ∑ z ∈ rows,«ω» z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι ⊕ Fin 2) (N+2) (by omega) ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows «ω» hω
  have hc : (Finset.univ : Finset (ι ⊕ Fin 2)).card ≤ N+2 := by
    simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hslots 2
  have hrow (z : O) :
      ‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
        (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
    unfold maskedRectangle
    rw [full_mask_eq_allocated_rectangles η m A z t S β D hD W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
    calc
      _ ≤ (∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) => (1:ℝ))
          (fun a => ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖))
  calc
    _ ≤ ∑ z ∈ rows,«ω» z*((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) :=
      Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hrow z) (hω z hz))
    _ = (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ z ∈ rows,«ω» z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
      simp_rw [mul_left_comm («ω» _) _,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero Finset.univ hc)
      (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun z hz => mul_nonneg (hω z hz) (sq_nonneg _))))

end CenteredMomentDivisorRowEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentSlotRatios
local notation "O" => Eisenstein.O

def logWindow (a b : ℝ) : ℝ := max |Real.log a| |Real.log b|

theorem logWindow_nonneg (a b : ℝ) : 0 ≤ logWindow a b :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem slot_log_ratio_bound (W : ℝ → ℂ) (a b P Z : ℝ) (I : Ideal O)
    (ha : 0 < a) (hZ : 1 < Z)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hW : W ((Ideal.absNorm I:ℝ)/P) ≠ 0) :
    |Real.logb Z ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b/Real.log Z := by
  have hw := hs hW
  have hr : 0 < (Ideal.absNorm I:ℝ)/P := ha.trans_le hw.1
  have hlow := Real.log_le_log ha hw.1
  have hhigh := Real.log_le_log hr hw.2
  have habs : |Real.log ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (Real.log a)
      have hm := le_max_left |Real.log a| |Real.log b|
      dsimp only [logWindow]
      linarith
    · exact hhigh.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [Real.logb,abs_div,abs_of_pos (Real.log_pos hZ)]
  exact div_le_div_of_nonneg_right habs (Real.log_pos hZ).le

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem frozen_subset_ratio_bound (entrance frozen : Finset ι) (hsub : frozen ⊆ entrance)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ frozen,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |∑ i ∈ frozen,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  calc
    _ ≤ ∑ i ∈ frozen,|Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ frozen,logWindow (a i) (b i)/Real.log Z :=
      Finset.sum_le_sum (fun i hi => slot_log_ratio_bound (W i) (a i) (b i) (P i) Z (v i)
        (ha i (hsub hi)) hZ (hs i (hsub hi)) (hW i hi))
    _ = (∑ i ∈ frozen,logWindow (a i) (b i))/Real.log Z := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => logWindow_nonneg (a i) (b i))) (Real.log_pos hZ).le

theorem disjoint_frozen_ratio_bound (entrance old fresh : Finset ι)
    (hold : old ⊆ entrance) (hfresh : fresh ⊆ entrance) (hdis : Disjoint old fresh)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ old ∪ fresh,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |(∑ i ∈ old,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))+
      (∑ i ∈ fresh,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  rw [← Finset.sum_union hdis]
  exact frozen_subset_ratio_bound entrance (old ∪ fresh) (Finset.union_subset hold hfresh)
    W a b P v Z hZ ha hs hW

end CenteredMomentSlotRatios

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentDivisorWitness
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentHeckeExpansion
open CenteredMomentRectangle HeckeFamily 
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_tsum_term {α : Type*} (f : α → ℂ) (h : (∑' x,f x) ≠ 0) :
    ∃ x,f x ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (by simp only [hn,tsum_zero])

theorem allocated_nonzero_witness (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    ∃ (v : (i : ι) → S i) (I J : Ideal O),
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a ≠ 0 ∧
      (∀ i,β i (v i) ≠ 0) ∧ idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J ≠ 0 := by
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hβ,ht⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨I,hI⟩ := exists_tsum_term _ ht
  obtain ⟨J,hJ⟩ := exists_tsum_term _ hI
  have hh := mul_ne_zero_iff.mp hJ
  exact ⟨v,I,J,(mul_ne_zero_iff.mp hh.1).1,
    fun i => Finset.prod_ne_zero_iff.mp hβ i (Finset.mem_univ i),hh.2⟩

def actualExtracted (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) : Ideal O :=
  (selectedPlain D a 0*selectedPlain D a 1)*∏ i∈frozenIndices D a,v i

private theorem prime_dvd_selectedPlain (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) (P : primeSupport D)
    (hP : P ∈ selectedPrimes D Finset.univ a (Sum.inr j)) :
    (P : Ideal O) ∣ selectedPlain D a j := by
  exact Finset.dvd_prod_of_mem (fun q : primeSupport D => (q : Ideal O))
    (a := P) (s := selectedPrimes D Finset.univ a (Sum.inr j)) hP

theorem divisor_dvd_actualExtracted (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    D ∣ actualExtracted D a v := by
  apply (squarefree_dvd_iff D _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (a PP).property).1
  have hmem : PP ∈ selectedPrimes D Finset.univ a i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  cases i with
  | inl i =>
      have hfr : i ∈ frozenIndices D a := Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨PP,hmem⟩⟩
      have hd : P∣v i := selected_divides_factor D Finset.univ (factorTuple v I J) a hn PP (Sum.inl i) hi
      exact dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem v (a := i) (s := frozenIndices D a) hfr)) _
  | inr j =>
      have hd : P∣selectedPlain D a j := prime_dvd_selectedPlain D a j PP hmem
      fin_cases j
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

theorem actualExtracted_ne_zero (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) : actualExtracted D a v ≠ 0 :=
  mul_ne_zero (mul_ne_zero (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i))

theorem actualExtracted_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    (Ideal.absNorm D:ℝ) ≤ selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i):ℝ) := by
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (actualExtracted_ne_zero D a v hv))) (map_dvd Ideal.absNorm (divisor_dvd_actualExtracted D hD a v I J hn))
  simpa only [actualExtracted,map_mul,map_prod,Nat.cast_mul,Nat.cast_prod,selectedNorm] using
    (show (Ideal.absNorm D:ℝ) ≤ Ideal.absNorm (actualExtracted D a v) by exact_mod_cast h)

end CenteredMomentDivisorWitness

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentDivisorActualBoundary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentDivisorWitness CenteredMomentSlotRatios HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem selected_log_identity (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i,0 < P i) (Z : ℝ) :
    Real.logb Z (selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i:Ideal O):ℝ)) =
      Real.logb Z (formalReductionFactor D a P)+
        ∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i) := by
  have hn (i : ι) : (Ideal.absNorm (v i:Ideal O):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i))
  unfold formalReductionFactor
  rw [Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)),
    Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne')),
    Real.logb_prod _ _ (fun i _ => hn i),Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  simp_rw [Real.logb_div (hn _) (hP _).ne']
  rw [Finset.sum_sub_distrib]
  ring

theorem nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (hβW : ∀ i I,β i I ≠ 0 → W i ((Ideal.absNorm I:ℝ)/P i) ≠ 0)
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨v,I,J,ha,hβ,hrect⟩ := allocated_nonzero_witness η m A z t S β D a
    W₁ W₂ X₁ X₂ Y₁ Y₂ hne
  have hv (i : ι) : (v i:Ideal O) ≠ 0 := (hS i (v i) (v i).property).ne_zero
  have hb := actualExtracted_norm_boundary D hD a (fun i => v i) hv I J ha
  have hND : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hl := Real.logb_le_logb_of_le hZ hND hb
  rw [selected_log_identity D a (fun i => v i) hv P hP Z] at hl
  have hr : |∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i)| ≤
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
    apply frozen_subset_ratio_bound (ι := ι) Finset.univ (frozenIndices D a) (Finset.subset_univ _)
      W lo hi P (fun i => (v i:Ideal O)) Z hZ
    · intro i _
      exact hlo i
    · intro i _
      exact hW i
    · intro i _
      exact hβW i (v i) (hβ i)
  have hh := (le_abs_self (∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i))).trans hr
  linarith

theorem original_nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z :=
  nonzero_row_formal_boundary η m A z t S hS _ W lo hi P hlo hP hW
    (fun _i _I h => (mul_ne_zero_iff.mp h).2) D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hne

end CenteredMomentDivisorActualBoundary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open SchwartzPlanePoisson InversePrincipalEnergy
local notation "O" => Eisenstein.O

def dilated (W : ℝ → ℂ) (c : ℝ) : ℝ → ℂ := fun x => W (c * x)

theorem dilated_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (c : ℝ) :
    ContDiff ℝ ∞ (dilated W c) :=
  hW.comp (contDiff_const.mul contDiff_id)

theorem dilated_support (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (dilated W c) ⊆ Set.Icc (a / B) b := by
  intro x hx
  have hv := hs hx
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx0 : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha hv.1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  constructor
  · apply (div_le_iff₀ hB0).mpr
    exact hv.1.trans (by nlinarith)
  · exact (show x ≤ c * x by nlinarith).trans hv.2

theorem seminorm_dilation_le (f g : 𝓢(ℝ, ℂ)) (ζ : ℂ) (c B : ℝ)
    (hζ : ‖ζ‖ = 1) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hg : ∀ x, g x = ζ * f (c * x)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n g ≤ B ^ n * SchwartzMap.seminorm ℝ k n f := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hB0 : 0 ≤ B := hc0.trans hcB
  have he : (g : ℝ → ℂ) = fun x => ζ * f (c * x) := funext hg
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (by positivity)
  intro x
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f.smooth n), norm_mul, hζ,
    one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 n)]
  have hx : |x| ^ k ≤ |c * x| ^ k := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  calc
    _ = c ^ n * (|x| ^ k * ‖iteratedDeriv n f (c * x)‖) := by ring
    _ ≤ c ^ n * (|c * x| ^ k * ‖iteratedDeriv n f (c * x)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (pow_nonneg hc0 n)
    _ ≤ c ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k n f (c * x))
        (pow_nonneg hc0 n)
    _ ≤ B ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcB _) (apply_nonneg _ _)

theorem normPowerProfile_dilated (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    normPowerProfile (dilated W c) (a / B) b
      (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t x =
      ((c : ℂ) ^ (Complex.I * t))⁻¹ *
        normPowerProfile W a b ha hs hW t (c * x) := by
  rw [normPowerProfile_apply, normPowerProfile_apply]
  by_cases hz : W (c * x) = 0
  · simp [dilated, hz]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hx : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha (hs hz).1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  have hp := Complex.mul_cpow_ofReal_nonneg hc0.le hx.le (Complex.I * t)
  rw [← Complex.ofReal_mul] at hp
  rw [hp]
  have hn : (c : ℂ) ^ (Complex.I * t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_real_imaginary_power c t hc0]; norm_num)
  dsimp only [dilated]
  simp only [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem normPowerProfile_dilated_seminorm (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n (normPowerProfile W a b ha hs hW t) := by
  apply seminorm_dilation_le _ _ ((c : ℂ) ^ (Complex.I * t))⁻¹ c B
    (by rw [norm_inv, norm_real_imaginary_power c t (lt_of_lt_of_le zero_lt_one hc), inv_one])
    hc hcB
  intro x
  exact normPowerProfile_dilated W a b B c ha hB hc hcB hs hW t x

theorem normPowerProfile_dilated_finite (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (F : Finset (ℕ × ℕ)) :
    F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) := by
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  apply (normPowerProfile_dilated_seminorm W a b B c ha hB hc hcB hs hW t z.1 z.2).trans
  exact mul_le_mul (pow_le_pow_right₀ hB (Finset.le_sup hz))
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hz) (apply_nonneg _ _) (by positivity)

theorem dilated_normPowerProfile_uniform_degree (a b B : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, ∀ hc : 1 ≤ c, ∀ hcB : c ≤ B, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (normPowerProfile (dilated W c) (a / B) b
          (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
          (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
        C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := normPowerProfile_uniform_degree a b ha F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  refine ⟨B ^ (F.sup Prod.snd) * C, mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hB) _) hC, ?_⟩
  intro c hc hcB t
  have ht : (1 + ‖t / (2 * Real.pi)‖) ^ J ≤ (1 + ‖t‖) ^ J := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  calc
    _ ≤ B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) :=
      normPowerProfile_dilated_finite W a b B c ha hB hc hcB hs hW t F
    _ ≤ B ^ (F.sup Prod.snd) * (C * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left
        ((hbound t).trans (mul_le_mul_of_nonneg_left ht hC.le)) (by positivity)
    _ = _ := by ring

def clippedScale (S : ℝ) : ℝ := max 1 S

def clipDilation (S : ℝ) : ℝ := clippedScale S / S

theorem clippedScale_ge_one (S : ℝ) : 1 ≤ clippedScale S := le_max_left _ _

theorem clipDilation_ge_one (S : ℝ) (hS : 0 < S) : 1 ≤ clipDilation S := by
  rw [clipDilation, le_div_iff₀ hS, one_mul]
  exact le_max_right _ _

theorem clipDilation_le (b S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) :
    clipDilation S ≤ max 1 b := by
  rw [clipDilation, div_le_iff₀ hS]
  apply max_le
  · exact hret.trans (by nlinarith [le_max_right (1 : ℝ) b])
  · nlinarith [le_max_left (1 : ℝ) b]

theorem clipDilation_eq_one (S : ℝ) (hS : 1 ≤ S) : clipDilation S = 1 := by
  simp [clipDilation, clippedScale, max_eq_right hS, ne_of_gt (lt_of_lt_of_le zero_lt_one hS)]

theorem clipDilation_subunit (S : ℝ) (hS : S ≤ 1) :
    clipDilation S = 1 / S := by simp [clipDilation, clippedScale, max_eq_left hS]

theorem clipped_source (W : ℝ → ℂ) (S x : ℝ) (hS : 0 < S) :
    dilated W (clipDilation S) (x / clippedScale S) = W (x / S) := by
  have hclip : clippedScale S ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (clippedScale_ge_one S))
  unfold dilated clipDilation
  congr 1
  field_simp

theorem strict_subunit_ideal_zero (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1)
    (I : Ideal O) (hI : I ≠ 0) : W ((Ideal.absNorm I : ℝ) / S) = 0 := by
  by_contra h
  have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := (div_le_iff₀ hS).mp (hs h)
  nlinarith

theorem strict_subunit_sum_zero (A : Ideal O → ℂ) (hA : A 0 = 0)
    (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) = 0 := by
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · rw [hI, hA, zero_mul]
      · rw [strict_subunit_ideal_zero W b S hS hs hstrict I hI, mul_zero]
    _ = 0 := tsum_zero

theorem clipped_ideal_sum (A : Ideal O → ℂ) (W : ℝ → ℂ) (S : ℝ) (hS : 0 < S) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) =
      ∑' I : Ideal O, A I * dilated W (clipDilation S)
        ((Ideal.absNorm I : ℝ) / clippedScale S) := by
  apply tsum_congr
  intro I
  rw [clipped_source W S _ hS]

theorem clipped_twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    twistedIdealSum χ W t S =
      twistedIdealSum χ (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_twistedIdealSum_zero (χ : Character) (W : ℝ → ℂ)
    (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : twistedIdealSum χ W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

theorem clipped_rowTwistedSum (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    rowTwistedSum η m A₀ z W t S =
      rowTwistedSum η m A₀ z (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_rowTwistedSum_zero (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : rowTwistedSum η m A₀ z W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

def retainedProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  normPowerProfile (dilated W (clipDilation S)) (a / max 1 b) b
    (div_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
      (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs)
    (dilated_contDiff W hW (clipDilation S)) t

theorem retainedProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t x : ℝ) :
    retainedProfile W a b ha hs hW S hS hret t x =
      (x : ℂ) ^ (Complex.I * t) * W (clipDilation S * x) :=
  normPowerProfile_apply _ _ _ _ _ _ _ _

theorem retainedProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    Function.support (retainedProfile W a b ha hs hW S hS hret t : ℝ → ℂ) ⊆
      Set.Icc (a / max 1 b) b := by
  apply (normPowerProfile_support _ _ _ _ _ _ _).trans
  exact dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
    (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs

theorem retainedProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W a b ha hs hW S hS hret t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := dilated_normPowerProfile_uniform_degree a b (max 1 b) ha (le_max_left _ _) F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  exact ⟨C, hC, fun S hS hret t =>
    hbound (clipDilation S) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) t⟩

theorem two_retainedProfile_uniform_degree (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ hW₁ : ContDiff ℝ ∞ W₁, ∀ hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ S₁ S₂ : ℝ, ∀ hS₁ : 0 < S₁, ∀ hS₂ : 0 < S₂,
      ∀ hret₁ : 1 ≤ S₁ * b₁, ∀ hret₂ : 1 ≤ S₂ * b₂, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ S₁ hS₁ hret₁ t) +
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ S₂ hS₂ hret₂ t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J₁, hJ₁⟩ := retainedProfile_uniform_degree a₁ b₁ ha₁ F
  obtain ⟨J₂, hJ₂⟩ := retainedProfile_uniform_degree a₂ b₂ ha₂ F
  refine ⟨max J₁ J₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C₁, hC₁, hb₁⟩ := hJ₁ W₁ hs₁ hW₁
  obtain ⟨C₂, hC₂, hb₂⟩ := hJ₂ W₂ hs₂ hW₂
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro S₁ S₂ hS₁ hS₂ hret₁ hret₂ t
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have h₁ := (hb₁ S₁ hS₁ hret₁ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left J₁ J₂)) hC₁.le)
  have h₂ := (hb₂ S₂ hS₂ hret₂ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right J₁ J₂)) hC₂.le)
  nlinarith

theorem retained_row_rectangle (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) =
      A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂)) := by
  rw [clipped_rowTwistedSum η m A₀ z W₁ t S₁ hS₁,
    clipped_rowTwistedSum η m A₀ z W₂ t S₂ hS₂]

theorem strict_subunit_row_rectangle_zero (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hstrict : S₁ * b₁ < 1 ∨ S₂ * b₂ < 1) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) = 0 := by
  rcases hstrict with h₁ | h₂
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₁ b₁ t S₁ hS₁ hs₁ h₁, zero_mul, mul_zero]
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₂ b₂ t S₂ hS₂ hs₂ h₂, mul_zero, mul_zero]

theorem two_retained_row_rectangles (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (A : ℂ) :
    ‖A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
      rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ≤
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ +
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ := by
  rw [mul_sub, retained_row_rectangle η m A₀ z W₁ W₂ t S₁ S₂ hS₁ hS₂ A,
    retained_row_rectangle η m A₀ z W₁ W₂ t T₁ T₂ hT₁ hT₂ A]
  exact norm_sub_le _ _

theorem two_retained_row_energies (η : Character) (m A₀ : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (rows : Finset O) (A : O → ℂ) (w : O → ℝ) (hw : ∀ z ∈ rows, 0 ≤ w z) :
    (∑ z ∈ rows, w z * ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2) ≤
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2) +
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hb := two_retained_row_rectangles η m A₀ z W₁ W₂ t S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hnorm : ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2 ≤
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2 +
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ -
       ‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖)]
  convert mul_le_mul_of_nonneg_left hnorm (hw z hz) using 1; ring

theorem retained_volumeControl_le (Q : Ideal O) (χ : Character)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
      (max 1 b) ^ (pvSeminorms.sup Prod.snd) *
        volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  have h := normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation S)
    ha (le_max_left _ _) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs hW t pvSeminorms
  change pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (retainedProfile W a b ha hs hW S hS hret t) ≤ _ at h
  unfold volumeControl pvControl
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ((idealDivisors χ.modulus).card : ℝ) *
      (Nat.card (O ⧸ Ideal.span {fixedPeriod Q}) : ℝ) * pvConstant from
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) pvConstant_pos.le)
  convert hh using 1 <;> first | rfl | ring

theorem retained_volumeControl_uniform_degree (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := volumeControl_polynomial_height Q a b ε B ha hε hB
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  let D := (max 1 b) ^ (pvSeminorms.sup Prod.snd)
  have hD : 0 < D := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro Z hZ χ hχ S hS hret t
  calc
    _ ≤ D * volumeControl Q χ (normPowerProfile W a b ha hs hW t) :=
      retained_volumeControl_le Q χ W a b ha hs hW S hS hret t
    _ ≤ D * (C * Z ^ ε * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left (hbound Z hZ χ hχ t) hD.le
    _ = _ := by ring

end CenteredMomentRetainedProfile

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
