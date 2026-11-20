import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.InvertingEveryTranslatedPrimeMoebiusProduct
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheFrobeniusOfTheTorsionIsGalois
import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev

/-!
# Quantitative nonvanishing of the prime Möbius frequencies

In each row the nonzero frequencies are all conjugates of one
cyclotomic integer. Its norm bounds their product from below. The
exact squarefree overlap supplies a second, additive constraint.
Together they bound the product on any prescribed subset of modes.
-/
noncomputable section
open Finset Complex Polynomial ArithmeticFunction
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {p : ℕ} [Fact p.Prime]
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod p) ℂ)
local notation "A" => cyclicAmbiguityAmplitude (cyclicMoebiusProfile p)
local notation "W" => cyclicAmbiguityWeight (cyclicMoebiusProfile p)

private def rowPoly (b : ZMod p) : ℤ[X] :=
  ∑ x : ZMod p, C ((moebius ((x+b).val+1):ℤ)*moebius (x.val+1))*X^x.val

private theorem phase_pow (a : ZMod p) (n : ℕ) :
    (χ (-a))^n=χ (-(a*(n:ZMod p))) := by
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  congr 1; ring

private theorem eval_row (a b : ZMod p) : aeval (χ (-a)) (rowPoly b) = A a b := by
  simp only [rowPoly,map_sum,map_mul,aeval_C,aeval_X,map_pow,cyclicAmbiguityAmplitude]
  refine sum_congr rfl fun x _ => ?_
  rw [phase_pow,ZMod.natCast_zmod_val]
  simp [cyclicMoebiusProfile]

private theorem primitive_phase {a : ZMod p} (ha : a ≠ 0) : IsPrimitiveRoot (χ (-a)) p := by
  have hp : p.Prime := Fact.out
  apply isPrimitiveRoot_of_mem_nthRootsFinset hp
  · apply (Polynomial.mem_nthRootsFinset hp.pos (1:ℂ)).mpr
    rw [phase_pow,ZMod.natCast_self,mul_zero,neg_zero,AddChar.map_zero_eq_one]
  · intro h
    have he : χ (-a) = χ 0 := by simpa only [AddChar.map_zero_eq_one] using h
    exact ha (neg_eq_zero.mp (ZMod.injective_stdAddChar he))

private theorem phase_image :
    (univ.erase (0:ZMod p)).image (fun a => χ (-a)) = primitiveRoots p ℂ := by
  classical
  have hp : p.Prime := Fact.out
  have hi : Function.Injective (fun a : ZMod p => χ (-a)) :=
    fun _ _ h => neg_injective (ZMod.injective_stdAddChar h)
  apply eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact (mem_primitiveRoots hp.pos).mpr (primitive_phase (mem_erase.mp ha).1)
  · rw [card_image_of_injective _ hi,card_erase_of_mem (mem_univ _),card_univ,ZMod.card,
      Complex.card_primitiveRoots,Nat.totient_prime hp]

/-- The squared Fourier amplitudes over the nonzero frequency axis
have product at least one in every row, uniformly in the lag. -/
theorem one_le_prime_moebius_frequency_product (hp : 5 ≤ p) (b : ZMod p) :
    1 ≤ ∏ a ∈ univ.erase (0:ZMod p),W a b := by
  classical
  have hp' : p.Prime := Fact.out
  have hp1 := primitive_phase (one_ne_zero : (1:ZMod p) ≠ 0)
  have hn : aeval (χ (-(1:ZMod p))) (rowPoly b) ≠ 0 := by
    rw [eval_row]
    intro he
    have h := every_nonzero_prime_moebius_frequency one_ne_zero hp b
    simp [cyclicAmbiguityWeight,he] at h
  have h := one_le_prod_norm_aeval_primitiveRoots hp'.pos (rowPoly b)
    ⟨_,(mem_primitiveRoots hp'.pos).mpr hp1,hn⟩
  rw [←phase_image,prod_image (fun a _ c _ he => neg_injective (ZMod.injective_stdAddChar he))] at h
  simp only [eval_row] at h
  have hs := pow_le_pow_left₀ zero_le_one h 2
  simpa only [one_pow,prod_pow,cyclicAmbiguityWeight] using hs

private theorem prod_le_mean_pow {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∏ i ∈ S,f i) ≤ ((∑ i ∈ S,f i)/(S.card:ℝ))^S.card := by
  by_cases he : S = ∅
  · subst S; simp
  have hs := Nat.cast_pos (α:=ℝ).mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr he))
  have h := Real.geom_mean_le_arith_mean S (fun _ => 1) f (fun _ _ => zero_le_one)
    (by simpa only [sum_const,nsmul_eq_mul,mul_one] using hs) hf
  simp only [Real.rpow_one,sum_const,nsmul_eq_mul,mul_one,one_mul] at h
  have hn := prod_nonneg hf
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hn _) h S.card
  rwa [←Real.rpow_natCast,←Real.rpow_mul hn,inv_mul_cancel₀ hs.ne',Real.rpow_one] at hpow

/-- For an arbitrary group of observed nonzero modes, the missing
modes can compensate only up to the power of their mean energy. -/
theorem selected_prime_moebius_frequency_product (hp : 5 ≤ p) (b : ZMod p)
    (S : Finset (ZMod p)) (hs : S ⊆ univ.erase 0) :
    let R := univ.erase (0:ZMod p) \ S
    1 ≤ (∏ a ∈ S,W a b) * (((p:ℝ)*(squarefreeCyclicPairs p b).card/R.card)^R.card) := by
  classical
  let R := univ.erase (0:ZMod p) \ S
  change 1 ≤ _ * ((_ / (R.card:ℝ)) ^ R.card)
  have hmass := sum_le_sum_of_subset_of_nonneg (subset_univ R) (fun a _ _ => sq_nonneg ‖A a b‖)
  change (∑ a ∈ R,W a b) ≤ ∑ a,W a b at hmass
  rw [cyclic_moebius_frequency_mass] at hmass
  have hr := (prod_le_mean_pow R (fun a => W a b) (fun _ _ => sq_nonneg _)).trans
    (pow_le_pow_left₀ (div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg R.card))
      (div_le_div_of_nonneg_right hmass (Nat.cast_nonneg _)) R.card)
  have h := one_le_prime_moebius_frequency_product hp b
  rw [←prod_sdiff hs] at h
  change 1 ≤ (∏ a ∈ R,W a b) * (∏ a ∈ S,W a b) at h
  exact h.trans ((mul_le_mul_of_nonneg_right hr (prod_nonneg (fun _ _ => sq_nonneg _))).trans_eq (mul_comm ..))

/-- A bound on the reciprocal energy of each nonzero Fourier mode. -/
def primeMoebiusInverseEnergyBound (b : ZMod p) : ℝ :=
  ((p:ℝ)*(squarefreeCyclicPairs p b).card/((p-2:ℕ):ℝ))^(p-2)

private theorem inverse_bound_nonneg (b : ZMod p) : 0 ≤ primeMoebiusInverseEnergyBound b := by
  unfold primeMoebiusInverseEnergyBound; positivity

theorem prime_moebius_mode_lower (hp : 5 ≤ p) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    1 ≤ W a b * primeMoebiusInverseEnergyBound b := by
  have hm : a ∈ univ.erase (0:ZMod p) := mem_erase.mpr ⟨ha,mem_univ _⟩
  have hc : ((univ.erase (0:ZMod p)) \ {a}).card = p-2 := by
    rw [sdiff_singleton_eq_erase,card_erase_of_mem hm,card_erase_of_mem (mem_univ _),card_univ,ZMod.card]
    omega
  simpa only [hc,prod_singleton,primeMoebiusInverseEnergyBound] using
    selected_prime_moebius_frequency_product hp b {a} (singleton_subset_iff.mpr hm)

/-- Quantitative inversion on zero-sum errors. The factor depends on
the squarefree overlap and is uniform over both signals being compared. -/
theorem prime_moebius_reconstruction_energy_bound (hp : 5 ≤ p) (b : ZMod p)
    (g : ZMod p → ℂ) (hg : ∑ j,g j=0) :
    (∑ j,‖g j‖^2) ≤ primeMoebiusInverseEnergyBound b *
      ∑ t,‖translatedMoebiusReading b g t‖^2 := by
  let y := translatedMoebiusReading b g
  let L := primeMoebiusInverseEnergyBound b
  have row (a : ZMod p) : ‖ZMod.dft g a‖^2 ≤ L*‖ZMod.dft y a‖^2 := by
    by_cases ha : a=0
    · subst a
      rw [ZMod.dft_apply_zero,hg,norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (inverse_bound_nonneg b) (sq_nonneg _)
    have hA : A a b ≠ 0 := by
      intro hz
      have hw := every_nonzero_prime_moebius_frequency ha hp b
      simp [cyclicAmbiguityWeight,hz] at hw
    have hd := congrArg (fun f : ZMod p → ℂ => ZMod.dft f a)
      (decode_moebius_translates_exactly b hp g).symm
    change ZMod.dft g a=ZMod.dft (decodeMoebiusTranslates b (∑ j,g j) y) a at hd
    rw [decodeMoebiusTranslates,LinearEquiv.apply_symm_apply,if_neg ha] at hd
    have he := (eq_div_iff hA).mp hd
    have hw : ‖ZMod.dft g a‖^2*W a b=‖ZMod.dft y a‖^2 := by
      rw [←he,norm_mul,mul_pow]; rfl
    calc ‖ZMod.dft g a‖^2 = ‖ZMod.dft g a‖^2*1 := (mul_one _).symm
         _ ≤ ‖ZMod.dft g a‖^2*(W a b*L) := mul_le_mul_of_nonneg_left
           (prime_moebius_mode_lower hp ha b) (sq_nonneg _)
         _ = L*‖ZMod.dft y a‖^2 := by rw [←hw]; ring
  have parseval (f : ZMod p → ℂ) :
      (∑ a,‖ZMod.dft f a‖^2) = (p:ℝ)*∑ j,‖f j‖^2 := by
    simpa only [Complex.normSq_eq_norm_sq] using
      GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval p f
  have h := sum_le_sum (s:=univ) (fun a _ => row a)
  rw [←mul_sum,parseval,parseval,mul_left_comm L] at h
  exact le_of_mul_le_mul_left h (Nat.cast_pos.mpr (by omega : 0<p))

/-- Omitting any prescribed translate costs at most a further factor
of p in squared reconstruction error. The known signal sum fixes the
sum of the readings, so Cauchy–Schwarz bounds the missing coordinate. -/
theorem prime_moebius_energy_after_one_erasure (hp : 5 ≤ p) (b r : ZMod p)
    (g : ZMod p → ℂ) (hg : ∑ j,g j=0) :
    (∑ j,‖g j‖^2) ≤ (p:ℝ)*primeMoebiusInverseEnergyBound b *
      ∑ t ∈ univ.erase r,‖translatedMoebiusReading b g t‖^2 := by
  let y := translatedMoebiusReading b g
  have hr : ∃! f : ZMod p → ℂ, (∑ t,f t)=0 ∧ translatedMoebiusReading b f=y := by
    refine ⟨g,⟨hg,rfl⟩,?_⟩
    rintro f ⟨hs,hy⟩
    calc f = decodeMoebiusTranslates b 0 y := by
           simpa only [hs,hy] using (decode_moebius_translates_exactly b hp f).symm
         _ = g := by simpa only [hg,y] using decode_moebius_translates_exactly b hp g
  have hy : ∑ t,y t=0 := by simpa only [mul_zero] using
    (unique_signal_from_moebius_translates_iff b hp 0 y).mp hr
  let R := univ.erase r
  have he := sum_erase_add univ y (mem_univ r)
  rw [hy] at he
  have hneg : y r = -(∑ t ∈ R,y t) := by
    change (∑ t ∈ R,y t) + y r = 0 at he
    linear_combination he
  have hbound : ‖y r‖^2 ≤ (R.card:ℝ)*∑ t ∈ R,‖y t‖^2 := by
    rw [hneg,norm_neg]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le R y) 2).trans
      (sq_sum_le_card_mul_sum_sq (s:=R) (f:=fun t => ‖y t‖))
  have hc : (R.card:ℝ)+1=p := by
    have hn := card_erase_add_one (mem_univ r)
    rw [card_univ,ZMod.card] at hn
    exact_mod_cast hn
  have hall : (∑ t,‖y t‖^2) ≤ (p:ℝ)*∑ t ∈ R,‖y t‖^2 := by
    rw [←sum_erase_add univ (fun t => ‖y t‖^2) (mem_univ r),←hc,add_mul,one_mul]
    linarith only [hbound]
  exact (prime_moebius_reconstruction_energy_bound hp b g hg).trans
    ((mul_le_mul_of_nonneg_left hall (inverse_bound_nonneg b)).trans_eq (by ring))

#print axioms one_le_prime_moebius_frequency_product
#print axioms selected_prime_moebius_frequency_product
#print axioms prime_moebius_mode_lower
#print axioms prime_moebius_reconstruction_energy_bound
#print axioms prime_moebius_energy_after_one_erasure
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
