import GaloisForLFunctions.GaloisTheoryOfZeros.TheArithmeticClassesOfAdditiveZeroRelations
import GaloisForLFunctions.HTGeometry.AlgebraicClosureAlgClosed
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rational independence of the prime-radical area weights

For prime p, the real p-th roots of 1,…,W are rationally independent
when W < 2^p. No two of these integers have ratio a rational p-th power.
Adjoining a primitive p-th root of unity preserves this distinction
because the cyclotomic degree is p−1. The radical characters then
separate the individual summands. The first dependence occurs at 2^p.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Two positive p-th-power-free integers in the same rational power
class coincide. The reduced numerator and denominator must both have magnitude one. -/
theorem power_free_ratio_rigid {m n p : ℕ} (hp : 0<p) (hm : 0 < m) (hn : 0<n)
    (hm' : ∀ a : ℕ, a^p ∣ m → a<2) (hn' : ∀ a : ℕ, a^p ∣ n → a<2)
    (q : ℚ) (hq : q^p=(m:ℚ)/n) : m=n := by
  have hqden : (q.num:ℚ)=q*(q.den:ℚ) :=
    (div_eq_iff (Nat.cast_ne_zero.mpr q.den_ne_zero)).mp q.num_div_den
  have qh : q^p*(n:ℚ)=(m:ℚ) := (eq_div_iff (Nat.cast_ne_zero.mpr hn.ne')).mp hq
  have hrat : (q.num:ℚ)^p*(n:ℚ)=(m:ℚ)*(q.den:ℚ)^p := by
    rw [hqden,mul_pow,mul_right_comm,qh]
  have hint : q.num^p*(n:ℤ)=(m:ℤ)*(q.den:ℤ)^p := by exact_mod_cast hrat
  have h := congrArg Int.natAbs hint
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at h
  have cop := (q.reduced.pow_left p).pow_right p
  have hnum : q.num.natAbs^p ∣ m := cop.dvd_of_dvd_mul_right ⟨n,h.symm⟩
  have hden : q.den^p ∣ n := cop.symm.dvd_of_dvd_mul_left ⟨m,h.trans (Nat.mul_comm ..)⟩
  have hden1 : q.den=1 := by have := hn' _ hden; have := q.den_pos; omega
  have hnum1 : q.num.natAbs=1 := by
    have hsmall := hm' _ hnum
    have hnz : q.num.natAbs≠0 := fun he => by
      rw [he,zero_pow hp.ne',zero_mul,hden1,one_pow,mul_one] at h
      exact hm.ne' h.symm
    omega
  simpa only [hden1,hnum1,one_pow,one_mul,mul_one] using h.symm

/-- In lowest terms both numerator and denominator of a nontrivial
rational p-th power cannot lie strictly below 2^p. -/
theorem small_rational_power_ratio {m n p : ℕ} (hp : 0<p) (hm : 0 < m) (hn : 0<n)
    (hm' : m<2^p) (hn' : n<2^p) (q : ℚ) (hq : q^p=(m:ℚ)/n) : m=n := by
  have hb {a b : ℕ} (hpos : 0<b) (hsmall : b<2^p) (hd : a^p ∣ b) : a<2 := by
    by_contra! ha
    exact hsmall.not_ge ((Nat.pow_le_pow_left ha p).trans (Nat.le_of_dvd hpos hd))
  exact power_free_ratio_rigid hp hm hn (fun _ => hb hm hm') (fun _ => hb hn hn') q hq

private theorem rational_cyclotomic_extension (p : ℕ) [NeZero p] :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) := by
  letI : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne p)⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

/-- The p-th power classes of rational numbers remain distinct after
adjoining the p-th roots of unity. The cyclotomic field has degree p−1. -/
theorem rational_power_classes_survive_cyclotomic {p : ℕ} (hp : p.Prime) (a : ℚ) :
    (∃ x : CyclotomicField p ℚ, x^p=(a:CyclotomicField p ℚ)) ↔ ∃ q : ℚ, q^p=a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI := rational_cyclotomic_extension p
  constructor
  · rintro ⟨x,hx⟩
    by_contra! hno
    have hI : Irreducible (X^p-C a) := X_pow_sub_C_irreducible_of_prime hp hno
    have he : aeval x (X^p-C a)=0 := by
      rw [map_sub,map_pow,aeval_X,aeval_C,sub_eq_zero]
      exact hx
    have hmin := minpoly.eq_of_irreducible_of_monic hI he (monic_X_pow_sub_C a hp.ne_zero)
    have hdeg := minpoly.natDegree_le (A:=ℚ) x
    rw [←hmin,natDegree_X_pow_sub_C,IsCyclotomicExtension.finrank (n:=p) (CyclotomicField p ℚ)
      (cyclotomic.irreducible_rat hp.pos),Nat.totient_prime hp] at hdeg
    exact (Nat.sub_lt hp.pos Nat.zero_lt_one).not_ge hdeg
  · rintro ⟨q,hq⟩
    exact ⟨q,by exact_mod_cast hq⟩

private def radicalCharacter {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x : L) (hx : x≠0)
    (a : K) (ha : x^p=algebraMap K L a) : (L ≃ₐ[K] L) →* L := by
  let χ (σ : L ≃ₐ[K] L) := σ x/x
  have hroot (σ : L ≃ₐ[K] L) : χ σ^p=1 := by
    dsimp only [χ]
    rw [div_pow,←map_pow,ha,σ.commutes,div_self]
    exact ha ▸ pow_ne_zero p hx
  have hfixed (σ τ : L ≃ₐ[K] L) : σ (χ τ)=χ τ := by
    obtain ⟨i,_,hi⟩ := (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one (hroot τ)
    rw [←hi,map_pow,σ.commutes]
  refine { toFun := χ, map_one' := div_self hx, map_mul' := ?_ }
  intro σ τ
  have ht : τ x=χ τ*x := (div_mul_cancel₀ _ hx).symm
  change σ (τ x)/x=χ σ*χ τ
  rw [ht,map_mul,hfixed]
  dsimp only [χ]
  ring

private theorem independent_radical_values {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (b : ι → L) (a : ι → K) (hb : ∀ i, b i≠0) (hp : ∀ i, b i^p=algebraMap K L (a i))
    (hd : ∀ i j, i≠j → ∀ v : K, v^p≠a i/a j) : LinearIndependent K b := by
  classical
  let χ (i : ι) := radicalCharacter hζ (b i) (hb i) (a i) (hp i)
  have hact (σ : L ≃ₐ[K] L) (i : ι) : σ (b i)=χ i σ*b i := (div_mul_cancel₀ _ (hb i)).symm
  have hinj : Function.Injective χ := by
    intro i j he
    by_contra hne
    have hfix (σ : L ≃ₐ[K] L) : σ (b i/b j)=b i/b j := by
      have hh : σ (b i)/b i=σ (b j)/b j := DFunLike.congr_fun he σ
      rw [map_div₀]
      exact (div_eq_div_iff ((_root_.map_ne_zero σ).mpr (hb j)) (hb j)).mpr
        (by linear_combination (div_eq_div_iff (hb i) (hb j)).mp hh)
    obtain ⟨v,hv⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b i/b j)).mpr hfix
    apply hd i j hne v
    apply (algebraMap K L).injective
    rw [map_pow,hv,div_pow,hp,hp,map_div₀]
  apply linearIndependent_iff'.mpr
  intro S c h i hi
  simp only [Algebra.smul_def] at h
  have hs := GaloisTheoryOfZeros.eigenvector_relation_component b χ hact S c h (χ i)
  have hF : S.filter (fun j => χ j=χ i)={i} := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_singleton,hinj.eq_iff]
    exact ⟨And.right,fun he => ⟨he ▸ hi,he⟩⟩
  rw [hF,Finset.sum_singleton] at hs
  exact (algebraMap K L).injective (by simpa only [map_zero] using (mul_eq_zero.mp hs).resolve_right (hb i))

section
variable {p : ℕ}
local notation "RadicalBase" => CyclotomicField p ℚ

/-- Distinct power classes over the cyclotomic field give independent
real radical weights of any positive degree. -/
theorem independent_cyclotomic_radical_weights {ι : Type*} (hp : 0<p)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hclasses : ∀ i j, i≠j → ∀ v : CyclotomicField p ℚ, v^p≠(m i:CyclotomicField p ℚ)/m j) :
    LinearIndependent ℚ (fun i => (m i:ℝ)^((p:ℝ)⁻¹)) := by
  classical
  letI : NeZero p := ⟨hp.ne'⟩
  letI := rational_cyclotomic_extension p
  letI : Algebra RadicalBase ℂ := (IsAlgClosed.lift : RadicalBase →ₐ[ℚ] ℂ).toRingHom.toAlgebra
  let A := algebraicClosure RadicalBase ℂ
  letI : IsAlgClosure RadicalBase A := ⟨HTGeometry.algebraicClosure_isAlgClosed RadicalBase ℂ,inferInstance⟩
  letI : IsGalois RadicalBase A := ⟨⟩
  let w (i : ι) : ℝ := (m i:ℝ)^((p:ℝ)⁻¹)
  have hw (i : ι) : ((w i:ℂ)^p)=(m i:ℂ) := by
    exact_mod_cast Real.rpow_inv_natCast_pow (Nat.cast_nonneg (m i) : (0:ℝ) ≤ m i) hp.ne'
  let b (i : ι) : A := ⟨(w i:ℂ),mem_algebraicClosure_iff.mpr
    ((IsIntegral.of_pow (R:=RadicalBase) hp (by
      rw [hw]
      rw [← map_natCast (algebraMap RadicalBase ℂ) (m i)]
      exact isIntegral_algebraMap)).isAlgebraic)⟩
  have hpow (i : ι) : b i^p=algebraMap RadicalBase A (m i:RadicalBase) := by
    rw [map_natCast]
    exact Subtype.ext (hw i)
  have hne (i : ι) : b i≠0 := by
    intro he
    have h := hpow i
    rw [he,zero_pow hp.ne',map_natCast] at h
    exact (Nat.cast_ne_zero.mpr (hm i).ne') h.symm
  have hI := independent_radical_values (IsCyclotomicExtension.zeta_spec p ℚ RadicalBase) b
    (fun i => (m i:RadicalBase)) hne hpow hclasses
  apply linearIndependent_iff'.mpr
  intro S c h i hi
  have hh : ∑ k ∈ S, ((c k:RadicalBase) • b k)=0 := by
    apply (algebraMap A ℂ).injective
    have he (k : ι) : algebraMap A ℂ (b k)=(w k:ℂ) := rfl
    simp only [Algebra.smul_def,map_sum,map_mul,map_zero,map_ratCast,he]
    simp only [Rat.smul_def] at h
    exact_mod_cast h
  have hc := linearIndependent_iff'.mp hI S (fun k => (c k:RadicalBase)) hh i hi
  exact_mod_cast hc

end

/-- Real roots from distinct rational p-th power classes are linearly
independent, with no limit on the size or number of the radicands. -/
theorem independent_prime_radical_classes {ι : Type*} {p : ℕ} (hp : p.Prime)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hd : ∀ i j, i≠j → ∀ q : ℚ, q^p≠(m i:ℚ)/m j) :
    LinearIndependent ℚ (fun i => (m i:ℝ)^((p:ℝ)⁻¹)) := by
  apply independent_cyclotomic_radical_weights hp.pos m hm
  intro i j hne v he
  obtain ⟨q,hq⟩ := (rational_power_classes_survive_cyclotomic hp ((m i:ℚ)/m j)).mp
    ⟨v,by simpa only [Rat.cast_div,Rat.cast_natCast] using he⟩
  exact hd i j hne q hq

/-- The first W positive prime radicals are rationally independent up
to the sharp first collision at the radicand 2^p. -/
theorem independent_prime_radical_weights {p W : ℕ} (hp : p.Prime) (hW : W<2^p) :
    LinearIndependent ℚ (fun i : Fin W => ((i.val+1:ℕ):ℝ)^((p:ℝ)⁻¹)) := by
  apply independent_prime_radical_classes hp (fun i : Fin W => i.val+1) (fun i => Nat.succ_pos _)
  intro i j hne q hq
  exact hne (Fin.ext (Nat.succ.inj (small_rational_power_ratio hp.pos (Nat.succ_pos _) (Nat.succ_pos _)
    ((Nat.succ_le_of_lt i.isLt).trans_lt hW) ((Nat.succ_le_of_lt j.isLt).trans_lt hW) q hq)))

/-- The next radicand gives a dependence with radicand one. -/
theorem prime_radical_first_collision {p : ℕ} (hp : 0<p) :
    ((2^p:ℕ):ℝ)^((p:ℝ)⁻¹) = 2*(1:ℝ)^((p:ℝ)⁻¹) := by
  rw [Nat.cast_pow,Real.one_rpow,mul_one]
  exact Real.pow_rpow_inv_natCast (by norm_num) hp.ne'

#print axioms small_rational_power_ratio
#print axioms power_free_ratio_rigid
#print axioms rational_power_classes_survive_cyclotomic
#print axioms independent_cyclotomic_radical_weights
#print axioms independent_prime_radical_classes
#print axioms independent_prime_radical_weights
#print axioms prime_radical_first_collision
end GaloisForLFunctions.ExceptionalLayerTheory
