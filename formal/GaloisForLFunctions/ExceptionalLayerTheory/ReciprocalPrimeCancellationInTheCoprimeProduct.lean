import GaloisForLFunctions.ExceptionalLayerTheory.OrdinaryPrimeCancellationInTheSquareRootBand
import GaloisForLFunctions.ExceptionalLayerTheory.CoprimeOrdinaryPrimeFactorsAtBothWidths

/-!
# Reciprocal-prime cancellation in the coprime product

For each small complementary factor, intersect the reciprocal-prime band
with the original product window. Its sharp endpoints preserve the prime
power saving. Summing over the complementary factors still costs less
than square-root error, uniformly in the lower product endpoint.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Complementary factors above the inner cutoff with a short power range. -/
def shortComplement (D X : ℕ) : Finset ℕ :=
  Ioc D ⌊(X : ℝ)^(1/10000 : ℝ)⌋₊

/-- The reciprocal-prime interval at the divided horizon, intersected
with both product endpoints and the lower prime cutoff. -/
def reciprocalProductPrimes (D X Y v : ℕ) : Finset ℕ :=
  let T := X/v
  (Ico (max ⌈(T : ℝ)^(49999/100000 : ℝ)⌉₊ (max (2*(D+1)+1) (Y/v+1)))
    (min (⌊(T : ℝ)^(50001/100000 : ℝ)⌋₊+1) (T+1))).filter Nat.Prime

/-- Part of the coprime product in the reciprocal-prime band. -/
def reciprocalProductBand (D R X Y : ℕ) : ℝ :=
  ∑ v ∈ shortComplement D X, innerJump D v*
    ∑ p ∈ reciprocalProductPrimes D X Y v, Real.log p*centeredPrimeWeight R (X/v/p)

/-- Remaining coprime products after removing the reciprocal-prime band. -/
def outsideReciprocalBand (D R X Y : ℕ) : ℝ :=
  ∑ p ∈ (Ioc (2*(D+1)) X).filter Nat.Prime, vonMangoldt p*
    ∑ v ∈ ((Ioc (Y/p) (X/p)).filter (p.Coprime ·)) with
      ¬(v ∈ shortComplement D X ∧ p ∈ reciprocalProductPrimes D X Y v),
      innerJump D v*centeredPrimeWeight R (X/p/v)

private theorem short_scale {X a v k : ℕ} {s : ℝ}
    (hx : 1 ≤ X) (hv : 0 < v) (hk : 0 < k)
    (ha : (a : ℝ) ≤ (X : ℝ)^s) (hvx : (v : ℝ) ≤ (X : ℝ)^(1/10000 : ℝ))
    (he : s*k+1/10000 ≤ 1) :
    (a : ℝ) ≤ ((X/v : ℕ) : ℝ)^(1/(k : ℝ)) := by
  have hx₁ : (1 : ℝ) ≤ X := by exact_mod_cast hx
  have hx₀ := zero_lt_one.trans_le hx₁
  have hprod : (a : ℝ)^k*v ≤ X := by
    apply (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) ha k) hvx
      (Nat.cast_nonneg v) (by positivity)).trans
    rw [←Real.rpow_natCast _ k,←Real.rpow_mul hx₀.le,←Real.rpow_add hx₀]
    exact (Real.rpow_le_rpow_of_exponent_le hx₁ he).trans_eq (Real.rpow_one _)
  have hnat := (Nat.le_div_iff_mul_le hv).mpr (show a^k*v ≤ X by exact_mod_cast hprod)
  have hreal : (a : ℝ)^k ≤ (X/v : ℕ) := by exact_mod_cast hnat
  have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  calc (a : ℝ) = ((a : ℝ)^k)^(1/(k : ℝ)) := by
          rw [←Real.rpow_natCast _ k,←Real.rpow_mul (Nat.cast_nonneg a),mul_one_div_cancel hk₀,Real.rpow_one]
       _ ≤ _ := Real.rpow_le_rpow (by positivity) hreal (by positivity)

private theorem complement_size {D X v : ℕ} (hv : v ∈ shortComplement D X) :
    D < v ∧ (v : ℝ) ≤ (X : ℝ)^(1/10000 : ℝ) := by
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hv
  exact ⟨hl,(by exact_mod_cast hu : (v : ℝ) ≤ (⌊(X : ℝ)^(1/10000 : ℝ)⌋₊ : ℕ)).trans
    (Nat.floor_le (by positivity))⟩

/-- Every prime in this window exceeds its complementary factor. -/
theorem reciprocal_product_prime_gt {D X Y v p : ℕ} (hD : 1 ≤ D) (hX : 1 ≤ X)
    (hv : v ∈ shortComplement D X) (hp : p ∈ reciprocalProductPrimes D X Y v) : v < p := by
  let T := X/v
  obtain ⟨hd,hvX⟩ := complement_size hv
  have hv₂ : (1 : ℝ) < v := by exact_mod_cast (by omega : 1 < v)
  have hvT : (v : ℝ) ≤ (T : ℝ)^(1/4 : ℝ) :=
    short_scale (k := 4) hX (by omega) (by decide) hvX hvX (by norm_num)
  have hT : (1 : ℝ) < T := by
    by_contra! h
    have ht := Real.rpow_le_rpow (Nat.cast_nonneg T) h (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [Real.one_rpow] at ht
    exact (not_lt_of_ge (hvT.trans ht)) hv₂
  have hl := (mem_Ico.mp (mem_filter.mp hp).1).1
  have hceil : ⌈(T : ℝ)^(49999/100000 : ℝ)⌉₊ ≤ p := (le_max_left ..).trans hl
  exact_mod_cast (hvT.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hT (by norm_num : (1/4:ℝ)<49999/100000))).trans_le
    ((Nat.le_ceil _).trans (by exact_mod_cast hceil : (⌈(T : ℝ)^(49999/100000 : ℝ)⌉₊ : ℝ) ≤ p))

/-- Exact partition of the original prime-first sum, including coprimality
and the strict lower endpoint of the product interval. -/
theorem reciprocal_product_partition {D X : ℕ} (hD : 1 ≤ D) (hX : 1 ≤ X) (R Y : ℕ) :
    coprimePrimeRow D R X Y = outsideReciprocalBand D R X Y + reciprocalProductBand D R X Y := by
  let P := (Ioc (2*(D+1)) X).filter Nat.Prime
  let S (p : ℕ) := (Ioc (Y/p) (X/p)).filter (p.Coprime ·)
  let B (p v : ℕ) := v ∈ shortComplement D X ∧ p ∈ reciprocalProductPrimes D X Y v
  let f (p v : ℕ) := innerJump D v*centeredPrimeWeight R (X/p/v)
  have idx (p v : ℕ) : p ∈ P ∧ v ∈ (S p).filter (B p) ↔
      p ∈ reciprocalProductPrimes D X Y v ∧ v ∈ shortComplement D X := by
    constructor
    · rintro ⟨_,hv⟩
      exact (mem_filter.mp hv).2.symm
    · rintro ⟨hp,hv⟩
      have hprime := (mem_filter.mp hp).2
      obtain ⟨hl,hu⟩ := mem_Ico.mp (mem_filter.mp hp).1
      have hcut := (le_max_right _ _).trans hl
      have h₁ : 2*(D+1)+1 ≤ p := (le_max_left ..).trans hcut
      have h₂ : Y/v+1 ≤ p := (le_max_right ..).trans hcut
      have h₃ : p ≤ X/v := by have := hu.trans_le (min_le_right ..); omega
      have hv₀ : 0 < v := by have := (complement_size hv).1; omega
      have hlow := (Nat.div_lt_iff_lt_mul hv₀).mp (show Y/v < p by omega)
      have hhigh := (Nat.le_div_iff_mul_le hv₀).mp h₃
      have hgt := reciprocal_product_prime_gt hD hX hv hp
      have hcop := hprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hv₀ hgt)
      refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,h₃.trans (Nat.div_le_self ..)⟩,hprime⟩,
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_,?_⟩,hcop⟩,hv,hp⟩⟩
      · exact (Nat.div_lt_iff_lt_mul hprime.pos).mpr (by simpa only [Nat.mul_comm] using hlow)
      · exact (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa only [Nat.mul_comm] using hhigh)
  calc
    coprimePrimeRow D R X Y = outsideReciprocalBand D R X Y +
        ∑ p ∈ P, ∑ v ∈ (S p).filter (B p), vonMangoldt p*f p v := by
      change (∑ p ∈ P, vonMangoldt p*∑ v ∈ S p, f p v) =
        (∑ p ∈ P, vonMangoldt p*∑ v ∈ (S p).filter (fun v => ¬ B p v), f p v)+_
      rw [←sum_add_distrib]
      apply sum_congr rfl
      intro p _
      rw [←mul_sum,←mul_add,add_comm,sum_filter_add_sum_filter_not]
    _ = outsideReciprocalBand D R X Y + reciprocalProductBand D R X Y := by
      rw [sum_comm' idx]
      congr 1
      apply sum_congr rfl
      intro v _
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [vonMangoldt_apply_prime (mem_filter.mp hp).2]
      dsimp only [f]
      rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.mul_comm p v]
      ring

/-- The signed contribution from the whole short-complement band is
strictly below square-root order, uniformly in the product cutoff. -/
theorem reciprocal_product_band_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X : ℕ}, 1 ≤ X → 1 ≤ D → 1 ≤ R →
      (D : ℝ) ≤ (X : ℝ)^(1/400000 : ℝ) → (R : ℝ) ≤ (X : ℝ)^(1/400000 : ℝ) → ∀ Y : ℕ,
      |reciprocalProductBand D R X Y| ≤ K*(X : ℝ)^(4999/10000 : ℝ) := by
  obtain ⟨C,hC,hs⟩ := centered_prime_subinterval
  obtain ⟨M,hM,hm⟩ := mass_uniform
  refine ⟨(2+4*M)*C,by positivity,?_⟩
  intro D R X hX hD hR hd hr Y
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx₀ := zero_lt_one.trans_le hx
  let P (t : ℝ) := (X : ℝ)^t
  have one (t : ℝ) (ht : 0 ≤ t) : 1 ≤ P t := Real.one_le_rpow hx ht
  have mul (a b : ℝ) : P a*P b=P (a+b) := (Real.rpow_add hx₀ _ _).symm
  have hmass := hm (D+1) (Nat.succ_pos D)
  have hd₁ : ((D+1 : ℕ) : ℝ) ≤ 2*P (1/400000) := by push_cast; linarith only [hd,one (1/400000) (by norm_num)]
  have hj (v : ℕ) : |innerJump D v| ≤ (2+4*M)*P (1/400000) := by
    apply (innerJump_pointwise_bound D v).trans
    linarith only [hmass,mul_le_mul_of_nonneg_left hd₁ hM,one (1/400000) (by norm_num)]
  let A := ((2+4*M)*C)*(P (1/400000)*P (4997/10000))
  have hA : 0 ≤ A := by dsimp [A,P]; positivity
  have term (v : ℕ) (hv : v ∈ shortComplement D X) :
      |innerJump D v*∑ p ∈ reciprocalProductPrimes D X Y v,
        Real.log p*centeredPrimeWeight R (X/v/p)| ≤ A := by
    let T := X/v
    obtain ⟨hDv,hvX⟩ := complement_size hv
    have hv₀ : 0 < v := by omega
    have hvnat : v ≤ X := by
      exact_mod_cast hvX.trans ((Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1/10000:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
    have hT := (Nat.one_le_div_iff hv₀).mpr hvnat
    have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hR' : (R : ℝ) ≤ (T : ℝ)^(1/100000 : ℝ) :=
      short_scale (k := 100000) hX hv₀ (by decide) hr hvX (by norm_num)
    let L := max ⌈(T : ℝ)^(49999/100000 : ℝ)⌉₊ (max (2*(D+1)+1) (Y/v+1))
    let U := min (⌊(T : ℝ)^(50001/100000 : ℝ)⌋₊+1) (T+1)
    have hL : (T : ℝ)^(49999/100000 : ℝ) ≤ L :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _ : ⌈(T : ℝ)^(49999/100000 : ℝ)⌉₊ ≤ L))
    have hL₁ : 1 ≤ L := (Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans_le hTr) _)).trans (le_max_left ..)
    have hUn : U ≤ ⌊(T : ℝ)^(50001/100000 : ℝ)⌋₊+1 := min_le_left ..
    have hU : (U : ℝ) ≤ 2*(T : ℝ)^(50001/100000 : ℝ) := by
      have hh : (U : ℝ) ≤ (⌊(T : ℝ)^(50001/100000 : ℝ)⌋₊ : ℝ)+1 := by exact_mod_cast hUn
      linarith only [hh,Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg T) (50001/100000 : ℝ)),
        Real.one_le_rpow hTr (by norm_num : (0 : ℝ) ≤ 50001/100000)]
    have hw := hs R T L U hR hT hL₁ hR' hL hU
    have ht : (T : ℝ)^(4997/10000 : ℝ) ≤ P (4997/10000) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self X v) (by norm_num)
    rw [abs_mul]
    exact (mul_le_mul (hj v) (hw.trans (mul_le_mul_of_nonneg_left ht hC)) (abs_nonneg _)
      (by dsimp [P]; positivity)).trans_eq (by dsimp [A]; ring)
  have hcard : ((shortComplement D X).card : ℝ) ≤ P (1/10000) := by
    unfold shortComplement
    rw [Nat.card_Ioc]
    exact (by exact_mod_cast Nat.sub_le ⌊P (1/10000)⌋₊ D : ((⌊P (1/10000)⌋₊-D : ℕ) : ℝ) ≤ (⌊P (1/10000)⌋₊ : ℕ)).trans
      (Nat.floor_le (by dsimp [P]; positivity))
  unfold reciprocalProductBand
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _v ∈ shortComplement D X, A := sum_le_sum term
       _ ≤ P (1/10000)*A := by
          rw [sum_const,nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard hA
       _ = ((2+4*M)*C)*P (1/10000+(1/400000+4997/10000)) := by
          dsimp only [A]
          rw [mul,←mul (1/10000) (1/400000+4997/10000)]
          ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) (by positivity)

/-- The same centered prime band with the logarithmic cutoff of the
paired Vaughan approximation at each individual horizon. -/
def logarithmicProductBand (X : ℕ) : ℝ :=
  let D := ⌊1+Real.log X⌋₊
  reciprocalProductBand D D X (productLower D X)

private theorem logarithmic_band_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      |logarithmicProductBand X| ≤ K*(X : ℝ)^(4999/10000 : ℝ) := by
  obtain ⟨C,hC,h⟩ := reciprocal_product_band_bound
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (Sieve.eventually_const_mul_one_add_log_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1/400000) (show (0 : ℝ) < 1 by norm_num) 1)
  let S := Icc 1 ⌈Z⌉₊
  let E := ∑ n ∈ S, |logarithmicProductBand n|
  have hE : 0 ≤ E := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C+E,add_nonneg hC hE,fun X hx => ?_⟩
  by_cases hZX : Z ≤ X
  · have hd : (1 : ℝ) ≤ 1+Real.log X := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
    have hD := (Nat.one_le_floor_iff _).mpr hd
    have hu := (Nat.floor_le (zero_le_one.trans hd)).trans
      (by simpa only [one_mul,pow_one] using hZ _ hZX : 1+Real.log X ≤ (X : ℝ)^(1/400000 : ℝ))
    exact (h hx hD hD hu hu _).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE) (by positivity))
  · have hceil : X ≤ ⌈Z⌉₊ := by exact_mod_cast (le_of_not_ge hZX).trans (Nat.le_ceil Z)
    have hmem : X ∈ S := mem_Icc.mpr ⟨hx,hceil⟩
    have hle : |logarithmicProductBand X| ≤ E := single_le_sum (fun n _ => abs_nonneg (logarithmicProductBand n)) hmem
    exact hle.trans ((le_add_of_nonneg_left hC).trans (le_mul_of_one_le_right (add_nonneg hC hE)
      (Real.one_le_rpow (by exact_mod_cast hx) (by norm_num))))

/-- The portion deleted at every Vaughan width saves a fixed power below
one half, even after summing over all divided horizons. -/
theorem reciprocal_band_cofactors :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*logarithmicProductBand (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(N : ℝ)^(4999/10000 : ℝ)) := by
  obtain ⟨K,hK,h⟩ := logarithmic_band_bound
  exact ⟨K,hK,cofactor_sum_majorant _ _ (fun _ => by positivity) (fun x n _ hxn =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg x) (by exact_mod_cast hxn) (by norm_num)) hK) h⟩

/-- At both Vaughan widths only coprime products outside the reciprocal
band are needed at square-root precision up to five logarithms. -/
theorem outside_reciprocal_band_cofactors :
    let row := fun X : ℕ =>
      let D := ⌊1+Real.log X⌋₊
      outsideReciprocalBand D D X (productLower D X)
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*row (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(1+Real.log N)^5*Real.sqrt N) := by
  intro row
  obtain ⟨C,hC,h⟩ := coprime_prime_row_bound
  obtain ⟨B,hB,hb⟩ := logarithmic_band_bound
  let K := C+B
  have hK : 0 ≤ K := add_nonneg hC hB
  refine ⟨K,hK,cofactor_transfer_majorant row (fun X => K*(1+Real.log X)^5*Real.sqrt X)
    (fun X => by have := Real.log_natCast_nonneg X; positivity) ?_ ?_⟩
  · intro x n hx hxn
    have hlog := Real.log_le_log (by exact_mod_cast hx : (0 : ℝ)<x) (by exact_mod_cast hxn : (x : ℝ) ≤ n)
    have hz := Real.log_natCast_nonneg x
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1 : ℝ)) hlog) 5) hK)
      (Real.sqrt_le_sqrt (by exact_mod_cast hxn)) (Real.sqrt_nonneg _) (by have := Real.log_natCast_nonneg n; positivity)
  · intro X hx
    let H := 1+Real.log X
    let D := ⌊H⌋₊
    have hH : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
    have hD : 1 ≤ D := (Nat.one_le_floor_iff _).mpr hH
    have hd := Nat.floor_le (zero_le_one.trans hH)
    have hu := h hx hD hD hH hd hd (show Real.log X ≤ H by dsimp [H]; linarith)
    have he := reciprocal_product_partition hD hx D (productLower D X)
    have hsplit : (Chebyshev.psi X-X)-row X =
        ((Chebyshev.psi X-X)-coprimePrimeRow D D X (productLower D X))+logarithmicProductBand X := by
      rw [he]
      change _-row X = (_-(row X+logarithmicProductBand X))+logarithmicProductBand X
      ring
    have hs : (X : ℝ)^(4999/10000 : ℝ) ≤ Real.sqrt X := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num)
    have hbig : Real.sqrt X ≤ H^5*Real.sqrt X :=
      le_mul_of_one_le_left (Real.sqrt_nonneg _) (one_le_pow₀ hH)
    rw [hsplit]
    apply (abs_add_le _ _).trans
    exact (add_le_add hu ((hb X hx).trans (mul_le_mul_of_nonneg_left (hs.trans hbig) hB))).trans_eq
      (by change C*H^5*Real.sqrt X+B*(H^5*Real.sqrt X)=(C+B)*H^5*Real.sqrt X; ring)

#print axioms reciprocal_product_partition
#print axioms reciprocal_product_band_bound
#print axioms reciprocal_band_cofactors
#print axioms outside_reciprocal_band_cofactors
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
