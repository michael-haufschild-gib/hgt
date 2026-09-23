import GaloisForLFunctions.RHTower.MobiusDivisorSmallCoreInteractions

/-!
# Quotient-local budgets for actual prime-merger gains

The copied child field depends only on processed primes below its adjacent
quotient cutoffs. Its square energy is supported on product-born cofactors.
Pairing that source-local budget with the current full parent energy removes
dependence on the number of other processed primes from the gain estimate.
No orientation, reserve, or successor-selection hypothesis is assumed.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

private lemma product_count (T : Finset (Finset ℕ)) (N : ℕ)
    (hT : ∀ R∈T,∀ p∈R,p.Prime) :
    (T.filter (fun R => (∏ p∈R,p)≤N)).card≤N := by
  let S := T.filter (fun R => (∏ p∈R,p)≤N)
  have hm : Set.MapsTo (fun R : Finset ℕ => ∏ p∈R,p) (↑S) (↑(Icc 1 N)) := by
    intro R hR
    exact mem_Icc.mpr ⟨prod_pos (fun p hp => (hT R (mem_filter.mp hR).1 p hp).pos),
      (mem_filter.mp hR).2⟩
  have hi : Set.InjOn (fun R : Finset ℕ => ∏ p∈R,p) (↑S) := by
    intro R hR V hV he
    have h := congrArg Nat.primeFactors he
    simpa only [Nat.primeFactors_prod (hT R (mem_filter.mp hR).1),
      Nat.primeFactors_prod (hT V (mem_filter.mp hV).1)] using h
  simpa [S] using card_le_card_of_injOn _ hm hi

private lemma amplitude_square (M k : ℕ) :
    ((3/5:ℝ)*2^k*Real.sqrt M)^(2 : ℕ)=(9/25:ℝ)*4^k*(M:ℝ) := by
  have hp : ((2:ℝ)^k)^(2 : ℕ)=4^k := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [mul_pow,mul_pow,hp,Real.sq_sqrt (Nat.cast_nonneg M)]
  ring

/-- The entire prime-containing child energy has a small-core budget,
including every sign defect and the exact clipped product support. -/
theorem sum_mobiusDivisorPrimeFibre_sq_le_small_core
    (M N : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime) {p : ℕ}
    (hp : p.Prime) (hpP : p∉P) (hN : M/p+1≤N) :
    (∑ R∈((mobiusDivisorSelectionPrimes M).erase p).powerset,
      (mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ))≤
        (9/25:ℝ)*4^((P.filter (fun r => r<N)).card-1)*(M:ℝ)*((M-1)/p:ℕ) := by
  let T := ((mobiusDivisorSelectionPrimes M).erase p).powerset
  let S := P.filter (fun r => r<N)
  let H := (3/5:ℝ)*2^(S.card-1)*Real.sqrt M
  let A := T.filter (fun R => (∏ r∈R,r)≤(M-1)/p)
  have hprime (R : Finset ℕ) (hR : R∈T) : ∀ r∈R,r.Prime := by
    intro r hr
    exact (mem_filter.mp (mem_erase.mp (mem_powerset.mp hR hr)).2).2
  have hpR (R : Finset ℕ) (hR : R∈T) : p∉R :=
    fun h => (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hz (R : Finset ℕ) (hR : R∈T) (hn : R∉A) :
      mobiusDivisorSelectionFibre M P (insert p R)=0 := by
    have hn' : (M-1)/p<∏ r∈R,r := by simpa [A,hR] using hn
    have hm := (Nat.div_lt_iff_lt_mul hp.pos).mp hn'
    rw [Nat.mul_comm] at hm
    apply mobiusDivisorSelectionFibre_eq_zero_of_le_product
    rw [prod_insert (hpR R hR)]
    omega
  have he : (∑ R∈T,(mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ))=
      ∑ R∈A,(mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ) := by
    symm
    exact sum_subset (filter_subset _ _) (fun R hR hn => by rw [hz R hR hn]; ring)
  have hb (R : Finset ℕ) (hR : R∈T) :
      (mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ)≤H^(2 : ℕ) := by
    rw [mobiusDivisorSelectionFibre_partner_filter_cutoff M N P R hp hpP (hpR R hR) hN]
    have h := abs_mobiusDivisorSelectionFibre_le_source_amplitude M S (insert p R)
      (fun r hr => hP r (mem_filter.mp hr).1) (by simpa using And.intro hp (hprime R hR))
    change |mobiusDivisorSelectionFibre M S (insert p R)|≤H at h
    simpa only [← pow_two,sq_abs] using
      mul_le_mul h h (abs_nonneg _) ((abs_nonneg _).trans h)
  change (∑ R∈T,_)≤_
  rw [he]
  calc
    _ ≤ ∑ _R∈A,H^(2 : ℕ) := sum_le_sum (fun R hR => hb R (mem_filter.mp hR).1)
    _ = (A.card:ℝ)*H^(2 : ℕ) := by simp
    _ ≤ (((M-1)/p:ℕ):ℝ)*H^(2 : ℕ) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast product_count T ((M-1)/p) hprime) (sq_nonneg H)
    _ = _ := by dsimp [H,S]; rw [amplitude_square]; ring

/-- Squared signed gain is controlled by current actual energy and the
small-prime quotient core, with no full processed-cardinality factor. -/
theorem sq_mobiusDivisorSelectionEnergy_insert_le_small_core
    (M N : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime) {p : ℕ}
    (hp : p.Prime) (hpM : p<M) (hpP : p∉P) (hN : M/p+1≤N) :
    (mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P)^(2 : ℕ)≤
      (36/25:ℝ)*4^((P.filter (fun r => r<N)).card-1)*(M:ℝ)*((M-1)/p:ℕ)*
        mobiusDivisorSelectionEnergy M P := by
  let T := ((mobiusDivisorSelectionPrimes M).erase p).powerset
  let f := mobiusDivisorSelectionFibre M P
  let g := fun R => mobiusDivisorSelectionFibre M P (insert p R)
  have hcs := sum_mul_sq_le_sq_mul_sq T f g
  have hf := sum_mobiusDivisorSelectionFibre_sq_le_energy M P T
  have hg := sum_mobiusDivisorPrimeFibre_sq_le_small_core M N P hP hp hpP hN
  have hQ : 0 ≤ mobiusDivisorSelectionEnergy M P :=
    (sum_nonneg (fun R (_hR : R∈T) => sq_nonneg (f R))).trans hf
  have hb := mul_le_mul hf hg (sum_nonneg (fun R (_hR : R∈T) => sq_nonneg (g R))) hQ
  rw [mobiusDivisorSelectionEnergy_insert_cross hp M P hpM hpP,mul_pow]
  change (2:ℝ)^(2 : ℕ)*(∑ R∈T,f R*g R)^(2 : ℕ)≤_
  norm_num only [show (2:ℝ)^(2 : ℕ)=4 by norm_num]
  calc
    _ ≤ 4*((∑ R∈T,(f R)^(2 : ℕ))*(∑ R∈T,(g R)^(2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ 4*(mobiusDivisorSelectionEnergy M P*
        ((9/25:ℝ)*4^((P.filter (fun r => r<N)).card-1)*(M:ℝ)*((M-1)/p:ℕ))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- At fixed quotient depth, the square of the gain is O(M times current
energy), uniformly in all processed primes and their retained signs. -/
theorem sq_mobiusDivisorSelectionEnergy_insert_le_fixed_quotient
    (M L : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime) {p : ℕ}
    (hp : p.Prime) (hpM : p<M) (hpP : p∉P) (hpL : M/p≤L) :
    (mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P)^(2 : ℕ)≤
      (36/25:ℝ)*4^L*(L:ℝ)*(M:ℝ)*mobiusDivisorSelectionEnergy M P := by
  have hb := sq_mobiusDivisorSelectionEnergy_insert_le_small_core M (L+1) P hP
    hp hpM hpP (by omega)
  have hc : (P.filter (fun r => r<L+1)).card≤L+1 := by
    calc
      _ ≤ (range (L+1)).card := card_le_card
        (fun r hr => mem_range.mpr (mem_filter.mp hr).2)
      _ = _ := card_range _
  have hpow : (4:ℝ)^((P.filter (fun r => r<L+1)).card-1)≤4^L :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv : (M-1)/p≤L := (Nat.div_le_div_right (Nat.sub_le M 1)).trans hpL
  have hQ : 0 ≤ mobiusDivisorSelectionEnergy M P := by
    change 0 ≤ ∑ R∈(mobiusDivisorSelectionPrimes M).powerset,
      (mobiusDivisorSelectionFibre M P R)^(2 : ℕ)
    exact sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ (36/25:ℝ)*4^((P.filter (fun r => r<L+1)).card-1)*(M:ℝ)*((M-1)/p:ℕ)*
        mobiusDivisorSelectionEnergy M P := hb
    _ ≤ (36/25:ℝ)*4^L*(M:ℝ)*(L:ℝ)*mobiusDivisorSelectionEnergy M P := by
      apply mul_le_mul_of_nonneg_right _ hQ
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Nat.cast_nonneg M))
        (by exact_mod_cast hdiv) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end RHTower
