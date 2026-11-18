import GaloisForLFunctions.ExceptionalLayerTheory.CancellationAcrossTheSquareRootProductInterval

/-!
# Removing large complementary factors from the coprime product

Subtracting the multiples of the first prime preserves bounded prefixes
of the inner weight. Above a lower complementary-factor threshold the
number of occupied quotients retains a full reciprocal prime weight.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem coprime_prefix {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime) (hlarge : 2*(D+1)<p) (T : ℕ) :
    |∑ v ∈ Ioc 0 T, (if p.Coprime v then innerJump D v else 0)| ≤ 2*(2+mass (D+1)) := by
  let a := innerJump D
  let I := Ioc 0 T
  have pos (t : ℕ) : Ioc 0 t=Icc 1 t := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  have split := sum_filter_add_sum_filter_not I (fun v => p∣v) a
  have eq : I.filter (fun v => ¬p∣v)=I.filter (p.Coprime ·) := filter_congr (fun _ _ => hp.coprime_iff_not_dvd.symm)
  rw [eq] at split
  have diff : (∑ v ∈ I with p.Coprime v, a v) =
      (∑ v ∈ I, a v)-(∑ v ∈ I with p∣v, a v) := by rw [←split]; ring
  change |∑ v ∈ I, (if p.Coprime v then a v else 0)| ≤ _
  rw [←sum_filter,diff]
  dsimp only [I,a]
  rw [sum_divisible_Ioc hp.pos,Nat.zero_div,pos,pos]
  apply (abs_sub _ _).trans
  linarith only [innerJump_prefix_bound D T,innerJump_prime_multiple_prefix_bound hD hp hlarge (T/p)]

/-- Coprime slice with a sharp upper bound on the complementary factor. -/
def cappedCoprimeSlice (D R X Y M p : ℕ) : ℝ :=
  ∑ v ∈ Ioc (Y/p) (min (X/p) M) with p.Coprime v,
    innerJump D v*centeredPrimeWeight R (X/p/v)

private theorem removed_slice {D R X Y M p : ℕ} :
    coprimeSlice D R X Y p-cappedCoprimeSlice D R X Y M p =
      ∑ v ∈ Ioc (max (Y/p) M) (X/p),
        (if p.Coprime v then innerJump D v else 0)*centeredPrimeWeight R (X/p/v) := by
  let S := (Ioc (Y/p) (X/p)).filter (p.Coprime ·)
  let f (v : ℕ) := innerJump D v*centeredPrimeWeight R (X/p/v)
  have eq := sum_filter_add_sum_filter_not S (fun v => v≤M) f
  have small : S.filter (fun v => v≤M) = (Ioc (Y/p) (min (X/p) M)).filter (p.Coprime ·) := by
    ext v; simp only [S,mem_filter,mem_Ioc,le_min_iff]; tauto
  have large : S.filter (fun v => ¬v≤M) = (Ioc (max (Y/p) M) (X/p)).filter (p.Coprime ·) := by
    ext v; simp only [S,mem_filter,mem_Ioc,max_lt_iff,not_le]; tauto
  rw [small,large] at eq
  change (∑ v ∈ S, f v)-(∑ v ∈ (Ioc (Y/p) (min (X/p) M)).filter (p.Coprime ·), f v) = _
  rw [←eq,add_sub_cancel_left,sum_filter]
  apply sum_congr rfl
  intro v _
  by_cases hv : p.Coprime v <;> simp [hv,f]

/-- For every common lower threshold the aggregate large-complement tail
costs the number of quotient fibres times the reciprocal prime mass. -/
theorem large_complement_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X F : ℕ}, 1 ≤ D → 1 ≤ R → 1 ≤ X → 2*(D+1) ≤ F → ∀ Y M : ℕ,
      |ordinaryFactorTail F X (coprimeSlice D R X Y)-ordinaryFactorTail F X (cappedCoprimeSlice D R X Y M)| ≤
        K*((D+1 : ℕ) : ℝ)*R*(X/(M+1) : ℕ)*(1+Real.log X) := by
  obtain ⟨B,hB,hm⟩ := mass_uniform
  obtain ⟨W,hW,hw⟩ := centeredPrimeWeight_uniform
  let E := Real.log 4+4
  have hE : 1 ≤ E := by dsimp [E]; linarith only [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  refine ⟨4*(2+B)*W*E,by positivity,?_⟩
  intro D R X F hD hR hx hF Y M
  let S := (Ioc F X).filter Nat.Prime
  let A := 2*(2+mass (D+1))
  let N := X/(M+1)
  let T := 2*A*(W*R)*(N : ℝ)
  have hm₀ := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have each (p : ℕ) (hpp : p ∈ S) :
      |coprimeSlice D R X Y p-cappedCoprimeSlice D R X Y M p| ≤ T/p := by
    obtain ⟨hi,prime⟩ := mem_filter.mp hpp
    have hlarge := hF.trans_lt (mem_Ioc.mp hi).1
    let L := max (Y/p) M
    have h := abs_quotient_tail_le (N := X/p) L (fun v => if p.Coprime v then innerJump D v else 0)
      (centeredPrimeWeight R) hA (fun t _ => coprime_prefix hD prime hlarge t) (hw hR)
    have hn : (X/p)/(L+1) ≤ N/p := by
      have ht : (X/p)/(L+1)*(L+1) ≤ X/p := Nat.div_mul_le_self ..
      apply (Nat.le_div_iff_mul_le prime.pos).mpr
      apply (Nat.le_div_iff_mul_le (Nat.succ_pos M)).mpr
      have hh := (Nat.le_div_iff_mul_le prime.pos).mp ht
      have hs := Nat.mul_le_mul_left ((X/p)/(L+1)) (Nat.succ_le_succ (le_max_right (Y/p) M))
      exact (show (X/p)/(L+1)*p*(M+1)=(X/p)/(L+1)*(M+1)*p by ring).le.trans
        ((Nat.mul_le_mul_right p hs).trans hh)
    have hquot : (((X/p)/(L+1) : ℕ) : ℝ) ≤ (N : ℝ)/p :=
      (by exact_mod_cast hn : (((X/p)/(L+1) : ℕ) : ℝ) ≤ (N/p : ℕ)).trans Nat.cast_div_le
    rw [removed_slice]
    exact h.trans ((mul_le_mul_of_nonneg_left hquot (by positivity)).trans_eq (by dsimp [T]; ring))
  have hmert : ∑ p ∈ S, vonMangoldt p/p ≤ E*(1+Real.log X) := by
    have sub : S ⊆ Icc 1 X := by
      intro p hp
      obtain ⟨hi,prime⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨prime.pos,(mem_Ioc.mp hi).2⟩
    apply (sum_le_sum_of_subset_of_nonneg sub
      (fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))).trans
    have hh := (abs_le.mp (Mertens.mertens_first X hx)).2
    have hs := mul_le_mul_of_nonneg_right hE (Real.log_natCast_nonneg X)
    dsimp [E] at hs ⊢; linarith only [hh,hs]
  have hd : (1 : ℝ) ≤ ((D+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos D
  have hAb : A ≤ 2*(2+B)*((D+1 : ℕ) : ℝ) := by
    dsimp [A]; linarith only [hd,hm (D+1) (Nat.succ_pos D)]
  unfold ordinaryFactorTail
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S, T*(vonMangoldt p/p) := by
            apply sum_le_sum
            intro p hp
            rw [←mul_sub,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
            exact (mul_le_mul_of_nonneg_left (each p hp) vonMangoldt_nonneg).trans_eq (by ring)
       _ ≤ T*(E*(1+Real.log X)) := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left hmert hT
       _ ≤ _ := by
            have hl := Real.log_natCast_nonneg X
            have he := mul_le_mul_of_nonneg_right hAb
              (by positivity : 0 ≤ 2*(W*R)*(N : ℝ)*(E*(1+Real.log X)))
            dsimp only [T,N] at he ⊢
            linarith only [he]

#print axioms large_complement_bound

/-- Ordinary prime row through the square-root complementary-factor cutoff. -/
def cappedProductRow (X : ℕ) : ℝ :=
  let D := ⌊1+Real.log X⌋₊
  let F := max (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
  ordinaryFactorTail F X (cappedCoprimeSlice D D X (max (productLower D X) (squareRootProductUpper X))
    ⌊Real.sqrt X⌋₊)

/-- After the whole square-root product interval has been deleted,
complementary factors also stop at the square root of the divided horizon. -/
theorem bounded_complement_cofactors :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*cappedProductRow (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(1+Real.log N)^6*Real.sqrt N) := by
  obtain ⟨C,hC,hprev⟩ := above_square_root_product_cofactors
  obtain ⟨K,hK,hcap⟩ := large_complement_bound
  let diff (X : ℕ) := aboveSquareRootProductRow X-cappedProductRow X
  have hrow (X : ℕ) (hx : 1 ≤ X) : |diff X| ≤ (2*K)*(1+Real.log X)^6*Real.sqrt X := by
    let H := 1+Real.log X
    let D := ⌊H⌋₊
    let F := max (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
    let Y := max (productLower D X) (squareRootProductUpper X)
    let M := ⌊Real.sqrt X⌋₊
    have hH : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
    have hH₀ := zero_le_one.trans hH
    have hD : 1 ≤ D := (Nat.one_le_floor_iff _).mpr hH
    have hd : (D : ℝ) ≤ H := Nat.floor_le hH₀
    have hd' : ((D+1 : ℕ) : ℝ) ≤ 2*H := by push_cast; linarith only [hd,hH]
    have hq : ((X/(M+1) : ℕ) : ℝ) ≤ Real.sqrt X := by
      apply Nat.cast_div_le.trans
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<(M+1 : ℕ))).mpr
      have hm : Real.sqrt X ≤ ((M+1 : ℕ) : ℝ) := by push_cast; exact (Nat.lt_floor_add_one _).le
      exact (Real.mul_self_sqrt (Nat.cast_nonneg X)).symm.le.trans (mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _))
    have ht := hcap hD hD hx (le_max_left (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊) Y M
    apply ht.trans
    have hh := mul_le_mul (mul_le_mul hd' hd (Nat.cast_nonneg D) (by positivity)) hq (Nat.cast_nonneg _) (by positivity)
    have hs := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (by norm_num : 3 ≤ 6)) (Real.sqrt_nonneg (X : ℝ))
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hK) hH₀
    have h₂ := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*K)
    change K*((D+1 : ℕ) : ℝ)*D*(X/(M+1) : ℕ)*H ≤ (2*K)*H^6*Real.sqrt X
    linarith only [h₁,h₂]
  refine ⟨C+2*K,by positivity,fun V W N => ?_⟩
  let g (n : ℕ) := (2*K)*(1+Real.log n)^6*Real.sqrt n
  have hg (n : ℕ) : 0 ≤ g n := by dsimp [g]; have := Real.log_natCast_nonneg n; positivity
  have mono (x n : ℕ) (hx : 1 ≤ x) (hxn : x ≤ n) : g x ≤ g n := by
    have hlog := Real.log_le_log (by exact_mod_cast hx : (0 : ℝ)<x) (by exact_mod_cast hxn : (x : ℝ)≤n)
    have hz := Real.log_natCast_nonneg x
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (add_le_add (le_refl (1 : ℝ)) hlog) 6) (by positivity)) (Real.sqrt_le_sqrt (by exact_mod_cast hxn))
      (Real.sqrt_nonneg _) (by have := Real.log_natCast_nonneg n; positivity)
  have hh := cofactor_sum_majorant diff g hg mono hrow V W N
  let I := Icc 1 (min N W)
  let w := Sieve.typeIIShort V
  have eq : cofactorCountError V W N-(∑ d ∈ I, w d*cappedProductRow (N/d)) =
      (cofactorCountError V W N-(∑ d ∈ I, w d*aboveSquareRootProductRow (N/d)))+
      (∑ d ∈ I, w d*diff (N/d)) := by
    simp only [diff,mul_sub,sum_sub_distrib]; ring
  rw [eq]
  exact (abs_add_le _ _).trans ((add_le_add (hprev V W N) hh).trans_eq (by dsimp [g]; ring))

#print axioms bounded_complement_cofactors

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
