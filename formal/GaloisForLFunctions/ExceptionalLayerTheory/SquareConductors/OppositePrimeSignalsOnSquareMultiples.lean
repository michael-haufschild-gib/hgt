import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheClippedSquareComplement
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CappedConductorPrefixes

/-!
# The prime contact on proper multiples of a square complement

At n = ℓm the cofactor cap excludes the prime ℓ from all surviving
products with cofactor ℓ²t. For t > 1 dilation preserves the inner
jump. The entire proper-multiple family is therefore a smaller capped
reading on the square mesh.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The original coprime cofactor slice at v = ℓ²t, t > 1, parametrized
by t. Both endpoints are divided with integer floors. -/
def properSquareSlice (ℓ k Y M p : ℕ) :=
  ∑ t ∈ Ioc (Y/ℓ^2/p) (min (k/ℓ^2/p) (M/ℓ^2)),
    if 1<t ∧ p.Coprime (ℓ^2*t) then
      innerJump 1 (ℓ^2*t)*centeredPrimeWeight 1 (k/(p*(ℓ^2*t))) else 0

/-- The proper multiples of a square in the square-conductor product. -/
def properSquareReading (ℓ n : ℕ) := splineCountReading n (fun k =>
  ordinaryFactorTail 4 (k/ℓ^2) (properSquareSlice ℓ k (max (productLower 1 k) (n*n.sqrt)) n))

/-- At the capped product cutoff the missing first prime ℓ cannot occur.
The original slice on proper multiples is exactly the divided slice. -/
theorem properSquareSlice_divided {ℓ p n Y : ℕ} (hℓ : ℓ.Prime) (h₄ : 4 < ℓ)
    (hp : p.Prime) (hl : ℓ ≤ n.sqrt) (hY : n*n.sqrt ≤ Y) (k : ℕ) :
    properSquareSlice ℓ k Y n p=cappedCoprimeSlice 1 1 (k/ℓ^2) (Y/ℓ^2) (n/ℓ^2) p := by
  have hd : 0 < ℓ^2 := pow_pos hℓ.pos 2
  unfold properSquareSlice cappedCoprimeSlice
  rw [sum_filter]
  apply sum_congr rfl; intro t ht
  obtain ⟨htl,htu⟩ := mem_Ioc.mp ht
  have ht₀ := (Nat.zero_le _).trans_lt htl
  have hdt : ℓ^2*t ≤ n := by
    simpa only [Nat.mul_comm t (ℓ^2)] using (Nat.le_div_iff_mul_le hd).mp (htu.trans (min_le_right ..))
  have hprod : Y < p*(ℓ^2*t) := by
    have h := (Nat.div_lt_iff_lt_mul hd).mp ((Nat.div_lt_iff_lt_mul hp.pos).mp htl)
    calc Y < t*p*ℓ^2 := h
      _ = p*(ℓ^2*t) := by ring
  have hbig : ℓ < p := by
    by_contra! h
    exact hprod.not_ge ((Nat.mul_le_mul (h.trans hl) hdt).trans (by rw [Nat.mul_comm]; exact hY))
  have hcop : ¬ p ∣ ℓ^2 := fun h => by
    rw [sq,hp.dvd_mul] at h
    exact hbig.not_ge (Nat.le_of_dvd hℓ.pos (h.elim id id))
  have hcd : p.Coprime (ℓ^2*t) ↔ p.Coprime t := by
    simp only [hp.coprime_iff_not_dvd,hp.dvd_mul,hcop,false_or]
  have hq : k/(p*(ℓ^2*t))=k/ℓ^2/p/t := by
    rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul]
    congr 1
    ring
  rw [hq]
  by_cases h₁ : t=1
  · subst h₁
    simp only [lt_irrefl,false_and,if_false,innerJump_small (D := 1) le_rfl,zero_mul,ite_self]
  · have ht₂ : 1 < t := by omega
    have hlt : ℓ*t≠1 := by have := Nat.le_mul_of_pos_right ℓ ht₀; omega
    have hg : innerJump 1 (ℓ^2*t)=innerJump 1 t := by
      rw [sq,Nat.mul_assoc,innerJump_prime_multiple le_rfl hℓ h₄ (Nat.mul_pos hℓ.pos ht₀),
        if_neg hlt,sub_zero,innerJump_prime_multiple le_rfl hℓ h₄ ht₀,if_neg h₁,sub_zero]
    simp only [ht₂,true_and,hcd,hg]

private theorem lower_mono {a b : ℕ} (hab : a≤b) : productLower 1 a≤productLower 1 b :=
  min_le_min hab (Nat.mul_le_mul_left _ (Nat.floor_mono (Real.sqrt_le_sqrt (by exact_mod_cast hab))))

/-- Exact identity once the sharp product threshold is above the moving
lower endpoint on both finite spline horizons. -/
theorem properSquareReading_exact {ℓ m : ℕ} (hℓ : ℓ.Prime) (h₄ : 4 < ℓ) (hm : 0 < m)
    (hl : ℓ ≤ (ℓ*m).sqrt)
    (hlarge : productLower 1 (splineHorizon (ℓ*m)) ≤ (ℓ*m)*(ℓ*m).sqrt)
    (hsmall : productLower 1 (splineHorizon m) ≤ ((ℓ*m)*(ℓ*m).sqrt)/ℓ^2) :
    properSquareReading ℓ (ℓ*m)=
      cappedUpperProductReading (((ℓ*m)*(ℓ*m).sqrt)/ℓ^2) ((ℓ*m)/ℓ^2) m/ℓ := by
  let f (j : ℕ) := ordinaryFactorTail 4 j (cappedCoprimeSlice 1 1 j (((ℓ*m)*(ℓ*m).sqrt)/ℓ^2) ((ℓ*m)/ℓ^2))
  have hf : f 0=0 := by simp [f,ordinaryFactorTail]
  have h₁ : properSquareReading ℓ (ℓ*m)=splineCountReading (ℓ*m) (fun k => f (k/ℓ^2)) := by
    unfold properSquareReading splineCountReading
    apply sum_congr rfl; intro k hk
    beta_reduce
    rw [max_eq_right ((lower_mono (mem_Icc.mp hk).2).trans hlarge)]
    congr 1
    unfold ordinaryFactorTail
    exact sum_congr rfl fun p hp => by rw [properSquareSlice_divided hℓ h₄ (mem_filter.mp hp).2 hl le_rfl]
  have h₂ : splineCountReading m f=cappedUpperProductReading (((ℓ*m)*(ℓ*m).sqrt)/ℓ^2) ((ℓ*m)/ℓ^2) m := by
    unfold cappedUpperProductReading splineCountReading
    apply sum_congr rfl; intro k hk
    beta_reduce
    rw [max_eq_right ((lower_mono (mem_Icc.mp hk).2).trans hsmall)]
  exact h₁.trans ((splineCountReading_square_dilation hm hℓ.pos f hf).trans (congrArg (·/(ℓ:ℝ)) h₂))

private theorem squareHorizonLower_le_linear : ∃ K : ℕ, 1≤K ∧ ∀ {j : ℕ}, 0<j →
    productLower 1 (splineHorizon j)≤K*j := by
  obtain ⟨A,hA,ha⟩ := successorSquare_window_bound
  let K := ⌈2*A⌉₊+1
  refine ⟨K,Nat.succ_pos _,fun {j} hj => ?_⟩
  have hA₀ := zero_le_one.trans hA
  have hs := Real.sqrt_le_sqrt (ha hj)
  rw [Real.sqrt_sq (mul_nonneg hA₀ (Nat.cast_nonneg j))] at hs
  let L := splineHorizon j
  have hfirst : (productLower 1 L:ℝ)≤2*Real.sqrt L := by
    apply (Nat.cast_le.mpr (min_le_right ..)).trans
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
  have hk : 2*A≤(K:ℝ) := (Nat.le_ceil (2*A)).trans (Nat.cast_le.mpr (Nat.le_succ _))
  have he : (productLower 1 L:ℝ)≤(K:ℝ)*j :=
    hfirst.trans ((mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2)).trans
      ((by ring : 2*(A*j)=2*A*j).le.trans (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg j))))
  exact_mod_cast he

/-- Both lower endpoints are inactive throughout the entire spline at
large multiples of ℓ, including the terminal cell. -/
theorem properSquareReading_eventually_exact {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) :
    ∀ᶠ m : ℕ in atTop, properSquareReading ℓ (ℓ*m)=
      cappedUpperProductReading (((ℓ*m)*(ℓ*m).sqrt)/ℓ^2) ((ℓ*m)/ℓ^2) m/ℓ := by
  obtain ⟨K,hK,hbound⟩ := squareHorizonLower_le_linear
  filter_upwards [eventually_ge_atTop ((ℓ*K)^2),eventually_ge_atTop (1:ℕ)] with m hcut hm
  let n := ℓ*m
  have hmn : m≤n := Nat.le_mul_of_pos_left m hℓ.pos
  have hs : ℓ*K≤n.sqrt := Nat.le_sqrt'.mpr (hcut.trans hmn)
  have hl : ℓ≤n.sqrt := (Nat.le_mul_of_pos_right ℓ hK).trans hs
  have hk : K≤n.sqrt := (Nat.le_mul_of_pos_left K hℓ.pos).trans hs
  apply properSquareReading_exact hℓ h₄ hm hl ((hbound (Nat.mul_pos hℓ.pos hm)).trans
    (by rw [Nat.mul_comm K]; exact Nat.mul_le_mul_left _ hk))
  apply (Nat.le_div_iff_mul_le (pow_pos hℓ.pos 2)).mpr
  calc productLower 1 (splineHorizon m)*ℓ^2 ≤ (K*m)*ℓ^2 := Nat.mul_le_mul_right _ (hbound hm)
       _ = n*(ℓ*K) := by dsimp [n]; ring
       _ ≤ n*n.sqrt := Nat.mul_le_mul_left n hs

/-- The reindexed product cutoff remains within the three-quarter range
in the squared estimate, uniformly in the dilation. -/
private theorem divided_cut_sq {ℓ m : ℕ} (hℓ : 0<ℓ) :
    (((ℓ*m*(ℓ*m).sqrt/ℓ^2:ℕ):ℝ))^2≤(m:ℝ)^3 := by
  let n := ℓ*m
  have hl : (0:ℝ)<ℓ := Nat.cast_pos.mpr hℓ
  have hs : (n.sqrt:ℝ)^2≤(ℓ:ℝ)*m := by
    exact_mod_cast (show n.sqrt^2≤n by simpa only [sq] using Nat.sqrt_le n)
  have hcut : ((n*n.sqrt/ℓ^2:ℕ):ℝ)≤(m:ℝ)*n.sqrt/ℓ := by
    apply (Nat.cast_div_le (m := n*n.sqrt) (n := ℓ^2)).trans_eq
    dsimp only [n]; push_cast; field_simp
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hcut 2).trans
  calc ((m:ℝ)*n.sqrt/ℓ)^2 = (m:ℝ)^2*(n.sqrt:ℝ)^2/(ℓ:ℝ)^2 := by ring
       _ ≤ (m:ℝ)^2*((ℓ:ℝ)*m)/(ℓ:ℝ)^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) (sq_nonneg _)
       _ = (m:ℝ)^3/ℓ := by field_simp
       _ ≤ (m:ℝ)^3 := div_le_self (by positivity) (by exact_mod_cast hℓ)

private theorem capped_at_divided_scale (r : ℕ) : ∃ K : ℝ, 0≤K ∧
    ∀ {m U M : ℕ}, 0 < m → 0<U → (U:ℝ)^2≤(m:ℝ)^3 → m≤r*(M+1) →
      |dyadicPrimeContact m-cappedUpperProductReading U M m|≤K*(conductorLog m)^6 := by
  obtain ⟨A,B,C,hA,hB,hC,h⟩ := dyadicPrimeContact_capped_upper_product_tail
  obtain ⟨J,hJ,hlog⟩ := splineHorizon_conductorLog
  refine ⟨A*J^6+2*B+C*r*J,by positivity,fun {m U M} hm hU hs hr => ?_⟩
  let L := splineHorizon m
  let H := conductorLog m
  have hH : 1≤H := conductorLog_one_le m
  have hH₀ := zero_le_one.trans hH
  have hm' : (0:ℝ)< m := Nat.cast_pos.mpr hm
  have hu' : (0:ℝ)<U := Nat.cast_pos.mpr hU
  have hL : 1+Real.log L≤J*H := hlog hm
  have hAterm := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg L)) hL 6
  rw [mul_pow] at hAterm
  have hlU : 1+Real.log (U:ℝ)≤2*H := by
    have hh := Real.log_le_log (sq_pos_of_pos hu') hs
    rw [Real.log_pow,Real.log_pow] at hh
    norm_num1 at hh
    have hg := Real.log_le_log hm' (by linarith only [hm'] : (m:ℝ)≤2*(m:ℝ))
    dsimp only [H,conductorLog]
    linarith only [hh,hg,Real.log_natCast_nonneg m]
  have hBterm : B*(1+Real.log (U:ℝ))*(U:ℝ)^2/(m:ℝ)^3 ≤ 2*B*H := by
    apply (div_le_iff₀ (pow_pos hm' 3)).mpr
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hlU hB) hs (sq_nonneg _) (by positivity)).trans_eq (by ring)
  have hCterm : C*m*(1+Real.log L)/(M+1:ℕ)≤C*r*J*H := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos M))).mpr
    have hreal : (m:ℝ)≤(r:ℝ)*(M+1:ℕ) := by exact_mod_cast hr
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hreal hC) hL
      (add_nonneg zero_le_one (Real.log_natCast_nonneg L)) (by positivity)
    exact hh.trans_eq (by ring)
  apply (h hm hU M).trans
  change A*(1+Real.log L)^6+_+_≤(A*J^6+2*B+C*r*J)*H^6
  have hh := le_self_pow₀ hH (by decide : 6≠0)
  linarith only [mul_le_mul_of_nonneg_left hAterm hA,hBterm,hCterm,
    mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*B),mul_le_mul_of_nonneg_left hh (by positivity : 0≤C*r*J)]

/-- The proper square multiples carry the positive divided prime contact
with six logarithms of error at every conductor multiple. -/
theorem properSquareReading_prime_contact {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) :
    ∃ C : ℝ, 0≤C ∧ ∀ {m : ℕ}, 0 < m →
      |(ℓ:ℝ)*properSquareReading ℓ (ℓ*m)-dyadicPrimeContact m|≤C*(conductorLog m)^6 := by
  obtain ⟨K,hK,h⟩ := capped_at_divided_scale ℓ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (properSquareReading_eventually_exact hℓ h₄)
  let B := max N ℓ
  let E (m : ℕ) := |(ℓ:ℝ)*properSquareReading ℓ (ℓ*m)-dyadicPrimeContact m|
  let F := ∑ j ∈ Icc 1 B, E j
  have hF : 0≤F := sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨F+K,add_nonneg hF hK,fun {m} hm => ?_⟩
  by_cases hbig : B≤ m
  swap
  · have hf : E m≤F := single_le_sum (fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨hm,by omega⟩)
    exact hf.trans ((le_add_of_nonneg_right hK).trans (le_mul_of_one_le_right (add_nonneg hF hK)
      (one_le_pow₀ (conductorLog_one_le m))))
  have hml : ℓ≤ m := (le_max_right ..).trans hbig
  let n := ℓ*m
  have hd : ℓ^2≤n := by simpa only [sq,n] using Nat.mul_le_mul_left ℓ hml
  have hs : ℓ≤n.sqrt := Nat.le_sqrt'.mpr hd
  have hu : 0<n*n.sqrt/ℓ^2 := (Nat.one_le_div_iff (pow_pos hℓ.pos 2)).mpr
    (hd.trans (Nat.le_mul_of_pos_right n (hℓ.pos.trans_le hs)))
  have hc : n/ℓ^2=m/ℓ := by dsimp [n]; rw [sq,←Nat.div_div_eq_div_mul,Nat.mul_div_cancel_left _ hℓ.pos]
  have hr : m≤ℓ*(n/ℓ^2+1) := by
    rw [hc,Nat.mul_comm]
    exact ((Nat.div_lt_iff_lt_mul hℓ.pos).mp (Nat.lt_succ_self (m/ℓ))).le
  have he : (ℓ:ℝ)*properSquareReading ℓ (ℓ*m)=cappedUpperProductReading (n*n.sqrt/ℓ^2) (n/ℓ^2) m := by
    rw [hN m ((le_max_left ..).trans hbig)]
    exact (Ne.isUnit (Nat.cast_ne_zero.mpr hℓ.ne_zero : (ℓ:ℝ) ≠ 0)).mul_div_cancel _
  rw [he,abs_sub_comm]
  exact (h hm hu (divided_cut_sq hℓ.pos) hr).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hF) (by positivity))

/-- The singleton square fibre of the actual conductor cutoffs. -/
def singletonSquareReading (ℓ n : ℕ) := splineCountReading n (cappedSquareComplementRow ℓ (n*n.sqrt) n)

private theorem conductorLog_dilate {ℓ m : ℕ} (hℓ : 0<ℓ) (hm : 0< m) :
    conductorLog (ℓ*m)≤(1+Real.log ℓ)*conductorLog m := by
  have hm' : (1:ℝ)≤ m := by exact_mod_cast hm
  have hl' : (0:ℝ)<ℓ := Nat.cast_pos.mpr hℓ
  have ht : 1≤2*(m:ℝ) := by linarith only [hm']
  simp only [conductorLog,Nat.cast_mul]
  rw [show 2*((ℓ:ℝ)*m)=(ℓ:ℝ)*(2*m) by ring,Real.log_mul hl'.ne' (zero_lt_one.trans_le ht).ne']
  linarith only [mul_nonneg (Real.log_natCast_nonneg ℓ) (Real.log_nonneg ht)]

/-- The singleton retains the negative contact after imposing both actual
cutoffs, including the finitely many conductors below the cofactor cap. -/
theorem singletonSquareReading_prime_contact {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) :
    ∃ C : ℝ, 0≤C ∧ ∀ {m : ℕ}, 0 < m →
      |(ℓ:ℝ)*singletonSquareReading ℓ (ℓ*m)+dyadicPrimeContact m|≤C*(conductorLog m)^6 := by
  obtain ⟨A,hA,hclip⟩ := squareComplementRow_clip_cost
  obtain ⟨B,hB,hfull⟩ := squareComplementRow_dyadicPrimeContact hℓ h₄
  obtain ⟨J,hJ,hhor⟩ := splineHorizon_conductorLog
  let H₀ := 1+Real.log (ℓ:ℝ)
  let K := 2*(ℓ:ℝ)*A+2*B*J^6
  let E (m : ℕ) := |(ℓ:ℝ)*singletonSquareReading ℓ (ℓ*m)+dyadicPrimeContact m|
  let F := ∑ m ∈ Icc 1 ℓ, E m
  have hF : 0≤F := sum_nonneg fun _ _ => abs_nonneg _
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨F+K*H₀^6,by positivity,fun {m} hm => ?_⟩
  by_cases hlarge : ℓ≤ m
  swap
  · have hsmall : E m≤F := single_le_sum (fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨hm,by omega⟩)
    exact hsmall.trans ((le_add_of_nonneg_right (mul_nonneg hK (by positivity : 0≤H₀^6))).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (conductorLog_one_le m))))
  let n := ℓ*m
  let U := n*n.sqrt
  let H := conductorLog n
  let f := splineCountReading n (squareComplementRow ℓ)
  let g := singletonSquareReading ℓ n
  have hn : 0<n := Nat.mul_pos hℓ.pos hm
  have hM : ℓ^2≤n := by simpa only [sq,n] using Nat.mul_le_mul_left ℓ hlarge
  have h₁ : 1≤H := conductorLog_one_le n
  have hU : 0<U := Nat.mul_pos hn (Nat.sqrt_pos.mpr hn)
  have hu' : (U:ℝ)≤(n:ℝ)^2 := by exact_mod_cast (Nat.mul_le_mul_left n (Nat.sqrt_le_self n)).trans_eq (sq n).symm
  have hlog : 1+Real.log U≤2*H := by
    have hu := Real.log_le_log (Nat.cast_pos.mpr hU : (0:ℝ)<U) hu'
    rw [Real.log_pow] at hu; norm_num1 at hu
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hg := Real.log_le_log hn' (by linarith only [hn'] : (n:ℝ)≤2*n)
    dsimp only [H,conductorLog]; linarith only [hu,hg]
  have hhead : |f-g|≤2*A*H^6 := by
    apply (hclip hℓ.pos hn hU le_rfl hM).trans
    have hh := mul_le_mul_of_nonneg_left hlog hA
    linarith only [hh,mul_le_mul_of_nonneg_left (le_self_pow₀ h₁ (by decide : 6≠0)) hA]
  have hbase {j : ℕ} (hj : 0<j) (hle : j≤n) :
      (1+Real.log (splineHorizon j))^6≤J^6*H^6 := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg _))
      ((hhor hj).trans (mul_le_mul_of_nonneg_left (conductorLog_mono hj hle) hJ)) 6
  have hf : |(ℓ:ℝ)*f+dyadicPrimeContact m|≤2*B*J^6*H^6 := by
    apply (hfull hm).trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (hbase hn le_rfl) (hbase hm (Nat.le_mul_of_pos_left m hℓ.pos))) hB).trans_eq (by ring)
  have he : (ℓ:ℝ)*g+dyadicPrimeContact m=((ℓ:ℝ)*f+dyadicPrimeContact m)-ℓ*(f-g) := by ring
  change |(ℓ:ℝ)*g+dyadicPrimeContact m|≤_
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ℓ)]
  have hab : 2*B*J^6*H^6+(ℓ:ℝ)*(2*A*H^6)=K*H^6 := by dsimp only [K]; ring
  apply ((add_le_add hf (mul_le_mul_of_nonneg_left hhead (Nat.cast_nonneg ℓ))).trans_eq hab).trans
  have hgrow := pow_le_pow_left₀ (zero_le_one.trans h₁) (conductorLog_dilate hℓ.pos hm) 6
  rw [mul_pow] at hgrow
  exact (mul_le_mul_of_nonneg_left hgrow hK).trans
    (by simpa only [mul_assoc,H₀] using mul_le_mul_of_nonneg_right
          (show K*H₀^6≤F+K*H₀^6 from le_add_of_nonneg_left hF) (by positivity : 0≤(conductorLog m)^6))

/-- Removing the singleton together with its proper multiples at every
aligned conductor costs only a cubic times six logarithms through all N. -/
theorem aligned_square_multiples_prefix {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |∑ m ∈ Icc 1 (N/ℓ), ((ℓ:ℝ)*m)^2*
      (properSquareReading ℓ (ℓ*m)+singletonSquareReading ℓ (ℓ*m))|≤C*(N:ℝ)^3*(conductorLog N)^6 := by
  obtain ⟨A,hA,ha⟩ := properSquareReading_prime_contact hℓ h₄
  obtain ⟨B,hB,hb⟩ := singletonSquareReading_prime_contact hℓ h₄
  refine ⟨A+B,add_nonneg hA hB,fun N => ?_⟩
  have hrow (m : ℕ) (hm : m∈Icc 1 (N/ℓ)) :
      |((ℓ:ℝ)*m)^2*(properSquareReading ℓ (ℓ*m)+singletonSquareReading ℓ (ℓ*m))| ≤
        (N:ℝ)^2*((A+B)*(conductorLog N)^6) := by
    obtain ⟨hpos,hupper⟩ := mem_Icc.mp hm
    have hnm : ℓ*m≤N := by simpa only [Nat.mul_comm m ℓ] using (Nat.le_div_iff_mul_le hℓ.pos).mp hupper
    have hℓ' : (1:ℝ)≤ℓ := by exact_mod_cast hℓ.pos
    let P := properSquareReading ℓ (ℓ*m)
    let S := singletonSquareReading ℓ (ℓ*m)
    have he : (ℓ:ℝ)*(P+S)=(ℓ*P-dyadicPrimeContact m)+(ℓ*S+dyadicPrimeContact m) := by ring
    have hcomb : |P+S|≤(A+B)*(conductorLog m)^6 := by
      calc |P+S| ≤ (ℓ:ℝ)*|P+S| := le_mul_of_one_le_left (abs_nonneg _) hℓ'
           _ = |(ℓ:ℝ)*(P+S)| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ℓ)]
           _ ≤ _ := by rw [he]; exact (abs_add_le _ _).trans ((add_le_add (ha hpos) (hb hpos)).trans_eq (by ring))
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hnm : (ℓ:ℝ)*m≤N) 2)
      (hcomb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (conductorLog_one_le m))
        (conductorLog_mono hpos (hupper.trans (Nat.div_le_self ..))) 6) (add_nonneg hA hB))) (abs_nonneg _) (sq_nonneg _)
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hrow).trans _)
  rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.div_le_self N ℓ) : ((N/ℓ:ℕ):ℝ)≤N) (by positivity)).trans_eq (by ring)

/-- Cofactors of the actual capped row that are not divisible by ℓ². -/
def squareCoprimeCofactorReading (ℓ n : ℕ) := splineCountReading n (fun k => ordinaryFactorTail 4 k (fun p =>
  ∑ v ∈ Ioc (max (productLower 1 k) (n*n.sqrt)/p) (min (k/p) n) with ¬ ℓ^2 ∣ v,
    if p.Coprime v then innerJump 1 v*centeredPrimeWeight 1 (k/p/v) else 0))

/-- At one first prime the capped slice splits into the cofactors prime to
ℓ², the square ℓ² itself and its proper multiples, with the same endpoints. -/
theorem cappedCoprimeSlice_square_split {ℓ p : ℕ} (hℓ : 0 < ℓ) (k Y M : ℕ) :
    cappedCoprimeSlice 1 1 k Y M p =
      (∑ v ∈ Ioc (Y/p) (min (k/p) M) with ¬ ℓ^2 ∣ v,
        if p.Coprime v then innerJump 1 v*centeredPrimeWeight 1 (k/p/v) else 0) +
      (if 1 ∈ Ioc (Y/ℓ^2/p) (min (k/ℓ^2/p) (M/ℓ^2)) ∧ p.Coprime (ℓ^2) then
          innerJump 1 (ℓ^2)*centeredPrimeWeight 1 (k/ℓ^2/p) else 0) +
      properSquareSlice ℓ k Y M p := by
  have hd : 0 < ℓ^2 := pow_pos hℓ 2
  have hdiv (x : ℕ) : x/p/ℓ^2 = x/ℓ^2/p := by
    rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.mul_comm]
  have hmin (a b : ℕ) : min a b/ℓ^2 = min (a/ℓ^2) (b/ℓ^2) := by
    rcases le_total a b with h|h
    · rw [min_eq_left h,min_eq_left (Nat.div_le_div_right h)]
    · rw [min_eq_right h,min_eq_right (Nat.div_le_div_right h)]
  let g (v : ℕ) : ℝ := if p.Coprime v then innerJump 1 v*centeredPrimeWeight 1 (k/p/v) else 0
  have hsplit : cappedCoprimeSlice 1 1 k Y M p =
      (∑ v ∈ Ioc (Y/p) (min (k/p) M) with ¬ ℓ^2 ∣ v, g v) +
        ∑ v ∈ Ioc (Y/p) (min (k/p) M) with ℓ^2 ∣ v, g v := by
    rw [add_comm,sum_filter_add_sum_filter_not,cappedCoprimeSlice,sum_filter]
  have hterm (t : ℕ) (ht : t ∈ Ioc (Y/ℓ^2/p) (min (k/ℓ^2/p) (M/ℓ^2))) : g (ℓ^2*t) =
      (if t = 1 then (if p.Coprime (ℓ^2) then innerJump 1 (ℓ^2)*centeredPrimeWeight 1 (k/ℓ^2/p) else 0)
        else 0) +
      (if 1 < t ∧ p.Coprime (ℓ^2*t) then
        innerJump 1 (ℓ^2*t)*centeredPrimeWeight 1 (k/(p*(ℓ^2*t))) else 0) := by
    have ht₀ : 0 < t := (Nat.zero_le _).trans_lt (mem_Ioc.mp ht).1
    have hq : k/p/(ℓ^2*t) = k/(p*(ℓ^2*t)) := Nat.div_div_eq_div_mul ..
    by_cases h₁ : t = 1
    · subst h₁
      simp only [g,mul_one,lt_irrefl,false_and,if_false,add_zero,eq_self_iff_true,if_true,↓reduceIte,hdiv]
    · have ht₂ : 1 < t := by omega
      simp only [g,h₁,ht₂,true_and,if_false,zero_add,hq]
  rw [hsplit,sum_divisible_Ioc hd,hmin,hdiv,hdiv,sum_congr rfl hterm,sum_add_distrib,sum_ite_eq',
    ite_and,add_assoc]
  all_goals rfl

private theorem cappedRow_square_split {ℓ : ℕ} (hℓ : 0 < ℓ) (U M k : ℕ) :
    ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) M) =
      ordinaryFactorTail 4 k (fun p => ∑ v ∈ Ioc (max (productLower 1 k) U/p) (min (k/p) M) with ¬ ℓ^2 ∣ v,
        if p.Coprime v then innerJump 1 v*centeredPrimeWeight 1 (k/p/v) else 0) +
      cappedSquareComplementRow ℓ U M k +
      ordinaryFactorTail 4 (k/ℓ^2) (properSquareSlice ℓ k (max (productLower 1 k) U) M) := by
  have hd : 0 < ℓ^2 := pow_pos hℓ 2
  have hpad : ordinaryFactorTail 4 (k/ℓ^2) (properSquareSlice ℓ k (max (productLower 1 k) U) M) =
      ordinaryFactorTail 4 k (properSquareSlice ℓ k (max (productLower 1 k) U) M) :=
    unit_prime_padding (Nat.div_le_self k (ℓ^2)) _ fun p hp => by
      unfold properSquareSlice
      rw [Nat.div_eq_of_lt hp,min_eq_left (Nat.zero_le _),Ioc_eq_empty_of_le (Nat.zero_le _),sum_empty]
  have hsing : ordinaryFactorTail 4 k (fun p =>
      if 1 ∈ Ioc (max (productLower 1 k) U/ℓ^2/p) (min (k/ℓ^2/p) (M/ℓ^2)) ∧ p.Coprime (ℓ^2) then
        innerJump 1 (ℓ^2)*centeredPrimeWeight 1 (k/ℓ^2/p) else 0) = cappedSquareComplementRow ℓ U M k := by
    unfold ordinaryFactorTail cappedSquareComplementRow
    simp only [mul_ite,mul_zero,← sum_filter,filter_filter]
    by_cases hM : ℓ^2 ≤ M
    · rw [if_pos hM]
      refine sum_congr ?_ (fun p _ => by ring)
      ext p
      simp only [mem_filter,mem_Ioc,mem_Icc,le_min_iff]
      constructor
      · rintro ⟨⟨h4,-⟩,hp,⟨hlo,h1k,-⟩,hc⟩
        have hp0 := hp.pos
        have hlt : max (productLower 1 k) U < p*ℓ^2 := by
          have h := (Nat.div_lt_iff_lt_mul hp0).mp hlo
          rw [one_mul] at h
          exact (Nat.div_lt_iff_lt_mul hd).mp h
        have hle : p ≤ k/ℓ^2 := by
          have h := (Nat.le_div_iff_mul_le hp0).mp h1k
          rwa [one_mul] at h
        exact ⟨⟨hp.one_lt.le,hle⟩,⟨hp,h4,hc,(max_lt_iff.mp hlt).1⟩,(max_lt_iff.mp hlt).2⟩
      · rintro ⟨⟨-,hle⟩,⟨hp,h4,hc,hpl⟩,hU⟩
        have hp0 := hp.pos
        refine ⟨⟨h4,hle.trans (Nat.div_le_self _ _)⟩,hp,⟨?_,?_,?_⟩,hc⟩
        · rw [Nat.div_lt_iff_lt_mul hp0,one_mul,Nat.div_lt_iff_lt_mul hd]
          exact max_lt hpl hU
        · rw [Nat.le_div_iff_mul_le hp0,one_mul]
          exact hle
        · rw [Nat.le_div_iff_mul_le hd,one_mul]
          exact hM
    · rw [if_neg hM]
      refine sum_eq_zero fun p hp => absurd ?_ hM
      have h := (mem_filter.mp hp).2.2.1
      rw [mem_Ioc,le_min_iff] at h
      simpa only [one_mul] using (Nat.le_div_iff_mul_le hd).mp h.2.2
  rw [hpad,← hsing]
  unfold ordinaryFactorTail
  rw [← sum_add_distrib,← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [cappedCoprimeSlice_square_split hℓ,mul_add,mul_add]

/-- The actual capped reading splits exactly by divisibility of the cofactor
by ℓ² into the remaining class, the square ℓ² and its proper multiples. -/
theorem cappedUpperProductReading_square_split {ℓ : ℕ} (hℓ : 0 < ℓ) (n : ℕ) :
    cappedUpperProductReading (n*n.sqrt) n n =
      squareCoprimeCofactorReading ℓ n + singletonSquareReading ℓ n + properSquareReading ℓ n := by
  unfold cappedUpperProductReading squareCoprimeCofactorReading singletonSquareReading
    properSquareReading splineCountReading
  rw [← sum_add_distrib,← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  beta_reduce
  rw [← add_mul,← add_mul,cappedRow_square_split hℓ]

/-- The whole square-divisible family of the actual capped reading, summed
over the aligned conductors ℓm ≤ N, costs a cube and six logarithms. -/
theorem aligned_square_divisible_family_prefix {ℓ : ℕ} (hℓ : ℓ.Prime) (h₄ : 4 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |∑ m ∈ Icc 1 (N/ℓ), ((ℓ:ℝ)*m)^2*
      (cappedUpperProductReading ((ℓ*m)*(ℓ*m).sqrt) (ℓ*m) (ℓ*m) -
        squareCoprimeCofactorReading ℓ (ℓ*m))| ≤ C*(N:ℝ)^3*(conductorLog N)^6 := by
  obtain ⟨C,hC,h⟩ := aligned_square_multiples_prefix hℓ h₄
  refine ⟨C,hC,fun N => ?_⟩
  have he : ∀ m ∈ Icc 1 (N/ℓ), ((ℓ:ℝ)*m)^2*(cappedUpperProductReading ((ℓ*m)*(ℓ*m).sqrt) (ℓ*m) (ℓ*m) -
      squareCoprimeCofactorReading ℓ (ℓ*m)) =
      ((ℓ:ℝ)*m)^2*(properSquareReading ℓ (ℓ*m)+singletonSquareReading ℓ (ℓ*m)) := fun m _ => by
    rw [cappedUpperProductReading_square_split hℓ.pos]
    ring
  rw [sum_congr rfl he]
  exact h N

#print axioms properSquareSlice_divided
#print axioms properSquareReading_eventually_exact
#print axioms properSquareReading_prime_contact
#print axioms singletonSquareReading_prime_contact
#print axioms aligned_square_multiples_prefix
#print axioms cappedCoprimeSlice_square_split
#print axioms cappedUpperProductReading_square_split
#print axioms aligned_square_divisible_family_prefix
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
