import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.DivisorInversionOnTheReciprocalPrimeOctave
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError
import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels

/-!
# Positive weights for the reciprocal prime octave

Integrating the parity of the outer quotient over each unit interval gives
weights between zero and one, equal to one on the upper half. Grouping the
mean of the reciprocal Mangoldt errors by the true product leaves only
alternating ordinary logarithms.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Length of the part of the unit interval below an outer endpoint. -/
def octaveUnitClip (x : ℝ) : ℝ := min 1 (max 0 x)

private theorem clip_eq (x : ℝ) : octaveUnitClip x = max 0 x-max 0 (x-1) := by
  unfold octaveUnitClip
  grind

private theorem positive_average {f : ℕ → ℝ} {N : ℕ}
    (h : ∀ n : ℕ, 1 ≤ n → 0 ≤ f n ∧ f (n+1) ≤ f n) :
    0 ≤ ∑ d ∈ Icc 1 N, alternatingDivisorCoeff d * f d ∧
      ∑ d ∈ Icc 1 N, alternatingDivisorCoeff d * f d ≤ f 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using (h 1 le_rfl).1
  have H := sum_smul_eq_prefix_differences alternatingDivisorCoeff f N
  simp only [smul_eq_mul,prefix_alternatingDivisorCoeff] at H
  rw [H]
  have hp (d : ℕ) : ((d%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show d%2 ≤ 1 by omega)
  have hd (d : ℕ) (hd : d ∈ Icc 1 N) : 0 ≤ f d - f (d+1) := sub_nonneg.mpr (h d (mem_Icc.mp hd).1).2
  have hn := (h (N+1) (Nat.succ_pos _)).1
  have telescope (m : ℕ) : f (m+1)+(∑ d ∈ Icc 1 m, (f d-f (d+1)))=f 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_Icc_succ_top (show 1 ≤ m+1 by omega)]
      linarith only [ih]
  exact ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) hn)
    (sum_nonneg (fun d hd' => mul_nonneg (Nat.cast_nonneg _) (hd d hd'))),
    (add_le_add (mul_le_of_le_one_left hn (hp N))
      (sum_le_sum (fun d hd' => mul_le_of_le_one_left (hd d hd') (hp d)))).trans_eq (telescope N)⟩

/-- Parity-weighted length read at the actual terminal X. -/
def octaveParityWeight (X n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 X, alternatingDivisorCoeff d * octaveUnitClip ((X:ℝ)/d-n)

theorem octave_parity_weight_range (X n : ℕ) :
    0 ≤ octaveParityWeight X n ∧ octaveParityWeight X n ≤ 1 := by
  let f (d : ℕ) := octaveUnitClip ((X:ℝ)/d-n)
  have h := positive_average (N := X) (f := f) (fun d hd => by
    have hd0 : (0:ℝ)<d := Nat.cast_pos.mpr hd
    exact ⟨le_min (by norm_num) (le_max_left ..),min_le_min_left 1 (max_le_max_left 0
      (sub_le_sub_right (div_le_div_of_nonneg_left (Nat.cast_nonneg X) hd0
        (Nat.cast_le.mpr (Nat.le_succ d))) _))⟩)
  exact ⟨h.1,h.2.trans (min_le_left ..)⟩

/-- Every integer in the last half below X receives full weight. -/
theorem octave_parity_weight_top {n X : ℕ} (hn : n<X) (hX : X≤2*n) :
    octaveParityWeight X n = 1 := by
  have h1 : 1∈Icc 1 X := mem_Icc.mpr ⟨le_rfl,(Nat.zero_le n).trans_lt hn⟩
  have hone : alternatingDivisorCoeff 1=1 := by
    simpa only [Icc_self,sum_singleton,Nat.reduceMod,Nat.cast_one] using prefix_alternatingDivisorCoeff 1
  unfold octaveParityWeight
  rw [sum_eq_single 1]
  · rw [hone,one_mul]
    have hh : (n:ℝ)+1≤X := by exact_mod_cast hn
    simp only [octaveUnitClip,Nat.cast_one,div_one]
    grind
  · intro d hd hd'
    have hd2 : 2≤d := by have := (mem_Icc.mp hd).1; omega
    have hb := Nat.mul_le_mul_right n hd2
    have hi : (X:ℝ)/d≤n := (div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0<d))).mpr (by
      exact_mod_cast (by simpa only [Nat.mul_comm] using hX.trans hb : X≤n*d))
    simp [octaveUnitClip,max_eq_left (sub_nonpos.mpr hi)]
  · exact fun hn' => (hn' h1).elim

private def ramp (y : ℝ) : ℝ := max 0 (y-1)

private def triangularHead (X n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 X, alternatingDivisorCoeff d * max 0 ((X:ℝ)/d-n)

private theorem head_difference (X n : ℕ) :
    triangularHead X n - triangularHead X (n+1) = octaveParityWeight X n := by
  rw [triangularHead,triangularHead,octaveParityWeight,←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  rw [clip_eq,mul_sub,Nat.cast_add,Nat.cast_one,sub_sub]

private theorem head_kernel (X n : ℕ) (hn : 0<n) : triangularHead X n =
    (n:ℝ)*arithmeticKernel alternatingDivisorCoeff ramp ((X:ℝ)/n) := by
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr hn
  unfold triangularHead arithmeticKernel
  rw [Nat.floor_div_natCast,Nat.floor_natCast,mul_sum]
  let f (d : ℕ) := alternatingDivisorCoeff d * max 0 ((X:ℝ)/d-n)
  have hs : Icc 1 (X/n) ⊆ Icc 1 X := Icc_subset_Icc le_rfl (Nat.div_le_self _ _)
  have ho : ∀ d ∈ Icc 1 X, d ∉ Icc 1 (X/n) → f d=0 := by
    intro d hd hcut
    have hd0 : 0<d := (mem_Icc.mp hd).1
    have hh : X/n<d := lt_of_not_ge fun he => hcut (mem_Icc.mpr ⟨hd0,he⟩)
    have hx : (X:ℝ)/d≤n := (div_le_iff₀ (Nat.cast_pos.mpr hd0)).mpr (by
      exact_mod_cast (show X≤n*d by simpa only [Nat.mul_comm] using ((Nat.div_lt_iff_lt_mul hn).mp hh).le))
    simp only [f,max_eq_left (sub_nonpos.mpr hx),mul_zero]
  change ∑ d ∈ Icc 1 X, f d = _
  rw [←sum_subset hs ho]
  apply sum_congr rfl
  intro d hd
  dsimp only [f,ramp,smul_eq_mul]
  have hr : (n:ℝ)*((X:ℝ)/n/d-1)=(X:ℝ)/d-n := by field_simp [hn0.ne']
  rw [mul_left_comm,show (n:ℝ)*max 0 ((X:ℝ)/n/d-1)=max 0 ((X:ℝ)/d-n) by
    rw [mul_max_of_nonneg _ _ hn0.le,mul_zero,hr]]

private theorem ramp_dyadic {y : ℝ} (hy : 0≤y) : arithmeticKernel dyadicCountDifference ramp y = octaveUnitClip (y-1) := by
  unfold arithmeticKernel
  change (∑ d ∈ Icc 1 ⌊y⌋₊, ((if d=1 then (1:ℝ) else 0)-(if d=2 then 2 else 0))*ramp (y/d)) = _
  simp only [sub_mul,ite_mul,zero_mul,one_mul,sum_sub_distrib,sum_ite_eq',mem_Icc,le_rfl,true_and,
    Nat.cast_one,Nat.cast_ofNat,div_one,show 1≤(2:ℕ) by decide]
  have h1 : 1≤⌊y⌋₊ ↔ 1≤y := Nat.one_le_floor_iff y
  have h2 : 2≤⌊y⌋₊ ↔ 2≤y := by simpa using Nat.le_floor_iff (n := 2) hy
  simp only [h1,h2]
  unfold ramp octaveUnitClip
  grind

private def octaveAtom : ArithmeticFunction ℝ where
  toFun := reciprocalOctaveAtom
  map_zero' := by simp [reciprocalOctaveAtom]

/-- The ordinary reciprocal Mangoldt octave, centered by its continuous density. -/
def reciprocalOctaveError (n : ℕ) : ℝ :=
  (∑ k ∈ Ioc (n/2) n, vonMangoldt k/k)-Real.log 2

private theorem octave_prefix {n : ℕ} (hn : 0<n) :
    (∑ k ∈ Icc 1 n, reciprocalOctaveAtom k/k) = reciprocalOctaveError n := by
  have hs : Icc 1 n = Ioc 0 n := by ext d; simp only [mem_Icc,mem_Ioc]; omega
  rw [hs,octave_atom_weighted_prefix hn,reciprocalOctaveError]

/-- The positive parity mean of the centered octave equals a single
alternating logarithm sum, including both truncated endpoints. -/
theorem reciprocal_octave_parity_mean (X : ℕ) :
    (∑ n ∈ Icc 1 X, reciprocalOctaveError n*octaveParityWeight X n) =
      ∑ d ∈ Icc 1 X, parityOctaveLog d*octaveUnitClip ((X:ℝ)/d-1) := by
  have hhead : triangularHead X (X+1)=0 := by
    unfold triangularHead
    apply sum_eq_zero
    intro d hd
    have hu := div_le_self (Nat.cast_nonneg X) (Nat.one_le_cast.mpr (mem_Icc.mp hd).1 : 1≤(d:ℝ))
    rw [max_eq_left (by push_cast; linarith only [hu]),mul_zero]
  have ht := sum_smul_eq_prefix_differences (fun n : ℕ => reciprocalOctaveAtom n/n) (triangularHead X) X
  simp only [smul_eq_mul,hhead,mul_zero,zero_add,head_difference] at ht
  rw [←sum_congr rfl (fun n hn => congrArg (· * octaveParityWeight X n) (octave_prefix (mem_Icc.mp hn).1)),←ht]
  have hrow : (∑ n ∈ Icc 1 X, reciprocalOctaveAtom n/n * triangularHead X n) =
      arithmeticKernel (octaveAtom*alternatingDivisorCoeff) ramp X := by
    rw [arithmeticKernel_mul,arithmeticKernel,Nat.floor_natCast]
    apply sum_congr rfl
    intro n hn
    rw [head_kernel X n (mem_Icc.mp hn).1,smul_eq_mul,←mul_assoc,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr
      (show 0<n from (mem_Icc.mp hn).1).ne')]
    rfl
  rw [hrow,alternatingDivisorCoeff,mul_comm dyadicCountDifference,←mul_assoc,arithmeticKernel_mul,arithmeticKernel,Nat.floor_natCast]
  apply sum_congr rfl
  intro d hd
  rw [coe_mul_zeta_apply,ramp_dyadic (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),smul_eq_mul]
  exact congrArg (· * _) (reciprocal_octave_divisor_identity (mem_Icc.mp hd).1)

private theorem parity_log_factor {d : ℕ} (hd : 0<d) :
    parityOctaveLog d = alternatingDivisorCoeff d * (Real.log d-Real.log 2) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have ha := prefix_alternatingDivisorCoeff (k+1)
  rw [sum_Icc_succ_top (show 1 ≤ k+1 by omega),prefix_alternatingDivisorCoeff] at ha
  have he (h : 2 ∣ k+1) : alternatingDivisorCoeff (k+1) = -1 := by
    have h0 : (k+1)%2=0 := Nat.mod_eq_zero_of_dvd h
    have h1 : k%2=1 := by omega
    rw [h0,h1] at ha
    norm_num at ha
    linarith only [ha]
  have ho (h : ¬2 ∣ k+1) : alternatingDivisorCoeff (k+1) = 1 := by
    have h0 : (k+1)%2≠0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
    have h1 : k%2=0 := by omega
    have h2 : (k+1)%2=1 := by omega
    simp only [h1,h2] at ha
    norm_num at ha
    exact ha
  rw [parityOctaveLog,Real.log_div (Nat.cast_ne_zero.mpr hd.ne') (by norm_num : (2:ℝ)≠0)]
  by_cases h : 2 ∣ k+1
  · rw [if_pos h,he h,neg_one_mul]
  · rw [if_neg h,ho h,one_mul]

/-- The signed error in the positive mean grows at most logarithmically. -/
theorem abs_reciprocal_octave_parity_mean (X : ℕ) :
    |∑ n ∈ Icc 1 X, reciprocalOctaveError n*octaveParityWeight X n| ≤ Real.log X+Real.log 2 := by
  rw [reciprocal_octave_parity_mean]
  let u (d : ℕ) := octaveUnitClip ((X:ℝ)/d-1)
  let v (d : ℕ) := max 0 (Real.log X-Real.log d)
  have hu (d : ℕ) (hd : 1≤d) : 0≤u d ∧ u (d+1)≤u d := by
    have hd0 : (0:ℝ)<d := Nat.cast_pos.mpr hd
    exact ⟨le_min (by norm_num) (le_max_left ..),min_le_min_left 1 (max_le_max_left 0
      (sub_le_sub_right (div_le_div_of_nonneg_left (Nat.cast_nonneg X) hd0
        (Nat.cast_le.mpr (Nat.le_succ d))) _))⟩
  have hv (d : ℕ) (hd : 1≤d) : 0≤v d ∧ v (d+1)≤v d :=
    ⟨le_max_left ..,max_le_max_left 0 (sub_le_sub_left (Real.log_le_log
      (Nat.cast_pos.mpr hd) (Nat.cast_le.mpr (Nat.le_succ d))) _)⟩
  let C := Real.log X-Real.log 2
  have hX0 := Real.log_natCast_nonneg X
  have h2 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hU := positive_average (N := X) hu
  have hU1 : (∑ d ∈ Icc 1 X, alternatingDivisorCoeff d*u d) ≤ 1 := hU.2.trans (min_le_left ..)
  have hV := positive_average (N := X) (f := fun d => v d*u d) (fun d hd =>
    ⟨mul_nonneg (hv d hd).1 (hu d hd).1,mul_le_mul (hv d hd).2 (hu d hd).2
      (hu (d+1) (Nat.succ_pos _)).1 (hv d hd).1⟩)
  have hV1 : (∑ d ∈ Icc 1 X, alternatingDivisorCoeff d*(v d*u d)) ≤ Real.log X := by
    have h := hV.2
    have h₁ : v 1=Real.log X := by simp [v,max_eq_right hX0]
    rw [h₁] at h
    exact h.trans (mul_le_of_le_one_right hX0 (min_le_left ..))
  have hh (d : ℕ) (hd : d∈Icc 1 X) : parityOctaveLog d*octaveUnitClip ((X:ℝ)/d-1) =
      C*(alternatingDivisorCoeff d*u d) - alternatingDivisorCoeff d*(v d*u d) := by
    have hl := Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hd).1) (Nat.cast_le.mpr (mem_Icc.mp hd).2)
    rw [parity_log_factor (mem_Icc.mp hd).1]
    dsimp only [C,u,v]
    rw [max_eq_right (sub_nonneg.mpr hl)]
    ring
  rw [sum_congr rfl hh,sum_sub_distrib,←mul_sum,abs_le]
  let U := ∑ d ∈ Icc 1 X, alternatingDivisorCoeff d*u d
  have hun : 0≤U := hU.1
  have hu1 : U≤1 := hU1
  have hUl : 0≤Real.log X*U := mul_nonneg hX0 hun
  have hUu := mul_le_of_le_one_right hX0 hu1
  have h2l := mul_nonneg h2 hun
  have h2u := mul_le_of_le_one_right h2 hu1
  change -(Real.log X+Real.log 2)≤C*U-_ ∧ C*U-_≤Real.log X+Real.log 2
  dsimp only [C]; rw [sub_mul]
  constructor <;> linarith only [hUl,hUu,h2l,h2u,hV.1,hV1,h2]

/-- On the last half the whole absolute octave error is bounded by the
opposite sign over the prefix, for either orientation of the error. -/
theorem last_half_abs_reciprocal_octave {X : ℕ} (hX : 0<X) {ε : ℝ} (he : |ε|=1) :
    (∑ n ∈ Ico ((X+1)/2) X, |reciprocalOctaveError n|) ≤ Real.log X+Real.log 2 +
      2*∑ n ∈ Icc 1 X, max (-(ε*reciprocalOctaveError n)) 0 := by
  let S := Ico ((X+1)/2) X
  let T := Icc 1 X
  let e := reciprocalOctaveError
  let w := octaveParityWeight X
  have hs : S ⊆ T := by
    intro n hn
    obtain ⟨hl,hu⟩ := mem_Ico.mp hn
    have hstart : 1≤(X+1)/2 := (Nat.one_le_div_iff (by decide : 0<2)).mpr (Nat.succ_le_succ hX)
    exact mem_Icc.mpr ⟨hstart.trans hl,hu.le⟩
  have h₁ : (∑ n ∈ S, |e n|) ≤ ∑ n ∈ T, |e n| *w n := by
    calc _ = ∑ n ∈ S, |e n| *w n := by
           apply sum_congr rfl
           intro n hn
           obtain ⟨hl,hu⟩ := mem_Ico.mp hn
           rw [show w n=1 from octave_parity_weight_top hu (by omega),mul_one]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs fun n _ _ =>
           mul_nonneg (abs_nonneg _) (octave_parity_weight_range X n).1
  have piece (n : ℕ) : |e n| = ε*e n+2*max (-(ε*e n)) 0 := by
    have hh : |ε*e n|=|e n| := by rw [abs_mul,he,one_mul]
    rw [←hh]
    by_cases h : 0≤ε*e n
    · rw [abs_of_nonneg h,max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [abs_of_nonpos (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]; ring
  have hsign : ε*(∑ n ∈ T, e n*w n) ≤ Real.log X+Real.log 2 := by
    apply (le_abs_self _).trans
    rw [abs_mul,he,one_mul]
    exact abs_reciprocal_octave_parity_mean X
  have h₂ : (∑ n ∈ T, |e n| *w n) ≤ (∑ n ∈ T, (ε*(e n*w n)+2*max (-(ε*e n)) 0)) := by
    apply sum_le_sum
    intro n _
    rw [piece,add_mul,mul_assoc,mul_assoc]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (le_max_right _ _)
      (octave_parity_weight_range X n).2) (by norm_num : (0:ℝ)≤2))
  rw [sum_add_distrib,←mul_sum,←mul_sum] at h₂
  exact h₁.trans (h₂.trans (add_le_add hsign le_rfl))


/-- Undivided octave atoms summed through the given integer. -/
def undividedOctavePrefix (n : ℕ) : ℝ := ∑ k ∈ Ioc 0 n, reciprocalOctaveAtom k

private theorem raw_atom_value {n : ℕ} (hn : 0<n) :
    undividedOctavePrefix n = Chebyshev.psi n - 2*Chebyshev.psi (n/2:ℕ)-Real.log 2 := by
  classical
  have he : (∑ k ∈ Ioc 0 n, if 2∣k then vonMangoldt (k/2) else 0) = Chebyshev.psi (n/2 : ℕ) := by
    rw [←sum_filter,sum_divisible_Ioc (by decide : 0<2),Nat.zero_div]
    simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),Chebyshev.psi,Nat.floor_natCast]
  have hu : (∑ k ∈ Ioc 0 n, if k=1 then Real.log 2 else 0)=Real.log 2 := by
    have hmem : 1 ∈ Ioc 0 n := mem_Ioc.mpr ⟨by decide,hn⟩
    simp [hmem]
  rw [undividedOctavePrefix]
  simp only [reciprocalOctaveAtom,sum_sub_distrib,←mul_sum,he,hu]
  simp only [Chebyshev.psi,Nat.floor_natCast]

/-- The sum of the undivided atoms is determined by the final reciprocal
octave error and its entire earlier prefix. -/
theorem reciprocal_octave_abel_identity {n : ℕ} (hn : 0<n) :
    undividedOctavePrefix n = (n:ℝ)*reciprocalOctaveError n -
      ∑ k ∈ Ico 1 n, reciprocalOctaveError k := by
  have hI : Ioc 0 n=Icc 1 n := by ext k; simp only [mem_Ioc,mem_Icc]; omega
  have hs := sum_smul_eq_prefix_differences (fun k : ℕ => reciprocalOctaveAtom k/k) (fun k : ℕ => (k:ℝ)) n
  simp only [smul_eq_mul] at hs
  have hu (k : ℕ) (hk : k∈Icc 1 n) : reciprocalOctaveAtom k/k*k=reciprocalOctaveAtom k :=
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (show 0<k from (mem_Icc.mp hk).1).ne')
  have hv (k : ℕ) (hk : k∈Icc 1 n) : (∑ j ∈ Icc 1 k, reciprocalOctaveAtom j/j) *
      ((k:ℝ)-((k+1:ℕ):ℝ)) = -reciprocalOctaveError k := by
    rw [octave_prefix (mem_Icc.mp hk).1,Nat.cast_add,Nat.cast_one]
    ring
  rw [sum_congr rfl hu,octave_prefix hn,sum_congr rfl hv,sum_neg_distrib] at hs
  have hh : Icc 1 n = insert n (Ico 1 n) := by ext d; simp only [mem_Icc,mem_insert,mem_Ico]; omega
  have hh' : (∑ k ∈ Icc 1 n, reciprocalOctaveError k) =
      reciprocalOctaveError n + ∑ k ∈ Ico 1 n, reciprocalOctaveError k := by
    rw [hh,sum_insert (by simp)]
  rw [hh',Nat.cast_add,Nat.cast_one] at hs
  rw [undividedOctavePrefix,hI,hs]
  ring

/-- Each of the two genuine offspring uses the same parent prime error.
The odd child retains its one-unit density correction. -/
theorem reciprocal_octave_binary_children {n : ℕ} (hn : 0<n) {r : ℕ} (hr : r≤1) :
    2*(Chebyshev.psi n-n) = (Chebyshev.psi (2*n+r : ℕ)-(2*n+r : ℕ))-undividedOctavePrefix (2*n+r)+(r:ℝ)-Real.log 2 := by
  have hm : 0<2*n+r := by omega
  rw [raw_atom_value hm,show (2*n+r)/2=n by omega]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

#print axioms reciprocal_octave_abel_identity
#print axioms reciprocal_octave_binary_children

/-- Harmonic absolute mass of the prime error below Y. -/
def primeErrorHarmonicMass (Y : ℕ) : ℝ :=
  ∑ n ∈ range Y, |Chebyshev.psi n-n| /(n+1)

/-- Absolute cost of the undivided octave atoms, with their unit correction. -/
def octaveAtomHarmonicMass (Y : ℕ) : ℝ :=
  ∑ m ∈ range Y, (|undividedOctavePrefix m|+1+Real.log 2)/(m+1)

private theorem sum_two_children (f : ℕ → ℝ) (Y : ℕ) :
    (∑ n ∈ range Y, (f (2*n)+f (2*n+1))) = ∑ m ∈ range (2*Y), f m := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [show 2*(Y+1)=(2*Y+1)+1 by omega,Finset.sum_range_succ f,Finset.sum_range_succ f,Finset.sum_range_succ,ih]
    ring

/-- Averaging the two children contracts the harmonic mass by one half.
Both parities are retained at each successive dyadic scale. -/
theorem reciprocal_octave_harmonic_descent (Y : ℕ) :
    primeErrorHarmonicMass Y ≤ (primeErrorHarmonicMass (2*Y)+octaveAtomHarmonicMass (2*Y))/2 := by
  let D (n : ℕ) := Chebyshev.psi n-n
  let B (n : ℕ) := |undividedOctavePrefix n|+1+Real.log 2
  let F (n : ℕ) := |D n| /(n+1)
  let G (n : ℕ) := B n/(n+1)
  have hl := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hB (m : ℕ) : 0≤B m := by dsimp only [B]; linarith only [abs_nonneg (undividedOctavePrefix m),hl]
  have child (n r : ℕ) (hn : 0<n) (hr : r≤1) : F n ≤ F (2*n+r)+G (2*n+r) := by
    let m := 2*n+r
    have he : 2*D n = D m-undividedOctavePrefix m+(r:ℝ)-Real.log 2 :=
      reciprocal_octave_binary_children hn hr
    have hb : 2*|D n|≤|D m|+B m := by
      rw [show 2*|D n|=|2*D n| by rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)],he]
      have h₁ := abs_sub (D m-undividedOctavePrefix m+(r:ℝ)) (Real.log 2)
      have h₂ := abs_add_le (D m-undividedOctavePrefix m) (r:ℝ)
      have h₃ := abs_sub (D m) (undividedOctavePrefix m)
      rw [abs_of_nonneg hl] at h₁
      rw [abs_of_nonneg (Nat.cast_nonneg r : (0:ℝ)≤r)] at h₂
      dsimp only [B]
      linarith only [h₁,h₂,h₃,(Nat.cast_le_one.mpr hr : (r:ℝ)≤1)]
    have hm : (m:ℝ)+1≤2*((n:ℝ)+1) := by dsimp only [m]; push_cast; linarith only [(Nat.cast_le_one.mpr hr : (r:ℝ)≤1)]
    change |D n| /(n+1) ≤ |D m| /(m+1)+B m/(m+1)
    rw [←add_div,div_le_div_iff₀ (by positivity) (by positivity)]
    calc _ ≤ |D n| *(2*((n:ℝ)+1)) := mul_le_mul_of_nonneg_left hm (abs_nonneg _)
         _ = (2*|D n|)*((n:ℝ)+1) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)
  have pair (n : ℕ) : 2*F n ≤ (F (2*n)+G (2*n)) + (F (2*n+1)+G (2*n+1)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hf : F 0=0 := by simp [F,D,Chebyshev.psi]
      have hFG (m : ℕ) : 0≤F m+G m := by
        dsimp only [F,G]
        exact add_nonneg (div_nonneg (abs_nonneg _) (by positivity)) (div_nonneg (hB m) (by positivity))
      calc 2*F 0 = 0 := by rw [hf,mul_zero]
           _ ≤ _ := add_nonneg (hFG (2*0)) (hFG (2*0+1))
    · have a := child n 0 hn (by decide)
      simp only [Nat.add_zero] at a
      linarith only [a,child n 1 hn le_rfl]
  have h := sum_le_sum (s := range Y) (fun n _ => pair n)
  rw [←mul_sum,sum_two_children (fun m => F m+G m),sum_add_distrib] at h
  change (∑ n ∈ range Y, F n) ≤ ((∑ m ∈ range (2*Y), F m)+(∑ m ∈ range (2*Y), G m))/2
  linarith only [h]

#print axioms reciprocal_octave_harmonic_descent

#print axioms last_half_abs_reciprocal_octave
#print axioms abs_reciprocal_octave_parity_mean
#print axioms reciprocal_octave_parity_mean
#print axioms octave_parity_weight_range
#print axioms octave_parity_weight_top
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
