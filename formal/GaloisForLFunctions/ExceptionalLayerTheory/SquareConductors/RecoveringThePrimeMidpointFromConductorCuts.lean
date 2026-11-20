import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheVariationOfTheMovingPrimeCut
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FractionalDiscrepancyAtThePrimeMidpoint

/-!
# The prime midpoint from the moving conductor cutoff

The real cutoff increments below the first knot carry an extra factor
of the index. Dividing each increment by its index recovers the signed
prime midpoint and its half-order integral. Discrete summation by parts
gives the exact norm of this recovery on prices of bounded oscillation.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment

/-- The first difference on an interval, weighted by reciprocal index. -/
def reciprocalCutRead (f : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ j ∈ Ioc a b, (f j-f (j-1))/(j:ℝ)

private theorem reciprocalCutRead_abel (f : ℕ → ℝ) {a b : ℕ} (hab : a≤b) :
    reciprocalCutRead f a b+f a/(a+1)=
      f b/(b+1)+∑ j ∈ Ioc a b, (1/(j:ℝ)-1/(j+1))*f j := by
  induction b, hab using Nat.le_induction with
  | base => simp [reciprocalCutRead]
  | succ b hab ih =>
    unfold reciprocalCutRead at ih ⊢
    rw [sum_Ioc_succ_top hab,sum_Ioc_succ_top hab,Nat.succ_sub_one,Nat.cast_succ]
    linarith only [ih]

/-- The boundary-corrected reading is monotone in every interior price.
The left endpoint need not satisfy the comparison. -/
theorem corrected_cut_read_mono {f g : ℕ → ℝ} {a b : ℕ} (hab : a<b)
    (h : ∀ j ∈ Ioc a b, f j≤g j) :
    reciprocalCutRead f a b+f a/(a+1) ≤ reciprocalCutRead g a b+g a/(a+1) := by
  rw [reciprocalCutRead_abel _ hab.le,reciprocalCutRead_abel _ hab.le]
  refine add_le_add (div_le_div_of_nonneg_right (h b (mem_Ioc.mpr ⟨hab,le_rfl⟩)) (by positivity))
    (sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (h j hj) ?_)
  have hj₀ : 0<(j:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le a).trans_lt (mem_Ioc.mp hj).1)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hj₀ (by linarith only))

private theorem reciprocalCutRead_bounds {f : ℕ → ℝ} {a b : ℕ} (hab : a<b) {L U : ℝ}
    (h : ∀ j ∈ Ioc a b, L≤f j ∧ f j≤U) :
    (L-f a)/(a+1) ≤ reciprocalCutRead f a b ∧ reciprocalCutRead f a b ≤ (U-f a)/(a+1) := by
  have hl := corrected_cut_read_mono (f:=fun _ => L) hab (fun j hj => (h j hj).1)
  have hu := corrected_cut_read_mono (g:=fun _ => U) hab (fun j hj => (h j hj).2)
  have he (v : ℝ) : reciprocalCutRead (fun _ => v) a b=0 := by simp [reciprocalCutRead]
  rw [he,zero_add] at hl hu
  constructor <;> rw [sub_div] <;> linarith only [hl,hu]

private theorem cut_read_abs {f : ℕ → ℝ} {a b : ℕ} (hab : a<b) {L U : ℝ}
    (h : ∀ j ∈ Icc a b, L≤f j ∧ f j≤U) : |reciprocalCutRead f a b| ≤ (U-L)/(a+1) := by
  obtain ⟨hl,hu⟩ := reciprocalCutRead_bounds hab fun j hj =>
    h j (mem_Icc.mpr ⟨(mem_Ioc.mp hj).1.le,(mem_Ioc.mp hj).2⟩)
  obtain ⟨h₁,h₂⟩ := h a (mem_Icc.mpr ⟨le_rfl,hab.le⟩)
  have ha : (0:ℝ) ≤ a+1 := by positivity
  apply abs_le.mpr
  constructor
  · rw [← neg_div,neg_sub]
    exact (div_le_div_of_nonneg_right (sub_le_sub_left h₂ _) ha).trans hl
  · exact hu.trans (div_le_div_of_nonneg_right (sub_le_sub_left h₁ _) ha)

/-- The reciprocal midpoint contrast has a sharp oscillation bound on
arbitrary adjacent integer windows. -/
theorem reciprocal_cut_contrast_bound {a b c : ℕ} (hab : a<b) (hbc : b<c) {L U : ℝ}
    (f : ℕ → ℝ) (h : ∀ j ∈ Icc a c, L≤f j ∧ f j≤U) :
    |reciprocalCutRead f a b-reciprocalCutRead f b c| ≤
      (U-L)*(1/(a+1:ℝ)+1/(b+1:ℝ)) := by
  have h₁ := cut_read_abs hab fun j hj => h j (mem_Icc.mpr
    ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans hbc.le⟩)
  have h₂ := cut_read_abs hbc fun j hj => h j (mem_Icc.mpr
    ⟨hab.le.trans (mem_Icc.mp hj).1,(mem_Icc.mp hj).2⟩)
  exact (abs_sub _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- A rectangular price on the first window realizes the bound, for every
choice of cutoffs and every pair of endpoint levels. -/
theorem reciprocal_cut_contrast_sharp {a b c : ℕ} (hab : a<b) (hbc : b<c) (L U : ℝ) :
    let f := fun j => if a<j ∧ j≤b then U else L
    reciprocalCutRead f a b-reciprocalCutRead f b c=(U-L)*(1/(a+1:ℝ)+1/(b+1:ℝ)) := by
  intro f
  have h₁ := reciprocalCutRead_bounds (f:=f) (L:=U) (U:=U) hab (fun j hj => by
    simp only [f,if_pos (mem_Ioc.mp hj),le_refl,and_self])
  have h₂ := reciprocalCutRead_bounds (f:=f) (L:=L) (U:=L) hbc (fun j hj => by
    simp only [f,if_neg (show ¬(a<j ∧ j≤b) from fun h => (mem_Ioc.mp hj).1.not_ge h.2),
      le_refl,and_self])
  rw [le_antisymm h₁.2 h₁.1,le_antisymm h₂.2 h₂.1]
  simp only [f,lt_irrefl,false_and,if_false,hab,le_refl,and_self,if_true]
  ring

private theorem read_conductor_interval {N a b : ℕ} (hN : 0<N)
    (hb : (b:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) :
    reciprocalCutRead (fun j => (centeredFixedPrimeTail N j).re) a b =
      innerPrimeSlope*((b-a:ℕ)-(∑ j ∈ (Ioc a b).filter Nat.Prime,Real.log j):ℝ) := by
  have he (j : ℕ) (hj : j ∈ Ioc a b) :
      ((centeredFixedPrimeTail N j).re-(centeredFixedPrimeTail N (j-1)).re)/(j:ℝ) =
        innerPrimeSlope*(1-if j.Prime then Real.log j else 0) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Ioc.mp hj).1; omega : j≠0)
    rw [Nat.succ_sub_one,←Complex.sub_re,inner_cutoff_jump hN ((Nat.cast_le.mpr (mem_Ioc.mp hj).2).trans hb),
      Complex.ofReal_re]
    field_simp [show ((k+1:ℕ):ℝ)≠0 by positivity] <;> ring
  rw [reciprocalCutRead,sum_congr rfl he,←mul_sum,sum_sub_distrib,←sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc]

/-- The same conductor and the original signed midpoint are used on both
windows. The integer background cancels because their lengths agree. -/
theorem conductor_recovers_prime_midpoint {N n : ℕ} (hN : 0<N)
    (hk : ((4*n:ℕ):ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) :
    let F := fun j => (centeredFixedPrimeTail N j).re
    reciprocalCutRead F (2*n) (3*n)-reciprocalCutRead F (3*n) (4*n) =
      -innerPrimeSlope*primeMidpointPrice n := by
  dsimp only
  rw [read_conductor_interval hN ((Nat.cast_le.mpr (show 3*n≤4*n by omega)).trans hk),
    read_conductor_interval hN hk,primeMidpointPrice,show 3*n-2*n=n by omega,
    show 4*n-3*n=n by omega]
  ring

/-- The half-order discrepancy pairing can be observed entirely through
real cutoff prices at a single terminal conductor. -/
theorem half_order_integral_from_conductor_cuts {N n : ℕ} (hN : 0<N)
    (hk : ((4*n:ℕ):ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) :
    let F := fun j => (centeredFixedPrimeTail N j).re
    innerPrimeSlope*(∫ x, midpointFractionalTest n (1/2) x*midpointFractionalField n (1/2) x) =
      -Real.pi*(reciprocalCutRead F (2*n) (3*n)-reciprocalCutRead F (3*n) (4*n)) := by
  dsimp only
  rw [half_order_prime_midpoint n,conductor_recovers_prime_midpoint hN hk]
  ring

/-- A prime midpoint excursion forces cutoff price oscillation, amplified
by one full power of the midpoint scale below the first spline knot. -/
theorem prime_midpoint_forces_cut_oscillation {N n : ℕ} (hn : 0<n) (hN : 0<N)
    (hk : ((4*n:ℕ):ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) {L U : ℝ}
    (h : ∀ j ∈ Icc (2*n) (4*n), L≤(centeredFixedPrimeTail N j).re ∧ (centeredFixedPrimeTail N j).re≤U) :
    innerPrimeSlope*|primeMidpointPrice n| ≤ (U-L)*(1/(2*(n:ℝ)+1)+1/(3*(n:ℝ)+1)) := by
  have hr := reciprocal_cut_contrast_bound (show 2*n<3*n by omega) (show 3*n<4*n by omega) _ h
  rw [conductor_recovers_prime_midpoint hN hk,abs_mul,abs_neg,abs_of_pos innerPrimeSlope_pos] at hr
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hr

/-- The unknown base price at a conductor disappears on subtraction.
All terminal conductors give the same complex differences below the knot. -/
theorem inner_cut_differences_independent {N M a b : ℕ}
    (hN : 0<N) (hM : 0<M) (hab : a≤b)
    (hn : (b:ℝ)≤Real.exp (-8)*(N:ℝ)^2) (hm : (b:ℝ)≤Real.exp (-8)*(M:ℝ)^2) :
    centeredFixedPrimeTail N b-centeredFixedPrimeTail N a =
      centeredFixedPrimeTail M b-centeredFixedPrimeTail M a := by
  rw [centered_tail_first_moment hN hn 0,centered_tail_first_moment hN ((Nat.cast_le.mpr hab).trans hn) 0,
    centered_tail_first_moment hM hm 0,centered_tail_first_moment hM ((Nat.cast_le.mpr hab).trans hm) 0]
  ring

private theorem reciprocal_prefix_inverse (f : ℕ → ℝ) (n : ℕ) :
    f n-f 0=n*reciprocalCutRead f 0 n-∑ i ∈ range n, reciprocalCutRead f 0 i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hinc : reciprocalCutRead f 0 (n+1)=reciprocalCutRead f 0 n+(f (n+1)-f n)/(n+1) := by
      rw [reciprocalCutRead,reciprocalCutRead,sum_Ioc_succ_top (Nat.zero_le n),Nat.succ_sub_one,Nat.cast_succ]
    have hc : ((n:ℝ)+1)*((f (n+1)-f n)/(n+1))=f (n+1)-f n := by
      field_simp [show (n:ℝ)+1≠0 by positivity]
    rw [sum_range_succ,hinc,Nat.cast_succ,mul_add,hc]
    linarith only [ih]

private theorem conductor_reciprocal_prefix {N n : ℕ} (hN : 0<N) (hk : (n:ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    reciprocalCutRead (fun j => (centeredFixedPrimeTail N j).re) 0 n =
      innerPrimeSlope*((n:ℝ)-Chebyshev.theta n) := by
  rw [read_conductor_interval hN hk,Nat.sub_zero]
  simp only [Chebyshev.theta,Nat.floor_natCast]

private theorem conductor_prefix_enclosure {N n : ℕ} (hN : 0<N) (hk : (n:ℝ)≤Real.exp (-8)*(N:ℝ)^2)
    {B : ℝ} (hB : ∀ i≤n, |Chebyshev.theta i-i|≤B) :
    |(centeredFixedPrimeTail N n).re-(centeredFixedPrimeTail N 0).re|≤2*n*(innerPrimeSlope*B) := by
  let f := fun j => (centeredFixedPrimeTail N j).re
  have hpre {i : ℕ} (hi : i≤n) : |reciprocalCutRead f 0 i| ≤ innerPrimeSlope*B := by
    rw [conductor_reciprocal_prefix hN ((Nat.cast_le.mpr hi).trans hk),abs_mul,abs_of_pos innerPrimeSlope_pos,abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (hB i hi) innerPrimeSlope_pos.le
  have hsum : |∑ i ∈ range n, reciprocalCutRead f 0 i| ≤ n*(innerPrimeSlope*B) := by
    apply (abs_sum_le_sum_abs _ _).trans
    simpa only [sum_const,card_range,nsmul_eq_mul] using
      (sum_le_sum (s:=range n) fun i hi => hpre (mem_range.mp hi).le)
  rw [show (centeredFixedPrimeTail N n).re-(centeredFixedPrimeTail N 0).re =
    n*reciprocalCutRead f 0 n-∑ i ∈ range n, reciprocalCutRead f 0 i from reciprocal_prefix_inverse f n]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
  linarith only [hsum,mul_le_mul_of_nonneg_left (hpre le_rfl) (Nat.cast_nonneg (α:=ℝ) n)]

private theorem theta_spectrum_majorant {b t : ℝ} (hb : 1/2 ≤ b) (ht : b<t)
    (hz : _root_.RHTower.zetaZeroAbscissa≤b) :
    ∃ C : ℝ, 0≤C ∧ ∀ i : ℕ, |Chebyshev.theta i-i|≤C*(i:ℝ)^t := by
  have hs := _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
    (_root_.RHTower.re_le_zetaZeroAbscissa (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy q)).trans hz
  obtain ⟨C,hC,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow (hs.trans_lt ht)
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C+|D|,add_nonneg hC (abs_nonneg _),?_⟩
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [Chebyshev.theta,Real.zero_rpow (by linarith only [hb,ht] : t≠0)]
  have h₁ : (1:ℝ) ≤ i := Nat.one_le_cast.mpr hi
  have hproper : |Chebyshev.psi i-Chebyshev.theta i| ≤ |D| * (i:ℝ)^t := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    apply (hD _).trans
    rw [Real.sqrt_eq_rpow]
    exact mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le h₁ (hb.trans ht.le))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _)
  have hdiff : Chebyshev.theta i-(i:ℝ)=(Chebyshev.psi i-i)-(Chebyshev.psi i-Chebyshev.theta i) := by ring
  rw [hdiff]
  exact (abs_sub _ _).trans ((add_le_add (hψ _ h₁) hproper).trans_eq (by ring))

/-- The zero abscissa controls the actual oscillation of the conductor
cut on each prime octave, uniformly in the admissible terminal conductor. -/
theorem conductor_octave_oscillation_of_zero_abscissa {b t : ℝ} (hb : 1/2≤b) (ht : b<t)
    (hz : _root_.RHTower.zetaZeroAbscissa≤b) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n N : ℕ), 0<n → 0<N → ((4*n:ℕ):ℝ)≤Real.exp (-8)*(N:ℝ)^2 →
      ∀ j∈Icc (2*n) (4*n), |(centeredFixedPrimeTail N j).re-(centeredFixedPrimeTail N (2*n)).re|
        ≤ C*(n:ℝ)^(1+t) := by
  obtain ⟨D,hD,he⟩ := theta_spectrum_majorant hb ht hz
  have hλ := innerPrimeSlope_pos
  refine ⟨16*innerPrimeSlope*D*(4:ℝ)^t,by positivity,?_⟩
  intro n N hn hN hk j hj
  have ht' : 0≤t := by linarith only [hb,ht]
  let B := D*((4*n:ℕ):ℝ)^t
  have hB : 0≤B := mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hf (i : ℕ) (hi : i≤4*n) : |Chebyshev.theta i-i|≤B :=
    (he i).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (Nat.cast_le.mpr hi) ht') hD)
  let F := fun i => (centeredFixedPrimeTail N i).re
  have hprice (i : ℕ) (hi : i≤4*n) : |F i-F 0| ≤ 2*((4*n:ℕ):ℝ)*(innerPrimeSlope*B) := by
    have h := conductor_prefix_enclosure hN ((Nat.cast_le.mpr hi).trans hk)
      (fun v hv => hf v (hv.trans hi))
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hi) (by norm_num))
      (mul_nonneg innerPrimeSlope_pos.le hB))
  have hc := (abs_sub (F j-F 0) (F (2*n)-F 0)).trans
    (add_le_add (hprice j (mem_Icc.mp hj).2) (hprice (2*n) (by omega)))
  rw [show (F j-F 0)-(F (2*n)-F 0)=F j-F (2*n) by ring] at hc
  apply hc.trans_eq
  simp only [B,Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0:ℝ)≤4) (Nat.cast_nonneg n),
    Real.rpow_add (Nat.cast_pos.mpr hn),Real.rpow_one]
  ring

/-- Measuring the entire inner-cut octave at one terminal conductor of
one's choice for each n already gives the exact zero-abscissa threshold.
The necessary oscillation exponent is shifted by one from the prime price. -/
theorem zero_abscissa_iff_one_conductor_per_octave {b : ℝ} (hb : 1/2≤b) :
    _root_.RHTower.zetaZeroAbscissa≤b ↔ ∀ t : ℝ, b<t → t<1 → ∃ C : ℝ, 0≤C ∧
      ∀ n : ℕ, 0<n → ∃ N : ℕ, 0<N ∧ ((4*n:ℕ):ℝ)≤Real.exp (-8)*(N:ℝ)^2 ∧
        ∀ j∈Icc (2*n) (4*n), |(centeredFixedPrimeTail N j).re-(centeredFixedPrimeTail N (2*n)).re|
          ≤ C*(n:ℝ)^(1+t) := by
  constructor
  · intro hz t ht _
    obtain ⟨C,hC,hh⟩ := conductor_octave_oscillation_of_zero_abscissa hb ht hz
    refine ⟨C,hC,?_⟩
    intro n hn
    let E := Real.exp (-8)
    have hE : 0<E := Real.exp_pos _
    obtain ⟨N,hN⟩ := exists_nat_gt (((4*n:ℕ):ℝ)/E+1)
    have hpos : 0≤((4*n:ℕ):ℝ)/E := div_nonneg (Nat.cast_nonneg _) hE.le
    have hN' : 1≤(N:ℝ) := by linarith only [hN,hpos]
    have hN₀ : 0<N := Nat.one_le_cast.mp hN'
    have hkn : ((4*n:ℕ):ℝ)≤E*(N:ℝ)^2 := by
      have hk := (div_lt_iff₀ hE).mp (show ((4*n:ℕ):ℝ)/E<N by linarith only [hN])
      have hh' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN' (Nat.cast_nonneg N)) hE.le
      linarith only [hk,hh']
    exact ⟨N,hN₀,hkn,hh n N hn hN₀ hkn⟩
  · intro h
    apply (prime_midpoint_upper_spectrum_iff hb).mp
    intro t ht ht'
    obtain ⟨C,hC,hobs⟩ := h t ht ht'
    refine ⟨4*C/innerPrimeSlope,?_⟩
    intro n hn
    obtain ⟨N,hN,hk,hbox⟩ := hobs n hn
    let a := (centeredFixedPrimeTail N (2*n)).re
    let B := C*(n:ℝ)^(1+t)
    have hB : 0≤B := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
    have he := prime_midpoint_forces_cut_oscillation hn hN hk (L:=a-B) (U:=a+B) (fun j hj => by
      have ht := abs_le.mp (hbox j hj)
      change a-B≤_ ∧ _≤a+B
      change -B≤(centeredFixedPrimeTail N j).re-a ∧ (centeredFixedPrimeTail N j).re-a≤B at ht
      constructor <;> linarith only [ht.1,ht.2])
    have hsum : 1/(2*(n:ℝ)+1)+1/(3*(n:ℝ)+1)≤2/(n:ℝ) := by
      have h₂ := one_div_le_one_div_of_le hn' (show (n:ℝ)≤2*n+1 by linarith only [hn'])
      have h₃ := one_div_le_one_div_of_le hn' (show (n:ℝ)≤3*n+1 by linarith only [hn'])
      linarith only [h₂,h₃]
    rw [show a+B-(a-B)=2*B by ring] at he
    have hpaid := he.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    have hf : innerPrimeSlope*|primeMidpointPrice n| ≤ 4*C*(n:ℝ)^t := hpaid.trans_eq (by
      dsimp only [B]
      rw [Real.rpow_add hn',Real.rpow_one]
      field_simp [hn'.ne'] <;> ring)
    calc primeMidpointPrice n≤|primeMidpointPrice n| := le_abs_self _
      _ ≤ 4*C*(n:ℝ)^t/innerPrimeSlope := (le_div_iff₀ innerPrimeSlope_pos).mpr (by rwa [mul_comm])
      _ = _ := by ring

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment
