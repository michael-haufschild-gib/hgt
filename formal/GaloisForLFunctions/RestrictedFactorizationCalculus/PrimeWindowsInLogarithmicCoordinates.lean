import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary

/-!
# Transporting the first Mertens prime weights to intervals

Assign the weight of each prime to the next interval of that length on the
real line. Both ends of the interval lie uniformly close to the logarithm of
the prime. Secant slopes on these disjoint intervals give sharp moving-window
quadrature without partitioning the exponent range into a fixed mesh.
-/

noncomputable section

open Finset RHTower.Sieve

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Prime mass up to a sharp integer endpoint, in units of the reference logarithm. -/
def mertensCoordinate (h : ℝ) (n : ℕ) := (∑ p ∈ Nat.primesLE n, Real.log p / p) / h

/-- A test evaluated at the physical prime exponents. -/
def primeCoordinateSum (h : ℝ) (f : ℝ → ℝ) (n : ℕ) :=
  ∑ p ∈ Nat.primesLE n, (Real.log p / p / h) * f (Real.log p / h)

/-- Uniform coordinate tolerance, including the left limit at a prime. -/
def coordinateRadius (h : ℝ) := (mertensBlockGapConst + Real.log 2) / h

private theorem coordinate_step (h : ℝ) (n : ℕ) :
    mertensCoordinate h (n+1) - mertensCoordinate h n =
      if (n+1).Prime then Real.log (n+1:ℕ) / (n+1:ℕ) / h else 0 := by
  rw [mertensCoordinate,mertensCoordinate,Nat.primesLE_succ]
  split_ifs with hp
  · have hnot : n+1 ∉ Nat.primesLE n := fun hn => (Nat.not_succ_le_self n) (Nat.mem_primesLE.mp hn).1
    rw [sum_insert hnot]; ring
  · ring

private theorem tested_step (h : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    primeCoordinateSum h f (n+1) - primeCoordinateSum h f n =
      (mertensCoordinate h (n+1) - mertensCoordinate h n) * f (Real.log (n+1:ℕ)/h) := by
  rw [primeCoordinateSum,primeCoordinateSum,Nat.primesLE_succ,coordinate_step]
  split_ifs with hp
  · have hnot : n+1 ∉ Nat.primesLE n := fun hn => (Nat.not_succ_le_self n) (Nat.mem_primesLE.mp hn).1
    rw [sum_insert hnot]; ring
  · ring

/-- Both ends of the interval assigned to n+1 lie within the same tolerance
of its physical logarithm. Composite indices correspond to empty intervals. -/
private theorem coordinate_cell {h : ℝ} (hh : 0 < h) {n : ℕ} (hn : 1 ≤ n) :
    let x := Real.log (n+1:ℕ)/h
    x-coordinateRadius h ≤ mertensCoordinate h n ∧
    mertensCoordinate h n ≤ mertensCoordinate h (n+1) ∧
    mertensCoordinate h (n+1) ≤ x+coordinateRadius h := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le h1
  have hl2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have hl4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have hlog := Real.log_le_log (by positivity : 0 < (n:ℝ)+1)
    (show (n:ℝ)+1 ≤ 2*n by linarith only [h1])
  rw [Real.log_mul (by norm_num) hn0.ne'] at hlog
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [coordinateRadius,mertensCoordinate,←sub_div,div_le_div_iff_of_pos_right hh]
    push_cast
    unfold mertensBlockGapConst
    linarith only [mertensFirst_lower hn,hlog,hl4]
  · apply sub_nonneg.mp
    rw [coordinate_step]
    split_ifs
    · have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n+1) : (1:ℝ) ≤ (n+1:ℕ))
      positivity
    · exact le_rfl
  · rw [coordinateRadius,mertensCoordinate,←add_div,div_le_div_iff_of_pos_right hh]
    unfold mertensBlockGapConst
    linarith only [mertensFirst_upper (show 1 ≤ n+1 by omega),logSqTailConst_nonneg,hl2]

private theorem secant_value {F f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hF : ∀ x ∈ Set.Icc u v, HasDerivAt F (f x) x) :
    ∃ t ∈ Set.Icc u v, F v-F u = (v-u)*f t := by
  rcases huv.eq_or_lt with he | h
  · subst v; exact ⟨u,⟨le_rfl,le_rfl⟩,by ring⟩
  obtain ⟨t,ht,hs⟩ := exists_hasDerivAt_eq_slope F f h
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
    (fun x hx => hF x ⟨hx.1.le,hx.2.le⟩)
  exact ⟨t,⟨ht.1.le,ht.2.le⟩,by rw [mul_comm]; exact ((eq_div_iff (sub_ne_zero.mpr h.ne')).1 hs).symm⟩

/-- In the transported coordinates, the error of a Lipschitz test is at most
its Lipschitz constant times the coordinate radius times the mass of the window. -/
theorem prime_coordinate_quadrature {h K : ℝ} (hh : 0 < h) (hK : 0 ≤ K) (a b : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (f F : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h),
      HasDerivAt F (f x) x)
    (hLip : ∀ x ∈ Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h),
      ∀ z ∈ Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h),
      |f x-f z| ≤ K*|x-z|) :
    |(primeCoordinateSum h f b - primeCoordinateSum h f a) -
        (F (mertensCoordinate h b) - F (mertensCoordinate h a))| ≤
      K*coordinateRadius h*(mertensCoordinate h b-mertensCoordinate h a) := by
  let δ := coordinateRadius h
  let X := fun n : ℕ => Real.log n / h
  let A := mertensCoordinate h
  let J := Set.Icc (X a-δ) (X b+δ)
  have hδ : 0 ≤ δ := div_nonneg (add_nonneg mertensBlockGapConst_nonneg
    (Real.log_nonneg (by norm_num))) hh.le
  have hxmono {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : X m ≤ X n := by
    exact div_le_div_of_nonneg_right (Real.log_le_log
      (by exact_mod_cast (by omega : 0 < m) : (0:ℝ) < m) (by exact_mod_cast hmn)) hh.le
  have piece (n : ℕ) (han : a ≤ n) (hnb : n+1 ≤ b) :
      |(primeCoordinateSum h f (n+1)-primeCoordinateSum h f n) -
          (F (A (n+1))-F (A n))| ≤ K*δ*(A (n+1)-A n) := by
    obtain ⟨hl,hm,hu⟩ := coordinate_cell hh (ha.trans han)
    have hxL := hxmono ha (han.trans (Nat.le_succ n))
    have hxU := hxmono (by omega : 1 ≤ n+1) hnb
    change X (n+1)-δ ≤ A n at hl
    change A n ≤ A (n+1) at hm
    change A (n+1) ≤ X (n+1)+δ at hu
    have hsub : Set.Icc (A n) (A (n+1)) ⊆ J := fun t ht =>
      ⟨(sub_le_sub_right hxL δ).trans (hl.trans ht.1),ht.2.trans (hu.trans (add_le_add_left hxU δ))⟩
    have hxJ : X (n+1) ∈ J := ⟨by linarith only [hxL,hδ],by linarith only [hxU,hδ]⟩
    obtain ⟨t,ht,he⟩ := secant_value hm (fun t ht => hF _ (hsub ht))
    have herr := hLip _ hxJ _ (hsub ht)
    have hdis : |X (n+1)-t| ≤ δ := abs_le.mpr ⟨by linarith only [hu,ht.2],by linarith only [hl,ht.1]⟩
    rw [tested_step,he]
    change |(A (n+1)-A n)*f (X (n+1)) - (A (n+1)-A n)*f t| ≤ _
    rw [←mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hm),mul_comm (K*δ)]
    exact mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_left hdis hK)) (sub_nonneg.mpr hm)
  let E := fun n : ℕ => primeCoordinateSum h f n-F (A n)
  have accum (u : ℕ) (hau : a ≤ u) : u ≤ b → |E u-E a| ≤ K*δ*(A u-A a) := by
    induction u,hau using Nat.le_induction with
    | base => simp
    | succ n han ih =>
      intro hnb
      have hs := piece n han hnb
      have hs' : |E (n+1)-E n| ≤ K*δ*(A (n+1)-A n) := by
        convert hs using 2 <;> dsimp [E] <;> ring
      exact (abs_sub_le _ (E n) _).trans
        ((add_le_add hs' (ih ((Nat.le_succ n).trans hnb))).trans_eq (by ring))
  convert accum b hab le_rfl using 2 <;> dsimp [E,A,δ] <;> ring

private theorem coordinate_error {h : ℝ} (hh : 0 < h) {n : ℕ} (hn : 1 ≤ n) :
    |mertensCoordinate h n-Real.log n/h| ≤ coordinateRadius h := by
  rw [mertensCoordinate,coordinateRadius,←sub_div,abs_div,abs_of_pos hh,
    div_le_div_iff_of_pos_right hh,abs_le]
  unfold mertensBlockGapConst
  have hl2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have hl4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  constructor <;> linarith only [mertensFirst_lower hn,mertensFirst_upper hn,hl2,hl4,logSqTailConst_nonneg]

/-- Sharp physical endpoints cost at most one displacement at each end.
The error is uniform in both endpoints and in all tests with the given bounds. -/
theorem sharp_prime_quadrature {h K B : ℝ} (hh : 0 < h) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (f F : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h),
      HasDerivAt F (f x) x)
    (hLip : ∀ x ∈ Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h),
      ∀ z ∈ Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h),
      |f x-f z| ≤ K*|x-z|)
    (hf : ∀ x ∈ Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h), |f x| ≤ B) :
    |(primeCoordinateSum h f b - primeCoordinateSum h f a) - (F (Real.log b/h) - F (Real.log a/h))| ≤
      coordinateRadius h * (2*B + K*((Real.log b/h-Real.log a/h)+2*coordinateRadius h)) := by
  let A := mertensCoordinate h
  let X := fun n : ℕ => Real.log n/h
  let δ := coordinateRadius h
  let J := Set.Icc (X a-δ) (X b+δ)
  have hδ : 0 ≤ δ := div_nonneg (add_nonneg mertensBlockGapConst_nonneg
    (Real.log_nonneg (by norm_num))) hh.le
  have hab' : X a ≤ X b := div_le_div_of_nonneg_right (Real.log_le_log
    (by exact_mod_cast (by omega : 0 < a) : (0:ℝ) < a) (by exact_mod_cast hab)) hh.le
  have hA : |A a-X a| ≤ δ := coordinate_error hh ha
  have hC : |A b-X b| ≤ δ := coordinate_error hh (ha.trans hab)
  have har := abs_le.mp hA
  have hbr := abs_le.mp hC
  have bound {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) (huv : u ≤ v) : |F v-F u| ≤ B*|v-u| := by
    have inc : Set.Icc u v ⊆ J := fun t ht => ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩
    obtain ⟨t,ht,he⟩ := secant_value huv (fun t ht => hF t (inc ht))
    rw [he,abs_mul,mul_comm B]
    exact mul_le_mul_of_nonneg_left (hf _ (inc ht)) (abs_nonneg _)
  have edge {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) (hdis : |u-v| ≤ δ) : |F u-F v| ≤ B*δ := by
    rcases le_total v u with h | h
    · exact (bound hv hu h).trans (mul_le_mul_of_nonneg_left hdis hB)
    · rw [abs_sub_comm] at hdis ⊢
      exact (bound hu hv h).trans (mul_le_mul_of_nonneg_left hdis hB)
  have haF := edge (u := A a) (v := X a)
    (show A a ∈ J from ⟨by linarith only [har.1],by linarith only [har.2,hab']⟩)
    (show X a ∈ J from ⟨by linarith only [hδ],by linarith only [hδ,hab']⟩) hA
  have hbF := edge (u := A b) (v := X b)
    (show A b ∈ J from ⟨by linarith only [hbr.1,hab'],by linarith only [hbr.2]⟩)
    (show X b ∈ J from ⟨by linarith only [hδ,hab'],by linarith only [hδ]⟩) hC
  let W := primeCoordinateSum h f b-primeCoordinateSum h f a
  have hW : |W-(F (A b)-F (A a))| ≤ K*δ*(A b-A a) := prime_coordinate_quadrature hh hK a b ha hab f F hF hLip
  have hlen : A b-A a ≤ X b-X a+2*δ := by linarith only [har.1,hbr.2]
  change |W-(F (X b)-F (X a))| ≤ _
  calc _ = |(W-(F (A b)-F (A a)))+(F (A b)-F (X b))-(F (A a)-F (X a))| := by congr 1; ring
       _ ≤ (|W-(F (A b)-F (A a))| + |F (A b)-F (X b)|) + |F (A a)-F (X a)| :=
         (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
       _ ≤ K*δ*(X b-X a+2*δ)+B*δ+B*δ := add_le_add (add_le_add
         (hW.trans (mul_le_mul_of_nonneg_left hlen (mul_nonneg hK hδ))) hbF) haF
       _ = _ := by dsimp [X,δ]; ring

/-- The antiderivative of the two-prime density on logarithmic coordinates. -/
def pairPrimitive (x : ℝ) := Real.log x-Real.log (1-x)

private theorem primitive_derivative {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    HasDerivAt pairPrimitive (1/(x*(1-x))) x := by
  have hc := (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
  have hp := (Real.hasDerivAt_log hx.ne').sub
    ((Real.hasDerivAt_log (sub_pos.mpr hx').ne').comp x hc)
  convert hp using 1
  · rfl
  · field_simp [hx.ne',(sub_pos.mpr hx').ne'] <;> ring

/-- The semiprime primitive on a compact exponent interval. The cubic term
records the curvature lost by the constant lower bound four for its density. -/
theorem pairPrimitive_increment {d a b : ℝ} (hd : 0 < d) (ha : d ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1-d) :
    4*(b-a)+(2/3)*((1-2*a)^3-(1-2*b)^3) ≤ pairPrimitive b-pairPrimitive a ∧
    pairPrimitive b-pairPrimitive a ≤ (b-a)/d^2 := by
  let G := fun x : ℝ => 4*x-(2/3)*(1-2*x)^3
  let g := fun x : ℝ => 4+4*(1-2*x)^2
  have hder (x : ℝ) (hx : x ∈ Set.Icc a b) := primitive_derivative
    (hd.trans_le (ha.trans hx.1)) (by linarith only [hx.2,hb,hd] : x < 1)
  have hG (x : ℝ) : HasDerivAt G (g x) x := by
    dsimp [G,g]
    convert (hasDerivAt_id x |>.const_mul 4).sub
      ((((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul 2)).pow 3).const_mul (2/3:ℝ))
      using 1 <;> ring
  obtain ⟨x,hx,he⟩ := secant_value hab (fun t ht => (hder t ht).sub (hG t))
  have dx : 0 < x*(1-x) := mul_pos (hd.trans_le (ha.trans hx.1))
    (by linarith only [hx.2,hb,hd])
  have km : 0 ≤ 1/(x*(1-x))-g x := by
    rw [sub_nonneg,le_div_iff₀ dx]
    dsimp [g]
    nlinarith only [sq_nonneg ((1-2*x)^2)]
  have hlo := mul_nonneg (sub_nonneg.mpr hab) km
  change (pairPrimitive b-G b)-(pairPrimitive a-G a) = (b-a)*(1/(x*(1-x))-g x) at he
  obtain ⟨z,hz,hz'⟩ := secant_value hab hder
  have dz := mul_le_mul (ha.trans hz.1) (show d ≤ 1-z by linarith only [hz.2,hb]) hd.le
    (hd.trans_le (ha.trans hz.1)).le
  have hk := one_div_le_one_div_of_le (mul_pos hd hd) dz
  refine ⟨?_,?_⟩
  · rw [←he] at hlo
    dsimp [G] at hlo
    linarith only [hlo]
  · rw [hz',pow_two]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr hab)

private theorem kernel_lip {d u v : ℝ} (hd : 0 < d)
    (hu : u ∈ Set.Icc d (1-d)) (hv : v ∈ Set.Icc d (1-d)) :
    |1/(u*(1-u))-1/(v*(1-v))| ≤ (1/d^4)*|u-v| := by
  have hu' : d ≤ 1-u := by linarith only [hu.2]
  have hv' : d ≤ 1-v := by linarith only [hv.2]
  have Du := mul_le_mul hu.1 hu' hd.le (hd.trans_le hu.1).le
  have Dv := mul_le_mul hv.1 hv' hd.le (hd.trans_le hv.1).le
  have hdu : 0 < u*(1-u) := (mul_pos hd hd).trans_le Du
  have hdv : 0 < v*(1-v) := (mul_pos hd hd).trans_le Dv
  have scale : d^4 ≤ (u*(1-u))*(v*(1-v)) := by
    calc d^4 = (d*d)*(d*d) := by ring
         _ ≤ _ := mul_le_mul Du Dv (mul_nonneg hd.le hd.le) hdu.le
  have hlin : |1-u-v| ≤ 1 := abs_le.mpr ⟨by linarith only [hu.2,hv.2,hd.le],
    by linarith only [hu.1,hv.1,hd.le]⟩
  have he : 1/(u*(1-u))-1/(v*(1-v)) =
      ((v-u)*(1-u-v))/((u*(1-u))*(v*(1-v))) := by
    field_simp [hdu.ne',hdv.ne'] <;> ring
  rw [he,abs_div,abs_mul,abs_of_pos (mul_pos hdu hdv),abs_sub_comm v u]
  calc _ ≤ |u-v|/((u*(1-u))*(v*(1-v))) := div_le_div_of_nonneg_right
             (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlin (abs_nonneg (u-v)))
             (mul_pos hdu hdv).le
       _ ≤ |u-v|/d^4 := div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hd _) scale
       _ = _ := by ring

/-- Uniform quadrature for the actual prime weight left by counting the larger
factor of a semiprime at product scale exp(h). Both integer endpoints may vary. -/
theorem semiprime_logarithmic_weight {h d : ℝ} (hh : 0 < h) (hd : 0 < d)
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hlo : d ≤ Real.log a/h-coordinateRadius h)
    (hhi : Real.log b/h+coordinateRadius h ≤ 1-d) :
    |(∑ p ∈ Nat.primesLE b \ Nat.primesLE a, h/((p:ℝ)*(h-Real.log p))) -
      (pairPrimitive (Real.log b/h)-pairPrimitive (Real.log a/h))| ≤
        coordinateRadius h*(2*(1/d^2)+(1/d^4)*((Real.log b/h-Real.log a/h)+2*coordinateRadius h)) := by
  let f := fun x : ℝ => 1/(x*(1-x))
  let J := Set.Icc (Real.log a/h-coordinateRadius h) (Real.log b/h+coordinateRadius h)
  have inside {x : ℝ} (hx : x ∈ J) : x ∈ Set.Icc d (1-d) := ⟨hlo.trans hx.1,hx.2.trans hhi⟩
  have hD (x : ℝ) (hx : x ∈ J) := primitive_derivative (hd.trans_le (inside hx).1)
    (by linarith only [(inside hx).2,hd] : x < 1)
  have hbound (x : ℝ) (hx : x ∈ J) : |f x| ≤ 1/d^2 := by
    have h1 := (inside hx).1
    have h2 : d ≤ 1-x := by linarith only [(inside hx).2]
    have hpos := mul_pos (hd.trans_le h1) (hd.trans_le h2)
    change |1/(x*(1-x))| ≤ _
    rw [abs_of_pos (one_div_pos.mpr hpos),pow_two]
    exact one_div_le_one_div_of_le (mul_pos hd hd) (mul_le_mul h1 h2 hd.le (hd.trans_le h1).le)
  have ht := sharp_prime_quadrature hh (by positivity : 0 ≤ 1/d^4) (by positivity : 0 ≤ 1/d^2)
    a b ha hab f pairPrimitive hD (fun _ hu _ hv => kernel_lip hd (inside hu) (inside hv)) hbound
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := fun p hp => Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp hp).1.trans hab,(Nat.mem_primesLE.mp hp).2⟩
  rw [primeCoordinateSum,primeCoordinateSum,←sum_sdiff_eq_sub hsub] at ht
  have hδ : 0 ≤ coordinateRadius h := div_nonneg (add_nonneg mertensBlockGapConst_nonneg
    (Real.log_nonneg (by norm_num))) hh.le
  have terms (p : ℕ) (hp : p ∈ Nat.primesLE b \ Nat.primesLE a) :
      (Real.log p/p/h)*f (Real.log p/h) = h/(p*(h-Real.log p)) := by
    have hpp := (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hl := Real.log_pos (by exact_mod_cast hpp.one_lt : (1:ℝ) < p)
    have hpB := Real.log_le_log hp0 (by exact_mod_cast (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).1 : (p:ℝ) ≤ b)
    have hlt : Real.log p/h < 1 := by
      linarith only [div_le_div_of_nonneg_right hpB hh.le,hhi,hd,hδ]
    have hne := (sub_pos.mpr ((div_lt_one hh).mp hlt)).ne'
    dsimp [f]
    rw [show 1-Real.log p/h = (h-Real.log p)/h from by field_simp]
    field_simp [hh.ne',hl.ne',hp0.ne',hne] <;> ring
  rwa [sum_congr rfl terms] at ht

end GaloisForLFunctions.RestrictedFactorizationCalculus
